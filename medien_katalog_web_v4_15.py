#!/usr/bin/env python3
"""Filme und Serien in einem lokalen Ordner oder auf einer SMB-Freigabe katalogisieren.

Das Skript erkennt Mediendateien anhand ihrer Dateinamen, fasst Episoden einer
Serie zusammen und ergänzt Titel, IMDb-Bewertung, Cover und Kurzbeschreibung über
die OMDb-API. Standardmäßig wird rekursiv die Medienfreigabe
``\\\\192.168.2.208\\Multimedia`` durchsucht. Nur Dateien unter den Ordnern
``Filme`` und ``Serien`` werden katalogisiert.

Beispiele:
    # Unter Windows genügt auch ein Doppelklick auf die Datei.
    # Alternativ explizit im Terminal:
    python medien_katalog_web.py --web

    # Alternativ eine andere Quelle verwenden
    python medien_katalog_web.py --quelle D:\\Medien --web

    # Erst einmal nur die Erkennung prüfen
    python medien_katalog_web.py --ohne-metadaten --pfade

Für SMB wird das optionale Paket ``smbprotocol`` benötigt:
    python -m pip install smbprotocol
"""

from __future__ import annotations

import argparse
import csv
import difflib
import getpass
import hashlib
import html
import ipaddress
import json
import os
import re
import socket
import sqlite3
import subprocess
import threading
import sys
import tempfile
import textwrap
import time
import unicodedata
import webbrowser
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path, PureWindowsPath
from typing import Any, Iterable, Iterator, Sequence
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, quote, unquote, urlencode, urlsplit
from urllib.request import Request, urlopen


VERSION = "4.15.0"
OMDB_ENDPOINT = "https://www.omdbapi.com/"
IMDB_SUGGEST_ENDPOINT = "https://v3.sg.media-imdb.com/suggestion/titles/x/"
DEFAULT_OMDB_API_KEY = "fae48dc5"
OMDB_DAILY_LIMIT = 100000  # Wird beim Start aus config.txt überschrieben.
DEFAULT_MEDIA_SOURCE = r"\\192.168.2.208\Multimedia"
DEFAULT_MOVIES_SOURCE = DEFAULT_MEDIA_SOURCE + r"\Filme"
DEFAULT_SERIES_SOURCE = DEFAULT_MEDIA_SOURCE + r"\Serien"
CONFIG_FILENAME = "config.txt"
DEFAULT_STARTUP_LANGUAGE = "de"
DEFAULT_SCAN_ON_STARTUP = True


def config_path() -> Path:
    """Konfiguration immer neben dem Python-Skript suchen."""
    return Path(__file__).resolve().parent / CONFIG_FILENAME


def _join_media_child(base: str, child: str) -> str:
    base = str(base or "").strip().rstrip("\\/")
    if not base:
        return child
    if base.casefold().startswith("smb://"):
        return base + "/" + child
    if base.startswith("\\\\") or re.match(r"^[A-Za-z]:[\\/]", base):
        return base + "\\" + child
    return str(Path(base) / child)


def _normalize_app_config(values: dict[str, Any], *, seen_keys: set[str] | None = None) -> dict[str, Any]:
    """Validate and normalize application settings.

    ``Media-Path`` is accepted as a legacy setting. If the new explicit movie
    and series paths are absent, they are derived from it automatically.
    """
    seen_keys = seen_keys or set(values)
    legacy_media = str(values.get("Media-Path") or DEFAULT_MEDIA_SOURCE).strip() or DEFAULT_MEDIA_SOURCE

    try:
        limit = int(str(values.get("Max-Requests", OMDB_DAILY_LIMIT)).replace(".", "").replace(" ", ""))
        if limit < 1:
            raise ValueError
    except (TypeError, ValueError):
        raise CatalogError("Max-Requests muss eine positive ganze Zahl sein.")

    language = str(values.get("Startup-Language", DEFAULT_STARTUP_LANGUAGE)).strip().casefold()
    aliases = {"de": "de", "deutsch": "de", "german": "de", "en": "en", "english": "en", "englisch": "en"}
    if language not in aliases:
        raise CatalogError("Startup-Language muss de oder en sein.")

    raw_scan = values.get("Scan-On-Startup", DEFAULT_SCAN_ON_STARTUP)
    if isinstance(raw_scan, bool):
        scan = raw_scan
    else:
        scan_text = str(raw_scan).strip().casefold()
        if scan_text in {"yes", "y", "ja", "j", "true", "1", "on"}:
            scan = True
        elif scan_text in {"no", "n", "nein", "false", "0", "off"}:
            scan = False
        else:
            raise CatalogError("Scan-On-Startup muss Yes oder No sein.")

    movies_value = str(values.get("Movies-Path") or "").strip()
    series_value = str(values.get("Series-Path") or "").strip()
    if "Movies-Path" not in seen_keys or not movies_value:
        movies_value = _join_media_child(legacy_media, "Filme")
    if "Series-Path" not in seen_keys or not series_value:
        series_value = _join_media_child(legacy_media, "Serien")
    if not movies_value or not series_value:
        raise CatalogError("Movies-Path und Series-Path dürfen nicht leer sein.")

    return {
        "API-Key": str(values.get("API-Key") or "").strip(),
        "Max-Requests": limit,
        "Startup-Language": aliases[language],
        "Scan-On-Startup": scan,
        "Movies-Path": movies_value,
        "Series-Path": series_value,
        "Media-Path": legacy_media,  # nur intern/abwärtskompatibel
    }


def load_app_config() -> dict[str, Any]:
    """Einfache Key=Value-Konfiguration aus config.txt laden.

    Die aktuellen Schlüssel sind API-Key, Max-Requests, Startup-Language,
    Scan-On-Startup, Movies-Path und Series-Path. ``Media-Path`` wird weiterhin
    gelesen, damit ältere config.txt-Dateien automatisch funktionieren.
    """
    raw: dict[str, Any] = {
        "API-Key": DEFAULT_OMDB_API_KEY,
        "Max-Requests": OMDB_DAILY_LIMIT,
        "Startup-Language": DEFAULT_STARTUP_LANGUAGE,
        "Scan-On-Startup": "Yes" if DEFAULT_SCAN_ON_STARTUP else "No",
        "Media-Path": DEFAULT_MEDIA_SOURCE,
    }
    known = {"API-Key", "Max-Requests", "Startup-Language", "Scan-On-Startup", "Movies-Path", "Series-Path", "Media-Path"}
    seen: set[str] = set()
    path = config_path()
    if path.exists():
        try:
            for raw_line in path.read_text(encoding="utf-8-sig").splitlines():
                line = raw_line.strip()
                if not line or line.startswith("#") or line.startswith(";"):
                    continue
                if "=" not in line:
                    print(f"Warnung: Ungültige config-Zeile wird ignoriert: {raw_line}", file=sys.stderr)
                    continue
                key, value = (part.strip() for part in line.split("=", 1))
                if key in known:
                    raw[key] = value
                    seen.add(key)
        except OSError as exc:
            print(f"Warnung: {path.name} konnte nicht gelesen werden: {exc}", file=sys.stderr)
    else:
        print(f"Hinweis: {path.name} nicht gefunden; interne Standardwerte werden verwendet.", file=sys.stderr)

    try:
        return _normalize_app_config(raw, seen_keys=seen)
    except CatalogError as exc:
        print(f"Warnung: {exc} Interne Standardwerte werden verwendet.", file=sys.stderr)
        fallback = {
            "API-Key": DEFAULT_OMDB_API_KEY,
            "Max-Requests": OMDB_DAILY_LIMIT,
            "Startup-Language": DEFAULT_STARTUP_LANGUAGE,
            "Scan-On-Startup": DEFAULT_SCAN_ON_STARTUP,
            "Media-Path": DEFAULT_MEDIA_SOURCE,
            "Movies-Path": DEFAULT_MOVIES_SOURCE,
            "Series-Path": DEFAULT_SERIES_SOURCE,
        }
        return _normalize_app_config(fallback, seen_keys=set(fallback))


def save_app_config(values: dict[str, Any]) -> dict[str, Any]:
    """Validate and atomically persist config.txt next to the script."""
    normalized = _normalize_app_config(values, seen_keys=set(values))
    lines = [
        "# Media Catalog Configuration",
        "# These values can also be changed from Settings in the web interface.",
        "#",
        "# Startup-Language: de = German, en = English",
        "# Scan-On-Startup: Yes = scan media folders at startup, No = open the existing database immediately",
        "#",
        "# Path examples:",
        r"# Windows UNC:     Movies-Path=\\192.168.2.208\Multimedia\Filme",
        r"# Windows UNC:     Series-Path=\\192.168.2.208\Multimedia\Serien",
        r"# Windows drive:   Movies-Path=Z:\Multimedia\Filme",
        r"# Windows drive:   Series-Path=Z:\Multimedia\Serien",
        "# Linux mount:     Movies-Path=/mnt/multimedia/Filme",
        "# Linux mount:     Series-Path=/mnt/multimedia/Serien",
        "",
        f"API-Key={normalized['API-Key']}",
        f"Max-Requests={normalized['Max-Requests']}",
        f"Startup-Language={normalized['Startup-Language']}",
        f"Scan-On-Startup={'Yes' if normalized['Scan-On-Startup'] else 'No'}",
        f"Movies-Path={normalized['Movies-Path']}",
        f"Series-Path={normalized['Series-Path']}",
        "",
    ]
    path = config_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", newline="\n", dir=path.parent,
        prefix=path.name + ".", suffix=".tmp", delete=False,
    ) as handle:
        handle.write("\n".join(lines))
        temporary = Path(handle.name)
    os.replace(temporary, path)
    return normalized


MOVIES_ROOT_NAME = "filme"
SERIES_ROOT_NAME = "serien"

MEDIA_EXTENSIONS = {
    ".3gp",
    ".avi",
    ".flv",
    ".iso",
    ".m2ts",
    ".m4v",
    ".mkv",
    ".mov",
    ".mp4",
    ".mpeg",
    ".mpg",
    ".mts",
    ".ogm",
    ".ogv",
    ".rmvb",
    ".ts",
    ".vob",
    ".webm",
    ".wmv",
}

SERIES_DIRECTORY_NAMES = {
    "anime",
    "sendungen",
    "serien",
    "series",
    "shows",
    "tv",
    "tv serien",
    "tv series",
    "tv shows",
}

GENERIC_DIRECTORY_NAMES = SERIES_DIRECTORY_NAMES | {
    "bdmv",
    "bluray",
    "disc",
    "disk",
    "dvd",
    "filme",
    "film",
    "media",
    "medien",
    "movies",
    "movie",
    "stream",
    "video ts",
    "videos",
}

SKIPPED_DIRECTORY_NAMES = {
    "actors",
    "appledouble",
    "behind the scenes",
    "bonus",
    "deleted scenes",
    "eadir",
    "extras",
    "featurettes",
    "git",
    "lost found",
    "recycle",
    "recycle bin",
    "sample",
    "samples",
    "system volume information",
    "trailer",
    "trailers",
}

GENERIC_FILE_NAMES = {
    "feature",
    "film",
    "main",
    "movie",
    "title",
    "video",
}

EPISODE_PATTERNS = (
    re.compile(r"(?i)(?<![A-Za-z0-9])S\s*\d{1,3}[ ._-]*E\s*\d{1,4}(?:[ ._-]*E\s*\d{1,4})*"),
    re.compile(r"(?i)(?<![A-Za-z0-9])\d{1,3}\s*[xX]\s*\d{1,4}(?:\s*[-+]\s*\d{1,4})?"),
    re.compile(r"(?i)(?<![A-Za-z0-9])Staffel\s*\d{1,3}[ ._-]*(?:Folge|Episode|E)\s*\d{1,4}"),
)

SEASON_DIRECTORY_RE = re.compile(r"(?i)^(?:season|staffel|s)\s*0*\d{1,3}$")
YEAR_RE = re.compile(r"(?<!\d)((?:18|19|20)\d{2})(?!\d)")
IMDB_ID_RE = re.compile(r"(?i)(?<![A-Za-z0-9])(tt\d{7,10})(?!\d)")

# Ab dem ersten typischen Release-/Technik-Token wird der Rest abgeschnitten.
METADATA_TOKEN_RE = re.compile(
    r"(?ix)(?<![A-Za-z0-9])(?:"
    r"2160p|1080[pi]|720p|576[pi]|480[pi]|4k|8k|"
    r"uhd|hdr10\+?|hdr|dolby[ ._-]*vision|dv|sdr|"
    r"blu[ ._-]*ray|bluray|bdrip|brrip|bdremux|remux|web[ ._-]*dl|webrip|"
    r"hdtv|dvdrip|dvd|cam|telesync|"
    r"x26[45]|h[ ._-]*26[45]|hevc|av1|xvid|divx|"
    r"aac(?:2\.0|5\.1|7\.1)?|ac3|eac3|ddp(?:2\.0|5\.1|7\.1)?|"
    r"dts(?:[ ._-]*hd)?|truehd|atmos|flac|mp3|"
    r"multi|multilingual|dual[ ._-]*audio|german|deutsch|english|englisch|"
    r"proper|repack|internal|limited|extended|unrated|retail|complete|"
    r"rarbg|yts|evo"
    r")(?![A-Za-z0-9])"
)

SUPPLEMENT_FILE_RE = re.compile(
    r"(?i)(?:^|[ ._-])(?:sample|trailer|featurette|proof|bonus|deleted[ ._-]*scene)(?:$|[ ._-])"
)


class CatalogError(RuntimeError):
    """Benutzerfreundlicher Fehler beim Einlesen oder Konfigurieren."""


class OmdbTemporaryError(CatalogError):
    """Ein einzelner OMDb-Aufruf ist vorübergehend fehlgeschlagen."""


class OmdbFatalError(CatalogError):
    """Weitere OMDb-Aufrufe sind mit dieser Konfiguration nicht sinnvoll."""


@dataclass(frozen=True)
class Candidate:
    kind: str  # "movie" oder "series"
    title: str
    year: int | None
    imdb_id: str | None
    path: str


@dataclass
class MediaItem:
    kind: str
    title: str
    year: int | None
    imdb_id: str | None
    paths: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class CatalogRecord:
    art: str
    titel: str
    jahr: str
    imdb_bewertung: str
    kurzbeschreibung: str
    imdb_id: str
    dateien: int
    fundorte: tuple[str, ...]
    status: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "Art": self.art,
            "Titel": self.titel,
            "Jahr": self.jahr,
            "IMDb-Bewertung": self.imdb_bewertung,
            "Kurzbeschreibung": self.kurzbeschreibung,
            "IMDb-ID": self.imdb_id,
            "Dateien": self.dateien,
            "Fundorte": list(self.fundorte),
            "Status": self.status,
        }


def normalized_words(value: str) -> str:
    """Text robust für Vergleiche normalisieren, ohne den Anzeigetitel zu verändern."""
    value = unicodedata.normalize("NFKD", value)
    value = "".join(char for char in value if not unicodedata.combining(char))
    value = value.casefold().replace("&", " and ")
    # [^\W_] umfasst Unicode-Buchstaben und Ziffern, aber keine Unterstriche.
    return " ".join(re.findall(r"[^\W_]+", value, flags=re.UNICODE))


def display_title(value: str) -> str:
    value = " ".join(value.split()).strip(" ._-–—")
    if value and (value.islower() or value.isupper()):
        return value.title()
    return value


def split_path(path: str) -> list[str]:
    return [part for part in re.split(r"[\\/]+", path) if part]


def stem_of(path: str) -> str:
    name = split_path(path)[-1]
    return name[: -len(Path(name).suffix)] if Path(name).suffix else name


def find_episode_marker(value: str) -> re.Match[str] | None:
    matches = [match for pattern in EPISODE_PATTERNS if (match := pattern.search(value))]
    return min(matches, key=lambda match: match.start()) if matches else None


def extract_imdb_id(value: str) -> str | None:
    match = IMDB_ID_RE.search(value)
    return match.group(1).lower() if match else None


def extract_year(value: str) -> int | None:
    matches = list(YEAR_RE.finditer(value))
    if not matches:
        return None
    # Release-Jahre stehen fast immer am Ende des Titels. So bleibt z. B.
    # "2001.A.Space.Odyssey.1968" korrekt als Titel "2001 A Space Odyssey".
    match = matches[-1]
    year = int(match.group(1))

    # Vierstellige Zahlen können Bestandteil des eigentlichen Filmtitels sein,
    # z. B. "Blade Runner 2049". Ein Jahr weit in der Zukunft kann zum
    # aktuellen Zeitpunkt kein Erscheinungsjahr der vorhandenen Mediendatei sein
    # und bleibt deshalb Teil des Titels. Das Folgejahr wird für bereits
    # angekündigte/veröffentlichte Titel noch akzeptiert.
    if year > datetime.now(timezone.utc).year + 1:
        return None

    # Reine Zahlentitel wie "1917" oder "1984" sind nicht automatisch ein Jahr.
    without_year = (value[: match.start()] + value[match.end() :]).strip(" ._()[]{}-")
    return year if without_year else None


def clean_title(value: str, *, cut_at_episode: bool = False) -> tuple[str, int | None]:
    """Release-Dateinamen in einen suchbaren Titel und ein optionales Jahr zerlegen."""
    # Der Aufrufer übergibt bereits einen Dateistamm oder Ordnernamen. Path.stem
    # wäre hier falsch: Bei "Once.Upon.a.Time" würde sonst ".Time" verschwinden.
    value = str(value)
    episode = find_episode_marker(value) if cut_at_episode else None
    if episode:
        value = value[: episode.start()]

    year = extract_year(value)
    value = IMDB_ID_RE.sub(" ", value)
    value = re.sub(r"\[[^\]]*]|\{[^}]*}", " ", value)
    if year is not None:
        value = re.sub(rf"(?<!\d){year}(?!\d)", " ", value, count=1)

    value = re.sub(r"[._]+", " ", value)
    value = re.sub(r"(?<=\w)-(?=\w)", " ", value)
    value = re.sub(r"(?i)\b(?:CD|DISC|DISK)\s*0*\d{1,2}\b", " ", value)
    value = re.sub(r"(?i)\b(?:SAMPLE|TRAILER)\b", " ", value)

    metadata = METADATA_TOKEN_RE.search(value)
    if metadata:
        value = value[: metadata.start()]

    value = re.sub(r"\([^)]*(?:1080|2160|720|bluray|web.?dl|x26[45])[^)]*\)", " ", value, flags=re.I)
    value = re.sub(r"\s+", " ", value).strip(" ._()[]{}-–—")
    return display_title(value), year


def is_generic_component(value: str) -> bool:
    normalized = normalized_words(value)
    return (
        not normalized
        or normalized in GENERIC_DIRECTORY_NAMES
        or normalized in GENERIC_FILE_NAMES
        or bool(SEASON_DIRECTORY_RE.fullmatch(value.strip()))
        or bool(re.fullmatch(r"(?:title|vts)\s*\d{1,5}", normalized))
        or bool(re.fullmatch(r"0{2,}\d*", normalized))
    )


def closest_meaningful_directory(parts: Sequence[str]) -> str | None:
    # parts enthält auch den Dateinamen; daher beim vorletzten Element beginnen.
    for part in reversed(parts[:-1]):
        if not is_generic_component(part) and normalized_words(part) not in SKIPPED_DIRECTORY_NAMES:
            return part
    return None


def should_skip_file(path: str) -> bool:
    parts = split_path(path)
    if not parts:
        return True
    name = parts[-1]
    if name.startswith("._") or Path(name).suffix.casefold() not in MEDIA_EXTENSIONS:
        return True
    if SUPPLEMENT_FILE_RE.search(Path(name).stem):
        return True
    return any(normalized_words(part) in SKIPPED_DIRECTORY_NAMES for part in parts[:-1])


def library_kind_from_path(path: str) -> str | None:
    """Medientyp anhand der festen Bibliotheksordner Filme/Serien bestimmen.

    Die Prüfung betrachtet sämtliche Verzeichnisebenen. Dadurch werden auch tief
    verschachtelte Unterordner zuverlässig dem Bereich Filme oder Serien zugeordnet.
    Dateien außerhalb dieser beiden Bereiche werden bewusst nicht katalogisiert.
    """
    parts = split_path(path)
    kind: str | None = None
    for part in parts[:-1]:
        normalized = normalized_words(part)
        if normalized == MOVIES_ROOT_NAME:
            kind = "movie"
        elif normalized == SERIES_ROOT_NAME:
            kind = "series"
    return kind


def series_main_directory(parts: Sequence[str]) -> str | None:
    """Den Serien-Hauptordner direkt unterhalb von ``Serien`` zurückgeben.

    Für die Bibliotheksstruktur gilt bewusst:

        ...\\Serien\\<Serienname>\\Episode.mkv
        ...\\Serien\\<Serienname>\\Staffel 01\\Episode.mkv

    Der Dateiname einer Episode wird daher niemals zur Bestimmung des
    Seriennamens verwendet. So werden auch Dateien wie ``01.mkv`` oder
    ``Pilot - 1080p.mkv`` zuverlässig derselben Serie zugeordnet.
    """
    for index, part in enumerate(parts[:-1]):
        if normalized_words(part) == SERIES_ROOT_NAME:
            # Das nächste Element muss ein Verzeichnis sein. Eine Datei direkt
            # in \Serien wird absichtlich nicht als eigenständige Serie behandelt.
            if index + 1 < len(parts) - 1:
                return parts[index + 1]
            return None
    return None


def candidate_from_path(path: str) -> Candidate | None:
    if should_skip_file(path):
        return None

    parts = split_path(path)
    kind = library_kind_from_path(path)
    if kind is None:
        return None

    raw_stem = stem_of(path)

    if kind == "series":
        # Bei Serien ist ausschließlich der erste Ordner unterhalb von
        # ``Serien`` die Identität der Serie. Staffel- und Episodennamen dürfen
        # die Gruppierung nicht beeinflussen.
        directory = series_main_directory(parts)
        if not directory:
            return None
        title, year = clean_title(directory)
        imdb_id = extract_imdb_id(directory)
    else:
        nearby = " ".join(parts[-4:])
        imdb_id = extract_imdb_id(nearby)
        title, year = clean_title(raw_stem)
        directory = closest_meaningful_directory(parts)
        folder_title, folder_year = clean_title(directory or "")
        if not title or is_generic_component(title):
            title = folder_title
            year = year or folder_year
        elif normalized_words(folder_title) == normalized_words(title):
            year = year or folder_year

    if not title:
        return None
    return Candidate(kind=kind, title=title, year=year, imdb_id=imdb_id, path=path)



def _source_root_parts(source: str) -> list[str]:
    source = str(source or "").strip()
    if source.casefold().startswith("smb://"):
        try:
            _host, _port, unc_root = parse_smb_source(source)
            return split_path(unc_root)
        except Exception:
            return []
    return split_path(source)


def _first_directory_under_source(path: str, source: str) -> str | None:
    """Return the first directory below a configured source root."""
    path_parts = split_path(path)
    root_parts = _source_root_parts(source)
    if root_parts and len(path_parts) > len(root_parts) + 1:
        prefix_ok = all(a.casefold() == b.casefold() for a, b in zip(path_parts[:len(root_parts)], root_parts))
        if prefix_ok:
            return path_parts[len(root_parts)]
    return None


def candidate_from_configured_source(path: str, *, kind: str, source_root: str) -> Candidate | None:
    """Create a candidate when movie and series roots are configured separately."""
    if should_skip_file(path):
        return None
    parts = split_path(path)
    raw_stem = stem_of(path)
    if kind == "series":
        directory = _first_directory_under_source(path, source_root) or series_main_directory(parts)
        if not directory:
            return None
        title, year = clean_title(directory)
        imdb_id = extract_imdb_id(directory)
    else:
        nearby = " ".join(parts[-4:])
        imdb_id = extract_imdb_id(nearby)
        title, year = clean_title(raw_stem)
        directory = closest_meaningful_directory(parts)
        folder_title, folder_year = clean_title(directory or "")
        if not title or is_generic_component(title):
            title = folder_title
            year = year or folder_year
        elif normalized_words(folder_title) == normalized_words(title):
            year = year or folder_year
    if not title:
        return None
    return Candidate(kind=kind, title=title, year=year, imdb_id=imdb_id, path=path)


def default_cache_path() -> Path:
    if os.name == "nt":
        base = Path(os.environ.get("LOCALAPPDATA", Path.home() / "AppData" / "Local"))
    else:
        base = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    return base / "medien_katalog" / "omdb_cache.json"


def _is_local_address(address: str) -> bool:
    try:
        ip = ipaddress.ip_address(address.split("%", 1)[0])
    except ValueError:
        return False
    return (ip.is_private or ip.is_loopback or ip.is_link_local) and not (
        ip.is_multicast or ip.is_unspecified
    )


def validate_local_host(host: str, *, allow_public: bool) -> None:
    """Verhindert standardmäßig, dass SMB-Zugangsdaten an öffentliche Hosts gehen."""
    if allow_public:
        return

    try:
        literal = ipaddress.ip_address(host.split("%", 1)[0])
    except ValueError:
        try:
            answers = socket.getaddrinfo(host, None, type=socket.SOCK_STREAM)
        except OSError as exc:
            raise CatalogError(f"Der SMB-Host {host!r} konnte nicht aufgelöst werden: {exc}") from exc
        addresses = {answer[4][0] for answer in answers}
        if not addresses or any(not _is_local_address(address) for address in addresses):
            raise CatalogError(
                f"Der SMB-Host {host!r} löst nicht ausschließlich auf lokale Adressen auf. "
                "Mit --oeffentliche-adresse-erlauben kann diese Sperre bewusst aufgehoben werden."
            )
    else:
        if not _is_local_address(str(literal)):
            raise CatalogError(
                f"{host!r} ist keine private, lokale oder Loopback-IP-Adresse. "
                "Mit --oeffentliche-adresse-erlauben kann diese Sperre bewusst aufgehoben werden."
            )


def parse_smb_source(source: str) -> tuple[str, int, str]:
    try:
        parsed = urlsplit(source)
        host = parsed.hostname
        port = parsed.port or 445
    except ValueError as exc:
        raise CatalogError(f"Ungültige SMB-Adresse: {exc}") from exc
    if parsed.scheme.casefold() != "smb" or not host:
        raise CatalogError("Ungültige SMB-Adresse. Erwartet wird smb://IP/Freigabe[/Ordner].")
    if parsed.username is not None or parsed.password is not None:
        raise CatalogError(
            "Bitte keine Zugangsdaten in die SMB-Adresse schreiben. Nutze SMB_BENUTZER und SMB_PASSWORT."
        )
    if parsed.query or parsed.fragment:
        raise CatalogError("Eine SMB-Adresse darf keine Query-Parameter oder Fragmente enthalten.")

    components = [unquote(part) for part in parsed.path.split("/") if part]
    if not components or any(part in {".", ".."} or "\\" in part for part in components):
        raise CatalogError("Die SMB-Adresse benötigt eine gültige Freigabe ohne .- oder ..-Segmente.")

    unc_path = "\\\\" + host + "\\" + "\\".join(components)
    return host, port, unc_path


def iter_local_files(source: str) -> Iterator[str]:
    root = Path(source).expanduser()
    if not root.exists():
        raise CatalogError(f"Der Ordner existiert nicht: {root}")
    if not root.is_dir():
        raise CatalogError(f"Die Quelle ist kein Ordner: {root}")

    def on_error(error: OSError) -> None:
        print(f"Warnung: Ordner konnte nicht gelesen werden: {error}", file=sys.stderr)

    for current, directories, files in os.walk(root, followlinks=False, onerror=on_error):
        directories[:] = [
            directory
            for directory in directories
            if normalized_words(directory) not in SKIPPED_DIRECTORY_NAMES
        ]
        for filename in files:
            if Path(filename).suffix.casefold() in MEDIA_EXTENSIONS:
                yield str(Path(current) / filename)


def iter_smb_files(
    source: str,
    *,
    username: str | None,
    password: str | None,
    timeout: int,
    allow_public: bool,
) -> Iterator[str]:
    host, port, unc_root = parse_smb_source(source)
    validate_local_host(host, allow_public=allow_public)

    try:
        import smbclient  # type: ignore[import-not-found]
    except ImportError as exc:
        raise CatalogError(
            "Für smb://-Quellen fehlt das Paket 'smbprotocol'. "
            "Installiere es mit: python -m pip install smbprotocol"
        ) from exc

    session_options: dict[str, Any] = {
        "port": port,
        "connection_timeout": timeout,
    }
    if username is not None:
        session_options["username"] = username
        session_options["password"] = password or ""

    try:
        smbclient.register_session(host, **session_options)
        for current, directories, files in smbclient.walk(unc_root, topdown=True):
            directories[:] = [
                directory
                for directory in directories
                if normalized_words(directory) not in SKIPPED_DIRECTORY_NAMES
            ]
            for filename in files:
                if Path(filename).suffix.casefold() in MEDIA_EXTENSIONS:
                    yield current.rstrip("\\/") + "\\" + filename
    except Exception as exc:
        # Bibliotheksfehler sind je nach Authentifizierungsart unterschiedlich; die
        # Zugangsdaten selbst werden bewusst nicht ausgegeben.
        raise CatalogError(
            f"Die SMB-Freigabe auf {host}:{port} konnte nicht gelesen werden: "
            f"{type(exc).__name__}: {exc}"
        ) from exc
    finally:
        try:
            smbclient.reset_connection_cache()
        except Exception:
            pass


def iter_source_files(
    source: str,
    *,
    username: str | None,
    password: str | None,
    timeout: int,
    allow_public: bool,
) -> Iterator[str]:
    if source.casefold().startswith("smb://"):
        yield from iter_smb_files(
            source,
            username=username,
            password=password,
            timeout=timeout,
            allow_public=allow_public,
        )
        return

    parsed = urlsplit(source)
    is_windows_drive = bool(re.match(r"^[A-Za-z]:[\\/]", source))
    if parsed.scheme and not is_windows_drive:
        raise CatalogError("Unterstützt werden lokale Ordner und Adressen im Format smb://IP/Freigabe.")
    yield from iter_local_files(source)


def configured_media_sources(args: argparse.Namespace) -> list[tuple[str, str]]:
    return [
        (str(getattr(args, "movies_path", "") or DEFAULT_MOVIES_SOURCE), "movie"),
        (str(getattr(args, "series_path", "") or DEFAULT_SERIES_SOURCE), "series"),
    ]


def iter_configured_candidates(
    args: argparse.Namespace,
    *,
    password: str | None,
) -> Iterator[Candidate]:
    seen_paths: set[str] = set()
    for source, kind in configured_media_sources(args):
        for path in iter_source_files(
            source,
            username=args.benutzer,
            password=password,
            timeout=args.smb_timeout,
            allow_public=args.oeffentliche_adresse_erlauben,
        ):
            identity = path.casefold()
            if identity in seen_paths:
                continue
            seen_paths.add(identity)
            candidate = candidate_from_configured_source(path, kind=kind, source_root=source)
            if candidate is not None:
                yield candidate


def configured_source_summary(args: argparse.Namespace) -> str:
    return f"Filme: {getattr(args, 'movies_path', DEFAULT_MOVIES_SOURCE)} | Serien: {getattr(args, 'series_path', DEFAULT_SERIES_SOURCE)}"


def configured_server_status(args: argparse.Namespace) -> tuple[bool, str]:
    statuses: list[tuple[bool, str]] = []
    seen: set[str] = set()
    for source, _kind in configured_media_sources(args):
        key = source.casefold()
        if key in seen:
            continue
        seen.add(key)
        statuses.append(media_server_status(source))
    if not statuses:
        return False, ""
    online = all(state for state, _label in statuses)
    labels = []
    for _state, label in statuses:
        if label and label not in labels:
            labels.append(label)
    return online, ", ".join(labels)


def merge_candidates(candidates: Iterable[Candidate], *, only: str) -> list[MediaItem]:
    grouped: dict[tuple[str, str, int | None, str], MediaItem] = {}
    for candidate in candidates:
        if only == "filme" and candidate.kind != "movie":
            continue
        if only == "serien" and candidate.kind != "series":
            continue
        identity = candidate.imdb_id or ""
        key = (candidate.kind, normalized_words(candidate.title), candidate.year, identity)
        item = grouped.get(key)
        if item is None:
            item = MediaItem(
                kind=candidate.kind,
                title=candidate.title,
                year=candidate.year,
                imdb_id=candidate.imdb_id,
            )
            grouped[key] = item
        if candidate.path not in item.paths:
            item.paths.append(candidate.path)

    # Bei Filmen werden gleichnamige Varianten mit/ohne vermeintliches Jahr
    # bewusst NICHT mehr automatisch zusammengeführt. Eine vierstellige Zahl kann
    # Teil des Titels sein (z. B. "Blade Runner 2049" oder "Dracula 2000").
    # Ein aggressives Zusammenführen würde dann zwei verschiedene Filme zu einem
    # Datensatz machen. Serien dürfen weiterhin die bisherige Jahr-Zusammenführung
    # verwenden; ihre Identität stammt ohnehin aus dem Serien-Hauptordner.
    by_title: dict[tuple[str, str], list[MediaItem]] = {}
    for item in grouped.values():
        by_title.setdefault((item.kind, normalized_words(item.title)), []).append(item)

    merged: list[MediaItem] = []
    for same_title in by_title.values():
        if same_title and same_title[0].kind == "movie":
            merged.extend(same_title)
            continue

        dated = [item for item in same_title if item.year is not None]
        undated = [item for item in same_title if item.year is None]
        if len(dated) == 1:
            target = dated[0]
            for item in undated:
                for path in item.paths:
                    if path not in target.paths:
                        target.paths.append(path)
                target.imdb_id = target.imdb_id or item.imdb_id
            merged.extend(dated)
        else:
            merged.extend(same_title)

    return sorted(merged, key=lambda item: (item.kind, normalized_words(item.title), item.year or 0))


def omdb_title_match_is_suspicious(item: MediaItem, remote_title: str) -> bool:
    """Offensichtliche Sammel-/Mehrfachtitel von einer Auto-Zuordnung ausschließen.

    OMDb Search kann bei lokalisierten Titeln gelegentlich Ergebnisse liefern, in
    denen der gesuchte Film nur als Teil eines längeren Podcast-/Listen-/Sammeltitels
    vorkommt, z. B. "208: <Film A> (1982) & <Film B> (1987)". Ein passendes Jahr
    allein darf so einen Treffer niemals zu einem gültigen Film-Match machen.

    Die Prüfung ist absichtlich konservativ: Ein komplett anderssprachiger
    kanonischer Titel (z. B. deutscher Suchname -> englischer OMDb-Titel) bleibt
    erlaubt, solange er nicht wie ein zusammengesetzter Titel aussieht.
    """
    remote_title = str(remote_title or "").strip()
    if not remote_title:
        return True

    local_raw = str(item.title or "").strip()
    wanted = normalized_words(local_raw)
    received = normalized_words(remote_title)
    if not wanted or not received:
        return True
    if wanted == received:
        return False

    # Typische Nummerierung von Podcast-/Listenepisoden wie "208: ...".
    numbered_remote = bool(re.match(r"^\s*\d{1,4}\s*:\s*", remote_title))
    numbered_local = bool(re.match(r"^\s*\d{1,4}\s*:\s*", local_raw))
    if numbered_remote and not numbered_local:
        return True

    wanted_tokens = wanted.split()
    received_tokens = received.split()
    wanted_set = set(wanted_tokens)
    overlap = len(wanted_set & set(received_tokens)) / max(1, len(wanted_set))

    remote_years = {match.group(1) for match in YEAR_RE.finditer(remote_title)}
    local_years = {match.group(1) for match in YEAR_RE.finditer(local_raw)}
    # Mehrere verschiedene Filmdaten in einem zurückgelieferten Titel sind ein
    # starkes Indiz für einen Sammel-/Vergleichstitel.
    if len(remote_years) >= 2 and len(local_years) < 2 and overlap >= 0.55:
        return True

    # Wenn der lokale Titel sehr gut zu nur EINEM Teil eines per &, /, + oder ;
    # zusammengesetzten OMDb-Titels passt, ist der Gesamttreffer nicht derselbe Film.
    parts = [
        part.strip()
        for part in re.split(r"\s+(?:&|\+|/|;)\s+|\s+[–—]\s+", remote_title)
        if part.strip()
    ]
    if len(parts) >= 2:
        full_similarity = difflib.SequenceMatcher(None, wanted, received).ratio()
        part_similarity = max(
            difflib.SequenceMatcher(None, wanted, normalized_words(part)).ratio()
            for part in parts
        )
        if part_similarity >= 0.72 and part_similarity >= full_similarity + 0.08:
            return True

    # Der gesuchte Titel steckt praktisch vollständig im Ergebnis, OMDb hängt aber
    # noch einen erheblichen zweiten Titel/Textblock an. Lieber unbekannt als falsch.
    if (
        wanted in received
        and overlap >= 0.85
        and len(received_tokens) >= len(wanted_tokens) + 4
        and len(received_tokens) > len(wanted_tokens) * 1.35
    ):
        return True

    return False


class OmdbClient:
    def __init__(self, api_key: str, cache_path: Path, cache_days: int, timeout: int = 12):
        self.api_key = api_key
        self.cache_path = cache_path
        self.max_age = timedelta(days=max(0, cache_days))
        self.timeout = timeout
        self.cache: dict[str, dict[str, Any]] = {}
        self.cache_dirty = False
        self._last_request_at = 0.0
        # Zählt nur echte HTTP-Aufrufe an OMDb. Cache-Treffer erhöhen den Zähler nicht.
        self.request_count = 0
        self.limit_reached = False
        self._load_cache()

    def _load_cache(self) -> None:
        try:
            raw = json.loads(self.cache_path.read_text(encoding="utf-8"))
            if raw.get("version") == 1 and isinstance(raw.get("entries"), dict):
                self.cache = raw["entries"]
        except FileNotFoundError:
            return
        except (OSError, json.JSONDecodeError, AttributeError, TypeError) as exc:
            print(f"Warnung: OMDb-Cache wird ignoriert: {exc}", file=sys.stderr)

    def save_cache(self) -> None:
        if not self.cache_dirty:
            return
        payload = json.dumps(
            {"version": 1, "entries": self.cache},
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        try:
            self.cache_path.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile(
                "w",
                encoding="utf-8",
                dir=self.cache_path.parent,
                prefix=self.cache_path.name + ".",
                suffix=".tmp",
                delete=False,
            ) as handle:
                handle.write(payload)
                temporary = Path(handle.name)
            os.replace(temporary, self.cache_path)
            self.cache_dirty = False
        except OSError as exc:
            print(f"Warnung: OMDb-Cache konnte nicht gespeichert werden: {exc}", file=sys.stderr)

    def _cache_key(self, item: MediaItem) -> str:
        return "|".join(
            [item.kind, item.imdb_id or "", normalized_words(item.title), str(item.year or "")]
        )

    def _cached(self, key: str) -> dict[str, Any] | None:
        entry = self.cache.get(key)
        if not isinstance(entry, dict) or not isinstance(entry.get("data"), dict):
            return None
        try:
            saved_at = datetime.fromisoformat(str(entry["saved_at"]))
            if saved_at.tzinfo is None:
                saved_at = saved_at.replace(tzinfo=timezone.utc)
        except (KeyError, TypeError, ValueError):
            return None
        if datetime.now(timezone.utc) - saved_at > self.max_age:
            return None
        return entry["data"]

    def _store(self, key: str, data: dict[str, Any]) -> None:
        self.cache[key] = {
            "saved_at": datetime.now(timezone.utc).isoformat(),
            "data": data,
        }
        self.cache_dirty = True

    def cached_by_imdb_id(self, imdb_id: str) -> dict[str, Any] | None:
        """Bereits gespeicherte OMDb-Daten anhand der IMDb-ID finden.

        Diese Suche ignoriert bewusst das Cache-Alter und sendet KEINEN HTTP-Request.
        Sie dient u. a. dazu, neue DB-Felder wie Regisseur und Schauspieler aus
        früheren OMDb-Antworten nachzutragen, ohne das Tageslimit zu belasten.
        """
        wanted = imdb_id.strip().casefold()
        if not wanted:
            return None
        for entry in self.cache.values():
            if not isinstance(entry, dict):
                continue
            data = entry.get("data")
            if not isinstance(data, dict) or data.get("Response") != "True":
                continue
            if str(data.get("imdbID") or "").casefold() == wanted:
                return data
        return None

    def _request(self, parameters: dict[str, str]) -> dict[str, Any]:
        query = dict(parameters)
        query.update({"apikey": self.api_key, "r": "json", "plot": "short"})
        url = OMDB_ENDPOINT + "?" + urlencode(query)
        request = Request(url, headers={"User-Agent": f"medien-katalog/{VERSION}"})

        # Kleine Mindestpause verhindert unnötige Lastspitzen bei großen Bibliotheken.
        wait_for = 0.10 - (time.monotonic() - self._last_request_at)
        if wait_for > 0:
            time.sleep(wait_for)

        last_error: Exception | None = None
        for attempt in range(3):
            try:
                self.request_count += 1
                with urlopen(request, timeout=self.timeout) as response:
                    body = response.read().decode("utf-8")
                self._last_request_at = time.monotonic()
                data = json.loads(body)
                if not isinstance(data, dict):
                    raise ValueError("Antwort ist kein JSON-Objekt")
                if "request limit reached" in str(data.get("Error", "")).casefold():
                    self.limit_reached = True
                return data
            except HTTPError as exc:
                self._last_request_at = time.monotonic()
                if exc.code in {401, 403}:
                    raise OmdbFatalError("OMDb hat den API-Schlüssel abgelehnt.") from exc
                last_error = exc
            except (URLError, TimeoutError, socket.timeout, json.JSONDecodeError, ValueError) as exc:
                self._last_request_at = time.monotonic()
                last_error = exc
            if attempt < 2:
                time.sleep(0.5 * (2**attempt))

        reason = type(last_error).__name__ if last_error else "unbekannter Fehler"
        raise OmdbTemporaryError(f"OMDb ist nach drei Versuchen nicht erreichbar ({reason}).")

    @staticmethod
    def _response_is_plausible(
        item: MediaItem,
        data: dict[str, Any],
        *,
        require_imdb_id: bool = False,
    ) -> bool:
        if data.get("Response") != "True":
            return False
        if data.get("Type") not in {item.kind, None}:
            return False
        if require_imdb_id and item.imdb_id:
            return str(data.get("imdbID", "")).casefold() == item.imdb_id.casefold()

        remote_title = str(data.get("Title", ""))
        if omdb_title_match_is_suspicious(item, remote_title):
            return False

        wanted = normalized_words(item.title)
        received = normalized_words(remote_title)
        similarity = difflib.SequenceMatcher(None, wanted, received).ratio()
        if similarity < 0.72:
            return False

        if item.year is not None:
            year_match = YEAR_RE.search(str(data.get("Year", "")))
            if year_match and abs(int(year_match.group(1)) - item.year) > 1:
                return False
        return True

    @staticmethod
    def _search_result_year(data: dict[str, Any]) -> int | None:
        match = YEAR_RE.search(str(data.get("Year", "")))
        return int(match.group(1)) if match else None

    @classmethod
    def _choose_search_result(
        cls, item: MediaItem, data: dict[str, Any]
    ) -> dict[str, Any] | None:
        """Bestes Ergebnis einer OMDb-s=Suche vorsichtig auswählen.

        Der Such-Endpunkt ist bei übersetzten/alternativen Titeln oft toleranter als
        die direkte t=-Abfrage. Besonders mit vorhandenem Erscheinungsjahr können
        wir deshalb auch einen Treffer akzeptieren, dessen zurückgelieferter
        kanonischer Titel deutlich vom deutschen Dateinamen abweicht.
        """
        results = data.get("Search")
        if data.get("Response") != "True" or not isinstance(results, list):
            return None

        # score, Titelähnlichkeit, Ergebnisjahr, Ergebnis
        compatible: list[tuple[float, float, int | None, dict[str, Any]]] = []
        wanted = normalized_words(item.title)
        for result in results:
            if not isinstance(result, dict):
                continue
            if str(result.get("Type") or "").casefold() not in {"", item.kind.casefold()}:
                continue

            remote_title = str(result.get("Title") or "")
            if omdb_title_match_is_suspicious(item, remote_title):
                continue

            result_year = cls._search_result_year(result)
            if item.year is not None and result_year is not None and abs(result_year - item.year) > 1:
                continue

            received = normalized_words(remote_title)
            similarity = difflib.SequenceMatcher(None, wanted, received).ratio()

            # Ein passendes Jahr ist weiterhin ein starkes Signal, darf aber nie
            # allein einen verdächtigen Mehrfachtitel legitimieren (siehe Guard oben).
            score = similarity
            if item.year is not None and result_year is not None:
                score += 0.50 if result_year == item.year else 0.35
            compatible.append((score, similarity, result_year, result))

        if not compatible:
            return None
        compatible.sort(key=lambda entry: entry[0], reverse=True)
        best_score, best_similarity, best_year, best = compatible[0]

        if item.year is not None:
            # Normale ähnlich benannte Treffer benötigen weiterhin echte
            # Titelähnlichkeit. Bei lokalisierten Titeln kann diese sehr klein sein
            # (z. B. "Das Ding aus einer anderen Welt" -> "The Thing"). In
            # diesem Sonderfall akzeptieren wir nur EINEN eindeutigen Treffer mit
            # exakt passendem Jahr.
            if best_similarity >= 0.35 and best_score >= 0.70:
                return best
            exact_year = [entry for entry in compatible if entry[2] == item.year]
            if best_year == item.year and len(exact_year) == 1:
                return best
            return None

        # Ohne Jahr bleiben wir konservativer, um ähnlich benannte Filme nicht
        # automatisch falsch zuzuordnen.
        if len(compatible) == 1 and best_score >= 0.45:
            return best
        return best if best_score >= 0.68 else None

    def _search_title_fallback(self, item: MediaItem) -> dict[str, Any] | None:
        """Über OMDb Search (s=) nach alternativen/übersetzten Titeln suchen.

        Diese Stufe läuft nur, wenn die direkten t=/i=-Versuche nichts ergeben
        haben. Sie verursacht daher nur bei neuen bzw. bislang unbekannten Titeln
        zusätzliche Requests.
        """
        parameters = {"s": item.title, "type": item.kind}
        if item.year is not None:
            parameters["y"] = str(item.year)

        search_data = self._request(parameters)
        error = str(search_data.get("Error", ""))
        error_folded = error.casefold()
        if any(
            marker in error_folded
            for marker in ("invalid api key", "no api key", "request limit reached")
        ):
            raise OmdbFatalError(f"OMDb-Fehler: {error}")

        candidate = self._choose_search_result(item, search_data)
        if candidate is None:
            return None
        imdb_id = str(candidate.get("imdbID") or "").strip()
        if not IMDB_ID_RE.fullmatch(imdb_id):
            return None

        detail = self._request({"i": imdb_id})
        error = str(detail.get("Error", ""))
        error_folded = error.casefold()
        if any(
            marker in error_folded
            for marker in ("invalid api key", "no api key", "request limit reached")
        ):
            raise OmdbFatalError(f"OMDb-Fehler: {error}")
        if detail.get("Response") != "True":
            return None
        if str(detail.get("Type") or "").casefold() not in {"", item.kind.casefold()}:
            return None
        if omdb_title_match_is_suspicious(item, str(detail.get("Title") or "")):
            return None
        return detail

    def lookup(self, item: MediaItem) -> dict[str, Any] | None:
        key = self._cache_key(item)

        # Falls eine vierstellige Zahl fälschlich wie ein Erscheinungsjahr aussieht,
        # kann sie in Wahrheit Teil des Titels sein (z. B. "Dracula 2000").
        # Diese alternative Lesart wird vor einer unspezifischen Titelsuche geprüft.
        numeric_title_item: MediaItem | None = None
        if item.year is not None and not item.imdb_id:
            numeric_title_item = MediaItem(
                kind=item.kind,
                title=f"{item.title} {item.year}",
                year=None,
                imdb_id=None,
            )

        cached = self._cached(key)
        if cached is not None:
            if self._response_is_plausible(item, cached):
                return cached
            if numeric_title_item and self._response_is_plausible(numeric_title_item, cached):
                return cached

        # Jeder Versuch enthält neben den Request-Parametern auch das Objekt, gegen
        # das die OMDb-Antwort plausibilisiert werden soll.
        attempts: list[tuple[dict[str, str], MediaItem]] = []
        if item.imdb_id:
            attempts.append(({"i": item.imdb_id}, item))

        with_year = {"t": item.title, "type": item.kind}
        if item.year is not None:
            with_year["y"] = str(item.year)
        attempts.append((with_year, item))

        if numeric_title_item is not None:
            attempts.append(({"t": numeric_title_item.title, "type": item.kind}, numeric_title_item))
            attempts.append(({"t": item.title, "type": item.kind}, item))

        for parameters, validation_item in attempts:
            data = self._request(parameters)
            error = str(data.get("Error", ""))
            error_folded = error.casefold()
            if any(
                marker in error_folded
                for marker in ("invalid api key", "no api key", "request limit reached")
            ):
                raise OmdbFatalError(f"OMDb-Fehler: {error}")
            if self._response_is_plausible(
                validation_item, data, require_imdb_id="i" in parameters
            ):
                self._store(key, data)
                return data

        # Zweite Suchstufe: OMDb Search ist bei alternativen bzw. lokalisierten
        # Titeln oft toleranter als die direkte t=-Abfrage. Damit können z. B.
        # deutsche Dateinamen auf den englischen OMDb-Haupttitel führen, sofern
        # OMDb den Alternativtitel in seiner Suche kennt.
        fallback = self._search_title_fallback(item)
        if fallback is not None:
            self._store(key, fallback)
            return fallback

        self._store(key, {"Response": "False", "Error": "No plausible match"})
        return None


def record_from_item(
    item: MediaItem,
    metadata: dict[str, Any] | None,
    *,
    lookup_attempted: bool = True,
) -> CatalogRecord:
    if metadata:
        title = str(metadata.get("Title") or item.title)
        year = str(metadata.get("Year") or item.year or "–")
        rating = str(metadata.get("imdbRating") or "–")
        if rating == "N/A":
            rating = "–"
        plot = str(metadata.get("Plot") or "Keine Kurzbeschreibung vorhanden.")
        if plot == "N/A":
            plot = "Keine Kurzbeschreibung vorhanden."
        imdb_id = str(metadata.get("imdbID") or item.imdb_id or "")
        status = "gefunden"
    else:
        title = item.title
        year = str(item.year or "–")
        rating = "–"
        plot = (
            "Keine eindeutige Zuordnung bei OMDb gefunden."
            if lookup_attempted
            else "Metadatenabfrage deaktiviert."
        )
        imdb_id = item.imdb_id or ""
        status = "nicht zugeordnet" if lookup_attempted else "Metadaten deaktiviert"

    return CatalogRecord(
        art="Film" if item.kind == "movie" else "Serie",
        titel=title,
        jahr=year,
        imdb_bewertung=rating,
        kurzbeschreibung=plot,
        imdb_id=imdb_id,
        dateien=len(item.paths),
        fundorte=tuple(sorted(item.paths)),
        status=status,
    )


def print_catalog(records: Sequence[CatalogRecord], *, show_paths: bool) -> None:
    width = max(60, min(110, os.get_terminal_size().columns if sys.stdout.isatty() else 90))
    print(f"\n{len(records)} Titel gefunden\n")
    for index, record in enumerate(records, start=1):
        year = f" ({record.jahr})" if record.jahr != "–" else ""
        rating = f"IMDb {record.imdb_bewertung}/10" if record.imdb_bewertung != "–" else "IMDb –"
        print(f"{index}. [{record.art}] {record.titel}{year} — {rating}")
        print(textwrap.fill(record.kurzbeschreibung, width=width, initial_indent="   ", subsequent_indent="   "))
        if record.art == "Serie" and record.dateien > 1:
            print(f"   Erkannte Episodendateien: {record.dateien}")
        if show_paths:
            for path in record.fundorte:
                print(textwrap.fill(path, width=width, initial_indent="   Pfad: ", subsequent_indent="         "))
        print()


def atomic_write_text(path: Path, content: str, *, encoding: str) -> None:
    path = path.expanduser()
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w",
        encoding=encoding,
        newline="",
        dir=path.parent,
        prefix=path.name + ".",
        suffix=".tmp",
        delete=False,
    ) as handle:
        handle.write(content)
        temporary = Path(handle.name)
    os.replace(temporary, path)


def write_csv(path: Path, records: Sequence[CatalogRecord]) -> None:
    import io

    buffer = io.StringIO(newline="")
    fieldnames = [
        "Art",
        "Titel",
        "Jahr",
        "IMDb-Bewertung",
        "Kurzbeschreibung",
        "IMDb-ID",
        "Dateien",
        "Fundorte",
        "Status",
    ]
    writer = csv.DictWriter(buffer, fieldnames=fieldnames, delimiter=";")
    writer.writeheader()
    for record in records:
        row = record.as_dict()
        row["Fundorte"] = " | ".join(record.fundorte)
        writer.writerow(row)
    atomic_write_text(path, buffer.getvalue(), encoding="utf-8-sig")


def write_json(path: Path, records: Sequence[CatalogRecord]) -> None:
    content = json.dumps([record.as_dict() for record in records], ensure_ascii=False, indent=2)
    atomic_write_text(path, content + "\n", encoding="utf-8")



def application_directory() -> Path:
    """Stabiler Programmordner, unabhängig vom Windows-Arbeitsverzeichnis."""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def default_database_path() -> Path:
    # Beim Doppelklick kann Windows ein anderes Arbeitsverzeichnis verwenden
    # (z. B. System32). Die Datenbank liegt deshalb immer neben dem Skript.
    return application_directory() / "medien_katalog.sqlite3"


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _scan_key(item: MediaItem) -> str:
    return "|".join((item.kind, normalized_words(item.title), str(item.year or "")))


def open_database(path: Path) -> sqlite3.Connection:
    path = path.expanduser()
    path.parent.mkdir(parents=True, exist_ok=True)
    connection = sqlite3.connect(path, timeout=30)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute("PRAGMA journal_mode = WAL")
    connection.executescript(
        """
        CREATE TABLE IF NOT EXISTS media (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            scan_key TEXT NOT NULL UNIQUE,
            kind TEXT NOT NULL,
            source_title TEXT NOT NULL,
            source_year INTEGER,
            imdb_id TEXT NOT NULL DEFAULT '',
            manual_imdb_id TEXT NOT NULL DEFAULT '',
            title TEXT NOT NULL,
            year TEXT NOT NULL DEFAULT '–',
            imdb_rating TEXT NOT NULL DEFAULT '–',
            plot TEXT NOT NULL DEFAULT '',
            poster TEXT NOT NULL DEFAULT '',
            genre TEXT NOT NULL DEFAULT '',
            director TEXT NOT NULL DEFAULT '',
            actors TEXT NOT NULL DEFAULT '',
            runtime TEXT NOT NULL DEFAULT '',
            age_rating TEXT NOT NULL DEFAULT '',
            status TEXT NOT NULL DEFAULT '',
            is_kids INTEGER NOT NULL DEFAULT 0,
            kids_manual INTEGER NOT NULL DEFAULT 0,
            file_count INTEGER NOT NULL DEFAULT 0,
            paths_json TEXT NOT NULL DEFAULT '[]',
            server_added_at TEXT NOT NULL DEFAULT '',
            last_seen_scan TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_media_kind_title ON media(kind, title);
        CREATE INDEX IF NOT EXISTS idx_media_imdb_id ON media(imdb_id);

        CREATE TABLE IF NOT EXISTS catalog_meta (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS omdb_usage (
            usage_date TEXT NOT NULL,
            api_key_hash TEXT NOT NULL,
            request_count INTEGER NOT NULL DEFAULT 0,
            PRIMARY KEY (usage_date, api_key_hash)
        );
        """
    )
    # Schema-Migration für bereits vorhandene Datenbanken aus älteren Versionen.
    columns = {str(row["name"]) for row in connection.execute("PRAGMA table_info(media)")}
    if "is_kids" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN is_kids INTEGER NOT NULL DEFAULT 0")
    if "kids_manual" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN kids_manual INTEGER NOT NULL DEFAULT 0")
    if "director" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN director TEXT NOT NULL DEFAULT ''")
    if "actors" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN actors TEXT NOT NULL DEFAULT ''")
    if "server_added_at" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN server_added_at TEXT NOT NULL DEFAULT ''")
    if "age_rating" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN age_rating TEXT NOT NULL DEFAULT ''")
    connection.commit()
    return connection


def _set_meta(connection: sqlite3.Connection, key: str, value: str) -> None:
    connection.execute(
        "INSERT INTO catalog_meta(key, value) VALUES(?, ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (key, value),
    )


def _omdb_usage_date() -> str:
    """Lokaler Kalendertag für den sichtbaren Tageszähler."""
    return datetime.now().astimezone().date().isoformat()


def _omdb_key_hash(api_key: str) -> str:
    # Der Schlüssel selbst wird nicht zusätzlich in der Datenbank gespeichert.
    return hashlib.sha256(api_key.encode("utf-8")).hexdigest()[:24]


def add_omdb_usage(
    connection: sqlite3.Connection,
    api_key: str,
    request_count: int,
    *,
    limit_reached: bool = False,
) -> None:
    """Die während einer Operation gezählten Requests atomar in SQLite übernehmen."""
    if not api_key:
        return
    count = max(0, int(request_count))
    if count:
        connection.execute(
            """
            INSERT INTO omdb_usage(usage_date, api_key_hash, request_count)
            VALUES(?, ?, ?)
            ON CONFLICT(usage_date, api_key_hash)
            DO UPDATE SET request_count=request_count+excluded.request_count
            """,
            (_omdb_usage_date(), _omdb_key_hash(api_key), count),
        )
    if limit_reached:
        connection.execute(
            """
            INSERT INTO omdb_usage(usage_date, api_key_hash, request_count)
            VALUES(?, ?, ?)
            ON CONFLICT(usage_date, api_key_hash)
            DO UPDATE SET request_count=MAX(request_count, excluded.request_count)
            """,
            (_omdb_usage_date(), _omdb_key_hash(api_key), OMDB_DAILY_LIMIT),
        )


def get_omdb_usage(db_path: Path, api_key: str) -> tuple[int, int, int]:
    """(lokal gezählt, Tageslimit, ungefähr verbleibend)."""
    if not api_key:
        return 0, OMDB_DAILY_LIMIT, OMDB_DAILY_LIMIT
    connection = open_database(db_path)
    try:
        row = connection.execute(
            "SELECT request_count FROM omdb_usage WHERE usage_date=? AND api_key_hash=?",
            (_omdb_usage_date(), _omdb_key_hash(api_key)),
        ).fetchone()
        used = int(row["request_count"]) if row else 0
    finally:
        connection.close()
    return used, OMDB_DAILY_LIMIT, max(0, OMDB_DAILY_LIMIT - used)


def _metadata_values(
    item: MediaItem,
    metadata: dict[str, Any] | None,
    *,
    old_row: sqlite3.Row | None = None,
    lookup_attempted: bool = True,
) -> dict[str, Any]:
    if metadata and metadata.get("Response") == "True":
        rating = str(metadata.get("imdbRating") or "–")
        if rating == "N/A":
            rating = "–"
        plot = str(metadata.get("Plot") or "Keine Kurzbeschreibung vorhanden.")
        if plot == "N/A":
            plot = "Keine Kurzbeschreibung vorhanden."
        poster = str(metadata.get("Poster") or "")
        if poster == "N/A":
            poster = ""
        return {
            "imdb_id": str(metadata.get("imdbID") or item.imdb_id or ""),
            "title": str(metadata.get("Title") or item.title),
            "year": str(metadata.get("Year") or item.year or "–"),
            "imdb_rating": rating,
            "plot": plot,
            "poster": poster,
            "genre": "" if metadata.get("Genre") == "N/A" else str(metadata.get("Genre") or ""),
            "director": "" if metadata.get("Director") == "N/A" else str(metadata.get("Director") or ""),
            "actors": "" if metadata.get("Actors") == "N/A" else str(metadata.get("Actors") or ""),
            "runtime": "" if metadata.get("Runtime") == "N/A" else str(metadata.get("Runtime") or ""),
            "age_rating": "" if metadata.get("Rated") == "N/A" else str(metadata.get("Rated") or ""),
            "status": "gefunden",
        }

    # Bei einem nur vorübergehend fehlgeschlagenen Refresh vorhandene gute Metadaten
    # nicht verwerfen. So bleibt der Katalog auch bei einer OMDb-Störung vollständig.
    if old_row is not None and old_row["imdb_id"]:
        return {
            "imdb_id": old_row["imdb_id"],
            "title": old_row["title"],
            "year": old_row["year"],
            "imdb_rating": old_row["imdb_rating"],
            "plot": old_row["plot"],
            "poster": old_row["poster"],
            "genre": old_row["genre"],
            "director": old_row["director"],
            "actors": old_row["actors"],
            "runtime": old_row["runtime"],
            "age_rating": old_row["age_rating"],
            "status": old_row["status"],
        }

    return {
        "imdb_id": item.imdb_id or "",
        "title": item.title,
        "year": str(item.year or "–"),
        "imdb_rating": "–",
        "plot": (
            "Keine eindeutige Zuordnung bei OMDb gefunden."
            if lookup_attempted
            else "Metadatenabfrage deaktiviert."
        ),
        "poster": "",
        "genre": "",
        "director": "",
        "actors": "",
        "runtime": "",
        "age_rating": "",
        "status": "nicht zugeordnet" if lookup_attempted else "Metadaten deaktiviert",
    }


def lookup_exact_imdb(client: OmdbClient, imdb_id: str) -> dict[str, Any]:
    """Eine vom Benutzer vorgegebene IMDb-ID ohne Titelfuzzy-Matching auflösen."""
    imdb_id = imdb_id.strip().lower()
    if not IMDB_ID_RE.fullmatch(imdb_id):
        raise CatalogError("Ungültige IMDb-ID. Erwartet wird z. B. tt1234567.")
    data = client._request({"i": imdb_id})
    if data.get("Response") != "True" or str(data.get("imdbID", "")).lower() != imdb_id:
        raise CatalogError(str(data.get("Error") or "IMDb-ID wurde bei OMDb nicht gefunden."))
    return data


def parse_imdb_reference(value: str) -> str:
    match = IMDB_ID_RE.search(value.strip())
    if not match:
        raise CatalogError(
            "Bitte eine IMDb-/OMDb-URL mit tt-ID oder direkt eine tt-ID wie tt1234567 eingeben."
        )
    return match.group(1).lower()


def _auto_kids_from_metadata(metadata: dict[str, Any] | None) -> int:
    """Konservative automatische Kinder-Einstufung aus OMDb-Metadaten.

    Die manuelle Kennzeichnung in der Weboberfläche hat immer Vorrang.
    """
    if not metadata or metadata.get("Response") != "True":
        return 0
    genre = normalized_words(str(metadata.get("Genre") or ""))
    rated = str(metadata.get("Rated") or "").strip().upper()
    genres = set(genre.split())
    if "family" in genres:
        return 1
    if rated in {"G", "TV-Y", "TV-Y7", "TV-G"}:
        return 1
    if "animation" in genres and rated in {"PG", "TV-PG"}:
        return 1
    return 0


def _stored_automatic_match_is_suspicious(old_row: sqlite3.Row | None) -> bool:
    """Bereits gespeicherte offensichtliche Fehlzuordnungen erneut prüfen.

    Manuelle IMDb-Zuordnungen werden niemals automatisch angezweifelt.
    """
    if old_row is None:
        return False
    if str(old_row["manual_imdb_id"] or "").strip():
        return False
    if str(old_row["status"] or "").casefold() != "gefunden":
        return False
    if not str(old_row["imdb_id"] or "").strip():
        return False

    try:
        source_year = int(old_row["source_year"]) if old_row["source_year"] not in (None, "", "–") else None
    except (TypeError, ValueError):
        source_year = None
    item = MediaItem(
        kind=str(old_row["kind"] or "movie"),
        title=str(old_row["source_title"] or old_row["title"] or ""),
        year=source_year,
        imdb_id=None,
    )
    if omdb_title_match_is_suspicious(item, str(old_row["title"] or "")):
        return True

    # Bei bekanntem lokalem Jahr ist auch ein deutlich anderes OMDb-Jahr verdächtig.
    if source_year is not None:
        match = YEAR_RE.search(str(old_row["year"] or ""))
        if match and abs(int(match.group(1)) - source_year) > 1:
            return True
    return False


def _existing_metadata_is_reusable(old_row: sqlite3.Row | None) -> bool:
    """True, wenn ein vorhandener DB-Eintrag ohne OMDb erneut benutzt werden kann.

    Erfolgreich automatisch gefundene Titel und weiterhin manuell fest zugeordnete
    Titel sind bereits vollständig in SQLite gespeichert. Offensichtlich verdächtige
    alte Auto-Treffer werden dagegen einmal neu geprüft.
    """
    if old_row is None:
        return False
    imdb_id = str(old_row["imdb_id"] or "").strip()
    if not imdb_id:
        return False
    manual_imdb_id = str(old_row["manual_imdb_id"] or "").strip()
    if manual_imdb_id:
        return True
    status = str(old_row["status"] or "").casefold()
    return status == "gefunden" and not _stored_automatic_match_is_suspicious(old_row)


def _server_stat_timestamp(path: str) -> float | None:
    """Robusten Zeitstempel für Datei oder Ordner liefern.

    Bei Windows/SMB ist ``st_ctime`` normalerweise die Erstellungszeit. Manche NAS-
    Implementierungen bzw. Kopierprogramme liefern jedoch sinnvollere Werte über
    ``st_mtime``. Deshalb verwenden wir bewusst den jüngeren der verfügbaren Werte.
    """
    try:
        stat_result = os.stat(path)
    except OSError:
        return None

    candidates: list[float] = []
    for value in (
        getattr(stat_result, "st_ctime", 0),
        getattr(stat_result, "st_mtime", 0),
        getattr(stat_result, "st_birthtime", 0),
    ):
        try:
            timestamp = float(value)
        except (TypeError, ValueError):
            continue
        if timestamp > 0:
            candidates.append(timestamp)
    return max(candidates) if candidates else None


def _server_timestamp_targets(path: str) -> list[str]:
    """Datei plus relevante Titel-/Staffelordner für die Zeitbestimmung liefern.

    Bei Serien ändert sich beim Hinzufügen einer Episode häufig nur der Staffelordner,
    nicht der Serien-Hauptordner. Deshalb werden die Elternordner bis zum Titelordner
    berücksichtigt. Bei Filmen gilt dasselbe für Unterstrukturen wie BDMV/STREAM.
    """
    targets = [path]
    use_windows = bool(re.match(r"^[A-Za-z]:[\\/]", path)) or "\\" in path
    pure = PureWindowsPath(path) if use_windows else Path(path)
    parts = list(pure.parts)
    if len(parts) < 2:
        return targets

    root_index: int | None = None
    for index, part in enumerate(parts[:-1]):
        normalized = normalized_words(str(part).rstrip("\\/"))
        if normalized in {MOVIES_ROOT_NAME, SERIES_ROOT_NAME}:
            root_index = index
    if root_index is None:
        return targets

    # Der erste Ordner nach Filme/Serien ist der Titelordner. Liegt eine Filmdatei
    # direkt unter Filme, existiert kein eigener Titelordner und nur die Datei zählt.
    title_dir_index = root_index + 1
    if title_dir_index >= len(parts) - 1:
        return targets

    path_cls = PureWindowsPath if use_windows else Path
    for end_index in range(len(parts) - 1, title_dir_index - 1, -1):
        try:
            parent = str(path_cls(*parts[: end_index + 1]))
        except (TypeError, ValueError):
            continue
        if parent and parent not in targets:
            targets.append(parent)
    return targets


def _server_file_timestamp(path: str) -> float | None:
    """Bestmöglichen Server-Zeitstempel einer Mediendatei ermitteln."""
    timestamps = [
        timestamp
        for target in _server_timestamp_targets(path)
        if (timestamp := _server_stat_timestamp(target)) is not None
    ]
    return max(timestamps) if timestamps else None


def _server_added_at(paths: Sequence[str], previous: str = "", fallback: str = "") -> str:
    """Jüngsten Server-Dateizeitpunkt eines Titels als UTC-ISO-Zeit speichern.

    ``fallback`` wird nur verwendet, wenn der Dateiserver für keinen gespeicherten
    Pfad einen Zeitstempel liefert. Damit bleiben bestehende Bibliotheken filterbar,
    selbst wenn ein NAS einzelne Stat-Abfragen nicht unterstützt.
    """
    timestamps = [timestamp for path in paths if (timestamp := _server_file_timestamp(path)) is not None]
    if timestamps:
        return datetime.fromtimestamp(max(timestamps), tz=timezone.utc).isoformat()
    return previous or fallback


def _backfill_server_added_dates(connection: sqlite3.Connection) -> tuple[int, int]:
    """Fehlende Serverdaten aus bereits in SQLite gespeicherten Pfaden nachtragen.

    Das ist besonders wichtig nach dem Upgrade von v3.x: Dort existiert die
    ``server_added_at``-Spalte noch nicht. Dadurch funktioniert der Zeitfilter auch,
    wenn der Nutzer beim Programmstart bewusst keinen vollständigen Scan auswählt.

    Rückgabe: (nachgetragen, weiterhin ohne Serverdatum).
    """
    rows = connection.execute(
        "SELECT id, paths_json, server_added_at, created_at FROM media"
    ).fetchall()
    updated = 0
    missing = 0
    for row in rows:
        if str(row["server_added_at"] or "").strip():
            continue
        try:
            paths = json.loads(row["paths_json"] or "[]")
        except (json.JSONDecodeError, TypeError):
            paths = []
        if not isinstance(paths, list):
            paths = []
        # created_at ist nur ein letzter Fallback. Normalerweise kommt der Wert direkt
        # vom Server; er verhindert aber dauerhaft leere Filter bei problematischen NAS.
        fallback = str(row["created_at"] or "").strip()
        added_at = _server_added_at([str(p) for p in paths], fallback=fallback)
        if added_at:
            connection.execute(
                "UPDATE media SET server_added_at=? WHERE id=?",
                (added_at, int(row["id"])),
            )
            updated += 1
        else:
            missing += 1
    if updated:
        connection.commit()
    return updated, missing


def scan_into_database(
    args: argparse.Namespace,
    *,
    password: str | None,
    omdb_key: str,
) -> tuple[int, int, int, int]:
    """Quelle vollständig scannen und SQLite atomar auf den aktuellen Bestand bringen.

    Rückgabe: (Titelanzahl, entfernte Titel, echte OMDb-HTTP-Aufrufe,
    aus SQLite wiederverwendete Metadatensätze).
    """
    candidates = iter_configured_candidates(args, password=password)
    items = merge_candidates(candidates, only=args.nur)
    limited_scan = bool(args.max_titel and len(items) > args.max_titel)
    if limited_scan:
        items = items[: args.max_titel]

    client = None if args.ohne_metadaten else OmdbClient(omdb_key, args.cache, args.cache_tage)
    omdb_available = client is not None
    omdb_error = ""
    scan_id = _utc_now()
    connection = open_database(args.db)
    try:
        connection.execute("BEGIN IMMEDIATE")
        reused_metadata = 0
        for index, item in enumerate(items, start=1):
            key = _scan_key(item)
            old_row = connection.execute("SELECT * FROM media WHERE scan_key = ?", (key,)).fetchone()
            manual_imdb_id = str(old_row["manual_imdb_id"]) if old_row else ""
            suspicious_existing = _stored_automatic_match_is_suspicious(old_row)
            reuse_existing = _existing_metadata_is_reusable(old_row)

            metadata: dict[str, Any] | None = None
            if reuse_existing:
                # Titel, Bewertung, Plot, Poster usw. liegen bereits in SQLite.
                # Ein Laufwerks-Scan aktualisiert dann nur Pfade/Dateizahl/Bestand.
                reused_metadata += 1
                if not args.ruhig:
                    print(f"DB   {index}/{len(items)}: {item.title}", file=sys.stderr)
            elif client and omdb_available:
                if not args.ruhig:
                    print(f"OMDb {index}/{len(items)}: {item.title}", file=sys.stderr)
                try:
                    # Ein noch aktiver manueller Eintrag wäre oben bereits als
                    # wiederverwendbar erkannt worden. Dieser Zweig ist daher vor
                    # allem für neue bzw. bisher unbekannte Titel gedacht.
                    if manual_imdb_id:
                        metadata = lookup_exact_imdb(client, manual_imdb_id)
                    else:
                        metadata = client.lookup(item)
                except OmdbTemporaryError as exc:
                    print(f"Warnung bei {item.title!r}: {exc}", file=sys.stderr)
                except OmdbFatalError as exc:
                    # Ein Tageslimit oder ein abgelehnter Key darf den eigentlichen
                    # Laufwerksabgleich nicht zurückrollen. Für diesen Scan werden
                    # weitere OMDb-Aufrufe ausgesetzt; Datei-/DB-Synchronisation läuft weiter.
                    omdb_available = False
                    omdb_error = str(exc)
                    print(
                        f"Warnung: {exc} Weitere OMDb-Abfragen werden für diesen Scan übersprungen; "
                        "die Bibliothek wird trotzdem vollständig synchronisiert.",
                        file=sys.stderr,
                    )

            values = _metadata_values(
                item,
                metadata,
                # Ein bekannter, aber offensichtlich falscher Auto-Treffer darf bei
                # einer fehlgeschlagenen Neuprüfung nicht erneut konserviert werden.
                # Dann ist "nicht zugeordnet" sicherer als eine falsche IMDb-ID.
                old_row=None if suspicious_existing else old_row,
                lookup_attempted=client is not None,
            )

            # Neue DB-Felder wie Regisseur und Schauspieler werden für bereits
            # bekannte Titel bevorzugt aus dem vorhandenen OMDb-Cache ergänzt.
            # Das erzeugt keinerlei neue API-Aufrufe.
            if (
                reuse_existing
                and client is not None
                and old_row is not None
                and (
                    not str(values.get("director") or "").strip()
                    or not str(values.get("actors") or "").strip()
                    or not str(values.get("age_rating") or "").strip()
                )
                and str(old_row["imdb_id"] or "").strip()
            ):
                cached_metadata = client.cached_by_imdb_id(str(old_row["imdb_id"]))
                if cached_metadata:
                    cached_director = cached_metadata.get("Director")
                    if not str(values.get("director") or "").strip() and cached_director and cached_director != "N/A":
                        values["director"] = str(cached_director)
                    cached_actors = cached_metadata.get("Actors")
                    if not str(values.get("actors") or "").strip() and cached_actors and cached_actors != "N/A":
                        values["actors"] = str(cached_actors)
                    cached_rated = cached_metadata.get("Rated")
                    if not str(values.get("age_rating") or "").strip() and cached_rated and cached_rated != "N/A":
                        values["age_rating"] = str(cached_rated)

                # Bei älteren Datenbanken fehlt Rated häufig auch im lokalen OMDb-Cache.
                # Dann wird die Altersfreigabe genau einmal anhand der bereits bekannten
                # IMDb-ID nachgeladen. Das betrifft nur Titel ohne age_rating; vollständig
                # gepflegte Altbestände verursachen weiterhin keinerlei API-Aufrufe.
                if (
                    not str(values.get("age_rating") or "").strip()
                    and client is not None
                    and omdb_available
                    and str(old_row["imdb_id"] or "").strip()
                ):
                    try:
                        fresh_metadata = lookup_exact_imdb(client, str(old_row["imdb_id"]))
                        fresh_rated = fresh_metadata.get("Rated")
                        if fresh_rated and fresh_rated != "N/A":
                            values["age_rating"] = str(fresh_rated)
                    except OmdbTemporaryError as exc:
                        print(f"Warnung beim Nachladen der Altersfreigabe für {item.title!r}: {exc}", file=sys.stderr)
                    except OmdbFatalError as exc:
                        omdb_available = False
                        omdb_error = str(exc)
                        print(
                            f"Warnung: {exc} Weitere OMDb-Abfragen werden für diesen Scan übersprungen; "
                            "die Bibliothek wird trotzdem vollständig synchronisiert.",
                            file=sys.stderr,
                        )
                    except CatalogError as exc:
                        print(f"Warnung beim Nachladen der Altersfreigabe für {item.title!r}: {exc}", file=sys.stderr)

            kids_manual = int(old_row["kids_manual"]) if old_row else 0
            if kids_manual:
                is_kids = int(old_row["is_kids"])
            elif metadata and metadata.get("Response") == "True":
                is_kids = _auto_kids_from_metadata(metadata)
            elif old_row:
                is_kids = int(old_row["is_kids"])
            else:
                is_kids = 0
            now = _utc_now()
            created_at = str(old_row["created_at"]) if old_row else now
            previous_server_added = str(old_row["server_added_at"] or "") if old_row else ""
            server_added_at = _server_added_at(item.paths, previous_server_added, created_at)
            connection.execute(
                """
                INSERT INTO media(
                    scan_key, kind, source_title, source_year, imdb_id, manual_imdb_id,
                    title, year, imdb_rating, plot, poster, genre, director, actors, runtime, age_rating, status,
                    is_kids, kids_manual, file_count, paths_json, server_added_at, last_seen_scan, created_at, updated_at
                ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(scan_key) DO UPDATE SET
                    kind=excluded.kind,
                    source_title=excluded.source_title,
                    source_year=excluded.source_year,
                    imdb_id=excluded.imdb_id,
                    title=excluded.title,
                    year=excluded.year,
                    imdb_rating=excluded.imdb_rating,
                    plot=excluded.plot,
                    poster=excluded.poster,
                    genre=excluded.genre,
                    director=excluded.director,
                    actors=excluded.actors,
                    runtime=excluded.runtime,
                    age_rating=excluded.age_rating,
                    status=excluded.status,
                    is_kids=excluded.is_kids,
                    kids_manual=excluded.kids_manual,
                    file_count=excluded.file_count,
                    paths_json=excluded.paths_json,
                    server_added_at=excluded.server_added_at,
                    last_seen_scan=excluded.last_seen_scan,
                    updated_at=excluded.updated_at
                """,
                (
                    key,
                    item.kind,
                    item.title,
                    item.year,
                    values["imdb_id"],
                    manual_imdb_id,
                    values["title"],
                    values["year"],
                    values["imdb_rating"],
                    values["plot"],
                    values["poster"],
                    values["genre"],
                    values["director"],
                    values["actors"],
                    values["runtime"],
                    values["age_rating"],
                    values["status"],
                    is_kids,
                    kids_manual,
                    len(item.paths),
                    json.dumps(sorted(item.paths), ensure_ascii=False),
                    server_added_at,
                    scan_id,
                    created_at,
                    now,
                ),
            )

        removed = 0
        if not limited_scan:
            cursor = connection.execute("DELETE FROM media WHERE last_seen_scan <> ?", (scan_id,))
            removed = max(0, cursor.rowcount)

        _set_meta(connection, "last_scan_at", scan_id)
        _set_meta(connection, "source", configured_source_summary(args))
        _set_meta(connection, "last_scan_count", str(len(items)))
        _set_meta(connection, "last_removed_count", str(removed))
        _set_meta(connection, "partial_scan", "1" if limited_scan else "0")
        api_requests = client.request_count if client else 0
        if client is not None:
            add_omdb_usage(
                connection,
                omdb_key,
                api_requests,
                limit_reached=client.limit_reached,
            )
        _set_meta(connection, "last_omdb_requests", str(api_requests))
        _set_meta(connection, "last_reused_metadata", str(reused_metadata))
        _set_meta(connection, "last_omdb_error", omdb_error)
        connection.commit()
        return len(items), removed, api_requests, reused_metadata
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()
        if client:
            client.save_cache()


def correct_database_item(
    args: argparse.Namespace,
    media_id: int,
    imdb_reference: str,
    *,
    omdb_key: str,
) -> str:
    if not omdb_key:
        raise CatalogError("OMDB_API_KEY ist nicht gesetzt; Korrektur ist daher nicht möglich.")
    imdb_id = parse_imdb_reference(imdb_reference)
    client = OmdbClient(omdb_key, args.cache, args.cache_tage)
    try:
        metadata = lookup_exact_imdb(client, imdb_id)
    finally:
        client.save_cache()
        usage_connection = open_database(args.db)
        try:
            add_omdb_usage(
                usage_connection,
                omdb_key,
                client.request_count,
                limit_reached=client.limit_reached,
            )
            usage_connection.commit()
        finally:
            usage_connection.close()

    connection = open_database(args.db)
    try:
        row = connection.execute("SELECT * FROM media WHERE id = ?", (media_id,)).fetchone()
        if row is None:
            raise CatalogError("Der Katalogeintrag existiert nicht mehr.")
        rating = str(metadata.get("imdbRating") or "–")
        if rating == "N/A":
            rating = "–"
        poster = str(metadata.get("Poster") or "")
        if poster == "N/A":
            poster = ""
        plot = str(metadata.get("Plot") or "Keine Kurzbeschreibung vorhanden.")
        if plot == "N/A":
            plot = "Keine Kurzbeschreibung vorhanden."
        auto_kids = _auto_kids_from_metadata(metadata)
        connection.execute(
            """
            UPDATE media SET
                manual_imdb_id=?, imdb_id=?, title=?, year=?, imdb_rating=?, plot=?,
                poster=?, genre=?, director=?, actors=?, runtime=?, age_rating=?, status='manuell zugeordnet',
                is_kids=CASE WHEN kids_manual=1 THEN is_kids ELSE ? END, updated_at=?
            WHERE id=?
            """,
            (
                imdb_id,
                imdb_id,
                str(metadata.get("Title") or row["source_title"]),
                str(metadata.get("Year") or row["source_year"] or "–"),
                rating,
                plot,
                poster,
                "" if metadata.get("Genre") == "N/A" else str(metadata.get("Genre") or ""),
                "" if metadata.get("Director") == "N/A" else str(metadata.get("Director") or ""),
                "" if metadata.get("Actors") == "N/A" else str(metadata.get("Actors") or ""),
                "" if metadata.get("Runtime") == "N/A" else str(metadata.get("Runtime") or ""),
                "" if metadata.get("Rated") == "N/A" else str(metadata.get("Rated") or ""),
                auto_kids,
                _utc_now(),
                media_id,
            ),
        )
        connection.commit()
        # Eine manuelle Neuzuordnung muss auch das Cover sofort wechseln.
        # Alte/negative Browser- oder Dateicaches dürfen dabei nicht weiterleben.
        invalidate_poster_cache(media_id, imdb_id)
        return imdb_id
    finally:
        connection.close()


def set_kids_flag(args: argparse.Namespace, media_id: int, is_kids: bool) -> None:
    """Kinder-Kennzeichnung dauerhaft manuell setzen oder entfernen."""
    connection = open_database(args.db)
    try:
        cursor = connection.execute(
            "UPDATE media SET is_kids=?, kids_manual=1, updated_at=? WHERE id=?",
            (1 if is_kids else 0, _utc_now(), media_id),
        )
        if cursor.rowcount == 0:
            raise CatalogError("Der Katalogeintrag existiert nicht mehr.")
        connection.commit()
    finally:
        connection.close()


def reset_database_item_mapping(args: argparse.Namespace, media_id: int) -> None:
    connection = open_database(args.db)
    try:
        cursor = connection.execute(
            "UPDATE media SET manual_imdb_id='', updated_at=? WHERE id=?",
            (_utc_now(), media_id),
        )
        if cursor.rowcount == 0:
            raise CatalogError("Der Katalogeintrag existiert nicht mehr.")
        connection.commit()
    finally:
        connection.close()


def _safe_poster_url(value: str) -> str:
    try:
        parsed = urlsplit(value)
    except ValueError:
        return ""
    return value if parsed.scheme in {"http", "https"} and parsed.netloc else ""


def _poster_host_allowed(value: str) -> bool:
    """Nur bekannte IMDb/Amazon-Bildhosts für den lokalen Cover-Proxy zulassen."""
    safe = _safe_poster_url(value)
    if not safe:
        return False
    host = (urlsplit(safe).hostname or "").casefold().rstrip(".")
    allowed_suffixes = (
        "media-amazon.com",
        "ssl-images-amazon.com",
        "imdb.com",
    )
    return any(host == suffix or host.endswith("." + suffix) for suffix in allowed_suffixes)


def _poster_cache_directory() -> Path:
    return application_directory() / "cover_cache"


def invalidate_poster_cache(media_id: int, imdb_id: str = "") -> None:
    """Veraltete lokale Cover-Dateien nach einer Zuordnungsänderung entfernen."""
    cache_dir = _poster_cache_directory()
    names = {f"media-{int(media_id)}.img"}
    normalized_id = str(imdb_id or "").strip().casefold()
    if IMDB_ID_RE.fullmatch(normalized_id):
        names.add(f"{normalized_id}.img")
    for name in names:
        try:
            (cache_dir / name).unlink(missing_ok=True)
        except OSError:
            pass


def _poster_version_token(row: sqlite3.Row) -> str:
    """Kurzer Cache-Buster für Browser-Cover, der sich bei Metadatenänderungen ändert."""
    raw = "|".join(
        (
            str(row["imdb_id"] or ""),
            str(row["poster"] or ""),
            str(row["updated_at"] or ""),
        )
    )
    return hashlib.sha256(raw.encode("utf-8", errors="replace")).hexdigest()[:16]


def _detect_image_content_type(data: bytes, declared: str = "") -> str:
    declared = declared.split(";", 1)[0].strip().casefold()
    if data.startswith(b"\xff\xd8\xff"):
        return "image/jpeg"
    if data.startswith(b"\x89PNG\r\n\x1a\n"):
        return "image/png"
    if data[:6] in {b"GIF87a", b"GIF89a"}:
        return "image/gif"
    if len(data) >= 12 and data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return "image/webp"
    if declared.startswith("image/"):
        return declared
    return "application/octet-stream"


def _download_poster_image(url: str, *, timeout: int = 12) -> tuple[bytes, str]:
    if not _poster_host_allowed(url):
        raise CatalogError("Nicht erlaubte Cover-Adresse.")
    request = Request(
        url,
        headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) MedienKatalog/4.6",
            "Accept": "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8",
            "Referer": "https://www.imdb.com/",
        },
    )
    try:
        with urlopen(request, timeout=timeout) as response:
            final_url = response.geturl()
            if not _poster_host_allowed(final_url):
                raise CatalogError("Cover wurde auf eine nicht erlaubte Adresse umgeleitet.")
            declared = str(response.headers.get("Content-Type") or "")
            data = response.read(8 * 1024 * 1024 + 1)
    except (HTTPError, URLError, TimeoutError, socket.timeout) as exc:
        raise CatalogError(f"Cover konnte nicht geladen werden ({type(exc).__name__}).") from exc
    if not data or len(data) > 8 * 1024 * 1024:
        raise CatalogError("Cover ist leer oder zu groß.")
    content_type = _detect_image_content_type(data, declared)
    if not content_type.startswith("image/"):
        raise CatalogError("Die Cover-Adresse lieferte kein Bild.")
    return data, content_type


def poster_for_database_item(args: argparse.Namespace, media_id: int) -> tuple[bytes, str]:
    """Cover lokal ausliefern, bei Bedarf IMDb als Fallback verwenden und cachen."""
    connection = open_database(args.db)
    try:
        row = connection.execute(
            "SELECT id, title, imdb_id, poster FROM media WHERE id=?",
            (media_id,),
        ).fetchone()
    finally:
        connection.close()
    if row is None:
        raise CatalogError("Der Katalogeintrag existiert nicht mehr.")

    imdb_id = str(row["imdb_id"] or "").strip().casefold()
    stored_url = _safe_poster_url(str(row["poster"] or "").strip())
    cache_key = imdb_id if IMDB_ID_RE.fullmatch(imdb_id) else f"media-{media_id}"
    cache_dir = _poster_cache_directory()
    cache_file = cache_dir / f"{cache_key}.img"
    if cache_file.is_file():
        try:
            data = cache_file.read_bytes()
            content_type = _detect_image_content_type(data)
            if data and content_type.startswith("image/"):
                return data, content_type
        except OSError:
            pass

    candidates: list[str] = []
    if stored_url and _poster_host_allowed(stored_url):
        candidates.append(stored_url)

    # OMDb kann einen gültigen Titel liefern, obwohl sein Poster-Link fehlt oder
    # nicht mehr direkt abrufbar ist. In diesem Fall versuchen wir das Cover
    # über IMDbs Suggestion-Dienst nachzuladen, ohne OMDb-Kontingent zu verbrauchen.
    if IMDB_ID_RE.fullmatch(imdb_id):
        for query in (imdb_id, str(row["title"] or "").strip()):
            if not query:
                continue
            try:
                results = search_imdb_titles(query, limit=10, timeout=8)
            except CatalogError:
                continue
            for result in results:
                if str(result.get("imdb_id", "")).casefold() != imdb_id:
                    continue
                image = _safe_poster_url(str(result.get("image") or ""))
                if image and _poster_host_allowed(image) and image not in candidates:
                    candidates.append(image)
                break
            if len(candidates) > (1 if stored_url else 0):
                break

    last_error: CatalogError | None = None
    for url in candidates:
        try:
            data, content_type = _download_poster_image(url)
            try:
                cache_dir.mkdir(parents=True, exist_ok=True)
                temporary = cache_file.with_suffix(".tmp")
                temporary.write_bytes(data)
                os.replace(temporary, cache_file)
            except OSError:
                pass
            return data, content_type
        except CatalogError as exc:
            last_error = exc

    raise last_error or CatalogError("Für diesen Titel ist kein abrufbares Cover verfügbar.")


def _parse_imdb_suggestion_data(data: dict[str, Any], *, limit: int = 10) -> list[dict[str, str]]:
    """IMDb-Suggestion-Antwort auf reine Titel mit tt-ID reduzieren."""
    results: list[dict[str, str]] = []
    raw_results = data.get("d", [])
    if not isinstance(raw_results, list):
        return results

    for entry in raw_results:
        if not isinstance(entry, dict):
            continue
        imdb_id = str(entry.get("id") or "").strip()
        if not IMDB_ID_RE.fullmatch(imdb_id):
            continue
        title = str(entry.get("l") or "").strip()
        if not title:
            continue

        year_raw = entry.get("y")
        year = str(year_raw).strip() if year_raw not in (None, "") else ""
        kind = str(entry.get("q") or entry.get("qid") or "").strip()
        subtitle = str(entry.get("s") or "").strip()

        image = ""
        image_data = entry.get("i")
        if isinstance(image_data, dict):
            image = str(image_data.get("imageUrl") or "").strip()
        elif isinstance(image_data, list) and image_data:
            image = str(image_data[0] or "").strip()
        image = _safe_poster_url(image)

        results.append({
            "imdb_id": imdb_id,
            "title": title,
            "year": year,
            "kind": kind,
            "subtitle": subtitle,
            "image": image,
        })
        if len(results) >= max(1, limit):
            break
    return results


def search_imdb_titles(query: str, *, limit: int = 10, timeout: int = 12) -> list[dict[str, str]]:
    """Bis zu ``limit`` Titel direkt aus IMDbs Suchvorschlägen laden.

    Dieser Aufruf verwendet keinen OMDb-API-Key und zählt daher nicht gegen das
    OMDb-Tageslimit. IMDb liefert bei manchen Suchbegriffen weniger als zehn
    Vorschläge; dann wird die tatsächlich verfügbare Anzahl zurückgegeben.
    """
    query = " ".join(str(query).split()).strip()[:200]
    if not query:
        return []

    url = IMDB_SUGGEST_ENDPOINT + quote(query.casefold(), safe="") + ".json?includeVideos=0"
    request = Request(
        url,
        headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) MedienKatalog/4.6",
            "Accept": "application/json,text/plain,*/*",
        },
    )
    try:
        with urlopen(request, timeout=timeout) as response:
            body = response.read().decode("utf-8")
        data = json.loads(body)
    except (HTTPError, URLError, TimeoutError, socket.timeout, json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise CatalogError(f"IMDb-Suche ist momentan nicht erreichbar ({type(exc).__name__}).") from exc

    if not isinstance(data, dict):
        raise CatalogError("IMDb-Suche hat eine unerwartete Antwort geliefert.")
    return _parse_imdb_suggestion_data(data, limit=limit)


def imdb_search_for_database_item(args: argparse.Namespace, media_id: int) -> tuple[str, list[dict[str, str]]]:
    """Lokalen Quelltitel lesen und damit IMDb durchsuchen."""
    connection = open_database(args.db)
    try:
        row = connection.execute(
            "SELECT source_title, title FROM media WHERE id = ?",
            (media_id,),
        ).fetchone()
    finally:
        connection.close()
    if row is None:
        raise CatalogError("Der Katalogeintrag existiert nicht mehr.")

    query = str(row["source_title"] or row["title"] or "").strip()
    if not query:
        raise CatalogError("Für diesen Eintrag ist kein suchbarer Titel gespeichert.")
    return query, search_imdb_titles(query, limit=10)


def _media_explorer_target_from_row(row: sqlite3.Row) -> tuple[str, bool]:
    """Bestimmt das konkrete Explorer-Ziel eines Katalogeintrags.

    Rückgabe ist ``(ziel, datei_markieren)``. Serien öffnen immer ihren
    Hauptordner direkt unterhalb von ``Serien``. Filme öffnen den konkreten
    Ordner, in dem der Titel liegt; bei BDMV/VIDEO_TS-artigen Unterstrukturen
    wird bis zum eigentlichen Filmordner hochgegangen. Liegt eine Filmdatei
    direkt im Ordner ``Filme``, existiert kein eigener Titelordner – dann wird
    die Datei im Explorer gezielt markiert, statt nur den allgemeinen
    Filme-Ordner zu öffnen.
    """
    try:
        paths = json.loads(row["paths_json"])
    except (json.JSONDecodeError, TypeError):
        paths = []
    if not isinstance(paths, list) or not paths:
        raise CatalogError("Für diesen Titel ist kein Dateipfad gespeichert.")

    first_path = str(paths[0]).strip()
    if not first_path:
        raise CatalogError("Für diesen Titel ist kein gültiger Dateipfad gespeichert.")

    media_path = PureWindowsPath(first_path)
    parts = media_path.parts
    kind = str(row["kind"])

    if kind == "series":
        # Die Serienidentität ist definitionsgemäß der erste Ordner direkt
        # unterhalb von \Serien. Genau diesen Ordner öffnen.
        for index, part in enumerate(parts[:-1]):
            if normalized_words(part) == SERIES_ROOT_NAME and index + 1 < len(parts) - 1:
                return str(PureWindowsPath(*parts[: index + 2])), False
        return str(media_path.parent), False

    # Filme: Normalfall ist der direkte Elternordner der Mediendatei. Bei
    # technischen Disc-Unterordnern (BDMV, STREAM, VIDEO_TS usw.) laufen wir
    # hoch, bis der echte Titelordner erreicht ist.
    folder = media_path.parent
    while folder.name:
        normalized = normalized_words(folder.name)
        if normalized == MOVIES_ROOT_NAME:
            # Die Datei liegt direkt unter \Filme. Es gibt keinen eigenen
            # Titelordner, daher die konkrete Datei im Explorer markieren.
            return first_path, True
        if normalized in GENERIC_DIRECTORY_NAMES or bool(SEASON_DIRECTORY_RE.fullmatch(folder.name)):
            parent = folder.parent
            if parent == folder:
                break
            folder = parent
            continue
        return str(folder), False

    return str(media_path.parent), False


def _media_folder_from_row(row: sqlite3.Row) -> str:
    """Kompatibilitätshelfer für Tests/ältere Aufrufer."""
    target, select_file = _media_explorer_target_from_row(row)
    return str(PureWindowsPath(target).parent) if select_file else target


def _media_file_from_row(row: sqlite3.Row) -> str:
    """Liefert eine konkrete Mediendatei zum Starten.

    Die gespeicherten Pfade sind bereits die beim Scan gefundenen Mediendateien.
    Bei Titeln mit mehreren Dateien wird der lexikografisch erste Pfad verwendet;
    bei Serien ist das damit in der Regel die erste erkannte Episode.
    """
    try:
        paths = json.loads(row["paths_json"])
    except (json.JSONDecodeError, TypeError):
        paths = []
    if not isinstance(paths, list):
        paths = []

    candidates = [str(path).strip() for path in paths if str(path).strip()]
    if not candidates:
        raise CatalogError("Für diesen Titel ist keine Mediendatei gespeichert.")

    def natural_key(value: str) -> tuple[Any, ...]:
        parts = re.split(r"(\d+)", value.casefold())
        return tuple(int(part) if part.isdigit() else part for part in parts)

    # Bei Filmen bevorzugen wir eine Datei, deren Dateiname exakt dem
    # Katalogtitel entspricht. Das ist z. B. bei "Alien.mkv" sinnvoller als
    # versehentlich "Alien CD2.mkv" zuerst zu starten. Danach folgt eine
    # natürliche Sortierung, die bei Serien S01E02 vor S01E10 hält.
    title_words = normalized_words(str(row["title"])) if "title" in row.keys() else ""
    kind = str(row["kind"]) if "kind" in row.keys() else ""

    def candidate_key(value: str) -> tuple[Any, ...]:
        stem_words = normalized_words(PureWindowsPath(value).stem)
        exact_movie = 0 if kind == "movie" and title_words and stem_words == title_words else 1
        return (exact_movie, natural_key(value))

    candidates.sort(key=candidate_key)
    return candidates[0]



def media_server_status(source: str, *, timeout: float = 1.2) -> tuple[bool, str]:
    """Prüft schnell, ob der Medien-/SMB-Server erreichbar ist.

    Bei UNC- und smb://-Quellen wird TCP/445 (bzw. der angegebene SMB-Port)
    getestet. Das vermeidet lange Hänger, die ein direkter Zugriff auf eine
    ausgeschaltete UNC-Freigabe verursachen kann. Bei lokalen Quellen wird
    geprüft, ob der Ordner existiert.
    """
    source = str(source or "").strip()
    if not source:
        return False, ""

    host = ""
    port = 445
    if source.casefold().startswith("smb://"):
        try:
            parsed = urlsplit(source)
            host = parsed.hostname or ""
            port = parsed.port or 445
        except ValueError:
            return False, ""
    elif source.startswith("\\\\"):
        match = re.match(r"^\\\\([^\\/]+)[\\/]", source)
        if match:
            host = match.group(1).strip()
    else:
        try:
            return Path(source).expanduser().is_dir(), source
        except OSError:
            return False, source

    if not host:
        return False, source
    try:
        with socket.create_connection((host, port), timeout=max(0.2, float(timeout))):
            return True, host
    except (OSError, TimeoutError):
        return False, host


def background_image_path() -> Path | None:
    """Liefert background.png/background.jpg neben dem Programm, falls vorhanden."""
    base = application_directory()
    try:
        files = [path for path in base.iterdir() if path.is_file()]
    except OSError:
        return None
    priority = {".png": 0, ".jpg": 1, ".jpeg": 2}
    candidates = [
        path for path in files
        if path.stem.casefold() == "background" and path.suffix.casefold() in priority
    ]
    if not candidates:
        return None
    candidates.sort(key=lambda path: (priority.get(path.suffix.casefold(), 99), path.name.casefold()))
    return candidates[0]


def _background_version_token(path: Path) -> str:
    try:
        stat = path.stat()
        raw = f"{path.name}|{stat.st_mtime_ns}|{stat.st_size}"
    except OSError:
        raw = path.name
    return hashlib.sha1(raw.encode("utf-8", errors="replace")).hexdigest()[:12]


def _register_pdf_fonts() -> tuple[str, str]:
    """Registriert nach Möglichkeit Arial/DejaVu für robuste Unicode-PDFs."""
    try:
        from reportlab.pdfbase import pdfmetrics
        from reportlab.pdfbase.ttfonts import TTFont
    except ImportError as exc:
        raise CatalogError(
            "Für den PDF-Export fehlt das Paket 'reportlab'. Installiere es einmalig mit: "
            "python -m pip install reportlab"
        ) from exc

    regular_name = "MedienKatalogSans"
    bold_name = "MedienKatalogSansBold"
    registered = set(pdfmetrics.getRegisteredFontNames())
    if regular_name in registered and bold_name in registered:
        return regular_name, bold_name

    windows = Path(os.environ.get("WINDIR", r"C:\Windows")) / "Fonts"
    candidates = [
        (windows / "arial.ttf", windows / "arialbd.ttf"),
        (Path("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"), Path("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf")),
        (Path("/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf"), Path("/usr/share/fonts/truetype/liberation2/LiberationSans-Bold.ttf")),
    ]
    for regular_path, bold_path in candidates:
        if regular_path.is_file() and bold_path.is_file():
            try:
                if regular_name not in registered:
                    pdfmetrics.registerFont(TTFont(regular_name, str(regular_path)))
                if bold_name not in registered:
                    pdfmetrics.registerFont(TTFont(bold_name, str(bold_path)))
                return regular_name, bold_name
            except Exception:
                continue
    return "Helvetica", "Helvetica-Bold"


def generate_catalog_pdf(
    args: argparse.Namespace,
    media_ids: Sequence[int],
    *,
    language: str = "de",
) -> bytes:
    """Erzeugt eine visuelle PDF-Liste der ausgewählten Filme/Serien.

    Jeder Titel wird als kompakter, möglichst ungeteilter Block ausgegeben:
    Cover links, IMDb-Bewertung als Grafik und die wichtigsten OMDb-Daten rechts.
    Die technische IMDb-ID (tt...) wird bewusst nicht gedruckt.
    """
    try:
        from io import BytesIO
        from reportlab.lib import colors
        from reportlab.lib.enums import TA_CENTER
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
        from reportlab.lib.units import mm
        from reportlab.lib.utils import ImageReader
        from reportlab.platypus import (
            Flowable,
            Image,
            KeepInFrame,
            KeepTogether,
            Paragraph,
            SimpleDocTemplate,
            Spacer,
            Table,
            TableStyle,
        )
    except ImportError as exc:
        raise CatalogError(
            "Für den PDF-Export fehlt das Paket 'reportlab'. Installiere es einmalig mit: "
            "python -m pip install reportlab"
        ) from exc

    ordered_ids: list[int] = []
    seen: set[int] = set()
    for value in media_ids:
        try:
            media_id = int(value)
        except (TypeError, ValueError):
            continue
        if media_id > 0 and media_id not in seen:
            seen.add(media_id)
            ordered_ids.append(media_id)
    if not ordered_ids:
        raise CatalogError("Keine Titel für den PDF-Export ausgewählt.")
    if len(ordered_ids) > 10000:
        raise CatalogError("Für einen einzelnen PDF-Export sind höchstens 10.000 Titel möglich.")

    connection = open_database(args.db)
    try:
        placeholders = ",".join("?" for _ in ordered_ids)
        found = connection.execute(
            f"SELECT * FROM media WHERE id IN ({placeholders})",
            tuple(ordered_ids),
        ).fetchall()
    finally:
        connection.close()
    by_id = {int(row["id"]): row for row in found}
    rows = [by_id[media_id] for media_id in ordered_ids if media_id in by_id]
    if not rows:
        raise CatalogError("Die ausgewählten Titel existieren nicht mehr in der Datenbank.")

    lang = "en" if language == "en" else "de"
    text = {
        "de": {
            "title": "Medienkatalog - IMDb-Liste",
            "created": "Erstellt",
            "count": "Titel",
            "movies": "Filme",
            "series": "Serien",
            "movie": "Film",
            "serie": "Serie",
            "rating": "IMDb",
            "genre": "Genre",
            "runtime": "Laufzeit",
            "director": "Regie",
            "cast": "Besetzung",
            "age_rating": "FSK/Rating",
            "plot": "Beschreibung",
            "no_cover": "Kein Cover",
            "unrated": "ohne Bewertung",
            "page": "Seite",
        },
        "en": {
            "title": "Media Library - IMDb List",
            "created": "Created",
            "count": "titles",
            "movies": "movies",
            "series": "series",
            "movie": "Movie",
            "serie": "Series",
            "rating": "IMDb",
            "genre": "Genre",
            "runtime": "Runtime",
            "director": "Director",
            "cast": "Cast",
            "age_rating": "Age rating",
            "plot": "Plot",
            "no_cover": "No cover",
            "unrated": "not rated",
            "page": "Page",
        },
    }[lang]

    regular_font, bold_font = _register_pdf_fonts()
    buffer = BytesIO()
    doc = SimpleDocTemplate(
        buffer,
        pagesize=A4,
        rightMargin=13 * mm,
        leftMargin=13 * mm,
        topMargin=15 * mm,
        bottomMargin=15 * mm,
        title=text["title"],
        author="Medienkatalog",
    )
    base = getSampleStyleSheet()
    title_style = ParagraphStyle(
        "CatalogTitle",
        parent=base["Title"],
        fontName=bold_font,
        fontSize=18,
        leading=21,
        alignment=TA_CENTER,
        textColor=colors.HexColor("#1D2733"),
        spaceAfter=4 * mm,
    )
    summary_style = ParagraphStyle(
        "CatalogSummary",
        parent=base["Normal"],
        fontName=regular_font,
        fontSize=8.7,
        leading=11,
        alignment=TA_CENTER,
        textColor=colors.HexColor("#4A5563"),
        spaceAfter=5 * mm,
    )
    heading_style = ParagraphStyle(
        "EntryTitle",
        parent=base["Heading2"],
        fontName=bold_font,
        fontSize=11.4,
        leading=13.6,
        textColor=colors.HexColor("#17202A"),
        spaceAfter=1.3 * mm,
    )
    info_style = ParagraphStyle(
        "EntryInfo",
        parent=base["Normal"],
        fontName=regular_font,
        fontSize=7.8,
        leading=9.8,
        textColor=colors.HexColor("#303A46"),
        spaceAfter=0.8 * mm,
    )
    plot_style = ParagraphStyle(
        "EntryPlot",
        parent=info_style,
        fontSize=7.5,
        leading=9.5,
        textColor=colors.HexColor("#20262D"),
        spaceBefore=0.5 * mm,
        spaceAfter=0,
    )
    placeholder_style = ParagraphStyle(
        "CoverPlaceholder",
        parent=base["Normal"],
        fontName=regular_font,
        fontSize=8,
        leading=10,
        alignment=TA_CENTER,
        textColor=colors.HexColor("#7B8490"),
    )

    def esc(value: Any) -> str:
        return html.escape(str(value or ""), quote=False).replace("\n", "<br/>")

    def shortened(value: str, maximum: int) -> str:
        value = " ".join(str(value or "").split())
        if len(value) <= maximum:
            return value
        cut = value[: max(0, maximum - 1)].rsplit(" ", 1)[0].rstrip(" ,.;:-")
        return (cut or value[: max(0, maximum - 1)]).rstrip() + "…"

    class RatingGraphic(Flowable):
        """Kompakter IMDb-Bewertungsbalken von 0 bis 10."""
        def __init__(self, rating_value: str):
            super().__init__()
            self.width = 58 * mm
            self.height = 6.6 * mm
            try:
                parsed = float(str(rating_value).replace(",", "."))
                self.rating = max(0.0, min(10.0, parsed))
            except (TypeError, ValueError):
                self.rating = None

        def draw(self) -> None:
            c = self.canv
            x = 0
            y = 0.8 * mm
            h = 4.8 * mm
            w = 42 * mm
            c.setFillColor(colors.HexColor("#E4E8EC"))
            c.roundRect(x, y, w, h, 1.6 * mm, stroke=0, fill=1)
            if self.rating is not None:
                fill_w = w * (self.rating / 10.0)
                if fill_w > 0:
                    c.setFillColor(colors.HexColor("#F5C451"))
                    c.roundRect(x, y, fill_w, h, min(1.6 * mm, fill_w / 2), stroke=0, fill=1)
                label = f"IMDb {self.rating:.1f} / 10"
            else:
                label = f"IMDb - {text['unrated']}"
            c.setFillColor(colors.HexColor("#1F2832"))
            c.setFont(bold_font, 7.4)
            c.drawString(1.8 * mm, y + 1.35 * mm, label)

    def cover_flowable(row: sqlite3.Row) -> Any:
        max_w = 30 * mm
        max_h = 45 * mm
        try:
            data, _content_type = poster_for_database_item(args, int(row["id"]))
            stream = BytesIO(data)
            reader = ImageReader(stream)
            iw, ih = reader.getSize()
            if iw <= 0 or ih <= 0:
                raise ValueError("invalid cover dimensions")
            scale = min(max_w / float(iw), max_h / float(ih))
            width = max(1, float(iw) * scale)
            height = max(1, float(ih) * scale)
            stream.seek(0)
            image = Image(stream, width=width, height=height)
            image.hAlign = "CENTER"
            return image
        except Exception:
            placeholder = Table(
                [[Paragraph(esc(text["no_cover"]), placeholder_style)]],
                colWidths=[max_w],
                rowHeights=[max_h],
            )
            placeholder.setStyle(TableStyle([
                ("BACKGROUND", (0, 0), (-1, -1), colors.HexColor("#F1F3F5")),
                ("BOX", (0, 0), (-1, -1), 0.5, colors.HexColor("#D3D8DE")),
                ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                ("LEFTPADDING", (0, 0), (-1, -1), 2 * mm),
                ("RIGHTPADDING", (0, 0), (-1, -1), 2 * mm),
            ]))
            return placeholder

    movie_count = sum(1 for row in rows if str(row["kind"]) == "movie")
    series_count = len(rows) - movie_count
    created = datetime.now().astimezone().strftime("%d.%m.%Y %H:%M")
    story: list[Any] = [
        Paragraph(text["title"], title_style),
        Paragraph(
            f'{esc(text["created"])}: {esc(created)} &nbsp;&nbsp;·&nbsp;&nbsp; '
            f'{len(rows)} {esc(text["count"])} &nbsp;&nbsp;·&nbsp;&nbsp; '
            f'{movie_count} {esc(text["movies"])} &nbsp;&nbsp;·&nbsp;&nbsp; '
            f'{series_count} {esc(text["series"])}',
            summary_style,
        ),
    ]

    entry_height = 51 * mm
    cover_col = 34 * mm
    right_col = doc.width - cover_col

    for index, row in enumerate(rows, start=1):
        kind_label = text["movie"] if str(row["kind"]) == "movie" else text["serie"]
        year = str(row["year"] or "").strip()
        year_suffix = f" ({esc(year)})" if year and year != "–" else ""
        right_story: list[Any] = [
            Paragraph(f"{index}. [{esc(kind_label)}] {esc(row['title'])}{year_suffix}", heading_style),
            RatingGraphic(str(row["imdb_rating"] or "")),
            Spacer(1, 0.6 * mm),
        ]

        facts: list[str] = []
        genre = str(row["genre"] or "").strip()
        if genre:
            facts.append(f'<b>{esc(text["genre"])}:</b> {esc(shortened(genre, 120))}')
        runtime = str(row["runtime"] or "").strip()
        if runtime:
            facts.append(f'<b>{esc(text["runtime"])}:</b> {esc(runtime)}')
        age_rating = str(row["age_rating"] or "").strip()
        facts.append(f'<b>{esc(text["age_rating"])}:</b> {esc(age_rating or "–")}')
        if facts:
            right_story.append(Paragraph(" &nbsp;·&nbsp; ".join(facts), info_style))

        director = str(row["director"] or "").strip()
        if director:
            right_story.append(Paragraph(f'<b>{esc(text["director"])}:</b> {esc(shortened(director, 150))}', info_style))
        actors = str(row["actors"] or "").strip()
        if actors:
            right_story.append(Paragraph(f'<b>{esc(text["cast"])}:</b> {esc(shortened(actors, 260))}', info_style))
        plot = str(row["plot"] or "").strip()
        if plot:
            right_story.append(Paragraph(f'<b>{esc(text["plot"])}:</b> {esc(shortened(plot, 620))}', plot_style))

        fitted_content = KeepInFrame(
            right_col - 6 * mm,
            entry_height - 5 * mm,
            right_story,
            mode="shrink",
            mergeSpace=True,
            hAlign="LEFT",
            vAlign="TOP",
        )
        entry = Table(
            [[cover_flowable(row), fitted_content]],
            colWidths=[cover_col, right_col],
            rowHeights=[entry_height],
            repeatRows=0,
            splitByRow=1,
        )
        entry.setStyle(TableStyle([
            ("VALIGN", (0, 0), (-1, -1), "TOP"),
            ("LEFTPADDING", (0, 0), (0, 0), 1.5 * mm),
            ("RIGHTPADDING", (0, 0), (0, 0), 2.5 * mm),
            ("TOPPADDING", (0, 0), (-1, -1), 2.2 * mm),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 2.2 * mm),
            ("LEFTPADDING", (1, 0), (1, 0), 2.5 * mm),
            ("RIGHTPADDING", (1, 0), (1, 0), 2.5 * mm),
            ("LINEBELOW", (0, 0), (-1, -1), 0.55, colors.HexColor("#CBD2D9")),
        ]))
        # Eine Tabellenzeile mit fester Höhe wird von ReportLab nicht zwischen
        # zwei Seiten geteilt. KeepTogether sorgt zusätzlich dafür, dass der
        # kleine Abstand darunter mitwandert.
        story.append(KeepTogether([entry, Spacer(1, 1.6 * mm)]))

    def footer(canvas: Any, document: Any) -> None:
        canvas.saveState()
        canvas.setFont(regular_font, 8)
        canvas.setFillColor(colors.HexColor("#68717D"))
        page_text = f'{text["page"]} {document.page}'
        canvas.drawCentredString(A4[0] / 2, 7 * mm, page_text)
        canvas.restoreState()

    doc.build(story, onFirstPage=footer, onLaterPages=footer)
    return buffer.getvalue()

def _configured_title_folder(row: sqlite3.Row, configured_root: str) -> str:
    """Liefert den konkreten Titelordner unterhalb eines konfigurierten Medien-Roots.

    Funktioniert für Windows-/UNC-Pfade und für normale POSIX-Pfade. Für smb://
    wird der konfigurierte Root zunächst in den entsprechenden UNC-Pfad umgesetzt,
    da smbclient die gefundenen Dateipfade ebenfalls als UNC speichert.
    """
    try:
        paths = json.loads(row["paths_json"])
    except (json.JSONDecodeError, TypeError):
        paths = []
    if not isinstance(paths, list) or not paths:
        raise CatalogError("Für diesen Titel ist kein Dateipfad gespeichert.")

    first_path = str(paths[0]).strip()
    if not first_path:
        raise CatalogError("Für diesen Titel ist kein gültiger Dateipfad gespeichert.")

    root = str(configured_root or "").strip()
    if root.casefold().startswith("smb://"):
        try:
            _host, _port, root = parse_smb_source(root)
        except CatalogError:
            root = ""

    use_windows = bool(re.match(r"^[A-Za-z]:[\\/]", first_path)) or first_path.startswith("\\\\") or "\\" in first_path
    path_cls = PureWindowsPath if use_windows else Path
    media_path = path_cls(first_path)

    if root:
        root_obj = path_cls(root)
        try:
            relative = media_path.relative_to(root_obj)
            if len(relative.parts) >= 2:
                return str(root_obj / relative.parts[0])
        except (ValueError, OSError):
            pass

    # Fallback: Bei Serien ist der direkte Elternordner einer Episode wenigstens
    # besser als ein generischer Root. Bei Staffelordnern eine Ebene hochgehen.
    parent = media_path.parent
    if bool(SEASON_DIRECTORY_RE.fullmatch(parent.name)):
        parent = parent.parent
    return str(parent)


def _open_with_desktop_default(target: str) -> None:
    """Öffnet Datei/Ordner mit der Desktop-Standardanwendung des Betriebssystems."""
    if os.name == "nt":
        os.startfile(target)  # type: ignore[attr-defined]
        return
    if sys.platform == "darwin":
        subprocess.Popen(["open", target], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return
    # Freedesktop-Standard unter Desktop-Linux (GNOME, KDE, XFCE, Cinnamon ...).
    subprocess.Popen(["xdg-open", target], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def start_media(args: argparse.Namespace, media_id: int) -> str:
    """Startet Filme bzw. öffnet bei Serien den Titelordner plattformneutral.

    Windows verwendet ``os.startfile``. Desktop-Linux verwendet ``xdg-open``
    und damit die dort konfigurierte Standardanwendung bzw. den Dateimanager.
    macOS wird über ``open`` ebenfalls unterstützt.
    """
    connection = open_database(args.db)
    try:
        row = connection.execute("SELECT * FROM media WHERE id=?", (media_id,)).fetchone()
    finally:
        connection.close()
    if row is None:
        raise CatalogError("Der ausgewählte Titel existiert nicht mehr in der Datenbank.")

    kind = str(row["kind"] or "")
    if kind == "series":
        target = _configured_title_folder(row, args.series_path)
        action_error = "Der Serienordner konnte nicht geöffnet werden"
    else:
        target = _media_file_from_row(row)
        action_error = "Der Film konnte nicht mit dem Standardplayer gestartet werden"

    try:
        _open_with_desktop_default(target)
    except (OSError, FileNotFoundError) as exc:
        raise CatalogError(f"{action_error}: {exc}") from exc
    return target


def _age_rating_badge_meta(value: str) -> tuple[str, str, str]:
    """Age-rating badge styling for the web UI.

    Returns (css_class, short_text, hint_text). The OMDb field Rated usually
    contains US ratings (e.g. PG-13, R) rather than German FSK values; the UI
    therefore presents them visually but does not attempt a lossy conversion.
    """
    raw = str(value or "").strip()
    if not raw or raw.upper() == "N/A":
        return ("unknown", "–", "Keine Angabe")

    upper = raw.upper()
    compact = upper.replace(" ", "").replace("_", "-")
    if compact in {"G", "TV-G", "TV-Y", "TV-Y7", "U", "0", "FSK0"}:
        return ("all", raw, "Für Kinder / allgemein freigegeben")
    if compact in {"PG", "TV-PG", "6", "FSK6", "7", "TV-Y7-FV"}:
        return ("kids", raw, "Mit elterlicher Begleitung / eher familienfreundlich")
    if compact in {"PG-13", "PG13", "12", "FSK12", "TV-14", "TV14"}:
        return ("teen", raw, "Ab Teenageralter empfohlen")
    if compact in {"R", "16", "FSK16", "MA15+", "M", "TV-MA", "TVMA"}:
        return ("mature", raw, "Für ältere Jugendliche/Erwachsene")
    if compact in {"NC-17", "NC17", "18", "FSK18", "AO", "X"}:
        return ("adult", raw, "Nur für Erwachsene")
    return ("neutral", raw, "Altersfreigabe laut Quelle")


def render_web_catalog(args: argparse.Namespace, *, notice: str = "", error: str = "") -> str:
    connection = open_database(args.db)
    try:
        backfilled_dates, missing_dates = _backfill_server_added_dates(connection)
        rows = connection.execute(
            "SELECT * FROM media ORDER BY CASE kind WHEN 'movie' THEN 0 ELSE 1 END, title COLLATE NOCASE, year"
        ).fetchall()
        meta = {row["key"]: row["value"] for row in connection.execute("SELECT key, value FROM catalog_meta")}
        meta["server_date_count"] = str(sum(1 for row in rows if str(row["server_added_at"] or "").strip()))
        meta["server_date_missing"] = str(missing_dates)
        meta["server_date_backfilled"] = str(backfilled_dates)
    finally:
        connection.close()

    server_online, server_host = configured_server_status(args)

    # Filterwerte aus allen gespeicherten OMDb-Daten sammeln. Ein Titel kann
    # mehrere Genres, Regisseure oder Schauspieler besitzen; OMDb trennt sie
    # üblicherweise mit Kommas.
    genre_names: set[str] = set()
    director_names: set[str] = set()
    actor_names: set[str] = set()
    for row in rows:
        genre_names.update(part.strip() for part in str(row["genre"] or "").split(",") if part.strip())
        director_names.update(part.strip() for part in str(row["director"] or "").split(",") if part.strip())
        actor_names.update(part.strip() for part in str(row["actors"] or "").split(",") if part.strip())

    genre_options = "".join(
        f'<option value="{html.escape(name.casefold(), quote=True)}">{html.escape(name)}</option>'
        for name in sorted(genre_names, key=str.casefold)
    )
    director_options = "".join(
        f'<option value="{html.escape(name.casefold(), quote=True)}">{html.escape(name)}</option>'
        for name in sorted(director_names, key=str.casefold)
    )
    actor_options = "".join(
        f'<option value="{html.escape(name.casefold(), quote=True)}">{html.escape(name)}</option>'
        for name in sorted(actor_names, key=str.casefold)
    )

    cards: list[str] = []
    for card_order, row in enumerate(rows):
        title = html.escape(str(row["title"]))
        source_title = html.escape(str(row["source_title"]))
        year = html.escape(str(row["year"]))
        rating = html.escape(str(row["imdb_rating"]))
        plot = html.escape(str(row["plot"] or ""))
        genre_raw = str(row["genre"] or "")
        director_raw = str(row["director"] or "")
        actors_raw = str(row["actors"] or "")
        genre = html.escape(genre_raw)
        director = html.escape(director_raw)
        actors = html.escape(actors_raw)
        genre_values = [part.strip().casefold() for part in genre_raw.split(",") if part.strip()]
        director_values = [part.strip().casefold() for part in director_raw.split(",") if part.strip()]
        actor_values = [part.strip().casefold() for part in actors_raw.split(",") if part.strip()]
        runtime = html.escape(str(row["runtime"] or ""))
        age_rating_raw = str(row["age_rating"] or "").strip()
        age_rating = html.escape(age_rating_raw)
        age_badge_class, age_badge_text, age_badge_hint = _age_rating_badge_meta(age_rating_raw)
        age_badge_text_html = html.escape(age_badge_text)
        age_badge_hint_html = html.escape(age_badge_hint)
        status_raw = str(row["status"] or "")
        imdb_id = str(row["imdb_id"] or "")
        manual = bool(row["manual_imdb_id"])
        is_kids = bool(row["is_kids"])
        kids_manual = bool(row["kids_manual"])
        unknown = not bool(imdb_id) or status_raw.casefold() not in {"gefunden", "manuell zugeordnet"}
        poster = _safe_poster_url(str(row["poster"] or ""))
        can_try_poster = bool(poster) or bool(IMDB_ID_RE.fullmatch(imdb_id))
        if can_try_poster:
            poster_version = _poster_version_token(row)
            poster_html = (
                '<div class="poster-slot">'
                f'<img class="poster" src="/poster/{int(row["id"])}?v={poster_version}" alt="Cover: {html.escape(str(row["title"]), quote=True)}" loading="lazy" '
                'onerror="this.style.display=\'none\';this.nextElementSibling.style.display=\'grid\';">'
                '<div class="poster placeholder poster-fallback" style="display:none" data-i18n="noCover">Kein Cover</div>'
                '</div>'
            )
        else:
            poster_html = '<div class="poster-slot"><div class="poster placeholder" data-i18n="noCover">Kein Cover</div></div>'
        imdb_html = (
            f'<a href="https://www.imdb.com/title/{html.escape(imdb_id, quote=True)}/" target="_blank" rel="noreferrer" data-i18n="openIMDb">IMDb öffnen</a>'
            if IMDB_ID_RE.fullmatch(imdb_id)
            else ""
        )
        # IMDb-Suche wird serverseitig über IMDbs eigenen Suggestion-Dienst
        # ausgeführt. So kann die Trefferliste direkt in der Karte erscheinen,
        # ohne OMDb-Kontingent zu verbrauchen.
        imdb_search_query = str(row["source_title"] or row["title"] or "").strip()
        imdb_search_html = (
            '<div class="imdb-search-tools">'
            f'<button class="imdb-search-button" type="button" onclick="searchIMDbResults({int(row["id"])}, this)" '
            'data-i18n="searchIMDb">Auf IMDb suchen</button>'
            '<span class="manual-note" data-i18n="imdbSearchHint">Bis zu 10 IMDb-Treffer anzeigen und direkt zuweisen.</span>'
            '</div>'
            f'<div class="imdb-results" id="imdb-results-{int(row["id"])}" aria-live="polite"></div>'
            if imdb_search_query
            else ""
        )
        try:
            paths = json.loads(row["paths_json"])
        except (json.JSONDecodeError, TypeError):
            paths = []
        paths_html = "".join(f"<li>{html.escape(str(path))}</li>" for path in paths)
        server_added_raw = str(row["server_added_at"] or "")
        server_added_ts = 0
        server_added_display = ""
        if server_added_raw:
            try:
                server_added_dt = datetime.fromisoformat(server_added_raw)
                if server_added_dt.tzinfo is None:
                    server_added_dt = server_added_dt.replace(tzinfo=timezone.utc)
                server_added_ts = int(server_added_dt.timestamp() * 1000)
                server_added_display = server_added_dt.astimezone().strftime("%d.%m.%Y")
            except ValueError:
                pass
        status_code = "manual" if manual else status_raw.casefold()
        cards.append(
            f"""
            <article class="card" id="media-{int(row['id'])}"
              data-media-id="{int(row['id'])}"
              data-title="{html.escape(str(row['title']), quote=True)}"
              data-year="{html.escape(str(row['year'] or ''), quote=True)}"
              data-search="{html.escape((str(row['title'])+' '+str(row['source_title'])+' '+str(row['year'])+' '+genre_raw+' '+director_raw+' '+actors_raw+' '+str(row['age_rating'] or '')).casefold(), quote=True)}"
              data-genres="{html.escape(json.dumps(genre_values, ensure_ascii=False), quote=True)}"
              data-directors="{html.escape(json.dumps(director_values, ensure_ascii=False), quote=True)}"
              data-actors="{html.escape(json.dumps(actor_values, ensure_ascii=False), quote=True)}"
              data-kind="{html.escape(str(row['kind']), quote=True)}"
              data-kids="{'1' if is_kids else '0'}"
              data-unknown="{'1' if unknown else '0'}"
              data-added-ts="{server_added_ts}"
              data-original-order="{card_order}">
              {poster_html}
              <div class="content">
                <div class="topline"><span class="kind" data-kind-code="{html.escape(str(row['kind']), quote=True)}">{'Film' if row['kind']=='movie' else 'Serie'}</span><span class="badges">{'<span class="kids-badge" data-i18n="kidsBadge">Kinder</span>' if is_kids else ''}<span class="status" data-status-code="{html.escape(status_code, quote=True)}">{html.escape('Manuell' if manual else status_raw)}</span></span></div>
                <h2>{title} <small>{year}</small></h2>
                <div class="rating">★ {rating}<span>/10</span></div>
                <div class="facts">{genre}{' · ' if genre and runtime else ''}{runtime}</div>
                <div class="facts age-rating"><span class="age-label" data-i18n="ageRatingLabel">FSK/Rating</span>: <span class="age-badge age-{age_badge_class}" title="{age_badge_hint_html}">{age_badge_text_html}</span></div>
                {f'<div class="facts added-date"><span data-i18n="addedLabel">Auf Server</span>: {html.escape(server_added_display)}</div>' if server_added_display else ''}
                {f'<div class="facts director"><span data-i18n="directorLabel">Regie</span>: {director}</div>' if director else ''}
                {f'<div class="facts actors"><span data-i18n="castLabel">Besetzung</span>: {actors}</div>' if actors else ''}
                <p>{plot}</p>
                <div class="links">{imdb_html}<button class="play-button" type="button" onclick="startMedia({int(row['id'])}, this, '{'series' if str(row['kind']) == 'series' else 'movie'}')" data-i18n="{'openFolder' if str(row['kind']) == 'series' else 'playFilm'}">{'Ordner öffnen' if str(row['kind']) == 'series' else 'Film starten'}</button><span>{int(row['file_count'])} <span data-i18n="files">Datei(en)</span></span></div>
                <details>
                  <summary data-i18n="sourceCorrection">Quelle &amp; Korrektur</summary>
                  <p class="detected"><span data-i18n="detectedAs">Erkannt als</span>: <strong>{source_title}</strong>{' ('+html.escape(str(row['source_year']))+')' if row['source_year'] else ''}</p>
                  <ul class="paths">{paths_html}</ul>
                  {imdb_search_html}
                  <form method="post" action="/correct/{int(row['id'])}" class="correction" onsubmit="saveViewState(this)">
                    <input name="imdb" placeholder="IMDb-/OMDb-URL oder tt1234567" data-i18n-placeholder="correctionPlaceholder" required>
                    <button type="submit" data-i18n="correctMapping">Zuordnung korrigieren</button>
                  </form>
                  <form method="post" action="/kids/{int(row['id'])}" class="kids-form" onsubmit="saveViewState(this)">
                    <input type="hidden" name="value" value="{'0' if is_kids else '1'}">
                    <button class="secondary" type="submit" data-i18n="{'removeKids' if is_kids else 'markKids'}">{'Kinder-Markierung entfernen' if is_kids else 'Als Kinderinhalt markieren'}</button>
                    {'<span class="manual-note" data-i18n="manualFixed">manuell festgelegt</span>' if kids_manual else '<span class="manual-note" data-i18n="autoDetected">automatisch erkannt</span>' if is_kids else ''}
                  </form>
                  {f'<form method="post" action="/reset/{int(row["id"])}" onsubmit="saveViewState(this)"><button class="secondary" type="submit" data-i18n="removeManualMapping">Manuelle Zuordnung entfernen</button></form>' if manual else ''}
                </details>
              </div>
            </article>
            """
        )

    last_scan = html.escape(meta.get("last_scan_at", "noch nicht"))
    source = html.escape(configured_source_summary(args))
    last_omdb_requests = html.escape(meta.get("last_omdb_requests", "0"))
    last_reused_metadata = html.escape(meta.get("last_reused_metadata", "0"))
    last_omdb_error = html.escape(meta.get("last_omdb_error", ""))
    active_omdb_key = str(getattr(args, "omdb_key", "") or DEFAULT_OMDB_API_KEY).strip()
    try:
        omdb_used, omdb_limit, omdb_remaining = get_omdb_usage(args.db, active_omdb_key)
    except sqlite3.Error:
        omdb_used, omdb_limit, omdb_remaining = 0, OMDB_DAILY_LIMIT, OMDB_DAILY_LIMIT
    omdb_state = (
        f' · OMDb: {last_omdb_requests} <span data-i18n="calls">Aufrufe</span>, '
        f'{last_reused_metadata} <span data-i18n="fromDb">aus DB</span>'
        f' · <span data-i18n="todayUsage">heute lokal gezählt</span>: '
        f'<strong>{omdb_used:,}</strong> / {omdb_limit:,} · '
        f'<span data-i18n="remainingApprox">ca. verbleibend</span>: <strong>{omdb_remaining:,}</strong>'
        + (f' · <span data-i18n="omdbNotice">OMDb-Hinweis</span>: {last_omdb_error}' if last_omdb_error else "")
    )
    background_path = background_image_path()
    if background_path is not None:
        background_token = _background_version_token(background_path)
        body_background_css = (
            "background-color:var(--bg);"
            "background-image:linear-gradient(rgba(10,12,16,.70),rgba(10,12,16,.78)),"
            f"url('/background?v={background_token}');"
            "background-size:cover;background-position:center;background-repeat:no-repeat;background-attachment:fixed;"
        )
    else:
        body_background_css = "background:var(--bg);"
    notice_html = f'<div class="message ok">{html.escape(notice)}</div>' if notice else ""
    error_html = f'<div class="message error">{html.escape(error)}</div>' if error else ""
    return f"""<!doctype html>
<html lang="de">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Medienkatalog</title>
<style>
:root {{ color-scheme: dark; --bg:#111318; --panel:#1a1e25; --muted:#a7afbd; --line:#2b313b; --accent:#f5c451; --play:#36c978; --play-hover:#48da8a; }}
* {{ box-sizing:border-box; }}
body {{ margin:0; font-family:system-ui,-apple-system,Segoe UI,sans-serif; {body_background_css} color:#f5f7fa; min-height:100vh; }}
header {{ position:sticky; top:0; z-index:5; background:rgba(17,19,24,.93); backdrop-filter:blur(12px); border-bottom:1px solid var(--line); padding:12px max(18px,4vw) 11px; box-shadow:0 6px 24px rgba(0,0,0,.14); }}
.header-main {{ display:flex; align-items:center; justify-content:space-between; gap:16px; flex-wrap:wrap; }}
.brand-row {{ display:flex; align-items:center; gap:12px; min-width:0; }}
h1 {{ margin:0; font-size:1.3rem; white-space:nowrap; }}
.header-actions {{ display:flex; gap:7px; align-items:center; flex-wrap:wrap; justify-content:flex-end; }}
.header-actions form {{ margin:0; }}
.header-actions button,.header-actions select {{ min-height:36px; padding:7px 10px; font-size:.8rem; }}
.search-row {{ display:flex; align-items:center; gap:8px; margin-top:10px; }}
.search-row .main-search {{ flex:2 1 420px; }}
.search-row .filename-search {{ flex:1 1 260px; }}
input[type=search], input[name=imdb], select {{ background:#0f1217; color:#fff; border:1px solid #39414d; border-radius:8px; padding:10px 12px; }}
input[type=search] {{ min-width:180px; }}
select {{ min-width:150px; }}
#languageSelect {{ min-width:105px; }}
button {{ border:0; border-radius:8px; padding:10px 14px; cursor:pointer; font-weight:700; background:var(--accent); color:#18130a; }}
.filter-toggle {{ background:#303745; color:#f4f6fa; border:1px solid #414a58; white-space:nowrap; display:inline-flex; align-items:center; gap:7px; min-height:40px; }}
.filter-toggle:hover {{ background:#394251; }}
.filter-count {{ display:none; min-width:19px; height:19px; padding:0 5px; border-radius:999px; place-items:center; background:var(--accent); color:#17130a; font-size:.7rem; font-weight:850; }}
.filter-count.active {{ display:inline-grid; }}
.filter-panel {{ margin-top:9px; padding:10px; border:1px solid #2f3641; border-radius:10px; background:rgba(13,16,21,.68); display:grid; grid-template-columns:repeat(5,minmax(145px,1fr)); gap:8px; }}
.filter-panel[hidden] {{ display:none; }}
.filter-panel select {{ width:100%; min-width:0; padding:8px 9px; font-size:.8rem; }}
button.secondary {{ background:#303745; color:#fff; margin-top:8px; }}
.random-movie-button {{ background:#7d5bd6; color:#fff; }}
.random-movie-button:hover {{ background:#9272e6; }}
.pdf-button {{ background:#2f7f89; color:#fff; }}
.pdf-button:hover {{ background:#3b919d; }}
.meta {{ color:var(--muted); font-size:.76rem; margin-top:8px; display:flex; gap:10px; align-items:center; flex-wrap:wrap; opacity:.92; }}
.server-health {{ display:inline-flex; align-items:center; gap:6px; padding:3px 8px; border:1px solid #39414d; border-radius:999px; background:#12161c; white-space:nowrap; }}
.server-led {{ width:10px; height:10px; border-radius:50%; display:inline-block; background:#717985; box-shadow:0 0 0 2px rgba(255,255,255,.04); }}
.server-led.online {{ background:#42d77d; box-shadow:0 0 8px rgba(66,215,125,.8); }}
.server-led.offline {{ background:#ef5b62; box-shadow:0 0 8px rgba(239,91,98,.75); }}
.server-led.checking {{ background:#e0b64d; box-shadow:0 0 7px rgba(224,182,77,.65); }}
main {{ padding:24px max(18px,4vw) 50px; }}
.message {{ border-radius:8px; padding:10px 12px; margin-bottom:16px; }} .ok {{ background:#173a2a; }} .error {{ background:#4b2024; }}
.grid {{ display:grid; grid-template-columns:repeat(auto-fill,minmax(360px,1fr)); gap:18px; }}
.card {{ display:grid; grid-template-columns:150px 1fr; min-height:225px; background:var(--panel); border:1px solid var(--line); border-radius:12px; overflow:hidden; box-shadow:0 8px 26px rgba(0,0,0,.16); }}
.poster-slot {{ width:150px; height:225px; background:#0d0f13; }}
.poster {{ width:150px; height:225px; object-fit:cover; background:#0d0f13; }} .placeholder {{ display:grid; place-items:center; color:#6f7784; text-align:center; }}
.content {{ padding:14px 15px; min-width:0; display:flex; flex-direction:column; }} .topline {{ display:flex; justify-content:space-between; gap:8px; color:var(--muted); font-size:.78rem; }}
.kind,.status,.kids-badge {{ border:1px solid #3a424f; border-radius:999px; padding:2px 7px; }} .badges {{ display:flex; gap:5px; align-items:center; }} .kids-badge {{ border-color:#7c6231; color:#ffd978; }} h2 {{ margin:8px 0 2px; font-size:1.15rem; }} h2 small {{ color:var(--muted); font-weight:500; }}
.rating {{ color:var(--accent); font-size:1.1rem; font-weight:800; }} .rating span {{ color:var(--muted); font-size:.8rem; }} .facts,.links,.detected {{ color:var(--muted); font-size:.84rem; }} .links {{ align-items:center; flex-wrap:wrap; }}
.age-rating {{ display:flex; align-items:center; gap:4px; flex-wrap:wrap; margin-top:2px; }}
.age-label {{ color:var(--muted); }}
.age-badge {{ display:inline-flex; align-items:center; padding:1px 6px; border-radius:6px; font-size:.72rem; line-height:1.35; font-weight:700; letter-spacing:.01em; border:1px solid #4a5260; background:#232933; color:#d7dde7; }}
.age-all {{ color:#86d79c; background:rgba(66,135,83,.12); border-color:rgba(104,188,124,.35); }}
.age-kids {{ color:#8ec8ee; background:rgba(68,126,165,.12); border-color:rgba(106,164,201,.35); }}
.age-teen {{ color:#e2c16f; background:rgba(148,117,45,.12); border-color:rgba(188,153,73,.35); }}
.age-mature {{ color:#df9b70; background:rgba(151,83,45,.12); border-color:rgba(188,107,64,.35); }}
.age-adult {{ color:#de848c; background:rgba(143,57,65,.12); border-color:rgba(184,79,89,.35); }}
.age-neutral {{ color:#c5ccd6; background:rgba(99,108,121,.10); border-color:rgba(126,136,150,.32); }}
.age-unknown {{ color:#9da5b1; background:rgba(83,91,103,.08); border-color:rgba(112,121,134,.25); }}
p {{ margin:8px 0; line-height:1.4; }} .links {{ display:flex; gap:12px; margin-top:auto; padding-top:10px; }} a {{ color:#8bc2ff; }}
.play-button {{ background:var(--play); color:#07140c; border:1px solid #63e8a0; padding:6px 11px; font-size:.8rem; box-shadow:0 2px 10px rgba(54,201,120,.18); }}
.play-button:hover {{ background:var(--play-hover); }} .play-button:disabled {{ opacity:.6; cursor:default; }}
.reset-filters {{ background:#252b35; color:#dfe4ec; border:1px solid #39414d; white-space:nowrap; }} .reset-filters:hover {{ background:#303845; }} details {{ margin-top:10px; border-top:1px solid var(--line); padding-top:8px; }} summary {{ cursor:pointer; color:#cdd3dd; }}
.paths {{ max-height:110px; overflow:auto; padding-left:18px; font-size:.75rem; color:var(--muted); word-break:break-all; }}
.imdb-search-tools {{ display:flex; gap:9px; align-items:center; flex-wrap:wrap; margin:8px 0 10px; }}
.imdb-search-button {{ display:inline-flex; align-items:center; min-height:38px; padding:8px 12px; border-radius:8px; background:#2d6da3; color:#fff; text-decoration:none; font-weight:700; border:1px solid #4388c2; }}
.imdb-search-button:hover {{ background:#397fb7; }}
.imdb-results {{ display:grid; gap:7px; margin:8px 0 12px; }}
.imdb-result {{ display:grid; grid-template-columns:42px minmax(0,1fr) auto; gap:9px; align-items:center; padding:7px 8px; border:1px solid #343c48; border-radius:8px; background:#13171d; }}
.imdb-result-poster {{ width:42px; height:58px; object-fit:cover; border-radius:5px; background:#0d0f13; }}
.imdb-result-poster.placeholder-mini {{ display:grid; place-items:center; color:#626b78; font-size:.65rem; }}
.imdb-result-main {{ min-width:0; }}
.imdb-result-title {{ font-weight:750; line-height:1.25; }}
.imdb-result-meta,.imdb-result-subtitle {{ color:var(--muted); font-size:.75rem; line-height:1.3; margin-top:2px; }}
.imdb-result-id {{ color:#8bc2ff; font-family:ui-monospace,SFMono-Regular,Consolas,monospace; }}
.imdb-assign-form {{ margin:0; }}
.imdb-assign-button {{ background:#3a82c4; color:#fff; padding:7px 10px; font-size:.78rem; border:1px solid #59a0df; }}
.imdb-search-status {{ color:var(--muted); font-size:.8rem; padding:5px 0; }}
@media (max-width:650px) {{ .imdb-result {{ grid-template-columns:36px minmax(0,1fr); }} .imdb-result-poster {{ width:36px; height:50px; }} .imdb-assign-form {{ grid-column:1 / -1; }} .imdb-assign-button {{ width:100%; }} }}
.correction {{ display:flex; gap:8px; flex-wrap:wrap; }} .correction input {{ flex:1; min-width:190px; }} .kids-form {{ display:flex; gap:8px; align-items:center; flex-wrap:wrap; }} .manual-note {{ color:var(--muted); font-size:.75rem; }}
.empty {{ color:var(--muted); padding:30px 0; }}
.config-button {{ background:#586273; color:#fff; }}
.config-button:hover {{ background:#687487; }}
dialog.config-dialog {{ width:min(700px,calc(100% - 28px)); border:1px solid #3b4350; border-radius:14px; padding:0; background:var(--panel); color:#f5f7fa; box-shadow:0 22px 70px rgba(0,0,0,.55); }}
dialog.config-dialog::backdrop {{ background:rgba(0,0,0,.68); }}
.config-dialog-inner {{ padding:18px; }}
.config-head {{ display:flex; align-items:center; justify-content:space-between; gap:12px; margin-bottom:14px; }}
.config-head h2 {{ margin:0; }}
.config-grid {{ display:grid; grid-template-columns:minmax(150px,.7fr) minmax(240px,1.5fr); gap:11px 14px; align-items:center; }}
.config-grid label {{ color:#d8dde5; font-size:.88rem; }}
.config-grid input,.config-grid select {{ width:100%; min-width:0; }}
.config-note {{ color:var(--muted); font-size:.78rem; margin:10px 0 0; line-height:1.4; }}
.config-actions {{ display:flex; gap:10px; justify-content:flex-end; align-items:center; flex-wrap:wrap; margin-top:16px; }}
.config-status {{ color:var(--muted); font-size:.82rem; margin-right:auto; }}
.config-status.ok {{ color:#82dea5; background:none; padding:0; }}
.config-status.error {{ color:#ff8c94; background:none; padding:0; }}
.config-close {{ background:#303745; color:#fff; }}
@media (max-width:620px) {{ .config-grid {{ grid-template-columns:1fr; gap:6px; }} .config-grid label {{ margin-top:6px; }} }}
dialog.random-dialog {{ width:min(720px,calc(100% - 28px)); border:1px solid #3b4350; border-radius:14px; padding:0; background:var(--panel); color:#f5f7fa; box-shadow:0 22px 70px rgba(0,0,0,.55); }}
dialog.random-dialog::backdrop {{ background:rgba(0,0,0,.68); }}
.random-dialog-inner {{ padding:18px; }}
.random-dialog-head {{ display:flex; align-items:center; justify-content:space-between; gap:12px; margin-bottom:14px; }}
.random-dialog-head h2 {{ margin:0; }}
.random-close {{ background:#303745; color:#fff; padding:7px 10px; }}
.random-layout {{ display:grid; grid-template-columns:150px minmax(0,1fr); gap:18px; }}
.random-poster {{ width:150px; height:225px; object-fit:cover; border-radius:8px; background:#0d0f13; }}
.random-poster.placeholder {{ padding:10px; }}
.random-info h3 {{ margin:0 0 6px; font-size:1.35rem; }}
.random-info .random-rating {{ color:var(--accent); font-size:1.05rem; font-weight:800; margin-bottom:6px; }}
.random-info .random-facts {{ color:var(--muted); font-size:.88rem; margin-bottom:10px; }}
.random-info .random-plot {{ line-height:1.45; }}
.random-actions {{ display:flex; gap:10px; flex-wrap:wrap; margin-top:14px; }}
@media (max-width:1050px) {{ .filter-panel {{ grid-template-columns:repeat(3,minmax(140px,1fr)); }} }}
@media (max-width:760px) {{ .header-main {{ align-items:flex-start; }} .header-actions {{ justify-content:flex-start; width:100%; }} .search-row {{ flex-wrap:wrap; }} .search-row .main-search,.search-row .filename-search {{ flex:1 1 100%; width:100%; }} .filter-toggle,.search-row .reset-filters {{ flex:1 1 auto; }} .filter-panel {{ grid-template-columns:repeat(2,minmax(130px,1fr)); }} }}
@media (max-width:480px) {{ .brand-row {{ width:100%; justify-content:space-between; }} .filter-panel {{ grid-template-columns:1fr; }} }}
@media (max-width:560px) {{ .grid {{ grid-template-columns:1fr; }} .card {{ grid-template-columns:105px 1fr; }} .poster-slot,.poster {{ width:105px; height:158px; }} .random-layout {{ grid-template-columns:95px minmax(0,1fr); gap:12px; }} .random-poster {{ width:95px; height:143px; }} }}
</style>
</head>
<body>
<header>
  <div class="header-main">
    <div class="brand-row">
      <h1><span data-i18n="catalogTitle">Medienkatalog</span> · <span id="visibleCount">{len(rows)}</span> <span data-i18n="titles">Titel</span></h1>
      <span class="server-health" id="serverHealth" title="{html.escape(server_host or configured_source_summary(args), quote=True)}">
        <span id="serverLed" class="server-led {'online' if server_online else 'offline'}" aria-hidden="true"></span>
        <span data-i18n="filmServer">Filmserver</span>: <strong id="serverStatusText" data-server-state="{'online' if server_online else 'offline'}">{'online' if server_online else 'offline'}</strong>
      </span>
    </div>
    <div class="header-actions">
      <button class="random-movie-button" type="button" onclick="showRandomMovie()" data-i18n="randomMovie">Zufälliger Film</button>
      <button class="pdf-button" type="button" onclick="exportPdf(this)" data-i18n="exportPdf">PDF-Liste erstellen</button>
      <form method="post" action="/scan" onsubmit="return refreshLibrary(event, this)"><button id="scanButton" type="submit" data-i18n="refreshLibrary">Bibliothek aktualisieren</button></form>
      <button class="config-button" type="button" onclick="openConfigDialog()" data-i18n="settings">Einstellungen</button>
      <select id="languageSelect" onchange="changeLanguage()" aria-label="Sprache / Language">
        <option value="de">DE</option>
        <option value="en">EN</option>
      </select>
    </div>
  </div>

  <div class="search-row">
    <input class="main-search" id="search" type="search" placeholder="Titel, Jahr, Genre, Regisseur oder Schauspieler filtern …" data-i18n-placeholder="searchPlaceholder" oninput="filterCards()">
    <input class="filename-search" id="filenameSearch" type="search" placeholder="Dateiname enthält …" data-i18n-placeholder="filenamePlaceholder" oninput="filterCards()" aria-label="Dateinamen filtern">
    <button id="filterToggle" class="filter-toggle" type="button" onclick="toggleFilterPanel()" aria-expanded="false">
      <span data-i18n="filters">Filter</span><span id="activeFilterCount" class="filter-count">0</span>
    </button>
    <button class="reset-filters" type="button" onclick="resetFilters()" data-i18n="resetFilters">Zurücksetzen</button>
  </div>

  <div id="filterPanel" class="filter-panel" hidden>
    <select id="catalogFilter" onchange="filterCards()" aria-label="Katalog filtern">
      <option value="all" data-i18n="allTitles">Alle Titel</option>
      <option value="movies" data-i18n="moviesOnly">Nur Filme</option>
      <option value="series" data-i18n="seriesOnly">Nur Serien</option>
      <option value="kids" data-i18n="kidsAll">Kinder: alle</option>
      <option value="kids-movies" data-i18n="kidsMovies">Kinderfilme</option>
      <option value="kids-series" data-i18n="kidsSeries">Kinderserien</option>
      <option value="unknown" data-i18n="unknown">Unbekannt / nicht zugeordnet</option>
    </select>
    <select id="genreFilter" onchange="filterCards()" aria-label="Nach Genre filtern">
      <option value="" data-i18n="allGenres">Alle Genres</option>
      {genre_options}
    </select>
    <select id="directorFilter" onchange="filterCards()" aria-label="Nach Regisseur filtern">
      <option value="" data-i18n="allDirectors">Alle Regisseure</option>
      {director_options}
    </select>
    <select id="actorFilter" onchange="filterCards()" aria-label="Nach Schauspieler filtern">
      <option value="" data-i18n="allActors">Alle Schauspieler</option>
      {actor_options}
    </select>
    <select id="recentFilter" onchange="filterCards()" aria-label="Nach Server-Datum filtern">
      <option value="" data-i18n="allAddedDates">Alle Speicherzeiten</option>
      <option value="7" data-i18n="last7Days">Zuletzt hinzugefügt: 7 Tage</option>
      <option value="30" data-i18n="last30Days">Zuletzt hinzugefügt: 30 Tage</option>
      <option value="90" data-i18n="last90Days">Zuletzt hinzugefügt: 90 Tage</option>
      <option value="365" data-i18n="last365Days">Zuletzt hinzugefügt: 1 Jahr</option>
    </select>
  </div>

  <div class="meta">
    <span><span data-i18n="source">Quellen</span>: <span id="sourceSummary">{source}</span> · <span data-i18n="lastScan">letzter Scan</span>: {last_scan}{omdb_state} · <span data-i18n="serverDates">Serverdaten</span>: {html.escape(meta.get("server_date_count", "0"))}/{len(rows)}</span>
  </div>
</header>
<main>
{notice_html}{error_html}
<div class="grid" id="grid">{''.join(cards)}</div>
<div class="empty" id="empty" style="display:none" data-i18n="noMatches">Keine passenden Titel.</div>
</main>
<dialog id="randomDialog" class="random-dialog">
  <div class="random-dialog-inner">
    <div class="random-dialog-head">
      <h2 data-i18n="randomMovieTitle">Dein Zufallsfilm</h2>
      <button class="random-close" type="button" onclick="closeRandomMovie()" aria-label="Schließen" data-i18n="close">Schließen</button>
    </div>
    <div class="random-layout">
      <div id="randomPosterSlot"><div class="random-poster placeholder" data-i18n="noCover">Kein Cover</div></div>
      <div class="random-info">
        <h3 id="randomTitle"></h3>
        <div class="random-rating" id="randomRating"></div>
        <div class="random-facts" id="randomFacts"></div>
        <p class="random-plot" id="randomPlot"></p>
        <div class="random-actions">
          <button id="randomPlayButton" class="play-button" type="button" data-i18n="playFilm">Film starten</button>
          <button class="secondary" type="button" onclick="showRandomMovie()" data-i18n="anotherRandom">Noch einen</button>
        </div>
      </div>
    </div>
  </div>
</dialog>
<dialog id="configDialog" class="config-dialog">
  <div class="config-dialog-inner">
    <div class="config-head">
      <h2 data-i18n="settingsTitle">Konfiguration</h2>
      <button class="config-close" type="button" onclick="closeConfigDialog()" data-i18n="close">Schließen</button>
    </div>
    <form id="configForm" onsubmit="saveConfig(event)">
      <div class="config-grid">
        <label for="cfgApiKey" data-i18n="cfgApiKey">OMDb API-Key</label>
        <input id="cfgApiKey" type="password" autocomplete="off" spellcheck="false">

        <label for="cfgMaxRequests" data-i18n="cfgMaxRequests">Max. Requests pro Tag</label>
        <input id="cfgMaxRequests" type="number" min="1" step="1">

        <label for="cfgStartupLanguage" data-i18n="cfgStartupLanguage">Startsprache</label>
        <select id="cfgStartupLanguage"><option value="de">Deutsch</option><option value="en">English</option></select>

        <label for="cfgScanStartup" data-i18n="cfgScanStartup">Scan beim Start</label>
        <select id="cfgScanStartup"><option value="yes" data-i18n="yes">Ja</option><option value="no" data-i18n="no">Nein</option></select>

        <label for="cfgMoviesPath" data-i18n="cfgMoviesPath">Pfad Filme</label>
        <input id="cfgMoviesPath" type="text" spellcheck="false">

        <label for="cfgSeriesPath" data-i18n="cfgSeriesPath">Pfad Serien</label>
        <input id="cfgSeriesPath" type="text" spellcheck="false">
      </div>
      <p class="config-note" data-i18n="configNote">Änderungen werden in config.txt neben dem Python-Skript gespeichert. Neue Pfade gelten beim nächsten Bibliotheks-Scan.</p>
      <div class="config-actions">
        <span id="configStatus" class="config-status" aria-live="polite"></span>
        <button class="config-close" type="button" onclick="closeConfigDialog()" data-i18n="cancel">Abbrechen</button>
        <button id="configSaveButton" type="submit" data-i18n="saveConfig">Speichern</button>
      </div>
    </form>
  </div>
</dialog>
<script>
const VIEW_STATE_KEY = 'medienkatalog-view-v1';
const LANGUAGE_KEY = 'medienkatalog-language-session-v1';
const CONFIG_STARTUP_LANGUAGE = {json.dumps(str(getattr(args, 'startup_language', 'de')) if str(getattr(args, 'startup_language', 'de')) in {'de','en'} else 'de')};
let activeLanguage = CONFIG_STARTUP_LANGUAGE;
const I18N = {{
  de: {{
    pageTitle:'Medienkatalog', catalogTitle:'Medienkatalog', titles:'Titel', filters:'Filter',
    searchPlaceholder:'Titel, Jahr, Genre, Regisseur oder Schauspieler filtern …',
    filenamePlaceholder:'Dateiname enthält …',
    allTitles:'Alle Titel', moviesOnly:'Nur Filme', seriesOnly:'Nur Serien', kidsAll:'Kinder: alle',
    kidsMovies:'Kinderfilme', kidsSeries:'Kinderserien', unknown:'Unbekannt / nicht zugeordnet',
    allGenres:'Alle Genres', allDirectors:'Alle Regisseure', allActors:'Alle Schauspieler',
    allAddedDates:'Alle Speicherzeiten', last7Days:'Zuletzt hinzugefügt: 7 Tage', last30Days:'Zuletzt hinzugefügt: 30 Tage',
    last90Days:'Zuletzt hinzugefügt: 90 Tage', last365Days:'Zuletzt hinzugefügt: 1 Jahr', addedLabel:'Auf Server',
    resetFilters:'Zurücksetzen', refreshLibrary:'Bibliothek aktualisieren', settings:'Einstellungen', settingsTitle:'Konfiguration', cfgApiKey:'OMDb API-Key', cfgMaxRequests:'Max. Requests pro Tag', cfgStartupLanguage:'Startsprache', cfgScanStartup:'Scan beim Start', cfgMoviesPath:'Pfad Filme', cfgSeriesPath:'Pfad Serien', configNote:'Änderungen werden in config.txt neben dem Python-Skript gespeichert. Neue Pfade gelten beim nächsten Bibliotheks-Scan.', saveConfig:'Speichern', savingConfig:'Speichere …', configSaved:'Konfiguration gespeichert.', configLoadFailed:'Konfiguration konnte nicht geladen werden.', configSaveFailed:'Konfiguration konnte nicht gespeichert werden.', cancel:'Abbrechen', yes:'Ja', no:'Nein', exportPdf:'PDF-Liste erstellen', pdfCreating:'PDF wird erstellt …', pdfFailed:'PDF konnte nicht erstellt werden.', noPdfTitles:'Keine sichtbaren Titel für den PDF-Export.', source:'Quelle',
    lastScan:'letzter Scan', serverDates:'Serverdaten', calls:'Aufrufe', fromDb:'aus DB', omdbNotice:'OMDb-Hinweis',
    todayUsage:'heute lokal gezählt', remainingApprox:'ca. verbleibend', filmServer:'Filmserver', online:'online', offline:'offline', checking:'prüfe …',
    noMatches:'Keine passenden Titel.', noCover:'Kein Cover', openIMDb:'IMDb öffnen',
    searchIMDb:'Auf IMDb suchen', imdbSearchHint:'Bis zu 10 IMDb-Treffer anzeigen und direkt zuweisen.',
    imdbSearching:'IMDb wird durchsucht …', imdbNoResults:'Keine IMDb-Treffer gefunden.', imdbSearchFailed:'IMDb-Suche fehlgeschlagen.', assignIMDb:'Zuweisen',
    kidsBadge:'Kinder', ageRatingLabel:'FSK/Rating', directorLabel:'Regie', castLabel:'Besetzung', playFilm:'Film starten', openFolder:'Ordner öffnen',
    files:'Datei(en)', sourceCorrection:'Quelle & Korrektur', detectedAs:'Erkannt als',
    correctionPlaceholder:'IMDb-/OMDb-URL oder tt1234567', correctMapping:'Zuordnung korrigieren',
    removeKids:'Kinder-Markierung entfernen', markKids:'Als Kinderinhalt markieren',
    manualFixed:'manuell festgelegt', autoDetected:'automatisch erkannt',
    removeManualMapping:'Manuelle Zuordnung entfernen', scanning:'Bibliothek wird aktualisiert …',
    scanFailed:'Bibliothek konnte nicht aktualisiert werden.', starting:'Öffne …', started:'Geöffnet',
    playFailed:'Medienaktion konnte nicht ausgeführt werden.', randomMovie:'Zufälliger Film',
    randomMovieTitle:'Dein Zufallsfilm', anotherRandom:'Noch einen', close:'Schließen', noMovies:'Keine Filme in der Bibliothek gefunden.'
  }},
  en: {{
    pageTitle:'Media Library', catalogTitle:'Media Library', titles:'titles', filters:'Filters',
    searchPlaceholder:'Filter by title, year, genre, director or actor …',
    filenamePlaceholder:'Filename contains …',
    allTitles:'All titles', moviesOnly:'Movies only', seriesOnly:'Series only', kidsAll:'Kids: all',
    kidsMovies:'Kids movies', kidsSeries:'Kids series', unknown:'Unknown / not matched',
    allGenres:'All genres', allDirectors:'All directors', allActors:'All actors',
    allAddedDates:'All added dates', last7Days:'Added in last 7 days', last30Days:'Added in last 30 days',
    last90Days:'Added in last 90 days', last365Days:'Added in last year', addedLabel:'On server',
    resetFilters:'Reset', refreshLibrary:'Update library', settings:'Settings', settingsTitle:'Configuration', cfgApiKey:'OMDb API key', cfgMaxRequests:'Max. requests per day', cfgStartupLanguage:'Startup language', cfgScanStartup:'Scan on startup', cfgMoviesPath:'Movies path', cfgSeriesPath:'Series path', configNote:'Changes are saved to config.txt next to the Python script. New paths apply to the next library scan.', saveConfig:'Save', savingConfig:'Saving …', configSaved:'Configuration saved.', configLoadFailed:'Configuration could not be loaded.', configSaveFailed:'Configuration could not be saved.', cancel:'Cancel', yes:'Yes', no:'No', exportPdf:'Create PDF list', pdfCreating:'Creating PDF …', pdfFailed:'PDF could not be created.', noPdfTitles:'No visible titles to export to PDF.', source:'Source',
    lastScan:'last scan', serverDates:'server dates', calls:'requests', fromDb:'from DB', omdbNotice:'OMDb notice',
    todayUsage:'locally counted today', remainingApprox:'approx. remaining', filmServer:'Movie server', online:'online', offline:'offline', checking:'checking …',
    noMatches:'No matching titles.', noCover:'No cover', openIMDb:'Open IMDb',
    searchIMDb:'Search IMDb', imdbSearchHint:'Show up to 10 IMDb results and assign one directly.',
    imdbSearching:'Searching IMDb …', imdbNoResults:'No IMDb results found.', imdbSearchFailed:'IMDb search failed.', assignIMDb:'Assign',
    kidsBadge:'Kids', ageRatingLabel:'Age rating', directorLabel:'Director', castLabel:'Cast', playFilm:'Play', openFolder:'Open folder',
    files:'file(s)', sourceCorrection:'Source & correction', detectedAs:'Detected as',
    correctionPlaceholder:'IMDb/OMDb URL or tt1234567', correctMapping:'Correct match',
    removeKids:'Remove kids tag', markKids:'Mark as kids content',
    manualFixed:'set manually', autoDetected:'detected automatically',
    removeManualMapping:'Remove manual match', scanning:'Updating library …',
    scanFailed:'Library could not be updated.', starting:'Opening …', started:'Opened',
    playFailed:'Media action could not be completed.', randomMovie:'Random movie',
    randomMovieTitle:'Your random movie', anotherRandom:'Another one', close:'Close', noMovies:'No movies found in the library.'
  }}
}};
const STATUS_I18N = {{
  de: {{ 'manual':'Manuell', 'gefunden':'gefunden', 'nicht zugeordnet':'nicht zugeordnet', 'metadaten deaktiviert':'Metadaten deaktiviert', 'manuell zugeordnet':'Manuell' }},
  en: {{ 'manual':'Manual', 'gefunden':'found', 'nicht zugeordnet':'not matched', 'metadaten deaktiviert':'metadata disabled', 'manuell zugeordnet':'Manual' }}
}};

function t(key) {{
  return (I18N[activeLanguage] && I18N[activeLanguage][key]) || I18N.de[key] || key;
}}

function applyLanguage(language) {{
  activeLanguage = language === 'en' ? 'en' : 'de';
  document.documentElement.lang = activeLanguage;
  document.title = t('pageTitle');
  document.querySelectorAll('[data-i18n]').forEach(element => {{
    const key = element.dataset.i18n;
    if (key) element.textContent = t(key);
  }});
  document.querySelectorAll('[data-i18n-placeholder]').forEach(element => {{
    const key = element.dataset.i18nPlaceholder;
    if (key) element.setAttribute('placeholder', t(key));
  }});
  document.querySelectorAll('[data-kind-code]').forEach(element => {{
    element.textContent = element.dataset.kindCode === 'series'
      ? (activeLanguage === 'en' ? 'Series' : 'Serie')
      : (activeLanguage === 'en' ? 'Movie' : 'Film');
  }});
  document.querySelectorAll('[data-status-code]').forEach(element => {{
    const code = (element.dataset.statusCode || '').toLocaleLowerCase();
    element.textContent = (STATUS_I18N[activeLanguage] && STATUS_I18N[activeLanguage][code]) || code;
  }});
  const languageSelect = document.getElementById('languageSelect');
  if (languageSelect) languageSelect.value = activeLanguage;
  updateServerStatusLabel();
  try {{ sessionStorage.setItem(LANGUAGE_KEY, activeLanguage); }} catch (_) {{}}
}}

function updateServerStatusLabel() {{
  const textElement = document.getElementById('serverStatusText');
  if (!textElement) return;
  const state = textElement.dataset.serverState || 'checking';
  textElement.textContent = t(state);
}}

function setServerStatus(state, host) {{
  const normalized = state === 'online' ? 'online' : (state === 'offline' ? 'offline' : 'checking');
  const led = document.getElementById('serverLed');
  const textElement = document.getElementById('serverStatusText');
  const wrapper = document.getElementById('serverHealth');
  if (led) led.className = 'server-led ' + normalized;
  if (textElement) {{
    textElement.dataset.serverState = normalized;
    textElement.textContent = t(normalized);
  }}
  if (wrapper && host) wrapper.title = String(host);
}}

async function refreshServerStatus() {{
  setServerStatus('checking');
  try {{
    const response = await fetch('/server-status', {{ cache:'no-store' }});
    const payload = await response.json().catch(() => ({{}}));
    if (!response.ok) throw new Error('status');
    setServerStatus(payload.online ? 'online' : 'offline', payload.host || '');
  }} catch (_) {{
    setServerStatus('offline');
  }}
}}

function changeLanguage() {{
  applyLanguage(document.getElementById('languageSelect').value);
}}

function toggleFilterPanel(forceOpen) {{
  const panel = document.getElementById('filterPanel');
  const button = document.getElementById('filterToggle');
  if (!panel || !button) return;
  const shouldOpen = typeof forceOpen === 'boolean' ? forceOpen : panel.hidden;
  panel.hidden = !shouldOpen;
  button.setAttribute('aria-expanded', shouldOpen ? 'true' : 'false');
}}

function updateFilterSummary() {{
  const active = [
    document.getElementById('catalogFilter').value !== 'all',
    Boolean(document.getElementById('genreFilter').value),
    Boolean(document.getElementById('directorFilter').value),
    Boolean(document.getElementById('actorFilter').value),
    Boolean(document.getElementById('recentFilter').value)
  ].filter(Boolean).length;
  const badge = document.getElementById('activeFilterCount');
  if (badge) {{
    badge.textContent = String(active);
    badge.classList.toggle('active', active > 0);
  }}
}}

function filterCards() {{
  const q = document.getElementById('search').value.trim().toLocaleLowerCase();
  const filenameQuery = document.getElementById('filenameSearch').value.trim().toLocaleLowerCase();
  const filter = document.getElementById('catalogFilter').value;
  const genre = document.getElementById('genreFilter').value;
  const director = document.getElementById('directorFilter').value;
  const actor = document.getElementById('actorFilter').value;
  const recent = document.getElementById('recentFilter').value;
  const recentDays = recent ? Number(recent) : 0;
  const recentCutoff = recentDays > 0 ? Date.now() - recentDays * 86400000 : 0;
  let visible = 0;
  document.querySelectorAll('.card').forEach(card => {{
    const searchMatch = !q || card.dataset.search.includes(q);
    let filenameMatch = true;
    if (filenameQuery) {{
      // Nur die eigentlichen Dateinamen durchsuchen, nicht die Ordnerpfade.
      // Das Ergebnis wird pro Karte gecacht, damit auch Serien mit vielen
      // Episoden beim Tippen flüssig filterbar bleiben.
      if (typeof card._filenameSearchCache !== 'string') {{
        card._filenameSearchCache = Array.from(card.querySelectorAll('.paths li'))
          .map(item => {{
            const fullPath = (item.textContent || '').trim();
            const parts = fullPath.split(/[\\/]/);
            return (parts[parts.length - 1] || '').toLocaleLowerCase();
          }})
          .join('\\n');
      }}
      filenameMatch = card._filenameSearchCache.includes(filenameQuery);
    }}
    let filterMatch = true;
    if (filter === 'movies') filterMatch = card.dataset.kind === 'movie';
    else if (filter === 'series') filterMatch = card.dataset.kind === 'series';
    else if (filter === 'kids') filterMatch = card.dataset.kids === '1';
    else if (filter === 'kids-movies') filterMatch = card.dataset.kids === '1' && card.dataset.kind === 'movie';
    else if (filter === 'kids-series') filterMatch = card.dataset.kids === '1' && card.dataset.kind === 'series';
    else if (filter === 'unknown') filterMatch = card.dataset.unknown === '1';
    let genreMatch = true;
    let directorMatch = true;
    let actorMatch = true;
    let recentMatch = true;
    if (genre) {{
      try {{ genreMatch = JSON.parse(card.dataset.genres || '[]').includes(genre); }}
      catch (_) {{ genreMatch = false; }}
    }}
    if (director) {{
      try {{ directorMatch = JSON.parse(card.dataset.directors || '[]').includes(director); }}
      catch (_) {{ directorMatch = false; }}
    }}
    if (actor) {{
      try {{ actorMatch = JSON.parse(card.dataset.actors || '[]').includes(actor); }}
      catch (_) {{ actorMatch = false; }}
    }}
    if (recentDays > 0) {{
      const addedTs = Number(card.dataset.addedTs || '0');
      recentMatch = addedTs > 0 && addedTs >= recentCutoff;
    }}
    const show = searchMatch && filenameMatch && filterMatch && genreMatch && directorMatch && actorMatch && recentMatch;
    card.style.display = show ? '' : 'none';
    if (show) visible++;
  }});
  const grid = document.getElementById('grid');
  const cards = Array.from(grid.querySelectorAll('.card'));
  cards.sort((a, b) => {{
    if (recentDays > 0) {{
      const byDate = Number(b.dataset.addedTs || '0') - Number(a.dataset.addedTs || '0');
      if (byDate !== 0) return byDate;
    }}
    return Number(a.dataset.originalOrder || '0') - Number(b.dataset.originalOrder || '0');
  }}).forEach(card => grid.appendChild(card));
  document.getElementById('empty').style.display = visible ? 'none' : 'block';
  document.getElementById('visibleCount').textContent = String(visible);
  updateFilterSummary();
}}

function resetFilters() {{
  document.getElementById('search').value = '';
  document.getElementById('filenameSearch').value = '';
  document.getElementById('catalogFilter').value = 'all';
  document.getElementById('genreFilter').value = '';
  document.getElementById('directorFilter').value = '';
  document.getElementById('actorFilter').value = '';
  document.getElementById('recentFilter').value = '';
  sessionStorage.removeItem(VIEW_STATE_KEY);
  filterCards();
  toggleFilterPanel(false);
}}

async function exportPdf(button) {{
  const ids = Array.from(document.querySelectorAll('.card'))
    .filter(card => card.style.display !== 'none')
    .map(card => Number(card.dataset.mediaId || '0'))
    .filter(id => Number.isInteger(id) && id > 0);
  if (!ids.length) {{
    alert(t('noPdfTitles'));
    return;
  }}
  const originalText = button ? button.textContent : '';
  if (button) {{
    button.disabled = true;
    button.textContent = t('pdfCreating');
  }}
  try {{
    const response = await fetch('/export-pdf', {{
      method: 'POST',
      headers: {{'Content-Type':'application/json'}},
      body: JSON.stringify({{ids: ids, language: activeLanguage}}),
      cache: 'no-store'
    }});
    if (!response.ok) {{
      const message = await response.text();
      throw new Error(message || t('pdfFailed'));
    }}
    const blob = await response.blob();
    let filename = 'Medienkatalog.pdf';
    const disposition = response.headers.get('Content-Disposition') || '';
    const match = disposition.match(/filename="?([^";]+)"?/i);
    if (match && match[1]) filename = match[1];
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = filename;
    document.body.appendChild(link);
    link.click();
    link.remove();
    window.setTimeout(() => URL.revokeObjectURL(url), 3000);
  }} catch (error) {{
    alert((error && error.message) ? error.message : t('pdfFailed'));
  }} finally {{
    if (button) {{
      button.disabled = false;
      button.textContent = originalText || t('exportPdf');
    }}
  }}
}}

function visibleAnchorCard() {{
  const cards = Array.from(document.querySelectorAll('.card'))
    .filter(card => card.style.display !== 'none');
  if (!cards.length) return null;

  const header = document.querySelector('header');
  const targetTop = header ? header.getBoundingClientRect().bottom + 8 : 8;
  let best = null;
  let bestDistance = Infinity;
  cards.forEach(card => {{
    const rect = card.getBoundingClientRect();
    if (rect.bottom <= targetTop || rect.top >= window.innerHeight) return;
    const distance = Math.abs(rect.top - targetTop);
    if (distance < bestDistance) {{
      best = card;
      bestDistance = distance;
    }}
  }});
  if (best) return best;

  cards.forEach(card => {{
    const distance = Math.abs(card.getBoundingClientRect().top - targetTop);
    if (distance < bestDistance) {{
      best = card;
      bestDistance = distance;
    }}
  }});
  return best;
}}

function saveViewState(form) {{
  const formCard = form ? form.closest('.card') : null;
  const card = formCard || visibleAnchorCard();
  const openDetails = Array.from(document.querySelectorAll('.card details[open]'))
    .map(details => details.closest('.card'))
    .filter(Boolean)
    .map(cardEl => cardEl.id);
  const state = {{
    search: document.getElementById('search').value,
    filenameSearch: document.getElementById('filenameSearch').value,
    filter: document.getElementById('catalogFilter').value,
    genre: document.getElementById('genreFilter').value,
    director: document.getElementById('directorFilter').value,
    actor: document.getElementById('actorFilter').value,
    recent: document.getElementById('recentFilter').value,
    filterPanelOpen: !document.getElementById('filterPanel').hidden,
    scrollY: window.scrollY,
    anchorId: card ? card.id : '',
    anchorTop: card ? card.getBoundingClientRect().top : 0,
    openDetails: openDetails
  }};
  sessionStorage.setItem(VIEW_STATE_KEY, JSON.stringify(state));
}}

async function refreshLibrary(event, form) {{
  event.preventDefault();
  saveViewState(null);
  const button = form.querySelector('button[type="submit"]');
  const originalText = button ? button.textContent : '';
  if (button) {{
    button.disabled = true;
    button.textContent = t('scanning');
  }}

  try {{
    const response = await fetch('/scan', {{
      method: 'POST',
      headers: {{ 'X-Requested-With': 'MedienKatalog' }},
      cache: 'no-store'
    }});
    const result = await response.json().catch(() => ({{}}));
    if (!response.ok || result.ok === false) {{
      throw new Error(result.error || t('scanFailed'));
    }}
    window.location.reload();
  }} catch (error) {{
    if (button) {{
      button.disabled = false;
      button.textContent = originalText;
    }}
    alert(error.message || String(error));
  }}
}}

function restoreViewState() {{
  const raw = sessionStorage.getItem(VIEW_STATE_KEY);
  if (!raw) {{ filterCards(); return; }}
  sessionStorage.removeItem(VIEW_STATE_KEY);
  try {{
    const state = JSON.parse(raw);
    if (typeof state.search === 'string') document.getElementById('search').value = state.search;
    if (typeof state.filenameSearch === 'string') document.getElementById('filenameSearch').value = state.filenameSearch;
    if (typeof state.filter === 'string') document.getElementById('catalogFilter').value = state.filter;
    if (typeof state.genre === 'string') document.getElementById('genreFilter').value = state.genre;
    if (typeof state.director === 'string') document.getElementById('directorFilter').value = state.director;
    if (typeof state.actor === 'string') document.getElementById('actorFilter').value = state.actor;
    if (typeof state.recent === 'string') document.getElementById('recentFilter').value = state.recent;
    filterCards();
    const hasAdvancedFilter = document.getElementById('catalogFilter').value !== 'all' || Boolean(document.getElementById('genreFilter').value) || Boolean(document.getElementById('directorFilter').value) || Boolean(document.getElementById('actorFilter').value) || Boolean(document.getElementById('recentFilter').value);
    toggleFilterPanel(typeof state.filterPanelOpen === 'boolean' ? state.filterPanelOpen : hasAdvancedFilter);
    if (Array.isArray(state.openDetails)) {{
      state.openDetails.forEach(id => {{
        const card = document.getElementById(id);
        const details = card ? card.querySelector('details') : null;
        if (details) details.open = true;
      }});
    }}
    requestAnimationFrame(() => {{
      const anchor = state.anchorId ? document.getElementById(state.anchorId) : null;
      if (anchor && anchor.style.display !== 'none' && Number.isFinite(state.anchorTop)) {{
        const delta = anchor.getBoundingClientRect().top - state.anchorTop;
        window.scrollBy(0, delta);
      }} else if (Number.isFinite(state.scrollY)) {{
        window.scrollTo(0, state.scrollY);
      }}
    }});
  }} catch (error) {{
    console.warn('View could not be restored:', error);
    filterCards();
  }}
}}

function escapeHtmlText(value) {{
  return String(value == null ? '' : value);
}}

function closeRandomMovie() {{
  const dialog = document.getElementById('randomDialog');
  if (dialog && dialog.open) dialog.close();
}}

function showRandomMovie() {{
  const allMovies = Array.from(document.querySelectorAll('.card[data-kind="movie"]'));
  if (!allMovies.length) {{
    alert(t('noMovies'));
    return;
  }}
  let candidates = allMovies.filter(card => card.style.display !== 'none');
  if (!candidates.length) candidates = allMovies;
  const card = candidates[Math.floor(Math.random() * candidates.length)];
  const mediaId = Number(card.dataset.mediaId || '0');

  document.getElementById('randomTitle').textContent = [card.dataset.title || '', card.dataset.year || ''].filter(Boolean).join(' · ');
  const rating = card.querySelector('.rating');
  document.getElementById('randomRating').textContent = rating ? rating.textContent.trim() : '';
  const facts = Array.from(card.querySelectorAll('.facts'))
    .map(element => element.textContent.trim())
    .filter(Boolean);
  document.getElementById('randomFacts').textContent = facts.join(' · ');
  const plot = card.querySelector('.content > p');
  document.getElementById('randomPlot').textContent = plot ? plot.textContent.trim() : '';

  const slot = document.getElementById('randomPosterSlot');
  slot.innerHTML = '';
  const cardPoster = card.querySelector('.poster-slot img');
  if (cardPoster && cardPoster.getAttribute('src')) {{
    const image = document.createElement('img');
    image.className = 'random-poster';
    image.src = cardPoster.getAttribute('src');
    image.alt = '';
    image.onerror = () => {{
      slot.innerHTML = '<div class="random-poster placeholder" data-i18n="noCover"></div>';
      applyLanguage(activeLanguage);
    }};
    slot.appendChild(image);
  }} else {{
    slot.innerHTML = '<div class="random-poster placeholder" data-i18n="noCover"></div>';
    applyLanguage(activeLanguage);
  }}

  const playButton = document.getElementById('randomPlayButton');
  playButton.disabled = false;
  playButton.textContent = t('playFilm');
  playButton.onclick = () => startMedia(mediaId, playButton, 'movie');

  const dialog = document.getElementById('randomDialog');
  if (dialog) {{
    if (typeof dialog.showModal === 'function') {{
      if (!dialog.open) dialog.showModal();
    }} else {{
      dialog.setAttribute('open', '');
    }}
  }}
}}

async function searchIMDbResults(mediaId, button) {{
  const target = document.getElementById('imdb-results-' + mediaId);
  if (!target) return;
  const originalText = button.textContent;
  button.disabled = true;
  button.textContent = t('imdbSearching');
  target.innerHTML = '';
  const status = document.createElement('div');
  status.className = 'imdb-search-status';
  status.textContent = t('imdbSearching');
  target.appendChild(status);

  try {{
    const response = await fetch('/imdb-search/' + mediaId, {{ cache: 'no-store' }});
    const payload = await response.json().catch(() => ({{}}));
    if (!response.ok || payload.ok === false) {{
      throw new Error(payload.error || t('imdbSearchFailed'));
    }}
    target.innerHTML = '';
    const results = Array.isArray(payload.results) ? payload.results : [];
    if (!results.length) {{
      const empty = document.createElement('div');
      empty.className = 'imdb-search-status';
      empty.textContent = t('imdbNoResults');
      target.appendChild(empty);
      return;
    }}

    results.slice(0, 10).forEach(result => {{
      const row = document.createElement('div');
      row.className = 'imdb-result';

      let poster;
      if (result.image) {{
        poster = document.createElement('img');
        poster.className = 'imdb-result-poster';
        poster.src = result.image;
        poster.alt = '';
        poster.loading = 'lazy';
      }} else {{
        poster = document.createElement('div');
        poster.className = 'imdb-result-poster placeholder-mini';
        poster.textContent = 'IMDb';
      }}
      row.appendChild(poster);

      const main = document.createElement('div');
      main.className = 'imdb-result-main';
      const titleLink = document.createElement('a');
      titleLink.className = 'imdb-result-title';
      titleLink.href = 'https://www.imdb.com/title/' + encodeURIComponent(result.imdb_id) + '/';
      titleLink.target = '_blank';
      titleLink.rel = 'noreferrer';
      titleLink.textContent = escapeHtmlText(result.title);
      main.appendChild(titleLink);

      const meta = document.createElement('div');
      meta.className = 'imdb-result-meta';
      const pieces = [];
      if (result.year) pieces.push(result.year);
      if (result.kind) pieces.push(result.kind);
      const idSpan = document.createElement('span');
      idSpan.className = 'imdb-result-id';
      idSpan.textContent = result.imdb_id;
      if (pieces.length) meta.appendChild(document.createTextNode(pieces.join(' · ') + ' · '));
      meta.appendChild(idSpan);
      main.appendChild(meta);

      if (result.subtitle) {{
        const subtitle = document.createElement('div');
        subtitle.className = 'imdb-result-subtitle';
        subtitle.textContent = escapeHtmlText(result.subtitle);
        main.appendChild(subtitle);
      }}
      row.appendChild(main);

      const form = document.createElement('form');
      form.method = 'post';
      form.action = '/correct/' + mediaId;
      form.className = 'imdb-assign-form';
      form.addEventListener('submit', () => saveViewState(form));
      const hidden = document.createElement('input');
      hidden.type = 'hidden';
      hidden.name = 'imdb';
      hidden.value = result.imdb_id;
      form.appendChild(hidden);
      const assign = document.createElement('button');
      assign.type = 'submit';
      assign.className = 'imdb-assign-button';
      assign.dataset.i18n = 'assignIMDb';
      assign.textContent = t('assignIMDb');
      form.appendChild(assign);
      row.appendChild(form);

      target.appendChild(row);
    }});
  }} catch (error) {{
    target.innerHTML = '';
    const failed = document.createElement('div');
    failed.className = 'imdb-search-status';
    failed.textContent = (error && error.message) ? error.message : t('imdbSearchFailed');
    target.appendChild(failed);
  }} finally {{
    button.disabled = false;
    button.textContent = originalText || t('searchIMDb');
    applyLanguage(activeLanguage);
  }}
}}

async function startMedia(mediaId, button, kind) {{
  const originalText = button.textContent;
  button.disabled = true;
  button.textContent = t('starting');
  try {{
    const response = await fetch('/play-media/' + mediaId, {{ method: 'POST' }});
    if (!response.ok) {{
      const message = await response.text();
      throw new Error(message || t('playFailed'));
    }}
    button.textContent = t('started');
    window.setTimeout(() => {{ button.textContent = t(kind === 'series' ? 'openFolder' : 'playFilm'); button.disabled = false; }}, 1200);
  }} catch (error) {{
    button.textContent = originalText;
    button.disabled = false;
    alert(error.message || String(error));
  }}
}}

async function openConfigDialog() {{
  const dialog = document.getElementById('configDialog');
  const status = document.getElementById('configStatus');
  if (status) {{ status.textContent = ''; status.className = 'config-status'; }}
  if (dialog) {{
    if (typeof dialog.showModal === 'function') {{
      if (!dialog.open) dialog.showModal();
    }} else {{
      dialog.setAttribute('open', '');
    }}
  }}
  try {{
    const response = await fetch('/config-data', {{cache:'no-store'}});
    const payload = await response.json().catch(() => ({{}}));
    if (!response.ok || payload.ok === false || !payload.config) {{
      throw new Error(payload.error || t('configLoadFailed'));
    }}
    const cfg = payload.config;
    document.getElementById('cfgApiKey').value = cfg['API-Key'] || '';
    document.getElementById('cfgMaxRequests').value = String(cfg['Max-Requests'] || '');
    document.getElementById('cfgStartupLanguage').value = cfg['Startup-Language'] === 'en' ? 'en' : 'de';
    document.getElementById('cfgScanStartup').value = cfg['Scan-On-Startup'] ? 'yes' : 'no';
    document.getElementById('cfgMoviesPath').value = cfg['Movies-Path'] || '';
    document.getElementById('cfgSeriesPath').value = cfg['Series-Path'] || '';
  }} catch (error) {{
    if (status) {{
      status.textContent = (error && error.message) ? error.message : t('configLoadFailed');
      status.className = 'config-status error';
    }}
  }}
}}

function closeConfigDialog() {{
  const dialog = document.getElementById('configDialog');
  if (!dialog) return;
  if (typeof dialog.close === 'function' && dialog.open) dialog.close();
  else dialog.removeAttribute('open');
}}

async function saveConfig(event) {{
  event.preventDefault();
  const button = document.getElementById('configSaveButton');
  const status = document.getElementById('configStatus');
  const originalText = button ? button.textContent : '';
  const payload = {{
    'API-Key': document.getElementById('cfgApiKey').value.trim(),
    'Max-Requests': Number(document.getElementById('cfgMaxRequests').value),
    'Startup-Language': document.getElementById('cfgStartupLanguage').value,
    'Scan-On-Startup': document.getElementById('cfgScanStartup').value === 'yes',
    'Movies-Path': document.getElementById('cfgMoviesPath').value.trim(),
    'Series-Path': document.getElementById('cfgSeriesPath').value.trim()
  }};
  if (button) {{ button.disabled = true; button.textContent = t('savingConfig'); }}
  if (status) {{ status.textContent = ''; status.className = 'config-status'; }}
  try {{
    const response = await fetch('/config', {{
      method:'POST',
      headers:{{'Content-Type':'application/json'}},
      body:JSON.stringify(payload),
      cache:'no-store'
    }});
    const result = await response.json().catch(() => ({{}}));
    if (!response.ok || result.ok === false) {{
      throw new Error(result.error || t('configSaveFailed'));
    }}
    if (status) {{ status.textContent = t('configSaved'); status.className = 'config-status ok'; }}
    try {{ sessionStorage.setItem(LANGUAGE_KEY, payload['Startup-Language'] === 'en' ? 'en' : 'de'); }} catch (_) {{}}
    saveViewState(null);
    window.setTimeout(() => window.location.reload(), 350);
  }} catch (error) {{
    if (status) {{ status.textContent = (error && error.message) ? error.message : t('configSaveFailed'); status.className = 'config-status error'; }}
    if (button) {{ button.disabled = false; button.textContent = originalText || t('saveConfig'); }}
  }}
}}

(function initializeCatalog() {{
  let savedLanguage = 'de';
  try {{ savedLanguage = sessionStorage.getItem(LANGUAGE_KEY) || CONFIG_STARTUP_LANGUAGE; }} catch (_) {{ savedLanguage = CONFIG_STARTUP_LANGUAGE; }}
  applyLanguage(savedLanguage);
  restoreViewState();
  refreshServerStatus();
  window.setInterval(refreshServerStatus, 15000);
}})();
</script>
</body>
</html>"""


class CatalogWebHandler(BaseHTTPRequestHandler):
    server_version = "MedienKatalog/4.12"

    def _send_html(self, content: str, status: int = 200) -> None:
        payload = content.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(payload)

    def _send_text(self, content: str, status: int = 200) -> None:
        payload = content.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(payload)

    def _send_json(self, data: dict[str, Any], status: int = 200) -> None:
        payload = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(payload)

    def _send_binary(self, payload: bytes, content_type: str, status: int = 200) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Cache-Control", "public, max-age=86400")
        self.end_headers()
        self.wfile.write(payload)

    def _send_download(self, payload: bytes, content_type: str, filename: str) -> None:
        safe_name = re.sub(r"[^A-Za-z0-9_.-]+", "_", filename).strip("._") or "Medienkatalog.pdf"
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Content-Disposition", f'attachment; filename="{safe_name}"')
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(payload)

    def _json_body(self) -> dict[str, Any]:
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            length = 0
        if length <= 0 or length > 2 * 1024 * 1024:
            return {}
        raw = self.rfile.read(length).decode("utf-8", errors="replace")
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            return {}
        return data if isinstance(data, dict) else {}

    def _redirect(self, location: str = "/") -> None:
        self.send_response(303)
        self.send_header("Location", location)
        self.end_headers()

    def _form(self) -> dict[str, list[str]]:
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            length = 0
        body = self.rfile.read(min(length, 64 * 1024)).decode("utf-8", errors="replace")
        return parse_qs(body, keep_blank_values=True)

    @property
    def app(self) -> Any:
        return self.server.app  # type: ignore[attr-defined]

    def do_GET(self) -> None:
        path = self.path.split("?", 1)[0]
        if path == "/config-data":
            cfg = load_app_config()
            self._send_json({
                "ok": True,
                "config": {
                    "API-Key": str(cfg.get("API-Key") or ""),
                    "Max-Requests": int(cfg.get("Max-Requests") or OMDB_DAILY_LIMIT),
                    "Startup-Language": str(cfg.get("Startup-Language") or "de"),
                    "Scan-On-Startup": bool(cfg.get("Scan-On-Startup", True)),
                    "Movies-Path": str(cfg.get("Movies-Path") or DEFAULT_MOVIES_SOURCE),
                    "Series-Path": str(cfg.get("Series-Path") or DEFAULT_SERIES_SOURCE),
                },
            })
            return
        if path == "/server-status":
            online, host = configured_server_status(self.app.args)
            self._send_json({"ok": True, "online": online, "host": host})
            return
        if path == "/background":
            image_path = background_image_path()
            if image_path is None:
                self.send_error(404, "Hintergrundbild nicht verfügbar")
                return
            try:
                payload = image_path.read_bytes()
            except OSError:
                self.send_error(404, "Hintergrundbild nicht verfügbar")
                return
            content_type = "image/png" if image_path.suffix.casefold() == ".png" else "image/jpeg"
            self._send_binary(payload, content_type)
            return
        match = re.fullmatch(r"/poster/(\d+)", path)
        if match:
            try:
                payload, content_type = poster_for_database_item(self.app.args, int(match.group(1)))
                self._send_binary(payload, content_type)
            except (CatalogError, OSError, sqlite3.Error):
                self.send_error(404, "Cover nicht verfügbar")
            return
        match = re.fullmatch(r"/imdb-search/(\d+)", path)
        if match:
            try:
                query, results = imdb_search_for_database_item(self.app.args, int(match.group(1)))
                self._send_json({"ok": True, "query": query, "results": results})
            except (CatalogError, OSError, sqlite3.Error) as exc:
                self._send_json({"ok": False, "error": str(exc)}, 400)
            return
        if path != "/":
            self.send_error(404)
            return
        self._send_html(render_web_catalog(self.app.args))

    def do_POST(self) -> None:
        path = self.path.split("?", 1)[0]
        try:
            if path == "/config":
                data = self._json_body()
                values = {
                    "API-Key": data.get("API-Key", ""),
                    "Max-Requests": data.get("Max-Requests", OMDB_DAILY_LIMIT),
                    "Startup-Language": data.get("Startup-Language", "de"),
                    "Scan-On-Startup": data.get("Scan-On-Startup", True),
                    "Movies-Path": data.get("Movies-Path", ""),
                    "Series-Path": data.get("Series-Path", ""),
                }
                config = save_app_config(values)
                self.app.apply_config(config)
                self._send_json({
                    "ok": True,
                    "config": {
                        "API-Key": config["API-Key"],
                        "Max-Requests": config["Max-Requests"],
                        "Startup-Language": config["Startup-Language"],
                        "Scan-On-Startup": config["Scan-On-Startup"],
                        "Movies-Path": config["Movies-Path"],
                        "Series-Path": config["Series-Path"],
                    },
                })
                return

            if path == "/export-pdf":
                data = self._json_body()
                raw_ids = data.get("ids", [])
                if not isinstance(raw_ids, list):
                    raise CatalogError("Ungültige Titelauswahl für den PDF-Export.")
                ids: list[int] = []
                for value in raw_ids:
                    try:
                        media_id = int(value)
                    except (TypeError, ValueError):
                        continue
                    if media_id > 0:
                        ids.append(media_id)
                language = "en" if str(data.get("language", "de")) == "en" else "de"
                payload = generate_catalog_pdf(self.app.args, ids, language=language)
                stamp = datetime.now().astimezone().strftime("%Y-%m-%d_%H%M")
                self._send_download(payload, "application/pdf", f"Medienkatalog_{stamp}.pdf")
                return

            match = re.fullmatch(r"/play-media/(\d+)", path)
            if match:
                media_file = start_media(self.app.args, int(match.group(1)))
                self._send_text(media_file)
                return

            if path == "/scan":
                ajax_scan = self.headers.get("X-Requested-With") == "MedienKatalog"
                if not self.app.scan_lock.acquire(blocking=False):
                    if ajax_scan:
                        self._send_json({"ok": False, "error": "Ein Scan läuft bereits."}, 409)
                    else:
                        self._send_html(render_web_catalog(self.app.args, error="Ein Scan läuft bereits."), 409)
                    return
                try:
                    count, removed, api_requests, reused_metadata = scan_into_database(
                        self.app.args,
                        password=self.app.password,
                        omdb_key=self.app.omdb_key,
                    )
                finally:
                    self.app.scan_lock.release()
                if ajax_scan:
                    self._send_json({
                        "ok": True,
                        "count": count,
                        "removed": removed,
                        "omdb_requests": api_requests,
                        "reused_metadata": reused_metadata,
                    })
                else:
                    self._send_html(
                        render_web_catalog(
                            self.app.args,
                            notice=(
                                f"Scan abgeschlossen: {count} Titel vorhanden, {removed} veraltete Einträge entfernt. "
                                f"OMDb-Aufrufe: {api_requests}; aus SQLite übernommen: {reused_metadata}."
                            ),
                        )
                    )
                return

            match = re.fullmatch(r"/correct/(\d+)", path)
            if match:
                form = self._form()
                value = form.get("imdb", [""])[0]
                imdb_id = correct_database_item(
                    self.app.args,
                    int(match.group(1)),
                    value,
                    omdb_key=self.app.omdb_key,
                )
                self._send_html(
                    render_web_catalog(self.app.args, notice=f"Zuordnung auf {imdb_id} korrigiert.")
                )
                return

            match = re.fullmatch(r"/kids/(\d+)", path)
            if match:
                form = self._form()
                value = form.get("value", ["0"])[0] == "1"
                set_kids_flag(self.app.args, int(match.group(1)), value)
                self._send_html(
                    render_web_catalog(
                        self.app.args,
                        notice="Kinder-Markierung gespeichert." if value else "Kinder-Markierung entfernt.",
                    )
                )
                return

            match = re.fullmatch(r"/reset/(\d+)", path)
            if match:
                reset_database_item_mapping(self.app.args, int(match.group(1)))
                self._send_html(
                    render_web_catalog(
                        self.app.args,
                        notice="Manuelle Zuordnung entfernt. Beim nächsten Scan greift wieder die automatische Suche.",
                    )
                )
                return

            self.send_error(404)
        except (CatalogError, OmdbFatalError, OSError, sqlite3.Error) as exc:
            if path == "/config":
                self._send_json({"ok": False, "error": str(exc)}, 400)
            elif path.startswith("/play-media/") or path == "/export-pdf":
                self._send_text(str(exc), 400)
            elif path == "/scan" and self.headers.get("X-Requested-With") == "MedienKatalog":
                self._send_json({"ok": False, "error": str(exc)}, 400)
            else:
                self._send_html(render_web_catalog(self.app.args, error=str(exc)), 400)

    def log_message(self, format: str, *args: Any) -> None:
        if not self.app.args.ruhig:
            super().log_message(format, *args)


@dataclass
class WebAppContext:
    args: argparse.Namespace
    password: str | None
    omdb_key: str
    scan_lock: threading.Lock = field(default_factory=threading.Lock)

    def apply_config(self, config: dict[str, Any]) -> None:
        global OMDB_DAILY_LIMIT
        self.omdb_key = str(config.get("API-Key") or "").strip()
        OMDB_DAILY_LIMIT = int(config.get("Max-Requests") or OMDB_DAILY_LIMIT)
        self.args.omdb_key = self.omdb_key
        self.args.startup_language = str(config.get("Startup-Language") or "de")
        self.args.scan_on_startup = bool(config.get("Scan-On-Startup", True))
        self.args.movies_path = str(config.get("Movies-Path") or DEFAULT_MOVIES_SOURCE)
        self.args.series_path = str(config.get("Series-Path") or DEFAULT_SERIES_SOURCE)
        self.args.quelle = configured_source_summary(self.args)


def choose_startup_scan() -> bool | None:
    """Beim normalen Windows-Start fragen, ob vor dem Öffnen gescannt werden soll.

    True = aktualisieren, False = vorhandene DB sofort öffnen, None = Start abbrechen.
    """
    if os.name == "nt":
        try:
            import tkinter as tk
            from tkinter import messagebox

            root = tk.Tk()
            root.withdraw()
            try:
                root.attributes("-topmost", True)
            except tk.TclError:
                pass
            answer = messagebox.askyesnocancel(
                "Medienkatalog",
                "Soll die Bibliothek vor dem Öffnen aktualisiert werden?\n\n"
                "Ja = Netzlaufwerk scannen und Datenbank aktualisieren\n"
                "Nein = vorhandene Datenbank sofort öffnen\n"
                "Abbrechen = Programm nicht starten",
                parent=root,
            )
            root.destroy()
            return answer
        except Exception as exc:
            # Falls Tkinter in der Python-Installation fehlt, auf Konsole zurückfallen.
            if sys.stdin.isatty():
                print(f"Hinweis: Windows-Auswahldialog nicht verfügbar ({exc}).")

    if sys.stdin.isatty():
        while True:
            answer = input("Bibliothek beim Start aktualisieren? [J]a / [N]ein / [A]bbrechen: ").strip().casefold()
            if answer in {"j", "ja", "y", "yes"}:
                return True
            if answer in {"n", "nein", "no"}:
                return False
            if answer in {"a", "abbrechen", "c", "cancel", "q"}:
                return None

    # Ohne Dialog und ohne interaktives Terminal lieber die vorhandene DB öffnen,
    # statt unerwartet einen möglicherweise langen Netzwerkscan zu starten.
    return False


def run_web_app(args: argparse.Namespace, *, password: str | None, omdb_key: str) -> int:
    # Datenbank schon vor dem ersten HTTP-Aufruf initialisieren.
    connection = open_database(args.db)
    connection.close()

    if not args.kein_startscan:
        try:
            count, removed, api_requests, reused_metadata = scan_into_database(
                args, password=password, omdb_key=omdb_key
            )
            if not args.ruhig:
                print(
                    f"Startscan abgeschlossen: {count} Titel, {removed} entfernt, "
                    f"{api_requests} OMDb-Aufrufe, {reused_metadata} aus SQLite übernommen.",
                    file=sys.stderr,
                )
        except (CatalogError, OmdbFatalError, OSError, sqlite3.Error) as exc:
            print(f"Warnung: Startscan fehlgeschlagen: {exc}", file=sys.stderr)

    context = WebAppContext(args=args, password=password, omdb_key=omdb_key)
    server = ThreadingHTTPServer((args.host, args.port), CatalogWebHandler)
    server.app = context  # type: ignore[attr-defined]
    shown_host = "127.0.0.1" if args.host in {"0.0.0.0", "::"} else args.host
    catalog_url = f"http://{shown_host}:{args.port}/"
    print(f"Medienkatalog läuft unter {catalog_url}")
    print("Beenden mit Strg+C.")

    # Beim Desktop-Start wird der Standardbrowser plattformneutral geöffnet.
    # Der kleine Timer verhindert, dass der erste Aufruf vor dem Serverstart erfolgt.
    if not args.kein_browser:
        def open_catalog_in_browser() -> None:
            try:
                if os.name == "nt" and hasattr(os, "startfile"):
                    os.startfile(catalog_url)  # type: ignore[attr-defined]
                else:
                    webbrowser.open(catalog_url, new=2)
            except Exception as exc:
                if not args.ruhig:
                    print(f"Warnung: Browser konnte nicht automatisch geöffnet werden: {exc}", file=sys.stderr)

        timer = threading.Timer(0.4, open_catalog_in_browser)
        timer.daemon = True
        timer.start()

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
    return 0

def parse_args(argv: Sequence[str] | None = None, *, app_config: dict[str, Any] | None = None) -> argparse.Namespace:
    app_config = app_config or load_app_config()
    parser = argparse.ArgumentParser(
        description=(
            "Durchsucht einen lokalen Medienordner oder eine SMB-Freigabe und ergänzt "
            "IMDb-Bewertung sowie Kurzbeschreibung über OMDb."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent(
            """
            Beispiele:
              python medien_katalog_web_v4_13.py --web
              python medien_katalog_web_v4_13.py --filme-pfad "D:\\Medien\\Filme" --serien-pfad "D:\\Medien\\Serien" --csv katalog.csv
              python medien_katalog_web_v4_13.py --ohne-metadaten --pfade

            Standardquelle:
              \\\\192.168.2.208\\Multimedia
              Rekursiv ausgewertet werden nur die Bereiche Filme und Serien.

            Konfiguration:
              config.txt neben dem Skript: API-Key, Max-Requests, Startup-Language,
              Scan-On-Startup, Movies-Path und Series-Path.

            Umgebungsvariablen:
              SMB_BENUTZER  Benutzername für eine smb://-Freigabe (optional)
              SMB_PASSWORT  Passwort; fehlt es im Terminal, wird sicher nachgefragt
            """
        ),
    )
    parser.add_argument(
        "--quelle",
        default=None,
        help="Legacy: gemeinsamer Medien-Stammordner; daraus werden Filme/Serien abgeleitet",
    )
    parser.add_argument(
        "--filme-pfad",
        dest="movies_path",
        default=str(app_config.get("Movies-Path") or DEFAULT_MOVIES_SOURCE),
        help="Pfad zum Filmordner",
    )
    parser.add_argument(
        "--serien-pfad",
        dest="series_path",
        default=str(app_config.get("Series-Path") or DEFAULT_SERIES_SOURCE),
        help="Pfad zum Serienordner",
    )
    parser.add_argument(
        "--benutzer",
        default=os.environ.get("SMB_BENUTZER"),
        help="SMB-Benutzername (Standard: SMB_BENUTZER)",
    )
    parser.add_argument("--smb-timeout", type=int, default=20, help="SMB-Verbindungs-Timeout in Sekunden")
    parser.add_argument(
        "--oeffentliche-adresse-erlauben",
        action="store_true",
        help="Auch nicht-lokale SMB-Adressen zulassen (standardmäßig aus Sicherheitsgründen gesperrt)",
    )
    parser.add_argument(
        "--nur",
        choices=("alle", "filme", "serien"),
        default="alle",
        help="Ergebnisse nach Medientyp filtern (Standard: alle)",
    )
    parser.add_argument(
        "--ohne-metadaten",
        action="store_true",
        help="Keine OMDb-Anfragen senden; nur erkannte Titel anzeigen",
    )
    parser.add_argument(
        "--cache",
        type=Path,
        default=default_cache_path(),
        help="Pfad zum OMDb-Cache",
    )
    parser.add_argument(
        "--cache-tage",
        type=int,
        default=7,
        help="Metadaten so viele Tage aus dem Cache verwenden (Standard: 7)",
    )
    parser.add_argument(
        "--max-titel",
        type=int,
        default=0,
        help="Höchstens so viele Titel verarbeiten; 0 bedeutet unbegrenzt",
    )
    parser.add_argument("--csv", type=Path, help="Zusätzlich als semikolongetrennte UTF-8-CSV speichern")
    parser.add_argument("--json", type=Path, help="Zusätzlich als JSON speichern")
    parser.add_argument("--db", type=Path, default=default_database_path(), help="SQLite-Datenbank für den Webkatalog")
    parser.add_argument("--web", action="store_true", help="Lokale HTML-Weboberfläche starten")
    parser.add_argument("--host", default="127.0.0.1", help="Webserver-Adresse (Standard: 127.0.0.1)")
    parser.add_argument("--port", type=int, default=8090, help="Webserver-Port (Standard: 8090)")
    parser.add_argument(
        "--kein-browser",
        action="store_true",
        help="Im Webmodus den Browser unter Windows nicht automatisch öffnen",
    )
    parser.add_argument("--kein-startscan", action="store_true", help="Im Webmodus nicht automatisch beim Start scannen")
    parser.add_argument("--pfade", action="store_true", help="Fundorte in der Konsolenausgabe anzeigen")
    parser.add_argument("--ruhig", action="store_true", help="Fortschrittsmeldungen unterdrücken")
    parser.add_argument("--version", action="version", version=f"%(prog)s {VERSION}")

    args = parser.parse_args(argv)
    if args.quelle:
        args.movies_path = _join_media_child(args.quelle, "Filme")
        args.series_path = _join_media_child(args.quelle, "Serien")
    # ``quelle`` bleibt als rein informative Legacy-Eigenschaft erhalten.
    args.quelle = configured_source_summary(args)
    if args.smb_timeout < 1:
        parser.error("--smb-timeout muss mindestens 1 sein")
    if args.cache_tage < 0:
        parser.error("--cache-tage darf nicht negativ sein")
    if args.max_titel < 0:
        parser.error("--max-titel darf nicht negativ sein")
    if not 1 <= args.port <= 65535:
        parser.error("--port muss zwischen 1 und 65535 liegen")
    return args


def main(argv: Sequence[str] | None = None) -> int:
    # Ein Doppelklick/Launcher-Aufruf ohne Argumente startet unter Windows und
    # Desktop-Linux automatisch die Weboberfläche. CLI-Aufrufe
    # mit Optionen behalten weiterhin ihr bisheriges Verhalten.
    app_config = load_app_config()
    global OMDB_DAILY_LIMIT
    OMDB_DAILY_LIMIT = int(app_config.get("Max-Requests") or 100000)

    effective_argv = list(sys.argv[1:] if argv is None else argv)
    launched_without_arguments = not effective_argv
    args = parse_args(effective_argv, app_config=app_config)
    args.startup_language = str(app_config.get("Startup-Language") or "de")
    args.scan_on_startup = bool(app_config.get("Scan-On-Startup", True))
    args.omdb_key = str(app_config.get("API-Key") or "").strip()
    if launched_without_arguments:
        # Doppelklick/Launcher ohne Argumente: auf Windows und Desktop-Linux
        # identisch behandeln und direkt die Weboberfläche starten.
        args.web = True
        args.kein_startscan = not bool(app_config.get("Scan-On-Startup", True))
    password = os.environ.get("SMB_PASSWORT")
    if any(source.casefold().startswith("smb://") for source, _kind in configured_media_sources(args)) and args.benutzer and password is None:
        if sys.stdin.isatty():
            password = getpass.getpass(f"SMB-Passwort für {args.benutzer}: ")
        else:
            print(
                "Fehler: SMB_PASSWORT fehlt und es steht kein interaktives Terminal zur Verfügung.",
                file=sys.stderr,
            )
            return 2

    omdb_key = str(app_config.get("API-Key") or os.environ.get("OMDB_API_KEY", DEFAULT_OMDB_API_KEY)).strip()
    args.omdb_key = omdb_key
    if not args.ohne_metadaten and not omdb_key:
        print(
            "Fehler: OMDB_API_KEY ist nicht gesetzt. Einen Schlüssel gibt es unter "
            "https://www.omdbapi.com/apikey.aspx. Für einen reinen Scan nutze --ohne-metadaten.",
            file=sys.stderr,
        )
        return 2

    if args.web:
        return run_web_app(args, password=password, omdb_key=omdb_key)

    if not args.ruhig:
        print("Durchsuche Medienquelle …", file=sys.stderr)

    try:
        candidates = iter_configured_candidates(args, password=password)
        items = merge_candidates(candidates, only=args.nur)
    except CatalogError as exc:
        print(f"Fehler: {exc}", file=sys.stderr)
        return 2

    if args.max_titel and len(items) > args.max_titel:
        if not args.ruhig:
            print(
                f"Hinweis: {len(items)} Titel erkannt; --max-titel begrenzt die Verarbeitung auf "
                f"{args.max_titel}.",
                file=sys.stderr,
            )
        items = items[: args.max_titel]

    if not items:
        print("Keine Film- oder Seriendateien gefunden.")
        return 0

    client = None if args.ohne_metadaten else OmdbClient(omdb_key, args.cache, args.cache_tage)
    records: list[CatalogRecord] = []

    try:
        for index, item in enumerate(items, start=1):
            if not args.ruhig and client:
                print(f"OMDb {index}/{len(items)}: {item.title}", file=sys.stderr)
            metadata: dict[str, Any] | None = None
            if client:
                try:
                    metadata = client.lookup(item)
                except OmdbTemporaryError as exc:
                    print(f"Warnung bei {item.title!r}: {exc}", file=sys.stderr)
                except OmdbFatalError:
                    raise
            records.append(record_from_item(item, metadata, lookup_attempted=client is not None))
    except OmdbFatalError as exc:
        print(f"Fehler: {exc}", file=sys.stderr)
        return 2
    finally:
        if client:
            client.save_cache()

    if client:
        usage_connection = open_database(args.db)
        try:
            add_omdb_usage(
                usage_connection,
                omdb_key,
                client.request_count,
                limit_reached=client.limit_reached,
            )
            usage_connection.commit()
        finally:
            usage_connection.close()

    records.sort(key=lambda record: (record.art, normalized_words(record.titel), record.jahr))
    print_catalog(records, show_paths=args.pfade)

    try:
        if args.csv:
            write_csv(args.csv, records)
            print(f"CSV gespeichert: {args.csv.expanduser().resolve()}")
        if args.json:
            write_json(args.json, records)
            print(f"JSON gespeichert: {args.json.expanduser().resolve()}")
    except OSError as exc:
        print(f"Fehler beim Speichern der Ausgabe: {exc}", file=sys.stderr)
        return 2

    return 0


if __name__ == "__main__":
    # Bei einem Windows-Doppelklick verschwindet ein Konsolenfenster bei einem
    # Startfehler sonst sofort. In diesem Fall bleibt die Fehlermeldung sichtbar.
    double_click_start = os.name == "nt" and len(sys.argv) == 1
    try:
        exit_code = main()
    except Exception as exc:
        if not double_click_start:
            raise
        print(f"Unerwarteter Startfehler: {type(exc).__name__}: {exc}", file=sys.stderr)
        exit_code = 2

    if double_click_start and exit_code != 0:
        try:
            input("\nZum Schließen Enter drücken …")
        except (EOFError, OSError):
            pass
    raise SystemExit(exit_code)
