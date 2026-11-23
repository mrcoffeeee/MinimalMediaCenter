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
import base64
import csv
import copy
import difflib
import getpass
import hashlib
import html
import ipaddress
import json
import secrets
import struct
import os
import re
import socket
import shutil
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


VERSION = "4.15.44"
OMDB_ENDPOINT = "https://www.omdbapi.com/"
IMDB_SUGGEST_ENDPOINT = "https://v3.sg.media-imdb.com/suggestion/titles/x/"
IMDB_GRAPHQL_ENDPOINT = "https://caching.graphql.imdb.com/"
DEFAULT_OMDB_API_KEY = "fae48dc5"
OMDB_DAILY_LIMIT = 100000  # Wird beim Start aus config.txt überschrieben.
# Platform-specific defaults. The current media server is reachable as a UNC share
# under Windows and as an SMB URI under desktop Linux. Existing config.txt files
# with only Movies-Path/Series-Path remain fully supported.
DEFAULT_WINDOWS_MEDIA_SOURCE = r"\\169.254.100.100\Multimedia"
DEFAULT_LINUX_MEDIA_SOURCE = "smb://169.254.100.100/Multimedia"
DEFAULT_WINDOWS_MOVIES_SOURCE = DEFAULT_WINDOWS_MEDIA_SOURCE + r"\Filme"
DEFAULT_WINDOWS_SERIES_SOURCE = DEFAULT_WINDOWS_MEDIA_SOURCE + r"\Serien"
DEFAULT_LINUX_MOVIES_SOURCE = DEFAULT_LINUX_MEDIA_SOURCE + "/Filme"
DEFAULT_LINUX_SERIES_SOURCE = DEFAULT_LINUX_MEDIA_SOURCE + "/Serien"
DEFAULT_MEDIA_SOURCE = DEFAULT_WINDOWS_MEDIA_SOURCE if os.name == "nt" else DEFAULT_LINUX_MEDIA_SOURCE
DEFAULT_MOVIES_SOURCE = DEFAULT_WINDOWS_MOVIES_SOURCE if os.name == "nt" else DEFAULT_LINUX_MOVIES_SOURCE
DEFAULT_SERIES_SOURCE = DEFAULT_WINDOWS_SERIES_SOURCE if os.name == "nt" else DEFAULT_LINUX_SERIES_SOURCE
CONFIG_FILENAME = "config.txt"
DEFAULT_STARTUP_LANGUAGE = "de"
DEFAULT_SCAN_ON_STARTUP = True


def config_path() -> Path:
    """Persistente Konfiguration im data-Unterordner."""
    return data_directory() / CONFIG_FILENAME


def _unc_to_smb_uri(target: str) -> str:
    r"""Convert a Windows UNC path into an SMB URI understood by Linux desktops."""
    value = str(target or "").strip()
    if not value.startswith("\\\\"):
        return value
    parts = [part for part in value.lstrip("\\").split("\\") if part]
    if len(parts) < 2:
        return value
    host = quote(parts[0], safe="[]:.-_~")
    path = "/".join(quote(part, safe="!$&'()*+,;=:@-._~") for part in parts[1:])
    return f"smb://{host}/{path}"


def _smb_uri_to_unc(target: str) -> str:
    """Convert smb://server/share/path into a Windows UNC path."""
    value = str(target or "").strip()
    if not value.casefold().startswith("smb://"):
        return value
    try:
        parsed = urlsplit(value)
    except ValueError:
        return value
    if not parsed.hostname:
        return value
    parts = [unquote(part) for part in parsed.path.split("/") if part]
    if not parts:
        return value
    return "\\\\" + parsed.hostname + "\\" + "\\".join(parts)


def _platform_media_path(value: str, *, platform: str | None = None) -> str:
    """Return a media path in the native form for Windows or desktop Linux.

    Windows prefers UNC paths, Linux/macOS prefers smb:// for network shares.
    Normal local POSIX paths are left untouched on non-Windows systems.
    """
    raw = str(value or "").strip()
    platform = platform or ("windows" if os.name == "nt" else "linux")
    if platform == "windows":
        return _smb_uri_to_unc(raw)
    return _unc_to_smb_uri(raw)


def _active_platform_paths(config: dict[str, Any]) -> tuple[str, str]:
    """Select the configured Windows or Linux roots for the current OS."""
    if os.name == "nt":
        movies = str(config.get("Windows-Movies-Path") or config.get("Movies-Path") or DEFAULT_WINDOWS_MOVIES_SOURCE)
        series = str(config.get("Windows-Series-Path") or config.get("Series-Path") or DEFAULT_WINDOWS_SERIES_SOURCE)
        return _platform_media_path(movies, platform="windows"), _platform_media_path(series, platform="windows")
    movies = str(config.get("Linux-Movies-Path") or config.get("Movies-Path") or DEFAULT_LINUX_MOVIES_SOURCE)
    series = str(config.get("Linux-Series-Path") or config.get("Series-Path") or DEFAULT_LINUX_SERIES_SOURCE)
    return _platform_media_path(movies, platform="linux"), _platform_media_path(series, platform="linux")


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
    """Validate settings and derive platform-specific media roots.

    Older config files containing only Movies-Path/Series-Path are migrated in
    memory automatically: UNC becomes smb:// on Linux, smb:// becomes UNC on
    Windows. New config files may store explicit paths for both operating systems.
    """
    seen_keys = seen_keys or set(values)
    legacy_media = str(values.get("Media-Path") or DEFAULT_WINDOWS_MEDIA_SOURCE).strip() or DEFAULT_WINDOWS_MEDIA_SOURCE

    try:
        limit = int(str(values.get("Max-Requests", OMDB_DAILY_LIMIT)).replace(".", "").replace(" ", ""))
        if limit < 1:
            raise ValueError
    except (TypeError, ValueError):
        raise CatalogError("Max-Requests muss eine positive ganze Zahl sein.")

    language = str(values.get("Startup-Language", DEFAULT_STARTUP_LANGUAGE)).strip().casefold()
    aliases = {"de":"de","deutsch":"de","german":"de","en":"en","english":"en","englisch":"en","es":"es","espanol":"es","español":"es","spanish":"es","spanisch":"es"}
    if language not in aliases:
        raise CatalogError("Startup-Language muss de, en oder es sein.")

    raw_scan = values.get("Scan-On-Startup", DEFAULT_SCAN_ON_STARTUP)
    if isinstance(raw_scan, bool):
        scan = raw_scan
    else:
        scan_text = str(raw_scan).strip().casefold()
        if scan_text in {"yes","y","ja","j","true","1","on"}:
            scan = True
        elif scan_text in {"no","n","nein","false","0","off"}:
            scan = False
        else:
            raise CatalogError("Scan-On-Startup muss Yes oder No sein.")

    generic_movies = str(values.get("Movies-Path") or "").strip()
    generic_series = str(values.get("Series-Path") or "").strip()
    if not generic_movies:
        generic_movies = _join_media_child(legacy_media, "Filme")
    if not generic_series:
        generic_series = _join_media_child(legacy_media, "Serien")

    windows_movies = str(values.get("Windows-Movies-Path") or "").strip()
    windows_series = str(values.get("Windows-Series-Path") or "").strip()
    linux_movies = str(values.get("Linux-Movies-Path") or "").strip()
    linux_series = str(values.get("Linux-Series-Path") or "").strip()

    if not windows_movies:
        windows_movies = _platform_media_path(generic_movies, platform="windows")
    if not windows_series:
        windows_series = _platform_media_path(generic_series, platform="windows")
    if not linux_movies:
        linux_movies = _platform_media_path(generic_movies, platform="linux")
    if not linux_series:
        linux_series = _platform_media_path(generic_series, platform="linux")

    if not windows_movies or not windows_series or not linux_movies or not linux_series:
        raise CatalogError("Die Medienpfade dürfen nicht leer sein.")

    normalized = {
        "API-Key": str(values.get("API-Key") or "").strip(),
        "Max-Requests": limit,
        "Startup-Language": aliases[language],
        "Scan-On-Startup": scan,
        "Windows-Movies-Path": windows_movies,
        "Windows-Series-Path": windows_series,
        "Linux-Movies-Path": linux_movies,
        "Linux-Series-Path": linux_series,
        "Media-Path": legacy_media,
    }
    active_movies, active_series = _active_platform_paths(normalized)
    normalized["Movies-Path"] = active_movies
    normalized["Series-Path"] = active_series
    return normalized

def load_app_config() -> dict[str, Any]:
    """Einfache Key=Value-Konfiguration aus config.txt laden.

    Die aktuellen Schlüssel sind API-Key, Max-Requests, Startup-Language,
    Scan-On-Startup sowie getrennte Windows-/Linux-Medienpfade. ``Media-Path`` wird weiterhin
    gelesen, damit ältere config.txt-Dateien automatisch funktionieren.
    """
    raw: dict[str, Any] = {
        "API-Key": DEFAULT_OMDB_API_KEY,
        "Max-Requests": OMDB_DAILY_LIMIT,
        "Startup-Language": DEFAULT_STARTUP_LANGUAGE,
        "Scan-On-Startup": "Yes" if DEFAULT_SCAN_ON_STARTUP else "No",
        "Media-Path": DEFAULT_WINDOWS_MEDIA_SOURCE,
    }
    known = {
        "API-Key", "Max-Requests", "Startup-Language", "Scan-On-Startup",
        "Movies-Path", "Series-Path", "Media-Path",
        "Windows-Movies-Path", "Windows-Series-Path",
        "Linux-Movies-Path", "Linux-Series-Path",
    }
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
            "Media-Path": DEFAULT_WINDOWS_MEDIA_SOURCE,
            "Windows-Movies-Path": DEFAULT_WINDOWS_MOVIES_SOURCE,
            "Windows-Series-Path": DEFAULT_WINDOWS_SERIES_SOURCE,
            "Linux-Movies-Path": DEFAULT_LINUX_MOVIES_SOURCE,
            "Linux-Series-Path": DEFAULT_LINUX_SERIES_SOURCE,
        }
        return _normalize_app_config(fallback, seen_keys=set(fallback))


def save_app_config(values: dict[str, Any]) -> dict[str, Any]:
    """Validate and atomically persist data/config.txt."""
    normalized = _normalize_app_config(values, seen_keys=set(values))
    lines = [
        "# Media Catalog Configuration",
        "# The operating system is detected automatically.",
        "# Windows uses the Windows-* paths; Linux uses the Linux-* paths.",
        "# Linux SMB paths do NOT need a /mnt mount and work directly via smb://.",
        "#",
        "# Startup-Language: de = German, en = English, es = Spanish",
        "# Scan-On-Startup: Yes = scan media folders at startup, No = open the existing database immediately",
        "#",
        r"# Windows example: \\169.254.100.100\Multimedia\Filme",
        "# Linux example:  smb://169.254.100.100/Multimedia/Filme",
        "",
        f"API-Key={normalized['API-Key']}",
        f"Max-Requests={normalized['Max-Requests']}",
        f"Startup-Language={normalized['Startup-Language']}",
        f"Scan-On-Startup={'Yes' if normalized['Scan-On-Startup'] else 'No'}",
        f"Windows-Movies-Path={normalized['Windows-Movies-Path']}",
        f"Windows-Series-Path={normalized['Windows-Series-Path']}",
        f"Linux-Movies-Path={normalized['Linux-Movies-Path']}",
        f"Linux-Series-Path={normalized['Linux-Series-Path']}",
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


class ImdbLocalizationError(CatalogError):
    """Die lokalisierte IMDb-Abfrage ist vorübergehend nicht verfügbar."""


_IMDB_LOCALIZATION_LOCK = threading.Lock()
_IMDB_LOCALIZATION_LAST_REQUEST_AT = 0.0


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
            f"SMB-Zugriff auf {host}:{port} fehlgeschlagen. "
            "Bitte Benutzername, Passwort und Berechtigungen prüfen."
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
    if source.startswith("\\\\") and username and password:
        # A protected Windows UNC share can also use explicit, scan-only credentials.
        yield from iter_smb_files(
            _unc_to_smb_uri(source), username=username, password=password,
            timeout=timeout, allow_public=allow_public,
        )
        return
    yield from iter_local_files(source)


def configured_media_sources(args: argparse.Namespace) -> list[tuple[str, str]]:
    return [
        (str(getattr(args, "movies_path", "") or DEFAULT_MOVIES_SOURCE), "movie"),
        (str(getattr(args, "series_path", "") or DEFAULT_SERIES_SOURCE), "series"),
    ]


def scan_needs_smb_auth(args: argparse.Namespace) -> bool:
    """Direct SMB URIs and Windows UNC shares require scan-only credentials."""
    return any(
        source.casefold().startswith("smb://") or source.startswith("\\\\")
        for source, _ in configured_media_sources(args)
    )


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
    """Beschreibbarer Ordner neben der tatsächlich gestarteten AppImage."""
    appimage = os.environ.get("APPIMAGE", "")
    if appimage and getattr(sys, "frozen", False):
        return Path(appimage).expanduser().absolute().parent
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def data_directory() -> Path:
    """Gemeinsamer, beschreibbarer Datenordner neben AppImage bzw. Python-Datei."""
    return application_directory() / "data"


def migrate_legacy_data() -> None:
    """Einmalige, nicht-destruktive Übernahme der bisherigen Speicherorte.

    Bestehende Dateien in data/ haben immer Vorrang. Alte Dateien bleiben als
    Sicherheitskopien erhalten. Für SQLite wird die Backup-API benutzt, damit
    auch Daten aus einer möglichen WAL-Datei übernommen werden.
    """
    old = application_directory()
    new = data_directory()
    new.mkdir(parents=True, exist_ok=True)
    for filename in (CONFIG_FILENAME,):
        source, target = old / filename, new / filename
        if source.is_file() and not target.exists():
            try:
                shutil.copy2(source, target)
                print(f"Mnemosyne: {filename} nach data/ übernommen.", file=sys.stderr)
            except OSError as exc:
                raise OSError(f"Konfiguration konnte nicht nach data/ übernommen werden: {exc}") from exc

    source, target = old / "medien_katalog.sqlite3", new / "medien_katalog.sqlite3"
    if source.is_file() and not target.exists():
        temporary = new / "medien_katalog.sqlite3.migration.tmp"
        if temporary.exists():
            temporary.unlink()
        try:
            with sqlite3.connect(f"file:{quote(str(source), safe='/')}?mode=ro", uri=True) as original:
                with sqlite3.connect(temporary) as destination:
                    original.backup(destination)
            os.replace(temporary, target)
            print("Mnemosyne: SQLite-Datenbank nach data/ übernommen.", file=sys.stderr)
        except Exception as exc:
            temporary.unlink(missing_ok=True)
            raise RuntimeError(f"Bestehende Datenbank konnte nicht sicher migriert werden: {exc}") from exc

    source, target = old / "cover_cache", new / "cover_cache"
    if source.is_dir() and not target.exists():
        try:
            shutil.copytree(source, target)
            print("Mnemosyne: Cover-Cache nach data/ übernommen.", file=sys.stderr)
        except OSError as exc:
            raise OSError(f"Cover-Cache konnte nicht nach data/ übernommen werden: {exc}") from exc


def packaged_resource_directory() -> Path:
    """Unveränderliche Ressourcen im AppImage; im Dev-Modus beim Skript."""
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        return Path(sys._MEIPASS) / "assets"
    return Path(__file__).resolve().parent


def default_database_path() -> Path:
    # Beim Doppelklick kann Windows ein anderes Arbeitsverzeichnis verwenden
    # (z. B. System32). Die Datenbank liegt deshalb immer neben dem Skript.
    return data_directory() / "medien_katalog.sqlite3"


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


_SEASON_DIR_RE = re.compile(r"(?i)^(?:season|staffel)\s*[ ._-]*0*(\d{1,3})(?:\b|[ ._-])")
_SEASON_SHORT_RE = re.compile(r"(?i)^s\s*0*(\d{1,3})(?:\b|[ ._-])")
_SEASON_EPISODE_RE = re.compile(r"(?i)(?<![A-Za-z0-9])s\s*0*(\d{1,3})\s*[ ._-]*e\s*0*\d{1,4}")
_X_EPISODE_RE = re.compile(r"(?i)(?<!\d)0*(\d{1,3})\s*[xX]\s*0*\d{1,4}")
_STAFFEL_EPISODE_RE = re.compile(r"(?i)staffel\s*0*(\d{1,3}).{0,12}(?:folge|episode|e)\s*0*\d{1,4}")
_SPECIAL_SEASON_NAMES = {"specials", "special", "spezial", "spezials", "spezialfolgen", "bonusfolgen"}


def detect_server_seasons(paths: Sequence[str], series_root: str = "") -> list[int]:
    """Detect season numbers present on disk from folder names and episode filenames.

    The configured series root and the series' own top-level directory are stripped
    where possible, so a series title containing e.g. "Season 2" is not mistaken
    for an actual season folder.
    """
    root_parts = _source_root_parts(series_root) if series_root else []
    found: set[int] = set()
    for path in paths:
        parts = split_path(str(path))
        relative = parts
        if root_parts and len(parts) > len(root_parts):
            prefix_ok = all(a.casefold() == b.casefold() for a, b in zip(parts[:len(root_parts)], root_parts))
            if prefix_ok:
                relative = parts[len(root_parts):]
        # First component below the configured series root is the series itself.
        if len(relative) > 1:
            relative = relative[1:]
        for component in relative:
            cleaned = component.strip(" ._-")
            folded = normalized_words(cleaned)
            if folded in _SPECIAL_SEASON_NAMES:
                found.add(0)
            for pattern in (_SEASON_DIR_RE, _SEASON_SHORT_RE, _SEASON_EPISODE_RE, _STAFFEL_EPISODE_RE, _X_EPISODE_RE):
                match = pattern.search(cleaned)
                if match:
                    try:
                        season = int(match.group(1))
                    except (TypeError, ValueError):
                        continue
                    if 0 <= season <= 999:
                        found.add(season)
                    break
    return sorted(found)


def _parse_total_seasons(value: Any) -> int | None:
    match = re.search(r"\d+", str(value or ""))
    if not match:
        return None
    try:
        result = int(match.group(0))
    except ValueError:
        return None
    return result if result > 0 else None


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
            german_title TEXT NOT NULL DEFAULT '',
            german_title_manual INTEGER NOT NULL DEFAULT 0,
            german_title_imdb TEXT NOT NULL DEFAULT '',
            german_plot TEXT NOT NULL DEFAULT '',
            imdb_de_checked_at TEXT NOT NULL DEFAULT '',
            spanish_title_imdb TEXT NOT NULL DEFAULT '',
            spanish_plot TEXT NOT NULL DEFAULT '',
            imdb_es_checked_at TEXT NOT NULL DEFAULT '',
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
            awards TEXT NOT NULL DEFAULT '',
            total_seasons TEXT NOT NULL DEFAULT '',
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
    if "german_title" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN german_title TEXT NOT NULL DEFAULT ''")
    if "german_title_manual" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN german_title_manual INTEGER NOT NULL DEFAULT 0")
    if "german_title_imdb" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN german_title_imdb TEXT NOT NULL DEFAULT ''")
    if "german_plot" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN german_plot TEXT NOT NULL DEFAULT ''")
    if "imdb_de_checked_at" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN imdb_de_checked_at TEXT NOT NULL DEFAULT ''")
    if "spanish_title_imdb" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN spanish_title_imdb TEXT NOT NULL DEFAULT ''")
    if "spanish_plot" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN spanish_plot TEXT NOT NULL DEFAULT ''")
    if "imdb_es_checked_at" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN imdb_es_checked_at TEXT NOT NULL DEFAULT ''")
    if "awards" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN awards TEXT NOT NULL DEFAULT ''")
    if "total_seasons" not in columns:
        connection.execute("ALTER TABLE media ADD COLUMN total_seasons TEXT NOT NULL DEFAULT ''")
    # Existing databases keep the locally detected filename/folder title until
    # the first successful German IMDb localization has been cached.
    connection.execute(
        "UPDATE media SET german_title=source_title WHERE TRIM(COALESCE(german_title,''))=''"
    )
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
            "awards": "" if metadata.get("Awards") == "N/A" else str(metadata.get("Awards") or ""),
            "total_seasons": "" if metadata.get("totalSeasons") == "N/A" else str(metadata.get("totalSeasons") or ""),
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
            "awards": old_row["awards"],
            "total_seasons": old_row["total_seasons"],
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
        "awards": "",
        "total_seasons": "",
        "status": "nicht zugeordnet" if lookup_attempted else "Metadaten deaktiviert",
    }



IMDB_DE_TITLE_QUERY = """
query TitleLocalization($id: ID!) {
  title(id: $id) {
    id
    titleText { text }
    plot { plotText { plainText } }
  }
}
"""


def _imdb_localization_stale(value: str, max_days: int = 180) -> bool:
    value = str(value or "").strip()
    if not value:
        return True
    try:
        checked = datetime.fromisoformat(value)
        if checked.tzinfo is None:
            checked = checked.replace(tzinfo=timezone.utc)
    except ValueError:
        return True
    return datetime.now(timezone.utc) - checked > timedelta(days=max_days)


def lookup_imdb_localization(
    imdb_id: str,
    *,
    language: str,
    country: str,
    timeout: int = 15,
) -> tuple[str, str]:
    """IMDb display title and plot localized for one language/country pair.

    IMDb's web GraphQL endpoint is queried with the same ``tt...`` id already
    stored by OMDb. No additional API key is required. Empty strings mean IMDb
    did not provide a localized value for the requested field.
    """
    imdb_id = str(imdb_id or "").strip().lower()
    if not IMDB_ID_RE.fullmatch(imdb_id):
        raise CatalogError("Ungültige IMDb-ID für Lokalisierung.")

    locale_map = {
        "de": ("de-DE", "DE", "de-DE,de;q=0.9,en;q=0.7", "de-DE,de,en-US,en"),
        "es": ("es-ES", "ES", "es-ES,es;q=0.9,en;q=0.7", "es-ES,es,en-US,en"),
    }
    language_key = str(language or "").strip().casefold()
    if language_key not in locale_map:
        raise CatalogError(f"Nicht unterstützte IMDb-Lokalisierung: {language}")
    imdb_language, default_country, accept_language, normalized_languages = locale_map[language_key]
    imdb_country = str(country or default_country).strip().upper() or default_country

    payload = json.dumps(
        {"query": IMDB_DE_TITLE_QUERY, "variables": {"id": imdb_id}},
        ensure_ascii=False,
    ).encode("utf-8")
    headers = {
        "Accept": "application/graphql+json, application/json",
        "Content-Type": "application/json",
        "Origin": "https://www.imdb.com",
        "Referer": "https://www.imdb.com/",
        "User-Agent": f"medien-katalog/{VERSION}",
        "Accept-Language": accept_language,
        "x-imdb-client-name": "imdb-web-next",
        "x-imdb-user-language": imdb_language,
        "x-imdb-user-country": imdb_country,
        "x-imdb-normalized-languages": normalized_languages,
    }

    global _IMDB_LOCALIZATION_LAST_REQUEST_AT
    last_error: Exception | None = None
    for attempt in range(3):
        try:
            with _IMDB_LOCALIZATION_LOCK:
                wait_for = 0.18 - (time.monotonic() - _IMDB_LOCALIZATION_LAST_REQUEST_AT)
                if wait_for > 0:
                    time.sleep(wait_for)
                request = Request(IMDB_GRAPHQL_ENDPOINT, data=payload, headers=headers, method="POST")
                with urlopen(request, timeout=timeout) as response:
                    body = response.read().decode("utf-8")
                _IMDB_LOCALIZATION_LAST_REQUEST_AT = time.monotonic()
            data = json.loads(body)
            title_node = ((data.get("data") or {}).get("title") or {})
            if not title_node:
                errors = data.get("errors") or []
                message = "; ".join(str(e.get("message") or e) for e in errors if isinstance(e, dict))
                raise ValueError(message or "IMDb lieferte keine Titeldaten")
            localized_title = str((title_node.get("titleText") or {}).get("text") or "").strip()
            localized_plot = str((((title_node.get("plot") or {}).get("plotText") or {}).get("plainText")) or "").strip()
            return localized_title, localized_plot
        except (HTTPError, URLError, TimeoutError, socket.timeout, json.JSONDecodeError, ValueError) as exc:
            last_error = exc
            _IMDB_LOCALIZATION_LAST_REQUEST_AT = time.monotonic()
            if attempt < 2:
                time.sleep(0.6 * (2 ** attempt))
    reason = str(last_error) if last_error else "unbekannter Fehler"
    raise ImdbLocalizationError(f"IMDb-{language_key.upper()} ist nach drei Versuchen nicht erreichbar ({reason}).")


def lookup_imdb_german_localization(imdb_id: str, timeout: int = 15) -> tuple[str, str]:
    return lookup_imdb_localization(imdb_id, language="de", country="DE", timeout=timeout)


def lookup_imdb_spanish_localization(imdb_id: str, timeout: int = 15) -> tuple[str, str]:
    return lookup_imdb_localization(imdb_id, language="es", country="ES", timeout=timeout)

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
    progress: Any = None,
) -> tuple[int, int, int, int]:
    """Quelle vollständig scannen und SQLite atomar auf den aktuellen Bestand bringen.

    Rückgabe: (Titelanzahl, entfernte Titel, echte OMDb-HTTP-Aufrufe,
    aus SQLite wiederverwendete Metadatensätze).
    """
    if progress:
        progress(stage="discover", current=0, total=0, title="")
    candidates = iter_configured_candidates(args, password=password)
    items = merge_candidates(candidates, only=args.nur)
    limited_scan = bool(args.max_titel and len(items) > args.max_titel)
    if limited_scan:
        items = items[: args.max_titel]

    client = None if args.ohne_metadaten else OmdbClient(omdb_key, args.cache, args.cache_tage)
    omdb_available = client is not None
    omdb_error = ""
    imdb_de_available = True
    imdb_es_available = True
    scan_id = _utc_now()
    if progress:
        progress(stage="process", current=0, total=len(items), title="")
    connection = open_database(args.db)
    try:
        connection.execute("BEGIN IMMEDIATE")
        reused_metadata = 0
        for index, item in enumerate(items, start=1):
            if progress:
                progress(stage="process", current=index - 1, total=len(items), title=item.title[:110])
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
                    or not str(values.get("awards") or "").strip()
                    or (item.kind == "series" and not str(values.get("total_seasons") or "").strip())
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
                    cached_awards = cached_metadata.get("Awards")
                    if not str(values.get("awards") or "").strip() and cached_awards and cached_awards != "N/A":
                        values["awards"] = str(cached_awards)
                    cached_total_seasons = cached_metadata.get("totalSeasons")
                    if item.kind == "series" and not str(values.get("total_seasons") or "").strip() and cached_total_seasons and cached_total_seasons != "N/A":
                        values["total_seasons"] = str(cached_total_seasons)

                # Neue Felder werden bevorzugt aus dem Cache ergänzt. Falls dort
                # noch etwas fehlt, reicht genau ein OMDb-Aufruf per bekannter IMDb-ID.
                # Dann wird die Altersfreigabe genau einmal anhand der bereits bekannten
                # IMDb-ID nachgeladen. Das betrifft nur Titel ohne age_rating; vollständig
                # gepflegte Altbestände verursachen weiterhin keinerlei API-Aufrufe.
                if (
                    (
                        not str(values.get("age_rating") or "").strip()
                        or not str(values.get("awards") or "").strip()
                        or (item.kind == "series" and not str(values.get("total_seasons") or "").strip())
                    )
                    and client is not None
                    and omdb_available
                    and str(old_row["imdb_id"] or "").strip()
                ):
                    try:
                        fresh_metadata = lookup_exact_imdb(client, str(old_row["imdb_id"]))
                        fresh_rated = fresh_metadata.get("Rated")
                        if not str(values.get("age_rating") or "").strip() and fresh_rated and fresh_rated != "N/A":
                            values["age_rating"] = str(fresh_rated)
                        fresh_awards = fresh_metadata.get("Awards")
                        if not str(values.get("awards") or "").strip() and fresh_awards and fresh_awards != "N/A":
                            values["awards"] = str(fresh_awards)
                        fresh_total_seasons = fresh_metadata.get("totalSeasons")
                        if item.kind == "series" and not str(values.get("total_seasons") or "").strip() and fresh_total_seasons and fresh_total_seasons != "N/A":
                            values["total_seasons"] = str(fresh_total_seasons)
                    except OmdbTemporaryError as exc:
                        print(f"Warnung beim Nachladen zusätzlicher OMDb-Daten für {item.title!r}: {exc}", file=sys.stderr)
                    except OmdbFatalError as exc:
                        omdb_available = False
                        omdb_error = str(exc)
                        print(
                            f"Warnung: {exc} Weitere OMDb-Abfragen werden für diesen Scan übersprungen; "
                            "die Bibliothek wird trotzdem vollständig synchronisiert.",
                            file=sys.stderr,
                        )
                    except CatalogError as exc:
                        print(f"Warnung beim Nachladen zusätzlicher OMDb-Daten für {item.title!r}: {exc}", file=sys.stderr)

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
            german_title_manual = int(old_row["german_title_manual"]) if old_row else 0
            german_title_imdb = str(old_row["german_title_imdb"] or "") if old_row else ""
            german_plot = str(old_row["german_plot"] or "") if old_row else ""
            imdb_de_checked_at = str(old_row["imdb_de_checked_at"] or "") if old_row else ""
            spanish_title_imdb = str(old_row["spanish_title_imdb"] or "") if old_row else ""
            spanish_plot = str(old_row["spanish_plot"] or "") if old_row else ""
            imdb_es_checked_at = str(old_row["imdb_es_checked_at"] or "") if old_row else ""
            current_imdb_id = str(values.get("imdb_id") or "").strip().lower()
            previous_imdb_id = str(old_row["imdb_id"] or "").strip().lower() if old_row else ""
            if previous_imdb_id and current_imdb_id != previous_imdb_id:
                german_title_imdb = ""
                german_plot = ""
                imdb_de_checked_at = ""
                spanish_title_imdb = ""
                spanish_plot = ""
                imdb_es_checked_at = ""

            if (
                imdb_de_available
                and IMDB_ID_RE.fullmatch(current_imdb_id)
                and _imdb_localization_stale(imdb_de_checked_at)
            ):
                if not args.ruhig:
                    print(f"IMDb-DE {index}/{len(items)}: {item.title}", file=sys.stderr)
                try:
                    localized_title, localized_plot = lookup_imdb_german_localization(current_imdb_id)
                    german_title_imdb = localized_title
                    german_plot = localized_plot
                    imdb_de_checked_at = _utc_now()
                except ImdbLocalizationError as exc:
                    imdb_de_available = False
                    print(
                        f"Warnung: {exc} Weitere deutsche IMDb-Abfragen werden für diesen Scan übersprungen.",
                        file=sys.stderr,
                    )

            if (
                imdb_es_available
                and IMDB_ID_RE.fullmatch(current_imdb_id)
                and _imdb_localization_stale(imdb_es_checked_at)
            ):
                if not args.ruhig:
                    print(f"IMDb-ES {index}/{len(items)}: {item.title}", file=sys.stderr)
                try:
                    localized_title_es, localized_plot_es = lookup_imdb_spanish_localization(current_imdb_id)
                    spanish_title_imdb = localized_title_es
                    spanish_plot = localized_plot_es
                    imdb_es_checked_at = _utc_now()
                except ImdbLocalizationError as exc:
                    imdb_es_available = False
                    print(
                        f"Warnung: {exc} Weitere spanische IMDb-Abfragen werden für diesen Scan übersprungen.",
                        file=sys.stderr,
                    )

            if old_row and german_title_manual:
                german_title = str(old_row["german_title"] or item.title)
            else:
                german_title = german_title_imdb or item.title or str(values.get("title") or "")
            connection.execute(
                """
                INSERT INTO media(
                    scan_key, kind, source_title, source_year, german_title, german_title_manual,
                    german_title_imdb, german_plot, imdb_de_checked_at,
                    spanish_title_imdb, spanish_plot, imdb_es_checked_at, imdb_id, manual_imdb_id,
                    title, year, imdb_rating, plot, poster, genre, director, actors, runtime, age_rating, awards, total_seasons, status,
                    is_kids, kids_manual, file_count, paths_json, server_added_at, last_seen_scan, created_at, updated_at
                ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(scan_key) DO UPDATE SET
                    kind=excluded.kind,
                    source_title=excluded.source_title,
                    source_year=excluded.source_year,
                    german_title=excluded.german_title,
                    german_title_manual=excluded.german_title_manual,
                    german_title_imdb=excluded.german_title_imdb,
                    german_plot=excluded.german_plot,
                    imdb_de_checked_at=excluded.imdb_de_checked_at,
                    spanish_title_imdb=excluded.spanish_title_imdb,
                    spanish_plot=excluded.spanish_plot,
                    imdb_es_checked_at=excluded.imdb_es_checked_at,
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
                    awards=excluded.awards,
                    total_seasons=excluded.total_seasons,
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
                    german_title,
                    german_title_manual,
                    german_title_imdb,
                    german_plot,
                    imdb_de_checked_at,
                    spanish_title_imdb,
                    spanish_plot,
                    imdb_es_checked_at,
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
                    values["awards"],
                    values["total_seasons"],
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

        if progress:
            progress(stage="commit", current=len(items), total=len(items), title="")
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
        localized_title = ""
        localized_plot = ""
        localized_checked_at = ""
        try:
            localized_title, localized_plot = lookup_imdb_german_localization(imdb_id)
            localized_checked_at = _utc_now()
        except ImdbLocalizationError as exc:
            print(f"Warnung bei deutscher IMDb-Lokalisierung für {imdb_id}: {exc}", file=sys.stderr)
        localized_title_es = ""
        localized_plot_es = ""
        localized_checked_at_es = ""
        try:
            localized_title_es, localized_plot_es = lookup_imdb_spanish_localization(imdb_id)
            localized_checked_at_es = _utc_now()
        except ImdbLocalizationError as exc:
            print(f"Warnung bei spanischer IMDb-Lokalisierung für {imdb_id}: {exc}", file=sys.stderr)
        auto_kids = _auto_kids_from_metadata(metadata)
        german_title_manual = bool(row["german_title_manual"])
        german_title = str(row["german_title"] or "") if german_title_manual else (
            localized_title or str(row["source_title"] or metadata.get("Title") or "")
        )
        connection.execute(
            """
            UPDATE media SET
                manual_imdb_id=?, imdb_id=?, title=?, year=?, imdb_rating=?, plot=?,
                german_title=?, german_title_imdb=?, german_plot=?, imdb_de_checked_at=?,
                spanish_title_imdb=?, spanish_plot=?, imdb_es_checked_at=?,
                poster=?, genre=?, director=?, actors=?, runtime=?, age_rating=?, awards=?, total_seasons=?, status='manuell zugeordnet',
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
                german_title,
                localized_title,
                localized_plot,
                localized_checked_at,
                localized_title_es,
                localized_plot_es,
                localized_checked_at_es,
                poster,
                "" if metadata.get("Genre") == "N/A" else str(metadata.get("Genre") or ""),
                "" if metadata.get("Director") == "N/A" else str(metadata.get("Director") or ""),
                "" if metadata.get("Actors") == "N/A" else str(metadata.get("Actors") or ""),
                "" if metadata.get("Runtime") == "N/A" else str(metadata.get("Runtime") or ""),
                "" if metadata.get("Rated") == "N/A" else str(metadata.get("Rated") or ""),
                "" if metadata.get("Awards") == "N/A" else str(metadata.get("Awards") or ""),
                "" if metadata.get("totalSeasons") == "N/A" else str(metadata.get("totalSeasons") or ""),
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


def set_german_title(args: argparse.Namespace, media_id: int, value: str) -> str:
    """Store a manually corrected German display title for a catalog item."""
    german_title = " ".join(str(value or "").split()).strip(" ._-–—")
    if not german_title:
        raise CatalogError("Der deutsche Titel darf nicht leer sein.")
    if len(german_title) > 300:
        raise CatalogError("Der deutsche Titel ist zu lang.")
    connection = open_database(args.db)
    try:
        cursor = connection.execute(
            "UPDATE media SET german_title=?, german_title_manual=1, updated_at=? WHERE id=?",
            (german_title, _utc_now(), media_id),
        )
        if cursor.rowcount == 0:
            raise CatalogError("Der Katalogeintrag existiert nicht mehr.")
        connection.commit()
    finally:
        connection.close()
    return german_title


def reset_german_title(args: argparse.Namespace, media_id: int) -> str:
    """Restore the automatically localized German IMDb title, with local fallback."""
    connection = open_database(args.db)
    try:
        row = connection.execute(
            "SELECT german_title_imdb, source_title, title FROM media WHERE id=?", (media_id,)
        ).fetchone()
        if row is None:
            raise CatalogError("Der Katalogeintrag existiert nicht mehr.")
        german_title = str(row["german_title_imdb"] or row["source_title"] or row["title"] or "").strip()
        connection.execute(
            "UPDATE media SET german_title=?, german_title_manual=0, updated_at=? WHERE id=?",
            (german_title, _utc_now(), media_id),
        )
        connection.commit()
    finally:
        connection.close()
    return german_title


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
    return data_directory() / "cover_cache"


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
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Mnemosyne/4.6",
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
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Mnemosyne/4.6",
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
    """Standardhintergrund aus dem AppImage, nicht aus dem Datenordner."""
    base = packaged_resource_directory()
    for name in ("background.png", "background.jpg", "background.jpeg"):
        path = base / name
        if path.is_file():
            return path
    return None


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

    regular_name = "MnemosyneSans"
    bold_name = "MnemosyneSansBold"
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

    lang = language if language in {"de", "en", "es"} else "de"
    text = {
        "de": {
            "title": "Mnemosyne - IMDb-Liste",
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
            "awards": "Auszeichnungen",
            "seasons": "Staffeln",
            "server_seasons": "Auf Server",
            "plot": "Beschreibung",
            "no_cover": "Kein Cover",
            "unrated": "ohne Bewertung",
            "page": "Seite",
        },
        "en": {
            "title": "Mnemosyne - IMDb List",
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
            "awards": "Awards",
            "seasons": "Seasons",
            "server_seasons": "On server",
            "plot": "Plot",
            "no_cover": "No cover",
            "unrated": "not rated",
            "page": "Page",
        },
        "es": {
            "title": "Mnemosyne - Lista IMDb",
            "created": "Creado",
            "count": "títulos",
            "movies": "películas",
            "series": "series",
            "movie": "Película",
            "serie": "Serie",
            "rating": "IMDb",
            "genre": "Género",
            "runtime": "Duración",
            "director": "Dirección",
            "cast": "Reparto",
            "age_rating": "Clasificación por edad",
            "awards": "Premios",
            "seasons": "Temporadas",
            "server_seasons": "En el servidor",
            "plot": "Sinopsis",
            "no_cover": "Sin carátula",
            "unrated": "sin valoración",
            "page": "Página",
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
        author="Mnemosyne",
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
        if lang == "de":
            display_title = str(row["german_title"] or row["german_title_imdb"] or row["source_title"] or row["title"])
        elif lang == "es":
            display_title = str(row["spanish_title_imdb"] or row["title"] or row["source_title"])
        else:
            display_title = str(row["title"] or row["source_title"])
        right_story: list[Any] = [
            Paragraph(f"{index}. [{esc(kind_label)}] {esc(display_title)}{year_suffix}", heading_style),
            RatingGraphic(str(row["imdb_rating"] or "")),
            Spacer(1, 0.6 * mm),
        ]

        facts: list[str] = []
        genre = localized_genre_text(str(row["genre"] or "").strip(), language)
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
        awards = str(row["awards"] or "").strip()
        if awards:
            right_story.append(Paragraph(f'<b>{esc(text["awards"])}:</b> {esc(shortened(awards, 240))}', info_style))
        if str(row["kind"]) == "series":
            total_seasons = _parse_total_seasons(row["total_seasons"])
            try:
                row_paths = json.loads(row["paths_json"] or "[]")
            except (json.JSONDecodeError, TypeError):
                row_paths = []
            server_seasons = detect_server_seasons(row_paths, str(getattr(args, "series_path", "") or ""))
            season_bits: list[str] = []
            if total_seasons:
                season_bits.append(f'<b>{esc(text["seasons"])}:</b> {total_seasons}')
            if server_seasons:
                shown = ", ".join("S0" if n == 0 else f"S{n}" for n in server_seasons)
                season_bits.append(f'<b>{esc(text["server_seasons"])}:</b> {esc(shown)}')
            if season_bits:
                right_story.append(Paragraph(" &nbsp;·&nbsp; ".join(season_bits), info_style))
        plot = str((row["german_plot"] if lang == "de" else (row["spanish_plot"] if lang == "es" else row["plot"])) or row["plot"] or "").strip()
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


def _rebase_stored_media_target(target: str, configured_root: str) -> str:
    """Setzt einen gespeicherten Medienpfad auf den aktuell konfigurierten Root um.

    Das ist vor allem bei gemeinsam genutzten SQLite-Datenbanken wichtig: Ein unter
    Windows gespeicherter UNC-Pfad kann unter Linux auf einen lokalen Mount oder auf
    eine andere SMB-Adresse zeigen. Ebenso werden alte Server-IP-Adressen ersetzt,
    solange der relative Pfad unterhalb von ``Filme``/``Serien`` gleich geblieben ist.
    """
    stored = str(target or "").strip()
    root = str(configured_root or "").strip().rstrip("\\/")
    if not stored or not root:
        return stored

    stored_parts = split_path(stored)
    if not stored_parts:
        return stored

    if root.casefold().startswith("smb://"):
        try:
            parsed = urlsplit(root)
            root_parts = [unquote(part) for part in parsed.path.split("/") if part]
        except ValueError:
            return stored
        if not root_parts:
            return stored
        marker = normalized_words(root_parts[-1])
        index = next((i for i, part in enumerate(stored_parts) if normalized_words(part) == marker), -1)
        if index < 0:
            return stored
        tail = stored_parts[index + 1 :]
        if not tail:
            return root
        encoded_tail = "/".join(quote(part, safe="!$&'()*+,;=:@-._~") for part in tail)
        return root + "/" + encoded_tail

    root_parts = split_path(root)
    if not root_parts:
        return stored
    marker = normalized_words(root_parts[-1])
    index = next((i for i, part in enumerate(stored_parts) if normalized_words(part) == marker), -1)
    if index < 0:
        return stored
    tail = stored_parts[index + 1 :]

    if root.startswith("\\") or re.match(r"^[A-Za-z]:[\\/]", root):
        return str(PureWindowsPath(root, *tail))
    return str(Path(root).joinpath(*tail))



def _open_with_desktop_default(target: str) -> None:
    """Öffnet Datei/Ordner mit der Desktop-Standardanwendung des Betriebssystems.

    Windows öffnet UNC-Pfade direkt. Unter Linux werden Windows-UNC-Pfade in
    ``smb://``-URIs umgewandelt, damit KDE/KIO, GNOME/GVfs usw. sie nicht als
    relative lokale Dateipfade interpretieren.
    """
    value = str(target or "").strip()
    if not value:
        raise FileNotFoundError("Leerer Medienpfad")

    if os.name == "nt":
        os.startfile(value)  # type: ignore[attr-defined]
        return
    if sys.platform == "darwin":
        subprocess.Popen(["open", value], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return

    linux_target = _unc_to_smb_uri(value)
    try:
        subprocess.Popen(["xdg-open", linux_target], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except FileNotFoundError:
        # ``gio open`` ist auf vielen GNOME-/GTK-Desktops verfügbar und versteht
        # ebenfalls smb://. Damit bleibt die Funktion auch ohne xdg-utils nutzbar.
        subprocess.Popen(["gio", "open", linux_target], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


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
        target = _rebase_stored_media_target(target, args.series_path)
        action_error = "Der Serienordner konnte nicht geöffnet werden"
    else:
        target = _media_file_from_row(row)
        target = _rebase_stored_media_target(target, args.movies_path)
        action_error = "Der Film konnte nicht mit dem Standardplayer gestartet werden"

    try:
        _open_with_desktop_default(target)
    except (OSError, FileNotFoundError) as exc:
        raise CatalogError(f"{action_error}: {exc}") from exc
    return target


GERMAN_GENRE_NAMES = {
    "Action": "Action", "Adventure": "Abenteuer", "Animation": "Animation", "Biography": "Biografie",
    "Comedy": "Komödie", "Crime": "Krimi", "Documentary": "Dokumentation", "Drama": "Drama",
    "Family": "Familie", "Fantasy": "Fantasy", "Film-Noir": "Film Noir", "Game-Show": "Spielshow",
    "History": "Geschichte", "Horror": "Horror", "Music": "Musik", "Musical": "Musical",
    "Mystery": "Mystery", "News": "Nachrichten", "Reality-TV": "Reality-TV", "Romance": "Liebesfilm",
    "Sci-Fi": "Science-Fiction", "Short": "Kurzfilm", "Sport": "Sport", "Talk-Show": "Talkshow",
    "Thriller": "Thriller", "War": "Krieg", "Western": "Western",
}

SPANISH_GENRE_NAMES = {
    "Action": "Acción", "Adventure": "Aventura", "Animation": "Animación", "Biography": "Biografía",
    "Comedy": "Comedia", "Crime": "Crimen", "Documentary": "Documental", "Drama": "Drama",
    "Family": "Familiar", "Fantasy": "Fantasía", "Film-Noir": "Cine negro", "Game-Show": "Concurso",
    "History": "Historia", "Horror": "Terror", "Music": "Música", "Musical": "Musical",
    "Mystery": "Misterio", "News": "Noticias", "Reality-TV": "Telerrealidad", "Romance": "Romance",
    "Sci-Fi": "Ciencia ficción", "Short": "Cortometraje", "Sport": "Deporte", "Talk-Show": "Talk show",
    "Thriller": "Suspense", "War": "Bélico", "Western": "Western",
}

def localized_genre_text(value: str, language: str) -> str:
    parts = [part.strip() for part in str(value or "").split(",") if part.strip()]
    if language == "de":
        return ", ".join(GERMAN_GENRE_NAMES.get(part, part) for part in parts)
    if language == "es":
        return ", ".join(SPANISH_GENRE_NAMES.get(part, part) for part in parts)
    return ", ".join(parts)


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
        f'<option value="{html.escape(name.casefold(), quote=True)}" data-genre-name="{html.escape(name, quote=True)}">{html.escape(name)}</option>'
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
        title_raw = str(row["title"] or row["source_title"] or "")
        german_title_raw = str(row["german_title"] or row["source_title"] or title_raw)
        spanish_title_raw = str(row["spanish_title_imdb"] or title_raw)
        title = html.escape(title_raw)
        german_title = html.escape(german_title_raw)
        source_title = html.escape(str(row["source_title"]))
        year = html.escape(str(row["year"]))
        rating = html.escape(str(row["imdb_rating"]))
        plot_en_raw = str(row["plot"] or "")
        plot_de_raw = str(row["german_plot"] or plot_en_raw)
        plot_es_raw = str(row["spanish_plot"] or plot_en_raw)
        plot = html.escape(plot_de_raw)
        # Keep compact cards fast; lengthy localized plots can be expanded per card.
        plot_toggle_html = (
            f'<button class="plot-more" type="button" aria-expanded="false" '
            f'aria-controls="plot-{int(row["id"])}" data-i18n="plotMore" '
            f'onclick="togglePlot(this)">Mehr anzeigen</button>'
            if any((plot_en_raw, plot_de_raw, plot_es_raw)) else ""
        )
        genre_raw = str(row["genre"] or "")
        director_raw = str(row["director"] or "")
        actors_raw = str(row["actors"] or "")
        awards_raw = str(row["awards"] or "").strip()
        total_seasons = _parse_total_seasons(row["total_seasons"]) if str(row["kind"]) == "series" else None
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
        trailer_html = (
            '<a class="trailer-link" href="#" target="_blank" rel="noreferrer" data-i18n="searchTrailer" '
            f'data-trailer-year="{html.escape(str(row["year"] or ""), quote=True)}">Trailer suchen</a>'
            if (title_raw or german_title_raw)
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
        server_seasons = detect_server_seasons(paths, str(getattr(args, "series_path", "") or "")) if str(row["kind"]) == "series" else []
        seasons_html = ""
        if str(row["kind"]) == "series" and (total_seasons or server_seasons):
            badge_seasons: list[int] = []
            if total_seasons:
                badge_seasons.extend(range(1, total_seasons + 1))
            for season_no in server_seasons:
                if season_no not in badge_seasons:
                    badge_seasons.append(season_no)
            badge_seasons = sorted(set(badge_seasons), key=lambda value: (value != 0, value))
            badges: list[str] = []
            for season_no in badge_seasons:
                available = season_no in server_seasons
                label = "S0" if season_no == 0 else f"S{season_no}"
                state = "available" if available else "missing"
                mark = "✓" if available else "—"
                badges.append(f'<span class="season-badge {state}">{label} {mark}</span>')
            count_html = f'<span class="season-count">{total_seasons}</span>' if total_seasons else ""
            separator = " · " if count_html and badges else ""
            seasons_html = (
                '<div class="facts seasons"><span data-i18n="seasonsLabel">Staffeln</span>: ' + count_html + separator +
                '<span class="season-badges" id="season-badges-' + str(int(row["id"])) + '">' +
                "".join(badges) + '</span>' +
                '<button class="season-expand" type="button" hidden aria-expanded="false" ' +
                'aria-controls="season-badges-' + str(int(row["id"])) + '" ' +
                'onclick="toggleSeasons(this)"></button></div>'
            )
        if str(row["kind"]) == "series" and not seasons_html:
            seasons_html = '<div class="facts seasons"><span data-i18n="seasonsLabel">Staffeln</span>: —</div>'
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
              data-title="{html.escape(title_raw, quote=True)}"
              data-title-en="{html.escape(title_raw, quote=True)}"
              data-title-de="{html.escape(german_title_raw, quote=True)}"
              data-title-es="{html.escape(spanish_title_raw, quote=True)}"
              data-year="{html.escape(str(row['year'] or ''), quote=True)}"
              data-search="{html.escape((title_raw+' '+german_title_raw+' '+spanish_title_raw+' '+str(row['source_title'])+' '+str(row['year'])+' '+genre_raw+' '+director_raw+' '+actors_raw+' '+awards_raw+' '+str(row['age_rating'] or '')).casefold(), quote=True)}"
              data-genres="{html.escape(json.dumps(genre_values, ensure_ascii=False), quote=True)}"
              data-directors="{html.escape(json.dumps(director_values, ensure_ascii=False), quote=True)}"
              data-actors="{html.escape(json.dumps(actor_values, ensure_ascii=False), quote=True)}"
              data-kind="{html.escape(str(row['kind']), quote=True)}"
              data-kids="{'1' if is_kids else '0'}"
              data-unknown="{'1' if unknown else '0'}"
              data-added-ts="{server_added_ts}"
              data-original-order="{card_order}">
              <div class="card-top">
                {poster_html}
                <div class="card-summary">
                  <div class="topline"><span class="kind" data-kind-code="{html.escape(str(row['kind']), quote=True)}">{'Film' if row['kind']=='movie' else 'Serie'}</span><span class="badges">{'<span class="kids-badge" data-i18n="kidsBadge">Kinder</span>' if is_kids else ''}<span class="status" data-status-code="{html.escape(status_code, quote=True)}">{html.escape('Manuell' if manual else status_raw)}</span><button class="favorite-btn" type="button" onclick="toggleFavorite({int(row['id'])})" aria-label="Favorit" title="Favorit">☆</button></span></div>
                <h2><span class="localized-title">{german_title}</span> <small>{year}</small></h2>
                <div class="rating">★ {rating}<span>/10</span></div>
                <div class="facts"><span class="genre-text" data-genre-raw="{html.escape(genre_raw, quote=True)}">{genre}</span>{' · ' if genre and runtime else ''}{runtime}</div>
                <div class="facts age-rating"><span class="age-label" data-i18n="ageRatingLabel">FSK/Rating</span>: <span class="age-badge age-{age_badge_class}" title="{age_badge_hint_html}">{age_badge_text_html}</span></div>
                {f'<div class="facts added-date"><span data-i18n="addedLabel">Auf Server</span>: {html.escape(server_added_display)}</div>' if server_added_display else ''}
                {f'<div class="facts director"><span data-i18n="directorLabel">Regie</span>: {director}</div>' if director else ''}
                {f'<div class="facts actors"><span data-i18n="castLabel">Besetzung</span>: {actors}</div>' if actors else ''}
                {f'<div class="facts awards"><span data-i18n="awardsLabel">Auszeichnungen</span>: {html.escape(awards_raw)}</div>' if awards_raw else ''}
                {'<button class="meta-expand" type="button" hidden aria-expanded="false" onclick="toggleSeriesMetadata(this)"></button>'}
                </div>
              </div>
              {seasons_html}
              <div class="content card-bottom">
                <div class="series-description">
                <p class="localized-plot" id="plot-{int(row['id'])}" data-plot-en="{html.escape(plot_en_raw, quote=True)}" data-plot-de="{html.escape(plot_de_raw, quote=True)}" data-plot-es="{html.escape(plot_es_raw, quote=True)}">{plot}</p>
                {plot_toggle_html}
                </div><div class="series-actions">
                <div class="links">{imdb_html}{trailer_html}<button class="play-button" type="button" onclick="startMedia({int(row['id'])}, this, '{'series' if str(row['kind']) == 'series' else 'movie'}')" data-i18n="{'openFolder' if str(row['kind']) == 'series' else 'playFilm'}">{'Ordner öffnen' if str(row['kind']) == 'series' else 'Film starten'}</button><span>{int(row['file_count'])} <span data-i18n="files">Datei(en)</span></span></div>
                <details>
                  <summary data-i18n="sourceCorrection">Quelle &amp; Korrektur</summary>
                  <p class="detected"><span data-i18n="detectedAs">Erkannt als</span>: <strong>{source_title}</strong>{' ('+html.escape(str(row['source_year']))+')' if row['source_year'] else ''}</p>
                  <form method="post" action="/german-title/{int(row['id'])}" class="correction german-title-form" onsubmit="saveViewState(this)">
                    <input name="german_title" value="{html.escape(german_title_raw, quote=True)}" placeholder="Deutscher Titel" data-i18n-placeholder="germanTitlePlaceholder" required>
                    <button type="submit" data-i18n="saveGermanTitle">Deutschen Titel speichern</button>
                  </form>
                  {f'<form method="post" action="/german-title-reset/{int(row["id"])}" class="german-title-reset" onsubmit="saveViewState(this)"><button class="secondary" type="submit" data-i18n="resetGermanTitle">Deutschen Titel zurücksetzen</button></form>' if bool(row['german_title_manual']) else ''}
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
              </div>
            </article>
            """
        )

    # The overview shows ONLY the newest 20 film/series tiles, not the full catalog.
    # No OMDb/IMDb requests, no extra tables, and no second library scan.
    by_date = sorted(
        rows,
        key=lambda row: str(row["server_added_at"] or row["created_at"] or ""), reverse=True,
    )[:20]
    featured_html: list[str] = []
    for row in by_date:
        mid = int(row["id"])
        title_en = str(row["title"] or row["source_title"] or "")
        title_de = str(row["german_title"] or title_en)
        title_es = str(row["spanish_title_imdb"] or title_en)
        poster_ok = bool(_safe_poster_url(str(row["poster"] or ""))) or bool(IMDB_ID_RE.fullmatch(str(row["imdb_id"] or "")))
        photo = (
            f'<img loading="eager" fetchpriority="high" decoding="async" src="/poster/{mid}?v={_poster_version_token(row)}" '
            f'alt="" onerror="this.style.display=\'none\';">'
            if poster_ok else '<div class="featured-placeholder" aria-hidden="true">▷</div>'
        )
        featured_html.append(
            f'<button type="button" class="featured-item" data-media-id="{mid}" onclick="showFeatured({mid})" '
            f'aria-label="{html.escape(title_de, quote=True)}">'
            f'{photo}<span class="featured-title" '
            f'data-title-en="{html.escape(title_en, quote=True)}" '
            f'data-title-de="{html.escape(title_de, quote=True)}" '
            f'data-title-es="{html.escape(title_es, quote=True)}">'
            f'{html.escape(title_de)}</span></button>'
        )
    movie_count = sum(1 for row in rows if row["kind"] == "movie")
    series_count = len(rows) - movie_count

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
    if background_path is not None:
        # Keep the user-provided background visible below the translucent Metro panels.
        metro_background_image = (
            "linear-gradient(90deg,rgba(15,29,43,.72) 0%,rgba(15,29,43,.55) 65%,"
            "rgba(15,29,43,.30) 100%),"
            f"url('/background?v={background_token}')"
        )
    else:
        metro_background_image = "linear-gradient(130deg,#1d2936 0%,#182533 60%,#213140 100%)"
    notice_html = f'<div class="message ok">{html.escape(notice)}</div>' if notice else ""
    error_html = f'<div class="message error">{html.escape(error)}</div>' if error else ""
    browser_warning_html = (
        '<div class="message browser-warning" role="status">'
        '<strong data-i18n="browserFallbackTitle">Browser-Hinweis:</strong>'
        '<span data-i18n="browserFallbackText">Der optimierte Browsermodus ist nicht verfügbar. Mnemosyne läuft im Standardbrowser; installierte Erweiterungen können die Oberfläche verlangsamen. Installiere Chromium, Chrome, Edge oder Brave für den isolierten Modus.</span>'
        '</div>'
        if bool(getattr(args, "browser_fallback", False)) else ""
    )
    return f"""<!doctype html>
<html lang="de">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Mnemosyne</title>
<link rel="icon" type="image/png" sizes="256x256" href="/mnemosyne_icon.png?v=4.15.44">
<link rel="shortcut icon" href="/favicon.ico?v=4.15.44" type="image/x-icon">
<link rel="preload" as="image" href="/mnemosyne_icon.png?v=4.15.44">
<style>
:root {{ color-scheme: dark; --bg:#111318; --panel:#1a1e25; --muted:#a7afbd; --line:#2b313b; --accent:#f5c451; --play:#36c978; --play-hover:#48da8a; }}
* {{ box-sizing:border-box; }}
body {{ margin:0; font-family:system-ui,-apple-system,Segoe UI,sans-serif; {body_background_css} color:#f5f7fa; min-height:100vh; }}
header {{ position:sticky; top:0; z-index:5; background:rgba(17,19,24,.93); backdrop-filter:blur(12px); border-bottom:1px solid var(--line); padding:12px max(18px,4vw) 11px; box-shadow:0 6px 24px rgba(0,0,0,.14); }}
.header-main {{ display:flex; align-items:center; justify-content:space-between; gap:16px; flex-wrap:wrap; }}
.brand-row {{ display:flex; align-items:center; gap:12px; min-width:0; }}
h1 {{ margin:0; font-size:1.08rem; white-space:nowrap; display:flex; align-items:baseline; gap:6px; }}
.brand-title {{ display:inline-block; font-family:Impact,Haettenschweiler,"Arial Narrow Bold","Liberation Sans Narrow","Nimbus Sans Narrow","DejaVu Sans Condensed",sans-serif; font-size:1.72rem; line-height:.82; font-weight:900; letter-spacing:.025em; text-transform:uppercase; font-stretch:condensed; color:#fff; text-shadow:0 1px 0 rgba(255,255,255,.05); }}
.brand-separator {{ color:#697382; font-weight:500; }}
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
.browser-warning {{ background:#3a2d12; border:1px solid #7f6528; color:#ffe7a3; box-shadow:0 6px 20px rgba(0,0,0,.18); }}
.browser-warning strong {{ color:#ffd66b; margin-right:5px; }}
.grid {{ display:grid; grid-template-columns:repeat(auto-fill,minmax(360px,1fr)); gap:18px; }}
.card {{ display:grid; grid-template-columns:150px 1fr; min-height:225px; background:var(--panel); border:1px solid var(--line); border-radius:12px; overflow:hidden; box-shadow:0 8px 26px rgba(0,0,0,.16); }}
.poster-slot {{ width:150px; height:225px; background:#0d0f13; }}
.poster {{ width:150px; height:225px; object-fit:cover; background:#0d0f13; }} .placeholder {{ display:grid; place-items:center; color:#6f7784; text-align:center; }}
.content {{ padding:14px 15px; min-width:0; display:flex; flex-direction:column; }} .topline {{ display:flex; justify-content:space-between; gap:8px; color:var(--muted); font-size:.78rem; }}
.kind,.status,.kids-badge {{ border:1px solid #3a424f; border-radius:999px; padding:2px 7px; }} .badges {{ display:flex; gap:5px; align-items:center; }} .kids-badge {{ border-color:#7c6231; color:#ffd978; }} h2 {{ margin:8px 0 2px; font-size:1.15rem; }} h2 small {{ color:var(--muted); font-weight:500; }}
.rating {{ color:var(--accent); font-size:1.1rem; font-weight:800; }} .rating span {{ color:var(--muted); font-size:.8rem; }} .facts,.links,.detected {{ color:var(--muted); font-size:.84rem; }} .links {{ align-items:center; flex-wrap:wrap; }}
.age-rating {{ display:flex; align-items:center; gap:4px; flex-wrap:wrap; margin-top:2px; }}
.seasons {{ display:flex; align-items:center; gap:5px; flex-wrap:wrap; margin-top:4px; }}
.season-badges {{ display:inline-flex; flex-wrap:wrap; gap:4px; }}
.card > .seasons {{ grid-column:1/-1; padding:6px 12px 0; }}
.season-badge {{ display:inline-flex; align-items:center; justify-content:center; min-width:38px; padding:2px 6px; border-radius:999px; border:1px solid rgba(160,170,185,.28); font-size:.74rem; line-height:1.25; }}
.season-badge.available {{ background:rgba(76,175,80,.16); border-color:rgba(95,190,100,.42); color:#a7e7aa; }}
.season-badge.missing {{ background:rgba(140,150,165,.08); color:var(--muted); opacity:.72; }}
.awards {{ margin-top:3px; }}
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
.trailer-link {{ display:inline-flex; align-items:center; padding:4px 8px; border-radius:7px; border:1px solid #704248; background:#392327; color:#ffb7bd; text-decoration:none; font-weight:700; }}
.trailer-link:hover {{ background:#4a2b30; color:#ffd2d6; }}
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
.alphabet-nav {{ position:fixed; z-index:7; right:7px; top:50%; transform:translateY(-50%); display:flex; flex-direction:column; gap:1px; padding:5px 4px; max-height:calc(100vh - 150px); overflow-y:auto; border:1px solid rgba(75,85,99,.7); border-radius:10px; background:rgba(17,19,24,.88); backdrop-filter:blur(8px); box-shadow:0 6px 20px rgba(0,0,0,.24); scrollbar-width:none; }}
.alphabet-nav::-webkit-scrollbar {{ display:none; }}
.alphabet-nav button {{ width:24px; min-height:20px; padding:1px 0; border-radius:5px; background:transparent; color:#cdd3dd; font-size:.69rem; line-height:1; font-weight:750; }}
.alphabet-nav button:hover:not(:disabled),.alphabet-nav button:focus-visible {{ background:#343c48; color:#fff; }}
.alphabet-nav button:disabled {{ color:#505865; cursor:default; opacity:.42; }}
.card {{ scroll-margin-top:185px; }}
.card.letter-jump {{ outline:2px solid rgba(245,196,81,.8); outline-offset:2px; }}
@media (max-width:1050px) {{ .filter-panel {{ grid-template-columns:repeat(3,minmax(140px,1fr)); }} }}
@media (max-width:760px) {{ .header-main {{ align-items:flex-start; }} .header-actions {{ justify-content:flex-start; width:100%; }} .search-row {{ flex-wrap:wrap; }} .search-row .main-search,.search-row .filename-search {{ flex:1 1 100%; width:100%; }} .filter-toggle,.search-row .reset-filters {{ flex:1 1 auto; }} .filter-panel {{ grid-template-columns:repeat(2,minmax(130px,1fr)); }} }}
@media (max-width:480px) {{ .brand-row {{ width:100%; justify-content:space-between; }} .filter-panel {{ grid-template-columns:1fr; }} }}
@media (max-width:560px) {{ .grid {{ grid-template-columns:1fr; }} .card {{ grid-template-columns:105px 1fr; }} .poster-slot,.poster {{ width:105px; height:158px; }} .random-layout {{ grid-template-columns:95px minmax(0,1fr); gap:12px; }} .random-poster {{ width:95px; height:143px; }} .alphabet-nav {{ right:3px; padding:3px 2px; }} .alphabet-nav button {{ width:20px; min-height:18px; font-size:.61rem; }} }}

/* Mnemosyne Metro UI – no external fonts, icon libraries, animation loops or new data calls. */
:root {{--bg:#1a2634;--panel:#212f3c;--line:#334554;--muted:#b7c7d7;--accent:#81c9e8;--play:#35b7b1;--play-hover:#44cec4}}
html {{scroll-behavior:smooth}}
body {{background-color:#142332 !important;background-image:{metro_background_image} !important;background-size:cover !important;background-position:center center !important;background-repeat:no-repeat !important;background-attachment:fixed !important;font-family:'Segoe UI','Noto Sans','DejaVu Sans',system-ui,sans-serif;color:#f1f5fa}}
header {{position:sticky;top:0;z-index:10;background:rgba(28,43,58,.95);border-bottom:1px solid #344655;backdrop-filter:none;box-shadow:none;padding:15px 28px}}
.header-main {{flex-wrap:nowrap;gap:24px}}
.brand-row {{gap:16px;flex:0 0 auto}}
.metro-logo {{width:52px;height:52px;flex:none;display:grid;place-items:center;border-right:1px solid #536879;padding-right:10px}}
.metro-logo svg {{display:block}}
.metro-brand-text {{display:flex;flex-direction:column;gap:4px}}
.brand-title {{font-family:'Montserrat','Avenir Next','Century Gothic','Gotham','DejaVu Sans',sans-serif;font-size:1.65rem;letter-spacing:.13em;font-weight:750;line-height:1.05;font-stretch:normal;text-shadow:none}}
.metro-brand-subtitle {{font-size:.64rem;font-weight:650;letter-spacing:.27em;color:#a4c0d4;white-space:nowrap}}
.header-actions {{gap:9px;flex-wrap:nowrap}}
.header-actions button,.header-actions select {{font-size:.8rem;min-height:37px;padding:9px 12px}}
button {{border-radius:3px;transition:background-color .1s ease, border-color .1s ease}}
button:focus-visible,a:focus-visible,input:focus-visible,select:focus-visible {{outline:2px solid #8bdcef;outline-offset:2px}}
input[type=search],input[name=imdb],select {{background:#142332;border:1px solid #415668;border-radius:3px;color:#f5f8fd}}
.metro-layout {{display:grid;grid-template-columns:218px minmax(0,1fr);min-height:calc(100vh - 83px)}}
.metro-sidebar {{background:rgba(27,42,58,.89);border-right:1px solid #344b5d;position:sticky;top:83px;height:calc(100vh - 83px);display:flex;flex-direction:column;padding:34px 0 18px}}
.metro-nav-btn {{display:flex;align-items:center;gap:17px;width:100%;text-align:left;border-radius:0;background:transparent;color:#dfecf4;padding:18px 22px;font-size:.94rem;font-weight:500;min-height:60px}}
.metro-nav-btn:hover {{background:#2b3c51}}
.metro-nav-btn.active,.metro-nav-btn.active:hover {{background:#6147a7;color:#fff}}
.metro-nav-icon {{font-family:'Segoe UI Symbol',sans-serif;font-size:1.55rem;width:30px;text-align:center;line-height:1}}
.metro-sidebar-footer {{margin-top:auto;padding:14px 22px;color:#7d94a6;font-size:.67rem;letter-spacing:.14em}}
.metro-sidebar-footer span {{display:block;letter-spacing:.04em;margin-top:5px}}
.metro-content {{min-width:0;padding:23px 27px 60px}}
.metro-overview {{display:block;margin-bottom:26px}}
.metro-overview[hidden] {{display:none !important}}
.metro-metrics {{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px}}
.metric-tile {{min-height:121px;border-radius:0;display:grid;grid-template-columns:68px auto;grid-template-rows:1fr 1fr;align-items:center;justify-content:stretch;column-gap:18px;text-align:left;padding:20px 28px;color:#fff;box-shadow:none}}
.metric-tile:hover {{filter:brightness(1.09)}}
.metric-movies {{background:#195a81}}
.metric-series {{background:#227d8d}}
.metric-all {{background:#614a99}}
.metric-icon {{grid-row:1/3;font-size:3rem;font-weight:300;line-height:1;text-align:center;color:#f0fbff}}
.metric-number {{font-size:2.7rem;font-weight:400;line-height:1;letter-spacing:.02em}}
.metric-label {{font-size:.9rem;font-weight:400;opacity:.88;align-self:start}}
.metro-section-title {{display:flex;align-items:center;justify-content:space-between;margin:30px 0 16px;gap:12px}}
.metro-section-title h2,.metro-library-heading h2 {{margin:0;font-size:1.35rem;letter-spacing:.005em;font-weight:580}}
.metro-all-link {{background:none;color:#c9dde9;border:0;font-weight:500;font-size:.86rem}}
.metro-all-link:hover {{background:#2b4052}}
.metro-featured {{display:grid;grid-template-columns:repeat(5,minmax(0,1fr));gap:12px;align-items:start}}
.featured-item {{min-width:0;padding:0;background:rgba(28,43,57,.95);color:#e7f0f8;border:1px solid #344858;border-radius:0;text-align:left;overflow:hidden}}
.featured-item:hover {{background:#2c4255;border-color:#6394a6}}
.featured-item img,.featured-placeholder {{display:block;width:100%;height:clamp(190px,19vw,305px);object-fit:contain;object-position:center center;background:rgba(10,22,32,.96)}}
.featured-placeholder {{display:grid;place-items:center;font-size:3rem;color:#9dacc0}}
.featured-title {{display:block;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;padding:9px 9px 10px;font-weight:560;font-size:.83rem}}
.metro-library-section[hidden],.alphabet-nav[hidden] {{display:none !important}}
.metro-library-heading {{display:flex;align-items:center;gap:13px;margin:20px 0 14px;scroll-margin-top:100px}}
.metro-count {{background:#344b5f;padding:3px 10px;font-size:.8rem;color:#d4e1eb}}
.search-row {{margin:0 0 12px;gap:8px}}
.search-row input {{min-height:44px}}
.filter-panel {{background:#1e2e3d;border-color:#334c5f;border-radius:0;margin:0 0 10px}}
.meta {{color:#8099ae;font-size:.72rem;margin:12px 0 20px;line-height:1.45}}
.server-health {{background:transparent;border-color:#435667;border-radius:3px}}
.server-led.online {{box-shadow:none}}
main {{padding:0}}
.grid {{grid-template-columns:repeat(auto-fill,minmax(345px,1fr));gap:12px}}
.card {{background:rgba(36,51,65,.93);border:1px solid #3a4a58;border-radius:0;box-shadow:none;content-visibility:auto;contain-intrinsic-size:auto 290px}}
.card:hover {{border-color:#6289a3}}
.content {{padding:13px 14px}}
.kind,.status,.kids-badge {{border-radius:2px;border-color:#546475}}
.card h2 {{font-size:1.06rem;font-weight:660;letter-spacing:.005em}}
.card h2 small {{font-weight:400}}
.rating {{color:#7dd8e8}}
.links {{gap:9px}}
a {{color:#a5dbef}}
.trailer-link {{border-radius:2px;background:#2d4456;color:#c5e8f2;border-color:#527589}}
.trailer-link:hover {{background:#365b70;color:#fff}}
.play-button {{background:#25877f;border-radius:2px;color:#fff;border-color:#309d95;box-shadow:none}}
.play-button:hover {{background:#2f9b91}}
.random-movie-button {{background:#6952aa}}
.pdf-button {{background:#277990}}
.config-button,.config-close,.reset-filters,.filter-toggle {{background:#34485a;border-color:#557084;border-radius:3px}}
.favorite-btn {{padding:0 4px;background:transparent;color:#98adbf;font-size:1.3rem;line-height:1.1;border:0}}
.favorite-btn:hover,.favorite-btn.active {{color:#e6c36e;background:transparent}}
.alphabet-nav {{border-radius:2px;right:3px;background:#1a2a39;border-color:#355168;box-shadow:none;backdrop-filter:none}}
.card {{scroll-margin-top:102px}}
dialog.config-dialog,dialog.random-dialog {{background:#223444;border-color:#4a6175;border-radius:4px}}
.browser-warning {{border-radius:2px;background:#494021;color:#fff0bd}}
@media(max-width:1250px){{.metro-layout{{grid-template-columns:175px minmax(0,1fr)}}.metro-sidebar{{padding-top:17px}}.metro-nav-btn{{padding:15px 17px}}.metro-content{{padding:20px 19px 40px}}.metric-tile{{padding:16px 18px;grid-template-columns:46px auto;column-gap:12px}}.metric-icon{{font-size:2.5rem}}.metro-featured{{grid-template-columns:repeat(4,minmax(0,1fr))}}.featured-item img,.featured-placeholder{{height:clamp(165px,24vw,275px)}}.header-actions{{justify-content:flex-end}}}}
@media(max-width:950px){{.header-actions{{flex-wrap:wrap}}header{{padding:12px 16px}}.header-main{{flex-wrap:wrap}}.metro-layout{{grid-template-columns:1fr}}.metro-sidebar{{height:auto;top:0;position:static;flex-direction:row;overflow-x:auto;padding:0;border-bottom:1px solid #405769}}.metro-nav-btn{{min-height:52px;width:auto;white-space:nowrap;padding:12px 16px}}.metro-nav-icon{{font-size:1.2rem;width:22px}}.metro-sidebar-footer{{display:none}}.metro-metrics{{gap:8px}}.metro-featured{{grid-template-columns:repeat(3,minmax(0,1fr))}}.featured-item img,.featured-placeholder{{height:clamp(200px,40vw,300px)}}}}
@media(max-width:600px){{.metro-logo{{width:40px;height:40px}}.metro-logo svg{{width:38px;height:38px}}.brand-title{{font-size:1.25rem}}.metro-brand-subtitle{{font-size:.47rem}}.metro-content{{padding:16px 12px 35px}}.metro-metrics{{grid-template-columns:repeat(3,minmax(0,1fr))}}.metric-tile{{padding:9px;grid-template-columns:1fr;grid-template-rows:auto auto;min-height:92px;gap:3px}}.metric-icon{{display:none}}.metric-number{{font-size:1.85rem}}.metric-label{{font-size:.74rem}}.metro-featured{{grid-template-columns:repeat(2,minmax(0,1fr))}}.grid{{grid-template-columns:1fr}}.card{{grid-template-columns:105px minmax(0,1fr)}}.poster-slot,.poster{{width:105px;height:158px}}.header-actions button{{padding:7px}}.metro-nav-btn{{font-size:.77rem;gap:7px;padding:9px}}}}
/* v4.15.19: poster and facts in a two-column header; plot and actions full width.
   Alphabet keeps a dedicated right gutter; the last-letter tail is added only on demand. */
.metro-content {{padding-right:106px}}
.metro-library-section .grid {{
  grid-template-columns:repeat(auto-fill,minmax(min(100%,250px),1fr));
  gap:14px;
  align-items:stretch;
}}
.metro-library-section .card {{
  display:flex;
  flex-direction:column;
  min-width:0;
  min-height:0;
  grid-template-columns:none;
  contain-intrinsic-size:auto 590px;
  background:rgba(33,49,64,.93);
}}
.metro-library-section .card .card-top {{
  display:grid;
  grid-template-columns:minmax(95px,43%) minmax(0,1fr);
  align-items:start;
  column-gap:10px;
  padding:11px 11px 0;
  width:100%;
  min-width:0;
}}
.metro-library-section .card .poster-slot {{
  width:100%;
  height:auto;
  aspect-ratio:2/3;
  min-height:0;
  background:rgba(12,23,33,.7);
  display:flex;
  justify-content:center;
  align-items:center;
  overflow:hidden;
}}
.metro-library-section .card .poster {{
  display:block;
  width:100%;
  height:100%;
  object-fit:contain;
  object-position:center;
}}
.metro-library-section .card .poster.placeholder {{display:grid;place-items:center}}
.metro-library-section .card .poster.poster-fallback[style*="none"] {{display:none}}
.metro-library-section .card .card-summary {{min-width:0;display:flex;flex-direction:column;gap:2px}}
.metro-library-section .card .topline {{gap:4px;flex-wrap:wrap;font-size:.68rem}}
.metro-library-section .card .badges {{gap:3px;max-width:100%}}
.metro-library-section .card .kind,.metro-library-section .card .status,.metro-library-section .card .kids-badge {{font-size:.64rem;padding:2px 4px}}
.metro-library-section .card .favorite-btn {{font-size:1.1rem}}
.metro-library-section .card h2 {{font-size:.95rem;line-height:1.24;margin:5px 0 3px;overflow-wrap:anywhere}}
.metro-library-section .card h2 small {{font-size:.73rem;white-space:normal}}
.metro-library-section .card .card-summary .rating {{font-size:1rem;margin-bottom:2px}}
.metro-library-section .card .facts {{font-size:.73rem;line-height:1.34;overflow-wrap:anywhere}}
/* Season availability spans the whole card, including the area under the poster. */
.metro-library-section .card > .seasons {{
  display:flex;
  align-items:flex-start;
  flex-wrap:wrap;
  gap:5px;
  width:100%;
  min-width:0;
  padding:9px 12px 0;
  margin-top:0;
  box-sizing:border-box;
}}
.metro-library-section .card > .seasons .season-badges {{
  display:flex;
  flex:1 1 100%;
  width:100%;
  flex-wrap:wrap;
  justify-content:flex-start;
  align-items:center;
  gap:4px;
}}
.metro-library-section .card > .seasons .season-badge {{flex:0 0 auto;}}
/* Compact seasons: no row-to-row equalization and no reserved blank zones.
   Three lines are visible by default; the rest can be expanded per card. */
.metro-library-section .card > .seasons {{
  border-top:1px solid rgba(140,173,194,.24);
  margin:13px 12px 0;
  padding:10px 0 0;
  width:calc(100% - 24px);
  display:block;
}}
.metro-library-section .card > .seasons .season-count {{font-weight:600;color:#d5e5ed}}
.metro-library-section .card > .seasons .season-badges {{
  display:flex;
  width:100%;
  flex-wrap:wrap;
  gap:4px;
  margin-top:8px;
  max-height:44px; /* 2 lines of 20px pills with 4px gap */
  overflow:hidden;
  align-content:flex-start;
}}
.metro-library-section .card > .seasons .season-badge {{
  flex:0 0 auto;
  box-sizing:border-box;
  height:20px;
  line-height:15px;
  padding:2px 6px;
}}
.metro-library-section .card > .seasons .season-badges.expanded {{
  max-height:none;
  overflow:visible;
}}
.metro-library-section .card > .seasons .season-expand {{
  display:block;
  width:100%;
  margin:7px 0 0;
  padding:3px 0;
  background:none;
  border:0;
  color:#9fe5ec;
  text-align:left;
  cursor:pointer;
  font-size:.78rem;
  font-weight:600;
}}
.metro-library-section .card > .seasons .season-expand[hidden] {{display:none;}}
.metro-library-section .card > .seasons .season-expand:hover {{text-decoration:underline;}}
.metro-library-section .card .content.card-bottom {{padding-top:13px;}}
/* The compact series header contains ONLY title, rating, genre and age.
   All secondary details remain accessible through the explicit toggle.
   This keeps the header no taller than the poster in the usual case. */
.metro-library-section .card[data-kind="series"] .card-summary:not(.meta-expanded) .added-date,
.metro-library-section .card[data-kind="series"] .card-summary:not(.meta-expanded) .director,
.metro-library-section .card[data-kind="series"] .card-summary:not(.meta-expanded) .actors,
.metro-library-section .card[data-kind="series"] .card-summary:not(.meta-expanded) .awards {{
  display:none;
}}
.metro-library-section .card[data-kind="series"] .card-summary.meta-expanded .added-date,
.metro-library-section .card[data-kind="series"] .card-summary.meta-expanded .director,
.metro-library-section .card[data-kind="series"] .card-summary.meta-expanded .actors,
.metro-library-section .card[data-kind="series"] .card-summary.meta-expanded .awards {{
  display:block;
  overflow:visible;
}}
.metro-library-section .card .meta-expand {{
  background:none;
  border:0;
  padding:5px 0 0;
  color:#9fe5ec;
  font-size:.73rem;
  text-align:left;
  cursor:pointer;
}}
.metro-library-section .card .meta-expand[hidden] {{display:none;}}
.metro-library-section .card .meta-expand:hover {{text-decoration:underline;}}
.metro-library-section .card .content.card-bottom {{padding-top:12px;}}


/* Series description follows the season badges immediately; buttons stay at the bottom.
   The top header is as tall as the cover (not a variable-length award list). */
.metro-library-section .card[data-kind="series"] .card-top {{align-items:start;}}
.metro-library-section .card[data-kind="series"] > .seasons {{margin-top:12px;}}
.metro-library-section .card[data-kind="series"] .content.card-bottom {{padding-top:12px;}}
.metro-library-section .card[data-kind="series"] .meta-expand {{line-height:1.25;}}

.metro-library-section .card .content.card-bottom {{
  flex:1;
  width:100%;
  min-width:0;
  padding:11px 12px 10px;
  display:flex;
  flex-direction:column;
}}
.metro-library-section .card .localized-plot {{font-size:.83rem;line-height:1.43;overflow-wrap:break-word;margin:0 0 7px}}
.metro-library-section .card .links {{
  display:grid;
  grid-template-columns:repeat(2,minmax(0,1fr));
  align-items:stretch;
  gap:7px;
  width:100%;
  padding-top:9px;
  margin-top:auto;
}}
.metro-library-section .card .links a {{
  display:flex;
  min-width:0;
  min-height:32px;
  align-items:center;
  justify-content:center;
  text-align:center;
  font-size:.79rem;
  border:1px solid #49657c;
  padding:5px 4px;
  text-decoration:none;
  background:rgba(35,58,75,.78);
  color:#c7e3ee;
}}
.metro-library-section .card .links a.trailer-link {{background:#28475b;border-color:#53788e}}
.metro-library-section .card .links .play-button {{
  grid-column:1 / -1;
  width:100%;
  min-height:34px;
  text-align:center;
}}
.metro-library-section .card .links > span {{
  grid-column:1 / -1;
  text-align:center;
  color:#a6b9c8;
  font-size:.73rem;
}}
.metro-library-section .card details {{width:100%;min-width:0;margin-top:8px}}
.metro-library-section .card .paths {{overflow-wrap:anywhere}}
.alphabet-jump-tail {{height:0;pointer-events:none}}
.alphabet-nav {{right:36px;width:34px;padding:6px 4px;align-items:center;z-index:9}}
.alphabet-nav button {{min-width:24px;min-height:20px}}
@media (max-width:1050px) {{
  .metro-library-section .grid {{grid-template-columns:repeat(auto-fill,minmax(min(100%,260px),1fr))}}
  .metro-content {{padding-right:88px}}
  .alphabet-nav {{right:28px;width:31px;padding:4px 2px}}
}}
@media (max-width:600px) {{
  .metro-content {{padding-right:76px}}
  .metro-library-section .grid {{grid-template-columns:repeat(auto-fill,minmax(min(100%,240px),1fr));gap:9px}}
  .metro-library-section .card .card-top {{grid-template-columns:minmax(90px,41%) minmax(0,1fr);gap:8px;padding:9px 9px 0}}
  .metro-library-section .card .content.card-bottom {{padding:10px 9px}}
  .alphabet-nav {{right:22px;width:29px}}
}}
@media (max-width:430px) {{
  .metro-library-section .grid {{grid-template-columns:1fr}}
  .metro-library-section .card .card-top {{grid-template-columns:minmax(94px,38%) minmax(0,1fr)}}
}}


/* v4.15.19 – Overview posters: card == image width. No crop, no wide letterbox. */
.metro-layout.showing-overview .metro-content {{padding-right:27px}}
.metro-featured {{
  grid-template-columns:repeat(auto-fill, 190px);
  gap:13px;
  align-items:start;
  justify-content:start;
}}
.metro-featured .featured-item {{width:190px;max-width:100%;min-width:0;align-self:start}}
.metro-featured .featured-item img {{
  display:block;
  width:100%;
  height:auto;
  max-width:100%;
  min-height:0;
  aspect-ratio:auto;
  object-fit:contain;
  object-position:center;
  background:none;
}}
.metro-featured .featured-placeholder {{width:100%;height:auto;aspect-ratio:2 / 3;min-height:0}}
.metro-featured .featured-title {{
  display:-webkit-box;
  -webkit-line-clamp:2;
  line-clamp:2;
  -webkit-box-orient:vertical;
  overflow:hidden;
  white-space:normal;
  line-height:1.3;
  min-height:2.75em;
  padding:7px 8px;
  font-size:.78rem;
}}
.metro-sidebar-footer {{letter-spacing:.07em;line-height:1.5}}
.metro-sidebar-footer strong {{color:#bdcddd;font-weight:650;letter-spacing:.11em}}
.metro-sidebar-footer .metro-author-line {{
  display:block;
  margin-top:5px;
  font-size:inherit;
  letter-spacing:.04em;
  line-height:1.5;
  color:inherit;
}}
@media (max-width:950px) {{
  .metro-featured {{grid-template-columns:repeat(auto-fill, 170px)}}
  .metro-featured .featured-item {{width:170px}}
  .metro-layout.showing-overview .metro-content {{padding-right:19px}}
}}
@media (max-width:600px) {{
  .metro-featured {{grid-template-columns:repeat(auto-fill, minmax(132px, 1fr));gap:10px}}
  .metro-featured .featured-item {{width:100%}}
  .metro-layout.showing-overview .metro-content {{padding-right:12px}}
}}

/* v4.15.19: larger responsive posters, with complete multiline titles.
   Film/series listing cards are intentionally left untouched. */
.metro-layout.showing-overview .metro-content {{padding:26px 34px 76px}}
.metro-layout.showing-overview .metro-overview {{max-width:1510px}}
.metro-layout.showing-overview .metro-metrics {{max-width:1070px;gap:12px}}
.metro-layout.showing-overview .metric-tile {{min-height:114px}}
.metro-layout.showing-overview .metro-section-title {{justify-content:flex-start;gap:14px;margin:30px 0 17px}}
.metro-layout.showing-overview .metro-featured {{
  display:grid;
  grid-template-columns:repeat(10,minmax(0,1fr));
  gap:10px;
  max-width:1510px;
  align-items:stretch;
}}
.metro-layout.showing-overview .featured-item {{
  width:auto;min-width:0;max-width:none;
  height:100%;
  display:flex;flex-direction:column;
  background:rgba(18,39,56,.76);
  border:1px solid rgba(125,173,197,.26);
  transition:background-color .14s ease,border-color .14s ease;
}}
.metro-layout.showing-overview .featured-item:hover {{background:rgba(33,66,88,.93);border-color:#8eb6c9}}
.metro-layout.showing-overview .featured-item img {{
  width:100%;height:auto;min-height:0;max-width:100%;
  aspect-ratio:2 / 3;object-fit:contain;object-position:center;
  background:rgba(9,19,29,.20);
}}
.metro-layout.showing-overview .featured-placeholder {{width:100%;aspect-ratio:2/3}}
.metro-layout.showing-overview .featured-title {{
  flex:1;display:block;overflow:visible;white-space:normal;
  overflow-wrap:anywhere;word-break:normal;
  line-height:1.35;padding:9px 8px 12px;min-height:0;
  font-size:.79rem;font-weight:560;
}}
/* Keep the film noir wallpaper visible to the right and below the tiles. */
.metro-layout.showing-overview {{background:linear-gradient(90deg,rgba(10,27,42,.18),rgba(10,27,42,.06) 68%,transparent 100%)}}
@media(max-width:1540px) {{
 .metro-layout.showing-overview .metro-featured {{grid-template-columns:repeat(8,minmax(0,1fr));max-width:1250px}}
 .metro-layout.showing-overview .metro-metrics {{max-width:1000px}}
}}
@media(max-width:1240px) {{
 .metro-layout.showing-overview .metro-featured {{grid-template-columns:repeat(6,minmax(0,1fr));max-width:1000px}}
 .metro-layout.showing-overview .metro-metrics {{max-width:850px}}
}}
@media(max-width:930px) {{
 .metro-layout.showing-overview .metro-content {{padding:18px 19px 55px}}
 .metro-layout.showing-overview .metro-featured {{grid-template-columns:repeat(4,minmax(0,1fr));max-width:640px;gap:9px}}
}}
@media(max-width:580px) {{
 .metro-layout.showing-overview .metro-content {{padding:14px 12px 42px}}
 .metro-layout.showing-overview .metro-featured {{grid-template-columns:repeat(2,minmax(0,1fr));max-width:420px}}
 .metro-layout.showing-overview .metro-metrics {{grid-template-columns:repeat(3,minmax(0,1fr))}}
}}

/* Expanding text only affects the card whose button was pressed. */
.metro-library-section .card .localized-plot:not(.expanded) {{
  display:-webkit-box;
  -webkit-box-orient:vertical;
  -webkit-line-clamp:5;
  line-clamp:5;
  overflow:hidden;
}}
.metro-library-section .card .plot-more {{
  border:0;
  background:none;
  color:#a4dfed;
  padding:0;
  margin:0 0 6px;
  font-size:.76rem;
  text-align:left;
  align-self:flex-start;
  min-height:22px;
}}
.metro-library-section .card .plot-more:hover {{background:none;text-decoration:underline;color:#fff}}

@media(prefers-reduced-motion:reduce){{html{{scroll-behavior:auto}}}}


/* Credentials are requested only in memory, never written to config or storage. */
dialog.smb-auth-dialog {{width:min(420px,calc(100% - 28px));padding:0;background:#223444;color:#f5f7fa;border:1px solid #536a80;border-radius:5px;box-shadow:0 25px 65px rgba(0,0,0,.55)}}
dialog.smb-auth-dialog::backdrop {{background:rgba(0,0,0,.73)}}
.smb-auth-inner {{padding:25px;display:flex;flex-direction:column;gap:13px}}
.smb-auth-inner h2 {{margin:0 0 2px;font-size:1.22rem}}
.smb-auth-inner p {{margin:0;color:#b4cadb;line-height:1.45;font-size:.91rem}}
.smb-auth-inner label {{display:flex;flex-direction:column;gap:5px;font-size:.9rem}}
.smb-auth-inner input {{width:100%;box-sizing:border-box;background:#101e2b;color:white;border:1px solid #647f92;border-radius:3px;padding:10px;font-size:1rem}}
.smb-auth-actions {{display:flex;justify-content:flex-end;gap:10px;margin-top:4px}}
/* Persistent scan progress modal: independent from the initial library warmup. */
dialog.scan-progress-dialog {{width:min(480px,calc(100% - 30px));background:#223444;color:#eff8ff;padding:0;border:1px solid #56758e;border-radius:5px;box-shadow:0 24px 70px #0009}}
dialog.scan-progress-dialog::backdrop {{background:rgba(5,12,20,.8);backdrop-filter:blur(3px)}}
.scan-progress-inner {{padding:30px;display:flex;flex-direction:column;gap:15px;align-items:center;text-align:center}}
.scan-progress-inner h2 {{font-size:1.18rem;margin:0}}
.scan-progress-inner p {{margin:0;color:#c2d6e6;line-height:1.5}}
.scan-progress-inner progress {{width:100%;height:15px;accent-color:#72c8e7}}
.scan-progress-inner #scanProgressCount {{font-size:.91rem;font-weight:600}}
.scan-progress-inner .scan-progress-current {{font-size:.82rem;max-width:100%;overflow-wrap:anywhere;min-height:1.4em;opacity:.82}}
/* Short, non-blocking visual feedback before first large library layout. */
.library-loading {{position:fixed;inset:0;z-index:30;display:flex;align-items:center;justify-content:center;background:rgba(9,22,34,.88);backdrop-filter:blur(3px);}}
.library-loading[hidden] {{display:none !important}}
.library-loading-panel {{display:flex;flex-direction:column;align-items:center;gap:15px;padding:28px 42px;background:rgba(27,44,62,.96);border:1px solid #56758e;box-shadow:0 14px 52px rgba(0,0,0,.32);color:#e5f4ff;font-weight:600;letter-spacing:.03em}}
.library-loading-detail {{font-size:.82rem;max-width:330px;text-align:center;color:#a8c9db;font-weight:400;line-height:1.5}}
.library-spinner {{width:41px;height:41px;border:4px solid rgba(126,199,229,.2);border-top-color:#81c9e8;border-radius:50%;animation:library-spin .85s linear infinite}}
@keyframes library-spin {{to {{transform:rotate(360deg)}}}}
@media (prefers-reduced-motion:reduce) {{.library-spinner {{animation:none;border-top-color:#81c9e8}}}}


/* v4.15.44 -- EXACT SIZES in the collapsed state, not minmax(auto).
   This is restricted to series cards. Content in excess of its track is
   clipped; its own accessible expansion button lets that track grow. */
.metro-library-section .card[data-kind="series"] {{
  --series-header-h:224px;
  --series-seasons-h:110px;
  --series-description-h:120px;
  --series-actions-h:132px;
  display:grid;
  grid-template-columns:minmax(0,1fr);
  grid-template-rows:var(--series-header-h) var(--series-seasons-h) calc(var(--series-description-h) + var(--series-actions-h));
  height:calc(var(--series-header-h) + var(--series-seasons-h) + var(--series-description-h) + var(--series-actions-h));
  min-height:0;
  align-items:stretch;
  align-content:start;
}}
.metro-library-section .card[data-kind="series"] > .card-top {{
  box-sizing:border-box;
  width:100%;height:var(--series-header-h);min-height:0;
  margin:0;padding:11px 11px 10px;
  overflow:hidden;
  align-items:start;
}}
.metro-library-section .card[data-kind="series"] .poster-slot {{
  width:100%;max-height:182px;aspect-ratio:2/3;
}}
.metro-library-section .card[data-kind="series"] .card-summary {{
  min-height:0;max-height:197px;overflow:hidden;
}}
.metro-library-section .card[data-kind="series"] > .seasons {{
  display:block;
  box-sizing:border-box;
  height:var(--series-seasons-h);min-height:0;
  width:calc(100% - 24px);margin:0 12px;
  padding:10px 0 8px;overflow:hidden;
  border-top:1px solid rgba(140,173,194,.28);
}}
.metro-library-section .card[data-kind="series"] > .seasons .season-badges {{
  display:flex;width:100%;flex-wrap:wrap;gap:4px;
  height:auto;max-height:44px;overflow:hidden;
  margin-top:8px;align-content:flex-start;
}}
.metro-library-section .card[data-kind="series"] > .content.card-bottom {{
  display:grid;box-sizing:border-box;
  grid-template-columns:minmax(0,1fr);
  grid-template-rows:var(--series-description-h) var(--series-actions-h);
  width:100%;height:calc(var(--series-description-h) + var(--series-actions-h));
  min-height:0;margin:0;padding:0 12px 10px;overflow:hidden;
}}
.metro-library-section .card[data-kind="series"] .series-description {{
  box-sizing:border-box;height:var(--series-description-h);min-height:0;
  padding-top:11px;overflow:hidden;
}}
.metro-library-section .card[data-kind="series"] .series-actions {{
  box-sizing:border-box;height:var(--series-actions-h);
  min-height:0;display:flex;flex-direction:column;
  justify-content:flex-end;
}}
.metro-library-section .card[data-kind="series"] .series-actions .links {{
  margin-top:0;
}}
.metro-library-section .card[data-kind="series"] .series-actions details {{
  flex-shrink:0;
}}
/* v4.15.44: short synopsis preview MUST leave space for its disclosure.
   Five lines + disclosure no longer fit the 120px fixed description track. */
.metro-library-section .card[data-kind="series"] .series-description .localized-plot:not(.expanded) {{
  display:-webkit-box;
  -webkit-box-orient:vertical;
  -webkit-line-clamp:3;
  line-clamp:3;
  overflow:hidden;
}}
.metro-library-section .card[data-kind="series"] .series-description .plot-more {{
  display:inline-block;
  line-height:20px;
  min-height:20px;
  margin-top:2px;
  padding:0;
  cursor:pointer;
}}
.metro-library-section .card[data-kind="series"] .series-description .plot-more[hidden] {{display:none;}}
/* Hide the optional description disclosure when the text fits. */
.metro-library-section .card[data-kind="series"] .plot-more[hidden] {{display:none;}}
/* A clicked expander grows only its own track; collapsed cards always have
   identical section heights, including when another card has many seasons. */
.metro-library-section .card[data-kind="series"]:has(.meta-expanded) {{
  height:auto;
  grid-template-rows:max-content var(--series-seasons-h) calc(var(--series-description-h) + var(--series-actions-h));
}}
.metro-library-section .card[data-kind="series"]:has(.meta-expanded) > .card-top {{
  height:auto;min-height:var(--series-header-h);overflow:visible;
}}
.metro-library-section .card[data-kind="series"]:has(.meta-expanded) .card-summary {{
  max-height:none;overflow:visible;
}}
.metro-library-section .card[data-kind="series"]:has(> .seasons .season-badges.expanded) {{
  height:auto;
  grid-template-rows:var(--series-header-h) max-content calc(var(--series-description-h) + var(--series-actions-h));
}}
.metro-library-section .card[data-kind="series"]:has(> .seasons .season-badges.expanded) > .seasons {{
  height:auto;min-height:var(--series-seasons-h);overflow:visible;
}}
.metro-library-section .card[data-kind="series"] > .seasons .season-badges.expanded {{
  max-height:none;overflow:visible;
}}
.metro-library-section .card[data-kind="series"]:has(.localized-plot.expanded) {{
  height:auto;
  grid-template-rows:var(--series-header-h) var(--series-seasons-h) max-content;
}}
.metro-library-section .card[data-kind="series"]:has(.localized-plot.expanded) > .content.card-bottom {{
  height:auto;grid-template-rows:max-content var(--series-actions-h);overflow:visible;
}}
.metro-library-section .card[data-kind="series"]:has(.localized-plot.expanded) .series-description {{
  height:auto;min-height:var(--series-description-h);overflow:visible;
}}
/* Combine expansions using the same intrinsic-size behavior for all three
   tracks. */
.metro-library-section .card[data-kind="series"]:has(.meta-expanded):has(> .seasons .season-badges.expanded) {{
  grid-template-rows:max-content max-content calc(var(--series-description-h) + var(--series-actions-h));
}}
.metro-library-section .card[data-kind="series"]:has(.meta-expanded):has(.localized-plot.expanded) {{
  grid-template-rows:max-content var(--series-seasons-h) max-content;
}}
.metro-library-section .card[data-kind="series"]:has(> .seasons .season-badges.expanded):has(.localized-plot.expanded) {{
  grid-template-rows:var(--series-header-h) max-content max-content;
}}
.metro-library-section .card[data-kind="series"]:has(.meta-expanded):has(> .seasons .season-badges.expanded):has(.localized-plot.expanded) {{
  grid-template-rows:max-content max-content max-content;
}}
.metro-library-section .card[data-kind="series"]:has(.series-actions details[open]) {{
  height:auto;
  grid-template-rows:var(--series-header-h) var(--series-seasons-h) max-content;
}}
.metro-library-section .card[data-kind="series"]:has(.series-actions details[open]) > .content.card-bottom {{
  height:auto;grid-template-rows:var(--series-description-h) max-content;overflow:visible;
}}
.metro-library-section .card[data-kind="series"]:has(.series-actions details[open]) .series-actions {{
  height:auto;min-height:var(--series-actions-h);
}}
@media(max-width:600px) {{
  .metro-library-section .card[data-kind="series"] {{
    --series-header-h:220px;
  }}
}}

/* v4.15.44 -- movie cards use the same reliable fixed-track design
   as v4.15.42 series cards, without an empty season section. */
.metro-library-section .card[data-kind="movie"] {{
  --movie-header-h:224px;
  --movie-description-h:120px;
  --movie-actions-h:132px;
  display:grid;
  grid-template-columns:minmax(0,1fr);
  grid-template-rows:var(--movie-header-h) calc(var(--movie-description-h) + var(--movie-actions-h));
  height:calc(var(--movie-header-h) + var(--movie-description-h) + var(--movie-actions-h));
  min-height:0;
  align-items:stretch;
  align-content:start;
}}
.metro-library-section .card[data-kind="movie"] > .card-top {{
  box-sizing:border-box;width:100%;height:var(--movie-header-h);
  min-height:0;margin:0;padding:11px 11px 10px;
  overflow:hidden;align-items:start;
}}
.metro-library-section .card[data-kind="movie"] .poster-slot {{
  width:100%;max-height:182px;aspect-ratio:2/3;
}}
.metro-library-section .card[data-kind="movie"] .card-summary {{
  min-height:0;max-height:197px;overflow:hidden;
}}
.metro-library-section .card[data-kind="movie"] .card-summary:not(.meta-expanded) .added-date,
.metro-library-section .card[data-kind="movie"] .card-summary:not(.meta-expanded) .director,
.metro-library-section .card[data-kind="movie"] .card-summary:not(.meta-expanded) .actors,
.metro-library-section .card[data-kind="movie"] .card-summary:not(.meta-expanded) .awards {{display:none;}}
.metro-library-section .card[data-kind="movie"] .card-summary.meta-expanded .added-date,
.metro-library-section .card[data-kind="movie"] .card-summary.meta-expanded .director,
.metro-library-section .card[data-kind="movie"] .card-summary.meta-expanded .actors,
.metro-library-section .card[data-kind="movie"] .card-summary.meta-expanded .awards {{display:block;overflow:visible;}}
.metro-library-section .card[data-kind="movie"] > .content.card-bottom {{
  display:grid;box-sizing:border-box;
  grid-template-columns:minmax(0,1fr);
  grid-template-rows:var(--movie-description-h) var(--movie-actions-h);
  width:100%;height:calc(var(--movie-description-h) + var(--movie-actions-h));
  min-height:0;margin:0;padding:0 12px 10px;overflow:hidden;
}}
.metro-library-section .card[data-kind="movie"] .series-description {{
  box-sizing:border-box;height:var(--movie-description-h);
  min-height:0;padding-top:11px;overflow:hidden;
}}
.metro-library-section .card[data-kind="movie"] .series-actions {{
  box-sizing:border-box;height:var(--movie-actions-h);
  min-height:0;display:flex;flex-direction:column;justify-content:flex-end;
}}
.metro-library-section .card[data-kind="movie"] .series-actions .links {{margin-top:0;}}
.metro-library-section .card[data-kind="movie"] .series-actions details {{flex-shrink:0;}}
.metro-library-section .card[data-kind="movie"] .series-description .localized-plot:not(.expanded) {{
  display:-webkit-box;-webkit-box-orient:vertical;
  -webkit-line-clamp:3;line-clamp:3;overflow:hidden;
}}
.metro-library-section .card[data-kind="movie"] .series-description .plot-more {{
  display:inline-block;line-height:20px;min-height:20px;margin-top:2px;padding:0;cursor:pointer;
}}
.metro-library-section .card[data-kind="movie"] .series-description .plot-more[hidden] {{display:none;}}
.metro-library-section .card[data-kind="movie"]:has(.meta-expanded) {{
  height:auto;
  grid-template-rows:max-content calc(var(--movie-description-h) + var(--movie-actions-h));
}}
.metro-library-section .card[data-kind="movie"]:has(.meta-expanded) > .card-top {{
  height:auto;min-height:var(--movie-header-h);overflow:visible;
}}
.metro-library-section .card[data-kind="movie"]:has(.meta-expanded) .card-summary {{
  max-height:none;overflow:visible;
}}
.metro-library-section .card[data-kind="movie"]:has(.localized-plot.expanded) {{
  height:auto;grid-template-rows:var(--movie-header-h) max-content;
}}
.metro-library-section .card[data-kind="movie"]:has(.localized-plot.expanded) > .content.card-bottom {{
  height:auto;grid-template-rows:max-content var(--movie-actions-h);overflow:visible;
}}
.metro-library-section .card[data-kind="movie"]:has(.localized-plot.expanded) .series-description {{
  height:auto;min-height:var(--movie-description-h);overflow:visible;
}}
.metro-library-section .card[data-kind="movie"]:has(.meta-expanded):has(.localized-plot.expanded) {{
  grid-template-rows:max-content max-content;
}}
.metro-library-section .card[data-kind="movie"]:has(.series-actions details[open]) {{
  height:auto;grid-template-rows:var(--movie-header-h) max-content;
}}
.metro-library-section .card[data-kind="movie"]:has(.series-actions details[open]) > .content.card-bottom {{
  height:auto;grid-template-rows:var(--movie-description-h) max-content;overflow:visible;
}}
.metro-library-section .card[data-kind="movie"]:has(.series-actions details[open]) .series-actions {{
  height:auto;min-height:var(--movie-actions-h);
}}
.metro-library-section .card[data-kind="movie"]:has(.meta-expanded):has(.series-actions details[open]) {{
  grid-template-rows:max-content max-content;
}}
.metro-library-section .card[data-kind="movie"]:has(.localized-plot.expanded):has(.series-actions details[open]) > .content.card-bottom {{
  grid-template-rows:max-content max-content;
}}
.metro-library-section .card[data-kind="movie"]:has(.meta-expanded):has(.localized-plot.expanded):has(.series-actions details[open]) {{
  grid-template-rows:max-content max-content;
}}
.metro-library-section .card[data-kind="movie"]:has(.meta-expanded):has(.localized-plot.expanded):has(.series-actions details[open]) > .content.card-bottom {{
  grid-template-rows:max-content max-content;
}}
@media(max-width:600px) {{
  .metro-library-section .card[data-kind="movie"] {{--movie-header-h:220px;}}
}}

/* 4.15.44: browser skips layout/paint of off-screen cards. The pre-set intrinsic
   height reserves the correct scroll area until the card enters the viewport. */
.metro-library-section .card[data-kind="movie"] {{
  content-visibility:auto;
  contain-intrinsic-size:auto 476px;
}}
.metro-library-section .card[data-kind="series"] {{
  content-visibility:auto;
  contain-intrinsic-size:auto 586px;
}}
</style>
</head>
<body>
<header>
  <div class="header-main">
    <div class="brand-row">
      <div class="metro-logo" aria-hidden="true"><svg width="51" height="51" viewBox="0 0 54 54" xmlns="http://www.w3.org/2000/svg"><path fill="#b061e4" d="M4 8v38h9V24l14 12v-13Z"/><path fill="#6382ec" d="M27 23v13l14-12v22h9V8Z"/><path fill="#54bbdf" d="M27 23 50 8v11L27 36Z"/><path fill="#9268da" d="M4 8 27 23l-9 8L4 19Z"/></svg></div>
      <div class="metro-brand-text"><h1><span class="brand-title" data-i18n="catalogTitle">MNEMOSYNE</span></h1><div class="metro-brand-subtitle" data-i18n="brandSubtitle">FILM- UND SERIENBIBLIOTHEK</div></div>
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
        <option value="es">ES</option>
      </select>
    </div>
  </div>

</header>
<dialog id="smbAuthDialog" class="smb-auth-dialog" aria-labelledby="smbAuthTitle">
  <form id="smbAuthForm" class="smb-auth-inner" autocomplete="off" onsubmit="submitSmbCredentials(event)">
    <h2 id="smbAuthTitle" data-i18n="smbAuthTitle">SMB-Anmeldung</h2>
    <p data-i18n="smbAuthHint">Für die Aktualisierung der Bibliothek benötigt der Medienserver Zugangsdaten. Sie werden nicht gespeichert.</p>
    <label><span data-i18n="smbUsername">Benutzername</span><input id="smbUsername" name="username" autocomplete="off" autocapitalize="none" spellcheck="false" maxlength="256" required></label>
    <label><span data-i18n="smbPassword">Passwort</span><input id="smbPassword" name="password" type="password" autocomplete="off" maxlength="1024" required></label>
    <div class="smb-auth-actions"><button type="button" class="secondary" onclick="closeSmbAuthDialog()" data-i18n="cancel">Abbrechen</button><button type="submit" id="smbAuthSubmit" data-i18n="smbConnect">Anmelden und aktualisieren</button></div>
  </form>
</dialog>
<dialog id="scanProgressDialog" class="scan-progress-dialog" aria-labelledby="scanProgressTitle" aria-modal="true">
  <div class="scan-progress-inner">
    <span class="library-spinner" aria-hidden="true"></span>
    <h2 id="scanProgressTitle">Bibliothek wird aktualisiert</h2>
    <p id="scanProgressPhase" role="status" aria-live="polite">Verbindung wird hergestellt …</p>
    <progress id="scanProgressBar" max="100"></progress>
    <span id="scanProgressCount">Medien werden gesucht …</span>
    <p id="scanProgressTitleName" class="scan-progress-current"></p>
    <button id="scanProgressClose" class="secondary" type="button" hidden onclick="closeScanProgressDialog()">Schließen</button>
  </div>
</dialog>
<div class="metro-layout">
  <aside class="metro-sidebar" aria-label="Bibliotheks-Navigation">
    <button class="metro-nav-btn active" type="button" data-metro-view="overview" onclick="setMetroView('overview')"><span class="metro-nav-icon">⌂</span><span data-i18n="navOverview">Übersicht</span></button>
    <button class="metro-nav-btn" type="button" data-metro-view="movies" onclick="setMetroView('movies')"><span class="metro-nav-icon">▤</span><span data-i18n="navMovies">Filme</span></button>
    <button class="metro-nav-btn" type="button" data-metro-view="series" onclick="setMetroView('series')"><span class="metro-nav-icon">▣</span><span data-i18n="navSeries">Serien</span></button>
    <button class="metro-nav-btn" type="button" data-metro-view="favorites" onclick="setMetroView('favorites')"><span class="metro-nav-icon">☆</span><span data-i18n="navFavorites">Favoriten</span></button>
    <button class="metro-nav-btn" type="button" data-metro-view="history" onclick="setMetroView('history')"><span class="metro-nav-icon">◷</span><span data-i18n="navHistory">Verlauf</span></button>
    <div class="metro-sidebar-footer"><strong>MNEMOSYNE</strong><span>v4.15.44</span><span class="metro-author-line">Johannes Wronka<br>ChatGPT (OpenAI)</span></div>
  </aside>
  <div class="metro-content">
    <section class="metro-overview" id="metroOverview" aria-label="Bibliotheksübersicht">
      <div class="metro-metrics">
        <button type="button" class="metric-tile metric-movies" onclick="setMetroView('movies')"><span class="metric-icon">▤</span><span class="metric-number">{movie_count}</span><span class="metric-label" data-i18n="navMovies">Filme</span></button>
        <button type="button" class="metric-tile metric-series" onclick="setMetroView('series')"><span class="metric-icon">▣</span><span class="metric-number">{series_count}</span><span class="metric-label" data-i18n="navSeries">Serien</span></button>
        <div class="metric-tile metric-all" role="group"><span class="metric-icon">▱</span><span class="metric-number">{len(rows)}</span><span class="metric-label" data-i18n="metricTotal">Titel gesamt</span></div>
      </div>
      <div class="metro-section-title"><h2 data-i18n="featuredRecent">Zuletzt hinzugefügt</h2><span class="metro-count" aria-label="20 neueste Titel">{len(by_date)} <span data-i18n="titles">Titel</span></span></div>
      <div class="metro-featured" id="metroFeatured">{''.join(featured_html) if featured_html else '<div class="metro-no-featured" data-i18n="noFeatured">Noch keine Datumsangaben vorhanden.</div>'}</div>
    </section>
    <div id="libraryLoading" class="library-loading" role="status" aria-live="polite" aria-label="Bibliothek wird geladen">
      <div class="library-loading-panel"><span class="library-spinner" aria-hidden="true"></span><span id="libraryLoadingText">Bibliothek wird vorbereitet …</span><span id="libraryLoadingDetail" class="library-loading-detail">Bitte einen Moment – Filme und Serien werden vorbereitet.</span></div>
    </div>
    <section class="metro-library-section" id="metroLibrary" hidden>
    <div class="metro-library-heading"><h2 id="metroSectionName" data-i18n="libraryHeading">Alle Titel</h2><span class="metro-count" id="visibleCount">{len(rows)}</span></div>
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
<main>
{browser_warning_html}{notice_html}{error_html}
<div class="grid" id="grid">{''.join(cards)}</div>
<div id="alphabetJumpTail" class="alphabet-jump-tail" aria-hidden="true"></div>
<div class="empty" id="empty" style="display:none" data-i18n="noMatches">Keine passenden Titel.</div>
</main>
    </section>
  </div>
</div>
<nav id="alphabetNav" class="alphabet-nav" hidden aria-label="A–Z navigation">
  {''.join(f'<button type="button" data-letter="{letter}" onclick="jumpToLetter(\'{letter}\')">{letter}</button>' for letter in ['#'] + list('ABCDEFGHIJKLMNOPQRSTUVWXYZ'))}
</nav>
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
        <select id="cfgStartupLanguage"><option value="de">Deutsch</option><option value="en">English</option><option value="es">Español</option></select>

        <label for="cfgScanStartup" data-i18n="cfgScanStartup">Scan beim Start</label>
        <select id="cfgScanStartup"><option value="yes" data-i18n="yes">Ja</option><option value="no" data-i18n="no">Nein</option></select>

        <label for="cfgWindowsMoviesPath" data-i18n="cfgWindowsMoviesPath">Windows: Pfad Filme</label>
        <input id="cfgWindowsMoviesPath" type="text" spellcheck="false">

        <label for="cfgWindowsSeriesPath" data-i18n="cfgWindowsSeriesPath">Windows: Pfad Serien</label>
        <input id="cfgWindowsSeriesPath" type="text" spellcheck="false">

        <label for="cfgLinuxMoviesPath" data-i18n="cfgLinuxMoviesPath">Linux: Pfad Filme</label>
        <input id="cfgLinuxMoviesPath" type="text" spellcheck="false">

        <label for="cfgLinuxSeriesPath" data-i18n="cfgLinuxSeriesPath">Linux: Pfad Serien</label>
        <input id="cfgLinuxSeriesPath" type="text" spellcheck="false">
      </div>
      <p class="config-note" data-i18n="configNote">Änderungen werden in data/config.txt gespeichert. Neue Pfade gelten beim nächsten Bibliotheks-Scan.</p>
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
const METRO_FAV_KEY = 'mnemosyne-metro-favs-v1';
const METRO_HISTORY_KEY = 'mnemosyne-metro-play-v1';
let activeMetroView = 'overview';
let metroRecentSort = false;
function readMetroList(key) {{
  try {{ const list = JSON.parse(localStorage.getItem(key) || '[]'); return Array.isArray(list) ? list.map(String) : []; }}
  catch (_) {{ return []; }}
}}
let metroFavorites = new Set(readMetroList(METRO_FAV_KEY));
let metroHistory = readMetroList(METRO_HISTORY_KEY);
function saveMetroList(key, list) {{ try {{ localStorage.setItem(key, JSON.stringify(list)); }} catch (_) {{}} }}
function updateFavoriteButtons() {{
  document.querySelectorAll('.favorite-btn').forEach(button => {{
    const id = String(button.closest('.card').dataset.mediaId);
    const favored = metroFavorites.has(id);
    button.classList.toggle('active', favored);
    button.textContent = favored ? '★' : '☆';
    button.setAttribute('aria-pressed', favored ? 'true' : 'false');
  }});
}}
function toggleFavorite(id) {{
  id = String(id);
  if (metroFavorites.has(id)) metroFavorites.delete(id); else metroFavorites.add(id);
  saveMetroList(METRO_FAV_KEY, [...metroFavorites]);
  updateFavoriteButtons();
  if (activeMetroView === 'favorites') filterCards();
}}
function rememberPlayed(id) {{
  id = String(id);
  metroHistory = [id, ...metroHistory.filter(x => x !== id)].slice(0, 100);
  saveMetroList(METRO_HISTORY_KEY, metroHistory);
}}
function updateMetroNavigation() {{
  document.querySelectorAll('[data-metro-view]').forEach(button => {{
    const selected = button.dataset.metroView === activeMetroView;
    button.classList.toggle('active', selected);
    button.setAttribute('aria-current', selected ? 'page' : 'false');
  }});
  const layout = document.querySelector('.metro-layout');
  if (layout) layout.classList.toggle('showing-overview', activeMetroView === 'overview');
  const overview = document.getElementById('metroOverview');
  if (overview) overview.hidden = activeMetroView !== 'overview';
  const library = document.getElementById('metroLibrary');
  if (library) library.hidden = activeMetroView === 'overview';
  const az = document.getElementById('alphabetNav');
  if (az) az.hidden = activeMetroView === 'overview';
  const sectionName = document.getElementById('metroSectionName');
  const nameKey = {{overview:'featuredRecent',movies:'navMovies',series:'navSeries',favorites:'navFavorites',history:'navHistory'}}[activeMetroView];
  if (sectionName) sectionName.textContent = t(nameKey || 'libraryHeading');
}}
function clearCatalogFilters() {{
  document.getElementById('search').value = '';
  document.getElementById('filenameSearch').value = '';
  document.getElementById('catalogFilter').value = 'all';
  document.getElementById('genreFilter').value = '';
  document.getElementById('directorFilter').value = '';
  document.getElementById('actorFilter').value = '';
  document.getElementById('recentFilter').value = '';
  toggleFilterPanel(false);
}}
// Keep the startup overlay visible until Chromium has actually completed
// the first library layouts. Loading a tab must never dismiss it prematurely.
let libraryBooting = true;
let libraryLoadGeneration = 0;
function libraryLoadingVisible(show, view, detail) {{
  const overlay = document.getElementById('libraryLoading');
  if (!overlay) return;
  if (show) {{
    const label = document.getElementById('libraryLoadingText');
    const sub = document.getElementById('libraryLoadingDetail');
    const names = {{movies:t('navMovies'),series:t('navSeries')}};
    if (label) label.textContent = view === 'startup'
      ? (activeLanguage === 'en' ? 'Preparing media library …' : activeLanguage === 'es' ? 'Preparando biblioteca …' : 'Medienbibliothek wird vorbereitet …')
      : (activeLanguage === 'en' ? 'Loading ' : activeLanguage === 'es' ? 'Cargando ' : 'Lade ') + (names[view] || t('libraryHeading')) + ' …';
    if (sub && detail) sub.textContent = detail;
  }}
  overlay.hidden = !show;
}}
function browserPaint() {{
  return new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)));
}}
function shortYield() {{return new Promise(resolve => setTimeout(resolve, 70));}}
// Chromium may initially display a generic app icon until it has fetched its
// first favicon. Refresh the link after the resource becomes available; the
// catalog refresh already implicitly did this by navigating to a new page.
async function initializeMnemosyneIcon() {{
  const url = '/mnemosyne_icon.png?v=4.15.44';
  try {{
    const response = await fetch(url, {{cache:'force-cache'}});
    if (!response.ok) return;
    await response.blob();
    const link = document.querySelector('link[rel="icon"]');
    if (link) {{
      const fresh = link.cloneNode();
      fresh.href = url + '&ready=1';
      link.replaceWith(fresh);
    }}
  }} catch (error) {{console.debug('Mnemosyne-Icon:', error);}}
}}
async function waitForOverviewPosters() {{
  // Image requests in the overview must finish (success OR failure) before
  // releasing the startup overlay. Previously `loading=lazy` delayed them.
  const posters = Array.from(document.querySelectorAll('#metroFeatured img'));
  if (!posters.length) return;
  await Promise.race([
    Promise.all(posters.map(img => img.complete ? Promise.resolve() :
      new Promise(resolve => {{
        img.addEventListener('load', resolve, {{once:true}});
        img.addEventListener('error', resolve, {{once:true}});
      }}))),
    new Promise(resolve => setTimeout(resolve, 6000))
  ]);
}}
async function prepareLibraryOnStartup() {{
  // Render and lay out each catalog section BEFORE making the dashboard usable.
  // This work is deliberately scheduled across different tasks so the progress
  // text can be painted, rather than appearing and disappearing in one frame.
  libraryLoadingVisible(true, 'startup');
  try {{
    await browserPaint();
    await shortYield();
    const grid = document.getElementById('grid');
    const library = document.getElementById('metroLibrary');
    const overview = document.getElementById('metroOverview');
    for (const [view, label] of [
      ['movies', [ 'Filme werden vorbereitet …','Preparing movies …','Preparando películas …']],
      ['series', [ 'Serien werden vorbereitet …','Preparing series …','Preparando series …']]
    ]) {{
      document.getElementById('libraryLoadingText').textContent = label[['de','en','es'].indexOf(activeLanguage)];
      const detail = document.getElementById('libraryLoadingDetail');
      if (detail) detail.textContent = activeLanguage === 'en'
        ? 'The catalog is being organized. The overview will unlock automatically.'
        : activeLanguage === 'es'
          ? 'Se está organizando el catálogo. La vista se desbloqueará automáticamente.'
          : 'Die Einträge werden vorbereitet. Die Übersicht wird anschließend freigegeben.';
      await browserPaint();
      await shortYield();
      activeMetroView = view;
      updateMetroNavigation();
      filterCards();
      // Force a genuine layout pass while the library is visible behind overlay.
      if (grid) void grid.getBoundingClientRect().height;
      await browserPaint();
      await shortYield();
    }}
    // Restore the dashboard without triggering another large filter operation.
    activeMetroView = 'overview';
    updateMetroNavigation();
    if (overview) void overview.offsetHeight;
    await browserPaint();
    // Prepare the actual overview covers before users can interact.
    await waitForOverviewPosters();
    await new Promise(resolve => setTimeout(resolve, 250));
    await browserPaint();
  }} catch (error) {{
    console.error('Mnemosyne: preparation failed:', error);
    const detail = document.getElementById('libraryLoadingDetail');
    if (detail) detail.textContent = 'Vorbereitung unvollständig – die Bibliothek kann dennoch verwendet werden.';
  }} finally {{
    libraryBooting = false;
    // Existing view restoration (e.g. after a scan) happens only after warm-up.
    try {{restoreViewState();}} catch (error) {{console.error('View restoration:', error);}}
    await browserPaint();
    libraryLoadingVisible(false);
  }}
}}
function setMetroView(view) {{
  if (libraryBooting) return;
  if (!['overview', 'movies', 'series', 'favorites', 'history'].includes(view)) return;
  ++libraryLoadGeneration;
  if (view !== activeMetroView) clearCatalogFilters();
  activeMetroView = view;
  metroRecentSort = false;
  updateMetroNavigation();
  filterCards();
  if (view === 'overview') {{
    window.scrollTo({{top:0,behavior:'smooth'}});
  }} else {{
    const heading = document.querySelector('.metro-library-heading');
    if (heading) heading.scrollIntoView({{behavior:'instant',block:'start'}});
  }}
}}
function showFeatured(id) {{
  const card = document.getElementById('media-' + id);
  if (!card) return;
  const view = card.dataset.kind === 'series' ? 'series' : 'movies';
  setMetroView(view);
  function scrollWhenReady() {{
    if (activeMetroView !== view) return;
    card.scrollIntoView({{behavior:'smooth',block:'start'}});
  }}
  requestAnimationFrame(scrollWhenReady);
}}
function updateFeaturedLanguage() {{
  document.querySelectorAll('.featured-title').forEach(item => {{
    const key = activeLanguage === 'es' ? 'titleEs' : (activeLanguage === 'en' ? 'titleEn' : 'titleDe');
    item.textContent = item.dataset[key] || item.dataset.titleEn || '';
  }});
}}
const CONFIG_STARTUP_LANGUAGE = {json.dumps(str(getattr(args, 'startup_language', 'de')) if str(getattr(args, 'startup_language', 'de')) in {'de','en','es'} else 'de')};
let activeLanguage = CONFIG_STARTUP_LANGUAGE;
const I18N = {{
  de: {{
    pageTitle:'Mnemosyne', catalogTitle:'MNEMOSYNE', titles:'Titel', filters:'Filter', brandSubtitle:'FILM- UND SERIENBIBLIOTHEK', navOverview:'Übersicht', navMovies:'Filme', navSeries:'Serien', navFavorites:'Favoriten', navHistory:'Verlauf', metricTotal:'Titel gesamt', featuredRecent:'Zuletzt hinzugefügt', showAllRecent:'Alle anzeigen ↗', noFeatured:'Noch keine Datumsangaben vorhanden.', libraryHeading:'Alle Titel', plotMore:'Mehr anzeigen', plotLess:'Weniger anzeigen',
    searchPlaceholder:'Titel, Jahr, Genre, Regisseur oder Schauspieler filtern …',
    filenamePlaceholder:'Dateiname enthält …',
    allTitles:'Alle Titel', moviesOnly:'Nur Filme', seriesOnly:'Nur Serien', kidsAll:'Kinder: alle',
    kidsMovies:'Kinderfilme', kidsSeries:'Kinderserien', unknown:'Unbekannt / nicht zugeordnet',
    allGenres:'Alle Genres', allDirectors:'Alle Regisseure', allActors:'Alle Schauspieler',
    allAddedDates:'Alle Speicherzeiten', last7Days:'Zuletzt hinzugefügt: 7 Tage', last30Days:'Zuletzt hinzugefügt: 30 Tage',
    last90Days:'Zuletzt hinzugefügt: 90 Tage', last365Days:'Zuletzt hinzugefügt: 1 Jahr', addedLabel:'Auf Server',
    resetFilters:'Zurücksetzen', refreshLibrary:'Bibliothek aktualisieren', settings:'Einstellungen', settingsTitle:'Konfiguration', cfgApiKey:'OMDb API-Key', cfgMaxRequests:'Max. Requests pro Tag', cfgStartupLanguage:'Startsprache', cfgScanStartup:'Scan beim Start', cfgWindowsMoviesPath:'Windows: Pfad Filme', cfgWindowsSeriesPath:'Windows: Pfad Serien', cfgLinuxMoviesPath:'Linux: Pfad Filme', cfgLinuxSeriesPath:'Linux: Pfad Serien', configNote:'Das Betriebssystem wird automatisch erkannt. Unter Linux kann direkt smb:// verwendet werden; ein /mnt-Mount ist nicht erforderlich. Neue Pfade gelten beim nächsten Bibliotheks-Scan.', saveConfig:'Speichern', savingConfig:'Speichere …', configSaved:'Konfiguration gespeichert.', configLoadFailed:'Konfiguration konnte nicht geladen werden.', configSaveFailed:'Konfiguration konnte nicht gespeichert werden.', cancel:'Abbrechen', yes:'Ja', no:'Nein', exportPdf:'PDF-Liste erstellen', pdfCreating:'PDF wird erstellt …', pdfFailed:'PDF konnte nicht erstellt werden.', noPdfTitles:'Keine Titel für den PDF-Export vorhanden.', source:'Quelle',
    lastScan:'letzter Scan', serverDates:'Serverdaten', calls:'Aufrufe', fromDb:'aus DB', omdbNotice:'OMDb-Hinweis',
    todayUsage:'heute lokal gezählt', remainingApprox:'ca. verbleibend', filmServer:'Filmserver', online:'online', offline:'offline', checking:'prüfe …',
    noMatches:'Keine passenden Titel.', noCover:'Kein Cover', openIMDb:'IMDb öffnen', searchTrailer:'Trailer suchen',
    searchIMDb:'Auf IMDb suchen', imdbSearchHint:'Bis zu 10 IMDb-Treffer anzeigen und direkt zuweisen.',
    imdbSearching:'IMDb wird durchsucht …', imdbNoResults:'Keine IMDb-Treffer gefunden.', imdbSearchFailed:'IMDb-Suche fehlgeschlagen.', assignIMDb:'Zuweisen',
    kidsBadge:'Kinder', ageRatingLabel:'FSK/Rating', directorLabel:'Regie', castLabel:'Besetzung', awardsLabel:'Auszeichnungen', seasonsLabel:'Staffeln', playFilm:'Film starten', openFolder:'Ordner öffnen',
    files:'Datei(en)', sourceCorrection:'Quelle & Korrektur', detectedAs:'Erkannt als',
    correctionPlaceholder:'IMDb-/OMDb-URL oder tt1234567', correctMapping:'Zuordnung korrigieren',
    removeKids:'Kinder-Markierung entfernen', markKids:'Als Kinderinhalt markieren',
    manualFixed:'manuell festgelegt', autoDetected:'automatisch erkannt',
    removeManualMapping:'Manuelle Zuordnung entfernen', scanning:'Bibliothek wird aktualisiert …',
    scanFailed:'Bibliothek konnte nicht aktualisiert werden.', smbAuthTitle:'SMB-Anmeldung', smbAuthHint:'Für die Aktualisierung der Bibliothek benötigt der Medienserver Zugangsdaten. Sie werden nur für diesen Scan verwendet und nicht gespeichert.', smbUsername:'Benutzername', smbPassword:'Passwort', smbConnect:'Anmelden und aktualisieren', starting:'Öffne …', started:'Geöffnet',
    playFailed:'Medienaktion konnte nicht ausgeführt werden.', randomMovie:'Zufälliger Film',
    randomMovieTitle:'Dein Zufallsfilm', anotherRandom:'Noch einen', close:'Schließen', noMovies:'Keine Filme in der Bibliothek gefunden.',
    windowMinimize:'Fenster minimieren', windowClose:'Mnemosyne schließen', germanTitlePlaceholder:'Deutscher Titel', saveGermanTitle:'Deutschen Titel speichern', resetGermanTitle:'Deutschen Titel zurücksetzen', browserFallbackTitle:'Browser-Hinweis:', browserFallbackText:'Der optimierte Browsermodus ist nicht verfügbar. Mnemosyne läuft im Standardbrowser; installierte Erweiterungen können die Oberfläche verlangsamen. Installiere Chromium, Chrome, Edge oder Brave für den isolierten Modus.'
  }},
  en: {{
    pageTitle:'Mnemosyne', catalogTitle:'MNEMOSYNE', titles:'titles', filters:'Filters', brandSubtitle:'MOVIE & SERIES LIBRARY', navOverview:'Overview', navMovies:'Movies', navSeries:'Series', navFavorites:'Favorites', navHistory:'History', metricTotal:'Total titles', featuredRecent:'Recently added', showAllRecent:'Show all ↗', noFeatured:'No dates available yet.', libraryHeading:'All titles', plotMore:'Read more', plotLess:'Show less',
    searchPlaceholder:'Filter by title, year, genre, director or actor …',
    filenamePlaceholder:'Filename contains …',
    allTitles:'All titles', moviesOnly:'Movies only', seriesOnly:'Series only', kidsAll:'Kids: all',
    kidsMovies:'Kids movies', kidsSeries:'Kids series', unknown:'Unknown / not matched',
    allGenres:'All genres', allDirectors:'All directors', allActors:'All actors',
    allAddedDates:'All added dates', last7Days:'Added in last 7 days', last30Days:'Added in last 30 days',
    last90Days:'Added in last 90 days', last365Days:'Added in last year', addedLabel:'On server',
    resetFilters:'Reset', refreshLibrary:'Update library', settings:'Settings', settingsTitle:'Configuration', cfgApiKey:'OMDb API key', cfgMaxRequests:'Max. requests per day', cfgStartupLanguage:'Startup language', cfgScanStartup:'Scan on startup', cfgWindowsMoviesPath:'Windows: movies path', cfgWindowsSeriesPath:'Windows: series path', cfgLinuxMoviesPath:'Linux: movies path', cfgLinuxSeriesPath:'Linux: series path', configNote:'The operating system is detected automatically. Linux can use smb:// directly; no /mnt mount is required. New paths apply to the next library scan.', saveConfig:'Save', savingConfig:'Saving …', configSaved:'Configuration saved.', configLoadFailed:'Configuration could not be loaded.', configSaveFailed:'Configuration could not be saved.', cancel:'Cancel', yes:'Yes', no:'No', exportPdf:'Create PDF list', pdfCreating:'Creating PDF …', pdfFailed:'PDF could not be created.', noPdfTitles:'No titles available for PDF export.', source:'Source',
    lastScan:'last scan', serverDates:'server dates', calls:'requests', fromDb:'from DB', omdbNotice:'OMDb notice',
    todayUsage:'locally counted today', remainingApprox:'approx. remaining', filmServer:'Movie server', online:'online', offline:'offline', checking:'checking …',
    noMatches:'No matching titles.', noCover:'No cover', openIMDb:'Open IMDb', searchTrailer:'Search trailer',
    searchIMDb:'Search IMDb', imdbSearchHint:'Show up to 10 IMDb results and assign one directly.',
    imdbSearching:'Searching IMDb …', imdbNoResults:'No IMDb results found.', imdbSearchFailed:'IMDb search failed.', assignIMDb:'Assign',
    kidsBadge:'Kids', ageRatingLabel:'Age rating', directorLabel:'Director', castLabel:'Cast', awardsLabel:'Awards', seasonsLabel:'Seasons', playFilm:'Play', openFolder:'Open folder',
    files:'file(s)', sourceCorrection:'Source & correction', detectedAs:'Detected as',
    correctionPlaceholder:'IMDb/OMDb URL or tt1234567', correctMapping:'Correct match',
    removeKids:'Remove kids tag', markKids:'Mark as kids content',
    manualFixed:'set manually', autoDetected:'detected automatically',
    removeManualMapping:'Remove manual match', scanning:'Updating library …',
    scanFailed:'Library could not be updated.', smbAuthTitle:'SMB sign-in', smbAuthHint:'The media server requires credentials to update the library. These are used only for this scan and are not saved.', smbUsername:'Username', smbPassword:'Password', smbConnect:'Sign in and update', starting:'Opening …', started:'Opened',
    playFailed:'Media action could not be completed.', randomMovie:'Random movie',
    randomMovieTitle:'Your random movie', anotherRandom:'Another one', close:'Close', noMovies:'No movies found in the library.',
    windowMinimize:'Minimize window', windowClose:'Close Mnemosyne', germanTitlePlaceholder:'German title', saveGermanTitle:'Save German title', resetGermanTitle:'Reset German title', browserFallbackTitle:'Browser notice:', browserFallbackText:'The optimized browser mode is unavailable. Mnemosyne is running in your default browser; installed extensions may slow the interface down. Install Chromium, Chrome, Edge or Brave for isolated mode.'
  }},
  es: {{
    pageTitle:'Mnemosyne', catalogTitle:'MNEMOSYNE', titles:'títulos', filters:'Filtros', brandSubtitle:'BIBLIOTECA DE CINE Y SERIES', navOverview:'Inicio', navMovies:'Películas', navSeries:'Series', navFavorites:'Favoritos', navHistory:'Historial', metricTotal:'Títulos en total', featuredRecent:'Añadidos recientemente', showAllRecent:'Ver todos ↗', noFeatured:'Todavía no hay fechas disponibles.', libraryHeading:'Todos los títulos', plotMore:'Leer más', plotLess:'Mostrar menos',
    searchPlaceholder:'Filtrar por título, año, género, director o actor …',
    filenamePlaceholder:'El nombre de archivo contiene …',
    allTitles:'Todos los títulos', moviesOnly:'Solo películas', seriesOnly:'Solo series', kidsAll:'Infantil: todo',
    kidsMovies:'Películas infantiles', kidsSeries:'Series infantiles', unknown:'Desconocido / sin asignar',
    allGenres:'Todos los géneros', allDirectors:'Todos los directores', allActors:'Todos los actores',
    allAddedDates:'Todas las fechas', last7Days:'Añadidos en los últimos 7 días', last30Days:'Añadidos en los últimos 30 días',
    last90Days:'Añadidos en los últimos 90 días', last365Days:'Añadidos en el último año', addedLabel:'En el servidor',
    resetFilters:'Restablecer', refreshLibrary:'Actualizar biblioteca', settings:'Ajustes', settingsTitle:'Configuración', cfgApiKey:'Clave API de OMDb', cfgMaxRequests:'Máx. solicitudes por día', cfgStartupLanguage:'Idioma inicial', cfgScanStartup:'Escanear al iniciar', cfgWindowsMoviesPath:'Windows: ruta de películas', cfgWindowsSeriesPath:'Windows: ruta de series', cfgLinuxMoviesPath:'Linux: ruta de películas', cfgLinuxSeriesPath:'Linux: ruta de series', configNote:'El sistema operativo se detecta automáticamente. Linux puede usar smb:// directamente; no se requiere un montaje /mnt. Las nuevas rutas se aplican en el próximo escaneo.', saveConfig:'Guardar', savingConfig:'Guardando …', configSaved:'Configuración guardada.', configLoadFailed:'No se pudo cargar la configuración.', configSaveFailed:'No se pudo guardar la configuración.', cancel:'Cancelar', yes:'Sí', no:'No', exportPdf:'Crear lista PDF', pdfCreating:'Creando PDF …', pdfFailed:'No se pudo crear el PDF.', noPdfTitles:'No hay títulos disponibles para exportar a PDF.', source:'Fuente',
    lastScan:'último escaneo', serverDates:'fechas del servidor', calls:'solicitudes', fromDb:'de la BD', omdbNotice:'Aviso de OMDb',
    todayUsage:'contado localmente hoy', remainingApprox:'aprox. restantes', filmServer:'Servidor multimedia', online:'en línea', offline:'sin conexión', checking:'comprobando …',
    noMatches:'No hay títulos coincidentes.', noCover:'Sin carátula', openIMDb:'Abrir IMDb', searchTrailer:'Buscar tráiler',
    searchIMDb:'Buscar en IMDb', imdbSearchHint:'Mostrar hasta 10 resultados de IMDb y asignar uno directamente.',
    imdbSearching:'Buscando en IMDb …', imdbNoResults:'No se encontraron resultados en IMDb.', imdbSearchFailed:'Falló la búsqueda en IMDb.', assignIMDb:'Asignar',
    kidsBadge:'Infantil', ageRatingLabel:'Clasificación por edad', directorLabel:'Dirección', castLabel:'Reparto', awardsLabel:'Premios', seasonsLabel:'Temporadas', playFilm:'Reproducir película', openFolder:'Abrir carpeta',
    files:'archivo(s)', sourceCorrection:'Fuente y corrección', detectedAs:'Detectado como',
    correctionPlaceholder:'URL de IMDb/OMDb o tt1234567', correctMapping:'Corregir asignación',
    removeKids:'Quitar etiqueta infantil', markKids:'Marcar como contenido infantil',
    manualFixed:'establecido manualmente', autoDetected:'detectado automáticamente',
    removeManualMapping:'Eliminar asignación manual', scanning:'Actualizando biblioteca …',
    scanFailed:'No se pudo actualizar la biblioteca.', smbAuthTitle:'Acceso SMB', smbAuthHint:'El servidor requiere credenciales para actualizar la biblioteca. Solo se usan para este análisis y no se guardan.', smbUsername:'Usuario', smbPassword:'Contraseña', smbConnect:'Acceder y actualizar', starting:'Abriendo …', started:'Abierto',
    playFailed:'No se pudo completar la acción multimedia.', randomMovie:'Película aleatoria',
    randomMovieTitle:'Tu película aleatoria', anotherRandom:'Otra', close:'Cerrar', noMovies:'No se encontraron películas en la biblioteca.',
    windowMinimize:'Minimizar ventana', windowClose:'Cerrar Mnemosyne', germanTitlePlaceholder:'Título alemán', saveGermanTitle:'Guardar título alemán', resetGermanTitle:'Restablecer título alemán', browserFallbackTitle:'Aviso del navegador:', browserFallbackText:'El modo de navegador optimizado no está disponible. Mnemosyne se ejecuta en el navegador predeterminado; las extensiones instaladas pueden ralentizar la interfaz. Instala Chromium, Chrome, Edge o Brave para usar el modo aislado.'
  }}
}};
const GENRE_DE = {{
  'Action':'Action','Adventure':'Abenteuer','Animation':'Animation','Biography':'Biografie',
  'Comedy':'Komödie','Crime':'Krimi','Documentary':'Dokumentation','Drama':'Drama',
  'Family':'Familie','Fantasy':'Fantasy','Film-Noir':'Film Noir','Game-Show':'Spielshow',
  'History':'Geschichte','Horror':'Horror','Music':'Musik','Musical':'Musical',
  'Mystery':'Mystery','News':'Nachrichten','Reality-TV':'Reality-TV','Romance':'Liebesfilm',
  'Sci-Fi':'Science-Fiction','Short':'Kurzfilm','Sport':'Sport','Talk-Show':'Talkshow',
  'Thriller':'Thriller','War':'Krieg','Western':'Western'
}};
const GENRE_ES = {{
  'Action':'Acción','Adventure':'Aventura','Animation':'Animación','Biography':'Biografía',
  'Comedy':'Comedia','Crime':'Crimen','Documentary':'Documental','Drama':'Drama',
  'Family':'Familiar','Fantasy':'Fantasía','Film-Noir':'Cine negro','Game-Show':'Concurso',
  'History':'Historia','Horror':'Terror','Music':'Música','Musical':'Musical',
  'Mystery':'Misterio','News':'Noticias','Reality-TV':'Telerrealidad','Romance':'Romance',
  'Sci-Fi':'Ciencia ficción','Short':'Cortometraje','Sport':'Deporte','Talk-Show':'Talk show',
  'Thriller':'Suspense','War':'Bélico','Western':'Western'
}};

function localizedGenreList(raw) {{
  const parts = String(raw || '').split(',').map(part => part.trim()).filter(Boolean);
  if (activeLanguage === 'de') return parts.map(part => GENRE_DE[part] || part).join(', ');
  if (activeLanguage === 'es') return parts.map(part => GENRE_ES[part] || part).join(', ');
  return parts.join(', ');
}}

const MNEMOSYNE_SCAN_NEEDS_SMB_AUTH = {str(scan_needs_smb_auth(args)).lower()};

const STATUS_I18N = {{
  de: {{ 'manual':'Manuell', 'gefunden':'gefunden', 'nicht zugeordnet':'nicht zugeordnet', 'metadaten deaktiviert':'Metadaten deaktiviert', 'manuell zugeordnet':'Manuell' }},
  en: {{ 'manual':'Manual', 'gefunden':'found', 'nicht zugeordnet':'not matched', 'metadaten deaktiviert':'metadata disabled', 'manuell zugeordnet':'Manual' }},
  es: {{ 'manual':'Manual', 'gefunden':'encontrado', 'nicht zugeordnet':'sin asignar', 'metadaten deaktiviert':'metadatos desactivados', 'manuell zugeordnet':'Manual' }}
}};

function togglePlot(button) {{
  const plot = button.previousElementSibling;
  if (!plot || !plot.classList.contains('localized-plot')) return;
  const expanded = plot.classList.toggle('expanded');
  button.setAttribute('aria-expanded', expanded ? 'true' : 'false');
  const key = expanded ? 'plotLess' : 'plotMore';
  button.dataset.i18n = key;
  button.textContent = t(key);
  scheduleSeasonRowAlignment();
}}

function t(key) {{
  return (I18N[activeLanguage] && I18N[activeLanguage][key]) || I18N.de[key] || key;
}}

function applyLanguage(language) {{
  activeLanguage = ['de','en','es'].includes(language) ? language : 'de';
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
  document.querySelectorAll('[data-i18n-title]').forEach(element => {{
    const key = element.dataset.i18nTitle;
    if (key) element.setAttribute('title', t(key));
  }});
  document.querySelectorAll('[data-i18n-aria-label]').forEach(element => {{
    const key = element.dataset.i18nAriaLabel;
    if (key) element.setAttribute('aria-label', t(key));
  }});
  document.querySelectorAll('[data-kind-code]').forEach(element => {{
    element.textContent = element.dataset.kindCode === 'series'
      ? (activeLanguage === 'en' ? 'Series' : 'Serie')
      : (activeLanguage === 'en' ? 'Movie' : (activeLanguage === 'es' ? 'Película' : 'Film'));
  }});
  document.querySelectorAll('[data-status-code]').forEach(element => {{
    const code = (element.dataset.statusCode || '').toLocaleLowerCase();
    element.textContent = (STATUS_I18N[activeLanguage] && STATUS_I18N[activeLanguage][code]) || code;
  }});
  document.querySelectorAll('.card').forEach(card => {{
    const localizedTitle = activeLanguage === 'de'
      ? (card.dataset.titleDe || card.dataset.titleEn || '')
      : (activeLanguage === 'es'
          ? (card.dataset.titleEs || card.dataset.titleEn || card.dataset.titleDe || '')
          : (card.dataset.titleEn || card.dataset.titleDe || card.dataset.titleEs || ''));
    card.dataset.title = localizedTitle;
    const titleElement = card.querySelector('.localized-title');
    if (titleElement) titleElement.textContent = localizedTitle;
    const trailer = card.querySelector('.trailer-link');
    if (trailer) {{
      const year = trailer.dataset.trailerYear || '';
      const query = [localizedTitle, year, 'trailer'].filter(Boolean).join(' ');
      trailer.href = 'https://www.youtube.com/results?search_query=' + encodeURIComponent(query);
    }}
  }});
  document.querySelectorAll('.localized-plot').forEach(element => {{
    element.textContent = activeLanguage === 'de'
      ? (element.dataset.plotDe || element.dataset.plotEn || '')
      : (activeLanguage === 'es'
          ? (element.dataset.plotEs || element.dataset.plotEn || element.dataset.plotDe || '')
          : (element.dataset.plotEn || element.dataset.plotDe || element.dataset.plotEs || ''));
  }});
  document.querySelectorAll('.genre-text[data-genre-raw]').forEach(element => {{
    element.textContent = localizedGenreList(element.dataset.genreRaw || '');
  }});
  document.querySelectorAll('#genreFilter option[data-genre-name]').forEach(option => {{
    option.textContent = localizedGenreList(option.dataset.genreName || '');
  }});
  const languageSelect = document.getElementById('languageSelect');
  if (languageSelect) languageSelect.value = activeLanguage;
  updateFeaturedLanguage();
  updateMetroNavigation();
  updateServerStatusLabel();
  try {{ sessionStorage.setItem(LANGUAGE_KEY, activeLanguage); }} catch (_) {{}}
  if (document.getElementById('grid')) filterCards();
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

function localizedSortTitle(card) {{
  const field = activeLanguage === 'es' ? 'titleEs' : (activeLanguage === 'en' ? 'titleEn' : 'titleDe');
  return (card.dataset[field] || card.dataset.titleEn || card.dataset.title || '').trim();
}}

function titleInitial(card) {{
  let title = localizedSortTitle(card);
  if (!title) return '#';
  let first = title.charAt(0);
  try {{ first = first.normalize('NFD').replace(/[\u0300-\u036f]/g, ''); }} catch (_) {{}}
  first = first.toUpperCase();
  return /^[A-Z]$/.test(first) ? first : '#';
}}

function resetAlphabetJumpTail() {{
  const tail = document.getElementById('alphabetJumpTail');
  if (tail) tail.style.height = '0px';
}}

function updateAlphabetNav() {{
  if (activeMetroView === 'overview') return;
  const available = new Set();
  document.querySelectorAll('#grid .card').forEach(card => {{
    if (card.style.display !== 'none') available.add(titleInitial(card));
  }});
  document.querySelectorAll('#alphabetNav button[data-letter]').forEach(button => {{
    button.disabled = !available.has(button.dataset.letter || '');
  }});
}}

let alphabetJumpSerial = 0;
function jumpToLetter(letter) {{
  // Search in the ACTUAL visible order and current GUI language, not the OMDb title.
  const target = Array.from(document.querySelectorAll('#grid .card')).find(card =>
    card.style.display !== 'none' && titleInitial(card) === letter
  );
  if (!target) return;
  const serial = ++alphabetJumpSerial;
  resetAlphabetJumpTail();
  const tail = document.getElementById('alphabetJumpTail');
  const header = document.querySelector('header');
  const headerGap = (header ? header.getBoundingClientRect().height : 0) + 14;
  document.querySelectorAll('#grid .card.letter-jump').forEach(card => card.classList.remove('letter-jump'));
  target.classList.add('letter-jump');

  function alignLetter() {{
    if (serial !== alphabetJumpSerial || target.style.display === 'none') return;
    const desiredY = window.scrollY + target.getBoundingClientRect().top - headerGap;
    const maxY = Math.max(0, document.documentElement.scrollHeight - window.innerHeight);
    // Without extra scroll room the last rows (especially Z) can never reach the top.
    if (tail && desiredY > maxY) {{
      const previous = parseFloat(tail.style.height || '0') || 0;
      tail.style.height = Math.ceil(previous + desiredY - maxY + 20) + 'px';
    }}
    window.scrollTo({{top:Math.max(0, desiredY), behavior:'instant'}});
  }}
  alignLetter();
  // content-visibility:auto may refine dimensions while Chromium scrolls across
  // hundreds of cards. Correct the scroll again once those dimensions settle.
  requestAnimationFrame(() => requestAnimationFrame(alignLetter));
  window.setTimeout(alignLetter, 180);
  window.setTimeout(alignLetter, 500);
  window.setTimeout(() => {{ if (serial === alphabetJumpSerial) target.classList.remove('letter-jump'); }}, 1600);
}}

// Recalculate visibility only for series actually shown on the current page.
// Only render and measure the small set of cards near the viewport.
// Measuring hundreds of off-screen, line-clamped plots on each navigation
// used to block Chromium's main thread for several seconds.
let seasonRefreshFrame = 0;
const cardsNearViewport = new Set();
const cardsPendingMeasurement = new Set();
let mediaCardObserver = null;
function initializeVisibleCardMeasurements() {{
  if (mediaCardObserver || !('IntersectionObserver' in window)) return;
  mediaCardObserver = new IntersectionObserver(entries => {{
    for (const entry of entries) {{
      if (entry.isIntersecting) {{
        cardsNearViewport.add(entry.target);
        cardsPendingMeasurement.add(entry.target);
      }} else {{
        cardsNearViewport.delete(entry.target);
        cardsPendingMeasurement.delete(entry.target);
      }}
    }}
    queueCardMeasurements();
  }}, {{rootMargin:'360px 0px 360px 0px', threshold:0}});
  document.querySelectorAll('#grid .card').forEach(card => mediaCardObserver.observe(card));
}}
function queueCardMeasurements() {{
  if (seasonRefreshFrame) return;
  seasonRefreshFrame = requestAnimationFrame(() => {{
    seasonRefreshFrame = 0;
    if (activeMetroView === 'overview') return;
    const batch = Array.from(cardsPendingMeasurement).slice(0, 10);
    for (const card of batch) cardsPendingMeasurement.delete(card);
    for (const card of batch) measureOneCard(card);
    if (cardsPendingMeasurement.size) queueCardMeasurements();
  }});
}}
function seasonButtonText(expanded, count) {{
  const labels = {{
    de: expanded ? 'Weniger Staffeln anzeigen' : `Alle ${{count}} Staffeln anzeigen`,
    en: expanded ? 'Show fewer seasons' : `Show all ${{count}} seasons`,
    es: expanded ? 'Mostrar menos temporadas' : `Mostrar las ${{count}} temporadas`
  }};
  return labels[activeLanguage] || labels.de;
}}
function toggleSeasons(button) {{
  const pills = button.previousElementSibling;
  if (!pills) return;
  const expanded = pills.classList.toggle('expanded');
  button.setAttribute('aria-expanded', String(expanded));
  const count = pills.querySelectorAll('.season-badge').length;
  button.textContent = seasonButtonText(expanded, count);
}}
function toggleSeriesMetadata(button) {{
  const summary = button.closest('.card-summary');
  if (!summary) return;
  const expanded = summary.classList.toggle('meta-expanded');
  button.setAttribute('aria-expanded', String(expanded));
  button.textContent = activeLanguage === 'en'
    ? (expanded ? 'Less information' : 'More information')
    : activeLanguage === 'es'
      ? (expanded ? 'Menos información' : 'Más información')
      : (expanded ? 'Weniger Informationen' : 'Weitere Informationen');
  scheduleSeasonRowAlignment();
}}
function measureOneCard(card) {{
  if (!card || card.style.display === 'none' || !card.isConnected) return;
  const pills = card.querySelector(':scope > .seasons .season-badges');
  const button = card.querySelector(':scope > .seasons .season-expand');
  if (pills && button) {{
    const expanded = pills.classList.contains('expanded');
    if (!expanded) {{
      // Check against the natural size using scrollHeight; do not stretch
      // other cards just because one series has dozens of seasons.
      button.hidden = pills.scrollHeight <= pills.clientHeight + 2;
    }}
    if (!button.hidden) {{
      button.textContent = seasonButtonText(expanded, pills.querySelectorAll('.season-badge').length);
    }}
  }}
  const description = card.querySelector('.series-description');
  const plot = description && description.querySelector('.localized-plot');
  const plotToggle = description && description.querySelector('.plot-more');
  if (plot && plotToggle) {{
    // A -webkit-line-clamp can report a reduced scrollHeight, so
    // checking scrollHeight/clientHeight on the clamped element itself
    // loses the "Mehr anzeigen" button. Measure unclamped natural
    // height briefly, then restore CSS before the next paint.
    const expanded = plot.classList.contains('expanded');
    const previousDisplay = plot.style.display;
    const previousClamp = plot.style.webkitLineClamp;
    const previousLineClamp = plot.style.lineClamp;
    plot.style.display = 'block';
    plot.style.webkitLineClamp = 'unset';
    plot.style.lineClamp = 'unset';
    const naturalHeight = plot.scrollHeight;
    plot.style.display = previousDisplay;
    plot.style.webkitLineClamp = previousClamp;
    plot.style.lineClamp = previousLineClamp;
    const lineHeight = parseFloat(getComputedStyle(plot).lineHeight) || 19;
    // The preview is deliberately three lines; taller text needs a toggle.
    plotToggle.hidden = !expanded && naturalHeight <= 3 * lineHeight + 2;
  }}
  const summary = card.querySelector('.card-summary');
  const meta = card.querySelector('.meta-expand');
  if (summary && meta) {{
    // Details are intentionally hidden by default, not text-clamped.
    // Never measure scrollHeight on a display:none element: that would
    // incorrectly hide the toggle and lose access to its information.
    const hasDetails = !!summary.querySelector('.added-date, .director, .actors, .awards');
    const topClipped = summary.scrollHeight > summary.clientHeight + 2;
    meta.hidden = !hasDetails && !topClipped;
    const expanded = summary.classList.contains('meta-expanded');
    meta.textContent = activeLanguage === 'en'
      ? (expanded ? 'Less information' : 'More information')
      : activeLanguage === 'es'
        ? (expanded ? 'Menos información' : 'Más información')
        : (expanded ? 'Weniger Informationen' : 'Weitere Informationen');
  }}
}}
function scheduleSeasonRowAlignment(card = null) {{
  initializeVisibleCardMeasurements();
  if (card && card instanceof Element) cardsPendingMeasurement.add(card.closest('.card') || card);
  else for (const visibleCard of cardsNearViewport) cardsPendingMeasurement.add(visibleCard);
  queueCardMeasurements();
}}
window.addEventListener('resize', () => scheduleSeasonRowAlignment(), {{passive:true}});

function filterCards() {{
  ++alphabetJumpSerial;
  resetAlphabetJumpTail();
  if (activeMetroView === 'overview') {{
    updateMetroNavigation();
    updateFilterSummary();
    return;
  }}
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
    const id = String(card.dataset.mediaId);
    const metroMatch = (activeMetroView === 'movies' && card.dataset.kind === 'movie') ||
      (activeMetroView === 'series' && card.dataset.kind === 'series') ||
      (activeMetroView === 'favorites' && metroFavorites.has(id)) ||
      (activeMetroView === 'history' && metroHistory.includes(id));
    const show = metroMatch && searchMatch && filenameMatch && filterMatch && genreMatch && directorMatch && actorMatch && recentMatch;
    card.style.display = show ? '' : 'none';
    if (show) visible++;
  }});
  const grid = document.getElementById('grid');
  const oldOrder = Array.from(grid.children);
  const sortedCards = oldOrder.slice().sort((a, b) => {{
    if (recentDays > 0 || metroRecentSort) {{
      const byDate = Number(b.dataset.addedTs || '0') - Number(a.dataset.addedTs || '0');
      if (byDate !== 0) return byDate;
    }}
    const kindOrderA = a.dataset.kind === 'series' ? 1 : 0;
    const kindOrderB = b.dataset.kind === 'series' ? 1 : 0;
    if (kindOrderA !== kindOrderB) return kindOrderA - kindOrderB;
    return localizedSortTitle(a).localeCompare(localizedSortTitle(b), activeLanguage === 'de' ? 'de' : (activeLanguage === 'es' ? 'es' : 'en'), {{sensitivity:'base'}});
  }});
  // Avoid detaching/reinserting all cards on every keystroke. 708 items
  // stay in place if the language/date ordering has not actually changed.
  if (sortedCards.some((card, index) => card !== oldOrder[index])) {{
    const fragment = document.createDocumentFragment();
    sortedCards.forEach(card => fragment.appendChild(card));
    grid.appendChild(fragment);
  }}
  document.getElementById('empty').style.display = visible ? 'none' : 'block';
  document.getElementById('visibleCount').textContent = String(visible);
  updateFilterSummary();
  updateAlphabetNav();
  scheduleSeasonRowAlignment();
}}

function resetFilters() {{
  clearCatalogFilters();
  metroRecentSort = false;
  updateMetroNavigation();
  try {{ sessionStorage.removeItem(VIEW_STATE_KEY); }} catch (_) {{}}
  filterCards();
}}

async function exportPdf(button) {{
  // Export the complete catalog, not just the featured overview or visible filters.
  // All full catalog cards exist in the DOM even when the library section is hidden.
  const ids = Array.from(document.querySelectorAll('#grid .card'))
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
    let filename = 'Mnemosyne.pdf';
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
    metroView: activeMetroView,
    recentSort: metroRecentSort,
    scrollY: window.scrollY,
    anchorId: card ? card.id : '',
    anchorTop: card ? card.getBoundingClientRect().top : 0,
    openDetails: openDetails
  }};
  try {{ sessionStorage.setItem(VIEW_STATE_KEY, JSON.stringify(state)); }} catch (_) {{}}
}}

let smbRefreshPendingForm = null;
function closeSmbAuthDialog() {{
  const dialog = document.getElementById('smbAuthDialog');
  if (dialog && dialog.open) dialog.close();
  document.getElementById('smbPassword').value = '';
  smbRefreshPendingForm = null;
}}
function submitSmbCredentials(event) {{
  event.preventDefault();
  const form = smbRefreshPendingForm;
  if (!form) return;
  const username = document.getElementById('smbUsername').value.trim();
  const password = document.getElementById('smbPassword').value;
  if (!username || !password) return;
  closeSmbAuthDialog();
  // Credentials are kept only in local variables during this request.
  runLibraryScan(form, {{username, password}});
}}
async function refreshLibrary(event, form) {{
  event.preventDefault();
  if (form.querySelector('button[type="submit"]').disabled) return false;
  // Direct smb:// requires explicit credentials. Local/mounted paths do not.
  if (MNEMOSYNE_SCAN_NEEDS_SMB_AUTH) {{
    smbRefreshPendingForm = form;
    const dialog = document.getElementById('smbAuthDialog');
    document.getElementById('smbUsername').value = '';
    document.getElementById('smbPassword').value = '';
    if (dialog && !dialog.open) dialog.showModal();
    document.getElementById('smbUsername').focus();
  }} else {{
    runLibraryScan(form, null);
  }}
  return false;
}}
let scanProgressTimer = null;
let scanProgressBusy = false;
function closeScanProgressDialog() {{
  const dialog = document.getElementById('scanProgressDialog');
  if (dialog && dialog.open) dialog.close();
}}
function showScanProgress() {{
  const dialog = document.getElementById('scanProgressDialog');
  document.getElementById('scanProgressTitle').textContent =
    activeLanguage === 'en' ? 'Updating library' : activeLanguage === 'es' ? 'Actualizando biblioteca' : 'Bibliothek wird aktualisiert';
  document.getElementById('scanProgressPhase').textContent =
    activeLanguage === 'en' ? 'Connecting …' : activeLanguage === 'es' ? 'Conectando …' : 'Verbindung wird hergestellt …';
  document.getElementById('scanProgressCount').textContent = '';
  document.getElementById('scanProgressTitleName').textContent = '';
  const bar = document.getElementById('scanProgressBar');
  bar.removeAttribute('value'); // Indeterminate during SMB directory discovery.
  document.getElementById('scanProgressClose').hidden = true;
  if (dialog && !dialog.open) dialog.showModal();
  if (dialog && !dialog.dataset.cancelProtected) {{
    dialog.addEventListener('cancel', event => {{
      if (document.getElementById('scanProgressClose').hidden) event.preventDefault();
    }});
    dialog.dataset.cancelProtected = '1';
  }}
}}
async function pollScanProgress() {{
  if (scanProgressBusy) return;
  scanProgressBusy = true;
  try {{
    const response = await fetch('/scan-progress', {{cache:'no-store'}});
    if (!response.ok) return;
    const state = await response.json();
    if (!state.running) return;
    const phase = document.getElementById('scanProgressPhase');
    const counter = document.getElementById('scanProgressCount');
    const currentTitle = document.getElementById('scanProgressTitleName');
    const bar = document.getElementById('scanProgressBar');
    const labels = {{
      de: {{connect:'Verbindung wird hergestellt …', discover:'Medienverzeichnisse werden durchsucht …',process:'Metadaten und Datenbank werden aktualisiert …',commit:'Änderungen werden gespeichert …'}},
      en: {{connect:'Connecting …', discover:'Searching media directories …',process:'Updating metadata and database …',commit:'Saving changes …'}},
      es: {{connect:'Conectando …', discover:'Buscando carpetas multimedia …',process:'Actualizando metadatos y base de datos …',commit:'Guardando cambios …'}}
    }};
    phase.textContent = (labels[activeLanguage] || labels.de)[state.stage] || labels.de.connect;
    if (state.stage === 'process' || state.stage === 'commit') {{
      const total = Math.max(0, Number(state.total) || 0);
      const current = Math.max(0, Math.min(total, Number(state.current) || 0));
      if (total > 0) {{
        bar.value = Math.round(100 * current / total);
        counter.textContent = `${{current}} / ${{total}} ` + (activeLanguage === 'en' ? 'titles' : activeLanguage === 'es' ? 'títulos' : 'Titel');
      }} else {{ bar.removeAttribute('value'); counter.textContent = ''; }}
      currentTitle.textContent = String(state.title || '');
    }} else {{
      bar.removeAttribute('value');
      counter.textContent = '';
      currentTitle.textContent = '';
    }}
  }} catch (error) {{ console.debug('Scan progress temporarily unavailable:', error); }}
  finally {{ scanProgressBusy = false; }}
}}
async function runLibraryScan(form, credentials) {{
  saveViewState(null);
  const button = form.querySelector('button[type="submit"]');
  const originalText = button ? button.textContent : '';
  if (button) {{button.disabled = true; button.textContent = t('scanning');}}
  showScanProgress();
  scanProgressTimer = setInterval(pollScanProgress, 350);
  try {{
    const response = await fetch('/scan', {{
      method: 'POST',
      headers: {{ 'X-Requested-With': 'Mnemosyne', 'Content-Type': 'application/json' }},
      body: JSON.stringify(credentials || {{}}),
      cache: 'no-store',
      credentials: 'same-origin'
    }});
    const result = await response.json().catch(() => ({{}}));
    if (!response.ok || result.ok === false) throw new Error(result.error || t('scanFailed'));
    document.getElementById('scanProgressPhase').textContent = activeLanguage === 'en' ? 'Complete!' : activeLanguage === 'es' ? '¡Completado!' : 'Aktualisierung abgeschlossen!';
    document.getElementById('scanProgressBar').value = 100;
    window.location.reload();
  }} catch (error) {{
    if (button) {{button.disabled = false; button.textContent = originalText;}}
    document.getElementById('scanProgressPhase').textContent = activeLanguage === 'en' ? 'Update failed' : activeLanguage === 'es' ? 'Actualización fallida' : 'Aktualisierung fehlgeschlagen';
    document.getElementById('scanProgressTitleName').textContent = error.message || String(error);
    document.getElementById('scanProgressClose').hidden = false;
    // A failed scan never discards the previously stored catalog.
  }} finally {{
    if (scanProgressTimer !== null) clearInterval(scanProgressTimer);
    scanProgressTimer = null;
  }}
}}

function restoreViewState() {{
  let raw = null;
  try {{ raw = sessionStorage.getItem(VIEW_STATE_KEY); }} catch (_) {{}}
  if (!raw) {{ filterCards(); return; }}
  try {{ sessionStorage.removeItem(VIEW_STATE_KEY); }} catch (_) {{}}
  try {{
    const state = JSON.parse(raw);
    if (typeof state.search === 'string') document.getElementById('search').value = state.search;
    if (typeof state.filenameSearch === 'string') document.getElementById('filenameSearch').value = state.filenameSearch;
    if (typeof state.filter === 'string') document.getElementById('catalogFilter').value = state.filter;
    if (typeof state.genre === 'string') document.getElementById('genreFilter').value = state.genre;
    if (typeof state.director === 'string') document.getElementById('directorFilter').value = state.director;
    if (typeof state.actor === 'string') document.getElementById('actorFilter').value = state.actor;
    if (typeof state.recent === 'string') document.getElementById('recentFilter').value = state.recent;
    if (typeof state.metroView === 'string' && ['overview','movies','series','favorites','history'].includes(state.metroView)) activeMetroView = state.metroView;
    metroRecentSort = Boolean(state.recentSort);
    updateMetroNavigation();
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
  let candidates = activeMetroView === 'overview' ? allMovies : allMovies.filter(card => card.style.display !== 'none');
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
    rememberPlayed(mediaId);
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
    document.getElementById('cfgStartupLanguage').value = ['de','en','es'].includes(cfg['Startup-Language']) ? cfg['Startup-Language'] : 'de';
    document.getElementById('cfgScanStartup').value = cfg['Scan-On-Startup'] ? 'yes' : 'no';
    document.getElementById('cfgWindowsMoviesPath').value = cfg['Windows-Movies-Path'] || '';
    document.getElementById('cfgWindowsSeriesPath').value = cfg['Windows-Series-Path'] || '';
    document.getElementById('cfgLinuxMoviesPath').value = cfg['Linux-Movies-Path'] || '';
    document.getElementById('cfgLinuxSeriesPath').value = cfg['Linux-Series-Path'] || '';
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
    'Windows-Movies-Path': document.getElementById('cfgWindowsMoviesPath').value.trim(),
    'Windows-Series-Path': document.getElementById('cfgWindowsSeriesPath').value.trim(),
    'Linux-Movies-Path': document.getElementById('cfgLinuxMoviesPath').value.trim(),
    'Linux-Series-Path': document.getElementById('cfgLinuxSeriesPath').value.trim()
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
    try {{ sessionStorage.setItem(LANGUAGE_KEY, ['de','en','es'].includes(payload['Startup-Language']) ? payload['Startup-Language'] : 'de'); }} catch (_) {{}}
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
  updateFavoriteButtons();
  initializeVisibleCardMeasurements();
  initializeMnemosyneIcon();
  // The startup overlay is already visible in HTML, before JS begins work.
  setTimeout(prepareLibraryOnStartup, 100);
  refreshServerStatus();
  window.setInterval(refreshServerStatus, 15000);
}})();
</script>
</body>
</html>"""


class CatalogWebHandler(BaseHTTPRequestHandler):
    server_version = "Mnemosyne/4.15.44"

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
        safe_name = re.sub(r"[^A-Za-z0-9_.-]+", "_", filename).strip("._") or "Mnemosyne.pdf"
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
        if path in ("/favicon.ico", "/mnemosyne_icon.png"):
            icon_name = "mnemosyne_icon.ico" if path == "/favicon.ico" else "mnemosyne_icon.png"
            icon_path = packaged_resource_directory() / icon_name
            try:
                self._send_binary(icon_path.read_bytes(), "image/x-icon" if path.endswith(".ico") else "image/png")
            except OSError:
                self.send_error(404, "Mnemosyne icon not found")
            return
        if path == "/config-data":
            cfg = load_app_config()
            self._send_json({
                "ok": True,
                "config": {
                    "API-Key": str(cfg.get("API-Key") or ""),
                    "Max-Requests": int(cfg.get("Max-Requests") or OMDB_DAILY_LIMIT),
                    "Startup-Language": str(cfg.get("Startup-Language") or "de"),
                    "Scan-On-Startup": bool(cfg.get("Scan-On-Startup", True)),
                    "Windows-Movies-Path": str(cfg.get("Windows-Movies-Path") or DEFAULT_WINDOWS_MOVIES_SOURCE),
                    "Windows-Series-Path": str(cfg.get("Windows-Series-Path") or DEFAULT_WINDOWS_SERIES_SOURCE),
                    "Linux-Movies-Path": str(cfg.get("Linux-Movies-Path") or DEFAULT_LINUX_MOVIES_SOURCE),
                    "Linux-Series-Path": str(cfg.get("Linux-Series-Path") or DEFAULT_LINUX_SERIES_SOURCE),
                },
            })
            return
        if path == "/scan-progress":
            self._send_json({"ok": True, **self.app.get_scan_progress()})
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
                    "Windows-Movies-Path": data.get("Windows-Movies-Path", ""),
                    "Windows-Series-Path": data.get("Windows-Series-Path", ""),
                    "Linux-Movies-Path": data.get("Linux-Movies-Path", ""),
                    "Linux-Series-Path": data.get("Linux-Series-Path", ""),
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
                        "Windows-Movies-Path": config["Windows-Movies-Path"],
                        "Windows-Series-Path": config["Windows-Series-Path"],
                        "Linux-Movies-Path": config["Linux-Movies-Path"],
                        "Linux-Series-Path": config["Linux-Series-Path"],
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
                language = str(data.get("language", "de")); language = language if language in {"de", "en", "es"} else "de"
                payload = generate_catalog_pdf(self.app.args, ids, language=language)
                stamp = datetime.now().astimezone().strftime("%Y-%m-%d_%H%M")
                self._send_download(payload, "application/pdf", f"Mnemosyne_{stamp}.pdf")
                return

            match = re.fullmatch(r"/play-media/(\d+)", path)
            if match:
                media_file = start_media(self.app.args, int(match.group(1)))
                self._send_text(media_file)
                return

            if path == "/scan":
                ajax_scan = self.headers.get("X-Requested-With") == "Mnemosyne"
                if not self.app.scan_lock.acquire(blocking=False):
                    if ajax_scan:
                        self._send_json({"ok": False, "error": "Ein Scan läuft bereits."}, 409)
                    else:
                        self._send_html(render_web_catalog(self.app.args, error="Ein Scan läuft bereits."), 409)
                    return
                self.app.set_scan_progress(running=True, stage="connect", current=0, total=0, title="")
                try:
                    scan_args = copy.copy(self.app.args)
                    scan_password = self.app.password
                    if ajax_scan:
                        payload = self._json_body()
                        if scan_needs_smb_auth(scan_args):
                            username = payload.get("username")
                            scan_password = payload.get("password")
                            if not isinstance(username, str) or not username.strip() or len(username) > 256:
                                raise CatalogError("Bitte einen gültigen SMB-Benutzernamen eingeben.")
                            if not isinstance(scan_password, str) or not scan_password or len(scan_password) > 1024:
                                raise CatalogError("Bitte das SMB-Passwort eingeben.")
                            scan_args.benutzer = username.strip()
                    count, removed, api_requests, reused_metadata = scan_into_database(
                        scan_args,
                        password=scan_password,
                        omdb_key=self.app.omdb_key,
                        progress=self.app.set_scan_progress,
                    )
                finally:
                    self.app.set_scan_progress(running=False, stage="done", title="")
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

            match = re.fullmatch(r"/german-title/(\d+)", path)
            if match:
                form = self._form()
                german_title = set_german_title(
                    self.app.args, int(match.group(1)), form.get("german_title", [""])[0]
                )
                self._send_html(
                    render_web_catalog(self.app.args, notice=f"Deutscher Titel gespeichert: {german_title}")
                )
                return

            match = re.fullmatch(r"/german-title-reset/(\d+)", path)
            if match:
                german_title = reset_german_title(self.app.args, int(match.group(1)))
                self._send_html(
                    render_web_catalog(self.app.args, notice=f"Deutscher Titel zurückgesetzt: {german_title}")
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
            elif path == "/scan" and self.headers.get("X-Requested-With") == "Mnemosyne":
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
    progress_lock: threading.Lock = field(default_factory=threading.Lock)
    scan_progress: dict[str, Any] = field(default_factory=lambda: {
        "running": False, "stage": "idle", "current": 0, "total": 0, "title": ""
    })

    def set_scan_progress(self, **changes: Any) -> None:
        # No SMB credentials or passwords are ever saved in progress state.
        with self.progress_lock:
            self.scan_progress.update(changes)

    def get_scan_progress(self) -> dict[str, Any]:
        with self.progress_lock:
            return dict(self.scan_progress)

    def apply_config(self, config: dict[str, Any]) -> None:
        global OMDB_DAILY_LIMIT
        self.omdb_key = str(config.get("API-Key") or "").strip()
        OMDB_DAILY_LIMIT = int(config.get("Max-Requests") or OMDB_DAILY_LIMIT)
        self.args.omdb_key = self.omdb_key
        self.args.startup_language = str(config.get("Startup-Language") or "de")
        self.args.scan_on_startup = bool(config.get("Scan-On-Startup", True))
        active_movies, active_series = _active_platform_paths(config)
        self.args.movies_path = active_movies
        self.args.series_path = active_series
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
                "Mnemosyne",
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



def _is_snap_chromium(executable: str) -> bool:
    """Recognize Ubuntu/Kubuntu's confined Snap Chromium launcher."""
    name = str(executable).replace("\\", "/")
    if name.startswith("/snap/bin/chromium"):
        return True
    if os.name == "nt":
        return False
    path = Path(executable)
    try:
        # /usr/bin/chromium-browser is sometimes just a Snap forwarding wrapper.
        if path.is_symlink() and "/snap/bin/chromium" in str(path.readlink()):
            return True
        if path.is_file() and path.stat().st_size < 16384:
            header = path.read_bytes()[:8192].decode("utf-8", "ignore").lower()
            if ("snap run chromium" in header or "/snap/bin/chromium" in header
                    or "exec snap" in header and "chromium" in header):
                return True
    except OSError:
        pass
    return False


def _mnemosyne_browser_profile_dir(port: int, executable: str = "") -> Path:
    """Use a writable path for Snap; keep all other profiles isolated as before."""
    if os.name == "nt":
        base = Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local")))
        profile = base / "Mnemosyne" / "BrowserProfile" / str(port)
    elif _is_snap_chromium(executable):
        # Strict Snap Chromium cannot write to ~/.cache/mnemosyne (hidden dir).
        # ~/snap/chromium/common is its allowed persistent user-data location.
        profile = Path.home() / "snap" / "chromium" / "common" / "mnemosyne-browser" / str(port)
    else:
        base = Path(os.environ.get("XDG_CACHE_HOME", str(Path.home() / ".cache")))
        profile = base / "mnemosyne" / "browser-profile" / str(port)
    profile.mkdir(parents=True, exist_ok=True)
    return profile


def _find_isolated_browsers() -> list[tuple[str, str]]:
    """Return every available browser in preferred order; a broken one can be skipped."""
    candidates: list[tuple[str, str]] = []
    custom = os.environ.get("MNEMOSYNE_BROWSER", "").strip()
    if custom:
        resolved = shutil.which(custom) or (custom if Path(custom).is_file() else None)
        if resolved:
            candidates.append(("Eigener Browser", resolved))
        else:
            print(f"Hinweis: MNEMOSYNE_BROWSER nicht gefunden: {custom}", file=sys.stderr)
    if os.name == "nt":
        program_files = [
            os.environ.get("PROGRAMFILES", ""),
            os.environ.get("PROGRAMFILES(X86)", ""),
            os.environ.get("LOCALAPPDATA", ""),
        ]
        explicit = [
            ("Microsoft Edge", "Microsoft/Edge/Application/msedge.exe"),
            ("Google Chrome", "Google/Chrome/Application/chrome.exe"),
            ("Chromium", "Chromium/Application/chrome.exe"),
            ("Brave", "BraveSoftware/Brave-Browser/Application/brave.exe"),
        ]
        for root in program_files:
            if not root:
                continue
            for label, relative in explicit:
                path = Path(root) / Path(relative)
                if path.is_file():
                    candidates.append((label, str(path)))
        path_names = [
            ("Microsoft Edge", "msedge"),
            ("Google Chrome", "chrome"),
            ("Chromium", "chromium"),
            ("Brave", "brave"),
        ]
    else:
        path_names = [
            ("Chromium", "chromium"),
            ("Chromium", "chromium-browser"),
            ("Google Chrome", "google-chrome-stable"),
            ("Google Chrome", "google-chrome"),
            ("Microsoft Edge", "microsoft-edge-stable"),
            ("Microsoft Edge", "microsoft-edge"),
            ("Brave", "brave-browser"),
            ("Brave", "brave-browser-stable"),
        ]
    for label, executable in path_names:
        resolved = shutil.which(executable)
        if resolved:
            candidates.append((label, resolved))
    seen: set[str] = set()
    result: list[tuple[str, str]] = []
    for label, executable in candidates:
        key = os.path.normcase(os.path.abspath(executable))
        if key not in seen:
            seen.add(key)
            result.append((label, executable))
    return result


def _find_isolated_browser() -> tuple[str, str] | None:
    """Compatibility wrapper used by older tools/tests."""
    browsers = _find_isolated_browsers()
    return browsers[0] if browsers else None


def _mnemosyne_browser_log() -> Path:
    if os.name == "nt":
        base = Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local"))) / "Mnemosyne"
    else:
        base = Path(os.environ.get("XDG_CACHE_HOME", str(Path.home() / ".cache"))) / "mnemosyne"
    try:
        base.mkdir(parents=True, exist_ok=True)
    except OSError:
        base = Path(tempfile.gettempdir())
    return base / "browser-start.log"


def _linux_profile_browser_alive(profile: Path) -> bool:
    """Snap wrappers can exit 0 after spawning Chromium: look for its live child."""
    if not sys.platform.startswith("linux"):
        return False
    marker = f"--user-data-dir={profile}".encode("utf-8")
    try:
        for name in os.listdir("/proc"):
            if not name.isdigit() or int(name) == os.getpid():
                continue
            try:
                cmd = (Path("/proc") / name / "cmdline").read_bytes()
                if marker in cmd and (b"chrom" in cmd.lower() or b"brave" in cmd.lower()):
                    return True
            except (OSError, PermissionError):
                continue
    except OSError:
        pass
    return False


def _browser_log_tail(path: Path) -> str:
    try:
        lines = [line.strip() for line in path.read_text(encoding="utf-8", errors="replace").splitlines() if line.strip()]
        return " | ".join(lines[-5:])[-550:]
    except OSError:
        return ""




def _launch_isolated_browser(browser: tuple[str, str], url: str, port: int) -> subprocess.Popen[Any]:
    """Start a browser, check early failure and preserve diagnostics.

    A spawned process is NOT proof a window appeared. Any immediate failure
    triggers another browser candidate or a visible default-browser fallback.
    """
    label, executable = browser
    profile_dir = _mnemosyne_browser_profile_dir(port, executable)
    command = [
        executable,
        f"--user-data-dir={profile_dir}",
        "--disable-extensions",
        "--disable-sync",
        "--no-first-run",
        "--no-default-browser-check",
        # Native browser title bar controls minimize, maximize and close.
        "--start-maximized",
        f"--app={url}",
    ]
    if sys.platform.startswith("linux"):
        # X11 WM_CLASS hint; on Wayland KDE uses the Chromium app_id instead.
        command.insert(-1, "--class=Mnemosyne")
    log_path = _mnemosyne_browser_log()
    kwargs: dict[str, Any] = {}
    if os.name != "nt":
        kwargs["start_new_session"] = True
    try:
        with log_path.open("ab") as log:
            log.write((f"\n[{datetime.now().isoformat(timespec='seconds')}] "
                       f"{label}: {executable} | profile={profile_dir} | url={url}\n").encode())
            log.flush()
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, **kwargs)
        try:
            code = process.wait(timeout=2.8)
        except subprocess.TimeoutExpired:
            # Normal Chromium keeps a process alive while the app window runs.
            return process
        if code == 0:
            # A snap/desktop wrapper may detach; only accept this when its
            # actual Chromium child can be found under our unique profile.
            if os.name == "nt":
                return process
            for _ in range(5):
                if _linux_profile_browser_alive(profile_dir):
                    return process
                time.sleep(0.25)
        detail = _browser_log_tail(log_path)
        raise RuntimeError(
            f"{label} wurde sofort beendet (Exit-Code {code}). "
            + (f"Ausgabe: {detail}. " if detail else "")
            + f"Log: {log_path}"
        )
    except OSError as exc:
        raise RuntimeError(f"{label}: {exc} (Log: {log_path})") from exc


def _watch_mnemosyne_window(
    server: ThreadingHTTPServer, browser: tuple[str, str], process: subprocess.Popen[Any], port: int
) -> None:
    """Stop this Mnemosyne web server after its isolated browser window is closed.

    Chromium's Snap launcher may exit immediately while its child continues,
    so watch the browser child via its dedicated user-data-dir on Linux.
    """
    try:
        profile_dir = _mnemosyne_browser_profile_dir(port, browser[1])
        if process.poll() is None:
            process.wait()
        if sys.platform.startswith("linux"):
            # The Snap launcher may have detached a child: continue tracking it.
            while _linux_profile_browser_alive(profile_dir):
                time.sleep(2.0)
        # Give browser processes a moment to detach before treating exit as close.
        if process.returncode is not None:
            time.sleep(1.5)
            if sys.platform.startswith("linux") and _linux_profile_browser_alive(profile_dir):
                while _linux_profile_browser_alive(profile_dir):
                    time.sleep(2.0)
        server.shutdown()
    except Exception as exc:
        print(f"Mnemosyne: Browser-Abschlussüberwachung: {exc}", file=sys.stderr)


def run_web_app(args: argparse.Namespace, *, password: str | None, omdb_key: str) -> int:
    # Datenbank schon vor dem ersten HTTP-Aufruf initialisieren.
    connection = open_database(args.db)
    connection.close()

    context = WebAppContext(args=args, password=password, omdb_key=omdb_key)

    # Port zuerst reservieren. Läuft noch eine ältere Instanz auf dem Standardport,
    # verwenden wir automatisch einen freien Betriebssystem-Port statt abzubrechen.
    try:
        server = ThreadingHTTPServer((args.host, args.port), CatalogWebHandler)
    except OSError as exc:
        if getattr(exc, "errno", None) not in {48, 98, 10048}:
            raise
        requested_port = args.port
        server = ThreadingHTTPServer((args.host, 0), CatalogWebHandler)
        args.port = int(server.server_address[1])
        print(
            f"Hinweis: Port {requested_port} ist bereits belegt; "
            f"Mnemosyne verwendet automatisch Port {args.port}.",
            file=sys.stderr,
        )
    server.app = context  # type: ignore[attr-defined]

    if not args.kein_startscan and scan_needs_smb_auth(args) and not (args.benutzer and password):
        print("SMB-Startscan übersprungen: Bibliothek kann über die Oberfläche mit Anmeldung aktualisiert werden.", file=sys.stderr)
        args.kein_startscan = True

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

    shown_host = "127.0.0.1" if args.host in {"0.0.0.0", "::"} else args.host
    catalog_url = f"http://{shown_host}:{args.port}/"
    print(f"Mnemosyne läuft unter {catalog_url}")
    print("Beenden mit Strg+C.")

    # Mnemosyne bevorzugt einen isolierten Chromium-Familienbrowser. Das separate
    # Profil enthält keine Erweiterungen des normalen Benutzerprofils; zusätzlich
    # werden Extensions explizit deaktiviert. Ist kein passender Browser vorhanden,
    # fällt Mnemosyne auf den Standardbrowser zurück und zeigt dort einen Hinweis.
    args.browser_fallback = False
    browser_candidates = _find_isolated_browsers() if not args.kein_browser else []
    if not args.kein_browser and not browser_candidates:
        args.browser_fallback = True
        print(
            "Hinweis: Kein Chromium-/Chrome-/Edge-/Brave-Browser für den isolierten "
            "Mnemosyne-Modus gefunden. Der Standardbrowser wird verwendet; Browser-Erweiterungen "
            "können die Oberfläche verlangsamen.",
            file=sys.stderr,
        )

    if not args.kein_browser:
        def open_catalog_in_browser() -> None:
            for browser in browser_candidates:
                try:
                    browser_process = _launch_isolated_browser(browser, catalog_url, args.port)
                    context.browser_profile = _mnemosyne_browser_profile_dir(args.port, browser[1])
                    context.browser_url = catalog_url
                    context.browser_process = browser_process
                    # The normal double-click launcher hides the terminal, so
                    # background server instances must not accumulate after closing.
                    threading.Thread(
                        target=_watch_mnemosyne_window,
                        args=(server, browser, browser_process, args.port),
                        daemon=True, name="MnemosyneBrowserLifetime"
                    ).start()
                    if not args.ruhig:
                        print(
                            f"Mnemosyne: Browserprozess in {browser[0]} gestartet "
                            "(separates Profil, Erweiterungen deaktiviert).",
                            file=sys.stderr,
                        )
                    return
                except Exception as exc:
                    print(f"Warnung: Isolierter Start von {browser[0]} fehlgeschlagen: {exc}", file=sys.stderr)
            args.browser_fallback = True
            print(
                "Mnemosyne-Hinweis: Kein optimierter Browser konnte gestartet werden. "
                f"Standardbrowser wird geöffnet: {catalog_url}",
                file=sys.stderr,
            )
            try:
                if not webbrowser.open(catalog_url, new=2):
                    print(f"Bitte manuell im Browser öffnen: {catalog_url}", file=sys.stderr)
            except Exception as exc:
                print(f"Warnung: Browser konnte nicht automatisch geöffnet werden: {exc}. "
                      f"Bitte manuell öffnen: {catalog_url}", file=sys.stderr)

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
              python medien_katalog_web_v4_15_6.py --web
              python medien_katalog_web_v4_15_6.py --filme-pfad "D:\\Medien\\Filme" --serien-pfad "D:\\Medien\\Serien" --csv katalog.csv
              python medien_katalog_web_v4_15_6.py --ohne-metadaten --pfade

            Standardquelle:
              \\\\192.168.2.208\\Multimedia
              Rekursiv ausgewertet werden nur die Bereiche Filme und Serien.

            Konfiguration:
              data/config.txt neben dem Programm: API-Key, Max-Requests, Startup-Language,
              Scan-On-Startup sowie getrennte Windows-/Linux-Medienpfade.

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
    # Auch explizite CLI-Pfade plattformgerecht behandeln: UNC -> smb:// unter
    # Linux, smb:// -> UNC unter Windows.
    args.movies_path = _platform_media_path(str(args.movies_path))
    args.series_path = _platform_media_path(str(args.series_path))
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
    migrate_legacy_data()
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
    if any(source.casefold().startswith("smb://") for source, _kind in configured_media_sources(args)) and args.benutzer and password is None and not args.web:
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
