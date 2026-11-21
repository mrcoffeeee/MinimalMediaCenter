#!/usr/bin/env python3
"""Mnemosyne als portable Windows-EXE erstellen (auf Windows ausführen).

Lege diesen Builder neben mnemosyne_web_vX_Y_Z.py, mnemosyne_icon.png,
mnemosyne_icon.ico und background.png/.jpg/.jpeg.

Bauen: py Mnemosyne_Windows_EXE_erstellen.py
Optional: py Mnemosyne_Windows_EXE_erstellen.py --console

Der Build erfolgt bewusst im lokalen Windows-Tempverzeichnis und lässt
config.txt, die SQLite-Datenbank sowie den Cover-Cache unverändert.
"""
from __future__ import annotations
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import venv
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PATTERN = re.compile(r"mnemosyne_web_v(\d+)_(\d+)_(\d+)\.py$", re.I)


def fail(msg: str) -> None:
    raise SystemExit("\nFEHLER: " + msg)


def run(cmd: list[str | Path], *, cwd: Path | None = None) -> None:
    c = [str(part) for part in cmd]
    print("\n> " + subprocess.list2cmdline(c), flush=True)
    subprocess.run(c, cwd=str(cwd) if cwd else None, check=True)


def source_file(explicit: str | None) -> tuple[Path, str]:
    matches = []
    for path in ROOT.iterdir():
        match = PATTERN.fullmatch(path.name)
        if match and path.is_file():
            matches.append((tuple(int(n) for n in match.groups()), path))
    if explicit:
        candidate = ROOT / explicit
        match = PATTERN.fullmatch(candidate.name)
        if not match or not candidate.is_file() or candidate.resolve().parent != ROOT:
            fail("--source muss den Namen einer vorhandenen Mnemosyne-Python-Datei im selben Ordner angeben.")
        return candidate, ".".join(match.groups())
    if not matches:
        fail("Keine Datei mnemosyne_web_vX_Y_Z.py im selben Ordner gefunden.")
    number, chosen = max(matches)
    return chosen, ".".join(map(str, number))


def validate_source(src: Path) -> None:
    content = src.read_text(encoding="utf-8")
    checks = {
        "beschreibbarer data-Ordner": 'return application_directory() / "data"',
        "Pfad neben einer portablen EXE": 'return Path(sys.executable).resolve().parent',
        "eingebaute Ressourcen": 'return Path(sys._MEIPASS) / "assets"',
    }
    for description, snippet in checks.items():
        if snippet not in content:
            fail(f"Die gewählte Mnemosyne-Version unterstützt {description} nicht wie erwartet. Bitte Version 4.15.29 oder neuer verwenden.")
    compile(content, str(src), "exec")


def get_assets() -> tuple[Path, Path, Path]:
    png = ROOT / "mnemosyne_icon.png"
    ico = ROOT / "mnemosyne_icon.ico"
    background = next((ROOT / name for name in ("background.png", "background.jpg", "background.jpeg") if (ROOT / name).is_file()), None)
    if not png.is_file():
        fail("mnemosyne_icon.png fehlt. Bitte das farbige M neben den Builder legen.")
    if not ico.is_file():
        fail("mnemosyne_icon.ico fehlt. Bitte das bisherige Windows-M-Icon neben den Builder legen.")
    if background is None:
        fail("Standard-Hintergrundbild fehlt. Bitte background.png, background.jpg oder background.jpeg neben den Builder legen.")
    return png, ico, background


def venv_python(work: Path) -> Path:
    env_dir = work / "venv"
    py = env_dir / "Scripts" / "python.exe"
    if not py.exists():
        print("Erstelle Windows-Build-Umgebung …", flush=True)
        venv.EnvBuilder(with_pip=True).create(env_dir)
    status = subprocess.run([str(py), "-m", "pip", "--version"], capture_output=True, text=True)
    if status.returncode:
        run([py, "-m", "ensurepip", "--upgrade"])
    status = subprocess.run([str(py), "-m", "pip", "--version"], capture_output=True, text=True)
    if status.returncode:
        fail("pip ist in der Build-Umgebung nicht verfügbar. Bitte Python von python.org mit pip/venv installieren.")
    return py


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", help="Dateiname der zu bauenden Mnemosyne-Version")
    p.add_argument("--console", action="store_true", help="Debug-EXE mit Konsolenfenster erzeugen")
    p.add_argument("--prepare-only", action="store_true", help="Nur Quellen und Assets prüfen")
    args = p.parse_args()
    if os.name != "nt":
        fail("Dieser Builder muss unter Windows ausgeführt werden. PyInstaller erstellt keine Windows-EXE aus Linux heraus.")
    src, version = source_file(args.source)
    validate_source(src)
    png, ico, background = get_assets()
    exe = ROOT / f"Mnemosyne_{version}.exe"
    print(f"Mnemosyne {version} – Windows Portable Build\nPython: {sys.executable}\nQuelle: {src.name}\nIcon: {ico.name}\nHintergrund: {background.name}\nZiel: {exe}", flush=True)
    if args.prepare_only:
        print("Prüfung erfolgreich. Keine Änderungen vorgenommen.")
        return
    # Auf einem lokal beschreibbaren Windows-Dateisystem bauen, nicht auf dem
    # eventuell externen Datenlaufwerk des Mnemosyne-Verzeichnisses.
    work = Path(tempfile.gettempdir()) / "mnemosyne-windows-build"
    work.mkdir(parents=True, exist_ok=True)
    py = venv_python(work)
    run([py, "-m", "pip", "install", "--disable-pip-version-check", "pyinstaller>=6,<7", "reportlab>=4,<5", "smbprotocol>=1.13,<2"])
    # Sämtliche statischen Dateien werden ins PyInstaller-Archiv eingebettet.
    # Zur Laufzeit löst Mnemosyne sie aus sys._MEIPASS/assets auf.
    pyinst = [py, "-m", "PyInstaller", "--noconfirm", "--clean", "--onefile", "--name", f"Mnemosyne_{version}",
              "--console" if args.console else "--windowed", "--icon", ico,
              "--distpath", work / "dist", "--workpath", work / "work", "--specpath", work,
              "--hidden-import", "smbclient", "--collect-submodules", "smbprotocol", "--collect-submodules", "reportlab",
              "--add-data", f"{png}{os.pathsep}assets", "--add-data", f"{ico}{os.pathsep}assets",
              "--add-data", f"{background}{os.pathsep}assets", src]
    run(pyinst, cwd=work)
    built = work / "dist" / f"Mnemosyne_{version}.exe"
    if not built.is_file():
        fail("PyInstaller hat keine EXE erzeugt.")
    # Windows kann eine gestartete EXE nicht überschreiben.
    if exe.exists():
        try:
            exe.unlink()
        except PermissionError:
            fail(f"{exe.name} wird noch ausgeführt oder ist schreibgeschützt. Bitte erst schließen.")
    shutil.copy2(built, exe)
    print("\nERFOLG!", exe, "\nDaten: data\\config.txt, data\\medien_katalog.sqlite3, data\\cover_cache\\", "\nChrome/Chromium/Edge (Chromium) als Browser wird weiterhin benötigt.", sep="", flush=True)
    print("\nHinweis: Die EXE wurde erstellt, aber noch nicht auf Windows gestartet oder funktional getestet.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as exc:
        fail(f"Build-Schritt fehlgeschlagen (Exit-Code {exc.returncode}). Siehe Meldung darüber.")
    except OSError as exc:
        fail(str(exc))
    except KeyboardInterrupt:
        fail("Build abgebrochen")
