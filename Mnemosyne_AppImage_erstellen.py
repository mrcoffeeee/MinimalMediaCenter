#!/usr/bin/env python3
"""Erstellt ein echtes Mnemosyne-AppImage ohne Installation der Anwendung.

Lege diesen Builder neben mnemosyne_web_vX_Y_Z.py, mnemosyne_icon.png,
(optional) mnemosyne_icon.ico und das Standardbild background.png/.jpg/.jpeg.
Bauen: python3 Mnemosyne_AppImage_erstellen.py
Voraussetzungen: Linux x86_64, python3-venv, Internet für Build-Tools.
Der Builder verändert niemals data/config.txt, SQLite oder den Cover-Cache.
"""
from __future__ import annotations

import argparse
import hashlib
import os
import platform
import re
import shutil
import stat
import subprocess
import sys
import urllib.request
import venv
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE_RE = re.compile(r"mnemosyne_web_v(\d+)_(\d+)_(\d+)\.py$")
TOOL_URL = 'https://github.com/AppImage/appimagetool/releases/download/continuous/appimagetool-x86_64.AppImage'


def fail(message):
    raise SystemExit('\nFEHLER: ' + str(message))


def run(args, *, cwd=None, env=None):
    print('\n> ' + ' '.join(map(str,args)),flush=True)
    subprocess.run(list(map(str,args)), cwd=cwd, env=env, check=True)


def select_source(explicit=None):
    items = []
    for path in ROOT.iterdir():
        m = SOURCE_RE.fullmatch(path.name)
        if path.is_file() and m:
            items.append((tuple(map(int,m.groups())),path))
    if explicit:
        p = (ROOT / explicit).resolve()
        if p.parent != ROOT or not p.is_file() or not SOURCE_RE.fullmatch(p.name):
            fail('--source muss eine Mnemosyne-Version aus diesem Verzeichnis sein')
        m=SOURCE_RE.fullmatch(p.name)
        return p,'.'.join(m.groups())
    if not items:
        fail('Keine mnemosyne_web_vX_Y_Z.py im selben Ordner gefunden')
    num,p=max(items)
    return p,'.'.join(map(str,num))


def get_pip(py):
    ok=subprocess.run([str(py),'-m','pip','--version'], stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    if ok.returncode==0:
        return
    subprocess.run([str(py),'-m','ensurepip','--upgrade'],check=False)
    ok=subprocess.run([str(py),'-m','pip','--version'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    if ok.returncode:
        fail('pip fehlt in der Build-venv. Einmalig ausführen: sudo apt install python3-venv python3-pip')


def ensure_assets():
    icon=ROOT/'mnemosyne_icon.png'
    if not icon.is_file():
        fail('mnemosyne_icon.png fehlt. Bitte das bestehende M-Logo neben den Builder legen.')
    bg=next((ROOT/name for name in ('background.png','background.jpg','background.jpeg') if (ROOT/name).is_file()),None)
    if bg is None:
        fail('Originalhintergrund fehlt: background.png oder background.jpg im Mnemosyne-Ordner bereitstellen.')
    return icon,bg


def patch_paths(source, dest):
    code=source.read_text(encoding='utf-8')
    if 'def packaged_resource_directory()' in code and 'os.environ.get("APPIMAGE"' in code:
        pass
    else:
        old='return Path(__file__).resolve().parent / CONFIG_FILENAME'
        if code.count(old)!=1:
            fail('config_path()-Struktur unerwartet geändert; Builder benötigt aktualisierte Pfadanpassung')
        code=code.replace(old,'return application_directory() / CONFIG_FILENAME',1)
        old='''def application_directory() -> Path:
    """Stabiler Programmordner, unabhängig vom Windows-Arbeitsverzeichnis."""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent'''
        new='''def application_directory() -> Path:
    """Beschreibbarer Ordner neben der AppImage-Datei."""
    appimage = os.environ.get("APPIMAGE", "")
    if appimage and getattr(sys, "frozen", False):
        return Path(appimage).expanduser().absolute().parent
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def packaged_resource_directory() -> Path:
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        return Path(sys._MEIPASS) / "assets"
    return Path(__file__).resolve().parent'''
        if code.count(old)!=1:
            fail('application_directory()-Struktur unerwartet geändert')
        code=code.replace(old,new,1)
        start=code.find('def background_image_path() -> Path | None:')
        end=code.find('\ndef _background_version_token',start)
        if start<0 or end<0:
            fail('background_image_path() wurde verändert')
        code=code[:start]+'''def background_image_path() -> Path | None:
    """Nur das im Paket enthaltene Standardhintergrundbild."""
    base = packaged_resource_directory()
    for name in ("background.png", "background.jpg", "background.jpeg"):
        p = base / name
        if p.is_file():
            return p
    return None

'''+code[end:]
        old='icon_path = Path(__file__).resolve().parent / icon_name'
        if code.count(old)!=1:
            fail('Icon-Pfad wurde verändert')
        code=code.replace(old,'icon_path = packaged_resource_directory() / icon_name',1)
    compile(code,str(dest),'exec')
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(code,encoding='utf-8')


def write_appdir(work, pyinstaller_dist, icon, version):
    appdir=work/'Mnemosyne.AppDir'
    if appdir.exists():
        shutil.rmtree(appdir)
    folder=appdir/'usr/bin/Mnemosyne'
    folder.parent.mkdir(parents=True,exist_ok=True)
    shutil.copytree(pyinstaller_dist,folder)
    launcher=appdir/'AppRun'
    # The PNG embedded in AppDir is the AppImage desktop icon. KDE/Chromium
    # additionally need a real desktop-entry/icon mapping to display it in
    # the taskbar; a browser favicon alone is not enough.
    launcher.write_text(r'''#!/bin/sh
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
# Portable: register only a per-user desktop shortcut and an icon cache entry.
# The real executable, its data/ folder, and all program resources remain in
# the AppImage. Registration is skipped if APPIMAGE is not available.
if [ -n "${APPIMAGE:-}" ] && [ -n "${HOME:-}" ]; then
  ICON_DIR="${XDG_DATA_HOME:-$HOME/.local/share}/icons/hicolor/256x256/apps"
  DESKTOP_DIR="${XDG_DATA_HOME:-$HOME/.local/share}/applications"
  if mkdir -p "$ICON_DIR" "$DESKTOP_DIR" 2>/dev/null; then
    cp "$HERE/mnemosyne.png" "$ICON_DIR/mnemosyne.png" 2>/dev/null || :
    # Desktop-file Exec quoting: spaces and %-characters in mounted paths.
    APPIMAGE_PATH=$(printf '%s' "$APPIMAGE" | sed 's/\\/\\\\/g; s/"/\\"/g; s/%/%%/g')
    printf '[Desktop Entry]\nType=Application\nName=Mnemosyne\nExec="%s"\nIcon=mnemosyne\nStartupWMClass=Mnemosyne\nTerminal=false\nCategories=AudioVideo;Video;\n' "$APPIMAGE_PATH" > "$DESKTOP_DIR/mnemosyne.desktop" 2>/dev/null || :
    # Native Wayland Chromium --app app_id, as reported by KDE Window Rules.
    # Match the desktop *filename* to the actual app_id, not just WM_CLASS.
    WAYLAND_APP_ID="chrome-127.0.0.1__-Default"
    printf '[Desktop Entry]\nType=Application\nName=Mnemosyne\nExec="%s"\nIcon=mnemosyne\nStartupWMClass=%s\nNoDisplay=true\nTerminal=false\nCategories=AudioVideo;Video;\n' "$APPIMAGE_PATH" "$WAYLAND_APP_ID" > "$DESKTOP_DIR/$WAYLAND_APP_ID.desktop" 2>/dev/null || :
  fi
fi
exec "$HERE/usr/bin/Mnemosyne/Mnemosyne" "$@"
''', encoding="utf-8")
    launcher.chmod(0o755)
    shutil.copy2(icon,appdir/'mnemosyne.png')
    (appdir/'.DirIcon').symlink_to('mnemosyne.png')
    desktop=appdir/'mnemosyne.desktop'
    desktop.write_text('[Desktop Entry]\nType=Application\nName=Mnemosyne\nComment=Film- und Serienbibliothek\nExec=Mnemosyne\nIcon=mnemosyne\nStartupWMClass=Mnemosyne\nTerminal=false\nCategories=AudioVideo;Video;\n',encoding='utf-8')
    return appdir


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',help='Bestimmte Mnemosyne-Version')
    p.add_argument('--prepare-only',action='store_true',help='Nur Projektstruktur und Pfadanpassungen erzeugen')
    p.add_argument('--appimagetool',help='Pfad zu bereits vorhandenem appimagetool')
    args=p.parse_args()
    if sys.platform!='linux' or platform.machine() not in ('x86_64','AMD64'):
        fail('Dieses Build-Skript ist für Linux x86_64 ausgelegt.')
    source,version=select_source(args.source)
    icon,bg=ensure_assets()
    print(f'Mnemosyne {version}: {source.name}\nLogo: {icon.name}\nHintergrund: {bg.name}',flush=True)
    # Build-Tools und Binärbibliotheken NIEMALS auf dem Medienlaufwerk
    # installieren: USB-/NTFS-/exFAT-Mounts unterstützen Linux-Symlinks,
    # Dateirechte und ausführbare Dateien nicht immer zuverlässig.
    # Alle temporären Dateien bleiben daher im Linux-Home-Verzeichnis.
    cache_home = Path(os.environ.get("XDG_CACHE_HOME") or (Path.home() / ".cache")).expanduser()
    root_id = hashlib.sha256(os.fsencode(str(ROOT))).hexdigest()[:12]
    work = cache_home / "mnemosyne-appimage-build" / root_id
    work.mkdir(parents=True, exist_ok=True)
    print(f"Build-Verzeichnis (Linux-Dateisystem): {work}", flush=True)
    if str(work).startswith(str(ROOT) + os.sep):
        fail("Build-Verzeichnis muss außerhalb des Mnemosyne-Ordners liegen")
    src=work/'source'/source.name
    patch_paths(source,src)
    if args.prepare_only:
        print('Vorbereitung abgeschlossen:',src)
        return
    venv_dir=work/'venv'
    python=venv_dir/'bin/python'
    if not python.is_file():
        print('Erstelle lokale Build-Umgebung ...',flush=True)
        try:
            venv.EnvBuilder(with_pip=True).create(venv_dir)
        except Exception as exc:
            if not python.is_file():
                fail(f'venv fehlgeschlagen ({exc}). sudo apt install python3-venv python3-pip')
    get_pip(python)
    # Alte unvollständige wheel-Installationen nicht wiederverwenden.
    run([python,'-m','pip','install','--no-cache-dir' ,'--disable-pip-version-check','pyinstaller>=6,<7','reportlab>=4,<5','smbprotocol>=1.13,<2'])
    dist=work/'dist'
    env=os.environ.copy()
    env['PYINSTALLER_CONFIG_DIR']=str(work/'pyinstaller-config')
    cmd=[python,'-m','PyInstaller','--noconfirm','--clean','--onedir','--contents-directory','_internal','--name','Mnemosyne',
         '--distpath',dist,'--workpath',work/'pyinstaller-work','--specpath',work,
         '--hidden-import','smbclient','--collect-submodules','smbprotocol','--collect-submodules','reportlab',
         '--add-data',f'{icon}:assets','--add-data',f'{bg}:assets']
    ico=ROOT/'mnemosyne_icon.ico'
    if ico.is_file():
        cmd+=['--add-data',f'{ico}:assets']
    else:
        # Favicon ICO is optional; PNG always included.
        pass
    cmd.append(src)
    run(cmd,cwd=work,env=env)
    appdir=write_appdir(work,dist/'Mnemosyne',icon,version)
    output=ROOT/f'Mnemosyne_{version}-x86_64.AppImage'
    tool=Path(args.appimagetool).expanduser().resolve() if args.appimagetool else shutil.which('appimagetool')
    if not tool:
        tool=work/'appimagetool-x86_64.AppImage'
        if not tool.is_file():
            print('Lade offizielles appimagetool herunter ...',flush=True)
            try:
                urllib.request.urlretrieve(TOOL_URL,tool)
            except Exception as exc:
                fail(f'appimagetool-Download fehlgeschlagen: {exc}\nAlternativ --appimagetool /pfad/zum/tool verwenden')
        tool.chmod(tool.stat().st_mode | stat.S_IXUSR)
    env['ARCH']='x86_64'
    env['VERSION']=version
    # APPIMAGE_EXTRACT_AND_RUN lets appimagetool run even without FUSE on the build host.
    env['APPIMAGE_EXTRACT_AND_RUN']='1'
    run([str(tool),str(appdir),str(output)],cwd=work,env=env)
    if not output.is_file():
        fail('appimagetool hat keine Ausgabedatei erstellt')
    output.chmod(output.stat().st_mode | stat.S_IXUSR)
    print('\nERFOLG:',output,'\nStart:',str(output),'\nDaten liegen im Unterordner data/ neben der AppImage.\nChromium/Chrome wird weiterhin benötigt.',flush=True)

if __name__=='__main__':
    try:
        main()
    except KeyboardInterrupt:
        fail('Abgebrochen')
    except (OSError,subprocess.CalledProcessError) as exc:
        fail(str(exc))
