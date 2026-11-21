# Mnemosyne

A lightweight, local movie and TV-series catalog for **Windows and Linux**. Mnemosyne started as a small, collaboratively developed Python project by **Johannes Wronka and ChatGPT (OpenAI)**. It prioritizes a focused, responsive media library instead of an overloaded media-center suite.

Mnemosyne scans movie and series folders recursively, enriches titles using [OMDb](https://www.omdbapi.com/), and stores the results in SQLite. Its Chromium-based desktop interface provides posters, ratings, search, filters, playback links, manual IMDb assignment, and complete-library PDF export.

**Current documented version: 4.15.29.** Portable releases are available as a Linux AppImage or Windows executable (built on the corresponding operating system). The source Python script remains available for development.

---

## Features

### Library scanning

- Recursively scans separate movie and series folders
- Automatically distinguishes movies and TV series
- Uses the main series folder as the series identity
- Supports nested season folders
- Adds new titles to the database
- Removes titles that no longer exist on disk
- Updates file paths and file counts
- Reuses existing metadata instead of querying OMDb again on every scan
- Keeps manual IMDb assignments across future scans

### Metadata

Metadata is loaded through the OMDb API and stored locally:

- Title
- Release year
- IMDb rating
- Plot
- Genre
- Runtime
- Director
- Actors
- Poster
- IMDb ID
- Age rating (`Rated` from OMDb)

> **Note:** OMDb's `Rated` field is usually a US/international content rating such as `PG-13`, `R`, or `TV-MA`. It is not guaranteed to be a German FSK rating.

### Web interface

- Responsive movie/series cards
- Poster display with local cover cache
- Automatic poster fallback through IMDb when possible
- German, English, and Spanish GUI
- Bundled default background image and the colorful M application icon
- Movie server online/offline LED
- Current result counter
- Configuration editor directly in the web interface
- Filters remain active after library updates or metadata changes
- Metro-style sidebar with Overview, Movies, Series, Favorites, and History
- Overview shows library totals and 20 recently added titles
- First-launch preparation screen prevents the interface from appearing unresponsive while the catalog is rendered
- Native browser title bar handles minimizing, maximizing, and closing

### Filters and search

The library can be filtered by:

- Movies
- Series
- Kids content
- Unknown / unassigned titles
- Genre
- Director
- Actor
- Recently added: 7 / 30 / 90 / 365 days
- Filename substring
- General text search

Filters can be combined.

Example:

```text
Movies + Sci-Fi + Harrison Ford + filename contains "2160p"
```

### IMDb correction and search

Every title can be searched directly on IMDb.

The built-in IMDb search displays up to 10 matching results with:

- Title
- Year
- Type
- IMDb ID (`tt...`)
- Optional cast information
- Optional poster
- **Assign** button

Selecting **Assign** stores the chosen IMDb ID and reloads the complete metadata through OMDb.

Manual assignment by IMDb/OMDb URL or direct `tt...` ID is also supported.

### Playback

On **Windows**:

- Movies are opened with the Windows default media player
- Series open their main series folder in File Explorer

On **Linux desktop systems**:

- Movies are opened using `xdg-open` and therefore use the configured default media player
- Series folders are opened using the default file manager

macOS uses the system `open` command as a fallback.

### Random movie

The **Random Movie** button selects a random movie from the current library.

Series are excluded.

If filters are currently active, the random selection prefers movies matching the visible filtered result set.

### PDF export

**Create PDF list** exports the **complete library of movies and series**, regardless of the currently selected page or active search filters. It no longer exports only the 20 titles on the Overview page.

The A4 PDF contains posters, titles, release years, IMDb ratings with graphical bars, genres, runtimes, age ratings, directors, cast, and plot descriptions. IMDb `tt...` identifiers are deliberately not printed.

PDF creation requires `reportlab` when running from Python source; the portable build packages its Python dependencies.

### Local caching

The application uses several local caches to minimize network requests:

- SQLite library database
- OMDb metadata cache
- Local poster cache

Already known titles normally do **not** cause new OMDb requests during a regular library scan.

---

## Requirements

### Portable AppImage / Windows EXE

- **No separate Python installation required** on the computer running a built portable release.
- An installed Chromium-based browser (Chromium or Chrome) is still required for the interface.
- Local media folders, mounted drives, and supported SMB paths must be accessible with suitable permissions.
- The application folder and its `data/` subfolder must be writable if the library is to be updated.

### Running from source

- Python 3.10 or newer is recommended.
- Install `reportlab` for PDF generation: `python -m pip install reportlab`.
- Install `smbprotocol` if direct `smb://` access is required: `python -m pip install smbprotocol`.
- A Chromium-based browser is recommended for the desktop-app window.

### Building portable releases

Build on the **target operating system** using the matching builder:

- Linux: `Mnemosyne_AppImage_erstellen.py` (PyInstaller and `appimagetool`).
- Windows: `Mnemosyne_Windows_EXE_erstellen.py` (PyInstaller).

The builders set up a separate build environment; internet access is normally required to obtain dependencies and build tools. Building is not necessary when you already have a ready-to-run AppImage or EXE.

---

## Portable installation and directory layout

There is **no application installer** for the portable distributions. Keep the executable and persistent data together:

```text
Mnemosyne/
├── Mnemosyne_4.15.29-x86_64.AppImage   # Linux
├── Mnemosyne_4.15.29.exe               # Windows (optional in the same folder)
└── data/
    ├── config.txt
    ├── medien_katalog.sqlite3
    └── cover_cache/
```

The **M icon and standard background are embedded** in the portable binaries; separate icon/background files are needed only as build inputs, not for normal use.

Mnemosyne reads and updates its database, settings, and poster cache under the `data/` folder **beside the executable**, not in the temporary PyInstaller/AppImage extraction directory. Both portable builds can share this folder if the media locations are configured for each operating system.

### Migrating from older versions

Version 4.15.29 includes a non-destructive one-time migration. If `config.txt`, `medien_katalog.sqlite3`, or `cover_cache/` still live in the main Mnemosyne folder, the missing counterparts are copied into `data/` on startup.

Files already in `data/` are **not overwritten**. The original legacy files remain in place until you have checked the new version. Close all old instances before upgrading, and make a backup of the SQLite database.

### Updating

Replace the old AppImage/EXE with a newer build; keep the existing `data/` directory. No rescan or database reset is required solely because the executable has changed, provided the new version remains compatible with the saved database schema.

---

## Configuration

`config.txt` must be placed next to the Python script.

Example:

```ini
API-Key=YOUR_OMDB_API_KEY
Max-Requests=1000
Startup-Language=en
Scan-On-Startup=Yes
Movies-Path=\\192.168.1.100\Media\Movies
Series-Path=\\192.168.1.100\Media\Series
```

### Available settings

| Setting | Description |
|---|---|
| `API-Key` | Your OMDb API key |
| `Max-Requests` | Daily OMDb request limit of your subscription |
| `Startup-Language` | `de` for German, `en` for English, or `es` for Spanish |
| `Scan-On-Startup` | `Yes` to scan at startup, `No` to open the existing database immediately |
| `Movies-Path` / `Series-Path` | Legacy media paths (still read for compatibility) |
| `Windows-Movies-Path` / `Windows-Series-Path` | Windows media locations |
| `Linux-Movies-Path` / `Linux-Series-Path` | Linux media locations (`/mnt/...` or `smb://...`) |

All current settings can be edited from **Settings** in the web interface. Mnemosyne selects the platform-specific paths automatically, so a single `config.txt` can describe both Linux and Windows media locations.

### Windows path examples

UNC network share:

```ini
Movies-Path=\\192.168.1.100\Multimedia\Movies
Series-Path=\\192.168.1.100\Multimedia\Series
```

Mapped network drive:

```ini
Movies-Path=Z:\Multimedia\Movies
Series-Path=Z:\Multimedia\Series
```

### Linux path examples

Mounted network share:

```ini
Movies-Path=/mnt/multimedia/movies
Series-Path=/mnt/multimedia/series
```

Another common mount location:

```ini
Movies-Path=/media/movies
Series-Path=/media/series
```

---

## Recommended folder structure

### Movies

Movies can be stored directly in the movie directory:

```text
Movies/
├── Alien.mkv
├── Blade Runner.mkv
└── Blade Runner 2049.mkv
```

or inside individual folders:

```text
Movies/
├── Alien/
│   └── Alien.mkv
├── Blade Runner/
│   └── Blade Runner.mkv
└── The Matrix/
    └── The.Matrix.1999.1080p.mkv
```

Nested Blu-ray/DVD structures are also supported.

### Series

For TV series, the **first directory below `Series-Path` is always treated as the series name**.

Example:

```text
Series/
├── Breaking Bad/
│   ├── Season 01/
│   │   ├── Breaking.Bad.S01E01.mkv
│   │   └── Breaking.Bad.S01E02.mkv
│   └── Season 02/
│       └── Breaking.Bad.S02E01.mkv
├── Dark/
│   ├── S01E01.mkv
│   └── S01E02.mkv
└── ALF/
    ├── Episode 01.mkv
    └── Episode 02.mkv
```

This produces only three catalog entries:

```text
Breaking Bad
Dark
ALF
```

Individual episodes are never intended to appear as separate catalog titles.

---

## Starting the application

### Linux (AppImage)

```bash
chmod +x Mnemosyne_4.15.29-x86_64.AppImage
./Mnemosyne_4.15.29-x86_64.AppImage
```

The AppImage can also be launched by double-clicking when the file manager allows executable files. It is not installed system-wide.

### Windows (portable EXE)

Double-click `Mnemosyne_4.15.29.exe`. There is no installer. The executable uses the `data/` folder alongside itself.

### From Python source

```bash
python3 mnemosyne_web_v4_15_29.py  # Linux
```

```powershell
py mnemosyne_web_v4_15_29.py       # Windows
```

Older versioned `.sh` and `.bat` launchers can still be used with their matching `.py` versions. The default local address is `http://127.0.0.1:8090/`; Mnemosyne binds to localhost by default.

### Creating portable builds

Copy the appropriate builder into the Mnemosyne source folder alongside the newest `mnemosyne_web_v*.py` and the build assets (`mnemosyne_icon.png`, `mnemosyne_icon.ico`, and the background image).

On **Linux**:

```bash
python3 Mnemosyne_AppImage_erstellen.py
```

The builder puts its temporary build environment under the Linux home cache to avoid problems with mounted NTFS/exFAT drives; the resulting AppImage is copied back into the Mnemosyne folder.

On **Windows**:

```powershell
py Mnemosyne_Windows_EXE_erstellen.py
```

Build each binary on its target operating system; a Linux PyInstaller build is not a native Windows EXE.

---

## Background image and application icon

The default background and the colorful Mnemosyne **M** icon are **embedded in the portable AppImage/EXE**. They are served from packaged resources, not read from `data/` at runtime.

For development and when building a new release, keep the original image files alongside the source script. The AppImage builder expects the background as `background.png`, `background.jpg`, or `background.jpeg`. Changing these bundled assets requires rebuilding the portable application; merely replacing an image beside the AppImage will not change the embedded default.

---

## Server status indicator

The web interface contains a small server-status LED:

- Green: media server/path is reachable
- Red: media server/path is unavailable
- Yellow: status check is in progress

The status is refreshed automatically.

This is only a connectivity indicator; it does not guarantee that every individual media file is readable.

---

## OMDb request counter

Mnemosyne keeps a local count of the OMDb requests made by this application.

The configured daily maximum comes from:

```ini
Max-Requests=100000
```

The counter is useful for monitoring usage, but it is **not an authoritative OMDb account counter**.

OMDb does not provide the application with a quota-status endpoint, so requests made with the same API key by other applications are not visible here.

---

## Kids content

Titles can be marked as kids content.

The application can make a conservative automatic suggestion from OMDb metadata, but every title can also be manually marked or unmarked.

Manual choices are preserved during future library scans.

---

## Recently added filter

The application stores a timestamp for media files on the server and can filter titles added within:

- 7 days
- 30 days
- 90 days
- 365 days

For series, the newest episode timestamp is used. Adding a new episode can therefore make the entire series appear under recently added titles again.

Depending on filesystem and network-share behavior, creation and modification timestamps may not exactly represent the original date a file was copied to the server.

---

## Filename search

The dedicated filename filter searches the actual stored media filenames.

Useful examples:

```text
2160p
1080p
REMUX
HEVC
x265
GERMAN
WEB-DL
DTS
```

For a TV series, the series is shown if at least one episode matches the filename substring.

---

## Supported media file extensions

The scanner recognizes common video and disc-image formats, including:

```text
.3gp .avi .flv .iso .m2ts .m4v .mkv .mov .mp4
.mpeg .mpg .mts .ogm .ogv .rmvb .ts .vob .webm .wmv
```

Samples, trailers, extras, featurettes, deleted scenes, and several common auxiliary directories are ignored automatically.

---

## Command-line examples

Start the web interface explicitly:

```bash
python mnemosyne_web_v4_15_29.py --web
```

Use different media paths without changing `config.txt`:

```bash
python mnemosyne_web_v4_15_29.py \
  --filme-pfad "/mnt/media/movies" \
  --serien-pfad "/mnt/media/series" \
  --web
```

Scan without requesting OMDb metadata:

```bash
python mnemosyne_web_v4_15_29.py --ohne-metadaten --pfade
```

Export a console scan to CSV:

```bash
python mnemosyne_web_v4_15_29.py --csv catalog.csv
```

Export to JSON:

```bash
python mnemosyne_web_v4_15_29.py --json catalog.json
```

Use another web port:

```bash
python mnemosyne_web_v4_15_29.py --web --port 8080
```

Do not open the browser automatically:

```bash
python mnemosyne_web_v4_15_29.py --web --kein-browser
```

Skip the initial scan for this run:

```bash
python mnemosyne_web_v4_15_29.py --web --kein-startscan
```

---

## Direct SMB access

Instead of mounting the share through the operating system, the application can also work with `smb://` paths when `smbprotocol` is installed.

Example:

```text
smb://192.168.1.100/Multimedia/Movies
```

Credentials are provided through environment variables:

### Windows PowerShell

```powershell
$env:SMB_BENUTZER="username"
$env:SMB_PASSWORT="password"
python mnemosyne_web_v4_15_29.py
```

### Linux

```bash
export SMB_BENUTZER="username"
export SMB_PASSWORT="password"
python3 mnemosyne_web_v4_15_29.py
```

By default, SMB credentials are only allowed for private/local addresses.

For desktop installations, mounting the network share through Windows or Linux is usually simpler.

---

## Database behavior

The SQLite database is stored in the persistent `data/` folder:

```text
data/medien_katalog.sqlite3
```

It is shared by the AppImage, portable EXE, and source version if they are launched from the same Mnemosyne directory.

A full scan:

1. Recursively reads the configured movie and series paths.
2. Identifies current titles.
3. Reuses stored metadata for already known titles.
4. Queries OMDb only when required.
5. Adds new titles.
6. Updates paths and file counts.
7. Removes titles no longer present on the media storage.

Manual IMDb mappings and manual kids-content flags are retained.

---

## Cover cache

Poster images are cached locally in:

```text
data/cover_cache/
```

The cache reduces repeated image downloads.

When a title is manually reassigned to another IMDb entry, the corresponding poster cache entry is invalidated so the corrected cover can be loaded.

---

## Security and GitHub

**Do not commit your personal OMDb API key to a public repository.**

A recommended `.gitignore` is:

```gitignore
# Private, persistent user data
data/

# Generated binaries and build intermediates
*.AppImage
*.exe
.mnemosyne_appimage_build/
.mnemosyne_portable_build/
*.pdf

# Python
__pycache__/
*.pyc
```

For GitHub, it is a good idea to commit a sanitized example file instead:

```text
config.example.txt
```

with:

```ini
API-Key=YOUR_OMDB_API_KEY
Max-Requests=1000
Startup-Language=en
Scan-On-Startup=Yes
Movies-Path=\\SERVER\Media\Movies
Series-Path=\\SERVER\Media\Series
```

Users can copy it to `data/config.txt` and enter their own values.

---

## Portable release notes

- The AppImage and Windows EXE are separate builds of the same Python application.
- Both can keep their persistent state in the same `data/` folder when placed side-by-side.
- Chromium/Chrome is still an external runtime dependency.
- AppImage compatibility depends on the target Linux system and its available libraries.
- Before sharing a portable folder, remove personal API keys, credentials, and your private library database.

---

## Notes and limitations

- Metadata quality depends on OMDb and the quality of local filenames/folder names.
- The IMDb suggestion search uses IMDb's suggestion service, which is not a formally documented public API and may change in the future.
- German/localized movie names are not always resolved perfectly by OMDb.
- Manual IMDb assignment is available for ambiguous or incorrect matches.
- OMDb age ratings are not guaranteed to correspond to German FSK ratings.
- The local OMDb request counter only tracks requests made by this application.
- Playing a movie opens it on the computer running Mnemosyne. It does not remotely launch playback on another device.
- Network-share timestamps may behave differently depending on NAS/server/filesystem configuration.

---

## Data sources

- Movie and TV metadata: [OMDb API](https://www.omdbapi.com/)
- IMDb title lookup / assignment: [IMDb](https://www.imdb.com/)

Mnemosyne is not affiliated with or endorsed by IMDb or OMDb.
