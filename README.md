# Minimal Media Center

A lightweight local movie and TV series catalog written in Python. Its vibecoded with ChatGPT Pro so if you´re not a fan of this feel free to ignore. To all others: It is very basic but its fast. Sometimes thats better than an overloadedmedia center ...

Minimal Media Center scans movie and series folders recursively, enriches detected titles with metadata from [OMDb](https://www.omdbapi.com/), stores the results in a local SQLite database, and presents the library in a browser-based interface with covers, ratings, filters, PDF export, and manual IMDb assignment.

The application is designed for desktop use on **Windows** and **Linux** and works well with local folders, mapped network drives, mounted network shares, or SMB sources.

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
- German and English GUI
- Optional custom background image
- Movie server online/offline LED
- Current result counter
- Configuration editor directly in the web interface
- Filters remain active after library updates or metadata changes

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

The currently visible library can be exported to an A4 PDF.

The PDF includes:

- Movie/series poster
- Title and year
- IMDb rating with graphical rating bar
- Genre
- Runtime
- Age rating
- Director
- Cast
- Plot

The IMDb `tt...` identifier is intentionally not printed in the PDF.

Active filters are respected, so you can for example export only:

```text
Movies + Action + last 90 days
```

### Local caching

The application uses several local caches to minimize network requests:

- SQLite library database
- OMDb metadata cache
- Local poster cache

Already known titles normally do **not** cause new OMDb requests during a regular library scan.

---

## Requirements

### Python

Python **3.10 or newer** is recommended.

Most of the application only uses the Python standard library.

### Required for PDF export

```bash
pip install reportlab
```

### Optional: direct `smb://` access

If the media paths are configured as direct SMB URLs, install:

```bash
pip install smbprotocol
```

If Windows already provides the share as a UNC path or drive letter, or Linux mounts the share into the local filesystem, `smbprotocol` is not required.

---

## Installation

Clone or download the project and keep the files together in one directory:

```text
MediaCatalog/
├── medien_katalog_web.py
├── config.txt
├── Medienkatalog_Start.cmd
└── Medienkatalog_Start.sh
```

The application creates additional files automatically:

```text
MediaCatalog/
├── medien_katalog.sqlite3
├── cover_cache/
└── background.jpg        # optional
```

The OMDb metadata cache is stored in the normal per-user cache directory.

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
| `Startup-Language` | `de` for German or `en` for English |
| `Scan-On-Startup` | `Yes` to scan at startup, `No` to open the existing database immediately |
| `Movies-Path` | Root directory containing movies |
| `Series-Path` | Root directory containing TV series |

The same values can be edited from **Settings** in the web interface.

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

### Windows

Double-click:

```text
Medienkatalog_Start.cmd
```

or run:

```powershell
python medien_katalog_web.py
```

With no command-line arguments, the application automatically starts the web interface and opens the default browser.

### Linux

Make the launcher executable once:

```bash
chmod +x Medienkatalog_Start.sh
```

Then run:

```bash
./Medienkatalog_Start.sh
```

or:

```bash
python3 medien_katalog_web.py
```

On desktop Linux, the default browser is opened automatically.

### Default web address

```text
http://127.0.0.1:8090/
```

The application listens only on localhost by default.

---

## Background image

To use a custom background, place one of these files next to the Python script:

```text
background.jpg
```

or:

```text
background.png
```

The image is detected automatically.

Remove the file to return to the default dark background.

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

Minimal Media Center keeps a local count of the OMDb requests made by this application.

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
python medien_katalog_web.py --web
```

Use different media paths without changing `config.txt`:

```bash
python medien_katalog_web.py \
  --filme-pfad "/mnt/media/movies" \
  --serien-pfad "/mnt/media/series" \
  --web
```

Scan without requesting OMDb metadata:

```bash
python medien_katalog_web.py --ohne-metadaten --pfade
```

Export a console scan to CSV:

```bash
python medien_katalog_web.py --csv catalog.csv
```

Export to JSON:

```bash
python medien_katalog_web.py --json catalog.json
```

Use another web port:

```bash
python medien_katalog_web.py --web --port 8080
```

Do not open the browser automatically:

```bash
python medien_katalog_web.py --web --kein-browser
```

Skip the initial scan for this run:

```bash
python medien_katalog_web.py --web --kein-startscan
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
python medien_katalog_web.py
```

### Linux

```bash
export SMB_BENUTZER="username"
export SMB_PASSWORT="password"
python3 medien_katalog_web.py
```

By default, SMB credentials are only allowed for private/local addresses.

For desktop installations, mounting the network share through Windows or Linux is usually simpler.

---

## Database behavior

The SQLite database is stored next to the Python script:

```text
medien_katalog.sqlite3
```

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
cover_cache/
```

The cache reduces repeated image downloads.

When a title is manually reassigned to another IMDb entry, the corresponding poster cache entry is invalidated so the corrected cover can be loaded.

---

## Security and GitHub

**Do not commit your personal OMDb API key to a public repository.**

A recommended `.gitignore` is:

```gitignore
# Private configuration
config.txt

# Local database and caches
medien_katalog.sqlite3
medien_katalog.sqlite3-shm
medien_katalog.sqlite3-wal
cover_cache/

# Optional local artwork
background.jpg
background.png

# Generated exports
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

Users can then copy it to `config.txt` and enter their own values.

---

## Notes and limitations

- Metadata quality depends on OMDb and the quality of local filenames/folder names.
- The IMDb suggestion search uses IMDb's suggestion service, which is not a formally documented public API and may change in the future.
- German/localized movie names are not always resolved perfectly by OMDb.
- Manual IMDb assignment is available for ambiguous or incorrect matches.
- OMDb age ratings are not guaranteed to correspond to German FSK ratings.
- The local OMDb request counter only tracks requests made by this application.
- Playing a movie opens it on the computer running Minimal Media Center. It does not remotely launch playback on another device.
- Network-share timestamps may behave differently depending on NAS/server/filesystem configuration.

---

## Data sources

- Movie and TV metadata: [OMDb API](https://www.omdbapi.com/)
- IMDb title lookup / assignment: [IMDb](https://www.imdb.com/)

Minimal Media Center is not affiliated with or endorsed by IMDb or OMDb.
