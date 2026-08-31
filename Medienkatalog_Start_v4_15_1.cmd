@echo off
setlocal
cd /d "%~dp0"

where py >nul 2>nul
if %errorlevel%==0 (
    py -3 "%~dp0medien_katalog_web_v4_15_1.py"
) else (
    python "%~dp0medien_katalog_web_v4_15_1.py"
)

if errorlevel 1 (
    echo.
    echo Medienkatalog wurde mit einem Fehler beendet.
    pause
)
