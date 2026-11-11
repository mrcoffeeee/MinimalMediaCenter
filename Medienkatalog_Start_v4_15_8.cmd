@echo off
cd /d "%~dp0"
set "PYTHON_BIN=python"
%PYTHON_BIN% "%~dp0medien_katalog_web_v4_15_8.py"
set "STATUS=%ERRORLEVEL%"
if not "%STATUS%"=="0" (
  echo.
  echo Medienkatalog wurde mit einem Fehler beendet ^(Code %STATUS%^).
  pause
)
exit /b %STATUS%
