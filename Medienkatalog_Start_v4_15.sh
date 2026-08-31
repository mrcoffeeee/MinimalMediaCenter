#!/usr/bin/env bash
set -u
cd -- "$(dirname -- "$0")"
PYTHON_BIN="${PYTHON_BIN:-python3}"
"$PYTHON_BIN" "$(pwd)/medien_katalog_web_v4_15.py"
status=$?
if [ $status -ne 0 ]; then
  echo
  echo "Medienkatalog wurde mit einem Fehler beendet (Code $status)."
  read -r -p "Enter zum Schließen ..." _
fi
exit $status
