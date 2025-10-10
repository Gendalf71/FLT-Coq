#!/usr/bin/env bash
set -euo pipefail

echo "Checking for 'Admitted.' in Coq sources..."
found=0

# Search all *.v files, excluding common vendor/build dirs if present
grep -R -n --include="*.v" -E '\bAdmitted\.' . || true

if grep -R -n --include="*.v" -E '\bAdmitted\.' . > /dev/null ; then
  echo "ERROR: Found 'Admitted.' in sources. Please remove or replace with a proof."
  exit 1
else
  echo "OK: no 'Admitted.' found."
fi
