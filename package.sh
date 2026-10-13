#!/usr/bin/env bash
# Build and validate a local VSIX; publishing is a separate explicit operation.
set -euo pipefail
cd "$(dirname "$0")"
version="$(python3 python/version.py)"
vsce_command="${VSCE:-vsce}"
if ! command -v "$vsce_command" >/dev/null 2>&1; then
  echo "Install @vscode/vsce 4.0.0 with Node.js 22 and set VSCE to its executable path." >&2
  exit 1
fi
vsce_command="$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$(command -v "$vsce_command")")"
# Only generated extension output is removed; source and dependencies stay in place.
rm -rf vscode/extension/build/extension
npm --prefix vscode/extension run compile
npm --prefix vscode/search run build
mkdir -p files/release
output="$PWD/files/release/venticorn-extension-$version.vsix"
(
  cd vscode/extension
  "$vsce_command" package --out "$output" --no-gitHubIssueLinking --no-gitLabIssueLinking
)
python3 tests/vsix_test.py "$output"
