#!/usr/bin/env bash
# Modified for Venticorn: checked local builds, with no installation or publishing.
set -euo pipefail
cd "$(dirname "$0")"
exec python3 python/crossbuild.py "$@"
