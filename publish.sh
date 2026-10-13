#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 python/version.py >/dev/null
exec python3 python/publish.py "$@"
