#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ -d .github/workflows ]]; then
  echo "Run validation locally; GitHub Actions workflows are not permitted." >&2
  exit 1
fi

cargo fmt --all -- --check
cargo test --locked --all-targets
cargo test --locked --all-targets --no-default-features
cargo build --locked --bins
python3 tests/language_server_test.py

(
  cd vscode/extension
  npm ci --no-audit --no-fund
  npm run compile
)

(
  cd vscode/search
  npm ci --no-audit --no-fund
  npm run check
  npm run build
)
