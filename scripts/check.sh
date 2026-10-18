#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ -d .github/workflows ]]; then
  echo "Run validation locally; GitHub Actions workflows are not permitted." >&2
  exit 1
fi

python3 python/version.py
python3 tests/version_test.py
python3 tests/publish_test.py
python3 tests/crossbuild_test.py
python3 scripts/check-library-pin.py
bash -n crossbuild.sh

cargo fmt --all -- --check
cargo test --locked --all-targets
cargo test --locked --all-targets --no-default-features
cargo build --locked --bins
python3 tests/language_server_test.py
python3 tests/language_server_documents_test.py
python3 tests/language_server_completion_test.py
python3 tests/language_server_build_test.py

(
  cd vscode/extension
  npm ci --no-audit --no-fund
  npm test
  npm run build
)

(
  cd vscode/assistant
  npm ci --no-audit --no-fund
  npm run check
  npm test
  npm run build
)
