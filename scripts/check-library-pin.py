#!/usr/bin/env python3
"""Check the vendored mathematical core against its reviewed library pin."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


MODULES = {"nat.ac", "pair.ac", "nat_gcd.ac"}


def check(root: Path, library: Path | None = None) -> str:
    pin = json.loads((root / "venticornlib.lock.json").read_text())
    if (
        not isinstance(pin, dict)
        or pin.get("schema_version") != 1
        or pin.get("repository") != "https://github.com/johnclyde/venticornlib"
        or pin.get("library_path") != "."
        or pin.get("bundled_directory") != "vscode/extension/acornlib"
        or not isinstance(pin.get("revision"), str)
        or not re.fullmatch(r"[0-9a-f]{40}", pin["revision"])
        or not isinstance(pin.get("files"), dict)
        or set(pin["files"]) != MODULES
    ):
        raise ValueError("invalid Venticornlib pin or unexpected core module set")

    directories = [root / pin["bundled_directory"]]
    if library is not None:
        library = library.resolve()
        revision = subprocess.check_output(
            ["git", "-C", str(library), "rev-parse", "HEAD"], text=True
        ).strip()
        if revision != pin["revision"]:
            raise ValueError("external Venticornlib checkout is not at the pinned revision")
        if {str(path.relative_to(library)) for path in library.rglob("*.ac")} != MODULES:
            raise ValueError("external Venticornlib checkout has an unexpected module set")
        directories.append(library)

    for name, expected in pin["files"].items():
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError(f"invalid SHA-256 for {name}")
        for directory in directories:
            path = directory / name
            if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                raise ValueError(f"library pin mismatch: {path}")
    return pin["revision"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, help="also check a local Venticornlib checkout")
    args = parser.parse_args()
    try:
        revision = check(Path(__file__).resolve().parents[1], args.library)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Library pin check failed: {error}", file=sys.stderr)
        return 1
    print(f"Venticornlib {revision}: all three bundled core modules match")
    return 0


if __name__ == "__main__":
    sys.exit(main())
