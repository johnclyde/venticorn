#!/usr/bin/env python3
"""Check release versions, or update all release manifests and lockfiles together."""

import argparse
import json
import os
from pathlib import Path
import re
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
VERSION_PATTERN = re.compile(r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\Z")


def replace_toml_version(text, section, version):
    """Preserve TOML formatting and every unrelated package version."""
    pattern = re.compile(r"(?ms)^" + re.escape(section) + r"\s*\n(?P<body>.*?)(?=^\[|\Z)")
    matches = list(pattern.finditer(text))
    if section == "[[package]]":
        matches = [m for m in matches if re.search(r'^name = "venticorn"\r?$', m['body'], re.M)]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one Venticorn {section} section")
    match = matches[0]
    body, count = re.subn(r'(?m)^version = "[^"]+"(\r?)$',
                          lambda m: f'version = "{version}"' + m[1], match['body'])
    if count != 1:
        raise ValueError(f"expected exactly one version in {section}")
    return text[:match.start('body')] + body + text[match.end('body'):]


def release_files(root):
    return [root / p for p in (
        "Cargo.toml", "Cargo.lock", "vscode/extension/package.json",
        "vscode/extension/package-lock.json", "VERSION",
    )]


def read_release(root):
    files = release_files(root)
    contents = []
    for path in files:
        # Rollback must preserve original bytes, including Windows line endings.
        with path.open(encoding="utf-8", newline="") as stream:
            contents.append(stream.read())
    cargo = tomllib.loads(contents[0])["package"]
    if cargo["name"] != "venticorn":
        raise ValueError("expected the venticorn Cargo package")
    packages = [p for p in tomllib.loads(contents[1])["package"] if p["name"] == "venticorn"]
    if len(packages) != 1:
        raise ValueError("expected one venticorn Cargo.lock package")
    extension, lock = map(json.loads, contents[2:4])
    if extension["name"] != lock["name"] or extension["name"] != lock["packages"][""]["name"]:
        raise ValueError("extension manifest and lockfile package names differ")
    versions = [cargo["version"], packages[0]["version"], extension["version"],
                lock["version"], lock["packages"][""]["version"], contents[4].strip()]
    if any(not VERSION_PATTERN.fullmatch(v) for v in versions):
        raise ValueError("release versions must be major.minor.patch without leading zeros")
    if len(set(versions)) != 1:
        raise ValueError("release manifests and lockfiles disagree: " + ", ".join(versions))
    return versions[0], files, contents


def stage_text(path, text):
    """Write beside the destination so replacement is atomic on its filesystem."""
    descriptor, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.chmod(path.stat().st_mode)
        return temporary
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def update_version(root, new_version=None):
    old_version, files, contents = read_release(root)
    if new_version is None:
        return old_version
    if not VERSION_PATTERN.fullmatch(new_version):
        raise ValueError("new version must be major.minor.patch without leading zeros")
    replacements = [replace_toml_version(contents[0], "[package]", new_version),
                    replace_toml_version(contents[1], "[[package]]", new_version)]
    extension, lock = map(json.loads, contents[2:4])
    extension["version"] = new_version
    lock["version"] = lock["packages"][""]["version"] = new_version
    replacements.extend(json.dumps(value, indent=2) + "\n" for value in (extension, lock))
    replacements.append(new_version + "\n")
    # Stage complete new files and rollback copies before changing any originals.
    staged = []
    backups = []
    replaced = []
    preserve_backups = False
    try:
        for path, replacement, original in zip(files, replacements, contents):
            staged.append(stage_text(path, replacement))
            backups.append(stage_text(path, original))
        try:
            for index, (path, temporary) in enumerate(zip(files, staged)):
                os.replace(temporary, path)
                replaced.append(index)
        except OSError as error:
            for index in reversed(replaced):
                try:
                    os.replace(backups[index], files[index])
                except OSError as rollback_error:
                    preserve_backups = True
                    raise OSError(
                        f"version update failed: {error}; rollback failed: {rollback_error}; "
                        f"original copies remain at {[str(p) for p in backups if p.exists()]}"
                    ) from rollback_error
            raise
    finally:
        for temporary in staged + ([] if preserve_backups else backups):
            temporary.unlink(missing_ok=True)
    return new_version


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("new_version", nargs="?", help="new major.minor.patch release version")
    args = parser.parse_args()
    try:
        print(update_version(ROOT, args.new_version))
    except (OSError, KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"version: {error}\n")


if __name__ == "__main__":
    main()
