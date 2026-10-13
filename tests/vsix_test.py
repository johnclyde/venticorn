#!/usr/bin/env python3
"""Validate a real, locally built VSIX, including its runtime module resolution."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile
from xml.etree import ElementTree


def check_vsix(filename):
    with zipfile.ZipFile(filename) as archive:
        names = set(archive.namelist())
        for required in [
            "extension/LICENSE.txt", "extension/NOTICE", "extension/readme.md",
            "extension/build/info/index.html",
            "extension/build/extension/THIRD_PARTY_NOTICES.txt",
        ]:
            assert required in names, f"VSIX is missing {required}"
        excluded = [
            "extension/src/", "extension/node_modules/",
            "extension/target/", "extension/files/", "extension/build/old/", "extension/build/test/",
        ]
        for name in names:
            assert not any(name.startswith(prefix) for prefix in excluded), f"Unexpected development file: {name}"
            assert "venticornserver" not in Path(name).name and "acornserver" not in Path(name).name, f"Unexpected bundled server: {name}"
            assert not Path(name).is_absolute() and ".." not in Path(name).parts, f"Invalid archive path: {name}"
        package = json.loads(archive.read("extension/package.json"))
        assert "extension/" + package["main"].removeprefix("./") in names, "VSIX entry point is missing"
        notices = archive.read("extension/build/extension/THIRD_PARTY_NOTICES.txt").decode()
        for dependency in ["vscode-languageclient", "vscode-languageserver-protocol", "vscode-jsonrpc"]:
            assert dependency in notices, f"Bundled dependency attribution is missing: {dependency}"
        manifest = ElementTree.fromstring(archive.read("extension.vsixmanifest"))
        identity = next(element for element in manifest.iter() if element.tag.endswith("Identity"))
        assert package.get("publisher") not in (None, "", "undefined"), "A stable extension publisher identity is required"
        assert identity.get("Publisher") == package["publisher"], "VSIX publisher identity differs from its package"
        assert identity.get("Version") == package["version"], "VSIX version differs from its package"
        with tempfile.TemporaryDirectory(prefix="venticorn-vsix-") as directory:
            archive.extractall(directory)
            extension = Path(directory) / "extension"
            # The VS Code host is the only dependency deliberately absent outside VS Code.
            # All JavaScript runtime dependencies must already be in the bundle.
            javascript = r'''
const Module = require("node:module");
const path = require("node:path");
const root = require("node:fs").realpathSync(process.argv[1]);
const manifest = require(path.join(root, "package.json"));
const builtins = new Set(Module.builtinModules.flatMap(name => [name, `node:${name}`]));
let host;
host = new Proxy(function () {}, {
  get: (_target, key) => key === "version" ? "1.82.0" : host,
  apply: () => host,
  construct: () => host,
});
const originalLoad = Module._load;
Module._load = function (name, parent, isMain) {
  if (name === "vscode") return host;
  if (!builtins.has(name) && !path.isAbsolute(name)) {
    throw new Error(`The extension bundle depends on an external runtime module: ${name}`);
  }
  return originalLoad.call(this, name, parent, isMain);
};
const extension = require(path.join(root, manifest.main));
if (typeof extension.activate !== "function" || typeof extension.deactivate !== "function") {
  throw new Error("The packaged extension does not expose its lifecycle entry points");
}
'''
            environment = {key: value for key, value in os.environ.items() if key != "NODE_PATH"}
            subprocess.run(["node", "-e", javascript, str(extension)], check=True, cwd=directory, env=environment)
    print(f"VSIX validation passed: {len(names)} entries, bundled entry point loads with only Node builtins and the VS Code host")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("Usage: python3 tests/vsix_test.py /path/to/extension.vsix")
    check_vsix(sys.argv[1])
