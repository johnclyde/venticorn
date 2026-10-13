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
            "extension/node_modules/vscode-languageclient/package.json",
            "extension/node_modules/vscode-languageserver-protocol/package.json",
            "extension/node_modules/vscode-jsonrpc/package.json",
            "extension/LICENSE.txt", "extension/NOTICE", "extension/readme.md",
            "extension/build/search/index.html",
        ]:
            assert required in names, f"VSIX is missing {required}"
        excluded = [
            "extension/src/", "extension/node_modules/typescript/",
            "extension/node_modules/prettier/", "extension/node_modules/@types/",
            "extension/target/", "extension/files/", "extension/build/old/",
        ]
        for name in names:
            assert not any(name.startswith(prefix) for prefix in excluded), f"Unexpected development file: {name}"
            assert "venticornserver" not in Path(name).name and "acornserver" not in Path(name).name, f"Unexpected bundled server: {name}"
            assert not Path(name).is_absolute() and ".." not in Path(name).parts, f"Invalid archive path: {name}"
        package = json.loads(archive.read("extension/package.json"))
        assert "extension/" + package["main"].removeprefix("./") in names, "VSIX entry point is missing"
        manifest = ElementTree.fromstring(archive.read("extension.vsixmanifest"))
        identity = next(element for element in manifest.iter() if element.tag.endswith("Identity"))
        assert package.get("publisher") not in (None, "", "undefined"), "A stable extension publisher identity is required"
        assert identity.get("Publisher") == package["publisher"], "VSIX publisher identity differs from its package"
        assert identity.get("Version") == package["version"], "VSIX version differs from its package"
        with tempfile.TemporaryDirectory(prefix="venticorn-vsix-") as directory:
            archive.extractall(directory)
            extension = Path(directory) / "extension"
            # The VS Code host is the only dependency deliberately absent outside VS Code.
            # All Node dependencies must resolve from the unpacked VSIX itself.
            javascript = r'''
const Module = require("node:module");
const path = require("node:path");
const root = require("node:fs").realpathSync(process.argv[1]);
for (const name of ["vscode-languageclient/node", "vscode-languageserver-protocol", "vscode-jsonrpc"]) {
  const resolved = require.resolve(name, { paths: [root] });
  if (!resolved.startsWith(root + path.sep)) throw new Error(`${name} resolved outside the VSIX`);
}
let host;
host = new Proxy(function () {}, {
  get: (_target, key) => key === "version" ? "1.82.0" : host,
  apply: () => host,
  construct: () => host,
});
const originalLoad = Module._load;
Module._load = function (name, parent, isMain) {
  return name === "vscode" ? host : originalLoad.call(this, name, parent, isMain);
};
const manifest = require(path.join(root, "package.json"));
const extension = require(path.join(root, manifest.main));
if (typeof extension.activate !== "function" || typeof extension.deactivate !== "function") {
  throw new Error("The packaged extension does not expose its lifecycle entry points");
}
'''
            environment = {key: value for key, value in os.environ.items() if key != "NODE_PATH"}
            subprocess.run(["node", "-e", javascript, str(extension)], check=True, cwd=directory, env=environment)
    print(f"VSIX validation passed: {len(names)} entries, production dependencies and extension entry point load correctly")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("Usage: python3 tests/vsix_test.py /path/to/extension.vsix")
    check_vsix(sys.argv[1])
