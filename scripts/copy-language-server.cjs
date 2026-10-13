// Modified for Venticorn: stage the locally built server on supported platforms.
const fs = require("node:fs");
const path = require("node:path");
const root = path.resolve(__dirname, "..");
const name = process.platform === "win32" ? "language_server.exe" : "language_server";
const source = path.join(root, "target", "release", name);
const destination = path.join(root, "vscode", "extension", "build", name);
fs.mkdirSync(path.dirname(destination), { recursive: true });
fs.copyFileSync(source, destination);
console.log(`Staged ${name} in the extension build directory.`);
