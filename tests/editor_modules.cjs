// Modified for Venticorn: test separate modules while production uses a bundle.
// Load compiled extension modules with isolated VS Code, environment, and network adapters.
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");

function loadEditorModule(entry, modules = {}, globals = {}) {
  const cache = new Map();
  function load(filename) {
    filename = path.resolve(filename.endsWith(".js") ? filename : filename + ".js");
    if (cache.has(filename)) return cache.get(filename);
    const exported = {};
    cache.set(filename, exported);
    vm.runInNewContext(fs.readFileSync(filename, "utf8"), {
      exports: exported,
      require: (name) => Object.hasOwn(modules, name) ? modules[name]
        : name.startsWith(".") ? load(path.resolve(path.dirname(filename), name)) : require(name),
      process, console, setTimeout, clearTimeout, __dirname: path.dirname(filename), ...globals,
    }, { filename });
    return exported;
  }
  const extensionRoot = path.join(__dirname, "../vscode/extension");
  // Tests need isolated modules for their mocked host and network adapters.
  const buildDirectory = "build/test";
  return load(path.join(extensionRoot, buildDirectory, entry));
}
module.exports = { loadEditorModule };
