// Modified for Venticorn: bundle the extension while retaining dependency licenses.
import { build } from "esbuild";
import * as fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const root = path.resolve(fileURLToPath(new URL(".", import.meta.url)));
const output = path.join(root, "build", "extension");
await fs.rm(output, { recursive: true, force: true });
const result = await build({
  absWorkingDir: root,
  entryPoints: ["src/extension.ts"],
  outfile: "build/extension/bundle.js",
  bundle: true,
  sourcemap: true,
  platform: "node",
  target: "es2020",
  format: "cjs",
  external: ["vscode"],
  legalComments: "linked",
  metafile: true,
});

// esbuild keeps marked license comments. Also include each bundled package's
// license file so dependency attribution survives removal of node_modules.
const packages = new Set();
for (const input of Object.keys(result.metafile.inputs)) {
  if (!input.includes("node_modules/")) continue;
  let directory = path.dirname(path.resolve(root, input));
  let found = false;
  while (directory !== root) {
    try {
      await fs.access(path.join(directory, "package.json"));
      packages.add(directory);
      found = true;
      break;
    } catch (error) {
      if (error.code !== "ENOENT") throw error;
      const parent = path.dirname(directory);
      if (parent === directory) break;
      directory = parent;
    }
  }
  if (!found) throw new Error(`No package manifest found for bundled input ${input}`);
}
const notices = [];
for (const directory of [...packages].sort()) {
  const manifest = JSON.parse(await fs.readFile(path.join(directory, "package.json"), "utf8"));
  const names = (await fs.readdir(directory)).filter((name) => /^(licen[sc]e|copying)([._-].*)?$/i.test(name)).sort();
  if (names.length === 0) throw new Error(`No license file found for bundled dependency ${manifest.name}`);
  notices.push(`${manifest.name} ${manifest.version}`);
  for (const name of names) {
    notices.push(`${name}\n${await fs.readFile(path.join(directory, name), "utf8")}`);
  }
}
await fs.writeFile(path.join(output, "THIRD_PARTY_NOTICES.txt"), notices.join("\n\n") + "\n");
