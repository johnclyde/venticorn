const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { pathToFileURL } = require("node:url");
const test = require("node:test");
const root = path.join(__dirname, "../vscode/assistant");
const resolve = (name) => require.resolve(name, { paths: [root] });
const { compile, preprocess } = require(resolve("svelte/compiler"));
const ts = require(resolve("typescript"));
const component = (async () => {
  const filename = path.join(root, "src/PreSaveHelp.svelte");
  const source = await preprocess(fs.readFileSync(filename, "utf8"), {
    script: ({ content }) => ({ code: ts.transpileModule(content, {
      compilerOptions: { target: ts.ScriptTarget.ES2020, module: ts.ModuleKind.ESNext },
    }).outputText }),
  }, { filename });
  const code = compile(source.code, { filename, generate: "ssr" }).js.code.replace(
    /from ["']svelte\/internal["']/g,
    `from ${JSON.stringify(pathToFileURL(resolve("svelte/internal")).href)}`);
  return (await import(`data:text/javascript;base64,${Buffer.from(code).toString("base64")}`)).default;
})();
test("Assistant guidance distinguishes inactive, untitled, dirty, and saved documents", async () => {
  const view = await component;
  for (const [help, expected] of [
    [{ noFile: true }, /Open an Acorn file/],
    [{ newDocument: true }, /Enter a theorem/],
    [{ unsaved: true }, /Save your changes/],
    [{}, /Select a proposition/],
  ]) {
    const html = view.render({ help }).html;
    assert.match(html, expected);
    assert.doesNotMatch(html, /Insert code|follows trivially/);
  }
});
