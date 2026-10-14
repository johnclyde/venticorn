const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { pathToFileURL } = require("node:url");
const test = require("node:test");
const info = path.join(__dirname, "../vscode/assistant");
const resolve = name => require.resolve(name, { paths: [info] });
const { compile, preprocess } = require(resolve("svelte/compiler"));
const ts = require(resolve("typescript"));

const component = (async () => {
  const filename = path.join(info, "src/ProofStatus.svelte");
  const source = await preprocess(fs.readFileSync(filename, "utf8"), {
    script: ({ content }) => ({ code: ts.transpileModule(content, {
      compilerOptions: { target: ts.ScriptTarget.ES2020, module: ts.ModuleKind.ESNext },
    }).outputText }),
  }, { filename });
  const compiled = compile(source.code, { filename, generate: "ssr" }).js.code;
  const code = compiled.replace(/from ["']svelte\/internal["']/g,
    `from ${JSON.stringify(pathToFileURL(resolve("svelte/internal")).href)}`);
  return (await import(`data:text/javascript;base64,${Buffer.from(code).toString("base64")}`)).default;
})();

async function render(overrides) {
  const status = { code: [], codeError: null, steps: [], outcome: "Success", needsSimplification: false, numActivated: 0, ...overrides };
  return (await component).render({ status }).html;
}

test("failed searches never render a trivial proof or insertion button", async () => {
  for (const outcome of ["Exhausted", "Timeout", "Interrupted", "Error"]) {
    const html = await render({ outcome, steps: null, code: null });
    assert.match(html, /We could not find a proof/);
    assert.doesNotMatch(html, /follows trivially|Insert code/);
  }
});

test("code generation errors take precedence over trivial-proof text and are escaped", async () => {
  const html = await render({ code: null, codeError: "<script>bad</script>" });
  assert.match(html, /Error during code generation/);
  assert.match(html, /&lt;script>/);
  assert.doesNotMatch(html, /follows trivially|<script>|Insert code/);
});

test("successful trivial and generated proofs retain their distinct presentations", async () => {
  assert.match(await render({}), /follows trivially/);
  const html = await render({ needsSimplification: true, code: ["exact known_fact"] });
  assert.match(html, /exact known_fact/);
  assert.match(html, /Insert code/);
});

test("running and inconsistent searches keep their own status messages", async () => {
  assert.match(await render({ outcome: null, steps: null, code: null }), /Working/);
  assert.match(await render({ outcome: "Inconsistent", steps: null, code: null }), /Local assumptions are inconsistent/);
});


test("status prose uses host typography without preformatted elements", async () => {
  const cases = [
    {},
    { outcome: null, steps: null, code: null },
    { outcome: "Inconsistent", steps: null, code: null },
    { outcome: "Exhausted", steps: null, code: null },
    { code: null, codeError: "cannot format this proof" },
    { needsSimplification: true, code: [] },
    { needsSimplification: true, code: ["claim"] },
  ];
  for (const status of cases) {
    const html = await render(status);
    assert.doesNotMatch(html, /<pre[ >]/);
    assert.match(html, /<p>/);
  }
});

test("generated code preserves nested indentation, line breaks and escaping", async () => {
  const code = ["if condition {", "\t<script>nested</script>", "    spaced", "}"];
  const html = await render({ needsSimplification: true, code });
  assert.match(html, /class="proof-code[^"]*"/);
  assert.ok(html.includes("if condition {\n\t&lt;script>nested&lt;/script>\n    spaced\n}"));
  assert.doesNotMatch(html, /<script>/);
  assert.match(html, /Insert code/);
});
