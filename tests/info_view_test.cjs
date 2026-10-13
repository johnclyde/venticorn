const assert = require("node:assert/strict");
const test = require("node:test");
const { loadEditorModule } = require("./editor_modules.cjs");

function openPanel() {
  const registrations = new Map();
  let creation;
  const disposable = () => ({ dispose() {} });
  const panel = {
    webview: {
      cspSource: "https://host.vscode-cdn.net",
      asWebviewUri: () => ({ toString: () => "https://host.vscode-cdn.net/path?name=a&b" }),
      onDidReceiveMessage: disposable,
    },
    onDidDispose: disposable,
    dispose() {},
  };
  const api = {
    commands: { registerTextEditorCommand: (name, callback) => { registrations.set(name, callback); return disposable(); } },
    window: {
      createTextEditorDecorationType: disposable,
      onDidChangeTextEditorSelection: disposable,
      createWebviewPanel: (...args) => { creation = args; return panel; },
    },
    workspace: { onDidSaveTextDocument: disposable },
    Uri: { file: (fsPath) => ({ fsPath }) },
    ViewColumn: { Two: 2, Three: 3 },
  };
  const { InfoView } = loadEditorModule("info-view", {
    vscode: api,
    "vscode-languageclient/node": {},
    fs: { readFileSync: () => '<html><head><script src="./app.js"></script></head></html>' },
  });
  const view = new InfoView({ isRunning: () => false }, "/extension/build/info");
  view.display(undefined);
  return { panel, view, registrations, creation };
}

test("webview policy allows only host-supplied packaged resources", () => {
  const { panel, creation } = openPanel();
  const html = panel.webview.html;
  const policy = html.match(/http-equiv="Content-Security-Policy" content="([^"]+)"/)[1];
  assert.match(policy, /default-src 'none'/);
  for (const directive of ["script-src", "style-src", "img-src", "base-uri"]) {
    assert.ok(policy.includes(`${directive} https://host.vscode-cdn.net;`));
  }
  assert.doesNotMatch(policy, /unsafe-inline|unsafe-eval|vscode-resource:|https:;/);
  assert.ok(html.indexOf("Content-Security-Policy") < html.indexOf("<script"));
  assert.match(html, /name=a&amp;b/);
  assert.equal(creation[3].localResourceRoots[0].fsPath, "/extension/build/info");
});

test("the Info View keeps legacy display and toggle command aliases", () => {
  const { view, registrations, creation } = openPanel();
  assert.equal(creation[0], "acornInfoView");
  let displayed = 0;
  let toggled = 0;
  view.display = () => displayed++;
  view.toggle = () => toggled++;
  for (const name of ["acorn.displayInfoView", "acorn.displaySearchPanel"]) registrations.get(name)();
  for (const name of ["acorn.toggleInfoView", "acorn.toggleSearchPanel"]) registrations.get(name)();
  assert.equal(displayed, 2);
  assert.equal(toggled, 2);
});
