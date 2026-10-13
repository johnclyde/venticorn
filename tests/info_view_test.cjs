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
  const { SearchPanel } = loadEditorModule("search-panel", {
    vscode: api,
    "vscode-languageclient/node": {},
    fs: { readFileSync: () => '<html><head><script src="./app.js"></script></head></html>' },
  });
  const view = new SearchPanel({ isRunning: () => false }, "/extension/build/search");
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
  assert.equal(creation[3].localResourceRoots[0].fsPath, "/extension/build/search");
});
