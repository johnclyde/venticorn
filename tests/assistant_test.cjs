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
  const { Assistant } = loadEditorModule("assistant", {
    vscode: api,
    "vscode-languageclient/node": {},
    fs: { readFileSync: () => '<html><head><script src="./app.js"></script></head></html>' },
  });
  const view = new Assistant({ isRunning: () => false }, "/extension/build/assistant");
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
  assert.equal(creation[3].localResourceRoots[0].fsPath, "/extension/build/assistant");
});

test("the Assistant keeps legacy display and toggle command aliases", () => {
  const { view, registrations, creation } = openPanel();
  assert.equal(creation[0], "acornAssistant");
  let displayed = 0;
  let toggled = 0;
  view.display = () => displayed++;
  view.toggle = () => toggled++;
  for (const name of ["acorn.displayAssistant", "acorn.displayInfoView", "acorn.displaySearchPanel"]) registrations.get(name)();
  for (const name of ["acorn.toggleAssistant", "acorn.toggleInfoView", "acorn.toggleSearchPanel"]) registrations.get(name)();
  assert.equal(displayed, 3);
  assert.equal(toggled, 3);
});

function searchFixture({ dirty = false, scheme = "file", sendRequest } = {}) {
  const registrations = new Map();
  const messages = [];
  const disposable = () => ({ dispose() {} });
  const document = { languageId: "acorn", isDirty: dirty, version: 1,
    uri: { scheme, toString: () => `${scheme}:test.ac` } };
  const editor = { document, selection: { start: { line: 0 } }, setDecorations() {} };
  const api = {
    commands: { registerTextEditorCommand: (name, callback) => { registrations.set(name, callback); return disposable(); } },
    window: { activeTextEditor: editor, createTextEditorDecorationType: disposable,
      onDidChangeTextEditorSelection: disposable },
    workspace: { textDocuments: [document], onDidSaveTextDocument: disposable },
  };
  const calls = [];
  const { Assistant } = loadEditorModule("assistant", { vscode: api, "vscode-languageclient/node": {} });
  const view = new Assistant({ isRunning: () => true, sendRequest: async (...args) => {
    calls.push(args);
    return sendRequest ? sendRequest(...args) : { loading: false, status: { outcome: "Success" } };
  } }, "/assistant");
  view.panel = { webview: { postMessage: (message) => messages.push(message) } };
  return { view, document, editor, api, calls, messages, registrations };
}

test("dirty and untitled documents never start proof searches", async () => {
  for (const options of [{ dirty: true }, { scheme: "untitled" }]) {
    const f = searchFixture(options);
    await f.view.searchOnSelection(true);
    assert.equal(f.calls.length, 0);
  }
});

test("a proof response cannot be displayed after its document is edited", async () => {
  let finish;
  const f = searchFixture({ sendRequest: () => new Promise((resolve) => { finish = resolve; }) });
  const pending = f.view.searchOnSelection(true);
  f.document.isDirty = true;
  finish({ loading: false, status: { outcome: "Success" } });
  await pending;
  assert.equal(f.messages.length, 0);
});

test("saved document versions are part of selection identity", async () => {
  const f = searchFixture();
  await f.view.searchOnSelection(false);
  f.document.version++;
  await f.view.searchOnSelection(false);
  assert.equal(f.calls.length, 2);
});

test("a pending proof remains valid when focus moves into the Assistant", async () => {
  let finish;
  const f = searchFixture({ sendRequest: () => new Promise(resolve => { finish = resolve; }) });
  const pending = f.view.searchOnSelection(true);
  f.api.window.activeTextEditor = undefined;
  finish({ loading: false, status: { outcome: "Success" } });
  await pending;
  assert.equal(f.messages.filter(message => message.type === "search").length, 1);
});

test("a pending proof follows another split editor of the same document", async () => {
  let finish;
  const f = searchFixture({ sendRequest: () => new Promise(resolve => { finish = resolve; }) });
  const pending = f.view.searchOnSelection(true);
  f.api.window.activeTextEditor = { ...f.editor };
  await f.view.searchOnSelection(false);
  finish({ loading: false, status: { outcome: "Success" } });
  await pending;
  assert.equal(f.calls.length, 1);
  assert.equal(f.messages.filter(message => message.type === "search").length, 1);
});
