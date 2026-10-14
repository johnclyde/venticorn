const assert = require("node:assert/strict");
const test = require("node:test");
const { loadEditorModule } = require("./editor_modules.cjs");

function openPanel() {
  const registrations = new Map();
  let creation;
  const disposable = () => ({ dispose() {} });
  const panel = {
    webview: {
      postMessage() {},
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
      onDidChangeActiveTextEditor: disposable, onDidChangeTextEditorSelection: disposable,
      createWebviewPanel: (...args) => { creation = args; return panel; },
    },
    workspace: { textDocuments: [], onDidChangeTextDocument: disposable, onDidCloseTextDocument: disposable, onDidSaveTextDocument: disposable },
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
  const events = {};
  const listen = (name) => (handler) => { events[name] = handler; return disposable(); };
  const disposable = () => ({ dispose() {} });
  const document = { languageId: "acorn", isDirty: dirty, version: 1,
    uri: { scheme, toString: () => `${scheme}:test.ac` } };
  const editor = { document, selection: { start: { line: 0 } }, setDecorations() {} };
  const api = {
    commands: { registerTextEditorCommand: (name, callback) => { registrations.set(name, callback); return disposable(); } },
    window: { activeTextEditor: editor, createTextEditorDecorationType: disposable,
      onDidChangeActiveTextEditor: listen("active"), onDidChangeTextEditorSelection: listen("selection") },
    workspace: { textDocuments: [document], onDidChangeTextDocument: listen("change"), onDidCloseTextDocument: listen("close"), onDidSaveTextDocument: listen("save") },
  };
  const calls = [];
  const { Assistant } = loadEditorModule("assistant", { vscode: api, "vscode-languageclient/node": {} });
  const view = new Assistant({ isRunning: () => true, sendRequest: async (...args) => {
    calls.push(args);
    return sendRequest ? sendRequest(...args) : { loading: false, status: { outcome: "Success" } };
  } }, "/assistant");
  view.panel = { webview: { postMessage: (message) => messages.push(message) } };
  return { view, document, editor, api, calls, messages, registrations, events };
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
  assert.equal(f.messages.filter((message) => message.type === "search").length, 0);
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

test("document edits and editor switches clear proof context immediately", async () => {
  const f = searchFixture();
  await f.view.searchOnSelection(true);
  assert.ok(f.view.currentParams);
  f.document.isDirty = true;
  f.events.change({ document: f.document });
  assert.equal(f.view.currentParams, null);
  assert.equal(f.messages.at(-1).help.unsaved, true);
  f.api.window.activeTextEditor = { document: { languageId: "plaintext" } };
  f.events.active(f.api.window.activeTextEditor);
  assert.equal(f.messages.at(-1).help.noFile, true);
  f.api.window.activeTextEditor = f.editor;
  f.document.uri.scheme = "untitled";
  f.events.active();
  assert.equal(f.messages.at(-1).help.newDocument, true);
  assert.equal(f.calls.length, 1);
});

test("late clause information cannot repopulate an inactive Assistant", async () => {
  let finish;
  const f = searchFixture({ sendRequest: (method, params) => method === "acorn/info"
    ? new Promise((resolve) => { finish = resolve; })
    : { id: params.id, loading: false, status: { outcome: "Success" } } });
  await f.view.searchOnSelection(true);
  const searchId = f.view.currentSearchId;
  const pending = f.view.handleWebviewMessage({ command: "infoRequest", params: { searchId, clauseId: 0 } });
  f.api.window.activeTextEditor = { document: { languageId: "plaintext" } };
  f.events.active(f.api.window.activeTextEditor);
  finish({ searchId, result: { clause: {} } });
  await pending;
  assert.equal(f.messages.filter((message) => message.type === "info").length, 0);
  assert.equal(f.messages.at(-1).help.noFile, true);
});

test("webview readiness resends appropriate unsaved guidance without a search", async () => {
  const f = searchFixture({ scheme: "untitled" });
  await f.view.handleWebviewMessage({ command: "ready" });
  assert.equal(f.messages.at(-1).help.newDocument, true);
  assert.equal(f.calls.length, 0);
});

test("queued proof insertion is discarded when its editor context is invalidated", async () => {
  const f = searchFixture();
  await f.view.searchOnSelection(true);
  let inserted = 0;
  f.view.insertProof = async () => inserted++;
  const message = { command: "insertProof", searchId: f.view.currentSearchId, uri: f.document.uri.toString(), version: 1 };
  f.document.isDirty = true;
  await f.view.handleWebviewMessage(message);
  f.events.change({ document: f.document });
  f.document.isDirty = false;
  await f.view.handleWebviewMessage(message);
  assert.equal(inserted, 0);
});

test("focusing the Assistant retains its open source and permits proof actions", async () => {
  const f = searchFixture({ sendRequest: (method, params) => method === "acorn/info"
    ? { searchId: params.searchId, result: { clause: {} } }
    : { id: params.id, loading: false, status: { outcome: "Success" } } });
  await f.view.searchOnSelection(true);
  const params = f.view.currentParams;
  f.api.window.activeTextEditor = undefined;
  f.events.active(undefined);
  assert.equal(f.view.currentParams, params);
  await f.view.handleWebviewMessage({ command: "infoRequest", params: { searchId: params.id, clauseId: 0 } });
  assert.equal(f.messages.at(-1).type, "info");
  let inserted = 0;
  f.view.insertProof = async () => inserted++;
  const insert = { command: "insertProof", searchId: params.id, uri: params.uri, version: params.version };
  await f.view.handleWebviewMessage(insert);
  assert.equal(inserted, 1);
  f.api.workspace.textDocuments = [];
  f.document.isClosed = true;
  f.events.close(f.document);
  await f.view.handleWebviewMessage(insert);
  assert.equal(inserted, 1);
  assert.equal(f.messages.at(-1).help.noFile, true);
});

test("queued insertion from another goal in the same file is rejected", async () => {
  const f = searchFixture();
  await f.view.searchOnSelection(true);
  const old = f.view.currentParams;
  f.editor.selection.start.line = 1;
  await f.view.searchOnSelection(true);
  let inserted = 0;
  f.view.insertProof = async () => inserted++;
  await f.view.handleWebviewMessage({ command: "insertProof", searchId: old.id, uri: old.uri, version: old.version });
  assert.equal(inserted, 0);
  assert.notEqual(f.view.currentParams.id, old.id);
});

test("insertion revalidates document lifetime after awaiting editor focus", async () => {
  const f = searchFixture();
  await f.view.searchOnSelection(true);
  const params = f.view.currentParams;
  let focus;
  f.view.focusEditor = () => new Promise(resolve => { focus = resolve; });
  let edits = 0;
  f.view.insertAtLineStart = async () => { edits++; };
  const pending = f.view.handleWebviewMessage({ command: "insertProof", searchId: params.id, uri: params.uri,
    version: params.version, line: 0, insertBlock: false, code: ["true"] });
  f.document.isClosed = true;
  f.events.close(f.document);
  const replacement = { ...f.editor, document: { ...f.document, isClosed: false } };
  f.api.window.activeTextEditor = replacement;
  f.api.workspace.textDocuments = [replacement.document];
  f.events.active(replacement);
  focus(replacement);
  await pending;
  assert.equal(edits, 0);
});
