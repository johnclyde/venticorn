// Modified for Venticorn.
// Exercise the compiled extension's startup callbacks without launching VS Code.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const test = require("node:test");
const { loadEditorModule } = require("./editor_modules.cjs");

function loadExtension({ failInitialization = false, serverPath = "/server", platform = process.platform, downloadReports, workspaceFolders, textDocuments = [], visibleEditors = [] } = {}) {
  const state = {
    notifications: [], logs: [], output: [], channels: [], commands: [], save: [], open: [], fileCommands: new Map(), newDocuments: [], shownDocuments: [],
    starts: 0, stops: 0, requests: 0, requestCalls: [], activeEditorChanges: [], panels: [], client: undefined, downloadWindows: [], reports: [],
  };
  const disposable = () => ({ dispose() {} });
  const listen = (handlers) => (handler) => {
    handlers.push(handler);
    return disposable();
  };
  const vscode = {
    ProgressLocation: { Notification: 15 },
    commands: {
      registerCommand: (name, callback) => {
        state.fileCommands.set(name, callback);
        return { dispose: () => state.fileCommands.delete(name) };
      },
      registerTextEditorCommand: (name) => {
        state.commands.push(name);
        return disposable();
      },
    },
    ViewColumn: { Two: 2, Three: 3 },
    Uri: { file: (fsPath) => ({ fsPath }) },
    window: {
      visibleTextEditors: visibleEditors,
      activeTextEditor: visibleEditors[0],
      onDidChangeActiveTextEditor: listen(state.activeEditorChanges),
      createWebviewPanel: (...args) => {
        const handlers = [];
        const panel = {
          args,
          webview: {
            cspSource: "https://host.vscode-cdn.net",
            asWebviewUri: () => ({ toString: () => "https://host.vscode-cdn.net/assistant" }),
            onDidReceiveMessage: disposable,
            postMessage() {},
          },
          onDidDispose: (handler) => { handlers.push(handler); return disposable(); },
          dispose: () => { for (const handler of handlers) handler(); },
        };
        state.panels.push(panel);
        return panel;
      },
      showTextDocument: async (document) => { state.shownDocuments.push(document); },
      withProgress: async (options, task) => {
        state.downloadWindows.push(options);
        return task({ report: (report) => state.reports.push(report) }, { onCancellationRequested() {} });
      },
      createTextEditorDecorationType: disposable,
      createOutputChannel: (name) => {
        state.channels.push(name);
        return { ...disposable(), appendLine: (message) => state.output.push(message) };
      },
      onDidChangeTextEditorSelection: () => disposable(),
      showErrorMessage: (message) => {
        state.notifications.push(message);
        return Promise.resolve();
      },
    },
    workspace: {
      openTextDocument: async (options) => {
        const document = { ...options, uri: "untitled:new-file" };
        state.newDocuments.push(document);
        return document;
      },
      workspaceFolders,
      textDocuments,
      createFileSystemWatcher: disposable,
      onDidSaveTextDocument: listen(state.save),
      onDidOpenTextDocument: listen(state.open),
    },
  };
  class FakeLanguageClient {
    constructor(_id, _name, _serverOptions, options) {
      state.serverOptions = _serverOptions;
      this.options = options;
      this.running = false;
      state.client = this;
    }
    async start() {
      state.starts++;
      if (failInitialization) {
        const error = new Error("no library found; set VENTICORN_LIBRARY");
        state.retry = this.options.initializationFailedHandler(error);
        // vscode-languageclient 9 also force-reports the rejected start after
        // invoking initializationFailedHandler. Exercise that virtual call.
        this.error("client could not create a connection", error, "force");
        throw error;
      }
      this.running = true;
    }
    isRunning() { return this.running; }
    async stop() {
      state.stops++;
      this.running = false;
    }
    async sendRequest(method, params) {
      state.requests++;
      state.requestCalls.push({ method, params });
      if (method === "acorn/search") return { loading: false, status: { outcome: "Success" } };
      return undefined;
    }
    error(message, data, showNotification = true) {
      state.logs.push({ message, data, showNotification });
      if (showNotification) state.notifications.push(message);
    }
  }
  const clientApi = {
    LanguageClient: FakeLanguageClient,
    CloseAction: { DoNotRestart: 1 },
    ErrorAction: { Shutdown: 2 },
  };
  const exported = loadEditorModule("extension", {
    ...(downloadReports ? { "./server": {
      getServerPath: async (_context, showProgress) => {
        await showProgress("server", async (report) => {
          for (const [received, total] of downloadReports) report(received, total);
        });
        return "/downloaded-server";
      },
    } } : {}),
    vscode,
    "vscode-languageclient/node": clientApi,
    os: { platform: () => platform, arch: () => platform === "darwin" ? "arm64" : "x64" },
    fs: { ...fs,
      readFileSync: (filename, encoding) => filename.endsWith("index.html") ? "<html><head></head></html>" : fs.readFileSync(filename, encoding),
      promises: {
      ...fs.promises,
      lstat: async () => { throw Object.assign(new Error("missing"), { code: "ENOENT" }); },
      mkdir: async () => {}, rm: async () => {},
    } },
    https: { get() { throw new Error("offline test"); } },
  }, {
    process: { env: serverPath ? { SERVER_PATH: serverPath } : {}, platform },
    console: { log() {}, warn() {}, error() {} },
  });
  const context = {
    extensionPath: "/installed extension",
    subscriptions: [], asAbsolutePath: (value) => value,
    extension: { packageJSON: { version: "0.1.0" } },
    globalStorageUri: { fsPath: "/extension-storage" },
  };
  return { state, context, vscode, ...exported };
}

test("failed initialization shows one specific error and installs no UI listeners", async () => {
  const extension = loadExtension({ failInitialization: true });
  await extension.activate(extension.context);
  const { state } = extension;
  assert.equal(state.starts, 1);
  assert.equal(state.retry, false);
  assert.deepEqual(state.notifications, ["Venticorn: no library found; set VENTICORN_LIBRARY"]);
  assert.equal(state.logs.length, 1);
  assert.equal(state.logs[0].showNotification, false);
  assert.deepEqual(state.commands, []);
  assert.deepEqual(state.save, []);
  assert.deepEqual(state.open, []);
  assert.equal(state.client.options.errorHandler.closed().handled, true);
  assert.equal(state.client.options.errorHandler.error(new Error("closed")).handled, true);
  state.client.options.initializationFailedHandler(new Error("repeated failure"));
  assert.equal(state.notifications.length, 1);
  await extension.deactivate();
  assert.equal(state.stops, 0);
});

test("a stopped initialized client receives no document requests or restart", async () => {
  const extension = loadExtension();
  await extension.activate(extension.context);
  const { state } = extension;
  assert.equal(state.commands.length, 6);
  assert.equal(state.notifications.length, 0);
  state.client.running = false;
  for (const handler of [...state.save, ...state.open]) {
    await handler({ languageId: "acorn" });
  }
  assert.equal(state.requests, 0);
  assert.equal(state.starts, 1);
  const closed = state.client.options.errorHandler.closed();
  assert.equal(closed.action, 1);
  assert.equal(closed.handled, false);
  const error = state.client.options.errorHandler.error(new Error("transport"));
  assert.equal(error.action, 2);
  assert.equal(error.handled, false);
  state.client.error("unexpected runtime error", undefined, "force");
  assert.deepEqual(state.notifications, ["unexpected runtime error"]);
});

test("deactivation stops a running client and disposes an unopened assistant", async () => {
  const extension = loadExtension();
  await extension.activate(extension.context);
  await extension.deactivate();
  assert.equal(extension.state.stops, 1);
  for (const subscription of extension.context.subscriptions) subscription.dispose();
});

test("an unavailable server reports one error and registers no proof-search commands", async () => {
  const extension = loadExtension({ serverPath: null });
  await extension.activate(extension.context);
  assert.equal(extension.state.starts, 0);
  assert.deepEqual(extension.state.commands, []);
  assert.equal(extension.state.notifications.length, 1);
  assert.match(extension.state.notifications[0], /SERVER_PATH/);
  await extension.deactivate();
});

test("the configured executable is used without copying it into the extension", async () => {
  const command = path.join("/local checkout", "venticornserver");
  const extension = loadExtension({ serverPath: command });
  await extension.activate(extension.context);
  assert.equal(extension.state.serverOptions.run.command, command);
  assert.equal(extension.state.serverOptions.debug.command, command);
  await extension.deactivate();
});


test("the extracted assistant does not send requests after its client stops", async () => {
  const extension = loadExtension();
  await extension.activate(extension.context);
  const panel = extension.context.subscriptions.find((value) => typeof value.sendSearchRequest === "function");
  assert.ok(panel);
  extension.state.client.running = false;
  await panel.sendSearchRequest({ id: 1, uri: "file:///proof.ac", version: 1, selectedLine: 0 });
  await panel.handleWebviewMessage({ command: "infoRequest", params: { clauseId: 1 } });
  assert.equal(extension.state.requests, 0);
  panel.dispose();
});


test("download notifications report bounded monotonic progress and support unknown sizes", async () => {
  const known = loadExtension({ downloadReports: [[0, 10], [5, 10], [4, 10], [10, 10], [12, 10]] });
  await known.activate(known.context);
  assert.equal(known.state.downloadWindows.length, 1);
  assert.equal(known.state.starts, 1);
  assert.deepEqual(known.state.reports.map((value) => value.increment), [0, 50, 0, 50, 0]);
  for (const total of [undefined, 0]) {
    const unknown = loadExtension({ downloadReports: [[0, total], [1024, total]] });
    await unknown.activate(unknown.context);
    assert.equal(unknown.state.downloadWindows.length, 1);
    assert.ok(unknown.state.reports.every((value) => value.increment === undefined && /MiB received/.test(value.message)));
  }
});


test("extension setup and failures remain visible in its output channel", async () => {
  const configured = loadExtension({ serverPath: "/configured/server" });
  await configured.activate(configured.context);
  assert.deepEqual(configured.state.channels, ["Venticorn Extension"]);
  assert.ok(configured.state.output.some(line => line.includes("/configured/server")));
  const failed = loadExtension({ serverPath: null });
  await failed.activate(failed.context);
  assert.ok(failed.state.output.some(line => line.includes("Language server setup failed")));
  assert.ok(failed.state.output.some(line => line.includes("offline test")));
  assert.equal(failed.state.notifications.length, 1);
});


test("local workspace roots are passed as one literal server argument", async () => {
  const root = "/workspace with spaces/proofs";
  const extension = loadExtension({ workspaceFolders: [{ uri: { scheme: "file", fsPath: root } }] });
  await extension.activate(extension.context);
  assert.deepEqual(Array.from(extension.state.serverOptions.run.args), ["--extension-root", "/installed extension", "--workspace-root", root]);
  const remote = loadExtension({ workspaceFolders: [{ uri: { scheme: "vscode-remote", fsPath: "/remote" } }] });
  await remote.activate(remote.context);
  assert.deepEqual(Array.from(remote.state.serverOptions.run.args), ["--extension-root", "/installed extension"]);
});

test("New Venticorn File opens the language mode even when the server is unavailable", async () => {
  const extension = loadExtension({ serverPath: null });
  await extension.activate(extension.context);
  await extension.state.fileCommands.get("acorn.newFile")();
  assert.equal(extension.state.newDocuments.length, 1);
  assert.equal(extension.state.newDocuments[0].language, "acorn");
  assert.equal(extension.state.shownDocuments[0], extension.state.newDocuments[0]);
  for (const subscription of extension.context.subscriptions) subscription.dispose();
  assert.equal(extension.state.fileCommands.size, 0);
});

test("untitled Acorn documents do not request verification before saving", async () => {
  const document = { languageId: "acorn", uri: { scheme: "untitled" } };
  const extension = loadExtension({ textDocuments: [document] });
  await extension.activate(extension.context);
  for (const handler of [...extension.state.open, ...extension.state.save]) await handler(document);
  assert.equal(extension.state.requests, 0);
  assert.equal(extension.state.notifications.length, 0);
  assert.equal(extension.state.client.options.documentSelector[0].scheme, "file");
});

function acornEditor(scheme = "file", name = "proof.ac") {
  return {
    document: { languageId: "acorn", version: 1, uri: { scheme, toString: () => `${scheme}:///${name}` } },
    selection: { start: { line: 0 } }, viewColumn: 1, setDecorations() {},
  };
}

test("untitled documents stay quiet until saved and the Assistant opens only once", async () => {
  const untitled = acornEditor("untitled");
  const extension = loadExtension();
  await extension.activate(extension.context);
  extension.vscode.window.visibleTextEditors = [untitled];
  extension.vscode.window.activeTextEditor = untitled;
  for (const handler of extension.state.open) await handler(untitled.document);
  for (const handler of extension.state.activeEditorChanges) handler(untitled);
  const assistant = extension.context.subscriptions.find((value) => typeof value.autoDisplay === "function");
  await assistant.searchOnSelection(true);
  assert.equal(extension.state.requests, 0);
  assert.equal(extension.state.panels.length, 0);
  const saved = acornEditor();
  extension.vscode.window.visibleTextEditors = [saved];
  extension.vscode.window.activeTextEditor = saved;
  for (const handler of extension.state.save) await handler(saved.document);
  assert.equal(extension.state.panels.length, 1);
  assert.equal(extension.state.panels[0].args[2].preserveFocus, true);
  assert.ok(extension.state.requestCalls.some((call) => call.method === "acorn/progress"));
  assert.ok(extension.state.requestCalls.some((call) => call.method === "acorn/search" && call.params.uri === "file:///proof.ac"));
  extension.state.panels[0].dispose();
  for (const handler of extension.state.activeEditorChanges) handler(saved);
  for (const handler of extension.state.save) await handler(saved.document);
  assert.equal(extension.state.panels.length, 1);
});

test("a file opened before it becomes visible opens the Assistant when activated", async () => {
  const extension = loadExtension();
  await extension.activate(extension.context);
  const editor = acornEditor();
  for (const handler of extension.state.open) await handler(editor.document);
  assert.equal(extension.state.panels.length, 0);
  extension.vscode.window.visibleTextEditors = [editor];
  extension.vscode.window.activeTextEditor = editor;
  for (const handler of extension.state.activeEditorChanges) handler(editor);
  assert.equal(extension.state.panels.length, 1);
});
