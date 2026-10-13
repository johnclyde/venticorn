// Modified for Venticorn.
// Exercise the compiled extension's startup callbacks without launching VS Code.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const test = require("node:test");
const vm = require("node:vm");

function loadExtension({ failInitialization = false, serverPath = "/server" } = {}) {
  const state = {
    notifications: [], logs: [], commands: [], save: [], open: [],
    starts: 0, stops: 0, requests: 0, client: undefined,
  };
  const disposable = () => ({ dispose() {} });
  const listen = (handlers) => (handler) => {
    handlers.push(handler);
    return disposable();
  };
  const vscode = {
    commands: {
      registerTextEditorCommand: (name) => {
        state.commands.push(name);
        return disposable();
      },
    },
    window: {
      createTextEditorDecorationType: disposable,
      createOutputChannel: disposable,
      onDidChangeTextEditorSelection: () => disposable(),
      showErrorMessage: (message) => {
        state.notifications.push(message);
        return Promise.resolve();
      },
    },
    workspace: {
      textDocuments: [],
      createFileSystemWatcher: disposable,
      onDidSaveTextDocument: listen(state.save),
      onDidOpenTextDocument: listen(state.open),
    },
  };
  class FakeLanguageClient {
    constructor(_id, _name, _serverOptions, options) {
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
    async sendRequest() {
      state.requests++;
      return { done: 0, total: 0 };
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
  const exported = {};
  const extensionRoot = path.join(__dirname, "../vscode/extension");
  const manifest = JSON.parse(fs.readFileSync(path.join(extensionRoot, "package.json"), "utf8"));
  const source = fs.readFileSync(path.join(extensionRoot, manifest.main), "utf8");
  vm.runInNewContext(source, {
    exports: exported,
    require: (name) => name === "vscode" ? vscode
      : name === "vscode-languageclient/node" ? clientApi : require(name),
    process: { env: serverPath ? { SERVER_PATH: serverPath } : {} },
    console: { log() {}, warn() {}, error() {} },
    setTimeout,
  });
  const context = { subscriptions: [], asAbsolutePath: (value) => value };
  return { state, context, ...exported };
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
  assert.equal(state.commands.length, 2);
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

test("deactivation stops a running client and disposes an unopened search panel", async () => {
  const extension = loadExtension();
  await extension.activate(extension.context);
  await extension.deactivate();
  assert.equal(extension.state.stops, 1);
  for (const subscription of extension.context.subscriptions) subscription.dispose();
});

test("a missing executable setting does not register proof-search commands", async () => {
  const extension = loadExtension({ serverPath: null });
  await extension.activate(extension.context);
  assert.equal(extension.state.starts, 0);
  assert.deepEqual(extension.state.commands, []);
  assert.deepEqual(extension.state.notifications, ["The SERVER_PATH environment variable is not defined."]);
  await extension.deactivate();
});
