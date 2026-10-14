// Modified for Venticorn: exercise the compiled polling loop with a deterministic host.
const assert = require("node:assert/strict");
const test = require("node:test");
const { loadEditorModule } = require("./editor_modules.cjs");
const tick = () => new Promise(setImmediate);
function host(responses) {
  const state = { calls: 0, windows: 0, reports: [], logs: [], running: true, time: 0, editors: [], events: {} };
  const listen = name => callback => { state.events[name] = callback; return { dispose() {} }; };
  const { ProgressTracker } = loadEditorModule("progress", { vscode: {
    ProgressLocation: { Notification: 15 },
    Uri: { parse: value => value },
    Range: class { constructor(line) { this.start = { line }; } },
    workspace: {
      onDidChangeTextDocument: listen("change"), onDidCloseTextDocument: listen("close"), onDidOpenTextDocument: listen("open"),
    },
    window: { visibleTextEditors: state.editors,
      onDidChangeVisibleTextEditors: listen("visible"),
      createTextEditorDecorationType: () => ({ dispose() {} }),
      withProgress: async (options, callback) => {
      state.windows++; assert.equal(options.cancellable, false);
      await callback({ report: value => state.reports.push(value) });
    } },
  } });
  const tracker = new ProgressTracker({
    isRunning: () => state.running,
    sendRequest: async () => { state.calls++; const value = responses.shift(); if (value instanceof Error) throw value; return typeof value === "function" ? value() : value; },
  }, message => state.logs.push(message), {
    now: () => state.time,
    pause: async ms => { state.time += ms; await tick(); },
  });
  return { tracker, state };
}
const progress = (done, total = 2) => ({ buildId: 1, done, total, finished: done >= total, docs: {} });

test("overlapping triggers share one polling loop and notification", async () => {
  const { tracker, state } = host([progress(0), progress(1), progress(2)]);
  await Promise.all([tracker.track(), tracker.track(), tracker.track()]);
  assert.equal(state.calls, 3); assert.equal(state.windows, 1);
  assert.ok(state.reports.every(report => report.increment >= 0));
});
test("request failure releases the tracker for a later build", async () => {
  const { tracker, state } = host([new Error("temporary"), progress(0), progress(2)]);
  await tracker.track(); await tracker.track();
  assert.equal(state.logs.length, 1); assert.equal(state.windows, 1);
});
test("disposal and a stopped client prevent more polling", async () => {
  let release;
  const { tracker, state } = host([() => new Promise(resolve => { release = resolve; })]);
  const pending = tracker.track(); tracker.dispose(); release(progress(0)); await pending;
  await tracker.track(); assert.equal(state.calls, 1); assert.equal(state.windows, 0);
  const stopped = host([]); stopped.state.running = false;
  await stopped.tracker.track(); assert.equal(stopped.state.calls, 0);
});

test("a completed new build is observed without waiting for nonzero work", async () => {
  const { tracker, state } = host([progress(2), { ...progress(0, 0), buildId: 2 }]);
  await tracker.track(); await tracker.track();
  assert.equal(state.calls, 2); assert.equal(state.windows, 0); assert.equal(state.time, 0);
});
test("tracking waits for a new build identity instead of redisplaying a completed build", async () => {
  const { tracker, state } = host([progress(2), progress(2), { ...progress(0), buildId: 2 }, { ...progress(2), buildId: 2 }]);
  await tracker.track(); await tracker.track();
  assert.equal(state.calls, 4); assert.equal(state.windows, 1);
});

function editor(state, version = 1) {
  const value = { document: { uri: { scheme: "file", toString: () => "file:///proof.ac" }, languageId: "acorn", version, lineCount: 5 },
    lines: [], setDecorations(_type, values) { this.lines = Array.from(values, value => value.range.start.line); } };
  state.editors.push(value); return value;
}
const marked = (buildId = 1, version = 1) => ({ buildId, done: 1, total: 1, finished: true, docs: { "file:///proof.ac": { version, verified: [[0, 0]] } } });
test("markers clear immediately on edit and reject a mismatched editor version", async () => {
  const { tracker, state } = host([marked(), marked(2, 1), marked(3, 2)]);
  const view = editor(state); await tracker.getProgress(); assert.deepEqual(view.lines, [0]);
  view.document.version = 2; state.events.change({ document: view.document, contentChanges: [{ text: "edit" }] }); assert.deepEqual(view.lines, []);
  await tracker.getProgress(); assert.deepEqual(view.lines, []);
  await tracker.getProgress(); assert.deepEqual(view.lines, [0]);
});
test("cached results cannot decorate a reopened same-version document", async () => {
  const { tracker, state } = host([marked(), marked(1), marked(2)]);
  const old = editor(state); await tracker.getProgress(); assert.deepEqual(old.lines, [0]);
  state.events.close(state.editors[0].document); state.events.open(state.editors[0].document); state.editors.splice(0); const reopened = editor(state);
  tracker.updateDecorations(reopened); assert.deepEqual(reopened.lines, []);
  await tracker.getProgress(); assert.deepEqual(reopened.lines, []);
  await tracker.getProgress(); assert.deepEqual(reopened.lines, [0]);
});
test("an in-flight response crossing close and reopen is retried before decorating", async () => {
  let release;
  const { tracker, state } = host([() => new Promise(resolve => { release = resolve; }), { ...marked(2), docs: {} }]);
  editor(state); const pending = tracker.getProgress();
  // Close invalidates before its polling loop can observe a new document lifetime.
  state.events.close(state.editors[0].document); state.events.open(state.editors[0].document); state.editors.splice(0); const reopened = editor(state);
  release(marked()); await pending; assert.deepEqual(reopened.lines, []); assert.equal(state.calls, 2);
});
test("out-of-order progress responses cannot replace the newest markers", async () => {
  let release;
  const { tracker, state } = host([() => new Promise(resolve => { release = resolve; }), { ...marked(2), docs: {} }]);
  const view = editor(state); const old = tracker.getProgress(); await tracker.getProgress();
  release(marked()); await old; assert.deepEqual(view.lines, []);
});

test("a trigger during the last in-flight request observes the following build", async () => {
  let release;
  const { tracker, state } = host([progress(0), () => new Promise(resolve => { release = resolve; }), marked(2)]);
  const view = editor(state); const first = tracker.track();
  while (!release) await tick();
  const second = tracker.track(); release(progress(2));
  await Promise.all([first, second]);
  assert.equal(state.calls, 3); assert.deepEqual(view.lines, [0]);
});

test("unrelated and metadata-only document events preserve Acorn marks", async () => {
  const { tracker, state } = host([marked(), marked()]);
  const view = editor(state); await tracker.getProgress();
  const markdown = { languageId: "markdown", uri: { scheme: "file" } };
  const untitled = { languageId: "acorn", uri: { scheme: "untitled" } };
  for (const document of [markdown, untitled]) {
    state.events.open(document); state.events.close(document);
    state.events.change({ document, contentChanges: [{ text: "changed" }] });
  }
  state.events.change({ document: view.document, contentChanges: [] });
  assert.deepEqual(view.lines, [0]); await tracker.getProgress(); assert.deepEqual(view.lines, [0]);
});
test("dirty documents never receive cached marks even when versions match", async () => {
  const { tracker, state } = host([marked()]);
  const view = editor(state); view.document.isDirty = true;
  await tracker.getProgress(); assert.deepEqual(view.lines, []);
});

test("a newly visible editor receives only its current cached marks", async () => {
  const { tracker, state } = host([marked()]);
  await tracker.getProgress(); const view = editor(state);
  state.events.visible([view]); assert.deepEqual(view.lines, [0]);
  view.document.version = 2; state.events.visible([view]); assert.deepEqual(view.lines, []);
  assert.equal(state.calls, 1);
});

test("a completed proof range creates one marker at its first line", async () => {
  const response = marked(); response.docs["file:///proof.ac"].verified = [[0, 3], [4, 4]];
  const { tracker, state } = host([response]); const view = editor(state);
  await tracker.getProgress(); assert.deepEqual(view.lines, [0, 4]);
});

test("an empty document gets fresh markers only after its edited text is saved", async () => {
  const empty = { buildId: 1, done: 0, total: 0, finished: true, docs: { "file:///proof.ac": { version: 1, verified: [] } } };
  const { tracker, state } = host([empty, empty, marked(2, 2)]);
  const view = editor(state);
  state.events.open(view.document);
  await tracker.getProgress();
  assert.deepEqual(view.lines, []);
  view.document.version = 2;
  state.events.change({ document: view.document, contentChanges: [{ text: "theorem ready { true }" }] });
  await tracker.getProgress();
  assert.deepEqual(view.lines, []);
  await tracker.getProgress();
  assert.deepEqual(view.lines, [0]);
});


test("polling keeps the final range even when counts finish before publication", async () => {
  const pending = { ...progress(0, 0), finished: false };
  const counted = { ...progress(1, 1), finished: false };
  const { tracker, state } = host([pending, counted, marked()]);
  const view = editor(state);
  await tracker.track();
  assert.equal(state.calls, 3);
  assert.deepEqual(view.lines, [0]);
  assert.ok(state.reports.every(report => Number.isFinite(report.increment)));
});

test("an initial zero count waits for an explicitly finished empty build", async () => {
  const initial = { buildId: null, done: 0, total: 0, finished: false, docs: {} };
  const { tracker, state } = host([initial, { ...progress(0, 0), finished: false }, progress(0, 0)]);
  await tracker.track();
  assert.equal(state.calls, 3); assert.equal(state.windows, 1);
  assert.deepEqual(state.reports, []);
});

test("an unsaved edit without a replacement build stops the active poll", async () => {
  const { tracker, state } = host([progress(0), { buildId: null, done: 0, total: 0, finished: false, docs: {} }]);
  await tracker.track();
  assert.equal(state.calls, 2);
  assert.equal(state.windows, 1);
  assert.equal(state.logs.length, 0);
});
