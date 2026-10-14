// Modified for Venticorn: exercise the compiled polling loop with a deterministic host.
const assert = require("node:assert/strict");
const test = require("node:test");
const { loadEditorModule } = require("./editor_modules.cjs");
const tick = () => new Promise(setImmediate);
function host(responses) {
  const state = { calls: 0, windows: 0, reports: [], logs: [], running: true, time: 0 };
  const { ProgressTracker } = loadEditorModule("progress", { vscode: {
    ProgressLocation: { Notification: 15 },
    window: { withProgress: async (options, callback) => {
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
const progress = (done, total = 2) => ({ buildId: 1, done, total, docs: {} });

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
