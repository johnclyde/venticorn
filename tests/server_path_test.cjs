const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const test = require("node:test");
const { loadEditorModule } = require("./editor_modules.cjs");

function fixture(t, env = {}, platform = "linux", arch = "x64") {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "venticorn-server-path-"));
  t.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const server = loadEditorModule("server", {
    os: { platform: () => platform, arch: () => arch },
    https: { get() { throw new Error("No network in server path tests"); } },
  }, { process: { env } });
  return {
    ...server, directory,
    context: { extension: { packageJSON: { version: "0.1.0" } }, globalStorageUri: { fsPath: directory } },
  };
}

test("explicit SERVER_PATH wins even for an unsupported packaged platform", async (t) => {
  const f = fixture(t, { SERVER_PATH: "/custom/server" }, "freebsd", "x64");
  assert.equal(await f.getServerPath(f.context), "/custom/server");
  assert.deepEqual(fs.readdirSync(f.directory), []);
});

test("asset names include the exact version and Windows executable suffix", (t) => {
  const f = fixture(t);
  assert.equal(f.serverAsset("0.1.0", "linux", "x64"), "venticornserver-v0.1.0-linux-x64");
  assert.equal(f.serverAsset("0.1.0", "darwin", "arm64"), "venticornserver-v0.1.0-darwin-arm64");
  assert.equal(f.serverAsset("0.1.0", "win32", "x64"), "venticornserver-v0.1.0-win32-x64.exe");
  assert.throws(() => f.serverAsset("../other", "linux", "x64"), /invalid server version/);
  assert.throws(() => f.serverAsset("0.1.0", "linux", "arm64"), /No packaged server supports/);
});

test("a matching cached binary is reused without needing a checkout", async (t) => {
  const f = fixture(t);
  const directory = path.join(f.directory, "bin");
  fs.mkdirSync(directory);
  const binary = path.join(directory, "venticornserver-v0.1.0-linux-x64");
  fs.writeFileSync(binary, "cached binary", { mode: 0o755 });
  assert.equal(await f.getServerPath(f.context), binary);
});

test("empty overrides and absent cached servers report actionable errors", async (t) => {
  const empty = fixture(t, { SERVER_PATH: " " });
  await assert.rejects(empty.getServerPath(empty.context), /SERVER_PATH is empty/);
  const missing = fixture(t);
  await assert.rejects(missing.getServerPath(missing.context), /SERVER_PATH/);
});
