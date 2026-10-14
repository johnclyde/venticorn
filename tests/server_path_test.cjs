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


test("cached POSIX servers regain executable permission", { skip: process.platform === "win32" }, async (t) => {
  const f = fixture(t);
  const directory = path.join(f.directory, "bin");
  fs.mkdirSync(directory);
  const binary = path.join(directory, "venticornserver-v0.1.0-linux-x64");
  fs.writeFileSync(binary, "cached binary", { mode: 0o600 });
  await f.getServerPath(f.context);
  assert.equal(fs.statSync(binary).mode & 0o777, 0o755);
});

test("Windows cached executables never use chmod", async () => {
  const server = loadEditorModule("server", {
    os: { platform: () => "win32", arch: () => "x64" },
    fs: { promises: {
      lstat: async () => ({ isFile: () => true, size: 8 }),
      chmod: async () => { throw new Error("chmod is unsupported"); },
    } },
  }, { process: { env: {} } });
  const context = { extension: { packageJSON: { version: "0.1.0" } }, globalStorageUri: { fsPath: "/storage" } };
  assert.equal(path.basename(await server.getServerPath(context)), "venticornserver-v0.1.0-win32-x64.exe");
});

test("cache clearing removes only owned assets and preserves SERVER_PATH", async (t) => {
  const env = {};
  const f = fixture(t, env);
  const bin = path.join(f.directory, "bin");
  fs.mkdirSync(bin);
  const keep = "venticornserver-v0.1.0-linux-x64";
  env.SERVER_PATH = path.join(bin, keep);
  for (const name of [keep, "venticornserver-v0.2.0-darwin-arm64", "venticornserver-v0.2.0-win32-x64.exe", "notes.txt", "venticornserver-v0.2.0-linux-x64.partial"]) fs.writeFileSync(path.join(bin, name), name);
  fs.mkdirSync(path.join(bin, "venticornserver-v0.3.0-linux-x64"));
  fs.symlinkSync(env.SERVER_PATH, path.join(bin, "venticornserver-v0.4.0-linux-x64"));
  assert.equal(await f.clearServerCache(f.context), 2);
  assert.equal(fs.readFileSync(env.SERVER_PATH, "utf8"), keep);
  assert.ok(fs.existsSync(path.join(bin, "notes.txt")));
  assert.ok(fs.existsSync(path.join(bin, "venticornserver-v0.2.0-linux-x64.partial")));
  assert.equal(fs.readdirSync(bin).length, 5);
});

test("cache clearing does not create storage or follow a directory symlink", async (t) => {
  const f = fixture(t);
  assert.equal(await f.clearServerCache(f.context), 0);
  assert.deepEqual(fs.readdirSync(f.directory), []);
  const elsewhere = fs.mkdtempSync(path.join(os.tmpdir(), "venticorn-cache-elsewhere-"));
  t.after(() => fs.rmSync(elsewhere, { recursive: true, force: true }));
  fs.writeFileSync(path.join(elsewhere, "venticornserver-v0.1.0-linux-x64"), "keep");
  fs.symlinkSync(elsewhere, path.join(f.directory, "bin"), "dir");
  await assert.rejects(f.clearServerCache(f.context), /not a regular directory/);
  assert.equal(fs.readdirSync(elsewhere).length, 1);
});

test("overlapping cache operations are rejected without downloading", async (t) => {
  const f = fixture(t);
  const first = f.clearServerCache(f.context);
  await assert.rejects(f.clearServerCache(f.context), /Wait for the current/);
  assert.equal(await first, 0);
});
