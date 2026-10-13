const assert = require("node:assert/strict");
const { EventEmitter } = require("node:events");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { PassThrough } = require("node:stream");
const test = require("node:test");
const { loadEditorModule } = require("./editor_modules.cjs");

function fixture(t, responses) {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "venticorn-download-"));
  t.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const requests = [];
  const https = {
    get(url, _options, callback) {
      requests.push(String(url));
      const request = new EventEmitter();
      request.setTimeout = () => request;
      request.destroy = (error) => { if (error) request.emit("error", error); };
      queueMicrotask(() => {
        const next = responses.shift();
        if (!next) return request.emit("error", new Error("unexpected network request"));
        if (next.error) return request.emit("error", new Error(next.error));
        const response = new PassThrough();
        response.statusCode = next.status ?? 200;
        response.headers = next.headers ?? {};
        response.complete = next.complete ?? true;
        callback(response);
        setImmediate(() => {
          if (next.abort) {
            response.write("partial");
            response.destroy(new Error("connection reset"));
          } else {
            response.end(next.body ?? "server binary");
          }
        });
      });
      return request;
    },
  };
  const modules = { https, os: { platform: () => "linux", arch: () => "x64" } };
  const globals = { process: { env: {} } };
  const download = loadEditorModule("download", modules, globals);
  const server = loadEditorModule("server", modules, globals);
  const context = { extension: { packageJSON: { version: "0.1.0" } }, globalStorageUri: { fsPath: directory } };
  return { directory, requests, download, server, context };
}
const releaseUrl = "https://github.com/johnclyde/venticorn/releases/download/v0.1.0/venticornserver-v0.1.0-linux-x64";

test("release redirects install one complete file and the versioned cache avoids repeat downloads", async (t) => {
  const f = fixture(t, [
    { status: 302, headers: { location: "https://release-assets.githubusercontent.com/path?token=test" } },
    { body: "binary", headers: { "content-length": "6" } },
  ]);
  const [first, second] = await Promise.all([
    f.server.getServerPath(f.context), f.server.getServerPath(f.context),
  ]);
  assert.equal(first, second);
  assert.equal(fs.readFileSync(first, "utf8"), "binary");
  assert.equal(await f.server.getServerPath(f.context), first);
  assert.equal(f.requests.length, 2);
  assert.equal(f.requests[0], releaseUrl);
  assert.deepEqual(fs.readdirSync(path.dirname(first)), [path.basename(first)]);
});

test("unpublished assets report a local build fallback without leaving an executable", async (t) => {
  const f = fixture(t, [{ status: 404 }]);
  await assert.rejects(f.server.getServerPath(f.context), /not been published.*SERVER_PATH/);
  assert.deepEqual(fs.readdirSync(path.join(f.directory, "bin")), []);
  assert.equal(f.requests.length, 1);
});

test("redirects are HTTPS, restricted to release hosts, and bounded", async (t) => {
  for (const location of ["http://github.com/johnclyde/venticorn/releases/download/x/y", "https://example.com/server", "https://github.com/other/project/releases/download/x/y", "https://github.com:444/johnclyde/venticorn/releases/download/x/y"]) {
    const f = fixture(t, [{ status: 302, headers: { location } }]);
    await assert.rejects(f.download.downloadServer(releaseUrl, path.join(f.directory, "server")), /allowed GitHub HTTPS/);
    assert.equal(f.requests.length, 1);
    assert.deepEqual(fs.readdirSync(f.directory), []);
  }
  const f = fixture(t, Array.from({ length: 6 }, () => ({ status: 302, headers: { location: releaseUrl } })));
  await assert.rejects(f.download.downloadServer(releaseUrl, path.join(f.directory, "server")), /too many redirects/);
  assert.equal(f.requests.length, 6);
  assert.deepEqual(fs.readdirSync(f.directory), []);
});

test("status, network, stream, and size failures clean partial downloads", async (t) => {
  for (const response of [
    { status: 503 }, { error: "offline" }, { abort: true },
    { body: "short", headers: { "content-length": "12" } },
    { body: "long", headers: { "content-length": "2" } },
    { body: "", headers: {} }, { body: "short", complete: false },
    { headers: { "content-length": "0" } },
    { headers: { "content-length": "536870913" } },
    { headers: { "content-length": "invalid" } },
    { headers: { "content-encoding": "gzip" } },
  ]) {
    const f = fixture(t, [response]);
    await assert.rejects(f.download.downloadServer(releaseUrl, path.join(f.directory, "server")));
    assert.deepEqual(fs.readdirSync(f.directory), []);
  }
});

test("failed replacement preserves a previous complete file", async (t) => {
  const f = fixture(t, [{ abort: true }]);
  const destination = path.join(f.directory, "server");
  fs.writeFileSync(destination, "previous binary");
  await assert.rejects(f.download.downloadServer(releaseUrl, destination));
  assert.equal(fs.readFileSync(destination, "utf8"), "previous binary");
  assert.deepEqual(fs.readdirSync(f.directory), ["server"]);
});

test("an asset without Content-Length can complete safely", async (t) => {
  const f = fixture(t, [{ body: "whole binary" }]);
  const destination = path.join(f.directory, "server");
  await f.download.downloadServer(releaseUrl, destination);
  assert.equal(fs.readFileSync(destination, "utf8"), "whole binary");
});


test("a filesystem installation failure removes its temporary download", async (t) => {
  const f = fixture(t, [{ body: "binary" }]);
  const destination = path.join(f.directory, "server");
  fs.mkdirSync(destination);
  await assert.rejects(f.download.downloadServer(releaseUrl, destination));
  assert.deepEqual(fs.readdirSync(f.directory), ["server"]);
  assert.ok(fs.statSync(destination).isDirectory());
});
