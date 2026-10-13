// Added for Venticorn. Download only versioned Venticorn release assets, then install them atomically.
import * as crypto from "crypto";
import * as fs from "fs";
import * as https from "https";
import type { IncomingMessage } from "http";
import { Transform } from "stream";
import { pipeline } from "stream/promises";
import { URL } from "url";

const releaseHosts = new Set([
  "github.com",
  "release-assets.githubusercontent.com",
  "objects.githubusercontent.com",
  "github-releases.githubusercontent.com",
]);
const maximumBytes = 512 * 1024 * 1024;
const maximumRedirects = 5;

function validateUrl(url: URL): void {
  if (url.protocol !== "https:" || url.username || url.password ||
      (url.port && url.port !== "443") || !releaseHosts.has(url.hostname) ||
      (url.hostname === "github.com" && !url.pathname.startsWith("/johnclyde/venticorn/releases/download/"))) {
    throw new Error("The release download redirected outside the allowed GitHub HTTPS hosts");
  }
}

function openResponse(url: URL): Promise<IncomingMessage> {
  return new Promise((resolve, reject) => {
    const request = https.get(url, {
      headers: { "User-Agent": "Venticorn-VSCode", "Accept": "application/octet-stream" },
    }, (response) => {
      response.once("close", () => clearTimeout(deadline));
      response.once("error", reject);
      resolve(response);
    });
    const deadline = setTimeout(() => request.destroy(new Error("Release download timed out")), 120_000);
    request.setTimeout(30_000, () => request.destroy(new Error("Release download stalled")));
    request.once("error", (error) => {
      clearTimeout(deadline);
      reject(error);
    });
  });
}

export async function downloadServer(url: string, serverPath: string): Promise<void> {
  const temporary = `${serverPath}.${crypto.randomUUID()}.partial`;
  let response: IncomingMessage | undefined;
  try {
    let current = new URL(url);
    for (let redirects = 0; ; redirects++) {
      validateUrl(current);
      response = await openResponse(current);
      const status = response.statusCode;
      if (status !== undefined && [301, 302, 303, 307, 308].includes(status)) {
        const location = response.headers.location;
        response.destroy();
        if (!location || redirects >= maximumRedirects) {
          throw new Error("The release download returned too many redirects or no redirect location");
        }
        current = new URL(location, current);
        continue;
      }
      if (status === 404) {
        throw new Error("The matching Venticorn release asset has not been published (HTTP 404)");
      }
      if (status !== 200) {
        throw new Error(`The release download failed with HTTP ${status ?? "unknown"}`);
      }
      break;
    }
    const length = response.headers["content-length"];
    const expected = length === undefined ? undefined : Number(length);
    if (length !== undefined && (!/^\d+$/.test(length) || !Number.isSafeInteger(expected) || expected <= 0 || expected > maximumBytes)) {
      throw new Error("The release asset has an invalid or excessive Content-Length");
    }
    if (response.headers["content-encoding"] && response.headers["content-encoding"] !== "identity") {
      throw new Error("The release asset uses an unsupported content encoding");
    }
    let received = 0;
    const count = new Transform({
      transform(chunk, _encoding, callback) {
        received += chunk.length;
        if (received > maximumBytes || (expected !== undefined && received > expected)) {
          callback(new Error("The release asset exceeded its expected size"));
        } else {
          callback(null, chunk);
        }
      },
    });
    await pipeline(response, count, fs.createWriteStream(temporary, { flags: "wx", mode: 0o755 }));
    if (!response.complete || received === 0 || (expected !== undefined && received !== expected)) {
      throw new Error("The release asset download was empty or incomplete");
    }
    await fs.promises.rename(temporary, serverPath);
  } finally {
    response?.destroy();
    await fs.promises.rm(temporary, { force: true });
  }
}
