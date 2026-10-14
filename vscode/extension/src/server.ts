// Added for Venticorn. Resolve the matching language server without depending on the working directory.
import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import type { ExtensionContext } from "vscode";
import { downloadServer, DownloadProgress } from "./download";

const downloads = new Map<string, Promise<string>>();
let clearingCache = false;

const supportedPlatforms = new Set(["linux-x64", "win32-x64", "darwin-arm64"]);
export const localBuildHelp = "Build locally with cargo build --locked --release --bin venticornserver, set SERVER_PATH to the binary's absolute path before starting VS Code, then reload the window.";

export function serverAsset(version: string, platform = os.platform(), arch = os.arch()): string {
  if (typeof version !== "string" || !/^\d+\.\d+\.\d+$/.test(version)) {
    throw new Error("The extension has an invalid server version. " + localBuildHelp);
  }
  if (!supportedPlatforms.has(`${platform}-${arch}`)) {
    throw new Error(`No packaged server supports ${platform}-${arch}. ${localBuildHelp}`);
  }
  return `venticornserver-v${version}-${platform}-${arch}${platform === "win32" ? ".exe" : ""}`;
}

async function isCachedServer(serverPath: string): Promise<boolean> {
  try {
    const stat = await fs.promises.lstat(serverPath);
    if (!stat.isFile()) {
      throw new Error(`The cached server is not a regular file: ${serverPath}`);
    }
    return stat.size > 0;
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === "ENOENT") {
      return false;
    }
    throw error;
  }
}

async function ensureExecutable(serverPath: string): Promise<void> {
  // Windows does not use POSIX executable bits; chmod can fail on its filesystems.
  if (os.platform() !== "win32") {
    await fs.promises.chmod(serverPath, 0o755);
  }
}

export type ShowDownloadProgress = (
  asset: string,
  download: (progress?: DownloadProgress) => Promise<void>,
) => Promise<void>;

export async function getServerPath(context: ExtensionContext, showDownloadProgress?: ShowDownloadProgress, log: (message: string) => void = () => {}): Promise<string> {
  if (process.env.SERVER_PATH !== undefined) {
    if (!process.env.SERVER_PATH.trim()) {
      throw new Error("SERVER_PATH is empty. " + localBuildHelp);
    }
    log(`Using configured language server: ${process.env.SERVER_PATH}`);
    return process.env.SERVER_PATH;
  }
  if (clearingCache) {
    throw new Error("The language server cache is being cleared. Try again when it finishes.");
  }
  const asset = serverAsset(context.extension.packageJSON.version);
  const serverPath = path.join(context.globalStorageUri.fsPath, "bin", asset);
  if (await isCachedServer(serverPath)) {
    await ensureExecutable(serverPath);
    log(`Using cached language server: ${serverPath}`);
    return serverPath;
  }
  if (clearingCache) {
    throw new Error("The language server cache is being cleared. Try again when it finishes.");
  }
  let pending = downloads.get(serverPath);
  if (!pending) {
    pending = (async () => {
      try {
        await fs.promises.mkdir(path.dirname(serverPath), { recursive: true });
        const url = `https://github.com/johnclyde/venticorn/releases/download/v${context.extension.packageJSON.version}/${asset}`;
        log(`Downloading ${url} to ${serverPath}`);
        const download = (progress?: DownloadProgress) => downloadServer(url, serverPath, progress);
        if (showDownloadProgress) {
          await showDownloadProgress(asset, download);
        } else {
          await download();
        }
        await ensureExecutable(serverPath);
        log(`Language server download complete: ${serverPath}`);
        return serverPath;
      } catch (error) {
        log(`Language server setup failed: ${(error as Error).message}`);
        throw new Error(`Could not prepare ${asset}: ${(error as Error).message}. ${localBuildHelp}`);
      } finally {
        downloads.delete(serverPath);
      }
    })();
    downloads.set(serverPath, pending);
  }
  return pending;
}

// Clear only completed, owned server assets. Never start a client or download here.
export async function clearServerCache(context: ExtensionContext): Promise<number> {
  if (clearingCache || downloads.size > 0) {
    throw new Error("Wait for the current language server download or cache operation to finish.");
  }
  clearingCache = true;
  try {
    const directory = path.join(context.globalStorageUri.fsPath, "bin");
    let entries: string[];
    try {
      const stat = await fs.promises.lstat(directory);
      if (!stat.isDirectory() || stat.isSymbolicLink()) {
        throw new Error("The language server cache directory is not a regular directory.");
      }
      entries = await fs.promises.readdir(directory);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === "ENOENT") return 0;
      throw error;
    }
    const override = process.env.SERVER_PATH;
    const protectedPath = override ? path.resolve(override) : undefined;
    const protectedRealPath = protectedPath
      ? await fs.promises.realpath(protectedPath).catch(() => protectedPath) : undefined;
    let removed = 0;
    for (const name of entries) {
      if (!/^venticornserver-v\d+\.\d+\.\d+-(?:linux-x64|darwin-arm64|win32-x64\.exe)$/.test(name)) continue;
      const candidate = path.join(directory, name);
      if (path.resolve(candidate) === protectedPath) continue;
      const stat = await fs.promises.lstat(candidate);
      if (!stat.isFile() || stat.isSymbolicLink()) continue;
      if (protectedRealPath && await fs.promises.realpath(candidate) === protectedRealPath) continue;
      await fs.promises.unlink(candidate);
      removed++;
    }
    return removed;
  } finally {
    clearingCache = false;
  }
}
