// Added for Venticorn. Resolve the matching language server without depending on the working directory.
import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import type { ExtensionContext } from "vscode";
import { downloadServer } from "./download";

const downloads = new Map<string, Promise<string>>();

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

export async function getServerPath(context: ExtensionContext): Promise<string> {
  if (process.env.SERVER_PATH !== undefined) {
    if (!process.env.SERVER_PATH.trim()) {
      throw new Error("SERVER_PATH is empty. " + localBuildHelp);
    }
    return process.env.SERVER_PATH;
  }
  const asset = serverAsset(context.extension.packageJSON.version);
  const serverPath = path.join(context.globalStorageUri.fsPath, "bin", asset);
  if (await isCachedServer(serverPath)) {
    await ensureExecutable(serverPath);
    return serverPath;
  }
  let pending = downloads.get(serverPath);
  if (!pending) {
    pending = (async () => {
      try {
        await fs.promises.mkdir(path.dirname(serverPath), { recursive: true });
        const url = `https://github.com/johnclyde/venticorn/releases/download/v${context.extension.packageJSON.version}/${asset}`;
        await downloadServer(url, serverPath);
        await ensureExecutable(serverPath);
        return serverPath;
      } catch (error) {
        throw new Error(`Could not prepare ${asset}: ${(error as Error).message}. ${localBuildHelp}`);
      } finally {
        downloads.delete(serverPath);
      }
    })();
    downloads.set(serverPath, pending);
  }
  return pending;
}
