// Added for Venticorn. Resolve the matching language server without depending on the working directory.
import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import type { ExtensionContext } from "vscode";

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
    return serverPath;
  }
  throw new Error(`No cached language server is available at ${serverPath}. ${localBuildHelp}`);
}
