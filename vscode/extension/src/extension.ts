// Modified for Venticorn: editor-facing names and language-server lifecycle.
import {
  ExtensionContext, OutputChannel, ProgressLocation, TextDocument, window, workspace,
} from "vscode";
import * as os from "os";
import {
  CloseAction,
  ErrorAction,
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";

import { getServerPath } from "./server";
import { InfoView } from "./info-view";

class VenticornLanguageClient extends LanguageClient {
  initializationFailed = false;

  error(message: string, data?: unknown, showNotification: boolean | "force" = true) {
    // The client library force-reports a rejected start even after our specific
    // initialization message. Keep that report in the output channel only.
    const alreadyReported = this.initializationFailed && showNotification === "force";
    super.error(message, data, alreadyReported ? false : showNotification);
  }
}

let client: VenticornLanguageClient;
let outputChannel: OutputChannel | undefined;

function log(message: string) {
  outputChannel?.appendLine(`[${new Date().toLocaleTimeString()}] ${message}`);
}

async function getProgress() {
  if (!client?.isRunning()) {
    return undefined;
  }
  try {
    return await client.sendRequest("acorn/progress", {});
  } catch (e) {
    if (!client?.isRunning()) {
      return undefined;
    }
    log(`Progress request failed: ${String(e)}`);
    throw e;
  }
}

// Automatically hides it when we are done.
async function showProgressBar() {
  let startTime = Date.now();

  try {
    let response: any = await getProgress();
    if (!response) {
      return;
    }

    while (response.done === response.total) {
      // Maybe progress just hasn't started yet.
      // Let's wait a bit and try again.
      await new Promise((resolve) => setTimeout(resolve, 100));
      response = await getProgress();
      if (!response) {
        return;
      }

      let elapsed = Date.now() - startTime;
      if (elapsed > 2000) {
        // It's been a while. Let's give up.
        log("No verification progress appeared before the notification timeout");
        return;
      }
    }

    let previousPercent = 0;
    await window.withProgress(
      {
        location: ProgressLocation.Notification,
        title: "Venticorn Validation",
        cancellable: true,
      },
      async (progress, token) => {
        token.onCancellationRequested(() => {
          log("Validation progress notification canceled");
        });

        while (response.total !== response.done) {
          let percent = Math.floor((100 * response.done) / response.total);
          let increment = percent - previousPercent;
          progress.report({ increment });
          previousPercent = percent;

          // We have something to show, so we can wait a bit before updating.
          await new Promise((resolve) => setTimeout(resolve, 100));
          response = await getProgress();
          if (!response) {
            return;
          }
        }
      }
    );
  } catch (e) {
    log(`Progress notification failed: ${String(e)}`);
  }
}

export async function activate(context: ExtensionContext) {
  outputChannel = window.createOutputChannel("Venticorn Extension");
  context.subscriptions.push(outputChannel);
  log(`Activating Venticorn ${context.extension.packageJSON.version} on ${os.platform()}-${os.arch()}`);

  let command: string;
  try {
    command = await getServerPath(context, async (_asset, download) => {
      await window.withProgress({
        location: ProgressLocation.Notification,
        title: "Downloading Venticorn language server",
        cancellable: false,
      }, async (progress) => {
        let previousPercent = 0;
        await download((received, total) => {
          const message = `${(received / (1024 * 1024)).toFixed(1)} MiB received`;
          if (total !== undefined && Number.isFinite(total) && total > 0) {
            const percent = Math.min(100, Math.max(previousPercent, Math.floor(100 * received / total)));
            progress.report({ message, increment: percent - previousPercent });
            previousPercent = percent;
          } else {
            // Chunked responses have no total, so show bytes without inventing a percentage.
            progress.report({ message });
          }
        });
      });
    }, log);
  } catch (error) {
    log(`Language server resolution failed: ${(error as Error).message}`);
    window.showErrorMessage("Venticorn: " + (error as Error).message);
    return;
  }

  const args: string[] = ["--extension-root", context.extensionPath];
  const workspaceRoot = workspace.workspaceFolders?.[0]?.uri;
  if (workspaceRoot?.scheme === "file") {
    args.push("--workspace-root", workspaceRoot.fsPath);
  }
  let exec: Executable = {
    command,
    args,
    options: {
      env: {
        RUST_BACKTRACE: "1",
        ...process.env,
      },
    },
  };

  // If the extension is launched in debug mode then the debug server options are used
  // Otherwise the run options are used
  let serverOptions: ServerOptions = {
    run: exec,
    debug: exec,
  };

  let clientOptions: LanguageClientOptions = {
    // Register the server for plain text documents
    documentSelector: [{ scheme: "file", language: "acorn" }],
    synchronize: {
      // Notify the server about file changes to '.clientrc files contained in the workspace
      fileEvents: workspace.createFileSystemWatcher("**/.clientrc"),
    },
    initializationFailedHandler: (error) => {
      if (!client.initializationFailed) {
        client.initializationFailed = true;
        window.showErrorMessage("Venticorn: " + error.message);
      }
      // Let the user fix the configuration before explicitly trying again.
      return false;
    },
    errorHandler: {
      error: (error) => {
        log(`Language server error: ${error.message}`);
        return { action: ErrorAction.Shutdown, handled: client.initializationFailed };
      },
      closed: () => {
        log("Language server process closed");
        return { action: CloseAction.DoNotRestart, handled: client.initializationFailed };
      },
    },
  };

  // Create the language client and start the client.
  client = new VenticornLanguageClient(
    "acornLanguageServer",
    "Venticorn Language Server",
    serverOptions,
    clientOptions
  );

  // Start the client. This will also launch the server
  try {
    await client.start();
  } catch (error) {
    log(`Language client failed to start: ${String(error)}`);
    return;
  }

  let infoViewPath = context.asAbsolutePath("build/info");
  context.subscriptions.push(new InfoView(client, infoViewPath));

  let onDocumentChange = async (document: TextDocument) => {
    if (document.languageId !== "acorn") {
      return;
    }
    await showProgressBar();
  };

  let hasAcornDocs = false;
  for (let doc of workspace.textDocuments) {
    if (doc.languageId === "acorn") {
      hasAcornDocs = true;
      break;
    }
  }

  if (hasAcornDocs) {
    showProgressBar();
  }

  context.subscriptions.push(workspace.onDidSaveTextDocument(onDocumentChange));
  context.subscriptions.push(workspace.onDidOpenTextDocument(onDocumentChange));
}

export function deactivate(): Thenable<void> | undefined {
  if (!client || !client.isRunning()) {
    return undefined;
  }
  return client.stop();
}
