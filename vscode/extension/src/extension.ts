// Modified for Venticorn: editor-facing names and language-server lifecycle.
import {
  ExtensionContext, ProgressLocation, TextDocument, window, workspace,
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
import { SearchPanel } from "./search-panel";

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
    console.error("error in getProgress:", e);
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
        console.log("giving up on progress bar");
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
          console.log("Venticorn validation progress bar canceled");
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
    console.error("error showing progress bar:", e);
  }
}

export async function activate(context: ExtensionContext) {
  let timestamp = new Date().toLocaleTimeString();
  console.log(
    `activating Venticorn-${os.platform()}-${os.arch()} extension at`,
    timestamp
  );
  let traceOutputChannel = window.createOutputChannel("Venticorn Language Server");
  context.subscriptions.push(traceOutputChannel);

  let command: string;
  try {
    command = await getServerPath(context);
  } catch (error) {
    console.error("language server resolution failed:", error);
    window.showErrorMessage("Venticorn: " + (error as Error).message);
    return;
  }

  let exec: Executable = {
    command,
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
    traceOutputChannel,
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
        console.error("language server error:", error);
        return { action: ErrorAction.Shutdown, handled: client.initializationFailed };
      },
      closed: () => {
        console.warn("language server process closed");
        return { action: CloseAction.DoNotRestart, handled: client.initializationFailed };
      },
    },
  };

  // Create the language client and start the client.
  client = new VenticornLanguageClient(
    "acornClient",
    "Venticorn Client",
    serverOptions,
    clientOptions
  );

  // Start the client. This will also launch the server
  try {
    await client.start();
  } catch (error) {
    console.error("client failed to start:", error);
    return;
  }

  let searchPath = context.asAbsolutePath("build/search");
  context.subscriptions.push(new SearchPanel(client, searchPath));

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
