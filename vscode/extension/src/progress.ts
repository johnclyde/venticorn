// Modified for Venticorn: one disposable polling loop owns verification progress.
import { Disposable, ProgressLocation, Range, TextDocument, TextEditor, Uri, window, workspace } from "vscode";
import { Buffer } from "buffer";

type ProgressClient = {
  isRunning(): boolean;
  sendRequest(method: string, params: object): Promise<unknown>;
};
type Clock = { now(): number; pause(milliseconds: number): Promise<void> };
const defaultClock: Clock = {
  now: () => Date.now(),
  pause: (milliseconds) => new Promise((resolve) => setTimeout(resolve, milliseconds)),
};

export class ProgressTracker {
  private active: Promise<void> | undefined;
  private startTime = 0;
  private disposed = false;
  private buildId: number | null = null;
  private invalidatedBuildId: number | null = null;
  private docs: { [uri: string]: DocumentProgress } = {};
  private epoch = 0;
  private request = 0;
  private wake = 0;
  private observedWake = 0;
  private subscriptions: Disposable[] = [];
  private decoration = window.createTextEditorDecorationType({
    gutterIconSize: "contain",
    light: { gutterIconPath: this.checkIcon("#6e6e6e") },
    dark: { gutterIconPath: this.checkIcon("#858585") },
  });

  constructor(private client: ProgressClient, private log: (message: string) => void, private clock: Clock = defaultClock) {
    this.subscriptions.push(
      window.onDidChangeVisibleTextEditors(editors => {
        for (const editor of editors) this.updateDecorations(editor);
      }),
      workspace.onDidChangeTextDocument(event => {
        if (this.isTracked(event.document) && event.contentChanges.length > 0) this.invalidate();
      }),
      workspace.onDidCloseTextDocument(document => { if (this.isTracked(document)) this.invalidate(); }),
      workspace.onDidOpenTextDocument(document => { if (this.isTracked(document)) this.invalidate(); }),
    );
  }

  private isTracked(document: TextDocument): boolean {
    return document?.languageId === "acorn" && document.uri?.scheme === "file";
  }

  private checkIcon(color: string): Uri {
    const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16"><path d="M3,7 L6,11 L13,4" fill="none" stroke="${color}" stroke-width="1"/></svg>`;
    return Uri.parse("data:image/svg+xml;base64," + Buffer.from(svg).toString("base64"));
  }

  private invalidate() {
    this.epoch++;
    this.invalidatedBuildId = this.buildId;
    this.docs = {};
    this.refresh();
  }

  private refresh() {
    for (const editor of window.visibleTextEditors) this.updateDecorations(editor);
  }

  updateDecorations(editor: TextEditor) {
    const document = editor.document;
    const progress = this.docs[document.uri.toString()];
    const lines = this.isTracked(document) && !document.isDirty
      && progress?.version === document.version ? progress.verified : [];
    editor.setDecorations(this.decoration, lines.filter(([first, last]) => Number.isInteger(first) && Number.isInteger(last)
      && first >= 0 && first <= last && last < document.lineCount)
      .map(([first]) => ({ range: new Range(first, 0, first, 0) })));
  }

  dispose() {
    this.disposed = true;
    this.invalidate();
    this.decoration.dispose();
    for (const subscription of this.subscriptions) subscription.dispose();
  }

  async getProgress(): Promise<ProgressResponse | undefined> {
    const request = ++this.request;
    while (!this.disposed && this.client.isRunning()) {
      const epoch = this.epoch;
      const wake = this.wake;
      const response = await this.client.sendRequest("acorn/progress", {}) as ProgressResponse;
      if (this.disposed || !this.client.isRunning() || request !== this.request) return undefined;
      // An editor transition can happen while the server response is in flight.
      // Retry after that transition rather than apply a response to a new document lifetime.
      if (epoch !== this.epoch) continue;
      this.observedWake = wake;
      if (!response) return undefined;
      this.buildId = response.buildId;
      this.docs = response.buildId !== null && response.buildId !== this.invalidatedBuildId ? response.docs : {};
      this.refresh();
      return response;
    }
    return undefined;
  }

  track(): Promise<void> {
    this.startTime = this.clock.now();
    this.wake++;
    if (this.active) return this.active;
    if (this.disposed) return Promise.resolve();
    this.active = this.run().catch((error) => {
      this.log(`Verification progress failed: ${String(error)}`);
    }).finally(() => { this.active = undefined; });
    return this.active;
  }

  private async run() {
    do {
      await this.trackHelper();
      // A save may arrive during the final request for a completed older build.
      // Do not lose that trigger when the shared polling promise finishes.
    } while (!this.disposed && this.client.isRunning() && this.observedWake < this.wake);
  }

  private async trackHelper() {
    const initialBuildId = this.buildId;
    let response = await this.getProgress();
    while (response && (response.buildId === null || (response.buildId === initialBuildId && response.done >= response.total))) {
      if (this.clock.now() - this.startTime >= 2000) return;
      await this.clock.pause(100);
      response = await this.getProgress();
    }
    if (!response || response.done >= response.total) return;
    await window.withProgress({
      location: ProgressLocation.Notification,
      title: "Venticorn Verification",
      cancellable: false,
    }, async (progress) => {
      let previous = 0;
      while (response && response.done < response.total) {
        const percent = Math.max(previous, Math.min(100, Math.floor(100 * response.done / response.total)));
        progress.report({ increment: percent - previous });
        previous = percent;
        await this.clock.pause(100);
        response = await this.getProgress();
      }
    });
  }
}
