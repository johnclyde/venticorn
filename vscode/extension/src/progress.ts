// Modified for Venticorn: one disposable polling loop owns verification progress.
import { ProgressLocation, window } from "vscode";

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

  constructor(private client: ProgressClient, private log: (message: string) => void, private clock: Clock = defaultClock) {}

  dispose() { this.disposed = true; }

  async getProgress(): Promise<ProgressResponse | undefined> {
    if (this.disposed || !this.client.isRunning()) return undefined;
    const response = await this.client.sendRequest("acorn/progress", {}) as ProgressResponse;
    if (this.disposed || !this.client.isRunning()) return undefined;
    if (response) this.buildId = response.buildId;
    return response;
  }

  track(): Promise<void> {
    this.startTime = this.clock.now();
    if (this.active) return this.active;
    if (this.disposed) return Promise.resolve();
    this.active = this.trackHelper().catch((error) => {
      this.log(`Verification progress failed: ${String(error)}`);
    }).finally(() => { this.active = undefined; });
    return this.active;
  }

  private async trackHelper() {
    const initialBuildId = this.buildId;
    let response = await this.getProgress();
    while (response && (response.buildId === null || response.buildId === initialBuildId)) {
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
