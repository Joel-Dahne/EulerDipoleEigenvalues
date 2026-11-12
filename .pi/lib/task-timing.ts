/** Wall-clock interval accounting. Timestamps are from performance.now(), not Date.now(). */
type Interval = readonly [number, number];

function unionMs(intervals: readonly Interval[], origin: number, duration: number): number {
  // Round endpoints on one common task-relative timeline. This keeps the
  // reported integer-millisecond partition consistent, including tiny intervals.
  const clip = (time: number) => Math.max(0, Math.min(duration, Math.round(time - origin)));
  const sorted = intervals.map(([start, end]) => [clip(start), clip(end)] as const)
    .filter(([start, end]) => end > start).sort((a, b) => a[0] - b[0]);
  let total = 0;
  let previousEnd = 0;
  for (const [start, end] of sorted) {
    total += Math.max(0, end - Math.max(start, previousEnd));
    previousEnd = Math.max(previousEnd, end);
  }
  return total;
}

export class TaskTiming {
  private modelIntervals: Interval[] = [];
  private toolIntervals: Interval[] = [];
  private runningTools = new Map<string, number>();
  private completedTools = 0;
  private toolEventIssues = 0;

  modelResponse(durationMs: number | undefined, endedAt: number) {
    if (typeof durationMs === "number" && Number.isFinite(durationMs) && durationMs >= 0) {
      // Anchor Pi's monotonic request duration to our receipt of message_end.
      // This avoids comparing provider epoch timestamps with a local monotonic clock.
      this.modelIntervals.push([endedAt - durationMs, endedAt]);
    }
  }

  toolStart(id: string, at: number) {
    if (this.runningTools.has(id)) {
      this.toolEventIssues++;
      return;
    }
    this.runningTools.set(id, at);
  }

  toolEnd(id: string, at: number) {
    const start = this.runningTools.get(id);
    if (start === undefined) {
      this.toolEventIssues++;
      return;
    }
    this.runningTools.delete(id);
    this.toolIntervals.push([start, at]);
    this.completedTools++;
  }

  summarize(origin: number, duration: number, assistantResponses: number, toolResults: number) {
    const missingModel = Math.max(0, assistantResponses - this.modelIntervals.length);
    const missingTool = Math.max(
      0, toolResults - this.completedTools, this.toolEventIssues + this.runningTools.size,
    );
    const model = unionMs(this.modelIntervals, origin, duration);
    const tools = unionMs(this.toolIntervals, origin, duration);
    const busy = unionMs([...this.modelIntervals, ...this.toolIntervals], origin, duration);
    const complete = missingModel === 0 && missingTool === 0;
    return {
      model_request_ms: missingModel === 0 ? model : null,
      tool_wall_ms: missingTool === 0 ? tools : null,
      overlap_ms: complete ? model + tools - busy : null,
      other_ms: complete ? duration - busy : null,
      model_responses_missing_timing: missingModel,
      tool_calls_missing_timing: missingTool,
    };
  }
}
