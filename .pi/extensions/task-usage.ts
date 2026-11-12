/**
 * Append one metadata-only record per settled user-initiated run.
 * See .pi/README.md for timing, accounting, and privacy limitations.
 */
import { appendFileSync, mkdirSync } from "node:fs";
import { join } from "node:path";
import { performance } from "node:perf_hooks";
import type { Usage } from "@earendil-works/pi-ai";
import type { ExtensionAPI, ExtensionContext } from "@earendil-works/pi-coding-agent";
import { TaskTiming } from "../lib/task-timing.ts";

interface Task {
  startedAt: string;
  startedClock: number;
  sessionId: string;
  existingEntries: Set<string>;
  active: boolean;
  timing: TaskTiming;
}

const SETTINGS_ENTRY = "task-usage-settings";

export default function (pi: ExtensionAPI) {
  let task: Task | undefined;
  let enabled = true;

  pi.on("session_start", (_event, ctx) => {
    task = undefined;
    enabled = true;
    const sessionId = ctx.sessionManager.getSessionId();
    // This preference is session-wide, not branch-sensitive. Ignore settings
    // copied from another session by /fork or /clone: new sessions default on.
    for (const entry of ctx.sessionManager.getEntries()) {
      if (entry.type !== "custom" || entry.customType !== SETTINGS_ENTRY) continue;
      const data = entry.data as { session_id?: unknown; enabled?: unknown } | undefined;
      if (data?.session_id === sessionId && typeof data.enabled === "boolean") {
        enabled = data.enabled;
      }
    }
  });

  pi.registerCommand("usage-log", {
    description: "Session usage logging: on, off, or status (default)",
    handler: async (args, ctx) => {
      const action = args.trim().toLowerCase() || "status";
      if (action !== "on" && action !== "off" && action !== "status") {
        const message = "Usage: /usage-log on | off | status";
        if (ctx.hasUI) ctx.ui.notify(message, "warning");
        else console.log(message);
        return;
      }
      if (action !== "status" && enabled !== (action === "on")) {
        enabled = action === "on";
        // Never emit a partial batch if logging is toggled during a run.
        task = undefined;
        pi.appendEntry(SETTINGS_ENTRY, {
          session_id: ctx.sessionManager.getSessionId(), enabled,
        });
      }
      const message = `Usage logging is ${enabled ? "ON" : "OFF"} for this session.`;
      if (ctx.hasUI) ctx.ui.notify(message, "info");
      else console.log(message);
    },
  });

  function start(ctx: ExtensionContext): Task {
    return {
      startedAt: new Date().toISOString(),
      startedClock: performance.now(),
      sessionId: ctx.sessionManager.getSessionId(),
      existingEntries: new Set(ctx.sessionManager.getEntries().map((entry) => entry.id)),
      active: false,
      timing: new TaskTiming(),
    };
  }

  pi.on("input", (_event, ctx) => {
    // Never reset accounting for steering or queued follow-ups. An idle input
    // replaces any candidate consumed by another extension without starting a run.
    if (enabled && ctx.isIdle()) task = start(ctx);
  });

  pi.on("before_agent_start", (event, ctx) => {
    if (!enabled || event.messageType !== "user") return;
    task ??= start(ctx);
    task.active = true;
  });

  pi.on("message_end", (event) => {
    if (task?.active && event.message.role === "assistant") {
      task.timing.modelResponse(event.message.durationMs, performance.now());
    }
  });

  pi.on("tool_execution_start", (event) => {
    if (task?.active && !event.parentToolCallId) {
      task.timing.toolStart(event.toolCallId, performance.now());
    }
  });

  pi.on("tool_execution_end", (event) => {
    if (task?.active && !event.parentToolCallId) {
      task.timing.toolEnd(event.toolCallId, performance.now());
    }
  });

  pi.on("agent_settled", (event, ctx) => {
    const finished = task;
    task = undefined;
    if (!enabled || !finished?.active) return;

    const completedAt = new Date().toISOString();
    const durationMs = Math.round(performance.now() - finished.startedClock);
    const tokens = { input: 0, output: 0, cache_read: 0, cache_write: 0, total: 0 };
    const estimatedCost: Record<keyof typeof tokens, number | null> = {
      input: 0, output: 0, cache_read: 0, cache_write: 0, total: 0,
    };
    let usageRecords = 0;
    let assistantResponses = 0;
    let toolResults = 0;
    let userMessages = 0;
    let lastStopReason: string | undefined;
    const models = new Set<string>();

    function addUsage(usage: Usage | undefined) {
      if (!usage) return;
      usageRecords++;
      tokens.input += usage.input;
      tokens.output += usage.output;
      tokens.cache_read += usage.cacheRead;
      tokens.cache_write += usage.cacheWrite;
      tokens.total += usage.totalTokens;

      // Pi may use an all-zero cost object when model pricing is unknown.
      // Conservatively distinguish that from a genuine zero for an unused
      // category. A positive report lets us retain zero-priced categories too.
      const hasPricing = Object.values(usage.cost ?? {}).some(
        (value) => Number.isFinite(value) && value > 0,
      );
      for (const [target, source] of [
        ["input", "input"], ["output", "output"],
        ["cache_read", "cacheRead"], ["cache_write", "cacheWrite"],
      ] as const) {
        const value = usage.cost?.[source];
        const unused = usage[source] === 0;
        if (unused && value == null) continue;
        if (typeof value !== "number" || !Number.isFinite(value) || value < 0 ||
            (value === 0 && !unused && !hasPricing)) {
          estimatedCost[target] = null;
        } else if (estimatedCost[target] !== null) {
          estimatedCost[target] += value;
        }
      }
    }

    // Use all new session entries, not just the current branch/context: retries
    // and compaction can remove responses from context without undoing their cost.
    // These are in-memory session metadata; the log itself is never read.
    for (const entry of ctx.sessionManager.getEntries()) {
      if (finished.existingEntries.has(entry.id)) continue;
      if (entry.type === "message") {
        const message = entry.message;
        if (message.role === "user") userMessages++;
        if (message.role === "assistant") {
          assistantResponses++;
          lastStopReason = message.stopReason;
          models.add(`${message.provider}/${message.model}`);
          addUsage(message.usage);
        } else if (message.role === "toolResult") {
          // Top-level tool results already aggregate nested tool usage.
          toolResults++;
          addUsage(message.usage);
        }
      } else if (entry.type === "compaction" || entry.type === "branch_summary") {
        addUsage(entry.usage);
      } else if (entry.type === "usage") {
        addUsage(entry.usage);
        models.add(`${entry.provider}/${entry.model}`);
      }
    }

    const categories = ["input", "output", "cache_read", "cache_write"] as const;
    estimatedCost.total = categories.reduce<number | null>((sum, key) => {
      const value = estimatedCost[key];
      return sum === null || value === null ? null : sum + value;
    }, 0);

    const record = {
      schema_version: 1,
      session_id: finished.sessionId,
      started_at: finished.startedAt,
      completed_at: completedAt,
      duration_ms: durationMs,
      timing: finished.timing.summarize(
        finished.startedClock, durationMs, assistantResponses, toolResults,
      ),
      outcome: event.aborted || lastStopReason === "aborted"
        ? "aborted"
        : lastStopReason === "error" ? "error" : "completed",
      last_stop_reason: lastStopReason ?? null,
      user_messages: userMessages,
      assistant_responses: assistantResponses,
      usage_records: usageRecords,
      models: [...models].sort(),
      tokens,
      estimated_cost_usd: estimatedCost,
    };
    const directory = join(ctx.cwd, ".pi", "logs");
    mkdirSync(directory, { recursive: true });
    // One append per record; never rewrite existing records. Let Pi report I/O
    // errors through its extension-error handling rather than silently losing data.
    appendFileSync(join(directory, "task-usage.jsonl"), `${JSON.stringify(record)}\n`, "utf8");
  });

  pi.on("session_shutdown", () => {
    // Reloads/switches must not carry a timing baseline into another session.
    task = undefined;
  });
}
