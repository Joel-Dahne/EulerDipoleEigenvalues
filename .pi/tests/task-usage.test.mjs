// Run with Node >= 24: node --test .pi/tests/task-usage.test.mjs
import assert from "node:assert/strict";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { performance } from "node:perf_hooks";
import { test } from "node:test";
import taskUsage from "../extensions/task-usage.ts";

const usage = (input, output, cacheRead = 0, cacheWrite = 0) => ({
  input, output, cacheRead, cacheWrite,
  totalTokens: input + output + cacheRead + cacheWrite,
  cost: { input: 0, output: 0, cacheRead: 0, cacheWrite: 0, total: 0 },
});

function harness(t) {
  const cwd = mkdtempSync(join(tmpdir(), "pi-task-usage-"));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  const handlers = new Map();
  const commands = new Map();
  const notifications = [];
  const entries = [];
  let idle = true;
  let sessionId = "test-session";
  const ctx = {
    cwd,
    hasUI: true,
    ui: { notify: (message, level) => notifications.push({ message, level }) },
    isIdle: () => idle,
    sessionManager: { getSessionId: () => sessionId, getEntries: () => entries },
  };
  const emit = (name, event = {}) => handlers.get(name)?.(event, ctx);
  const add = (entry) => entries.push({ id: String(entries.length), ...entry });
  const assistant = (u, stopReason = "stop", durationMs = 0) => {
    const message = {
      role: "assistant", provider: "test", model: "model", usage: u, stopReason, durationMs,
    };
    emit("message_end", { message });
    add({ type: "message", message });
  };
  const begin = () => {
    emit("input", { source: "interactive", text: "PRIVATE PROMPT" });
    idle = false;
    emit("before_agent_start", { messageType: "user" });
    add({ type: "message", message: { role: "user", content: "PRIVATE PROMPT" } });
  };
  const settle = (aborted = false) => {
    idle = true;
    emit("agent_settled", { aborted });
  };
  const log = join(cwd, ".pi", "logs", "task-usage.jsonl");
  const records = () => readFileSync(log, "utf8").trim().split("\n").map(JSON.parse);
  const reload = () => {
    handlers.clear();
    commands.clear();
    taskUsage({
      on: (name, handler) => handlers.set(name, handler),
      registerCommand: (name, command) => commands.set(name, command),
      appendEntry: (customType, data) => add({ type: "custom", customType, data }),
    });
    emit("session_start");
  };
  const command = (args = "") => commands.get("usage-log").handler(args, ctx);
  const switchSession = (id, history = []) => {
    emit("session_shutdown");
    sessionId = id;
    entries.splice(0, entries.length, ...history);
    idle = true;
    reload();
  };
  reload();
  return {
    emit, add, assistant, begin, settle, log, records, ctx,
    command, reload, switchSession, notifications, entries,
  };
}

test("one record includes retries, tools and compaction, not historical usage", (t) => {
  const h = harness(t);
  h.assistant(usage(999, 999));
  h.begin();
  h.assistant(usage(10, 2, 30, 4), "error");
  h.emit("agent_end");
  assert.equal(existsSync(h.log), false);
  h.add({ type: "compaction", usage: usage(5, 1) });
  h.assistant(usage(7, 3, 20));
  h.add({ type: "message", message: { role: "toolResult", usage: usage(2, 1) } });
  h.add({ type: "usage", provider: "test", model: "other", usage: usage(1, 1) });
  h.settle();
  const [r] = h.records();
  assert.deepEqual(r.tokens, { input: 25, output: 8, cache_read: 50, cache_write: 4, total: 87 });
  assert.equal(r.usage_records, 5);
  assert.equal(r.assistant_responses, 2);
  assert.equal(r.outcome, "completed");
  assert.equal(r.session_id, "test-session");
  assert.deepEqual(r.models, ["test/model", "test/other"]);
  assert.ok(r.duration_ms >= 0);
  assert.ok(Date.parse(r.completed_at) >= Date.parse(r.started_at));
  assert.ok(!readFileSync(h.log, "utf8").includes("PRIVATE PROMPT"));
  h.settle();
  assert.equal(h.records().length, 1); // A repeated settlement cannot double-count.
});

test("queued messages stay in one batch, next idle prompt gets a fresh baseline", (t) => {
  const h = harness(t);
  h.begin();
  h.assistant(usage(10, 2));
  h.emit("input", { source: "interactive", streamingBehavior: "followUp" });
  h.add({ type: "message", message: { role: "user" } });
  h.assistant(usage(3, 4));
  h.settle();
  assert.equal(h.records()[0].user_messages, 2);
  assert.equal(h.records()[0].tokens.total, 19);
  h.begin();
  h.assistant(usage(1, 1));
  h.settle();
  assert.equal(h.records().length, 2);
  assert.equal(h.records()[1].tokens.total, 2);
});

test("aborts and final provider errors are distinguished from completion", (t) => {
  const h = harness(t);
  h.begin();
  h.assistant(usage(3, 2), "aborted");
  h.settle(true);
  h.begin();
  h.assistant(usage(1, 0), "error");
  h.settle();
  assert.deepEqual(h.records().map((r) => r.outcome), ["aborted", "error"]);
});

test("custom runs and shutdown do not produce spurious records", (t) => {
  const h = harness(t);
  h.emit("before_agent_start", { messageType: "custom" });
  h.settle();
  assert.equal(existsSync(h.log), false);
  h.begin();
  h.emit("session_shutdown");
  h.settle();
  assert.equal(existsSync(h.log), false);
});

test("costs sum across responses, tools, summaries and usage entries, excluding history", (t) => {
  const h = harness(t);
  const priced = {
    ...usage(10, 2, 30, 4),
    cost: { input: 1, output: 2, cacheRead: 3, cacheWrite: 4, total: 10 },
  };
  h.assistant(priced); // Historical charges must not enter this batch.
  h.begin();
  h.assistant(priced, "error");
  h.assistant(priced);
  h.add({ type: "message", message: { role: "toolResult", usage: priced } });
  h.add({ type: "compaction", usage: priced });
  h.add({ type: "branch_summary", usage: priced });
  h.add({ type: "usage", provider: "test", model: "model", usage: priced });
  h.settle();
  const [r] = h.records();
  assert.equal(r.schema_version, 1);
  assert.deepEqual(r.estimated_cost_usd, {
    input: 6, output: 12, cache_read: 18, cache_write: 24, total: 60,
  });
});

test("all-zero pricing with nonzero tokens is unavailable, not free", (t) => {
  const h = harness(t);
  h.begin();
  h.assistant(usage(10, 2, 30));
  h.settle();
  assert.deepEqual(h.records()[0].estimated_cost_usd, {
    input: null, output: null, cache_read: null, cache_write: 0, total: null,
  });
  assert.equal(h.records()[0].tokens.total, 42);
});

test("an otherwise priced report can include genuinely zero-priced categories", (t) => {
  const h = harness(t);
  h.begin();
  h.assistant({ ...usage(1, 1, 1, 1),
    cost: { input: 1, output: 2, cacheRead: 0, cacheWrite: 0, total: 3 } });
  h.settle();
  assert.deepEqual(h.records()[0].estimated_cost_usd, {
    input: 1, output: 2, cache_read: 0, cache_write: 0, total: 3,
  });
});

test("missing cost contaminates the affected aggregate, not unrelated categories", (t) => {
  const h = harness(t);
  h.begin();
  h.assistant({ ...usage(5, 0), cost: undefined });
  h.assistant({ ...usage(5, 2),
    cost: { input: 1, output: 2, cacheRead: 0, cacheWrite: 0, total: 3 } });
  h.settle();
  assert.deepEqual(h.records()[0].estimated_cost_usd, {
    input: null, output: 2, cache_read: 0, cache_write: 0, total: null,
  });
});

test("invalid estimates become unavailable without breaking token logging", (t) => {
  const h = harness(t);
  h.begin();
  h.assistant({ ...usage(1, 1, 1, 1),
    cost: { input: NaN, output: Infinity, cacheRead: -1, cacheWrite: undefined, total: 0 } });
  h.settle();
  assert.deepEqual(h.records()[0].estimated_cost_usd, {
    input: null, output: null, cache_read: null, cache_write: null, total: null,
  });
  assert.equal(h.records()[0].tokens.total, 4);
});

test("event timing splits a batch without double-counting parallel or nested tools", (t) => {
  let clock = 1000;
  t.mock.method(performance, "now", () => clock);
  const h = harness(t);
  h.begin();
  clock = 1080;
  h.assistant(usage(1, 1), "toolUse", 60);
  clock = 1090;
  h.emit("tool_execution_start", { toolCallId: "a" });
  clock = 1100;
  h.emit("tool_execution_start", { toolCallId: "b" });
  clock = 1110;
  h.emit("tool_execution_start", { toolCallId: "a/1", parentToolCallId: "a" });
  clock = 1150;
  h.emit("tool_execution_end", { toolCallId: "a/1", parentToolCallId: "a" });
  clock = 1190;
  h.emit("tool_execution_end", { toolCallId: "a" });
  clock = 1220;
  h.emit("tool_execution_end", { toolCallId: "b" });
  h.add({ type: "message", message: { role: "toolResult" } });
  h.add({ type: "message", message: { role: "toolResult" } });
  clock = 1280;
  h.assistant(usage(1, 1), "stop", 50);
  clock = 1300;
  h.settle();
  const [r] = h.records();
  assert.equal(r.duration_ms, 300);
  assert.deepEqual(r.timing, {
    model_request_ms: 110, tool_wall_ms: 130, overlap_ms: 0, other_ms: 60,
    model_responses_missing_timing: 0, tool_calls_missing_timing: 0,
  });
  h.begin(); // The next task must not retain the old task's timing intervals.
  clock = 1400;
  h.assistant(usage(1, 1), "stop", 20);
  h.settle();
  assert.equal(h.records()[1].timing.model_request_ms, 20);
  assert.equal(h.records()[1].timing.tool_wall_ms, 0);
});

test("missing response durations and tool events are flagged in the log", (t) => {
  const h = harness(t);
  h.begin();
  h.assistant(usage(1, 1), "stop", null);
  h.add({ type: "message", message: { role: "toolResult" } });
  h.settle();
  assert.deepEqual(h.records()[0].timing, {
    model_request_ms: null, tool_wall_ms: null, overlap_ms: null, other_ms: null,
    model_responses_missing_timing: 1, tool_calls_missing_timing: 1,
  });
});

test("off skips batches, on restores logging without backfilling or modifying old records", async (t) => {
  const h = harness(t);
  h.begin();
  h.assistant(usage(1, 1));
  h.settle();
  const original = readFileSync(h.log, "utf8");
  await h.command("off");
  h.begin();
  h.assistant(usage(99, 99));
  h.settle();
  assert.equal(readFileSync(h.log, "utf8"), original);
  await h.command("on");
  h.begin();
  h.assistant(usage(2, 3));
  h.settle();
  assert.equal(h.records().length, 2);
  assert.equal(h.records()[1].tokens.total, 5);
  assert.equal(h.entries.filter((e) => e.type === "custom").length, 2);
});

test("off persists across extension reload and resuming the same session", async (t) => {
  const h = harness(t);
  await h.command("off");
  const saved = [...h.entries];
  h.reload();
  await h.command("status");
  assert.match(h.notifications.at(-1).message, /OFF/);
  h.begin();
  h.assistant(usage(1, 1));
  h.settle();
  assert.equal(existsSync(h.log), false);
  h.switchSession("other");
  await h.command("status");
  assert.match(h.notifications.at(-1).message, /ON/);
  h.switchSession("test-session", saved);
  await h.command("status");
  assert.match(h.notifications.at(-1).message, /OFF/);
  await h.command("on");
  h.reload();
  await h.command("status");
  assert.match(h.notifications.at(-1).message, /ON/);
});

test("new and forked sessions default to on even with inherited settings", async (t) => {
  const h = harness(t);
  await h.command("off");
  const inherited = [...h.entries];
  h.switchSession("forked-session", inherited);
  await h.command();
  assert.match(h.notifications.at(-1).message, /ON/);
  h.begin();
  h.assistant(usage(1, 1));
  h.settle();
  assert.equal(h.records()[0].session_id, "forked-session");
});

test("status, no-op commands and invalid arguments do not save settings or log", async (t) => {
  const h = harness(t);
  await h.command();
  await h.command("status");
  await h.command("on");
  await h.command("invalid");
  assert.equal(h.notifications.at(-1).level, "warning");
  assert.equal(h.entries.length, 0);
  assert.equal(existsSync(h.log), false);
  await h.command("  OFF  ");
  await h.command("off");
  assert.equal(h.entries.length, 1);
  assert.match(h.notifications.at(-1).message, /OFF/);
});

test("toggling during a run discards that batch, rather than logging a partial task", async (t) => {
  const h = harness(t);
  h.begin();
  h.assistant(usage(10, 10));
  await h.command("off");
  await h.command("on");
  h.assistant(usage(20, 20));
  h.settle();
  assert.equal(existsSync(h.log), false);
  h.begin();
  h.assistant(usage(1, 1));
  h.settle();
  assert.equal(h.records().length, 1);
  assert.equal(h.records()[0].tokens.total, 2);
});

test("non-UI commands print their result without requiring a model or UI", async (t) => {
  const h = harness(t);
  h.ctx.hasUI = false;
  const messages = [];
  t.mock.method(console, "log", (message) => messages.push(message));
  await h.command("off");
  await h.command("status");
  await h.command("invalid");
  assert.match(messages[0], /OFF/);
  assert.match(messages[1], /OFF/);
  assert.match(messages[2], /Usage:/);
  assert.equal(h.notifications.length, 0);
});

test("fallback without input works and existing log is only appended to", (t) => {
  const h = harness(t);
  h.emit("before_agent_start", { messageType: "user" });
  h.assistant(usage(1, 2));
  h.settle();
  writeFileSync(h.log, "an opaque pre-existing line\n");
  h.begin();
  h.assistant(usage(3, 4));
  h.settle();
  const lines = readFileSync(h.log, "utf8").trim().split("\n");
  assert.equal(lines[0], "an opaque pre-existing line");
  assert.equal(JSON.parse(lines[1]).tokens.total, 7);
});
