import assert from "node:assert/strict";
import { test } from "node:test";
import { TaskTiming } from "../lib/task-timing.ts";

test("parallel tool time is an interval union, independent of completion order", () => {
  const t = new TaskTiming();
  t.toolStart("long", 10);
  t.toolStart("short", 20);
  t.toolEnd("short", 40);
  t.toolStart("later", 70);
  t.toolEnd("long", 80);
  t.toolEnd("later", 100);
  assert.deepEqual(t.summarize(0, 120, 0, 3), {
    model_request_ms: 0, tool_wall_ms: 90, overlap_ms: 0, other_ms: 30,
    model_responses_missing_timing: 0, tool_calls_missing_timing: 0,
  });
});

test("overlap is explicit and subtracted when computing remaining wall time", () => {
  const t = new TaskTiming();
  t.modelResponse(60, 70); // [10, 70]
  t.toolStart("tool", 50);
  t.toolEnd("tool", 90);
  assert.deepEqual(t.summarize(0, 100, 1, 1), {
    model_request_ms: 60, tool_wall_ms: 40, overlap_ms: 20, other_ms: 20,
    model_responses_missing_timing: 0, tool_calls_missing_timing: 0,
  });
});

test("missing model timing leaves measured tool time available", () => {
  const t = new TaskTiming();
  t.modelResponse(undefined, 20);
  t.toolStart("tool", 30);
  t.toolEnd("tool", 40);
  assert.deepEqual(t.summarize(0, 100, 1, 1), {
    model_request_ms: null, tool_wall_ms: 10, overlap_ms: null, other_ms: null,
    model_responses_missing_timing: 1, tool_calls_missing_timing: 0,
  });
});

test("unfinished tools on abort are not silently assigned zero duration", () => {
  const t = new TaskTiming();
  t.modelResponse(20, 20);
  t.toolStart("tool", 30);
  assert.deepEqual(t.summarize(0, 100, 1, 0), {
    model_request_ms: 20, tool_wall_ms: null, overlap_ms: null, other_ms: null,
    model_responses_missing_timing: 0, tool_calls_missing_timing: 1,
  });
});

test("unmatched ends and unobserved result entries flag tool timing gaps", () => {
  const t = new TaskTiming();
  t.toolEnd("missing-start", 20);
  assert.equal(t.summarize(0, 100, 0, 1).tool_calls_missing_timing, 1);
  const unseen = new TaskTiming();
  assert.equal(unseen.summarize(0, 100, 0, 1).tool_wall_ms, null);
});

test("invalid model durations are unavailable, but zero is a valid duration", () => {
  const t = new TaskTiming();
  t.modelResponse(NaN, 20);
  t.modelResponse(-1, 30);
  t.modelResponse(Infinity, 40);
  t.modelResponse(0, 50);
  const result = t.summarize(0, 100, 4, 0);
  assert.equal(result.model_responses_missing_timing, 3);
  assert.equal(result.model_request_ms, null);
});

test("clipping and submillisecond rounding preserve the wall-time identity", () => {
  const t = new TaskTiming();
  t.modelResponse(30.7, 110.4); // Starts before origin; clip to the batch.
  t.toolStart("tool", 110.6);
  t.toolEnd("tool", 122.7); // Ends beyond the batch; clip here too.
  const r = t.summarize(100, 20, 1, 1);
  assert.equal(r.model_request_ms, 10);
  assert.equal(r.tool_wall_ms, 9);
  assert.equal(r.other_ms, 1);
  assert.equal(r.model_request_ms + r.tool_wall_ms - r.overlap_ms + r.other_ms, 20);
});
