# Project-local Pi extensions

## Completion usage log

[`extensions/task-usage.ts`](extensions/task-usage.ts) appends one
JSON object per line to **`.pi/logs/task-usage.jsonl`** after a user-initiated
run reaches `agent_settled`. The extension is project-local; start Pi at the
repository root and run `/reload` after installing or changing it. The log
directory is created on the first recorded completion and is ignored by Git.
No additional package or model call is required.

### Session controls

- `/usage-log off`: stop logging for this session; existing records are unchanged.
- `/usage-log on`: resume logging from the next fresh prompt.
- `/usage-log status` (or `/usage-log`): show the current setting.

These are local commands, not model requests. The setting is stored as a Pi
custom session entry, excluded from model context; it survives `/reload` and
resuming the same saved session. New sessions, including forks/clones, default
to on. The preference applies across all branches of a session, so navigating
the session tree does not rewind it. In ephemeral (`--no-session`) sessions it
cannot survive exiting Pi. Turning logging off during a run discards that
batch; turning it back on does not backfill it or start a partial record.

Each record contains:

- `started_at` and `completed_at`: UTC ISO timestamps.
- `duration_ms`: elapsed wall time measured with a monotonic clock, from Pi's
  `input` event until settlement. This includes tool execution, retries,
  automatic compaction and waiting during the run, but not your time composing
  the prompt. If no input event is available, timing starts at
  `before_agent_start` instead.
- `timing`: a wall-clock split into `model_request_ms`, `tool_wall_ms`,
  `overlap_ms`, and `other_ms`; see below for scope and missing-data flags.
- `tokens.input`: uncached input tokens; `tokens.output`: generated tokens
  (including reasoning where Pi includes it); `tokens.cache_read`: reused
  cached input; `tokens.cache_write`: newly cached input; `tokens.total`: sum
  of Pi's reported total-token counts across usage records. These are token
  counts, not monetary charges. Cache writes are **not** output tokens.
- `estimated_cost_usd`: summed Pi-reported USD estimates for `input`, `output`,
  `cache_read`, `cache_write`, and their `total`. These use Pi's model pricing,
  not your bill; subscriptions, discounts and stale pricing can differ. No
  prices are fetched and no model calls are added. A category is `null` if any
  contributing usage record lacks a usable estimate; `total` is `null` if any
  category is unavailable, rather than showing a misleading partial total.
  An all-zero cost report with nonzero tokens is conservatively treated as
  unavailable for the used categories, since Pi does not distinguish missing
  pricing from genuinely free usage. Unused categories remain zero.
- `schema_version`: `1` identifies the current format, including token usage,
  estimated costs and timing.
- `session_id`, observed `models`, `user_messages`, `assistant_responses` and
  `usage_records`, to identify and interpret the batch.
- `outcome` (`completed`, `aborted` or `error`) and `last_stop_reason`.
  Completion means processing stopped, not that the task was verified correct.

A batch includes queued follow-ups and steering received before settlement;
its clock stays anchored to the **first** prompt rather than resetting at each
message. A new prompt after settlement starts a new record. Usage is summed
from new in-memory session entries, including assistant responses,
compaction/branch summaries, tool-reported model usage and explicit usage
entries. Historical session usage is not counted again, even on resume.
Only usage Pi records is available: missing provider/tool reports cannot be
recovered, and an unsupported cache category may be reported as zero. Background
usage outside a batch (such as idle cache warming) is excluded. Token counts
remain available even when cost estimates are unavailable.

### Timing breakdown

- `model_request_ms`: union of main-model response intervals, reconstructed
  from Pi's `AssistantMessage.durationMs` and the local monotonic time of its
  `message_end` event. Includes provider queuing, network latency, reasoning and
  response streaming, not just model computation. Event delivery can introduce
  small measurement errors; this is a diagnostic wall-clock split.
- `tool_wall_ms`: union of top-level tool start/end intervals. Parallel tools
  are counted once; nested calls (e.g. within `codemode`) belong to the outer
  tool interval. Includes tool-side waiting, network calls and any model work
  invoked inside tools; it is not CPU time.
- `overlap_ms`: any overlap between the model and tool unions. Usually zero,
  but kept explicit rather than double-counting simultaneous activity.
- `other_ms`: elapsed time outside both unions: preparation, retry backoff,
  orchestration and compaction not timed as a main-model response. Thus
  `duration_ms = model_request_ms + tool_wall_ms - overlap_ms + other_ms`.

Intervals are clipped to the batch and rounded on a common millisecond
timeline. Missing/invalid response durations or missing tool event pairs set
the affected category to `null`; `overlap_ms` and `other_ms` are then also
`null`, not a misleading residual. The counters `model_responses_missing_timing`
and `tool_calls_missing_timing` flag those gaps. Unfinished tools at settlement
(e.g. after an abort) also flag missing timing. No breakdown is backfilled for
earlier records.

The extension never reads the log or injects it into model context. Records
contain no prompts, responses or tool arguments. The Git-ignored log is not
automatically loaded as project context, but remains accessible to filesystem
tools. Pure extension-triggered runs are not logged. Reloading, switching
sessions or a process crash can discard an unfinished batch; there is no
retroactive reconstruction.

Regression tests (Node 24 or later; not needed to run the extension):

```sh
node --test .pi/tests/*.test.mjs
```
