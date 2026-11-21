# Lean diagnostic latency

A persistent language server reuses imports and unchanged source prefixes, but
this does not make every edit a sub-second check. Diagnostic latency includes
proof elaboration **and** server reporting/reference-metadata work.

## Controlled measurements

Measured on 2026-10-30 with Lean 4.34.1, lean-lsp-mcp 0.31.0 and leanclient
0.12.0 in the 4-core, 12 GB VM. The same worker checked the 3,136-line
`NoEmbeddedEigenvalues/OddOdd/WeightedVirial/OddOddVirial.lean` throughout. Test edits were restored
byte-for-byte; all complete checks passed. No builds were run.

| Request | Elapsed time |
|---|---:|
| Initial open and full diagnostics | 42 s |
| Unchanged-file diagnostics | 0.03–0.26 s |
| Tiny proof edit/restoration near the end | 9.8–10.4 s |
| Tiny proof edit/restoration near the beginning | 20.4–22.1 s |
| Add, edit or remove a trivial example at the end | 5.1–5.2 s |

CPU counters showed about 10 CPU-seconds for a late edit and 66 CPU-seconds
for an early edit; multiple threads account for CPU time exceeding elapsed
time. These checks had no recorded physical disk reads or major page faults.
The warm-edit bottleneck was CPU work in the Lean worker, not repeated cold
import loading. This does not characterize cold-load I/O costs.

For the final theorem, `trace.profiler` reported 3.51 s of asynchronous proof
elaboration within a roughly 10 s diagnostic call. The much shorter
`Elab.command` trace only measures scheduling that asynchronous work.

## Small-module experiment

Keeping the same imports, path and worker, temporarily reduced the file to its
first self-contained block: weak-operator definitions, jet identification and
L² jet stability (388 lines). Applied exactly the same parenthesization edit
near line 94 in both versions, then restored the full source byte-for-byte.
All complete checks passed.

| Version | Warm edit/restoration time |
|---|---:|
| Full file (3,136 lines; two checks) | 20.59–21.36 s |
| Small module (388 lines; six checks) | 1.50–1.56 s |

The median fell from 20.97 s to 1.55 s, about **13.5× faster**. This supports
focused modules as a repository-side improvement without modifying Lean or
the MCP server. It measures local development checks, not total project
validation: downstream modules still need checking at integration checkpoints.
The initial small-module check reused existing snapshots, so this experiment
also does not measure a new module's cold-open cost. A permanent split needs
review of dependencies and private helper visibility.

## Build concurrency

A broad rebuild after an `OrbitCoordinates.lean` change exhausted the 12 GB
VM's memory while spawning Lean processes, even with the language server
stopped. Retrying the remaining build with `LEAN_NUM_THREADS=2` succeeded.
The subsequent cached build and admission audit passed with default concurrency.
This was not a timing comparison: the retry reused work from the first build.

On that VM, start broad rebuilds with `LEAN_NUM_THREADS=2 just build` and
try `1` if memory is still tight. Leave routine checks alone. If weighing more
RAM against lower concurrency, compare elapsed time and peak memory on the same
representative rebuild with equivalent starting artifacts; a cached build
won't answer that question.

## Synchronization and reporting

Source inspection of these versions establishes:

- `reload_from_disk` sends changes only when text differs; `fresh=True`
  waits for a versioned diagnostic barrier, without reopening the file.
- Full-text changes retain Lean's unchanged-prefix snapshot reuse. A syntactic
  change generally invalidates downstream command processing.
- Diagnostic line ranges filter output **after** the barrier; they do not
  bound the elaboration/reporting wait.
- Lean's `handleWaitForDiagnostics` waits for both command snapshots and the
  reporter. Before finishing, `reportSnapshots` collects reference metadata
  from the whole file's info trees; changed trees can also be collected for
  incremental updates.

Reference collection/reporting is therefore a strong candidate for avoidable
latency, especially the five-second trivial-edit baseline. Its individual
cost has not yet been isolated. Separately timing command completion, reference
extraction and reporter completion could distinguish these costs. The small-module
experiment already demonstrates a practical improvement without server changes.

A one-second timeout during the trivial-example test returned a partial result
with no pending elaboration ranges, followed by another four seconds of waiting
for full completion. Neither empty ranges nor partial diagnostics replace a
complete, version-matched check.
