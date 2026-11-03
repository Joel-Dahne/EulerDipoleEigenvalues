---
name: lean-performance
description: Diagnose slow Lean edit/recheck cycles, elaboration timeouts, or expensive imports. Use before performance-driven proof rewrites, carrier changes, instance caches, import changes, or file splitting; measure one intervention at a time.
license: CC-BY-4.0
---

# Targeted Lean performance diagnosis

Follow [project policy](../../../AGENTS.md) and the
[Lean-LSP setup](../../../docs/tooling/pi.md). Optimize the workflow actually
being used, usually edits in an already open file. A clean build and a warm
language-server recheck measure different things.

## Procedure

1. Name the symptom and target: initial file opening, recheck after a specific
   edit, a theorem timeout, or checkpoint build cost. Record the toolchain and
   relevant imports.
2. Establish a baseline with Lean-LSP. Distinguish unchanged diagnostics from
   re-elaboration after an edit. Record which source prefix was invalidated;
   repeatedly requesting unchanged diagnostics is not an edit benchmark.
3. Locate the expensive declaration or phase. Read
   [references/diagnosis.md](references/diagnosis.md) before selecting a
   profiling experiment or optimization.
4. If a fresh-process profile is needed, run one bounded, serial experiment
   after arranging memory headroom. Do not run a heavy profiler/build alongside
   an open broad-Mathlib server.
5. Change one thing. Preserve the mathematical statement and compare equivalent
   baseline and variant runs. Recheck a representative consumer if imports,
   instances, or exported interfaces changed.
6. Keep an edit only when the relevant cost improves repeatably without an
   unacceptable regression elsewhere. Report a null or noisy result honestly.

## Limits

- Do not run a clean rebuild campaign by default. Never delete dependency
  artifacts, run `lake clean`, update pins, or change cache/toolchain settings
  as an optimization shortcut.
- Do not kill another session's Lean process. Coordinate expensive experiments.
- Do not change a carrier, public statement, heartbeat policy, or module system
  merely because an upstream performance recipe recommends it.
- Profile-based instance caching is an experiment, not a universal rule.
- File splitting may improve edit latency while increasing total build cost;
  state which metric motivated it.

Report the exact file/declaration, measurement conditions, before/after result,
checks run, and limitations. Put stable implementation explanations in module
documentation; keep scratch measurements out of the repository unless requested.

Adapted from Scott Armstrong's elaboration guidance; see
[attribution and changes](../ATTRIBUTION.md).
