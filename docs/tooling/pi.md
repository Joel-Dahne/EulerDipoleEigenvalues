# Pi tooling

Project-specific Pi setup and experiments. Keep tool-specific instructions in
`docs/tooling/`, separate from the general guidance in `AGENTS.md` and the
mathematical digest notes in the blueprint.

## Shared Lean MCP server

Pi's parent and proof-worker sessions can share one persistent Lean MCP server
and its warmed Lean client for this project.

From the repository root, run:

```sh
just lean-mcp
```

Keep this running in a separate terminal. Stop it with Ctrl+C when finished;
connected sessions will lose their Lean tools. The recipe runs:

```sh
lean-lsp-mcp --transport streamable-http \
  --host 127.0.0.1 --port 8765 --lean-project-path "$PWD"
```

The endpoint has no authentication. Keep it bound to localhost, not a public
interface. It is shared by sessions in the same machine/network namespace;
`127.0.0.1` on the host and inside a VM need not refer to the same endpoint.

### Pi configuration

The project's `.pi/mcp.json` contains:

```json
{
  "mcpServers": {
    "lean-lsp": {
      "url": "http://127.0.0.1:8765/mcp",
      "timeout": 120
    }
  }
}
```

Trust the project configuration in Pi. After changing the connection, run
`/reload` in existing Pi sessions. New sessions and workers launched from this
repository use the same configuration. Check connectivity with:

```sh
pi mcp list --json
```

The `lean-lsp` entry should report `connected` and the HTTP URL. Do not start
a second server if this port is already occupied: first check whether the
existing server belongs to this project.

Claude Code's separate `.mcp.json` still launches its own stdio server; it is
not changed by this Pi configuration.

### Working with a shared server

- Take turns editing/checking the target file. Sharing Lean state does not
  prevent conflicting edits or checks against an intermediate revision.
- Disconnecting a Pi client does not shut down the shared Lean client. Later
  worker sessions can reuse its warmed state while the server stays running.
- Different open files can still consume substantial memory. Prefer one file
  at a time and do not run a full build alongside a heavyweight Lean session.
- Stopping/restarting the server loses its warmed state.

### Verification performed

With the installed `lean-lsp-mcp` version 0.28.1:

- Two simultaneous HTTP sessions checking one disposable Lean file reused the
  same Lean server and file-worker process IDs.
- After both sessions disconnected, a replacement session reused those same
  processes.
- The initial check took 9.84 seconds; warm checks took 0.01–0.02 seconds.
  This was a small smoke test using `Mathlib.Data.Nat.Basic`, not a benchmark
  of the full project or an `import Mathlib` file.
- Separate clients detected a deliberate proof error and its repair.
- `pi mcp list --json` confirmed that Pi connects through the HTTP configuration.

No production Lean files were changed by these tests.

## Proof-worker workflow

The default is **dispatch, wait, review**, not live supervision. Delegation
should leave the parent free to wait or do independent work, rather than
monitoring each proof attempt.

### Recommended sequence

1. **Prepare once.** Check the shared server and target-file imports before
   dispatch. Settle the theorem interface and any essential mathematical
   outline; leave local lemma discovery and proof iteration to the worker.
2. **Assign one coherent task.** Specify the target declarations, permitted
   file edits, allowed helpers and completion checks. Do not split a proof
   into many tiny assignments by default. Split further when an actual
   blocker or failed attempt shows that it is useful.
3. **Run and wait.** Invoke the runner in the foreground with a suitable
   timeout and wait for its final report. Do not routinely background it,
   poll its transcript, inspect intermediate edits or prepare corrective
   subtasks while it is still working. Do not edit/check the target file or
   change the shared Lean server during the run.
4. **Review after completion.** Inspect the diff and independently check Lean
   diagnostics and axioms. This review is required even when the worker
   reports success; avoiding supervision does not mean skipping validation.
5. **Escalate only on evidence.** If the worker reports a blocker, times out
   or fails validation, inspect the relevant logs and decide whether to
   repair, retry or split the task. Intervene during a run only for a
   concrete infrastructure or safety problem, not merely because it is
   taking time.

Keep mathematical preparation, worker execution and independent review
separate. The aim is less coordination, not a detailed record of every
intermediate attempt.

### Runner

The sequential runner is `scripts/pi_proof_worker.py`. Start the shared server,
then supply a short task file specifying the exact theorem, permitted edits,
and optional proof outline:

```sh
python3 scripts/pi_proof_worker.py /tmp/task.md
# Optional overrides:
python3 scripts/pi_proof_worker.py /tmp/task.md \
  --model openai-codex/gpt-6-luna --thinking medium --timeout 600
```

The default model is `openai-codex/gpt-6-luna`, with medium thinking;
model availability and an authenticated test response were verified. The worker gets [compact instructions](pi-proof-worker.md), not the
parent conversation or automatically loaded `AGENTS.md`/`STATUS.md`. It can
edit files and call the shared Lean tools. Extra extensions, skills and
prompt templates are disabled; only built-in MCP/codemode support is loaded.

Full events, stderr, the task and a usage summary are saved in a fresh
`/tmp/pi-proof-worker-*` directory. Only the final report and usage summary
are printed. Logs may contain source code and should be treated as private.
The timeout or Ctrl+C terminates the worker process group, not the external
HTTP server. A zero exit status means the agent finished normally, **not**
that the proof is correct. Always review the diff and independently check
Lean diagnostics and axioms. File restrictions are instructions, not a sandbox.

## Proof-worker experiment history

The first two trials used `openai-codex/gpt-5.6-luna`; the later hands-off
trial used GPT-6 Luna. These are observations, not additional steps in the
default workflow above.

### First lemma trial

Luna implemented `integral_mollifierKernel` in `LineMollifier.lean`: for
`ε > 0`, the rescaled kernel has integral one. The proof cancels the scaling
factor using the real change-of-variables formula and `integral_stdBump`.

| Run | Seconds | Turns | Uncached input | Output | Cache read |
| --- | ---: | ---: | ---: | ---: | ---: |
| Implementation, blocked on stale imports | 63.07 | 23 | 27,475 | 2,907 | 310,912 |
| Fresh worker validating after dependency rebuild | 44.76 | 6 | 7,804 | 390 | 25,344 |

The first worker reported the import blocker rather than claiming validation.
The parent rebuilt the stale dependencies through `SobolevLocal` with the
shared server stopped, then restarted it. The second worker checked the
original candidate without modifying it. Parent checks independently confirmed
clean diagnostics apart from the seven existing admissions, and axioms only
`propext`, `Classical.choice`, `Quot.sound`. No existing admission was discharged;
this adds a proved prerequisite for the mollifier estimates.

The two runs reported 374,832 total tokens, of which 336,256 were cache reads;
Pi's catalog-based cost estimate was about $0.018, not an invoice. Counts sum
completed assistant responses, not streaming deltas. The runner has a hard
wall-clock timeout; its instruction to stop after about 15 unproductive tool
calls is advisory. The initial run exposed discovery/filename mistakes and
repeated import checks; the worker prompt now gives a direct diagnostics
example and asks it to stop immediately on stale imports.

This is an end-to-end functionality test, not evidence of savings yet. Parent
setup/debugging/review usage is not included in that table.

### Second lemma trial

One fresh Luna worker proved `contDiff_mollifierKernel`,
`hasCompactSupport_mollifierKernel` and `integral_deriv_mollifierKernel` in
`LineMollifier.lean`, without parent intervention during implementation.
The parent supplied the fixed statements and a short outline: composition
preserves smoothness, scaling preserves compact support, and FTC gives zero
integral of the derivative. The worker used Mathlib's compact-support scaling
and half-line FTC results; the two half-line boundary contributions cancel.

Dependencies were preflighted before delegation. The single run took 128.84
seconds and 31 assistant turns, with 31,520 uncached input tokens, 5,047 output
tokens and 508,928 cache-read tokens (545,495 total). Pi's catalog-based cost
estimate was about $0.023. The parent reviewed the source and independently
checked full-file diagnostics and all three axiom lists using the shared
server. Each theorem uses only `propext`, `Classical.choice`, `Quot.sound`;
the seven pre-existing mollifier admissions remain unchanged.

A parent-usage snapshot through dispatch of the independent verification call
recorded six assistant responses: 12,079 uncached input, 2,895 output and
785,536 cache-read tokens (800,510 total). This **excludes subsequent**
documentation, blueprint validation and the final response, so is only a
partial coordination/review count, not an end-to-end cost. The parent's
long conversation and the worker's fresh context also differ substantially.
No matched parent-only baseline has been measured; these successful trials
do not yet establish token or cost savings.

### First GPT-6 Luna hands-off trial

The task was `transversalMollifier_eq_zero`: pointwise support of the
transversal mollifier in a fixed compact subset of the punctured cell.
Imports were preflighted and a short compact-band/kernel-support outline was
supplied. Each worker ran in the foreground; the parent waited for the final
report, without polling transcripts, editing the target or directing the run.

| Thinking | Seconds | Responses | Uncached input | Output | Cache read | Outcome |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| medium | 17.88 | 8 | 16,414 | 691 | 63,488 | No edits; incomplete |
| high (retry) | 57.22 | 15 | 20,155 | 2,146 | 143,104 | No edits; incomplete |

Both used `openai-codex/gpt-6-luna`. The retry was prompted by the first
failure, not live supervision. Both returned normally but stopped without
an implemented proof or a concrete Lean obstruction. Autonomous success was
0/2; a successful runner exit is not proof success. Recorded worker usage was
245,998 tokens, including 206,592 cache-read tokens, excluding parent work.
The parent subsequently proved the lemma directly, without admitted
dependencies. This small unsuccessful trial does not establish GPT-6 Luna's
general suitability or any end-to-end savings.
