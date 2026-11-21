# AGENTS.md

Guidance for AI agents (and humans) working in this repository.

## Name results by their blueprint labels

Use the exact blueprint label (e.g. `lem:elliptic-local`) when referring to a
graph node in explanations, plans, progress updates, final summaries, or status
pages. The label alone is enough; the title is optional. Use Lean names for
code, commands, and diagnostics, not in place of labels in user-facing reports.

## Project

Formalization in Lean 4 + Mathlib of the paper *Absence of nonzero embedded
eigenvalues for the two-dimensional Euler equation linearized around the
dipole* (Joel Dahne, Hao Jia). The dipole is the stream function
`cos x + cos y` on the torus `(R/2πZ)^2`. The argument uses virial identities
and explicit comparison functions whose signs are certified by exact
arithmetic.

**Current priority: complete the Lean formalization of the main theorem
without admissions.** Defer a standalone review of the argument and a rewrite
of the manuscript until then. As part of formalizing, investigate gaps and
errors, look for simpler proofs, and record what you learn in the blueprint.

- `Manuscript/eigenvalues.tex` is the unchanged original reference. In this
  repository "the manuscript" means this file. It is **not** a trusted source.
- `blueprint/` is the dependency graph, formalization plan and staging area
  for corrections. See `blueprint/README.md` and `blueprint/src/chapters/intro.tex`.
- `NoEmbeddedEigenvalues/` is the Lean library.

## Working on the mathematics

- Be skeptical of the manuscript. "Asserted", "by the argument of",
  "similarly" and unexplained constants are places to look closely. Report
  what you actually verified and how (symbolic check, numerical check, full
  derivation), and keep sanity checks clearly separate from proofs.
- When explaining a step, give the mechanism (why it works, what the key
  cancellation or sign is), not only a restatement.
- Record problems as digest notes (see below) instead of quietly fixing them
  in the blueprint, so the authors see what changed and why.
- Prefer simpler proof routes when they help the formalization. Look for
  unnecessary hypotheses, duplicated arguments, and dependencies that can be
  avoided.
- Scratch computations (SymPy, numerics) belong in a scratch directory. Do not
  add them to the repository unless asked; verification scripts for the
  certificates are an exception, once they are planned.
- Never edit `eigenvalues.tex`. Record mathematical changes in the blueprint.

## Navigation and audit boundary

Start with [STATUS.md](STATUS.md) and the relevant topic page. Use the
[blueprint graph](blueprint/README.md#building) and
[generated report](docs/status/generated.md) to find unfinished prerequisites.
Consult [the architecture guide](docs/architecture.md) as needed for the module
map and verification tools.

- `NoEmbeddedEigenvalues.lean` imports every library module. Add new modules
  there; declarations belong to namespace `NoEmbeddedEigenvalues` regardless
  of subdirectory.
- `Challenge.lean` states the main theorem and definition sanity checks with
  Mathlib only and `sorry` proofs; it is the reader's audit target.
  `Solution.lean` repeats its definitions verbatim and proves the theorems
  through library bridges. `comparator.json` lists compared theorems and
  permitted axioms. Change Challenge definitions only with the authors'
  agreement, and copy changes to Solution.
- `lakefile.toml` and `lean-toolchain`: Lean and Mathlib `v4.35.0`.
- `justfile`: build recipes; run `just` to list them.

## Building and verification

- Use `just check-blueprint` for source consistency checks and
  `just test-blueprint` for checker/report regression tests.
- Use `just web`, not `leanblueprint web`: the recipe handles read-only plasTeX
  assets and regenerates the graphs and status report. Use `just status-blueprint`
  when only the report is needed. See the [blueprint build guide](blueprint/README.md#building)
  for serving and custom graphs. Run `just pdf` and `just manuscript` on a host
  with the required TeX tools, not the standard agent VM.
- Run `just build` at integration checkpoints, not for each edit. On a fresh
  checkout, first fetch Mathlib's build cache with `lake exe cache get`.
- Run `just sorries NAME...` for actual transitive admissions, on request or
  when needed to establish admission-freedom or inspect a dependency frontier.
  `NAME` is a Lean declaration name, not a blueprint label.
- Run `just challenge` **only** after changes to `Challenge.lean`,
  `Solution.lean`, comparator configuration/checker or Lean/Mathlib versions,
  or when the user explicitly requests it. It is not a routine build or commit
  check.

### Memory on the VM

Start broad rebuilds on the 12 GB VM with `LEAN_NUM_THREADS=2 just build`.
Use the same prefix for `just sorries` or `just challenge` if they will trigger
such a rebuild. If memory is still tight, retry with `LEAN_NUM_THREADS=1`.
Avoid overlapping heavy builds or audits with active Lean language-server
workers; reducing build concurrency does not free their memory.

This is a per-command setting, not a global cap on routine checks. A retry at
2 threads succeeded after a broad build ran out of memory; the effect on build
time has not been measured. See [Lean performance notes](docs/tooling/lean-performance.md#build-concurrency).

## Working with Lean

Use the persistent `lean-lsp` MCP server for edits and rechecks, rather than
repeated `lake build`, `lake env lean`, or `lean_multi_attempt`. In Pi, if
`lean-lsp` tools are available, use them directly; no setup reading is needed.
Consult [Pi troubleshooting](docs/tooling/pi.md) only if the tools are missing,
the server won't connect, or you're changing its configuration.

- Keep new modules focused on a blueprint node or a small coherent group.
  If a file grows large, look for meaningful intermediate results. Keep
  technical helpers near the result they support.
- Prefer targeted Mathlib imports to `import Mathlib` where practical.
- Look up lemma names rather than guessing. Use `lean_local_search` for
  names, `rg` in `.lake/packages/mathlib` for prefixes, and the remote
  `lean_loogle`, `lean_leansearch`, or `lean_leanfinder` when local search
  is insufficient.

## Blueprint conventions

- Node environments: `definition`, `lemma`, `proposition`, `theorem`,
  `corollary`. `remark` is deliberately **not** a graph node; it is used for
  commentary.
- Label prefixes: `chap:`, `sec:`, `def:`, `lem:`, `prop:`, `thm:`, `cor:`, and
  `cert:` for computer-certified inequalities (these are `lemma`s in
  `certificates.tex`).
- Dependencies: `\uses{...}` in a statement lists what is needed to *state* the
  node; in a proof, what is needed to *prove* it. Keep these accurate: they are
  the whole point of the dependency graph. Every label in `\uses` must exist.
- Lean status: `\lean{Name}`, `\leanok` (statement in Lean, or in a proof: proof
  done), `\mathlibok`, `\notready` (not precise enough yet to formalize). Only
  mark a node `\leanok` when the Lean code covers the whole statement;
  assertions that Lean does not cover yet go in a separate node. In a proof,
  `\leanok` means the Lean proof has no `sorry` of its own; it may cite
  results that are still admitted, which the graph shows through their status.
- A `definition` node contains only definitions; claims about them (that a
  series converges, that a family is a basis) are separate `lemma` nodes.
- Manuscript cross-references are written as `(manuscript \texttt{(label)})`,
  quoting the `\label` in the original `eigenvalues.tex`, so they can be
  found by text search.
- **Digest notes**: questions or problems found in the manuscript go in
  `\begin{remark}[Digest note: ...]` next to the relevant node, and are also
  listed in `chapters/notes.tex`. Remove an item from `notes.tex` once it is
  resolved and record the resolution in the node.
- **Sobolev tiers** (see `chapters/analysis.tex`): every node whose statement
  involves a Sobolev space `\uses` exactly the relevant one of
  `def:h1-interval` (bounded-interval H^1 via absolute continuity), `def:sobolev-torus`
  (H^s(T^2) via Fourier coefficients), or `def:sobolev-local` (Sobolev spaces on
  open sets, weighted PDE spaces, curve traces; the main infrastructure gap in Mathlib).
  Interval nodes also list the relevant derived definitions (`def:h1-zero-interval`,
  `def:h2-interval`, `def:weighted-boundary-domain`) and
  `lem:h1-interval-endpoints` when
  endpoint traces are needed. These are distinct targets, not bundled into H^1.
  This keeps visible in the graph where Sobolev theory enters. The setup and
  symmetry chapters intentionally use none of them: `Δ^{-1}` and `L_0` are
  defined through Fourier coefficients.
- Separate algebraic identities from their analytic justification. Certificates
  use exact arithmetic (e.g. verified Bernstein-coefficient positivity), not
  numerical sanity checks.
- Style: short, precise statements and short proofs; plain prose, no
  marketing language.

## Workflow

1. Use the blueprint to break the proof into precise steps for Lean. Record
   gaps or doubts as digest notes.
2. State the result in Lean with `sorry` and check it with
   `lean_diagnostic_messages`. Add `\lean{...}` and the statement's `\leanok`.
3. Inspect goals with `lean_goal`; fill the proof and recheck diagnostics as
   you go. Add `\leanok` to the completed proof and reflect any statement or
   dependency changes in the blueprint.

## Status updates

Keep per-node progress in blueprint markers. Refresh `docs/status/generated.md`
with `just status-blueprint`; don't copy counts into handwritten files. Update
`STATUS.md` or a topic page only when its overview or durable blockers change.
Use digest notes for mathematical gaps, module docs for implementation details,
and Git for history. Remove obsolete warnings when closing a gap; keep the
mathematical explanation, not temporary proof-status claims.
