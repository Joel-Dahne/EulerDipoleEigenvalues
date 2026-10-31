# AGENTS.md

Guidance for AI agents (and humans) working in this repository.

## Project

Formalization in Lean 4 + Mathlib of the paper *Absence of nonzero embedded
eigenvalues for the two-dimensional Euler equation linearized around the
dipole* (Joel Dahne, Hao Jia). The dipole is the stream function
`cos x + cos y` on the torus `(R/2πZ)^2`. The argument uses virial identities
and explicit comparison functions whose signs are certified by exact
arithmetic.

The project has three goals of equal weight, pursued together:

1. **Formalize** the result in Lean.
2. **Digest** the result. The manuscript was mostly AI-generated, and the
   authors do not yet fully own the argument. The aim is to understand why
   each step works, find gaps and errors, and find simpler routes.
3. **Improve the manuscript**, which is currently very rough, into a
   well-presented paper (`Manuscript/manuscript.tex`).

The blueprint links all three: small nodes make the argument easier to digest
and formalize, and the settled structure feeds back into the paper.

- `Manuscript/eigenvalues.tex` is the unchanged original reference. In this
  repository "the manuscript" means this file. It is **not** a trusted source.
- `blueprint/` is the dependency graph, formalization plan and staging area
  for corrections. See `blueprint/README.md` and `blueprint/src/chapters/intro.tex`.
- `NoEmbeddedEigenvalues/` is the Lean library.
- `Manuscript/manuscript.tex` is the reworked paper: current understanding,
  written as a paper rather than a blueprint, with placeholders for unsettled
  sections. Update it only with the authors' agreement.

## Working on the mathematics

- Be skeptical of the manuscript. "Asserted", "by the argument of",
  "similarly" and unexplained constants are places to look closely. Report
  what you actually verified and how (symbolic check, numerical check, full
  derivation), and keep sanity checks clearly separate from proofs.
- When explaining a step, give the mechanism (why it works, what the key
  cancellation or sign is), not only a restatement.
- In explanations, plans and progress reports, prefer the Blueprint node's
  title and label over its Lean declaration name when both exist. Include
  the label (e.g. `thm:ee-exclusion`) so the node is easy to find in the graph.
  Add the Lean name in parentheses only when useful for locating code; use
  exact Lean names when discussing code or diagnostics.
- Record problems as digest notes (see below) instead of quietly fixing them
  in the blueprint, so the authors see what changed and why.
- Look out for simplifications and better structure: unused generality, results
  proved twice, notation clashes, and arguments that become shorter in a
  different order. These are candidates for the paper.
- Scratch computations (SymPy, numerics) belong in a scratch directory. Do not
  add them to the repository unless asked; verification scripts for the
  certificates are an exception, once they are planned.
- Never edit `eigenvalues.tex`. Do not edit `manuscript.tex` on your own
  initiative: changes go into the blueprint first and are brought into the
  reworked manuscript once a chapter has settled and the authors agree.

## Navigation and audit boundary

Read `STATUS.md` and the relevant topic page at the start of a session.
Use [the architecture guide](docs/architecture.md) on demand for the module
map, blueprint layout and verification tools; do not load the full map for
unrelated work. Module docstrings describe implementation details.

- `NoEmbeddedEigenvalues.lean` imports every library module. Add new modules
  there; declarations belong to namespace `NoEmbeddedEigenvalues` regardless
  of subdirectory.
- `Challenge.lean` states the main theorem and definition sanity checks with
  Mathlib only and `sorry` proofs; it is the reader's audit target.
  `Solution.lean` repeats its definitions verbatim and proves the theorems
  through library bridges. `comparator.json` lists compared theorems and
  permitted axioms. Change Challenge definitions only with the authors'
  agreement, and copy changes to Solution.
- `lakefile.toml` and `lean-toolchain`: Lean and Mathlib `v4.34.1`.
- `justfile`: build recipes; run `just` to list them.

## Building

```sh
just check-blueprint # fast source label/reference/dependency checks
just test-blueprint  # checker/report regression tests
just status-blueprint # regenerate sector counts and unfinished-node report
just web             # source checks + website, sector graphs and status report
just serve           # serve it at http://localhost:8000 (needs only python3)
just graph thm:ee-exclusion  # graph of a node and all it depends on (after just web)
just pdf             # blueprint PDF in blueprint/print
just build           # lake build
just manuscript      # reworked manuscript PDF, rebuilt on change (needs xelatex, latexmk)
just manuscript eigenvalues  # same for the original manuscript
```

Task-specific audits:
- `just challenge` (~2 min): statement/axiom comparison after changes to
  `Challenge.lean`, `Solution.lean`, comparator configuration/checker or Lean/Mathlib
  versions, or for requested/milestone audits.
- `just sorries NAME...` (~50 s): actual transitive Lean admissions, on request
  or when needed to establish admission-freedom or inspect a dependency frontier.

Agents usually run in a VM that has `just`, `leanblueprint` and `kpsewhich`
installed system-wide; there, run `just web` directly. The user runs
`just serve` on the host to look at the result. `just web` also regenerates
all three sector subgraphs, linked from the index and chapter sidebars;
a separate `just graph` is needed only for custom views. The VM has no
`xelatex`/`latexmk`, so `just pdf` and `just manuscript`
are for the host.

Gotchas:

- Run `just web`, not `leanblueprint web`: the recipe checks source consistency,
  then makes `blueprint/web` writable, because plasTeX copies read-only files
  out of the Nix store and a second build would fail on them.
- Messages that `gs`, `pdflatex`, `dvisvgm` or `pdf2svg` were not found are
  harmless: they come from plasTeX's image converters, which this blueprint
  does not use. `graphviz` is not needed either; the graph is rendered in the
  browser.
- Lean and Mathlib come from `elan`/`lake`; run `lake exe cache get` before the
  first `lake build` to download Mathlib's build cache.

## Working with Lean

Use the `lean-lsp` MCP server (provided by the VM's `lean-lsp-mcp`) rather
than repeated `lake build` or `lake env lean`. It keeps a Lean language server
running and reuses unchanged imports and source prefixes. Edit latency depends
on the invalidated work.

Tool-specific setup notes live in `docs/tooling/`. When using Pi, read
[the Pi setup notes](docs/tooling/pi.md) for its stdio Lean MCP configuration.

Costs measured in the VM (4 cores, 12 GB):

| Operation | Time |
|---|---|
| Any new Lean process with `import Mathlib` (`lake env lean`, a module in `lake build`, opening a file in the server) | ~50 s, ~6.5 GB |
| Same with a single targeted Mathlib import | ~15 s, ~2.4 GB |
| Diagnostics in an open file | ~0.2 s unchanged; edits can take seconds |
| `lean_multi_attempt` | ~60 s (reloads Mathlib) |

Almost all of the 50 s is spent loading Mathlib's `.olean` files over the
`virtiofs` share, not computing, and it is paid again by every new process.

Module layout (older code may not follow these conventions):

- Keep new modules focused on one blueprint node or a small coherent group;
  small actively edited files keep diagnostic checks fast.
- Use topic subdirectories roughly following blueprint chapters (e.g.
  `Analysis/`, `Geometry/`, `OddOdd/`), with shared infrastructure in its natural topic.
- When a node needs a large file, look for meaningful intermediate results to
  expose as smaller blueprint nodes. Keep technical Lean helpers with the result
  they support.

Workflow:

1. Write the statement with `sorry`, then use `lean_diagnostic_messages` and
   `lean_goal` to check it and inspect goals. Read goals instead of guessing.
2. Fill the proof step by step, editing the file and rechecking diagnostics.
   Prefer editing and rechecking over `lean_multi_attempt`, which is slow here.
3. Find lemmas with `lean_local_search` (ripgrep over the project and
   Mathlib sources; it matches declaration names, not prefixes like
   `Real.Angle.cos_`, so use `rg` in `.lake/packages/mathlib` for those),
   `lean_loogle`, `lean_leansearch` or `lean_leanfinder`, rather than
   guessing names. The last three are remote services with rate limits.
   Prefer targeted Mathlib imports while the file is small: they load in
   ~15 s instead of ~50 s.
4. Run `lake build` only at checkpoints, such as before a commit.

Memory: each process that imports Mathlib takes about 6.5 GB, so two at once
may not fit in 12 GB (untested). Avoid running `lake build` while the language
server has a file open, and keep work in one file at a time where possible.

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
  `def:h2-interval`, `def:h1-periodic`, `def:weighted-boundary-domain`) and
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

1. Digest a manuscript argument into small blueprint nodes; record doubts as
   digest notes.
2. State in Lean with `sorry`; add `\lean{...}` and `\leanok` to the statement.
   The Lean statement must be reviewed carefully by a human, since Lean cannot
   check that it says the right thing.
3. Prove in Lean; add `\leanok` to the proof.
4. Feed changes in statements or structure back into the blueprint and, once a
   chapter has settled, into the reworked manuscript (`manuscript.tex`).

## Status

Read `STATUS.md` at the start of a work session, then the relevant pages in
`docs/status/`. Update the affected topic pages at the end; change the root
status only when project-wide priorities, constraints or overall state change.
Keep these files as short current snapshots, not logs or inventories of completed
lemmas. Shared infrastructure belongs in `docs/status/shared.md`; sector pages
should link there rather than duplicate its backlog. Per-node progress belongs
in the blueprint, mathematical gaps in its digest notes, implementation details
in module documentation, and history in Git. Do not hand-maintain graph counts:
use `just status-blueprint` to refresh `docs/status/generated.md`. Its markers
are not an audit of Lean declarations or axioms.
Keep docstrings and blueprint prose focused on stable mathematical content,
not temporary progress claims such as “still admitted” or lists of remaining
prerequisites. Use blueprint status markers, generated reports and topic status
pages for progress. When closing a gap, remove obsolete warnings and retain
only the mathematical explanation of the resolution.

This file is for guidance that stays valid across sessions.
