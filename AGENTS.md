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

The blueprint links all three: breaking the argument into small nodes for Lean
is also how we digest it, and the resulting structure is what should go back
into the paper. This way of working is an experiment; expect to adjust it.

There are three layers, plus the reworked paper:

1. `Manuscript/eigenvalues.tex`: the original manuscript, kept unchanged as
   the reference. In this repository "the manuscript" means this file. It is
   the origin of the argument but **not** a trusted source: treat its claims
   as unverified until they are checked, either by an independent derivation
   or in Lean.
2. `blueprint/`: a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
   that restructures the manuscript into small nodes (definitions and lemmas)
   with a dependency graph. It is the to-do list for the formalization, the
   place to digest the manuscript, and a staging area for changes that should
   go back into the paper. See `blueprint/README.md` and
   `blueprint/src/chapters/intro.tex`.
3. `NoEmbeddedEigenvalues/`: the Lean code.

The reworked manuscript `Manuscript/manuscript.tex` is the paper being
written. It is written as we go and should always represent our current
understanding: a section is filled in once the corresponding part of the
argument is understood, otherwise it is a placeholder. Its content comes from
the blueprint, but it is written as a paper: fewer and larger results,
motivation, and standard facts cited rather than proved.

## Working on the mathematics

- Be skeptical of the manuscript. "Asserted", "by the argument of",
  "similarly" and unexplained constants are places to look closely. Report
  what you actually verified and how (symbolic check, numerical check, full
  derivation), and keep sanity checks clearly separate from proofs.
- When explaining a step, give the mechanism (why it works, what the key
  cancellation or sign is), not only a restatement.
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

## Layout

- `Manuscript/eigenvalues.tex`: the original manuscript (unchanged reference).
- `Manuscript/manuscript.tex`: the reworked manuscript. Both build into
  `Manuscript/build`.
- `blueprint/src/content.tex`: list of chapters, in order.
- `blueprint/src/chapters/*.tex`: one file per chapter: `intro`, `setup`,
  `symmetry`, `geometry`, `analysis`, `virial`, `transport`, `even_even`,
  `regularity`, `odd_odd`, `mixed`, `certificates`, `notes`.
- `blueprint/src/macros/common.tex`: theorem environments and math macros for
  both builds (`\T \R \Z \N \C`, `\Div`, `\Dom`, `\Cell`, `\ip{}{}`, ...).
  `macros/print.tex` defines no-op versions of the blueprint macros for the PDF.
- `NoEmbeddedEigenvalues.lean`: Lean library root, importing every module.
- `NoEmbeddedEigenvalues/*.lean`: the Lean modules, following the blueprint
  chapters; a chapter may be split over several modules. Setup chapter:
  `TorusL2.lean` (measure, `L²`, characters, coefficients), `Fourier.lean`
  (Hilbert basis, Parseval, bounded Fourier multipliers), `Setup.lean`
  (`Δ⁻¹`, `L₀`, domain, eigenvalue problem), `Derivatives.lean`
  (Fourier-defined and weak derivatives). Symmetry chapter: `Symmetry.lean`
  (pointwise maps), `SymmetryL2.lean` (action on `L²`), `Sectors.lean`. Then
  `IntervalH1.lean` supplies bounded-interval H¹ and endpoint traces;
  `IntervalH1Estimates.lean` proves endpoint estimates and vanishing rescaled layers;
  `IntervalZeroExtension.lean` proves jump-free zero extension of zero-trace H¹ data;
  `BoundaryForm.lean` proves the classical boundary positivity argument;
  `WeightedBoundary.lean` defines its weighted second-order domain and proves
  classical inclusion, local regularity and affine stability.
  `BoundaryCutoff.lean` proves multiplier stability and convergence for
  uniformly controlled cutoff families. `BoundaryCutoffConstruction.lean`
  constructs a smooth family with uniform bounds and proves unconditional
  endpoint cutoff approximation; interior mollification is still pending.
  Sector exclusions are in `EvenEven.lean`, `OddOdd.lean`, `Mixed.lean` and
  `Main.lean`. Each module docstring says what it contains and which blueprint
  nodes it covers.
- `lakefile.toml`, `lean-toolchain`: Lean `v4.34.1`, Mathlib `v4.34.1`.
- `STATUS.md`: current state, decisions and next steps.
- `justfile`: build recipes (run `just` to list them).
- `.mcp.json`: registers the `lean-lsp` MCP server for Claude Code.
- `.github/workflows/`: the Lean template CI (lean-action, docgen).

## Building

```sh
just web             # blueprint website in blueprint/web (with dependency graph)
just serve           # serve it at http://localhost:8000 (needs only python3)
just pdf             # blueprint PDF in blueprint/print
just build           # lake build
just manuscript      # reworked manuscript PDF, rebuilt on change (needs xelatex, latexmk)
just manuscript eigenvalues  # same for the original manuscript
```

Agents usually run in a VM that has `just`, `leanblueprint` and `kpsewhich`
installed system-wide; there, run `just web` directly. The user runs
`just serve` on the host to look at the result. The VM has no
`xelatex`/`latexmk`, so `just pdf` and `just manuscript` are for the host.

Gotchas:

- Run `just web`, not `leanblueprint web`: the recipe first makes
  `blueprint/web` writable, because plasTeX copies read-only files out of the
  Nix store and a second build would fail on them.
- Messages that `gs`, `pdflatex`, `dvisvgm` or `pdf2svg` were not found are
  harmless: they come from plasTeX's image converters, which this blueprint
  does not use. `graphviz` is not needed either; the graph is rendered in the
  browser.
- Lean and Mathlib come from `elan`/`lake`; run `lake exe cache get` before the
  first `lake build` to download Mathlib's build cache.

## Working with Lean

Use the `lean-lsp` MCP server (configured in `.mcp.json`, provided by the
VM's `lean-lsp-mcp`) rather than repeated `lake build` or `lake env lean`.
It keeps a Lean language server running, so after a file has been opened once
an edit is rechecked in well under a second.

Costs measured in the VM (4 cores, 12 GB):

| Operation | Time |
|---|---|
| Any new Lean process with `import Mathlib` (`lake env lean`, a module in `lake build`, opening a file in the server) | ~50 s, ~6.5 GB |
| Same with a single targeted Mathlib import | ~15 s, ~2.4 GB |
| Recheck after an edit in an open file | ~0.2 s |
| `lean_multi_attempt` | ~60 s (reloads Mathlib) |

Almost all of the 50 s is spent loading Mathlib's `.olean` files over the
`virtiofs` share, not computing, and it is paid again by every new process.

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
- New Lean modules must be imported in `NoEmbeddedEigenvalues.lean`. Lean
  names are in the namespace `NoEmbeddedEigenvalues`.
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
- Algebraic identities are separated from their analytic justification; the
  algebraic nodes and `certificates.tex` (Bernstein-coefficient positivity,
  meant to be checked by `decide`/`native_decide`) are the first formalization
  targets.
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

The current state, decisions and next steps are in `STATUS.md`. Read it at
the start of a work session and update it at the end. It is a snapshot:
rewrite it rather than append to it. This file is for guidance that stays
valid across sessions.
