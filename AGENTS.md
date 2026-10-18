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
  (Fourier-defined and weak derivatives), `SobolevTorus.lean` (`Hˢ(𝕋²)` via
  Fourier coefficients, elliptic regularity of `Δ⁻¹`). Symmetry chapter: `Symmetry.lean`
  (pointwise maps), `SymmetryL2.lean` (action on `L²`), `Sectors.lean`.
  `DipoleCalculus.lean` defines classical partial derivatives, `L₀` and
  adapted fields on the real lift `ℝ²` and proves the dipole identities;
  `NormalField.lean` proves the even–even normal field algebra;
  `VirialAlgebra.lean` proves the pointwise commutator identities;
  `SeparatrixArc.lean` treats the explicit heteroclinic arc;
  `FlowBoundaryForm.lean` transforms the flow-time boundary form to the
  `ξ = tanh s` form and proves its positivity; `LiftIntegration.lean`
  integrates periodic lifts over `[0, 2π]²` (integration by parts,
  skew-symmetry of `D` and `L₀`); `VirialSmooth.lean` and
  `VirialQuadratic.lean` prove the two forms of the smooth virial identity;
  `VirialFourier.lean` writes the virial pairings as torus inner products and proves the
  Fourier integrations by parts (skew-symmetry of `D` on `H¹`, the equivalence of the two
  forms on `X`); `CellPeriodization.lean` periodizes compactly supported cell functions to
  the torus (`boxPeriodize`) and proves uniqueness of weak derivatives; `VirialL2.lean`
  proves the `H¹` commutator identity and the virial identities for `L²` eigenfunctions and
  fields supported in an annulus from the mollifier lemmas; `TransportOperator.lean`
  defines `H = -iL₀` as an unbounded operator and states its self-adjointness;
  `LiftTorus.lean` relates periodic lifts to functions on the torus (classical
  vs Fourier derivatives, `Cᵏ ⊂ Hᵏ`, integrals); `SobolevLocal.lean` defines
  weak derivatives and `Hᵏ(U)`, `Hᵏ_loc(U)`, weighted `Hᵏ` on open `U ⊆ ℝ²`;
  `LiftPeriodization.lean` periodizes compactly supported functions on `ℝ²` to the
  torus, unfolds integrals against lifts, proves `L₀` against `H¹` tests on the torus,
  and transfers torus Sobolev regularity and the weak `L₀` relation to lifts;
  `Cells.lean` treats the cells, separatrix, critical points and the cell as a
  square in diagonal coordinates; `Period.lean` defines the period function;
  `DipoleFlow.lean` constructs the global dipole flow and proves the orbit and
  period lemma. `OrbitCoordinates.lean` defines the orbit coordinates `(h, t)`,
  flow-time level integrals and normal/tangential derivatives. `Transport.lean` defines transport pairs on open unions of orbits.
  `TransportODE.lean` gives finite-interval transport/pairing estimates and nonresonant
  periodic uniqueness with inherited translation characters, together with the shared
  monotone/antitone AC composition lemmas.
  `CanonicalProfile.lean` defines the canonical transport profile on an arc.
  `CanonicalBoundaryForm.lean` identifies its arc form with the explicit-derivative
  boundary form, using a.e. chain rules under `tanh` on the weighted domain.
  `EigenfunctionTransport.lean` prepares Melnikov and the pairing limit for
  eigenfunctions (explicit invariant neighbourhood of the cell, continuity of the
  flow, changes of representative on levels and in transport pairs).
  `ResonantVanishing.lean` proves the orbitwise transport equation, the mode relation and
  resonant vanishing. `Melnikov.lean` proves the Melnikov condition (arc trace, Hölder
  continuity near the separatrix segment, resonant levels, quarter identity) and
  specializes it and the pairing limit to eigenfunctions (`ee_melnikov`,
  `ee_transport_traces`).
  `DiagonalCalculus.lean` treats integrals and derivatives in diagonal
  coordinates; `QuarterOrbits.lean` writes levels as four quarter orbits and these, and the
  separatrix arc, as explicit graphs in diagonal coordinates; `SeparatrixTraces.lean` defines
  line representatives (`IsLineRep`) and proves the even–even separatrix traces (arc traces,
  arc energy, level traces, corner tails); `SegmentEstimates.lean` bounds
  restrictions to curves near a line (segment and hyperbola estimates); `LineMollifier.lean` mollifies functions on `ℝ²` in the first variable;
  `AnglePeriodization.lean` constructs smooth periodic angular tests, their integral
  unfolding and a compact angular partition of unity;
  `TransversalMollifier.lean` treats weak derivatives in action-angle coordinates and the
  mollifier in the level variable used for the `L²` virial identity; `OddHardy.lean` proves the critical Hardy inequality for odd
  functions in Gagliardo form.
  Then
  `DuBoisReymond.lean` proves the du Bois-Reymond lemma on an interval;
  `IntervalH1.lean` supplies bounded-interval H¹ and endpoint traces;
  `IntervalH1Estimates.lean` proves endpoint estimates and vanishing rescaled layers;
  `IntervalZeroExtension.lean` proves jump-free zero extension of zero-trace H¹ data;
  `BoundaryForm.lean` proves the classical boundary positivity argument;
  `WeightedBoundary.lean` defines its weighted second-order domain and proves
  classical inclusion, local regularity and affine stability.
  `WeightedBoundaryForm.lean` extends the completion of squares, affine
  splitting and positivity of the boundary form to that domain by exhausting
  the interval. `BoundaryCutoff.lean` proves multiplier stability and
  convergence for uniformly controlled cutoff families, and
  `BoundaryCutoffConstruction.lean` constructs a smooth such family (an
  approximation route the main argument no longer uses).
  Sector exclusions are in `EvenEven.lean` (the even–even assembly proof, direct
  vorticity endgame, and named admitted analytic inputs), `OddOdd.lean`,
  `Mixed.lean` and `Main.lean`. Each module docstring says what it contains and which blueprint
  nodes it covers.
- `lakefile.toml`, `lean-toolchain`: Lean `v4.34.1`, Mathlib `v4.34.1`.
- `STATUS.md`: short project-wide status and entry point to `docs/status/`.
- `docs/status/{even-even,odd-odd,mixed,shared}.md`: current sector-specific
  and shared-infrastructure blockers, priorities and implementation pointers.
- `justfile`: build recipes (run `just` to list them).
- `scripts/`: helper scripts. `check_blueprint.py` (behind
  `just check-blueprint`, also run before web/PDF builds) checks source labels,
  references and dependency cycles without Lean or plasTeX. The same source
  model feeds `blueprint_status.py` (`just status-blueprint`), which writes the
  Git-ignored `docs/status/generated.md` report and also runs during `just web`.
  `blueprint_subgraph.py` (used by `just web` and `just graph`) restricts the
  web dependency graph to chosen nodes and their dependencies, drawn in one
  box per chapter (`--no-chapters` for the plain layout).
  `SorryDeps.lean` (behind `just sorries`) loads the built library and lists the
  declarations with `sorry` (and project axioms) that given Lean declarations
  depend on, transitively, with source locations.
- `.mcp.json`: registers the `lean-lsp` MCP server for Claude Code.
- `.github/workflows/`: the Lean template CI (lean-action, docgen).

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
just sorries virial_l2  # admitted declarations it depends on (default: main; ~50 s)
just manuscript      # reworked manuscript PDF, rebuilt on change (needs xelatex, latexmk)
just manuscript eigenvalues  # same for the original manuscript
```

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
running, so after a file has been opened once an edit is rechecked in well
under a second.

Tool-specific setup notes live in `docs/tooling/`. When using Pi, read
[the Pi setup notes](docs/tooling/pi.md) for its shared Lean MCP configuration.

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
This file is for guidance that stays valid across sessions.
