# Status

A snapshot of where the project stands. Rewrite it at the end of each work
session instead of appending to it; the history is in `git log`.

Not repeated here: progress per node is in the blueprint's dependency graph
(`\leanok`), and open mathematical problems are in
`blueprint/src/chapters/notes.tex`.

## Next steps

Agreed 2026-10-12:

1. Setup chapter infrastructure: Parseval and a Hilbert basis for the
   2π-torus, by transporting Mathlib's `mFourierBasis` along the scaling map.
   This is what the setup lemmas `hasL0_iff_fourierCoeff`,
   `exists_hasL0_invLap` and `hasL_iff_isEigenSolution` need.
2. Digest the even–even sector end to end: check identities with SymPy,
   explain the mechanism, write digest notes, formalize the algebraic nodes.
3. Soon after: assess the largest gap, the odd–odd renormalized virial
   identity (`prop:dd-virial`). If the user is more worried about the
   correctness of the result than about the workflow, do this before 2.

## Current state

- **Blueprint**: all 13 chapters drafted, with the Sobolev tiers in place.
  `intro.tex` and `blueprint/README.md` do not mention the tiers yet.
- **Lean**: `Symmetry.lean` formalizes `def:reflections` and
  `lem:reflection-algebra`, fully proved. `Setup.lean` states every node of
  the setup chapter, including `thm:main`, with `sorry`; the user reviewed the
  definitions (2026-10-13). The sanity lemmas `char_coe`, `L0char_coe` and
  `volume_univ_torus` are proved.
- **Reworked manuscript** (`manuscript.tex`): front matter and the
  introduction up to the main theorem. The other sections are placeholders.

## Decisions

Each points to where the decision is recorded in detail.

- `L²` model (2026-10-13, as a first attempt): `Lp` on `Angle × Angle`, `L₀`
  as a relation tested against characters, `Δ⁻¹` as a series of characters.
  Remark "Lean model" in `setup.tex`.
- Notation (2026-10-13): the mean-zero space is `X` (not `L^2_0`, which
  typesets like `L_0^2`); the velocity field `(sin y, −sin x)` is `Y`. Remark
  after `def:torus`.
- The main theorem is stated for real `λ`; non-real eigenvalues are excluded
  by an elementary argument in a remark (2026-10-13). Remark "Non-real
  eigenvalues" in `setup.tex`.
- `eigenvalues.tex` stays unchanged as the reference; `manuscript.tex` is
  written as we go (2026-10-13). `AGENTS.md`.

## Not set up yet

Needs a GitHub remote first (there is none): `checkdecls` in the lakefile,
the `\home`/`\github`/`\dochome` links in `blueprint/src/web.tex`,
`blueprint: true` in the docgen CI step, and the GitHub settings described in
the top-level `README.md`.
