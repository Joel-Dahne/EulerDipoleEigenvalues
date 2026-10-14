# Status

A snapshot of where the project stands. Rewrite it at the end of each work
session instead of appending to it; the history is in `git log`.

Not repeated here: progress per node is in the blueprint's dependency graph
(`\leanok`), and open mathematical problems are in
`blueprint/src/chapters/notes.tex`.

## Next steps

1. Finish the setup lemmas using the now-proved Fourier infrastructure:
   - Prove linearity of `HasL0` and `hasL_iff_isEigenSolution`.
   - Add integral bridge lemmas for `fourierCoeff` and `MeanZero`; the full
     inverse-Laplacian blueprint definition also asserts second derivatives.
   The import cycle has been removed: `TorusL2.lean` contains the foundations,
   `Fourier.lean` imports it, and `Setup.lean` imports Fourier.
2. Digest the even–even sector end to end: check identities with SymPy,
   explain the mechanism, write digest notes, formalize the algebraic nodes.
3. Soon after: assess the largest gap, the odd–odd renormalized virial
   identity (`prop:dd-virial`). If correctness of the result is the priority,
   do this before 2.

## Current state

- **Blueprint**: all 13 chapters drafted, with the Sobolev tiers in place.
  `intro.tex` and `blueprint/README.md` do not mention the tiers yet.
  Setup now has separate fully proved Fourier-basis and reconstruction/
  Parseval nodes. Removed overly broad statement-level `\leanok` markings
  from the torus and inverse-Laplacian definitions; remaining coverage is
  explained next to the nodes. The new `lem:transport-fourier` node records
  the fully proved character expansion and weak/Fourier equivalence.
  `lem:inverse-laplacian-fourier` now records proved convergence, coefficients,
  square summability and mean zero; the derivative claims remain unmarked.
  `lem:L0-stream` is now fully proved, using component-weighted coefficients
  and perpendicular shifts. The proof also works for inputs with nonzero mean.
- **Lean**: `Symmetry.lean` formalizes reflections and reflection algebra,
  fully proved. `Setup.lean` states every original setup node, including
  `thm:main`, with two remaining `sorry`s (main theorem and reduction);
  the user reviewed the definitions (2026-10-13).
  `TorusL2.lean` now holds the unchanged measure/L2/character foundations;
  all declaration names remain unchanged. `char_coe`, `L0char_coe`, and
  `volume_univ_torus` are proved. `L0char_fourier`, `L0charLp_fourier`,
  `fourier_transport_pairing`, and `hasL0_iff_fourierCoeff` are proved.
  Setup also proves positivity of `normSq` at nonzero frequencies, the
  coefficient norm bound, square summability, `hasSum_invLap`,
  `fourierCoeff_invLap`, and `meanZero_invLap`. The existing definition of
  `invLap` is unchanged; its `tsum` now has a convergence proof.
  `exists_hasL0_invLap` is proved for all `ω : L2`. Its helpers show
  `|k_j| ≤ normSq k`, bound `k_j * fourierCoeff (invLap ω) k` by the
  input coefficient norm, and prove square summability of the transport
  coefficients. The key simplification is that perpendicular frequency
  shifts do not change the multiplying component.
  `Fourier.lean` has no `sorry`s: scaling and change of measure, character
  identification with unit monomials, dense spans, orthogonality, the Hilbert
  basis `(2π)⁻¹ e_k`, coordinates `2π ĝ_k`, L2 reconstruction, Parseval,
  coefficient uniqueness, square summability, and existence for any
  prescribed square-summable coefficient sequence. New reusable lemmas
  `summable_fourier_series` and `fourierCoeff_tsum` turn square-summable
  sequences into convergent series with the exact prescribed coefficients.
- **Validation**: `lake build` and `just web` pass after the stream-function
  transport proof. Lean LSP reports only the two expected Setup `sorry`
  warnings. Axiom verification of `hasL0_iff_fourierCoeff`,
  `fourierCoeff_invLap`, and `exists_hasL0_invLap` reports only `propext`,
  `Classical.choice`, and `Quot.sound` (no `sorryAx`).
  The native Pi MCP integration now works; diagnostics reuse the Lean server.
  Reinstalling Lean 4.34.1 repaired stale Nix paths after the VM update.
- **Reworked manuscript** (`manuscript.tex`): front matter and the
  introduction up to the main theorem. The other sections are placeholders.
  Neither manuscript was changed in the Fourier work.

## Decisions

Each points to where the decision is recorded in detail.

- `L²` model (2026-10-13, as a first attempt): `Lp` on `Angle × Angle`, `L₀`
  as a relation tested against characters, `Δ⁻¹` as a series of characters.
  Remark "Lean model" in `setup.tex`.
- Fourier transport: use the scaling homeomorphism to transport continuous
  monomial density and orthogonality, then construct the physical Hilbert
  basis directly. No separate L2 scaling equivalence is needed. This avoids
  the extra quotient-function and measure-rescaling plumbing. `Fourier.lean`
  and the Fourier-basis proof in `setup.tex`.
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
