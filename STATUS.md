# Status

A snapshot of where the project stands. Rewrite it at the end of each work
session instead of appending to it; the history is in `git log`.

Not repeated here: progress per node is in the blueprint's dependency graph
(`\leanok`), and open mathematical problems are in
`blueprint/src/chapters/notes.tex`.

## Next steps

1. First-partial Fourier/all-smooth-test equivalence is proved. Review the new
   classical test-pair and smoothness definitions; AI review and Lean proof
   checking do not replace human sign-off. Transport, second-order and Laplace
   arbitrary-test bridges are still deferred.
2. The user has paused starting the even–even sector. When requested, digest
   it end to end: check identities with SymPy, explain the mechanism, write
   digest notes, formalize the algebraic nodes.
3. Soon after: assess the largest gap, the odd–odd renormalized virial
   identity (`prop:dd-virial`). If correctness of the result is the priority,
   do this before 2.

## Current state

- **Blueprint**: all 13 chapters drafted, with the Sobolev tiers in place.
  `intro.tex` and `blueprint/README.md` do not mention the tiers yet.
  Setup has separate proved nodes for integral characterizations, Fourier
  basis/reconstruction, inverse-Laplacian convergence and derivatives,
  transport Fourier algebra, weak-transport linearity, stream-function
  transport, and reduction. The torus and inverse-Laplacian definition
  status markings have been restored after the previously missing bridges
  were proved. New nodes define classical test pairs, prove their derivative
  coefficient formula, and prove the first-partial all-smooth-test equivalence.
  The transport, second-order and Laplace arbitrary-test bridges remain deferred.
- **Lean foundations**: `Symmetry.lean` proves reflections and reflection
  algebra. `TorusL2.lean` holds the measure/L2/character foundations and now
  proves integrability, the integral formulas for Fourier coefficients,
  conjugation/zero-character identities, and
  `meanZero_iff_integral_eq_zero`. `Fourier.lean` proves the normalized
  Hilbert basis `(2π)⁻¹ e_k`, coordinates `2π ĝ_k`, reconstruction, Parseval,
  uniqueness and existence for square-summable coefficients, and convergence
  with exact coefficients for arbitrary square-summable Fourier series.
  The import chain is `Symmetry → TorusL2 → Fourier → Setup → WeakDerivatives`.
- **Lean setup**: only the main theorem remains as `sorry`.
  The inverse-Laplacian series definition is unchanged; its convergence,
  coefficient formula and mean-zero output are proved.
  `exists_hasL0_invLap` is proved for every input, using component-weighted
  coefficients and perpendicular shifts.
  `HasL0.zero`, `.add`, `.sub`, `.smul`, and
  `hasL_iff_isEigenSolution` are proved; reduction also holds at `λ = 0`.
  The first- and second-derivative Fourier relations are now defined.
  `exists_fourierPartial_invLap` and `exists_fourierSecondPartial_invLap`
  prove their L2 existence by the bounds `|k_j|, |k_i k_j| ≤ |k|²`.
  `hasFourierPartial_iff_second` checks iteration, and
  `hasFourierLaplacian_of_second` checks that the pure second partials sum
  to the Laplacian. `hasFourierLaplacian_invLap` proves the Poisson equation
  for mean-zero input.
  The user reviewed the original setup definitions on 2026-10-13;
  AI review of the new derivative relations is complete. Temporary Lean
  examples verify their action on every character, uniqueness of each
  output, the x/y indexing, and the integration-by-parts pairing sign.
  No definition changes were needed; docstrings now spell out partial-operator
  domains and the intermediate-first-derivative hypothesis. Human sign-off
  remains separate. The review is recorded next to `def:fourier-derivatives`.
- **Weak derivatives**: `WeakDerivatives.lean` has no `sorry`.
  `hasFourierPartial_iff_smoothWeakPartial` proves the bilinear distributional
  identity against every smooth periodic test pair; the stronger
  `hasFourierPartial_iff_weakPartial` allows every continuous test with a
  continuous classical derivative in the tested coordinate.
  Classical tests are continuous functions paired with a continuous derivative,
  certified by `HasDerivAt` on every real coordinate line. Smoothness means
  `ContDiff ℝ ∞` of the periodic real lift (not `⊤`, which means analytic in
  this Mathlib). This module does not define a derivative operator on all
  continuous torus functions or a general derivative-descent theorem.
  The proof uses periodic one-dimensional integration by parts, Fubini, and
  Hilbert-basis Parseval, avoiding derivative-convergent test approximations.
  AI definition review checked coordinate indexing, period, regularity order,
  and the bilinear sign; human sign-off remains separate.
- **Validation**: `lake build` and `just web` pass including `WeakDerivatives`,
  with only the main-theorem `sorry` warning (and the usual missing image
  converters for the website). LSP diagnostics for the new module are clean.
  Axiom checks of both weak-partial equivalences and the classical coefficient
  bridge use only `propext`, `Classical.choice`, and `Quot.sound` (no `sorryAx`),
  as do the earlier transport, reduction, inverse-Laplacian coefficient,
  second-derivative existence and Poisson results. Temporary Lean examples
  check that inverse-Laplacian first derivatives now satisfy smooth-test weak
  identities, and that every weak first derivative has mean zero.
  Native Pi MCP integration works and diagnostics reuse the Lean server.
  Reinstalling Lean 4.34.1 repaired stale Nix paths after the VM update.
- **Reworked manuscript** (`manuscript.tex`): front matter and the
  introduction up to the main theorem. The other sections are placeholders.
  Neither manuscript was changed in the setup/Fourier/weak-derivative work.

## Decisions

Each points to where the decision is recorded in detail.

- `L²` model (2026-10-13, as a first attempt): `Lp` on `Angle × Angle`, `L₀`
  as a relation tested against characters, `Δ⁻¹` as a series of characters.
  Remark "Lean model" in `setup.tex`.
- Fourier transport: use the scaling homeomorphism to transport continuous
  monomial density and orthogonality, then construct the physical Hilbert
  basis directly. No separate L2 scaling equivalence is needed. `Fourier.lean`
  and the Fourier-basis proof in `setup.tex`.
- Derivative scope: use relations defined by first/second Fourier multipliers
  and the Laplace multiplier, in keeping with the Sobolev-free setup chapter.
  First partials now agree with arbitrary smooth-test weak differentiation;
  use periodic integration by parts and Parseval rather than a new smooth-test
  approximation theory. Test pairs carry their certified classical derivatives.
  Second-order, Laplace and transport bridges remain deferred.
  `def:fourier-derivatives`, `def:classical-tests` and
  `lem:partial-weak-equivalence` in `setup.tex`.
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
