# Status

A snapshot of where the project stands. Rewrite it at the end of each work
session instead of appending to it; the history is in `git log`.

Not repeated here: progress per node is in the blueprint's dependency graph
(`\leanok`), and open mathematical problems are in
`blueprint/src/chapters/notes.tex`.

## Next steps

1. Human sign-off on the Lean statements of the setup, symmetry and sector
   layer. On 2026-10-14 an agent checked that they agree with the blueprint
   and fixed the blueprint where they did not (see "Current state").
2. Lean follow-ups from that review, not done yet:
   - Lean lemmas for the two new non-`\leanok` nodes: `lem:sector-projections`
     (the `P_ε` are commuting orthogonal projections, identity on their sector)
     and `lem:stream-sector` (`ψ` has the parities of `ω`; short from
     `invLap_commute`).
   - `exists_hasL0_iff_summable` (the blueprint defines `L₀g ∈ L²` by square
     summability, `Dom` by `∃ h, HasL0 g h`) and uniqueness `HasL0.unique`.
   - Restructuring: move `fourierCoeff_add/smul`, `char_ne_zero`,
     `char_add_point`, `char_neg_point` to `TorusL2.lean`; `invLap_add/smul`
     and `IsEigenSolution.add/smul` to `Setup.lean`; move the Fourier-multiplier
     derivative section of `Setup.lean` (not on the import path of `main`)
     next to `WeakDerivatives.lean`; consider a general Fourier-multiplier
     operator `L2 →L[ℂ] L2` (gives linearity and continuity of `invLap`); drop
     the derivable fields `zero_iff` and `phase_ne_zero` of
     `CharacterSymmetry`; one lemma for `(2π : ℂ) ≠ 0`; fix stale module
     docstrings in `Symmetry.lean` and `Setup.lean`. `AGENTS.md` still says
     one module per chapter, which no longer holds; update it or use
     subdirectories.
3. The user had paused starting the even–even sector. When requested, digest it
   end to end: check identities with SymPy, explain the mechanism, write digest
   notes, and formalize the algebraic nodes.
4. Soon after: assess the largest gap, the odd–odd renormalized virial identity
   (`prop:dd-virial`). If correctness of the result is the priority, do this
   before 3.

## Current state

- **Blueprint**: all 13 chapters drafted, with the Sobolev tiers in place.
  Blueprint/Lean consistency review (2026-10-14): definition nodes now contain
  only definitions (`lem:torus-fourier-basis` and
  `lem:fourier-derivative-composition` split off), the over-claimed
  `lem:sector-reduction` was split into a proved part and the new nodes
  `lem:sector-projections` and `lem:stream-sector` (used by `lem:ee-neumann`
  and `lem:dd-orthogonality`), the second mixed sector is the new
  `cor:mixed-other-exclusion`, no Lean name is listed in two nodes, and
  proofs done in Lean carry `\leanok` (including `thm:main`, whose proof has
  no local `sorry`; convention recorded in `AGENTS.md`).
  `intro.tex` and `blueprint/README.md` do not mention the tiers yet. Setup has
  separate proved nodes for integral characterizations, Fourier
  basis/reconstruction, inverse-Laplacian convergence and derivatives,
  transport Fourier algebra, weak-transport linearity, stream-function
  transport, reduction, and the first-partial all-smooth-test equivalence. The
  transport, second-order and Laplace arbitrary-test bridges remain deferred.
  Symmetry now has Lean annotations for the L² symmetry commutation layer,
  sector projections/reconstruction, sector preservation, and mixed-sector
  swapping. The sector exclusion theorem statements in the even–even, odd–odd,
  and mixed chapters are linked to their Lean declarations, but their proofs
  are still mathematical placeholders/admissions.
- **Lean foundations**: `Symmetry.lean` proves pointwise torus reflections,
  rotation and reflection algebra. `TorusL2.lean` holds the measure/L2/character
  foundations and proves integrability, integral formulas for Fourier
  coefficients, conjugation/zero-character identities, and
  `meanZero_iff_integral_eq_zero`. `Fourier.lean` proves the normalized Hilbert
  basis `(2π)⁻¹ e_k`, coordinates `2π ĝ_k`, reconstruction, Parseval,
  uniqueness and existence for square-summable coefficients, and convergence
  with exact coefficients for arbitrary square-summable Fourier series. The
  Lean import chain now continues through `Setup`, `SymmetryL2`, `Sectors`, the
  three sector files, and `Main`.
- **Lean setup and weak derivatives**: `Setup.lean` no longer contains the main
  theorem; it contains the Fourier model, inverse Laplacian, derivative
  relations, domain, `HasL`, eigenvalue problem, and reduction. The
  inverse-Laplacian convergence/coefficient/mean-zero results, `exists_hasL0_invLap`,
  `HasL0` linearity, `hasL_iff_isEigenSolution`, Fourier derivative existence,
  and Poisson result are proved. `WeakDerivatives.lean` has no `sorry`; the
  first-partial Fourier relation is proved equivalent to smooth-test weak
  differentiation and to the stronger classical-test formulation described in
  that module.
- **Lean symmetries and sectors**: `SymmetryL2.lean` proves measure-preserving
  L² pullbacks for `S₁`, `S₂`, and `R`, their action on characters and
  transport characters, preservation of mean zero, commutation with `Δ⁻¹` and
  `L₀`, preservation of `IsEigenSolution`, and the L² reflection/rotation
  algebra. `Sectors.lean` defines `InSector` and `sectorProjection`, proves the
  four projected pieces lie in the desired parities, reconstruct the original
  function, preserve the eigenvalue equation, and that rotation swaps parities.
  `Mixed.lean` proves the second mixed sector from the first by rotation.
  `Main.lean` proves `main` from reduction, sector decomposition, and the three
  admitted sector exclusions.
- **Validation**: `lake build` passes. `just web` passes, with only the usual
  missing image-converter messages from plasTeX. Warnings are the three sector
  exclusion `sorry`s. Axiom checks: `IsEigenSolution.sectorProjection` uses only
  `propext`, `Classical.choice`, and `Quot.sound`; `main` and
  `mixed_other_exclusion` also depend on `sorryAx`, exactly through the admitted
  sector exclusions.
- **Reworked manuscript** (`manuscript.tex`): front matter and the introduction
  up to the main theorem. The other sections are placeholders. Neither
  manuscript was changed in the setup/Fourier/weak-derivative/symmetry-sector
  work.

## Decisions

Each points to where the decision is recorded in detail.

- `L²` model (2026-10-13, as a first attempt): `Lp` on `Angle × Angle`, `L₀`
  as a relation tested against characters, `Δ⁻¹` as a series of characters.
  Remark "Lean model" in `setup.tex`.
- Fourier transport: use the scaling homeomorphism to transport continuous
  monomial density and orthogonality, then construct the physical Hilbert basis
  directly. No separate L2 scaling equivalence is needed. `Fourier.lean` and the
  Fourier-basis proof in `setup.tex`.
- Derivative scope: use relations defined by first/second Fourier multipliers
  and the Laplace multiplier, in keeping with the Sobolev-free setup chapter.
  First partials now agree with arbitrary smooth-test weak differentiation; use
  periodic integration by parts and Parseval rather than a new smooth-test
  approximation theory. Test pairs carry their certified classical derivatives.
  Second-order, Laplace and transport bridges remain deferred.
  `def:fourier-derivatives`, `def:classical-tests` and
  `lem:partial-weak-equivalence` in `setup.tex`.
- Sector assembly: keep the analytic sector exclusions as separate top-level
  theorems (`EvenEven.lean`, `OddOdd.lean`, `Mixed.lean`) and prove the main
  theorem in `Main.lean` from sector projections. This makes the remaining
  analytic gaps explicit while allowing the algebraic reduction layer to be
  checked.
- Notation (2026-10-13): the mean-zero space is `X` (not `L^2_0`, which
  typesets like `L_0^2`); the velocity field `(sin y, −sin x)` is `Y`. Remark
  after `def:torus`.
- The main theorem is stated for real `λ`; non-real eigenvalues are excluded by
  an elementary argument in a remark (2026-10-13). Remark "Non-real eigenvalues"
  in `setup.tex`.
- `eigenvalues.tex` stays unchanged as the reference; `manuscript.tex` is
  written as we go (2026-10-13). `AGENTS.md`.

## Not set up yet

Needs a GitHub remote first (there is none): `checkdecls` in the lakefile, the
`\home`/`\github`/`\dochome` links in `blueprint/src/web.tex`, `blueprint: true`
in the docgen CI step, and the GitHub settings described in the top-level
`README.md`.
