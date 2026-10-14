# Status

A snapshot of where the project stands. Rewrite it at the end of each work
session instead of appending to it; the history is in `git log`.

Not repeated here: progress per node is in the blueprint's dependency graph
(`\leanok`), and open mathematical problems are in
`blueprint/src/chapters/notes.tex`.

## Next steps

1. Review the newly added L² symmetry/sector Lean layer: pullbacks for
   `S₁`, `S₂`, `R`, commutation with `Δ⁻¹` and `L₀`, sector projections,
   sector preservation of the eigenvalue equation, and assembly of `main` from
   the three sector exclusions. Lean checked the proofs, but human sign-off on
   the statements is still needed.
2. The three sector exclusion theorems are now Lean statements with `sorry`:
   `even_even_exclusion`, `odd_odd_exclusion`, and `mixed_exclusion`. The main
   theorem has no local `sorry`, but it depends on these three admitted
   exclusions.
3. The user had paused starting the even–even sector. When requested, digest it
   end to end: check identities with SymPy, explain the mechanism, write digest
   notes, and formalize the algebraic nodes.
4. Soon after: assess the largest gap, the odd–odd renormalized virial identity
   (`prop:dd-virial`). If correctness of the result is the priority, do this
   before 3.

## Current state

- **Blueprint**: all 13 chapters drafted, with the Sobolev tiers in place.
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
