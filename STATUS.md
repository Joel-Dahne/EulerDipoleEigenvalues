# Status

A snapshot of where the project stands. Rewrite it at the end of each work
session instead of appending to it; the history is in `git log`.

Not repeated here: progress per node is in the blueprint's dependency graph
(`\leanok`), and open mathematical problems are in
`blueprint/src/chapters/notes.tex`.

## Next steps

1. Human sign-off on the Lean statements of the setup, symmetry and sector
   layer. On 2026-10-14 an agent checked that they agree with the blueprint
   and fixed the blueprint where they did not (see "Current state"). Also
   review the bounded-interval H¹ representative/derivative model,
   endpoint traces and the new weighted boundary-domain statements.
2. Lean lemma for `lem:sector-projections` (the `P_ε` are commuting
   orthogonal projections, the identity on their sector); it has no
   dependents. `lem:stream-sector` is done (`InSector.invLap`).
3. Cheap algebra (user's choice on 2026-10-15 while digesting is paused).
   Done: `lem:dipole-identities` and `lem:normal-field-algebra` on the real
   lift (`DipoleCalculus.lean`, `NormalField.lean`), with `def:lift-operators`
   and `def:adapted-field` now the Lie-bracket form `[Y,W] = fY`; the
   half-density generator is the separate `def:half-density-generator`.
   Method: identities are rational in sin/cos; SymPy (Gröbner division in lex
   order) gives the cofactors for `linear_combination` with `sin²+cos²=1` and
   `ρ²·ρ⁻² = 1`. Also done: `lem:lift-calculus` (product rules, symmetric
   mixed partials) and the new node `lem:commutator-pointwise`
   (`[L₀, W·∇] = f L₀`, `L₀ div W = L₀ f`, `[L₀, D] = ½(f L₀ + L₀ f)`) in
   `VirialAlgebra.lean`. Left in `lem:commutator-algebra`: skew-symmetry of
   `D` and the `H = -iL₀` form; these and `lem:virial-smooth` need
   integration by parts on the torus. Also done (2026-10-15):
   `lem:ee-density`, `def:separatrix-arc`/`lem:separatrix-arc`
   (`SeparatrixArc.lean`), and `def:boundary-form`/`lem:boundary-form-xi`
   (`FlowBoundaryForm.lean`, change of variables `ξ = tanh s`), which makes
   `lem:ee-trace-positivity` `\leanok` in the manuscript's flow-time form.
4. Even–even. Boundary positivity on the weighted domain is now proved in
   Lean (2026-10-15, `WeightedBoundaryForm.lean`), by exhausting (-1,1)
   with interior intervals instead of cutoff + mollification + density
   (digest note after `lem:weighted-boundary-positivity`); with
   `lem:boundary-form-xi` now formalized, `lem:ee-trace-positivity` is
   `\leanok` too. The new nodes
   `lem:l2-endpoint-liminf`, `lem:boundary-flux`,
   `lem:weighted-boundary-integrable`, `lem:weighted-completion`,
   `lem:weighted-affine-splitting` and `lem:weighted-boundary-positivity`
   are `\leanok` in statement and proof, using only `propext`,
   `Classical.choice`, `Quot.sound`. The now-unused cutoff/zero-extension
   modules (`BoundaryCutoff*.lean`,
   `IntervalZeroExtension.lean`, layer estimates) and their blueprint
   subsection are kept as infrastructure for now (decision 2026-10-15; noted
   in the module docstrings). Later: restructure `even_even.tex`
   (generic interval material to `analysis.tex`, remove status chatter from
   nodes). Remaining even–even inputs: `lem:ee-boundary-regularity` and
   the trace and transport inputs, which remain unverified.
   Lean cleanups found in the 2026-10-15 review (none done yet): shared
   "locally AC with a.e. derivative" predicate under `HasIntervalH1` and
   `HasWeightedBoundaryH2`; a `HasIntervalH10` structure for the repeated
   zero-trace hypothesis pair; merge left/right duplicates in
   `IntervalH1Estimates.lean`; move general AC/MemLp utilities to one module
   with Mathlib-style names; a `@[fun_prop]` lemma for the weight; rename
   `BoundaryJet.weighted_extension_eq`; drop status claims from docstrings.
5. Soon after: assess the largest gap, the odd–odd renormalized virial identity
   (`prop:dd-virial`). If correctness of the result is the priority, do this
   before 4.

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
- **Lean foundations** (`TorusL2.lean`, `Fourier.lean`): measure, `L²`,
  characters, Fourier coefficients and their linearity, integral formulas,
  mean zero; the Hilbert basis `(2π)⁻¹ e_k`, reconstruction, Parseval,
  uniqueness and existence for square-summable coefficients; bounded Fourier
  multipliers `fourierMultiplier : L2 →L[ℂ] L2`.
- **Lean setup** (`Setup.lean`, `Derivatives.lean`): `Δ⁻¹` is the multiplier
  `invLapSymbol`, hence a continuous linear map of norm at most one. `L₀` is
  the character-tested relation `HasL0`, with the Fourier formula
  `transportCoeff`, uniqueness, and `L₀g ∈ L²` iff `transportCoeff g` is
  square summable. Domain, `HasL`, `IsEigenSolution` (a linear subspace),
  `L₀Δ⁻¹ω ∈ L²`, reduction. `Derivatives.lean`: Fourier-defined derivative
  relations, derivatives of `ψ` up to order two (as multipliers),
  `Δψ = ω`, and equivalence of first partials with smooth-test and
  classical-test weak differentiation.
- **Lean symmetries and sectors** (`Symmetry.lean`, `SymmetryL2.lean`,
  `Sectors.lean`): pointwise maps and their algebra; `CharacterSymmetry`
  packages a measure-preserving map with its action on characters and on
  `L₀e_k`, from which preservation of mean zero, commutation with `Δ⁻¹` and
  `L₀`, and invariance of the eigenvalue problem follow; `reflect₁`,
  `reflect₂`, `rotate` are its instances. Sector projections, their parities
  and sum, invariance of solutions, and the rotation swap of parities.
  Rotation characters: lifted `R² = Ic = S₁S₂` to L²; proved involutivity on
  both equal-parity sectors, defined `(g + κ R*g)/2`, proved character and
  sector membership, reconstruction, zero intersection, and preservation of
  eigenfunctions at the same λ. `IsEigenSolution.rotation_decomposition`
  packages the full decomposition. `lem:rotation-characters` is now `\leanok`
  in statement and proof; no new `sorry`s. Its decomposition, involutivity and
  disjointness proofs use only `propext`, `Classical.choice`, and `Quot.sound`.
  `Mixed.lean` gets the second mixed sector by rotation; `Main.lean` proves
  `main` from the three admitted sector exclusions.
- **Even–even boundary calculus** (`BoundaryForm.lean`): the finite-interval
  quadratic form takes explicit value/first/second derivative functions, so
  it can later accommodate weak derivatives. `BoundaryJet` is the classical
  domain. Proved the pointwise flux identity, completion of squares including
  the endpoint correction, the zero-endpoint sum of squares, affine splitting,
  and positivity for equal or opposite endpoints, for every real λ. Dedicated
  classical blueprint nodes are `\leanok` in statement and proof; the original
  weighted H¹ positivity and flow-time coordinate-change nodes are not marked
  formalized. No new `sorry`s. The three main boundary theorems use only
  `propext`, `Classical.choice`, and `Quot.sound` (checked with `#print axioms`).
- **Interval H¹** (`IntervalH1.lean`): `HasIntervalH1 a b F D` records a
  locally absolutely continuous complex representative on `(a,b)`, the a.e.
  derivative `D`, and L² membership of both. `MemIntervalH1` existentially
  hides `D`; constants, addition and scalar multiplication are supported.
  Proved complex AC FTC, interior FTC, and the unique continuous extension
  `F((a+b)/2) + ∫ D`, independent of the derivative chosen. FTC also holds
  up to the endpoints for that extension. Raw endpoint values are unrestricted.
  `MemIntervalH10` uses zero traces; proved that its test is independent of
  the chosen derivative. Endpoint existence/uniqueness, closed-interval FTC
  and the zero-trace test use only `propext`, `Classical.choice`, `Quot.sound`.
  `IntervalH1Estimates.lean` now proves Cauchy–Schwarz bounds for increments
  of the continuous extension, pointwise zero-trace endpoint bounds, uniform
  bounds for rescaled layers, and their vanishing limits at both endpoints.
  These are separate proved blueprint nodes. The local derivative energy
  controls the cutoff errors directly, so `lem:trace-sos-extension` no longer
  depends on the still-unproved Hardy inequality. The increment bound,
  rescaled left-layer bound and both vanishing limits use only `propext`,
  `Classical.choice`, `Quot.sound` (checked with `#print axioms`).
  No normed/quotient Sobolev space, weak-test bridge, density, ordinary
  interval H² or periodic H¹ yet. The weighted second-order domain is now
  implemented separately, as described below.
  The former blueprint `def:h1-interval` is split into bounded H¹, the proved
  endpoint lemma, zero-trace H¹, and separate deferred H²/periodic definitions;
  dependent nodes and the Sobolev-tier guidance now distinguish these. The
  endpoint Hardy inequality is separately stated (not yet proved in Lean);
  it is not needed for the boundary-form cutoff step.
- **First-order zero extension** (`IntervalZeroExtension.lean`):
  `intervalZeroExtension a b F` keeps the interior values and is zero
  elsewhere, including at the endpoints. Proved global L¹/L² membership,
  compact support in `[a,b]`, preservation of the squared L² integral, and
  invariance of interval integrals between points of `[a,b]`. For zero-trace
  H¹ data, the zero extension is globally the primitive of the extended
  derivative, continuous on ℝ, absolutely continuous on every bounded
  interval and H¹ on every bounded interval with the correct a.e. derivative.
  The a.e. derivative statement alone needs no zero traces; the absolute
  continuity does. There are no new admissions or warnings. The primitive
  identity, H¹ extension and L² integral identity use only `propext`,
  `Classical.choice`, `Quot.sound` (checked with `#print axioms`). This is
  first-order only: applying it to the first derivative of a cutoff triple
  requires its own zero-trace/support checks, isolated in the still-unformalized
  `lem:boundary-cutoff-global-regularity`. Mollification and smooth density
  are not proved.
- **Weighted boundary domain** (`WeightedBoundary.lean`):
  `HasWeightedBoundaryH2 F D E` combines interval H¹ data `(F,D)`, local
  absolute continuity of `D` with a.e. derivative `E`, and L² membership of
  `(1-x²)E`. `MemWeightedBoundaryH2` existentially hides the derivatives.
  It imposes no global L² condition on `E` or endpoint traces of `D`.
  Proved addition, scalar multiplication, subtraction, affine membership
  and subtraction, inclusion of classical boundary jets with the correct
  value traces, and `D ∈ H¹(c,d)` for every interior subinterval (invert the
  weight, bounded away from zero there). The blueprint now gives the domain
  its own definition and three proved property nodes; full weighted
  completion/positivity are still unformalized. The example
  `F(x)=(1-x)^(3/2)` distinguishes the domain from ordinary H² by explicit
  differentiation/integration, not a Lean-formalized counterexample.
  The distributional weak-test bridge, boundary-integrand integrability,
  density and continuity results remain pending. Classical inclusion,
  local H¹ and affine subtraction use only `propext`, `Classical.choice`,
  `Quot.sound` (checked with `#print axioms`).
- **Boundary cutoffs** (`BoundaryCutoff.lean`, `BoundaryCutoffConstruction.lean`):
  proved preservation of the
  weighted domain under multiplication by a classical C² coefficient, the
  full first/second product rules, layer localization bounds, vanishing L²
  mass in shrinking layers, and vanishing rescaled mass for zero-trace H¹.
  `BoundaryCutoffControl` specifies compact interior support, the constant
  middle jet `(1,0,0)`, and uniform value/first/second derivative bounds.
  Proved the four cutoff error estimates and conditional convergence of all
  three graph components `(F,D,wE)`, with genuine compact interior support and
  zero value traces. All of this is without `sorry`; multiplier stability,
  conditional convergence and zero traces use only `propext`, `Classical.choice`,
  `Quot.sound` (checked with `#print axioms`). The construction module now
  bounds the first two smoothTransition derivatives by a fixed `B ≥ 1`,
  proves the explicit rescaled product's first/second derivative formulas,
  and verifies its support, flat middle jet, global smoothness and uniform
  constant `32*(B+1)^2`. The new blueprint definition and existence lemma
  are formalized, as is `lem:boundary-cutoff-approximation`: all three graph
  errors tend to zero for the explicit family, without a cutoff-family
  assumption. The products have compact interior support and zero value
  traces, but are not asserted smooth yet. Existence of the controlled
  family, its complex-valued smoothness and unconditional convergence use
  only `propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`).
  The second-order application of zero extension, interior mollification,
  full smooth density and boundary-form continuity remain pending. These
  results do not yet prove weighted boundary positivity.
- **Lean restructuring** (2026-10-14): the items from the review are done
  (lemmas moved to where they belong, derivative section moved to
  `Derivatives.lean`, renamed from `WeakDerivatives.lean`, multiplier
  operator, `transportCoeff`, derived `CharacterSymmetry` fields, stale
  docstrings, module layout in `AGENTS.md`). Not done, optional: a `Parity`
  type instead of `Bool` for sectors; merging the near-duplicate x/y proofs
  in `Derivatives.lean`.
- **Validation**: full `lake build` and `just web` pass after first-order zero extension,
  cutoff construction,
  conditional-cutoff and weighted-domain,
  endpoint-estimate, interval-H¹, boundary-form and rotation-character work;
  the only Lean warnings are the three existing sector exclusion `sorry`s.
  The interval/endpoint, boundary/weighted/cutoff, symmetry and sector modules have no warnings. The web build has only the usual missing image-converter messages
  from plasTeX. Every `\lean` name in the blueprint resolves. Axioms: `main` depends on `sorryAx` exactly through the admitted
  sector exclusions; `IsEigenSolution.sectorProjection`, `exists_hasL0_invLap`,
  `reflect₁_rotate` and `hasFourierPartial_iff_weakPartial` use only `propext`,
  `Classical.choice` and `Quot.sound`.
- **Reworked manuscript** (`manuscript.tex`): front matter and the introduction
  up to the main theorem. The other sections are placeholders. Neither
  manuscript was changed in the setup/Fourier/weak-derivative/symmetry-sector
  work.

## Decisions

Each points to where the decision is recorded in detail.

- `L²` model (2026-10-13, as a first attempt): `Lp` on `Angle × Angle`, `L₀`
  as a relation tested against characters, `Δ⁻¹` as a series of characters,
  built as a bounded Fourier multiplier (2026-10-14).
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
