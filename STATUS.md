# Status

A snapshot of where the project stands. Rewrite it at the end of each work
session instead of appending to it; the history is in `git log`.

Not repeated here: progress per node is in the blueprint's dependency graph
(`\leanok`), and open mathematical problems are in
`blueprint/src/chapters/notes.tex`.

## Statement-review corrections

The three issues found in the even–even review have been corrected in Lean
and the blueprint; their analytic proofs remain admitted.

- Replaced the false global `norm_fderiv_timeCoord_le` with
  `norm_fderiv_quarterTimeCoord_le` on the four separately recentered
  quarter-orbit patches, using `quarterTimeCoord k p = timeCoord (R^(3k) p)`.
  The global time's local smoothness off its cut is now the separate
  `contDiffAt_timeCoord` statement in `lem:orbit-coordinates`.
  `lem:coarea` needs only this local regularity, not the near-separatrix
  uniform estimate. The level-derivative proof sketch uses variational
  equations instead of trying to infer second derivatives from a
  first-gradient bound. The counterexample to the former global claim is
  retained at `lem:orbit-coordinate-gradients`.
- `norm_canonicalProfile_le_exp` now has complex endpoint parameters
  `cp cm`, with the exponent and bound constant still real.
- `absolutelyContinuous_trace_of_H2` now requires its returned gradient
  representative to be locally absolutely continuous on almost every
  transverse line. This pins down its trace and makes it compatible with
  other transverse ACL representatives. `exists_acl_trace` now quantifies
  its nonnegative estimate constant before the open set and functions,
  making it uniform with the rectangle and trace line fixed.
  Both trace statements explicitly assume positive rectangle width.
- Review axiom checks on thirteen representative proved results (weighted
  boundary calculus, smooth virials, orbit periodicity/minimality, odd
  Hardy, continuous representatives, lift Sobolev regularity, cutoff
  localization and the canonical ODE) have no `sorryAx` dependency. This
  does not validate the remaining admitted analytic results.

## Next steps

**Backwards even–even assembly is proved.** `even_even_character_exclusion`
and `even_even_exclusion` now have no `sorry` of their own. The proof combines
the a.e. truncated virial identity and boundary limits outside a single null
set, uses the canonical arc positivity, and exhausts the cell with nonnegative
truncated integrals. The endgame uses `f > 0` almost everywhere to deduce
`ω = 0` directly; it needs neither global bulk integrability nor a weak-gradient
constant-function theorem.

Proved without admissions: the null cosine diagonal, strict positivity of `f`
off it, zero density forcing zero vorticity, the measure/symmetry transfer from
the positive-cell lift to the torus, and a generic nonnegative exhaustion lemma.
The truncated virial statement now explicitly requires `λ ≠ 0`, includes
integrability on each truncated cell, uses `h = ε/2`, and separates the three
level integrals.

**The canonical boundary-form interface is now proved.**
`CanonicalBoundaryForm.lean` proves `canonicalArcForm_eq_flowBoundaryForm`
(`lem:canonical-arc-form`) with no admissions or additional hypotheses. It also
proves continuity of the canonical profile, pullback of a.e. statements under
`tanh`, the two a.e. weighted chain rules, and continuity of the first flow
jet (`lem:weighted-flow-derivatives`). The weighted-domain derivative of `z`
and the profile ODE first give a.e. differentiability of `g`; uniqueness of
derivatives identifies the first jet with `-iΩ` a.e. Continuity upgrades this
to pointwise equality, allowing differentiation once more to identify the
second jet. The original weighted trace-energy hypothesis is retained in the
API, although the equality of total integrals does not use it.

**The eigenfunction transport interface is now proved.**
`EigenfunctionTransport.lean` proves `ee_transport_traces`
(`lem:ee-transport-traces`) with no `sorry` of its own; it rests on the
admitted `isTransportPair_of_isEigenSolution`, `melnikov`, `pairing_limit`
and `lintegral_cellSquare_eq`. New blueprint nodes, all `\leanok`:
`lem:cell-neighbourhood` (the diagonal square `|a|,|b| < 3π/2` is a bounded
invariant open union of orbits: its edges are barriers by scalar ODE
uniqueness, so no flow saturation is needed), `lem:lift-representatives`
(`ψ = ψ̃` a.e. on `ℝ²`, `ψ̃` has the rotation character pointwise),
`lem:transport-pair-continuous` (`(ω, ψ̃)` is a transport pair),
`lem:flow-continuity` (joint continuity of the flow from Gronwall, without
differentiable dependence on data) and `lem:level-integral-congr` (a.e.
equal measurable functions have equal level integrals on a.e. level).
`#print axioms`: the new helpers use only `propext`, `Classical.choice`,
`Quot.sound`, except `ae_levelIntegral_congr` (admitted
`lintegral_cellSquare_eq`) and `isTransportPair_contStream` (admitted
`isTransportPair_of_isEigenSolution`). The even–even hypothesis of
`ee_transport_traces` is unused (only the rotation character is needed).
The admitted `ee_transport_traces` copy was removed from `EvenEven.lean`,
which now imports the new module.

**`ee_neumann` is proved** (`lem:ee-neumann`), using only `propext`,
`Classical.choice`, `Quot.sound`. The new node `lem:stream-derivative-parities`
(symmetry chapter) is the chain rule `∂ⱼΔ⁻¹T* = σ T*∂ⱼ'Δ⁻¹` for the
reflections, proved on Fourier coefficients
(`CharacterSymmetry.streamPartial_action`; `SymmetryL2.lean` now imports
`Derivatives.lean`), with its sector form in `Sectors.lean`. The pointwise
algebra was also checked by hand: both reflections reverse `ψₙ` and fix `ψₜ`.

**`lem:virial-l2` digested on paper (2026-10-15).** The manuscript's `U_t`
argument looks correct (its key formulas were rederived), but needs the flow
of `W`, its Jacobian and `U_t` theory. Proposed replacement (digest note
`rem:virial-transversal-mollifier` in `virial.tex`): for `W` supported in a
compact sub-annulus of the cell, (1) the exact identity
`⟨Va,Ha⟩ - ⟨VHa,a⟩ = λ(⟨Vψ,ω⟩ - ⟨Vω,ψ⟩)` for any linear `V` replaces the
`A = I + Δ⁻¹` machinery; (2) in action-angle coordinates `(h, θ)`,
`L₀ = S(h)⁻¹∂_θ`, so mollifying in `h` gives `‖[H,J_ε]a‖ = O(ε)` while
`‖DJ_ε a‖ = o(1/ε)`; (3) `V = J_ε† D J_ε` and the limit. Separately, the
center can be cut out of `lem:ee-truncated-virial` (inner boundary terms
vanish along a sequence; remark in `even_even.tex`), so the even–even graph
would no longer need `lem:normal-field-center`, `lem:H-selfadjoint` or
`C^{2,1}` fields. New infrastructure needed: a `C¹` action-angle chart on a
compact annulus (from the explicit `(h, t)` map and the inverse function
theorem). **Decision pending:** restate `lem:virial-l2`/`virial_l2` for
annulus-supported smooth fields and restructure the proof of
`lem:ee-truncated-virial` accordingly. Odd–odd (weighted analogue) not yet
examined.

**Next:** that decision, then formalize. Remaining direct even–even inputs:
`ee_boundary_regularity`, `ee_gradient_traces`, `ee_truncated_virial`, and
the transport inputs (`melnikov`, `pairing_limit`,
`isTransportPair_of_isEigenSolution`). The sector exclusion still depends on
these admitted analytic results.

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
   `VirialAlgebra.lean`. Integration by parts on the lift
   (`LiftIntegration.lean`: `def:square-integral`,
   `lem:square-integral-partial`, `lem:square-pairing`), skew-symmetry of `D`
   and `L₀` (`lem:commutator-algebra`, restated), and the first form of the
   smooth virial identity (`lem:virial-smooth`, `VirialSmooth.lean`) are
   done, and so is `lem:virial-smooth-quadratic` (`VirialQuadratic.lean`; all
   integrations by parts via skew-symmetry of `∂ₓ`, `∂_y`). The next virial
   step is `lem:virial-l2`, the identity on the original `L²` domain, which
   needs the analytic setup (self-adjointness, `H²` regularity of `ψ`) and
   should be digested first. `H^s(𝕋²)` is now defined through Fourier
   coefficients (`SobolevTorus.lean`, `def:sobolev-torus`,
   `lem:sobolev-torus-basic`), with `lem:elliptic-torus` proved: `Δ⁻¹`
   gains two derivatives (constant 4), `∂_j` loses one, and `Δ⁻¹ω ∈ H²` for
   every `ω ∈ L²`. Linked to the lift calculus in `LiftTorus.lean`
   (`def:torus-of-lift`, `lem:lift-torus`, `lem:lift-sobolev`): periodic
   lifts descend to the torus, classical partials are the Fourier partials,
   periodic `Cᵏ` lifts are in `Hᵏ`, and lift integrals/pairings are torus
   integrals/`L²` inner products. Not done: `lem:sobolev-embedding`.
   Local Sobolev spaces (`SobolevLocal.lean`): `def:sobolev-local` split into
   `def:weak-derivative-local`, `def:sobolev-local` (`Hᵏ(U)`, `Hᵏ_loc`,
   weighted) and `def:sobolev-fractional` (Mathlib's `MemSobolev`). Proved:
   `lem:weak-derivative-basic`, `lem:weak-derivative-classical` (`Cᵏ ⊆ Hᵏ_loc`),
   `lem:localization-cutoff` (`χu ∈ Hᵏ(ℝ²)`). Open: `lem:local-to-global`, the
   `ℝ² ↔ 𝕋²` unfolding (periodized test functions); then the assumption file
   for `lem:elliptic-local`, `lem:traces`, `lem:coarea`, `lem:odd-hardy`.
   Remaining definitions (user's focus, 2026-10-15): `def:cells` is now
   definitions only and formalized (`Cells.lean`), with new proved lemmas
   `lem:separatrix-lines`, `lem:dipole-critical-points`, `lem:cell-square`;
   `lem:diagonal-calculus` (`dx dy = 2 da db`, `∂_a, ∂_b`, `Δ` in `a, b`) is
   proved (`DiagonalCalculus.lean`). `def:h2-interval` and `def:h1-periodic` are formalized too
   (`IntervalH1.lean`, with `lem:interval-h2-periodic`). `def:period` is
   now definitions only (`Period.lean`: `L`, `S = 8L`, `b = 2π/S`), with
   `lem:period-integral` proved (second formula by substitution, positivity)
   and `lem:period-orbit` proved (`DipoleFlow.lean`): global flows of bounded
   Lipschitz fields (`lem:global-flow`), the dipole flow (`def:dipole-flow`,
   `lem:dipole-velocity`, `lem:dipole-flow`: uniqueness, group property,
   conservation of `Ψ`, time reversal by reflections), and for the orbit
   `γ_h`: level and square, diagonal at `±L(h)`, quarter rotation, minimal
   period `S(h)`. The manuscript's `dt = -da/√(cos²a-h²)` needed a continuity
   argument (`b > 0` up to `L(h)`); noted in the remark after the lemma,
   together with the clash of `b` (coordinate) and `b(h)` (frequency).
   `def:transport-pair` is formalized (`Transport.lean`) on the lift: open
   unions of orbits, weak `L₀` (`∫ g L₀φ = -∫ hφ`), transport pairs and the
   transport unknown, with `lem:transport-unknown` proved. Modelling choice
   (remark after the node): `U` is a subset of `ℝ²`, bounded in the
   applications, instead of the torus. `lem:transport-pair-eigen` (eigenfunctions give
   pairs) is stated, waiting for `lem:local-to-global`.
   `def:canonical-profile` is formalized (`CanonicalProfile.lean`) by the
   formula `Ω(s) = e^{iλs} ∫_s^∞ g' e^{-iλt}` instead of "the decaying
   solution"; `lem:canonical-profile-ode` is proved (Lebesgue
   differentiation: `Ω' = iλΩ - g'`, `Pz = -Ω`, `(P - λ)z = g` a.e.; decay at
   `+∞`; decay at `-∞` iff Melnikov, then the left formula).
   `lem:canonical-profile` keeps uniqueness and the decay rates. With this all
   definitions in the even–even graph are in Lean. `lem:odd-hardy` is
   restated with the Gagliardo seminorm (`def:gagliardo`) and proved
   (`OddHardy.lean`) by a new pointwise argument (parallelogram law, no
   integrability or compact support needed; digest note). The link to
   `H^{1/2}` is the new stated node `lem:sobolev-fractional-gagliardo`
   (Plancherel), used in `lem:ee-gradient-traces`; whether `lem:traces`
   should give the Gagliardo bound directly is open (notes).
   Stating the remaining even–even lemmas (plan agreed 2026-10-15): level
   curves are handled through orbit coordinates `(h, t) ↦ γ_h(t)` and
   restrictions to almost every level (Fubini), not trace operators.
   Batch A (stated with `sorry`, no new infrastructure) is done:
   `lem:period` (asymptotics checked numerically), `lem:good-windows`
   (explicit constant `2 sin(π/12)`), `lem:canonical-profile` (decay rate
   now a hypothesis on `g`, weighted bound with constant 1),
   `lem:sobolev-embedding`, `lem:sobolev-fractional-gagliardo` (iff only),
   `lem:transport-pair-eigen` (with `liftL2`), `lem:melnikov` (hypotheses of
   the section made explicit). Batch B definitions are done:
   `def:stream-derivatives` (`∂ⱼΔ⁻¹`, `∂ᵢ∂ⱼΔ⁻¹` as bounded multipliers),
   `def:continuous-representative` with `lem:continuous-representative`
   proved (`H²` Fourier series converge absolutely; `ψ̃` continuous),
   `def:orbit-coordinates` (explicit inverse `h = Ψ/2`, flow time `t` from
   `orbitTime`; avoids smooth dependence of ODE flows, not in Mathlib) with
   `lem:orbit-coordinates` stated (bijection, `dx dy = 2 dh dt`, a.e. level
   restrictions; `OrbitCoordinates.lean`), `def:level-integral`,
   `def:normal-tangent`. Batch B statements done (2026-10-15):
   `lem:corner-coordinates` proved (with `def:corner-chart`);
   `lem:orbit-comparison` split into closeness, saddle distance, level
   derivatives, coordinate gradients, time integrals (all checked
   numerically, `def:cell-arcs` for arcs and `d`); stated: `lem:coarea`
   (now only `H¹` along a.e. orbit), `lem:resonant-vanishing` (continuity of
   `f` a hypothesis), `lem:pairing-limit`, `lem:ee-neumann` (restated as
   reflection parity of `ψₙ`, `ψₜ`), `lem:ee-truncated-virial`,
   `lem:ee-gradient-traces` (limits along levels outside a null set; arc
   term via `ψ̃ ∘ γ`), `lem:ee-boundary-regularity` (`def:stream-lifts`).
   The smooth cutoff algebra for the truncated virial identity has now
   been independently rederived: its signs and factor `2 - ε` are correct
   (remark at the node). The original-domain justification and the
   almost-every-level limit remain admitted. Batch C stated: `lem:normal-field-center`
   (series expansion checked; `C^{2,1}`, `C^{1,1}` are sharp),
   `lem:local-to-global`, `lem:traces` (restated as absolute continuity on
   lines and line traces in diagonal coordinates, Gagliardo bound included,
   so `lem:sobolev-fractional-gagliardo` left the even–even graph),
   `lem:virial-l2` (`VirialL2.lean`), and `lem:H-selfadjoint` with
   `def:transport-operator` (`TransportOperator.lean`: `H = -iL₀` as a
   `LinearPMap`, `IsSelfAdjoint`, `HasCore` of smooth functions, the flow
   on the torus measure preserving, generator via difference quotients;
   Mathlib has no Stone's theorem). Every node of the even–even graph now
   has a Lean statement. The least verified step is the flow group `U_t` of
   the cut-off normal field `W` in the proof of `lem:virial-l2` (needs the
   Jacobian of the flow of `W`; possibly explicit in orbit coordinates;
   digest note and notes item). Other open
   definitions: `def:numerator`, odd–odd and mixed, and
   `def:bernstein`. Noticed: `def:numerator` contains a claim (variation of
   constants), to split when the transport chapter is digested.
   Also done (2026-10-15):
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
  `lem:sector-projections` and `lem:stream-sector` (used by
  `lem:dd-orthogonality`), the second mixed sector is the new
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
  swapping. The sector exclusion statements are linked to Lean. Even–even
  now has a complete assembly proof from admitted analytic inputs; odd–odd
  and mixed still have admitted exclusion proofs.
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
  `main` from the three sector exclusions. Even–even now has an assembly
  proof from admitted analytic inputs; odd–odd and mixed remain admitted.
- **Even–even boundary calculus** (`BoundaryForm.lean`): the finite-interval
  quadratic form takes explicit value/first/second derivative functions, so
  it can later accommodate weak derivatives. `BoundaryJet` is the classical
  domain. Proved the pointwise flux identity, completion of squares including
  the endpoint correction, the zero-endpoint sum of squares, affine splitting,
  and positivity for equal or opposite endpoints, for every real λ. Dedicated
  classical blueprint nodes are `\leanok` in statement and proof; weighted
  H¹ positivity and the flow-time coordinate change are now formalized too. No new `sorry`s. The three main boundary theorems use only
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
  No normed/quotient Sobolev space, weak-test bridge or density yet.
  Ordinary interval H² and periodic H¹ are now defined in `IntervalH1.lean`.
  The weighted second-order domain is implemented separately, as below.
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
  completion/positivity are now proved in `WeightedBoundaryForm.lean`. The example
  `F(x)=(1-x)^(3/2)` distinguishes the domain from ordinary H² by explicit
  differentiation/integration, not a Lean-formalized counterexample.
  Boundary-integrand integrability is now proved in
  `WeightedBoundaryForm.lean`. The distributional weak-test bridge,
  density and continuity results remain pending (density is no longer
  needed for positivity). Classical inclusion,
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
- **Validation**: full Lean build and `just web` pass after proving the
  even–even Neumann parities; `just graph thm:ee-exclusion` regenerates
  its graph (135 nodes). All 640 blueprint Lean references resolve without
  duplicates, and every `\uses` label exists. There are now 48 admitted
  declarations.
  `CanonicalBoundaryForm.lean` and `EigenfunctionTransport.lean` have no
  warnings; `EvenEven.lean` has only its three admitted-input warnings. Axiom checks on the canonical arc identity
  and all five new helpers use only `propext`, `Classical.choice` and
  `Quot.sound`. The earlier six endgame foundations have the same axiom
  status. Arc positivity, both exclusion proofs, and `main` still depend
  on `sorryAx` through their other named analytic inputs. Earlier checks on
  weighted boundary calculus and smooth virials remain valid. The web build
  has only the usual missing image-converter messages.
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
