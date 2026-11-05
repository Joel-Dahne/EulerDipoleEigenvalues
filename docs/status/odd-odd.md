# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` and its character-wise assembly have no `sorry` of their
own. In [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean), the Picone
current is also assembled without its own `sorry`, from explicit analytic
inputs, reaching ten admissions. Corrected boundary nonnegativity depends
only on zero-trace forcing energy and traces in
[CorrectedBoundaryForm.lean](../../NoEmbeddedEigenvalues/CorrectedBoundaryForm.lean).
Quotient existence in [OddOddQuotient.lean](../../NoEmbeddedEigenvalues/OddOddQuotient.lean)
has an assembled stream-H² stage and three remaining outer admissions.
The stream-H² assembly reaches nine existing local analytic admissions, so the
quotient domain has twelve transitive admissions. The current full odd–odd
audit finds twenty-five admissions. The bulk bound depends only on the two
residual-certificate inputs. This is not an admission-free exclusion.
The recursive statement pass covers the odd–odd dependency closure, including
the weighted spectral inputs. The zonal basis and weak mode pairings are proved.
Certificate tools and residual sign claims have statement/Mathlib markers. These markers are
neither a human compatibility review nor a proof audit.

The Bulk Picone bound (`lem:dd-bulk-picone`, `dd_bulk_picone`) now has no
`sorry` of its own: it adds `dd_bulk_gradient_bound` and
`dd_bulk_potential_bound`, using `80/27 - 5/2 = 25/54`. Both immediate
inputs now also have proofs without their own admissions. The gradient proof
uses the weighted-domain bridge, constrained Poincaré, matrix bound and finite
weighted integrals; the potential proof integrates the coefficient bound.
Their statements are unchanged. The weighted form-domain bridge
(`lem:dd-bulk-form-domain`) and ground-state/matrix bounds
(`lem:dd-ground-matrix-bounds`) are now transitively admission-free.
The matrix proof uses scalar polynomial inequalities and the normal/tangent
orthonormal frame, without a residual certificate. The domain proof uses
global C¹ regularity of the reciprocal ground state, including at the center,
and C¹ multiplication of lifted Fourier data. It does not use the supplied
H² or Picone-energy hypotheses; these remain in the common bulk interface.
The simplification is recorded in the Blueprint digest notes.

The non-certificate bulk route is admission-free. Weighted Poincaré
(`lem:zonal-poincare`) is proved with its original maximal `DDWeightedH1`
domain and a.e. central parity, without boundary traces, separate reflection
symmetries or weighted Sobolev density.
[Analysis/ZonalSpectral.lean](../../NoEmbeddedEigenvalues/Analysis/ZonalSpectral.lean)
assembles Parseval for the values, normalized gradient orthonormality from weak
mode pairings, odd-degree coefficient cancellation and Bessel. The exact
mean/variance and Cartesian-energy transport is applied in `OddOddCoercivity.lean`.
The basis uses polynomial spanning and Stone–Weierstrass; the weak pairings
use interior cutoffs and dominated convergence against weighted L¹.
Weighted Poincaré, constrained Poincaré and the bulk gradient bound each have
zero transitive admissions. The bulk bound has exactly two: the unchanged
residual identity/sign inputs. The requested traversal excludes
`cert:dd-residual` and its dependency subtree. The standalone Kantorovich
lemma is off this route: a completed square gives the weighted-mean estimate.
Weighted mass, finite integrals and the weighted-mean estimate have no admissions.

The interfaces use actual Fourier derivatives, continuous quotient traces,
weighted interval domains and H¹ endpoint traces. Picone supplies absolute
bulk integrability; coercivity consumes it explicitly. The final contradiction
and the bridges from zero mass to zero quotient and vorticity are proved.
Only nonnegative corrected boundary energy is consumed; strict positivity
and a boundary equality classification are off the exclusion route.

Quotient orthogonality is admission-free for any supplied quotient data; it
does not invoke the admitted existence theorem. The supporting
[DipoleOrthogonality.lean](../../NoEmbeddedEigenvalues/DipoleOrthogonality.lean)
uses four Fourier modes and reflection/cell measure identities, not
self-adjointness. Only the quotient multiplication identity and even parity
are consumed in this step.

Canonical boundary regularity is also admission-free for supplied quotient
data. Even H² arc energy follows by reconstruction through `Δφ` plus the
mean. The quotient transport pair gives Melnikov, and an abstract canonical
profile theorem supplies the weighted interval domain, forcing identity and
endpoint values. Rotation extends through the separatrix by continuity.
No stronger quotient assumptions or separate corner remainders are needed.

The Picone interfaces separate three bulk integrability assertions, Sobolev
Picone on a positive truncation, the character-wise virial limit, and three
geometric level/current limits. The common logarithmic counterterm and the
whole value finite part cancel in Lean. Ordinary exhaustion and boundary-form
identification are admission-free, as are the scalar B derivative formula
and β normalization. Correction integrability now follows directly from the
weighted interval domain, not the admitted B-trace limit. No sign certificate
is used by the current assembly.

The corrected-boundary review replaces the auxiliary scalar Picone function
by a first-order midpoint estimate, and replaces the sharp Poincaré constant
by half-interval Cauchy–Schwarz. The pointwise β lower/absolute/central/tail bounds,
forcing H¹ regularity, correction integrability, the midpoint bound, both affine
estimates, logarithmic endpoint moments and closing rational margins are proved.
The cutoff is the rational 1/7; the constants 203/1920 and λ²/96 come from
exact polynomial integration.
Nonnegativity needs no nonzero-parameter hypothesis; the outer API retains it.

## Statement coverage and analytic frontier

The shared prerequisites have Blueprint proof outlines and explicit dependencies.
Every result in the exclusion's recorded dependency closure has a proof
environment; this is not an audit of all its arguments.
The stream-H² route is now assembled in Lean as described below. Compatibility
review of the other analytic branches remains separate.

The certificate chapter is stated in `BernsteinCertificates.lean`,
`MixedComparison.lean` and `PolynomialInequalities.lean`, with `sorry` proofs.
The explicit odd–odd residual table has a separate identity with the actual
operator, and the sign statement is independent of any Bernstein algorithm.
Coefficient generation, polynomialization and exact verification are not supplied;
no proof backend has been selected. The same distinction is retained for the
mixed interior and Robin inequalities. No exclusion assembly has changed.

[OddOddCoercivity.lean](../../NoEmbeddedEigenvalues/OddOddCoercivity.lean)
now states the bulk form-domain/Poincaré branch. `DDWeightedH1` is the maximal
weak weighted H¹ domain, without boundary traces or a density hypothesis.
The actual quotient-rule derivatives feed it from the existing Picone-energy
hypothesis; no stronger quotient regularity is assumed. Central parity gives
Cartesian Poincaré constant 3; a completed-square estimate handles the mean
under `∫wz = 0`. Gradient coercivity and the residual-certificate potential
bound are separate interfaces. Their assemblies and the constrained estimate
are proved. The form-domain, matrix bound and weighted Poincaré are
admission-free; only the residual certificate remains admitted on this branch.
The outer bulk bound combines the two estimates; the exclusion assembly and
statement of `zonal-poincare` are unchanged. Its weak-domain spectral proof is
fully formalized and spelled out in the Blueprint.
The coefficient bounds exclude the totalized matrix value at the center,
which does not affect any integral. The certificate statements now complete
this branch at Blueprint-node level; their proofs and verification data remain
separate work.

The dependency closures of zero-trace forcing energy, the midpoint bound and
the negative affine correction are now stated. The sum-of-squares nodes reuse
existing proved classical/weighted interfaces; no density argument or duplicate
admission is introduced. Logarithmic endpoint moments
(`lem:corrected-log-moments`) are proved in `CorrectedBoundaryForm.lean`, including
nonnegativity, integrability and the exact value for every natural power.
The negative affine correction (`lem:corrected-negative-affine`) is also
admission-free: the endpoint β bound and the first three logarithmic moments
are combined with zero-trace Cauchy–Schwarz using separate half-interval energies.
The midpoint bound (`lem:corrected-midpoint-bound`) is admission-free too:
central increments cost at most one eighth of the derivative energy, and each
negative endpoint logarithmic layer has mass 1/7. The resulting exact margins
are 5/112 for the midpoint value and 53/448 for the energy.
Only zero-trace forcing energy/endpoints remain admitted on this branch.

Sobolev Picone on a positive truncation (`lem:dd-truncated-picone`) is
transitively admission-free in
[OddOddPicone.lean](../../NoEmbeddedEigenvalues/OddOddPicone.lean).
[OddOddGroundResidual.lean](../../NoEmbeddedEigenvalues/OddOddGroundResidual.lean)
proves absolute potential integrability (`lem:dd-picone-potential-integrable`)
already for L² data. The actual differentiated residual is a polynomial in the
bounded coordinates `s`, `r`, `s(2-s)/r`, `r log(r/2)`, hence uniformly bounded;
no residual sign certificate or singular-log integration is used.
[OddOddPiconeCutoff.lean](../../NoEmbeddedEigenvalues/OddOddPiconeCutoff.lean)
uses quadratic Fourier testing and common-null annular extraction, without density.
Current continuity and the full-level center-current bound restore all levels.
[OddOddPiconeIntegrability.lean](../../NoEmbeddedEigenvalues/OddOddPiconeIntegrability.lean)
supplies ground-state estimates and raw/divided-gradient integrability.
The shared classical identities in [Picone.lean](../../NoEmbeddedEigenvalues/Picone.lean)
are also admission-free. Remaining current work includes the boundary-B trace,
full-level remainder and scalar value finite part, not truncated Picone.

`dd_character_virial_limit` reaches six admissions: `local_h2_smooth_approximation`,
`dd_weighted_first`, `dd_quotient_equations`,
`dd_quotient_gradient_traces`, `dd_value_finite_part` and `dd_renormalized_bulk`.
[OddOddVirial.lean](../../NoEmbeddedEigenvalues/OddOddVirial.lean) proves the
raw/supplied quotient bridge and almost-everywhere coarea splitting of all five
boundary terms. The assembly in `OddOdd.lean` pulls gradient exceptional levels
back under `h ↦ 2h`, selects one pairing sequence avoiding every exceptional set,
and identifies the full bulk limit by uniqueness. The coefficient error is
`ε³ log(1/ε) → 0`. The inward normal convention is preserved throughout.

`dd_cutoff_identity` has no `sorry` of its own. It combines the assembled
weak Green identity and proved boundary-flux identification with the admitted
weighted first identity and quotient equation. The weak Green statement
takes local H² for the stream, local L² for its operator value, and
`HasDDOperator` with specified weak gradients; it uses neither an eigenfunction
nor a derivative of the forcing. Boundary-flux identification is admission-free:
normal–tangent orthogonality reduces the quadratic terms, and
`-μq = (8-s³)/3` identifies the coefficient with the prescribed boundary density.
It assumes neither a PDE nor regularity of the supplied values. Its use is confined
to nonzero cutoff-derivative levels, automatically away from the center.
The assembly obtains local quotient regularity by smooth division and transfers
the weak Poisson equation to arbitrary supplied witnesses by uniqueness.
The original cutoff and annular statements are unchanged; no global quotient
domain or stronger hypothesis has been introduced.

`dd_truncated_virial` follows from `dd_annular_virial`, whose only input with
admissions is the assembled cutoff identity. Positive-truncation integrability,
coefficient bounds, center removal, coarea and common-exceptional-set extraction
are proved without admissions. A Cauchy–Schwarz flux estimate and an
integrable-energy sequence remove the center; dominated convergence closes the
annular limit. Measurable versions and null hulls handle arbitrary witnesses.
Weighted differential algebra and raw half-density conjugation are also
admission-free. The local classical Green identity (`lem:dd-green`) is now
admission-free too: direct flux differentiation cancels the mixed Hessian terms,
and the constant weighted defect identifies the remaining quadratic form.
Its smooth annular cutoff integration (`lem:dd-smooth-green`) is also
admission-free, including the compact-support/divergence argument and the
half-density correction. Weighted-operator identification from specified weak jets
(`lem:dd-operator-jet`) and strong L² operator stability
(`lem:dd-operator-jet-stability`) are also admission-free. They feed the assembled
weak Green identity.

The cutoff and truncated-virial assemblies reach three admissions: local H²
smooth approximation, weighted first identity and quotient equation. The audit
reaches ten admissions below `dd_picone_current`.
The weak Green proof is split at `lem:local-h2-smooth-approximation`, stated
with `sorry` in `SobolevApproximation.lean`. It supplies compactly supported
smooth approximants on the original open domain and strong L² convergence of
all jets through order two on a precompact patch, without boundary assumptions.
`tendsto_integral_mul_conj_of_L2` proves bounded-coefficient quadratic-integral
stability without admissions. `ddWeightedDiv_cutoff` and
`ddWeightedGenerator_cutoff` prove the cutoff half-density correction pointwise
on the regular cell, without classical derivatives of the supplied function.
The smooth endpoint allows compact support anywhere inside the original cell,
not only inside the approximation annulus. Weak Green (`lem:dd-weak-green`) now has
no `sorry` of its own: a compact regular patch contains the cutoff support, and
all four integrands are finite bounded-coefficient quadratic forms in the value,
forcing and weak gradients. Strong L² approximation passes their integrals to the
limit. Its only transitive admission is `local_h2_smooth_approximation`; the original
hypotheses are unchanged. The remaining analytic work on this route is that density
theorem, the weighted first identity and the quotient equation.

[OddOddForms.lean](../../NoEmbeddedEigenvalues/OddOddForms.lean) holds the common
forms, boundary data, characters and value finite-part interface below the virial,
avoiding an import cycle. The weak/classical quotient equations remain separate
from this assembly. `Period.lean` states the leading value asymptotic separately
from sharp remainders.

`dd_exclusion_domain` now follows in Lean from four explicit inputs:
`dd_stream_quotient_h2`, `even_h2_dipole_laplacian`,
`dd_quotient_transport`, and `transport_first_gain_periodic`.
The construction uses no corner-remainder hypotheses: stream H²
implies vorticity L² by coordinate Hardy and the Poisson product rule;
weak transport division and the first gain then give `ν/d ∈ L²`.
The stream proof spells out the dyadic third-derivative estimate, weighted
cone division and H² point removal. The separate angular-Hardy vorticity
division argument is no longer needed. Invariant cutoff testing supplies quotient
transport without closedness of the global transport operator.

The first recursive layer is now stated, not proved, in
[QuotientLocal.lean](../../NoEmbeddedEigenvalues/QuotientLocal.lean),
[OddOddSaddle.lean](../../NoEmbeddedEigenvalues/OddOddSaddle.lean) and
[OddOddRegularity.lean](../../NoEmbeddedEigenvalues/OddOddRegularity.lean).
Using the shared definitions in `LocalJets.lean` and `WeightedTraces.lean`,
it supplies local division and removal,
coordinate Hardy, elliptic regularity/dyadic bounds, local invariant division,
the first two transport gains, and the sector saddle/separatrix/gradient inputs.
Canonical transverse interval H¹ extensions encode zero traces.

The shared scalar/geometry batch is stated in
[ScalarDivision.lean](../../NoEmbeddedEigenvalues/ScalarDivision.lean) and
[SaddleNormalForm.lean](../../NoEmbeddedEigenvalues/SaddleNormalForm.lean):
endpoint/second Hardy, coarse period derivatives, uniform complete-cell estimates
and global division, plus explicit orthonormal charts, parity and differentiated
Taylor bounds. The chart quadratic has the same coefficient as the Cartesian
normalization. Angular Hardy and linearized-Hamiltonian claims are separated
from this route; existing primitive Hardy and period smoothness are reused.

The weighted regularity batch is now stated in
[CylinderInverse.lean](../../NoEmbeddedEigenvalues/CylinderInverse.lean),
[WeightedTraces.lean](../../NoEmbeddedEigenvalues/WeightedTraces.lean) and
[WeightedTransport.lean](../../NoEmbeddedEigenvalues/WeightedTransport.lean).
The cylinder input uses physical-area weight `F/r^(a-1)`; finite harmonic
Taylor jets suffice for the bootstrap. Trace matching uses separate one-sided
ACL data, not an already-glued representative. Zero forcing is required on a
whole edge. The weighted forcing remains `f/d², ∇f/d^(3/2) ∈ L²`, with no
elliptic/parity/midpoint assumptions. Quarter derivatives are weak derivatives
on separate patches; the physical collar cutoff is `Ψ < 2h₀`.

The numerator/logarithmic batch is stated in `OrbitNumerators.lean`,
`WeightedNumerators.lean`, `LogarithmicWeights.lean` and
`OddOddLogarithmic.lean`. `QuarterCoordinates.lean` supplies the shared maps;
`StreamJet.lean` fixes the same Fourier derivatives for bulk, ray and orbit
estimates. Endpoint values come from orbitwise ACL witnesses with separate
locally L² endpoint functions. Ray values are canonical transverse traces.
Fiber integrability and quantitative numerator bounds are exported explicitly.
Logarithmic bulk norms are local on the periodic lift; all four recentered
quarters' rays are covered.

`dd_stream_quotient_h2` now has no `sorry` of its own. Its construction is in
[StreamQuotientAssembly.lean](../../NoEmbeddedEigenvalues/StreamQuotientAssembly.lean):
bounded radial powers give H³ for the saddle remainder; affine pullback mixes
all jet indices; double division feeds point removal before smooth inverse
multiplication. Explicit diagonal charts cover regular separatrix points.
Local a.e. representatives identify one periodic raw quotient, which is glued
and reconstructed on the torus. The multiplication identity descends through
continuous representatives. `InSector.even_dipole_quotient` then supplies parity.
No fourth derivative, extra corner hypothesis or vorticity quotient is used.

The source assembly introduces no new admission. Its transitive audit exposes
nine existing inputs: weighted third jets, separatrix H³, specified-jet
realization, local division/removal and saddle geometry/parity. Their proofs
remain the stream-H² frontier. The other three quotient stages remain admitted.
The larger audit count reflects expansion of the former outer admission, not
new assumptions. The Blueprint proof is marked complete relative to these inputs.

Reusable congruence, gluing, affine, periodic and smooth-multiplier interfaces
are admission-free; see [shared infrastructure](shared.md). The local multiplier
in `SobolevMultipliers.lean` uses compact cutoffs, so inverse factors only need
to be smooth on their nonzero neighbourhoods, without global derivative bounds.

The bundled `def:dd-quotient`, including classical and weak operator E, is
linked in `OddOddVirial.lean`; it is not a dependency of the stream-H² proposition.
The periodic first gain includes cell covering on the full fixed neighbourhood;
it assumes a global torus relation, not merely a pair on that neighbourhood.

Shared jet/trace definitions and the normalized quadratic have moved unchanged
below the parent interfaces. `SaddleNormalForm.lean` no longer imports
`OddOddRegularity.lean`, so the saddle bootstrap can use its geometry without
an import cycle. Ordinary saddle/separatrix statements are now below the
logarithmic layer, which is below the weighted-gradient/third-jet statements.
The Lean audit now follows the stream-H² assembly to its lower Blueprint inputs;
the other three quotient stages still stop at their outer admissions.
Zero-trace forcing energy/endpoints remain the corrected-boundary proof backlog.
Bulk coercivity's weighted-domain, matrix and Poincaré bounds are proved; the certificate
backend remains open.

The exclusion consumes only the minimal data in `cor:dd-exclusion-domain`
(Lean: `dd_exclusion_domain`): even global H² for `φ`, the multiplication
identities, the quotient transport pair and `ν/d ∈ L²`. The additional corner
bounds follow from even H² alone by coordinate and radial Hardy estimates.
Thus `prop:dd-quotient-domain` is now downstream of the minimal result and
off the exclusion route, not an independent stronger regularity obligation.
The numerator's weighted jet and third derivative are still used internally
to prove stream H². The quotient assembly has no own `sorry` and twelve
transitive admissions. `dd_vorticity_quotient_l2` is derived from the first
two inputs. The generic continuous-representative transport-pair bridge has
zero transitive admissions. No quantitative divided-Laplacian norm bound is
included in the Lean interface; it is a separate optional blueprint node.

## Analytic review boundary

The blueprint derives the saddle jet, separatrix H¹/zero traces, local H³ and
`∇ω/d ∈ L²`; their principal interfaces are now stated in Lean with `sorry`. Double division for the H² stream quotient, the subsequent
Hardy/Poisson proof of `ω/Ψ ∈ L²`, and invariant division have explicit
analytic blueprint derivations. Their analytic inputs remain admitted in Lean;
the quotient and transport-domain assemblies are proved. The virial uses only the
minimal quotient data. Its character-wise assembly and representative/exceptional-level
bridges are checked; the six admitted virial inputs and the remaining inputs below
Picone still need proofs and analytic review. Weighted
Poincaré and its basis, cutoff weak pairing and spectral assembly are
transitively admission-free. The corrected-boundary constants have explicit rational derivations;
zero-trace forcing energy/endpoints remain admitted in Lean.
Certificate verification remains deferred.

The virial finite parts use only the leading period value asymptotic, not the
elliptic identity or sharp remainders. Logarithmic multiplication uses slicing,
not the finite-p embedding. Shared infrastructure and character limitations
are tracked in [shared status](shared.md); mathematical questions are in the
[blueprint digest notes](../../blueprint/src/chapters/notes.tex).
