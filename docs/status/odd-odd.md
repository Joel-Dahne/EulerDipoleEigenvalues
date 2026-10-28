# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` and its character-wise assembly have no `sorry` of their
own. In [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean), the Picone
current is also assembled without its own `sorry`, from eight explicit
analytic inputs. Corrected boundary nonnegativity is assembled from three
interval estimates in [CorrectedBoundaryForm.lean](../../NoEmbeddedEigenvalues/CorrectedBoundaryForm.lean).
Quotient existence in [OddOddQuotient.lean](../../NoEmbeddedEigenvalues/OddOddQuotient.lean)
has an assembled stream-H² stage and three remaining outer admissions.
The stream-H² assembly reaches nine existing local analytic admissions, so the
quotient domain has twelve transitive admissions and the full odd–odd exclusion
has twenty-four. This is not an admission-free exclusion.
All nodes in the recursive Blueprint dependency closure of `thm:dd-exclusion`
now have statement/Mathlib markers, including the certificate tools and residual
sign claim. Off-route auxiliary results may remain unstated. These markers are
neither a human compatibility review nor a proof audit.

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
forcing H¹ regularity, correction integrability, the positive-central estimate
and closing rational margins are proved. The cutoff is the rational 1/7;
the constants 203/1920 and λ²/96 come from exact polynomial integration.
Nonnegativity needs no nonzero-parameter hypothesis; the outer API retains it.

## Statement coverage and analytic frontier

The formerly outline-free shared prerequisites now have Blueprint proofs and
explicit dependencies. Every result in the exclusion's recorded dependency
closure has a proof environment; this is not an audit of all its arguments.
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
Cartesian Poincaré constant 3; Kantorovich handles the mean under `∫wz = 0`.
Gradient coercivity and the residual-certificate potential bound are separate
interfaces. All new proofs are `sorry`; the existing outer admission and
exclusion assembly have not changed. The orange statement flag is removed
from `zonal-poincare`, but its weak-domain spectral proof remains open.
The coefficient bounds exclude the totalized matrix value at the center,
which does not affect any integral. The certificate statements now complete
this branch at Blueprint-node level; their proofs and verification data remain
separate work.

The dependency closures of zero-trace forcing energy, the midpoint bound and
the negative affine correction are now stated. The sum-of-squares nodes reuse
existing proved classical/weighted interfaces; no density argument or duplicate
admission is introduced. `CorrectedBoundaryForm.lean` now states the nonnegative,
integrable logarithmic endpoint moments for all natural powers, with `sorry`.
The three interval estimates themselves remain admitted; no parent assembly or
transitive exclusion admission count has changed.

The `dd-truncated-picone` dependency closure is now stated too. Its only missing
result was the shared classical Picone identity, now in
[Picone.lean](../../NoEmbeddedEigenvalues/Picone.lean), with `sorry` proofs.
The integrated interface assumes absolute integrability and the outward
divergence formula for the actual current. It does not supply the weak H²
extension or center removal in `dd_truncated_picone`; that parent and the
exclusion assemblies are unchanged. Compatibility review remains deferred
while the statement pass continues.

[OddOddVirial.lean](../../NoEmbeddedEigenvalues/OddOddVirial.lean) now covers
the missing weighted-virial interfaces below `dd-character-virial-limit`, including
the quotient/operator definitions; `Period.lean` states the leading value asymptotic
separately from sharp remainders. All new theorem proofs are `sorry`; no parent
assembly or transitive exclusion admission count has changed. The interfaces
separate weak quotient equations from classical Green/conjugation identities,
raw local quotients from supplied global data, common exceptional-level sets
from full bulk limits, and inward from the library's outward normal derivative.
The deferred compatibility review must pass from supplied data to the raw local
virial, rescale exceptional levels by `ε = 2h`, and align the pairing subsequence
with all exceptional sets. This is statement/interface work, not new analytic
proof work.

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
The three interval estimates (zero-trace forcing energy/endpoints, midpoint,
and negative affine tail) remain a separate proof backlog. Bulk coercivity's
weighted-domain and inequality interfaces are now stated; their proofs and
the certificate backend remain open.

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
the quotient and transport-domain assemblies are proved. The virial uses only the minimal quotient data; its Lean
character-wise interface and its newly stated recursive virial inputs, as well
as the analytic inputs below Picone, still need compatibility review. Weighted
Poincaré now has a precise weak form-domain statement, but no spectral proof. The corrected-boundary constants have explicit rational derivations;
the three remaining interval estimates are not Lean proofs.
Certificate verification remains deferred.

The virial finite parts use only the leading period value asymptotic, not the
elliptic identity or sharp remainders. Logarithmic multiplication uses slicing,
not the finite-p embedding. Shared infrastructure and character limitations
are tracked in [shared status](shared.md); mathematical questions are in the
[blueprint digest notes](../../blueprint/src/chapters/notes.tex).
