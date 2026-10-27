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
is assembled from four admitted analytic inputs. Together with bulk coercivity
this gives sixteen transitive admissions, not an admission-free exclusion.
All nodes in the recursive dependency closures of the minimal quotient
construction, `lem:dd-character-virial-limit`, `lem:dd-truncated-picone`
and the three corrected-boundary interval estimates now have linked Lean statements.
Other parts of the odd–odd graph still have unstated results; statement markers
are not proofs.

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

## Current work: recursive statement pass

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

The `prop:dd-stream-quotient-h2` compatibility review finds matching analytic
inputs without a fourth derivative or new corner hypothesis. Bounded radial
powers supply ordinary H³; chart changes must mix derivative indices. Double
division feeds point removal directly: remove the point for V first, then shrink
before multiplying by the smooth inverse factor. A common periodic raw quotient
fixes a.e. overlap agreement, without matching assigned separatrix values.

The next statement-level bridges are affine pullback of weak jets/radial L²
bounds, Sobolev congruence under a.e. equality on the domain, and periodic
local-to-global gluing. `DiagonalACL.lean` supplies first-order diagonal cases;
`SobolevLocal.lean` currently gives global-a.e. congruence;
`LocalToGlobal.lean` already periodizes arbitrary compactly supported Hᵏ data.
Domain-a.e. weak congruence is proved privately as `HasWeakPartialOn.congr_ae_on`
in `TransversalMollifier.lean`: promote it and derive its Sobolev version, rather
than add an admission. For periodic gluing, reuse the rescaled/tensored
`anglePartition` and `memSobolev_compactPeriodize`; local Sobolev gluing on the
lift still needs an exposed interface. These are Lean interface gaps, not
extra eigenfunction hypotheses. No analytic
proofs or parent assemblies have changed. A statement marker is not a proof audit.
The bundled `def:dd-quotient`, including classical and weak operator E, is
linked in `OddOddVirial.lean`; it is not a dependency of the stream-H² proposition.
The periodic first gain includes cell covering on the full fixed neighbourhood;
it assumes a global torus relation, not merely a pair on that neighbourhood.

Shared jet/trace definitions and the normalized quadratic have moved unchanged
below the parent interfaces. `SaddleNormalForm.lean` no longer imports
`OddOddRegularity.lean`, so the saddle bootstrap can use its geometry without
an import cycle. Ordinary saddle/separatrix statements are now below the
logarithmic layer, which is below the weighted-gradient/third-jet statements.
Parent admissions have not been replaced by assemblies: the blueprint records
the intended recursive dependencies, whereas the Lean sorry audit still stops
at the four existing quotient inputs (sixteen for the full exclusion).
The three interval estimates (zero-trace forcing energy/endpoints, midpoint,
and negative affine tail) remain a separate backlog. Bulk coercivity and its
certificate remain deferred.

The exclusion consumes only the minimal data in `cor:dd-exclusion-domain`
(Lean: `dd_exclusion_domain`): even global H² for `φ`, the multiplication
identities, the quotient transport pair and `ν/d ∈ L²`. The additional corner
bounds follow from even H² alone by coordinate and radial Hardy estimates.
Thus `prop:dd-quotient-domain` is now downstream of the minimal result and
off the exclusion route, not an independent stronger regularity obligation.
The numerator's weighted jet and third derivative are still used internally
to prove stream H². The quotient assembly has no own `sorry` and four
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
as the analytic inputs below Picone and weighted Poincaré, still need review. The corrected-boundary constants have explicit rational derivations;
the three remaining interval estimates are not Lean proofs.
Certificate verification remains deferred.

The virial finite parts use only the leading period value asymptotic, not the
elliptic identity or sharp remainders. Logarithmic multiplication uses slicing,
not the finite-p embedding. Shared infrastructure and character limitations
are tracked in [shared status](shared.md); mathematical questions are in the
[blueprint digest notes](../../blueprint/src/chapters/notes.tex).
