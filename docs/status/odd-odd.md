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
The full recursive analytic graph is not yet stated in Lean.

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
[QuotientLocal.lean](../../NoEmbeddedEigenvalues/QuotientLocal.lean) and
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

Next finish quarter endpoint/resonant-zero and weighted numerator interfaces,
then logarithmic multiplication, forcing/numerators and weighted phase-cell
division. Do not start proofs during this statement pass. Human review of
hypotheses and derivative/trace packaging is still needed.
The periodic first gain includes cell covering on the full fixed neighbourhood;
it assumes a global torus relation, not merely a pair on that neighbourhood.

Shared jet/trace definitions and the normalized quadratic have moved unchanged
below the parent interfaces. `SaddleNormalForm.lean` no longer imports
`OddOddRegularity.lean`, so the saddle bootstrap can use its geometry without
an import cycle.
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
character-wise interface and the analytic inputs below Picone and weighted
Poincaré still need review. The corrected-boundary constants have explicit rational derivations;
the three remaining interval estimates are not Lean proofs.
Certificate verification remains deferred.

The virial finite parts use only the leading period value asymptotic, not the
elliptic identity or sharp remainders. Logarithmic multiplication uses slicing,
not the finite-p embedding. Shared infrastructure and character limitations
are tracked in [shared status](shared.md); mathematical questions are in the
[blueprint digest notes](../../blueprint/src/chapters/notes.tex).
