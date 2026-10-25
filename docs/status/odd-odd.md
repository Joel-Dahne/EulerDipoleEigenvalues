# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` and its character-wise assembly have no `sorry` of their
own. In [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean), the Picone
current is also assembled without its own `sorry`, from eight explicit
analytic inputs. Corrected boundary nonnegativity is assembled from three
interval estimates in [CorrectedBoundaryForm.lean](../../NoEmbeddedEigenvalues/CorrectedBoundaryForm.lean).
Together with quotient existence and bulk coercivity this gives thirteen
transitive admissions, not an admission-free exclusion. The full recursive
analytic graph is not yet stated in Lean.

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

## Next work: the three interval estimates

Prove zero-trace forcing energy/endpoints, the logarithmic midpoint bound,
and the negative affine-tail bound. Their blueprint derivations use elementary
integration by parts, endpoint estimates and logarithmic moments; they remain
Lean admissions. Then return to Picone density integrability and weak
truncation/virial limits. Bulk coercivity and its certificate remain deferred.

The exclusion consumes only the minimal data in `cor:dd-exclusion-domain`:
even global H² for `φ`, the multiplication identities, the quotient transport
pair and `ν/d ∈ L²`. Separate weighted corner remainders are not fields of
this interface. The stronger `prop:dd-quotient-domain` remains available as a
proposed sufficient route, not a proved Lean prerequisite.

## Analytic review boundary

The blueprint derives the saddle jet, separatrix H¹/zero traces, local H³,
`∇ω/d ∈ L²` and `ω/Ψ ∈ L²`. Double division for the H² stream quotient and
transport-domain assembly still need mathematical review. The renormalized
virial is derived conditional on the quotient domain; its Lean character-wise
interface and the analytic inputs below Picone and weighted Poincaré still
need review. The corrected-boundary constants have explicit rational derivations;
the three remaining interval estimates are not Lean proofs.
Certificate verification remains deferred.

The virial finite parts use only the leading period value asymptotic, not the
elliptic identity or sharp remainders. Logarithmic multiplication uses slicing,
not the finite-p embedding. Shared infrastructure and character limitations
are tracked in [shared status](shared.md); mathematical questions are in the
[blueprint digest notes](../../blueprint/src/chapters/notes.tex).
