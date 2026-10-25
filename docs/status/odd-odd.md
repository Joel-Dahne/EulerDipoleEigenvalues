# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` and its character-wise assembly have no `sorry` of their
own. They depend on five explicit admitted analytic inputs in
[OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean): quotient existence,
canonical boundary regularity, the Picone current, bulk coercivity and
corrected interval nonnegativity. This is a conditional assembly,
not an admission-free exclusion. The full dependency graph has not yet been
translated into Lean statements.

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

## Next work: the canonical boundary bridge

Review and prove `dd_boundary_regularity` using the existing even–even
canonical-profile machinery and the supplied quotient data. Then expand
corrected boundary nonnegativity into its one-dimensional ingredients.
Keep bulk coercivity and its certificate deferred. This top-down work tests
the final steps before further investment in the regularity bootstrap.

The exclusion consumes only the minimal data in `cor:dd-exclusion-domain`:
even global H² for `φ`, the multiplication identities, the quotient transport
pair and `ν/d ∈ L²`. Separate weighted corner remainders are not fields of
this interface. The stronger `prop:dd-quotient-domain` remains available as a
proposed sufficient route, not a proved Lean prerequisite.

## Analytic review boundary

The blueprint derives the saddle jet, separatrix H¹/zero traces, local H³,
`∇ω/d ∈ L²` and `ω/Ψ ∈ L²`. Double division for the H² stream quotient and
transport-domain assembly still need mathematical review. The renormalized
virial is derived conditional on the quotient domain; the Picone current,
weighted Poincaré and corrected boundary constants still need review.
Certificate verification remains deferred.

The virial finite parts use only the leading period value asymptotic, not the
elliptic identity or sharp remainders. Logarithmic multiplication uses slicing,
not the finite-p embedding. Shared infrastructure and character limitations
are tracked in [shared status](shared.md); mathematical questions are in the
[blueprint digest notes](../../blueprint/src/chapters/notes.tex).
