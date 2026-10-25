# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` is stated with an admitted proof. The blueprint regularity
review has reached `∇ω/d ∈ L²` and `ν = ω/Ψ ∈ L²`; global H² regularity of
the stream quotient remains open. The renormalized virial is derived
conditional on that quotient domain. These analytic derivations are not
in Lean; the rest of the exclusion remains unverified.

## Main priority when work resumes

Audit the dyadic elliptic estimate and double division near the saddle in
`prop:dd-quotient-domain`. The weighted gradient and L² vorticity quotient
are now derived; the H² stream quotient, corner remainders and quotient
transport-domain assembly are the remaining regularity steps.
For the virial limit, the additional regularity needed is even global H²
for `φ`, `ν/d ∈ L²`, and the quotient transport equation; the separate
weighted corner remainder estimates are not needed there.

The even–even gradient traces apply to `φ` via the auxiliary vorticity
`Δφ`. Hardy division controls the singular bulk gradient coefficient,
and Hölder continuity controls the renormalized potential. This proves
existence of a full bulk limit, which can then be identified using the
canonical pairing only along good levels. The scalar finite part fixes
the edge endpoint constant `log 8 / 2`. See `prop:dd-virial`.

Other inputs needing review include the Picone/current argument, the weighted
Poincaré inequality, and constants in the corrected boundary estimate. The
weighted-forcing H¹ route now covers both odd–odd and mixed, replacing the
tentative generic H¹ sketch. Zero forcing on an edge and the weighted corner
trace force zero vorticity trace there; no midpoint condition is needed.
The transport gains handle all four characters through local endpoint
formulas; the quotient's pairing application needs only the implemented ±1.
See [shared infrastructure](shared.md). Exact certificate verification is also
pending and is deferred while the analytic review continues. The detailed
questions live in the blueprint's digest notes.

The finite parts now use only the leading period value asymptotic, derived
directly from the defining integral in `lem:period-leading-asymptotic`;
they no longer depend on the elliptic identity or sharp derivative remainders.
Hölder embedding remains a dependency. The logarithmic multiplier now uses
coordinate slicing, so the finite-p embedding is off the current sector
route. The new logarithmic nodes make the weighted-gradient argument explicit
in the generated odd–odd graph.

## Where to work

- [Odd–odd blueprint](../../blueprint/src/chapters/odd_odd.tex),
  [regularity](../../blueprint/src/chapters/regularity.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean).
- [Certificates](../../blueprint/src/chapters/certificates.tex):
  shared checking infrastructure is tracked in [shared status](shared.md).
