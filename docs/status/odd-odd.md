# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` is stated with an admitted proof. The blueprint derives
the renormalized weighted virial conditional on the quotient domain, and
saddle/H¹ separatrix regularity including zero edge traces and local H³
regularity of `ψ`. These analytic derivations are not in Lean.
The quotient regularity and the rest of the exclusion remain unverified.

## Main priority when work resumes

Continue with the logarithmically weighted vorticity-gradient and division
steps in `prop:dd-quotient-domain`. The ordinary H¹ gain is now derived;
it does not yet establish the stronger quotient estimates.
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
pending. The detailed questions live in the blueprint's digest notes.

The finite parts now use only the leading period value asymptotic, derived
directly from the defining integral in `lem:period-leading-asymptotic`;
they no longer depend on the elliptic identity or sharp derivative remainders.
Both Hölder and finite-p embeddings remain dependencies of the less-settled
quotient argument pending review.

## Where to work

- [Odd–odd blueprint](../../blueprint/src/chapters/odd_odd.tex),
  [regularity](../../blueprint/src/chapters/regularity.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean).
- [Certificates](../../blueprint/src/chapters/certificates.tex):
  shared checking infrastructure is tracked in [shared status](shared.md).
