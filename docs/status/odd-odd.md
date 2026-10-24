# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` is stated with an admitted proof. The blueprint now
derives the weighted virial through its renormalized separatrix limit,
conditional on the quotient-domain conclusions. The first two transport
gains and cylinder inverse now also have explicit blueprint derivations,
giving the odd–odd quadratic saddle jet. None of these new derivations is
in Lean. The quotient regularity and the rest of the exclusion remain
unverified.

## Main priority when work resumes

Continue with `prop:dd-separatrix-h1`, then the logarithmically weighted
vorticity-gradient and division steps in `prop:dd-quotient-domain`.
The saddle bootstrap does not yet give these H¹/quotient estimates.
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
generic H¹ transport gain remains tentative. The first two transport gains
handle all four characters through local endpoint formulas; the quotient's
Melnikov/pairing application needs only the implemented ±1 characters.
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
