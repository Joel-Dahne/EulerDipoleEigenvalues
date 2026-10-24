# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

`odd_odd_exclusion` is stated with an admitted proof. Unlike even–even, this
sector has not had the recent prerequisite-by-prerequisite first-pass review.
The blueprint is a proposed argument, not a verified analytic proof.

## Main priority when work resumes

Digest `prop:dd-virial`, the renormalized weighted virial identity. The blueprint
identifies this as the largest mathematical gap. Its weighted L² justification,
boundary integral and corner finite-part limit still need to be derived.
Do not assume the even–even mollifier argument transfers unchanged.

Other inputs needing review include the quotient domain and saddle regularity,
the Picone/current argument, the weighted Poincaré inequality, and constants in
the corrected boundary estimate. The shared transport gains remain tentative;
unlike mixed, this sector uses only the existing ±1 rotation characters.
See [shared infrastructure](shared.md). Exact certificate verification is also pending.
The detailed questions live in the blueprint's digest notes.

The finite-part calculation retains the elliptic period formula and sharp
asymptotics. Both Hölder and finite-p embeddings remain dependencies of the
less-settled quotient argument pending review; do not remove them merely
because even–even does not need both.

## Where to work

- [Odd–odd blueprint](../../blueprint/src/chapters/odd_odd.tex),
  [regularity](../../blueprint/src/chapters/regularity.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean).
- [Certificates](../../blueprint/src/chapters/certificates.tex):
  shared checking infrastructure is tracked in [shared status](shared.md).
