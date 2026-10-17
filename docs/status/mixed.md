# Mixed-sector status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#mixed)

## Current position

`mixed_exclusion` for the odd–even sector is stated with an admitted proof.
`mixed_other_exclusion` is proved by rotation to that result, so it is still
conditional on the admitted exclusion. No separate analytic proof is needed
for the second mixed sector.

This sector has not had the recent even–even prerequisite review. Several
regularity and virial statements remain marked `notready` in the blueprint.

## Priorities when work resumes

- Digest the mixed quotient/regularity domain and saddle jets.
- Justify the paired flux and mixed virial identities, including cancellation
  of adjacent divergent edge energies.
- Extend the smooth boundary-square identity to eigenfunction traces.
- Verify the comparison/coercivity route and its exact certificates.

Before investing in elliptic-center regularity, check whether the boundary
trace argument can use only local separatrix regularity. The blueprint records
this possible simplification: the global H¹ corollary is currently used only
at `lem:mixed-boundary-square-traces`.

Algebraic or numerical sanity checks are not proofs of the analytic identities
or certificate inequalities.

## Where to work

- [Mixed blueprint](../../blueprint/src/chapters/mixed.tex),
  [regularity](../../blueprint/src/chapters/regularity.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [Mixed.lean](../../NoEmbeddedEigenvalues/Mixed.lean).
- [Certificates](../../blueprint/src/chapters/certificates.tex):
  shared checking infrastructure is tracked in [shared status](shared.md).
