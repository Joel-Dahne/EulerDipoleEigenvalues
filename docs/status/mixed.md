# Mixed-sector status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#mixed)

## Current position

`mixed_exclusion` for the odd–even sector is stated with an admitted proof.
`mixed_other_exclusion` is proved by rotation to that result, so it is still
conditional on the admitted exclusion. No separate analytic proof is needed
for the second mixed sector.

The blueprint has local boundary-square and weighted-forcing H¹ derivations.
The latter applies to the jet-subtracted mixed remainder without an elliptic
relation. The shared first saddle gain and cylinder inverse now have explicit
blueprint derivations, not Lean proofs. Paired flux remains unverified.
No new part of the exclusion is proved in Lean.

`MixedComparison.lean` now defines the second-order coefficients and both
comparison functions; boundedness claims are separate statements.
`PolynomialInequalities.lean` states their interior sign claims, normalized
residual/operator identities and the Robin polynomial inequality, all with
`sorry` proofs. The Robin derivative identity is restricted to `h>0` and its
continuous polynomial extension covers zero: raw corner partials do not give
the same endpoint value. No certificate checker or proof backend is selected.

## Priorities when work resumes

- Reuse the shared saddle bootstrap for the linear jet; formalize its
  inputs and the weighted-forcing H¹ lemma, numerator estimates and
  phase-cell division. The quotient by `cos a` is not a transport pair.
- Extend Melnikov/pairing reuse to rotation characters ±i (the implemented
  results accept only ±1), or derive a half-orbit alternative.
- Justify the paired flux and mixed virial, including cancellation of
  adjacent divergent edge energies; even–even gradient limits do not apply.
- Formalize the local corner trace, one-sided H² trace and weighted
  boundary-square extension; then verify coercivity and its certificates.

Global H¹ and elliptic-center regularity are no longer prerequisites in the
blueprint route. The mixed quotient domain already supplies local H¹ and
`ω/r ∈ L²`, which give the `L²(dt)` corner trace. This is a mathematical
derivation conditional on that domain, not a Lean proof of mixed regularity.
The mixed route uses the weighted-forcing H¹ lemma rather than the
pointwise second-gain hypotheses. The same H¹ lemma now covers odd–odd
with weaker forcing weights. Neither route needs the elliptic period
identity/sharp asymptotics: coarse first/second period derivative bounds
from the regular integral suffice.

Algebraic or numerical sanity checks are not proofs of the analytic identities
or certificate inequalities.

## Where to work

- [Mixed blueprint](../../blueprint/src/chapters/mixed.tex),
  [regularity](../../blueprint/src/chapters/regularity.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [Mixed.lean](../../NoEmbeddedEigenvalues/Mixed.lean).
- [Certificates](../../blueprint/src/chapters/certificates.tex):
  shared checking infrastructure is tracked in [shared status](shared.md).
