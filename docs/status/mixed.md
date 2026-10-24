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
relation. First saddle gain, the cylinder inverse, and paired flux remain
unverified inputs. No new part of the exclusion is proved in Lean.

## Priorities when work resumes

- Review the first saddle gain and cylinder inverse that supply the linear
  jet; formalize the weighted-forcing H¹ lemma, numerator estimates and
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
The mixed route also avoids the tentative generic second/H¹ gains and the
elliptic period identity/sharp asymptotics: coarse first/second period
derivative bounds from the regular integral suffice.

Algebraic or numerical sanity checks are not proofs of the analytic identities
or certificate inequalities.

## Where to work

- [Mixed blueprint](../../blueprint/src/chapters/mixed.tex),
  [regularity](../../blueprint/src/chapters/regularity.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [Mixed.lean](../../NoEmbeddedEigenvalues/Mixed.lean).
- [Certificates](../../blueprint/src/chapters/certificates.tex):
  shared checking infrastructure is tracked in [shared status](shared.md).
