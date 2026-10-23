# Even–even status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#even-even)

## Current position

The even–even exclusion is formalized without admissions: the transitive
admission audit (`just sorries`) reports zero admissions for both
`even_even_exclusion` and `even_even_character_exclusion`.

The prerequisites have had a first-pass blueprint review, not a full
independent mathematical audit. Proof details are at the nodes.

## Remaining work

- Human review of the Lean statements on the route, in particular the setup,
  the eigenvalue problem, sector reduction, interval representatives and the
  weighted boundary domain. Lean cannot check that they say the right thing.
- Bring the settled even–even argument into the reworked manuscript, once the
  authors agree on its structure.

The even–even route does **not** use finite-p Sobolev embedding, the
elliptic-integral period identity, sharp period asymptotics, or transport
self-adjointness.

## Optional routes

Explicit quarter formulas might simplify `ee_first_trace_limit`; this is
unworked. Boundary positivity uses direct interval exhaustion, not density theory.

## Where to work

- [Blueprint](../../blueprint/src/chapters/even_even.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [EvenEven.lean](../../NoEmbeddedEigenvalues/EvenEven.lean) for assembly;
  [architecture guide](../architecture.md) for the supporting modules.
