# Even–even status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#even-even)

## Current position

The even–even exclusion is formalized without admissions: the transitive
admission audit (`just sorries`) reports zero admissions for both
`even_even_exclusion` and `even_even_character_exclusion`. The last inputs were
`lem:local-to-global` (`LocalToGlobal.lean`) and `lem:coarea`
(`OrbitRestriction.lean`).

The analysis, geometry, virial and transport prerequisites have had a first-pass
blueprint review. Proof sketches and dependency corrections are recorded at
the nodes, not reproduced here. This was not a full independent proof audit.

## Remaining work

- Human review of the Lean statements on the route, in particular the setup,
  the eigenvalue problem, sector reduction, interval representatives and the
  weighted boundary domain. Lean cannot check that they say the right thing.
- Bring the settled even–even argument into the reworked manuscript, once the
  authors agree on its structure.

The even–even route does **not** use finite-p Sobolev embedding, the
elliptic-integral period identity, sharp period asymptotics, or transport
self-adjointness.

## Deferred possibilities

- Check whether `ee_first_trace_limit` can also use explicit quarter formulas,
  avoiding its saddle-distance/coarea route. This has not been worked out.
- The old boundary cutoff/zero-extension approximation route is retained as
  infrastructure but is not needed for positivity. Do not prioritize completing
  its density theory on that account.

## Where to work

- [Blueprint](../../blueprint/src/chapters/even_even.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex).
- [EvenEven.lean](../../NoEmbeddedEigenvalues/EvenEven.lean),
  [SeparatrixTraces.lean](../../NoEmbeddedEigenvalues/SeparatrixTraces.lean) and
  [EigenfunctionTransport.lean](../../NoEmbeddedEigenvalues/EigenfunctionTransport.lean)
  and [PairingLimit.lean](../../NoEmbeddedEigenvalues/PairingLimit.lean).
