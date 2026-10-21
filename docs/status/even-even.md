# Even–even status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#even-even)

## Current position

The assembly proofs `even_even_character_exclusion` and `even_even_exclusion`
have no `sorry` of their own. They still depend on admitted analytic inputs;
the sector is not yet proved independently of admissions.

The analysis, geometry, virial and transport prerequisites have had a first-pass
blueprint review. Proof sketches and dependency corrections are recorded at
the nodes, not reproduced here. This was not a full independent proof audit.

## What is already assembled

- The truncated virial and boundary limits combine outside a common null set.
  Positivity and nonnegative exhaustion give `ω = 0` directly, without a
  global bulk-integrability or weak-gradient constant-function argument.
- The cutoff, annular and center-limit assemblies are proved from their named
  inputs. The L² virial identity is proved without admitted dependencies,
  including its weak-gradient chain rules, orbit coordinates and area formula.
- Separatrix arc energy and level traces have no admitted dependencies (axiom
  audits passed), using the rectangle trace proofs and explicit quarter graphs.
  The first-order trace limit still uses the area formula and saddle-distance estimates.
- Weighted boundary positivity and the canonical boundary-form interface are
  proved. Positivity uses interval exhaustion, not smooth density.
- The eigenfunction transport, pairing-limit and boundary-regularity assemblies
  are proved from the remaining trace, coarea and geometry inputs.

## Remaining routes

The open analytic work is owned by [shared infrastructure](shared.md):
Sobolev bridges and the remaining analytic prerequisites of the transport
and boundary limits. The orbit chart, quarter-orbit bounds, transversal estimates
and H¹/L² virial route are proved without admitted dependencies.

The current even–even route does **not** require finite-p Sobolev embedding,
the elliptic-integral period identity, sharp period asymptotics, or transport
self-adjointness. Keep these out of its prerequisites unless the argument changes.

All transversal mollifier lemmas and the eigenfunction transport pair are proved;
the transitive admission audit reports zero admissions for `virial_l2`.

The rectangle trace inputs are proved without admissions.
Pairing-limit assembly is complete from its analytic prerequisites;
see [shared infrastructure](shared.md).
Relative difficulty assessments are preliminary, not timing estimates.

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
