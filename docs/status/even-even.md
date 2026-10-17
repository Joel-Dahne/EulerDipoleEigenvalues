# Even–even status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)

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
  inputs. The virial branch ultimately needs the L² virial identity and the
  orbit area formula.
- Separatrix arc energy and level traces are proved from the trace/local-Sobolev
  inputs using explicit quarter graphs. The first-order trace limit still uses
  the area formula and saddle-distance estimates.
- Weighted boundary positivity and the canonical boundary-form interface are
  proved. Positivity uses interval exhaustion, not smooth density.
- The eigenfunction transport and boundary-regularity assemblies are proved
  from the remaining generic transport, trace and geometry inputs.

## Remaining routes

The open analytic work is owned by [shared infrastructure](shared.md):
Sobolev/trace bridges, orbit charts and bounds, stronger transversal estimates,
H¹/L² virials, and the generic transport limits.

The current even–even route does **not** require finite-p Sobolev embedding,
the elliptic-integral period identity, sharp period asymptotics, or transport
self-adjointness. Keep these out of its prerequisites unless the argument changes.

A candidate next Lean task is `transversalMollifier_hasWeakL0On`: its weak
transport and line-commutator ingredients are ready, conditional on the chart
inputs. Selecting it would resume proof implementation; that has not been decided.

The largest reviewed work packages are the fractional trace infrastructure,
full-gradient/stronger transversal estimates, and pairing-limit assembly.
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
  [EigenfunctionTransport.lean](../../NoEmbeddedEigenvalues/EigenfunctionTransport.lean).
