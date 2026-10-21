# Shared infrastructure status

[Project status](../../STATUS.md) · [Even–even](even-even.md) ·
[Odd–odd](odd-odd.md) · [Mixed](mixed.md)

This page owns cross-sector infrastructure and candidate tasks. Sector pages
explain how it is used. Exact statements, proof mechanisms and per-node progress
belong in the blueprint, not in another status inventory.

## Available foundations

Fourier/L² setup, symmetry and rotation decompositions, inverse-Laplacian
regularity, classical lift calculus, smooth virials, Fourier product/IBP
rules and the periodization of compactly supported cell functions are formalized. Interval H¹ and weighted boundary calculus are available;
full smooth-density theory is not.

`LineMollifier.lean`, `AnglePeriodization.lean` and `LiftPeriodization.lean` have no
admissions. The last gives the `2π`-periodization of compactly supported tests, unfolding,
the lift direction of the torus/local-Sobolev bridge (`lem:lift-sobolev-local`) and
`L₀` against `H¹` tests (`lem:L0-h1-tests`); with it `isTransportPair_of_isEigenSolution`
has no admissions.
The orbit-coordinate regularity and area inputs of the transversal L² estimates
and weak action-angle transport equivalence are proved. Both full weak-gradient
chain rules are proved without admissions, using direct test functions rather
than Sobolev approximation. The reverse rule handles the angular seam through
periodic representatives of the weak derivatives and cofactor cancellation.

## Analytic backlog

Difficulty assessments below come from a first-pass review, not a complete
proof audit or timing estimate.

### Sobolev and traces

See the [analysis blueprint](../../blueprint/src/chapters/analysis.tex).

- Orbitwise restriction: moderate once the coordinate inputs exist.
- Finite-p embedding: medium–high and outside the even–even route; inverse
  Hausdorff–Young or Mathlib's compact-support Sobolev inequality are candidate
  approaches, not completed implementations.

`lem:sobolev-holder` is proved without admitted dependencies in `SobolevHolder.lean`,
using the continuous Fourier representative, fractional character increments and
weighted Cauchy–Schwarz, uniformly for each exponent `0 ≤ α < 1`.

`lem:acl-slicing` is proved without admitted dependencies in `ACLSlicing.lean`,
including a jointly measurable representative, unbounded intervals and whole-section
uniqueness. `lem:local-to-global` is proved without admitted dependencies in `LocalToGlobal.lean`:
both directions of the torus/local-Sobolev bridge are now available. Weak derivatives of
compactly supported functions are tested against cut-off characters, as for box periodization.
`lem:trace-l2` is proved without admitted dependencies in
`TraceL2.lean`: the exact elementary bound, canonical endpoint limits and
independence of ACL representatives are available.
`lem:trace-acl` is proved without admitted dependencies in `DiagonalACL.lean`,
using the linear weak chain rule and directional slicing. The line-representative
construction for torus lifts now uses this independent ACL theorem.
`lem:trace-h2` is proved without admitted dependencies in `TraceH2.lean`.
Horizontal FTC and transverse dominated convergence replace smooth approximation.
`lem:trace-gagliardo` is proved without admitted dependencies in `TraceGagliardo.lean`,
retaining `exists_acl_trace`'s uniform constant and ACL representative guarantees.
Averaged rectangular paths and the constant-four Hardy inequality (`HardyAverage.lean`)
avoid rectangle extension and density. The rectangle trace package has no remaining
blockers; extension/density infrastructure is not needed for these results.

### Orbit geometry

See the [geometry blueprint](../../blueprint/src/chapters/geometry.tex).

- The orbit-coordinate inverse identities, regularity, angular seams, area
  formula and level-cutoff coarea are proved without admissions in
  `OrbitCoordinates.lean`. The area argument uses the smooth orbit map's
  constant Jacobian `2` directly on the half-open time domain. Fubini and
  periodicity give integrability of the level integral on closed level bands.
- Period regularity (`lem:period-regularity`) is proved without admissions in
  `Period.lean`: the regular fixed-interval integral gives smoothness and
  `L' < 0`, hence strict decrease of `L` and `S`. The full coarse period
  bounds (`lem:period-coarse`) are proved without admissions in
  `OrbitCoordinates.lean`, using the endpoint cosine estimates; the global
  upper exponential bound `exp_eighthPeriod_le` has moved there from
  `Period.lean` to avoid an import cycle. Sharp asymptotics remain open.
- Full weak-gradient transfer is proved in both directions, including the
  angular seam; see the virial regularization section below.
- Saddle-distance, endpoint and orbit-comparison bounds are proved without
  admissions in `OrbitCoordinates.lean`. A bounded integrating factor gives
  saddle distance independently of period bounds; Grönwall and the proved
  coarse period bound give orbit comparison in both time directions.
  First and second level-derivative bounds, including their saddle-distance
  form, are also proved without admissions, using mixed-derivative symmetry
  and homogeneous Grönwall estimates for the variations.
  Coordinate-gradient and flow-time power-integral bounds are also proved
  without admissions: inverse-Jacobian algebra and rotation invariance give
  the gradients, and exact exponential integration gives the power bounds.
  There are no remaining admissions in `OrbitCoordinates.lean`.
  Keep recentered quarter times: the former global time-gradient estimate
  was false.
- The elliptic identity and sharp value/derivative asymptotics are outside the
  even–even route. Sharp remainders still need a precise reference or quantified
  proof, especially for the derivative.

### Virial regularization

See the [virial blueprint](../../blueprint/src/chapters/virial.tex),
[TransversalMollifier.lean](../../NoEmbeddedEigenvalues/TransversalMollifier.lean),
[CellPeriodization.lean](../../NoEmbeddedEigenvalues/CellPeriodization.lean) and
[VirialL2.lean](../../NoEmbeddedEigenvalues/VirialL2.lean).

`virial_l2` is proved without admitted dependencies (verified by the transitive
admission audit). Its H¹ commutator, skew-symmetry, cell periodization,
transversal mollifier and chart prerequisites have no admissions.
The reverse rule `HasWeakPartialOn.comp_actionAngle`
(`lem:action-angle-weak-cell`) uses direct cofactor-weighted tests: symmetry of
mixed derivatives gives the Piola cancellation. Weak-derivative uniqueness gives
a.e. angular periodicity; the angular partition produces periodic representatives,
and the area formula transfers their a.e. equality back to the cell. This handles
the seam without local W¹,¹ approximation or a separate gluing theorem.
The periodization part of `lem:local-to-global` is not used. The virial regularization route has no remaining blockers.

### Transport and later-sector regularity

See the [transport blueprint](../../blueprint/src/chapters/transport.tex) and
[regularity blueprint](../../blueprint/src/chapters/regularity.tex).

The eigenfunction-to-transport bridge is proved. Resonant vanishing is proved from
`lem:coarea`, the area formula and differentiability of `L`. `lem:coarea` is proved in
`OrbitRestriction.lean` from the weak action-angle transport equivalence and ACL slicing,
after a level cutoff; it needs only local integrability, not `L²`. Melnikov is proved from
these and the trace, periodization, torus Hölder, orbit-comparison and coarse period
inputs (`Melnikov.lean`). The canonical-profile inputs (local absolute continuity,
uniqueness, exponential decay and the constant-one weighted bound) and good windows
are proved without admissions. The forcing comparison, quarter pairing limit and
`pairing_limit` are assembled in `PairingLimit.lean` with no `sorry` of their own,
from the existing trace, Hölder/periodization, orbit-comparison, period-bound and
coarea prerequisites. Periodic uniqueness supplies the quarter character, so no
planar a.e. rotation hypothesis on the vorticity is needed. Only the upper bound
on `exp L` and `L → ∞` enter the limit; sharp period asymptotics are not needed.
The revised sketches use test H¹ density and separatrix-only integration by
parts, not orbit regularity at prescribed resonant levels.

Beyond even–even, transport gain statements, weighted quotient domains and
elliptic-center regularity still need digestion. Local elliptic regularity and
interval Hardy inputs also remain open. Transport self-adjointness/core
results in `TransportOperator.lean` remain admitted, but are not prerequisites
of the current even–even proof.

## Other open work

- Human review of Lean statements remains important, particularly the setup,
  sector reduction, interval representatives and weighted boundary domain.
- `lem:sector-projections` still lacks a linked Lean statement/proof for the
  full orthogonal-projection claim. It is not needed by the current exclusion
  assembly.
- Certificates for odd–odd and mixed lack the verification scripts/data
  described in the manuscript. Plan a sound exact checker and verified links
  from coefficient data to defining expressions; numerical checks are not
  substitutes. See the [certificate blueprint](../../blueprint/src/chapters/certificates.tex).
- Optional cleanup candidates: shared AC/derivative predicates and zero-trace
  packaging, factoring x/y and left/right duplicates, general AC utilities and
  Mathlib-style names. Reassess against current code before starting; these
  are not prerequisites for the next proof.
- No Git remote is configured. Publishing still needs the remote, blueprint
  URLs, declaration checking and docgen/Pages configuration; see the
  [repository setup](../../README.md) and [blueprint setup](../../blueprint/README.md).

Keep this a current work list, not a catalogue of completed declarations.
Implementation details belong in module documentation; resolved items should
leave this page rather than accumulate below it.
