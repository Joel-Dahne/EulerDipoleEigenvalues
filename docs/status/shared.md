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
and weak action-angle transport equivalence are proved. The full forward
weak-gradient chain rule is also proved without admissions, using direct test
functions rather than Sobolev approximation. Only reverse weak-gradient transfer
remains admitted in the action-angle interface.

## Analytic backlog

Difficulty assessments below come from a first-pass review, not a complete
proof audit or timing estimate.

### Sobolev and traces

See the [analysis blueprint](../../blueprint/src/chapters/analysis.tex).

- Hölder embedding and the periodization direction of the torus/local-Sobolev bridge
  (`exists_memSobolev_periodize`): moderate. The lift direction is proved.
- Directional ACL slicing: moderate; diagonal representatives and elementary
  L²/endpoint trace estimates should be smaller steps once slicing is available.
- H² trace differentiation: medium–high, including smooth approximation.
- Fractional trace control: the largest analysis task; rectangle extension and
  density are still infrastructure gaps.
- Orbitwise restriction: moderate once the coordinate inputs exist.
- Finite-p embedding: medium–high and outside the even–even route; inverse
  Hausdorff–Young or Mathlib's compact-support Sobolev inequality are candidate
  approaches, not completed implementations.

`lem:acl-slicing` and `lem:trace-l2` have no Lean statements yet.
`lem:trace-acl` and `lem:trace-gagliardo` still share the admitted
`exists_acl_trace`; the split did not create independent Lean proofs.
H² trace differentiation needs elementary L² trace control, not the fractional
bound. Preserve the ACL representative compatibility and uniform trace constants
in the current statements.

### Orbit geometry

See the [geometry blueprint](../../blueprint/src/chapters/geometry.tex).

- The orbit-coordinate inverse identities, regularity, angular seams, area
  formula and level-cutoff coarea are proved without admissions in
  `OrbitCoordinates.lean`. The area argument uses the smooth orbit map's
  constant Jacobian `2` directly on the half-open time domain. Fubini and
  periodicity give integrability of the level integral on closed level bands.
- Period regularity (`lem:period-regularity`) is proved without admissions in
  `Period.lean`: the regular fixed-interval integral gives smoothness and
  `L' < 0`, hence strict decrease of `L` and `S`. Coarse logarithmic bounds
  remain open and come independently from corner dynamics and endpoint distance.
  The full `lem:period-coarse` statement is blueprint-only; its Lean link covers
  just the global upper exponential bound. The elementary lower bound
  `L(h) ≥ ½ log(1/h)` (`lem:period-basic`) is proved.
- Full forward weak-gradient transfer is proved. Reverse transfer remains open;
  see the virial regularization section below.
- Saddle-distance and level-derivative bounds are medium–high; inverse-coordinate
  gradients are moderate and time integrals smaller once those bounds exist.
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

`virial_l2` has no `sorry` of its own. The H¹ commutator identity `virial_h1`
(proved directly on H¹, no truncation), H¹ skew-symmetry, the box periodization
of compactly supported cell functions, uniqueness of weak derivatives and the
equivalence of the two virial forms on `X` have no admissions. All transversal
mollifier lemmas are proved: the commutator from the chart inputs and the transport
chain rule only, the derivative lemmas also from the remaining reverse
weak-gradient rule. The periodization
part of `lem:local-to-global` (`exists_memSobolev_periodize`) is not used.
The only remaining admission of `virial_l2` is
`HasWeakPartialOn.comp_actionAngle` (`lem:action-angle-weak-cell`) in
`TransversalMollifier.lean`: reverse weak-gradient transfer and seam gluing.
Local W¹,¹ approximation is one route, not an available infrastructure result;
the direct test method used for the forward rule is another approach to explore.
The full forward rule `comp_actionAngleInv`, including both coordinate directions,
has no admitted dependencies.

### Transport and later-sector regularity

See the [transport blueprint](../../blueprint/src/chapters/transport.tex) and
[regularity blueprint](../../blueprint/src/chapters/regularity.tex).

The eigenfunction-to-transport bridge is proved. Resonant vanishing is proved from
`lem:coarea`, the area formula and differentiability of `L`. Melnikov is proved from
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
