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

`LineMollifier.lean` and `AnglePeriodization.lean` have no admissions.
The basic transversal L² estimates and weak action-angle transport equivalence
have no `sorry` of their own, but still depend on admitted chart/coarea inputs.
Transversal support is proved without those admitted dependencies.

## Analytic backlog

Difficulty assessments below come from a first-pass review, not a complete
proof audit or timing estimate.

### Sobolev and traces

See the [analysis blueprint](../../blueprint/src/chapters/analysis.tex).

- Hölder embedding and the torus/local-Sobolev bridge: moderate.
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

- Inverse identities → local smoothness → area formula are separate tasks.
  The first two are moderate; measure/change-of-variables assembly is
  medium–high. Local smoothness does not depend on the area formula.
- Period regularity comes from the regular fixed-interval integral. Coarse
  logarithmic bounds come independently from corner dynamics and endpoint
  distance. The full `lem:period-coarse` statement is blueprint-only; its Lean
  link covers just the global upper exponential bound.
- The smooth action-angle chart is moderate conditional on these inputs;
  full weak-gradient transfer is medium–high. General chain rules use local
  W¹,¹ approximation; compact-band H¹ specializations may suffice for virials.
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

`virial_l2` has no `sorry` of its own. H¹ skew-symmetry, the box periodization
of compactly supported cell functions, uniqueness of weak derivatives and the
equivalence of the two virial forms on `X` have no admissions. The periodization
part of `lem:local-to-global` (`exists_memSobolev_periodize`) is not used.
Remaining admitted inputs of `virial_l2`, in a candidate order:

1. `transversalMollifier_hasWeakL0On`: moderate conditional on chart inputs.
   Combine the proved weak transport equivalence with line weak derivatives,
   the Lipschitz commutator, and compact-band/zero-extension estimates.
   Full-gradient chain rules are not needed for this commutator.
2. `transversalMollifier_hasWeakPartialOn` and
   `tendsto_transversalMollifier_partial`: medium–high (full-gradient transfer).
   The gradient error must be o(1/ε), not just O(1/ε).
3. `virial_h1`: moderate. Fourier truncation, continuity of the two quadratic
   forms on H¹ and the smooth identity; skew-symmetry is already available.
4. Shared with other routes: `hasWeakPartialOn_liftL2` (`lem:local-to-global`),
   `isTransportPair_of_isEigenSolution` and the chart/coarea inputs.

### Transport and later-sector regularity

See the [transport blueprint](../../blueprint/src/chapters/transport.tex) and
[regularity blueprint](../../blueprint/src/chapters/regularity.tex).

The eigenfunction-to-transport bridge is moderate; resonant vanishing and
Melnikov are medium–high. Canonical-profile uniqueness/decay/weighted bounds
are moderate; good windows are low–moderate. Pairing-limit assembly is high,
with representative compatibility and common exceptional sets the main work.
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
