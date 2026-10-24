# Shared infrastructure status

[Project status](../../STATUS.md) · [Even–even](even-even.md) ·
[Odd–odd](odd-odd.md) · [Mixed](mixed.md)

Current shared capabilities and blockers. Use the
[architecture guide](../architecture.md) to locate modules; exact statements
and proof mechanisms belong in the blueprint and module documentation.

## Available foundations

The even–even route is admission-free, including:

- Fourier/L² setup, symmetry/rotation decompositions and inverse-Laplacian
  regularity.
- Torus/local Sobolev bridges, continuous Hölder representatives, ACL slicing,
  rectangle traces and even–even separatrix traces.
- Orbit coordinates, area/coarea, orbit restriction, coarse period bounds,
  saddle-distance/comparison and level-derivative estimates.
- Weak action-angle chain rules in both directions, periodization, transversal
  mollification, H¹ commutator and the annular L² virial.
- Eigenfunction transport, resonant vanishing, Melnikov, canonical profiles
  and pairing limits.
- Interval H¹ and weighted boundary positivity by exhaustion. General
  smooth-density theory is not required by these results.

Reuse requires checking the hypotheses, especially parity/rotation characters,
weights and local versus global regularity.

## Next session

1. **Mathematical review first:** continue the odd–odd logarithmically
   weighted quotient estimates and double division in the
   [transport](../../blueprint/src/chapters/transport.tex) and
   [regularity](../../blueprint/src/chapters/regularity.tex) chapters.
   The first two transport gains, cylinder inverse and ordinary H¹
   separatrix gain now have explicit blueprint derivations, not Lean proofs.
   Review these arguments before translating them to Lean.
2. **Bounded shared formalization:** coarse period derivative bounds
   (`lem:period-derivative-bounds`, starting in `Period.lean`) and phase-cell
   Hardy division (`lem:phase-cell-division`) are reusable first targets.
3. **Character API:** plan the ±i extension of `Melnikov.lean` and
   `PairingLimit.lean`, preserving the completed ±1 interfaces. The ODE
   character helpers already allow complex characters; check resonant phases
   and conjugation rather than assuming the existing proofs transfer unchanged.

## Open analytic work

- [Transport and regularity](../../blueprint/src/chapters/regularity.tex):
  odd–odd logarithmically weighted gradient and quotient division work still
  need review. The weighted-forcing H¹ route only needs
  `f/d², ∇f/d^(3/2) ∈ L²`, covering both the odd–odd quadratic jet and mixed
  zero-jet remainder. Zero forcing on an edge and a weighted corner trace
  force zero vorticity trace, without a midpoint condition. Crossing-edge
  H¹ gluing has an explicit cutoff proof. These derivations, the first two
  transport gains and cylinder inverse are not yet in Lean.
  The transport gains cover all four characters without Melnikov;
  implemented Melnikov/pairing results still only accept ±1.
  Local elliptic regularity, corner traces/gluing and interval Hardy inputs
  still need Lean proofs. Elliptic-center regularity is not a prerequisite.
- [Finite-p Sobolev embedding](../../blueprint/src/chapters/analysis.tex):
  outside the even–even route; inverse Hausdorff–Young or a compact-support
  Sobolev inequality are candidate approaches.
- [Period estimates](../../blueprint/src/chapters/geometry.tex): coarse
  derivative bounds from the regular integral suffice for the transport
  gains; they still need Lean proofs. The odd–odd finite parts now use only
  the leading value asymptotic, with a direct blueprint derivation from the
  defining integral. The elliptic identity and sharp remainders are off all
  sector routes; they remain unproved in Lean. Sharp remainders also need a
  quantified mathematical proof or precise reference; differentiating a
  value O-term is not sufficient.
- `TransportOperator.lean`: self-adjointness/core/group results remain
  admitted and are not prerequisites of the even–even proof.
- [Certificates](../../blueprint/src/chapters/certificates.tex): odd–odd/mixed
  verification scripts and data are missing. A sound exact checker must
  connect coefficient data to the defining expressions, not merely check tables.

## Other open work

- Human statement review, particularly setup, sector reduction, interval
  representatives and the weighted boundary domain.
- `lem:sector-projections` lacks a linked Lean statement/proof of the full
  orthogonal-projection claim; current exclusion assembly does not need it.
- Publishing: no Git remote is configured. Blueprint URLs, declaration
  checking and docgen/Pages configuration remain; see
  [blueprint setup](../../blueprint/README.md#publication-setup).
