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

1. **Mathematical review first:** audit the first saddle gain
   (`lem:transport-first-gain`, `prop:saddle-first-gain`) and cylinder inverse
   (`lem:cylinder-inverse`) in the [transport](../../blueprint/src/chapters/transport.tex)
   and [regularity](../../blueprint/src/chapters/regularity.tex) chapters.
   Review the new weighted-forcing statements before translating them to Lean;
   their blueprint derivations are not formal proofs.
2. **Bounded shared formalization:** coarse period derivative bounds
   (`lem:period-derivative-bounds`, starting in `Period.lean`) and phase-cell
   Hardy division (`lem:phase-cell-division`) are reusable first targets.
3. **Character API:** plan the ±i extension of `Melnikov.lean` and
   `PairingLimit.lean`, preserving the completed ±1 interfaces. The ODE
   character helpers already allow complex characters; check resonant phases
   and conjugation rather than assuming the existing proofs transfer unchanged.

## Open analytic work

- [Transport and regularity](../../blueprint/src/chapters/regularity.tex):
  first saddle gain, cylinder inverse and odd–odd weighted quotient work
  need review. The mixed zero-jet case has a separate weighted-forcing H¹
  derivation, with numerator and phase-cell estimates, not yet in Lean.
  Generic gains remain tentative; zero-edge trace requires zero forcing
  as well as zero midpoint value. All four rotation characters are needed;
  implemented Melnikov/pairing results only accept ±1.
  Local elliptic regularity, corner traces and interval Hardy inputs remain
  open. Elliptic-center regularity is not a sector prerequisite.
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
