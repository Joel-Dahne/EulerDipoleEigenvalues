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

## Open analytic work

- [Transport and regularity](../../blueprint/src/chapters/regularity.tex):
  transport gains and weighted saddle/quotient domains need digestion.
  The gains must cover all four rotation characters; implemented Melnikov
  and pairing limits only cover ±1. Local elliptic regularity, weighted
  corner traces and interval Hardy inputs remain open. The
  [transport blueprint](../../blueprint/src/chapters/transport.tex) records
  tentative gain hypotheses. Its zero-edge conclusion needs both zero
  midpoint value and zero forcing trace. Elliptic-center regularity is
  separate and no longer a prerequisite of either remaining sector exclusion.
- [Finite-p Sobolev embedding](../../blueprint/src/chapters/analysis.tex):
  outside the even–even route; inverse Hausdorff–Young or a compact-support
  Sobolev inequality are candidate approaches.
- [Elliptic period identity and sharp asymptotics](../../blueprint/src/chapters/geometry.tex):
  outside the even–even route. Sharp value/derivative remainders need a
  quantified proof or precise reference; differentiating a value O-term is
  not sufficient.
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
