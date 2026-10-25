# Shared infrastructure status

[Project status](../../STATUS.md) · [Even–even](even-even.md) ·
[Odd–odd](odd-odd.md) · [Mixed](mixed.md)

Current shared capabilities and blockers. Use the
[architecture guide](../architecture.md) to locate modules; exact statements
and proof mechanisms belong in the blueprint and module documentation.

## Available foundations

The even–even route is admission-free, including:

- Fourier/L² setup, symmetry/rotation decompositions and inverse-Laplacian
  regularity. Weak dipole testing and odd cell-pairing identities need
  neither self-adjointness nor Sobolev regularity.
- Torus/local Sobolev bridges, continuous Hölder representatives, ACL slicing,
  rectangle traces and even–even separatrix traces.
- Orbit coordinates, area/coarea, orbit restriction, coarse period bounds,
  saddle-distance/comparison and level-derivative estimates.
- Weak action-angle chain rules in both directions, periodization, transversal
  mollification, H¹ commutator and the annular L² virial.
- Eigenfunction transport, resonant vanishing, Melnikov, canonical profiles
  and pairing limits.
- Interval H¹ and weighted boundary positivity by exhaustion. Abstract
  canonical profiles have weighted interval regularity and identified
  forcing/endpoints; even H² torus functions have the needed arc energy.
  General smooth-density theory is not required by these results.

Reuse requires checking the hypotheses, especially parity/rotation characters,
weights and local versus global regularity.

## Next session

1. **Top-down odd–odd interfaces:** review the explicit analytic inputs in
   [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean), from which the
   exclusion is now assembled. Next expand corrected boundary nonnegativity
   into its scalar and one-dimensional ingredients. Bulk coercivity and its
   certificate remain deferred. See [odd–odd status](odd-odd.md). The earlier
   saddle, H¹ and weighted-gradient derivations remain blueprint mathematics,
   not Lean proofs.
2. **Bounded shared formalization:** coarse period derivative bounds
   (`lem:period-derivative-bounds`, starting in `Period.lean`) and phase-cell
   Hardy division (`lem:phase-cell-division`) are reusable first targets.
3. **Character API:** plan the ±i extension of `Melnikov.lean` and
   `PairingLimit.lean`, preserving the completed ±1 interfaces. The ODE
   character helpers already allow complex characters; check resonant phases
   and conjugation rather than assuming the existing proofs transfer unchanged.

## Open analytic work

- [Transport and regularity](../../blueprint/src/chapters/regularity.tex):
  odd–odd H² quotient division still needs review. The logarithmic gradient
  gain and L² vorticity division now have blueprint derivations.
  The weighted-forcing H¹ route only needs
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
  off the current sector routes. Odd–odd logarithmic multiplication now uses
  coordinate slicing instead. This optional Lean infrastructure remains
  open; inverse Hausdorff–Young or a compact-support Sobolev inequality are
  candidate approaches.
- [Period estimates](../../blueprint/src/chapters/geometry.tex): coarse
  derivative bounds from the regular integral suffice for the transport
  gains; they still need Lean proofs. The odd–odd finite parts now use only
  the leading value asymptotic, with a direct blueprint derivation from the
  defining integral. The elliptic identity and sharp remainders are off all
  sector routes; they remain unproved in Lean. Sharp remainders also need a
  quantified mathematical proof or precise reference; differentiating a
  value O-term is not sufficient.
- `TransportOperator.lean`: self-adjointness/core/group results remain
  admitted and are not prerequisites of either the even–even or odd–odd
  route.
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
