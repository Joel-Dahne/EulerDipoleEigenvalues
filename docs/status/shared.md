# Shared infrastructure status

[Project status](../../STATUS.md) · [Even–even](even-even.md) ·
[Odd–odd](odd-odd.md) · [Mixed](mixed.md)

Current shared capabilities and blockers. Use the
[architecture guide](../architecture.md) to locate modules; exact statements
and proof mechanisms belong in the blueprint and module documentation.

## Available foundations

The even–even route is admission-free. Available foundations include:

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
  and pairing limits. The generic periodic-to-continuous transport-pair bridge
  is admission-free; minimal odd–odd quotient existence is assembled from
  four explicit admitted inputs.
- Interval H¹ and weighted boundary positivity by exhaustion. Abstract
  canonical profiles have weighted interval regularity and identified
  forcing/endpoints; even H² torus functions have the needed arc energy.
  General smooth-density theory is not required by these results.
- Ordinary exhaustion by stream levels and exact one-dimensional B/β
  boundary normalization. Picone's finite-part assembly is conditional on
  separate analytic integrability and trace inputs.
- Corrected-boundary forcing H¹ regularity, logarithmic correction
  integrability and pointwise β bounds; half-interval Dirichlet estimates
  and the exact positive-central affine correction. Boundary nonnegativity
  is conditional on three further interval estimates.

Reuse requires checking the hypotheses, especially parity/rotation characters,
weights and local versus global regularity.

## Next session

1. **Top-down odd–odd interfaces:** review the explicit analytic inputs in
   [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean), from which the
   exclusion is now assembled. Quotient existence is assembled in
   `OddOddQuotient.lean` from four admitted inputs. The current pass is
   statements only: `QuotientLocal.lean` and `OddOddRegularity.lean` state the
   next local/sector layer with `sorry`. The scalar/geometry batch is now
   stated in `ScalarDivision.lean` and `SaddleNormalForm.lean`; cylinder
   inversion and weighted transport/gluing are stated in `CylinderInverse.lean`,
   `WeightedTraces.lean` and `WeightedTransport.lean`. The endpoint/resonant-zero,
   weighted numerator and logarithmic interfaces are now stated too, covering
   the quotient branch's result nodes. The stream-H² compatibility review
   identifies affine weak-jet/radial-L² pullback, domain-a.e. congruence and
   periodic gluing as the next interface bridges, before choosing proof work.
   `OddOddVirial.lean` now states the entire missing weighted-virial layer below
   `dd-character-virial-limit`, including the bundled quotient/operator E definition;
   `Period.lean` separately states the leading value asymptotic. The new proofs
   remain `sorry`. Next review the raw/supplied quotient bridge, inward normal
   convention, `ε = 2h` exceptional-level rescaling and common pairing subsequence.
   The `dd-truncated-picone` dependency closure is also stated: `Picone.lean`
   supplies the shared classical identities with `sorry` proofs. Its integrated
   version consumes the outward divergence formula and integrability, not a
   Sobolev extension or singular-point removal. Continue the statement pass;
   the compatibility review and analytic proofs remain deferred.
   The three corrected-boundary estimates and eight Picone inputs remain
   separate work.
   Bulk coercivity and its certificate remain deferred.
   See [odd–odd status](odd-odd.md). The earlier
   saddle, H¹ and weighted-gradient derivations remain blueprint mathematics,
   not Lean proofs.
2. **Shared interface review:** check the uniform complete-cell estimates
   needed for logarithmic summation, canonical interval traces and compatibility
   of Cartesian/orthonormal saddle quadratics. Orbit numerators must use the
   continuous forcing representative, not raw values on exceptional orbits.
   Check real cylinder exponents, finite harmonic jets, one-sided trace
   matching and the whole-edge forcing hypothesis. Shared jet/trace/quadratic
   data now sit below their parent interfaces; saddle geometry no longer
   imports eigenfunction regularity. Ordinary saddle/separatrix interfaces,
   logarithmic estimates and weighted gradients now occupy separate layers.
   Check cutoff restriction of the quantitative numerator data, agreement of
   canonical ray traces and the distinction between local lifted bulk norms
   and finite norms on bounded representative collars.
   For stream H², remove the point for the double quotient V before smooth
   multiplication, and shrink disks/rectangles before taking inverse factors.
   Coordinate changes mix derivative indices; the first-order diagonal chain
   rule is not yet a higher-order affine-jet interface. Localization of one
   cut-off piece is not yet the periodic gluing interface. Reuse the private
   domain-a.e. congruence proof in `TransversalMollifier.lean` instead of adding
   an admission. After local Sobolev gluing on the lift, tensor/rescale the
   existing `anglePartition` and use `memSobolev_compactPeriodize` to avoid
   constructing a new partition of unity on the torus.
   Angular Hardy and mixed saddle linearization are off the odd–odd route.
3. **Character API:** plan the ±i extension of `Melnikov.lean` and
   `PairingLimit.lean`, preserving the completed ±1 interfaces. The ODE
   character helpers already allow complex characters; check resonant phases
   and conjugation rather than assuming the existing proofs transfer unchanged.

## Open analytic work

- [Transport and regularity](../../blueprint/src/chapters/regularity.tex):
  odd–odd H² quotient division now has an explicit dyadic/cone blueprint
  derivation, as does the logarithmic gradient gain. Once the even stream
  quotient is H², coordinate Hardy plus Poisson gives the L² vorticity
  quotient; its separate angular-Hardy argument is unnecessary.
  Even H² also implies the advertised extra corner bounds, so the bundled
  quotient-domain proposition is downstream and off the exclusion route.
  Invariant-cutoff testing avoids global transport-operator closedness.
  The quotient and representative-change assemblies are proved in Lean;
  four analytic interfaces remain admitted. The periodic first gain explicitly
  includes cell covering beyond the fixed neighbourhood's boundary saddles.
  The weighted-forcing H¹ route only needs
  `f/d², ∇f/d^(3/2) ∈ L²`, covering both the odd–odd quadratic jet and mixed
  zero-jet remainder. Zero forcing on an edge and a weighted corner trace
  force zero vorticity trace, without a midpoint condition. Crossing-edge
  H¹ gluing has an explicit cutoff proof. The first two transport gains and
  the sector saddle/separatrix/gradient interfaces are now stated with `sorry`.
  Scalar Hardy/phase-cell and explicit saddle-chart interfaces are also stated.
  Cylinder inversion and the weighted H¹/corner/edge/gluing layer are now
  stated too, as are the quarter endpoint/resonant-zero and weighted/logarithmic
  numerator interfaces. Quantitative bounds and actual fiber integrability
  are explicit. No new analytic proofs were supplied in the statement pass.
  The transport gains cover all four characters without Melnikov;
  implemented Melnikov/pairing results still only accept ±1.
  Local elliptic regularity, cylinder inversion, corner traces/gluing and
  interval Hardy inputs still need Lean proofs. Elliptic-center regularity
  is not a prerequisite.
- [Finite-p Sobolev embedding](../../blueprint/src/chapters/analysis.tex):
  off the current sector routes. Odd–odd logarithmic multiplication now uses
  coordinate slicing instead. This optional Lean infrastructure remains
  open; inverse Hausdorff–Young or a compact-support Sobolev inequality are
  candidate approaches.
- [Period estimates](../../blueprint/src/chapters/geometry.tex): coarse
  derivative bounds from the regular integral suffice for the transport
  gains; they are stated in `ScalarDivision.lean` and still need Lean proofs.
  Smoothness and strict decrease were already proved in `Period.lean`.
  The odd–odd finite parts now use only
  the leading value asymptotic, stated separately in `Period.lean`, with a direct
  blueprint derivation from the defining integral. The elliptic identity and sharp remainders are off all
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
