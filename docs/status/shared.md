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
- Torus/local Sobolev bridges, domain-a.e. congruence, local Sobolev gluing,
  volume-preserving affine weak-jet/radial-L² pullback, and periodic Hᵏ_loc
  reconstruction. Local smooth Sobolev multipliers use compact cutoffs,
  without global derivative bounds. The local weak product rule also allows
  smooth multipliers without compact support. Compact C¹ Fourier testing and
  C¹ multiplication for lifted Fourier derivatives are proved in
  `Analysis/FourierC1Multiplier.lean`, without smooth density. The normalized saddle chart instantiates
  the affine interface.
  Continuous Hölder representatives, ACL slicing, rectangle traces and
  even–even separatrix traces.
- Orbit coordinates, area/coarea, orbit restriction, coarse period bounds,
  saddle-distance/comparison and level-derivative estimates.
- Weak action-angle chain rules in both directions, periodization, transversal
  mollification, H¹ commutator and the annular L² virial.
- Eigenfunction transport, resonant vanishing, Melnikov, canonical profiles
  and pairing limits. The generic periodic-to-continuous transport-pair bridge
  is admission-free. The odd–odd stream-H² quotient is assembled from
  explicit local analytic inputs; Hardy–Poisson division and the periodic first
  gain remain admitted. Periodic quotient transport is admission-free.
- Interval H¹ and weighted boundary positivity by exhaustion. Abstract
  canonical profiles have weighted interval regularity and identified
  forcing/endpoints; even H² torus functions have the needed arc energy.
  General smooth-density theory is not required by these results.
- Ordinary exhaustion by stream levels, exact one-dimensional B/β boundary
  normalization, the B-weighted full-level trace and the integrated current
  remainder. These value-only limits use bounded diagonal densities or a
  uniform coefficient error times the logarithmic period, not derivative traces.
  Picone's finite-part assembly remains conditional on separate analytic inputs.
- Bounded-coefficient L² product-integral convergence, using the continuous
  L∞ multiplier and L² inner product, without smooth density or domination.
- Corrected-boundary forcing H¹ regularity, logarithmic correction
  integrability and pointwise β bounds; half-interval Dirichlet estimates
  and both affine correction estimates, including exact logarithmic endpoint
  moments and the midpoint bound. Zero-trace forcing energy/traces and
  corrected-boundary nonnegativity are admission-free; integration by parts
  supplies the energy estimate, and the L² endpoint liminf gives zero traces.

Reuse requires checking the hypotheses, especially parity/rotation characters,
weights and local versus global regularity.

## Next session

1. **Top-down odd–odd interfaces:** review the explicit analytic inputs in
   [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean), from which the
   exclusion is now assembled. Quotient existence is assembled in
   `Regularity/OddOddQuotient.lean`: its stream-H² stage expands to explicit
   local analytic admissions; Hardy–Poisson division and the periodic first gain
   remain outer admissions. Periodic quotient transport is proved directly by
   invariant regularized reciprocals and C¹ torus testing.
   The next local/sector layer is in `Regularity/QuotientLocal.lean` and
   `Regularity/OddOddRegularity.lean`. The weighted third-stream step
   (`lem:dd-weighted-third-stream`) is assembled from the saddle jet and
   weighted gradient: the Hessian trace supplies the weighted vorticity input,
   without ordinary separatrix H³ or a fixed-cell localization bridge.
   Its generic weighted elliptic gain (`lem:elliptic-weighted-third`) and
   Cartesian Taylor correction (`lem:saddle-taylor-correction`) are explicit
   outside-section admissions. The weighted-gradient branch now has a checked
   scalar stage, Logarithmic midpoint data (`lem:dd-log-midpoint`): phase
   division, specified local H¹ derivative, and a common a.e. orbitwise
   reconstruction. The generic midpoint gain has zero transitive admissions;
   the sector assembly retains its existing logarithmic-numerator and five
   scalar/orbit inputs. No new admissions were added. Next is Strong weighted
   quarter derivatives (`lem:dd-quarter-weighted-derivatives`): weak level
   differentiation of the joint reconstruction, logarithmic-length summation,
   then inverse-coordinate transfer and periodic/reflected covering.
   `dd_weighted_gradient` itself remains admitted; its logarithmic numerator
   input and the saddle estimates are also separate in-section proof work.
   The weighted third-stream audit still reaches the saddle and weighted-gradient
   inputs, plus the two outside-section corollaries, stream weak jet and saddle
   factorization. The scalar/geometry batch is now
   stated in `ScalarDivision.lean` and `Regularity/SaddleNormalForm.lean`; cylinder
   inversion and weighted transport/gluing are stated in `Regularity/CylinderInverse.lean`,
   `WeightedTraces.lean` and `WeightedTransport.lean`. The endpoint/resonant-zero,
   weighted numerator and logarithmic interfaces are now stated too, covering
   the quotient branch's result nodes. The stream-H² congruence, local gluing,
   affine pullback and periodic reconstruction bridges are now admission-free:
   `SobolevLocal.lean`, `SobolevGluing.lean`, `AffineJets.lean`,
   `SaddleChartPullback.lean` and `PeriodicSobolev.lean`. Local smooth multiplication
   is proved in `SobolevMultipliers.lean`. `Regularity/StreamQuotientAssembly.lean` now
   assembles `dd_stream_quotient_h2`, with no `sorry` of its own and no stronger
   hypotheses. Next proof work is its recorded local analytic frontier or the
   other quotient stages, not a remaining generic gluing interface.
   `dd_character_virial_limit` is assembled without its own `sorry`, from two
   admissions: local H² smooth approximation and the leading period value
   asymptotic. `OddOddGradientTraces.lean` proves the unchanged even-H² gradient
   limits without admissions by Laplacian reconstruction and the existing
   even–even traces. A shared bounded-value Cauchy–Schwarz estimate handles
   the nonzero mean; one rescaled null set serves all three limits.
   Truncated virial follows from the annular identity;
   local H¹ division, coefficient bounds and center removal are proved without
   quotient existence. Weighted differential algebra is also admission-free;
   a generic cutoff-to-annular extraction handles common exceptional sets.
   Annular virial is assembled from `dd_cutoff_identity`, now itself proved
   from the assembled weak Green identity, proved weighted first identity and
   proved quotient equation, with admission-free pointwise boundary-flux algebra.
   Normal–tangent orthogonality and `-μq = (8-s³)/3` give the flux identification, with the inward
   normal convention unchanged. Coarea and endpoint assembly are checked.
   The weak Green proof uses the admitted local H² approximation
   interface in `SobolevApproximation.lean`. Its quadratic-integral limit and
   pointwise cutoff-generator helpers are proved. The local classical Green
   identity is now admission-free, by direct flux differentiation and the constant
   weighted defect. Its smooth annular cutoff integration is now admission-free
   too: the cutoff flux is globally C¹ and compactly supported, and the half-density
   correction has the required sign. Weak-operator jet identification and strong L²
   operator stability are now admission-free, without a derivative of the forcing.
   Weak Green is now assembled: on a compact regular cutoff patch its four
   integrands are finite bounded-coefficient quadratic forms, so their integrals
   converge under strong L² approximation. Its only transitive admission is the
   local H² density theorem; the original hypotheses are unchanged. The cutoff and
   truncated-virial audits now reach only that density theorem.
   `OddOddQuotientEquations.lean` proves the raw and supplied-data Poisson
   equations, weighted cell unitary map and classical conjugation without
   admissions. The flux `s∇ψ - ψ∇s` uses only mean-zero Poisson and local
   division, not transport, parity, global quotient existence or density.
   Multiplying back by Ψ identifies arbitrary raw weak gradients with
   Fourier stream derivatives and proves half-density conjugation. Annular
   normal-field factorization and the unweighted L² virial prove the weighted
   first identity without admissions, global divided regularity or parity.
   Raw/supplied quotient changes, coarea splitting,
   `ε = 2h` exceptional-set rescaling and common pairing selection are checked.
   These admitted inputs are the virial frontier; the leading period value
   asymptotic in `Period.lean` remains separate from sharp remainders.
   `OddOddRenormalizedBulk.lean` assembles the unchanged full bulk limit by
   ordinary exhaustion, reaching only `orbitPeriod_leading_asymptotic`.
   `OddOddGradientIntegrability.lean` proves both gradient energies without
   admissions. `EvenGradientHardy.lean` supplies diagonal cosine division using
   ACL zero traces and primitive Hardy averaging. Bounded normalized ground
   derivatives preserve this class under the Picone quotient rule, with no
   bounded-value or density assumption.
   `OddOddFinitePart.lean` proves the exact scalar coefficient integral without
   admissions, and its finite part relative only to the leading period
   asymptotic. That input is still admitted in `Period.lean`; sharp remainders
   and the elliptic identity are not needed.
   `OddOddPotentialMass.lean` reaches that same period admission:
   two-saddle interpolation and coordinate exchange leave an integrable Hölder remainder.
   Generic weighted forcing integrability and its vorticity specialization are admission-free in
   `OddOddBulkIntegrability.lean`: the explicit bound `0 ≤ Fd² ≤ 16π²` supplies
   a bounded multiplier of the integrable weighted square.
   `dd_truncated_picone` and potential integrability are transitively admission-free.
   `OddOddGroundResidual.lean` factors the actual differentiated residual into
   a polynomial in bounded coordinates, giving a uniform bound and potential
   integrability for all L² data, independently of its sign. Ground estimates,
   quadratic Fourier cutoff testing, annular extraction and current continuity
   supply the truncated identity without density or gradient traces.
   `Picone.lean` proves the shared classical algebra and integrated identity;
   its generic integrated interface assumes a divergence formula, while the
   truncated application instead uses the Fourier cutoff route. The current's
   B-weighted trace is admission-free in `OddOddBoundaryTrace.lean`: a square-root
   bound for B cancels the quarter graph's time Jacobian and gives dominated
   convergence on a fixed finite interval. `OddOddCurrentRemainder.lean` proves
   the integrated remainder by a uniform `64ε` coefficient error and the coarse
   logarithmic period bound. `OddOddValueFinitePart.lean` proves the scalar
   value finite part: shared squared-value Hölder continuity controls exponential
   endpoint tails and the integrated orbit error. Arc-remainder integrability
   has zero admissions; the value finite part and ground-current limit reach
   only `orbitPeriod_leading_asymptotic`, already shared by the bulk finite part.
   Corrected-boundary nonnegativity and all its interval inputs are
   admission-free in `CorrectedBoundaryForm.lean`; no corrected-boundary
   analytic admissions remain. The two transitive Picone inputs remain proof work.
   Bulk coercivity is assembled through the weighted-domain bridge and separate
   gradient/potential bounds. Weighted mass/finite integrals and the constrained
   mean estimate are proved; a completed square removes Kantorovich from the
   route. The weighted form-domain bridge and ground-state/matrix bounds are
   admission-free too. Global C¹ reciprocal regularity proves the domain without
   Picone energy or point removal. The non-certificate bulk route is closed:
   central-parity Poincaré and the bulk gradient bound are admission-free.
   The weighted zonal basis, cutoff weak pairings, coefficient parity and Bessel
   give Poincaré on the original maximal weak domain, with exact physical
   mean/variance and Cartesian-energy normalization. No weighted Sobolev
   density or boundary trace hypothesis is used; see [odd–odd status](odd-odd.md).
   The coefficient assembly uses the
   admitted residual identity/sign, excluded from the current breadth-first
   traversal; see [odd–odd status](odd-odd.md). The prior recursive statement pass
   covers nodes below odd–odd exclusion, including the weighted spectral inputs.
   The certificate chapter's
   statements and explicit operator identities are in `BernsteinCertificates.lean`,
   `MixedComparison.lean` and `PolynomialInequalities.lean`, with `sorry` proofs.
   No coefficient checker or subdivision dataset is implemented, and no backend
   is selected. Exact certificate verification and the other analytic branches
   remain open; statement markers are not a compatibility audit.
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
   The stream-H² local/global compatibility is checked by
   `Regularity/StreamQuotientAssembly.lean`: remove the point before smooth multiplication,
   restrict to nonzero inverse-factor neighbourhoods, transform all derivative
   indices, identify local representatives a.e., and reconstruct via the tensor
   angular cutoff. Its analytic input proofs remain separate.
   Angular Hardy and mixed saddle linearization are off the odd–odd route.
3. **Character API:** plan the ±i extension of `Melnikov.lean` and
   `PairingLimit.lean`, preserving the completed ±1 interfaces. The ODE
   character helpers already allow complex characters; check resonant phases
   and conjugation rather than assuming the existing proofs transfer unchanged.

## Open analytic work

The chapter-specific Lean interfaces and quotient assembly are grouped in
[`NoEmbeddedEigenvalues/Regularity/`](../../NoEmbeddedEigenvalues/Regularity/).
Declarations use the namespace `NoEmbeddedEigenvalues`. Shared analytic
prerequisites remain outside this directory; see the
[module map](../architecture.md#eigenfunction-regularity).

- [Transport and regularity](../../blueprint/src/chapters/regularity.tex):
  odd–odd H² quotient division now has an explicit dyadic/cone blueprint
  derivation, as does the logarithmic gradient gain. Once the even stream
  quotient is H², coordinate Hardy plus Poisson gives the L² vorticity
  quotient; its separate angular-Hardy argument is unnecessary.
  Even H² also implies the advertised extra corner bounds, so the bundled
  quotient-domain proposition is downstream and off the exclusion route.
  Invariant-cutoff testing avoids global transport-operator closedness.
  The quotient and representative-change assemblies are proved in Lean.
  Stream-H² expands to explicit local analytic admissions;
  Hardy–Poisson division and the periodic first gain remain the other two outer
  quotient admissions. Periodic quotient transport is proved directly on the torus.
  The periodic first gain includes
  cell covering beyond the fixed neighbourhood's boundary saddles.
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
  The shared jet, saddle normalization, endpoint Hardy and local elliptic
  prerequisites have substantive Blueprint derivations with explicit proof
  dependencies; their Lean proofs remain admitted. Cylinder inversion and
  corner traces/gluing also still need Lean proofs. Elliptic-center regularity
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
- [Certificates](../../blueprint/src/chapters/certificates.tex): all chapter
  statements are linked, including operator-to-residual identities. Proofs remain
  `sorry`. The original verification scripts and generated data are missing;
  polynomialization and any exact checker must still be proved sound. The
  statements do not require choosing Bernstein subdivision as the final method.

## Blueprint navigation

Graph statement popups include clickable **Depends on** and **Used by** lists,
using Blueprint labels and the direct edges visible in the current full or
sector/custom graph. Status dots copy each node's graph fill and border colours.
See [Blueprint navigation](../../blueprint/README.md#building).

## Other open work

- Human statement review, particularly setup, sector reduction, interval
  representatives and the weighted boundary domain.
- `lem:sector-projections` lacks a linked Lean statement/proof of the full
  orthogonal-projection claim; current exclusion assembly does not need it.
- Publishing: no Git remote is configured. Blueprint URLs, declaration
  checking and docgen/Pages configuration remain; see
  [blueprint setup](../../blueprint/README.md#publication-setup).
