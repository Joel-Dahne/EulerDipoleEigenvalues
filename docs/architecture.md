# Architecture and navigation

An on-demand map, not a progress report or a required session read.
Start with [STATUS.md](../STATUS.md) for current priorities; consult the
relevant module docstrings and blueprint nodes for exact statements and
proof mechanisms. Module names below are relative to
`NoEmbeddedEigenvalues/`.

## Mathematical sources and audit entry points

- `Manuscript/eigenvalues.tex`: unchanged original reference, not a trusted proof.
- `Manuscript/manuscript.tex`: reworked paper, updated with the authors'
  agreement once the corresponding argument has settled. Both manuscripts
  build into `Manuscript/build`.
- `blueprint/src/content.tex`: ordered chapter list; `chapters/*.tex` contains
  setup, symmetry, geometry, analysis, virial, transport, sector arguments,
  regularity, certificates and digest notes.
- `blueprint/src/macros/common.tex`: shared theorem environments and notation
  (`\T \R \Z \N \C`, `\Div`, `\Dom`, `\Cell`, `\ip{}{}`, …).
  `macros/print.tex` supplies no-op blueprint macros for the PDF.
- `Challenge.lean`, `Solution.lean`, `comparator.json`: external statement
  boundary, library bridges, and permitted axioms. See the change restrictions
  in [AGENTS.md](../AGENTS.md).
- `NoEmbeddedEigenvalues.lean`: library root importing every module.

## Find a Lean capability

### Fourier setup, symmetry and representatives

- `TorusL2.lean`, `Fourier.lean`: torus measure, L², characters,
  coefficients, Hilbert basis, Parseval and bounded Fourier multipliers.
- `Setup.lean`, `Derivatives.lean`, `SobolevTorus.lean`: inverse Laplacian,
  transport domain and eigenvalue equation; Fourier/weak derivatives;
  Fourier-defined Sobolev spaces and elliptic regularity of the inverse Laplacian.
- `Symmetry.lean`, `SymmetryL2.lean`, `Sectors.lean`: pointwise symmetries,
  their L² action, reflection sectors and rotation characters.
- `DipoleOrthogonality.lean`: four-mode weak dipole testing, inverse-Laplacian
  pairings and reflection/cell integral identities.
- `SobolevHolder.lean`: continuous Fourier representative, Hölder embedding and
  the shared one-half Hölder estimate for squared values.

### Local Sobolev spaces, lifts and traces

- `SobolevLocal.lean`: weak derivatives, local Sobolev spaces and weighted norms.
- `SobolevGluing.lean`: neighbourhood-wise local Sobolev regularity and gluing
  of representatives agreeing a.e.; separate from torus periodization.
- `SobolevMultipliers.lean`: local multiplication by smooth factors and
  division by smooth nonvanishing real factors, via compact cutoffs.
- `LocalJets.lean`: Euclidean disk/axis geometry, specified weak and classical
  complex jets, integer and real-power radial integrability, energies and the
  Sobolev/jet interface.
- `SobolevApproximation.lean`: local H² smooth-approximation interface on
  precompact patches, and bounded-coefficient L² product-integral stability.
- `AffineJets.lean`: volume-preserving affine pullback of weak derivatives,
  full specified jets, Sobolev regularity and radius-preserving radial L² bounds.
- `SaddleChartPullback.lean`: the explicit normalized saddle chart instantiated
  in the affine Sobolev/jet/radial interface.
- `StreamJet.lean`: the canonical second stream jet from the existing Fourier
  partial multipliers, and its weak-jet interface.
- `QuotientLocal.lean`: division/removal, coordinate Hardy, local/dyadic elliptic,
  invariant division and first/second transport-gain interfaces.
- `WeightedTraces.lean`: canonical transverse, radial, cell-edge and separatrix
  trace data; weighted corner trace and crossing-edge H¹ gluing interfaces.
- `CylinderInverse.lean`: parity/nonresonance data, the physical weighted
  cylinder inverse and smooth harmonic remainder with finite Taylor jets.
- `LiftTorus.lean`, `LiftIntegration.lean`: classical/Fourier derivative
  correspondence, smooth lifts and integration by parts over `[0, 2π]²`.
- `LiftPeriodization.lean`: compact-test periodization, integral unfolding,
  H¹ transport tests, and transfer of torus Sobolev/transport relations to lifts.
- `LocalToGlobal.lean`: periodization of compactly supported local Sobolev data.
- `PeriodicSobolev.lean`: compact tensor angular partition and reconstruction
  of torus Hᵏ data from a periodic Hᵏ_loc lift.
- `CellPeriodization.lean`: box periodization of compactly supported cell data
  and uniqueness of weak derivatives.
- `ACLSlicing.lean`, `DiagonalACL.lean`: ACL representatives and diagonal slicing.
- `TraceL2.lean`, `TraceH2.lean`, `TraceGagliardo.lean`: rectangle trace package.
  `HardyAverage.lean` and `OddHardy.lean`: averaging and odd-function Hardy estimates.
- `ScalarDivision.lean`: canonical-trace endpoint/second Hardy, coarse period
  derivative and uniform complete-cell/global quotient interfaces, for all four
  quarter characters.
- `LogarithmicWeights.lean`: level/torus/lift/radial weights, the rectangle
  multiplier and logarithmic phase-cell division interfaces.
- `DiagonalCalculus.lean`, `SegmentEstimates.lean`: diagonal calculus and
  restrictions to segments/hyperbolas near a line.
- `SeparatrixTraces.lean`: line representatives, even–even arc/level traces,
  arc energy and corner tails; `QuarterOrbits.lean` gives explicit quarter graphs.

### Flow, orbit geometry and transport

- `DipoleCalculus.lean`, `Cells.lean`, `SeparatrixArc.lean`: dipole identities,
  cells/critical sets, diagonal square and explicit heteroclinic arc.
- `SaddleNormalForm.lean`: normalized Cartesian quadratics, explicit orthonormal
  saddle charts and sinc factor; parity, differentiated Taylor bounds and
  quadratic compatibility. Independent of the eigenfunction regularity modules.
- `SmoothIntervalIntegral.lean`, `Period.lean`: smooth parameter integrals and
  period function.
- `DipoleFlow.lean`, `OrbitCoordinates.lean`: global flow, orbit/period relation,
  orbit coordinates, level integrals, area formula, coarse period bounds,
  saddle distance, orbit comparison and level-derivative estimates.
  Time-gradient bounds use separately recentered quarter patches, not a
  single global time coordinate.
- `Transport.lean`, `TransportODE.lean`: weak transport pairs, finite-interval
  ODE/pairing estimates, periodic uniqueness and AC composition utilities.
- `QuarterCoordinates.lean`: cell collars, recentered quarter domains/maps,
  endpoint rays and canonical radial/transverse trace data.
- `OrbitNumerators.lean`: endpoint ACL/local-L² data, resonant numerator zeros
  and the independent divisor-geometry interfaces, for all four characters.
- `WeightedNumerators.lean`: compatible numerator derivatives, canonical ray
  traces, fiber integrability and exported quantitative subinterval bounds.
- `WeightedTransport.lean`: zero-saddle first gain, weighted forcing/H¹ and
  whole-edge zero-trace interfaces, with weak recentered quarter derivatives.
- `OrbitRestriction.lean`, `ResonantVanishing.lean`: restriction to almost every
  orbit, orbitwise mode equations and resonant vanishing.
- `CanonicalProfile.lean`: canonical arc transport profile and weighted estimates.
- `EigenfunctionTransport.lean`: invariant cell neighbourhood and representative
  changes for eigenfunction transport pairs and level integrals.
- `Melnikov.lean`, `PairingLimit.lean`: Melnikov condition, forcing comparison,
  quarter/full pairing limits and eigenfunction specializations.
- `TransportOperator.lean`: unbounded `H = -iL₀`, self-adjointness/core/group
  statements. This is a separate route, not required by the even–even exclusion.

### Virials and regularization

- `NormalField.lean`, `VirialAlgebra.lean`: normal-field algebra and pointwise
  commutator identities.
- `NormalVirial.lean`: bulk/level densities, annular virial, center limit and
  truncated normal-field virial, without reflection-sector assumptions.
- `VirialSmooth.lean`, `VirialQuadratic.lean`, `VirialFourier.lean`: smooth
  identities, torus inner-product forms and Fourier integration by parts.
- `LineMollifier.lean`, `AnglePeriodization.lean`: one-variable mollification,
  periodic angular tests and a compact angular partition.
- `TransversalMollifier.lean`: weak action-angle chain rules and level-variable
  regularization; `VirialL2.lean`: H¹ commutator and L² virial for annular fields.

### Interval boundary forms and sector assembly

- `Picone.lean`: finite-dimensional symmetric-matrix Picone algebra, classical
  planar differential identities and an integrated identity conditional on
  integrability and the outward divergence formula for the actual current.
- `DuBoisReymond.lean`, `IntervalH1.lean`, `IntervalH1Estimates.lean`:
  interval weak calculus, endpoint traces, estimates and vanishing layers.
- `BoundaryForm.lean`, `WeightedBoundary.lean`, `WeightedBoundaryForm.lean`:
  classical positivity, weighted second-order domain, completion of squares,
  affine splitting and positivity by interval exhaustion.
- `CorrectedBoundaryForm.lean`: logarithmic β bounds, forcing H¹ regularity,
  absolute correction integrability, rational affine estimates and the
  equal/opposite endpoint assemblies.
- `FlowBoundaryForm.lean`, `CanonicalBoundaryForm.lean`: flow-time to
  `ξ = tanh s` transformation and identification of the canonical arc form.
- `IntervalZeroExtension.lean`: jump-free zero extension of zero-trace H¹
  data, and complex primitive/zero-extension helpers used by `TraceH2.lean`.
- `EvenEvenBoundary.lean`: even–even gradient traces, arc absolute continuity,
  even H² arc estimates via Laplacian reconstruction, abstract canonical
  profile interval regularity, and canonical arc positivity.
- `EvenEven.lean`: cell-vanishing bridges, nonnegative exhaustion and exclusion
  assembly, ending directly with vanishing of the vorticity.
- `OddOddSaddle.lean`: eigenfunction saddle estimates, weaker forcing weights
  and ordinary separatrix H¹/H³ interfaces.
- `OddOddLogarithmic.lean`: logarithmic bulk/ray forcing and numerator interfaces,
  using one fixed canonical stream jet.
- `OddOddRegularity.lean`: weighted vorticity gradient and third stream jet;
  sits above the ordinary and logarithmic layers without circular imports.
- `StreamQuotientAssembly.lean`: saddle division/removal, regular-edge chart
  covering, local smooth division, gluing and reconstruction of the H² stream
  quotient from the lower local analytic inputs.
- `OddOddQuotient.lean`: minimal quotient data, stream H²/Hardy–Poisson/weak
  invariant division/periodic gain interfaces, the generic continuous-forcing
  transport-pair bridge, and quotient-existence assembly.
- `OddOddForms.lean`: quotient orthogonality, boundary data, continuous
  characters and boundary regularity; bulk forms, truncated Picone energies,
  currents and common renormalization data. Sits below the weighted virial.
- `OddOddVirial.lean`: classical and weak quotient operators, weighted virial
  algebra and Green flux, raw-quotient annular/truncated identities, even H²
  gradient traces. Positive-truncation H¹
  division, weak-witness uniqueness, coefficient bounds and center-flux removal
  assemble the truncated identity from the annular one. Weighted differential
  algebra and cutoff-to-annular extraction separate `dd_cutoff_identity`
  from boundary integrability and exceptional-level bookkeeping. The cutoff
  combines local weak Green and pointwise boundary-flux interfaces with the
  weighted first identity and weak quotient equation. Annular normal-field
  factorization and the unweighted L² virial give the first identity.
  Weak product-rule and generator conjugation identify the raw quotient gradient
  with Fourier stream derivatives, without the quotient PDE or parity. Supplied-data bridges
  and coarea splitting use `h = ε/2`; inward virial normals are separate from
  the shared outward derivative convention.
- `OddOddBulkIntegrability.lean`: saddle-weighted coefficient bound, generic forcing
  integrability, its torus-vorticity specialization, squared-dipole cell integral
  and ordinary stream-level exhaustion.
- `OddOddFinitePart.lean`: exact truncated coefficient integral via the periodic
  normal-field divergence, center removal and continuity; its scalar finite part
  follows from the leading period asymptotic.
- `OddOddValueFinitePart.lean`: endpoint-subtracted arc integrability, the integrated
  squared-value orbit comparison and the scalar level-value finite part.
- `OddOddPotentialMass.lean`: two-saddle trigonometric interpolation, integrability
  of the Hölder corner remainder and the weighted value-mass finite part.
- `OddOddRenormalizedBulk.lean`: full renormalized bulk assembly from forcing
  integrability, the raw conclusion of the both-gradient estimate and the weighted
  value-mass finite part.
- `OddOddPiconeIntegrability.lean`: ground-state first derivatives,
  positive-truncation energy integrability and a full-level center-current bound.
- `OddOddGroundResidual.lean`: exact bounded-coordinate factorization of the
  differentiated residual, its uniform bound and potential integrability for L² data;
  the assembled positive-truncation integrability interface.
- `OddOddPiconeCutoff.lean`: quadratic Fourier integration by parts, normalized
  ground-flux algebra, weak Picone cutoff testing and common-null annular extraction.
- `OddOddPicone.lean`: regular-level current continuity and the Picone identity
  at every positive truncation, by simultaneous endpoint exhaustion.
- `OddOdd.lean`: character-wise virial-limit assembly, scalar finite-part
  cancellation, boundary-form identification, bulk coercivity interface and
  odd–odd exclusion assembly.
- `OddOddCoercivity.lean`: maximal weak weighted H¹ cell triples, normalized
  means and unnormalized energies, central-parity Poincaré, Kantorovich,
  constrained coercivity and the bridge from the actual Picone quotient.
  Separates the gradient estimate from the residual-certificate potential bound.
- `Mixed.lean`, `Main.lean`: mixed-sector interfaces, rotation between mixed
  sectors, and main theorem assembly. Consult
  [sector status](../STATUS.md#topic-pages) for proof completion.

### Certificate interfaces

- `BernsteinCertificates.lean`: exact rational power/Bernstein arrays and affine
  box pullbacks, expansion and positivity statements, rational logarithmic bounds
  and affine interpolation. Uses Mathlib's Bernstein basis; no checker is defined.
- `MixedComparison.lean`: actual diagonal-coordinate mixed matrix, potential,
  differential operator and explicit odd-in-a/b comparison functions.
- `PolynomialInequalities.lean`: explicit odd–odd residual table and its operator
  identity, mixed normalized differential residuals and interior sign claims,
  and the Robin margin polynomial with its positive-level derivative identity.

## Source checks and verification tools

- `scripts/check_blueprint.py` (`just check-blueprint`): source labels,
  references, metadata and dependency cycles, without Lean or plasTeX.
- `scripts/blueprint_status.py` (`just status-blueprint`, also `just web`):
  generates Git-ignored `docs/status/generated.md` from the same source model.
  Blueprint markers do not audit Lean declarations or axioms.
- `scripts/blueprint_subgraph.py` (`just web` / `just graph LABEL`):
  sector/custom dependency views, grouped by chapter unless `--no-chapters`.
- `scripts/CheckChallenge.lean` (`just challenge`): compares Challenge/Solution
  statements and axioms, without the comparator's sandbox or kernel replay.
- `scripts/SorryDeps.lean` (`just sorries DECL`): transitive admission/project-axiom
  dependencies with source locations, using the built library.
- `scripts/tests/` (`just test-blueprint`): checker/report regression tests.
- `.mcp.json`, `docs/tooling/`: Lean MCP configuration and agent-tooling notes.
- `.github/workflows/`: Lean CI and docgen.
  Publication setup is described in [blueprint/README.md](../blueprint/README.md).
