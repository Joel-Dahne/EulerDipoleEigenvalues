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
- `WeightedTraces.lean`: canonical transverse, radial, cell-edge and separatrix
  trace data; weighted corner trace and crossing-edge H¹ gluing interfaces.
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
  `ACLWeakDerivative.lean` gives the weak time identity from orbitwise ACL data,
  without selecting jointly measurable ACL representatives.
- `WeakPartialLocality.lean`: gluing one specified weak derivative by a partition of tests.
  `IntervalH1WeakLift.lean` lifts interval H¹ data to planar weak level derivatives.
  `WeakParameterIntegral.lean` proves local integrability and weak differentiation
  of signed midpoint primitives by sliced testing and Fubini.
- `TraceL2.lean`, `TraceH2.lean`, `TraceGagliardo.lean`: rectangle trace package.
  `HardyAverage.lean` and `OddHardy.lean`: averaging and odd-function Hardy estimates.
  `EvenGradientHardy.lean`: ACL zero traces and cosine division of even H²
  diagonal derivatives, through the primitive Hardy estimate.
- `ScalarDivision.lean`: canonical-trace endpoint/second Hardy, coarse period
  derivative and uniform complete-cell/global quotient interfaces, for all four
  quarter characters.
- `LogarithmicWeights.lean`: level/torus/lift/radial weights, the rectangle
  multiplier and logarithmic phase-cell division interfaces.
- `LogarithmicQuarterMass.lean`: compact collar localization of local logarithmic
  jet norms, constant-Jacobian quarter pullback and integrable fiber summation.
  `LogarithmicRayTransport.lean` proves the radius Jacobian, logarithmic comparison
  and weighted endpoint-energy change of variables, with explicit measurability.
  `LogarithmicNumerators.lean` restricts compatible numerator data without changing
  witnesses, transfers radial weighted L² using existing endpoint measurability,
  and sums the quantitative derivative bounds against the logarithmic weight.
- `LogarithmicMidpoint.lean`: local interval H¹ multiplication, logarithmic midpoint
  control, null quarter resonances and the orbitwise midpoint/reconstruction identity.
- `QuarterReconstruction.lean`: signed midpoint-integral bounds, a.e. measurability
  on moving quarter strips, fiber-integral L² summation, the forcing-level L²
  bound from weighted jet mass and logarithmic summation of the joint level candidate.
- `QuarterMeasureTransport.lean`: spatial L² pullback through constant-Jacobian coarea.
  `QuarterRotation.lean` transfers measurable spatial a.e. identities to joint
  quarter identities and gives the raw profiles' iterated rotation character.
  `QuarterTimeDerivative.lean` transfers specified weak transport derivatives to
  weak quarter-time derivatives using orbit restriction and rectangular ACL testing.
  `SaddleTransportWeights.lean` controls the d⁻² sine-transport terms by d⁻³ᐟ²
  gradient components, globally and without a cutoff.
- `WeakDerivativeGluing.lean`: specified measurable weak gradients from local H¹,
  by countable a.e. overlap compatibility, weak locality and local L² gluing.
  `WeightedFrame.lean` transfers the H and T/d² weights through bounded normalized
  frame coefficients. `QuarterInverseFrame.lean` gives the actual quarter's
  measurable dual coefficients, exact inverse algebra and weighted candidate L².
  `SmoothChartTests.lean` gives compact zero-extended chart tests, local L¹/L²
  and a.e. transport. `WeakChartTransport.lean` reconstructs weak spatial gradients
  by divergence-free cofactors. `QuarterChart.lean` instantiates the actual open
  quarter chart; `QuarterGradient.lean` identifies the inverse frame, transfers
  its weighted L² norm by coarea and identifies arbitrary specified gradients
  on spatial overlaps or in source coordinates.
  `QuarterCellCover.lean` covers a positive collar by rotated open quarter images
  up to null Cartesian seams and shrinks collars into open separatrix domains.
  `RotationWeakGradient.lean` transports derivative indices and weighted norms,
  then identifies one specified gradient on the finite quarter cover.
  `CellFolding.lean` supplies reflected periodic affine isometries, saddle-distance
  invariance and bounded period-index covering. `PeriodicWeightedGradient.lean`
  transports whole-cell weighted gradients to local norms for the same specified
  gradient on a lifted separatrix neighbourhood, without a new jump argument.
- `WeakQuarterReconstruction.lean`: midpoint-containing rectangle covers, weak
  differentiation of primitives and full reconstructions, and joint a.e. equality
  from a.e. fiber equality.
- `DiagonalCalculus.lean`, `SegmentEstimates.lean`: diagonal calculus and
  restrictions to segments/hyperbolas near a line.
- `SeparatrixTraces.lean`: line representatives, even–even arc/level traces,
  arc energy and corner tails; `QuarterOrbits.lean` gives explicit quarter graphs.

### Flow, orbit geometry and transport

- `DipoleCalculus.lean`, `Cells.lean`, `SeparatrixArc.lean`: dipole identities,
  cells/critical sets, diagonal square and explicit heteroclinic arc.
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
  `QuarterRayTraceUniqueness.lean` identifies canonical traces from different open
  neighbourhoods by common transverse rectangles and a countable interval cover.
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

### Eigenfunction regularity

The Lean results for [Regularity of eigenfunctions](../blueprint/src/chapters/regularity.tex)
live in `Regularity/`, retaining the namespace `NoEmbeddedEigenvalues`.
General Sobolev/jet, trace and weighted-transport prerequisites remain shared
in the sections above. Mixed-sector and center results without Lean statements
can be added here as they are formalized.

- `Regularity/CylinderInverse.lean`: parity/nonresonance data, the physical weighted
  cylinder inverse and smooth harmonic remainder with finite Taylor jets.
- `Regularity/SaddleNormalForm.lean`: normalized Cartesian quadratics, explicit orthonormal
  saddle charts and sinc factor; parity, differentiated Taylor bounds and
  quadratic compatibility. Independent of the eigenfunction regularity modules.
- `Regularity/OddOddSaddle.lean`: eigenfunction saddle estimates, weaker forcing weights
  and ordinary separatrix H¹/H³ interfaces.
- `Regularity/OddOddLogarithmic.lean`: logarithmic bulk/ray forcing interface and
  numerator assembly, using one fixed canonical stream jet. The assembly localizes
  the bulk norms and identifies the forcing traces with the existing numerator
  traces before logarithmic summation; rotation character is not used in this step.
- `Regularity/OddOddMidpoint.lean`: logarithmic phase quotient and midpoint data for
  either odd–odd rotation character, with a common a.e. orbit reconstruction.
- `Regularity/OddOddQuarter.lean`: the actual base-quarter vorticity level derivative
  from midpoint reconstruction and forcing-level L². `Regularity/QuarterTime.lean`
  gives the specified weak time identity for every eigenfunction; no saddle
  regularity or packed-jet admission is used. `Regularity/OddOddQuarterTime.lean`
  adds the stronger saddle weight and assembles both base-quarter derivatives.
  `Regularity/OddOddQuarters.lean` transfers them to all four recentered quarters
  on a common cutoff by joint a.e. congruence and saddle-distance invariance.
  `Regularity/OddOddGradientCoordinates.lean` extracts a single measurable ordinary
  separatrix gradient and reconstructs weighted spatial derivatives on the actual
  base-quarter image. Two-character summation removes the character premise;
  weak uniqueness transfers the weighted norm to the same ordinary gradient
  on the base-quarter overlap. `Regularity/OddOddCellGradient.lean` assembles the
  weighted gradient on an entire positive cell collar by rotations, compactness
  and two-character summation.
- `Regularity/OddOddRegularity.lean`: weighted vorticity gradient and third stream jet;
  the third-jet assembly uses the saddle jet and weighted gradient, with the
  generic dyadic gain in `WeightedElliptic.lean` and the Cartesian correction in
  `SaddleTaylorJet.lean`. `WeakJetOperations.lean` supplies jet restriction,
  linearity, uniqueness and classical-to-weak conversion.
- `Regularity/QuotientLocal.lean`: division/removal, coordinate Hardy, local/dyadic elliptic
  and first/second transport-gain interfaces.
- `Regularity/StreamQuotientAssembly.lean`: saddle division/removal, regular-edge chart
  covering, local smooth division, gluing and reconstruction of the H² stream
  quotient from the lower local analytic inputs.
- `Regularity/OddOddQuotient.lean`: minimal quotient data, stream H²/Hardy–Poisson/weak
  invariant division/periodic gain interfaces, the generic continuous-forcing
  transport-pair bridge, and quotient-existence assembly.

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
- `EvenEvenBoundary.lean`: bounded-value first-order level estimates,
  even–even gradient traces, arc absolute continuity,
  even H² arc estimates via Laplacian reconstruction, abstract canonical
  profile interval regularity, and canonical arc positivity.
- `EvenEven.lean`: cell-vanishing bridges, nonnegative exhaustion and exclusion
  assembly, ending directly with vanishing of the vorticity.
- `OddOddForms.lean`: quotient orthogonality, boundary data, continuous
  characters and boundary regularity; bulk forms, truncated Picone energies,
  currents and common renormalization data. Sits below the weighted virial.
- `OddOddQuotientEquations.lean`: weighted cell measure and weak operator,
  unitary multiplication by the dipole, local classical conjugation, and raw/
  supplied-data weak Poisson identities through specified Fourier derivatives.
- `OddOddGradientTraces.lean`: even H² gradient level limits from Laplacian
  reconstruction and even–even traces; a bounded-value first-order estimate
  and one rescaled exceptional set.
- `OddOddVirial.lean`: weighted operator jets, virial algebra and Green flux,
  raw-quotient annular/truncated identities. Positive-truncation H¹
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
- `OddOddGradientIntegrability.lean`: diagonal domination of the singular matrix
  form and whole-cell integrability of both the raw and divided gradient energies.
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
  means and unnormalized energies, central-parity Poincaré,
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
