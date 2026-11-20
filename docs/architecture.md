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
  `LocalL2Multipliers.lean` needs only bounded measurable coefficients at order
  zero, or continuous coefficients bounded on each compact localization. It also
  restricts whole-plane local L² to a finite norm on any bounded set.
- `LocalJets.lean`: Euclidean disk/axis geometry, specified weak and classical
  complex jets, integer and real-power radial integrability, energies and the
  Sobolev/jet interface.
- `SmoothJetBounds.lean`: uniform finite Taylor bounds for every ordered classical
  derivative, by top-jet compact bounds and repeated mean-value inequalities.
  Product-norm balls are distinguished from Euclidean disks. Local smoothness
  supplies actual weak jets; bounded radial quotients give genuine finite L² norms.
- `SobolevApproximation.lean`: local H² smooth-approximation interface on
  precompact patches, and bounded-coefficient L² product-integral stability.
- `AffineJets.lean`: volume-preserving affine pullback of weak derivatives,
  full specified jets, Sobolev regularity and radius-preserving radial L² bounds.
- `SaddleChartPullback.lean`: the explicit normalized saddle chart instantiated
  in the affine Sobolev/jet/radial interface. Orthogonality preserves the second
  jet's Laplacian without assuming symmetry of mixed entries. Integer period
  identities conjugate local axis reflections to the two torus reflections;
  measure-preserving pullback transports actual raw a.e. parity.
- `SaddleDistance.lean`: lattice separation/closedness, identification of the
  nearest saddle on a small ball, Euclidean/product radius comparisons and
  bounded-measurable transfer of radial local L² to saddle-distance weights.
  Radial mass at each saddle and ordinary local L² elsewhere glue to weighted
  local L² on the whole lift, without a uniform-radius or global-norm premise.
- `StreamJet.lean`: the canonical second stream jet from the existing Fourier
  partial multipliers, and its weak-jet interface.
  `SaddleStreamJet.lean` shares weak uniqueness for the original saddle remainder
  entries and the explicit quadratic first-jet bounds between ordinary and
  logarithmic forcing. `StreamParity.lean` transfers odd reflection parity to
  the continuous stream everywhere and proves zero values on the full separatrix.
  `SaddleCoefficient.lean` proves coefficient uniqueness from the weighted Hessian
  alone, on possibly different disk radii, and packages existence as uniqueness.
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
  `DiagonalSobolev.lean` iterates the weak coordinate rule at arbitrary integer
  order and supplies a specified diagonal Poisson jet.
  The latter owns raw diagonal L² transport in both directions, shared by the
  logarithmic multiplier and even-gradient Hardy proofs.
  `DiagonalH1.lean`, `DiagonalH1Inverse.lean` give ordinary H¹ in both directions
  for the actual diagonal trace charts, using the determinant-two weak test identity.
  `ACLWeakDerivative.lean` gives the weak time identity from orbitwise ACL data,
  without selecting jointly measurable ACL representatives.
- `WeakPartialLocality.lean`: gluing one specified weak derivative by a partition of tests.
- `WeakPartialLimit.lean`: fixed L² test pairing continuity and closedness of a
  specified weak partial under strong joint L² convergence of both entries on
  the same domain, without Sobolev density, pointwise convergence or traces.
- `WeakPointRemoval.lean`: finite whole-punctured-domain H¹ extends through a point;
  a cutoff in the other coordinate removes a parallel line from a tangential
  weak identity under local L¹ hypotheses, hence removes an isolated point too,
  without a radial tail. This is not a normal jump-removal theorem.
  `SaddlePointRemoval.lean` isolates each saddle using lattice separation,
  obtains finite whole-punctured-neighbourhood H¹ from full-domain local norms,
  and removes the entire lattice by local Sobolev gluing.
- `WeakJetFiniteness.lean`: recursive Sobolev membership from one fixed finite
  weak jet, and isolated-point removal for every ordered pair using whole-domain
  finite norms. No independently chosen derivatives or mixed-word commutation.
- `RadialWeakMultiplier.lean`: the local smooth weak product rule, radial derivatives,
  weaker-weight L² transport and H¹ of divided gradients through their center.
  The stronger quotients R/r³ and ∂ⱼR/r² support ordinary Cartesian ray traces.
  `IntervalH1WeakLift.lean` gives AC integration by parts, with or without boundary
  terms, and lifts interval H¹ data to planar weak level derivatives.
  `IntervalTraceIntegration.lean` identifies the canonical endpoint boundary terms
  for interval H¹ data, using the absolutely continuous closed-interval extension.
  `WeakParameterIntegral.lean` proves local integrability and weak differentiation
  of signed midpoint primitives by sliced testing and Fubini.
- `TraceL2.lean`, `TraceH2.lean`, `TraceGagliardo.lean`: rectangle trace package.
  `BoundaryTraceH2.lean` states the one-sided tangential trace result.
  `TraceWeakGluing.lean` retains specified derivatives and the common canonical trace
  across a matching-trace line, by fiberwise integration by parts and transverse
  cutoffs. Derivative-witness replacement and nested normal-window consistency
  include endpoint traces. Actual whole-rectangle norms precede weak gluing.
  `TraceWindowRestriction.lean` restricts the same canonical ACL witnesses to
  smaller normal windows, identifying continuous extension values at endpoints.
  `ReflectedTraces.lean` transports H¹ and canonical traces under normal reflection,
  comparing continuous interval extensions rather than raw boundary values.
  `RectangleH1Gluing.lean` constructs finite whole-rectangle derivative norms from
  half-rectangle H¹ before applying matching-trace weak gluing.
  `OddOddEdgeTraces.lean` identifies actual odd pullback parity for all four cell
  edges and constructs the reflected/periodically translated canonical zero traces.
  `OddOddSobolevTraces.lean` handles every lifted diagonal zero line: odd parity
  makes the canonical trace vanish on a symmetric rectangle still inside the
  absolute-level collar; restriction recovers every original endpoint window.
  `InteriorTrace.lean` selects an interior value from continuous section germs,
  proves agreement with the existing ACL trace, and supplies window independence
  and continuous trace products without evaluating raw planar representatives.
- `QuarterRayCharts.lean`: the actual volume-preserving affine endpoint charts,
  their Euclidean radius identities and canonical traces on every admissible window.
  `QuarterRayRadialTrace.lean` converts whole-disk H¹ radial quotients into genuine
  subcritical logarithmic ray norms for that same interior trace choice.
  `SaddleQuadraticRay.lean` supplies explicit quadratic/gradient homogeneity and
  logarithmic ray bounds, independently of saddle factorization.
  `HardyAverage.lean` and `OddHardy.lean`: averaging and odd-function Hardy estimates.
  `EvenGradientHardy.lean`: ACL zero traces and cosine division of even H²
  diagonal derivatives, through the primitive Hardy estimate.
- `ScalarDivision.lean`: canonical-trace endpoint/second Hardy, coarse period
  derivative and uniform complete-cell/global quotient interfaces, for all four
  quarter characters.
- `LogarithmicWeights.lean`: level/torus/lift/radial weights, the rectangle
  multiplier and logarithmic phase-cell division. `SeparableMultiplier.lean`
  bounds integrable coordinate weights by ACL section energies, including genuine
  weighted L² membership and an explicit uniform integral estimate.
  `DipoleLogMultiplier.lean` uses Ψ = 2 cos(a) cos(b), diagonal weak-derivative
  transport and compact localization to absorb the physical logarithm in local H¹.
- `LogarithmicRadialMass.lean`: a separable integrable power majorant for the
  crossing logarithm divided by radius, and absorption of radial logarithms by
  positive powers on bounded intervals.
- `RadialNonintegrability.lean`: critical inverse-square nonintegrability in
  physical dimension two, by Euclidean/product-radius comparison and Mathlib's
  norm-radial Haar formula. Nonzero constant Hessian defects cannot satisfy
  the weighted L² condition.
- `SaddleForcingMass.lean`: ordinary quadratic value/gradient mass on bounded
  physical disks. Inverse Euclidean radius is integrable by comparison with
  the product-norm power of exponent −1 in real dimension two; no logarithmic
  factorization or ordinary separatrix H¹/H³ is used.
- `SaddleLogarithmicMass.lean`: the physical logarithm near each saddle, actual
  integrability of Λ/r and logarithmic quadratic-gradient L², using the normalized
  factorization and volume/radius-preserving affine chart.
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
  and a.e. transport. `WeakChartTransportVariable.lean` transports specified weak
  pairs through a negative variable Jacobian by divergence-free cofactor tests,
  with physical local integrability supplied independently.
  `WeakChartTransport.lean` reconstructs weak spatial gradients
  by divergence-free cofactors. `QuarterChart.lean` instantiates the actual open
  quarter chart; `QuarterGradient.lean` identifies the inverse frame, transfers
  its weighted L² norm by coarea and identifies arbitrary specified gradients
  on spatial overlaps or in source coordinates.
  `QuarterCellCover.lean` covers a positive collar by rotated open quarter images
  up to null Cartesian seams and shrinks collars into open separatrix domains.
  `RotationWeakGradient.lean` transports derivative indices and weighted norms,
  then identifies one specified gradient on the finite quarter cover.
  `CellFolding.lean` supplies reflected periodic affine isometries, saddle-distance
  invariance, exact nonzero-collar containment and bounded period-index covering.
  `RegularEdgeCover.lean` covers every nonsaddle zero-level point by an admissible
  reflected-periodic edge window, using Cartesian period reduction and a small
  positive-cell normal interval. This is an actual seam cover, not an a.e. cover.
  `PeriodicWeightedGradient.lean` supplies the generic measurable finite-fold L²
  norm cover, shared by ordinary and weighted gradients, and
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
  quarter/full pairing limits for all four rotation characters and eigenfunction
  specializations. The full pairing also accepts a prescribed good sequence.
- `TransportOperator.lean`: unbounded `H = -iL₀`, self-adjointness/core/group
  statements. This is a separate route, not required by the even–even exclusion.

### Eigenfunction regularity

The Lean results for [Regularity of eigenfunctions](../blueprint/src/chapters/regularity.tex)
live in `Regularity/`, retaining the namespace `NoEmbeddedEigenvalues`.
General Sobolev/jet, trace and weighted-transport prerequisites remain shared
in the sections above. `Regularity/Center.lean` states local elliptic-center
regularity and the global H¹/H³ conclusion for sectors with an odd reflection.

- `Analysis/AxisReflectionJets.lean`: volume-preserving axis reflections, disk
  invariance and diagonal pullback of ordered weak jets. Weak uniqueness transfers
  scalar reflection parity to each specified entry and its Laplacian, without
  mixed-entry symmetry or a separate forcing-parity premise.
- `Analysis/CylinderAngularSpectrum.lean`: probability-Haar angular parity,
  Fourier translation/reflection identities and allowed support, including the
  zero-mode restriction. Integrable data give genuine coefficient integrals.
  Its circle premises require joint transport/a.e. slicing of planar data,
  not evaluation of raw planar L² functions on a chosen circle.
- `Analysis/LogPolarCoordinates.lean`: real-angle and circle-valued logarithmic
  cylinder maps, exact derivative/Jacobian, area-preserving weighted chart and
  joint null-set transport. The null angular seam and probability-Haar scaling
  are handled before slicing.
- `Analysis/LogPolarL2.lean`: square-root-Jacobian L² pullback, actual finite norms,
  exact 1/(2π) squared-mass normalization and a.e. angular L² slices.
- `Analysis/LogPolarInverse.lean`: measurable circle-valued inverse coordinates,
  continuity at every nonzero point, both pointwise round-trips and joint
  planar-to-cylinder null-set transport, including all real-angle seams.
- `Analysis/LogPolarAtlas.lean`: two genuine open real-angle charts with opposite
  cuts cover the entire punctured plane. Both forward maps are exactly Γ,
  with the same derivative and negative variable Jacobian.
- `Analysis/CylinderPhysicalValue.lean`: the same pointwise cylinder candidate
  reconstructed as rᵃS; global continuity through zero for a positive exponent,
  the unchanged uniform growth constant and pointwise axis parity.
- `Analysis/CylinderPhysicalL2.lean`: inverse square-root-Jacobian reconstruction,
  genuine planar L² before its exact 2π mass identity, weighted L² for every
  real homogeneity and bounded-disk restoration of nonnegative radial weights.
- `Analysis/CylinderCartesianJet.lean`: fixed ordered first/second Cartesian
  candidates, bounded angular coefficients, global weighted and whole-disk
  unweighted finite norms. The two mixed cylinder words remain distinct.
  The algebraic trace recovers the original forcing by joint null-set transport;
  weak derivative identification is separate.
- `Analysis/CylinderCartesianSource.lean`: smooth lifted radial/angular frames,
  exponential weights and weak product rules for the first coefficient.
  Its time and angular derivatives retain the two distinct mixed entries.
- `Analysis/CylinderPhysicalWeak.lean`: homogeneous physical weak pairs from
  source weak pairs and the same pointwise pullbacks; cofactor tests on both
  angular charts followed by genuine open-patch weak locality.
- `Analysis/CylinderCartesianWeak.lean`: local integrability from whole bounded
  disk norms and identification of every fixed Cartesian weak pair through
  order two on the entire punctured plane.
- `Analysis/WeakLaplacian.lean`: compact-test Laplacians of the specified ordered
  weak jet, classical zero-trace identification, reflected translations and
  the Euclidean complex-plane Laplacian bridge without changing the product norm.
- `Analysis/RadialMeanKernel.lean`: explicit inner-product radial bump, genuine
  positive finite planar mass and normalized Euclidean compact kernel.
- `Analysis/PlaneConvolution.lean`: smooth compact-kernel Cartesian derivatives,
  compact-test harmonicity of local smoothing and finite Fubini kernel exchange.
- `Analysis/RadialMeanValue.lean`: classical circle means on the actual polar
  strip and reproduction by the normalized radial kernel, with genuine bounded
  polar-rectangle integrability before Fubini.
- `Analysis/WeakHarmonicLocal.lean`: actual approximate-identity limits and a
  fixed smooth local representative of weak-harmonic data; pointwise agreement
  on open overlaps gives a same-domain smooth harmonic representative, with
  the whole-domain a.e. identity obtained through a countable subcover.
- `Analysis/CylinderAngularTransform.lean`: normalized angular coefficient
  functions, Parseval on a.e. slices and actual real-line L² membership of each
  coefficient, using the Parseval sum as an integrable majorant.
- `Analysis/CylinderFourier.lean`: actual real-line L² coefficient classes and
  cycle-frequency Fourier modes, integrated angular Parseval, Plancherel and
  inverse/scalar relations. No time L¹ assumption is needed.
- `Analysis/CylinderFourierData.lean`: exact cycle/angular-frequency measure
  transport, joint Borel spectral representatives and genuine product L² mass
  on dξ/(2π) times signed counting measure. Support and scalar mode relations
  survive representative choice; normalized modewise inversion recovers the
  specified coefficients a.e.
- `Analysis/CylinderTrigData.lean`: signed-to-trigonometric folding with factors
  2, 2i and the separate constant mode; actual joint L² amplitudes, allowed-measure
  domination and integrable slices at every allowed degree.
- `Analysis/CylinderTrigInverse.lean`: the actual folded data's nonresonant
  spectral quotient, weighted L²/L¹ and bounded continuous synthesis candidate;
  each allowed frequency mode has genuine L¹ and L².
- `Analysis/CylinderTrigParity.lean`: allowed-degree character and pointwise
  reflection identities for the trigonometric modes and their synthesis.
- `Analysis/FourierL2Integral.lean`: the inverse integral of actual L¹ ∩ L² data
  represents the L² inverse a.e., by Schwartz pairings and tempered-distribution
  compatibility. L² of the integral is inferred only after this identification.
- `Analysis/CylinderTimeSynthesis.lean`: exact cycle/angular-frequency conversion
  of the time inverse integral, its L² representative and Plancherel mass;
  specialization to every allowed mode of the actual spectral candidate.
- `Analysis/CylinderJointSynthesis.lean`: actual signed complex-mode integral on
  the angular circle; continuity/bounds, genuine angular L² slices and coefficient
  extraction by Fubini. Every coefficient is the specified time inverse integral.
- `Analysis/CylinderJointL2.lean`: actual time-mode family's joint L² and mass,
  angular Parseval and genuine joint cylinder L² of the bounded integral, with
  exact inverse Plancherel mass. Finiteness precedes the mass identity.
- `Analysis/CylinderJointParity.lean`: pointwise signed synthesis parity from
  countably combined negative-mode relations and the allowed half-turn character.
- `Analysis/CylinderSignedMass.lean`: reciprocal signed Sobolev weight in genuine
  normalized spectral L², and weighted-L² to L¹ via Hölder.
- `Analysis/CylinderSignedInverse.lean`: the original normalized signed spectrum's
  nonresonant quotient, weighted/unweighted L², actual L¹, allowed support and
  spectral multiplier identity; forbidden zero data need no invertible symbol.
- `Analysis/CylinderSymbol.lean`: exact logarithmic-cylinder symbol factorization,
  a uniform gap on a discrete angular spectrum, order-two ellipticity and a
  genuine spectral L² inverse with uniform weighted norm bound. Frequency ξ is
  angular frequency, not the cycle frequency used by Mathlib's Fourier transform.
- `Analysis/CylinderSpectralMass.lean`: integrability of the inverse squared
  Sobolev weight on real frequency times counting measure, and weighted-L² to
  L¹ spectral data by a separable majorant and Hölder.
- `Analysis/CylinderSynthesis.lean`: measurable, continuous, bounded cosine/sine
  synthesis kernels; genuine integrals, dominated continuity and pointwise
  angular periodicity. Modes are unnormalized; unitary Fourier reconstruction
  and identification of physical weak derivatives are separate from these bounds.
- `Regularity/CylinderData.lean`: axis parity, allowed angular degrees and
  Cartesian smooth harmonicity, independent of the inverse theorem.
- `Regularity/CylinderParity.lean`: parity of the actual weak Poisson forcing,
  continuous pointwise reflection identities and forbidden Taylor jets from
  smooth axis parity alone. Upgrading a.e. identities precedes center evaluation.
- `Regularity/CylinderForcing.lean`: zero-extended physical forcing and exact
  logarithmic-cylinder weight/mass formulas. The original solution parity and
  specified weak Laplacian give joint forcing parity, a.e. angular slices and
  allowed Fourier support. Its mode functions are real-line L², with forbidden
  modes zero a.e.; no separate support premise or chosen-circle evaluation.
- `Regularity/CylinderFourierForcing.lean`: original physical Poisson data produce
  the normalized product spectrum, exact physical weighted mass, joint allowed
  support and negative-mode reflection sign.
- `Regularity/CylinderSpectralForcing.lean`: original physical forcing gives exact
  signed-pair/constant-mode folding and a finite weighted spectral inverse with
  bounded continuous periodic synthesis and both pointwise reflection signs.
  Its actual modewise time inverse integrals have genuine L² and exact mass.
  Physical weak derivatives are separate from these trigonometric bounds.
- `Regularity/CylinderJointForcing.lean`: the original physical Poisson data give
  their own signed spectral inverse and actual continuous bounded reconstruction,
  with genuine joint cylinder L², exact mass, identified angular coefficients and
  both pointwise reflection signs. No extra support/reconstruction premise.
  Direct signed synthesis avoids a trigonometric-normalization bridge for the
  existential physical inverse; weak cylinder and Cartesian jets are separate.
- `Analysis/CylinderL2Inverse.lean`: isometric extension of actual signed synthesis
  from the dense L¹-intersection subspace to all normalized joint spectral L².
  Genuine joint inverse witnesses and exact mass need no L¹ premise; integrable
  inputs retain the same actual integral a.e. Analysis and weak derivatives
  are handled in the modules below.
- `Analysis/CylinderFourierRelations.lean`: representative-compatible joint a.e.
  congruence, addition and scalar relations for actual normalized spectral data;
  joint cylinder identities are sliced only a.e. before mode extraction.
- `Analysis/CylinderFourierL2.lean`: class-valued normalized joint analysis as a
  linear isometry, with exact agreement with the specified raw Fourier data.
- `Analysis/CylinderFourierRoundtrip.lean`: analysis of the actual integrable
  synthesis and both L² round-trips. Density and injectivity recover arbitrary
  original cylinder L² data with no L¹ premise on it or its Fourier data.
- `Analysis/CylinderJetCandidates.lean`: ordered derivative multipliers through
  degree two, their quadratic-weight domination and actual finite spectral L²;
  specified joint L² inverse entries with exact mass and a pointwise actual nil
  integral. It asserts no weak derivative identities.
- `Analysis/CylinderCandidateEquation.lean`: the signed symbol equals the ordered
  jet polynomial, and its actual spectral multiplier equation gives the original
  forcing in the same L² candidate entries, by the full normalized round-trip.
  This algebraic a.e. identity does not assert that those entries are derivatives.
- `Analysis/CylinderLift.lean`: finite joint mass on every translated angular
  period and local integrability on the full real-angle lift, including all seams.
  It asserts neither global planar L² nor weak gluing from a null seam.
- `Analysis/CylinderLiftL2.lean`: exact translated-strip squared mass with factor
  2π, transport of joint strong L² convergence, and joint null-set pullback to
  the entire real-angle plane. No global planar L² or weak seam gluing.
- `Analysis/CylinderIntegralWeak.lean`: classical lifted kernel derivatives and
  Fubini transfer of test pairings. Actual integrable spectra and their specified
  integrable first multipliers give whole-plane weak partials of the integrals.
- `Analysis/CylinderSpectralCutoff.lean`: one common finite-mass exhaustion
  commutes with every ordered multiplier. Each L² spectrum has actual integrable
  truncations; their inverse integrals converge strongly to its L² inverse class.
- `Analysis/CylinderL2Weak.lean`: whole-lift weak partials of arbitrary L² inverse
  classes with L² derivative multipliers. Closedness on translated strips and
  open-patch weak locality retain every ordered inverse-family entry and the
  pointwise actual nil integral, without derivative-L¹ premises.
- `Regularity/CylinderWeak.lean`: specified finite second weak cylinder jets on
  the full periodic real-angle lift, the conjugated Laplacian, and normalized
  signed weak inversion. The same actual integral and finite ordered entries
  solve the equation with the original forcing; no seam or extra source premise
  is omitted.
- `Regularity/CylinderParticular.lean`: weighted Cartesian reconstruction from
  that specified cylinder jet, whole-disk weak Poisson identities, finite radial
  norms, growth and parity, with a pointwise identity tying it to the same input
  cylinder candidate. The explicit formulas and whole-disk finite norms separate
  weak transport on the punctured disk from ordered center removal.
  The source-facing assembly supplies all premises from the original Poisson
  data and adds no support or cylinder-jet hypothesis.
- `Regularity/HarmonicComparison.lean`: same-domain specified second weak jets
  and equal weak Laplacians give a smooth harmonic difference with common parity.
  The bounded disk gives an integrable zero extension; compact tests retain the
  original weak equation, radial smoothing supplies its smooth representative
  on that same disk, and joint a.e. reflection transport retains parity.
  No radial weights, spectral inversion or Taylor extraction are used.
- `Regularity/CylinderInverse.lean`: assembly of the physical particular solution,
  smooth harmonic comparison and parity's forbidden Taylor jets; its original
  public statement and all derivative witnesses are retained.
  Explicit gap lemmas cover exponents three halves and three for odd–odd data.
- `Regularity/MixedSaddle.lean`: the exponent-two inverse gives the unique
  linear jet in the odd coordinate and the three weighted remainders.
  `Regularity/SaddleLinearization.lean` computes the Jacobian and Hamiltonian
  actions in the normalized coordinates.
- `Regularity/MixedCellH1.lean`: interpolates a smooth transport correction
  at the four lifted saddles and applies weighted transport to the remainder.
  The inward H¹ collar and odd-side zero traces do not require seam gluing
  or the mixed quotient data.
- `Regularity/MixedSeparatrix.lean`: glues the odd zero and even reflected
  traces, then uses the first-odd fold cover and saddle removal shared with
  `Regularity/OddOddRegularSeams.lean`. Interior elliptic regularity gives
  the H³ stream on the same collar.
- `Regularity/MixedQuotient.lean`: assembles the continuous closed-cell
  quotient and its specified jet. `MixedVorticityDivision.lean` localizes the
  cosine Hardy estimate to the collar. `MixedStreamDivision.lean` divides in
  translated odd-side charts and extends the H² quotient past the corners.
  `MixedQuotientTraces.lean` uses reflection to prove zero normal traces;
  `MixedDividedEquation.lean` identifies the divided Poisson equation by weak
  jet uniqueness. These four files also live in `Regularity/`.
- `Regularity/SaddleNormalForm.lean`: normalized Cartesian quadratics, explicit orthonormal
  saddle charts and sinc factor, exact factorization and quadratic compatibility.
  The raw chart parity theorem lives in `SaddleChartPullback.lean`, after its
  measure transport.
- `Regularity/SaddleNormalFormDerivatives.lean`: matches the ordered sine-product
  jets with the quadratic through order three and applies the finite Taylor
  bounds; the first derivative estimates also bound the squared gradient defect.
- `SaddleStreamCoordinates.lean`: finite H² and the fixed Fourier weak jet in
  saddle coordinates, actual charted Poisson and continuous-stream a.e. parity.
  The cylinder specialization keeps the physical weighted vorticity norm explicit
  and returns the same weighted particular jet and smooth harmonic remainder.
  It uses no ordinary separatrix H¹/H³ or weighted-forcing input.
- `HarmonicSaddleJets.lean`: pointwise axis parity for continuous cylinder data,
  pure Hessian vanishing, the normalized mixed quadratic and finite fourth-order
  remainder mass. The subcritical summand uses quadratic vanishing and inverse
  square-root radius mass, without an infinite harmonic expansion.
- `SaddleCylinderRemainder.lean`: actual stream bounds at exponent three halves
  and the critical quadratic remainder at exponent three. A.e. decomposition
  identifies the continuous value everywhere and the specified jets by weak
  uniqueness. Inverse affine transport retains the original physical quadratic;
  the final physical witness uses the fixed Fourier jet minus its classical jet.
  Both applications keep their weighted-vorticity norms explicit.
- `SaddleBootstrapMass.lean`: periodic box mass localizes the first vorticity
  weight at every lifted saddle; two reflected cell norms give finite mass on
  any bounded lift set. Odd parity reduces these to one cell norm. Distance-to-
  radius weakening supplies physical cylinder inputs without whole-plane norms.
- `SaddleSubcritical.lean`: derives the half-radius cylinder input from the first
  weight and transports the subcritical value/gradient estimates back through
  the inverse affine frame, retaining the specified Fourier first derivatives.
- `SaddleGrowth.lean`: local pointwise saddle growth and continuity away from the
  lattice give a common constant on compact sets by a finite open cover. No
  classification of the cell corners or global uniform saddle radius is needed.
- `Regularity/OddOddSaddle.lean`: first eigenfunction gain, odd–odd saddle bootstrap
  and weaker forcing, upstream of ordinary separatrix/logarithmic regularity.
  The first gain uses both the original and reflected eigenfunction. The second
  gain consumes the continuous-stream pointwise bound and the same specified
  weak gradient; bounded reflected-periodic mass supplies the critical cylinder
  input at every saddle. The original unique quadratic remainder is retained.
  The forcing
  assembly retains the original saddle coefficient and Fourier derivatives,
  weakens the remainder weights, adds actual quadratic mass, transfers to saddle
  distance and restricts to the fixed bounded cell neighbourhood.
  `Regularity/OddOddCellH1.lean` assembles a single positive-cell H¹ strip and
  canonical zero traces on all four edges, using the actual continuous forcing.
  `Regularity/OddOddEdgeTraces.lean` assembles paired canonical traces and Cartesian
  H¹ across every admissible reflected-periodic regular-edge rectangle, with one
  cell strip and genuine finite patch norms. The full-window trace remains zero.
  `Regularity/OddOddPuncturedH1.lean` covers every small nonzero level by reflected
  periodic cell strips, selects one measurable weak gradient there and gives its
  actual local L² norms on the full collar. Norm covering does not glue weak identities.
  `Regularity/OddOddRegularSeams.lean` glues the regular seams on one full collar,
  identifies the specified finite-norm gradient by weak uniqueness, and removes
  the isolated saddles using genuine whole-punctured-neighbourhood norms.
  `Regularity/OddOddSeparatrix.lean` houses the whole-lift H¹/zero-trace/H³ endpoint,
  separate from its cellwise producers to keep the dependency direction acyclic.
- `Regularity/StreamElliptic.lean`: canonical Fourier-jet Poisson identity and
  same-domain H³ stream completion from ordinary vorticity H¹, via the interior
  elliptic interface. Only compact localizations of the periodic lift have finite norms.
- `Regularity/OddOddLogBulk.lean`: all logarithmic bulk bounds on one lifted
  separatrix neighbourhood. Ordinary first/second jet masses come from H³;
  saddle bounds and continuous inverse distance away from saddles glue locally.
- `Regularity/OddOddLogSaddle.lean`: the divided saddle remainder gradient in the
  canonical stream jet minus the classical quadratic jet, first with Euclidean
  radius. Adding the quadratic and shrinking the disk gives the complete canonical
  gradient bound with the lattice-distance weight. Weak uniqueness also identifies
  strong whole-disk Cartesian H¹ quotients with the same canonical remainder entries.
- `Regularity/OddOddLogRays.lean`: logarithmic values and canonical gradient traces
  on each of the eight rays, using the same saddle coefficient in value and gradient.
- `Regularity/OddOddLogarithmic.lean`: logarithmic bulk/ray forcing and
  numerator assemblies, using one fixed canonical stream jet. The forcing chooses
  one neighbourhood and one common radius, with canonical traces on every window. The assembly localizes
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
  addition/subtraction, uniqueness including a.e.-equal base values,
  classical-to-weak conversion and regularity transfer
  from recursive Sobolev witnesses to each specified jet entry.
- `Regularity/QuotientLocal.lean`: division/removal, coordinate Hardy, local/dyadic elliptic
  and first/second transport-gain interfaces.
- `Regularity/StreamQuotientAssembly.lean`: saddle division/removal, regular-edge chart
  covering, local smooth division, gluing and reconstruction of the H² stream
  quotient from the lower local analytic inputs.
- `Regularity/OddOddQuotient.lean`: minimal quotient data, stream H²/Hardy–Poisson/weak
  invariant division/periodic gain interfaces, the generic continuous-forcing
  transport-pair bridge, and quotient-existence assembly. The full quotient
  statement and quantitative divided-Laplacian bound are in
  `Regularity/OddOddDomain.lean`, with the independent corner Hardy statement
  in `Regularity/EvenCornerHardy.lean`.

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
- `MixedField.lean`, `MixedBoundarySquare.lean`: the adapted field and the
  smooth and weighted one-edge boundary squares.
- `MixedComparison.lean`: explicit comparison functions, coefficient bounds
  and the positive determinant expansion. Homogeneous rational terms control
  the odd-in-a exponent through the corner and its derivatives on the regular
  strip. The odd-in-b multiplier uses bounded polynomial coefficients times
  `h log h`; its positive bounds and Robin inequality are elementary.
- `MixedRobinCurrent.lean`: abstract Robin multipliers, regular conormal
  formulas and the pointwise mixed Picone inequality.
- `MixedRobinRectangle.lean`: Fubini and sectionwise integration of the
  classical current, with the nonnegative Robin side removed and the other
  currents retained.
- `MixedRobinCutoff.lean`: odd-face and degenerate right-face current bounds,
  and removal of both cutoffs for smooth tests.
- `RectangleH1Approximation.lean`: matching-trace reflections and odd
  projection of interior smooth approximants give strong H¹ convergence
  on the square. A fixed-rectangle trace estimate gives L² convergence
  of the top values to the canonical trace.
- `MixedComparisonForm.lean`: the quarter-cell form and logarithmic Robin
  comparison on either odd axis. Bounded L² pairings from
  `SobolevApproximation.lean` pass the smooth-test inequality to the full
  quarter form domain, retaining its canonical Robin trace.
- `CosineTraceHardy.lean`: division by the normal cosine using two
  canonical zero traces and interval Hardy on inward sections.
- `MixedRellich.lean`: subtracts the signed mass current before integrating,
  factors the combined current, and assembles the Rellich form from volume and
  edge integrability and a Sobolev flux identity.
- `MixedStaticForm.lean`: the quotient interface, paired trace mass, weighted
  form and square completion. It splits the second-order form
  and mass by parity, assembles the quarter bounds, and converts the
  coercivity estimate to Cartesian stream mass.
- `MixedVirialBulk.lean`: normal-field bulk integrability and its
  Cartesian representative, exhaustion on good truncations, and the exact
  tangential field and model corner cancellation.
- `MixedTangentialCurrent.lean`: exact level-conormal current, integrable
  Hardy remainder, and antisymmetrization of the continuous corner model.
- `MixedTangentialShell.lean`: uniform absolute mass on shrinking
  cosine-product shells and the vanishing lower-cutoff current.
- `MixedTangentialCutoff.lean`: smooth annular difference field, quadratic
  Sobolev virial on the period square, and exact pullback of the cutoff current.
- `MixedTangentialLimit.lean`: simultaneous removal of the lower and center
  cutoffs; assembly of the integrated field comparison.
- `MixedPairing.lean`: pointwise projection of transport pairs onto the
  imaginary characters; common good levels and cross-term cancellation
  on the period and the four canonical arcs.
- `MixedFlux.lean`: quotient-domain producer, physical Neumann trace,
  paired virials and the static identity.
- `Mixed.lean`, `Main.lean`: mixed-sector exclusions, rotation between mixed
  sectors, and main theorem assembly. Consult
  [sector status](../STATUS.md#topic-pages) for proof completion.

### Certified polynomial inequalities

The certificate code is in [`Certificates/`](../NoEmbeddedEigenvalues/Certificates/).

- `Certificates/Bernstein.lean`: exact rational power and Bernstein arrays, affine
  box pullback, expansion and positivity. Uses Mathlib's Bernstein basis.
- `Certificates/Logarithm.lean`: rational logarithm bounds from geometric
  tail estimates and affine interpolation between endpoint bounds.
- `Certificates/OddOddResidual.lean`: explicit odd–odd residual table and
  unit-square parametrization of its geometric range.
- `Certificates/OddOddLower.lean`, `Certificates/OddOddUpper.lean`: sign
  inequalities at the two rational logarithm bounds. Each module separates
  its polynomial identity from the kernel-checked Bernstein coefficients.
  The assembly imports these proofs, so downstream edits do not replay the
  coefficient checks.
- `Certificates/OddOdd.lean`: differentiated ground residual identity and
  interpolation between the two endpoint inequalities.
- `Certificates/Mixed.lean`: local cosine-coordinate flux factorizations
  for the two normalized interior residual identities, and the
  regular-edge identity for the odd-in-a Robin margin. The three sign
  checks are separate from these identities. The matrix, potential,
  operator, and comparison functions live in `MixedComparison.lean`.

## Source checks and verification tools

- `scripts/verify_dd_residual.py` (Python 3 with SymPy): independently reproduce
  the exact odd–odd certificate data. Run with `--lean-power lower` or
  `--lean-power upper` to print a quotient power table. Not part of the Lean build.
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
