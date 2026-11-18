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
- Orbit coordinates, area/coarea, orbit restriction, coarse period value and
  first/second derivative bounds, saddle-distance/comparison and level-derivative estimates.
- Weak action-angle chain rules in both directions, periodization, transversal
  mollification, H¹ commutator and the annular L² virial.
- Eigenfunction transport, resonant vanishing, Melnikov, canonical profiles
  and pairing limits. The generic periodic-to-continuous transport-pair bridge
  is admission-free. The odd–odd stream-H² quotient is assembled from
  explicit local analytic inputs; Hardy–Poisson division remains admitted.
  First transport gain (`lem:transport-first-gain`) and Periodic first transport
  gain (`cor:transport-first-gain-periodic`) are admission-free, without parity.
  Periodic quotient transport is admission-free.
- Interval H¹, endpoint Hardy with constant four and an explicit L² conclusion,
  H² division by a linear factor with a universal derivative-energy bound,
  uniform complete-cell quotient and weighted derivative estimates,
  global phase-cell division with a canonical zero trace,
  and weighted boundary positivity by exhaustion. Abstract
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
   local analytic admissions; Hardy–Poisson division remains an outer admission.
   First transport gain (`lem:transport-first-gain`), its periodic corollary
   (`cor:transport-first-gain-periodic`) and First eigenfunction saddle gain
   (`prop:saddle-first-gain`) are transitively admission-free.
   The periodic bridge and reflected-cell assembly are in `PeriodicTransportGain.lean`.
   Periodic quotient transport is proved directly by
   invariant regularized reciprocals and C¹ torus testing.
   The next local/sector layer is in `Regularity/QuotientLocal.lean` and
   `Regularity/OddOddRegularity.lean`. The weighted third-stream step
   (`lem:dd-weighted-third-stream`) is assembled from the saddle jet and
   weighted gradient: the Hessian trace supplies the weighted vorticity input,
   without ordinary separatrix H³ or a fixed-cell localization bridge.
   Its generic weighted elliptic gain (`lem:elliptic-weighted-third`) and
   Cartesian Taylor correction (`lem:saddle-taylor-correction`) are explicit
   outside-section admissions. Weighted vorticity gradient, odd–odd
   (`prop:dd-weighted-gradient`) now has a proof of its own, with its original
   lifted-neighbourhood statement. Base-quarter reconstruction identifies genuine
   spatial weak derivatives; rotations cover a full positive collar up to null
   axes. Compactness, affine derivative-index transport and finite reflected
   periodic covering transfer the weighted norm to one specified ordinary
   gradient on the whole lifted neighbourhood. The generic reconstruction and
   covering layer has zero transitive admissions. No new trace/no-jump input was added.
   Logarithmic numerator bounds (`lem:dd-log-numerators`) also have an assembly
   proof: a compact collar turns local bulk norms into finite quarter mass;
   canonical ray uniqueness identifies the existing data's traces with the
   logarithmic forcing traces. The radius Jacobian controls the endpoint masses,
   with measurability supplied by the original unweighted endpoint L² data.
   All generic localization/trace/summation helpers have zero transitive admissions.
   The numerator assembly uses Logarithmic forcing (`lem:dd-log-forcing`),
   Weighted forcing (`lem:dd-weighted-forcing`) and Weighted numerator estimates
   (`lem:weighted-numerator-estimates`). The first now expands through its own
   proof; the audited transitive frontier is recorded in the root status.
   The canonical stream weak jet is admission-free.
   **Logarithmic forcing is assembled** (`lem:dd-log-forcing`), with its original
   statement and no admission of its own. Its direct assembly inputs are
   Ordinary separatrix H¹/H³ (`prop:dd-separatrix-h1`), Saddle jet (`prop:saddle-dd`)
   and the explicit saddle factorization within Saddle normal form
   (`lem:saddle-normal-form`). Bulk norms and canonical ray norms use the same
   fixed jet, one lifted neighbourhood and one positive radius for all eight rays.
   Whole-disk H¹ of R/r³ and ∂ⱼR/r² supplies ordinary Cartesian rectangle traces;
   a continuous-section germ choice agrees with the existing ACL trace on every
   admissible window. The quadratic ray bounds and all new generic trace helpers
   are admission-free. No polar trace, extra corner assumption or raw gradient
   evaluation is used.
   **Ordinary separatrix H¹/H³ is assembled** (`prop:dd-separatrix-h1`),
   with its unchanged statement in `Regularity/OddOddSeparatrix.lean`.
   `OddOddRegularSeams.lean` covers every regular seam by actual Cartesian
   patches and identifies their gradients with the full-collar norm candidate.
   Finite whole-punctured-neighbourhood H¹ removes every isolated saddle.
   `OddOddSobolevTraces.lean` uses odd reflection on a symmetric window still
   inside the same absolute-level collar, then canonical restriction to obtain
   zero traces on every original window, including normal endpoints.
   The canonical Poisson identity gives stream H³ on exactly that same collar.
   All new generic layers are transitively admission-free; null seams are used
   for norms and a.e. gradient identification, never as a substitute for weak gluing.
   **Weighted forcing is assembled** (`lem:dd-weighted-forcing`), with its original
   finite norms on the bounded cell neighbourhood and pointwise zero continuous
   stream values on every lifted separatrix line. It reaches only Odd–odd saddle
   estimates (`prop:saddle-dd`). Inverse-radius integrability in physical dimension
   two gives the quadratic mass; weaker remainder weights retain the original
   coefficient and specified Fourier derivatives. Radius-to-distance transport
   and compact localization give the finite cell norms. Continuous odd parity
   gives the zero stream values independently of the eigenfunction equation.
   These generic layers are admission-free. Neither ordinary separatrix H¹/H³
   nor logarithmic forcing is used, so the dependency direction remains acyclic.
   **Odd–odd saddle estimates are assembled** (`prop:saddle-dd`), with the
   original bounded-neighbourhood norm, every lifted saddle and unique normalized
   coefficient. The first eigenfunction gain also has a proof of its own, using
   the original and reflected eigenfunctions without parity decomposition.
   Periodic box mass supplies actual local cylinder inputs; inverse affine weak
   transport retains the physical Fourier first derivatives. Compact growth
   bounds and local-to-bounded L² gluing supply the second transport hypotheses,
   without explicit corner classification or vorticity H¹. Reflected-periodic
   bounded covering supplies the d² norm and the critical input at every saddle.
   Weak uniqueness retains the canonical quadratic remainder jet.
   **Saddle frontier closed:** First and Second transport gains,
   Odd–odd saddle estimates and the weighted forcing endpoint are admission-free.
   **Cylinder inverse is admission-free** (`lem:cylinder-inverse`), as is its
   odd–odd application, with their unchanged statements and original data.
   Full-lift weak inversion preserves the actual nil integral and every
   ordered inverse entry without derivative-L¹ premises. Cartesian reconstruction
   preserves the same pointwise value, original forcing, growth, parity and
   genuine weighted/whole-disk norms. Overlapping cofactor charts include both
   angular cuts before center removal; no raw representative is sliced on a ray.
   **Smooth harmonic comparison is admission-free**
   (`lem:weak-poisson-harmonic-comparison`, `Regularity/HarmonicComparison.lean`)
   on the same whole disk. Two weak test integrations identify the zero Laplacian
   of the raw difference. A genuine integrable zero extension, fixed radial
   smoothing and pointwise overlap compatibility give its smooth representative;
   joint a.e. reflection transport retains parity. No admitted elliptic theorem,
   stronger source hypothesis or smaller comparison disk is used.
   **Transport-gain prerequisites:** Quarter-orbit endpoint formula
   (`lem:quarter-endpoint-formula`) and Numerator vanishes at divisor zeros
   (`lem:numerator-zeros`) are transitively admission-free with their original
   statements. Fixed-window integration gives local numerator H¹ from continuous H¹
   forcing. Local L¹ endpoint integrability forces cancellation, without
   raw resonant-orbit values or simple-zero geometry.
   Geometry of quarter-divisor zeros (`lem:quarter-divisor-geometry`) now has
   its original-statement proof in `QuarterDivisorGeometry.lean`: a phase lattice
   enumerates all resonances, logarithmic comparison gives uniform level ratios,
   and Jordan's inequality gives the full-cell divisor bound. This geometry and
   Coarse period derivative bounds (`lem:period-derivative-bounds`) are now
   transitively admission-free. `PeriodDerivativeBounds.lean` differentiates the
   regular quadrature twice and integrates explicit inverse-power bounds, without
   elliptic identities or sharp asymptotics.
   Endpoint Hardy (`lem:hardy-endpoint`) and Second Hardy division
   (`lem:hardy-second`) are transitively admission-free with their original
   statements. The latter uses Segment averaging preserves H¹
   (`lem:segment-average-h1`) and the uniform choice K = 1, including endpoint zeros.
   Uniform complete-cell estimates (`lem:phase-cell-estimates`) have their
   original-statement proof in `PhaseCellEstimates.lean`, with zero transitive
   admissions. The smooth inverse divisor factor has a common collar and bounds
   independent of the character;
   the derivative estimate uses exactly N′ and hN″.
   Phase-cell division (`lem:phase-cell-division`) is also transitively
   admission-free with its original statement in `PhaseCellDivision.lean`.
   Complete cells cover the collar up to countably many endpoints; nonresonant
   boundary neighborhoods supply local H¹ without raw endpoint assignments.
   Countable energy summation, local-to-global H¹ and reciprocal-distance
   integrability give the global quotient and canonical zero trace.
   Zero-saddle forcing decay (`lem:zero-saddle-forcing-decay`) and its two
   oscillatory tails (`lem:zero-saddle-forcing-tails`) are transitively
   admission-free in `ZeroSaddleForcing.lean`, including actual tail integrability
   and uniformity in every real frequency. The corner-distance bounds identify
   the specific zero forcing value, not merely the nearest saddle distance.
   The weak moving-endpoint formula (`lem:numerator-moving-endpoints`) and
   zero-saddle numerator derivative estimate (`lem:zero-saddle-numerator-derivative`)
   are transitively admission-free in `OrbitNumeratorDerivative.lean` and
   `ZeroSaddleNumerator.lean`. Period variation cancels as an angular divergence,
   leaving the fixed-time level contraction and the two continuous endpoint values.
   The original transport pair supplies the first weak gradient; coarea gives
   actual integrable fiber energy E, and |N′|² ≤ K E/h + K/(h√h), uniformly in
   every real frequency on one collar. No global numerator H² hypothesis is used.
   **Both transport gains are admission-free** (`lem:transport-first-gain`,
   `lem:transport-second-gain`), with their verbatim original statements in
   `FirstTransportGain.lean` and `SecondTransportGain.lean`, reexported by
   `Regularity/QuotientLocal.lean`. The first gain uses smooth saddle-value
   interpolation and zero-saddle character norms. The second retains the
   original continuous forcing and supplied weak first gradient: weighted
   fiber energy gives actual N′ ∈ L² and C/h ∈ L²; canonical nearer-endpoint
   reconstruction preserves exp(-(2-δ)|t|) decay and gives raw v/d² mass.
   Cartesian rotation and finite linearity preserve the specified weighted
   gradient in every projection. Full physical-cell character norms recombine
   for all four complex characters and either frequency sign, without a common
   collar, raw endpoint values, gradient-ray traces or second numerator derivatives.
   Periodic first transport gain (`cor:transport-first-gain-periodic`) and
   First eigenfunction saddle gain (`prop:saddle-first-gain`) are admission-free.
   **Weighted forcing route:** Cellwise H¹ from weighted forcing
   (`lem:weighted-transport-h1`) has an assembly proof with its unchanged
   statement. Its original-hypothesis second mass
   (`lem:weighted-transport-second-mass`) and full/half numerator H¹
   (`lem:weighted-numerators-h1`) are proved. Local full-numerator H² is
   proved on that same all-frequency collar (`lem:weighted-numerator-local-h2`).
   Its ordinary first derivative agrees a.e. with the supplied-gradient candidate;
   the half derivative is retained unchanged. No raw endpoint prescription or
   zero canonical trace is inferred. Canonical gradient endpoint energy is proved
   (`lem:weighted-gradient-endpoint-energy`), including measurability of the
   radius pullback; no raw weak gradient is evaluated on a ray.
   **Second fixed-time bulk** (`lem:second-numerator-bulk`) has actual h-scaled
   L² mass and a common pointwise energy bound for every real frequency on one
   good-level set. Recursive H² gives the original ordered jet's finite norms.
   The pair constructs second entries when only the first gradient is supplied,
   retaining that gradient exactly (`lem:transport-second-bulk-data`); no Hessian
   or scalar regularity premise is added. The actual second weak moving-endpoint
   formula is proved (`lem:numerator-second-moving-endpoints`), identifying N″
   with this fixed-time second bulk and canonical normalized-angle endpoint terms.
   It retains the original continuous numerator, its ordinary first derivative,
   and every ordered jet entry; no mixed weak entries are commuted. The pair
   constructs the jet while keeping the supplied first gradient exactly, on any
   existing collar for every real frequency. The first bulk is only equated a.e.
   to its continuous scalar representative (`lem:first-bulk-moving-endpoints`).
   The normalized endpoint-value derivative now has a genuine global L² norm
   (`lem:weighted-endpoint-tangential-trace`): scalar derivative uniqueness
   identifies its tangential contraction with the radius Jacobian times the
   affine tangential gradient trace, without general trace-chart covariance.
   The complete endpoint-value contribution hE₁ is L² on one all-frequency collar
   (`lem:weighted-numerator-endpoint-derivative`), with the original forcing and
   gradient; the original-input producer also retains the true ordered jet.
   Single-character weighted weak quarter derivatives
   (`lem:weighted-character-quarter-derivatives`) are admission-free for supplied
   ordinary scalar data. The midpoint gain uses Q/h; the inner distance-one and
   outer distance-square moments give genuine weighted reconstruction norms
   without a logarithmic loss. The actual weak forward rule and raw time pullback
   retain the supplied Cartesian entries and the same raw v. Joint restricted
   character congruence transfers these fields to all four quarters without
   differentiated time shifts or a jointly selected ACL family.
   **Global ordinary second numerator norm**
   (`lem:weighted-numerator-second-norm`) is admission-free with the original
   forcing weights, continuous representative and supplied first gradient.
   The first-bulk time derivative has genuine joint L² energy: velocity cancels
   the inverse-distance level-vector coefficient of each ordered Hessian entry.
   Unit-time-window traces control the complete first-bulk boundary potentials
   without logarithmic Hessian weights (`lem:first-bulk-endpoint-energy`).
   Combining their hS′-weighted norm with the second bulk and hE₁ controls the
   actual ordinary hN″, on one collar for all real frequencies.
   Individual gradient traces in the two transverse charts remain unidentified;
   this route does not need that comparison.
   Ordinary scalar division (`lem:quarter-h1-scalar-data`) and four-character
   weighted weak quarter data (`lem:weighted-transport-quarter-assembly`) are
   admission-free under the original inputs. **Cellwise H¹ regularity from weighted
   forcing** (`lem:weighted-transport-h1`) is now admission-free too, with the
   original statement. Physical quarter gluing (`lem:transport-quarter-h1-gluing`)
   preserves the same collar: compactness extends the small-level inverse-frame
   bound to every supplied b < 1/2, giving actual full-collar gradient norms.
   Tangential cutoffs extend one partial across each axis; the global weak
   transport equation for v+f determines the missing normal partial locally.
   Subtract the same H¹ forcing. No separately assumed trace equality, raw ray
   evaluation, global inverse-velocity norm or jointly selected ACL family is used.
   The stronger logarithmic numerator package and full angular corner trace
   remain separate.
   **Whole-edge zero trace** (`lem:transport-zero-edge-trace`) is admission-free
   with its original statement. The inward normal chart gives a constant
   modulus on each regular window, and trace uniqueness identifies it across
   the edge. The original v/d and H¹ norms on the translated Cartesian
   half-cone exclude a nonzero modulus. A common inward subwindow identifies the
   zero trace on every original admissible endpoint window; there is no
   assumption of raw boundary values or stronger polar traces.
   **Next:** Interior elliptic H³ (`lem:elliptic-local`).
   **Logarithmically weighted phase-cell division** (`lem:log-phase-cell-division`)
   is admission-free with its original statement. A common quotient construction
   transfers the cell energies by comparing the weight to its right-endpoint
   value; it does not differentiate the weight. Weighted numerator estimates
   (`lem:weighted-numerator-estimates`) remain a separate admitted input.
   The simultaneous full/half first bounds and the pointwise endpoint-value
   flux derivative bound are proved. The quantitative assembly is proved
   conditional on one pointwise energy bound for the first-bulk boundary term.
   To supply it, compare the normalized-angle trace of the fixed-time level
   derivative with the canonical affine gradient on the ray. A global unweighted
   boundary norm alone does not give the pointwise bound needed by logarithmic
   summation.
   Prioritize the odd–odd applications at exponents three halves and three;
   their finite Taylor extraction is proved. Leave mixed linear-jet extraction deferred.
   **Ordinary separatrix frontier:** Interior elliptic H³ (`lem:elliptic-local`)
   is the only remaining primitive input for ordinary separatrix H¹/H³
   and logarithmic forcing.
   **Possible dependency simplification:** ordinary forcing already follows
   mathematically from the subcritical stage: the value quotient is bounded by
   C times inverse square-root radius, and the first-derivative norm is supplied.
   The current Lean forcing assembly still uses the full saddle jet; wiring the
   shorter route would remove its second-transport-gain dependency.
   Stronger logarithmic scalar/orbit inputs remain explicit outside-section
   prerequisites. The weighted-gradient and third-stream
   assemblies still depend on their recorded transport and elliptic/Taylor inputs.
   On those stronger routes, rotations after spatial reconstruction avoid
   differentiated time shifts; the separate four-quarter derivative family is
   not needed there. The ordinary H¹ route instead uses its proved four-quarter
   weak data.
   Generic stream-H² congruence, local gluing, affine pullback, smooth
   multiplication and periodic reconstruction are admission-free. The stream-H²
   assembly has no admission of its own and no stronger hypotheses. Next proof
   work is its recorded local analytic frontier or the other quotient stages,
   not a remaining generic gluing interface.
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
   See [odd–odd status](odd-odd.md). The saddle and ordinary across-separatrix
   H¹/H³ assemblies reach the primitive analytic frontier listed above.
2. **Shared interface review:** check logarithmically weighted summation from the
   uniform complete-cell estimates, canonical interval traces and
   compatibility of Cartesian/orthonormal saddle quadratics. Orbit numerators must use the
   continuous forcing representative, not raw values on exceptional orbits.
   Check real cylinder exponents, finite harmonic jets, one-sided trace
   matching and the whole-edge forcing hypothesis. Shared jet/trace/quadratic
   data now sit below their parent interfaces; saddle geometry no longer
   imports eigenfunction regularity. Ordinary saddle/separatrix interfaces,
   logarithmic estimates and weighted gradients now occupy separate layers.
   Cutoff restriction, canonical ray-trace agreement and compact localization of
   local logarithmic bulk norms are checked in `LogarithmicNumerators.lean`,
   `QuarterRayTraceUniqueness.lean` and `LogarithmicQuarterMass.lean`.
   Keep local lifted norms distinct from full-plane periodic norms.
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
  Hardy–Poisson division remains an outer quotient admission. First transport
  gain and its periodic corollary are admission-free, with reflected-periodic
  covering beyond the fixed neighbourhood's boundary saddles.
  Periodic quotient transport is proved directly on the torus.
  The weighted-forcing H¹ route only needs
  `f/d², ∇f/d^(3/2) ∈ L²`, covering both the odd–odd quadratic jet and mixed
  zero-jet remainder. Zero forcing on an edge and a weighted corner trace
  force zero vorticity trace, without a midpoint condition. Crossing-edge
  H¹ gluing has an explicit cutoff proof. Both transport gains, cylinder
  inversion and the saddle jet are admission-free; weighted transport H¹,
  zero trace and elliptic H³ remain.
  The weighted-gradient and whole-lift ordinary
  separatrix H¹/H³ endpoints have assembly proofs, with explicit remaining
  weighted transport, trace and elliptic inputs rather than a stronger corner premise.
  Scalar endpoint/second Hardy, uniform complete-cell estimates and both
  global phase-cell division theorems are proved. Explicit saddle-chart
  interfaces remain separate prerequisites.
  The weighted H¹/corner/edge/gluing, quarter endpoint/resonant-zero and
  weighted/logarithmic numerator interfaces retain explicit quantitative
  bounds and actual fiber-integrability conclusions.
  The transport gains cover all four characters without Melnikov;
  implemented Melnikov/pairing results still only accept ±1.
  The shared jet, saddle normalization, endpoint Hardy and local elliptic
  prerequisites have substantive Blueprint derivations with explicit proof
  dependencies. Cylinder inversion is admission-free across all three interfaces
  above; the remaining corner/weighted-transport prerequisites are also
  recorded there. Elliptic-center regularity is not a prerequisite.
- [Finite-p Sobolev embedding](../../blueprint/src/chapters/analysis.tex):
  off the current sector routes. Odd–odd logarithmic multiplication now uses
  coordinate slicing and the exact diagonal factorization instead. Both
  logarithmic multipliers are proved. This optional Lean infrastructure remains
  open; inverse Hausdorff–Young or a compact-support Sobolev inequality are
  candidate approaches.
- [Period estimates](../../blueprint/src/chapters/geometry.tex): coarse
  first/second derivative bounds from the regular integral are admission-free in
  `PeriodDerivativeBounds.lean`, as are smoothness and strict decrease in `Period.lean`.
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
