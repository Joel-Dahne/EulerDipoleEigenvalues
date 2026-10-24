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
- `SobolevHolder.lean`: continuous Fourier representative and Hölder embedding.

### Local Sobolev spaces, lifts and traces

- `SobolevLocal.lean`: weak derivatives, local Sobolev spaces and weighted norms.
- `LiftTorus.lean`, `LiftIntegration.lean`: classical/Fourier derivative
  correspondence, smooth lifts and integration by parts over `[0, 2π]²`.
- `LiftPeriodization.lean`: compact-test periodization, integral unfolding,
  H¹ transport tests, and transfer of torus Sobolev/transport relations to lifts.
- `LocalToGlobal.lean`: periodization of compactly supported local Sobolev data.
- `CellPeriodization.lean`: box periodization of compactly supported cell data
  and uniqueness of weak derivatives.
- `ACLSlicing.lean`, `DiagonalACL.lean`: ACL representatives and diagonal slicing.
- `TraceL2.lean`, `TraceH2.lean`, `TraceGagliardo.lean`: rectangle trace package.
  `HardyAverage.lean` and `OddHardy.lean`: averaging and odd-function Hardy estimates.
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

- `DuBoisReymond.lean`, `IntervalH1.lean`, `IntervalH1Estimates.lean`:
  interval weak calculus, endpoint traces, estimates and vanishing layers.
- `BoundaryForm.lean`, `WeightedBoundary.lean`, `WeightedBoundaryForm.lean`:
  classical positivity, weighted second-order domain, completion of squares,
  affine splitting and positivity by interval exhaustion.
- `FlowBoundaryForm.lean`, `CanonicalBoundaryForm.lean`: flow-time to
  `ξ = tanh s` transformation and identification of the canonical arc form.
- `IntervalZeroExtension.lean`: jump-free zero extension of zero-trace H¹
  data, and complex primitive/zero-extension helpers used by `TraceH2.lean`.
- `EvenEvenBoundary.lean`: even–even gradient traces, arc absolute continuity,
  weighted boundary regularity and canonical arc positivity.
- `EvenEven.lean`: cell-vanishing bridges, nonnegative exhaustion and exclusion
  assembly, ending directly with vanishing of the vorticity.
- `OddOdd.lean`, `Mixed.lean`, `Main.lean`: remaining sector interfaces,
  rotation between mixed sectors, and main theorem assembly.
  Consult [sector status](../STATUS.md#topic-pages) for proof completion.

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
