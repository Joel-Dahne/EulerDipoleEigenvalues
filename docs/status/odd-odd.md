# Odd–odd status

[Project status](../../STATUS.md) · [Shared infrastructure](shared.md)
· [Generated sector report](generated.md#odd-odd)

## Current position

All nodes in the odd–odd chapter have Lean statement and proof markers,
including Odd–odd exclusion (`thm:dd-exclusion`). The exclusion and
its character-wise assembly have no `sorry` of their own. The remaining
admissions lie in prerequisite chapters: this is **not** an admission-free
exclusion. Blueprint markers do not constitute a human statement review or
a transitive Lean audit.

The corrected-boundary nonnegativity branch and the non-certificate bulk
coercivity branch are transitively admission-free, including weighted Poincaré
on the original maximal weak domain. Quotient orthogonality and canonical
boundary regularity are admission-free for supplied quotient data.

## Remaining prerequisites

Proof work is now outside the odd–odd chapter:

- **Quotient existence:** the minimal quotient domain (`cor:dd-exclusion-domain`)
  is assembled from stream H², Hardy–Poisson vorticity division, periodic
  quotient transport and the periodic first transport gain. Stream H²
  (`prop:dd-stream-quotient-h2`) is itself assembled from local analytic inputs;
  those proofs and Hardy–Poisson division remain admitted. First transport gain
  (`lem:transport-first-gain`) and Periodic first transport gain
  (`cor:transport-first-gain-periodic`) are now transitively admission-free.
  The weighted third-stream step (`lem:dd-weighted-third-stream`)
  now has an assembly proof from the saddle jet, weighted gradient and two
  explicit outside-section elliptic/Taylor corollaries; see
  [shared status](shared.md#next-session) for that frontier.
  Weighted vorticity gradient, odd–odd
  (`prop:dd-weighted-gradient`) now has a proof of its own, with no statement
  change: actual weak spatial gradients and weighted norms are assembled on the
  full lifted separatrix neighbourhood. The generic weak-coordinate and
  finite-quarter/reflected-periodic covering layers are admission-free.
  Logarithmic numerator bounds (`lem:dd-log-numerators`) now also have a proof
  of their own, retaining the same derivative and trace witnesses. The generic
  compact-localization, canonical-trace uniqueness and logarithmic mass-summation
  layers and the canonical stream weak jet are admission-free.
  Logarithmically weighted phase-cell division (`lem:log-phase-cell-division`)
  is also admission-free, retaining the same canonical quotient and zero trace
  conclusion. The expanded analytic frontier is recorded in the root validation baseline.
  Logarithmic forcing (`lem:dd-log-forcing`) has a proof of its own, retaining
  the whole lifted neighbourhood, all eight canonical ray traces and one common
  radius. It uses the saddle jet, ordinary separatrix H¹/H³ and saddle
  factorization. No polar trace or stronger corner premise was added.
  Ordinary separatrix H¹/H³ (`prop:dd-separatrix-h1`) now also has an assembly
  proof with its original whole-lift statement. Regular Cartesian patches cover
  every nonsaddle seam; weak uniqueness retains the full-collar finite-norm
  gradient for point removal. Odd reflection and canonical window restriction
  give zero traces on every admissible window, including normal endpoints.
  These generic layers have zero admissions. Weighted forcing
  (`lem:dd-weighted-forcing`) and Odd–odd saddle estimates (`prop:saddle-dd`)
  are admission-free with their original statements, canonical Fourier remainder
  jets and the unique normalized quadratic. Neither ordinary separatrix H¹/H³
  nor logarithmic forcing is used by the weighted forcing.
  Both transport gains (`lem:transport-first-gain`, `lem:transport-second-gain`)
  and First eigenfunction saddle gain (`prop:saddle-first-gain`) are admission-free.
  Cellwise H¹ regularity from weighted forcing (`lem:weighted-transport-h1`)
  is admission-free with its original statement. Physical quarter gluing keeps
  the supplied collar and uses the global weak equation, not null seams alone.
  The ordinary separatrix parent reaches only Interior elliptic H³
  (`lem:elliptic-local`); see [shared status](shared.md#next-session).
  **Weak full-cylinder inversion is admission-free**
  (`lem:cylinder-weak-inverse`), retaining its original hypotheses and actual nil
  integral. Finite-mass spectral cutoffs make every ordered derivative spectrum
  integrable without assuming the originals L¹. Kernel weak identities,
  joint L² convergence, exact strip mass and genuine open-patch locality give
  all weak entries on the entire real-angle lift. The Fourier round-trip
  identifies the original forcing. No mixed-entry commutation or null-seam
  weak gluing is used.
  **Weighted Cartesian particular solution is admission-free**
  (`lem:cylinder-cartesian-particular`), with every specified ordered entry,
  unchanged norms, pointwise candidate and original forcing. Cofactor-weighted
  tests and overlapping charts handle both angular cuts before center removal.
  Its original-forcing assembly is admission-free too.
  **Smooth harmonic comparison is admission-free**
  (`lem:weak-poisson-harmonic-comparison`) on the same whole disk, with its
  original parity. Fixed radial smoothing and pointwise overlap compatibility
  give a genuine smooth representative of the raw weak-harmonic difference.
  Cylinder inverse (`lem:cylinder-inverse`) and its odd–odd application now
  have zero transitive admissions, with their original statements and data.
  Whole-edge zero trace (`lem:transport-zero-edge-trace`) is admission-free
  on every admissible original window. Ordinary separatrix H¹/H³ and logarithmic
  forcing now reach only **Interior elliptic H³** (`lem:elliptic-local`).
  Prioritize the odd–odd applications at three halves and three; their finite
  Taylor extraction is proved. Keep the shared interfaces generic and defer
  mixed linear-jet extraction.
  See [shared status](shared.md#next-session).
  Periodic quotient transport is
  admission-free: invariant regularized reciprocals and C¹ testing give
  division directly on the torus.
  No stronger corner hypothesis is needed. The stronger bundled
  quotient-domain proposition is downstream and off the exclusion route.
- **Picone/virial limits:** the remaining inputs are Local H² smooth
  approximation (`lem:local-h2-smooth-approximation`) and Leading period
  asymptotic (`lem:period-leading-asymptotic`). The finite parts need only the
  leading period value, not the elliptic identity or sharp remainders.
- **Bulk potential bound:** Odd–odd residual (`cert:dd-residual`) still needs
  both the operator-to-residual identity and the residual sign proof. No exact
  certificate backend or verification dataset has been supplied.

The detailed analytic backlog and interface-review questions belong in
[shared status](shared.md#open-analytic-work); the
[generated report](generated.md#odd-odd) lists unfinished prerequisite nodes.
The last recorded transitive audit is summarized in
[project status](../../STATUS.md#validation-baseline). These are different
views of the frontier, not interchangeable counts of gaps.

## Review and optional work

- Human review of the Lean statements and analytic inputs remains necessary;
  a completed assembly verifies compatibility, not the intended mathematics.
- Bring the settled argument into the reworked manuscript only with the
  authors’ agreement.

## Where to work

- [Odd–odd blueprint](../../blueprint/src/chapters/odd_odd.tex) and
  [digest notes](../../blueprint/src/chapters/notes.tex) for mathematical details.
- [OddOdd.lean](../../NoEmbeddedEigenvalues/OddOdd.lean) for the exclusion and
  Picone-current assemblies;
  [Regularity/OddOddQuotient.lean](../../NoEmbeddedEigenvalues/Regularity/OddOddQuotient.lean)
  for the quotient-domain assembly.
- [Shared infrastructure](shared.md) for prerequisite work and the
  [architecture guide](../architecture.md) for supporting modules.
