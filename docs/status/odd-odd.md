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
  those proofs, Hardy–Poisson division and the periodic first gain remain
  admitted. The weighted third-stream step (`lem:dd-weighted-third-stream`)
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
  layers and the canonical stream weak jet are admission-free. The expanded
  analytic frontier is recorded in the root validation baseline.
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
  (`lem:dd-weighted-forcing`) now also has a proof with its original statement,
  depending only on Odd–odd saddle estimates (`prop:saddle-dd`). Its quadratic
  mass and continuous-stream parity helpers are admission-free; no ordinary
  separatrix H¹/H³ or logarithmic forcing is used. The ordinary separatrix parent
  therefore reaches four existing inputs: the saddle jet, Weighted transport H¹,
  Whole-edge zero trace and Interior elliptic H³. Proving these inputs remains work.
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
