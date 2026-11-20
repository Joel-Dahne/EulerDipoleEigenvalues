# Mixed-sector status

[Project status](../../STATUS.md) · [Generated sector report](generated.md#mixed)
· [Blueprint chapter](../../blueprint/src/chapters/mixed.tex)

`thm:mixed-exclusion` (odd–even) is proved from `prop:mixed-quotient-domain`,
`lem:mixed-K-identity` and `thm:mixed-coercivity` in
[Mixed.lean](../../NoEmbeddedEigenvalues/Mixed.lean).
`cor:mixed-other-exclusion` follows by rotation. The analytic inputs are not
admission-free; see [the module map](../architecture.md).

- **Regularity:** `cor:mixed-saddle-jet` supplies the jet removed by
  `lem:mixed-weighted-forcing-remainder`. The resulting
  `lem:mixed-cell-separatrix-h1` gives an inward collar and zero odd-side
  traces. `lem:mixed-separatrix-h1` glues across regular sides, removes the
  saddles and gains local H³ for the stream on the full collar.
  `prop:mixed-quotient-domain` constructs the data from that collar:
  `lem:mixed-vorticity-division` gives the divided vorticity in L², and
  `lem:mixed-stream-division` gives an H² extension through the sides
  and corners. The same weak jet supplies the zero normal traces and
  the divided Poisson equation.
- **Virial:** `prop:mixed-virial` is assembled in Lean from
  `prop:mixed-paired-flux` and `lem:mixed-tangential-virial`; both inputs
  still have admissions. The field algebra, full-cell integrability,
  Fourier-gradient identification and normal bulk truncation limit are
  admission-free. The exact tangential field factors through the
  antisymmetric cosine difference, and its leading current cancels on
  symmetric shells. `lem:mixed-tangential-current` factors out the level
  from the analytic remainder; the normal Hardy bounds give an L¹ dominator,
  so the cutoff remainder vanishes. `lem:mixed-tangential-model` reduces
  the model term to a continuous antisymmetric defect that is zero at
  all four corners. `lem:mixed-tangential-shell` bounds the shell mass
  by integrating first in the smaller inward distance and proves that
  the full current vanishes against the lower cutoff derivative. The
  Sobolev cutoff identity and removal of the center cutoff remain.
- **Paired flux:** `lem:melnikov` and `lem:pairing-limit` cover ±i.
  The mixed application still needs a common good-level sequence and
  cancellation of the cross terms. Adjacent divergent edge energies must
  also be paired; the even–even trace limits do not justify that step.
- **Neumann traces:** `lem:mixed-boundary-square-traces` is assembled in Lean.
  The profile ODE and square integrability force decay at both ends; uniqueness
  identifies the physical trace with the canonical profile, and decay at
  `−∞` gives the Melnikov condition. `lem:mixed-neumann-stream-trace` and
  its one-sided trace input `lem:trace-h2-boundary` are admission-free.
  `lem:mixed-neumann-strip-weight` gives a canonical inward trace in
  `L²(dt)` for the vorticity on a Sobolev cell collar and identifies it
  with the trace on every regular cell-side window. The nonzero-forcing
  equation on compact regular windows is proved in `lem:edge-window-transport`.
  `lem:mixed-neumann-vorticity-trace` glues the local representatives
  before changing to flow time. It uses the inward collar from
  `lem:mixed-cell-separatrix-h1`, not across-separatrix regularity.
  `lem:mixed-boundary-square-weighted` is admission-free: its current is
  bounded by a multiple of `1 − x²` and needs no endpoint traces of `F`.
  `lem:mixed-boundary-square` is its smooth specialization: derivatives
  within the closed interval give finite energy without imposing endpoint data.
- **Static identity:** `lem:mixed-K-identity` follows from the cutoff limits
  and the boundary-square identity. The single-edge calculation
  `lem:mixed-neumann-renormalization` is admission-free from the
  quotient data now constructed by `prop:mixed-quotient-domain`.
  The remaining admitted inputs to the static identity are
  `lem:mixed-trace-mass` and `prop:mixed-virial`.
  `lem:mixed-trace-field` proves the divergence and normal-flux algebra;
  the Sobolev divergence argument and limit for `lem:mixed-trace-mass` remain.
- **Rellich form:** `lem:mixed-rellich` and `lem:mixed-rellich-flux` are
  admission-free. Subtracting the signed trace-mass current first leaves
  a bounded ratio `h/(h+k)` times a gradient polynomial. In
  `lem:mixed-rellich-integrable-sections`, Hardy estimates control the
  divided first derivatives and make the two normal current derivatives
  separately integrable. Their bulk formulas agree with the ACL section
  derivatives and sum to the corrected divergence. Integrating by Fubini
  uses the canonical Neumann traces and needs no separate corner flux.
- **Coercivity:** `thm:mixed-coercivity` is assembled from the square
  completion and the two quarter comparisons; it is not admission-free.
  The parity splitting of the form and mass, the Cartesian mass conversion,
  and the matrix positivity and coefficient bounds are admission-free.
  The certified comparison inequalities reduce to the three deferred sign
  checks `cert:odd-b`, `cert:odd-a`, and `cert:robin`. The two interior
  differential identities and the odd-in-a Robin polynomial identity are
  admission-free. So is `lem:mixed-robin-multipliers`: homogeneity controls
  the rational exponent and its first derivatives up to the regular Robin
  edge, and the factor `h log h` gives continuity and the logarithmic
  derivative bound for the odd-in-b multiplier.
  The generic `lem:robin-comparison` is admission-free: an integrable
  inverse-square-root weight controls the right-face current up to the top
  corner, and `lem:mixed-quarter-smooth-approximation` uses reflection and
  mollification to preserve the zero odd-axis condition while converging in
  H¹ and in the canonical top trace. The remaining analytic inputs are
  `lem:mixed-fold-quarter` (including the canonical traces) and
  `lem:mixed-completion`. See [shared certificate work](shared.md#shared-certificate-work)
  for the sign checks.

See the [digest notes](../../blueprint/src/chapters/notes.tex) for mathematical
gaps and the generated report for per-node status.
