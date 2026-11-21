# Mixed-sector status

[Project status](../../STATUS.md) · [Generated sector report](generated.md#mixed)
· [Blueprint chapter](../../blueprint/src/chapters/mixed.tex)

`thm:mixed-exclusion` (odd–even) is proved from `prop:mixed-quotient-domain`,
`lem:mixed-K-identity` and `thm:mixed-coercivity` in
[Mixed.lean](../../NoEmbeddedEigenvalues/Mixed.lean).
`cor:mixed-other-exclusion` follows by rotation. Both exclusions are
admission-free. See [the module map](../architecture.md).

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
- **Virial:** `prop:mixed-virial` is admission-free, including
  `prop:mixed-paired-flux` and `lem:mixed-tangential-virial`. The field
  algebra, full-cell integrability, Fourier-gradient identification and
  normal bulk truncation limit are also admission-free. The exact tangential field factors through the
  antisymmetric cosine difference, and its leading current cancels on
  symmetric shells. `lem:mixed-tangential-current` factors out the level
  from the analytic remainder; the normal Hardy bounds give an L¹ dominator,
  so the cutoff remainder vanishes. `lem:mixed-tangential-model` reduces
  the model term to a continuous antisymmetric defect that is zero at
  all four corners. `lem:mixed-tangential-shell` bounds the shell mass
  by integrating first in the smaller inward distance and proves that
  the full current vanishes against the lower cutoff derivative.
  `lem:mixed-tangential-cutoff` applies the quadratic Sobolev virial to
  the difference field, whose cutoff divergence equals its adapted
  coefficient. `lem:mixed-tangential-center` bounds the upper cutoff
  current by an integrable gradient energy after absorbing the derivative.
  Removing both cutoffs proves `lem:mixed-tangential-virial`.
- **Paired flux:** `lem:mixed-pairing-levels` chooses common good levels
  for the two imaginary characters and the truncated virial. Shifting
  by a quarter cancels their cross terms on the orbit and on the arcs.
  `lem:mixed-canonical-cutoff` identifies the arc sum with the two
  Neumann cutoff pairings. `lem:mixed-edge-mass` combines the four
  singular trace masses before integration; `lem:mixed-gradient-cutoff`
  uses this to prove the centered signed gradient limit.
  `lem:mixed-level-model` proves convergence of the paired leading
  boundary model with the exact level weight.
  `lem:mixed-quarter-mass-replacement` replaces the quotient mass on
  all four quarter graphs by the canonical edge mass.
  `lem:mixed-level-density` factors a Dirichlet cosine out of the
  remaining signed gradient terms, and `lem:mixed-quarter-section-envelope`
  provides the dominated trace-product limit for bounded coefficients.
  `lem:mixed-signed-quarters` gives the exact full-orbit decomposition
  and the transfer of cell integrability and a.e. identities.
  `lem:mixed-level-remainders` proves the vanishing full first-order
  term, identifies the finite gradient remainders on the four sides,
  and matches the weighted tangential energy to the centered-time one.
  `lem:mixed-level-signed-gradient` pairs the leading mass before taking
  the limit and adds these finite remainders. `lem:mixed-geometric-level`
  identifies the resulting limit with the centered cutoff finite part
  using the corrected Neumann edge integrals.
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
- **Static identity:** `lem:mixed-K-identity` is admission-free, including
  `lem:mixed-neumann-renormalization`, `lem:mixed-trace-mass`, and
  `prop:mixed-virial`. For the trace-mass identity, regularize the field
  denominator by adding ε, integrate along closed coordinate sections,
  and pair the side masses before taking the limit. Divided normal
  derivatives control the bulk density; the divergence error is
  uniformly bounded and tends to zero.
- **Rellich form:** `lem:mixed-rellich` and `lem:mixed-rellich-flux` are
  admission-free. Subtracting the signed trace-mass current first leaves
  a bounded ratio `h/(h+k)` times a gradient polynomial. In
  `lem:mixed-rellich-integrable-sections`, Hardy estimates control the
  divided first derivatives and make the two normal current derivatives
  separately integrable. Their bulk formulas agree with the ACL section
  derivatives and sum to the corrected divergence. Integrating by Fubini
  uses the canonical Neumann traces and needs no separate corner flux.
- **Coercivity:** `thm:mixed-coercivity` is assembled from the square
  completion and the two quarter comparisons and is admission-free.
  The parity splitting of the form and mass, the Cartesian mass conversion,
  and the matrix positivity and coefficient bounds are admission-free.
  The signs `cert:odd-a`, `cert:robin`, and `cert:odd-b` are admission-free.
  For `cert:odd-b-strips`, Lean checks each root conversion and then verifies
  scaled integer midpoint restrictions on a shared tree for each strip.
  Both interior differential identities and the Robin polynomial identity
  are admission-free. In `lem:mixed-robin-multipliers`, homogeneity controls
  the rational exponent and its first derivatives up to the regular Robin
  edge, and the factor `h log h` gives continuity and the logarithmic
  derivative bound for the odd-in-b multiplier.
  The generic `lem:robin-comparison` is admission-free: an integrable
  inverse-square-root weight controls the right-face current up to the top
  corner, and `lem:mixed-quarter-smooth-approximation` uses reflection and
  mollification to preserve the zero odd-axis condition while converging in
  H¹ and in the canonical top trace. The admission-free
  `lem:mixed-fold-quarter` uses the reflected weak gradients to keep
  the exact form and mass scaling and identifies the canonical Robin
  and odd-axis traces by continuity. In the admission-free
  `lem:mixed-completion`, a single current converts the Rellich density
  directly to the square and second-order bulk. Its Neumann flux cancels
  the Rellich edge energy and supplies the Robin mass. The proof also
  bounds the second-order form on H¹.
  See [shared certificate work](shared.md#shared-certificate-work) for
  the implementation of the sign checks.

See the [digest notes](../../blueprint/src/chapters/notes.tex) for mathematical
gaps and the generated report for per-node status.
