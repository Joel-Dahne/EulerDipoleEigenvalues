# Mixed-sector status

[Project status](../../STATUS.md) · [Generated sector report](generated.md#mixed)
· [Blueprint chapter](../../blueprint/src/chapters/mixed.tex)

`thm:mixed-exclusion` (odd–even) is proved from `prop:mixed-quotient-domain`,
`lem:mixed-K-identity` and `thm:mixed-coercivity` in
[Mixed.lean](../../NoEmbeddedEigenvalues/Mixed.lean).
`cor:mixed-other-exclusion` follows by rotation. The analytic inputs are not
admission-free; see [the module map](../architecture.md).

- **Regularity:** the route can reuse the shared cylinder inverse and
  weighted-forcing H¹ theorem. `cor:mixed-saddle-jet` is proved using the
  first vorticity weight; `prop:mixed-quotient-domain` still needs a proof. The blueprint
  uses the weighted-forcing theorem on the jet-subtracted remainder, not on
  the quotient by `cos a`.
- **Paired flux:** `lem:melnikov` and `lem:pairing-limit` now cover ±i.
  The mixed application still needs a common good-level sequence and
  cancellation of the cross terms. Adjacent divergent edge energies must
  also be paired; the even–even trace limits do not justify that step.
- **Neumann traces:** `lem:mixed-boundary-square-traces` is assembled in Lean.
  The profile ODE and square integrability force decay at both ends; uniqueness
  identifies the physical trace with the canonical profile, and decay at
  `−∞` gives the Melnikov condition. `lem:mixed-neumann-stream-trace` is
  proved from `lem:trace-h2-boundary`, which is still admitted.
  `lem:mixed-neumann-strip-weight` provides the `L²(dt)` estimate for a
  canonical inward-strip trace without admissions. Applying that estimate to
  the physical collar and restricting the transport equation to the edge in
  `lem:mixed-neumann-vorticity-trace` remain open.
  `lem:mixed-boundary-square-weighted` is admission-free: its current is
  bounded by a multiple of `1 − x²` and needs no endpoint traces of `F`.
- **Static identity:** `lem:mixed-K-identity` follows from the cutoff limits
  and the boundary-square identity. The single-edge calculation
  `lem:mixed-neumann-renormalization` is proved from the boundary trace
  data. The remaining direct inputs are `lem:mixed-trace-mass`,
  `prop:mixed-virial`, and `lem:mixed-boundary-square-traces`.
  `lem:mixed-trace-field` proves the divergence and normal-flux algebra;
  the Sobolev divergence argument and limit for `lem:mixed-trace-mass` remain.
- **Coercivity:** the comparison functions are defined in Lean, but the
  boundary/virial passage and `thm:mixed-coercivity` are unproved. See
  [shared certificate work](shared.md#shared-certificate-work) for the sign
  checks.

See the [digest notes](../../blueprint/src/chapters/notes.tex) for mathematical
gaps and the generated report for per-node status.
