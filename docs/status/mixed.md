# Mixed-sector status

[Project status](../../STATUS.md) · [Generated sector report](generated.md#mixed)
· [Blueprint chapter](../../blueprint/src/chapters/mixed.tex)

`thm:mixed-exclusion` (odd–even) is admitted in
[Mixed.lean](../../NoEmbeddedEigenvalues/Mixed.lean).
`cor:mixed-other-exclusion` follows by rotation.

The mixed chapter now has Lean statements for the analytic chain through
`thm:mixed-coercivity`. The new results are admitted, and the top-level
exclusion has not been rewired. See [the module map](../architecture.md) for
where the statements live.

- **Regularity:** the route can reuse the shared cylinder inverse and
  weighted-forcing H¹ theorem. `cor:mixed-saddle-jet` still needs a Lean
  statement, and `prop:mixed-quotient-domain` still needs a proof. The blueprint
  uses the weighted-forcing theorem on the jet-subtracted remainder, not on
  the quotient by `cos a`.
- **Paired flux:** the existing Melnikov and pairing limits only cover
  rotation characters ±1. The mixed argument needs ±i or a separate
  half-orbit proof. Adjacent divergent edge energies must be paired; the
  even–even trace limits do not justify this step.
- **Coercivity:** the comparison functions are defined in Lean, but the
  boundary/virial passage and `thm:mixed-coercivity` are unproved. See
  [shared certificate work](shared.md#shared-certificate-work) for the sign
  checks.

See the [digest notes](../../blueprint/src/chapters/notes.tex) for mathematical
gaps and the generated report for per-node status.
