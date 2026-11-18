# Mixed-sector status

[Project status](../../STATUS.md) · [Generated sector report](generated.md#mixed)
· [Blueprint chapter](../../blueprint/src/chapters/mixed.tex)

In [Mixed.lean](../../NoEmbeddedEigenvalues/Mixed.lean), `mixed_exclusion`
(odd–even) is admitted. The even–odd exclusion follows by rotation; it does
not need a second analytic argument.

- **Regularity:** the route can reuse the shared cylinder inverse and
  weighted-forcing H¹ theorem. The mixed linear jet and quotient domain still
  need proofs. The blueprint uses the weighted-forcing theorem on the
  jet-subtracted remainder, not on the quotient by `cos a`.
- **Paired flux:** the existing Melnikov and pairing limits only cover
  rotation characters ±1. The mixed argument needs ±i or a separate
  half-orbit proof. Adjacent divergent edge energies must be paired; the
  even–even trace limits do not justify this step.
- **Coercivity:** the comparison functions are defined in Lean, but the
  boundary/virial passage and coercivity proof are unfinished. See
  [shared certificate work](shared.md#shared-certificate-work) for the sign
  checks.

See the [digest notes](../../blueprint/src/chapters/notes.tex) for mathematical
gaps and the generated report for per-node status.
