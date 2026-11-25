# Project status

Use the [blueprint dependency graphs](blueprint/README.md#building) to explore
the proof. Run `just status-blueprint` to generate the
[local status report](blueprint/README.md#generated-status-report);
`just web` builds both the graphs and the report.

## Overall state

- **Even–even:** the exclusion is admission-free.
- **Odd–odd:** the exclusion is admission-free, including the two endpoint
  certificates for the residual bound.
- **Mixed:** `thm:mixed-exclusion` is admission-free, including `cert:odd-b`.
  The other mixed sector follows by rotation.

`thm:main` combines the sector exclusions and is admission-free. The blueprint
tracks this proof and retains the smooth virial identities for exposition.
The Lean library has no admissions. `Challenge.lean` still uses placeholders
by design; its statements are proved in `Solution.lean`.

## Topic pages

[Even–even](docs/status/even-even.md) · [Odd–odd](docs/status/odd-odd.md) ·
[Mixed](docs/status/mixed.md) · [Shared infrastructure](docs/status/shared.md)

## Review and verification

Blueprint proof markers mean no admission in the proof itself, not that all
its dependencies are proved. Use `just sorries main` (or pass a sector's Lean
declaration) to audit actual transitive admissions. Neither check replaces
human review of the Lean statements against the intended mathematics.

See [AGENTS.md](AGENTS.md) for workflow, [architecture](docs/architecture.md)
for the module map, and the [digest notes](blueprint/src/chapters/notes.tex)
for differences from the manuscript. Keep per-node status in the blueprint
and history in Git.
