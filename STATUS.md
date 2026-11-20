# Project status

Use the [blueprint dependency graphs](blueprint/README.md#building) to choose
proof work and the [generated report](docs/status/generated.md) for the list of
unfinished nodes. Refresh the report with `just status-blueprint`; `just web`
rebuilds both the graphs and the report.

## Overall state

- **Even–even:** the exclusion is admission-free.
- **Odd–odd:** the exclusion is admission-free, including the two endpoint
  certificates for the residual bound.
- **Mixed:** `thm:mixed-exclusion` depends only on the deferred comparison
  sign certificates `cert:odd-b`, `cert:odd-a`, and `cert:robin`; the other
  mixed sector follows by rotation.

All blueprint statements are represented in Lean. The main theorem combines
the sector exclusions and is not yet admission-free.
The reworked manuscript presents the introduction through the main theorem;
later sections are placeholders.

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
for mathematical gaps. Keep per-node progress in the blueprint and history in Git.
