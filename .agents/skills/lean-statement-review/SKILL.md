---
name: lean-statement-review
description: Review a Lean theorem, definition, or interface application against a blueprint node and agreed mathematical intent. Use for binder, representative, domain, constant-dependence, or producer-to-consumer compatibility checks; distinguish fidelity from proof completion.
license: CC-BY-4.0
---

# Blueprint-to-Lean statement review

Follow [project policy](../../../AGENTS.md). Review by reading and reporting;
do not change the target statement or source as part of a review unless asked.
This is a lightweight procedure, not a frozen-anchor or certification system.

## Procedure

1. Identify the blueprint title/label and exact Lean export, plus the definitions
   that determine its meaning. Read the relevant status and agreed corrections.
2. Reconstruct the intended mathematical statement from the blueprint before
   relying on the implementation. Consult the original manuscript as evidence,
   not authority. Preserve unresolved disagreements as questions.
3. Compare all logical inputs, including implicit arguments, instances, and
   fields of project-owned bundles. Check quantifier order, constants, domain,
   regularity, representatives, and conclusion.
4. Inspect definitions used in the statement far enough to understand their
   semantics. Matching names and result types do not establish matching objects.
5. At important applications, check how the producer actually supplies the
   consumer's premises. Use Lean-LSP goals/diagnostics for an exact application
   when compatibility is uncertain; graph reachability is not a term-level check.
6. Use [references/checklist.md](references/checklist.md) for the detailed
   checklist and report format. State what was checked and what remains open.

## Fidelity and completion are separate

An intended statement may have a `sorry` proof. A proved assembly may depend on
admitted inputs. Conditional helpers are useful when clearly identified, but
they do not discharge the hypotheses they accept or replace the source-facing
endpoint.

Do not run every expensive audit by default. Use `just sorries NAME...` when
establishing transitive admission-freedom or inspecting the proof frontier.
Use `just challenge` only at the triggers documented in `AGENTS.md`.
Neither source comparison nor these checks constitute independent kernel replay.

Report mismatches before proposing repairs. Manuscript problems belong in
digest notes; changes to the Challenge definitions require author agreement.
Human review is still needed, and a second pass by the same agent is not an
independent audit.

Adapted from Scott Armstrong's statement-audit guidance; see
[attribution and changes](../ATTRIBUTION.md).
