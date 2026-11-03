---
name: lean-analysis-patterns
description: Develop or repair Lean analysis proofs involving Lp and raw representatives, restricted measures, integrability, approximation, limits, or scalar inequalities. Use when a proof is blocked by representation changes or analysis API choices.
license: CC-BY-4.0
---

# Analysis proof patterns

Follow [project policy](../../../AGENTS.md), the pinned toolchain, and the
relevant blueprint node. This skill supplies proof-engineering suggestions,
not new mathematical assumptions or a general-purpose Sobolev library.

## Procedure

1. Identify the exact step: algebra, representation transport, integrability,
   convergence, or regularity. Explain its mathematical mechanism before
   selecting tactics.
2. Search the project and pinned Mathlib for the required interface. Verify
   signatures and imports; names in reference notes are search seeds.
3. State the smallest useful intermediate result. Keep representation changes
   separate from estimates, and exact identities separate from limit arguments.
4. Use the side of the API that owns the next theorem: bundled `Lp` for normed
   space arguments, raw functions for pointwise or weak-derivative work. Cross
   the boundary through a small, explicit bridge.
5. Check finiteness, measurability, representatives, weights, and domains before
   applying integral or norm identities. A real-valued norm expression alone
   need not establish integrability.
6. Keep scalar algebra local and controlled. Do not ask arithmetic tactics to
   unfold large transcendental or function-space expressions.
7. Validate incrementally with Lean-LSP diagnostics and goals. Keep statements
   fixed while repairing proofs; report an incorrect statement rather than
   silently weakening it.

Read [references/patterns.md](references/patterns.md) when choosing a concrete
bridge, approximation route, or algebraic decomposition.

## Scope and handoff

- Build only infrastructure consumed by an identified result; look for existing
  bridges before introducing another carrier or abstraction.
- Statement-first `sorry` declarations and conditional helpers are permitted
  under project policy. Name the missing input; do not describe a conditional
  assembly as a closed proof.
- Report the blueprint title/label, key idea, exact declarations checked, and
  unresolved mathematical or Lean obligations. Put manuscript problems in
  digest notes, not silent source corrections.

Adapted from Scott Armstrong's analysis guidance; see
[attribution and changes](../ATTRIBUTION.md).
