# Project Lean skills

Optional procedures for interactive Lean work. [AGENTS.md](../../AGENTS.md)
remains the source of project policy; these skills do not replace it or the
blueprint.

| Skill | When to use it |
| --- | --- |
| [lean-analysis-patterns](lean-analysis-patterns/SKILL.md) | Analysis proofs involving function-space representations, integrability, limits, or scalar estimates |
| [lean-performance](lean-performance/SKILL.md) | Slow edit/recheck cycles, expensive elaboration, or proposed performance refactors |
| [lean-statement-review](lean-statement-review/SKILL.md) | Checking a Lean statement or definition against a blueprint node and agreed mathematical intent |

Each skill has a short entry point and an on-demand reference. They add no
scripts, dependencies, frozen-statement manifests, or autonomous orchestration.

Pi discovers this directory when the project is trusted. Run `/reload` in an
existing session after adding or editing skills. To select one explicitly:

```text
/skill:lean-analysis-patterns <proof or obstruction>
/skill:lean-performance <slow file or declaration>
/skill:lean-statement-review <blueprint label or Lean declaration>
```

Automatic selection is advisory, not guaranteed. Mandatory constraints belong
in `AGENTS.md`, not only in a skill.

See [ATTRIBUTION.md](ATTRIBUTION.md) for upstream sources, licensing, and the
changes made for this project.
