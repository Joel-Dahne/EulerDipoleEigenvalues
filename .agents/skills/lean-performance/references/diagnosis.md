# Diagnosing the cost

## Choose the measurement

For interactive work, first use Lean-LSP to isolate a slow recheck. Reuse the
open file; prefer small controlled edits near the affected declaration.
Moving an early definition can invalidate a long source suffix, so compare
edits at equivalent positions.

When that is insufficient, a fresh-process profile can separate import cost
from proof/statement work. After arranging memory headroom and checking that
project dependencies are built, a typical targeted command is:

```sh
lake env lean --profile EulerDipoleEigenvalues/<File>.lean
```

Replace the path with an actual module. This is an occasional diagnostic, not
the edit–check loop. It pays import loading again; narrow its scope and avoid
parallel Mathlib-heavy processes. Do not run it against stale project imports
and interpret those errors as proof failures.

Keep profiles in scratch or temporary storage. If command-line output lacks
declaration attribution, narrow the experiment in an untracked scratch copy
rather than adding permanent diagnostic commands to the library.

## Route by evidence

| Expensive part | First experiment |
| --- | --- |
| Import loading | Inspect transitive imports; test a narrower provider import |
| Typeclass inference | Supply concrete carrier/type annotations at an unresolved metavariable |
| Simplification/unfolding | Replace one expensive call with targeted rewriting or `simp only` |
| Arithmetic tactics | Extract the scalar core; reduce the supplied hypothesis set |
| Statement elaboration/unification | Match a consumer's existing abbreviation; isolate dependent arguments |
| Congruence search | Use `congrArg` with the known function explicitly supplied |
| Large proof term or local context | Extract a genuine helper lemma with a minimal signature |

An import-dominated file is not evidence that its proof tactics need rewriting.
Conversely, loading fewer imports does not fix an intrinsically expensive
dependent signature.

To distinguish statement from proof cost, a scratch variant with the same type
and a `sorry` proof may be useful. Never overwrite another session's work or
land that variant as a proof. Treat it only as a timing probe; do not update
blueprint proof status from it.

## Interventions to test, not apply mechanically

- **Explicit types:** if an overloaded operation triggers instance search before
  its carrier is known, a type annotation can solve the cause. More instances
  may instead enlarge the search.
- **Instance caches:** consider only when profiling shows repeated expensive
  closed instance goals. Test placement, parameters, scope, and downstream
  effects in the pinned Lean version. Do not copy a cache from another file
  by analogy or assume a private instance helps importers.
- **Abbreviations:** if a dependent consumer expects an existing `abbrev`, state
  the hypothesis using it rather than repeatedly unfolding its entire type.
  Confirm definitional equality; do not hide extra mathematical assumptions.
- **Helpers:** a small standalone lemma can remove an expensive call from a
  large local context. Keep the lemma's assumptions explicit and justified.
- **File splits:** seek an actual mathematical/import boundary. A chain of
  files that all load the same heavy imports can increase work. Small active
  files may still improve interactive rechecks; measure that separately.
- **Imports:** grep is a candidate finder, not proof that an import is unused.
  Instances and tactics may be load-bearing; validate every removal.

## Compare fairly

Keep imports, target scope, toolchain, cache conditions, and concurrency
comparable. Repeat noisy timings; do not import numerical thresholds or
expected speedups from another machine.

Build logs, profiler phase totals, and wall time measure different things.
Lake's displayed job times are not automatically summed CPU time; concurrent
work, waiting, serialization, and unreported short jobs complicate comparisons.
A profile is evidence about one run, not a noise-free performance guarantee.

Report what improved: first-open cost, edit latency, own-file elaboration, or
checkpoint build time. Do not trade away statement correctness for any of them.
