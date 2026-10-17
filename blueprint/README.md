# Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) for the
formalization of `Manuscript/eigenvalues.tex`.

## What a blueprint is

A blueprint is a LaTeX document written as a sequence of small definitions and
lemmas, each with a `\label`. Special macros record how the pieces depend on
each other and how far the Lean formalization has come. From this, plasTeX
builds a website with a clickable **dependency graph**, where each node is
coloured by its status. The same source also compiles to an ordinary PDF.

The macros (invisible in the PDF):

| Macro | Where | Meaning |
|---|---|---|
| `\uses{a, b}` | in a statement | definitions/results needed to *state* this node |
| `\uses{a, b}` | in a proof | results needed to *prove* this node |
| `\lean{Foo.bar}` | in a statement | the corresponding Lean declaration(s) |
| `\leanok` | in a statement | the Lean statement exists (may still be `sorry`) |
| `\leanok` | in a proof | the Lean proof is complete |
| `\mathlibok` | in a statement | already in Mathlib |
| `\notready` | in a statement | not yet precise enough to formalize |

Remarks are not graph nodes. We use `\begin{remark}[Digest note]` for
questions and problems found in the manuscript, and collect them in
`chapters/notes.tex`.

## Workflow

1. **Digest:** turn a manuscript argument into small nodes with precise
   statements and short proofs, and record any doubts as digest notes.
2. **State in Lean** with `sorry`, add `\lean{...}` and `\leanok` to the
   statement. Review the Lean statement carefully; this is the part Lean
   cannot check for us.
3. **Prove** in Lean, then add `\leanok` to the proof.
4. **Feed back:** carry changes in statements or structure back into the
   blueprint and, once a chapter has settled, into the reworked manuscript
   (`Manuscript/manuscript.tex`).

## Layout

- `src/content.tex`: list of chapters
- `src/chapters/*.tex`: the content, one file per chapter
- `src/macros/common.tex`: theorem environments and math macros, shared by
  both versions
- `src/web.tex`, `src/print.tex`: preambles for the web and PDF versions
- `src/plastex.cfg`: web build configuration
- `src/sectorgraphs.py`: local plasTeX package adding sector graph links to
  the HTML5 sidebar (loaded only by `web.tex`)
- `../scripts/check_blueprint.py`: source-only consistency checker

## Building

Run these recipes from the repository root. The web build needs `just`,
`leanblueprint` (Python package) and Python 3; the PDF also needs a TeX
installation. The dependency graphs are rendered in the browser.

```sh
just check-blueprint # source consistency checks (Python 3 only)
just web             # checks, then HTML + full and three sector dependency graphs
just serve           # view it at http://localhost:8000
just pdf             # PDF in blueprint/print
just graph LABEL     # optional custom dependency view, after just web
```

Use `just web`, not `leanblueprint web` directly: the recipe handles
read-only static files on rebuild and regenerates these sector views:

- [Even–even](http://localhost:8000/dep_graph_thm-ee-exclusion.html)
  (`thm:ee-exclusion`).
- [Odd–odd](http://localhost:8000/dep_graph_thm-dd-exclusion.html)
  (`thm:dd-exclusion`).
- [Mixed](http://localhost:8000/dep_graph_thm-mixed-exclusion.html)
  (`thm:mixed-exclusion`); the other mixed sector follows by rotation.

The index and chapter sidebars list these three views below the full
Dependency graph link. These entries use plasTeX's native HTML5 navigation
extension, so they are regenerated with the site rather than patched into HTML.

## Consistency checks

`just check-blueprint` reports duplicate labels, unresolved references and
metadata targets, and dependency cycles through statement and proof `\uses`.
It also rejects missing/recursive includes and metadata that cannot be associated
with a graph node. Errors give source paths and line numbers; cycles include a
witness chain. `just web` and `just pdf` run this check before rendering.

The checker reads `src/content.tex` and its recursive `\input`/`\include` files,
not generated HTML or all files in the directory. Comments, `\verb` examples and
common verbatim environments are ignored. Metadata must use literal braced
arguments; the checker does not expand macros or evaluate TeX conditionals.
Ordinary cross-references do not create dependency edges. Proof dependencies
belong to the preceding node, or the explicit `\proves{label}` target.

This is not a full LaTeX checker, a Lean declaration/axiom audit, or a check of
`\leanok` annotations or mathematical correctness. Run `just test-blueprint` for
the checker's regression tests. For another source tree, use
`python3 scripts/check_blueprint.py --src PATH` from the repository root.

## Publication setup

Not set up yet (it needs Lean declarations and a GitHub remote first):
- `checkdecls` in the lakefile, so `leanblueprint checkdecls` verifies that
  every `\lean{...}` name exists;
- the `\home`, `\github`, `\dochome` links in `src/web.tex`;
- `blueprint: true` in the docgen CI step, to publish the blueprint on GitHub
  Pages.
