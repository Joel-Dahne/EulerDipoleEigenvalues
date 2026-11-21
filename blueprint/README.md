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
   blueprint.

## Layout

- `src/content.tex`: list of chapters
- `src/chapters/*.tex`: the content, one file per chapter
- `src/macros/common.tex`: theorem environments and math macros, shared by
  both versions
- `src/web.tex`, `src/print.tex`: preambles for the web and PDF versions
- `src/plastex.cfg`: web build configuration
- `src/sectorgraphs.py`: local plasTeX package adding sector graph links to
  the HTML5 sidebar (loaded only by `web.tex`)
- `src/graph_neighbours.js`: graph zoom configuration and clickable
  prerequisite/dependent lists in statement popups, loaded through `plastex.cfg`
- `../scripts/check_blueprint.py`: source-only consistency checker and metadata reader
- `../scripts/blueprint_status.py`: generated sector status report

## Building

Run these recipes from the repository root. The web build needs `just`,
`leanblueprint` (Python package) and Python 3; the PDF also needs a TeX
installation. The dependency graphs are rendered in the browser.

```sh
just check-blueprint # source consistency checks (Python 3 only)
just status-blueprint # generate docs/status/generated.md without a web/Lean build
just web             # quiet build: checks, website, sector graphs and status report
just web --verbose   # same build with full output (also accepts -v)
just serve           # view it at http://localhost:8000
just pdf             # PDF in blueprint/print
just graph LABEL     # optional custom dependency view, after just web
```

`just web` prints a short success summary and the path to the full build log
(in the system temporary directory). On failure it prints the last 60 log lines
and exits unsuccessfully. Use `just web --verbose` to stream the full output;
that output is also saved to a log.

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

Use the mouse wheel or trackpad to zoom and drag to pan. The graph starts fitted
to the viewport, but the renderer's default zoom-in cap is removed so you can
keep zooming to read labels on large graphs.

Clicking a graph node opens its statement with **Depends on** and **Used by**
Blueprint-label lists. A dot beside each label copies its graph node's fill and
border colours, with the same status meanings as the graph legend (including
hollow nodes). Click a label to open that neighbour's statement in the same graph;
Ctrl/Cmd-click opens its chapter entry in a new tab. The lists follow
immediate edges in the displayed graph: transitively redundant edges are omitted,
and sector/custom views list only neighbours inside that view. Long popups scroll.
The local script extends the standard renderer without an upstream fork.
Its DOM regression fixture runs with `just test-blueprint` when Node is installed.

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

## Generated status report

`just status-blueprint` writes `docs/status/generated.md` from the same checked
source model as the consistency checker. `just web` also regenerates it.
The file is ignored by Git; regenerate it after source edits or on a fresh
checkout rather than editing or committing generated counts. `just clean`
removes it along with the generated website and PDF.

For each sector, it counts the target and all transitive statement/proof
prerequisites, separates definitions from results, and reports statement/proof
completion markers. Unfinished nodes are listed in chapter order with source
links, missing markers and `\notready` flags. Mathlib markers are counted
separately; definitions do not need proof markers, and Lean links alone do
not imply completion. Shared nodes count once per sector, not once globally
across the sector rows.

The report describes blueprint annotations, not Lean axiom independence or
mathematical correctness. Counts are nodes, not distinct declarations or gaps;
a marked proof may still depend on admitted prerequisites. Handwritten status
pages retain priorities and explanations instead of duplicating these numbers.

For stdout or another source tree:

```sh
python3 scripts/blueprint_status.py
python3 scripts/blueprint_status.py --src PATH --output REPORT.md
```

`just test-blueprint` covers both the checker and report generator.

## Publication setup

Not set up yet (it needs Lean declarations and a GitHub remote first):
- `checkdecls` in the lakefile, so `leanblueprint checkdecls` verifies that
  every `\lean{...}` name exists;
- the `\home`, `\github`, `\dochome` links in `src/web.tex`;
- `blueprint: true` in the docgen CI step, to publish the blueprint on GitHub
  Pages.
