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

## Building

Requirements: `leanblueprint` (Python package), `graphviz`, and for the PDF a
TeX distribution with `xelatex` and `latexmk`.

```sh
leanblueprint web     # HTML + dependency graph in blueprint/web
leanblueprint serve   # view it at http://localhost:8000
leanblueprint pdf     # PDF in blueprint/print
```

Not set up yet (it needs Lean declarations and a GitHub remote first):
- `checkdecls` in the lakefile, so `leanblueprint checkdecls` verifies that
  every `\lean{...}` name exists;
- the `\home`, `\github`, `\dochome` links in `src/web.tex`;
- `blueprint: true` in the docgen CI step, to publish the blueprint on GitHub
  Pages.
