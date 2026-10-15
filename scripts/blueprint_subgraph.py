#!/usr/bin/env python3
"""Restrict the blueprint dependency graph to what some nodes depend on.

Reads `dep_graph_document.html`, the graph page written by `just web`, keeps
the given nodes together with everything they depend on (directly or
transitively, through statements and proofs), and writes the result next to it
as `dep_graph_<labels>.html`. The new page keeps the colours, the legend and
the statement pop-ups of the full graph.

Usage: python3 scripts/blueprint_subgraph.py [--web DIR] LABEL [LABEL ...]
Example: python3 scripts/blueprint_subgraph.py thm:ee-exclusion
"""

import argparse
import difflib
import re
import sys
from pathlib import Path

RENDER_DOT = re.compile(r"\.renderDot\(`(.*?)`\)", re.S)
QUOTED = r'"((?:[^"\\]|\\.)*)"'
EDGE = re.compile(rf"^{QUOTED}\s*->\s*{QUOTED}")
NODE = re.compile(rf"^{QUOTED}\s*(?:\[|$)")


def split_statements(body: str) -> list[str]:
    """Split a DOT graph body at top-level semicolons (outside quotes and [])."""
    statements, current = [], []
    depth, in_quote, escaped = 0, False, False
    for ch in body:
        if in_quote:
            current.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_quote = False
            continue
        if ch == '"':
            in_quote = True
        elif ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        elif ch == ";" and depth == 0:
            statements.append("".join(current).strip())
            current = []
            continue
        current.append(ch)
    statements.append("".join(current).strip())
    return [s for s in statements if s]


def ancestors(targets: list[str], edges: list[tuple[str, str]]) -> set[str]:
    """The targets and every node with a path to one of them."""
    preds: dict[str, set[str]] = {}
    for source, target in edges:
        preds.setdefault(target, set()).add(source)
    keep, stack = set(), list(targets)
    while stack:
        node = stack.pop()
        if node not in keep:
            keep.add(node)
            stack.extend(preds.get(node, ()))
    return keep


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("labels", nargs="+", help="blueprint labels, e.g. thm:ee-exclusion")
    parser.add_argument("--web", default="blueprint/web", help="blueprint website directory")
    args = parser.parse_args()

    web = Path(args.web)
    source = web / "dep_graph_document.html"
    if not source.exists():
        sys.exit(f"{source} not found; run `just web` first.")
    html = source.read_text(encoding="utf-8")

    match = RENDER_DOT.search(html)
    if match is None:
        sys.exit(f"No graph found in {source}.")
    dot = match.group(1)
    head, body = dot[: dot.index("{") + 1], dot[dot.index("{") + 1 : dot.rindex("}")]

    statements = split_statements(body)
    nodes, edges = set(), []
    for s in statements:
        if m := EDGE.match(s):
            edges.append((m.group(1), m.group(2)))
        elif m := NODE.match(s):
            nodes.add(m.group(1))

    unknown = [label for label in args.labels if label not in nodes]
    for label in unknown:
        close = difflib.get_close_matches(label, sorted(nodes), n=3)
        hint = f" Did you mean: {', '.join(close)}?" if close else ""
        print(f"Unknown label {label}.{hint}", file=sys.stderr)
    if unknown:
        return 1

    keep = ancestors(args.labels, edges)
    kept = []
    for s in statements:
        if m := EDGE.match(s):
            if m.group(1) in keep and m.group(2) in keep:
                kept.append(s)
        elif m := NODE.match(s):
            if m.group(1) in keep:
                kept.append(s)
        else:  # graph, node and edge defaults
            kept.append(s)
    new_dot = head + "\t" + ";\t".join(kept) + ";}"

    title = "Dependencies of " + ", ".join(args.labels)
    out_html = html[: match.start(1)] + new_dot + html[match.end(1) :]
    out_html = out_html.replace("<title>Dependency graph</title>", f"<title>{title}</title>", 1)
    out_html = out_html.replace('<h1 id="doc_title">Dependencies</h1>',
                                f'<h1 id="doc_title">{title}</h1>', 1)

    name = "+".join(label.replace(":", "-") for label in args.labels)
    target = web / f"dep_graph_{name}.html"
    target.write_text(out_html, encoding="utf-8")
    print(f"{len(keep)} of {len(nodes)} nodes. Wrote {target}")
    print(f"With `just serve`: http://localhost:8000/{target.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
