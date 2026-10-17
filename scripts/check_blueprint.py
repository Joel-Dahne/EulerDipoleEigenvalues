#!/usr/bin/env python3
"""Check literal blueprint labels, references and dependency cycles.

Read content.tex and its recursive \\input/\\include files, without building
HTML or running Lean. This is a checker for the project's source conventions,
not a TeX interpreter: metadata arguments must be literal, not macro-generated.
Comments, \\verb examples and common verbatim environments are ignored.
"""

import argparse
from dataclasses import dataclass, field
import difflib
from pathlib import Path
import re
import sys

NODE_TYPES = {"definition", "lemma", "proposition", "theorem", "corollary"}
REFERENCES = {"ref", "eqref", "pageref", "autoref", "nameref", "cref", "Cref"}
NODE_REFERENCES = {"uses", "proves", "alsoIn"}
LIST_ARGUMENTS = {"uses", "alsoIn", "cref", "Cref"}
VERBATIM = {"verbatim", "verbatim*", "lstlisting", "minted", "comment"}
COMMAND = re.compile(r"\\([A-Za-z]+|[^\n])|%")
ARGUMENT = re.compile(r"\s*\{([^{}]*)\}")


@dataclass(frozen=True)
class Location:
    path: Path
    line: int

    def __str__(self):
        return f"{self.path}:{self.line}"


@dataclass(frozen=True)
class Token:
    command: str
    value: str
    location: Location


@dataclass(frozen=True, eq=False)
class Chapter:
    # A repeated heading input still starts a distinct chapter occurrence.
    title: str
    location: Location


@dataclass
class NodeMetadata:
    kind: str
    chapter: Chapter | None
    statement_leanok: bool = False
    proof_leanok: bool = False
    mathlibok: bool = False
    notready: bool = False
    has_proof: bool = False


@dataclass
class Scope:
    kind: str
    location: Location
    label: str | None = None
    target: "Scope | str | None" = None
    uses: list[Token] = field(default_factory=list)
    chapter: Chapter | None = None
    flags: set[str] = field(default_factory=set)


@dataclass
class Blueprint:
    labels: dict[str, Location] = field(default_factory=dict)
    nodes: dict[str, Location] = field(default_factory=dict)
    dependencies: dict[str, dict[str, Location]] = field(default_factory=dict)
    chapters: list[Chapter] = field(default_factory=list)
    metadata: dict[str, NodeMetadata] = field(default_factory=dict)
    errors: list[str] = field(default_factory=list)
    source: Path | None = None

    def error(self, location, message):
        self.errors.append(f"{location}: error: {message}")


def mask_literals(text: str, path: Path, result: Blueprint) -> str:
    """Blank comments and literal examples, preserving offsets and line numbers."""
    chars = list(text)

    def blank(start, end):
        chars[start:end] = ["\n" if c == "\n" else " " for c in text[start:end]]

    pos = 0
    while match := COMMAND.search(text, pos):
        pos = match.end()
        command = match.group(1)
        if command is None:  # An unescaped percent sign.
            end = text.find("\n", pos)
            pos = len(text) if end == -1 else end
            blank(match.start(), pos)
        elif command == "verb":
            if pos < len(text) and text[pos] == "*":
                pos += 1
            end = text.find(text[pos], pos + 1) if pos < len(text) else -1
            newline = text.find("\n", pos)
            if end == -1 or (newline != -1 and newline < end):
                result.error(Location(path, text.count("\n", 0, match.start()) + 1),
                             "unterminated \\verb example")
                end = len(text) if newline == -1 else newline
                pos = end
            else:
                pos = end + 1
            blank(match.start(), pos)
        elif command == "begin":
            arg = ARGUMENT.match(text, pos)
            if arg and arg[1].strip() in VERBATIM:
                end = re.search(r"\\end\s*\{\s*" + re.escape(arg[1].strip()) + r"\s*\}",
                                text[arg.end():])
                if end is None:
                    result.error(Location(path, text.count("\n", 0, match.start()) + 1),
                                 f"unterminated {arg[1]} environment")
                    pos = len(text)
                else:
                    pos = arg.end() + end.end()
                blank(match.start(), pos)
    return "".join(chars)


def tokens(path: Path, result: Blueprint):
    text = mask_literals(path.read_text(encoding="utf-8"), path, result)
    pos = 0
    commands = REFERENCES | NODE_REFERENCES | {"label", "begin", "end", "input", "include"}
    while match := COMMAND.search(text, pos):
        pos = match.end()
        command = match.group(1)
        location = Location(path, text.count("\n", 0, match.start()) + 1)
        if command == "chapter":
            title_pos = pos + 1 if text[pos:pos + 1] == "*" else pos
            title = ARGUMENT.match(text, title_pos)
            # Formatted titles may contain nested braces; grouping still works
            # with the source filename as a fallback, without interpreting TeX.
            yield Token(command, title[1] if title else path.stem, location)
        elif command in {"leanok", "mathlibok", "notready"}:
            yield Token(command, "", location)
        elif command in commands:
            if command in REFERENCES and pos < len(text) and text[pos] == "*":
                pos += 1
            arg = ARGUMENT.match(text, pos)
            if arg is None:
                result.error(location, f"\\{command} needs a literal braced argument")
                continue
            pos = arg.end()
            value = arg[1].strip()
            if not value or any(c in value for c in "\\#"):
                result.error(location, f"\\{command} needs a nonempty literal argument")
                continue
            yield Token(command, value, location)


def expanded_tokens(src: Path, path: Path, result: Blueprint, active=()):
    """Expand includes in document order, including repeated inputs as TeX does."""
    try:
        stream = tokens(path, result)
        for token in stream:
            if token.command not in {"input", "include"}:
                yield token
                continue
            child = src / token.value
            if not child.suffix:
                child = child.with_suffix(".tex")
            if child.resolve() in (*active, path.resolve()):
                result.error(token.location, f"recursive include of {child}")
            elif not child.is_file():
                result.error(token.location, f"included file not found: {child}")
            else:
                yield from expanded_tokens(src, child, result, (*active, path.resolve()))
    except (OSError, UnicodeError) as error:
        result.error(Location(path, 1), f"cannot read source: {error}")


def check_blueprint(src: Path) -> Blueprint:
    result = Blueprint(source=src)
    stack: list[Scope] = []
    scopes = []
    references = []
    previous = None
    chapter = None
    for token in expanded_tokens(src, src / "content.tex", result):
        command, value, location = token.command, token.value, token.location
        if command == "chapter":
            previous = None
            chapter = Chapter(value, location)
            result.chapters.append(chapter)
        elif command == "begin":
            scope = Scope(value, location, target=previous if value == "proof" else None,
                          chapter=chapter)
            stack.append(scope)
            if value in NODE_TYPES | {"proof"}:
                scopes.append(scope)
        elif command == "end":
            if not stack or stack[-1].kind != value:
                result.error(location, f"unmatched \\end{{{value}}}")
            else:
                scope = stack.pop()
                # Remarks are theorem-like too, but are deliberately not graph nodes.
                if value in NODE_TYPES | {"remark"}:
                    previous = scope if value in NODE_TYPES else None
        elif command == "label":
            if value in result.labels:
                result.error(location, f"duplicate label {value!r}; first defined at {result.labels[value]}")
            else:
                result.labels[value] = location
            if stack and stack[-1].kind in NODE_TYPES and stack[-1].label is None:
                stack[-1].label = value
                result.nodes.setdefault(value, location)
        elif command in {"leanok", "mathlibok", "notready"}:
            owner = next((s for s in reversed(stack)
                          if s.kind in NODE_TYPES | {"proof", "remark"}), None)
            if owner is not None and owner.kind != "remark":
                owner.flags.add(command)
        else:
            values = value.split(",") if command in LIST_ARGUMENTS else [value]
            for label in values:
                label = label.strip()
                ref = Token(command, label, location)
                references.append(ref)
                if command == "uses":
                    owner = next((s for s in reversed(stack)
                                  if s.kind in NODE_TYPES | {"proof", "remark"}), None)
                    if owner is None or owner.kind == "remark":
                        result.error(location, "\\uses is outside a graph node or its proof")
                    else:
                        owner.uses.append(ref)
                elif command == "proves":
                    proof = next((s for s in reversed(stack) if s.kind == "proof"), None)
                    if proof is None:
                        result.error(location, "\\proves is outside a proof")
                    else:
                        proof.target = label
    for scope in stack:
        result.error(scope.location, f"unclosed {scope.kind} environment")
    for ref in references:
        if ref.value not in result.labels:
            close = difflib.get_close_matches(ref.value, sorted(result.labels), n=1)
            hint = f"; did you mean {close[0]!r}?" if close else ""
            result.error(ref.location, f"unknown label {ref.value!r} in \\{ref.command}{hint}")
        elif ref.command in NODE_REFERENCES and ref.value not in result.nodes:
            result.error(ref.location, f"\\{ref.command} target {ref.value!r} is not a graph node")
    # Register statements first, so explicit forward \proves targets also work.
    for scope in scopes:
        if scope.kind in NODE_TYPES and scope.label is not None:
            result.metadata.setdefault(scope.label, NodeMetadata(
                kind=scope.kind, chapter=scope.chapter,
                statement_leanok="leanok" in scope.flags,
                mathlibok="mathlibok" in scope.flags,
                notready="notready" in scope.flags))
    for scope in scopes:
        if scope.kind == "proof":
            owner = scope.target.label if isinstance(scope.target, Scope) else scope.target
            if owner is None and scope.uses:
                result.error(scope.location, "cannot associate proof dependencies with a graph node; use \\proves{label}")
        else:
            owner = scope.label
            if owner is None:
                result.error(scope.location, f"{scope.kind} graph node has no label")
        if owner in result.nodes:
            if scope.kind == "proof":
                metadata = result.metadata[owner]
                metadata.has_proof = True
                # Like plasTeX, use the last associated proof's completion flag.
                metadata.proof_leanok = "leanok" in scope.flags
            deps = result.dependencies.setdefault(owner, {})
            for ref in scope.uses:
                if ref.value in result.nodes:
                    deps.setdefault(ref.value, ref.location)
    check_cycles(result)
    return result


def check_cycles(result: Blueprint):
    """Iterative DFS: report cycle witnesses without a Python recursion limit."""
    done = set()
    for root in sorted(result.nodes):
        if root in done:
            continue
        trail, active = [root], {root: 0}
        stack = [iter(sorted(result.dependencies.get(root, {})))]
        while stack:
            node = trail[-1]
            child = next(stack[-1], None)
            if child is None:
                stack.pop()
                trail.pop()
                active.pop(node)
                done.add(node)
            elif child in active:
                cycle = trail[active[child]:] + [child]
                result.error(result.dependencies[node][child],
                             "dependency cycle (arrows mean 'depends on'): " + " -> ".join(cycle))
            elif child not in done:
                active[child] = len(trail)
                trail.append(child)
                stack.append(iter(sorted(result.dependencies.get(child, {}))))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--src", type=Path, default=Path("blueprint/src"),
                        help="blueprint source directory (default: blueprint/src)")
    args = parser.parse_args()
    result = check_blueprint(args.src)
    if result.errors:
        for error in result.errors:
            print(error, file=sys.stderr)
        print(f"Blueprint consistency check failed ({len(result.errors)} errors).", file=sys.stderr)
        return 1
    print("Blueprint consistency checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
