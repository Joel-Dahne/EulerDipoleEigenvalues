"""Regression tests for the source-only blueprint consistency checker."""

from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import textwrap
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_blueprint import Blueprint, Location, check_blueprint, check_cycles


class BlueprintTests(unittest.TestCase):
    def setUp(self):
        self.tmp = TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.src = Path(self.tmp.name)

    def write(self, name, text):
        path = self.src / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(text).lstrip("\n"), encoding="utf-8")

    def check(self, text, files=None):
        self.write("content.tex", text)
        for name, body in (files or {}).items():
            self.write(name, body)
        return check_blueprint(self.src)

    def assertError(self, result, message):
        self.assertTrue(any(message in e for e in result.errors), result.errors)

    def test_valid_forward_references_and_nested_proof_dependencies(self):
        result = self.check(r"""
            \chapter{Example}\label{chap:test}
            \begin{lemma}\label{lem:a}\uses{lem:b}
            See \ref{chap:test}, \eqref{eq:x} and \cref{lem:a, lem:b}.
            \end{lemma}
            \begin{proof}
            \begin{enumerate}\item \uses{lem:b}\end{enumerate}
            \begin{equation}\label{eq:x}1=1\end{equation}
            \end{proof}
            \begin{definition}\label{lem:b}\end{definition}
        """)
        self.assertEqual(result.errors, [])
        self.assertEqual(set(result.nodes), {"lem:a", "lem:b"})
        self.assertEqual(set(result.dependencies["lem:a"]), {"lem:b"})

    def test_duplicate_labels_report_both_locations(self):
        result = self.check("\\label{same}\n\\input{other}\n",
                            {"other.tex": "\\label{same}\n"})
        self.assertEqual(len(result.errors), 1)
        self.assertError(result, "other.tex:1: error: duplicate label 'same'")
        self.assertError(result, "first defined at " + str(self.src / "content.tex") + ":1")

    def test_repeated_input_is_not_silently_deduplicated(self):
        result = self.check(r"\input{other}\input{other}",
                            {"other.tex": r"\label{same}"})
        self.assertError(result, "duplicate label 'same'")

    def test_each_reference_command_is_checked(self):
        for command in ["ref", "eqref", "pageref", "autoref", "nameref", "cref", "Cref"]:
            with self.subTest(command=command):
                result = self.check("\\" + command + "*{missing}")
                self.assertError(result, "unknown label 'missing'")

    def test_unknown_dependencies_have_source_lines_and_suggestions(self):
        result = self.check(r"""
            \begin{lemma}\label{lem:known}
            \uses{lem:knwon}
            \end{lemma}
        """)
        self.assertError(result, "content.tex:2: error:")
        self.assertError(result, "unknown label 'lem:knwon' in \\uses")
        self.assertError(result, "did you mean 'lem:known'")

    def test_dependency_must_be_a_graph_node(self):
        result = self.check(r"""
            \chapter{Title}\label{chap:test}
            \begin{lemma}\label{lem:a}\uses{chap:test}\end{lemma}
        """)
        self.assertError(result, "target 'chap:test' is not a graph node")

    def test_empty_list_entry_fails(self):
        result = self.check(r"\begin{lemma}\label{a}\uses{a,}\end{lemma}")
        self.assertError(result, "unknown label ''")

    def test_statement_cycle(self):
        result = self.check(r"""
            \begin{lemma}\label{a}\uses{b}\end{lemma}
            \begin{lemma}\label{b}\uses{a}\end{lemma}
        """)
        self.assertError(result, "a -> b -> a")

    def test_cycle_across_statement_and_proof(self):
        result = self.check(r"""
            \begin{lemma}\label{a}\uses{b}\end{lemma}
            \begin{lemma}\label{b}\end{lemma}
            \begin{proof}\uses{a}\end{proof}
        """)
        self.assertError(result, "a -> b -> a")

    def test_self_dependency(self):
        result = self.check(r"\begin{lemma}\label{a}\uses{a}\end{lemma}")
        self.assertError(result, "a -> a")

    def test_normal_cross_references_do_not_create_cycles(self):
        result = self.check(r"""
            \begin{lemma}\label{a}See \ref{b}.\end{lemma}
            \begin{lemma}\label{b}See \ref{a}.\end{lemma}
        """)
        self.assertEqual(result.errors, [])

    def test_explicit_proves_overrides_previous_node(self):
        result = self.check(r"""
            \begin{lemma}\label{a}\end{lemma}
            \begin{lemma}\label{b}\end{lemma}
            \begin{proof}\uses{b}\proves{a}\end{proof}
        """)
        self.assertEqual(result.errors, [])
        self.assertEqual(set(result.dependencies["a"]), {"b"})
        self.assertEqual(result.dependencies["b"], {})

    def test_unknown_proves_and_alsoIn_targets(self):
        result = self.check(r"""
            \begin{lemma}\label{a}\alsoIn{missing}\end{lemma}
            \begin{proof}\proves{missing}\end{proof}
        """)
        self.assertError(result, "unknown label 'missing' in \\proves")
        self.assertError(result, "unknown label 'missing' in \\alsoIn")

    def test_dependency_metadata_outside_node_fails(self):
        result = self.check(r"\uses{a}\begin{lemma}\label{a}\end{lemma}")
        self.assertError(result, "\\uses is outside a graph node or its proof")

    def test_orphan_proof_dependencies_are_not_discarded(self):
        result = self.check(r"""
            \begin{proof}\uses{a}\end{proof}
            \begin{lemma}\label{a}\end{lemma}
        """)
        self.assertError(result, "cannot associate proof dependencies")

    def test_chapter_and_remark_do_not_inherit_previous_proof_owner(self):
        for separator in [r"\chapter{Next}", r"\begin{remark}Text\end{remark}"]:
            with self.subTest(separator=separator):
                result = self.check(r"\begin{lemma}\label{a}\end{lemma}" + separator
                                    + r"\begin{proof}\uses{a}\end{proof}")
                self.assertError(result, "cannot associate proof dependencies")

    def test_comments_and_literal_examples_are_ignored(self):
        result = self.check(r"""
            % \label{a}\uses{missing}
            \verb|\label{a}\uses{missing}|
            \verb*+\ref{missing}+
            \verb|% \label{a}| \ref{a}
            \begin{verbatim}
            \begin{proof}\label{a}\uses{missing}\end{proof}
            \end{verbatim}
            \begin{minted}{tex}\ref{missing}\end{minted}
            \begin{comment}\label{a}\end{comment}
            \begin{lemma}\label{a}\end{lemma}
        """)
        self.assertEqual(result.errors, [])
        self.assertEqual(set(result.labels), {"a"})

    def test_all_supported_literal_environments(self):
        for kind in ["verbatim", "verbatim*", "lstlisting", "minted", "comment"]:
            with self.subTest(kind=kind):
                result = self.check(r"\begin{ " + kind + r" }\ref{missing}\end{ " + kind
                                    + r" }\label{live}")
                self.assertEqual(result.errors, [])
                self.assertEqual(set(result.labels), {"live"})

    def test_escaped_percent_and_comment_between_command_and_argument(self):
        result = self.check(r"""
            \% \label{real}
            \\% \label{commented}
            \ref% ignored comment
              {real}
        """)
        self.assertEqual(result.errors, [])
        self.assertEqual(set(result.labels), {"real"})

    def test_multiline_dependency_with_comments(self):
        result = self.check(r"""
            \begin{lemma}\label{a}\end{lemma}
            \begin{lemma}\label{b}
            \uses{ % explanation
              a % another explanation
            }
            \end{lemma}
        """)
        self.assertEqual(result.errors, [])
        self.assertEqual(set(result.dependencies["b"]), {"a"})

    def test_includes_and_proof_across_files(self):
        result = self.check(r"\input{chapters/statement}\include{chapters/proof.tex}", {
            "chapters/statement.tex": r"\begin{lemma}\label{a}\end{lemma}",
            "chapters/proof.tex": r"\begin{proof}\uses{b}\end{proof}\begin{lemma}\label{b}\end{lemma}",
        })
        self.assertEqual(result.errors, [])
        self.assertEqual(set(result.dependencies["a"]), {"b"})

    def test_missing_and_recursive_includes(self):
        result = self.check(r"\input{missing}\input{other}",
                            {"other.tex": r"\input{content}"})
        self.assertError(result, "included file not found")
        self.assertError(result, "recursive include")

    def test_unreferenced_files_are_not_part_of_the_document(self):
        result = self.check(r"\label{a}", {"unused.tex": r"\ref{missing}\label{a}"})
        self.assertEqual(result.errors, [])

    def test_malformed_metadata_fails_instead_of_being_skipped(self):
        for text in [r"\uses{", r"\ref{nested{label}}", r"\label{}", r"\ref{\macro}"]:
            with self.subTest(text=text):
                result = self.check(text)
                self.assertError(result, "literal")

    def test_unlabeled_nodes_and_unbalanced_environments_fail(self):
        result = self.check(r"\begin{lemma}Text\end{lemma}\end{proof}\begin{definition}")
        self.assertError(result, "graph node has no label")
        self.assertError(result, "unmatched \\end{proof}")
        self.assertError(result, "unclosed definition")

    def test_unterminated_literals_fail(self):
        for text in ["\\verb|unterminated\n", r"\begin{verbatim}unterminated"]:
            with self.subTest(text=text):
                result = self.check(text)
                self.assertError(result, "unterminated")

    def test_long_graph_and_multiple_cycles(self):
        location = Location(self.src / "content.tex", 1)
        result = Blueprint(nodes={f"n{i}": location for i in range(1500)})
        result.dependencies = {f"n{i}": {f"n{i+1}": location} for i in range(1499)}
        check_cycles(result)
        self.assertEqual(result.errors, [])
        result.dependencies["n1499"] = {"n1498": location}
        result.dependencies["n1"] = {"n0": location}
        check_cycles(result)
        self.assertEqual(len(result.errors), 2)
        self.assertError(result, "n0 -> n1 -> n0")
        self.assertError(result, "n1498 -> n1499 -> n1498")

    def test_cli_exit_codes(self):
        script = Path(__file__).resolve().parents[1] / "check_blueprint.py"
        for body, code, message in [(r"\label{valid}", 0, "checks passed"),
                                    (r"\ref{missing}", 1, "unknown label")]:
            with self.subTest(code=code):
                self.write("content.tex", body)
                run = subprocess.run([sys.executable, str(script), "--src", str(self.src)],
                                     text=True, capture_output=True)
                self.assertEqual(run.returncode, code, run.stderr)
                self.assertIn(message, run.stdout + run.stderr)
                self.assertNotIn("Traceback", run.stderr)
        (self.src / "content.tex").unlink()
        run = subprocess.run([sys.executable, str(script), "--src", str(self.src)],
                             text=True, capture_output=True)
        self.assertEqual(run.returncode, 1)
        self.assertIn("cannot read source", run.stderr)


if __name__ == "__main__":
    unittest.main()
