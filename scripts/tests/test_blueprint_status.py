"""Tests of source metadata placement, sector closures and generated reports."""

from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory
import textwrap
import unittest
from urllib.parse import unquote

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_blueprint import check_blueprint
from blueprint_status import SECTORS, closure, counts, remaining, render_report

TEST_SECTORS = (("Test", "thm:test", "test"),)


class StatusTests(unittest.TestCase):
    def setUp(self):
        self.tmp = TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.src = Path(self.tmp.name)

    def write(self, name, text):
        path = self.src / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(text).lstrip("\n"), encoding="utf-8")

    def parse(self, text, files=None):
        self.write("content.tex", text)
        for name, body in (files or {}).items():
            self.write(name, body)
        blueprint = check_blueprint(self.src)
        self.assertEqual(blueprint.errors, [])
        return blueprint

    def render(self, blueprint):
        return render_report(blueprint, self.src / "reports", TEST_SECTORS)

    def test_statement_and_proof_markers_are_separate(self):
        b = self.parse(r"""
            \chapter{Example}
            \begin{definition}\label{d}\leanok\end{definition}
            \begin{lemma}\label{a}\leanok\end{lemma}
            \begin{proof}\leanok\end{proof}
            \begin{lemma}\label{b}\lean{Some.declaration}\notready\end{lemma}
            \begin{proof}\leanok\end{proof}
        """)
        self.assertTrue(b.metadata["d"].statement_leanok)
        self.assertFalse(b.metadata["d"].proof_leanok)
        self.assertFalse(b.metadata["d"].has_proof)
        self.assertFalse(remaining(b.metadata["d"]))
        self.assertFalse(remaining(b.metadata["a"]))
        self.assertFalse(b.metadata["b"].statement_leanok)
        self.assertTrue(b.metadata["b"].proof_leanok)
        self.assertTrue(b.metadata["b"].notready)
        self.assertTrue(remaining(b.metadata["b"]))
        c = counts(b, set(b.nodes))
        self.assertEqual((c["nodes"], c["definitions"], c["results"]), (3, 1, 2))
        self.assertEqual((c["statements"], c["proofs"], c["remaining_results"]), (2, 2, 1))

    def test_mathlib_markers_are_counted_separately(self):
        b = self.parse(r"""
            \begin{definition}\label{d}\mathlibok\end{definition}
            \begin{lemma}\label{a}\mathlibok\end{lemma}
            \begin{lemma}\label{b}\leanok\mathlibok\end{lemma}
        """)
        c = counts(b, set(b.nodes))
        self.assertEqual((c["statements"], c["proofs"], c["mathlib"]), (1, 0, 3))
        self.assertEqual((c["remaining_results"], c["remaining_definitions"]), (0, 0))

    def test_comments_literal_examples_and_remark_flags_do_not_count(self):
        b = self.parse(r"""
            \begin{lemma}\label{a}
            % \leanok
            \verb|\leanok|
            \begin{remark}\leanok\mathlibok\notready\end{remark}
            \end{lemma}
            \begin{proof}\verb|\leanok|\end{proof}
            \begin{remark}\leanok\end{remark}
            \begin{lemma}\label{b}\end{lemma}
            \begin{proof}\begin{verbatim}\leanok\end{verbatim}\end{proof}
        """)
        for m in b.metadata.values():
            self.assertFalse(m.statement_leanok)
            self.assertFalse(m.proof_leanok)
            self.assertFalse(m.mathlibok)
            self.assertFalse(m.notready)
            self.assertTrue(m.has_proof)

    def test_explicit_forward_proof_target(self):
        b = self.parse(r"""
            \begin{proof}\proves{a}\leanok\end{proof}
            \begin{lemma}\label{a}\leanok\end{lemma}
            \begin{lemma}\label{b}\leanok\end{lemma}
        """)
        self.assertTrue(b.metadata["a"].proof_leanok)
        self.assertFalse(b.metadata["b"].proof_leanok)

    def test_last_associated_proof_controls_completion_like_plastex(self):
        b = self.parse(r"""
            \begin{lemma}\label{a}\leanok\end{lemma}
            \begin{proof}\leanok\end{proof}
            \begin{proof}Another argument.\end{proof}
        """)
        self.assertTrue(b.metadata["a"].has_proof)
        self.assertFalse(b.metadata["a"].proof_leanok)

    def test_closure_includes_root_and_both_kinds_of_prerequisites_once(self):
        b = self.parse(r"""
            \begin{definition}\label{d}\end{definition}
            \begin{lemma}\label{a}\uses{d}\end{lemma}
            \begin{lemma}\label{unrelated}\end{lemma}
            \begin{theorem}\label{thm:test}\uses{d}\leanok\end{theorem}
            \begin{proof}\uses{a,d}\leanok\end{proof}
        """)
        labels = closure(b, "thm:test")
        self.assertEqual(labels, {"thm:test", "a", "d"})
        c = counts(b, labels)
        self.assertEqual((c["remaining_results"], c["remaining_definitions"]), (1, 1))
        report = self.render(b)
        self.assertIn("**Remaining:** 1 result and 1 definition.", report)
        self.assertNotIn("[`unrelated`]", report)
        self.assertIn("A marked proof may depend on admitted inputs", report)
        with self.assertRaisesRegex(ValueError, "not a blueprint graph node"):
            closure(b, "missing")

    def test_chapters_and_nodes_keep_document_order_across_inputs(self):
        b = self.parse(r"""
            \begin{definition}\label{d}\end{definition}
            \chapter{Zeta}
            \input{chapter}
            \chapter{Alpha}
            \begin{lemma}\label{a}\end{lemma}
            \begin{theorem}\label{thm:test}\uses{a,z,d}\leanok\end{theorem}
            \begin{proof}\leanok\end{proof}
        """, {"chapter.tex": r"\begin{lemma}\label{z}\end{lemma}"})
        self.assertEqual(b.metadata["z"].chapter.title, "Zeta")
        report = self.render(b)
        self.assertLess(report.index("### Unchaptered nodes"), report.index("### Zeta"))
        self.assertLess(report.index("### Zeta"), report.index("### Alpha"))
        self.assertLess(report.index("[`z`]"), report.index("[`a`]"))

    def test_repeated_heading_inputs_do_not_merge_chapters(self):
        b = self.parse(r"""
            \input{heading}
            \begin{lemma}\label{a}\end{lemma}
            \input{heading}
            \begin{lemma}\label{b}\end{lemma}
            \begin{theorem}\label{thm:test}\uses{a,b}\leanok\end{theorem}
            \begin{proof}\leanok\end{proof}
        """, {"heading.tex": r"\chapter{Repeated heading}"})
        self.assertIsNot(b.metadata["a"].chapter, b.metadata["b"].chapter)
        report = self.render(b)
        self.assertEqual(report.count("### Repeated heading"), 2)
        self.assertEqual(report.count("[`a`]"), 1)
        self.assertEqual(report.count("[`b`]"), 1)

    def test_formatted_chapter_title_uses_filename_fallback(self):
        b = self.parse(r"""
            \chapter{A \emph{formatted} title}
            \begin{theorem}\label{thm:test}\end{theorem}
        """)
        self.assertEqual(b.metadata["thm:test"].chapter.title, "content")
        self.assertIn("### content", self.render(b))

    def test_source_links_are_relative_to_output_and_point_to_label_lines(self):
        b = self.parse(r"\input{nested folder/chapter}", {"nested folder/chapter.tex": r"""
            \chapter{Example}
            \begin{theorem}\label{thm:test}\end{theorem}
        """})
        report = self.render(b)
        self.assertIn("../nested%20folder/chapter.tex#L2", report)
        self.assertIn("[content.tex](../content.tex)", report)
        for target in re.findall(r"\]\(([^)]+)\)", report):
            if target.startswith("#"):
                continue
            path, _, anchor = target.partition("#")
            source = (self.src / "reports" / unquote(path)).resolve()
            self.assertTrue(source.is_file(), target)
            if anchor.startswith("L"):
                self.assertIn(r"\label{thm:test}", source.read_text().splitlines()[int(anchor[1:]) - 1])

    def test_report_shows_partial_statement_and_missing_proof_environment(self):
        b = self.parse(r"""
            \begin{lemma}\label{a}\lean{Partial.link}\end{lemma}
            \begin{lemma}\label{b}\end{lemma}
            \begin{proof}\leanok\end{proof}
            \begin{theorem}\label{thm:test}\uses{a,b}\end{theorem}
        """)
        report = self.render(b)
        self.assertIn("| lemma | Unmarked | No proof environment | No |", report)
        self.assertIn(r"| lemma | Unmarked | `\leanok` | No |", report)
        self.assertIn(r"A `\lean{...}` link alone does not count", report)

    def test_completed_scope_and_notready_flag_are_not_reinterpreted(self):
        b = self.parse(r"""
            \begin{theorem}\label{thm:test}\leanok\notready\end{theorem}
            \begin{proof}\leanok\end{proof}
        """)
        self.assertTrue(b.metadata["thm:test"].notready)
        self.assertFalse(remaining(b.metadata["thm:test"]))
        report = self.render(b)
        self.assertIn("No unfinished nodes according to these markers.", report)
        self.assertEqual(report, self.render(b))

    def run_cli(self, *args):
        script = Path(__file__).resolve().parents[1] / "blueprint_status.py"
        return subprocess.run([sys.executable, str(script), "--src", str(self.src), *map(str, args)],
                              text=True, capture_output=True)

    def sector_fixture(self):
        self.write("content.tex", "\n".join(
            r"\begin{theorem}\label{" + target + r"}\end{theorem}"
            for _, target, _ in SECTORS))

    def test_cli_stdout_and_output_file_are_deterministic(self):
        self.sector_fixture()
        first, second = self.run_cli(), self.run_cli()
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(first.stdout, second.stdout)
        self.assertIn("# Generated blueprint status", first.stdout)
        target = self.src / "reports/status.md"
        run = self.run_cli("--output", target)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("<!-- Generated", target.read_text())
        self.assertIn('id="even-even"', target.read_text())
        self.assertIn('id="odd-odd"', target.read_text())
        self.assertIn('id="mixed"', target.read_text())
        before = target.read_bytes()
        self.assertEqual(self.run_cli("--output", target).returncode, 0)
        self.assertEqual(target.read_bytes(), before)

    def test_cli_refuses_invalid_sources_without_overwriting_report(self):
        target = self.src / "status.md"
        target.write_text("old report")
        self.write("content.tex", r"\ref{missing}")
        run = self.run_cli("--output", target)
        self.assertEqual(run.returncode, 1)
        self.assertIn("consistency checks failed", run.stderr)
        self.assertEqual(target.read_text(), "old report")
        self.assertNotIn("Traceback", run.stderr)

    def test_cli_refuses_missing_sector_targets(self):
        self.write("content.tex", r"\begin{lemma}\label{a}\end{lemma}")
        target = self.src / "status.md"
        run = self.run_cli("--output", target)
        self.assertEqual(run.returncode, 1)
        self.assertIn("report target", run.stderr)
        self.assertFalse(target.exists())

    def test_cli_output_errors_do_not_traceback(self):
        self.sector_fixture()
        blocker = self.src / "not-a-directory"
        blocker.write_text("file")
        run = self.run_cli("--output", blocker / "status.md")
        self.assertEqual(run.returncode, 1)
        self.assertIn("Status report not generated", run.stderr)
        self.assertNotIn("Traceback", run.stderr)


if __name__ == "__main__":
    unittest.main()
