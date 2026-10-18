"""Exercise the web recipe's output handling without running plasTeX."""

import os
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory
import unittest


JUST = shutil.which("just")
JUSTFILE = Path(__file__).resolve().parents[2] / "justfile"


@unittest.skipUnless(JUST, "just is not installed")
class WebRecipeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        bin_dir = self.root / "bin"
        bin_dir.mkdir()
        # Only the nested `_web` invocation is stubbed; the outer recipe is real.
        stub = bin_dir / "just"
        stub.write_text(
            '#!/bin/sh\n'
            '[ "$1" = --justfile ] && [ "$3" = _web ] || exit 99\n'
            'i=0\n'
            'while [ "$i" -lt 80 ]; do echo "detail-$i"; i=$((i + 1)); done\n'
            'echo "child stderr" >&2\n'
            'exit "${WEB_TEST_EXIT:-0}"\n',
            encoding="utf-8",
        )
        stub.chmod(0o755)
        self.env = dict(os.environ, PATH=f"{bin_dir}{os.pathsep}{os.environ['PATH']}",
                        TMPDIR=str(self.root))

    def run_web(self, *args, exit_code=0):
        env = dict(self.env, WEB_TEST_EXIT=str(exit_code))
        return subprocess.run(
            [JUST, "--justfile", str(JUSTFILE), "web", *args],
            env=env, capture_output=True, text=True, timeout=10,
        )

    def log(self):
        logs = list(self.root.glob("blueprint-web.*"))
        self.assertEqual(len(logs), 1)
        return logs[0]

    def test_quiet_success_retains_full_log(self):
        result = self.run_web()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Web build passed", result.stdout)
        self.assertNotIn("detail-", result.stdout)
        self.assertEqual(result.stderr, "")
        log = self.log()
        self.assertIn(str(log), result.stdout)
        self.assertIn("detail-0\n", log.read_text())
        self.assertIn("child stderr", log.read_text())

    def test_verbose_flags_stream_output(self):
        for flag in ("--verbose", "-v"):
            with self.subTest(flag=flag):
                result = self.run_web(flag)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("detail-0\n", result.stdout)
                self.assertIn("child stderr", result.stdout)
                self.assertIn("Web build passed", result.stdout)
                self.log().unlink()

    def test_quiet_failure_prints_tail_and_preserves_failure(self):
        result = self.run_web(exit_code=7)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("Web build passed", result.stdout)
        self.assertNotIn("detail-0\n", result.stderr)
        self.assertIn("detail-79\n", result.stderr)
        self.assertIn("child stderr", result.stderr)
        self.assertIn("Web build failed", result.stderr)
        log = self.log()
        self.assertIn(str(log), result.stderr)
        self.assertIn("detail-0\n", log.read_text())

    def test_verbose_failure_is_not_masked_by_tee(self):
        result = self.run_web("--verbose", exit_code=7)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("detail-0\n", result.stdout)
        self.assertIn("Web build failed", result.stderr)
        self.assertIn(str(self.log()), result.stderr)

    def test_unknown_option_rejected_before_build(self):
        result = self.run_web("--unknown")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Usage: just web", result.stderr)
        self.assertEqual(list(self.root.glob("blueprint-web.*")), [])


if __name__ == "__main__":
    unittest.main()
