"""Regression tests for the Lean trace generator (no Lean build required)."""

from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'generate_mixed_odd_b_traces.py'


class MixedOddBTraceTests(unittest.TestCase):
    def run_generator(self, *args, cwd=None):
        return subprocess.run([sys.executable, '-B', SCRIPT, *args], cwd=cwd,
                              capture_output=True, text=True)

    def assert_success(self, result):
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_committed_traces(self):
        self.assert_success(self.run_generator('--check'))

    def test_regenerate_and_detect_mismatches(self):
        with TemporaryDirectory() as tmp:
            output = Path(tmp) / 'traces'
            args = ('--output-dir', output, '8', '9')
            self.assert_success(self.run_generator(*args, cwd=tmp))
            self.assert_success(self.run_generator('--check', *args, cwd=tmp))
            missing = output / 'Strip8Full.lean'
            missing.unlink()
            changed = output / 'Strip9.lean'
            changed.write_bytes(b'changed\n')
            stale = output / 'Strip8' / 'Stale.lean'
            stale.touch()
            result = self.run_generator('--check', *args, cwd=tmp)
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn(f'missing: {missing}', result.stderr)
            self.assertIn(f'differs: {changed}', result.stderr)
            self.assertIn(f'unexpected generated file: {stale}', result.stderr)
            self.assertFalse(missing.exists())
            self.assertEqual(changed.read_bytes(), b'changed\n')
            self.assertTrue(stale.is_file())
            stale.unlink()
            self.assert_success(self.run_generator(*args, cwd=tmp))
            self.assert_success(self.run_generator('--check', *args, cwd=tmp))


if __name__ == '__main__':
    unittest.main()
