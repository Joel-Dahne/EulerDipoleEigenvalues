"""Test the local compilation cache without requiring plasTeX or Jinja."""

from pathlib import Path
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "blueprint/src"))
from templatecache import cache_templates


class Environment:
    def __init__(self, **kwargs):
        self.calls = []

    def from_string(self, source, globals=None, template_class=None):
        self.calls.append((source, globals, template_class))
        if source == "invalid":
            raise ValueError("invalid template")
        return object()


class TemplateCacheTests(unittest.TestCase):
    def setUp(self):
        self.renderer = SimpleNamespace(Environment=Environment)
        cache_templates(self.renderer)
        self.env = self.renderer.Environment()

    def test_reuses_compilation_of_the_same_source(self):
        first = self.env.from_string("hello")
        self.assertIs(self.env.from_string("hello"), first)
        self.assertEqual(self.env.calls, [("hello", None, None)])

    def test_different_sources_compile_separately(self):
        first = self.env.from_string("hello")
        second = self.env.from_string("world")
        self.assertIsNot(first, second)
        self.assertIs(self.env.from_string("hello"), first)
        self.assertEqual(len(self.env.calls), 2)

    def test_compilation_is_lazy_and_errors_are_not_cached(self):
        self.assertEqual(self.env.calls, [])
        for _ in range(2):
            with self.assertRaisesRegex(ValueError, "invalid template"):
                self.env.from_string("invalid")
        self.assertEqual(len(self.env.calls), 2)

    def test_cache_does_not_cross_environments_or_change_the_base_class(self):
        other = self.renderer.Environment()
        self.assertIsNot(self.env.from_string("hello"), other.from_string("hello"))
        self.assertEqual(len(other.calls), 1)
        base = Environment()
        self.assertIsNot(base.from_string("hello"), base.from_string("hello"))

    def test_explicit_globals_bypass_the_cache(self):
        original = self.env.from_string("hello")
        globals = {"name": "world"}
        self.assertIsNot(self.env.from_string("hello", globals=globals), original)
        self.assertIsNot(self.env.from_string("hello", globals=globals), original)
        self.assertEqual(self.env.calls[1:], [("hello", globals, None)] * 2)
        self.assertIs(self.env.from_string("hello"), original)

    def test_explicit_template_class_bypasses_the_cache(self):
        first = self.env.from_string("hello", template_class=object)
        self.assertIsNot(self.env.from_string("hello", template_class=object), first)
        self.assertEqual(self.env.calls, [("hello", None, object)] * 2)

    def test_non_string_source_bypasses_the_cache(self):
        source = []  # An unhashable stand-in for a parsed Jinja template tree.
        first = self.env.from_string(source)
        self.assertIsNot(self.env.from_string(source), first)
        self.assertEqual(self.env.calls, [(source, None, None)] * 2)


if __name__ == "__main__":
    unittest.main()
