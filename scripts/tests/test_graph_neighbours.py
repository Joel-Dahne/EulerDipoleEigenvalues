"""Check graph-script configuration and, when Node is available, its DOM behaviour."""

import configparser
import json
from pathlib import Path
import shutil
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "blueprint/src/graph_neighbours.js"
FIXTURE = Path(__file__).with_name("graph_neighbours.test.js")
NODE = shutil.which("node") or shutil.which("nodejs")


class GraphNeighbourTests(unittest.TestCase):
    def test_extra_script_is_configured_and_exists(self):
        # The standalone graph template reads config extra-js, not PackageJs
        # resources; using only the latter silently omits the script on graphs.
        config = configparser.ConfigParser()
        config.read(ROOT / "blueprint/src/plastex.cfg")
        self.assertIn(SOURCE.name, config["html5"]["extra-js"].split())
        self.assertTrue(SOURCE.is_file())

    @unittest.skipUnless(NODE, "Node is not installed (DOM fixture also runs in other JS engines)")
    def test_dom_behaviour(self):
        program = FIXTURE.read_text(encoding="utf-8") + "\nconsole.log(testGraphNeighbours(" + json.dumps(
            SOURCE.read_text(encoding="utf-8")
        ) + "));\n"
        result = subprocess.run(
            [NODE], input=program, text=True, capture_output=True, timeout=10,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Graph neighbour DOM tests passed", result.stdout)


if __name__ == "__main__":
    unittest.main()
