#!/usr/bin/env python3
"""The import-tier gate (tools/import_gate.py, ARCHITECTURE.md §4.4): its header reader, the
miniature hub of tools/fixtures/import-gate (which passes), each breakage (which fails with its
rule), and the shipped tier file (which loads and claims every module of the hub). The hub's own
violations are not asserted: the packages mix tiers until the window, which is why the gate runs
in report mode."""
import contextlib
import io
import os
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
sys.path.insert(0, os.path.join(ROOT, "tools", "fixtures", "import-gate"))
import import_gate as ig  # noqa: E402
import import_breakages as ib  # noqa: E402


def rules(res):
    return {v["rule"] for v in res["violations"]} | ({"CONFIG"} if res["config"] else set())


class HeaderReader(unittest.TestCase):
    def test_reads_only_the_header(self):
        text = ("/- a /- nested -/ comment\nimport X.Commented -/\n-- import X.Line\n"
                "module\npublic import A.B\nmeta import C\nimport all D.E -- tail\n"
                "\n/-! doc\nimport X.Doc\n-/\nimport F\nnamespace N\nimport X.After\nend N\n")
        self.assertEqual(ig.header_imports(text), [(5, "A.B"), (6, "C"), (7, "D.E"), (12, "F")])

    def test_stops_at_the_first_command(self):
        self.assertEqual(ig.header_imports("theorem t : True := trivial\nimport A\n"), [])

    def test_patterns(self):
        self.assertTrue(ig.pattern_matches("Causal.Flat", "Causal.Flat.Lox.X"))
        self.assertTrue(ig.pattern_matches("Causal.Flat", "Causal.Flat"))
        self.assertFalse(ig.pattern_matches("Causal.Flat", "Causal.FlatX"))
        self.assertTrue(ig.pattern_matches("Causal.Flat.Selberg*", "Causal.Flat.SelbergBase"))
        self.assertFalse(ig.pattern_matches("Causal.Flat.Selberg*", "Causal.Flat.Abel"))


class Fixture(unittest.TestCase):
    def run_gate(self, name=None):
        with tempfile.TemporaryDirectory() as d:
            ib.build(d, name)
            return ig.run(d, os.path.join(d, "tiers.toml"))

    def test_the_unbroken_hub_passes(self):
        res = self.run_gate()
        self.assertEqual((res["config"], res["violations"]), ([], []))
        self.assertEqual(res["stats"]["imports"], 11)  # the comments in A.Core are not counted

    def test_every_breakage_fails_with_its_rule(self):
        for name, (rule, _, _) in ib.BREAKAGES.items():
            with self.subTest(breakage=name):
                self.assertIn(rule, rules(self.run_gate(name)))

    def test_check_exits_1_and_report_exits_0(self):
        with tempfile.TemporaryDirectory() as d:
            ib.build(d, "upward")
            args = ["--hub", d, "--tiers", os.path.join(d, "tiers.toml")]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(ig.main(["check"] + args), 1)
                self.assertEqual(ig.main(["report"] + args), 0)


class ShippedTiers(unittest.TestCase):
    # Only the tier file itself is asserted. What the hub's modules do (an undeclared new package, a
    # stale import) is the report's business, not a red test, until the window (§5).
    def test_the_tier_file_loads(self):
        libs, errs = ig.load_tiers(os.path.join(ROOT, "tools", "import_tiers.toml"))
        self.assertEqual(errs, [])
        self.assertTrue({"ETT", "GX", "AffineGX", "Lorentzian", "orbit-discrete-groups"} <= set(libs))

    def test_the_hub_is_read(self):
        res = ig.run(ROOT, os.path.join(ROOT, "tools", "import_tiers.toml"))
        self.assertGreater(res["stats"]["modules"], 0)
        self.assertGreater(res["stats"]["imports"], 0)

if __name__ == "__main__":
    unittest.main()
