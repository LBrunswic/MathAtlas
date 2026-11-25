#!/usr/bin/env python3
"""The restatement registers' rules (tools/restate.py): every shipped register passes, each breakage
of tools/fixtures/restate fails the check, in-process, and the detector reads its signals."""
import os
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
sys.path.insert(0, os.path.join(ROOT, "tools", "fixtures", "restate"))
import restate as rs  # noqa: E402
import restate_breakages  # noqa: E402

SLUG = "gx"


class RestateRules(unittest.TestCase):
    def test_every_shipped_register_passes(self):
        for s in rs.slugs_all():
            with self.subTest(paper=s):
                self.assertEqual(rs.errors(s)[0], [])

    def test_every_breakage_fails(self):
        entries = rs.load(SLUG)
        with tempfile.TemporaryDirectory() as t:
            for name, broken in restate_breakages.BREAKAGES(SLUG, entries).items():
                with self.subTest(breakage=name):
                    p = os.path.join(t, name + ".toml")
                    rs.save(SLUG, broken, p)
                    self.assertTrue(rs.errors(SLUG, p)[0], name)

    def test_signals(self):
        row = {"decls": ["GX.not_foo"], "paper_findings": ["fine"], "notes": ""}
        self.assertEqual(rs.signals(row)[0], "strong")
        row = {"decls": [], "paper_findings": ["l.12: false as printed, see below"], "notes": ""}
        self.assertEqual(rs.signals(row)[0], "strong")
        row = {"decls": [], "paper_findings": ["the corrected form adds n >= 1"], "notes": ""}
        self.assertEqual(rs.signals(row)[0], "weak")
        row = {"decls": ["GX.foo"], "paper_findings": ["clean"], "notes": "audited"}
        self.assertIsNone(rs.signals(row)[0])

    def test_dump_round_trips_latex(self):
        e = dict(rs.load(SLUG)[0], rewritten="Let $\\alpha \\in A$.\nThen \"x\".", changes=["+ hypothesis: $n \\ge 1$"])
        with tempfile.TemporaryDirectory() as t:
            p = os.path.join(t, "r.toml")
            rs.save(SLUG, [e], p)
            self.assertEqual(rs.load(SLUG, p)[0]["rewritten"].strip(), e["rewritten"].strip())
            self.assertEqual(rs.load(SLUG, p)[0]["changes"], e["changes"])


if __name__ == "__main__":
    unittest.main()
