#!/usr/bin/env python3
"""The EGF corrections register's rules (tools/corrections.py): the shipped register passes, and each
breakage of tools/fixtures/corrections fails the check, in-process."""
import os
import sys
import tomllib
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
sys.path.insert(0, os.path.join(ROOT, "tools", "fixtures", "corrections"))
import corrections as cr  # noqa: E402
import breakages  # noqa: E402


class CorrectionsRules(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = open(cr.FILE, encoding="utf-8").read()
        cls.data = tomllib.loads(cls.text)
        cls.names = cr.lean_decls()

    def errs(self, data):
        return cr.check(data, names=self.names)

    def test_the_shipped_register_passes(self):
        self.assertEqual(self.errs(self.data), [])

    def test_every_breakage_fails(self):
        for name, snippet in breakages.BREAKAGES(self.data).items():
            with self.subTest(breakage=name):
                self.assertTrue(self.errs(tomllib.loads(self.text + snippet)), name)

    def test_the_lean_index_reads_namespaces(self):
        for n in ("EGF.main_universality", "EGF.TwoPoint.negative_control_sharp", "EGF.Swap.printed_pinsker_negative_control_false"):
            self.assertIn(n, self.names)

    def test_set_status_edits_only_its_block(self):
        cid = self.data["correction"][1]["id"]
        new = tomllib.loads(cr.set_status(self.text, cid, "adopted"))
        old = {c["id"]: c for c in self.data["correction"]}
        for c in new["correction"]:
            if c["id"] == cid:
                self.assertEqual(c["status"], "adopted")
            else:
                self.assertEqual(c, old[c["id"]])

    def test_errata_lists_only_applied_entries(self):
        self.assertEqual(cr.errata(self.data), "")
        e = dict(self.data["correction"][0], status="applied")
        self.assertIn(e["summary"], cr.errata({"correction": [e]}))


if __name__ == "__main__":
    unittest.main()
