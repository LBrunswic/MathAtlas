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
        # Independent of how far the shipped register has got: below `applied` nothing is listed,
        # and an applied (or reviewed) entry is listed by its summary.
        entries = [c for c in self.data["correction"] if c.get("summary")]
        below = [dict(c, status="adopted") for c in entries]
        self.assertEqual(cr.errata({"correction": below}), "")
        for st in ("applied", "reviewed"):
            e = dict(entries[0], status=st)
            self.assertIn(e["summary"], cr.errata({"correction": [e] + below[1:]}))
        shipped = cr.errata(self.data)
        for c in self.data["correction"]:
            if c.get("summary") and c["status"] not in ("applied", "reviewed"):
                self.assertNotIn(c["summary"], shipped, c["id"])

    def test_a_superseded_entry_closes_with_its_superseders(self):
        sup = {"id": "C-1", "status": "proved", "superseded_by": ["C-2", "C-3"]}
        by = lambda a, b: {"C-1": sup, "C-2": {"id": "C-2", "status": a}, "C-3": {"id": "C-3", "status": b}}
        self.assertFalse(cr.closed(sup, by("adopted", "applied")))
        self.assertTrue(cr.closed(sup, by("applied", "reviewed")))
        self.assertFalse(cr.closed({"id": "C-4", "status": "proved"}, {}))
        self.assertTrue(cr.closed({"id": "C-5", "status": "applied"}, {}))

    def test_errata_omits_a_superseded_entry(self):
        e = dict(next(c for c in self.data["correction"] if c.get("summary")), status="applied")
        self.assertIn(e["summary"], cr.errata({"correction": [e]}))
        self.assertNotIn(e["summary"], cr.errata({"correction": [dict(e, superseded_by=["C-1"])]}))


if __name__ == "__main__":
    unittest.main()
