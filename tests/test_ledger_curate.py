#!/usr/bin/env python3
"""The curation file is the whole truth about the curated fields, and nothing else moves.

A three-row ledger is enough: a row the file curates, a row it used to curate and no longer
names, and a row it never touched. The tool must write the first, clear the second, leave the
third alone, and refuse a label or a field that does not exist.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
import ledger_curate as lc  # noqa: E402


def row(label, **kw):
    r = {"label": label, "kind": "theorem", "lean_stated": "strict", "lean_proved": "closed",
         "lean_files": ["L/A.lean"], "decls": [], "bucket": "", "deps": []}
    r.update(kw)
    return r


def ledger():
    return {"paper": {"path": "p.tex"}, "lean": {},
            "statements": [row("theo:a"),
                           row("theo:b", decls=["L.old"], bucket="A", notes="stale note"),
                           row("theo:c")]}


class Apply(unittest.TestCase):

    def test_a_curated_field_is_written(self):
        out = lc.apply(ledger(), {"row": [{"label": "theo:a", "decls": ["L.main"], "bucket": "A",
                                          "paper_findings": ["a hypothesis is not used"]}]})
        a = out["statements"][0]
        self.assertEqual(a["decls"], ["L.main"])
        self.assertEqual(a["bucket"], "A")
        self.assertEqual(a["paper_findings"], ["a hypothesis is not used"])

    def test_a_field_the_file_no_longer_names_is_cleared(self):
        out = lc.apply(ledger(), {"row": [{"label": "theo:a", "bucket": "A"}]})
        b = out["statements"][1]
        self.assertEqual(b["decls"], [])
        self.assertEqual(b["bucket"], "")
        self.assertNotIn("notes", b)

    def test_a_computed_field_never_moves(self):
        before = ledger()
        out = lc.apply(ledger(), {"row": [{"label": "theo:a", "bucket": "B",
                                          "lean_proved_override": "partial"}]})
        for s, t in zip(out["statements"], before["statements"]):
            for k in ("lean_stated", "lean_proved", "lean_files", "deps", "kind"):
                self.assertEqual(s[k], t[k])
        self.assertEqual(out["paper"]["path"], "p.tex")

    def test_the_triage_is_top_level(self):
        tri = [{"label": "theo:a", "kind": "sentence", "one_line": "x"}]
        out = lc.apply(ledger(), {"findings_triage": tri})
        self.assertEqual(out["paper"]["findings_triage"], tri)
        again = lc.apply(out, {})
        self.assertNotIn("findings_triage", again["paper"])

    def test_applying_twice_changes_nothing(self):
        cur = {"row": [{"label": "theo:c", "decls": ["L.c"], "notes": "n"}]}
        once = lc.apply(ledger(), cur)
        twice = lc.apply(lc.apply(ledger(), cur), cur)
        self.assertEqual(once, twice)


class Refusals(unittest.TestCase):

    def test_a_label_absent_from_the_ledger_is_refused(self):
        with self.assertRaises(lc.Misconfigured):
            lc.apply(ledger(), {"row": [{"label": "theo:nope", "bucket": "A"}]})

    def test_a_field_which_is_not_curated_is_refused(self):
        with self.assertRaises(lc.Misconfigured):
            lc.apply(ledger(), {"row": [{"label": "theo:a", "lean_proved": "closed"}]})

    def test_a_misspelt_field_is_refused_not_dropped(self):
        with self.assertRaises(lc.Misconfigured):
            lc.apply(ledger(), {"row": [{"label": "theo:a", "bukcet": "A"}]})

    def test_a_label_curated_twice_is_refused(self):
        with self.assertRaises(lc.Misconfigured):
            lc.apply(ledger(), {"row": [{"label": "theo:a", "bucket": "A"},
                                        {"label": "theo:a", "bucket": "B"}]})


if __name__ == "__main__":
    unittest.main()
