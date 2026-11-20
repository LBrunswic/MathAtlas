#!/usr/bin/env python3
"""The ETT programme's tools: the ladder's rules, the binder's links, the leases' ownership.

Each rule is shown to fail on a hand-built input that breaks it, and the shipped files to pass.
"""
import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import binder as bd  # noqa: E402
import ladder as ld  # noqa: E402
import lease as ls  # noqa: E402

NAMES = {"P.a", "P.b", "P.c", "a_to_b", "B.toC", "cex_a_not_c", "P.closedJ"}


def prop(i):
    return {"id": i, "lean": "P." + i, "what": i}


def lad(**kw):
    d = {"property": [prop("a"), prop("b"), prop("c")],
         "implies": [{"from": ["a"], "to": "b", "witness": "a_to_b", "status": "checked"}]}
    d.update(kw)
    return d


class Ladder(unittest.TestCase):
    def test_shipped_ladder_passes(self):
        self.assertEqual(ld.check(ld.load()), [])

    def test_good_ladder_passes(self):
        self.assertEqual(ld.check(lad(), NAMES), [])

    def test_unresolved_witness_fails(self):
        d = lad(implies=[{"from": ["a"], "to": "b", "witness": "nowhere", "status": "seed"}])
        self.assertTrue(any("witness not found" in e for e in ld.check(d, NAMES)))

    def test_contradiction_fails(self):
        d = lad(implies=[{"from": ["a"], "to": "b", "witness": "a_to_b", "status": "checked"},
                         {"from": ["b"], "to": "c", "witness": "B.toC", "status": "checked"}],
                fails=[{"from": "a", "to": "c", "witness": "cex_a_not_c", "status": "checked"}])
        self.assertTrue(any("contradiction" in e for e in ld.check(d, NAMES)))

    def test_counterexample_propagates(self):
        d = lad(fails=[{"from": "a", "to": "c", "witness": "cex_a_not_c", "status": "checked"}])
        m = ld.matrix(d)
        self.assertEqual(m[("a", "b")], "implied")
        self.assertEqual(m[("a", "c")], "fails")
        self.assertEqual(m[("b", "c")], "fails")     # the counterexample has a, hence b, and lacks c
        self.assertEqual(m[("c", "a")], "unknown")

    def test_settled_open_fails(self):
        d = lad(open=[{"from": "a", "to": "b", "note": "?"}])
        self.assertTrue(any("already settled" in e for e in ld.check(d, NAMES)))

    def test_emit_only_checked_single_premise(self):
        d = lad(implies=[{"from": ["a"], "to": "b", "witness": "a_to_b", "status": "checked"},
                         {"from": ["b"], "to": "c", "witness": "B.toC", "status": "seed"}])
        out = ld.emit_lean(d)
        self.assertIn("a_to_b", out)
        self.assertNotIn("B.toC", out)


class Binder(unittest.TestCase):
    def setUp(self):
        self.lp = os.path.join(ROOT, "papers", "zz-binder-test", "ledger")
        os.makedirs(self.lp, exist_ok=True)
        open(os.path.join(self.lp, "ledger.json"), "w").write('{"statements": [{"label": "thm:x"}]}')

    def tearDown(self):
        import shutil
        shutil.rmtree(os.path.join(ROOT, "papers", "zz-binder-test"))

    def errs(self, rows):
        return bd.check("zz-binder-test", {"bind": rows}, NAMES, {"a", "b"}, {"T-abs-x"})

    def test_good_binder_passes(self):
        r = {"label": "thm:x", "ett": ["T-abs-x"], "localisation": ["a"],
             "geometric": [{"model": "minkowski", "proves": ["a"], "by": ["a_to_b"]}]}
        self.assertEqual(self.errs([r]), [])

    def test_unbound_localisation_fails(self):
        r = {"label": "thm:x", "ett": ["T-abs-x"], "localisation": ["a"]}
        self.assertTrue(any("provided by no geometric" in e for e in self.errs([r])))

    def test_declared_open_localisation_passes(self):
        r = {"label": "thm:x", "ett": ["T-abs-x"], "localisation": ["a"], "open_localisation": ["a"]}
        self.assertEqual(self.errs([r]), [])

    def test_unknown_label_and_target_fail(self):
        e = self.errs([{"label": "thm:none", "ett": ["T-abs-missing"]}])
        self.assertTrue(any("not a ledger label" in x for x in e))
        self.assertTrue(any("resolves to neither" in x for x in e))


class Lease(unittest.TestCase):
    def test_covers_is_a_path_prefix(self):
        self.assertTrue(ls.covers("lean-causal", "lean-causal/Causal/X.lean"))
        self.assertFalse(ls.covers("lean-causal", "lean-causal-extra/X.lean"))
        self.assertTrue(ls.overlap("lean-causal/Causal", "lean-causal"))

    def test_holder(self):
        held = {"atlas": {"pid": 1, "paths": ["lean-gx"]}, "prog": {"pid": 2, "paths": ["programme"]}}
        self.assertEqual(ls.holder("programme/roadmap.toml", held), "prog")
        self.assertIsNone(ls.holder("lean-causal/Causal.lean", held))


if __name__ == "__main__":
    unittest.main()
