#!/usr/bin/env python3
"""The roadmap's rules, on hand-built targets: each rule is shown to fail on a target that breaks it."""
import os
import sys
import tomllib
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import roadmap as rm  # noqa: E402


def target(**kw):
    t = {"id": "T-a", "title": "a", "stream": "s", "kind": "tooling", "status": "ready", "owner": "builder",
         "priority": 1, "evidence": "e", "added": "2026-11-20", "proposed_by": "test"}
    t.update(kw)
    return t


class RoadmapRules(unittest.TestCase):
    def errs(self, *targets):
        return rm.check({"target": list(targets)}, root=ROOT)

    def test_a_good_target_passes(self):
        self.assertEqual(self.errs(target()), [])

    def test_the_shipped_roadmap_passes(self):
        self.assertEqual(rm.check(rm.load(), root=ROOT), [])

    def test_unknown_label_fails(self):
        e = self.errs(target(kind="close", owner="closer", paper="gx", labels=["theo:no_such_label"]))
        self.assertTrue(any("not in papers/gx/ledger" in x for x in e), e)

    def test_close_without_labels_fails(self):
        self.assertTrue(self.errs(target(kind="close", owner="closer", paper="gx")))

    def test_needs_ruling_without_question_fails(self):
        self.assertTrue(any("question" in x for x in self.errs(target(status="needs-ruling"))))

    def test_blocked_on_a_ruled_question_fails(self):
        self.assertTrue(any("OPEN" in x for x in self.errs(target(status="blocked", oq="OQ-7"))))

    def test_done_without_commit_fails(self):
        self.assertTrue(any("commit" in x for x in self.errs(target(status="done"))))

    def test_cycle_fails(self):
        e = self.errs(target(id="T-a", status="planned", depends=["T-b"]), target(id="T-b", status="planned", depends=["T-a"]))
        self.assertTrue(any("cycle" in x for x in e), e)

    def test_ready_before_its_dependency_fails(self):
        e = self.errs(target(id="T-a", depends=["T-b"]), target(id="T-b", status="planned"))
        self.assertTrue(any("dependency" in x for x in e), e)

    def test_too_many_active_fail(self):
        ts = [target(id="T-a%d" % i, status="active") for i in range(rm.MAX_PARALLEL + 1)]
        self.assertTrue(any("MAX_PARALLEL" in x for x in self.errs(*ts)))
        self.assertFalse(any("MAX_PARALLEL" in x for x in self.errs(*ts[:rm.MAX_PARALLEL])))

    def test_wave_keeps_targets_independent(self):
        c = lambda tid, p, labels, **kw: target(id=tid, owner="closer", kind="close", paper=p, labels=labels, **kw)
        d = {"target": [
            c("T-a", "ett", ["x"], priority=1), c("T-b", "ett", ["x"], priority=2),      # shares a label with T-a
            c("T-c", "ett", ["y"], priority=3), c("T-d", "ett", ["z"], priority=4),
            c("T-e", "ett", ["w"], priority=5),                                          # 4th in lean-causal
            c("T-f", "gx", ["u"], priority=6, exclusive=True), c("T-g", "gx", ["v"], priority=7),
            c("T-h", "benzecri", ["t"], priority=8, depends=["T-a"]),                   # dependency not done
            target(id="T-i", priority=9), target(id="T-j", priority=10)]}               # two builders
        self.assertEqual(rm.wave(d), ["T-a", "T-c", "T-d", "T-f", "T-i"])
        d["target"][0]["status"] = "active"                                              # T-a running
        self.assertEqual(rm.wave(d), ["T-c", "T-d", "T-f", "T-i"])

    def test_next_respects_priority_and_owner(self):
        d = {"target": [target(id="T-a", priority=2), target(id="T-b", priority=1, owner="closer", kind="research"),
                        target(id="T-c", priority=0, status="planned")]}
        self.assertEqual(rm.next_target(d), "T-b")
        self.assertEqual(rm.next_target(d, owner="builder"), "T-a")

    def test_set_status_edits_only_its_block(self):
        text = '# head\n[[target]]\nid = "T-a"\nstatus = "ready"\n\n[[target]]\nid = "T-b"\nstatus = "ready"\n'
        out = rm.set_status(text, "T-a", "active", oq="OQ-1")
        d = tomllib.loads(out)
        self.assertEqual([t["status"] for t in d["target"]], ["active", "ready"])
        self.assertEqual(d["target"][0]["oq"], "OQ-1")
        self.assertTrue(out.startswith("# head\n"))

    def test_gates_flags_only_new_red(self):
        log = ("papers/bbs\n  FAIL no ledger\npapers/gx\n  ok\n"
               "make[1]: *** [Makefile:25: gate-registers] Error 1\n"
               "make: *** [Makefile:43: gate-tests] Error 1\nmake: *** [Makefile:58: papers-check] Error 1\n")
        d = {"gates": {"known_red": ["gate-tests: freeze", "papers-check: papers/bbs has no ledger"]}}
        self.assertEqual(rm.new_red(d, log), [])
        self.assertEqual(rm.new_red(d, log + "papers/ett\n  FAIL x\nmake: *** [Makefile:50: lib-check] Error 2\n"),
                         ["lib-check", "papers-check: papers/ett"])

    def test_ledger_row_blocked_on_a_done_target_fails(self):
        # A copied ledger (T-ledger-stale-blockers): a row naming a done or dropped target as its
        # blocker fails; one naming an open target, or a done id inside a longer one, does not.
        import json
        import tempfile
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "papers", "p", "ledger"))
            rows = [{"label": "thm:a", "blocked_on": "T-old: the port (DEC-1)"},
                    {"label": "thm:b", "blocked_on": "T-open, after T-old-sfa"},
                    {"label": "thm:c", "blocked_on": "T-gone"}]
            json.dump({"statements": rows}, open(os.path.join(root, "papers", "p", "ledger", "ledger.json"), "w"))
            data = {"target": [target(id="T-old", status="done", commit="0" * 40), target(id="T-old-sfa"),
                               target(id="T-open", status="planned"), target(id="T-gone", status="dropped")]}
            e = rm.stale_blockers(data, root=root)
            self.assertEqual(len(e), 2, e)
            self.assertTrue(any("thm:a" in x and "T-old," in x for x in e), e)
            self.assertTrue(any("thm:c" in x and "dropped" in x for x in e), e)
            self.assertFalse(any("thm:b" in x for x in e), e)
        self.assertEqual(rm.stale_blockers(rm.load(), root=ROOT), [])


if __name__ == "__main__":
    unittest.main()
