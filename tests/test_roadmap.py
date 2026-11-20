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

    def test_two_active_fail(self):
        self.assertTrue(self.errs(target(id="T-a", status="active"), target(id="T-b", status="active")))

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


if __name__ == "__main__":
    unittest.main()
