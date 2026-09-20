#!/usr/bin/env python3
"""The reconciliation pass: what goes into the question, and what may come back out of it."""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOOLS = os.path.join(ROOT, "tools")
sys.path.insert(0, TOOLS)
import dag_reconcile as rc  # noqa: E402

FACTS = {
    "A.main": {"kind": "theorem", "module": "P.Alpha", "line": 1, "doc": "The assembly.",
               "type": "∀ x, P x", "uses_value": ["B.main"], "uses_type": [],
               "axioms": [], "nonstandard_axioms": [], "uses_external": 0},
    "B.main": {"kind": "theorem", "module": "P.Beta", "line": 2, "doc": "The lemma.",
               "type": "∀ y, Q y", "uses_value": [], "uses_type": [],
               "axioms": [], "nonstandard_axioms": [], "uses_external": 0},
}
ROWS = [
    {"label": "theo:alpha", "kind": "theorem", "number": "1", "title": "Alpha", "file": "p.tex",
     "line": 1, "tex_span": [1, 3], "proof": None, "proof_span": None, "deps": [],
     "decls": ["A.main"]},
    {"label": "lem:beta", "kind": "lemma", "number": "2", "title": "Beta", "file": "p.tex",
     "line": 5, "tex_span": [5, 7], "proof": None, "proof_span": None, "deps": [],
     "decls": ["B.main"]},
]
EDGE = {"source": "theo:alpha", "target": "lem:beta", "kind": "lean-only",
        "witness": ["A.main", "B.main"]}


class Prompt(unittest.TestCase):
    def setUp(self):
        self.tex = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.tex)
        with open(os.path.join(self.tex, "p.tex"), "w", encoding="utf-8") as fh:
            fh.write("\\begin{theorem}\\label{theo:alpha}\nAlpha holds.\n\\end{theorem}\n"
                     "\\begin{lemma}\\label{lem:beta}\nBeta holds.\n\\end{lemma}\n")

    def test_the_question_carries_both_statements_and_the_witness(self):
        p = rc.prompt_for(EDGE, ROWS, FACTS, self.tex)
        self.assertIn("Alpha holds.", p)
        self.assertIn("Beta holds.", p)
        self.assertIn("A.main", p)
        self.assertIn("B.main", p)
        self.assertIn("The assembly.", p, "a declaration's docstring is evidence")

    def test_the_question_offers_only_its_own_verdicts(self):
        p = rc.prompt_for(EDGE, ROWS, FACTS, self.tex)
        for v in rc.VERDICTS["lean-only"]:
            self.assertIn(v, p)
        for v in rc.VERDICTS["tex-only"]:
            self.assertNotIn(v, p)

    def test_a_missing_source_file_does_not_crash_the_question(self):
        p = rc.prompt_for(EDGE, ROWS, FACTS, "/nonexistent")
        self.assertIn("source not available", p)


class Validator(unittest.TestCase):
    def setUp(self):
        self.check = rc.validator("lean-only", ROWS, FACTS)

    def ok(self, **kw):
        a = {"verdict": "proof-detail", "confidence": "high", "why": "Because.", "action": "None."}
        a.update(kw)
        return a

    def test_a_good_answer_passes(self):
        self.assertIsNone(self.check(self.ok()))

    def test_a_verdict_from_the_other_kind_is_refused(self):
        self.assertIn("not one of", self.check(self.ok(verdict="decorative-reference")))

    def test_an_invented_declaration_is_refused(self):
        why = self.check(self.ok(why="It rests on `GFNBounds.Nonexistent.lemma`."))
        self.assertIn("neither a paper label nor a declaration", why)

    def test_an_invented_label_is_refused(self):
        self.assertIn("neither a paper label nor a declaration",
                      self.check(self.ok(why="See `theo:nowhere`.")))

    def test_a_real_declaration_is_accepted(self):
        self.assertIsNone(self.check(self.ok(why="It rests on `B.main`.")))

    def test_a_real_label_is_accepted(self):
        self.assertIsNone(self.check(self.ok(why="It rests on `lem:beta`.")))

    def test_a_real_module_file_is_accepted(self):
        """Naming the file a scope note lives in is legitimate, and was once refused."""
        self.assertIsNone(self.check(self.ok(why="Its scope note in `P/Beta.lean` says so.")))
        self.assertIsNone(self.check(self.ok(why="See `Beta.lean`.")))

    def test_an_empty_reason_is_refused(self):
        self.assertIn("no reason", self.check(self.ok(why="  ")))

    def test_an_answer_with_no_action_is_refused(self):
        self.assertIn("no action", self.check(self.ok(action="")))

    def test_a_rambling_reason_is_refused(self):
        self.assertIn("runs to", self.check(self.ok(why="word " * 200)))


class RealPair(unittest.TestCase):
    """The committed cassettes replay against the real GFN pair, when it is on this host.

    The draft lives outside this repository (`~/Dropbox/GFN Bounds`), so the test skips where it
    is absent rather than pretending to have checked something.
    """

    DRAFT = os.path.expanduser("~/Dropbox/GFN Bounds")
    LEDGER = os.path.join(DRAFT, "formalization-ledger.json")
    FACTS = os.path.join(ROOT, "lean", "docs", "lean-facts.json")
    DD = os.path.join(ROOT, "reports", "doubledag", "gfnbounds", "doubledag.json")

    @unittest.skipUnless(os.path.exists(LEDGER) and os.path.exists(FACTS) and os.path.exists(DD),
                         "the GFN Bounds draft or the Lean submodule is not on this host")
    def test_the_recorded_verdicts_replay_offline(self):
        env = dict(os.environ, LEANARTICLES_LLM="cassette", LEANARTICLES_LLM_CMD="false")
        tmp = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, tmp)
        out = os.path.join(tmp, "replay.json")
        r = subprocess.run(
            [sys.executable, os.path.join(TOOLS, "dag_reconcile.py"), "--dd", self.DD,
             "--ledger", self.LEDGER, "--facts", self.FACTS, "--tex-root", self.DRAFT,
             "--kind", "lean-only", "--limit", "6", "-o", out],
            capture_output=True, text=True, env=env)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        with open(out, encoding="utf-8") as fh:
            d = json.load(fh)
        self.assertEqual(len(d["proposals"]), 6)
        for p in d["proposals"]:
            self.assertIn(p["verdict"], rc.VERDICTS["lean-only"], p)
            self.assertTrue(p["witness"], "every lean-only edge carries its witness")


if __name__ == "__main__":
    unittest.main()
