#!/usr/bin/env python3
"""A paper whose ledger spans two Lean roots (T-arch-multiroot-ledgers, ARCHITECTURE.md §4.1).

A three-statement draft and two fake packages, built in a temporary directory, no Lean needed:

    pa/  (the primary [lean] root)   strict A/, scaffold S/
    pb/  (a [[lean.extra]] root)     strict S/, scaffold T/

The libraries are crossed on purpose: `S/` is pa's scaffold and pb's strict library, so a tool that
judged a file by the wrong root's libraries would call `pa/S/C.lean` strict or `pb/S/B.lean`
scaffold. Both roots are git repositories with commits of their own, so the per-root `git_commit`
is checked against each one's HEAD. The double DAG reads both roots' facts, and its one Lean edge
crosses the roots.
"""
import contextlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import doubledag as dd  # noqa: E402
import ledger  # noqa: E402

TEX = r"""\documentclass{article}
\begin{document}
\begin{theorem}\label{thm:a} A. \end{theorem}
\begin{proof} By Lemma~\ref{lem:b}. \end{proof}
\begin{lemma}\label{lem:b} B. \end{lemma}
\begin{proof} Trivial. \end{proof}
\begin{lemma}\label{lem:c} C. \end{lemma}
\end{document}
"""

PAPER = '''[paper]
root = "../legacy"
document = "p.tex"

[lean]
root = "../../pa"
strict = ["A"]
scaffold = ["S"]
scope = ["*"]
%s
[output]
render = false
'''

EXTRA = '''
[[lean.extra]]
root = "../../pb"
strict = ["S"]
scaffold = ["T"]
'''


def fact(uses=()):
    return {"kind": "theorem", "module": "M", "line": 1, "type": "True", "doc": "",
            "uses_value": list(uses), "uses_type": [], "axioms": [], "nonstandard_axioms": [],
            "uses_external": 0}


def git(path, *args):
    return subprocess.check_output(["git", "-C", path, "-c", "user.name=t", "-c", "user.email=t@t",
                                    "-c", "core.abbrev=7", *args], text=True).strip()


class TwoRoots(unittest.TestCase):

    def setUp(self):
        self.t = tempfile.mkdtemp()
        self.w("paper/legacy/p.tex", TEX)
        self.cfg = self.w("paper/ledger/ledger.toml", PAPER % EXTRA)
        self.w("pa/A/Main.lean", "/-! **`thm:a`** -/\nnamespace A\ntheorem main : True := trivial\nend A\n")
        self.w("pa/S/C.lean", "/-! **`lem:c`** -/\ntheorem c_pa : True := trivial\n")
        self.w("pb/S/B.lean", "/-! **`lem:b`** -/\nnamespace B\ntheorem main : True := trivial\nend B\n")
        self.w("pa/docs/lean-facts.json", json.dumps({"declarations": {
            "A.main": fact(["B.main"]), "c_pa": fact()}}))
        self.w("pb/docs/lean-facts.json", json.dumps({"declarations": {
            "B.main": fact(), "A.main": fact()}}))      # a duplicate: the primary's entry wins
        self.heads = []
        for r in ("pa", "pb"):
            p = os.path.join(self.t, r)
            git(p, "init", "-q")
            git(p, "add", "-A")
            git(p, "commit", "-qm", r)
            if r == "pb":                                  # two commits: distinct from pa's
                self.w("pb/T/README", "x")
                git(p, "add", "-A")
                git(p, "commit", "-qm", "second")
            self.heads.append(git(p, "rev-parse", "--short", "HEAD"))

    def tearDown(self):
        shutil.rmtree(self.t)

    def w(self, rel, text):
        p = os.path.join(self.t, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, "w", encoding="utf-8").write(text)
        return p

    def run_ledger(self, *cmd):
        with contextlib.redirect_stdout(io.StringIO()) as out:
            rc = ledger.main(["-c", self.cfg, *cmd])
        return rc, out.getvalue()

    def built(self):
        self.assertEqual(self.run_ledger("build")[0], 0)
        return json.load(open(os.path.join(self.t, "paper/ledger/ledger.json"), encoding="utf-8"))

    def test_files_found_in_both_roots_with_each_roots_libraries(self):
        rows = {s["label"]: s for s in self.built()["statements"]}
        self.assertEqual(rows["thm:a"]["lean_files"], ["A/Main.lean"])
        self.assertEqual(rows["lem:b"]["lean_files"], ["../pb/S/B.lean"])   # primary-relative
        self.assertEqual(rows["lem:c"]["lean_files"], ["S/C.lean"])
        self.assertEqual((rows["thm:a"]["lean_stated"], rows["thm:a"]["lean_proved"]), ("strict", "closed"))
        # pb's S/ is strict there; pa's S/ is scaffold here, whatever the other root says.
        self.assertEqual((rows["lem:b"]["lean_stated"], rows["lem:b"]["lean_proved"]), ("strict", "closed"))
        self.assertEqual((rows["lem:c"]["lean_stated"], rows["lem:c"]["lean_proved"]), ("scaffold", "none"))

    def test_git_commit_is_one_entry_per_root_in_order(self):
        lean = self.built()["lean"]
        self.assertEqual(lean["root"], os.path.join(self.t, "pa"))
        self.assertEqual(lean["git_commit"], self.heads[0])
        self.assertEqual([(r["root"], r["git_commit"]) for r in lean["roots"]],
                         [(os.path.join(self.t, "pa"), self.heads[0]),
                          (os.path.join(self.t, "pb"), self.heads[1])])
        self.assertNotEqual(self.heads[0], self.heads[1])
        self.assertEqual([(r["strict"], r["scaffold"]) for r in lean["roots"]],
                         [(["A"], ["S"]), (["S"], ["T"])])
        md = open(os.path.join(self.t, "paper/ledger/LEDGER.md"), encoding="utf-8").read()
        self.assertIn("`%s` at `%s`, `%s` at `%s`" % (os.path.join(self.t, "pa"), self.heads[0],
                                                      os.path.join(self.t, "pb"), self.heads[1]), md)
        self.assertIn("`A/` or `S/`, where `sorry` is a compile error", md)

    def test_single_root_has_no_roots_key(self):
        open(self.cfg, "w", encoding="utf-8").write(PAPER % "")
        led = self.built()
        self.assertEqual(set(led["lean"]), {"root", "git_commit"})
        rows = {s["label"]: s for s in led["statements"]}
        self.assertEqual(rows["lem:b"]["lean_files"], [])        # pb is no longer read
        self.assertEqual(rows["lem:c"]["lean_stated"], "scaffold")

    def curate(self, decls):
        p = os.path.join(self.t, "paper/ledger/ledger.json")
        led = json.load(open(p, encoding="utf-8"))
        for s in led["statements"]:
            s["decls"] = decls.get(s["label"], [])
        json.dump(led, open(p, "w", encoding="utf-8"), indent=2, ensure_ascii=False)
        self.assertEqual(self.run_ledger("build")[0], 0)   # curated decls survive the rebuild

    def test_check_resolves_decls_in_either_root(self):
        self.built()
        self.curate({"thm:a": ["A.main"], "lem:b": ["B.main"], "lem:c": ["c_pa"]})
        rc, out = self.run_ledger("check")
        self.assertEqual(rc, 0, out)

    def test_check_bites_on_a_decl_of_the_other_root(self):
        self.built()
        self.curate({"thm:a": ["A.main"], "lem:b": ["A.main"]})   # A.main is pa's, not in B.lean
        rc, out = self.run_ledger("check")
        self.assertNotEqual(rc, 0)
        self.assertIn("lem:b: declaration A.main not found in its listed files", out)

    def test_paper_level_keys_refused_in_an_extra_root(self):
        open(self.cfg, "w", encoding="utf-8").write(PAPER % (EXTRA + 'scope = ["*"]\n'))
        with contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(SystemExit) as e:
                ledger.main(["-c", self.cfg, "build"])
        self.assertEqual(e.exception.code, 2)

    def test_doubledag_reads_both_roots_facts(self):
        self.built()
        self.curate({"thm:a": ["A.main"], "lem:b": ["B.main"], "lem:c": ["c_pa"]})
        paper = os.path.join(self.t, "paper")
        _l, facts, _m = dd.paper_paths(paper)
        self.assertEqual(facts, os.path.join(self.t, "pa", "docs", "lean-facts.json"))  # unchanged
        fps = dd.facts_paths(paper)
        self.assertEqual(fps, [facts, os.path.join(self.t, "pb", "docs", "lean-facts.json")])
        rows, f = dd.load(os.path.join(paper, "ledger", "ledger.json"), fps)
        self.assertEqual(f["A.main"]["uses_value"], ["B.main"])     # first root wins
        g = dd.build(rows, f)
        self.assertEqual(g["summary"]["declarations_in_environment"], 3)
        edges = {(e["source"], e["target"]): e["kind"] for e in g["edges"]}
        self.assertEqual(edges.get(("thm:a", "lem:b")), "both")
        # With the primary's facts alone, the cross-root edge is lost: the extra root is load-bearing.
        g1 = dd.build(*dd.load(os.path.join(paper, "ledger", "ledger.json"), facts))
        self.assertNotEqual({(e["source"], e["target"]): e["kind"] for e in g1["edges"]}
                            .get(("thm:a", "lem:b")), "both")
        # The CLI reads them too, through --paper.
        out = os.path.join(self.t, "dd.json")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(dd.main(["build", "--paper", paper, "-o", out]), 0)
        self.assertEqual(json.load(open(out, encoding="utf-8")), json.loads(json.dumps(g)))


if __name__ == "__main__":
    unittest.main()
