#!/usr/bin/env python3
"""The coupled graph, on a hand-built pair whose right answer is known by eye.

Six declarations and four labels are enough to pin every claim the tool makes: what a principal
is, why a shared helper must not make an edge, that the witness is a shortest chain, and that a
body/full-form twin is a restatement rather than a dependency.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
import doubledag as dd  # noqa: E402


def decl(uses_value=(), uses_type=(), module="M", doc=""):
    return {"kind": "theorem", "module": module, "line": 1, "type": "True", "doc": doc,
            "uses_value": list(uses_value), "uses_type": list(uses_type),
            "axioms": [], "nonstandard_axioms": [], "uses_external": 0}


def row(label, deps=(), decls=(), **kw):
    r = {"label": label, "kind": "theorem", "title": label, "number": "", "file": "p.tex",
         "line": 1, "tex_span": [1, 2], "proof": None, "proof_span": None, "twin": None,
         "twin_of": None, "cites": [], "deps": list(deps), "nl_status": "proved",
         "lean_stated": "strict", "lean_proved": "closed", "decls": list(decls),
         "lean_files": [], "bucket": "A", "scope_notes": ""}
    r.update(kw)
    return r


class Principals(unittest.TestCase):
    """A.main uses A.step and the shared helper; the helper is listed under A and under B."""

    def setUp(self):
        self.facts = {
            "A.main": decl(uses_value=["A.step", "Shared"]),
            "A.step": decl(uses_value=["Shared"]),
            "B.main": decl(uses_value=["B.step"]),
            "B.step": decl(uses_value=["Shared"]),
            "Shared": decl(),
            "C.main": decl(),
        }
        self.rows = [row("a", decls=["A.main", "A.step", "Shared"]),
                     row("b", decls=["B.main", "B.step", "Shared"]),
                     row("c", decls=["C.main"])]

    def test_the_top_of_a_label_is_its_principal(self):
        g = dd.build(self.rows, self.facts)
        by = {n["label"]: n for n in g["nodes"]}
        self.assertEqual(by["a"]["principals"], ["A.main"])
        self.assertEqual(sorted(by["a"]["subordinates"]), ["A.step", "Shared"])
        self.assertEqual(by["b"]["principals"], ["B.main"])

    def test_a_shared_helper_makes_no_edge(self):
        """The whole point: `Shared` sits under both labels and is subordinate to both."""
        g = dd.build(self.rows, self.facts)
        self.assertEqual([e for e in g["edges"] if e["kind"] in ("both", "lean-only")], [])

    def test_the_flat_projection_invents_the_edge_the_principal_one_refuses(self):
        flat = dd.build(self.rows, self.facts, flat=True)
        pairs = {(e["source"], e["target"]) for e in flat["edges"] if e["kind"] == "lean-only"}
        self.assertIn(("a", "b"), pairs)
        self.assertIn(("b", "a"), pairs)

    def test_several_principals_when_nothing_assembles_them(self):
        rows = [row("a", decls=["A.main", "B.main"])]
        g = dd.build(rows, self.facts)
        self.assertEqual(sorted(g["nodes"][0]["principals"]), ["A.main", "B.main"])


class Edges(unittest.TestCase):
    """`a` really does rest on `b`: A.main -> A.step -> B.main, B.main being b's principal."""

    def setUp(self):
        self.facts = {
            "A.main": decl(uses_value=["A.step"]),
            "A.step": decl(uses_value=["B.main"]),
            "B.main": decl(uses_value=["B.step"]),
            "B.step": decl(),
            "C.main": decl(),
        }

    def test_lean_only_when_the_draft_is_silent(self):
        g = dd.build([row("a", decls=["A.main", "A.step"]), row("b", decls=["B.main", "B.step"])],
                     self.facts)
        e = [x for x in g["edges"] if x["source"] == "a"]
        self.assertEqual([(x["target"], x["kind"]) for x in e], [("b", "lean-only")])

    def test_both_when_the_draft_says_so(self):
        g = dd.build([row("a", deps=["b"], decls=["A.main", "A.step"]),
                      row("b", decls=["B.main", "B.step"])], self.facts)
        self.assertEqual([x["kind"] for x in g["edges"] if x["source"] == "a"], ["both"])

    def test_tex_only_when_the_proof_term_does_not_reach_it(self):
        g = dd.build([row("a", deps=["c"], decls=["A.main"]), row("c", decls=["C.main"])],
                     self.facts)
        self.assertEqual([x["kind"] for x in g["edges"] if x["source"] == "a"], ["tex-only"])

    def test_tex_only_unformalized_when_one_end_has_no_lean(self):
        g = dd.build([row("a", deps=["z"], decls=["A.main"]),
                      row("z", decls=[], lean_stated="none", lean_proved="none")], self.facts)
        self.assertEqual([x["kind"] for x in g["edges"] if x["source"] == "a"],
                         ["tex-only-unformalized"])

    def test_the_witness_is_a_shortest_chain(self):
        g = dd.build([row("a", decls=["A.main", "A.step"]), row("b", decls=["B.main", "B.step"])],
                     self.facts)
        e = [x for x in g["edges"] if x["source"] == "a"][0]
        self.assertEqual(e["witness"], ["A.main", "A.step", "B.main"])

    def test_the_witness_starts_at_a_principal_and_ends_at_one(self):
        g = dd.build([row("a", decls=["A.main", "A.step"]), row("b", decls=["B.main", "B.step"])],
                     self.facts)
        by = {n["label"]: n for n in g["nodes"]}
        w = [x for x in g["edges"] if x["source"] == "a"][0]["witness"]
        self.assertIn(w[0], by["a"]["principals"])
        self.assertIn(w[-1], by["b"]["principals"])


class Twins(unittest.TestCase):
    def test_a_twin_edge_is_a_restatement_not_a_disagreement(self):
        facts = {"F.main": decl()}
        rows = [row("body", deps=["full"], twin="full", decls=["F.main"]),
                row("full", twin_of="body", decls=["F.main"])]
        g = dd.build(rows, facts)
        self.assertEqual([e["kind"] for e in g["edges"] if e["source"] == "body"], ["twin"])
        self.assertEqual(g["summary"]["edges_tex_only"], 0)


class Robustness(unittest.TestCase):
    def test_a_cycle_in_the_environment_does_not_hang(self):
        facts = {"X": decl(uses_value=["Y"]), "Y": decl(uses_value=["X"]), "Z": decl()}
        g = dd.build([row("a", decls=["X"]), row("b", decls=["Z"])], facts)
        self.assertEqual(g["summary"]["labels"], 2)

    def test_declarations_absent_from_the_environment_are_counted_not_silently_dropped(self):
        facts = {"A.main": decl()}
        g = dd.build([row("a", decls=["A.main", "A.ghost"])], facts)
        self.assertEqual(g["summary"]["declarations_missing_from_environment"], 1)
        self.assertEqual(g["nodes"][0]["principals"], ["A.main"])

    def test_uses_type_counts_as_a_dependency(self):
        facts = {"A.main": decl(uses_type=["B.main"]), "B.main": decl()}
        g = dd.build([row("a", decls=["A.main"]), row("b", decls=["B.main"])], facts)
        self.assertEqual([e["kind"] for e in g["edges"]], ["lean-only"])


class Report(unittest.TestCase):
    def test_the_report_states_the_trade_rather_than_claiming_a_win(self):
        facts = {"A.main": decl(uses_value=["B.main"]), "B.main": decl()}
        rows = [row("a", decls=["A.main"]), row("b", decls=["B.main"])]
        g, flat = dd.build(rows, facts), dd.build(rows, facts, flat=True)
        text = dd.report(g, flat)
        self.assertIn("Read it as a trade, not a win", text)
        self.assertIn("The double DAG", text)

    def test_the_dot_carries_every_edge(self):
        facts = {"A.main": decl(uses_value=["B.main"]), "B.main": decl()}
        g = dd.build([row("a", decls=["A.main"]), row("b", decls=["B.main"])], facts)
        self.assertIn('"a" -> "b"', dd.to_dot(g))


if __name__ == "__main__":
    unittest.main()
