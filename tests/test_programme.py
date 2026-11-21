#!/usr/bin/env python3
"""The ETT programme's tools: the ladder's rules, the binder's links, the leases' ownership.

Each rule is shown to fail on a hand-built input that breaks it, and the shipped files to pass.
"""
import os
import re
import subprocess
import sys
import tempfile
import tomllib
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

    def test_emit_only_checked_edges(self):
        # A seed edge is neither a rule nor a skipped line; a checked one whose witness the index
        # knows is a rule line (not merely a mention: the old form of this test passed on a
        # `-- skipped a_to_b ... not found` comment).
        out = ld.emit_lean(ladder5([edge(["a"], "b", "w_ab"),
                                    edge(["b"], "c", "w_bc", status="seed")]), index())
        self.assertIn(FWD + "w_ab\n", out)
        self.assertNotIn("w_bc", out)


CC, PC = "Causal.Causality.", "Causal.Precausality."
FWD = "attribute [aesop safe forward (rule_sets := [CausalLadder])] "


def cprop(i, lean=None, **kw):
    d = {"id": i, "lean": lean or CC + i.upper(), "what": i}
    d.update(kw)
    return d


def edge(frm, to, w, **kw):
    d = {"from": frm, "to": to, "witness": w, "status": "checked"}
    d.update(kw)
    return d


def index(**extra):
    """A hand-built lean_index: Causal.Base and Causal.Conj are ETT-layer, Causal.UsesModel
    reaches the model module Causal.Flat.Form through Causal.Mid."""
    decls = {CC + x: "Causal.Base" for x in "ABCDE"}
    decls.update({PC + "E": "Causal.Base", CC + "Two": "Causal.Base", CC + "Far": "Causal.UsesModel",
                  "w_ab": "Causal.Base", "w_bc": "Causal.Base", "w_conj": "Causal.Conj",
                  "w_model": "Causal.UsesModel", "w_geo": "Causal.Base"})
    sigs = {CC + x: ([], "Prop") for x in "ABCDE"}
    sigs.update({PC + "E": (["Q : Precausality M"], "Prop"),
                 CC + "Two": (["C : Causality M", "D : Causality N"], "Prop"),
                 CC + "Far": ([], "Prop")})
    ix = {"decls": decls, "sigs": sigs,
          "imports": {"Causal.Base": [], "Causal.Conj": ["Causal.Base"],
                      "Causal.UsesModel": ["Causal.Mid"], "Causal.Mid": ["Causal.Flat.Form"],
                      "Causal.Flat.Form": []}}
    for k, v in extra.items():
        ix[k].update(v)
    return ix


def ladder5(implies, **kw):
    d = {"property": [cprop(x) for x in "abcde"], "implies": implies}
    d.update(kw)
    return d


class LadderEmit(unittest.TestCase):
    """emit-lean: which checked edges become CausalLadder rules, and the tests written with them."""

    def test_emit_skips_every_edge_with_under(self):
        d = ladder5([edge(["a"], "b", "w_ab"),
                     edge(["b"], "c", "w_bc", under="M is T1 ([T1Space M])")])
        out = ld.emit_lean(d, index())
        self.assertIn(FWD + "w_ab\n", out)
        self.assertNotIn(FWD + "w_bc", out)
        self.assertIn("-- skipped w_bc (b ⇒ c): under: M is T1 ([T1Space M])", out)

    def test_emit_conjunction_is_one_forward_rule(self):
        out = ld.emit_lean(ladder5([edge(["a", "d"], "e", "w_conj")]), index())
        self.assertIn(FWD + "w_conj\n", out)
        self.assertIn("-- a ∧ d ⇒ e", out)
        self.assertNotIn("apply", out)

    def test_emit_imports_the_witness_modules_only(self):
        out = ld.emit_lean(ladder5([edge(["a", "d"], "e", "w_conj"),
                                    edge(["a"], "c", "w_model")]), index())
        imports = [x for x in out.splitlines() if x.startswith("import ")]
        self.assertEqual(imports, ["import Causal.Ladder.Basic", "import Causal.Conj"])

    def test_emit_skips_a_witness_whose_module_imports_a_model(self):
        out = ld.emit_lean(ladder5([edge(["a"], "c", "w_model")]), index())
        self.assertNotIn(FWD + "w_model", out)
        self.assertIn("-- skipped w_model (a ⇒ c): layer: w_model lives in Causal.UsesModel, which "
                      "imports a model (Causal.UsesModel → Causal.Mid → Causal.Flat.Form)", out)

    def test_model_layer(self):
        imp = {"Causal.X": ["Causal.MinkowskiMeasure"], "Causal.MinkowskiMeasure": ["Causal.Minkowski"]}
        for m in ("Causal.Minkowski", "Causal.Static", "Causal.SingularFlat", "Causal.Flat.Form",
                  "Causal.Model.Cone", "Causal.Port.GXBasic"):
            self.assertTrue(ld.is_model(m), m)
        for m in ("Causal.MinkowskiMeasure", "Causal.StaticX", "Causal.Flatness", "Causal.Properties"):
            self.assertFalse(ld.is_model(m), m)
        self.assertEqual(ld.model_path("Causal.X", imp),
                         ["Causal.X", "Causal.MinkowskiMeasure", "Causal.Minkowski"])
        self.assertIsNone(ld.model_path("Causal.Properties", imp))

    def test_emit_skips_geometry_sort_and_unlocated_witnesses(self):
        d = ladder5([edge(["a"], "b", "w_geo"), edge(["c"], "d", "nowhere")])
        d["property"][1]["sort"] = "geometry"
        out = ld.emit_lean(d, index())
        self.assertNotIn("attribute", out)
        self.assertIn("-- skipped w_geo (a ⇒ b): sort:", out)
        self.assertIn("-- skipped nowhere (c ⇒ d): not found:", out)

    def test_emit_ignores_seed_edges(self):
        out = ld.emit_lean(ladder5([edge(["a"], "b", "w_ab", status="seed")]), index())
        self.assertNotIn("w_ab", out)

    def examples(self, text):
        """{(premises, conclusion): 'derived' | 'not derived'} read off a generated Test.lean."""
        out, lines = {}, text.splitlines()
        for x, nxt in zip(lines, lines[1:]):
            if x.startswith("-- ") and nxt.startswith("example"):
                kind = "not derived" if "⇏" in x else "derived"
                lhs, rhs = x[3:].split(" ⇏ " if kind == "not derived" else " ⇒ ")
                out[(tuple(lhs.split(" ∧ ")), rhs.split(" (")[0])] = kind
        return out

    def test_emit_test_is_the_closure_of_the_emitted_edges(self):
        d = ladder5([edge(["a"], "b", "w_ab"), edge(["b"], "c", "w_bc", under="local push-up"),
                     edge(["a", "d"], "e", "w_conj")])
        text = ld.emit_test(d, index())
        ex = self.examples(text)
        derived = {k for k, v in ex.items() if v == "derived"}
        self.assertEqual(derived, {(("a",), "b"), (("a", "d"), "b"), (("a", "d"), "e")})
        self.assertEqual(ex[(("a",), "c")], "not derived")      # chained only through `under`
        self.assertEqual(ex[(("d",), "e")], "not derived")      # a conjunctive rule needs every premise
        self.assertEqual(len([k for k in ex if len(k[0]) == 1]), 5 * 4)
        self.assertIn("-- a ⇏ c (matrix: the matrix chains it through an edge not emitted)", text)
        self.assertIn("example (_h0 : Causal.Causality.A C) (_h1 : Causal.Causality.D C) : "
                      "Causal.Causality.E C := by causal_ladder", text)
        self.assertIn("  fail_if_success have : Causal.Causality.C C := by causal_ladder", text)
        self.assertIn("throwError", text)                         # the layer guard

    def test_emit_test_drops_each_premise_of_a_conjunction(self):
        ex = self.examples(ld.emit_test(ladder5([edge(["a", "c", "d"], "e", "w_conj")]), index()))
        self.assertEqual(ex[(("a", "c", "d"), "e")], "derived")
        for src in (("c", "d"), ("a", "d"), ("a", "c")):
            self.assertEqual(ex[(src, "e")], "not derived", src)

    def test_emit_test_fails_on_a_refuted_pair(self):
        d = ladder5([edge(["a"], "b", "w_ab")],
                    fails=[{"from": "a", "to": "c", "witness": "cex", "status": "checked"}])
        self.assertIn("-- a ⇏ c (matrix: refuted by a counterexample)", ld.emit_test(d, index()))

    def test_emit_test_writes_only_predicates_on_one_causality(self):
        d = {"property": [cprop("a"), cprop("e", PC + "E"), cprop("two", CC + "Two"),
                          cprop("far", CC + "Far"), cprop("g", CC + "B", sort="geometry")],
             "implies": [edge(["a"], "e", "w_ab")]}
        text = ld.emit_test(d, index())
        self.assertIn("Causal.Precausality.E C.toPrecausality := by causal_ladder", text)
        self.assertIn("-- no example for two: Causal.Causality.Two is not a predicate on one causality", text)
        self.assertIn("-- no example for far: Causal.Causality.Far lives in Causal.UsesModel", text)
        self.assertNotIn("for g:", text)                          # another sort: not a test subject
        self.assertNotIn("Causal.Causality.B", text)
        imports = [x for x in text.splitlines() if x.startswith("import ")]
        self.assertEqual(imports, ["import Causal.Ladder.Rules", "import Causal.Base"])

    def test_lean_index_reads_namespaces_imports_and_signatures(self):
        import tempfile
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "Causal", "Sub"))
            foo = os.path.join(root, "Causal", "Sub", "Foo.lean")
            bar = os.path.join(root, "Causal", "Bar.lean")
            with open(foo, "w") as fh:
                fh.write(
                    "import Causal.Bar\nimport Mathlib.Topology.Basic\n\n"
                    "/-! # Foo\ntheorem notADecl : True -/\n"
                    "namespace Causal\nnamespace Causality\nvariable (C : Causality M)\n"
                    "def Prop1 : Prop := True\n"
                    "-- theorem commented : True\n"
                    "@[simp, aesop safe (rule_sets := [X])] theorem Prop1.toTwo (h : C.Prop1) : True := trivial\n"
                    "section Inner\n"
                    "def Prop2 (D : Precausality M)\n    (U : Opens M) : Prop :=\n  True\n"
                    "end Inner\n"
                    "theorem _root_.rootThm : True := trivial\n"
                    "end Causality\n"
                    "def Causality.Prop3 {M : Type*} [TopologicalSpace M] (C : Causality M) : Prop := True\n"
                    "end Causal\n")
            with open(bar, "w") as fh:
                fh.write("namespace Causal.Bar\ndef baz : Nat := 0\nend Causal.Bar\n")
            ix = ld.lean_index(root)
        self.assertEqual(ix["imports"], {"Causal.Sub.Foo": ["Causal.Bar"], "Causal.Bar": []})
        self.assertEqual(ix["decls"], {"Causal.Causality.Prop1": "Causal.Sub.Foo",
                                       "Causal.Causality.Prop1.toTwo": "Causal.Sub.Foo",
                                       "Causal.Causality.Prop2": "Causal.Sub.Foo",
                                       "rootThm": "Causal.Sub.Foo",
                                       "Causal.Causality.Prop3": "Causal.Sub.Foo",
                                       "Causal.Bar.baz": "Causal.Bar"})
        self.assertEqual(ix["sigs"]["Causal.Causality.Prop1"], ([], "Prop"))
        self.assertEqual(ix["sigs"]["Causal.Causality.Prop2"], (["D : Precausality M", "U : Opens M"], "Prop"))
        self.assertEqual(ix["sigs"]["Causal.Causality.Prop3"], (["C : Causality M"], "Prop"))
        self.assertEqual(ix["sigs"]["Causal.Bar.baz"], ([], "Nat"))

    def test_shipped_index_resolves_the_ladder(self):
        ix, d = ld.lean_index(), ld.load()
        names = [p["lean"] for p in d["property"]] + [
            e["witness"] for k in ("implies", "fails", "consequence") for e in d.get(k, [])]
        self.assertEqual([n for n in names if n not in ix["decls"]], [])

    def test_shipped_rules_and_tests_are_generated(self):
        """Causal/Ladder/Rules.lean and Test.lean are emit-lean's output, never edited by hand:
        after a change to programme/ladder.toml, run `python3 tools/ladder.py emit-lean`."""
        ix, d = ld.lean_index(), ld.load()
        for path, text in ((ld.RULES, ld.emit_lean(d, ix)), (ld.TEST, ld.emit_test(d, ix))):
            with open(path, encoding="utf-8") as fh:
                self.assertEqual(fh.read(), text, "%s is stale or hand-edited: run "
                                 "python3 tools/ladder.py emit-lean" % os.path.relpath(path, ROOT))


LABELS = {"def:x"}


def chk(d, names=NAMES, labels=LABELS):
    return ld.check(d, names, labels)


def imp(frm, to, w="a_to_b", **kw):
    d = {"from": frm, "to": to, "witness": w, "status": "checked"}
    d.update(kw)
    return d


def has(errs, text):
    return any(text in e for e in errs)


class LadderStanding(unittest.TestCase):
    """`standing`: separation and countability hypotheses, read by the closure against the ambient
    (ETT's spacetimes: T2, second countable), and a counterexample read on its own space."""

    def test_standing_within_the_ambient_is_implied(self):
        d = lad(implies=[imp(["a"], "b", standing=["T1"])])
        self.assertEqual(chk(d), [])
        self.assertEqual(ld.matrix(d)[("a", "b")], "implied")      # T1 follows from the ambient T2

    def test_standing_beyond_the_ambient_is_implied_under_standing_only(self):
        d = lad(implies=[imp(["a"], "b", standing=["connected"])])
        self.assertEqual(chk(d), [])
        self.assertEqual(ld.matrix(d)[("a", "b")], "implied-standing")
        s = ld.summary(d)
        self.assertEqual((s["classified"], s["implied_standing"]), (0, 1))

    def test_declared_ambient(self):
        d = lad(implies=[imp(["a"], "b", standing=["T2"])], ambient={"standing": ["T1"]})
        self.assertEqual(chk(d), [])
        self.assertEqual(ld.matrix(d)[("a", "b")], "implied-standing")
        d["ambient"] = {"standing": ["metrizable"]}                # metrizable gives T2
        self.assertEqual(ld.matrix(d)[("a", "b")], "implied")
        d["ambient"] = {"standing": ["Hausdorff"]}
        self.assertTrue(has(chk(d), "ambient: unknown standing word 'Hausdorff'"))
        d["ambient"] = {"standing": ["T2"], "label": "def:y"}
        self.assertTrue(has(chk(d), "ambient: label def:y is not a label"))

    def test_legacy_under_is_chained_as_before(self):
        d = lad(implies=[imp(["a"], "b", under="M is T1 ([T1Space M])")])
        self.assertEqual(chk(d), [])
        self.assertEqual(ld.matrix(d)[("a", "b")], "implied")

    def test_unknown_standing_word_fails(self):
        self.assertTrue(has(chk(lad(implies=[imp(["a"], "b", standing=["Hausdorff"])])),
                            "unknown standing word 'Hausdorff'"))

    def test_standing_must_be_a_list(self):
        self.assertTrue(has(chk(lad(implies=[imp(["a"], "b", standing="T1")])), "standing must be a list"))

    def test_counterexample_is_read_on_its_space(self):
        # b ⇒ c on Hausdorff spaces. A counterexample with a and without c, one of ETT's spacetimes,
        # lacks b too; a non-Hausdorff one (space T1, a branching line) says nothing of b.
        imps = [imp(["b"], "c", "B.toC", standing=["T2"])]
        f = {"from": "a", "to": "c", "witness": "cex_a_not_c", "status": "checked"}
        self.assertEqual(ld.matrix(lad(implies=imps, fails=[f]))[("a", "b")], "fails")
        d = lad(implies=imps, fails=[dict(f, space=["T1"])])
        self.assertEqual(chk(d), [])
        self.assertEqual(ld.matrix(d)[("a", "b")], "unknown")
        self.assertEqual(ld.matrix(d)[("a", "c")], "fails-off")   # a T1 space is no ETT spacetime
        self.assertTrue(has(chk(lad(implies=imps, fails=[dict(f, space=["hausdorff"])])),
                            "unknown space word 'hausdorff'"))

    def test_a_counterexample_off_the_ambient_refutes_nothing_on_it(self):
        # T-tool-ladder-space: the vee (three points, T0 and not T1) is absolutely minimal, locally
        # push-up and not push-up, while absolutely_minimal ∧ locally_push_up ⇒ push_up holds on every
        # T1 space; it must not make a ⇏ c `fails` on ETT's spacetimes.
        imps = [imp(["a", "b"], "c", "B.toC", standing=["T1"])]
        vee = {"from": ["a", "b"], "to": "c", "witness": "cex_a_not_c", "status": "checked", "space": ["T0"]}
        d = lad(implies=imps, fails=[vee])
        self.assertEqual(chk(d), [])
        m = ld.matrix(d)
        self.assertEqual((m[("a", "c")], m[("b", "c")]), ("fails-off", "fails-off"))
        self.assertEqual(ld.off_spaces(d, "a", "c"), [("T0",)])
        s = ld.summary(d)
        self.assertEqual(s["fails_off"], 2)
        self.assertEqual(s["classified"], sum(1 for v in m.values() if v in ld.CLASSIFIED))
        self.assertNotIn(("a", "c"), ld.refuted(d))
        self.assertIn(("a", "c"), ld.refuted(d, off=True))
        # an [[open]] entry for a pair refuted only off the ambient stays legal
        self.assertEqual(chk(dict(d, open=[{"from": "a", "to": "c", "note": "x"}])), [])
        # the same counterexample with no space, or a space implying the ambient's words, is on it
        for sp in (None, ["T2", "second_countable"], ["metrizable", "second_countable"]):
            f = {k: v for k, v in vee.items() if k != "space"}
            if sp:
                f["space"] = sp
            e = lad(implies=[imp(["a", "b"], "c", "B.toC", standing=["connected"])], fails=[f])
            self.assertEqual(ld.matrix(e)[("a", "c")], "fails", sp)
            self.assertTrue(has(chk(dict(e, open=[{"from": "a", "to": "c", "note": "x"}])), "already settled"), sp)

    def test_a_counterexample_is_read_backwards_through_a_conjunctive_edge(self):
        # T-tool-ladder-py-2: a ∧ b ⇒ c; a counterexample with a and without c lacks b
        imps = [imp(["a", "b"], "c", "B.toC")]
        f = {"from": "a", "to": "c", "witness": "cex_a_not_c", "status": "checked"}
        d = lad(implies=imps, fails=[f])
        self.assertEqual(chk(d), [])
        self.assertEqual(ld.matrix(d)[("a", "b")], "fails")
        has_, lacks = ld.counterexample(d, f)
        self.assertEqual((has_, lacks & {"b", "c"}), ({"a"}, {"b", "c"}))
        # an [[open]] entry for the pair is now settled
        self.assertTrue(has(chk(dict(d, open=[{"from": "a", "to": "b", "note": "x"}])), "already settled"))
        # an edge invalid on the counterexample's space is not read backwards
        e = lad(implies=[imp(["a", "b"], "c", "B.toC", standing=["T2"])], fails=[dict(f, space=["T1"])])
        self.assertNotEqual(ld.matrix(e)[("a", "b")], "fails")

    def test_a_fact_holds_on_every_space_of_its_sort(self):
        # T-tool-ladder-py-2: a premise-free fact (every local model is rigid) classifies each pair
        # into it implied, and a counterexample lacking it is a contradiction
        fact = {"property": "c", "witness": "B.toC", "status": "checked"}
        d = lad(implies=[], fact=[fact])
        self.assertEqual(chk(d), [])
        m = ld.matrix(d)
        self.assertEqual((m[("a", "c")], m[("b", "c")], m[("c", "a")]), ("implied", "implied", "unknown"))
        f = {"from": "a", "to": "c", "witness": "cex_a_not_c", "status": "checked"}
        self.assertTrue(has(chk(dict(d, fails=[f])), "contradiction"))
        # a fact with standing beyond the ambient is implied under standing only
        e = lad(implies=[], fact=[dict(fact, standing=["connected"])])
        self.assertEqual(ld.matrix(e)[("a", "c")], "implied-standing")
        self.assertEqual(ld.needed_standing(("a",), "c", ld.edges_on(e, None) + ld.fact_edges(e, "a"),
                                            ld.ambient(e)), ["connected"])
        self.assertEqual(chk(dict(e, fails=[f])), [])            # not a contradiction on the ambient
        # schema
        self.assertTrue(has(chk(lad(fact=[dict(fact, property="zz")])), "unknown property 'zz'"))
        self.assertTrue(has(chk(lad(fact=[dict(fact, witness="nope")])), "witness not found"))
        self.assertTrue(has(chk(lad(fact=[dict(fact, status="maybe")])), "status must be one of"))
        self.assertTrue(has(chk(lad(fact=[dict(fact, sideways=1)])), "unknown key 'sideways'"))

    def test_a_contradiction_off_the_ambient_is_still_one(self):
        # check reads every counterexample on its own space, on the ambient or off it
        f = {"from": "a", "to": "b", "witness": "cex_a_not_c", "status": "checked", "space": ["T0"]}
        self.assertTrue(has(chk(lad(fails=[f])), "contradiction"))

    def test_contradiction_is_read_on_the_counterexample_space(self):
        imps = [imp(["a"], "c", standing=["T2"])]
        f = {"from": "a", "to": "c", "witness": "cex_a_not_c", "status": "checked"}
        self.assertTrue(has(chk(lad(implies=imps, fails=[f])), "contradiction"))
        self.assertEqual(chk(lad(implies=imps, fails=[dict(f, space=["T1"])])), [])

    def test_refuted_with_a_given_closure(self):
        # the reading of older callers (reports/blueprint/build.py): one closure for every counterexample
        d = lad(fails=[{"from": "a", "to": "c", "witness": "cex_a_not_c", "status": "checked"}])
        self.assertEqual(ld.refuted(d, ld.closure(d)), {("a", "c"), ("b", "c")})
        self.assertEqual(ld.refuted(d, ld.closure(d)), ld.refuted(d))

    def test_needed_standing_is_irredundant_and_closed(self):
        es = [imp(["a"], "b", standing=["T1"]), imp(["b"], "c", standing=["T2", "second_countable"])]
        self.assertEqual(ld.needed_standing(("a",), "b", es), ["T1"])
        self.assertEqual(ld.needed_standing(("a",), "c", es), ["T2", "second_countable"])
        self.assertEqual(ld.vocab_closure(["T2", "second_countable"]),
                         {"T0", "T1", "T2", "second_countable", "first_countable", "separable"})


class LadderNames(unittest.TestCase):
    """Lean names resolve namespace-exactly: a declared full name, not a dotted suffix."""

    def test_resolution_is_namespace_exact(self):
        full = "Causal.Causality.StronglyCausal.isCausal"
        self.assertTrue(ld.resolves(full, {full}))
        for n in ("StronglyCausal.isCausal", "isCausal", "Causal.Other.StronglyCausal.isCausal",
                  "X." + full):
            self.assertFalse(ld.resolves(n, {full}), n)
        self.assertFalse(ld.resolves(full, {"StronglyCausal.isCausal"}))   # the old suffix rule

    def test_check_refuses_suffix_names(self):
        d = lad(implies=[imp(["a"], "b", "Causal.a_to_b")])
        self.assertTrue(has(chk(d), "witness not found"))
        d = lad()
        d["property"][0]["lean"] = "a"                                        # P.a is declared
        self.assertTrue(has(chk(d), "Lean definition a not found"))

    def test_lean_names_are_full_names(self):
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "Causal"))
            with open(os.path.join(root, "Causal", "A.lean"), "w") as fh:
                fh.write("namespace Causal.Causality\n-- theorem commented : True\n"
                         "theorem StronglyCausal.isCausal : True := trivial\nend Causal.Causality\n")
            names = ld.lean_names(root)
        self.assertEqual(names, {"Causal.Causality.StronglyCausal.isCausal"})


class LadderSchema(unittest.TestCase):
    """Unknown keys and tables, conjunctive `at`, labels against papers/ett's ledger."""

    def test_unknown_key_fails(self):
        self.assertTrue(has(chk(lad(implies=[imp(["a"], "b", standnig=["T1"])])), "unknown key 'standnig'"))

    def test_unknown_table_fails(self):
        self.assertTrue(has(chk(lad(implication=[imp(["a"], "b")])), "unknown table 'implication'"))

    def test_a_table_of_the_wrong_shape_fails(self):
        self.assertTrue(has(chk({"property": prop("a")}), "property: must be an array of tables"))
        self.assertTrue(has(chk(lad(implies=["a"])), "implies: must be an array of tables"))

    def test_consequence_at_is_an_id_or_a_conjunction(self):
        c = {"statement": "s", "witness": "a_to_b", "status": "checked"}
        self.assertEqual(chk(lad(consequence=[dict(c, at="a")])), [])
        self.assertEqual(chk(lad(consequence=[dict(c, at=["a", "c"])])), [])
        self.assertTrue(has(chk(lad(consequence=[dict(c, at=["a", "zz"])])), "unknown property 'zz'"))
        self.assertTrue(has(chk(lad(consequence=[dict(c, at=[])])), "missing at"))
        self.assertTrue(has(chk(lad(consequence=[dict(c, at=[1])])), "at must be an id or a list"))
        self.assertTrue(has(chk(lad(consequence=[dict(c, at=["a", "a"])])), "repeated"))

    def test_label_is_an_ett_label(self):
        d = lad()
        d["property"][0]["label"] = "def:x"
        self.assertEqual(chk(d), [])
        d["property"][0]["label"] = "def:y"
        self.assertTrue(has(chk(d), "label def:y is not a label of papers/ett/ledger/ledger.json"))

    def test_label_without_the_ett_ledger_fails(self):
        d = lad()
        d["property"][0]["label"] = "def:x"
        saved, ld.ETT_LEDGER = ld.ETT_LEDGER, os.path.join(ROOT, "no-such-dir", "ledger.json")
        try:
            errs = ld.check(d, NAMES)
        finally:
            ld.ETT_LEDGER = saved
        self.assertTrue(has(errs, "cannot be checked: no ETT ledger"))


class LadderSorts(unittest.TestCase):
    """`sort` read by check and matrix: pairs within one sort are classified, the others ill-typed;
    `fails` with a list `from`."""

    def sorted5(self, **kw):
        d = {"property": [prop("a"), prop("b"), prop("c"), dict(prop("g"), sort="geometry"),
                          dict(prop("h"), sort="geometry")],
             "implies": [imp(["a"], "b")]}
        d.update(kw)
        return d

    def test_cross_sort_pairs_are_ill_typed_and_not_counted(self):
        d = self.sorted5(open=[{"from": "g", "to": "h", "note": "?"}])
        m = ld.matrix(d)
        self.assertEqual((m[("a", "g")], m[("g", "a")], m[("g", "h")]), ("ill-typed", "ill-typed", "open"))
        s = ld.summary(d)
        self.assertEqual((s["pairs"], s["within"], s["ill_typed"], s["classified"]), (20, 8, 12, 2))

    def test_entries_joining_two_sorts_fail(self):
        names = NAMES | {"P.g", "P.h"}
        cases = {"implies": imp(["a"], "g"),
                 "fails": {"from": "a", "to": "g", "witness": "cex_a_not_c", "status": "checked"},
                 "open": {"from": "a", "to": "g", "note": "?"},
                 "consequence": {"at": ["a", "g"], "statement": "s", "witness": "a_to_b", "status": "checked"}}
        self.assertEqual(chk(self.sorted5(), names), [])
        for kind, e in cases.items():
            d = self.sorted5()
            d.setdefault(kind, []).append(e)
            self.assertTrue(has(chk(d, names), "joins two sorts"), kind)

    def test_unknown_sort_fails(self):
        d = lad()
        d["property"][2]["sort"] = "spacetime"
        self.assertTrue(has(chk(d), "sort 'spacetime' is not one of"))

    def test_check_line_is_parseable(self):
        d = self.sorted5()
        line = ld.check_line(ld.summary(d))
        m = re.match(r"ladder: (\d+) properties, (\d+) implications, (\d+) counterexamples, (\d+) consequences; "
                     r"(\d+) of (\d+) ordered pairs classified \(within one sort\), (\d+) ill-typed \(across sorts\), "
                     r"(\d+) implied under standing only, (\d+) refuted off the ambient only, (\d+) transfers$", line)
        self.assertIsNotNone(m, line)
        self.assertEqual([int(x) for x in m.groups()], [5, 1, 0, 0, 1, 8, 12, 0, 0, 0])
        self.assertTrue(ld.check_line(ld.summary(d, ["x", "y"])).endswith("consequences; 2 violation(s)"))

    def five(self, **kw):
        d = {"property": [prop(x) for x in "abcde"], "implies": [imp(["a", "d"], "e")]}
        d.update(kw)
        return d

    def test_fails_with_a_list_from(self):
        f = {"from": ["a", "d"], "to": "c", "witness": "cex_a_not_c", "status": "checked"}
        d = self.five(fails=[f])
        self.assertEqual(chk(d, NAMES | {"P.d", "P.e"}), [])
        m = ld.matrix(d)
        for a in "ade":       # the counterexample has a and d, hence e, and lacks c
            self.assertEqual(m[(a, "c")], "fails", a)
        self.assertEqual(ld.matrix(self.five(fails=[dict(f, **{"from": "a"})]))[("e", "c")], "unknown")

    def test_fails_with_a_list_from_contradiction(self):
        d = self.five(fails=[{"from": ["a", "d"], "to": "e", "witness": "cex_a_not_c", "status": "checked"}])
        self.assertTrue(has(chk(d, NAMES | {"P.d", "P.e"}), "contradiction: counterexample cex_a_not_c has a ∧ d"))
        d = self.five(fails=[{"from": [], "to": "e", "witness": "cex_a_not_c", "status": "checked"}])
        self.assertTrue(has(chk(d, NAMES | {"P.d", "P.e"}), "empty premise"))


class LadderTransfer(unittest.TestCase):
    """[[transfer]]: what a nesting (sort pair) carries between the wider and the narrower causality."""
    NAMES = NAMES | {"P.n", "P.k", "w_tr", "cex_tr"}

    def tl(self, *transfers):
        return {"property": [prop("a"), prop("b"), prop("c"), dict(prop("n"), sort="pair"),
                             dict(prop("k"), sort="pair")],
                "implies": [imp(["a"], "b"), imp(["n"], "k", "B.toC")], "transfer": list(transfers)}

    def w(self, pair="k", prop_="a", **kw):
        d = {"pair": pair, "property": prop_, "witness": "w_tr", "status": "checked"}
        d.update(kw)
        return d

    def c(self, pair="n", prop_="a", **kw):
        d = {"pair": pair, "property": prop_, "counterexample": "cex_tr", "status": "checked"}
        d.update(kw)
        return d

    def errs(self, *transfers):
        return chk(self.tl(*transfers), self.NAMES)

    def test_good_transfers_pass(self):
        self.assertEqual(self.errs(self.w(), self.w(direction="to_wider", narrower=["c"]),
                                   self.c(prop_="c")), [])
        self.assertEqual(ld.summary(self.tl(self.w()))["transfers"], 1)

    def test_transfer_sorts(self):
        self.assertTrue(has(self.errs(self.w(pair="a")), "pair a is of sort causality, not pair"))
        self.assertTrue(has(self.errs(self.w(prop_="n")), "property n is of sort pair, not causality"))
        self.assertTrue(has(self.errs(self.w(narrower=["k"])), "narrower id k is of sort pair"))
        self.assertTrue(has(self.errs(self.w(wider=["zz"])), "unknown property 'zz'"))

    def test_transfer_needs_exactly_one_of_witness_and_counterexample(self):
        self.assertTrue(has(self.errs(self.w(counterexample="cex_tr")), "exactly one of witness"))
        bare = self.w()
        del bare["witness"]
        self.assertTrue(has(self.errs(bare), "exactly one of witness"))
        self.assertTrue(has(self.errs(self.w(witness="tr")), "witness not found"))

    def test_transfer_direction(self):
        self.assertTrue(has(self.errs(self.w(direction="down")), "direction must be one of"))

    def test_transfer_vacuous(self):
        self.assertTrue(has(self.errs(self.w(narrower=["a"])), "vacuous"))
        self.assertEqual(self.errs(self.w(wider=["c"])), [])

    def test_transfer_contradiction(self):
        # the counterexample is ≤-nested along n, hence along k (n ⇒ k): the proved transfer applies
        self.assertTrue(has(self.errs(self.w(), self.c()), "contradiction: transfer w_tr"))
        self.assertEqual(self.errs(self.w(pair="n"), self.c(pair="k")), [])        # k does not give n
        self.assertEqual(self.errs(self.w(narrower=["c"]), self.c()), [])         # the target lacks c
        self.assertTrue(has(self.errs(self.w(narrower=["c"]), self.c(narrower=["c"])), "contradiction"))
        self.assertEqual(self.errs(self.w(), self.c(direction="to_wider")), [])   # the other direction
        self.assertEqual(self.errs(self.w(standing=["T2"]), self.c(space=["T1"])), [])
        self.assertTrue(has(self.errs(self.w(standing=["T2"]), self.c()), "contradiction"))
        # T-tool-ladder-py-2: a transfer proved only under a condition in words is conditional, kept
        # out of the contradiction check (the counterexample need not meet the condition)
        self.assertEqual(self.errs(self.w(under="closed diamonds"), self.c()), [])

    def test_transfer_counterexample_whose_target_has_the_property(self):
        self.assertTrue(has(self.errs(self.c(prop_="b", narrower=["a"])), "its target has a, hence b"))

    def test_transfer_fields_of_the_other_kind(self):
        self.assertTrue(has(self.errs(self.w(space=["T1"])), "space is a counterexample's field"))
        self.assertTrue(has(self.errs(self.c(standing=["T1"])), "standing is a witness's field"))


class LadderEmitStanding(unittest.TestCase):
    """emit-lean: standing edges are rules whose tests carry the instances; an edge with a property
    without a Lean form is skipped."""

    def test_emit_skips_an_edge_with_a_formless_property(self):
        d = {"property": [cprop("a"), cprop("two", CC + "Two"), cprop("far", CC + "Far")],
             "implies": [edge(["a"], "two", "w_ab"), edge(["a"], "far", "w_bc")]}
        out = ld.emit_lean(d, index())
        self.assertNotIn("attribute", out)
        self.assertIn("-- skipped w_ab (a ⇒ two): no Lean form: two (Causal.Causality.Two is not a "
                      "predicate on one causality", out)
        self.assertIn("-- skipped w_bc (a ⇒ far): no Lean form: far (Causal.Causality.Far lives in "
                      "Causal.UsesModel, which imports a model)", out)

    def test_emit_standing_edge_is_a_rule(self):
        out = ld.emit_lean(ladder5([edge(["a"], "b", "w_ab", standing=["T1"])]), index())
        self.assertIn("-- a ⇒ b (standing: T1)\n" + FWD + "w_ab\n", out)

    def test_emit_skips_standing_with_under_and_unknown_words(self):
        out = ld.emit_lean(ladder5([edge(["a"], "b", "w_ab", standing=["T1"], under="local push-up"),
                                    edge(["b"], "c", "w_bc", standing=["Hausdorff"])]), index())
        self.assertNotIn("attribute", out)
        self.assertIn("-- skipped w_ab (a ⇒ b): under: local push-up", out)
        self.assertIn("-- skipped w_bc (b ⇒ c): standing: Hausdorff not in the vocabulary", out)

    def test_emit_test_carries_the_instances(self):
        d = ladder5([edge(["a"], "b", "w_ab", standing=["T1"]),
                     edge(["b"], "c", "w_bc", standing=["T2", "second_countable"]), edge(["c"], "d", "w_geo")])
        text = ld.emit_test(d, index())
        A, B, C_, D = ("Causal.Causality.%s C" % x for x in "ABCD")
        self.assertIn("-- a ⇒ b (standing: T1)\nexample [T1Space M] (_h0 : %s) : %s := by causal_ladder" % (A, B), text)
        self.assertIn("-- a ⇒ d (standing: T2, second_countable)\nexample [T2Space M] [SecondCountableTopology M] "
                      "(_h0 : %s) : %s := by causal_ladder" % (A, D), text)
        self.assertIn("-- c ⇒ d\nexample (_h0 : %s) : %s := by causal_ladder" % (C_, D), text)
        self.assertIn("-- a ⇏ b (standing dropped: T1)\nexample (_h0 : %s) : True := by\n"
                      "  fail_if_success have : %s := by causal_ladder" % (A, B), text)
        self.assertIn("-- b ⇏ d (standing dropped: T2, second_countable)", text)
        ex = LadderEmit.examples(None, text)
        self.assertEqual(ex[(("a",), "e")], "not derived")

    def test_emit_test_conjunction_with_standing(self):
        text = ld.emit_test(ladder5([edge(["a", "d"], "e", "w_conj", standing=["T1"])]), index())
        self.assertIn("-- a ∧ d ⇒ e (standing: T1)\nexample [T1Space M] (_h0 : Causal.Causality.A C) "
                      "(_h1 : Causal.Causality.D C) : Causal.Causality.E C := by causal_ladder", text)
        self.assertIn("-- d ⇏ e (a dropped from w_conj)\nexample [T1Space M] (_h0 : Causal.Causality.D C) : True", text)
        self.assertIn("-- a ∧ d ⇏ e (standing dropped: T1)\nexample (_h0 : Causal.Causality.A C) "
                      "(_h1 : Causal.Causality.D C) : True", text)


class LadderFixture(unittest.TestCase):
    """tools/fixtures/ladder: each breakage of the shipped ladder fails `check` with its violation."""
    DIR = os.path.join(ROOT, "tools", "fixtures", "ladder")

    def test_each_breakage_fails_with_its_violation(self):
        ns = {"__name__": "ladder_breakages"}
        path = os.path.join(self.DIR, "breakages.py")
        with open(path, encoding="utf-8") as fh:
            exec(compile(fh.read(), path, "exec"), ns)
        with open(ld.FILE, encoding="utf-8") as fh:
            text = fh.read()
        names, labels = ld.lean_names(), ld.ett_labels()
        self.assertEqual(ld.check(tomllib.loads(text), names, labels), [])
        self.assertGreaterEqual(len(ns["BREAKAGES"]), 20)
        for name, (want, _) in ns["BREAKAGES"].items():
            errs = ld.check(tomllib.loads(ns["broken"](text, name)), names, labels)
            self.assertTrue(has(errs, want), (name, want, errs))

    def test_run_sh_bites(self):
        r = subprocess.run(["bash", os.path.join(self.DIR, "run.sh")], capture_output=True, text=True,
                           env={**os.environ, "LEANARTICLES_HUB": ROOT})
        self.assertNotEqual(r.returncode, 0, r.stdout)
        self.assertIn("every breakage fails the check", r.stdout)


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

    def test_lean_names_resolve_namespace_exactly(self):
        for x in ("toC", "Causal.B.toC"):        # B.toC is declared: a suffix either way
            r = {"label": "thm:x", "ett": [x]}
            self.assertTrue(any("ett %s resolves to neither" % x in e for e in self.errs([r])), x)
        self.assertEqual(self.errs([{"label": "thm:x", "ett": ["B.toC"]}]), [])

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
