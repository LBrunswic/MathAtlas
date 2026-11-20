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
