#!/usr/bin/env python3
"""The mechanical rename tool (tools/rename_tool.py, ARCHITECTURE.md §4.2): the token rewriter's
rules, a rename round trip on the miniature hub of tools/fixtures/rename (apply, then the inverse
map, gives the tree back byte for byte), the resolution check failing on each dangling breakage,
the relative namespace the rewrite cannot carry (a manual item in the plan, a regression in
apply), the dry run writing nothing, and the refusal to apply on the live tree."""
import contextlib
import io
import os
import shutil
import sys
import tempfile
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
sys.path.insert(0, os.path.join(ROOT, "tools", "fixtures", "rename"))
import rename_tool as rt  # noqa: E402
import minihub  # noqa: E402

INVERSE = '[rename]\n"Alpha.Lorentz" = "Alpha.Flat"\n"AlphaScaffold.Lorentz" = "AlphaScaffold.Flat"\n'


def run(*argv):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = rt.main(list(argv))
    return rc, out.getvalue()


def snapshot(d):
    out = {}
    for dp, _dns, fns in os.walk(d):
        for f in fns:
            p = os.path.join(dp, f)
            with open(p, "rb") as fh:
                out[os.path.relpath(p, d)] = fh.read()
    return out


class Rewriter(unittest.TestCase):
    def setUp(self):
        self.m = rt.RenameMap({"Alpha": "Beta", "Alpha.Flat": "Gamma.Flat"}, {"Alpha": "Beta", "Alpha.Flat": "Gamma.Flat"})

    def line(self, s, ctx="body", prose=True):
        return rt.rewrite_line(s, self.m, ctx, set(), prose)[0]

    def test_longest_key_and_boundaries(self):
        self.assertEqual(self.line("Alpha.Flat.foo and Alpha.x and Alpha.Flatten"),
                         "Gamma.Flat.foo and Beta.x and Beta.Flatten")
        self.assertEqual(self.line("h.Alpha.x lean-Alpha.x AlphaX.y"), "h.Alpha.x lean-Alpha.x AlphaX.y")

    def test_a_bare_one_component_key_is_prose_except_on_a_command_line(self):
        self.assertEqual(self.line("Alpha theory."), "Alpha theory.")
        self.assertEqual(self.line("namespace Alpha\n", "command", False), "namespace Beta\n")
        self.assertEqual(self.line("import Alpha\n", "import", False), "import Beta\n")

    def test_root_prefix_paths_and_prose_suffixes(self):
        self.assertEqual(self.line("_root_.Alpha.Flat.x", prose=False), "_root_.Gamma.Flat.x")
        self.assertEqual(self.line("see Alpha/Flat/Basic.lean:3 and lean-a/Alpha/X.lean"),
                         "see Gamma/Flat/Basic.lean:3 and lean-a/Beta/X.lean")
        self.assertEqual(self.line("is it Alpha.Flat.foo? Alpha.Flat.foo's proof"),
                         "is it Gamma.Flat.foo? Gamma.Flat.foo's proof")

    def test_bad_maps_are_refused(self):
        with tempfile.TemporaryDirectory() as d:
            for text in ('[rename]\n"A" = "A"\n', '[other]\n"A" = "B"\n', '[rename]\n"A b" = "C"\n', ""):
                p = os.path.join(d, "m.toml")
                with open(p, "w") as f:
                    f.write(text)
                rc, out = run("plan", p, "--target", d)
                self.assertEqual(rc, 2, text)
                self.assertIn("bad map", out)


class RoundTrip(unittest.TestCase):
    def test_apply_then_inverse_gives_the_tree_back(self):
        with tempfile.TemporaryDirectory() as d:
            base, work = os.path.join(d, "base"), os.path.join(d, "work")
            minihub.build(base)
            shutil.copytree(base, work)
            rc, out = run("apply", os.path.join(base, "rename.toml"), "--target", work)
            self.assertEqual(rc, 0, out)
            self.assertIn("0 regression(s)", out)
            self.assertIn("-> OK", out)
            moved = os.path.join(work, "lean-alpha/Alpha/Lorentz/Basic.lean")
            self.assertTrue(os.path.isfile(moved))
            self.assertFalse(os.path.exists(os.path.join(work, "lean-alpha/Alpha/Flat")))
            self.assertTrue(os.path.isfile(os.path.join(work, "lean-alpha/scaffold/AlphaScaffold/Lorentz/Draft.lean")))
            with open(moved) as f:
                self.assertIn("namespace Alpha.Lorentz", f.read())
            for rel, want in (("papers/p/certificate/curation.toml", '"Alpha.Lorentz.foo"'),
                              ("papers/p/certificate/curation.toml", '"Alpha/Lorentz/Basic.lean"'),
                              ("programme/ladder.toml", '"Alpha.Lorentz.Bar"'),
                              ("roadmap/roadmap.toml", "Alpha.Lorentz.{foo,foo'}"),
                              ("lean-alpha/kb/entries/0001-flat.md", "Alpha theory, in prose"),
                              ("reports/atlas/lean/edges-p.json", "lean-alpha/Alpha/Lorentz/Basic.lean:11"),
                              ("reports/atlas/lean/facts-lean-alpha.json", '"module": "Alpha.Lorentz.Basic"')):
                with open(os.path.join(work, rel)) as f:
                    self.assertIn(want, f.read(), rel)
            self.assertEqual(run("check", "--target", work)[0], 0)
            inv = os.path.join(d, "inverse.toml")
            with open(inv, "w") as f:
                f.write(INVERSE)
            rc, out = run("apply", inv, "--target", work)
            self.assertEqual(rc, 0, out)
            self.assertEqual(snapshot(work), snapshot(base))

    def test_the_dry_run_writes_nothing(self):
        with tempfile.TemporaryDirectory() as d:
            minihub.build(d)
            before = snapshot(d)
            rc, out = run(os.path.join(d, "rename.toml"), "--target", d)   # no subcommand: plan
            self.assertEqual(rc, 0, out)
            self.assertIn("dry run: nothing is written", out)
            self.assertIn("moves: 2 module files", out)
            self.assertEqual(snapshot(d), before)


class Dangling(unittest.TestCase):
    def test_the_unbroken_hub_passes(self):
        with tempfile.TemporaryDirectory() as d:
            minihub.build(d)
            rc, out = run("check", "--target", d)
            self.assertEqual(rc, 0, out)
            self.assertIn("the compiled facts", out)

    def test_every_check_breakage_fails_with_dangling(self):
        names = {"dangling-decl": "Alpha.Flat.ghost", "dangling-path": "Alpha/Flat/Ghost.lean",
                 "dangling-import": "Alpha.Flat.Ghost"}
        for name, (rule, how, _) in minihub.BREAKAGES.items():
            if how != "check":
                continue
            with self.subTest(breakage=name), tempfile.TemporaryDirectory() as d:
                minihub.build(d, name)
                rc, out = run("check", "--target", d)
                self.assertEqual(rc, 1, out)
                self.assertRegex(out, r"(?m)^%s .* %s$" % (rule, names[name].replace(".", r"\.")))

    def test_grep_resolution_without_facts(self):
        with tempfile.TemporaryDirectory() as d:
            minihub.build(d, "dangling-decl")
            os.remove(os.path.join(d, "reports/atlas/lean/facts-lean-alpha.json"))
            rc, out = run("check", "--target", d)
            self.assertEqual(rc, 1, out)
            self.assertIn("a grep of the declarations in the .lean sources", out)
            self.assertIn("Alpha.Flat.ghost", out)
            self.assertNotIn("Alpha.Flat.foo\n", out)

    def test_a_relative_namespace_is_manual_in_the_plan_and_a_regression_in_apply(self):
        with tempfile.TemporaryDirectory() as d:
            minihub.build(d, "relative-namespace")
            rc, out = run("plan", os.path.join(d, "rename.toml"), "--target", d)
            self.assertIn("relative-namespace lean-alpha/Alpha/Flat/Extra.lean:5", out)
            rc, out = run("apply", os.path.join(d, "rename.toml"), "--target", d)
            self.assertEqual(rc, 1, out)
            self.assertRegex(out, r"(?m)^regression ladder decl programme/ladder.toml:\d+ Alpha\.Lorentz\.qux ")


class LiveTree(unittest.TestCase):
    def test_apply_refuses_the_hub_checkout_its_insides_and_its_ancestors(self):
        with tempfile.TemporaryDirectory() as d:
            minihub.build(d)
            m = os.path.join(d, "rename.toml")

            def must_not_plan(*_a, **_k):     # were the guard to fail, nothing may touch the live tree
                raise AssertionError("apply went past its guard on the live tree")

            real, rt.make_plan = rt.make_plan, must_not_plan
            try:
                for target in (ROOT, os.path.join(ROOT, "tools"), os.path.dirname(ROOT)):
                    with self.subTest(target=target):
                        rc, out = run("apply", m, "--target", target)
                        self.assertEqual(rc, 2, out)
                        self.assertIn("REFUSED", out)
            finally:
                rt.make_plan = real

    def test_apply_has_no_default_target(self):
        with tempfile.TemporaryDirectory() as d:
            minihub.build(d)
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as e:
                run("apply", os.path.join(d, "rename.toml"))
            self.assertEqual(e.exception.code, 2)

    def test_the_plan_names_the_live_tree(self):
        self.assertIsNotNone(rt.refusal(ROOT))
        with tempfile.TemporaryDirectory() as d:
            self.assertIsNone(rt.refusal(d))


if __name__ == "__main__":
    unittest.main()
