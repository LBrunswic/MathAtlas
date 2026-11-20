#!/usr/bin/env python3
"""No gate calls a model.

A gate decides whether the work is sound. A model is a proposal engine: it is allowed to be
wrong, and the author rules on what it says. If a model sat in `make check`, a green gate would
mean "a model was content", which is not a fact about the mathematics -- and the answer would
change from run to run, which is not a gate at all.

Two independent checks, because each can pass while the other fails: the gate scripts do not
reach `tools/llm.py` through any chain of imports, and the whole gate runs with every ask
refused.
"""
import ast
import os
import re
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOOLS = os.path.join(ROOT, "tools")


def gate_scripts():
    """Every `tools/*.py` the `check` target reaches, read out of the Makefile itself."""
    with open(os.path.join(ROOT, "Makefile"), encoding="utf-8") as fh:
        mk = fh.read()
    m = re.search(r"^check:([^\n]*)\n", mk, re.M)
    assert m, "the Makefile has no `check` target"
    targets = m.group(1).split()
    scripts, seen = set(), set()
    while targets:
        t = targets.pop()
        if t in seen:
            continue
        seen.add(t)
        body = re.search(r"^%s:([^\n]*)\n((?:[ \t\t].*\n|\n)*)" % re.escape(t), mk, re.M)
        if not body:
            continue
        targets += body.group(1).split()
        for s in re.findall(r"tools/(\w+)\.py", body.group(2)):
            scripts.add(s)
    return scripts


def imports_of(module):
    p = os.path.join(TOOLS, module + ".py")
    if not os.path.exists(p):
        return set()
    with open(p, encoding="utf-8") as fh:
        tree = ast.parse(fh.read())
    out = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            out |= {a.name.split(".")[0] for a in node.names}
        elif isinstance(node, ast.ImportFrom) and node.module and node.level == 0:
            out.add(node.module.split(".")[0])
    return out


class NoModelInGates(unittest.TestCase):
    def test_the_gates_are_the_ones_we_think(self):
        scripts = gate_scripts()
        self.assertIn("registers", scripts)
        self.assertIn("papers_check", scripts)
        self.assertGreater(len(scripts), 3, "the check target reaches almost nothing: parsed wrong?")

    def test_no_gate_reaches_the_model_backend(self):
        seen, stack = set(), list(gate_scripts())
        # papers_check invokes its per-paper gates as subprocesses, so follow those names too.
        stack += ["legacy_check", "ledger", "story_lint", "no_legacy_prose", "doubledag"]
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            deps = imports_of(m)
            self.assertNotIn("llm", deps,
                             "tools/%s.py is reached by `make check` and imports the model "
                             "backend" % m)
            stack += [d for d in deps if os.path.exists(os.path.join(TOOLS, d + ".py"))]

    def test_the_whole_gate_runs_with_every_ask_refused(self):
        env = dict(os.environ, LEANARTICLES_SKIP_LIB="1", LEANARTICLES_LLM="off", LEANARTICLES_LLM_CMD="false",
                   LEANARTICLES_IN_TESTS="1")
        r = subprocess.run(["make", "check"], cwd=ROOT, capture_output=True, text=True, env=env)
        self.assertEqual(r.returncode, 0,
                         "`make check` does not pass with the model backend switched off:\n"
                         + r.stdout[-3000:] + r.stderr[-2000:])


if __name__ == "__main__":
    unittest.main()
