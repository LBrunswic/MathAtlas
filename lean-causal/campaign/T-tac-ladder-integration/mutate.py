"""Mutation checks of T-tac-ladder-integration: each guard of emit-lean's new code switched off in
a copy of tools/ladder.py, under a temporary root, and the emit tests of tests/test_programme.py run
against it. Every mutant must turn at least one test red.

    python3 -I lean-causal/campaign/T-tac-ladder-integration/mutate.py
"""
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
CLASSES = ["LadderEmit", "LadderEmitStanding", "LadderEmitFacts"]
MUTANTS = {
    "fact standing ignored": ('    return {"from": [], "to": f["property"], "standing": standing(f), "witness": f["witness"]}',
                              '    return {"from": [], "to": f["property"], "standing": [], "witness": f["witness"]}'),
    "fact standing dropped from examples": ("def instances(words):\n    \"\"\"The instance binders of the standing `words`, on the space M of Causal.Ladder.Test.\"\"\"\n    return",
                                            "def instances(words):\n    \"\"\"The instance binders of the standing `words`, on the space M of Causal.Ladder.Test.\"\"\"\n    return '' and"),
    "no word drops": ('            if len(words) < 2 or not all(x in form for x in src) or r["to"] not in form:',
                      '            if True or len(words) < 2 or not all(x in form for x in src) or r["to"] not in form:'),
    "no local bare drop": ('                    if words and (not src or b not in local_ids):',
                           '                    if False:'),
    "fact cycle ignored": ("                if cycle:\n                    in_test.append(item + (cycle,))",
                           "                if False:\n                    in_test.append(item + (cycle,))"),
    "edge cycle ignored": ("        elif cycle:\n            skipped.append((e, _cycle(w, mod, cycle)))",
                           "        elif False:\n            skipped.append((e, _cycle(w, mod, cycle)))"),
    "never forward": ("    if forward:\n        out.append(", "    if False:\n        out.append("),
    "any binder": ("    m = FACT_BINDER.match(explicit[0]) if len(explicit) == 1 else None",
                   "    m = __import__('re').match(r'(\\S*)', 'C')"),
    "dual always imported": ("    chain = import_chain(DUAL_MODULE, index[\"imports\"], RULES_MODULE)\n    if chain:",
                             "    chain = import_chain(DUAL_MODULE, index[\"imports\"], RULES_MODULE)\n    if False:"),
    "dual never imported": ("    if DUAL_MODULE not in index[\"imports\"]:\n        return False, None",
                            "    if True:\n        return False, None"),
    "shipped C.dual example dropped": ('    dual_pos = [((), f["property"], standing(f)) for f, *_ in facts if f["property"] in form]',
                                       '    dual_pos = []'),
}


def run(tmp):
    cmd = [sys.executable, "-B", "-m", "unittest"] + ["tests.test_programme." + c for c in CLASSES]
    p = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True,
                       env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    last = [x for x in p.stderr.splitlines() if x.startswith(("OK", "FAILED"))]
    return p.returncode, (last[-1] if last else p.stderr[-300:])


def main():
    src = open(os.path.join(ROOT, "tools", "ladder.py"), encoding="utf-8").read()
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        os.makedirs(os.path.join(tmp, "tools"))
        os.makedirs(os.path.join(tmp, "tests"))
        shutil.copy(os.path.join(ROOT, "tests", "test_programme.py"), os.path.join(tmp, "tests"))
        for x in ("binder.py", "lease.py", "fixtures"):
            os.symlink(os.path.join(ROOT, "tools", x), os.path.join(tmp, "tools", x))
        for x in ("programme", "lean-causal", "papers", "registers"):
            os.symlink(os.path.join(ROOT, x), os.path.join(tmp, x))
        target = os.path.join(tmp, "tools", "ladder.py")
        with open(target, "w", encoding="utf-8") as fh:
            fh.write(src)
        code, last = run(tmp)
        print("%-40s %s" % ("(unmutated)", last))
        bad += code != 0
        for name, (old, new) in MUTANTS.items():
            if src.count(old) != 1:
                print("%-40s MUTATION NOT APPLICABLE (%d matches)" % (name, src.count(old)))
                bad += 1
                continue
            with open(target, "w", encoding="utf-8") as fh:
                fh.write(src.replace(old, new))
            code, last = run(tmp)
            print("%-40s %s" % (name, last))
            bad += code == 0
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
