"""Rewrite every negative of a causal_ladder test file as a plain example (kb/0225's check).

    python3 -I negatives_plain.py IN OUT

Each `example HYPS : True := by` / `  fail_if_success have : G := by causal_ladder` / `  trivial`
(HYPS possibly continued on indented lines) becomes `example HYPS : G := by causal_ladder`; the
positives and the `run_cmd` guard are dropped. Run OUT with `lake env lean -DmaxErrors=100000`:
every error must be "failed to prove the goal after exhaustive search", none a limit.
Writes OUT, deterministic.
"""
import re
import sys

src = open(sys.argv[1], encoding="utf-8").read()
head = [l for l in src.split("\n")
        if l.startswith(("import ", "section", "universe ", "variable ", "open Causal"))]
neg = re.findall(r"^example ([^\n]*(?:\n    [^\n]*)*) : True := by\n"
                 r"  fail_if_success have : ([^\n]*) := by causal_ladder\n  trivial$", src, re.M)
body = ["example %s : %s := by causal_ladder" % (" ".join(h.split()), g) for h, g in neg]
with open(sys.argv[2], "w", encoding="utf-8") as fh:
    fh.write("\n".join(head + body + ["end"]) + "\n")
print(len(neg), "negatives;", src.count("fail_if_success"), "fail_if_success in", sys.argv[1])
