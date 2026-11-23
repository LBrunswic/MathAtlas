"""T-tac-curves-fact-rule: before the master's emit-lean, check that every module downstream of
Causal.Ladder.Rules that does not already see Causal.CurvesExtendSecondCountable still compiles
(warningAsError) once Rules imports it and carries curves_extend's fact rule. Each such module is
copied to OUT with two lines after its imports:

    import Causal.CurvesExtendSecondCountable
    attribute [local aesop safe apply (rule_sets := [CausalLadder])] Causal.Causality.curvesExtend_of_t1_secondCountable

and typechecked with `lake env lean -DwarningAsError=true`. Writes only under OUT.

    python3 -I simulate_rules_import.py OUT      (then: ls OUT/*.lean | xargs -P 6 -I{} lake env lean ...)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
ROOT = os.path.join(REPO, "lean-causal")
sys.path.insert(0, os.path.join(REPO, "tools"))
import ladder as ld  # noqa: E402

RULE = ("attribute [local aesop safe apply (rule_sets := [CausalLadder])] "
        "Causal.Causality.curvesExtend_of_t1_secondCountable")


def closure(imp, m):
    seen, st = set(), [m]
    while st:
        for n in imp.get(st.pop(), []):
            if n not in seen:
                seen.add(n)
                st.append(n)
    return seen


def main(out):
    imp = ld.lean_index()["imports"]
    cesc = closure(imp, "Causal.CurvesExtendSecondCountable") | {"Causal.CurvesExtendSecondCountable"}
    assert ld.RULES_MODULE not in cesc, "Causal.CurvesExtendSecondCountable reaches Rules: a cycle"
    mods = sorted(m for m in imp if ld.RULES_MODULE in closure(imp, m)
                  and not cesc <= (closure(imp, m) | {m}))
    os.makedirs(out, exist_ok=True)
    for m in mods:
        with open(os.path.join(ROOT, *m.split(".")) + ".lean", encoding="utf-8") as fh:
            lines = fh.read().split("\n")
        k = max(i for i, x in enumerate(lines[:60]) if x.startswith("import "))
        lines[k + 1:k + 1] = ["import Causal.CurvesExtendSecondCountable", "", RULE]
        with open(os.path.join(out, m + ".lean"), "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines))
    print("%d modules written to %s" % (len(mods), out))


if __name__ == "__main__":
    main(sys.argv[1])
