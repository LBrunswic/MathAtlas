"""T-tac-ladder-dual-key: the emitter of the dual rules, checked before any key is filled.

An IN-MEMORY copy of programme/ladder.toml gets the 23 keys of the table of the hand-written
Causal/Ladder/Dual.lean (:71-:94) and inextensible_nested's; nothing in the tree is written but the
scratch files of this directory.

    python3 -I keyed.py TOOLS report      check the keyed copy, compare with the hand-written files
    python3 -I keyed.py TOOLS variants    the other shapes (VARIANTS): DualKeyedVariants.lean, the
                                          generated rules and tests of the variant keys, one file
    python3 -I keyed.py TOOLS write       also write the scratch modules beside this script:
        DualKeyed.lean          emit_dual of the keyed copy, as emit-lean would write Causal/Ladder/Dual.lean
        DualKeyedTest.lean      one file: the edge rules of Rules.lean, the generated dual rules, the
                                generated DualTest examples and the hand-written examples of
                                Causal/Ladder/DualTest.lean, importing neither Causal.Ladder.Rules nor
                                the hand-written Causal.Ladder.Dual (the rules are the generated ones)
        DualKeyedExact.lean     the same rules; every single-literal pair across time reversal,
                                derived or not (the unknown ones included), and every same-side pair
                                that only the dual rules derive

TOOLS is the directory holding the ladder.py to test (tools/ of the repository once installed).
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(sys.argv[1]))
import ladder as ld  # noqa: E402

CC = "Causal.Causality."
KEYS = {
    "is_causal": CC + "dual_isCausal",
    "strongly_causal": CC + "dual_stronglyCausal",
    "strongly_causal_open": CC + "dual_stronglyCausalOpen",
    "globally_hyperbolic": CC + "dual_globallyHyperbolic",
    "causally_compact": CC + "dual_causallyCompact",
    "push_up": CC + "dual_pushUp",
    "causally_open": CC + "dual_causallyOpen",
    "absolutely_minimal": CC + "dual_absolutelyMinimal",
    "causally_arc_connected": CC + "dual_causallyArcConnectedOn",
    "causally_plain": CC + "dual_causallyPlain",
    "tarentin": CC + "dual_tarentin",
    "time_function": CC + "dual_hasTimeFunction",
    "curves_extend": CC + "CurvesExtend.dual",
    "locally_push_up": CC + "dual_locallyPushUp",
    "locally_causally_open": CC + "dual_locallyCausallyOpen",
    "chronal_neighbours": CC + "dual_chronalNeighbours",
    "has_chronal_neighbour": CC + "dual_hasChronalNeighbourEverywhere",
    "future_one_connected": CC + "dual_futureOneConnected",
    "locally_strongly_causal": CC + "dual_locallyStronglyCausal",
    "causally_open_future": {"introduces": "causally_open", "lemma": CC + "causallyOpen_iff"},
    "locally_causally_open_future": {"introduces": "locally_causally_open", "lemma": CC + "LocallyCausallyOpen"},
    "le_nested": CC + "dual_leNested_iff",
    "curve_nested": CC + "dual_curveNestedOn_iff",
    "inextensible_nested": CC + "dual_inextensibleNestedOn_iff",   # the 24th: no rule in Dual.lean
}
# The other shapes the library allows: the pair implications `R C C' W → R C.dual C'.dual W`, and
# causal openness introduced by its definition (`causallyOpen_iff` is `Iff.rfl`).
VARIANTS = dict(KEYS, curve_nested=CC + "CurveNestedOn.dual", inextensible_nested=CC + "InextensibleNestedOn.dual",
                causally_open_future={"introduces": "causally_open", "lemma": CC + "CausallyOpen"})
LADDER = os.path.join(ld.LEAN_ROOT, "Causal", "Ladder")


def keyed(keys=KEYS):
    data = ld.load()
    ids = {p["id"] for p in data["property"]}
    assert set(keys) <= ids, set(keys) - ids
    for p in data["property"]:
        if p["id"] in keys:
            p["dual"] = keys[p["id"]]
    return data


def variants():
    """The variant keys: check, emit, and one scratch file with the generated rules and tests."""
    data, ix = keyed(VARIANTS), ld.lean_index()
    errs = ld.check(data)
    rev, intro, faults = ld.dual_keys(data, ix)
    shapes = {r["id"]: r["shape"] for r in rev + intro if r["id"] in ("curve_nested", "inextensible_nested",
                                                                       "causally_open_future")}
    gtest = ld.emit_dual_test(data, ix)
    tests = gtest.split("\nopen Lean in\n", 1)[1].splitlines()
    with open(os.path.join(HERE, "DualKeyedVariants.lean"), "w", encoding="utf-8") as fh:
        fh.write(combined(data, ix, ["open Lean in"] + tests))
    print(json.dumps({"check": errs or "passes", "faults": faults, "shapes": shapes,
                      "examples": gtest.count("\nexample ")}, indent=1, ensure_ascii=False))


def attribute_rules(text):
    """{rule name (last component): 'forward' | 'pattern'} of the attribute lines of a Lean text."""
    out = {}
    for block in re.findall(r"attribute \[aesop safe forward (.*?)\(rule_sets := \[CausalLadder\]\)\]"
                            r"((?:[ \t]+[\w.']+|\n[ \t]+[\w.']+)+)", text):
        kind = "pattern" if "pattern :=" in block[0] else "forward"
        for n in block[1].split():
            out[n.rsplit(".", 1)[-1]] = kind
    return out


def theorems(text):
    return re.findall(r"^theorem ([\w.']+)", text, re.M)


def sections(text):
    """The examples of a DualTest text, by section title (generated sections only)."""
    out, cur = {}, None
    for line in text.splitlines():
        m = re.match(r"/-! ## (.*) -/$", line)
        if m:
            cur = m.group(1)
            out[cur] = []
        elif cur is not None and line.strip() and line not in ("end",):
            out[cur].append(line)
    return out


def body(text, start, stop=None):
    i = text.index(start)
    j = text.index(stop, i) + len(stop) if stop else len(text)
    return text[i:j]


def imports(text):
    return [l.split()[1] for l in text.splitlines() if l.startswith("import ")]


def combined(data, ix, tests):
    """One scratch file: Rules' edge rules, the generated dual rules, then `tests` (lines)."""
    rules, dual = ld.emit_lean(data, ix), ld.emit_dual(data, ix)
    hand = open(os.path.join(LADDER, "DualTest.lean"), encoding="utf-8").read()
    mods = []
    for t in (rules, dual, hand):
        for m in imports(t):
            if m not in (ld.RULES_MODULE, ld.DUAL_MODULE) and m not in mods:
                mods.append(m)
    for m in mods:                       # the hand-written rules must not come in transitively
        for bad in (ld.RULES_MODULE, ld.DUAL_MODULE):
            assert ld.import_chain(m, ix["imports"], bad) is None, (m, bad)
    rbody = rules.split("\n-/\n", 1)[1]
    dbody = body(dual, "namespace " + ld.DUAL_NAMESPACE, "end " + ld.DUAL_NAMESPACE)
    return "\n".join(["import %s" % m for m in mods] + [
        "", "-- scratch (T-tac-ladder-dual-key): the edge rules of Causal.Ladder.Rules (emit_lean), the dual",
        "-- rules emit_dual generates from the keyed copy of the ladder, and their tests; the hand-written",
        "-- Causal.Ladder.Dual is not imported, directly or transitively.", "", rbody, dbody, ""] + tests) + "\n"


def hand_examples():
    hand = open(os.path.join(LADDER, "DualTest.lean"), encoding="utf-8").read()
    return body(hand, "/-! ## More than one time reversal -/", None).split(
        "/-! ## Derived across time reversal, from one property -/")[0]


def exact_tests(data, ix):
    lits = ld.dual_lits(data, ix)
    forms, ids, two, one, edges = lits
    der, ref, unk = ld.dual_pairs(data, lits)
    out = ["section", "universe u", "variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M)", ""]

    def f(l):
        return forms[l[0]][l[1]]
    for a, b in der:
        out += ["example (_h0 : %s) : %s := by causal_ladder" % (f(a), f(b))]
    for a, b, w in ref + unk:
        out += ["-- %s %s ⇏ %s" % ("refuted" if w else "unknown", a, b),
                "example (_h0 : %s) : True := by" % f(a),
                "  fail_if_success have : %s := by causal_ladder" % f(b), "  trivial"]
    same = []
    for a in ids:
        base = ld._saturate((a,), edges)
        for s in (0, 1):
            clo = ld.dual_close({(a, s)}, edges, two, one)
            for b in ids:
                if b != a and (b, s) in clo and b not in base:
                    same.append(((a, s), (b, s)))
                    out += ["-- same side, through the dual rules only",
                            "example (_h0 : %s) : %s := by causal_ladder" % (f((a, s)), f((b, s)))]
    out += ["", "end"]
    return out, {"derived": len(der), "refuted": len(ref), "unknown": len(unk), "same_side_dual_only": len(same)}


def report(write=False):
    data, ix = keyed(), ld.lean_index()
    out = {}
    errs = ld.check(data)
    out["check_keyed"] = errs or "passes"
    out["check_line_keyed"] = ld.check_line(ld.summary(data, errs))
    rev, intro, faults = ld.dual_keys(data, ix)
    out["keys"] = {"reversals": len(rev), "introductions": len(intro), "faults": faults,
                   "shapes": {r["id"]: r["shape"] for r in rev + intro}}
    dual = ld.emit_dual(data, ix)
    hand = open(os.path.join(LADDER, "Dual.lean"), encoding="utf-8").read()
    gen_rules, hand_rules = attribute_rules(dual), attribute_rules(hand)
    out["rules"] = {"generated": len(gen_rules), "hand_written": len(hand_rules),
                    "same_name_and_kind": sorted(n for n in hand_rules if gen_rules.get(n) == hand_rules[n]),
                    "hand_written_only": sorted(set(hand_rules) - set(gen_rules)),
                    "generated_only": {n: gen_rules[n] for n in sorted(set(gen_rules) - set(hand_rules))},
                    "kind_differs": sorted(n for n in hand_rules if n in gen_rules and gen_rules[n] != hand_rules[n])}
    out["theorems"] = {"generated": len(theorems(dual)), "hand_written": len(theorems(hand)),
                       "hand_written_not_rules": sorted(set(theorems(hand)) - set(hand_rules))}
    gtest = ld.emit_dual_test(data, ix)
    htest = open(os.path.join(LADDER, "DualTest.lean"), encoding="utf-8").read()
    gs, hs = sections(gtest), sections(htest)
    out["dual_test"] = {"generated_examples": gtest.count("\nexample "),
                        "hand_written_examples": htest.count("\nexample ")}
    for title in ("Derived across time reversal, from one property",
                  "Derived on `C.dual` through a conjunctive rule, two-sided premises on `C`",
                  "Not derived across time reversal: refuted pairs"):
        out["dual_test"][title] = {"generated": sum(l.startswith("example") for l in gs.get(title, [])),
                                   "hand_written": sum(l.startswith("example") for l in hs.get(title, [])),
                                   "identical_lines": gs.get(title) == hs.get(title)}
    out["rules_lean_unchanged_by_keys"] = ld.emit_lean(data, ix) == open(ld.RULES, encoding="utf-8").read()
    out["test_lean_unchanged_by_keys"] = ld.emit_test(data, ix) == open(ld.TEST, encoding="utf-8").read()
    out["dual_generated_with_hand_written_in_tree"] = ld.dual_generated(data, ix)
    # once the hand-written Dual.lean is removed (the switch), Rules says so in its docstring only
    gone = dict(ix, imports={k: v for k, v in ix["imports"].items() if k not in (ld.DUAL_MODULE, ld.DUAL_TEST_MODULE)})
    after = ld.emit_lean(data, gone).splitlines()
    now = open(ld.RULES, encoding="utf-8").read().splitlines()
    out["rules_lean_after_switch_diff"] = [("-" + a, "+" + b) for a, b in zip(now, after) if a != b] + (
        ["length differs"] if len(now) != len(after) else [])
    if write:
        with open(os.path.join(HERE, "DualKeyed.lean"), "w", encoding="utf-8") as fh:
            fh.write(dual)
        with open(os.path.join(HERE, "DualKeyedDualTest.lean"), "w", encoding="utf-8") as fh:
            fh.write(gtest)
        tests = gtest.split("\nopen Lean in\n", 1)[1].splitlines()
        tests = ["open Lean in"] + tests[:-1] + ["", "section", "open Causal Causal.Causality", "",
                                                 "-- the hand-written examples of Causal/Ladder/DualTest.lean",
                                                 hand_examples(), "end", "", "end"]
        with open(os.path.join(HERE, "DualKeyedTest.lean"), "w", encoding="utf-8") as fh:
            fh.write(combined(data, ix, tests))
        ex, counts = exact_tests(data, ix)
        out["exact"] = counts
        with open(os.path.join(HERE, "DualKeyedExact.lean"), "w", encoding="utf-8") as fh:
            fh.write(combined(data, ix, ex))
    print(json.dumps(out, indent=1, ensure_ascii=False, default=sorted))


if __name__ == "__main__":
    if sys.argv[2:] == ["variants"]:
        variants()
    else:
        report(write=sys.argv[2:] == ["write"])
