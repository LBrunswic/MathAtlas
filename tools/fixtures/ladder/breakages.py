#!/usr/bin/env python3
"""Breakages of a copy of programme/ladder.toml: one per rule `tools/ladder.py check` gained with
T-tool-ladder-py (and its successors: the `dual` key's, T-tac-ladder-dual-key). Each must make the
check fail, with the violation named here.

    python3 breakages.py --list                 the breakage names, one per line
    python3 breakages.py LADDER NAME OUT        write LADDER broken by NAME to OUT

A breakage APPENDS entries to the ladder (TOML lets an array of tables continue anywhere), built
from the ids and witnesses the ladder already has, so that the keeper's edits do not stale it.
tests/test_programme.py imports BREAKAGES and checks each in-process; run.sh drives the CLI.
"""
import os
import sys
import tomllib


def _q(x):
    return '"%s"' % x


def ids(x):
    return x if isinstance(x, list) else [x]


def _lst(xs):
    return "[%s]" % ", ".join(_q(x) for x in xs)


def picks(data):
    """The ids and witnesses a breakage is built from; an AssertionError if the ladder lacks one."""
    props = data["property"]
    cau = [p["id"] for p in props if p.get("sort", "causality") == "causality"]
    pair = [p["id"] for p in props if p.get("sort") == "pair"]
    edge = next(e for e in data["implies"] if e.get("status") == "checked")
    conj = next(e for e in data["implies"] if isinstance(e.get("from"), list) and len(e["from"]) > 1)
    cons = next(e for e in data["consequence"] if "." in e["witness"])
    fail = data["fails"][0]
    bare = next(e for e in data["implies"] if e.get("status") == "checked" and not e.get("standing"))
    fact = data["fact"][0]
    srt = {q["id"]: q.get("sort", "causality") for q in props}
    other = next(q["id"] for q in props if srt[q["id"]] == srt[fact["property"]] and q["id"] != fact["property"])
    assert len(cau) >= 2 and pair, "the ladder needs two causality-sort properties and one pair-sort one"
    return {"c1": cau[0], "c2": cau[1], "pair": pair[0], "edge": edge, "conj": conj, "cons": cons,
            "fail": fail, "bare": bare, "fact": fact, "fact_other": other, "lean": props[0]["lean"],
            "props": props, "pair_lean": next(q["lean"] for q in props if q.get("sort") == "pair")}


def _implies(e, extra=""):
    return "\n[[implies]]\nfrom = %s\nto = %s\nwitness = %s\nstatus = \"checked\"\n%s" % (
        _lst(e["from"] if isinstance(e["from"], list) else [e["from"]]), _q(e["to"]), _q(e["witness"]), extra)


def _consequence(at, witness, extra=""):
    return "\n[[consequence]]\nat = %s\nstatement = \"fixture\"\nwitness = %s\nstatus = \"checked\"\n%s" % (
        at, _q(witness), extra)


# name -> (a substring of the violation it must cause, data -> the TOML text appended)
BREAKAGES = {
    "standing-word": ("unknown standing word 'Hausdorff'",
                      lambda p: _implies(p["edge"], 'standing = ["Hausdorff"]\n')),
    "standing-word-r1": ("unknown standing word 'R_1'",
                         lambda p: _implies(p["edge"], 'standing = ["R_1"]\n')),
    "standing-not-a-list": ("standing must be a list of words",
                            lambda p: _implies(p["edge"], 'standing = "T1"\n')),
    "unknown-key": ("unknown key 'standnig'",
                    lambda p: _implies(p["edge"], 'standnig = ["T1"]\n')),
    "unknown-table": ("unknown table 'implication'",
                      lambda p: "\n[[implication]]\nfrom = [%s]\nto = %s\n" % (_q(p["c1"]), _q(p["c2"]))),
    "suffix-name": ("witness not found in lean-causal (a full name)",
                    lambda p: _consequence(_q(p["cons"]["at"] if isinstance(p["cons"]["at"], str) else p["cons"]["at"][0]),
                                           p["cons"]["witness"].rsplit(".", 1)[1])),
    "at-unknown": ("unknown property 'no_such_property'",
                   lambda p: _consequence(_lst([p["c1"], "no_such_property"]), p["cons"]["witness"])),
    "at-empty": ("missing at", lambda p: _consequence("[]", p["cons"]["witness"])),
    "at-two-sorts": ("joins two sorts", lambda p: _consequence(_lst([p["c1"], p["pair"]]), p["cons"]["witness"])),
    "label": ("label def:no_such_label is not a label of papers/ett/ledger/ledger.json",
              lambda p: "\n[[property]]\nid = \"zz_fixture\"\nlean = %s\nlabel = \"def:no_such_label\"\nwhat = \"x\"\n"
              % _q(p["lean"])),
    "sort-unknown": ("sort 'spacetime' is not one of",
                     lambda p: "\n[[property]]\nid = \"zz_fixture\"\nlean = %s\nsort = \"spacetime\"\nwhat = \"x\"\n"
                     % _q(p["lean"])),
    "implies-two-sorts": ("joins two sorts",
                          lambda p: _implies({"from": [p["c1"]], "to": p["pair"], "witness": p["edge"]["witness"]})),
    "open-two-sorts": ("joins two sorts",
                       lambda p: "\n[[open]]\nfrom = %s\nto = %s\nnote = \"x\"\n" % (_q(p["c1"]), _q(p["pair"]))),
    "fails-list-contradiction": ("contradiction: counterexample",
                                 lambda p: "\n[[fails]]\nfrom = %s\nto = %s\nwitness = %s\nstatus = \"checked\"\n" % (
                                     _lst(p["conj"]["from"]), _q(p["conj"]["to"]), _q(p["fail"]["witness"]))),
    # T-tool-ladder-space: a counterexample OFF the ambient (space T0) refutes nothing on ETT's
    # spacetimes, but check still reads it on its own space: one that has its `to` by an edge valid
    # on every space is a contradiction.
    "fails-off-contradiction": ("contradiction: counterexample",
                                lambda p: "\n[[fails]]\nfrom = %s\nto = %s\nwitness = %s\nstatus = \"checked\"\n"
                                "space = [\"T0\"]\n" % (_lst(ids(p["bare"]["from"])), _q(p["bare"]["to"]),
                                                          _q(p["fail"]["witness"]))),
    # T-tool-ladder-py-2: a [[fact]] is had by every space of its sort, so a counterexample lacking it
    # is a contradiction; a fact names a property. (The backward reading of conjunctive edges adds no
    # contradiction the forward one misses, so it has no breakage: tests/test_programme.py checks
    # what it classifies.)
    "fact-contradiction": ("contradiction: counterexample",
                           lambda p: "\n[[fails]]\nfrom = %s\nto = %s\nwitness = %s\nstatus = \"checked\"\n" % (
                               _lst([p["fact_other"]]), _q(p["fact"]["property"]), _q(p["fail"]["witness"]))),
    "fact-unknown-property": ("unknown property 'no_such_property'",
                              lambda p: "\n[[fact]]\nproperty = \"no_such_property\"\nwitness = %s\n"
                              "status = \"checked\"\n" % _q(p["fact"]["witness"])),
    "fails-space-word": ("unknown space word 'hausdorff'",
                         lambda p: "\n[[fails]]\nfrom = %s\nto = %s\nwitness = %s\nstatus = \"checked\"\n"
                         "space = [\"hausdorff\"]\n" % (_q(p["fail"]["from"]) if isinstance(p["fail"]["from"], str)
                                                       else _lst(p["fail"]["from"]), _q(p["fail"]["to"]),
                                                       _q(p["fail"]["witness"]))),
    "transfer-sorts": ("is of sort causality, not pair",
                       lambda p: "\n[[transfer]]\npair = %s\nproperty = %s\nwitness = %s\nstatus = \"checked\"\n" % (
                           _q(p["c1"]), _q(p["c2"]), _q(p["edge"]["witness"]))),
    "transfer-witness-and-counterexample": (
        "exactly one of witness",
        lambda p: "\n[[transfer]]\npair = %s\nproperty = %s\nwitness = %s\ncounterexample = %s\nstatus = \"checked\"\n" % (
            _q(p["pair"]), _q(p["c1"]), _q(p["edge"]["witness"]), _q(p["fail"]["witness"]))),
    "ambient-word": ("ambient: unknown standing word 'Hausdorff'",
                     lambda p: '\n[ambient]\nstanding = ["Hausdorff"]\n'),
    "transfer-direction": ("direction must be one of",
                           lambda p: "\n[[transfer]]\npair = %s\nproperty = %s\ndirection = \"down\"\nwitness = %s\n"
                           "status = \"checked\"\n" % (_q(p["pair"]), _q(p["c1"]), _q(p["edge"]["witness"]))),
    "transfer-vacuous": ("vacuous",
                         lambda p: "\n[[transfer]]\npair = %s\nproperty = %s\nnarrower = [%s]\nwitness = %s\n"
                         "status = \"checked\"\n" % (_q(p["pair"]), _q(p["c1"]), _q(p["c1"]), _q(p["edge"]["witness"]))),
    # T-tool-ladder-edge-hypotheses: an edge hypothesis's Lean name resolves, and its id is no property id.
    "edge-hypothesis-lean": ("Lean definition Causal.no_such_edge_hypothesis not found",
                             lambda p: "\n[[edge_hypothesis]]\nid = \"eh_fixture\"\nlean = \"Causal.no_such_edge_hypothesis\"\n"
                                       "what = \"fixture\"\n"),
    "edge-hypothesis-id-clash": ("id is a [[property]] id",
                                 lambda p: "\n[[edge_hypothesis]]\nid = %s\nlean = %s\nwhat = \"fixture\"\n" % (
                                     _q(p["c1"]), _q(p["lean"]))),
    "transfer-contradiction": (
        "contradiction: transfer",
        lambda p: ("\n[[transfer]]\npair = %s\nproperty = %s\nwitness = %s\nstatus = \"checked\"\n"
                   "\n[[transfer]]\npair = %s\nproperty = %s\ncounterexample = %s\nstatus = \"checked\"\n") % (
            _q(p["pair"]), _q(p["c1"]), _q(p["edge"]["witness"]), _q(p["pair"]), _q(p["c1"]), _q(p["fail"]["witness"]))),
}


# T-tac-ladder-dual-key: the `dual` key. A breakage cannot add a key to a node of the ladder (TOML
# closes a table once the next one starts), so it appends fixture nodes `zz_*` carrying the keys.
# The library lemmas they name are those of the hand-written Causal/Ladder/Dual.lean (DUAL_LIB);
# the lemmas a key may not name are found in the Lean index (lean_index), so that a move in the
# library does not stale them.
DUAL_LIB = {"two": "Causal.Causality.CausallyOpen", "one": "Causal.Causality.CausallyOpenFuture",
            "two_key": "Causal.Causality.dual_causallyOpen", "intro": "Causal.Causality.causallyOpen_iff",
            "edge": "Causal.Causality.CausallyOpen.future"}


def _ladder_module():
    try:
        import ladder
    except ImportError:
        sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")))
        import ladder
    return ladder


def _index_pick(kind):
    """A theorem of lean-causal stated as a time-reversal iff whose module imports a model
    (kind 'model') or Causal.Ladder.Rules (kind 'rules'); any theorem there if none is an iff."""
    ld = _ladder_module()
    ix = ld.lean_index()

    def bad(n):
        m = ix["decls"][n]
        if kind == "model":
            return ld.model_path(m, ix["imports"]) is not None
        chain = ld.import_chain(m, ix["imports"], ld.RULES_MODULE)
        return chain is not None and len(chain) > 1 and ld.model_path(m, ix["imports"]) is None
    names = sorted(n for n in ix["tsigs"] if bad(n))
    assert names, "no theorem of lean-causal in a module importing %s" % kind
    iffs = [n for n in names if not ix["tsigs"][n][0] and "dual" in (ix["tsigs"][n][1] or "") and "↔" in ix["tsigs"][n][1]]
    return (iffs or names)[0]


def _node(i, lean, dual, sort=None):
    key = _q(dual) if isinstance(dual, str) else "{ %s }" % ", ".join("%s = %s" % (k, _q(v)) for k, v in dual.items())
    return "\n[[property]]\nid = %s\nlean = %s\nwhat = \"fixture\"\n%sdual = %s\n" % (
        _q(i), _q(lean), "sort = %s\n" % _q(sort) if sort else "", key)


def _geo(p):
    return next(q["lean"] for q in p["props"] if q.get("sort") == "geometry")


DUAL_BREAKAGES = {
    # the four of the target's acceptance
    "dual-not-found": ("dual: lemma 'Causal.Causality.no_such_dual' not found in lean-causal (a full name)",
                       lambda p: _node("zz_fixture", DUAL_LIB["two"], "Causal.Causality.no_such_dual")),
    "dual-geometry": ("dual: a geometry node has no time reversal",
                      lambda p: _node("zz_fixture", _geo(p), DUAL_LIB["two_key"], sort="geometry")),
    "dual-introduces-one-sided": (
        "dual: introduces zz_one, a one-sided node (its own key is an introduction)",
        lambda p: (_node("zz_two", DUAL_LIB["two"], DUAL_LIB["two_key"])
                   + _node("zz_one", DUAL_LIB["one"], {"introduces": "zz_two", "lemma": DUAL_LIB["intro"]})
                   + _node("zz_bad", DUAL_LIB["one"], {"introduces": "zz_one", "lemma": DUAL_LIB["intro"]}))),
    "dual-imports-rules": ("which imports Causal.Ladder.Rules",
                           lambda p: _node("zz_fixture", DUAL_LIB["two"], _index_pick("rules"))),
    # the other checks of the key
    "dual-model-layer": ("which imports a model", lambda p: _node("zz_fixture", DUAL_LIB["two"], _index_pick("model"))),
    "dual-shape": ("is neither `C.dual.P ↔ C.P` nor `C.P → C.dual.P`",
                   lambda p: _node("zz_fixture", DUAL_LIB["two"], DUAL_LIB["edge"])),
    "dual-introduces-keyless": (
        "dual: introduces zz_two, which carries no two-sided dual key",
        lambda p: ("\n[[property]]\nid = \"zz_two\"\nlean = %s\nwhat = \"fixture\"\n" % _q(DUAL_LIB["two"])
                   + _node("zz_one", DUAL_LIB["one"], {"introduces": "zz_two", "lemma": DUAL_LIB["intro"]}))),
    "dual-pair-introduction": ("dual: an introduction is the key of a one-sided node of sort causality",
                               lambda p: _node("zz_fixture", p["pair_lean"],
                                               {"introduces": p["c1"], "lemma": DUAL_LIB["intro"]}, sort="pair")),
    "dual-introduction-shape": (
        "is none of `C.Q ↔ C.P ∧ C.dual.P` and",
        lambda p: (_node("zz_two", DUAL_LIB["two"], DUAL_LIB["two_key"])
                   + _node("zz_one", DUAL_LIB["one"], {"introduces": "zz_two", "lemma": DUAL_LIB["two_key"]}))),
    # another node's lemma whose name the node's only starts (the audit of T-tac-ladder-dual-key):
    # strongly_causal keyed with the lemma of strongly_causal_open
    "dual-prefix-name": ("is `C.dual.P ↔ C.P` for a P other than Causal.Causality.StronglyCausal",
                         lambda p: _node("zz_fixture", "Causal.Causality.StronglyCausal",
                                         "Causal.Causality.dual_stronglyCausalOpen")),
    # a two-sided r, r ⇒ p, p one-sided introducing a two-sided q: a counterexample with r and
    # without q is no contradiction on C alone, and is one across time reversal
    "dual-contradiction": (
        "contradiction across time reversal: counterexample",
        lambda p: (_node("zz_r", DUAL_LIB["two"], DUAL_LIB["two_key"])
                   + _node("zz_p", DUAL_LIB["one"], {"introduces": "zz_q", "lemma": DUAL_LIB["intro"]})
                   + _node("zz_q", DUAL_LIB["two"], DUAL_LIB["two_key"])
                   + _implies({"from": ["zz_r"], "to": "zz_p", "witness": DUAL_LIB["edge"]})
                   + "\n[[fails]]\nfrom = \"zz_r\"\nto = \"zz_q\"\nwitness = %s\nstatus = \"checked\"\n" % _q(
                       p["fail"]["witness"]))),
}
BREAKAGES.update(DUAL_BREAKAGES)


def broken(text, name):
    """The ladder's TOML text with the breakage `name` appended."""
    return text.rstrip("\n") + "\n" + BREAKAGES[name][1](picks(tomllib.loads(text)))


def main(argv):
    if argv == ["--list"]:
        print("\n".join(BREAKAGES))
        return 0
    if len(argv) != 3 or argv[1] not in BREAKAGES:
        sys.exit(__doc__)
    src, name, out = argv
    with open(src, encoding="utf-8") as fh:
        text = broken(fh.read(), name)
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
