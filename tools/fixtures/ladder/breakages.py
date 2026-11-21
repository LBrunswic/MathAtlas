#!/usr/bin/env python3
"""Breakages of a copy of programme/ladder.toml: one per rule `tools/ladder.py check` gained with
T-tool-ladder-py. Each must make the check fail, with the violation named here.

    python3 breakages.py --list                 the breakage names, one per line
    python3 breakages.py LADDER NAME OUT        write LADDER broken by NAME to OUT

A breakage APPENDS entries to the ladder (TOML lets an array of tables continue anywhere), built
from the ids and witnesses the ladder already has, so that the keeper's edits do not stale it.
tests/test_programme.py imports BREAKAGES and checks each in-process; run.sh drives the CLI.
"""
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
            "fail": fail, "bare": bare, "fact": fact, "fact_other": other, "lean": props[0]["lean"]}


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
    "transfer-contradiction": (
        "contradiction: transfer",
        lambda p: ("\n[[transfer]]\npair = %s\nproperty = %s\nwitness = %s\nstatus = \"checked\"\n"
                   "\n[[transfer]]\npair = %s\nproperty = %s\ncounterexample = %s\nstatus = \"checked\"\n") % (
            _q(p["pair"]), _q(p["c1"]), _q(p["edge"]["witness"]), _q(p["pair"]), _q(p["c1"]), _q(p["fail"]["witness"]))),
}


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
