#!/usr/bin/env python3
"""Breakages of a copy of papers/egf/programme/corrections.toml: one per rule of
`tools/corrections.py check`. Each must make the check fail.

    python3 breakages.py --list                     the breakage names, one per line
    python3 breakages.py REGISTER NAME OUT          write REGISTER broken by NAME to OUT

A breakage APPENDS one [[correction]] table (TOML lets an array of tables continue anywhere), built
from what the register already has, so the planner's edits do not stale it.
tests/test_corrections.py imports BREAKAGES and checks each in-process; run.sh drives the CLI.
"""
import sys
import tomllib

GOOD = {"printed": "main.tex:362", "kind": "gap", "finding": "fixture", "status": "found"}


def entry(**kw):
    e = dict(GOOD, id="C-9001")
    e.update(kw)
    out = ["", "[[correction]]"]
    for k, v in e.items():
        if isinstance(v, list):
            out.append("%s = [%s]" % (k, ", ".join('"%s"' % x for x in v)))
        else:
            out.append('%s = "%s"' % (k, v))
    return "\n".join(out) + "\n"


def BREAKAGES(data):
    first = data["correction"][0]["id"]
    return {
        "duplicate-id": entry(id=first),
        "bad-id": entry(id="X-1"),
        "unknown-kind": entry(kind="mistake"),
        "unknown-status": entry(status="done"),
        "printed-outside": entry(printed="main.tex:999999"),
        "printed-malformed": entry(printed="l.362"),
        "unknown-label": entry(label="theo:no_such_label"),
        "unknown-basis": entry(basis=["OQ-99999"]),
        "unknown-batch": entry(batch="T-egf-no-such-batch"),
        "false-without-refutation": entry(kind="false"),
        "refutation-unresolved": entry(kind="false", refutation=["EGF.no_such_refutation"]),
        "proved-without-anchor": entry(status="proved"),
        "anchor-unresolved": entry(status="proved", anchor=["EGF.no_such_anchor"]),
        "adopted-without-dec": entry(status="adopted", anchor=["EGF.main_universality"], basis=["OQ-50"],
                                     corrected="x", summary="x", added_hypotheses=[]),
        "applied-without-commit": entry(status="applied", anchor=["EGF.main_universality"], basis=["DEC-1"],
                                        corrected="x", summary="x", added_hypotheses=[],
                                        v2_commit="0000000000000000000000000000000000000000"),
    }


if __name__ == "__main__":
    if sys.argv[1:] == ["--list"]:
        print("\n".join(BREAKAGES({"correction": [{"id": "C-1"}]})))
        sys.exit(0)
    src, name, out = sys.argv[1:4]
    text = open(src, encoding="utf-8").read()
    br = BREAKAGES(tomllib.loads(text))
    if name not in br:
        sys.exit("no breakage %s" % name)
    open(out, "w", encoding="utf-8").write(text + br[name])
