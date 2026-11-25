#!/usr/bin/env python3
"""Breakages of a copy of a paper's restatement register: one per rule of `tools/restate.py check`.
Each must make the check fail.

    python3 restate_breakages.py --list              the breakage names, one per line
    python3 restate_breakages.py SLUG NAME OUT       write SLUG's register broken by NAME to OUT

A breakage edits the list of entries the register already has (the first one is the victim), so
the agents' later edits do not stale it. tests/test_restate.py checks each in-process; run.sh drives
the CLI.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", ".."))
import restate  # noqa: E402

DRAFT = {"status": "drafted", "kind": "imprecise", "anchor": None, "rewritten": "Let $x$ be.",
         "changes": ["~ fixture"]}


def BREAKAGES(slug, entries):
    """name -> the broken list of entries."""
    first, rest = entries[0], entries[1:]
    anchor = sorted(restate.strict_decls(slug))[:1]

    def with_(**kw):
        e = dict(first)
        e.update(kw)
        return [{k: v for k, v in e.items() if v is not None}] + rest

    draft = dict(DRAFT, anchor=anchor)
    out = {
        "unknown-status": with_(status="done"),
        "not-a-label": with_(label="thm:no-such-label-anywhere"),
        "stale-sha": with_(printed_sha256="0" * 64),
        "stale-span": with_(printed="Nowhere.tex:1-2"),
        "no-finding": with_(finding=" "),
        "unknown-kind": with_(kind="mistake"),
        "refutation-not-a-decl": with_(refutation=["No.Such.declaration_anywhere"]),
        "basis-not-a-row": with_(basis=["DEC-999999"]),
        "dismissed-without-reason": with_(status="dismissed", reason=None),
        "blocked-not-open": with_(status="blocked", oq="OQ-1"),
        "drafted-without-anchor": with_(**dict(draft, anchor=[])),
        "drafted-without-rewritten": with_(**dict(draft, rewritten=" ")),
        "drafted-without-changes": with_(**dict(draft, changes=[])),
        "drafted-without-kind": with_(**dict(draft, kind=None)),
        "rewritten-unbalanced": with_(**dict(draft, rewritten="Let $\\{x$ be.")),
        "rewritten-with-label": with_(**dict(draft, rewritten="\\label{x} Let $x$ be.")),
        "false-without-refutation": with_(**dict(draft, kind="false", refutation=None, refutation_note=None)),
        "underspecified-without-dec": with_(**dict(draft, kind="underspecified", basis=None)),
        "checked-without-check": with_(**dict(draft, status="checked", check=None)),
        "checked-missing-file": with_(**dict(draft, status="checked", check="CHECK-none.json")),
        "reviewed-without-review": with_(**dict(draft, status="reviewed", check=None, review=None)),
        "rewritten-with-lean-identifier": with_(**dict(draft, rewritten="By GX.not_isAEAtlas_iUnion_empty, $x$.")),
        "reviewed-with-unruled-reading": with_(**dict(draft, status="reviewed", check=None, review="x",
                                                      reading="tame = locally flat", basis=None)),
        "duplicate-entry": [first] + entries,
        "strong-candidate-dropped": rest,
    }
    return out


def main(argv):
    if argv == ["--list"]:
        slug = os.environ.get("RESTATE_FIXTURE_SLUG", "gx")
        print("\n".join(BREAKAGES(slug, restate.load(slug))))
        return 0
    slug, name, out = argv
    entries = restate.load(slug)
    restate.save(slug, BREAKAGES(slug, entries)[name], out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
