#!/usr/bin/env python3
"""The legacy draft is frozen, and `labeled/` differs from it by `\\label{}` only.

    python3 tools/legacy_check.py --paper papers/<slug>   # exit 1 on any deviation

Two invariants, both about "forget the first writing" staying checkable:
  1. every file in `legacy/orig/` has the sha256 `legacy/MANIFEST.json` recorded, and the
     manifest lists no file that is missing -- the snapshot is the story source, and it does
     not move;
  2. for every file in `legacy/labeled/`, removing every `\\label{...}` token yields `orig/`'s
     text modulo whitespace -- labels are the ONLY edit allowed there, because the ledger keys
     on them and nothing else may be "improved" in a draft that is to be forgotten.
Exit 2 if the paper has no legacy/ at all.
"""
import hashlib
import json
import os
import re
import sys

LABEL = re.compile(r"\\label\{[^}]*\}")


def norm(text):
    return " ".join(LABEL.sub("", text).split())


def main():
    if "--paper" not in sys.argv:
        print(__doc__)
        return 2
    paper = sys.argv[sys.argv.index("--paper") + 1]
    leg = os.path.join(paper, "legacy")
    man_p = os.path.join(leg, "MANIFEST.json")
    if not os.path.exists(man_p):
        print("legacy_check: FAIL no %s" % man_p)
        return 2
    man = json.load(open(man_p, encoding="utf-8"))
    fail = 0
    orig = os.path.join(leg, "orig")
    for f, rec in man["files"].items():
        p = os.path.join(orig, f)
        if not os.path.exists(p):
            print("legacy_check: FAIL %s listed in the manifest is missing" % f)
            fail += 1
            continue
        h = hashlib.sha256(open(p, "rb").read()).hexdigest()
        if h != rec["sha256"]:
            print("legacy_check: FAIL %s changed since the snapshot (sha256 %s..)" % (f, h[:12]))
            fail += 1
    for dirpath, _d, names in os.walk(orig):
        for n in names:
            rel = os.path.relpath(os.path.join(dirpath, n), orig)
            if rel not in man["files"]:
                print("legacy_check: FAIL %s is in orig/ but not in the manifest" % rel)
                fail += 1
    labeled = os.path.join(leg, "labeled")
    if os.path.isdir(labeled):
        for dirpath, _d, names in os.walk(labeled):
            for n in names:
                if not n.endswith(".tex"):
                    continue
                rel = os.path.relpath(os.path.join(dirpath, n), labeled)
                op = os.path.join(orig, rel)
                if not os.path.exists(op):
                    print("legacy_check: FAIL labeled/%s has no counterpart in orig/" % rel)
                    fail += 1
                    continue
                a = norm(open(op, encoding="utf-8", errors="replace").read())
                b = norm(open(os.path.join(labeled, rel), encoding="utf-8",
                              errors="replace").read())
                if a != b:
                    # locate the first divergence for the reader
                    i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]),
                             min(len(a), len(b)))
                    print("legacy_check: FAIL labeled/%s differs from orig/ beyond \\label "
                          "(near: ...%s...)" % (rel, b[max(0, i - 40):i + 40]))
                    fail += 1
    if fail:
        return 1
    print("legacy_check: %s frozen (%d files)%s" % (
        paper, len(man["files"]), "; labeled/ = orig/ + labels" if os.path.isdir(labeled) else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
