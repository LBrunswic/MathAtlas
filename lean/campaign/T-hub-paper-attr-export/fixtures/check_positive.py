#!/usr/bin/env python3
"""Check the positive export: run.sh's scenario `pos` (fixtures A and C imported).

    python3 -I check_positive.py <exported lean-facts.json> <baseline lean-facts.json>

The baseline is the export of the same tree with no fixture imported. Every baseline object
must be byte-identical in the fixture export except `validLabel` and `labels`, which differ only
by an added `paper` key; the fixture modules' own keys carry exactly the fields expected.
"""
import json
import sys

got = json.load(open(sys.argv[1]))["declarations"]
base = json.load(open(sys.argv[2]))["declarations"]
errs = []

want_paper = {
    "GFNBounds.Paper.validLabel": ["lem:paperattr_test_export_same", "lem:paperattr_test_export_c"],
    "GFNBounds.Paper.labels": ["lem:paperattr_test_export_dup"],
    "GFNBounds.Paper.FixA.asm": ["lem:paperattr_test_export_asm"],
    "GFNBounds.Paper.FixA.d": ["lem:paperattr_test_export_def"],
    "GFNBounds.Paper.FixC.single": ["lem:paperattr_test_export_single"],
}
want_conj = {"GFNBounds.Paper.FixA.asm": ["GFNBounds.Paper.FixA.zero_eq",
                                          "GFNBounds.Paper.FixA.one_eq"]}

for k, v in base.items():
    if k not in got:
        errs.append("baseline key missing: " + k)
        continue
    g = dict(got[k])
    if k in want_paper:
        g.pop("paper", None)
    if g != v:
        errs.append("baseline object changed: " + k)

for k, o in got.items():
    if "paper" in o and k not in want_paper:
        errs.append("unexpected paper on " + k)
    if "conjuncts" in o and k not in want_conj:
        errs.append("unexpected conjuncts on " + k)
for k, ls in want_paper.items():
    if got.get(k, {}).get("paper") != ls:
        errs.append("paper of %s: %r, expected %r" % (k, got.get(k, {}).get("paper"), ls))
for k, cs in want_conj.items():
    if got.get(k, {}).get("conjuncts") != cs:
        errs.append("conjuncts of %s: %r, expected %r" % (k, got.get(k, {}).get("conjuncts"), cs))

new = sorted(set(got) - set(base))
mods = sorted({got[k]["module"] for k in new})
if mods != ["GFNBounds.Paper.AppendixFixA", "GFNBounds.Paper.FixC"]:
    errs.append("new keys from modules %r" % mods)

if errs:
    print("check_positive: FAIL\n  " + "\n  ".join(errs))
    sys.exit(1)
print("check_positive: ok (%d baseline objects unchanged but 2 gained paper; %d new keys from %s)"
      % (len(base) - 2, len(new), ", ".join(mods)))
