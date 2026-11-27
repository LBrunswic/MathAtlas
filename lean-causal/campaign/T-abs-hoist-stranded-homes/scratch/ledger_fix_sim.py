"""Read-only simulation: would the ETT ledger check pass once cor:massA_cac's curated
extra_lean_files also lists Causal/GXStructure.lean (the new home of Causal.ChartIso.curveOn_symm)?
Patches ledger.load_ledger in memory; writes nothing."""
import os
import sys

HUB = "/home/maxbrain/Dropbox/LeanArticles"
sys.path.insert(0, os.path.join(HUB, "tools"))
os.chdir(HUB)
import ledger  # noqa: E402

ledger.CFG = ledger.Config("papers/ett/ledger/ledger.toml")
_orig = ledger.load_ledger


def patched():
    led = _orig()
    for s in led["statements"]:
        if s.get("label") == "cor:massA_cac":
            extra = list(s.get("extra_lean_files", []))
            extra.append("Causal/GXStructure.lean")
            s["extra_lean_files"] = extra
            print("patched extra_lean_files:", extra)
    return led


ledger.load_ledger = patched
try:
    rc = ledger.check()
except SystemExit as e:  # check() may exit with its status
    rc = e.code
print("check returned:", rc)
