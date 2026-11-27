"""Read-only: rebuild each ledger in memory (ledger.build(write=False)) and list the fields that
differ from the ledger.json on disk, for the rows naming a constant this target touched."""
import sys, json, os
HUB = "/home/maxbrain/Dropbox/LeanArticles"
sys.path.insert(0, os.path.join(HUB, "tools"))
os.chdir(HUB)
import ledger
TOUCHED = ["ChartIso.curveOn_symm", "chartImage_subset_target", "chronalCurveOn_image",
           "chronalCurveOn_symm_image", "curveOn_chart_symm", "hasChronalNeighbourEverywhere",
           "chronalFutureNeighbours", "Iplus_nonempty"]
for p in ["ett", "barbot", "ers-predictability", "sbierski-mghd", "sbierski-schwarzschild"]:
    ledger.CFG = ledger.Config("papers/%s/ledger/ledger.toml" % p)
    new = ledger.build(write=False)
    old = json.load(open(ledger.CFG.ledger, encoding="utf-8"))
    ob = {s["label"]: s for s in old["statements"]}
    nb = {s["label"]: s for s in new["statements"]}
    diffs = []
    for lab in sorted(set(ob) | set(nb)):
        a, b = ob.get(lab), nb.get(lab)
        if a is None or b is None:
            diffs.append((lab, "row added/removed")); continue
        for k in sorted(set(a) | set(b)):
            if a.get(k) != b.get(k):
                diffs.append((lab, k))
    touched = [s["label"] for s in new["statements"] if any(t in d for d in s.get("decls", []) for t in TOUCHED)]
    print("==", p, "rows differing:", len({d[0] for d in diffs}), "fields:", sorted({d[1] for d in diffs}))
    print("   rows naming a touched constant:", touched)
    for lab, k in diffs:
        if lab in touched:
            print("   ", lab, k, "| before:", json.dumps(ob[lab].get(k))[:300], "| after:", json.dumps(nb[lab].get(k))[:300])
