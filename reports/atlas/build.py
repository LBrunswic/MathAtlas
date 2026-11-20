#!/usr/bin/env python3
"""Assemble the atlas page: data.json (extract.py) + hub.toml + roadmap/roadmap.toml + live numbers.

Numbers are never typed: the library cards read each package's sorry_count.py and the axiom-sweep
cache sweep.json (refreshed from `make -C <pkg> check` logs by `python3 build.py --logs DIR`); the
GFN Bounds card reads lean/docs/COVERAGE.md and reports/doubledag/gfnbounds/doubledag.json. The
Lean overlay reads the committed lean/edges-<paper>.json (lean_edges.py) and never runs Lean.
"""
import json
import os
import sys
import tomllib

sys.dont_write_bytecode = True   # nothing written beside the sources, here or in tools/

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import status_report as sr  # noqa: E402
sys.path.insert(0, HERE)
import lean_edges as le  # noqa: E402

hub = tomllib.load(open(os.path.join(HERE, "hub.toml"), "rb"))
road = tomllib.load(open(os.path.join(ROOT, "roadmap", "roadmap.toml"), "rb"))
logs = sys.argv[sys.argv.index("--logs") + 1] if "--logs" in sys.argv else None
sweep = sr.read_sweeps(logs, os.path.join(HERE, "sweep.json"))
with open(os.path.join(HERE, "sweep.json"), "w") as fh:
    json.dump(sweep, fh, indent=2, sort_keys=True)
    fh.write("\n")

libs = {}
for lid, l in hub["lib"].items():
    L = dict(l)
    if l.get("package"):
        f = sr.package_figures(l["package"], sweep)
        L["stats"] = "{:,} decls · {} strict sorry".format(f["decls"], f["sorrystrict"])
        L["cells"] = [["{:,}".format(f["decls"]), "strict declarations"], [str(f["modules"]), "modules"],
                      [str(f["sorryscaffold"]), "scaffold sorrys"]]
    else:
        g = sr.gfn_figures()
        L["stats"] = "%d/%d rows closed" % (g["closed"], g["statements"])
        L["cells"] = [[str(g["closed"]), "rows closed"], [str(g["statements"]), "rows"], [str(g["open"]), "open (terminal)"]]
    libs[lid] = L
papers = dict(hub["paper"])
g = sr.gfn_figures()
papers["gfnbounds"] = dict(papers["gfnbounds"], closed=g["closed"], target=g["statements"] - g["open"])
D = json.loads(open(os.path.join(HERE, "data.json"), encoding="utf-8").read())
for slug in D:
    if slug not in papers:   # a ledger hub.toml does not curate yet: a placeholder card, said as such
        papers[slug] = {"short": slug, "cluster": "other", "authors": "", "title": slug, "headline": [],
                        "summary": "Ledgered, but not yet curated in reports/atlas/hub.toml."}

# The double DAG of the GFN pair, as committed by tools/doubledag_gfnbounds.sh.
ddg = os.path.join(ROOT, "reports", "doubledag", "gfnbounds", "doubledag.json")
if os.path.exists(ddg):
    papers["gfnbounds"] = dict(papers["gfnbounds"], dd=json.load(open(ddg, encoding="utf-8"))["summary"],
                               ddpath="reports/doubledag/gfnbounds/DOUBLEDAG.md")

# The Lean overlay: lean/edges-<paper>.json (lean_edges.py edges), packed against data.json's node
# order, with each file's freshness read off the ledger and the package as they are now.
LEAN = {}
KIND = {k: i for i, k in enumerate(le.KINDS)}
for slug in D:
    ep = le.edges_path(slug)
    if not os.path.exists(ep):
        continue
    E = json.load(open(ep, encoding="utf-8"))
    ix = {n["id"]: i for i, n in enumerate(D[slug]["nodes"])}
    names = sorted(E["decls"])
    nx = {n: i for i, n in enumerate(names)}
    edges = [[ix[e["source"]], ix[e["target"]], KIND[e["kind"]], [nx[d] for d in e.get("witness") or []]]
             for e in E["edges"] if e["source"] in ix and e["target"] in ix]
    fr = le.freshness(slug, E)
    LEAN[slug] = {
        "package": E["package"], "commit": (E["extracted"]["commit"] or "")[:7],
        "dirty": E["extracted"]["dirty"], "now": (fr["commit_now"] or "")[:7], "current": fr["current"],
        "why": fr["why"], "facts": E["facts"], "summary": E["summary"], "flat": E["flat"],
        "missing": E["missing"], "names": names, "where": [E["decls"][n] for n in names],
        "principals": [[ix[l], [nx[d] for d in ps]] for l, ps in sorted(E["principals"].items()) if l in ix],
        "edges": edges}

HUB = {"clusters": hub["cluster"], "papers": papers, "libs": libs, "edges": hub["edge"],
       "provenance": hub["provenance"]}
ROAD = {"targets": road.get("target", []), "known_red": road.get("gates", {}).get("known_red", [])}

t = open(os.path.join(HERE, "template.html"), encoding="utf-8").read()
Dtext = open(os.path.join(HERE, "data.json"), encoding="utf-8").read()
out = (t.replace("__DATA__", Dtext).replace("__HUB__", json.dumps(HUB, ensure_ascii=False))
        .replace("__ROAD__", json.dumps(ROAD, ensure_ascii=False))
        .replace("__LEAN__", json.dumps(LEAN, ensure_ascii=False, separators=(",", ":"))))
open(os.path.join(HERE, "atlas.body.html"), "w", encoding="utf-8").write(out)
print("atlas: %d bytes, %d roadmap targets, Lean overlay for %s%s" % (
    len(out), len(ROAD["targets"]), ", ".join(sorted(LEAN)),
    "".join("; %s STALE (%s)" % (k, "; ".join(v["why"])) for k, v in sorted(LEAN.items()) if not v["current"])))
