#!/usr/bin/env python3
"""Assemble the atlas page: data.json (extract.py) + hub.toml + roadmap/roadmap.toml + live numbers.

Numbers are never typed: the library cards read each package's sorry_count.py and the axiom-sweep
cache sweep.json (refreshed from `make -C <pkg> check` logs by `python3 build.py --logs DIR`); the
GFN Bounds card reads lean/docs/COVERAGE.md.
"""
import json
import os
import sys
import tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import status_report as sr  # noqa: E402

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

HUB = {"clusters": hub["cluster"], "papers": papers, "libs": libs, "edges": hub["edge"],
       "provenance": hub["provenance"]}
ROAD = {"targets": road.get("target", []), "known_red": road.get("gates", {}).get("known_red", [])}

t = open(os.path.join(HERE, "template.html"), encoding="utf-8").read()
D = open(os.path.join(HERE, "data.json"), encoding="utf-8").read()
out = (t.replace("__DATA__", D).replace("__HUB__", json.dumps(HUB, ensure_ascii=False))
        .replace("__ROAD__", json.dumps(ROAD, ensure_ascii=False)))
open(os.path.join(HERE, "atlas.body.html"), "w", encoding="utf-8").write(out)
print("atlas: %d bytes, %d roadmap targets" % (len(out), len(ROAD["targets"])))
