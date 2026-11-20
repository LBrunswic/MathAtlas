#!/usr/bin/env python3
"""Assemble the atlas page: data.json (extract.py) + hub.toml + roadmap/roadmap.toml + live numbers.

Numbers are never typed: the library cards read each package's sorry_count.py and the axiom-sweep
cache sweep.json (refreshed from `make -C <pkg> check` logs by `python3 build.py --logs DIR`, one
check-<pkg>.log per package of hub.toml's lib table); the GFN Bounds card reads lean/docs/COVERAGE.md
and reports/doubledag/gfnbounds/doubledag.json. The Lean overlay reads the committed
lean/edges-<paper>.json (lean_edges.py) and never runs Lean.
"""
import glob
import json
import os
import re
import subprocess
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


def strict_lib(pkg):
    """The package's strict library: the one lean_lib its lakefile compiles with warningAsError."""
    lake = tomllib.load(open(os.path.join(ROOT, pkg, "lakefile.toml"), "rb"))
    names = [x["name"] for x in lake.get("lean_lib", []) if (x.get("leanOptions") or {}).get("warningAsError")]
    assert len(names) == 1, "%s/lakefile.toml: expected one strict lean_lib, found %r" % (pkg, names)
    return names[0]


# Every package of the lib table, not only the ones tools/status_report.py lists: a package the hub
# has just created gets its card from its own lakefile and sorry_count.py.
PKGS = {l["package"]: strict_lib(l["package"]) for l in hub["lib"].values() if l.get("package")}
assert all(PKGS.get(p) == lib for p, lib in sr.PACKAGES.items()), \
    "hub.toml's lib table must list every package of tools/status_report.py, with the same strict lib"


def read_sweeps(logdir, cache):
    """status_report.read_sweeps over PKGS. With --logs every package's check log is read (the same
    two lines status_report matches); without, the cache is reused, and a package it does not hold
    yet is drawn as not swept rather than given a number."""
    sweep = json.load(open(cache)) if os.path.exists(cache) else {}
    if logdir:
        for pkg in sorted(PKGS):
            log = os.path.join(logdir, "check-%s.log" % pkg)
            text = open(log, encoding="utf-8").read()
            m = re.search(r"axiom sweep \(strict\): (\d+) declarations in (\d+) modules", text)
            ok = re.search(r"axiom sweep: all within propext/Classical\.choice/Quot\.sound", text)
            assert m and ok, "no clean axiom sweep in " + log
            sweep[pkg] = {"decls": int(m[1]), "modules": int(m[2])}
    missing = sorted(set(sr.PACKAGES) - set(sweep))
    assert not missing, "axiom-sweep counts missing for %s: pass --logs once" % ", ".join(missing)
    return {p: sweep[p] for p in sorted(sweep) if p in PKGS}


def package_figures(pkg):
    """status_report.package_figures for any package of PKGS: strict files, the two sorry counts
    (the package's scripts/sorry_count.py), and the cached sweep when there is one."""
    d = os.path.join(ROOT, pkg)
    files = glob.glob(os.path.join(d, PKGS[pkg], "**", "*.lean"), recursive=True)
    out = subprocess.run([sys.executable, os.path.join(d, "scripts", "sorry_count.py")], cwd=d,
                         capture_output=True, text=True)
    strict = re.search(r"sorry \(strict[^:]*:\s*(\d+)", out.stdout)
    scaff = re.search(r"sorry \(scaffold[^:]*:\s*(\d+)", out.stdout)
    assert strict and scaff, "unrecognised sorry_count output in " + pkg + ": " + out.stdout[-300:]
    f = {"files": len(files), "sorrystrict": int(strict[1]), "sorryscaffold": int(scaff[1])}
    f.update(sweep.get(pkg, {}))
    return f


sweep = read_sweeps(logs, os.path.join(HERE, "sweep.json"))
with open(os.path.join(HERE, "sweep.json"), "w") as fh:
    json.dump(sweep, fh, indent=2, sort_keys=True)
    fh.write("\n")

libs = {}
g = sr.gfn_figures()
for lid, l in hub["lib"].items():
    L = dict(l)
    pkg = l.get("package")
    if pkg:
        f = package_figures(pkg)
        if "decls" in f:
            L["stats"] = "{:,} decls · {} strict sorry".format(f["decls"], f["sorrystrict"])
            L["cells"] = [["{:,}".format(f["decls"]), "strict declarations"], [str(f["modules"]), "modules"],
                          [str(f["sorryscaffold"]), "scaffold sorrys"]]
            L["prov"] = ("Declarations and modules: the strict axiom sweep of make -C %s check, cached in "
                         "reports/atlas/sweep.json and refreshed by make -C reports/atlas LOGS=<dir>. "
                         "Sorrys: %s/scripts/sorry_count.py, read at build." % (pkg, pkg))
        else:
            L["stats"] = "not swept · {} strict sorry".format(f["sorrystrict"])
            L["cells"] = [[str(f["files"]), "strict files"], [str(f["sorrystrict"]), "strict sorrys"],
                          [str(f["sorryscaffold"]), "scaffold sorrys"]]
            L["prov"] = ("No axiom sweep of %s has been read yet, so its declarations are not counted here: "
                         "make -C reports/atlas LOGS=<dir> reads them from make -C %s check. Files: %s/%s/; "
                         "sorrys: %s/scripts/sorry_count.py, read at build." % (pkg, pkg, pkg, PKGS[pkg], pkg))
    else:
        L["stats"] = "%d/%d rows closed" % (g["closed"], g["statements"])
        L["cells"] = [[str(g["closed"]), "rows closed"], [str(g["statements"]), "rows"], [str(g["open"]), "open (terminal)"]]
        L["prov"] = "Rows: lean/docs/COVERAGE.md, GFNBoundsLean's own generated coverage."
    libs[lid] = L
papers = dict(hub["paper"])
papers["gfnbounds"] = dict(papers["gfnbounds"], closed=g["closed"], target=g["statements"] - g["open"],
                           badge="%d rows · %d terminal" % (g["statements"], g["open"]))
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
