#!/usr/bin/env python3
"""The import-tier gate of ARCHITECTURE.md §4.4 (DEC-212; target T-arch-import-gate).

    python3 tools/import_gate.py report   # print the violations, exit 0 (today: the move's worklist)
    python3 tools/import_gate.py check    # exit 1 on any violation (the gate after the window, §5)
        [--hub DIR] [--tiers FILE] [--all] [--json FILE]

Every library declares its tier in tools/import_tiers.toml (general, local, global, orbit, outside).
The gate reads the header `import` lines of every module of every lean_lib of every package
(`lean/` and `lean-*/` with a lakefile.toml, and every package hub.toml names); it reads them and
edits nothing. A module belongs to the declared library whose `modules` pattern matches it most
specifically; a scaffold module (`XScaffold.Foo`) belongs where its strict mirror `X.Foo` does.
For each import between two different declared libraries A -> B:

  upward             tiers rank general < local < global, and B ranks above A; or A is general
                     (general imports mathlib only, §1)
  undeclared-orbit   B is an orbit not in A's `inputs` (an orbit is a named external input, §1)
  orbit-imports-hub  A is an orbit and B is a hub library other than a declared input orbit
  into-outside       A is in the theory (general/local/global/orbit) and B is outside it
  undeclared-dep     A lists `depends` and B is not in their transitive closure (§1's table)
  cycle              the graph of declared libraries has a cycle (once per strongly connected
                     component, with a shortest cycle and one import witnessing each edge)
  root-aggregator    the import is made by a lakefile library's root module (`Causal`, `GX`), which
                     today aggregates libraries of several tiers; kept out of the graph
and, per module:
  strict-imports-scaffold   a strict module imports a scaffold module (never, lakefiles)
  undeclared-module         a module no declared library claims
  unresolved                an import that is neither a hub module nor an external root (Mathlib, ...)

Imports inside one declared library are never a violation (Lean itself forbids module cycles).
Report mode exits 0 whatever it finds, including a broken tier file (printed as CONFIG lines): the
packages mix tiers until the window, and the target keeps the gate out of `make check` until then.
"""
import argparse
import collections
import fnmatch
import json
import os
import re
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TIERS = ("general", "local", "global", "orbit", "outside")
RANK = {"general": 0, "local": 1, "global": 2}
THEORY = ("general", "local", "global", "orbit")
# Roots of modules that come from outside the hub: mathlib and what it brings, and Lean itself.
EXTERNAL = {"Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq", "Plausible", "ProofWidgets",
            "ImportGraph", "LeanSearchClient", "Lake", "Cli"}
IDENT = re.compile(r"[A-Za-z_«][^\s]*$")


# ------------------------------------------------------------------ the Lean header
def header_imports(text):
    """[(line, module)] of the header of a Lean 4 file: `module`, `prelude` and `[public] [meta]
    import [all] M` commands, with comments skipped, up to the first other token."""
    out, i, n, line = [], 0, len(text), 1

    def skip():
        nonlocal i, line
        while i < n:
            c = text[i]
            if c in " \t\r":
                i += 1
            elif c == "\n":
                i += 1
                line += 1
            elif text.startswith("--", i):
                j = text.find("\n", i)
                i = n if j < 0 else j
            elif text.startswith("/-", i):
                depth, i = 1, i + 2
                while i < n and depth:
                    if text.startswith("/-", i):
                        depth, i = depth + 1, i + 2
                    elif text.startswith("-/", i):
                        depth, i = depth - 1, i + 2
                    else:
                        line += text[i] == "\n"
                        i += 1
            else:
                return

    def token():
        nonlocal i
        j = i
        while j < n and not text[j].isspace() and not text.startswith("--", j) and not text.startswith("/-", j):
            j += 1
        t, i = text[i:j], j
        return t

    while True:
        skip()
        if i >= n:
            return out
        save_i, save_line = i, line
        t = token()
        if t in ("module", "prelude"):
            continue
        mods = []
        while t in ("public", "private", "meta"):
            mods.append(t)
            skip()
            t = token()
        if t != "import":
            i, line = save_i, save_line
            return out
        skip()
        at = line
        t = token()
        if t == "all":
            skip()
            at = line
            t = token()
        if not IDENT.match(t or ""):
            return out
        out.append((at, t))


# ------------------------------------------------------------------ packages and modules
def packages(hub):
    """Package directories, relative to the hub: lean/ and lean-*/ with a lakefile.toml, and every
    package hub.toml's dropbox_ignored names (`<pkg>/.lake`). Returns (dirs, problems)."""
    found, problems = set(), []
    for d in sorted(os.listdir(hub)):
        if (d == "lean" or d.startswith("lean-")) and os.path.isfile(os.path.join(hub, d, "lakefile.toml")):
            found.add(d)
    hubtoml = os.path.join(hub, "hub.toml")
    if os.path.isfile(hubtoml):
        with open(hubtoml, "rb") as f:
            cfg = tomllib.load(f)
        for p in cfg.get("hub", {}).get("dropbox_ignored", []) + cfg.get("dropbox_ignored", []):
            d = p[:-len("/.lake")] if p.endswith("/.lake") else None
            if d is None:
                continue
            if os.path.isfile(os.path.join(hub, d, "lakefile.toml")):
                found.add(d)
            else:
                problems.append("hub.toml names package %s, which has no lakefile.toml" % d)
    return sorted(found), problems


def lib_roots(lib):
    roots = []
    for g in lib.get("globs", []) or lib.get("roots", []) or [lib["name"]]:
        roots.append(re.sub(r"\.[*+]$", "", g))
    return roots


def modules(hub, pkg):
    """{module: (lib_name, is_scaffold, strict_lib_or_None, relpath)} of a package's lean_libs."""
    with open(os.path.join(hub, pkg, "lakefile.toml"), "rb") as f:
        lake = tomllib.load(f)
    libs = lake.get("lean_lib", [])
    names = {lib["name"] for lib in libs}
    out = {}
    for lib in libs:
        name = lib["name"]
        strict = name[:-len("Scaffold")] if name.endswith("Scaffold") and name[:-len("Scaffold")] in names else None
        src = os.path.join(hub, pkg, lib.get("srcDir", "."))
        for root in lib_roots(lib):
            base = os.path.join(src, *root.split("."))
            cands = []
            if os.path.isfile(base + ".lean"):
                cands.append(base + ".lean")
            if os.path.isdir(base):
                for dp, dns, fns in os.walk(base):
                    dns[:] = sorted(x for x in dns if x != ".lake" and not x.startswith("."))
                    cands += [os.path.join(dp, fn) for fn in sorted(fns) if fn.endswith(".lean")]
            for c in cands:
                rel = os.path.relpath(c, src)[:-len(".lean")]
                out[rel.replace(os.sep, ".")] = (name, strict is not None, strict, os.path.relpath(c, hub))
    return out


# ------------------------------------------------------------------ tiers
def load_tiers(path):
    """(libraries {name: entry}, config errors)."""
    errs = []
    try:
        with open(path, "rb") as f:
            data = tomllib.load(f)
    except (OSError, tomllib.TOMLDecodeError) as e:
        return {}, ["cannot read %s: %s" % (path, e)]
    libs = {}
    for e in data.get("library", []):
        n = e.get("name")
        if not n:
            errs.append("a [[library]] has no name")
            continue
        if n in libs:
            errs.append("library %s declared twice" % n)
        if e.get("tier") not in TIERS:
            errs.append("library %s: tier %r is not one of %s" % (n, e.get("tier"), ", ".join(TIERS)))
        libs[n] = e
    for n, e in libs.items():
        for d in e.get("depends", []):
            if d not in libs:
                errs.append("library %s depends on undeclared library %s" % (n, d))
        for d in e.get("inputs", []):
            if d not in libs:
                errs.append("library %s takes undeclared input %s" % (n, d))
            elif libs[d].get("tier") != "orbit":
                errs.append("library %s: input %s is not an orbit" % (n, d))
    seen = {}
    for n, e in libs.items():
        for p in e.get("modules", []):
            if p in seen:
                errs.append("pattern %s claimed by both %s and %s" % (p, seen[p], n))
            seen[p] = n
    return libs, errs


def pattern_matches(p, m):
    if p.endswith("*"):
        return fnmatch.fnmatchcase(m, p) or fnmatch.fnmatchcase(m, p + ".*")
    return m == p or m.startswith(p + ".")


def assign(libs, m):
    best, size = None, -1
    for n, e in libs.items():
        for p in e.get("modules", []):
            if pattern_matches(p, m) and len(p.rstrip("*")) > size:
                best, size = n, len(p.rstrip("*"))
    return best


def closure(libs, n):
    seen, todo = set(), list(libs[n].get("depends", []))
    while todo:
        d = todo.pop()
        if d not in seen and d in libs:
            seen.add(d)
            todo += libs[d].get("depends", [])
    return seen


def edge_rule(libs, a, b):
    """The rules an import from declared library a into b breaks (a != b)."""
    ta, tb = libs[a]["tier"], libs[b]["tier"]
    out = []
    if tb == "orbit":
        if b not in libs[a].get("inputs", []):
            out.append("undeclared-orbit")
    elif ta == "orbit":
        out.append("orbit-imports-hub")
    elif ta in THEORY and tb == "outside":
        out.append("into-outside")
    elif ta in RANK and tb in RANK and (ta == "general" or RANK[tb] > RANK[ta]):
        out.append("upward")
    if not out and "depends" in libs[a] and tb != "orbit" and b not in closure(libs, a):
        out.append("undeclared-dep")
    return out


def sccs(nodes, edges):
    """Tarjan: the strongly connected components of size > 1 (or with a self-loop)."""
    index, low, stack, on, out, k = {}, {}, [], set(), [], [0]

    def visit(v):
        index[v] = low[v] = k[0]
        k[0] += 1
        stack.append(v)
        on.add(v)
        for w in sorted(edges.get(v, ())):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1:
                out.append(sorted(comp))

    sys.setrecursionlimit(10000)
    for v in sorted(nodes):
        if v not in index:
            visit(v)
    return out


def shortest_cycle(comp, edges):
    """A shortest cycle inside a strongly connected component, as a list of its nodes."""
    best = None
    inside = set(comp)
    for s in sorted(comp):
        prev, frontier, found = {s: None}, [s], None
        while frontier and found is None:
            nxt = []
            for v in frontier:
                for w in sorted(edges.get(v, ())):
                    if w == s:
                        found = v
                        break
                    if w in inside and w not in prev:
                        prev[w] = v
                        nxt.append(w)
                if found is not None:
                    break
            frontier = nxt
        if found is not None:
            path, v = [], found
            while v is not None:
                path.append(v)
                v = prev[v]
            path.reverse()
            if best is None or len(path) < len(best):
                best = path
    return best


# ------------------------------------------------------------------ the gate
def run(hub, tiers_path):
    """{config: [...], violations: [ {rule, from, to, module, file, line, imports} ], stats}."""
    libs, config = load_tiers(tiers_path)
    pkgs, problems = packages(hub)
    config += problems
    index = {}
    for p in pkgs:
        for m, v in modules(hub, p).items():
            if m in index and index[m][3] != v[3]:
                config.append("module %s defined twice: %s and %s" % (m, index[m][3], v[3]))
            index[m] = v
    owner = {}
    viol = []
    for m, (lib, scaffold, strict, rel) in index.items():
        mirror = strict + m[len(lib):] if scaffold and m.startswith(lib) else m
        owner[m] = assign(libs, mirror)
        if owner[m] is None:
            viol.append({"rule": "undeclared-module", "from": "(%s)" % lib, "to": "", "module": m,
                         "file": rel, "line": 0, "imports": ""})
    graph = collections.defaultdict(set)
    witness = {}
    n_imports = 0
    for m in sorted(index):
        lib, scaffold, strict, rel = index[m]
        with open(os.path.join(hub, rel), encoding="utf-8", errors="replace") as f:
            imps = header_imports(f.read())
        for line, imp in imps:
            n_imports += 1
            rec = {"module": m, "file": rel, "line": line, "imports": imp}
            if imp not in index:
                if imp.split(".")[0] not in EXTERNAL:
                    viol.append(dict(rec, rule="unresolved", **{"from": owner[m] or "(%s)" % lib, "to": ""}))
                continue
            if not scaffold and index[imp][1]:
                viol.append(dict(rec, rule="strict-imports-scaffold", **{"from": owner[m] or lib, "to": index[imp][0]}))
            a, b = owner[m], owner[imp]
            if a is None or b is None or a == b:
                continue
            if m in (lib, strict):
                # A lakefile library's root module aggregates its whole lean_lib, which today spans
                # tiers; after the move each library has its own root. Reported, kept out of the graph.
                viol.append(dict(rec, rule="root-aggregator", **{"from": a, "to": b}))
                continue
            graph[a].add(b)
            witness.setdefault((a, b), rec)
            for rule in edge_rule(libs, a, b):
                viol.append(dict(rec, rule=rule, **{"from": a, "to": b}))
    for comp in sccs(set(libs) | set(graph), graph):
        cyc = shortest_cycle(comp, graph)
        steps = ["%s -> %s (%s:%d)" % (x, y, witness[(x, y)]["file"], witness[(x, y)]["line"])
                 for x, y in zip(cyc, cyc[1:] + cyc[:1])]
        viol.append({"rule": "cycle", "from": ", ".join(comp), "to": "", "module": "", "file": "",
                     "line": 0, "imports": "", "witness": steps})
    stats = {"packages": pkgs, "modules": len(index), "imports": n_imports,
             "libraries": {n: sum(1 for m in owner if owner[m] == n) for n in libs},
             "edges": {a: sorted(bs) for a, bs in sorted(graph.items())}}
    return {"config": config, "violations": viol, "stats": stats}


def render(res, show_all=False, limit=3):
    lines = []
    st = res["stats"]
    lines.append("import-gate: %d packages (%s), %d modules, %d header imports"
                 % (len(st["packages"]), ", ".join(st["packages"]), st["modules"], st["imports"]))
    for c in res["config"]:
        lines.append("CONFIG  %s" % c)
    groups = collections.OrderedDict()
    for v in sorted(res["violations"], key=lambda v: (v["rule"], v["from"], v["to"], v["file"], v["line"])):
        groups.setdefault((v["rule"], v["from"], v["to"]), []).append(v)
    for (rule, a, b), vs in groups.items():
        if rule == "cycle":
            for v in vs:
                lines.append("%-24s {%s}; a shortest one:" % (rule, v["from"]))
                lines += ["    " + w for w in v["witness"]]
            continue
        head = "%s -> %s" % (a, b) if b else a
        noun = "module" if rule == "undeclared-module" else "import"
        lines.append("%-24s %-44s %4d %s%s" % (rule, head, len(vs), noun, "" if len(vs) == 1 else "s"))
        for v in (vs if show_all else vs[:limit]):
            lines.append("    %s:%d  %s%s" % (v["file"], v["line"], "import " if v["imports"] else "",
                                             v["imports"] or v["module"]))
        if not show_all and len(vs) > limit:
            lines.append("    ... %d more (--all)" % (len(vs) - limit))
    by_rule = collections.Counter(v["rule"] for v in res["violations"])
    lines.append("import-gate: %d violation%s%s%s" % (
        len(res["violations"]), "" if len(res["violations"]) == 1 else "s",
        (" (" + ", ".join("%s %d" % kv for kv in sorted(by_rule.items())) + ")") if by_rule else "",
        ", %d config error%s" % (len(res["config"]), "" if len(res["config"]) == 1 else "s") if res["config"] else ""))
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("mode", choices=("report", "check"))
    ap.add_argument("--hub", default=os.environ.get("LEANARTICLES_ROOT", ROOT))
    ap.add_argument("--tiers", default=None, help="default: <hub>/tools/import_tiers.toml")
    ap.add_argument("--all", action="store_true", help="list every violating import, not three per group")
    ap.add_argument("--json", default=None, help="also write the full result as JSON to this file")
    a = ap.parse_args(argv)
    tiers = a.tiers or os.path.join(a.hub, "tools", "import_tiers.toml")
    res = run(a.hub, tiers)
    print(render(res, show_all=a.all))
    if a.json:
        with open(a.json, "w", encoding="utf-8") as f:
            json.dump(res, f, indent=1, sort_keys=True)
    if a.mode == "report":
        print("import-gate: REPORT mode (T-arch-import-gate): findings are the migration worklist, exit 0")
        return 0
    bad = len(res["violations"]) + len(res["config"])
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
