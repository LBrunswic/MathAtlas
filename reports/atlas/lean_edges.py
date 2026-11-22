#!/usr/bin/env python3
"""The atlas's Lean overlay: the Lean edges between a paper's labels, each with its witness.

    python3 lean_edges.py facts [PKG ...]   # RUNS LEAN: lean/facts-<pkg>.json, a local cache
    python3 lean_edges.py edges [PKG ...]   # no Lean: lean/edges-<paper>.json, committed
    python3 lean_edges.py status            # is each edge file current?

`facts` feeds `lean_facts.lean`, behind one `import` per library of the package's lakefile, to
`lake env lean --stdin` inside the package: it reads the package's built oleans and writes only
under reports/atlas/lean/. It never builds, and it refuses to start while a `lean` or `lake`
process is already working in that package. Each facts file records the package commit it was
read at, whether the package had uncommitted changes, and a fingerprint of the package's olean
hashes, so a later rebuild of the package shows up as a stale overlay on the page.

`edges` is `tools/doubledag.py`'s coupling, imported rather than re-implemented: `load` and
`build` (principal projection, shortest witnesses, edge kinds), plus the flat projection's counts
beside it. It reads the cached facts and the *current* ledgers, so it is cheap and is the target
to rerun when only a ledger has moved. Given package names it rewrites only those packages' papers,
so a refresh that skipped a busy package does not couple that package's older facts with a ledger
that has since moved (its edge file stays as it was, and the page keeps calling it stale).

The default `make` never comes here for Lean: build.py reads the committed edge files and
`freshness()` compares them with the ledgers and packages as they are now.
"""
import glob
import hashlib
import json
import os
import subprocess
import sys
import tomllib

sys.dont_write_bytecode = True   # nothing written beside the sources, here or in tools/

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OUT = os.path.join(HERE, "lean")
sys.path.insert(0, os.path.join(ROOT, "tools"))
import doubledag as dd  # noqa: E402

KINDS = ["both", "lean-only", "tex-only", "tex-only-unformalized", "twin", "both-unformalized"]


# ----------------------------------------------------------------- the hub --
def ledgered():
    """Every paper with a generated ledger, sorted."""
    return sorted(os.path.basename(os.path.dirname(os.path.dirname(p)))
                  for p in glob.glob(os.path.join(ROOT, "papers", "*", "ledger", "ledger.json")))


def home(slug):
    """(ledger.json, package dir or None, paper map or None) for a paper, as doubledag reads it."""
    ledger, facts, pmap = dd.paper_paths(os.path.join(ROOT, "papers", slug))
    pkg = os.path.dirname(os.path.dirname(facts)) if facts else None
    return ledger, pkg, pmap


def libs(pkg):
    """[(lib name, srcDir)] from the package's lakefile.toml, in file order."""
    lf = os.path.join(pkg, "lakefile.toml")
    if not os.path.exists(lf):
        return []
    cfg = tomllib.load(open(lf, "rb"))
    return [(l["name"], l.get("srcDir", ".")) for l in cfg.get("lean_lib", [])]


def strict_libs(slug):
    cfg = tomllib.load(open(os.path.join(ROOT, "papers", slug, "ledger", "ledger.toml"), "rb"))
    return cfg.get("lean", {}).get("strict", [])


def packages():
    """{package dir: [papers]} for every package that declares the strict library its ledgers name."""
    out = {}
    for slug in ledgered():
        _, pkg, _ = home(slug)
        if pkg and set(strict_libs(slug)) <= {n for n, _ in libs(pkg)}:
            out.setdefault(pkg, []).append(slug)
    return dict(sorted(out.items()))


def git(*args):
    r = subprocess.run(["git", "-C", ROOT] + list(args), capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def package_commit(pkg):
    return git("log", "-1", "--format=%H", "--", os.path.relpath(pkg, ROOT))


def olean_fingerprint(pkg):
    """sha256 over the package's own `.olean.hash` files: it moves exactly when the package is rebuilt."""
    base = os.path.join(pkg, ".lake", "build", "lib", "lean")
    if not os.path.isdir(base):
        return None
    h = hashlib.sha256()
    files = []
    for name, _ in libs(pkg):
        files += glob.glob(os.path.join(base, name + ".olean.hash"))
        files += glob.glob(os.path.join(base, name, "**", "*.olean.hash"), recursive=True)
    for f in sorted(set(files)):
        h.update(os.path.relpath(f, base).encode() + b"\0" + open(f, "rb").read() + b"\0")
    return h.hexdigest()


def coupling_inputs(ledger):
    """sha256 of what the coupling reads from a ledger: labels, declarations, references, twins."""
    rows = json.load(open(ledger, encoding="utf-8"))["statements"]
    key = [[r["label"], r.get("decls") or [], r.get("deps") or [], r.get("twin") or "",
            r.get("twin_of") or ""] for r in rows]
    return hashlib.sha256(json.dumps(key, ensure_ascii=False).encode()).hexdigest()


def facts_path(pkg):
    return os.path.join(OUT, "facts-%s.json" % os.path.basename(pkg))


def edges_path(slug):
    return os.path.join(OUT, "edges-%s.json" % slug)


# ------------------------------------------------------------------- facts --
def busy(pkg):
    """pids of `lean`/`lake` processes whose working directory is inside the package."""
    out = []
    pkg = os.path.realpath(pkg)
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            comm = open("/proc/%s/comm" % pid).read().strip()
            cwd = os.readlink("/proc/%s/cwd" % pid)
        except OSError:
            continue
        if comm in ("lean", "lake") and (cwd == pkg or cwd.startswith(pkg + os.sep)):
            out.append(int(pid))
    return sorted(out)


def selected(names):
    """The packages of `packages()` named on the command line (all of them when none is)."""
    pk = packages()
    todo = [p for p in pk if not names or os.path.basename(p) in names]
    if names and len(todo) != len(set(names)):
        sys.exit("lean_edges: unknown package among %s (known: %s)"
                 % (names, ", ".join(os.path.basename(p) for p in pk)))
    return todo


def cmd_facts(names):
    todo = selected(names)
    body = open(os.path.join(HERE, "lean_facts.lean"), encoding="utf-8").read()
    os.makedirs(OUT, exist_ok=True)
    bad = 0
    for pkg in todo:
        name = os.path.basename(pkg)
        b = busy(pkg)
        if b:
            print("lean_edges: %s SKIPPED: Lean processes %s are working in it" % (name, b))
            bad = 1
            continue
        roots = [n for n, _ in libs(pkg)]
        out = facts_path(pkg)
        tmp = out + ".part"
        src = "".join("import %s\n" % r for r in roots) + body
        env = dict(os.environ, ATLAS_ROOTS=",".join(roots), ATLAS_OUT=tmp)
        r = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=pkg, input=src, text=True,
                           capture_output=True, env=env, timeout=3600)
        if r.returncode != 0 or not os.path.exists(tmp):
            print("lean_edges: %s FAILED (exit %d)\n%s" % (name, r.returncode, (r.stdout + r.stderr)[-3000:]))
            bad = 1
            continue
        F = json.load(open(tmp, encoding="utf-8"))
        os.remove(tmp)
        rel = os.path.relpath(pkg, ROOT)
        F["extracted"] = {"package": name, "commit": package_commit(pkg),
                          "dirty": bool(git("status", "--porcelain", "--", rel)),
                          "oleans": olean_fingerprint(pkg), "libs": libs(pkg)}
        with open(out, "w", encoding="utf-8") as fh:
            json.dump(F, fh, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
            fh.write("\n")
        print("lean_edges: %s: %d declarations at %s%s" % (name, len(F["declarations"]),
              (F["extracted"]["commit"] or "?")[:7], " (+ uncommitted changes)" if F["extracted"]["dirty"] else ""))
    return bad


# ------------------------------------------------------------------- edges --
def where(pkg, libmap, module, line):
    """`lean-causal/scaffold/CausalScaffold/X.lean:72` for a module of the package."""
    root = module.split(".")[0]
    src = libmap.get(root, ".")
    path = os.path.normpath(os.path.join(os.path.basename(pkg), src, module.replace(".", "/") + ".lean"))
    return "%s:%d" % (path, line)


def dump(obj, path):
    """Deterministic, and one edge per line so that a refresh diffs edge by edge."""
    parts = []
    for k in sorted(obj):
        v = obj[k]
        if isinstance(v, list) and v:
            body = "[\n" + ",\n".join("  " + json.dumps(x, ensure_ascii=False, sort_keys=True) for x in v) + "\n ]"
        elif isinstance(v, dict) and k in ("decls", "principals"):
            body = "{\n" + ",\n".join("  %s: %s" % (json.dumps(kk, ensure_ascii=False),
                                                   json.dumps(v[kk], ensure_ascii=False)) for kk in sorted(v)) + "\n }" if v else "{}"
        else:
            body = json.dumps(v, ensure_ascii=False, sort_keys=True)
        parts.append(" %s: %s" % (json.dumps(k), body))
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("{\n" + ",\n".join(parts) + "\n}\n")


def cmd_edges(names):
    os.makedirs(OUT, exist_ok=True)
    pk = packages()
    for pkg in selected(names):
        slugs = pk[pkg]
        fp = facts_path(pkg)
        if not os.path.exists(fp):
            print("lean_edges: no facts for %s: run `make -C reports/atlas lean-facts`" % os.path.basename(pkg))
            continue
        F = json.load(open(fp, encoding="utf-8"))
        facts = F["declarations"]
        libmap = {n: s for n, s in F["extracted"]["libs"]}
        for slug in slugs:
            ledger, _, pmap = home(slug)
            rows, _ = dd.load(ledger, None, pmap)
            G = dd.build(rows, facts)
            flat = dd.build(rows, facts, flat=True)["summary"]
            principals = {n["label"]: n["principals"] for n in G["nodes"] if n["principals"]}
            names = set()
            for e in G["edges"]:
                names.update(e.get("witness") or [])
            for ps in principals.values():
                names.update(ps)
            # Every witness is re-checked against the facts it came from: it starts at a principal
            # of the source, ends at a principal of the target, and each step is a use.
            for e in G["edges"]:
                w = e.get("witness")
                if not w:
                    continue
                steps = all(b in facts[a].get("uses_value", []) or b in facts[a].get("uses_type", [])
                            for a, b in zip(w, w[1:]))
                if not (w[0] in principals.get(e["source"], ()) and w[-1] in principals.get(e["target"], ())
                        and steps):
                    sys.exit("lean_edges: %s: the witness of %s -> %s does not check" % (slug, e["source"], e["target"]))
            missing = sorted({d for r in rows for d in (r.get("decls") or []) if d not in facts})
            out = {
                "paper": slug,
                "package": os.path.basename(pkg),
                "projection": G["projection"],
                "generator": "reports/atlas/lean_edges.py edges: tools/doubledag.py build over "
                             "reports/atlas/lean/facts-%s.json" % os.path.basename(pkg),
                "extracted": {k: F["extracted"][k] for k in ("commit", "dirty", "oleans")},
                "facts": {"declarations": len(facts), "modules": F["modules"], "roots": F["roots"]},
                "ledger_inputs": coupling_inputs(ledger),
                "summary": G["summary"],
                "flat": {k: flat[k] for k in ("edges_both", "edges_lean_only", "edges_tex_only")},
                "missing": missing,
                "principals": principals,
                "decls": {d: where(pkg, libmap, facts[d]["module"], facts[d]["line"]) for d in sorted(names)},
                "edges": G["edges"],
            }
            dump(out, edges_path(slug))
            s = G["summary"]
            print("lean_edges: %s: %d labels with Lean; both %d, lean-only %d, tex-only %d, "
                  "tex-only-unformalized %d, twin %d; %d declarations missing from the environment"
                  % (slug, s["labels_with_lean"], s["edges_both"], s["edges_lean_only"], s["edges_tex_only"],
                     s["edges_tex_only_unformalized"], s["edges_twin"], len(missing)))
    return 0


# --------------------------------------------------------------- freshness --
def freshness(slug, E):
    """Why the committed edge file of a paper may no longer be what `make lean` would write."""
    ledger, pkg, _ = home(slug)
    why = []
    if coupling_inputs(ledger) != E["ledger_inputs"]:
        why.append("the ledger's labels, declarations or references changed since: run "
                   "make -C reports/atlas lean-edges")
    cur = olean_fingerprint(pkg) if pkg else None
    if cur is None:
        why.append("the package's build is not present on this host, so its freshness is unknown")
    elif cur != E["extracted"]["oleans"]:
        why.append("%s was rebuilt since the facts were read: run make -C reports/atlas lean"
                   % E["package"])
    return {"current": not why, "why": why, "commit_now": package_commit(pkg) if pkg else None}


def cmd_status():
    bad = 0
    for slug in ledgered():
        p = edges_path(slug)
        if not os.path.exists(p):
            continue
        f = freshness(slug, json.load(open(p, encoding="utf-8")))
        print("%-10s %s%s" % (slug, "current" if f["current"] else "STALE", "".join("\n  " + w for w in f["why"])))
        bad |= not f["current"]
    return bad


def main(argv):
    if not argv or argv[0] not in ("facts", "edges", "status"):
        print(__doc__)
        return 2
    if argv[0] == "facts":
        return cmd_facts(argv[1:])
    if argv[0] == "edges":
        return cmd_edges(argv[1:])
    return cmd_status()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
