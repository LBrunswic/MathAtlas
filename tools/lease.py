#!/usr/bin/env python3
"""Leases: how /atlas-team and /ett-programme share one checkout without stepping on each other.

    python3 tools/lease.py take LOOP PID PATH...   claim paths (a package dir, a paper dir, a file); refuses an overlap with a live lease
    python3 tools/lease.py drop LOOP               release every path LOOP holds
    python3 tools/lease.py show                    the live leases
    python3 tools/lease.py tree LOOP               every changed path in `git status` is held by LOOP or by another live loop;
                                                   exit 1 on a change nobody holds (a human, or a dead loop's leftovers)
    python3 tools/lease.py mine LOOP               the changed paths LOOP holds (what LOOP may `git commit --only`)

A lease is `.leases/<LOOP>.json` = {"pid": int, "paths": [...]} (git-ignored). It is live while its
pid is alive, so a crashed loop releases itself. Paths are repository-relative prefixes; `lean-causal`
holds everything under it. Both loops commit with `git commit --only $(lease.py mine LOOP)` so that
neither commits the other's work, and never run `git checkout`/`stash` on paths they do not hold.
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIR = os.path.join(ROOT, ".leases")


def alive(pid):
    try:
        os.kill(int(pid), 0)
        return True
    except (OSError, ValueError):
        return False


def leases():
    out = {}
    if os.path.isdir(DIR):
        for f in sorted(os.listdir(DIR)):
            if f.endswith(".json"):
                d = json.load(open(os.path.join(DIR, f)))
                if alive(d.get("pid")):
                    out[f[:-5]] = d
    return out


def norm(p):
    return p.strip("/").rstrip("/")


def covers(prefix, path):
    prefix, path = norm(prefix), norm(path)
    return path == prefix or path.startswith(prefix + "/")


def overlap(a, b):
    return covers(a, b) or covers(b, a)


def changed():
    out = subprocess.run(["git", "-C", ROOT, "status", "--porcelain", "--untracked-files=all"],
                         capture_output=True, text=True).stdout.splitlines()
    paths = []
    for l in out:
        p = l[3:]
        if " -> " in p:
            a, b = p.split(" -> ")
            paths += [a, b]
        else:
            paths.append(p)
    return [p.strip('"') for p in paths]


def holder(path, ls):
    for loop, d in ls.items():
        if any(covers(p, path) for p in d["paths"]):
            return loop
    return None


def main(argv):
    if not argv:
        sys.exit(__doc__)
    cmd = argv[0]
    ls = leases()
    if cmd == "take":
        loop, pid, paths = argv[1], int(argv[2]), [norm(p) for p in argv[3:]]
        for other, d in ls.items():
            if other == loop:
                continue
            for p in paths:
                for q in d["paths"]:
                    if overlap(p, q):
                        sys.exit("lease: %s is held by %s (%s)" % (p, other, q))
        os.makedirs(DIR, exist_ok=True)
        mine = ls.get(loop, {"paths": []})["paths"] if loop in ls else []
        json.dump({"pid": pid, "paths": sorted(set(mine + paths))}, open(os.path.join(DIR, loop + ".json"), "w"))
        print("lease: %s holds %s" % (loop, ", ".join(sorted(set(mine + paths)))))
        return
    if cmd == "drop":
        f = os.path.join(DIR, argv[1] + ".json")
        if os.path.exists(f):
            os.remove(f)
        print("lease: %s released" % argv[1])
        return
    if cmd == "show":
        for loop, d in ls.items():
            print("%s (pid %s): %s" % (loop, d["pid"], ", ".join(d["paths"])))
        return
    if cmd in ("tree", "mine"):
        loop = argv[1]
        ch = [p for p in changed() if not covers(".leases", p)]
        if cmd == "mine":
            for p in ch:
                if holder(p, {loop: ls[loop]} if loop in ls else {}) == loop:
                    print(p)
            return
        stray = [p for p in ch if holder(p, ls) is None]
        for p in stray:
            print("lease: %s is changed and held by no live loop" % p)
        sys.exit(1 if stray else 0)
    sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
