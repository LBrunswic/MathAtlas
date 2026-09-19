#!/usr/bin/env python3
"""Every Lean dependency is registered, and every register row is a real dependency.

    python3 tools/deps_register.py   # exit 1 on a lakefile require or a port with no DEPS row,
                                     # or a live-dep row with no require

Reads `lean/lakefile.toml` (`[[require]] name = ...`), `lean/deps/ports/*` and
`registers/DEPS.md`'s table (`| name | upstream | rev | toolchain | license | used by | status |`).
Status vocabulary: live-dep · vendored-slice · reference · to-survey · rejected. A `live-dep`
row needs a matching `[[require]]`; a `vendored-slice` row needs `lean/deps/ports/<name>`;
mathlib is always required. Exit 2 if the lakefile is missing (before Phase 1 the library is a
submodule whose lakefile is read in place).
"""
import os
import re
import sys
import tomllib

ROOT = os.environ.get("LEANARTICLES_ROOT") or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATUSES = {"live-dep", "vendored-slice", "reference", "to-survey", "rejected"}


def table_rows(path):
    rows = []
    for line in open(path, encoding="utf-8"):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if not cells or cells[0] in ("name", "") or set(cells[0]) <= {"-", ":"}:
            continue
        rows.append(cells)
    return rows


def main():
    lake = os.path.join(ROOT, "lean", "lakefile.toml")
    if not os.path.exists(lake):
        print("deps_register: FAIL no %s" % lake)
        return 2
    with open(lake, "rb") as fh:
        reqs = {r["name"] for r in tomllib.load(fh).get("require", [])}
    ports = set()
    pd = os.path.join(ROOT, "lean", "deps", "ports")
    if os.path.isdir(pd):
        ports = set(os.listdir(pd))
    reg = os.path.join(ROOT, "registers", "DEPS.md")
    rows = table_rows(reg) if os.path.exists(reg) else []
    fail = 0
    by = {}
    for r in rows:
        if len(r) < 7:
            print("deps_register: FAIL short row: %s" % " | ".join(r))
            fail += 1
            continue
        name, status = r[0].strip("`"), r[6]
        if status not in STATUSES:
            print("deps_register: FAIL %s: status %r not in %s" % (name, status, sorted(STATUSES)))
            fail += 1
        by[name] = status
        if status == "live-dep" and name not in reqs:
            print("deps_register: FAIL %s is live-dep in DEPS.md but not required by the lakefile" % name)
            fail += 1
        if status == "vendored-slice" and name not in ports:
            print("deps_register: FAIL %s is vendored-slice in DEPS.md but lean/deps/ports/%s is absent" % (name, name))
            fail += 1
    for name in sorted(reqs):
        if by.get(name) != "live-dep":
            print("deps_register: FAIL lakefile requires %s with no live-dep row in DEPS.md" % name)
            fail += 1
    for name in sorted(ports):
        if by.get(name) != "vendored-slice":
            print("deps_register: FAIL lean/deps/ports/%s has no vendored-slice row in DEPS.md" % name)
            fail += 1
    if fail:
        return 1
    print("deps_register: %d requires, %d ports, %d rows agree" % (len(reqs), len(ports), len(rows)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
