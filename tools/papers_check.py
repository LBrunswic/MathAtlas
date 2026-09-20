#!/usr/bin/env python3
"""Run every paper's gates, in hub.toml's order.

    python3 tools/papers_check.py [--paper <slug>]   # exit 1 if any gate of any paper fails

Per paper (a directory under papers/ with ledger/ledger.toml): legacy-frozen, ledger check,
story lint, no-legacy-prose. A paper listed in hub.toml `[papers.blocked]` is skipped with a
loud BLOCKED line naming its open question (tools/registers.py checks that question is still
OPEN). A paper directory with no ledger.toml is a failure: a paper nobody counts is worse than a
red one.
"""
import os
import subprocess
import sys
import tomllib

ROOT = os.environ.get("LEANARTICLES_ROOT") or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOOLS = os.path.dirname(os.path.abspath(__file__))


def run(name, cmd):
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    tail = (r.stdout.strip().split("\n") or [""])[-1]
    print("  %-16s %s  %s" % (name, "ok " if r.returncode == 0 else "FAIL", tail))
    if r.returncode != 0:
        for line in (r.stdout + r.stderr).strip().split("\n"):
            print("      " + line)
    return r.returncode == 0


def main():
    with open(os.path.join(ROOT, "hub.toml"), "rb") as fh:
        hub = tomllib.load(fh)
    order = hub["papers"]["order"]
    blocked = hub["papers"].get("blocked", {})
    only = sys.argv[sys.argv.index("--paper") + 1] if "--paper" in sys.argv else None
    found = sorted(d for d in os.listdir(os.path.join(ROOT, "papers"))
                   if os.path.isdir(os.path.join(ROOT, "papers", d)))
    slugs = [s for s in order if s in found] + [s for s in found if s not in order]
    fail = 0
    for slug in slugs:
        if only and slug != only:
            continue
        pdir = os.path.join("papers", slug)
        print("papers/%s" % slug)
        if slug in blocked:
            print("  BLOCKED on %s — gates not run" % blocked[slug])
            continue
        if not os.path.exists(os.path.join(ROOT, pdir, "ledger", "ledger.toml")):
            print("  FAIL no ledger/ledger.toml: this paper is not counted")
            fail += 1
            continue
        cfg = os.path.join(pdir, "ledger", "ledger.toml")
        ok = True
        ok &= run("legacy-frozen", ["python3", os.path.join(TOOLS, "legacy_check.py"), "--paper", pdir])
        ok &= run("ledger", ["python3", os.path.join(TOOLS, "ledger.py"), "-c", cfg, "check"])
        ok &= run("story", ["python3", os.path.join(TOOLS, "story_lint.py"), "--paper", pdir])
        ok &= run("no-legacy-prose", ["python3", os.path.join(TOOLS, "no_legacy_prose.py"), "--paper", pdir])
        # The double DAG, once the paper has one: its committed artifacts must be what a build
        # would write. A paper with no Lean yet has no doubledag/ and nothing to check.
        if os.path.isdir(os.path.join(ROOT, pdir, "doubledag")):
            ok &= run("doubledag", ["python3", os.path.join(TOOLS, "doubledag.py"), "check",
                                    "--paper", pdir])
        if not ok:
            fail += 1
    if fail:
        print("papers_check: %d paper(s) failing" % fail)
        return 1
    print("papers_check: all papers green")
    return 0


if __name__ == "__main__":
    sys.exit(main())
