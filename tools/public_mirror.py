#!/usr/bin/env python3
"""The public mirror of this hub: LBrunswic/MathAtlas (DEC-203, DEC-207).

    python3 tools/public_mirror.py build [DIR]   # a filtered clone of main in DIR, verified; pushes nothing
    python3 tools/public_mirror.py push  [DIR]   # build, then push main and gh-pages to the mirror
    python3 tools/public_mirror.py rules         # print the strip rules

The private repository and the loops are untouched: the mirror is rebuilt from scratch on every
run, from a fresh clone outside the Dropbox tree, and never edited by hand. Its `main` is this
repository's `main` with every path matching `STRIP` removed from the whole history
(`git filter-repo --invert-paths`). Filtering is deterministic, so a run with unchanged rules
re-creates the same commits and `main` is pushed as a fast-forward. A change to `STRIP` rewrites
the mirror's history, and the push is then refused unless `--rewrite` is given. Its `gh-pages` is
one commit holding the atlas (`reports/atlas/atlas.html` as `index.html`), force-pushed each run;
GitHub Pages serves it.

What is stripped is the third-party material: the archived sources of every paper (their `.md`
notes stay, as pointers), the PDFs of the BBS references and the hub's reference texts and PDFs
(DEC-203), plus, by DEC-207, the full texts of the external papers in their `legacy/` (their
`MANIFEST.json` stays, naming each source) and the archived sources inside the 2026 Syracuse
programme snapshot. The author's own drafts, the programme and `lean/` are published (DEC-207).

Needs `git filter-repo` (on PATH, or its path in $GIT_FILTER_REPO) and push rights on the mirror
through the host's git credentials. Never part of a gate.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HUB = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MIRROR = "git@github.com:LBrunswic/MathAtlas.git"
ATLAS = "reports/atlas/atlas.html"

#: Paths removed from every commit. A `.md` inside a `sources/` folder is a note, kept as a pointer.
STRIP = (
    r"^papers/[^/]+/sources/(?!.*\.md$)",
    r"^papers/syracuse/programme-2026/(.+/)?sources/(?!.*\.md$)",
    r"^papers/bbs/references/[^/]+/pdf/",
    r"^references/[^/]+/(text|pdf)/",
    r"^papers/(barbot|bbs|sbierski-mghd|ers-predictability|benzecri)/legacy/(orig|labeled)/",
)


def stripped(path):
    return any(re.search(r, path) for r in STRIP)


def run(*cmd, cwd=None, capture=False):
    r = subprocess.run(cmd, cwd=cwd, check=True, text=True,
                       stdout=subprocess.PIPE if capture else None)
    return r.stdout if capture else None


def build(out):
    if os.path.exists(out):
        shutil.rmtree(out)
    run("git", "clone", "-q", "--no-local", "--single-branch", "--branch", "main", HUB, out)
    fr = os.environ.get("GIT_FILTER_REPO") or shutil.which("git-filter-repo")
    if not fr:
        sys.exit("public_mirror: git filter-repo not found (set $GIT_FILTER_REPO)")
    args = [fr, "--force", "--invert-paths"]
    for r in STRIP:
        args += ["--path-regex", r]
    run(*args, cwd=out)
    paths = set(run("git", "log", "--format=", "--name-only", "main", cwd=out, capture=True).split())
    bad = sorted(p for p in paths if stripped(p))
    if bad:
        sys.exit("public_mirror: FAIL %d stripped path(s) survive, e.g. %s" % (len(bad), bad[0]))
    n = run("git", "rev-list", "--count", "main", cwd=out, capture=True).strip()
    print("public_mirror: %s commits, %d paths in history, none stripped survives" % (n, len(paths)))
    return out


def pages(out):
    """The gh-pages commit: the atlas of the mirror's tip as index.html."""
    site = tempfile.mkdtemp(prefix="mathatlas-pages-")
    shutil.copy(os.path.join(out, ATLAS), os.path.join(site, "index.html"))
    open(os.path.join(site, ".nojekyll"), "w").close()
    tip = run("git", "rev-parse", "--short", "main", cwd=out, capture=True).strip()
    run("git", "init", "-q", "-b", "gh-pages", cwd=site)
    run("git", "add", "-A", cwd=site)
    who = [run("git", "-C", HUB, "config", k, capture=True).strip() for k in ("user.name", "user.email")]
    run("git", "-c", "user.name=" + who[0], "-c", "user.email=" + who[1], "commit", "-q",
        "-m", "atlas at %s" % tip, cwd=site)
    return site


def push(out, rewrite):
    run("git", "push", *(["--force"] if rewrite else []), MIRROR, "main:main", cwd=out)
    site = pages(out)
    run("git", "push", "--force", MIRROR, "gh-pages:gh-pages", cwd=site)
    shutil.rmtree(site)


def main(argv):
    cmd = argv[0] if argv else "build"
    out = next((a for a in argv[1:] if not a.startswith("--")), "/tmp/mathatlas-mirror")
    if cmd == "rules":
        print("\n".join(STRIP))
    elif cmd == "build":
        build(out)
    elif cmd == "push":
        push(build(out), "--rewrite" in argv)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
