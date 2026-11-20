#!/usr/bin/env python3
"""STORY.md is anchored: every fragment names something that exists, every anchor is told.

    python3 tools/story_lint.py --paper papers/<slug>   # exit 1 on any violation

`STORY.md` is the fresh story of the paper. A story fragment is a heading `## S-<slug>-NN`
(or `### S-...`) followed by a paragraph; each fragment must cite at least one ledger label
in backticks (`theo:universality`) or one Lean declaration (`EGF.main_universality`) that
`ledger/ledger.json` or `lean/docs/lean-facts.json` knows. Conversely every anchor declared
in `certificate/appendix.toml` (`decls = [...]`) must be cited by at least one fragment:
an anchor no fragment tells is an orphan of the story. Fragment ids must be consecutive.
Exit 2 if there is no STORY.md.
"""
import json
import os
import re
import sys
import tomllib

FRAG = re.compile(r"^#{2,3}\s+(S-[a-z0-9-]+-(\d+))\b(.*)$", re.M)   # a slug may hold hyphens
TICK = re.compile(r"`([^`\s]+)`")


def main():
    if "--paper" not in sys.argv:
        print(__doc__)
        return 2
    paper = sys.argv[sys.argv.index("--paper") + 1]
    slug = os.path.basename(os.path.normpath(paper))
    story_p = os.path.join(paper, "STORY.md")
    if not os.path.exists(story_p):
        print("story_lint: FAIL no STORY.md in %s" % paper)
        return 2
    story = open(story_p, encoding="utf-8").read()
    labels = set()
    lj = os.path.join(paper, "ledger", "ledger.json")
    if os.path.exists(lj):
        labels = {s["label"] for s in json.load(open(lj, encoding="utf-8"))["statements"]}
    decls = set()
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    facts = os.path.join(root, "lean", "docs", "lean-facts.json")
    if os.path.exists(facts):
        decls = set(json.load(open(facts, encoding="utf-8")).get("declarations", {}))
    anchors = []
    app = os.path.join(paper, "certificate", "appendix.toml")
    if os.path.exists(app):
        with open(app, "rb") as fh:
            cfg = tomllib.load(fh)
        for ch in cfg.get("chapter", []):
            ns = ch.get("namespace", "")
            for sec in ch.get("section", []):
                for d in sec.get("decls", []):
                    anchors.append(ns + "." + d if ns and "." not in d else d)
    fail = 0
    frags = list(FRAG.finditer(story))
    if not frags:
        print("story_lint: FAIL no fragment heading `## S-%s-NN` in STORY.md" % slug)
        fail += 1
    cited = set()
    for k, m in enumerate(frags):
        fid, num = m.group(1), int(m.group(2))
        if not fid.startswith("S-%s-" % slug):
            print("story_lint: FAIL %s: fragment id must start with S-%s-" % (fid, slug))
            fail += 1
        if num != k + 1:
            print("story_lint: FAIL %s: fragments must be numbered consecutively (expected %d)"
                  % (fid, k + 1))
            fail += 1
        end = frags[k + 1].start() if k + 1 < len(frags) else len(story)
        body = story[m.end():end]
        names = [t for t in TICK.findall(body)]
        known = [t for t in names if t in labels or t in decls
                 or any(t.endswith("." + a.split(".")[-1]) or a.endswith("." + t) for a in anchors)]
        if not known:
            print("story_lint: FAIL %s cites no ledger label and no known Lean declaration "
                  "(cited: %s)" % (fid, ", ".join(names[:5]) or "nothing"))
            fail += 1
        unknown = [t for t in names if ":" in t and t not in labels]
        for t in unknown:
            print("story_lint: FAIL %s cites `%s`, which is not a ledger label" % (fid, t))
            fail += 1
        cited.update(names)
    for a in anchors:
        short = a.split(".")[-1]
        if not any(c == a or c.endswith("." + short) or c == short for c in cited):
            print("story_lint: FAIL anchor %s is told by no fragment" % a)
            fail += 1
    if fail:
        return 1
    print("story_lint: %s — %d fragments, %d anchors, all anchored" % (slug, len(frags), len(anchors)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
