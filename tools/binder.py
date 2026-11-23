#!/usr/bin/env python3
"""Binders: each ledgered result of a paper bound to the ETT programme's three layers.

    python3 tools/binder.py check [SLUG...]   every binder resolves (default: every papers/*/certificate/binder.toml)
    python3 tools/binder.py status [SLUG...]  rows bound, and per layer how many are Lean-closed / targeted / open

A binder is papers/<slug>/certificate/binder.toml, authored by the programme-planner:

    [[bind]]
    label = "thm:..."                 # a row of papers/<slug>/ledger/ledger.json
    ett = ["Causal.foo", "T-abs-..."] # layer 1: the ETT theorem(s), as Lean names or programme targets
    localisation = ["rigid", ...]     # layer 2: the localisation properties, as programme/ladder.toml ids
                                      # ([[property]] or [[edge_hypothesis]] ids)
    note = "..."                      # how the paper's argument factors
    [[bind.geometric]]                # layer 3, one per model class
    model = "smooth-vacuum"           # minkowski | flat-gx | E_alpha | E_0 | C0 | lipschitz | smooth-vacuum | quasilinear | ...
    proves = ["rigid"]                # which localisation properties this lemma provides
    by = ["T-loc-...", "Causal.bar"]  # Lean names or programme targets

Every label, ladder id, Lean name and target id must resolve; every localisation property must be
provided by some geometric entry (or the row says `open_localisation = ["..."]` with a reason).
A Lean name resolves namespace-exactly, as in tools/ladder.py: it is the full name of a declaration
of lean-causal/Causal (namespace and section blocks read, comments blanked); a dotted suffix of a
declared name, or a declared name that is a suffix of it, is not enough.
"""
import glob
import json
import os
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import ladder as ld  # noqa: E402

PROGRAMME = os.path.join(ROOT, "programme", "roadmap.toml")


def binders(slugs=None):
    out = {}
    for f in sorted(glob.glob(os.path.join(ROOT, "papers", "*", "certificate", "binder.toml"))):
        slug = f.split(os.sep)[-3]
        if not slugs or slug in slugs:
            out[slug] = tomllib.load(open(f, "rb"))
    return out


def ref_ok(x, names, targets):
    """A programme target id, or a Lean full name of lean-causal/Causal (namespace-exact)."""
    return x in targets if x.startswith("T-") else ld.resolves(x, names)


def check(slug, b, names, ladder_ids, targets, edge_ids=frozenset()):
    """`ladder_ids`: the ladder's [[property]] ids; `edge_ids`: its [[edge_hypothesis]] ids, accepted as
    localisation, open_localisation and proves ids too (T-tool-ladder-edge-hypotheses)."""
    known = set(ladder_ids) | set(edge_ids)
    errs = []
    lp = os.path.join(ROOT, "papers", slug, "ledger", "ledger.json")
    if not os.path.exists(lp):
        return ["%s: a binder needs the paper's ledger (papers/%s/ledger/ledger.json)" % (slug, slug)]
    labels = {r["label"] for r in json.load(open(lp, encoding="utf-8"))["statements"]}
    seen = set()
    for r in b.get("bind", []):
        lab = r.get("label")
        tag = "%s %s" % (slug, lab)
        if lab not in labels:
            errs.append("%s: not a ledger label" % tag)
        if lab in seen:
            errs.append("%s: bound twice" % tag)
        seen.add(lab)
        if not r.get("ett"):
            errs.append("%s: no ETT theorem (layer 1)" % tag)
        for x in r.get("ett", []):
            if not ref_ok(x, names, targets):
                errs.append("%s: ett %s resolves to neither a Lean name nor a programme target" % (tag, x))
        provided = set()
        for g in r.get("geometric", []):
            if not g.get("model"):
                errs.append("%s: geometric entry without model" % tag)
            for p in g.get("proves", []):
                if p not in known:
                    errs.append("%s: geometric proves %r, not a ladder property or edge hypothesis" % (tag, p))
                provided.add(p)
            for x in g.get("by", []):
                if not ref_ok(x, names, targets):
                    errs.append("%s: geometric by %s resolves to neither a Lean name nor a programme target" % (tag, x))
        for p in r.get("localisation", []):
            if p not in known:
                errs.append("%s: localisation %r is not a ladder property or edge hypothesis" % (tag, p))
            elif p not in provided and p not in r.get("open_localisation", []):
                errs.append("%s: localisation %r is provided by no geometric entry and not declared open" % (tag, p))
    return errs


def main(argv):
    if not argv:
        sys.exit(__doc__)
    cmd, slugs = argv[0], argv[1:]
    bs = binders(slugs)
    names = ld.lean_names()   # the declarations' full names
    lad = ld.load()
    ladder_ids = {p["id"] for p in lad.get("property", [])}
    edge_ids = {e["id"] for e in lad.get("edge_hypothesis", []) if e.get("id")}
    targets = {t["id"] for t in tomllib.load(open(PROGRAMME, "rb")).get("target", [])} if os.path.exists(PROGRAMME) else set()
    if cmd == "check":
        errs = [e for s, b in bs.items() for e in check(s, b, names, ladder_ids, targets, edge_ids)]
        for e in errs:
            print("binder: " + e)
        print("binder: %d binder(s), %s" % (len(bs), "%d violation(s)" % len(errs) if errs else "all links resolve"))
        sys.exit(1 if errs else 0)
    if cmd == "status":
        for s, b in bs.items():
            rows = b.get("bind", [])
            lean = lambda xs: all(not x.startswith("T-") for x in xs) and bool(xs)
            print("%s: %d rows bound; layer 1 in Lean %d; layer 3 in Lean %d" % (
                s, len(rows), sum(1 for r in rows if lean(r.get("ett", []))),
                sum(1 for r in rows if r.get("geometric") and all(lean(g.get("by", [])) for g in r["geometric"]))))
        return
    sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
