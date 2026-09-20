#!/usr/bin/env python3
r"""The double DAG: the draft's statement graph and the Lean dependency graph, coupled.

    python3 tools/doubledag.py build  --paper papers/<slug> [-o out.json]
    python3 tools/doubledag.py build  --ledger L.json --facts F.json [--map paper-map.json]
    python3 tools/doubledag.py report --paper papers/<slug> [-o REPORT.md]
    python3 tools/doubledag.py edges  --paper ... --kind lean-only|tex-only|both [--limit N]
    python3 tools/doubledag.py dot    --paper ... -o coupled.dot
    python3 tools/doubledag.py check  --paper ...        # the committed artifacts are current

Two graphs over one mathematics.

  **The statement DAG** is read top-down off the draft: nodes are `\label`s, and `A -> B` when
  the statement of `A` or its proof invokes `B` (`tools/ledger.py`).
  **The Lean DAG** is read bottom-up off the compiled environment: nodes are declarations, and
  `d -> e` when `e` occurs in `d`'s type (`uses_type`) or in its proof term (`uses_value`).

They are coupled by the map `label -> declarations`. Projecting the Lean DAG onto labels through
that map is what makes the two comparable -- and doing it naively is what makes the comparison
useless: a helper lemma listed under two labels puts a Lean edge between them that no mathematics
justifies. LeanLink measured that on the GFN pair in 2026-09 and stopped there -- 190 of 600
mapped declarations claimed by more than one label, 228 Lean-only edges "mostly artefacts of
shared decls" (`~/Dropbox/LeanLink/evidence/dagcmp.py`). Over the whole 1,879-declaration map the
same naive walk gives 501 shared and 522 Lean-only edges.

So the projection goes through **principals**. Within a label's declarations, a declaration is
*subordinate* when another declaration of the same label transitively uses it; the rest are the
label's **principals** -- its assembly theorems, in the iceberg sense. A walk from `L`'s principals
stops when it reaches a principal of another label `M`, and that is the edge `L -> M`. A shared
helper is subordinate to both labels, so the walk passes through it instead of inventing an edge.
`--flat` computes the naive projection beside it, and the report prints both: the difference is
what the principal notion buys, measured rather than asserted.

Every edge of the coupled graph is then one of

  `both`       the draft cites it and the Lean proof term uses it
  `lean-only`  the Lean proof uses it and the draft never says so
  `tex-only`   the draft cites it and the Lean proof does not use it

and each disagreement is a question about the paper, not a defect of the tool. Which question is
`tools/dag_reconcile.py`'s business; nothing here asks a model anything.
"""
import argparse
import json
import os
import sys
import tomllib

ROOT = os.environ.get("LEANARTICLES_ROOT") or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


# ------------------------------------------------------------------ inputs --
def paper_paths(paper):
    """(ledger.json, lean-facts.json, map or None) for a hub paper directory."""
    cfg_p = os.path.join(paper, "ledger", "ledger.toml")
    with open(cfg_p, "rb") as fh:
        cfg = tomllib.load(fh)
    base = os.path.dirname(os.path.abspath(cfg_p))
    out = cfg.get("output", {})
    ledger = os.path.join(base, out.get("dir", "."), out.get("json", "ledger.json"))
    lean = cfg.get("lean", {})
    root = os.path.normpath(os.path.join(base, os.path.expanduser(lean.get("root", "")))) \
        if lean.get("root") else None
    facts = os.path.join(root, "docs", "lean-facts.json") if root else None
    pmap = os.path.join(root, lean["paper_map"]) if root and lean.get("paper_map") else None
    return os.path.normpath(ledger), facts, pmap


def load(ledger_p, facts_p, map_p=None):
    rows = json.load(open(ledger_p, encoding="utf-8"))["statements"]
    facts = json.load(open(facts_p, encoding="utf-8"))["declarations"] if facts_p and \
        os.path.exists(facts_p) else {}
    if map_p and os.path.exists(map_p):
        # The Lean library's own map owns the label -> declarations facts; where it speaks, it wins.
        m = {s["label"]: s for s in json.load(open(map_p, encoding="utf-8"))["statements"]}
        for r in rows:
            mm = m.get(r["label"])
            if mm and mm.get("decls"):
                r["decls"] = list(mm["decls"])
    return rows, facts


# -------------------------------------------------------------- the coupling --
def build(rows, facts, flat=False):
    """The coupled graph. Returns a dict ready to serialise."""
    by_label = {r["label"]: r for r in rows}
    owners = {}                                   # decl -> [labels]
    for r in rows:
        for d in r.get("decls") or []:
            owners.setdefault(d, []).append(r["label"])
    mapped = [d for d in owners if d in facts]
    idx = {d: i for i, d in enumerate(mapped)}

    def uses(d):
        f = facts.get(d)
        if not f:
            return ()
        return tuple(f.get("uses_value") or ()) + tuple(f.get("uses_type") or ())

    # reach_mapped[d] = bitmask of MAPPED declarations transitively reachable from d (not d).
    # One memoised pass over the whole environment; iterative, so a 5,700-node graph cannot
    # blow the stack, and cycle-safe (Lean's graph is acyclic, but a bad facts file is not).
    reach = {}
    for src in list(facts):
        if src in reach:
            continue
        stack = [(src, iter(uses(src)))]
        onstack = {src}
        acc = {src: 0}
        while stack:
            node, it = stack[-1]
            advanced = False
            for nxt in it:
                if nxt not in facts:
                    continue
                bit = (1 << idx[nxt]) if nxt in idx else 0
                if nxt in reach:
                    acc[node] |= reach[nxt] | bit
                    continue
                if nxt in onstack:            # a cycle: take what is known, do not recurse
                    acc[node] |= bit
                    continue
                stack.append((nxt, iter(uses(nxt))))
                onstack.add(nxt)
                acc[nxt] = 0
                advanced = True
                break
            if advanced:
                continue
            stack.pop()
            onstack.discard(node)
            reach[node] = acc.pop(node)
            if stack:
                parent = stack[-1][0]
                acc[parent] |= reach[node] | ((1 << idx[node]) if node in idx else 0)

    # principals: a declaration of L that no other declaration of L transitively uses
    principals, subordinates = {}, {}
    for r in rows:
        own = [d for d in (r.get("decls") or []) if d in facts]
        if not own:
            continue
        sub = []
        for d in own:
            others = 0
            for e in own:
                if e != d:
                    others |= reach.get(e, 0)
            if d in idx and (others >> idx[d]) & 1:
                sub.append(d)
        principals[r["label"]] = [d for d in own if d not in sub]
        subordinates[r["label"]] = sub

    # The stop set: which declarations end a walk, and for which label. Under `--flat` that is
    # every mapped declaration (LeanLink's baseline); by principals it is the principals alone.
    stop = {}
    if flat:
        for d, labs in owners.items():
            stop[d] = set(labs)
    else:
        for lab, ps in principals.items():
            for d in ps:
                stop.setdefault(d, set()).add(lab)

    # The walk is breadth-first so that the witness it records is a SHORTEST chain of
    # declarations from one of `lab`'s principals to the principal of another label. An edge a
    # reader cannot check is an assertion; the witness is what makes it checkable, and it is what
    # `tools/dag_reconcile.py` puts in front of a model.
    from collections import deque
    lean_edges, witness = {}, {}
    for lab, ps in principals.items():
        if not ps:
            continue
        seen = set(ps)
        parent = {d: None for d in ps}
        q = deque(ps)
        hit = {}
        while q:
            d = q.popleft()
            for u in uses(d):
                if u in seen or u not in facts:
                    continue
                seen.add(u)
                parent[u] = d
                other = stop.get(u, set()) - {lab}
                if other:
                    chain, x = [], u
                    while x is not None:
                        chain.append(x)
                        x = parent[x]
                    chain.reverse()
                    for m in other:
                        hit.setdefault(m, chain)
                else:
                    q.append(u)
        lean_edges[lab] = sorted(hit)
        witness[lab] = hit

    has_decls = {lab for lab, ps in principals.items() if ps}
    # A body statement and its appendix full form are the same mathematics said twice. The ledger
    # carries that as a dependency edge, and the Lean cannot match it: a twin pair shares its whole
    # declaration list, so neither ever reaches the other's principals. It is a RESTATEMENT, not a
    # dependency, and counting it as a disagreement would put every twin in the tex-only column.
    twin_of = {}
    for r in rows:
        for t in (r.get("twin"), r.get("twin_of")):
            if t:
                twin_of.setdefault(r["label"], set()).add(t)
    edges = []
    for r in rows:
        lab = r["label"]
        tex = [d for d in (r.get("deps") or []) if d in by_label and d != lab]
        lean = lean_edges.get(lab, [])
        for t in sorted(set(tex) | set(lean)):
            if t in twin_of.get(lab, ()):  # or lab in twin_of.get(t, ()) -- symmetric below
                kind = "twin"
            elif lab in twin_of.get(t, ()):
                kind = "twin"
            elif lab not in has_decls or t not in has_decls:
                kind = "both-unformalized" if t in lean and t in tex else (
                    "lean-only" if t in lean else "tex-only-unformalized")
            elif t in tex and t in lean:
                kind = "both"
            elif t in lean:
                kind = "lean-only"
            else:
                kind = "tex-only"
            e = {"source": lab, "target": t, "kind": kind}
            w = witness.get(lab, {}).get(t)
            if w:
                e["witness"] = w
            edges.append(e)

    nodes = []
    for r in rows:
        lab = r["label"]
        nodes.append({
            "label": lab, "kind": r.get("kind"), "title": r.get("title"),
            "where": "%s:%d" % (r.get("file", "?"), r.get("line", 0)),
            "lean_stated": r.get("lean_stated"), "lean_proved": r.get("lean_proved"),
            "decls": list(r.get("decls") or []),
            "principals": principals.get(lab, []),
            "subordinates": subordinates.get(lab, []),
        })
    counts = {}
    for e in edges:
        counts[e["kind"]] = counts.get(e["kind"], 0) + 1
    return {
        "projection": "flat" if flat else "principal",
        "summary": {
            "labels": len(rows),
            "labels_with_lean": len(has_decls),
            "declarations_in_environment": len(facts),
            "declarations_mapped": len(owners),
            "declarations_missing_from_environment": sum(1 for d in owners if d not in facts),
            "declarations_shared_by_several_labels": sum(1 for ls in owners.values() if len(ls) > 1),
            "principals": sum(len(p) for p in principals.values()),
            "subordinates": sum(len(s) for s in subordinates.values()),
            "edges_both": counts.get("both", 0),
            "edges_lean_only": counts.get("lean-only", 0),
            "edges_tex_only": counts.get("tex-only", 0),
            "edges_tex_only_unformalized": counts.get("tex-only-unformalized", 0),
            "edges_twin": counts.get("twin", 0),
        },
        "nodes": nodes,
        "edges": edges,
    }


# ------------------------------------------------------------------ report --
def report(dd, flat=None):
    s = dd["summary"]
    L = []
    A = L.append
    A("# The double DAG")
    A("")
    A("Generated by `tools/doubledag.py`; **do not edit by hand**.")
    A("")
    A("The draft's statement graph and the Lean dependency graph, coupled by the map "
      "`label -> declarations` and compared edge by edge. The projection is by **principals**: "
      "within a label, a declaration another declaration of the same label transitively uses is "
      "*subordinate*, and a walk stops only at another label's principal, so a helper listed "
      "under two labels no longer fabricates an edge between them.")
    A("")
    A("| | |")
    A("|---|---:|")
    for k, v in s.items():
        A("| %s | %d |" % (k.replace("_", " "), v))
    A("")
    if flat:
        f = flat["summary"]
        A("## What the principal projection buys")
        A("")
        A("The same comparison with the naive projection -- a walk stopping at *any* declaration "
          "listed under another label -- beside it:")
        A("")
        A("| edges | principal | flat |")
        A("|---|---:|---:|")
        for k in ("edges_both", "edges_lean_only", "edges_tex_only"):
            A("| %s | %d | %d |" % (k.replace("edges_", "").replace("_", "-"), s[k], f[k]))
        A("")
        A("Read it as a trade, not a win: the naive projection agrees with %d of the draft's "
          "edges and adds %d of its own, the principal projection agrees with %d and adds %d. "
          "It keeps %.0f%% of the agreements and drops %.0f%% of the Lean-only edges, so each "
          "surviving disagreement is likelier to be about the mathematics than about the map."
          % (f["edges_both"], f["edges_lean_only"], s["edges_both"], s["edges_lean_only"],
             100.0 * s["edges_both"] / max(f["edges_both"], 1),
             100.0 * (f["edges_lean_only"] - s["edges_lean_only"]) / max(f["edges_lean_only"], 1)))
        A("")
    kinds = [("lean-only", "The Lean proof uses it; the draft never says so",
              "Either the draft omits a dependency it really has, or the Lean proof reaches for "
              "a step the paper takes for granted. `tools/dag_reconcile.py` asks which."),
             ("tex-only", "The draft cites it; the Lean proof term does not use it",
              "Either the reference is decorative, or the Lean statement is narrower than the "
              "paper's and does not need it -- which is the direction DEC-17 forbids."),
             ("tex-only-unformalized", "The draft cites it and one of the two ends has no Lean",
              "Nothing to compare yet; these disappear as the formalization advances."),
             ("twin", "A body statement and its appendix full form",
              "A restatement, not a dependency: the pair shares its whole declaration list, so "
              "neither can reach the other's principals. Excluded from the disagreements.")]
    for kind, title, note in kinds:
        rows = [e for e in dd["edges"] if e["kind"] == kind]
        A("## %s — %d" % (title, len(rows)))
        A("")
        A(note)
        A("")
        if not rows:
            A("*(none)*")
            A("")
            continue
        A("| from | to | witness (the declaration chain) |")
        A("|---|---|---|")
        for e in rows[:200]:
            w = e.get("witness") or []
            short = " → ".join("`%s`" % x.split(".")[-1] for x in (w[:1] + (["…"] if len(w) > 3 else []) + w[-2:] if len(w) > 3 else w))
            A("| `%s` | `%s` | %s |" % (e["source"], e["target"], short or "—"))
        if len(rows) > 200:
            A("")
            A("*(%d more in `doubledag.json`)*" % (len(rows) - 200))
        A("")
    multi = [n for n in dd["nodes"] if len(n["principals"]) > 1]
    A("## Labels with several principals — %d" % len(multi))
    A("")
    A("A label whose declarations have no single top: a multi-item statement, or a label that "
      "wants an assembly theorem. Sizing those is storytelling, i.e. the author's.")
    A("")
    if multi:
        A("| label | principals |")
        A("|---|---|")
        for n in multi[:60]:
            A("| `%s` | %s |" % (n["label"], ", ".join("`%s`" % p for p in n["principals"][:6])
                                 + (" +%d" % (len(n["principals"]) - 6) if len(n["principals"]) > 6 else "")))
    A("")
    return "\n".join(L) + "\n"


def to_dot(dd):
    color = {"both": "#2d6a4f", "lean-only": "#b35c00", "tex-only": "#9d0208",
             "tex-only-unformalized": "#cccccc", "twin": "#4361ee", "both-unformalized": "#cccccc"}
    style = {"both": "solid", "lean-only": "dashed", "tex-only": "dotted",
             "tex-only-unformalized": "dotted", "twin": "solid", "both-unformalized": "dotted"}
    L = ["digraph doubledag {", '  rankdir=BT; node [shape=box, style=filled, fontsize=9,',
         '    fontname="Helvetica", fillcolor="#ffffff"];']
    for n in dd["nodes"]:
        fill = "#b7e4c7" if n.get("lean_proved") == "closed" else (
            "#ffe08a" if n.get("principals") else "#ffffff")
        L.append('  "%s" [label="%s", fillcolor="%s"];'
                 % (n["label"], (n["label"] + "\\n" + (n["title"] or "")[:26]).replace('"', "'"), fill))
    for e in dd["edges"]:
        L.append('  "%s" -> "%s" [color="%s", style=%s];'
                 % (e["source"], e["target"], color[e["kind"]], style[e["kind"]]))
    L.append('  subgraph cluster_legend { label="edges"; fontsize=10; color="#cccccc";')
    L.append('    a [label="both"]; b [label="lean only"]; c [label="tex only"];')
    L.append('    a -> b [color="#b35c00", style=dashed]; b -> c [color="#9d0208", style=dotted]; }')
    L.append("}")
    return "\n".join(L) + "\n"


# --------------------------------------------------------------------- cli --
def resolve(a):
    if a.paper:
        ledger, facts, pmap = paper_paths(a.paper)
        return a.ledger or ledger, a.facts or facts, a.map or pmap
    if not (a.ledger and a.facts):
        sys.exit("doubledag: give --paper, or both --ledger and --facts")
    return a.ledger, a.facts, a.map


def out_paths(a):
    if a.paper:
        d = os.path.join(a.paper, "doubledag")
        return os.path.join(d, "doubledag.json"), os.path.join(d, "DOUBLEDAG.md"), \
            os.path.join(d, "coupled.dot")
    return a.o or "doubledag.json", a.o or "DOUBLEDAG.md", a.o or "coupled.dot"


def cmd_build(a):
    ledger, facts, pmap = resolve(a)
    rows, f = load(ledger, facts, pmap)
    dd = build(rows, f, flat=a.flat)
    jp, mp, dp = out_paths(a)
    jp = a.o or jp
    os.makedirs(os.path.dirname(os.path.abspath(jp)), exist_ok=True)
    with open(jp, "w", encoding="utf-8") as fh:
        json.dump(dd, fh, indent=2, ensure_ascii=False)
        fh.write("\n")
    s = dd["summary"]
    print("doubledag: %d labels (%d with Lean), %d edges — both %d, lean-only %d, tex-only %d; %s"
          % (s["labels"], s["labels_with_lean"], len(dd["edges"]), s["edges_both"],
             s["edges_lean_only"], s["edges_tex_only"], jp))
    return 0


def cmd_report(a):
    ledger, facts, pmap = resolve(a)
    rows, f = load(ledger, facts, pmap)
    dd = build(rows, f)
    flat = build(rows, f, flat=True) if not a.no_flat else None
    jp, mp, dp = out_paths(a)
    mp = a.o or mp
    os.makedirs(os.path.dirname(os.path.abspath(mp)), exist_ok=True)
    open(mp, "w", encoding="utf-8").write(report(dd, flat))
    print("doubledag: wrote %s" % mp)
    return 0


def cmd_edges(a):
    ledger, facts, pmap = resolve(a)
    rows, f = load(ledger, facts, pmap)
    dd = build(rows, f)
    by = {n["label"]: n for n in dd["nodes"]}
    rows_out = [e for e in dd["edges"] if e["kind"] == a.kind]
    for e in rows_out[:a.limit]:
        print("%-38s -> %-38s  %s" % (e["source"], e["target"],
                                      (by[e["target"]].get("title") or "")[:40]))
    print("%d %s edges" % (len(rows_out), a.kind))
    return 0


def cmd_dot(a):
    ledger, facts, pmap = resolve(a)
    rows, f = load(ledger, facts, pmap)
    dd = build(rows, f)
    jp, mp, dp = out_paths(a)
    dp = a.o or dp
    os.makedirs(os.path.dirname(os.path.abspath(dp)), exist_ok=True)
    open(dp, "w", encoding="utf-8").write(to_dot(dd))
    print("doubledag: wrote %s" % dp)
    return 0


def cmd_check(a):
    """The committed artifacts are what a build would write."""
    ledger, facts, pmap = resolve(a)
    rows, f = load(ledger, facts, pmap)
    dd = build(rows, f)
    jp, mp, _dp = out_paths(a)
    bad = 0
    if not os.path.exists(jp):
        print("doubledag: FAIL %s does not exist — run build" % jp)
        return 1
    cur = json.load(open(jp, encoding="utf-8"))
    if cur != json.loads(json.dumps(dd, ensure_ascii=False)):
        print("doubledag: FAIL %s is not what build would write" % jp)
        bad = 1
    if os.path.exists(mp):
        flat = build(rows, f, flat=True)
        if open(mp, encoding="utf-8").read() != report(dd, flat):
            print("doubledag: FAIL %s is not what report would write" % mp)
            bad = 1
    if bad:
        return 1
    print("doubledag: %s current (%d edges)" % (os.path.basename(jp), len(dd["edges"])))
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd")
    for name, fn in (("build", cmd_build), ("report", cmd_report), ("edges", cmd_edges),
                     ("dot", cmd_dot), ("check", cmd_check)):
        p = sub.add_parser(name)
        p.add_argument("--paper")
        p.add_argument("--ledger")
        p.add_argument("--facts")
        p.add_argument("--map")
        p.add_argument("-o")
        if name == "build":
            p.add_argument("--flat", action="store_true",
                           help="the naive projection: stop at any declaration of another label")
        if name == "report":
            p.add_argument("--no-flat", action="store_true")
        if name == "edges":
            p.add_argument("--kind", default="lean-only",
                           choices=["both", "lean-only", "tex-only", "tex-only-unformalized",
                                    "twin", "both-unformalized"])
            p.add_argument("--limit", type=int, default=40)
        p.set_defaults(fn=fn)
    a = ap.parse_args(argv)
    if not getattr(a, "fn", None):
        ap.print_help()
        return 2
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
