#!/usr/bin/env python3
r"""Ask Claude Opus what each disagreement between the two DAGs means. Proposals only.

    python3 tools/dag_reconcile.py --paper papers/<slug> --kind lean-only --limit 8
    python3 tools/dag_reconcile.py --dd doubledag.json --ledger L.json --facts F.json \
                                   --tex-root DIR --kind tex-only --limit 8 -o proposals.json
    python3 tools/dag_reconcile.py --show proposals.json        # read them back, no model

`tools/doubledag.py` finds the edges the draft and the Lean disagree about, and proves each one
with a witness: the chain of declarations from a principal of the source to a principal of the
target. It cannot say what a disagreement *means*. That is a mathematical reading of two
statements and a proof term, and it is what this asks a model -- one edge per question, with the
statements, the witness chain and each declaration's elaborated type in front of it.

A **lean-only** edge (the Lean proof uses it, the draft never says so) is one of

    dependency-missing-from-draft   the proof really does rest on it and the draft should say so
    proof-detail                    the Lean needs it for a step the paper takes as read
    mapping-artefact                an artefact of which declarations are listed under the labels

A **tex-only** edge (the draft cites it, the Lean proof term does not use it) is one of

    lean-statement-narrower         the Lean says less, which is why it does not need it  (DEC-17)
    decorative-reference            "see Lemma 7" is a pointer, not a use
    proof-differs                   the Lean proves it another way

Nothing here edits the ledger, the draft or the map: it writes `proposals.json`, the author
rules, and `tools/ledger.py` carries the ruling as curated fields. The model runs through
`tools/llm.py`, so every exchange is recorded in a cassette, tests replay them offline, and an
answer that names a label or a declaration that does not exist is refused rather than returned.
"""
import argparse
import json
import os
import re
import sys
import tomllib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import llm  # noqa: E402

VERDICTS = {
    "lean-only": ["dependency-missing-from-draft", "proof-detail", "mapping-artefact"],
    "tex-only": ["lean-statement-narrower", "decorative-reference", "proof-differs"],
}
GUIDE = {
    "lean-only": (
        "The Lean proof of the first statement reaches the second through the declaration chain "
        "below, and the draft never cites it there.\n"
        "  dependency-missing-from-draft — the argument really does rest on the second statement, "
        "and a reader of the draft is not told;\n"
        "  proof-detail — the chain is a step the paper takes as read (an ambient fact, a "
        "bookkeeping lemma), so the draft is right not to cite it;\n"
        "  mapping-artefact — the chain says nothing about the mathematics: it passes through a "
        "declaration that happens to be listed under the second label, or the two labels share "
        "vocabulary rather than content."),
    "tex-only": (
        "The draft cites the second statement in the first's statement or proof, and the Lean "
        "proof term of the first does not reach the second's principal declarations.\n"
        "  lean-statement-narrower — the Lean statement of the first says less than the paper's, "
        "which is why it does not need the second. This is the direction the project forbids "
        "(a Lean statement may be stronger than the paper's, never weaker), so say so plainly;\n"
        "  decorative-reference — the citation points the reader somewhere and is not a use;\n"
        "  proof-differs — both are faithful, and the Lean proves it another way."),
}
SCHEMA = {
    "type": "object",
    "properties": {
        "verdict": {"type": "string"},
        "confidence": {"type": "string", "enum": ["high", "medium", "low"]},
        "why": {"type": "string", "description": "One or two sentences, under 60 words."},
        "action": {"type": "string", "description": "What the author should do, under 25 words."},
    },
    "required": ["verdict", "confidence", "why", "action"],
    "additionalProperties": False,
}
TICK = re.compile(r"`([^`\s]+)`")


# ------------------------------------------------------------------ inputs --
def slice_tex(root, rel, span, limit=1800):
    p = os.path.join(root, rel)
    if not (root and os.path.exists(p) and span):
        return ""
    with open(p, encoding="utf-8", errors="replace") as fh:
        lines = fh.read().split("\n")
    text = "\n".join(lines[span[0] - 1:span[1]])
    return text[:limit] + ("\n…(truncated)" if len(text) > limit else "")


def decl_card(facts, name, limit=420):
    f = facts.get(name)
    if not f:
        return "%s  (not in the environment)" % name
    t = " ".join((f.get("type") or "").split())
    doc = " ".join((f.get("doc") or "").split())
    out = "%s : %s" % (name, t[:limit] + ("…" if len(t) > limit else ""))
    if doc:
        out += "\n    doc: " + doc[:240] + ("…" if len(doc) > 240 else "")
    return out


def prompt_for(edge, rows, facts, tex_root):
    by = {r["label"]: r for r in rows}
    src, tgt = by[edge["source"]], by[edge["target"]]
    kind = edge["kind"]
    w = edge.get("witness") or []
    L = []
    A = L.append
    A("You are auditing the link between a mathematics paper and its Lean 4 formalization.")
    A("")
    A(GUIDE[kind])
    A("")
    A("## First statement — `%s` (%s %s)%s" % (src["label"], src.get("kind", ""),
                                               src.get("number", ""), ": " + (src.get("title") or "")))
    A("")
    A("```latex")
    A(slice_tex(tex_root, src.get("file"), src.get("tex_span")) or "(source not available)")
    A("```")
    if src.get("proof_span"):
        # The proof may live in another file from the statement -- a body theorem proved in an
        # appendix, through its twin. `proof` carries "file:line"; the statement's file does not.
        pfile = (src.get("proof") or ":").rsplit(":", 1)[0] or src.get("file")
        A("")
        A("Its proof in the draft (`%s`)%s:"
          % (pfile, ", reached through its full form" if src.get("proof_via_twin") else ""))
        A("")
        A("```latex")
        A(slice_tex(tex_root, pfile, src.get("proof_span"), 1400) or "(not available)")
        A("```")
    A("")
    A("## Second statement — `%s` (%s %s)%s" % (tgt["label"], tgt.get("kind", ""),
                                                tgt.get("number", ""), ": " + (tgt.get("title") or "")))
    A("")
    A("```latex")
    A(slice_tex(tex_root, tgt.get("file"), tgt.get("tex_span")) or "(source not available)")
    A("```")
    A("")
    if w:
        A("## The Lean witness: a shortest chain of declarations from the first to the second")
        A("")
        A("Each line uses the next in its statement or its proof term. The first is a principal "
          "declaration of `%s`; the last is a principal of `%s`." % (src["label"], tgt["label"]))
        A("")
        for i, d in enumerate(w):
            A("%d. %s" % (i + 1, decl_card(facts, d)))
    else:
        A("## The Lean declarations")
        A("")
        A("Principals of `%s`:" % src["label"])
        for d in (src.get("decls") or [])[:6]:
            A("  - " + decl_card(facts, d, 240))
        A("")
        A("Principals of `%s`:" % tgt["label"])
        for d in (tgt.get("decls") or [])[:6]:
            A("  - " + decl_card(facts, d, 240))
    A("")
    A("## Your answer")
    A("")
    A("Choose exactly one verdict from: %s." % ", ".join(VERDICTS[kind]))
    A("Judge the mathematics, not the style. If the evidence does not settle it, say so with "
      "confidence \"low\" rather than guessing.")
    A("In `why`, name a Lean declaration or a paper label only if it appears above, and write it "
      "in backticks. Do not invent names. Under 60 words.")
    A("In `action`, say what the author should do in under 25 words.")
    return "\n".join(L)


def validator(kind, rows, facts):
    known = {r["label"] for r in rows} | set(facts)
    short = {n.split(".")[-1] for n in facts}
    # A module is a real thing to name -- `GFNBounds/Balance/GlobalConvergence.lean` is where a
    # scope note lives -- so the environment's modules count as known names, in both spellings.
    modules = {f.get("module") for f in facts.values() if f.get("module")}
    known |= modules
    known |= {m.replace(".", "/") + ".lean" for m in modules}
    short |= {m.rsplit(".", 1)[-1] + ".lean" for m in modules}

    def check(ans):
        if ans.get("verdict") not in VERDICTS[kind]:
            return "verdict %r is not one of %s" % (ans.get("verdict"), VERDICTS[kind])
        why = (ans.get("why") or "").strip()
        if not why:
            return "no reason given"
        if len(why.split()) > 90:
            return "the reason runs to %d words" % len(why.split())
        if not (ans.get("action") or "").strip():
            return "no action given"
        for tok in TICK.findall(why) + TICK.findall(ans.get("action") or ""):
            t = tok.strip(".,;:()")
            if t in known or t in short or t.split(".")[-1] in short:
                continue
            if ":" in t or "." in t:      # it looks like a label or a declaration, and is neither
                return "the answer names %r, which is neither a paper label nor a declaration" % t
        return None

    return check


# ------------------------------------------------------------------- main --
def resolve(a):
    if a.paper:
        with open(os.path.join(a.paper, "ledger", "ledger.toml"), "rb") as fh:
            cfg = tomllib.load(fh)
        base = os.path.join(os.path.abspath(a.paper), "ledger")
        out = cfg.get("output", {})
        ledger = os.path.join(base, out.get("dir", "."), out.get("json", "ledger.json"))
        lean = cfg.get("lean", {})
        root = os.path.normpath(os.path.join(base, os.path.expanduser(lean.get("root", ""))))
        facts = os.path.join(root, "docs", "lean-facts.json")
        dd = os.path.join(a.paper, "doubledag", "doubledag.json")
        tex = os.path.normpath(os.path.join(base, cfg["paper"].get("root", ".")))
        o = a.o or os.path.join(a.paper, "doubledag", "proposals.json")
        return (a.dd or dd, a.ledger or os.path.normpath(ledger), a.facts or facts,
                a.tex_root or tex, o)
    if not (a.dd and a.ledger and a.facts):
        sys.exit("dag_reconcile: give --paper, or --dd, --ledger and --facts")
    return a.dd, a.ledger, a.facts, a.tex_root, (a.o or "proposals.json")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--paper")
    ap.add_argument("--dd")
    ap.add_argument("--ledger")
    ap.add_argument("--facts")
    ap.add_argument("--tex-root")
    ap.add_argument("--kind", default="lean-only", choices=sorted(VERDICTS))
    ap.add_argument("--limit", type=int, default=8)
    ap.add_argument("--edge", action="append", help="source->target; repeatable, overrides --limit")
    ap.add_argument("--print-prompt", action="store_true", help="build the prompt, ask nothing")
    ap.add_argument("--show")
    ap.add_argument("-o")
    a = ap.parse_args(argv)

    if a.show:
        d = json.load(open(a.show, encoding="utf-8"))
        for p in d["proposals"]:
            v = p.get("verdict") or ("REFUSED: " + p.get("refused", ""))
            print("%-34s -> %-34s %-30s %s" % (p["source"], p["target"], v, p.get("confidence", "")))
            if p.get("why"):
                print("    %s" % p["why"])
            if p.get("action"):
                print("    action: %s" % p["action"])
        ok = [p for p in d["proposals"] if p.get("verdict")]
        print("%d proposals, %d answered, %.3f USD" % (len(d["proposals"]), len(ok),
                                                       d.get("cost_usd") or 0.0))
        return 0

    dd_p, ledger_p, facts_p, tex_root, out_p = resolve(a)
    dd = json.load(open(dd_p, encoding="utf-8"))
    rows = json.load(open(ledger_p, encoding="utf-8"))["statements"]
    facts = json.load(open(facts_p, encoding="utf-8"))["declarations"]
    by = {r["label"]: r for r in rows}

    edges = [e for e in dd["edges"] if e["kind"] == a.kind
             and e["source"] in by and e["target"] in by]
    if a.edge:
        want = {tuple(x.split("->")) for x in a.edge}
        edges = [e for e in edges if (e["source"], e["target"]) in want]
    else:
        # deterministic and worth asking about first: the longest witness chains are the ones a
        # reader is least able to check by eye.
        edges.sort(key=lambda e: (-len(e.get("witness") or []), e["source"], e["target"]))
        edges = edges[:a.limit]

    if a.print_prompt:
        for e in edges:
            print(prompt_for(e, rows, facts, tex_root))
            print("\n" + "=" * 78 + "\n")
        return 0

    check = validator(a.kind, rows, facts)
    proposals, cost = [], 0.0
    for e in edges:
        prompt = prompt_for(e, rows, facts, tex_root)
        rec = {"source": e["source"], "target": e["target"], "kind": a.kind,
               "witness": e.get("witness") or [],
               "cassette": llm.key("dag-%s" % a.kind, prompt, SCHEMA, llm.MODEL)[:8]}
        try:
            ans = llm.ask("dag-%s" % a.kind, prompt, SCHEMA, validate=check,
                          note="%s -> %s" % (e["source"], e["target"]))
            rec.update(verdict=ans["verdict"], confidence=ans["confidence"],
                       why=ans["why"], action=ans["action"])
        except llm.Refused as ex:
            rec["refused"] = str(ex)
        c = llm.load_cassette("dag-%s" % a.kind, llm.key("dag-%s" % a.kind, prompt, SCHEMA, llm.MODEL))
        if c:
            cost += c.get("cost_usd") or 0.0
        proposals.append(rec)
        print("%-34s -> %-34s %s" % (rec["source"], rec["target"],
                                     rec.get("verdict") or "REFUSED: " + rec.get("refused", "")))

    doc = {"kind": a.kind, "model": llm.MODEL, "doubledag": os.path.basename(dd_p),
           "cost_usd": round(cost, 4), "proposals": proposals}
    os.makedirs(os.path.dirname(os.path.abspath(out_p)), exist_ok=True)
    with open(out_p, "w", encoding="utf-8") as fh:
        json.dump(doc, fh, indent=2, ensure_ascii=False)
        fh.write("\n")
    answered = sum(1 for p in proposals if p.get("verdict"))
    print("dag_reconcile: %d proposals (%d answered), %.3f USD — %s"
          % (len(proposals), answered, cost, out_p))
    return 0 if answered == len(proposals) else 1


if __name__ == "__main__":
    sys.exit(main())
