#!/usr/bin/env python3
"""Regenerate papers/gx/certificate/curation.toml from the campaign's REPORT.json files.

The master session's tool (not a gate). Later packages override earlier ones label by label
(PKGS is in chronological order). The terminal rows (after \\end{document}) are kept.
    python3 lean-gx/campaign/curate.py && python3 tools/ledger_curate.py --paper papers/gx
"""
import json, os, re, sys

HUB = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CAMP = os.path.join(HUB, "lean-gx", "campaign")
CUR = os.path.join(HUB, "papers", "gx", "certificate", "curation.toml")
LED = os.path.join(HUB, "papers", "gx", "ledger", "ledger.json")

# package -> strict (or scaffold) file, relative to lean-gx/
PKGS = [
    ("WP-24a", "GX/Topology/Portly.lean"), ("WP-24d", "GX/Spread/Basic.lean"),
    ("WP-24e", "GX/Singular/Atlas.lean"),
    ("WP-25a", "GX/Spread/Basic.lean"), ("WP-25b", "GX/Singular/Atlas.lean"),
    ("WP-25c", "GX/Spread/Completion.lean"), ("WP-25d", "GX/Branched/Basic.lean"),
    ("WP-25e", "GX/Branched/Universality.lean"), ("WP-25f", "GX/Singular/Quotient.lean"),
    ("WP-25g", "GX/Singular/Suspension.lean"),
    ("WP-26a", "GX/Singular/Atlas.lean"), ("WP-26b", "GX/Singular/Quotient.lean"),
    ("WP-26c", "GX/Branched/Universality.lean"), ("WP-26g", "GX/Topology/PortlyExamples.lean"),
    ("WP-26e", "GX/Branched/Paths.lean"), ("WP-26f", "GX/Branched/Galois.lean"),
    ("WP-26h", "scaffold/GXScaffold/Branched/GaloisExamples.lean"),
    ("WP-27a", "GX/Singular/Atlas.lean"), ("WP-27b", "GX/Singular/Quotient.lean"),
    ("WP-27c", "GX/Branched/Universality.lean"), ("WP-27d", "GX/Branched/Paths.lean"),
    ("WP-27e", "GX/Branched/Galois.lean"), ("WP-27f", "scaffold/GXScaffold/Branched/GaloisExamples.lean"),
    ("WP-27g", "GX/SingularII/Unloopable.lean"), ("WP-27h", "GX/SingularII/Developing.lean"),
    ("WP-27i", "GX/SingularII/Tame.lean"), ("WP-27j", "scaffold/GXScaffold/SingularII/Models.lean"),
    ("WP-27k", "scaffold/GXScaffold/SingularII/SpreadTop.lean"),
    ("WP-35a", "GX/Branched/Paths.lean"), ("WP-35b", "GX/Branched/Galois.lean"),
    ("WP-35c", "GX/SingularII/Unloopable.lean"), ("WP-35d", "GX/SingularII/Developing.lean"),
    ("WP-35e", "GX/SingularII/Tame.lean"), ("WP-35f", "scaffold/GXScaffold/SingularII/Models.lean"),
    ("WP-35g", "scaffold/GXScaffold/SingularII/SpreadTop.lean"),
    ("WP-35h", "scaffold/GXScaffold/Branched/GaloisExamples.lean"), ("WP-35i", "GX/Hyperbolic/Plane.lean"),
    ("WP-40a", "GX/Branched/Paths.lean"), ("WP-40b", "GX/Hyperbolic/Plane.lean"),
    ("WP-40c", "scaffold/GXScaffold/SingularII/Models.lean"), ("WP-40d", "scaffold/GXScaffold/SingularII/SpreadTop.lean"),
    ("WP-40e", "scaffold/GXScaffold/Branched/GaloisExamples.lean"),
]
FILE_OVERRIDE = {"ex:following_example_skeletal_itemize": "GX/Topology/PortlyExamples.lean"}
RENAMES = {  # (file, old) -> new, applied at graduation to resolve name clashes
    ("GX/Spread/Completion.lean", "GX.isPreconnected_ball_diff_countable"): "GX.isPreconnected_ball_diff_countable_complex",
    ("GX/Branched/Universality.lean", "GX.isSkeletal_of_countable"): "GX.isSkeletal_of_countable_complex",
}

def q(s):
    return json.dumps(s, ensure_ascii=False)

def decl_exists(file, name):
    """A textual, non-instance declaration of `name` in `file` (ledger.py reads instances as unnamed)."""
    src = open(os.path.join(HUB, "lean-gx", file), encoding="utf-8").read()
    if re.search(r"instance\s+" + re.escape(name.split(".")[-1]) + r"\b", src):
        return None
    short = name.split(".")[-1]
    return re.search(r"(?<![\w.'])" + re.escape(short) + r"(?![\w'])", src) is not None and \
        re.search(r"(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+(\S*\.)?" + re.escape(short) + r"\b", src)

def main():
    led = {s["label"]: s for s in json.load(open(LED, encoding="utf-8"))["statements"]}
    rows = {}
    for pkg, file in PKGS:
        rp = os.path.join(CAMP, pkg, "REPORT.json")
        if not os.path.exists(rp):
            continue
        r = json.load(open(rp, encoding="utf-8"))
        for l in r["labels"]:
            lab = l["label"]
            if lab not in led:
                continue
            f = FILE_OVERRIDE.get(lab, file)
            decls = [RENAMES.get((f, d), d) for d in l.get("decls", [])]
            dropped = [d for d in decls if not decl_exists(f, d)]
            decls = [d for d in decls if d not in dropped]
            rows[lab] = dict(pkg=pkg, file=f, status=l["status"], decls=decls,
                             findings=l.get("findings", []), questions=l.get("questions", []),
                             sorries=[s.get("obstruction", "") for s in l.get("sorries", [])],
                             dropped=dropped)
    head, term = [], []
    txt = open(CUR, encoding="utf-8").read()
    head.append(txt.split("[[row]]")[0].rstrip() + "\n")
    for block in txt.split("[[row]]")[1:]:
        if 'bucket = "T"' in block:
            term.append("[[row]]" + block.rstrip() + "\n")
    out = head + term
    for lab, x in rows.items():
        o = ["[[row]]", "label = " + q(lab), "decls = " + q(x["decls"])]
        if x["status"] == "closed":
            # extra_lean_files: the ledger reads marks only in a module docstring's first 4000
            # characters, so a long docstring can hide a mark; name the file explicitly.
            o.append("extra_lean_files = " + q([x["file"]]))
            if x["file"].startswith("GX/"):
                o.append('bucket = "A"')
                note = "%s, audited clean." % x["pkg"]
            else:
                o.append('bucket = "B"')
                note = "%s, audited clean; closed in the scaffold, its module waits on a sorry elsewhere to graduate." % x["pkg"]
        else:
            o += ['bucket = "C"', "extra_lean_files = " + q([x["file"]]), 'lean_proved_override = "partial"']
            why = ("tagged sorry: " + "; ".join(x["sorries"])) if x["sorries"] else \
                  ("paper statement corrected (DEC-27)" if x["findings"] else "a reading awaiting the author")
            note = "%s, audited clean. Partial: %s" % (x["pkg"], why)
        if x["questions"]:
            note += " Readings/questions: " + " | ".join(x["questions"])
        o.append("notes = " + q(note))
        if x["findings"]:
            o.append("paper_findings = " + q(x["findings"]))
        out.append("\n".join(o) + "\n")
        if x["dropped"]:
            print("dropped (not found in %s): %s" % (x["file"], x["dropped"]), file=sys.stderr)
    open(CUR, "w", encoding="utf-8").write("\n".join(out))
    print("curate: %d rows (+%d terminal)" % (len(rows), len(term)))

if __name__ == "__main__":
    main()
