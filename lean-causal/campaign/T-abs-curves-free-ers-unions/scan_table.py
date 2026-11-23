"""The scan table of T-abs-curves-free-ers-unions, from Probe.lean's output. Run from lean-causal/:

    taskset -c 0-11 lake env lean campaign/T-abs-curves-free-ers-unions/Probe.lean > /tmp/probe.out
    python3 -I campaign/T-abs-curves-free-ers-unions/scan_table.py /tmp/probe.out \
        campaign/T-abs-curves-free-ers-unions/scan.json

For every declaration of the ETT layer with a flagged binder (kb/0259: a binder whose elaborated
type mentions CurvesExtend, CurvesExtendOn, InextensibleThrough, SplitBy, or inline Inextensible,
Extensible, FutureInextensible, PastInextensible), and every structure field so flagged, it looks
for a covering form: a declaration with a [SecondCountableTopology _] binder, the same conclusion
(whitespace-normalised pretty-printed string), every explicit or implicit binder among the
original's (same name, same type), and every instance it adds a SecondCountableTopology or a
T1Space. Such a form implies the original less the binders it drops, on a second countable (T1)
space. The candidate dropping the fewest binders wins; ties go to the closest name. It prints
the per-module counts and writes the table."""
import collections
import difflib
import json
import re
import sys

CE = {"Causal.Causality.CurvesExtend", "Causal.Causality.CurvesExtendOn"}
OKINST = re.compile(r"^(SecondCountableTopology|T1Space) \S+$")
TARGET_MODULES = ("Causal.ErsUnions", "Causal.ErsMughd")


def norm(t):
    return re.sub(r"\s+", " ", t)


def tup(r):
    return [(b[0], b[1], norm(b[2])) for b in r["binders"]]


def main(src, dst):
    recs = [json.loads(line[len("BINDERS "):]) for line in open(src, encoding="utf-8")
            if line.startswith("BINDERS ")]
    scanned = re.search(r"^SCANNED (\d+) modules, (\d+) declarations", open(src).read(), re.M)
    forms = [r for r in recs if r["secondCountable"]]
    bycon = collections.defaultdict(list)
    for f in forms:
        bycon[norm(f["concl"])].append(f)
    rows = []
    for t in recs:
        if not t["flagged"]:
            continue
        T = tup(t)
        tnt = {(x[1], x[2]) for x in T}
        tinst = {x[2] for x in T if x[0] == "[]"}
        cands = []
        for f in bycon.get(norm(t["concl"]), []) if t["kind"] == "theorem" else []:
            if f["name"] == t["name"]:
                continue
            F = tup(f)
            fnt = {(y[1], y[2]) for y in F}
            extra = [x for x in F if x[0] != "[]" and (x[1], x[2]) not in tnt]
            addinst = [x[2] for x in F if x[0] == "[]" and x[2] not in tinst]
            removed = [x for x in T if x[0] != "[]" and (x[1], x[2]) not in fnt]
            if extra or not all(OKINST.match(a) for a in addinst):
                continue
            sim = difflib.SequenceMatcher(a=t["name"].split(".")[-1],
                                          b=f["name"].split(".")[-1]).ratio()
            cands.append((-len(removed), sim, f["name"], f["module"], f["line"], removed, addinst))
        cands.sort(reverse=True)
        flagged_names = {(fl["name"], norm(fl["type"])) for fl in t["flagged"]}
        best = cands[0] if cands else None
        rows.append({
            "decl": t["name"],
            "kind": "structure field" if t["kind"] == "ctor" else t["kind"],
            "file_line": f"{t['module'].replace('.', '/')}.lean:{t['line']}",
            "module": t["module"],
            "curve_binders": [{"binder": f"({fl['name']} : {norm(fl['type'])})",
                               "flags": [x.split(".")[-1] for x in fl["flags"]]}
                              for fl in t["flagged"]],
            "curvesExtend_binder": any(set(fl["flags"]) & CE for fl in t["flagged"]),
            "form": best and best[2],
            "form_file_line": best and f"{best[3].replace('.', '/')}.lean:{best[4]}",
            "form_drops": best and [f"({x[1]} : {x[2]})" for x in best[5]],
            "form_adds_instances": best and best[6],
            "form_drops_every_flagged_binder": bool(best) and all(
                (n, ty) in {(x[1], x[2]) for x in best[5]} for n, ty in flagged_names),
            "form_exact": bool(best) and {(x[1], x[2]) for x in best[5]} == flagged_names,
        })
    rows.sort(key=lambda r: (r["module"], int(r["file_line"].rsplit(":", 1)[1])))
    out = {"scanned": scanned and {"modules": int(scanned[1]), "declarations": int(scanned[2])},
           "rows": rows}
    json.dump(out, open(dst, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    ce = [r for r in rows if r["curvesExtend_binder"]]
    per = collections.Counter(r["module"] for r in ce)
    unf = [r for r in ce if not r["form_drops_every_flagged_binder"] or not any(
        "CurvesExtend" in " ".join(b["flags"]) for b in r["curve_binders"])]
    print(f"scanned: {out['scanned']}; flagged declarations: {len(rows)}; "
          f"with a CurvesExtend(On) binder: {len(ce)}")
    for m, c in sorted(per.items()):
        covered = sum(1 for r in ce if r["module"] == m and r["form"] and any(
            set(b["flags"]) & {"CurvesExtend", "CurvesExtendOn"} and b["binder"] in r["form_drops"]
            for b in r["curve_binders"]))
        print(f"  {m}: {c} with a CurvesExtend(On) binder, {covered} with a form dropping it")
    for r in rows:
        if r["module"] in TARGET_MODULES:
            print(f"{r['file_line']} {r['decl']} [{r['kind']}]: "
                  + "; ".join(b["binder"] for b in r["curve_binders"])
                  + (f"\n    -> {r['form']} ({r['form_file_line']}), drops "
                     f"{', '.join(r['form_drops'])}, adds {', '.join(r['form_adds_instances'])}"
                     f"{' [exact]' if r['form_exact'] else ''}" if r["form"] else
                     "\n    -> no covering form"))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
