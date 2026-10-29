#!/usr/bin/env python3
"""Write a paper's curated ledger fields from an authored file.

    python3 tools/ledger_curate.py --paper papers/<slug>          # apply, then rebuild the ledger
    python3 tools/ledger_curate.py --paper papers/<slug> --check  # exit 1 if ledger.json differs

The ledger's curated fields (`decls`, `bucket`, `notes`, `paper_findings`, the overrides, ...) live
in `ledger/ledger.json` and survive a rebuild, but a JSON edited by hand has no source a reviewer
can read. This tool makes `papers/<slug>/certificate/curation.toml` that source: one `[[row]]` per
label, holding curated fields only, and an optional top-level `findings_triage`. It writes those
fields into `ledger.json` and removes a curated field the file no longer names, so the file is the
whole truth about what was curated. It never touches a computed field: `ledger.py build` does
that, and is run after.

Exit 0 on success, 1 on a difference under `--check`, 2 on a misconfiguration: a label absent from
the ledger, or a field which is not a curated one -- a typo must not be silently dropped.
"""
import json
import os
import subprocess
import sys
import tomllib

TOOLS = os.path.dirname(os.path.abspath(__file__))

#: tools/ledger.py `CURATED` and `CURATED_TOP`: the only fields this tool may write.
CURATED = ("nl_status_override", "nl_reason", "bucket", "decls",
           "notes", "blocked_on", "lean_stated_override", "lean_proved_override",
           "paper_findings", "extra_lean_files", "restatement", "restatement_note",
           "terminal_reason", "size", "fidelity")
CURATED_TOP = ("findings_triage",)


class Misconfigured(Exception):
    pass


def apply(ledger, curation):
    """The ledger with the curated fields of `curation`, and nothing else changed."""
    by_label = {s["label"]: s for s in ledger["statements"]}
    rows = curation.get("row", [])
    seen = set()
    for r in rows:
        lab = r.get("label")
        if not lab:
            raise Misconfigured("a [[row]] has no label")
        if lab in seen:
            raise Misconfigured("%s: two [[row]] entries" % lab)
        seen.add(lab)
        if lab not in by_label:
            raise Misconfigured("%s: not a ledger statement" % lab)
        for k in r:
            if k != "label" and k not in CURATED:
                raise Misconfigured("%s: `%s` is not a curated field" % (lab, k))
    for k in curation:
        if k != "row" and k not in CURATED_TOP:
            raise Misconfigured("top level: `%s` is not a curated field" % k)
    wanted = {r["label"]: {k: v for k, v in r.items() if k != "label"} for r in rows}
    for s in ledger["statements"]:
        w = wanted.get(s["label"], {})
        for k in CURATED:
            if k in w:
                s[k] = w[k]
            elif k in s:
                # `decls` and `bucket` are always present in a built row: reset, do not delete.
                if k == "decls":
                    s[k] = []
                elif k == "bucket":
                    s[k] = ""
                else:
                    del s[k]
    paper = ledger.setdefault("paper", {})
    for k in CURATED_TOP:
        if k in curation:
            paper[k] = curation[k]
        elif k in paper:
            del paper[k]
    return ledger


def main(argv):
    if "--paper" not in argv:
        print(__doc__)
        return 2
    paper = argv[argv.index("--paper") + 1]
    check = "--check" in argv
    cur_path = os.path.join(paper, "certificate", "curation.toml")
    led_path = os.path.join(paper, "ledger", "ledger.json")
    cfg = os.path.join(paper, "ledger", "ledger.toml")
    if not os.path.exists(cur_path):
        print("ledger_curate: %s does not exist" % cur_path)
        return 2
    if not os.path.exists(led_path):
        print("ledger_curate: %s does not exist -- run `ledger.py build` first" % led_path)
        return 2
    with open(cur_path, "rb") as fh:
        curation = tomllib.load(fh)
    before = json.load(open(led_path, encoding="utf-8"))
    try:
        after = apply(json.loads(json.dumps(before)), curation)
    except Misconfigured as e:
        print("ledger_curate: %s" % e)
        return 2
    if check:
        if after != before:
            changed = [s["label"] for s, t in zip(after["statements"], before["statements"])
                       if s != t]
            print("ledger_curate: FAIL %s does not carry %s (%d rows differ: %s)"
                  % (led_path, cur_path, len(changed), ", ".join(changed[:5])))
            return 1
        print("ledger_curate: %s carries %s (%d curated rows)"
              % (led_path, cur_path, len(curation.get("row", []))))
        return 0
    with open(led_path, "w", encoding="utf-8") as fh:
        json.dump(after, fh, ensure_ascii=False, indent=1)
        fh.write("\n")
    r = subprocess.run([sys.executable, os.path.join(TOOLS, "ledger.py"), "-c", cfg, "build"])
    if r.returncode != 0:
        return r.returncode
    print("ledger_curate: wrote %d curated rows into %s" % (len(curation.get("row", [])), led_path))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
