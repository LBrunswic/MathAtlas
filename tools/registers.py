#!/usr/bin/env python3
"""The register gate: the registers are well formed, append-only where they must be, and agree.

    python3 tools/registers.py check      # exit 1 on any violation; prints each with file:line
    python3 tools/registers.py selftest   # every fixture in tools/fixtures/registers/ must make `check` fail

The hub's light governance (DEC-1): five hand-curated markdown tables, no generated state.

    registers/DECISIONS.md   DEC rows (append-only) and open questions OQ
    registers/WORK.md        WP rows
    registers/QA.md          QA rows
    registers/RISKS.md       R rows
    registers/DEPS.md        dependency rows (their agreement with the lakefile is deps_register.py's)

Rules (each has a fixture, and `selftest` fails if one has none):

 1  tables       every register exists with its exact table header, and rows have its width
 2  ids          identifiers are well formed and unique within their table
 3  vocabulary   statuses, results, probabilities belong to their vocabulary; every date is a
                 real calendar date YYYY-MM-DD; DEC rows are decided by AUTHOR
 4  references   every DEC-n, R-n, WP-n, QA-n, OQ-n cited in registers/, CLAUDE.md, README.md
                 or hub.toml exists
 5  decisions    DEC ids are consecutive from 1 with non-decreasing dates, and every DEC row
                 committed at HEAD is present verbatim (append-only)
 6  evaluation   a PASS or FAIL in QA names a date, an existing commit and evidence
 7  freeze       hub.toml's [freeze].until is a date; FREEZE=1 in the environment after that
                 date is a violation (the freeze is DEC-2 and it expires)

A fixture is a JSON object: {"rule": R, "expect": substring-of-a-violation, and one edit:
"file": F, "find": S, "replace": T | "file": F, "append": T | "delete_file": F | "env": {K: V}}.
Fixtures are applied to a temporary copy of the repository's registers, never to the tree.
"""
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = os.environ.get("LEANARTICLES_ROOT") or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RULES = ("tables", "ids", "vocabulary", "references", "decisions", "evaluation", "freeze")

TABLES = {
    "DECISIONS.md": [("DEC", "| DEC | Date | Decision | By | Context |"),
                     ("OQ", "| OQ | Raised | Question | Blocks | Status |")],
    "WORK.md": [("WP", "| WP | Phase | Item | Status | Updated | Note |")],
    "QA.md": [("QA", "| QA | Gate | Paper | Result | Evaluated | Commit | Evidence |")],
    "RISKS.md": [("R", "| R | Raised | Risk | Prob | Impact | Response | Owner | Status |")],
    "DEPS.md": [("name", "| name | upstream | rev | toolchain | license | used by | status |")],
}
VOCAB = {
    "WP.Status": {"PROPOSED", "APPROVED", "IN-PROGRESS", "BLOCKED", "IN-REVIEW", "DONE", "DROPPED", "SUPERSEDED"},
    "QA.Result": {"PASS", "FAIL", "WAIVED"},
    "R.Prob": {"L", "M", "H"}, "R.Impact": {"L", "M", "H"},
    "R.Status": {"OPEN", "MITIGATED", "OCCURRED", "CLOSED"},
    "OQ.Status": {"OPEN", "RULED"},
    "name.status": {"live-dep", "vendored-slice", "reference", "to-survey", "rejected"},
}
ID_RE = {"DEC": r"DEC-\d+", "OQ": r"OQ-\d+", "WP": r"WP-\d+", "QA": r"QA-\d+", "R": r"R-\d+",
         "name": r"`[A-Za-z0-9_.\-]+`"}
DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def is_date(s):
    if not DATE.match(s):
        return False
    try:
        datetime.date.fromisoformat(s)
        return True
    except ValueError:
        return False


def read_tables(regdir):
    """file -> {table_key: (header_line_no, [ (line_no, cells) ])}"""
    out = {}
    for fname, specs in TABLES.items():
        path = os.path.join(regdir, fname)
        out[fname] = {}
        if not os.path.exists(path):
            continue
        lines = open(path, encoding="utf-8").read().split("\n")
        for key, header in specs:
            hits = [i for i, l in enumerate(lines) if l.strip() == header]
            rows = []
            if hits:
                i = hits[0] + 2
                while i < len(lines) and lines[i].startswith("|"):
                    cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
                    rows.append((i + 1, cells))
                    i += 1
            out[fname][key] = (hits, header, rows)
    return out


def check(regdir=None, env=None, quiet=False):
    regdir = regdir or os.path.join(ROOT, "registers")
    env = os.environ if env is None else env
    v = []

    def bad(rule, where, msg):
        v.append("[%s] %s: %s" % (rule, where, msg))

    tabs = read_tables(regdir)
    for fname, specs in TABLES.items():
        if not os.path.exists(os.path.join(regdir, fname)):
            bad("tables", fname, "missing register")
            continue
        for key, header in specs:
            hits, _h, rows = tabs[fname][key]
            if len(hits) != 1:
                bad("tables", fname, "table with header %r present %d times" % (header, len(hits)))
                continue
            width = header.count("|") - 1
            for ln, cells in rows:
                if len(cells) != width:
                    bad("tables", "%s:%d" % (fname, ln), "row has %d cells, header %d" % (len(cells), width))
    # ids
    known = set()
    for fname, tables in tabs.items():
        for key, (hits, header, rows) in tables.items():
            seen = set()
            for ln, cells in rows:
                if not cells:
                    continue
                cid = cells[0]
                if not re.fullmatch(ID_RE[key], cid):
                    bad("ids", "%s:%d" % (fname, ln), "malformed id %r" % cid)
                if cid in seen:
                    bad("ids", "%s:%d" % (fname, ln), "duplicate id %s" % cid)
                seen.add(cid)
                known.add(cid)
    # vocabulary and dates
    for fname, tables in tabs.items():
        for key, (hits, header, rows) in tables.items():
            cols = [c.strip() for c in header.strip().strip("|").split("|")]
            for ln, cells in rows:
                if len(cells) != len(cols):
                    continue
                row = dict(zip(cols, cells))
                for col, val in row.items():
                    vk = "%s.%s" % (key, col)
                    if vk in VOCAB:
                        head = val.split(" ")[0]
                        if head not in VOCAB[vk]:
                            bad("vocabulary", "%s:%d" % (fname, ln), "%s %r not in %s" % (col, val, sorted(VOCAB[vk])))
                    if col in ("Date", "Raised", "Updated") or (col == "Evaluated" and val not in ("", "—")):
                        if not is_date(val):
                            bad("vocabulary", "%s:%d" % (fname, ln), "%s %r is not a date" % (col, val))
                if key == "DEC" and row.get("By") != "AUTHOR":
                    bad("vocabulary", "%s:%d" % (fname, ln), "a decision is decided by AUTHOR, not %r" % row.get("By"))
    # references
    cite = re.compile(r"\b(DEC|OQ|WP|QA|R)-(\d+)\b")
    texts = []
    for fname in TABLES:
        p = os.path.join(regdir, fname)
        if os.path.exists(p):
            texts.append((fname, open(p, encoding="utf-8").read()))
    for extra in ("CLAUDE.md", "README.md", "hub.toml"):
        p = os.path.join(os.path.dirname(regdir), extra)
        if os.path.exists(p):
            texts.append((extra, open(p, encoding="utf-8").read()))
    for fname, text in texts:
        for i, line in enumerate(text.split("\n"), 1):
            for m in cite.finditer(line):
                if m.group(0) not in known:
                    bad("references", "%s:%d" % (fname, i), "%s does not exist" % m.group(0))
    # decisions: consecutive, dates non-decreasing, append-only against HEAD
    dec = tabs["DECISIONS.md"].get("DEC", ([], "", []))[2]
    last_date = None
    for k, (ln, cells) in enumerate(dec):
        if cells and cells[0] != "DEC-%d" % (k + 1):
            bad("decisions", "DECISIONS.md:%d" % ln, "expected DEC-%d, found %s" % (k + 1, cells[0]))
        if len(cells) > 1 and is_date(cells[1]):
            if last_date and cells[1] < last_date:
                bad("decisions", "DECISIONS.md:%d" % ln, "date %s earlier than the previous row" % cells[1])
            last_date = cells[1]
    try:
        head = subprocess.check_output(["git", "-C", ROOT, "show", "HEAD:registers/DECISIONS.md"],
                                       text=True, stderr=subprocess.DEVNULL)
        cur_rows = {"|".join(c) for _ln, c in dec}
        for line in head.split("\n"):
            if line.startswith("| DEC-"):
                cells = [c.strip() for c in line.strip().strip("|").split("|")]
                if "|".join(cells) not in cur_rows:
                    bad("decisions", "DECISIONS.md", "committed row %s was edited or removed" % cells[0])
    except subprocess.CalledProcessError:
        if not quiet:
            print("registers: no committed DECISIONS.md yet; append-only rule skipped")
    # evaluation
    for ln, cells in tabs["QA.md"].get("QA", ([], "", []))[2]:
        if len(cells) != 7:
            continue
        res = cells[3].split(" ")[0]
        if res in ("PASS", "FAIL"):
            if not is_date(cells[4]):
                bad("evaluation", "QA.md:%d" % ln, "%s without a date" % res)
            commit = cells[5].strip("`")
            ok = subprocess.run(["git", "-C", ROOT, "cat-file", "-e", commit + "^{commit}"],
                                capture_output=True).returncode == 0
            if not ok:
                bad("evaluation", "QA.md:%d" % ln, "commit %r does not exist" % commit)
            if not cells[6]:
                bad("evaluation", "QA.md:%d" % ln, "%s without evidence" % res)
    # freeze
    hub = os.path.join(os.path.dirname(regdir), "hub.toml")
    if os.path.exists(hub):
        with open(hub, "rb") as fh:
            until = str(tomllib.load(fh).get("freeze", {}).get("until", ""))
        if until and not is_date(until):
            bad("freeze", "hub.toml", "[freeze].until %r is not a date" % until)
        elif until and env.get("FREEZE") == "1":
            today = env.get("LEANARTICLES_TODAY") or datetime.date.today().isoformat()
            if today > until:
                bad("freeze", "hub.toml", "FREEZE=1 on %s, but the freeze (DEC-2) expired on %s" % (today, until))
    # blocked papers: each names an OPEN question; a RULED one no longer blocks anything
    if os.path.exists(hub):
        with open(hub, "rb") as fh:
            blocked = tomllib.load(fh).get("papers", {}).get("blocked", {})
        oq_rows = {c[0]: c for _ln, c in tabs["DECISIONS.md"].get("OQ", ([], "", []))[2]}
        for slug, oq in blocked.items():
            row = oq_rows.get(oq)
            if row is None:
                bad("references", "hub.toml", "papers.blocked.%s names %s, which does not exist" % (slug, oq))
            elif len(row) > 4 and row[4] != "OPEN":
                bad("freeze", "hub.toml", "papers.blocked.%s names %s, which is %s: the block has expired"
                    % (slug, oq, row[4]))
    if not quiet:
        for x in v:
            print(x)
        if not v:
            print("registers: %d ids, all rules hold" % len(known))
    return v


def selftest():
    fdir = os.path.join(ROOT, "tools", "fixtures", "registers")
    fixtures = sorted(f for f in os.listdir(fdir) if f.endswith(".json")) if os.path.isdir(fdir) else []
    covered, fail = set(), 0
    base = check(quiet=True)
    if base:
        print("selftest: the live registers already fail:\n  " + "\n  ".join(base))
        return 1
    for f in fixtures:
        fx = json.load(open(os.path.join(fdir, f), encoding="utf-8"))
        tmp = tempfile.mkdtemp()
        try:
            shutil.copytree(os.path.join(ROOT, "registers"), os.path.join(tmp, "registers"))
            for extra in ("CLAUDE.md", "hub.toml"):
                shutil.copy(os.path.join(ROOT, extra), tmp)
            env = dict(os.environ)
            env.update(fx.get("env", {}))
            if "delete_file" in fx:
                os.remove(os.path.join(tmp, fx["delete_file"]))
            elif "append" in fx:
                with open(os.path.join(tmp, fx["file"]), "a", encoding="utf-8") as fh:
                    fh.write(fx["append"])
            elif "find" in fx:
                p = os.path.join(tmp, fx["file"])
                s = open(p, encoding="utf-8").read()
                assert s.count(fx["find"]) == 1, (f, "find must occur exactly once")
                open(p, "w", encoding="utf-8").write(s.replace(fx["find"], fx["replace"]))
            v = check(os.path.join(tmp, "registers"), env=env, quiet=True)
            hit = [x for x in v if x.startswith("[%s]" % fx["rule"]) and fx["expect"] in x]
            if hit:
                print("selftest: %s -> %s" % (f, hit[0]))
                covered.add(fx["rule"])
            else:
                print("selftest: FAIL %s did not produce a [%s] violation containing %r; got: %s"
                      % (f, fx["rule"], fx["expect"], v or "nothing"))
                fail += 1
        finally:
            shutil.rmtree(tmp)
    for r in RULES:
        if r not in covered:
            print("selftest: FAIL rule %r has no fixture that breaks it" % r)
            fail += 1
    if fail:
        return 1
    print("selftest: %d fixtures, every rule shown to bite" % len(fixtures))
    return 0


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    if cmd == "check":
        return 1 if check() else 0
    if cmd == "selftest":
        return selftest()
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
