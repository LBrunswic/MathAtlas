#!/usr/bin/env python3
"""The EGF corrections register: every place where formalizing found the paper wrong or short,
what replaces it, and how far the replacement has got. Kept by /egf-programme (papers/egf/programme).

    python3 tools/corrections.py check [--file F] [--v2 DIR]   every rule below; exit 1 on a violation
    python3 tools/corrections.py status [--file F]             one line per entry, grouped by status
    python3 tools/corrections.py errata [--file F] [--format md|tex]
                                                               the "Changes from v1" list (applied and reviewed entries)
    python3 tools/corrections.py set ID STATUS [--file F] [--commit SHA] [--review TEXT]
                                                               move one entry, in place; refuses an edit that breaks a rule

An entry is a `[[correction]]` table (schema in the register's header). Its status only moves forward:

    found     formalizing found it; `printed`, `kind`, `finding` say where and what
    proved    the corrected form is proved: every `anchor` is a declaration of the strict library
    adopted   a DEC row rules it the form of record (`basis` names it); `corrected` and `summary` say what replaces the print
    applied   the v2 working copy carries it: `v2_commit` is a commit of that repository
    reviewed  the author has read the applied edit: `review` records when and how

Rules (each is a gate, shown to bite by tools/fixtures/corrections):
- ids are unique and match C-<n>; `kind` and `status` are in their vocabularies;
- `printed` is `main.tex:<line>` or `main.tex:<a>-<b>`, inside legacy/orig/main.tex;
- `label`, when given, is a row of papers/egf/ledger; `basis` names only existing OQ/DEC rows;
- `batch`, when given, is a `correct` target of papers/egf/programme/roadmap.toml;
- a `false` entry names a `refutation`, a declaration of the strict library;
- from `proved` on: a non-empty `anchor` (a `typo` needs none), every name a declaration of the strict library;
- from `adopted` on: a DEC row in `basis`, non-empty `corrected` and `summary`, and `added_hypotheses` (a list, maybe empty);
- from `applied` on: `v2_commit` is a commit of the v2 repository; `reviewed` also needs `review`.

Declarations are read off lean-egf/EGF/**.lean without Lean (comments blanked, namespaces tracked),
as tools/ladder.py reads lean-causal. The strict library is sorry-free by its own gate
(warningAsError), so a declaration found there is a proved one.
"""
import glob
import json
import os
import re
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import ladder  # noqa: E402  (its comment blanker and declaration regexes)

FILE = os.path.join(ROOT, "papers", "egf", "programme", "corrections.toml")
LEAN_ROOT = os.path.join(ROOT, "lean-egf")
LEGACY = os.path.join(ROOT, "papers", "egf", "legacy", "orig", "main.tex")
LEDGER = os.path.join(ROOT, "papers", "egf", "ledger", "ledger.json")
DECISIONS = os.path.join(ROOT, "registers", "DECISIONS.md")
ROADMAP = os.path.join(ROOT, "papers", "egf", "programme", "roadmap.toml")
# The v2 working copy (DEC-141): outside the hub, beside it in Dropbox.
V2 = os.path.join(os.path.dirname(ROOT), "ErgodicGFN arXiv", "source")

STATUS = ["found", "proved", "adopted", "applied", "reviewed"]
KIND = ["false", "missing-hypothesis", "gap", "convention", "typo", "strengthening"]
REQUIRED = ["id", "printed", "kind", "finding", "status"]


def load(path=FILE):
    with open(path, "rb") as fh:
        return tomllib.load(fh)


def rank(status):
    return STATUS.index(status) if status in STATUS else -1


def lean_decls(root=LEAN_ROOT, lib="EGF"):
    """Full names of the declarations of `root/lib/**.lean` (namespaces tracked, comments blanked)."""
    decls = set()
    for f in sorted(glob.glob(os.path.join(root, lib, "**", "*.lean"), recursive=True)):
        with open(f, encoding="utf-8") as fh:
            code = ladder._code(fh.read())
        stack, header = [], True
        for line in code.split("\n"):
            s = line.strip()
            if not s:
                continue
            if header:
                if s in ("module", "prelude") or ladder.IMPORT.match(s):
                    continue
                header = False
            m = re.match(r"namespace\s+(\S+)", s)
            if m:
                stack.extend(("namespace", x) for x in m.group(1).split("."))
                continue
            m = re.match(r"(?:@\[.*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section\b\s*(\S*)", s)
            if m:
                stack.extend(("section", x) for x in (m.group(1).split(".") if m.group(1) else [""]))
                continue
            m = re.match(r"end\b\s*(\S*)", s)
            if m:
                for _ in (m.group(1).split(".") if m.group(1) else [""]):
                    if stack:
                        stack.pop()
                continue
            while s.startswith("@["):
                d, k = 0, 1
                for k in range(1, len(s)):
                    d += s[k] == "["
                    d -= s[k] == "]"
                    if d == 0:
                        break
                s = s[k + 1:].lstrip()
            m = ladder.DECL_FQ.match(s)
            if not m:
                continue
            name = m.group(2)
            full = name[len("_root_."):] if name.startswith("_root_.") else \
                ".".join([x for k, x in stack if k == "namespace"] + [name])
            decls.add(full)
    return decls


def ledger_labels(path=LEDGER):
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as fh:
        return {r["label"] for r in json.load(fh)["statements"]}


def register_rows(path=DECISIONS):
    """The ids of the DEC and OQ rows of registers/DECISIONS.md."""
    out = set()
    if os.path.exists(path):
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                m = re.match(r"\|\s*((?:DEC|OQ)-\d+)\s*\|", line)
                if m:
                    out.add(m[1])
    return out


def legacy_lines(path=LEGACY):
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as fh:
        return sum(1 for _ in fh)


def is_commit(repo, sha):
    if not sha or not os.path.isdir(os.path.join(repo, ".git")):
        return False
    return subprocess.run(["git", "-C", repo, "cat-file", "-e", sha + "^{commit}"],
                          capture_output=True).returncode == 0


def as_list(x):
    return x if isinstance(x, list) else ([] if x in (None, "") else [x])


def correct_targets(path=ROADMAP):
    """The ids of the `correct` targets of the EGF programme's roadmap, or None when it is absent."""
    if not os.path.exists(path):
        return None
    with open(path, "rb") as fh:
        return {t["id"] for t in tomllib.load(fh).get("target", []) if t.get("kind") == "correct"}


def check(data, names=None, labels=None, rows=None, nlines=None, v2=V2, batches=None):
    batches = correct_targets() if batches is None else batches
    names = lean_decls() if names is None else names
    labels = ledger_labels() if labels is None else labels
    rows = register_rows() if rows is None else rows
    nlines = legacy_lines() if nlines is None else nlines
    errs = []
    bad = lambda cid, msg: errs.append("%s: %s" % (cid, msg))
    entries = data.get("correction", [])
    ids = [c.get("id", "?") for c in entries]
    for cid in sorted(set(i for i in ids if ids.count(i) > 1)):
        bad(cid, "duplicate id")
    for c in entries:
        cid = c.get("id", "?")
        for k in REQUIRED:
            if k not in c or c[k] in ("", None, []):
                bad(cid, "missing %s" % k)
        if not re.fullmatch(r"C-\d+", cid):
            bad(cid, "id must match C-<n>")
        st = c.get("status")
        if st not in STATUS:
            bad(cid, "status %r not in %s" % (st, STATUS))
        if c.get("kind") not in KIND:
            bad(cid, "kind %r not in %s" % (c.get("kind"), KIND))
        for p in as_list(c.get("printed")):
            m = re.fullmatch(r"main\.tex:(\d+)(?:-(\d+))?", p)
            if not m:
                bad(cid, "printed %r is not main.tex:<line> or main.tex:<a>-<b>" % p)
                continue
            a, b = int(m[1]), int(m[2] or m[1])
            if a < 1 or b < a or (nlines is not None and b > nlines):
                bad(cid, "printed %r is outside legacy/orig/main.tex (%s lines)" % (p, nlines))
        if c.get("batch") and batches is not None and c["batch"] not in batches:
            bad(cid, "batch %r is not a `correct` target of papers/egf/programme/roadmap.toml" % c["batch"])
        lab = c.get("label")
        if lab and labels is not None and lab not in labels:
            bad(cid, "label %r is not a row of papers/egf/ledger" % lab)
        for r in as_list(c.get("basis")):
            if not re.fullmatch(r"(DEC|OQ)-\d+", r):
                bad(cid, "basis %r is not a DEC-n or OQ-n" % r)
            elif r not in rows:
                bad(cid, "basis %s is not a row of registers/DECISIONS.md" % r)
        if c.get("kind") == "false":
            ref = as_list(c.get("refutation"))
            if not ref:
                bad(cid, "a false entry names its refutation (a declaration of the strict library)")
            for n in ref:
                if n not in names:
                    bad(cid, "refutation %s is not a declaration of lean-egf/EGF" % n)
        if rank(st) >= rank("proved"):
            anchors = as_list(c.get("anchor"))
            if not anchors and c.get("kind") != "typo":
                bad(cid, "%s without an anchor" % st)
            for n in anchors:
                if n not in names:
                    bad(cid, "anchor %s is not a declaration of lean-egf/EGF (strict)" % n)
        if rank(st) >= rank("adopted"):
            if not any(str(r).startswith("DEC-") for r in as_list(c.get("basis"))):
                bad(cid, "%s without a DEC row in basis: only the author rules" % st)
            for k in ("corrected", "summary"):
                if not c.get(k):
                    bad(cid, "%s without %s" % (st, k))
            if not isinstance(c.get("added_hypotheses"), list):
                bad(cid, "%s without added_hypotheses (a list, empty when none)" % st)
        if rank(st) >= rank("applied"):
            if not is_commit(v2, c.get("v2_commit", "")):
                bad(cid, "%s, but v2_commit %r is not a commit of %s" % (st, c.get("v2_commit"), v2))
        if st == "reviewed" and not c.get("review"):
            bad(cid, "reviewed without review (when and how the author read it)")
    return errs


def set_status(text, cid, status, commit=None, review=None):
    """Edit the block of `cid` in place (comments and layout survive). Returns the new text."""
    lines = text.split("\n")
    start = next((i for i, l in enumerate(lines) if re.fullmatch(r'id\s*=\s*"%s"' % re.escape(cid), l.strip())), None)
    if start is None:
        raise SystemExit("corrections: no entry %s" % cid)
    end = next((i for i in range(start + 1, len(lines)) if lines[i].startswith("[")), len(lines))
    while end > start and (lines[end - 1].strip() == "" or lines[end - 1].lstrip().startswith("#")):
        end -= 1

    def put(key, value):
        nonlocal end
        rendered = '%s = "%s"' % (key, value.replace("\\", "\\\\").replace('"', '\\"'))
        for i in range(start, end):
            if re.match(r"%s\s*=" % key, lines[i]):
                lines[i] = rendered
                return
        lines.insert(end, rendered)
        end += 1
    put("status", status)
    if commit:
        put("v2_commit", commit)
    if review:
        put("review", review)
    return "\n".join(lines)


def errata(data, fmt="md"):
    rows = [c for c in data.get("correction", []) if rank(c.get("status")) >= rank("applied")]
    rows.sort(key=lambda c: int(re.sub(r"\D", "", as_list(c["printed"])[0].split(":")[1]) or 0))
    out = []
    for c in rows:
        where = c.get("where") or c.get("label") or as_list(c["printed"])[0]
        if fmt == "tex":
            out.append("\\item \\textbf{%s.} %s" % (where, c["summary"]))
        else:
            out.append("- **%s** (%s): %s" % (where, ", ".join(as_list(c["printed"])), c["summary"]))
    if fmt == "tex":
        return "\\begin{itemize}\n%s\n\\end{itemize}" % "\n".join(out) if out else ""
    return "\n".join(out)


def main(argv):
    global FILE, V2
    for flag in ("--file", "--v2"):
        if flag in argv:
            i = argv.index(flag)
            val = argv[i + 1] if os.path.isabs(argv[i + 1]) else os.path.join(os.getcwd(), argv[i + 1])
            if flag == "--file":
                FILE = val
            else:
                V2 = val
            argv = argv[:i] + argv[i + 2:]
    if not argv:
        sys.exit(__doc__)
    cmd = argv[0]
    data = load(FILE)
    if cmd == "check":
        errs = check(data, v2=V2)
        for e in errs:
            print("corrections: " + e)
        n = len(data.get("correction", []))
        print("corrections: %d entries, %s" % (n, "%d violation(s)" % len(errs) if errs else "all rules hold"))
        sys.exit(1 if errs else 0)
    if cmd == "status":
        by = {}
        for c in data.get("correction", []):
            by.setdefault(c.get("status"), []).append(c)
        for st in STATUS:
            for c in by.get(st, []):
                print("%-9s %-5s %-18s %-30s %s" % (st, c["id"], c["kind"], c.get("label") or c.get("where", ""),
                                                   ", ".join(as_list(c["printed"]))))
        print("corrections: " + ", ".join("%d %s" % (len(by.get(s, [])), s) for s in STATUS))
        return
    if cmd == "errata":
        fmt = argv[argv.index("--format") + 1] if "--format" in argv else "md"
        print(errata(data, fmt))
        return
    if cmd == "set":
        cid, status = argv[1], argv[2]
        opt = lambda k: argv[argv.index(k) + 1] if k in argv else None
        cur = next((c for c in data.get("correction", []) if c.get("id") == cid), None)
        if cur is None:
            sys.exit("corrections: no entry %s" % cid)
        if rank(status) < rank(cur.get("status")):
            sys.exit("corrections: %s is %s; a status only moves forward" % (cid, cur.get("status")))
        text = set_status(open(FILE, encoding="utf-8").read(), cid, status, opt("--commit"), opt("--review"))
        errs = check(tomllib.loads(text), v2=V2)
        mine = [e for e in errs if e.startswith(cid + ":")]
        if mine:
            for e in mine:
                print("corrections: " + e)
            sys.exit("corrections: refused; %s unchanged" % cid)
        with open(FILE, "w", encoding="utf-8") as fh:
            fh.write(text)
        print("corrections: %s -> %s" % (cid, status))
        return
    sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
