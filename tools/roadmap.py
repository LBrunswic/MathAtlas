#!/usr/bin/env python3
"""The roadmap of the /atlas-team loop: check it, summarise it, pick the next target, move one.

    python3 tools/roadmap.py check                  every rule below; exit 1 on a violation
    python3 tools/roadmap.py status                 one line per target, grouped by status
    python3 tools/roadmap.py next [--owner OWNER]   the id of the next dispatchable target, or nothing
    python3 tools/roadmap.py set ID STATUS [--evidence TEXT] [--oq OQ-n] [--commit SHA]
    python3 tools/roadmap.py gates LOG              a `make -k check` log adds no failure to [gates] known_red

The file is roadmap/roadmap.toml (schema in its header). `set` edits the target's block in place,
so comments and layout survive; it re-checks the whole file and refuses an edit that breaks a rule.
The loop moves statuses; only the author rules, so `set` never turns `needs-ruling` into anything
but `ready`/`planned`/`dropped` without `--evidence` naming the DEC row.
"""
import os
import re
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILE = os.path.join(ROOT, "roadmap", "roadmap.toml")
STATUS = ["planned", "ready", "active", "needs-ruling", "blocked", "done", "dropped"]
OWNER = ["closer", "planner", "builder", "master", "author"]
KIND = ["close", "package", "research", "tooling", "author"]
REQUIRED = ["id", "title", "stream", "kind", "status", "owner", "priority", "evidence", "added", "proposed_by"]


def load(path=FILE):
    with open(path, "rb") as fh:
        return tomllib.load(fh)


def ledger_labels(root, paper):
    import json
    p = os.path.join(root, "papers", paper, "ledger", "ledger.json")
    if not os.path.exists(p):
        return None
    return {r["label"] for r in json.load(open(p, encoding="utf-8"))["statements"]}


def open_questions(root):
    """OQ id -> status, read off registers/DECISIONS.md's question table."""
    p = os.path.join(root, "registers", "DECISIONS.md")
    out = {}
    if os.path.exists(p):
        for line in open(p, encoding="utf-8"):
            m = re.match(r"\|\s*(OQ-\d+)\s*\|.*\|\s*([A-Z]+)[^|]*\|\s*$", line)
            if m:
                out[m[1]] = m[2]
    return out


def check(data, root=ROOT):
    errs = []
    bad = lambda tid, msg: errs.append("%s: %s" % (tid, msg))
    targets = data.get("target", [])
    ids = [t.get("id", "?") for t in targets]
    for tid in set(i for i in ids if ids.count(i) > 1):
        bad(tid, "duplicate id")
    known = set(ids)
    oqs = open_questions(root)
    active = [t["id"] for t in targets if t.get("status") == "active"]
    if len(active) > 1:
        bad(",".join(active), "more than one target is active")
    for t in targets:
        tid = t.get("id", "?")
        for k in REQUIRED:
            if k not in t or t[k] in ("", None):
                bad(tid, "missing %s" % k)
        if not re.fullmatch(r"T-[a-z0-9-]+", tid):
            bad(tid, "id must match T-[a-z0-9-]+")
        if t.get("status") not in STATUS:
            bad(tid, "status %r not in %s" % (t.get("status"), STATUS))
        if t.get("owner") not in OWNER:
            bad(tid, "owner %r not in %s" % (t.get("owner"), OWNER))
        if t.get("kind") not in KIND:
            bad(tid, "kind %r not in %s" % (t.get("kind"), KIND))
        if t.get("kind") == "author" and t.get("owner") != "author":
            bad(tid, "an author target is owned by the author")
        if not isinstance(t.get("priority"), int):
            bad(tid, "priority must be an integer")
        paper = t.get("paper")
        labels = t.get("labels", [])
        if paper:
            if not os.path.isdir(os.path.join(root, "papers", paper)):
                bad(tid, "paper %r has no directory under papers/" % paper)
            have = ledger_labels(root, paper)
            if have is not None:
                for lab in labels:
                    if lab not in have:
                        bad(tid, "label %r is not in papers/%s/ledger" % (lab, paper))
            elif labels:
                bad(tid, "labels given but papers/%s has no ledger" % paper)
        if t.get("kind") == "close" and not labels:
            bad(tid, "a close target names its ledger labels")
        for d in t.get("depends", []):
            if d not in known:
                bad(tid, "depends on unknown %s" % d)
        st = t.get("status")
        if st == "needs-ruling" and not t.get("question"):
            bad(tid, "needs-ruling without a question")
        if st == "blocked":
            oq = t.get("oq", "")
            if oqs.get(oq) != "OPEN":
                bad(tid, "blocked on %r, which is not an OPEN question of registers/DECISIONS.md" % oq)
        if st == "done":
            c = t.get("commit", "")
            ok = c and subprocess.run(["git", "-C", root, "cat-file", "-e", c + "^{commit}"],
                                      capture_output=True).returncode == 0
            if not ok:
                bad(tid, "done without an existing commit")
        if st == "ready":
            for d in t.get("depends", []):
                dep = next((x for x in targets if x.get("id") == d), None)
                if dep and dep.get("status") != "done":
                    bad(tid, "ready while its dependency %s is %s" % (d, dep.get("status")))
    # dependency cycles
    graph = {t.get("id"): t.get("depends", []) for t in targets}
    state = {}

    def visit(n, path):
        if state.get(n) == 1:
            bad(n, "dependency cycle: " + " -> ".join(path + [n]))
            return
        if state.get(n) == 2:
            return
        state[n] = 1
        for m in graph.get(n, []):
            visit(m, path + [n])
        state[n] = 2
    for n in graph:
        visit(n, [])
    return errs


def next_target(data, owner=None):
    done = {t["id"] for t in data.get("target", []) if t.get("status") == "done"}
    cands = [t for t in data.get("target", [])
             if t.get("status") == "ready" and (owner is None or t.get("owner") in owner.split(","))
             and all(d in done for d in t.get("depends", []))]
    cands.sort(key=lambda t: (t.get("priority", 99), data["target"].index(t)))
    return cands[0]["id"] if cands else None


def set_status(text, tid, status, evidence=None, oq=None, commit=None):
    """Edit the block of `tid` in place. Returns the new text."""
    lines = text.split("\n")
    start = next((i for i, l in enumerate(lines) if re.fullmatch(r'id\s*=\s*"%s"' % re.escape(tid), l.strip())), None)
    if start is None:
        raise SystemExit("roadmap: no target %s" % tid)
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
    if evidence:
        put("evidence", evidence)
    if oq:
        put("oq", oq)
    if commit:
        put("commit", commit)
    return "\n".join(lines)


def gate_failures(log_text):
    """Top-level gate targets that failed in a `make -k check` log, and the papers papers-check failed.

    Only `make: ***` lines count (a nested `make[1]: ***` is a gate run inside a test, already
    reported by the outer target)."""
    targets = sorted(set(re.findall(r"^make: \*\*\* \[[^\]]*?:\d+: ([\w-]+)\]", log_text, re.M)))
    papers, cur = set(), None
    for line in log_text.split("\n"):
        m = re.match(r"^papers/([\w-]+)\s*$", line)
        if m:
            cur = m[1]
        elif cur and re.match(r"^\s+FAIL\b", line):
            papers.add(cur)
    return targets, sorted(papers)


def new_red(data, log_text):
    known = data.get("gates", {}).get("known_red", [])
    targets, papers = gate_failures(log_text)
    out = [t for t in targets if not any(k.startswith(t + ":") for k in known)]
    allowed = set(re.findall(r"papers/([\w-]+)", " ".join(k for k in known if k.startswith("papers-check:"))))
    out += ["papers-check: papers/%s" % p for p in papers if p not in allowed]
    return out


def main(argv):
    if not argv:
        sys.exit(__doc__)
    cmd = argv[0]
    data = load()
    if cmd == "check":
        errs = check(data)
        for e in errs:
            print("roadmap: " + e)
        print("roadmap: %d targets, %s" % (len(data.get("target", [])), "%d violation(s)" % len(errs) if errs else "all rules hold"))
        sys.exit(1 if errs else 0)
    if cmd == "status":
        by = {}
        for t in data.get("target", []):
            by.setdefault(t["status"], []).append(t)
        for st in STATUS:
            for t in sorted(by.get(st, []), key=lambda t: t["priority"]):
                print("%-12s p%-2d %-26s %-8s %s" % (st, t["priority"], t["id"], t["owner"], t["title"]))
        return
    if cmd == "next":
        owner = argv[argv.index("--owner") + 1] if "--owner" in argv else None
        n = next_target(data, owner)
        if n:
            print(n)
        return
    if cmd == "gates":
        bad = new_red(data, open(argv[1], encoding="utf-8", errors="replace").read())
        for b in bad:
            print("roadmap: NEW RED " + b)
        print("roadmap: hub gate %s" % ("adds %d failure(s)" % len(bad) if bad else "no new red"))
        sys.exit(1 if bad else 0)
    if cmd == "set":
        tid, status = argv[1], argv[2]
        opt = lambda k: argv[argv.index(k) + 1] if k in argv else None
        cur = next((t for t in data["target"] if t["id"] == tid), None)
        if cur is None:
            sys.exit("roadmap: no target %s" % tid)
        if cur["status"] == "needs-ruling" and status in ("ready", "planned") and not re.search(r"DEC-\d+", opt("--evidence") or ""):
            sys.exit("roadmap: %s needs a ruling; --evidence must name the DEC row that rules it" % tid)
        text = set_status(open(FILE, encoding="utf-8").read(), tid, status, opt("--evidence"), opt("--oq"), opt("--commit"))
        errs = check(tomllib.loads(text))
        if errs:
            sys.exit("roadmap: refused, the edit breaks a rule:\n  " + "\n  ".join(errs))
        open(FILE, "w", encoding="utf-8").write(text)
        print("roadmap: %s -> %s" % (tid, status))
        return
    sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
