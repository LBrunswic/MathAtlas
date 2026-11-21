#!/usr/bin/env python3
"""The roadmap of the /atlas-team loop: check it, summarise it, pick the next target, move one.

    python3 tools/roadmap.py check                  every rule below; exit 1 on a violation
    python3 tools/roadmap.py status                 one line per target, grouped by status
    python3 tools/roadmap.py next [--owner OWNER]   the id of the next dispatchable target, or nothing
    python3 tools/roadmap.py wave [--owner O1,O2]   the targets of the next wave: up to MAX_PARALLEL independent ones
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
# `--file programme/roadmap.toml` (anywhere on the command line) selects the ETT programme's roadmap.
LADDER = os.path.join(ROOT, "programme", "ladder.toml")
STATUS = ["planned", "ready", "active", "needs-ruling", "blocked", "done", "dropped"]
OWNER = ["closer", "planner", "builder", "master", "author",
         "keeper", "tactician", "publisher"]          # the last three: /ett-programme (programme/README.md)
KIND = ["close", "package", "research", "tooling", "author",
        # /ett-programme: layer 1 (causal-topological theorem), layer 3 (geometric lemma for one model),
        # the ladder, a paper's binder, Lean automation, a publication
        "abstract", "localisation", "ladder", "binder", "tactic", "publish"]
# The wave: how many targets one /atlas-team iteration may run at once, and how many of them may
# share one Lean package (node1: 32 threads, 94 GB; lake builds run under taskset -c 0-11, and each
# closer/auditor elaborates one module at a time). The skill reads these; change them here only.
MAX_PARALLEL = 6
MAX_PER_PACKAGE = 3
# paper -> the Lean package its closers write in (a target may override it with `package = "..."`)
PACKAGE_OF = {"ett": "lean-causal", "barbot": "lean-causal", "gx": "lean-gx", "bbs": "lean-gx",
              "benzecri": "lean-benzecri", "egf": "lean-egf", "syracuse": "lean-syracuse",
              "yamabe": "lean-yamabe"}
# ledgered Sbierski papers (programme): their ETT layers live in lean-causal
PACKAGE_OF.update({s: "lean-causal" for s in ("sbierski-mghd", "ers-predictability", "sbierski-schwarzschild",
                                               "sbierski-boundary", "sbierski-flrw", "sbierski-extensions",
                                               "sbierski-holonomy", "gls-timelike")})
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
    if len(active) > MAX_PARALLEL:
        bad(",".join(active), "more than MAX_PARALLEL=%d targets are active" % MAX_PARALLEL)
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
            waits_setup = t.get("status") in ("planned", "needs-ruling", "blocked") and any(
                x.get("id") in t.get("depends", []) and x.get("kind") == "package" for x in targets)
            if not os.path.isdir(os.path.join(root, "papers", paper)) and not waits_setup:
                bad(tid, "paper %r has no directory under papers/ (allowed only while it waits on a package target)" % paper)
            have = ledger_labels(root, paper)
            if have is not None:
                for lab in labels:
                    if lab not in have:
                        bad(tid, "label %r is not in papers/%s/ledger" % (lab, paper))
            elif labels:
                bad(tid, "labels given but papers/%s has no ledger" % paper)
        if t.get("kind") == "close" and not labels:
            bad(tid, "a close target names its ledger labels")
        if t.get("kind") in ("abstract", "localisation"):
            lad = ladder_ids(root)
            need = "uses" if t["kind"] == "abstract" else "provides"
            if need not in t:
                bad(tid, "an %s target lists the ladder properties it %s (`%s = [...]`, empty for pure topology)"
                    % (t["kind"], need, need))
            for p in t.get(need, []) + (t.get("uses", []) if need == "provides" else []):
                if lad is not None and p not in lad:
                    bad(tid, "%r is not a property of programme/ladder.toml" % p)
            if t["kind"] == "localisation" and not t.get("model"):
                bad(tid, "a localisation target names its model class (`model`)")
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
    errs.extend(stale_blockers(data, root))
    return errs


def stale_blockers(data, root=ROOT):
    """Ledger rows whose `blocked_on` names a target, of either roadmap, that is done or dropped:
    such a row misreports what blocks it, and so does every count of rulings read off the ledgers
    (T-ledger-stale-blockers: 17 ETT rows named the done T-ett-port-e0). The roadmap being checked
    gives its own statuses; the other roadmap is read from its file."""
    import glob
    import json
    status = {}
    for path in (os.path.join(root, "roadmap", "roadmap.toml"), os.path.join(root, "programme", "roadmap.toml")):
        if os.path.exists(path):
            status.update({t.get("id"): t.get("status") for t in load(path).get("target", [])})
    status.update({t.get("id"): t.get("status") for t in data.get("target", [])})
    out = []
    for p in sorted(glob.glob(os.path.join(root, "papers", "*", "ledger", "ledger.json"))):
        paper = p.split(os.sep)[-3]
        for s in json.load(open(p, encoding="utf-8")).get("statements", []):
            for tid in sorted(set(re.findall(r"\bT-[a-z0-9]+(?:-[a-z0-9]+)*", s.get("blocked_on") or ""))):
                if status.get(tid) in ("done", "dropped"):
                    out.append("papers/%s %s: blocked_on names %s, which is %s; name its current blocker"
                               % (paper, s.get("label"), tid, status[tid]))
    return out


def ladder_ids(root=ROOT):
    p = os.path.join(root, "programme", "ladder.toml")
    if not os.path.exists(p):
        return None
    with open(p, "rb") as fh:
        return {x["id"] for x in tomllib.load(fh).get("property", [])}


def next_target(data, owner=None):
    done = {t["id"] for t in data.get("target", []) if t.get("status") == "done"}
    cands = [t for t in data.get("target", [])
             if t.get("status") == "ready" and (owner is None or t.get("owner") in owner.split(","))
             and all(d in done for d in t.get("depends", []))]
    cands.sort(key=lambda t: (t.get("priority", 99), data["target"].index(t)))
    return cands[0]["id"] if cands else None


def package_of(t):
    """The Lean package a target writes in; None for targets that write no Lean (builder, planner)."""
    if t.get("owner") in ("builder", "planner", "author", "keeper", "publisher"):
        return None
    return t.get("package") or PACKAGE_OF.get(t.get("paper", ""))


def wave(data, owners=("closer", "master", "builder", "tactician", "keeper", "publisher"), limit=MAX_PARALLEL, per_package=MAX_PER_PACKAGE):
    """The next wave: ready targets in priority order whose dependencies are done, pairwise
    independent -- no shared label, no dependency between them, at most `per_package` per Lean
    package, an `exclusive` target alone in its package, at most one builder (it owns
    reports/atlas) -- and none touching a package that a still-active target holds."""
    targets = data.get("target", [])
    done = {t["id"] for t in targets if t.get("status") == "done"}
    active = [t for t in targets if t.get("status") == "active"]
    load = {}
    for t in active:
        p = package_of(t)
        if p:
            load[p] = load.get(p, 0) + (per_package if t.get("exclusive") else 1)
    chosen = []
    labels = {(t.get("paper"), l) for t in active for l in t.get("labels", [])}
    cands = [t for t in targets if t.get("status") == "ready" and t.get("owner") in owners
             and all(d in done for d in t.get("depends", []))]
    cands.sort(key=lambda t: (t.get("priority", 99), targets.index(t)))
    for t in cands:
        if len(chosen) + len(active) >= limit:
            break
        labs = {(t.get("paper"), l) for l in t.get("labels", [])}
        if labs & labels:
            continue
        solo = ("builder", "keeper", "publisher", "tactician")   # each owns one area: one at a time
        if t.get("owner") in solo and any(c.get("owner") == t.get("owner") for c in chosen + active):
            continue
        p = package_of(t)
        if p:
            cost = per_package if t.get("exclusive") else 1
            if load.get(p, 0) + cost > per_package:
                continue
            load[p] = load.get(p, 0) + cost
        chosen.append(t)
        labels |= labs
    return [t["id"] for t in chosen]


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
    global FILE
    if "--file" in argv:
        i = argv.index("--file")
        FILE = os.path.join(ROOT, argv[i + 1]) if not os.path.isabs(argv[i + 1]) else argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    if not argv:
        sys.exit(__doc__)
    cmd = argv[0]
    data = load(FILE)
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
    if cmd == "wave":
        owners = tuple(argv[argv.index("--owner") + 1].split(",")) if "--owner" in argv else ("closer", "master", "builder")
        for tid in wave(data, owners):
            t = next(x for x in data["target"] if x["id"] == tid)
            print("%-28s %-8s %s" % (tid, t["owner"], package_of(t) or "-"))
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
