#!/usr/bin/env python3
"""The numbers of a progress report of the ETT programme, read off one commit of the repository.

    python3 reports/programme/numbers.py OUTDIR --rev REV   write OUTDIR/generated/ (below)
    python3 reports/programme/numbers.py --prose FILE...    exit 1 if a FILE shares a 12-word run
                                                            with a legacy draft (papers/*/legacy/orig)

Every figure is read from commit REV, never from the working tree, so two runs give the same bytes
whatever the shared checkout holds meanwhile. The files a figure comes from are extracted from REV
(`git archive`, read-only) into a temporary directory and read there by the tools of that commit:

  programme/ladder.toml                 tools/ladder.py: check(), summary(), matrix(), emitted()
  papers/*/certificate/binder.toml      tools/binder.py: `status` (its three counts) and `check`;
                                        the per-layer coverage below is read off binders()
  programme/roadmap.toml                tools/roadmap.py: load(), STATUS and KIND (their order);
                                        the date a target was done is its `commit`'s commit time
  papers/<slug>/ledger/                 tools/status_report.py: ledger_figures() (the figures of
                                        reports/status-2026-11), and the buckets of ledger.json
  registers/DECISIONS.md                the OPEN OQ rows that mention "ETT programme", and the DEC
                                        rows they cite
  programme/JOURNAL.md                  its entries, and its "for the author" lines

The two series (the ladder, the binders) are the same tools at every commit up to REV that touched
programme/ladder.toml or a binder: each commit's OWN tools/ladder.py (binder.py) run on that
commit's files, so a point of a series is what the tool said at the time, read the way it read then.

A title is the first clause of a row (text up to its first top-level ': ', ';' or '. ', outside
parentheses, brackets, quotes and code spans), with the row's own words: nothing is paraphrased.

Writes OUTDIR/generated/numbers.tex (one \\newcommand per figure: \\num... for counts, \\prog...
for commit ids and dates, and \\progPdfId, the md5 of REV, which report.tex makes the PDF's /ID so
that the PDF does not depend on the directory it is built in) and one table body per table
(*.tex). No model is called and no Lean is built.

The --prose check reads tools/no_legacy_prose.py's normalise() and shingles() from the working
tree, and every papers/*/legacy/orig/**/*.tex: the gate's own reading, applied to this report.
"""
import collections
import datetime
import glob
import hashlib
import importlib
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
ROOT = subprocess.run(["git", "-C", os.path.dirname(os.path.abspath(__file__)), "rev-parse",
                       "--show-toplevel"], capture_output=True, text=True, check=True).stdout.strip()
ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", PYTHONHASHSEED="0")
SLUGS = ("ers-predictability", "sbierski-mghd")   # the ledgered Sbierski papers with a binder
LEDGERS = SLUGS + ("ett",)                        # and the ETT ledger, whose labels the ladder carries
PATHS = ["tools", "programme", "registers", "lean-causal/Causal",
         "papers/*/ledger/ledger.json", "papers/*/ledger/LEDGER.md", "papers/*/certificate/binder.toml"]
LADDER_PATHS = ["tools/ladder.py", "programme/ladder.toml", "papers/ett/ledger/ledger.json",
                "lean-causal/Causal"]
BINDER_PATHS = ["tools/binder.py", "tools/ladder.py", "programme/ladder.toml", "programme/roadmap.toml",
                "papers/*/ledger/ledger.json", "papers/*/certificate/binder.toml", "lean-causal/Causal"]
MONTHS = ("January", "February", "March", "April", "May", "June", "July", "August", "September",
          "October", "November", "December")


# ------------------------------------------------------------------ git, read-only

def git(*args):
    return subprocess.run(["git", "-C", ROOT] + list(args), capture_output=True, text=True,
                          check=True).stdout


def commit_time(sha):
    """The commit time of `sha`, in UTC."""
    return datetime.datetime.fromtimestamp(int(git("log", "-1", "--format=%ct", sha).strip()),
                                           datetime.timezone.utc)


def extract(rev, paths, dest):
    """The files `paths` (pathspecs) of commit `rev`, written under `dest`."""
    tar = subprocess.run(["git", "-C", ROOT, "archive", "--format=tar", rev, "--"] + paths,
                         capture_output=True, check=True).stdout
    with tarfile.open(fileobj=io.BytesIO(tar)) as tf:
        tf.extractall(dest, filter="data")


def run_tool(snap, *argv):
    out = subprocess.run([sys.executable, os.path.join(snap, "tools", argv[0])] + list(argv[1:]),
                         cwd=snap, capture_output=True, text=True, env=ENV)
    return out.returncode, out.stdout


def touching(rev, pathspecs):
    """The commits up to `rev` that touched `pathspecs`, oldest first."""
    return git("log", "--reverse", "--format=%H", rev, "--", *pathspecs).split()


def utc(t):
    return t.strftime("%Y-%m-%d %H:%M")


def long_date(t):
    return "%d %s %d" % (t.day, MONTHS[t.month - 1], t.year)


# ------------------------------------------------------------------ text from files, for TeX

def first_clause(s):
    """The text up to the first top-level ': ', ';' or '. ' (outside (), [], quotes and `code`)."""
    depth, code, quote = 0, False, False
    for i, ch in enumerate(s):
        if ch == "`":
            code = not code
        elif code:
            continue
        elif ch == '"':
            quote = not quote
        elif ch in "“":
            quote = True
        elif ch in "”":
            quote = False
        elif quote:
            continue
        elif ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif depth == 0 and (ch == ";" or (ch in ":." and (i + 1 == len(s) or s[i + 1] == " "))):
            return s[:i].strip()
    return s.strip()


SPECIAL = {"\\": "\\textbackslash{}", "&": "\\&", "%": "\\%", "$": "\\$", "#": "\\#", "_": "\\_",
           "{": "\\{", "}": "\\}", "~": "\\textasciitilde{}", "^": "\\textasciicircum{}"}


def tex_plain(s):
    """Escaped, with a break point after '.', '_' and '/' inside a word (Lean names in titles)."""
    out = []
    for i, c in enumerate(s):
        out.append(SPECIAL.get(c, c))
        if c in "._/" and 0 < i < len(s) - 1 and not s[i - 1].isspace() and not s[i + 1].isspace():
            out.append("\\allowbreak{}")
    return "".join(out)


def tex(s):
    """A string of a file as TeX: `code` through \\lean (the name breaker), **bold** as \\textbf,
    "quotes" as curly quotes, every other special character escaped."""
    out = []
    for k, part in enumerate(re.split(r"`([^`]*)`", s)):
        if k % 2:
            assert not re.search(r"[%#{}\\]", part), "a code span TeX cannot pass to \\lean: " + part
            out.append("\\lean{%s}" % part)
            continue
        bits = re.split(r"\*\*(.+?)\*\*", part)
        for j, b in enumerate(bits):
            b = re.sub(r'"([^"]*)"', "“\\1”", b)
            out.append(("\\textbf{%s}" if j % 2 else "%s") % tex_plain(b))
    return "".join(out)


def tid(x):
    return "\\tid{%s}" % x


def macro_name(*parts):
    """\\numLadderFails from ('ladder', 'fails'): letters only, each part capitalised."""
    out = "num"
    for p in parts:
        for w in re.split(r"[^A-Za-z]+", str(p)):
            out += w[:1].upper() + w[1:]
    return out


def fmt(n):
    return "{:,}".format(n).replace(",", "\\,") if isinstance(n, int) else n


# ------------------------------------------------------------------ the snapshot's tools, in process

def tools_of(snap):
    sys.path.insert(0, os.path.join(snap, "tools"))
    mods = {m: importlib.import_module(m) for m in ("ladder", "binder", "roadmap", "status_report")}
    for m in mods.values():
        assert os.path.abspath(m.__file__).startswith(os.path.abspath(snap)), m.__file__
    return mods


# ------------------------------------------------------------------ the ladder

CHECK = re.compile(r"ladder: (\d+) properties, (\d+) implications, (\d+) counterexamples, "
                   r"(\d+) consequences; (\d+) of (\d+) ordered pairs classified( \(within one sort\))?")


def ladder_now(ld, macros, tables):
    data = ld.load()
    errs = ld.check(data)
    s = ld.summary(data, errs)
    for k in ("properties", "implies", "fails", "consequences", "transfers", "violations", "within",
              "ill_typed", "classified", "implied_standing", "fails_off"):
        macros[macro_name("ladder", k)] = s[k]
    macros[macro_name("ladder", "open entries")] = len(data.get("open", []))
    for sec in ("implies", "fails", "consequence", "transfer"):
        st = collections.Counter(e.get("status") for e in data.get(sec, []))
        for v in ld.STATUS:
            macros[macro_name("ladder", sec, v)] = st.get(v, 0)
    macros[macro_name("ladder", "consequence levels")] = len(
        {tuple(ld.ids_of(c.get("at"))) for c in data.get("consequence", [])})
    sort = ld.sort_of(data)
    m = ld.matrix(data)
    classes = ("implied", "fails", "open", "fails-off", "implied-standing", "unknown")
    within = collections.Counter(v for v in m.values() if v != "ill-typed")
    for v in classes:
        macros[macro_name("ladder", "class", v)] = within.get(v, 0)
    assert sum(within.values()) == s["within"]
    rows = []
    for so in ld.SORTS:
        ids = [p for p, x in sort.items() if x == so]
        c = collections.Counter(v for (a, b), v in m.items() if sort[a] == so and v != "ill-typed")
        macros[macro_name("ladder", "sort", so)] = len(ids)
        rows.append("\\texttt{%s} & %d & %d & %s \\\\" % (
            so, len(ids), sum(c.values()), " & ".join(str(c.get(v, 0)) for v in classes)))
    rows.append("\\midrule all & %d & %d & %s \\\\" % (
        s["properties"], s["within"], " & ".join(str(within.get(v, 0)) for v in classes)))
    tables["ladder-matrix"] = rows
    unknown = sorted(k for k, v in m.items() if v == "unknown")
    macros["progLadderUnknownPairs"] = ", ".join(
        "(\\lean{%s}, \\lean{%s})" % ab for ab in unknown) or "none"
    rules, skipped = ld.emitted(data, ld.lean_index())
    macros[macro_name("ladder", "rules")] = len(rules)
    macros[macro_name("ladder", "rules skipped")] = len(skipped)
    return data


def ladder_series(rev, done_by_commit, macros, tables):
    rows, first_within = [], None
    pts = []
    for sha in touching(rev, ["programme/ladder.toml"]):
        with tempfile.TemporaryDirectory(prefix="progladder.") as snap:
            extract(sha, LADDER_PATHS, snap)
            rc, out = run_tool(snap, "ladder.py", "check")
            line = out.strip().splitlines()[-1] if out.strip() else ""
            mt = CHECK.match(line)
            assert mt, "%s: unrecognised ladder check line %r" % (sha[:7], line)
            rc2, mout = run_tool(snap, "ladder.py", "matrix")
            assert rc2 == 0, "%s: ladder matrix failed" % sha[:7]
        cls = collections.Counter(l.split()[2] for l in mout.splitlines() if l.strip())
        within = bool(mt[7])
        if within and first_within is None:
            first_within = sha
        t = commit_time(sha)
        pts.append((sha, t, [int(x) for x in mt.groups()[:6]], within, cls, rc))
        rows.append("\\texttt{%s} & %s & %s & %s & %s%s & %d & %d & %d \\\\" % (
            sha[:7], utc(t), ", ".join(tid(x) for x in done_by_commit(sha)) or "---",
            " & ".join(mt.group(i) for i in range(1, 6)), mt[6], "" if within else "$^\\dagger$",
            cls.get("implied", 0), cls.get("fails", 0), cls.get("open", 0)))
        assert rc == 0, "%s: ladder check reported violations" % sha[:7]
    tables["ladder-series"] = rows
    macros[macro_name("ladder series commits")] = len(pts)
    macros["progLadderFirstRev"] = pts[0][0][:7]
    macros["progLadderFirstTime"] = utc(pts[0][1])
    first = pts[0][2]
    for k, v in zip(("properties", "implies", "fails", "consequences", "classified", "pairs"), first):
        macros[macro_name("ladder first", k)] = v
    macros["progLadderWithinRev"] = first_within[:7] if first_within else "---"
    # the commit whose tools/ladder.py first counts the pairs within one sort
    tool = [c for c in touching(rev, ["tools/ladder.py"])
            if "(within one sort)" in git("show", c + ":tools/ladder.py")]
    macros["progLadderToolWithinRev"] = tool[0][:7] if tool else "---"
    return pts


# ------------------------------------------------------------------ the binders

STATUS_LINE = re.compile(r"([\w-]+): (\d+) rows bound; layer 1 in Lean (\d+); layer 3 in Lean (\d+)$")


def binder_status(snap):
    rc, out = run_tool(snap, "binder.py", "status")
    assert rc == 0, "binder status failed"
    got = {}
    for l in out.splitlines():
        mt = STATUS_LINE.match(l.strip())
        assert mt, "unrecognised binder status line %r" % l
        got[mt[1]] = tuple(int(mt[i]) for i in (2, 3, 4))
    return got


def binders_now(snap, bd, ld, macros, tables):
    rc, out = run_tool(snap, "binder.py", "check")
    macros[macro_name("binder check violations")] = 0 if rc == 0 else len(
        [l for l in out.splitlines() if l.startswith("binder: ") and "violation" not in l])
    status = binder_status(snap)
    bs = bd.binders()
    ladder_ids = {p["id"] for p in ld.load().get("property", [])}
    macros[macro_name("binders")] = len(bs)
    lean = lambda xs: bool(xs) and all(not x.startswith("T-") for x in xs)
    cov, models, opn = [], [], []
    for slug, b in bs.items():
        rows = b.get("bind", [])
        led = json.load(open(os.path.join(snap, "papers", slug, "ledger", "ledger.json"),
                             encoding="utf-8"))["statements"]
        geo = [g for r in rows for g in r.get("geometric", [])]
        links = [(r["label"], p) for r in rows for p in r.get("localisation", [])]
        provided = {(r["label"], p) for r in rows for g in r.get("geometric", []) for p in g.get("proves", [])}
        opened = [x for r in rows for x in r.get("open_localisation", [])]
        f = {
            "ledger rows": len(led),
            "rows": len(rows),
            "layer one lean": sum(1 for r in rows if lean(r.get("ett", []))),
            "layer one target": sum(1 for r in rows if any(x.startswith("T-") for x in r.get("ett", []))),
            "layer two rows": sum(1 for r in rows if r.get("localisation")),
            "layer two links": len(links),
            "layer two provided": sum(1 for x in links if x in provided),
            "layer two open rows": sum(1 for r in rows if r.get("open_localisation")),
            "layer two open entries": len(opened),
            "layer two open names": len(set(opened)),
            "layer two open nonladder": len({x for x in opened if x not in ladder_ids}),
            "layer two properties": len({p for _, p in links}),
            "layer three rows": sum(1 for r in rows if r.get("geometric")),
            "layer three lean rows": sum(1 for r in rows if r.get("geometric")
                                and all(lean(g.get("by", [])) for g in r["geometric"])),
            "layer three entries": len(geo),
            "layer three lean entries": sum(1 for g in geo if lean(g.get("by", []))),
            "layer three models": len({g.get("model") for g in geo}),
            "proposed": len(b.get("proposed", [])),
            "layer two open proposed": len({x for x in opened if x not in ladder_ids}
                                           & {q.get("id") for q in b.get("proposed", [])}),
        }
        tool = status[slug]
        assert (f["rows"], f["layer one lean"], f["layer three lean rows"]) == tool, (slug, tool)
        for k, v in f.items():
            macros[macro_name("binder", slug, k)] = v
        opn.append("\\texttt{%s} & %d & %d & %d & %d & %d & %d \\\\" % (
            slug, f["layer two open rows"], f["layer two open entries"], f["layer two open names"],
            f["layer two open nonladder"], f["layer two open proposed"], f["proposed"]))
        cov.append("\\texttt{%s} & %d & %d & %d & %d & %d/%d & %d & %d & %d/%d \\\\" % (
            slug, f["ledger rows"], f["rows"], f["layer one lean"], f["layer one target"], f["layer two provided"],
            f["layer two links"], f["layer two open entries"], f["layer three lean rows"], f["layer three lean entries"], f["layer three entries"]))
        per = collections.OrderedDict()
        for g in geo:
            e = per.setdefault(g.get("model"), [0, 0, 0])
            e[0] += 1
            e[1] += lean(g.get("by", []))
            e[2] += any(x.startswith("T-") for x in g.get("by", []))
        for mdl in sorted(per):
            models.append("\\texttt{%s} & \\texttt{%s} & %d & %d & %d \\\\" % (slug, mdl, *per[mdl]))
    tables["binder-coverage"] = cov
    tables["binder-models"] = models
    tables["binder-open"] = opn
    return status


def binder_series(rev, done_by_commit, macros, tables):
    rows = []
    shas = touching(rev, ["papers/*/certificate/binder.toml"])
    for sha in shas:
        with tempfile.TemporaryDirectory(prefix="progbinder.") as snap:
            extract(sha, BINDER_PATHS, snap)
            st = binder_status(snap)
        cells = " & ".join("%d & %d & %d" % st[s] if s in st else "--- & --- & ---" for s in SLUGS)
        rows.append("\\texttt{%s} & %s & %s & %s \\\\" % (
            sha[:7], utc(commit_time(sha)), ", ".join(tid(x) for x in done_by_commit(sha)) or "---", cells))
    tables["binder-series"] = rows
    macros[macro_name("binder series commits")] = len(shas)


# ------------------------------------------------------------------ the ledgers

def ledgers_now(snap, sr, macros, tables):
    rows = []
    for slug in LEDGERS:
        f = sr.ledger_figures(slug)
        assert f, "no ledger for " + slug
        led = json.load(open(os.path.join(snap, "papers", slug, "ledger", "ledger.json"), encoding="utf-8"))
        st = led["statements"]
        macros["prog" + macro_name("ledger", slug, "lean rev")[3:]] = led["lean"]["git_commit"][:7]
        b = collections.Counter(r.get("bucket") or "none" for r in st)
        f.update({"bucket " + k: b.get(k, 0) for k in ("A", "B", "C", "D", "T", "none")})
        for k, v in f.items():
            macros[macro_name("ledger", slug, k)] = v
        rows.append("\\texttt{%s} & %d & %d & %d & %d & %s & \\textbf{%d/%d} \\\\" % (
            slug, f["statements"], f["stated"], f["closedlean"], f["partial"],
            " & ".join(str(b.get(k, 0)) for k in ("A", "B", "C", "D", "T", "none")), f["closed"], f["target"]))
    tables["ledgers"] = rows


# ------------------------------------------------------------------ the roadmap

def roadmap_now(snap, rm, rev_time, macros, tables):
    data = rm.load(os.path.join(snap, "programme", "roadmap.toml"))
    ts = data.get("target", [])
    macros[macro_name("targets")] = len(ts)
    by = collections.Counter(t["status"] for t in ts)
    for s in rm.STATUS:
        macros[macro_name("targets", s)] = by.get(s, 0)
    kinds = [k for k in rm.KIND if any(t["kind"] == k for t in ts)]
    rows = []
    for k in kinds:
        c = collections.Counter(t["status"] for t in ts if t["kind"] == k)
        rows.append("\\texttt{%s} & %s & %d \\\\" % (k, " & ".join(str(c.get(s, 0)) for s in rm.STATUS),
                                                    sum(c.values())))
    rows.append("\\midrule all & %s & %d \\\\" % (" & ".join(str(by.get(s, 0)) for s in rm.STATUS), len(ts)))
    tables["targets-kind"] = rows
    macros[macro_name("target kinds")] = len(kinds)
    # done: by the commit time of the commit each records
    done = []
    for t in ts:
        if t["status"] == "done":
            full = git("rev-parse", t["commit"] + "^{commit}").strip()
            done.append((commit_time(full), t["id"], t["kind"], full))
    done.sort()
    today = [d for d in done if d[0].date() == rev_time.date()]
    macros[macro_name("targets done on rev date")] = len(today)
    macros[macro_name("targets done before rev date")] = len(done) - len(today)
    tables["targets-done-today"] = ["%s & \\texttt{%s} & \\texttt{%s} & %s \\\\" % (
        tid(i), k, c[:7], t.strftime("%H:%M")) for t, i, k, c in today]
    tables["targets-ready"] = ["%s & \\texttt{%s} & %d & %s \\\\" % (
        tid(t["id"]), t["kind"], t["priority"], tex(first_clause(t["title"])))
        for t in sorted((t for t in ts if t["status"] == "ready"), key=lambda t: (t["priority"], t["id"]))]
    tables["targets-ruling"] = ["%s & \\texttt{%s} & %s \\\\" % (tid(t["id"]), t["kind"], tex(first_clause(t["question"])))
                                for t in sorted((t for t in ts if t["status"] == "needs-ruling"), key=lambda t: t["id"])]

    def by_commit(sha):
        return sorted(t["id"] for t in ts if t.get("status") == "done" and t.get("commit")
                      and sha.startswith(t["commit"]))
    blocked = collections.defaultdict(list)
    for t in ts:
        if t["status"] == "blocked":
            blocked[t.get("oq", "")].append(t["id"])
    return by_commit, blocked


# ------------------------------------------------------------------ the registers and the journal

def cells(line):
    return [c.strip() for c in re.split(r"(?<!\\)\|", line.strip())[1:-1]]


def questions_now(snap, blocked, macros, tables):
    text = open(os.path.join(snap, "registers", "DECISIONS.md"), encoding="utf-8").read()
    decs = {}
    oqs = []
    for line in text.splitlines():
        if line.startswith("| DEC-"):
            c = cells(line)
            decs[c[0]] = c
        elif line.startswith("| OQ-") and "ETT programme" in line:
            c = cells(line)
            assert len(c) == 5, "unrecognised OQ row " + c[0]
            if c[4].startswith("OPEN"):
                oqs.append((c, sorted(set(re.findall(r"DEC-\d+", line)), key=lambda d: int(d[4:]))))
    oqs.sort(key=lambda x: int(x[0][0][3:]))
    macros[macro_name("oq open")] = len(oqs)
    dates = collections.Counter(c[1] for c, _ in oqs)
    macros[macro_name("oq raised dates")] = len(dates)
    rows = []
    for c, ds in oqs:
        title = first_clause(c[2])
        title = title[len("ETT programme, "):] if title.startswith("ETT programme, ") else title
        rows.append("\\textbf{%s} & %s & %s & %s & %s \\\\" % (
            c[0], c[1], tex(title), ", ".join(ds) or "---", ", ".join(tid(x) for x in blocked.get(c[0], [])) or "---"))
    tables["oq"] = rows
    cited = sorted({d for _, ds in oqs for d in ds}, key=lambda d: int(d[4:]))
    macros[macro_name("oq cited decs")] = len(cited)
    tables["dec"] = ["\\textbf{%s} & %s & %s \\\\" % (d, decs[d][1], tex(first_clause(decs[d][2]))) for d in cited]
    macros[macro_name("targets blocked on oq")] = sum(len(v) for k, v in blocked.items() if k in {c[0] for c, _ in oqs})


def journal_now(snap, macros, tables):
    text = open(os.path.join(snap, "programme", "JOURNAL.md"), encoding="utf-8").read()
    heads = re.findall(r"^## (\d{4}-\d\d-\d\d \d\d:\d\d) · ([^·\n]+)", text, re.M)
    macros[macro_name("journal entries")] = len(heads)
    macros[macro_name("journal waves")] = sum(1 for _, k in heads if "wave" in k)
    macros[macro_name("journal plans")] = sum(1 for _, k in heads if "plan" in k)
    macros["progJournalFirst"] = heads[0][0] if heads else "---"
    macros["progJournalLast"] = heads[-1][0] if heads else "---"
    rows, named = [], []
    cur = None
    for line in text.splitlines():
        h = re.match(r"^## (\d{4}-\d\d-\d\d \d\d:\d\d)", line)
        if h:
            cur = h[1]
        mt = re.match(r"^- for the author: (.*)$", line)
        if mt:
            ids = re.findall(r"\bOQ-\d+", mt[1])
            if ids:
                named += [i for i in ids if i not in named]
            else:
                rows.append("%s & %s \\\\" % (cur, tex(first_clause(mt[1]))))
    macros[macro_name("journal author lines")] = len(re.findall(r"^- for the author: ", text, re.M))
    macros["progJournalAuthorOqs"] = ", ".join(sorted(named, key=lambda x: int(x[3:]))) or "none"
    tables["journal-author"] = rows


# ------------------------------------------------------------------ main

def write(outdir, macros, tables):
    gen = os.path.join(outdir, "generated")
    os.makedirs(gen, exist_ok=True)
    head = "% generated by reports/programme/numbers.py -- do not edit\n"
    with open(os.path.join(gen, "numbers.tex"), "w", encoding="utf-8") as fh:
        fh.write(head)
        for k in sorted(macros):
            fh.write("\\newcommand{\\%s}{%s}\n" % (k, fmt(macros[k])))
    for name in sorted(tables):
        with open(os.path.join(gen, name + ".tex"), "w", encoding="utf-8") as fh:
            fh.write(head + "\n".join(tables[name]) + ("\n" if tables[name] else ""))
    return gen


def generate(outdir, rev):
    sha = git("rev-parse", rev + "^{commit}").strip()
    t = commit_time(sha)
    start = touching(sha, ["programme/README.md"])[0]
    macros = {"progRev": sha[:7], "progRevTime": utc(t), "progRevDate": long_date(t),
              "progPdfId": hashlib.md5(sha.encode()).hexdigest().upper(),
              "progStartRev": start[:7], "progStartTime": utc(commit_time(start))}
    tables = {}
    with tempfile.TemporaryDirectory(prefix="progsnap.") as snap:
        extract(sha, PATHS, snap)
        mods = tools_of(snap)
        ladder_now(mods["ladder"], macros, tables)
        binders_now(snap, mods["binder"], mods["ladder"], macros, tables)
        ledgers_now(snap, mods["status_report"], macros, tables)
        by_commit, blocked = roadmap_now(snap, mods["roadmap"], t, macros, tables)
        questions_now(snap, blocked, macros, tables)
        journal_now(snap, macros, tables)
    ladder_series(sha, by_commit, macros, tables)
    binder_series(sha, by_commit, macros, tables)
    gen = write(outdir, macros, tables)
    print("numbers: %d macros, %d tables from %s (%s UTC) -> %s" % (
        len(macros), len(tables), sha[:7], utc(t), os.path.relpath(gen)))


def prose(files, n=12):
    """No run of n words shared with any legacy draft, by tools/no_legacy_prose.py's own reading."""
    sys.path.insert(0, os.path.join(ROOT, "tools"))
    nlp = importlib.import_module("no_legacy_prose")
    legacy = {}
    for p in sorted(glob.glob(os.path.join(ROOT, "papers", "*", "legacy", "orig", "**", "*.tex"), recursive=True)):
        for sh in nlp.shingles(nlp.normalise(open(p, encoding="utf-8", errors="replace").read()), n):
            legacy.setdefault(sh, os.path.relpath(p, ROOT))
    hits = 0
    for f in files:
        words = nlp.normalise(open(f, encoding="utf-8").read())
        for i in range(len(words) - n + 1):
            sh = tuple(words[i:i + n])
            if sh in legacy:
                print("numbers: FAIL %s word %d shares %d words with %s: %s" % (f, i, n, legacy[sh], " ".join(sh)))
                hits += 1
    print("numbers: %d file(s), %s" % (len(files), "%d shared run(s)" % hits if hits else
                                         "no %d-word run shared with papers/*/legacy/orig" % n))
    return 1 if hits else 0


def main(argv):
    if argv and argv[0] == "--prose":
        sys.exit(prose(argv[1:]))
    if not argv or argv[0].startswith("-") or "--rev" not in argv:
        sys.exit(__doc__)
    generate(argv[0], argv[argv.index("--rev") + 1])


if __name__ == "__main__":
    main(sys.argv[1:])
