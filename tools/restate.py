#!/usr/bin/env python3
"""Restatements: every paper statement found false or imprecise as written, rewritten in natural
language from the rigorous Lean that replaced it. Kept by /restate (.claude/skills/restate).

    python3 tools/restate.py detect [SLUG...] [--all]     candidates the register does not hold yet
    python3 tools/restate.py seed SLUG... [--all]         append them as `found` entries
    python3 tools/restate.py context SLUG LABEL [--full]  the dossier an agent works from
    python3 tools/restate.py decl SLUG NAME...            one declaration: docstring, statement, variables in scope
    python3 tools/restate.py check [SLUG...] [--file F]   every rule below; exit 1 on a violation
    python3 tools/restate.py check SLUG --label LABEL     the rules of one entry (an agent's own work)
    python3 tools/restate.py status [SLUG...]             counts per paper and status
    python3 tools/restate.py set SLUG LABEL STATUS [--check FILE] [--review TEXT] [--reason TEXT]
    python3 tools/restate.py render SLUG...               write papers/<slug>/certificate/RESTATED.md

The register is papers/<slug>/certificate/restatements.toml, one [[entry]] per ledger label:

    label            a row of the paper's ledger
    status           found → drafted → checked → reviewed, or dismissed (with `reason`) or
                     blocked (with `oq`, an OPEN question: the reading is the author's)
    kind             false          the printed statement is refuted (`refutation`, or `refutation_note`
                                    for an informal counterexample)
                     underspecified true only under a reading, which a DEC row in `basis` rules
                     imprecise      a hypothesis, a quantifier or a convention is implicit or misplaced
    printed          File.tex:a-b, the ledger's span; `printed_sha256` its statement digest. Both are
                     checked against the ledger: a changed source stales the entry
    finding          one or two lines: what is wrong as written
    refutation       Lean declarations refuting the printed form
    anchor           Lean declarations the rewritten statement states (the rigorous form)
    basis            DEC/OQ rows behind the form; `correction` an EGF register id (papers/egf)
    reading          a reading the rewrite takes that no DEC row rules (e.g. "tame knot = locally
                     flat"): shown first to the author, who rules it (a DEC row in `basis`) before
                     `reviewed`
    rewritten        the natural-language statement, LaTeX, saying exactly what `anchor` says
    changes          one line per change from the printed form ("+ hypothesis: …", "- conclusion: …",
                     "~ …")
    check            from `checked` on: a CHECK file under papers/<slug>/certificate/restate/, written
                     by statement-checker, verdict `faithful`, for this label, these anchors and the
                     sha256 of this `rewritten`: editing the text after the check stales it
    review           from `reviewed` on: when and how the author read it

Detection is deterministic and reads the curated ledger (no model): a row is a STRONG candidate when
its findings or notes say "FALSE", "false/wrong/incorrect as printed/written/stated", or when one of
its declarations is a refutation (a name component starting `not_`, or containing `Cex`/`cex`/
`counterexample`). `--all` adds the weak signals (refuted, counterexample, corrected form, missing or
added hypothesis, narrowing, reading). The gate requires every strong candidate to be registered:
dismissing one is a recorded decision with a reason, never a silence.

Declarations resolve against the paper's strict Lean libraries (ledger.toml [lean] root + strict),
read without Lean as tools/corrections.py reads them.
"""
import glob
import hashlib
import json
import os
import re
import sys
import tomllib

ROOT = os.environ.get("LEANARTICLES_ROOT") or os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.realpath(__file__))))
import corrections  # noqa: E402  (lean_decls: the strict declarations, read without Lean)

STATUS = ("found", "drafted", "checked", "reviewed")
OTHER = ("dismissed", "blocked")
KINDS = ("false", "underspecified", "imprecise")
FIELDS = ("label", "status", "kind", "printed", "printed_sha256", "finding", "refutation",
          "refutation_note", "anchor", "basis", "correction", "oq", "reading", "rewritten", "changes",
          "check", "review", "reason")
LISTS = ("refutation", "anchor", "basis", "changes")
HEADER = """# Restatements of papers/{slug}: statements false or imprecise as written, rewritten in natural
# language from the rigorous Lean. Schema and rules: tools/restate.py. Written by /restate (the
# statement-rewriter and statement-checker agents, the master's `restate.py set`); reviewed by the
# author. Every strong candidate of `restate.py detect` has an entry here (the gate checks it).
"""

STRONG_TEXT = re.compile(r"\b(?:false|wrong|incorrect)\s+as\s+(?:printed|written|stated)\b", re.I)
STRONG_CAPS = re.compile(r"\bFALSE\b")
WEAK_TEXT = re.compile(r"\brefut|counterexample|corrected form|missing hypothesis|added hypothes"
                       r"|\bnarrow|\breading\b", re.I)
NEG_PART = re.compile(r"^not_|Cex|cex|counterexample")


def rank(status):
    return STATUS.index(status) if status in STATUS else -1


def sha(text):
    return hashlib.sha256(text.strip().encode("utf-8")).hexdigest()


def slugs_all():
    return sorted(os.path.basename(os.path.dirname(os.path.dirname(f)))
                  for f in glob.glob(os.path.join(ROOT, "papers", "*", "ledger", "ledger.json")))


def pdir(slug):
    return os.path.join(ROOT, "papers", slug)


def register_path(slug):
    return os.path.join(pdir(slug), "certificate", "restatements.toml")


def rendered_path(slug):
    return os.path.join(pdir(slug), "certificate", "RESTATED.md")


def config(slug):
    with open(os.path.join(pdir(slug), "ledger", "ledger.toml"), "rb") as fh:
        return tomllib.load(fh)


def ledger(slug):
    with open(os.path.join(pdir(slug), "ledger", "ledger.json"), encoding="utf-8") as fh:
        return {s["label"]: s for s in json.load(fh)["statements"]}


_DECLS = {}


def strict_decls(slug):
    """Full names of the declarations of the paper's strict Lean libraries."""
    lean = config(slug).get("lean", {})
    if not lean.get("root"):
        return set()
    root = os.path.normpath(os.path.join(pdir(slug), "ledger", lean["root"]))
    key = (root, tuple(lean.get("strict", [])))
    if key not in _DECLS:
        _DECLS[key] = set().union(*[corrections.lean_decls(root, lib) for lib in lean.get("strict", [])] or [set()])
    return _DECLS[key]


def lean_root(slug):
    lean = config(slug).get("lean", {})
    return os.path.normpath(os.path.join(pdir(slug), "ledger", lean["root"])) if lean.get("root") else None


def printed_of(row):
    a, b = row["tex_span"]
    return "%s:%d-%d" % (row["file"], a, b)


def digest_of(row):
    return row.get("statement_sha256_current") or row.get("statement_sha256") or ""


def texts(row):
    f = row.get("paper_findings") or []
    return [str(x) for x in (f if isinstance(f, list) else [f])] + [str(row.get("notes") or "")]


def clip(t, a, b, before=160, after=320):
    """The text around [a, b), cut at sentence or word boundaries."""
    lo = max(0, a - before)
    if lo:
        k = max(t.rfind(". ", lo, a), t.rfind("; ", lo, a))
        lo = k + 2 if k >= 0 else (t.find(" ", lo) + 1 or lo)
    hi = min(len(t), b + after)
    if hi < len(t):
        k = max(t.rfind(". ", b, hi), t.rfind("; ", b, hi))
        hi = k + 1 if k >= 0 else (t.rfind(" ", b, hi) if t.rfind(" ", b, hi) > b else hi)
    return ("… " if lo else "") + t[lo:hi].strip() + (" …" if hi < len(t) else "")


def signals(row):
    """(strength, reasons, excerpt, refuting declarations) of one ledger row."""
    reasons, excerpt = [], ""
    neg = [d for d in row.get("decls", []) if any(NEG_PART.search(p) for p in d.split("."))]
    for t in texts(row):
        for rx, name in ((STRONG_TEXT, "false as written"), (STRONG_CAPS, "FALSE")):
            m = rx.search(t)
            if m:
                reasons.append(name)
                excerpt = excerpt or clip(t, m.start(), m.end())
    if neg:
        reasons.append("refuting declaration")
    if reasons:
        joined = "; ".join(x for x in texts(row) if x.strip())
        return "strong", sorted(set(reasons)), excerpt or clip(joined, 0, 0, 0, 480), neg
    for t in texts(row):
        m = WEAK_TEXT.search(t)
        if m:
            return "weak", [m.group(0).lower()], clip(t, m.start(), m.end()), neg
    return None, [], "", neg


def load(slug, path=None):
    p = path or register_path(slug)
    if not os.path.exists(p):
        return []
    with open(p, "rb") as fh:
        return tomllib.load(fh).get("entry", [])


def toml_str(v):
    """LaTeX reads best unescaped: a multi-line literal string for a text with newlines, a literal
    string for one line with backslashes, a basic string otherwise."""
    if "\n" in v:
        assert "'''" not in v, "a value contains ''' and cannot be a TOML literal string"
        return "'''\n%s'''" % (v if v.endswith("\n") else v + "\n")
    if "\\" in v and "'" not in v:
        return "'%s'" % v
    return json.dumps(v, ensure_ascii=False)


def dump(slug, entries):
    out = [HEADER.format(slug=slug)]
    for e in entries:
        unknown = set(e) - set(FIELDS)
        assert not unknown, "%s: unknown fields %s" % (e.get("label"), sorted(unknown))
        out.append("[[entry]]")
        for k in FIELDS:
            if k not in e:
                continue
            v = e[k]
            if isinstance(v, list):
                out.append("%s = [%s]" % (k, ", ".join(toml_str(str(x)) for x in v)))
            else:
                out.append("%s = %s" % (k, toml_str(str(v))))
        out.append("")
    return "\n".join(out)


def save(slug, entries, path=None):
    text = dump(slug, entries)
    tomllib.loads(text)  # assert the programmatic edit round-trips
    with open(path or register_path(slug), "w", encoding="utf-8") as fh:
        fh.write(text)


def decisions():
    """(DEC ids, OQ id -> status) from registers/DECISIONS.md."""
    dec, oq = set(), {}
    with open(os.path.join(ROOT, "registers", "DECISIONS.md"), encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r"\|\s*(DEC-\d+|OQ-\d+)\s*\|", line)
            if not m:
                continue
            if m.group(1).startswith("DEC"):
                dec.add(m.group(1))
            else:
                cells = [c.strip() for c in line.strip().strip("|").split("|")]
                oq[m.group(1)] = cells[-1].split()[0] if cells[-1] else ""
    return dec, oq


def egf_corrections():
    p = os.path.join(ROOT, "papers", "egf", "programme", "corrections.toml")
    if not os.path.exists(p):
        return set()
    with open(p, "rb") as fh:
        return {c["id"] for c in tomllib.load(fh).get("correction", [])}


def check_file(slug, name):
    return os.path.join(pdir(slug), "certificate", "restate", name)


def entry_errors(slug, e, rows, decls, dec, oq, corr):
    lab = e.get("label", "?")
    tag = "%s %s" % (slug, lab)
    errs = []
    st = e.get("status")
    if st not in STATUS + OTHER:
        return ["%s: status %r not in %s" % (tag, st, STATUS + OTHER)]
    row = rows.get(lab)
    if row is None:
        return ["%s: not a ledger label" % tag]
    if e.get("printed") != printed_of(row) or e.get("printed_sha256") != digest_of(row):
        errs.append("%s: stale: the ledger now reads %s (sha %s…); re-triage the entry"
                    % (tag, printed_of(row), digest_of(row)[:12]))
    if not str(e.get("finding", "")).strip():
        errs.append("%s: no finding" % tag)
    for k in LISTS:
        if k in e and not isinstance(e[k], list):
            errs.append("%s: `%s` is not a list" % (tag, k))
    if e.get("kind") is not None and e["kind"] not in KINDS:
        errs.append("%s: kind %r not in %s" % (tag, e["kind"], KINDS))
    for k in ("refutation", "anchor"):
        for d in e.get(k, []) if isinstance(e.get(k, []), list) else []:
            if d not in decls:
                errs.append("%s: %s %s is not a declaration of the strict library" % (tag, k, d))
    for b in e.get("basis", []) if isinstance(e.get("basis", []), list) else []:
        if not (b in dec or b in oq):
            errs.append("%s: basis %s is not a row of registers/DECISIONS.md" % (tag, b))
    if e.get("correction") and e["correction"] not in corr:
        errs.append("%s: correction %s is not an entry of the EGF register" % (tag, e["correction"]))
    if st == "dismissed" and not str(e.get("reason", "")).strip():
        errs.append("%s: dismissed without a reason" % tag)
    if st == "blocked" and oq.get(e.get("oq", "")) != "OPEN":
        errs.append("%s: blocked needs `oq`, an OPEN question (got %r)" % (tag, e.get("oq")))
    if rank(st) >= rank("drafted"):
        if e.get("kind") not in KINDS:
            errs.append("%s: from drafted on, `kind` is one of %s" % (tag, KINDS))
        if e.get("kind") == "false" and not (e.get("refutation") or str(e.get("refutation_note", "")).strip()):
            errs.append("%s: kind false names a refutation (or a refutation_note)" % tag)
        if e.get("kind") == "underspecified" and not any(b.startswith("DEC-") for b in e.get("basis", [])):
            errs.append("%s: kind underspecified needs the DEC row ruling the reading in `basis`" % tag)
        if not e.get("anchor"):
            errs.append("%s: from drafted on, `anchor` names the Lean the rewrite states" % tag)
        rw = str(e.get("rewritten", ""))
        if not rw.strip():
            errs.append("%s: from drafted on, `rewritten` is the rewritten statement" % tag)
        if rw.count("{") != rw.count("}"):
            errs.append("%s: rewritten has unbalanced braces" % tag)
        if re.search(r"\\label\b|\\begin\{proof\}", rw):
            errs.append("%s: rewritten carries a \\label or a proof" % tag)
        if not e.get("changes"):
            errs.append("%s: from drafted on, `changes` lists what changed from the printed form" % tag)
    if rank(st) >= rank("checked"):
        cf = check_file(slug, str(e.get("check", "")))
        if not e.get("check") or not os.path.exists(cf):
            errs.append("%s: from checked on, `check` names a CHECK file under certificate/restate/" % tag)
        else:
            with open(cf, encoding="utf-8") as fh:
                c = json.load(fh)
            if c.get("label") != lab:
                errs.append("%s: %s is the check of %s" % (tag, e["check"], c.get("label")))
            if c.get("verdict") != "faithful":
                errs.append("%s: %s verdict is %r, not faithful" % (tag, e["check"], c.get("verdict")))
            if c.get("rewritten_sha256") != sha(str(e.get("rewritten", ""))):
                errs.append("%s: rewritten changed after %s (sha mismatch)" % (tag, e["check"]))
            if sorted(c.get("anchor", [])) != sorted(e.get("anchor", [])):
                errs.append("%s: %s checked other anchors" % (tag, e["check"]))
    if st == "reviewed" and not str(e.get("review", "")).strip():
        errs.append("%s: reviewed without `review`" % tag)
    if st == "reviewed" and str(e.get("reading", "")).strip() and not any(
            b.startswith("DEC-") for b in e.get("basis", [])):
        errs.append("%s: reviewed with an unruled `reading`: a DEC row in `basis` rules it first" % tag)
    rw = str(e.get("rewritten", ""))
    if rank(st) >= rank("drafted") and re.search(r"(?<![\\\w])[A-Z][A-Za-z]+\.[a-z][A-Za-z0-9_]*_[A-Za-z0-9_]+", rw):
        errs.append("%s: rewritten names a Lean identifier; write the mathematics" % tag)
    return errs


def errors(slug, path=None):
    rows = ledger(slug)
    entries = load(slug, path)
    decls = strict_decls(slug)
    dec, oq = decisions()
    corr = egf_corrections() if slug == "egf" else set()
    errs, seen = [], set()
    for e in entries:
        if e.get("label") in seen:
            errs.append("%s %s: two entries" % (slug, e.get("label")))
        seen.add(e.get("label"))
        errs += entry_errors(slug, e, rows, decls, dec, oq, corr)
    for lab, row in rows.items():
        strength, why, _, _ = signals(row)
        if strength == "strong" and lab not in seen:
            errs.append("%s %s: a strong candidate (%s) with no entry; run `restate.py seed %s`"
                        % (slug, lab, ", ".join(why), slug))
    if path is None and entries:
        rp = rendered_path(slug)
        want = render(slug, entries, rows)
        have = None
        if os.path.exists(rp):
            with open(rp, encoding="utf-8") as fh:
                have = fh.read()
        if have != want:
            errs.append("%s: certificate/RESTATED.md is not what `restate.py render %s` writes" % (slug, slug))
    return errs, len(entries)


def candidates(slug, every=False):
    have = {e["label"] for e in load(slug)}
    out = []
    for lab, row in ledger(slug).items():
        strength, why, ex, neg = signals(row)
        if strength == "strong" or (every and strength == "weak"):
            if lab not in have:
                out.append((lab, strength, why, ex, neg, row))
    return out


def seed(slug, every=False):
    entries = load(slug)
    new = []
    decls = strict_decls(slug)
    for lab, strength, why, ex, neg, row in candidates(slug, every):
        e = {"label": lab, "status": "found", "printed": printed_of(row), "printed_sha256": digest_of(row),
             "finding": "[%s: %s] %s" % (strength, ", ".join(why), " ".join(ex.split()))}
        ref = [d for d in neg if d in decls]
        if ref:
            e["refutation"] = ref
        new.append(e)
    if new:
        save(slug, entries + new)
    return len(new)


def render(slug, entries=None, rows=None):
    entries = load(slug) if entries is None else entries
    rows = ledger(slug) if rows is None else rows
    order = {lab: i for i, lab in enumerate(rows)}
    lines = ["# Restatements of papers/%s" % slug, "",
             "Generated by `tools/restate.py render %s` from `restatements.toml`; never edit by hand." % slug,
             "", "| status | count |", "|---|---:|"]
    for s in STATUS + OTHER:
        n = sum(1 for e in entries if e["status"] == s)
        if n:
            lines.append("| %s | %d |" % (s, n))
    for e in sorted(entries, key=lambda e: order.get(e["label"], 10 ** 6)):
        lines += ["", "## `%s` — %s%s" % (e["label"], e["status"], (", " + e["kind"]) if e.get("kind") else ""),
                  "", "Printed at `%s`. %s" % (e["printed"], " ".join(str(e.get("finding", "")).split()))]
        for k, title in (("refutation", "Refuted by"), ("anchor", "Lean"), ("basis", "Basis")):
            if e.get(k):
                lines.append("")
                lines.append("%s: %s" % (title, ", ".join("`%s`" % x for x in e[k])))
        if e.get("reading"):
            lines += ["", "**Reading taken, unruled:** %s" % " ".join(str(e["reading"]).split())]
        if e.get("rewritten"):
            lines += ["", "Rewritten:", "", "```latex", e["rewritten"].rstrip(), "```"]
        if e.get("changes"):
            lines += [""] + ["- %s" % c for c in e["changes"]]
        for k in ("reason", "oq", "review", "check"):
            if e.get(k):
                lines += ["", "%s: %s" % (k.capitalize(), e[k])]
    return "\n".join(lines) + "\n"


_SRC = {}


def decl_index(slug):
    """Full name -> (file, line index, the `variable` lines in scope) for the paper's strict Lean
    libraries, read without Lean (comments blanked, namespaces and sections tracked, as
    corrections.lean_decls reads them)."""
    root = lean_root(slug)
    libs = tuple(config(slug).get("lean", {}).get("strict", []))
    if (root, libs) in _SRC:
        return _SRC[(root, libs)]
    idx = {}
    for lib in libs:
        for f in sorted(glob.glob(os.path.join(root, lib, "**", "*.lean"), recursive=True)):
            with open(f, encoding="utf-8") as fh:
                raw = fh.read()
            code = corrections.ladder._code(raw).split("\n")
            rawl = raw.split("\n")
            stack = []   # (kind, name, [variable blocks opened in this scope])
            top_vars = []
            header = True
            i = 0
            while i < len(code):
                s = code[i].strip()
                if not s:
                    i += 1
                    continue
                if header:
                    if s in ("module", "prelude") or corrections.ladder.IMPORT.match(s):
                        i += 1
                        continue
                    header = False
                m = re.match(r"namespace\s+(\S+)", s)
                if m:
                    stack.extend(("namespace", x, []) for x in m.group(1).split("."))
                    i += 1
                    continue
                m = re.match(r"(?:@\[.*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section\b\s*(\S*)", s)
                if m:
                    stack.extend(("section", x, []) for x in (m.group(1).split(".") if m.group(1) else [""]))
                    i += 1
                    continue
                m = re.match(r"end\b\s*(\S*)", s)
                if m:
                    for _ in (m.group(1).split(".") if m.group(1) else [""]):
                        if stack:
                            stack.pop()
                    i += 1
                    continue
                if re.match(r"(?:omit\s.*\s)?variable\b", s) or re.match(r"include\b", s):
                    j = i + 1
                    while j < len(code) and code[j][:1] in (" ", "\t") and code[j].strip():
                        j += 1
                    # `variable … in` binds the next declaration only: not a scope's variable
                    if not re.search(r"\bin\s*$", code[j - 1]):
                        (stack[-1][2] if stack else top_vars).append("\n".join(rawl[i:j]))
                    i = j
                    continue
                t = s
                while t.startswith("@["):
                    d, k = 0, 1
                    for k in range(1, len(t)):
                        d += t[k] == "["
                        d -= t[k] == "]"
                        if d == 0:
                            break
                    t = t[k + 1:].lstrip()
                m = corrections.ladder.DECL_FQ.match(t)
                if m:
                    name = m.group(2)
                    full = name[len("_root_."):] if name.startswith("_root_.") else \
                        ".".join([x for k, x, _ in stack if k == "namespace"] + [name])
                    idx.setdefault(full, (f, i, top_vars + [v for _, _, vs in stack for v in vs]))
                i += 1
    _SRC[(root, libs)] = idx
    return idx


def decl_source(slug, name, variables=True):
    """The source of declaration `name`: its docstring, its statement (a theorem up to `:=`; a
    definition's body too, up to the next blank line, since the body is its meaning), and the
    `variable` lines in scope, which carry hypotheses its own signature does not show."""
    hit = decl_index(slug).get(name)
    if not hit:
        return "(source not found in the strict library)"
    f, i, vs = hit
    with open(f, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    is_thm = re.search(r"\b(?:theorem|lemma)\s", lines[i]) is not None
    j = i
    while j > 0 and i - j < 30 and (lines[j - 1].strip().startswith(("/--", "-", "*", "`")) or
                                    lines[j - 1].strip().endswith("-/") or
                                    (lines[j - 1].strip() and not lines[j - 1].startswith(("theorem", "lemma", "def", "end", "namespace", "section", "variable", "@[", "open", "instance", "abbrev", "structure", "noncomputable", "private", "protected")))):
        j -= 1
    block, k = [], i
    while k < len(lines) and k < i + 60:
        block.append(lines[k])
        if is_thm and (":=" in lines[k] or lines[k].rstrip().endswith(" where")):
            break
        if k > i and not lines[k].strip():
            break
        k += 1
    out = "%s:%d" % (os.path.relpath(f, ROOT), i + 1)
    if variables and vs:
        out += "\n-- variables in scope:\n" + "\n".join(vs)
    return out + "\n" + "\n".join(lines[j:i] + block)


def cited_rows(text):
    """The DEC/OQ rows of registers/DECISIONS.md that `text` cites, verbatim."""
    ids = set(re.findall(r"\b(?:DEC|OQ)-\d+", text))
    out = []
    with open(os.path.join(ROOT, "registers", "DECISIONS.md"), encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r"\|\s*((?:DEC|OQ)-\d+)\s*\|", line)
            if m and m.group(1) in ids:
                out.append(line.rstrip())
    return out


def context(slug, lab, full=False):
    rows = ledger(slug)
    row = rows[lab]
    cfg = config(slug)
    src = os.path.normpath(os.path.join(pdir(slug), "ledger", cfg["paper"]["root"], row["file"]))
    a, b = row["tex_span"]
    with open(src, encoding="utf-8", errors="replace") as fh:
        tex = fh.read().split("\n")[a - 1:b]
    e = {x["label"]: x for x in load(slug)}.get(lab)
    print("== %s %s (%s, printed %s)" % (slug, lab, row.get("kind"), printed_of(row)))
    print("\n".join(tex))
    print("\n== ledger: nl_status %s, lean_stated %s, lean_proved %s" %
          (row.get("nl_status"), row.get("lean_stated"), row.get("lean_proved")))
    for t in texts(row):
        if t.strip():
            print("- " + t)
    if e:
        print("\n== register entry\n" + dump(slug, [e]).split("\n", 5)[-1])
    # the paper lines the findings cite (standing assumptions, definitions), two lines of context each
    cited = sorted({int(x) for x in re.findall(r"\bl\.\s?(\d+)", " ".join(texts(row)) + json.dumps(e or {}))
                    if not a <= int(x) <= b})[:15]
    if cited:
        with open(src, encoding="utf-8", errors="replace") as fh:
            all_tex = fh.read().split("\n")
        print("\n== paper lines cited (%s)" % row["file"])
        for x in cited:
            print("-- l.%d\n%s" % (x, "\n".join(all_tex[max(0, x - 2):x + 1])))
    rules = cited_rows(" ".join(texts(row)) + " " + json.dumps(e or {}, ensure_ascii=False))
    if rules:
        print("== rulings and questions cited\n" + "\n".join(rules))
    if not lean_root(slug):
        return
    first = list(dict.fromkeys((e or {}).get("anchor", []) + (e or {}).get("refutation", [])))
    rest = [d for d in row.get("decls", []) if d not in first]
    # the row's declarations a reader starts from: not_ theorems, iff and assembly forms (no helper
    # of another declaration of the row is used by it, by name)
    if not first:
        first = [d for d in rest if any(NEG_PART.search(p) for p in d.split("."))
                 or re.search(r"(?:_iff|Statement|_unconditional|_full)$", d)] or rest[:3]
        rest = [d for d in rest if d not in first]
    for d in first + (rest if full else []):
        print("\n== %s\n%s" % (d, decl_source(slug, d)))
    if rest and not full:
        print("\n== other declarations of the row (by name; `restate.py decl %s NAME` prints one, "
              "`context --full` prints all)\n%s" % (slug, "\n".join("- " + d for d in rest)))


def set_status(slug, lab, status, check=None, review=None, reason=None):
    entries = load(slug)
    e = next((x for x in entries if x["label"] == lab), None)
    if e is None:
        sys.exit("restate: %s %s has no entry" % (slug, lab))
    if status in STATUS and e["status"] in STATUS and rank(status) < rank(e["status"]):
        sys.exit("restate: %s %s: a status only moves forward (%s -> %s)" % (slug, lab, e["status"], status))
    e = dict(e, status=status)
    for k, v in (("check", check), ("review", review), ("reason", reason)):
        if v:
            e[k] = v
    dec, oq = decisions()
    errs = entry_errors(slug, e, ledger(slug), strict_decls(slug), dec, oq,
                        egf_corrections() if slug == "egf" else set())
    if errs:
        sys.exit("restate: refused:\n  " + "\n  ".join(errs))
    save(slug, [e if x["label"] == lab else x for x in entries])
    with open(rendered_path(slug), "w", encoding="utf-8") as fh:
        fh.write(render(slug))
    print("restate: %s %s -> %s" % (slug, lab, status))


def main(argv):
    if not argv:
        sys.exit(__doc__)
    cmd, rest = argv[0], argv[1:]
    every = "--all" in rest
    path = rest[rest.index("--file") + 1] if "--file" in rest else None
    opts = {}
    for k in ("--check", "--review", "--reason", "--file", "--label"):
        if k in rest:
            i = rest.index(k)
            opts[k] = rest[i + 1]
            del rest[i:i + 2]
    args = [a for a in rest if not a.startswith("--")]
    if cmd == "set":
        if len(args) != 3:
            sys.exit(__doc__)
        return set_status(args[0], args[1], args[2], opts.get("--check"), opts.get("--review"), opts.get("--reason"))
    if cmd == "context":
        return context(args[0], args[1], full=every or "--full" in argv)
    if cmd == "decl":
        for d in args[1:]:
            print("== %s\n%s" % (d, decl_source(args[0], d)))
        return
    slugs = args or slugs_all()
    if cmd == "detect":
        n = 0
        for s in slugs:
            for lab, strength, why, ex, neg, _ in candidates(s, every):
                n += 1
                print("%s %s [%s: %s] %s" % (s, lab, strength, ", ".join(why), " ".join(ex.split())[:240]))
        print("restate: %d unregistered candidate(s)" % n)
        return
    if cmd == "seed":
        for s in slugs:
            k = seed(s, every)
            if k or os.path.exists(register_path(s)):
                with open(rendered_path(s), "w", encoding="utf-8") as fh:
                    fh.write(render(s))
            print("restate: %s: %d entr%s added" % (s, k, "y" if k == 1 else "ies"))
        return
    if cmd == "render":
        for s in slugs:
            with open(rendered_path(s), "w", encoding="utf-8") as fh:
                fh.write(render(s))
        return
    if cmd == "status":
        for s in slugs:
            es = load(s)
            if es:
                c = {k: sum(1 for e in es if e["status"] == k) for k in STATUS + OTHER}
                print("%-24s %s" % (s, "  ".join("%s %d" % (k, v) for k, v in c.items() if v)))
        return
    if cmd == "check":
        allerr, n = [], 0
        if path:
            if len(slugs) != 1:
                sys.exit("restate: --file needs exactly one SLUG")
            errs, k = errors(slugs[0], path)
            allerr, n = errs, k
        elif opts.get("--label"):
            if len(slugs) != 1:
                sys.exit("restate: --label needs exactly one SLUG")
            e = [x for x in load(slugs[0]) if x["label"] == opts["--label"]]
            if not e:
                sys.exit("restate: %s has no entry %s" % (slugs[0], opts["--label"]))
            dec, oq = decisions()
            allerr = entry_errors(slugs[0], e[0], ledger(slugs[0]), strict_decls(slugs[0]), dec, oq,
                                  egf_corrections() if slugs[0] == "egf" else set())
            n = 1
        else:
            for s in slugs:
                errs, k = errors(s)
                allerr += errs
                n += k
        for x in allerr:
            print("restate: " + x)
        print("restate: %d entries, %s" % (n, "%d violation(s)" % len(allerr) if allerr else "all rules hold"))
        sys.exit(1 if allerr else 0)
    sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
