#!/usr/bin/env python3
r"""The formalization ledger: every statement of a paper, in three states.

For each theorem-like environment of a draft this records

  1. **natural language** --- is it proved in the paper, cited from the literature,
     partially proved, or open?  With a link to the proof: `file:line`.
  2. **Lean stated** --- is there a Lean declaration carrying the statement, and is it
     in the strict library or the scaffold?
  3. **Lean proved** --- is that declaration closed, or does it rest on a `sorry`?

and the **DAG**: `A -> B` when the statement or the proof of `A` invokes `B`.  The
topological order of that DAG is the order in which the paper may be formalized.

    python3 tools/ledger.py -c papers/<slug>/ledger/ledger.toml build    # regenerate the ledger and the DAG
    ... check         # exit 1 on drift, on an unlabeled statement, on a dangling dep; no writes
    ... label-audit   # every statement environment with no \label, file:line; exit 1 if any
    ... crosscheck    # agree with the Lean library's paper-map.json, when one is configured
    ... sync-map      # push the triage onto paper-map.json
    ... reaffirm LBL  # accept a changed LaTeX block, clearing stale
    ... next          # the closure queue: unfinished target rows, nearest first
    ... stats         # counts by status, by section
    ... order         # formalization order, dependencies first
    ... node LBL      # one row, with its dependencies both ways
    ... ready         # unformalized statements whose deps are all done

Generalised from `~/Dropbox/GFN Bounds/formalization_ledger.py` on 2026-09-19: every module
constant of that script (the file list, the section titles, the Lean root and scope, the twins,
the statement environments and their per-paper aliases, the milestones) now comes from the
paper's `ledger.toml`, and the regression fixture `tools/fixtures/regression/gfnbounds.toml`
reproduces that paper's ledger byte for byte.  Exit status: 0 pass, 1 fail, 2 misconfiguration
(including `source = "pdf"`: a paper whose draft has no .tex has no ledger, and saying so is
the gate).

Mechanical fields are rewritten on every `build`; curated fields are preserved.  The
curated ones are `nl_status` (when `nl_status_override` is set), `bucket`, `lean_files`,
`decls`, `notes` and `blocked_on`.  A statement whose LaTeX changed is flagged `stale`
so that a Lean file is never left certifying a statement the paper no longer makes.

Nothing here edits the draft, and nothing here edits the Lean library's `paper-map.json`
except `sync-map`, explicitly.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tomllib
from collections import OrderedDict, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import texgraph as pg  # noqa: E402


# ----------------------------------------------------------------- config --
class Config:
    """Everything `formalization_ledger.py` used to hardcode."""

    def __init__(self, path):
        self.path = os.path.abspath(path)
        base = os.path.dirname(self.path)
        with open(self.path, "rb") as fh:
            c = tomllib.load(fh)
        p = c.get("paper", {})
        self.source = p.get("source", "tex")
        self.root = os.path.normpath(os.path.join(base, p.get("root", ".")))
        self.document = p.get("document", "main.tex")
        self.notation = list(p.get("notation", ["notation.tex"]))
        self.aux = p.get("aux")
        self.files = [tuple(f) for f in p.get("files", [])]
        self.titles = dict(p.get("titles", {}))
        self.out_of_document = dict(p.get("out_of_document", {}))
        self.coverage_skip = list(p.get("coverage_skip", []))
        self.coverage_recursive = bool(p.get("coverage_recursive", False))
        self.statement_envs = p.get("statement_envs")
        self.env_alias = dict(p.get("env_alias", {}))
        self.proof_macros = [list(m) for m in p.get("proof_macros", [])]
        self.label_prefixes = list(p.get("label_prefixes",
                                         ["theo", "thm", "lem", "prop", "cor", "def", "defi",
                                          "rem", "assum", "conj", "ex", "fact", "claim"]))
        self.twins = dict(p.get("twins", {}))
        l = c.get("lean", {})
        self.lean_root = (os.path.normpath(os.path.join(base, os.path.expanduser(l["root"])))
                          if l.get("root") else None)
        self.strict = list(l.get("strict", []))
        self.scaffold = list(l.get("scaffold", []))
        self.scope = set(l.get("scope", ["*"]))
        self.paper_map = l.get("paper_map")
        self.strict_label = l.get("strict_label") or "/".join(self.strict[:1]) + "/"
        self.scaffold_label = l.get("scaffold_label") or "/".join(self.scaffold[:1]) + "/"
        o = c.get("output", {})
        self.out_dir = os.path.normpath(os.path.join(base, o.get("dir", ".")))
        self.ledger = os.path.join(self.out_dir, o.get("json", "ledger.json"))
        self.markdown = os.path.join(self.out_dir, o.get("markdown", "LEDGER.md"))
        self.dot = os.path.join(self.out_dir, o.get("dot", "dag.dot"))
        self.tool_name = o.get("tool_name", "tools/ledger.py")
        m = c.get("markdown", {})
        self.roadmap_intro = m.get("roadmap_intro", "")
        self.obstruction_note = m.get("obstruction_note", "")
        self.scope_blurb = m.get("scope_blurb", "")
        self.milestones = [(x["name"], x.get("blurb", ""), list(x.get("labels", [])))
                           for x in m.get("milestones", [])]
        self.render = bool(o.get("render", True))

    def files_or_expand(self):
        """The explicit reading order, or the document's `\\input` closure if none is given."""
        if self.files:
            return self.files
        out = []
        seen = set()
        for fname, _text, _line in pg.expand(self.document, self.root):
            if fname not in seen:
                seen.add(fname)
                out.append((fname, "body", "body"))
        return out


CFG = None  # set by main(); every function below reads it


def die(msg, code=2):
    print("ledger: %s" % msg)
    sys.exit(code)


# Natural-language status.  `proved` and `definition` are read off the .tex; the rest
# are judgements, and every one of them is carried here with its reason rather than
# inferred, so that a regeneration cannot quietly promote an open statement.
NL_STATUSES = ("definition", "proved", "cited", "partial", "open", "informal")

STATUS_GLYPH = {
    "definition": "def",
    "proved": "proved",
    "cited": "cited",
    "partial": "partial",
    "open": "open",
    "informal": "informal",
}

LEAN_STATED = ("none", "scaffold", "strict")
LEAN_PROVED = ("none", "partial", "closed")

BUCKETS = {
    "A": "nothing left; certified in full",
    "B": "routine on the layers already built",
    "C": "hard --- attempted and blocked on a named obstruction",
    "D": "deferred --- needs a layer not built, or the paper itself does not prove it",
    "T": "terminal --- not certifiable by design; out of the closure target, with a reason",
    "": "not yet triaged",
}


# ------------------------------------------------------------------ paper --
def build_graph():
    """Parse the whole document, including the appendices the current mainfile comments out."""
    pg.configure(main=CFG.document, notation=CFG.notation, aux=CFG.aux,
                 env_alias=CFG.env_alias, twins=CFG.twins, statement_envs=CFG.statement_envs,
                 proof_macros=CFG.proof_macros)
    pg.load_notation(CFG.root, (CFG.document,))
    g = pg.Graph("paper")
    for fname, where, _sig in CFG.files_or_expand():
        path = os.path.join(CFG.root, fname)
        if not os.path.exists(path):
            continue
        if where == "appendix":
            g.in_appendix = True
        text = pg.strip_comments(open(path, encoding="utf-8", errors="replace").read())
        pg.scan(g, fname, text, 1)
    pg.link(g)
    aux = pg.enrich(g, CFG.root)
    return g, aux


def statement_nodes(g):
    return [n for n in g.nodes.values() if n["kind"] == "statement"]


def file_signature(fname):
    for f, _where, sig in CFG.files_or_expand():
        if f == fname:
            return sig if sig else "body"
    return "body"


def digest(text):
    return hashlib.sha256(" ".join(text.split()).encode("utf-8")).hexdigest()


def git_commit(path):
    if not path:
        return "unknown"
    try:
        top = subprocess.check_output(["git", "-C", path, "rev-parse", "--show-toplevel"],
                                      text=True, stderr=subprocess.DEVNULL).strip()
        if top == os.path.expanduser("~"):
            return "unknown"   # the $HOME repository is not the draft's
        if os.path.realpath(path) != os.path.realpath(top):
            # A directory inside a larger repository (lean-causal/ in the hub): the last commit that
            # touched it. HEAD would name the commit that records this very ledger, which moves
            # with every commit and could never be committed in agreement with `build`.
            sha = subprocess.check_output(["git", "-C", path, "log", "-1", "--format=%h", "--", "."],
                                          text=True, stderr=subprocess.DEVNULL).strip()
            if sha:
                return sha
        return subprocess.check_output(
            ["git", "-C", path, "rev-parse", "--short", "HEAD"],
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return "unknown"


def source_commit():
    """The commit of the DRAFT, not of this repository.

    A snapshotted legacy draft lives inside the hub, so `git rev-parse HEAD` there returns the
    hub's own head -- which moves with every unrelated commit and would stale every ledger on
    disk. The draft's provenance is in `legacy/MANIFEST.json`, recorded when it was snapshotted;
    that is what belongs in the ledger. A paper read in place (the GFN Bounds regression) keeps
    its own repository's commit.
    """
    man = os.path.join(os.path.dirname(CFG.root), "MANIFEST.json")
    if os.path.basename(os.path.dirname(CFG.root)) == "legacy" or os.path.exists(man):
        if os.path.exists(man):
            return json.load(open(man, encoding="utf-8")).get("source_git_commit") or "snapshot"
        return "snapshot"
    return git_commit(CFG.root)


def env_span(fname, line, env):
    r"""1-indexed inclusive `(first, last)` of the `\begin{env}` starting at `line`."""
    path = os.path.join(CFG.root, fname)
    if not os.path.exists(path):
        return [line, line]
    lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
    depth = 0
    for i in range(line - 1, len(lines)):
        depth += lines[i].count("\\begin{%s}" % env)
        depth -= lines[i].count("\\end{%s}" % env)
        if depth == 0:
            return [line, i + 1]
    return [line, len(lines)]


# ------------------------------------------------------------------- Lean --
def docstring_label_re():
    return re.compile(r"\*\*`((?:%s):[A-Za-z_0-9.\-]+)`\*\*" % "|".join(
        re.escape(p) for p in CFG.label_prefixes))


#: A curated decl: a dotted Lean name, no whitespace, brackets or punctuation of prose.
LEAN_NAME = re.compile(r"^[^\s()\[\],;:]+$")

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(theorem|lemma|def|structure|class|inductive|abbrev|instance|example)\s+"
    r"([A-Za-z_][\w.'!?]*)", re.M)


def lean_sources():
    """rel-path -> text, for both libraries."""
    out = {}
    if not CFG.lean_root:
        return out
    for sub in CFG.strict + CFG.scaffold:
        base = os.path.join(CFG.lean_root, sub)
        for dirpath, _dirs, names in os.walk(base):
            for n in sorted(names):
                if n.endswith(".lean"):
                    p = os.path.join(dirpath, n)
                    out[os.path.relpath(p, CFG.lean_root)] = open(
                        p, encoding="utf-8", errors="replace").read()
    return out


def is_strict(relpath):
    return any(relpath.startswith(s.rstrip("/") + "/") for s in CFG.strict)


def strip_lean_comments(text):
    """Lean source with `--` line comments and nested `/- ... -/` blocks (docstrings included)
    removed.  String literals containing comment markers are not handled."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def lean_index(src):
    """label -> {'files': [...], 'strict': bool, 'sorries': n}.

    A file announces the paper statement it certifies in its module docstring, in the
    house form ``**`lem:doubling_escape`**``.  Declarations are read off the file; the
    ones a statement actually claims are curated in the ledger, this index only says
    *which files* speak to the label and whether they compile without `sorry`.
    """
    label_re = docstring_label_re()
    idx = defaultdict(lambda: {"files": [], "strict": False, "sorries": 0})
    for path, text in src.items():
        head = text[:4000]
        labels = OrderedDict.fromkeys(label_re.findall(head))
        if not labels:
            continue
        strict = is_strict(path)
        # Count `sorry` in CODE only.  A docstring that says "No `sorry`." is prose.
        sorries = len(re.findall(r"(?<![\w'])sorry(?![\w'])", strip_lean_comments(text)))
        for lab in labels:
            e = idx[lab]
            e["files"].append(path)
            e["strict"] = e["strict"] or strict
            e["sorries"] += sorries
    return dict(idx)


#: A module's own disclosure block: a `## SCOPE (disclosed)` section in the module docstring,
#: written beside the proof by whoever wrote it.  Read from there rather than copied.
SCOPE_BLOCK = re.compile(r"^##\s*SCOPE\b.*?(?=^Provenance:|^-/)", re.M | re.S)


def lean_scope_blocks(src, files):
    """The disclosed scope of each module carrying a statement, in the order listed."""
    out = []
    for f in files:
        text = src.get(f)
        if text is None:
            continue
        m = SCOPE_BLOCK.search(text[:8000])
        if not m:
            continue
        body = re.sub(r"\n{3,}", "\n\n", m.group(0).strip())
        out.append("**%s**\n\n%s" % (os.path.basename(f), body))
    return out


def paper_map_path():
    if not (CFG.lean_root and CFG.paper_map):
        return None
    return os.path.join(CFG.lean_root, CFG.paper_map)


def read_paper_map():
    """The Lean library's own map: label -> row.  Read-only; its gate owns it."""
    p = paper_map_path()
    if not p or not os.path.exists(p):
        return {}
    m = json.load(open(p, encoding="utf-8"))
    return {s["label"]: s for s in m.get("statements", [])}


def decl_line(src, files, decl):
    short = decl.split(".")[-1]
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
                     r"(?:theorem|lemma|def|structure|class|inductive|abbrev|instance)\s+"
                     r"(?:[A-Za-z_][\w.']*\.)?%s(?![\w'])" % re.escape(short), re.M)
    for f in files:
        if f not in src:
            continue
        m = pat.search(src[f])
        if m:
            return f, src[f].count("\n", 0, m.start()) + 1
    return None, None


# ----------------------------------------------------------------- ledger --
def load_ledger():
    if os.path.exists(CFG.ledger):
        return json.load(open(CFG.ledger, encoding="utf-8"))
    return {"paper": {}, "lean": {}, "statements": []}


CURATED = ("nl_status_override", "nl_reason", "bucket", "decls",
           "notes", "blocked_on", "lean_stated_override", "lean_proved_override",
           "paper_findings", "extra_lean_files", "restatement", "restatement_note",
           "terminal_reason", "size", "fidelity")

#: A body statement inherits its appendix twin's Lean status only if the body form really
#: is a restatement of the full form.  That is a reading, not a fact the parser can check,
#: so it is curated per row and defaults to the cautious value:
#:   "verified" / "unverified" / "differs" (reported `partial` whatever the twin's status).
RESTATEMENT_DEFAULT = "unverified"

#: top-level ledger fields that are curated by hand and must survive a rebuild.
CURATED_TOP = ("findings_triage",)


def build(write=True):
    g, aux = build_graph()
    src = lean_sources()
    lidx = lean_index(src)
    pmap = read_paper_map()
    old = {s["label"]: s for s in load_ledger()["statements"] if s.get("label")}

    # ---- statement -> statement dependency edges, statement and proof together ----
    labels = {n["label"] for n in statement_nodes(g) if n["label"]}
    proof_of = {n["proves"]: n for n in g.nodes.values()
                if n["kind"] == "proof" and n.get("proves")}

    by_twin_file = {n["label"]: n["file"] for n in statement_nodes(g) if n["label"]}
    rows = []
    for n in statement_nodes(g):
        lab = n["label"]
        if not lab:
            continue
        proof = proof_of.get(lab)
        span = env_span(n["file"], n["line"], n.get("env", n["subkind"]))

        deps = []
        for holder in (n, proof):
            if holder is None:
                continue
            for r in holder["refs"]:
                t = r.get("to", r["target"])   # a secondary \label resolves to its statement
                if t in labels and t != lab and t not in deps:
                    deps.append(t)
        cites = list(n["cites"]) + (list(proof["cites"]) if proof else [])
        for key in re.findall(r"\[([A-Za-z][A-Za-z0-9_]{3,})\]", n["title"] or ""):
            if key not in cites:
                cites.append(key)

        # -- natural language --------------------------------------------------
        if n["subkind"] == "definition":
            nl = "definition"
        elif proof is not None:
            nl = "proved"
        elif n["subkind"] == "remark":
            # A remark that mentions prior work is still the paper's own remark.
            nl = "informal"
        elif cites:
            nl = "cited"
        else:
            nl = "open"

        prev = old.get(lab, {})
        row = OrderedDict()
        row["label"] = lab
        row["number"] = n.get("number", "")
        row["kind"] = n["subkind"]
        row["title"] = n["title"]
        row["appendix"] = file_signature(n["file"])
        row["file"] = n["file"]
        row["line"] = n["line"]
        row["tex_span"] = span
        row["proof"] = ("%s:%d" % (proof["file"], proof["line"])) if proof else None
        row["proof_span"] = (None if not proof else
                             [proof["line"], proof["end_line"]] if "end_line" in proof else
                             env_span(proof["file"], proof["line"], proof.get("env", "proof")))
        row["twin_of"] = n.get("twin_of")
        row["twin"] = n.get("twin")
        row["cites"] = cites
        row["deps"] = deps
        row["nl_status"] = prev.get("nl_status_override") or nl
        row["nl_status_auto"] = nl
        # `statement_sha256` is the last REAFFIRMED digest, not the current one. It moves only
        # on `reaffirm`; `statement_sha256_current` is what the .tex says now.
        row["statement_sha256"] = prev.get("statement_sha256") or digest(n["text"])
        row["statement_sha256_current"] = digest(n["text"])

        # -- Lean --------------------------------------------------------------
        pm = pmap.get(lab)
        li = lidx.get(lab)
        # `lean_files` is MECHANICAL, never carried over from the previous ledger.
        files = list(li["files"]) if li else []
        if pm and pm.get("lean_files"):
            for f in pm["lean_files"]:
                if f not in files and os.path.exists(os.path.join(CFG.lean_root, f)):
                    files.append(f)
        for f in prev.get("extra_lean_files", []):
            if f not in files and os.path.exists(os.path.join(CFG.lean_root, f)):
                files.append(f)
        decls = (pm.get("decls") if pm and pm.get("decls") else prev.get("decls")) or []
        row["lean_files"] = files
        row["decls"] = decls

        if not files:
            stated, proved = "none", "none"
        else:
            stated = "strict" if any(is_strict(f) for f in files) else "scaffold"
            sorries = li["sorries"] if li else 0
            if pm:
                proved = {"closed": "closed", "partial": "partial",
                          "open": "none", "stale": "partial"}.get(pm.get("status"), "partial")
            elif stated == "scaffold":
                # Scaffold work is not yet verified and graduated: `none` is the honest default.
                proved = "none"
            elif stated == "strict" and sorries == 0:
                proved = "closed"
            else:
                proved = "partial"
        row["lean_stated"] = prev.get("lean_stated_override") or stated
        row["lean_proved"] = prev.get("lean_proved_override") or proved
        row["bucket"] = prev.get("bucket") or (pm.get("bucket", "") if pm else "")
        row["scope_notes"] = (pm.get("scope_notes", "") if pm else prev.get("notes", ""))
        if not row["scope_notes"] and files:
            blocks = lean_scope_blocks(src, files)
            if blocks:
                row["scope_notes"] = ("Disclosed by the modules themselves; no note curated "
                                      "against the statement yet.\n\n" + "\n\n".join(blocks))
                row["scope_from_lean"] = True
        for k in CURATED:
            if k in prev and k != "decls":
                row[k] = prev[k]
        in_scope_sig = ("*" in CFG.scope) or (row["appendix"] in CFG.scope)
        twin_in_scope = (row.get("twin") is not None and (
            "*" in CFG.scope
            or file_signature(by_twin_file.get(row["twin"], "")) in CFG.scope))
        row["in_lean_scope"] = in_scope_sig or twin_in_scope or bool(files)
        row["stale"] = row["statement_sha256"] != row["statement_sha256_current"]
        rows.append(row)

    # A body statement is discharged by its appendix full form.
    by = {r["label"]: r for r in rows}
    for r in rows:
        full = r.get("twin")
        if not full or full not in by:
            continue
        f = by[full]
        if full not in r["deps"]:
            r["deps"].append(full)
        if r["proof"] is None and f["proof"]:
            r["proof"] = f["proof"]
            r["proof_span"] = f["proof_span"]
            r["proof_via_twin"] = True
        if r.get("restatement") == "differs":
            r["bucket"] = r.get("bucket") or "D"
        elif f["bucket"]:
            r["bucket"] = f["bucket"]
        if r["bucket"] and (not r.get("notes")
                            or r["notes"].startswith(("Body form of `",
                                                      "Certified through its full form"))):
            r["notes"] = (("Body form of `%s`; its status is the twin's. %s"
                           % (full, f.get("notes", "")))
                          if r.get("restatement") != "differs" else
                          ("Body form of `%s`, and it claims more. %s"
                           % (full, r.get("restatement_note", ""))))[:600]
        if r["lean_stated"] == "none" and f["lean_stated"] != "none":
            rest = r.get("restatement") or RESTATEMENT_DEFAULT
            r["restatement"] = rest
            r["lean_stated"] = f["lean_stated"]
            r["lean_proved"] = "partial" if rest == "differs" else f["lean_proved"]
            r["lean_files"] = list(f["lean_files"])
            r["decls"] = list(f["decls"])
            r["lean_via_twin"] = True
            if not r.get("notes"):
                r["notes"] = ("Certified through its full form `%s`; the body statement carries "
                              "no separate Lean declaration, so its status is the twin's to the "
                              "extent that it restates it." % full)
        if r["nl_status_auto"] == "open" and f["nl_status"] in ("proved", "partial"):
            r["nl_status_auto"] = f["nl_status"]
            if not r.get("nl_status_override"):
                r["nl_status"] = f["nl_status"]

    prev_top = load_ledger().get("paper", {})
    led = {
        "paper": {"root": CFG.root, "document": CFG.document,
                  "git_commit": source_commit(),
                  "files": [f for f, _, _ in CFG.files_or_expand()],
                  **{k: prev_top[k] for k in CURATED_TOP if k in prev_top}},
        "lean": {"root": CFG.lean_root, "git_commit": git_commit(CFG.lean_root)},
        "statements": rows,
    }
    if write:
        os.makedirs(CFG.out_dir, exist_ok=True)
        with open(CFG.ledger, "w", encoding="utf-8") as fh:
            json.dump(led, fh, indent=2, ensure_ascii=False)
            fh.write("\n")
        write_markdown(led, aux)
        write_dot(led)
    return led


# ---------------------------------------------------------------- the DAG --
def dag(led):
    """label -> [labels it depends on], restricted to statements in the ledger."""
    known = {s["label"] for s in led["statements"]}
    out = OrderedDict()
    for s in led["statements"]:
        out[s["label"]] = [d for d in s["deps"] if d in known]
    return out


def topo_order(led):
    """Dependencies first.  Cycles are broken by document order and reported."""
    d = dag(led)
    order_of = {s["label"]: i for i, s in enumerate(led["statements"])}
    seen, stack, out, cycles = set(), set(), [], []

    def visit(lab, path):
        if lab in seen:
            return
        if lab in stack:
            cycles.append(path + [lab])
            return
        stack.add(lab)
        for dep in sorted(d.get(lab, []), key=lambda x: order_of.get(x, 1 << 30)):
            visit(dep, path + [lab])
        stack.discard(lab)
        seen.add(lab)
        out.append(lab)

    for s in led["statements"]:
        visit(s["label"], [])
    return out, cycles


def depth(led):
    """Longest dependency chain below each statement --- the DAG's levels."""
    d = dag(led)
    memo, guard = {}, set()

    def go(lab):
        if lab in memo:
            return memo[lab]
        if lab in guard:
            return 0
        guard.add(lab)
        v = 1 + max([go(x) for x in d.get(lab, [])], default=-1)
        guard.discard(lab)
        memo[lab] = v
        return v

    return {s["label"]: go(s["label"]) for s in led["statements"]}


def title_of(sig):
    return CFG.titles.get(sig, sig)


def write_dot(led):
    by = {s["label"]: s for s in led["statements"]}
    fill = {("strict", "closed"): "#b7e4c7",
            ("strict", "partial"): "#ffe08a",
            ("scaffold", "partial"): "#ffd6a5",
            ("scaffold", "none"): "#ffd6a5",
            ("none", "none"): "#ffffff"}
    shape = {"definition": "box", "theorem": "doubleoctagon", "proposition": "ellipse",
             "lemma": "ellipse", "corollary": "ellipse", "remark": "note"}
    lines = ["digraph formalization {",
             '  rankdir=BT; node [style=filled,fontname="Helvetica",fontsize=9];',
             '  edge [color="#888888",arrowsize=0.6];']
    groups = defaultdict(list)
    for s in led["statements"]:
        groups[s["appendix"]].append(s)
    for sig, members in groups.items():
        lines.append('  subgraph "cluster_%s" {' % sig)
        lines.append('    label="%s"; color="#cccccc";' % title_of(sig))
        for s in members:
            key = (s["lean_stated"], s["lean_proved"])
            lines.append(
                '    "%s" [label="%s\\n%s", shape=%s, fillcolor="%s"];'
                % (s["label"], s["number"] or s["label"], (s["title"] or "")[:28],
                   shape.get(s["kind"], "ellipse"), fill.get(key, "#ffffff")))
        lines.append("  }")
    for s in led["statements"]:
        for dep in s["deps"]:
            if dep in by:
                lines.append('  "%s" -> "%s";' % (s["label"], dep))
    lines.append('  subgraph "cluster_legend" {')
    lines.append('    label="legend"; color="#cccccc"; fontsize=10;')
    lines.append('    l0 [label="closed in Lean", fillcolor="#b7e4c7", shape=box];')
    lines.append('    l1 [label="stated, partial", fillcolor="#ffe08a", shape=box];')
    lines.append('    l2 [label="scaffold", fillcolor="#ffd6a5", shape=box];')
    lines.append('    l3 [label="no Lean", fillcolor="#ffffff", shape=box];')
    lines.append('    l0 -> l1 -> l2 -> l3 [style=invis];')
    lines.append("  }")
    lines.append("}")
    open(CFG.dot, "w", encoding="utf-8").write("\n".join(lines) + "\n")
    # Render if graphviz is on the path; the .dot is the artifact, the rest is convenience.
    import shutil
    if CFG.render and shutil.which("dot"):
        stem = os.path.splitext(CFG.dot)[0]
        for fmt in ("svg", "pdf"):
            try:
                subprocess.run(["dot", "-T" + fmt, CFG.dot, "-o", stem + "." + fmt],
                               check=True, capture_output=True)
            except Exception:
                pass


def mermaid(led, sig):
    """One mermaid graph per section: its statements, and the edges leaving it."""
    by = {s["label"]: s for s in led["statements"]}
    members = [s for s in led["statements"] if s["appendix"] == sig]
    if not members:
        return ""
    ids = {}

    def nid(lab):
        if lab not in ids:
            ids[lab] = "n%d" % len(ids)
        return ids[lab]

    cls = {("strict", "closed"): "done", ("strict", "partial"): "part",
           ("scaffold", "partial"): "scaf", ("scaffold", "none"): "scaf"}
    out = ["```mermaid", "graph BT"]
    inside = {s["label"] for s in members}
    ext = OrderedDict()
    for s in members:
        for d in s["deps"]:
            if d in by and d not in inside:
                ext[d] = by[d]
    for s in members:
        lab = (s["number"] or s["label"]).replace('"', "'")
        short = s["title"] or s["label"].split(":", 1)[-1].replace("_", " ")
        out.append('  %s["%s %s"]' % (nid(s["label"]), lab,
                                      short[:30].replace('"', "'")))
        c = cls.get((s["lean_stated"], s["lean_proved"]))
        if c:
            out.append("  class %s %s;" % (nid(s["label"]), c))
    for lab, s in ext.items():
        out.append('  %s(["%s %s"])'
                   % (nid(lab), (s["number"] or lab).replace('"', "'"),
                      (s["title"] or "")[:22].replace('"', "'")))
    for s in members:
        for d in s["deps"]:
            if d in by:
                out.append("  %s --> %s" % (nid(s["label"]), nid(d)))
    out.append("  classDef done fill:#b7e4c7,stroke:#2d6a4f;")
    out.append("  classDef part fill:#ffe08a,stroke:#b07d00;")
    out.append("  classDef scaf fill:#ffd6a5,stroke:#b35c00;")
    out.append("```")
    return "\n".join(out)


# -------------------------------------------------------------- markdown ---
def cell_nl(s):
    g = STATUS_GLYPH[s["nl_status"]]
    if s["proof"]:
        f, ln = s["proof"].split(":")
        via = " *(via `%s`)*" % s["twin"] if s.get("proof_via_twin") else ""
        return "%s — [`%s:%s`](%s#L%s)%s" % (g, f, ln, f, ln, via)
    if s["nl_status"] == "cited" and s["cites"]:
        return "%s — `%s`" % (g, s["cites"][0])
    if s.get("nl_reason"):
        return "%s — %s" % (g, s["nl_reason"])
    return g


def cell_lean(s):
    if s["lean_stated"] == "none":
        return "—", "—"
    stated = {"strict": "strict", "scaffold": "scaffold"}[s["lean_stated"]]
    if s.get("lean_via_twin"):
        stated += {"verified": " *(via twin)*",
                   "differs": " *(via twin; restatement claims more)*",
                   }.get(s.get("restatement"), " *(via twin; restatement unchecked)*")
    if s["lean_files"]:
        stated += " (%s)" % ", ".join(
            os.path.basename(f) for f in s["lean_files"][:3])
        if len(s["lean_files"]) > 3:
            stated += " +%d" % (len(s["lean_files"]) - 3)
    proved = {"closed": "**yes**", "partial": "partial", "none": "no"}[s["lean_proved"]]
    return stated, proved


def write_markdown(led, aux):
    by_label = {s["label"]: s for s in led["statements"]}
    lv = depth(led)
    order, cycles = topo_order(led)
    rank = {lab: i for i, lab in enumerate(order)}
    n = len(led["statements"])
    closed = sum(1 for s in led["statements"] if s["lean_proved"] == "closed")
    part = sum(1 for s in led["statements"] if s["lean_proved"] == "partial")
    stated = sum(1 for s in led["statements"] if s["lean_stated"] != "none")
    nlproved = sum(1 for s in led["statements"] if s["nl_status"] in ("proved", "definition"))

    L = []
    A = L.append
    A("# The formalization ledger")
    A("")
    A("Generated by `%s`; **do not edit by hand** — curated fields "
      "(`bucket`, `nl_status_override`, `decls`, `notes`) live in "
      "`%s` and survive a rebuild." % (CFG.tool_name, os.path.basename(CFG.ledger)))
    A("")
    A("Paper `%s` at `%s`; Lean `%s` at `%s`."
      % (led["paper"]["document"], led["paper"]["git_commit"],
         led["lean"]["root"], led["lean"]["git_commit"]))
    A("")
    A("**%d statements.** Natural language: %d proved or definitional. "
      "Lean: **%d stated**, of which **%d closed** and %d partial."
      % (n, nlproved, stated, closed, part))
    A("")
    _inscope, _term, _target, _done = closure(led)
    A("**Closure: %d of %d.** The target is the %d in-scope statements less the %d terminal "
      "ones (bucket `T`, each with its reason); a row counts as done only when it is closed in "
      "Lean **in bucket A**."
      % (len(_done), len(_target), len(_inscope), len(_term)))
    A("")
    A("## How to read a row")
    A("")
    A("| column | says |")
    A("|---|---|")
    A("| **natural language** | the paper's own status, and where its proof is. "
      "`proved` — a `proof` environment discharges it here; `cited` — it is quoted from "
      "the literature; `partial` — the paper itself discloses a gap; `open` — asserted "
      "and not proved; `informal` — a remark that argues rather than proves. |")
    A("| **Lean stated** | a declaration carries the statement. `strict` — in "
      "`%s`, where `sorry` is a compile error; `scaffold` — in "
      "`%s`, where it is permitted and audited. |" % (CFG.strict_label, CFG.scaffold_label))
    A("| **Lean proved** | **yes** — closed, no `sorry` anywhere beneath it; `partial` — "
      "some items of a multi-part statement, or a disclosed weakening; `no` — stated only. |")
    A("| **lvl** | height in the dependency DAG: 0 depends on nothing in the paper. "
      "Formalize upwards. |")
    A("| **bucket** | how far the rest is. " +
      " · ".join("`%s` %s" % (k, v) for k, v in BUCKETS.items() if k) + " |")
    A("")
    A("A row is marked ⚠️ **stale** when its LaTeX changed after the Lean was written: "
      "the certificate may no longer certify the statement the paper makes.")
    A("")
    A("The DAG's edges are **references**, not always logical dependencies: a statement "
      "that says *see Lemma 7* gets an edge to Lemma 7 even when it does not stand on it. "
      "That is why the graph has cycles, and why `lvl` is a reading order rather than a "
      "proof order. Where the two disagree, the proof is the authority.")
    A("")

    # ---- what formalizing found out about the paper ----
    found = [x for x in led["statements"] if x.get("paper_findings")]
    if found:
        A("## What formalizing found in the paper")
        A("")
        A("Formalizing is a proof-reading pass with a machine holding the pen. These are the "
          "places where writing the Lean turned up something about the **paper** — a hypothesis "
          "used but not stated, a constant that needs a side condition, a step that does not go "
          "through as written. None is a refutation; each is a sentence the author may want to "
          "change. Entries marked **APPLIED** were applied through `/writer` on the date given; the "
          "rest are the author's call, and edits to the `.tex` go through `/writer`.")
        A("")
        triage = led.get("paper", {}).get("findings_triage") or []
        if triage:
            A("### Triage")
            A("")
            for kind, blurb in (("sentence", "**Would change a sentence.** A reader following "
                                 "the proof as written can be misled, or the statement is one "
                                 "reading away from false."),
                                ("context", "**Worth knowing; changes nothing.** The paper is "
                                 "correct as written, but something is doing quiet work."),
                                ("mathlib", "**Not about the paper.** What the formalization "
                                 "cost, recorded so the price is visible.")):
                rows = [t for t in triage if t.get("kind") == kind]
                if not rows:
                    continue
                A(blurb)
                A("")
                for t in rows:
                    A("- `%s` — %s" % (t["label"], t["one_line"]))
                A("")
        for x in found:
            A("### `%s` — %s" % (x["label"], x["title"] or x["kind"]))
            A("")
            A("*%s:%d*" % (x["file"], x["line"]))
            A("")
            for f in x["paper_findings"]:
                A("- %s" % f)
            A("")
    # ---- the roadmap ----
    A("## The roadmap")
    A("")
    if CFG.roadmap_intro:
        A(CFG.roadmap_intro)
        A("")
    for name, blurb, labs in CFG.milestones:
        rows = [by_label[x] for x in labs if x in by_label]
        done = sum(1 for r in rows if r["lean_proved"] == "closed")
        A("### %s — %d/%d closed" % (name, done, len(rows)))
        A("")
        A(blurb)
        A("")
        for r in rows:
            mark = {"closed": "✅", "partial": "🟡", "none": "⬜"}[r["lean_proved"]]
            A("- %s `%s` — %s *(%s, bucket %s)*"
              % (mark, r["label"], r["title"] or r["kind"],
                 "%s:%d" % (r["file"], r["line"]), r["bucket"] or "—"))
        A("")
    inscope = [s2 for s2 in led["statements"] if s2.get("in_lean_scope")]
    A("**In scope: %d statements**%s, of which %d are closed in Lean and %d partial. "
      "Out of scope: %d."
      % (len(inscope), (" (%s)" % CFG.scope_blurb) if CFG.scope_blurb else "",
         sum(1 for s2 in inscope if s2["lean_proved"] == "closed"),
         sum(1 for s2 in inscope if s2["lean_proved"] == "partial"),
         len(led["statements"]) - len(inscope)))
    A("")
    rest = [s2 for s2 in led["statements"]
            if s2["bucket"] in ("C", "D") and s2.get("in_lean_scope")]
    A("### Behind an obstruction — %d statements, in scope" % len(rest))
    A("")
    A("`C` is attempted-and-blocked, `D` is deferred; each row's `notes` field in "
      "`%s` names the obstruction.%s"
      % (os.path.basename(CFG.ledger),
         (" " + CFG.obstruction_note) if CFG.obstruction_note else ""))
    A("")

    # ---- the summary by section ----
    A("## Where it stands, by appendix")
    A("")
    A("| appendix | statements | NL proved | Lean stated | Lean closed |")
    A("|---|---:|---:|---:|---:|")
    groups = OrderedDict()
    for s in led["statements"]:
        groups.setdefault(s["appendix"], []).append(s)
    for sig, members in groups.items():
        A("| %s | %d | %d | %d | %d |"
          % (title_of(sig), len(members),
             sum(1 for s in members if s["nl_status"] in ("proved", "definition")),
             sum(1 for s in members if s["lean_stated"] != "none"),
             sum(1 for s in members if s["lean_proved"] == "closed")))
    A("")

    # ---- the tables ----
    for sig, members in groups.items():
        A("## %s" % title_of(sig))
        A("")
        A("| lvl | statement | natural language | Lean stated | Lean proved | bucket |")
        A("|---:|---|---|---|---|---|")
        for s in sorted(members, key=lambda x: rank.get(x["label"], 0)):
            st, pv = cell_lean(s)
            name = "%s %s" % (s["kind"].capitalize(), s["number"] or "")
            title = (" — %s" % s["title"]) if s["title"] else ""
            flag = " ⚠️" if s.get("stale") else ""
            twin = (" *(full form: `%s`)*" % s["twin"]) if s.get("twin") else ""
            A("| %d | **%s**%s%s<br>`%s` — [`%s:%d`](%s#L%d)%s | %s | %s | %s | %s |"
              % (lv[s["label"]], name.strip(), title, flag, s["label"],
                 s["file"], s["line"], s["file"], s["line"], twin,
                 cell_nl(s), st, pv, s["bucket"] or "—"))
        A("")
        m = mermaid(led, sig)
        if m:
            A("<details><summary>dependency graph — %s</summary>" % title_of(sig))
            A("")
            A(m)
            A("")
            A("</details>")
            A("")

    # ---- formalization order ----
    A("## Formalization order")
    A("")
    A("The DAG, flattened dependencies-first. A statement is ready when every row above "
      "it that it depends on is closed.")
    A("")
    if cycles:
        seen, uniq = set(), []
        for c in cycles:
            k = tuple(sorted(set(c)))
            if k not in seen:
                seen.add(k)
                uniq.append(c)
        A("**Reference cycles** — %d, broken by document order. Each is a statement "
          "pointing forward at one that points back; none is a circular proof, and "
          "`proof-checker` owns the question of whether any of them ever becomes one."
          % len(uniq))
        A("")
        for c in uniq:
            A("- " + " → ".join("`%s`" % x for x in c))
        A("")
    ready = ready_rows(led)
    A("### Ready now — every dependency is closed in Lean, and nothing is stated yet")
    A("")
    if ready:
        A("| lvl | statement | where | deps |")
        A("|---:|---|---|---:|")
        for s in ready:
            A("| %d | `%s` — %s | `%s:%d` | %d |"
              % (lv[s["label"]], s["label"], s["title"] or s["kind"],
                 s["file"], s["line"], len(s["deps"])))
    else:
        A("*(none — every statement whose dependencies are closed is already stated)*")
    A("")
    open(CFG.markdown, "w", encoding="utf-8").write("\n".join(L) + "\n")


def closure(led):
    """The closure target and how much of it is done."""
    inscope = [s for s in led["statements"] if s.get("in_lean_scope")]
    terminal = [s for s in inscope if s.get("bucket") == "T"]
    target = [s for s in inscope if s.get("bucket") != "T"]
    done = [s for s in target if s["lean_proved"] == "closed" and s.get("bucket") == "A"]
    return inscope, terminal, target, done


def next_rows(led):
    """Target rows not yet done, ordered by how close they are."""
    by = {s["label"]: s for s in led["statements"]}
    _, _, target, done = closure(led)
    done_labels = {s["label"] for s in done}
    rank_b = {"A": 0, "B": 1, "C": 2, "D": 3, "": 4}
    rank_z = {"S": 0, "M": 1, "L": 2, "": 3}
    out = []
    for s in target:
        if s["label"] in done_labels:
            continue
        deps = [by[d] for d in s["deps"] if d in by and d != s["label"]]
        open_deps = [d["label"] for d in deps if d["lean_proved"] != "closed"]
        out.append((rank_b.get(s.get("bucket") or "", 4), len(open_deps),
                    rank_z.get(s.get("size") or "", 3), s["label"], s, open_deps))
    out.sort(key=lambda t: t[:4])
    return [(t[4], t[5]) for t in out]


def ready_rows(led):
    by = {s["label"]: s for s in led["statements"]}
    out = []
    for s in led["statements"]:
        if s["lean_stated"] != "none":
            continue
        if s["nl_status"] in ("open", "informal"):
            continue
        deps = [by[d] for d in s["deps"] if d in by]
        if all(d["lean_proved"] == "closed" for d in deps):
            out.append(s)
    return out


# ----------------------------------------------------------- completeness --
def statement_env_pattern():
    envs = set(CFG.statement_envs or pg.CANONICAL_STATEMENT_ENVS) | set(CFG.env_alias)
    return re.compile(r"\\begin\{(%s)\}" % "|".join(sorted(re.escape(e) for e in envs)))


def tex_files_for_coverage():
    import fnmatch
    import glob
    pattern = os.path.join(CFG.root, "**", "*.tex") if CFG.coverage_recursive \
        else os.path.join(CFG.root, "*.tex")
    out = []
    for path in sorted(glob.glob(pattern, recursive=CFG.coverage_recursive)):
        rel = os.path.relpath(path, CFG.root)
        # `out_of_document` keys are exact relative paths or fnmatch patterns; each carries a reason.
        if rel in CFG.out_of_document or any(fnmatch.fnmatch(rel, k) for k in CFG.out_of_document):
            continue
        if any(fnmatch.fnmatch(rel, pat) or fnmatch.fnmatch(os.path.basename(rel), pat)
               for pat in CFG.coverage_skip):
            continue
        out.append((rel, path))
    return out


def coverage_gaps(unlabeled_only=False):
    """Every statement environment in the paper's directory that the ledger carries no row for.

    Two ways a statement escapes the ledger, both silent until this runs: it carries no
    `\\label`, so there is no key to file it under, or it lives in a `.tex` that is not in
    the file list.  An uncounted statement is worse than an uncertified one.
    """
    gaps = []
    listed = {f for f, _, _ in CFG.files_or_expand()}
    pat = statement_env_pattern()
    for rel, path in tex_files_for_coverage():
        text = pg.strip_comments(open(path, encoding="utf-8", errors="replace").read())
        for m in pat.finditer(text):
            env = m.group(1)
            line = text.count("\n", 0, m.start()) + 1
            end = text.find("\\end{%s}" % env, m.end())
            body = text[m.end(): end if end != -1 else len(text)]
            lab = re.search(r"\\label\{([^}]*)\}", body)
            if rel not in listed:
                if not unlabeled_only:
                    gaps.append("%s:%d: %s in a file the ledger does not read "
                                "(add it to [paper].files, or to out_of_document with a reason)"
                                % (rel, line, env))
            elif not lab:
                gaps.append("%s:%d: %s carries no \\label, so the ledger has no row for it"
                            % (rel, line, env))
    return gaps


# ------------------------------------------------------------------ check --
def check():
    led = build(write=False)
    src = lean_sources()
    fail, stale = [], []
    for s in led["statements"]:
        if s.get("stale"):
            stale.append(s["label"])
        for f in s["lean_files"]:
            if f not in src:
                fail.append("%s: listed Lean file %s does not exist" % (s["label"], f))
        for d in s["decls"]:
            # A decl is a bare Lean name: prose ("(related, …) Causal.foo") is found by its last
            # component below and would pass, while resolving to nothing in the environment.
            if not LEAN_NAME.match(d):
                fail.append("%s: decl %r is not a Lean name (prose belongs in notes)"
                            % (s["label"], d))
                continue
            f, ln = decl_line(src, s["lean_files"], d)
            if f is None:
                fail.append("%s: declaration %s not found in its listed files"
                            % (s["label"], d))
    # A proof whose title \ref's something that is no statement falls back to the most recent
    # statement without a proof, silently the wrong row (T-texgraph-proof-titles: five such proofs).
    g_titles, _aux = build_graph()
    for f, ln, opt in getattr(g_titles, "unresolved_proof_titles", []):
        fail.append("%s:%s: proof title %r names no statement (\\ref to a missing or "
                    "non-statement label)" % (f, ln, opt))
    # A configured proof macro that opens no proof is a typo or a stale config: its proofs, and
    # their edges, would be silently missing.
    for m in CFG.proof_macros:
        if not pg.PROOF_MACROS_USED.get(m[0]):
            fail.append("[paper] proof_macros: %s opens no proof in the document" % m[0])
    known = {s["label"] for s in led["statements"]}
    for s in led["statements"]:
        for d in s["deps"]:
            if d not in known:
                fail.append("%s: dependency %s is not a ledger statement" % (s["label"], d))
    for g in coverage_gaps():
        fail.append("uncounted statement — %s" % g)
    for s in led["statements"]:
        if s.get("bucket") == "T" and not s.get("terminal_reason"):
            fail.append("%s: bucket T with no terminal_reason" % s["label"])
        if s.get("terminal_reason") and s.get("bucket") != "T":
            fail.append("%s: terminal_reason set but bucket is %r" % (s["label"], s.get("bucket")))
        if s.get("bucket") == "T" and s["lean_proved"] == "closed":
            fail.append("%s: terminal but closed in Lean -- a closed claim is done, not terminal"
                        % s["label"])
    if not led["statements"]:
        fail.append("the ledger has no statements at all: nothing labelled in %s" % CFG.root)
    if os.path.exists(CFG.ledger):
        # The committed artifacts must be what a build would write: a stale ledger is drift.
        cur = json.load(open(CFG.ledger, encoding="utf-8"))
        want = json.loads(json.dumps(led, ensure_ascii=False))
        if cur != want:
            fail.append("%s is not what `build` would write — run build and commit"
                        % os.path.basename(CFG.ledger))
    else:
        fail.append("%s does not exist — run build" % os.path.basename(CFG.ledger))
    for lab in stale:
        print("STALE: %s — its LaTeX changed since the ledger was written." % lab)
    for e in fail:
        print("FAIL: %s" % e)
    if fail or stale:
        return 1
    print("ledger: %d statements, %d Lean-stated, all links resolve."
          % (len(led["statements"]),
             sum(1 for s in led["statements"] if s["lean_stated"] != "none")))
    return 0


def label_audit():
    gaps = coverage_gaps(unlabeled_only=True)
    for g in gaps:
        print("UNLABELED: %s" % g)
    print("label-audit: %d unlabeled statement environments" % len(gaps))
    return 1 if gaps else 0


def crosscheck():
    """The ledger and the Lean library's paper-map.json are two views of the same statements."""
    pmp = paper_map_path()
    if not pmp:
        print("crosscheck: no paper_map configured; nothing to compare")
        return 0
    if not os.path.exists(pmp):
        print("crosscheck: no paper-map.json at %s" % pmp)
        return 0
    led = {s["label"]: s for s in load_ledger()["statements"]}
    pm = json.load(open(pmp, encoding="utf-8"))["statements"]
    want = {"closed": "closed", "partial": "partial", "open": "none", "stale": "partial"}
    bad, detached = [], []
    for row in pm:
        lab = row["label"]
        l = led.get(lab)
        if l is None:
            bad.append("%s: in the map, absent from the ledger" % lab)
            continue
        if l["lean_proved"] != want.get(row["status"], "partial"):
            bad.append("%s: map status %s, ledger %s" % (lab, row["status"], l["lean_proved"]))
        end = l["proof_span"][1] if l["proof_span"] else l["tex_span"][1]
        if row["tex_span"] != [l["tex_span"][0], end]:
            if row["tex_span"] == l["tex_span"]:
                detached.append(lab)      # proof does not immediately follow: both are right
            else:
                bad.append("%s: map span %s, ledger %s..%s"
                           % (lab, row["tex_span"], l["tex_span"][0], end))
    for e in bad:
        print("FAIL: %s" % e)
    if detached:
        print("note: %d statements whose proof does not immediately follow them (%s) — the map "
              "stops at the statement, the ledger points at the proof; both correct."
              % (len(detached), ", ".join(detached)))
    if bad:
        return 1
    print("crosscheck: %d mapped statements agree with the ledger" % len(pm))
    return 0


def reaffirm(label):
    """Accept the current LaTeX of one statement as its baseline, clearing `stale`."""
    led = load_ledger()
    hit = [s for s in led["statements"] if s["label"] == label]
    if not hit:
        print("reaffirm: no such statement: %s" % label)
        return 1
    row = hit[0]
    if not row.get("stale"):
        print("reaffirm: %s is not stale; nothing to do" % label)
        return 0
    row["statement_sha256"] = row["statement_sha256_current"]
    row["stale"] = False
    with open(CFG.ledger, "w", encoding="utf-8") as fh:
        json.dump(led, fh, indent=2, ensure_ascii=False)
        fh.write("\n")
    print("reaffirm: %s accepted at its current LaTeX" % label)
    return 0


def sync_map():
    """Push the ledger's triage onto the Lean library's paper-map.json (judgements only)."""
    pmp = paper_map_path()
    if not pmp or not os.path.exists(pmp):
        print("sync_map: no paper-map.json configured or present")
        return 1
    led = {s["label"]: s for s in load_ledger()["statements"]}
    m = json.load(open(pmp, encoding="utf-8"))
    status_of = {"closed": "closed", "partial": "partial", "none": "open"}
    changed = []
    for row in m["statements"]:
        l = led.get(row["label"])
        if l is None:
            continue
        new = {"bucket": l["bucket"], "status": status_of[l["lean_proved"]]}
        if row.get("status") == "stale":          # a stale row is trace_check's to clear
            new.pop("status")
        if any(row.get(k) != v for k, v in new.items()):
            changed.append(row["label"])
        row.update(new)
    with open(pmp, "w", encoding="utf-8") as fh:
        json.dump(m, fh, indent=2, ensure_ascii=False)
        fh.write("\n")
    print("sync_map: %d rows updated (%s)"
          % (len(changed), ", ".join(changed[:6]) + ("…" if len(changed) > 6 else "")))
    return 0


# ------------------------------------------------------------------ query --
def stats(led):
    n = led["statements"]
    print("%d statements\n" % len(n))
    print("natural language")
    for k in NL_STATUSES:
        c = sum(1 for s in n if s["nl_status"] == k)
        if c:
            print("  %-10s %3d" % (k, c))
    print("\nLean")
    for k in LEAN_STATED:
        print("  stated %-9s %3d" % (k, sum(1 for s in n if s["lean_stated"] == k)))
    for k in LEAN_PROVED:
        print("  proved %-9s %3d" % (k, sum(1 for s in n if s["lean_proved"] == k)))
    inscope, terminal, target, done = closure(led)
    print("\nclosure  %d / %d   (in scope %d, terminal %d; done = closed in bucket A)"
          % (len(done), len(target), len(inscope), len(terminal)))
    twins = [s for s in n if s.get("lean_via_twin")]
    if twins:
        print("\nof which carried by an appendix twin (%d)" % len(twins))
        for k in ("verified", "unverified", "differs"):
            c = [s for s in twins if (s.get("restatement") or RESTATEMENT_DEFAULT) == k]
            if c:
                print("  restatement %-11s %3d   (%d closed)"
                      % (k, len(c), sum(1 for s in c if s["lean_proved"] == "closed")))
    print("\nby appendix")
    g = OrderedDict()
    for s in n:
        g.setdefault(s["appendix"], []).append(s)
    for sig, m in g.items():
        print("  %-6s %3d statements  %3d stated  %3d closed"
              % (sig, len(m),
                 sum(1 for s in m if s["lean_stated"] != "none"),
                 sum(1 for s in m if s["lean_proved"] == "closed")))


def show(led, lab):
    by = {s["label"]: s for s in led["statements"]}
    s = by.get(lab)
    if not s:
        print("no such statement: %s" % lab)
        return 1
    lv = depth(led)
    print("%s %s — %s" % (s["kind"].capitalize(), s["number"], s["title"]))
    print("  label      %s" % s["label"])
    print("  where      %s:%d–%d  (appendix %s, DAG level %d)"
          % (s["file"], s["tex_span"][0], s["tex_span"][1], s["appendix"], lv[lab]))
    print("  NL         %s%s" % (s["nl_status"],
                                 ("  proof at %s" % s["proof"]) if s["proof"] else ""))
    print("  Lean       stated=%s proved=%s bucket=%s"
          % (s["lean_stated"], s["lean_proved"], s["bucket"] or "—"))
    for f in s["lean_files"]:
        print("             %s" % f)
    for d in s["decls"]:
        print("             · %s" % d)
    if s["scope_notes"]:
        print("  scope      %s" % s["scope_notes"])
    print("  depends on (%d)" % len(s["deps"]))
    for d in s["deps"]:
        t = by.get(d)
        print("    -> %-34s %s" % (d, ("[%s/%s]" % (t["lean_stated"], t["lean_proved"]))
                                   if t else ""))
    used = [x["label"] for x in led["statements"] if lab in x["deps"]]
    print("  used by (%d)" % len(used))
    for u in used:
        print("    <- %s" % u)
    return 0


def main(argv=None):
    global CFG
    argv = list(sys.argv[1:] if argv is None else argv)
    cfg_path = "ledger.toml"
    if "-c" in argv or "--config" in argv:
        k = argv.index("-c") if "-c" in argv else argv.index("--config")
        cfg_path = argv[k + 1]
        del argv[k:k + 2]
    if not os.path.exists(cfg_path):
        die("no such config: %s" % cfg_path)
    CFG = Config(cfg_path)
    if CFG.source != "tex":
        die("[paper].source is %r: a ledger needs the .tex source of the draft, and this "
            "paper has none on this host (see legacy/MANIFEST.json)" % CFG.source)
    if not os.path.isdir(CFG.root):
        die("[paper].root does not exist: %s" % CFG.root)
    cmd = argv[0] if argv else "build"
    if cmd == "build":
        led = build()
        print("wrote %s, %s and %s — %d statements"
              % (os.path.basename(CFG.ledger), os.path.basename(CFG.markdown),
                 os.path.basename(CFG.dot), len(led["statements"])))
        return 0
    if cmd == "check":
        return check() or crosscheck()
    if cmd == "label-audit":
        return label_audit()
    if cmd == "crosscheck":
        return crosscheck()
    if cmd == "sync-map":
        return sync_map()
    if cmd == "reaffirm":
        return reaffirm(argv[1])
    led = load_ledger() if os.path.exists(CFG.ledger) else build(write=False)
    if cmd == "stats":
        stats(led)
    elif cmd == "order":
        lv, (order, cycles) = depth(led), topo_order(led)
        by = {s["label"]: s for s in led["statements"]}
        for lab in order:
            s = by[lab]
            print("%2d  %-8s %-38s %-9s %-8s %s"
                  % (lv[lab], s["appendix"], lab, s["lean_stated"], s["lean_proved"],
                     s["title"] or s["kind"]))
        if cycles:
            print("\ncycles: %d" % len(cycles))
    elif cmd == "ready":
        lv = depth(led)
        for s in ready_rows(led):
            print("%2d  %-8s %-38s %s" % (lv[s["label"]], s["appendix"], s["label"],
                                          s["title"] or s["kind"]))
    elif cmd == "next":
        lv = depth(led)
        for s, open_deps in next_rows(led):
            print("%-2s %-2s %-8s %-36s %-8s %s%s"
                  % (s.get("bucket") or "—", s.get("size") or "·", s["appendix"], s["label"],
                     s["lean_proved"],
                     ("remains: %s" % s["blocked_on"]) if s.get("blocked_on") else "",
                     ("  open refs: %s" % ", ".join(open_deps)) if open_deps else ""))
    elif cmd == "node":
        return show(led, argv[1])
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
