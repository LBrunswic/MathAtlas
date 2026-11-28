#!/usr/bin/env python3
"""The mechanical rename tool of ARCHITECTURE.md §4.2 (DEC-211; target T-arch-rename-tool).

    python3 tools/rename_tool.py MAP [--target DIR] [--verbose]     # = plan: a dry run, writes nothing
    python3 tools/rename_tool.py plan  MAP [--target DIR] [--verbose]
    python3 tools/rename_tool.py apply MAP --target DIR              # DIR must NOT be the hub checkout
    python3 tools/rename_tool.py check [--target DIR] [--resolve auto|facts|grep] [--all]

It is run on a scratch copy before the migration window, never on the live tree: `apply` refuses
a target that is, contains, or lies inside the hub checkout this tool belongs to (or
~/Dropbox/LeanArticles, ~/LeanArticles, $LEANARTICLES_HUB), and has no default target.

THE MAP is a TOML file of dotted prefixes, matched component-wise, longest key first:

    [rename]        # module names AND namespaces / declaration names
    "Causal.Flat" = "Lorentzian.Flat"
    [modules]       # module names only (imports, module files, paths)
    [namespaces]    # namespaces and declaration names only

A one-component key ("Causal") is rewritten only in a dotted token ("Causal.x") or on a Lean
`import` / `namespace` / `end` / `open` / `export` line, never as a bare word of prose.

WHAT `apply` REWRITES (textually, so comments and layout are kept), in DIR:
  lean      every module of every lean_lib of every package (lean/, lean-*/ with a lakefile.toml):
            `import` lines by the module map; `namespace`/`end`/`open`/`export` lines and every
            fully qualified name (also `_root_.X`) by the namespace map; paths X/Y.lean by the
            module map. A module whose name the module map changes is MOVED inside its srcDir.
  curation  papers/*/certificate/curation.toml (decls, extra_lean_files, and the notes' text)
  binder    papers/*/certificate/binder.toml
  ladder    programme/ladder.toml (lean, witness, and the text)
  roadmap   roadmap/roadmap.toml, programme/roadmap.toml, papers/*/programme/roadmap.toml
  kb        lean/kb/**/*.md, lean-*/kb/**/*.md
  atlas     reports/atlas/hub.toml, reports/atlas/lean/*.json (facts and edges: declaration
            names, module names and file paths)
In a token outside a Lean command line, a name the old tree knows as a module takes the module
map, anything else the namespace map (then the module map if no namespace key applies).

WHAT `check` RESOLVES. References: Lean `import`s (against module files); curation `decls` and
`extra_lean_files`; binder ett/localisation/open_localisation/geometric.proves/geometric.by/
proposed.lean; ladder lean/witness; hub.toml headlines; the edges files' decls, principals,
witnesses and paths (all STRUCTURED: a dangling one fails the check); and every hub-rooted dotted
name or .lean path in the text of those files (TEXT: reported, never fatal: evidence quotes
history). The source (`--resolve auto`, the default): the compiled facts, reports/atlas/lean/
facts-*.json and */docs/lean-facts.json, with module files from the tree; a name the facts lack
falls back to a grep of the declarations in the .lean sources (namespace-aware, approximate: a
name under a declared name, e.g. a field, resolves), and is counted apart. `--resolve facts` or
`grep` forces one.

`apply` checks twice: a grep-resolved baseline before, and after the rewrite every reference that
resolved before must still resolve with its rewritten name, by the grep of the REWRITTEN sources
(the facts are rewritten mechanically by the same map and would hide a missed relative name).
A miss is a `regression` line and exit 1. Exit 2: refused (live tree, bad map, move collision).

NOT COVERED (listed by the plan as `manual`, `warning` or `not covered`): relative names in Lean
bodies (the build finds them), relative `namespace`/`open`/declaration names that the rewrite
cannot express (reported with file:line), lakefiles (lib names, roots, globs), moves between
packages (`git mv` in the window's step 2), papers/*/ledger/ (generated, and ledger.toml roots),
lean/docs, paper-map.json, the rest of the tree (counted as `not covered` files still naming an
old prefix), and non-ASCII keys in \\u-escaped JSON.
"""
import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import import_gate as ig  # noqa: E402  (packages, modules, header_imports, EXTERNAL)

COMP = r"[^\W\d][\w'!?]*"
NAME_RE = re.compile(r"^%s(?:\.%s)*$" % (COMP, COMP))
TOKEN = re.compile(r"(?<![\w.'!?«/\\-])%s(?:\.%s)*" % (COMP, COMP))
BRACES = re.compile(r"(?<![\w.'!?«/\\-])(%s(?:\.%s)*)\.\{([^{}\s]+(?:,\s*[^{}\s,]+)*)\}" % (COMP, COMP))
PATH_TOKEN = re.compile(r"(?<![\w./-])((?:[\w.+-]+/)*[\w'+-]+\.lean)\b")
FILE_EXT = re.compile(r"\.(lean|md|toml|json|py|tex|txt|olean|sh)$")
CATEGORIES = ("lean", "curation", "binder", "ladder", "roadmap", "kb", "atlas")


# ------------------------------------------------------------------ the map
class RenameMap:
    def __init__(self, modules, namespaces, source="<map>"):
        self.mod, self.ns, self.source = dict(modules), dict(namespaces), source
        self.roots = {k.split(".")[0] for k in list(self.mod) + list(self.ns)}
        self._path = None

    @classmethod
    def load(cls, path):
        with open(path, "rb") as f:
            cfg = tomllib.load(f)
        bad = set(cfg) - {"rename", "modules", "namespaces"}
        if bad:
            raise ValueError("unknown section(s) %s (want [rename], [modules], [namespaces])" % sorted(bad))
        both, mods, nss = cfg.get("rename", {}), cfg.get("modules", {}), cfg.get("namespaces", {})
        for sec, table in (("rename", both), ("modules", mods), ("namespaces", nss)):
            for k, v in table.items():
                if not isinstance(v, str) or not NAME_RE.match(k) or not NAME_RE.match(v):
                    raise ValueError("[%s] %r = %r: keys and values must be dotted Lean names" % (sec, k, v))
                if k == v:
                    raise ValueError("[%s] %r maps to itself" % (sec, k))
        for k in set(both) & (set(mods) | set(nss)):
            raise ValueError("%r is in [rename] and in [modules]/[namespaces]" % k)
        if not (both or mods or nss):
            raise ValueError("the map is empty")
        return cls({**both, **mods}, {**both, **nss}, path)

    def inverse(self):
        return RenameMap({v: k for k, v in self.mod.items()}, {v: k for k, v in self.ns.items()})

    @staticmethod
    def _remap(name, table, single):
        parts = name.split(".")
        for k in range(len(parts), 0, -1):
            key = ".".join(parts[:k])
            if key in table:
                if k == 1 and len(parts) == 1 and not single:
                    return None
                return ".".join([table[key]] + parts[k:])
        return None

    def module(self, name, single=True):
        return self._remap(name, self.mod, single)

    def namespace(self, name, single=True):
        return self._remap(name, self.ns, single)

    def name(self, name, modules=(), single=False):
        """A dotted name of free text: the module map if the old tree knows it as a module."""
        if name in modules:
            return self.module(name, single) or self.namespace(name, single)
        return self.namespace(name, single) or self.module(name, single)

    def path_re(self):
        if self._path is None and self.mod:
            keys = sorted(self.mod, key=len, reverse=True)
            alt = "|".join(re.escape(k.replace(".", "/")) for k in keys)
            self._path = re.compile(r"(?:(?<=/)|(?<![\w./-]))(%s)(?=/|\.lean\b)" % alt)
        return self._path

    def path(self, p):
        r = self.path_re()
        if r is None:
            return p
        return r.sub(lambda m: self.mod[m.group(1).replace("/", ".")].replace(".", "/"), p)

    def describe(self):
        out = []
        for k in sorted(set(self.mod) | set(self.ns)):
            kinds = [n for n, t in (("modules", self.mod), ("namespaces", self.ns)) if k in t]
            v = self.mod.get(k) or self.ns.get(k)
            out.append("  %s -> %s   [%s]" % (k, v, ", ".join(kinds)))
        return out


# ------------------------------------------------------------------ text rewriting
def _split_suffix(tok, prose):
    if not prose:
        return tok, ""
    m = re.search(r"('s|'|[?!]+)$", tok)
    if m and "." in tok[:m.start()]:
        return tok[:m.start()], m.group(0)
    return tok, ""


def rewrite_line(line, rmap, ctx, modules, prose):
    """(new line, count). ctx: 'import' (module map), 'command' (namespace map, bare keys too),
    'body' (per-token choice, dotted tokens only)."""
    count = 0
    if not (rmap.roots & set(re.findall(r"[^\W\d][\w'!?]*", line))):
        return line, 0

    def sub(m):
        nonlocal count
        tok = m.group(0)
        if FILE_EXT.search(tok):
            return tok
        pre = ""
        if tok.startswith("_root_."):
            pre, tok = "_root_.", tok[len("_root_."):]
        core, suf = _split_suffix(tok, prose)
        if ctx == "import":
            new = rmap.module(core, True)
        elif ctx == "command":
            new = rmap.namespace(core, True)
        else:
            new = rmap.name(core, modules, False)
        if new is None:
            return m.group(0)
        count += 1
        return pre + new + suf

    line = TOKEN.sub(sub, line)
    r = rmap.path_re()
    if r is not None:
        line, n = r.subn(lambda m: rmap.mod[m.group(1).replace("/", ".")].replace(".", "/"), line)
        count += n
    return line, count


def rewrite_text(text, rmap, modules, lean=False):
    ctx = lean_contexts(text) if lean else {}
    out, total = [], 0
    for i, line in enumerate(text.splitlines(keepends=True), 1):
        new, n = rewrite_line(line, rmap, ctx.get(i, "body"), modules, prose=not lean)
        out.append(new)
        total += n
    return "".join(out), total


# ------------------------------------------------------------------ Lean scanning
NS_RE = re.compile(r"^\s*namespace\s+(\S+)")
SEC_RE = re.compile(r"^\s*(?:noncomputable\s+)?section\b")
END_RE = re.compile(r"^\s*end\b\s*(\S+)?")
MUTUAL_RE = re.compile(r"^\s*mutual\b")
OPEN_RE = re.compile(r"^\s*(?:open|export)\s+(.*)")
DECL_RE = re.compile(r"^\s*(?:@\[.*?\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)\s+)*"
                     r"(theorem|lemma|def|abbrev|instance|structure|class\s+inductive|class|inductive|axiom|"
                     r"opaque|irreducible_def|alias)\s+([^\s:(){}\[\]⦃⟨,]+)")
OPEN_SKIP = {"scoped", "in", "hiding", "renaming", "→", "->"}


def code_lines(text):
    """Each line with its comments (nested /- -/, --) removed; string literals kept."""
    out, depth = [], 0
    for line in text.split("\n"):
        i, n, buf = 0, len(line), []
        while i < n:
            if depth:
                if line.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif line.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            elif line.startswith("/-", i):
                depth, i = 1, i + 2
            elif line.startswith("--", i):
                break
            elif line[i] == '"':
                j = i + 1
                while j < n and line[j] != '"':
                    j += 2 if line[j] == "\\" else 1
                buf.append(line[i:j + 1])
                i = j + 1
            else:
                buf.append(line[i])
                i += 1
        out.append("".join(buf))
    return out


def lean_contexts(text):
    ctx = {ln: "import" for ln, _ in ig.header_imports(text)}
    for ln, code in enumerate(code_lines(text), 1):
        if ln not in ctx and (NS_RE.match(code) or END_RE.match(code) or OPEN_RE.match(code)):
            ctx[ln] = "command"
    return ctx


def join(a, b):
    return b if not a else a + "." + b


def open_ids(rest):
    rest = re.split(r"\bin\b\s*$|\(|\bhiding\b|\brenaming\b", rest)[0]
    return [w for w in rest.split() if w not in OPEN_SKIP and NAME_RE.match(w)]


def lean_scan(text):
    """Declarations (line, full, kind), namespaces opened, and the events a rename must re-read:
    ('namespace' | 'decl' | 'open', line, written, outer_namespace_stack)."""
    stack, decls, namespaces, events = [], [], set(), []

    def cur():
        fulls = [e[1] for e in stack if e[0] == "ns"]
        return fulls[-1] if fulls else ""

    for ln, code in enumerate(code_lines(text), 1):
        m = NS_RE.match(code)
        if m:
            w = m.group(1)
            events.append(("namespace", ln, w, cur()))
            full = join(cur(), w)
            stack.append(("ns", full))
            parts = full.split(".")
            namespaces.update(".".join(parts[:k]) for k in range(1, len(parts) + 1))
            continue
        if SEC_RE.match(code) or MUTUAL_RE.match(code):
            stack.append(("sec", None))
            continue
        m = END_RE.match(code)
        if m and not code.strip().startswith("end_"):
            if stack:
                stack.pop()
            continue
        m = OPEN_RE.match(code)
        if m:
            for w in open_ids(m.group(1)):
                events.append(("open", ln, w, cur()))
            continue
        m = DECL_RE.match(code)
        if m:
            kind, w = m.group(1), m.group(2).rstrip(".")
            if not NAME_RE.match(w.replace("_root_.", "")):
                continue
            full = w[len("_root_."):] if w.startswith("_root_.") else join(cur(), w)
            decls.append((ln, full, kind))
            events.append(("decl", ln, w, cur()))
    return decls, namespaces, events


def lean_manual(events, rmap, known_ns):
    """Events whose meaning the textual rewrite does not preserve: (rule, line, message)."""
    out, newns = [], {}

    def renamed(full):
        return rmap.namespace(full, True) or full

    for kind, ln, w, outer in events:
        new_outer = renamed(outer) if outer else ""
        if kind == "open":
            cands = []
            parts = outer.split(".") if outer else []
            for k in range(len(parts), 0, -1):
                cands.append(".".join(parts[:k]) + "." + w)
            chosen = next((c for c in cands if c in known_ns), w)
            if chosen == w:
                continue                  # absolute: rewritten on its command line
            new_w = rmap.namespace(w, True) or w
            level = chosen[:-len(w) - 1]  # the enclosing namespace it resolves under
            actual, expected = join(renamed(level), new_w), renamed(chosen)
            if actual != expected:
                out.append(("relative-open", ln, "`open %s` inside %s means %s: the rewrite gives %s, the rename wants %s"
                            % (w, outer, chosen, actual, expected)))
            continue
        if w.startswith("_root_."):
            continue
        new_w = rmap.namespace(w, kind == "namespace") or w
        actual, expected = join(new_outer, new_w), renamed(join(outer, w))
        if actual != expected:
            rule = "relative-namespace" if kind == "namespace" else "relative-declaration"
            out.append((rule, ln, "`%s %s` inside %s: the rewrite gives %s, the rename wants %s" %
                        ("namespace" if kind == "namespace" else "declaration", w, outer or "(root)",
                         actual, expected)))
    return out


# ------------------------------------------------------------------ the tree
def lean_modules(hub):
    """{module: (pkg, srcdir_rel_hub, file_rel_hub)} over every lean_lib of every package."""
    pkgs, _ = ig.packages(hub)
    out = {}
    for pkg in pkgs:
        for mod, (_lib, _sc, _st, rel) in ig.modules(hub, pkg).items():
            src = rel[:-len(".lean")][:-len(mod)].rstrip("/")
            out[mod] = (pkg, src, rel)
        # Module trees under a lib's srcDir that no lib root claims (a rename moved them out of the
        # roots before the lakefile is edited): every capitalised top-level entry, as Lean roots are.
        for lib, _roots in lib_roots_of(hub, pkg):
            src = os.path.normpath(os.path.join(pkg, dict(_lib_src(hub, pkg)).get(lib, ".")))
            base = os.path.join(hub, src)
            for top in sorted(os.listdir(base)) if os.path.isdir(base) else []:
                if not top[:1].isupper():
                    continue
                p = os.path.join(base, top)
                cands = [p] if top.endswith(".lean") and os.path.isfile(p) else []
                if os.path.isdir(p):
                    for dp, dns, fns in os.walk(p):
                        dns[:] = sorted(d for d in dns if not d.startswith("."))
                        cands += [os.path.join(dp, f) for f in sorted(fns) if f.endswith(".lean")]
                for c in cands:
                    mod = os.path.relpath(c, base)[:-len(".lean")].replace(os.sep, ".")
                    out.setdefault(mod, (pkg, src, os.path.relpath(c, hub)))
    return out


def _lib_src(hub, pkg):
    with open(os.path.join(hub, pkg, "lakefile.toml"), "rb") as f:
        lake = tomllib.load(f)
    return [(lib["name"], lib.get("srcDir", ".")) for lib in lake.get("lean_lib", [])]


def lib_roots_of(hub, pkg):
    with open(os.path.join(hub, pkg, "lakefile.toml"), "rb") as f:
        lake = tomllib.load(f)
    return [(lib["name"], ig.lib_roots(lib)) for lib in lake.get("lean_lib", [])]


def covered_files(hub, mods=None):
    mods = lean_modules(hub) if mods is None else mods
    g = lambda pat: sorted(os.path.relpath(p, hub) for p in glob.glob(os.path.join(hub, pat), recursive=True)
                           if os.path.isfile(p))
    return {
        "lean": sorted(v[2] for v in mods.values()),
        "curation": g("papers/*/certificate/curation.toml"),
        "binder": g("papers/*/certificate/binder.toml"),
        "ladder": g("programme/ladder.toml"),
        "roadmap": g("roadmap/roadmap.toml") + g("programme/roadmap.toml") + g("papers/*/programme/roadmap.toml"),
        "kb": g("lean/kb/**/*.md") + g("lean-*/kb/**/*.md"),
        "atlas": g("reports/atlas/hub.toml") + g("reports/atlas/lean/*.json"),
    }


def read(hub, rel):
    with open(os.path.join(hub, rel), encoding="utf-8") as f:
        return f.read()


# ------------------------------------------------------------------ the resolution index
class Index:
    def __init__(self):
        self.facts_decls, self.facts_modules = set(), set()
        self.grep_decls, self.grep_ns = set(), set()
        self.file_modules, self.lean_files = set(), set()
        self.facts_files, self.pkg_bases = [], set()
        self._ns = None

    @classmethod
    def build(cls, hub, mods=None):
        idx = cls()
        mods = lean_modules(hub) if mods is None else mods
        for mod, (pkg, src, rel) in mods.items():
            idx.file_modules.add(mod)
            idx.lean_files.add(rel)
            idx.pkg_bases.update({pkg, src})
            decls, namespaces, _ = lean_scan(read(hub, rel))
            idx.grep_decls.update(d for _, d, _ in decls)
            idx.grep_ns.update(namespaces)
        for pkg in ig.packages(hub)[0]:
            for dp, dns, fns in os.walk(os.path.join(hub, pkg)):
                dns[:] = [d for d in dns if not d.startswith(".")]
                idx.lean_files.update(os.path.relpath(os.path.join(dp, f), hub) for f in fns if f.endswith(".lean"))
        for p in sorted(glob.glob(os.path.join(hub, "reports/atlas/lean/facts-*.json")) +
                        glob.glob(os.path.join(hub, "lean*/docs/lean-facts.json"))):
            with open(p, encoding="utf-8") as f:
                data = json.load(f)
            decls = data.get("declarations", {})
            idx.facts_decls.update(decls)
            idx.facts_modules.update(v.get("module") for v in decls.values() if isinstance(v, dict) and v.get("module"))
            idx.facts_files.append(os.path.relpath(p, hub))
        return idx

    def namespaces(self):
        if self._ns is None:
            ns = set(self.grep_ns)
            for n in self.facts_decls | self.grep_decls | self.facts_modules | self.file_modules:
                parts = n.split(".")
                ns.update(".".join(parts[:k]) for k in range(1, len(parts)))
            self._ns = ns
        return self._ns

    def roots(self):
        return {m.split(".")[0] for m in self.file_modules | self.facts_modules}

    def modules(self):
        return self.file_modules | self.facts_modules

    def resolve(self, name, mode):
        """'facts' | 'grep' | 'files' | None."""
        for n in variants(name):
            if mode in ("auto", "facts") and (n in self.facts_decls or n in self.facts_modules):
                return "facts"
            if n in self.file_modules:
                return "files"
            if mode in ("auto", "facts") and self.facts_decls and n in self.namespaces():
                return "facts"
            if mode in ("auto", "grep"):
                if n in self.grep_decls or n in self.grep_ns:
                    return "grep"
                parts = n.split(".")
                if any(".".join(parts[:k]) in self.grep_decls for k in range(1, len(parts))):
                    return "grep"
                if mode == "grep" and n in self.namespaces():
                    return "grep"
        return None

    def resolve_path(self, p):
        p = re.sub(r":\d+(?:[-–]\d+)?$", "", p)
        if p in self.lean_files:
            return "files"
        for base in self.pkg_bases:
            if os.path.normpath(os.path.join(base, p)) in self.lean_files:
                return "files"
        return None


def variants(name):
    out = [name]
    for pat in (r"[?!]+$", r"'s$", r"'$"):
        v = re.sub(pat, "", name)
        if v != name and v not in out:
            out.append(v)
    return out


# ------------------------------------------------------------------ references
class Ref:
    __slots__ = ("kind", "category", "file", "line", "name", "structured")

    def __init__(self, kind, category, file, line, name, structured):
        self.kind, self.category, self.file, self.line, self.name, self.structured = \
            kind, category, file, line, name, structured


def line_of(text, s):
    i = text.find('"%s"' % s)
    if i < 0:
        i = text.find(s)
    return text.count("\n", 0, i) + 1 if i >= 0 else 0


def strings(o):
    if isinstance(o, str):
        yield o
    elif isinstance(o, list):
        for v in o:
            yield from strings(v)
    elif isinstance(o, dict):
        for v in o.values():
            yield from strings(v)


def hubname(s, roots, modules):
    return isinstance(s, str) and NAME_RE.match(s) and (s in modules or ("." in s and s.split(".")[0] in roots))


def collect_refs(hub, idx, mods=None):
    mods = lean_modules(hub) if mods is None else mods
    files = covered_files(hub, mods)
    roots, modules = idx.roots(), idx.modules()
    refs = []
    for rel in files["lean"]:
        for ln, m in ig.header_imports(read(hub, rel)):
            if m.split(".")[0] not in ig.EXTERNAL:
                refs.append(Ref("module", "lean-import", rel, ln, m, True))
    for cat in CATEGORIES[1:]:
        for rel in files[cat]:
            text = read(hub, rel)
            structured = set()

            def add(kind, name):
                if (kind, name) not in structured:
                    structured.add((kind, name))
                    refs.append(Ref(kind, cat, rel, line_of(text, name), name, True))

            if rel.endswith(".toml"):
                try:
                    data = tomllib.loads(text)
                except tomllib.TOMLDecodeError as e:
                    refs.append(Ref("toml", cat, rel, 0, str(e), True))
                    continue
            else:
                data = json.loads(text) if rel.endswith(".json") else None
            if cat == "curation":
                for row in data.get("row", []):
                    for d in row.get("decls", []):
                        add("decl", d)
                    for p in row.get("extra_lean_files", []):
                        add("path", p)
            elif cat == "binder":
                for b in data.get("bind", []):
                    for key in ("ett", "localisation", "open_localisation"):
                        for s in strings(b.get(key, [])):
                            if hubname(s, roots, modules):
                                add("decl", s)
                    for g in b.get("geometric", []):
                        for s in strings([g.get("proves", []), g.get("by", [])]):
                            if hubname(s, roots, modules):
                                add("decl", s)
                for p in data.get("proposed", []):
                    for s in strings(p.get("lean", [])):
                        if hubname(s, roots, modules):
                            add("decl", s)
            elif cat == "ladder":
                for sec, entries in data.items():
                    for e in entries if isinstance(entries, list) else []:
                        for key in ("lean", "witness"):
                            for s in strings(e.get(key, [])) if isinstance(e, dict) else []:
                                if hubname(s, roots, modules):
                                    add("decl", s)
            elif cat == "atlas" and rel.endswith("hub.toml"):
                for p in data.get("paper", {}).values():
                    for s in p.get("headline", []):
                        add("decl", s)
            elif cat == "atlas" and os.path.basename(rel).startswith("edges-"):
                for d, where in data.get("decls", {}).items():
                    add("decl", d)
                    if isinstance(where, str) and ".lean" in where:
                        add("path", where)
                for ds in data.get("principals", {}).values():
                    for d in ds:
                        add("decl", d)
                for e in data.get("edges", []):
                    for d in e.get("witness", []):
                        add("decl", d)
            if cat == "atlas" and rel.endswith(".json"):
                continue                      # generated: the structured fields are the whole content
            seen = set(structured)
            text_names = [m.group(0) for m in TOKEN.finditer(text)]
            for m in BRACES.finditer(text):
                text_names += [m.group(1) + "." + x.strip() for x in m.group(2).split(",")]
            for tok in text_names:
                if FILE_EXT.search(tok) or not hubname(tok, roots, modules):
                    continue
                if ("decl", tok) not in seen:
                    seen.add(("decl", tok))
                    refs.append(Ref("decl", cat, rel, line_of(text, tok), tok, False))
            for m in PATH_TOKEN.finditer(text):
                p = m.group(1)
                first = p.split("/")[0]
                if first in roots or first in idx.pkg_bases or first == "scaffold" or \
                        first.endswith("Scaffold"):
                    if ("path", p) not in seen:
                        seen.add(("path", p))
                        refs.append(Ref("path", cat, rel, line_of(text, p), p, False))
    return refs


def resolve_ref(r, idx, mode):
    if r.kind == "path":
        return idx.resolve_path(r.name)
    if r.kind == "module":
        return "files" if r.name in idx.file_modules else None
    if r.kind == "toml":
        return None
    return idx.resolve(r.name, mode)


def run_check(hub, mode="auto"):
    mods = lean_modules(hub)
    idx = Index.build(hub, mods)
    if mode == "facts" and not idx.facts_files:
        raise SystemExit("rename check: --resolve facts, but no facts file in %s" % hub)
    refs = collect_refs(hub, idx, mods)
    res = [(r, resolve_ref(r, idx, mode)) for r in refs]
    return idx, res


def source_line(idx, mode):
    if mode == "grep" or not idx.facts_files:
        why = "" if mode == "grep" else " (no facts file in the tree)"
        return "resolution: a grep of the declarations in the .lean sources%s, module files from the tree" % why
    return ("resolution: the compiled facts (%s: %d declarations, %d modules), module files from the tree%s" %
            (", ".join(idx.facts_files), len(idx.facts_decls), len(idx.facts_modules),
             ", and a grep of the .lean sources for names the facts lack" if mode == "auto" else ""))


def report_check(hub, mode, show_all, out=None):
    out = out or sys.stdout
    idx, res = run_check(hub, mode)
    print("rename check: " + source_line(idx, mode), file=out)
    dangling = [(r, s) for r, s in res if s is None and r.structured]
    text = [(r, s) for r, s in res if s is None and not r.structured]
    for r, _ in dangling:
        print("dangling %s %s %s:%d %s" % (r.category, r.kind, r.file, r.line, r.name), file=out)
    for r, _ in (text if show_all else text[:20]):
        print("text-dangling %s %s %s:%d %s" % (r.category, r.kind, r.file, r.line, r.name), file=out)
    if len(text) > 20 and not show_all:
        print("  ... %d more text-dangling (--all lists them)" % (len(text) - 20), file=out)
    by = {}
    for _, s in res:
        by[s] = by.get(s, 0) + 1
    n_struct = sum(1 for r, _ in res if r.structured)
    print("rename check: %d references (%d structured, %d text); resolved by facts %d, files %d, grep %d; "
          "%d structured dangling, %d text dangling (warnings) -> %s" %
          (len(res), n_struct, len(res) - n_struct, by.get("facts", 0), by.get("files", 0), by.get("grep", 0),
           len(dangling), len(text), "FAIL" if dangling else "OK"), file=out)
    return 1 if dangling else 0


# ------------------------------------------------------------------ the plan
def make_plan(hub, rmap):
    mods = lean_modules(hub)
    idx = Index.build(hub, mods)
    old_modules = idx.modules()
    files = covered_files(hub, mods)
    plan = {"rewrites": {}, "moves": [], "manual": [], "warnings": [], "errors": [], "counts": {}}
    known_ns = idx.namespaces()
    for cat in CATEGORIES:
        nf = nr = 0
        for rel in files[cat]:
            text = read(hub, rel)
            new, n = rewrite_text(text, rmap, old_modules, lean=(cat == "lean"))
            if cat == "lean":
                for rule, ln, msg in lean_manual(lean_scan(text)[2], rmap, known_ns):
                    plan["manual"].append("%s %s:%d %s" % (rule, rel, ln, msg))
            if n:
                plan["rewrites"][rel] = (cat, new, n)
                nf, nr = nf + 1, nr + n
        plan["counts"][cat] = (nf, nr)
    # moves
    pkg_roots, dests, outside = {}, {}, {}
    for mod, (pkg, src, rel) in sorted(mods.items()):
        new = rmap.module(mod, True)
        if not new:
            continue
        dst = os.path.join(src, *new.split(".")) + ".lean" if src else os.path.join(*new.split(".")) + ".lean"
        plan["moves"].append((rel, dst, mod, new, pkg))
        if dst in dests:
            plan["errors"].append("collision: %s and %s both move to %s" % (dests[dst], rel, dst))
        dests[dst] = rel
        if pkg not in pkg_roots:
            pkg_roots[pkg] = lib_roots_of(hub, pkg)
        if not any(new == r or new.startswith(r + ".") for _, rs in pkg_roots[pkg] for r in rs):
            outside.setdefault(pkg, []).append(new)
    for pkg, news in sorted(outside.items()):
        plan["warnings"].append("lakefile %s: %d moved module(s) fall outside every lean_lib root (%s), e.g. %s; "
                                "the lakefile is not edited"
                                % (pkg, len(news), ", ".join(r for _, rs in pkg_roots[pkg] for r in rs), news[0]))
    moving = {m[0] for m in plan["moves"]}
    for rel, dst, *_ in plan["moves"]:
        if os.path.exists(os.path.join(hub, dst)) and dst not in moving:
            plan["errors"].append("collision: %s -> %s, which exists and is not moved" % (rel, dst))
    for new in set(rmap.module(m, True) for m in mods if rmap.module(m, True)) & (set(mods) - {m[2] for m in plan["moves"]}):
        plan["errors"].append("collision: module %s exists and is also a rename target" % new)
    # scaffold mirrors
    for key in rmap.mod:
        root, rest = key.split(".")[0], key.split(".")[1:]
        if root.endswith("Scaffold"):
            continue
        mirror = ".".join([root + "Scaffold"] + rest)
        if mirror not in rmap.mod and any(m == mirror or m.startswith(mirror + ".") for m in mods):
            plan["warnings"].append("scaffold-mirror: %s is renamed but its mirror %s has modules and no key"
                                    % (key, mirror))
    # lakefiles naming a key
    for pkg in ig.packages(hub)[0]:
        lake = read(hub, os.path.join(pkg, "lakefile.toml"))
        hits = [k for k in set(rmap.mod) | set(rmap.ns) if re.search(r'"%s(?:[."]|\b)' % re.escape(k), lake)]
        if hits:
            plan["warnings"].append("lakefile %s/lakefile.toml names %s; lakefiles are not edited" % (pkg, ", ".join(sorted(hits))))
    plan["residue"] = residue(hub, rmap, set(f for fs in files.values() for f in fs), old_modules)
    plan["prediction"] = predict(hub, rmap, idx, mods, plan)
    return plan


def tracked_files(hub):
    try:
        r = subprocess.run(["git", "-C", hub, "ls-files", "-z"], capture_output=True, text=True, check=True)
        if r.stdout:
            return [f for f in r.stdout.split("\0") if f]
    except (OSError, subprocess.CalledProcessError):
        pass
    out = []
    for dp, dns, fns in os.walk(hub):
        dns[:] = [d for d in dns if not d.startswith(".")]
        out += [os.path.relpath(os.path.join(dp, f), hub) for f in fns]
    return out


def residue(hub, rmap, covered, modules):
    """Files the tool does not rewrite that name an old prefix: {file: count}."""
    keys = sorted(set(rmap.mod) | set(rmap.ns), key=len, reverse=True)
    pat = re.compile(r"(?<![\w.'!?«/\\-])(?:%s)(?:\.%s)" % ("|".join(re.escape(k) for k in keys), COMP) +
                     "|" + "|".join(r"(?<![\w.'!?«/\\-])%s(?![\w'!?])" % re.escape(k) for k in keys if "." in k)
                     + ("|" + rmap.path_re().pattern if rmap.path_re() else ""))
    out = {}
    for rel in tracked_files(hub):
        if rel in covered or "/.lake/" in "/" + rel:
            continue
        p = os.path.join(hub, rel)
        try:
            if os.path.getsize(p) > 50_000_000:
                continue
            with open(p, encoding="utf-8") as f:
                text = f.read()
        except (OSError, UnicodeDecodeError):
            continue
        if not any(r in text for r in rmap.roots):
            continue
        n = len(pat.findall(text))
        if n:
            out[rel] = n
    return out


def predict(hub, rmap, idx, mods, plan):
    """References touched by the map: do they resolve before, and (against the mapped index) after?"""
    refs = collect_refs(hub, idx, mods)
    after = Index()
    mapn = lambda n: rmap.namespace(n, True) or rmap.module(n, True) or n
    after.facts_decls = {mapn(d) for d in idx.facts_decls}
    after.facts_modules = {rmap.module(m, True) or m for m in idx.facts_modules}
    after.grep_decls = {mapn(d) for d in idx.grep_decls}
    after.grep_ns = {mapn(n) for n in idx.grep_ns}
    after.file_modules = {rmap.module(m, True) or m for m in idx.file_modules}
    after.lean_files = {rmap.path(f) for f in idx.lean_files}
    after.pkg_bases = idx.pkg_bases
    after.facts_files = idx.facts_files
    old_modules = idx.modules()
    touched = before_ok = 0
    lost = []
    for r in refs:
        if r.kind == "path":
            new = rmap.path(r.name)
        elif r.kind == "module":
            new = rmap.module(r.name, True) or r.name
        else:
            new = rmap.name(r.name, old_modules, False) or r.name
        if new == r.name:
            continue
        touched += 1
        ok_before = resolve_ref(r, idx, "auto")
        if ok_before:
            before_ok += 1
            r2 = Ref(r.kind, r.category, r.file, r.line, new, r.structured)
            if not resolve_ref(r2, after, "auto"):
                lost.append((r, new))
    return {"touched": touched, "before_ok": before_ok, "lost": lost}


def print_plan(hub, rmap, plan, verbose, live, out=None):
    out = out or sys.stdout
    p = lambda s="": print(s, file=out)
    p("rename plan (dry run: nothing is written) -- target %s%s" % (hub, " (the live hub checkout)" if live else ""))
    p("map %s:" % rmap.source)
    for line in rmap.describe():
        p(line)
    nfiles = len(plan["rewrites"])
    nrep = sum(v[2] for v in plan["rewrites"].values())
    p("rewrites: %d files, %d replacements" % (nfiles, nrep))
    for cat in CATEGORIES:
        nf, nr = plan["counts"].get(cat, (0, 0))
        p("  %-9s %4d files %6d replacements" % (cat, nf, nr))
    items = sorted(plan["rewrites"].items(), key=lambda kv: -kv[1][2])
    for rel, (cat, _, n) in (items if verbose else items[:15]):
        p("    %5d  %s" % (n, rel))
    if len(items) > 15 and not verbose:
        p("    ... %d more files (--verbose lists them)" % (len(items) - 15))
    p("moves: %d module files" % len(plan["moves"]))
    for rel, dst, *_ in (plan["moves"] if verbose else plan["moves"][:15]):
        p("  %s -> %s" % (rel, dst))
    if len(plan["moves"]) > 15 and not verbose:
        p("  ... %d more moves (--verbose lists them)" % (len(plan["moves"]) - 15))
    p("manual (not rewritten; fix by hand, the build finds what is left): %d" % len(plan["manual"]))
    for m in plan["manual"] if verbose else plan["manual"][:20]:
        p("  " + m)
    for w in plan["warnings"]:
        p("warning " + w)
    for e in plan["errors"]:
        p("error " + e)
    res = plan["residue"]
    p("not covered, naming an old prefix: %d files, %d mentions" % (len(res), sum(res.values())))
    for rel, n in (sorted(res.items(), key=lambda kv: -kv[1]) if verbose else sorted(res.items(), key=lambda kv: -kv[1])[:15]):
        p("    %5d  %s" % (n, rel))
    pr = plan["prediction"]
    p("predicted resolution: %d references touched by the map, %d resolve today, %d would not resolve after"
      % (pr["touched"], pr["before_ok"], len(pr["lost"])))
    for r, new in pr["lost"]:
        p("  predicted-dangling %s %s:%d %s -> %s" % (r.category, r.file, r.line, r.name, new))
    bad = len(plan["errors"]) + len(pr["lost"])
    p("rename plan: %d files, %d replacements, %d moves, %d manual, %d warnings, %d errors, %d predicted dangling"
      % (nfiles, nrep, len(plan["moves"]), len(plan["manual"]), len(plan["warnings"]), len(plan["errors"]),
         len(pr["lost"])))
    return 1 if bad else 0


# ------------------------------------------------------------------ apply
def live_roots():
    out = {os.path.realpath(ROOT)}
    for p in (os.environ.get("LEANARTICLES_HUB"), "~/Dropbox/LeanArticles", "~/LeanArticles"):
        if p and os.path.exists(os.path.expanduser(p)):
            out.add(os.path.realpath(os.path.expanduser(p)))
    return out


def refusal(target):
    t = os.path.realpath(target)
    for live in sorted(live_roots()):
        if t == live:
            return "%s is the hub checkout" % target
        if t.startswith(live + os.sep):
            return "%s is inside the hub checkout %s" % (target, live)
        if live.startswith(t + os.sep):
            return "%s contains the hub checkout %s" % (target, live)
    return None


def do_apply(target, rmap, out=None):
    out = out or sys.stdout
    why = refusal(target)
    if why:
        print("rename apply: REFUSED: %s. Run it on a scratch copy (cp -r, without .lake), never on the live tree."
              % why, file=out)
        return 2
    if not os.path.isdir(target):
        print("rename apply: REFUSED: %s is not a directory" % target, file=out)
        return 2
    plan = make_plan(target, rmap)
    if plan["errors"]:
        for e in plan["errors"]:
            print("error " + e, file=out)
        print("rename apply: REFUSED: %d error(s) in the plan; nothing written" % len(plan["errors"]), file=out)
        return 2
    # the baseline: what resolves today, by the grep of the sources (and files)
    idx0, res0 = run_check(target, "grep")
    old_modules = idx0.modules()

    def mapped(r):
        if r.kind == "path":
            return rmap.path(r.name)
        if r.kind == "module":
            return rmap.module(r.name, True) or r.name
        return rmap.name(r.name, old_modules, False) or r.name

    baseline = {(r.kind, mapped(r)) for r, s in res0 if s}
    for rel, (_cat, new, _n) in plan["rewrites"].items():
        with open(os.path.join(target, rel), "w", encoding="utf-8") as f:
            f.write(new)
    tmp = []
    for i, (rel, dst, *_rest) in enumerate(plan["moves"]):
        t = os.path.join(target, rel + ".rename-%d.tmp" % i)
        os.rename(os.path.join(target, rel), t)
        tmp.append((t, os.path.join(target, dst), os.path.dirname(os.path.join(target, rel))))
    for t, dst, srcdir in tmp:
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        os.rename(t, dst)
    for _t, _dst, srcdir in tmp:
        d = srcdir
        while d.startswith(target) and os.path.isdir(d) and not os.listdir(d):
            os.rmdir(d)
            d = os.path.dirname(d)
    print("rename apply: %s: %d files rewritten (%d replacements), %d modules moved, %d manual items"
          % (target, len(plan["rewrites"]), sum(v[2] for v in plan["rewrites"].values()), len(plan["moves"]),
             len(plan["manual"])), file=out)
    for m in plan["manual"]:
        print("manual " + m, file=out)
    _idx1, res1 = run_check(target, "grep")
    regressions = [r for r, s in res1 if not s and (r.kind, r.name) in baseline]
    for r in regressions:
        print("regression %s %s %s:%d %s (resolved before the rename, not after, by the grep of the rewritten sources)"
              % (r.category, r.kind, r.file, r.line, r.name), file=out)
    rc = report_check(target, "auto", False, out)
    print("rename apply: %d regression(s)%s" % (len(regressions), " -> FAIL" if regressions else ""), file=out)
    return 1 if regressions else rc


# ------------------------------------------------------------------ main
def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] not in ("plan", "apply", "check", "-h", "--help"):
        argv.insert(0, "plan")
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    pl = sub.add_parser("plan", help="dry run (the default): print what apply would do")
    pl.add_argument("map")
    pl.add_argument("--target", default=ROOT)
    pl.add_argument("--verbose", "-v", action="store_true")
    ap_ = sub.add_parser("apply", help="rewrite and move, in a scratch copy only")
    ap_.add_argument("map")
    ap_.add_argument("--target", required=True)
    ch = sub.add_parser("check", help="does every referenced name resolve?")
    ch.add_argument("--target", default=ROOT)
    ch.add_argument("--resolve", choices=("auto", "facts", "grep"), default="auto")
    ch.add_argument("--all", action="store_true")
    a = ap.parse_args(argv)
    if a.cmd == "check":
        return report_check(os.path.abspath(a.target), a.resolve, a.all)
    try:
        rmap = RenameMap.load(a.map)
    except (OSError, ValueError, tomllib.TOMLDecodeError) as e:
        print("rename %s: bad map %s: %s" % (a.cmd, a.map, e))
        return 2
    if a.cmd == "plan":
        target = os.path.abspath(a.target)
        return print_plan(target, rmap, make_plan(target, rmap), a.verbose, refusal(target) is not None)
    return do_apply(os.path.abspath(a.target), rmap)


if __name__ == "__main__":
    sys.exit(main())
