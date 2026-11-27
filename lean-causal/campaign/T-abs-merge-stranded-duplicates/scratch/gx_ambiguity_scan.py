"""Textual scan: at a future bump of lean-gx's Causal pin, could a declaration newly imported
through `Causal.CBG.Ppcm -> Causal.CauchySeparation` change how a lean-gx identifier resolves?
Flags (a) a token that would resolve to a new declaration through an enclosing namespace
(Lean's namespace resolution wins over `open`), (b) a token that would resolve to a new
declaration through an `open` while it also resolves to an existing lean-causal/lean-gx one
(an ambiguity), (c) a `.foo` field token whose name is the last component of a new
declaration in a type namespace (generalised field notation). Heuristic; read-only."""
import sys, glob, os, re
sys.path.insert(0, "tools")
import ladder

idx = ladder.lean_index()
imps_after = {k: list(v) for k, v in idx["imports"].items()}
imps_before = {k: [x for x in v if not (k == "Causal.CBG.Ppcm" and x == "Causal.CauchySeparation")
                   and not (k == "Causal.LemmaK" and x == "Causal.LadderLocal")] for k, v in imps_after.items()}

def closure(ms, imps):
    seen, st = set(ms), list(ms)
    while st:
        x = st.pop()
        for n in imps.get(x, []):
            if n not in seen: seen.add(n); st.append(n)
    return seen

# lean-gx modules: imports (all), source
gx = {}
for f in glob.glob("lean-gx/GX/**/*.lean", recursive=True) + glob.glob("lean-gx/scaffold/**/*.lean", recursive=True):
    if "/.lake/" in f: continue
    rel = os.path.relpath(f, "lean-gx")
    if rel.startswith("scaffold/"): rel = rel[len("scaffold/"):]
    mod = rel[:-5].replace(os.sep, ".")
    src = open(f, encoding="utf-8").read()
    head = src.split("/-!")[0]
    gx[mod] = (f, re.findall(r"^import\s+(\S+)", head, re.M), src)

def causal_closure(mod, imps, memo):
    if mod in memo: return memo[mod]
    memo[mod] = set()
    f, ims, _ = gx[mod]
    out = set()
    for m in ims:
        if m.startswith("Causal."): out |= closure([m], imps)
        elif m in gx: out |= causal_closure(m, imps, memo)
    memo[mod] = out
    return out

mb, ma = {}, {}
affected = {}
for mod in gx:
    gain = causal_closure(mod, imps_after, ma) - causal_closure(mod, imps_before, mb)
    if gain: affected[mod] = gain
print("affected lean-gx modules:", len(affected))
new_mods = set().union(*affected.values()) if affected else set()
new_decls = {n for n, m in idx["decls"].items() if m in new_mods}
print("new modules:", sorted(new_mods), "new decls:", len(new_decls))

gxdecls = set()
for k in ("GX", "scaffold"):
    src = __import__("inspect").getsource(ladder._lean_index).replace('"Causal", "**"', '"%s", "**"' % k).replace("def _lean_index", "def _x")
    ns = dict(vars(ladder)); exec(src, ns)
    gxdecls |= set(ns["_x"]("lean-gx")["decls"])

def strip_comments(s):
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    s = re.sub(r"--[^\n]*", " ", s)
    return s

TOK = re.compile(r"(?<![\w.'])(@?[A-Za-z_Ͱ-Ͽ][\w'₀-₉Ͱ-Ͽ!?]*(?:\.[A-Za-z_Ͱ-Ͽ][\w'₀-₉Ͱ-Ͽ!?]*)*)")
FIELD = re.compile(r"(?<=[\w)\]])\.([A-Za-z_][\w']*)")
new_last = {}
for n in new_decls:
    parts = n.split(".")
    if len(parts) >= 2 and parts[-2][:1].isupper() and parts[-2] not in ("Causal", "Causality"):
        new_last.setdefault(parts[-1], set()).add(n)
flags = []
for mod in sorted(affected):
    f, _, src = gx[mod]
    code = strip_comments(src)
    nss, opens = [], set()
    for m in re.finditer(r"^\s*namespace\s+(\S+)", code, re.M):
        nss.append(m.group(1))
    for m in re.finditer(r"^\s*open\s+([^\n]+)", code, re.M):
        for w in m.group(1).split():
            if w in ("in", "hiding", "renaming", "scoped") or w.startswith("(") or w.startswith("["): continue
            opens.add(w)
    # cumulative enclosing namespaces (approximate: all prefixes of every namespace opened in the file)
    prefixes = set()
    acc = []
    for n in nss:
        acc_n = n.split(".")
        for i in range(1, len(acc_n) + 1): prefixes.add(".".join(acc_n[:i]))
    if any(n.startswith("Causal") for n in nss): pass
    toks = set(t.lstrip("@") for t in TOK.findall(code))
    exist = (set(idx["decls"]) - new_decls) | gxdecls
    opens_full = set(opens) | {p + "." + o for p in prefixes for o in opens}
    for t in toks:
        via_ns = [p + "." + t for p in prefixes if p + "." + t in new_decls]
        via_open = [o + "." + t for o in opens_full if o + "." + t in new_decls] + ([t] if t in new_decls else [])
        if via_ns:
            flags.append((mod, "namespace", t, via_ns))
        elif via_open:
            others = [p + "." + t for p in prefixes | opens_full if p + "." + t in exist] + ([t] if t in exist else [])
            if others: flags.append((mod, "open-ambiguity", t, via_open + ["vs"] + others))
    for fld in set(FIELD.findall(code)):
        if fld in new_last:
            flags.append((mod, "field", "." + fld, sorted(new_last[fld])))
print("flags:", len(flags))
for x in flags: print("  ", x)
