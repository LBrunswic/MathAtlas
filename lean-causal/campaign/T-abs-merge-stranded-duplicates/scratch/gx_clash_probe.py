"""Would the new imports bring into lean-gx (at a future pin bump) a declaration whose full name
lean-gx also declares? Text index of lean-gx built with tools/ladder.py's own scanner."""
import sys, inspect, re
sys.path.insert(0, "tools")
import ladder

idx = ladder.lean_index()
imports = idx["imports"]

def closure(m):
    seen, st = {m}, [m]
    while st:
        x = st.pop()
        for n in imports.get(x, []):
            if n not in seen:
                seen.add(n); st.append(n)
    return seen

src = inspect.getsource(ladder._lean_index).replace('"Causal", "**"', '"GX", "**"').replace("def _lean_index", "def _gx_index")
src2 = src.replace('"GX", "**"', '"scaffold", "**"').replace("def _gx_index", "def _gxs_index")
ns = dict(vars(ladder))
exec(src, ns); exec(src2, ns)
gx = ns["_gx_index"]("lean-gx")
gxs = ns["_gxs_index"]("lean-gx")
gxdecls = dict(gx["decls"]); gxdecls.update(gxs["decls"])
print("lean-gx decls indexed:", len(gxdecls))

for a, b in [("Causal.CBG.Ppcm", "Causal.CauchySeparation"), ("Causal.LemmaK", "Causal.LadderLocal")]:
    saved = list(imports[a])
    imports[a] = [x for x in saved if x != b]      # the tree before the new edge
    before = closure(a)
    imports[a] = saved
    new_mods = closure(b) - before
    new_decls = {n: m for n, m in idx["decls"].items() if m in new_mods}
    print("==", a, "+", b, ": new modules", len(new_mods), "new decls", len(new_decls))
    clash = sorted(n for n in new_decls if n in gxdecls)
    print("  full-name clashes with lean-gx:", clash)
    # which lean-gx modules import a (transitively, across the package boundary)?
    gximps = {}
    gximps.update(gx["imports"]); gximps.update(gxs["imports"])
    # collect lean-gx module headers importing Causal.* directly
    users = []
    import glob, os
    for f in glob.glob("lean-gx/**/*.lean", recursive=True):
        if "/.lake/" in f: continue
        head = open(f, encoding="utf-8").read().split("/-!")[0]
        for m in re.findall(r"^import\s+(Causal\.\S+)", head, re.M):
            if a in closure(m):
                users.append((f, m))
    print("  lean-gx files whose Causal imports reach", a, ":", len(users))
    # same-name clash within lean-causal downstream of a: declarations downstream of a that share a full name with new decls
    rev = {}
    for k, v in imports.items():
        for n in v: rev.setdefault(n, []).append(k)
    down, st = {a}, [a]
    while st:
        x = st.pop()
        for n in rev.get(x, []):
            if n not in down: down.add(n); st.append(n)
    dd = {n for n, m in idx["decls"].items() if m in down}
    print("  full-name clashes within lean-causal downstream:", sorted(set(new_decls) & dd))
