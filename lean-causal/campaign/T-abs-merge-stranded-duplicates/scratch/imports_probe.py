"""Import-index probe for T-abs-merge-stranded-duplicates (run from the hub root).
For each proposed new import `A -> B`: is B (transitively) importing A (a cycle)? Does B reach a
model module (layer rule)? Does B reach Causal.Ladder.Rules (kb/0221)? Does A sit in Rules'
closure (so B would enter it)? Optional extra edges simulate the new imports."""
import sys, json
sys.path.insert(0, "tools")
import ladder

idx = ladder.lean_index()
imports = {k: list(v) for k, v in idx["imports"].items()}
R = ladder.RULES_MODULE

def closure(m, imps):
    seen, st = set(), [m]
    while st:
        x = st.pop()
        for n in imps.get(x, []):
            if n not in seen:
                seen.add(n); st.append(n)
    return seen

PROPOSED = [
    ("Causal.LemmaK", "Causal.LadderLocal"),
    ("Causal.CBG.Ppcm", "Causal.CauchySeparation"),
]
for a, b in PROPOSED:
    print("==", a, "->", b)
    print("  already imports (transitively):", b in closure(a, imports))
    print("  cycle (b reaches a):", ladder.import_chain(b, imports, a))
    print("  b model path:", ladder.model_path(b, imports))
    print("  a model path:", ladder.model_path(a, imports))
    print("  b reaches Rules:", ladder.import_chain(b, imports, R))
    print("  a reaches Rules:", ladder.import_chain(a, imports, R))
    rc = closure(R, imports)
    print("  a in Rules closure:", a in rc, "; b in Rules closure:", b in rc)

# simulate all proposed edges together
sim = {k: list(v) for k, v in imports.items()}
for a, b in PROPOSED:
    sim[a].append(b)
# cycle check over the whole graph
def has_cycle(imps):
    WHITE, GREY, BLACK = 0, 1, 2
    col = {}
    sys.setrecursionlimit(100000)
    def dfs(u, path):
        col[u] = GREY
        for v in imps.get(u, []):
            c = col.get(v, WHITE)
            if c == GREY:
                return path + [u, v]
            if c == WHITE:
                r = dfs(v, path + [u])
                if r: return r
        col[u] = BLACK
        return None
    for u in list(imps):
        if col.get(u, WHITE) == WHITE:
            r = dfs(u, [])
            if r: return r
    return None
print("cycle after simulated edges:", has_cycle(sim))
print("Rules closure size before/after:", len(closure(R, imports)), len(closure(R, sim)))
new = closure(R, sim) - closure(R, imports)
print("new modules in Rules closure:", sorted(new))
# do any modules in the new Rules closure use causal_ladder?
import os, re
for m in sorted(closure(R, sim)):
    f = os.path.join("lean-causal", *m.split(".")) + ".lean"
    if os.path.exists(f):
        src = open(f, encoding="utf-8").read()
        if "causal_ladder" in src and m != R and not m.startswith("Causal.Ladder."):
            print("  causal_ladder mentioned in Rules-closure module:", m)
for m in ["Causal.Cauchy", "Causal.LadderLocal", "Causal.LemmaK", "Causal.CauchySeparation"]:
    print("model path of", m, ladder.model_path(m, sim))
# downstream counts
def rev_closure(m, imps):
    rev = {}
    for k, v in imps.items():
        for n in v: rev.setdefault(n, []).append(k)
    return closure(m, rev)
for m in ["Causal.Cauchy", "Causal.LadderLocal", "Causal.LemmaK", "Causal.CauchySeparation", "Causal.CBG.Ppcm", "Causal.Ers475CauchyForm", "Causal.Flat.CBG", "Causal.Flat.CBGSlice"]:
    print("downstream of", m, len(rev_closure(m, imports)))
