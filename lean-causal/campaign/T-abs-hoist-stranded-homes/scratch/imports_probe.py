"""Import-index probe for T-abs-hoist-stranded-homes (run from the hub root, read-only).

For every module this target edits: its model path (layer rule), whether it reaches
Causal.Ladder.Rules (kb/0221), whether it sits in Rules' closure or in
Causal.CurvesExtendSecondCountable's closure, and whether its source mentions causal_ladder.
For every citation the target introduces (citer module -> module defining the cited lemma), the
citer must already import the home, directly or transitively, so no import is added. The import
graph is checked for a cycle as it stands."""
import os
import sys

HUB = "/home/maxbrain/Dropbox/LeanArticles"
sys.path.insert(0, os.path.join(HUB, "tools"))
os.chdir(HUB)
import ladder  # noqa: E402

idx = ladder.lean_index()
imports = {k: list(v) for k, v in idx["imports"].items()}
R = ladder.RULES_MODULE
CES = "Causal.CurvesExtendSecondCountable"


def closure(m, imps):
    seen, st = set(), [m]
    while st:
        x = st.pop()
        for n in imps.get(x, []):
            if n not in seen:
                seen.add(n)
                st.append(n)
    return seen


def has_cycle(imps):
    sys.setrecursionlimit(100000)
    col = {}

    def dfs(u, path):
        col[u] = 1
        for v in imps.get(u, []):
            c = col.get(v, 0)
            if c == 1:
                return path + [u, v]
            if c == 0:
                r = dfs(v, path + [u])
                if r:
                    return r
        col[u] = 2
        return None

    for u in list(imps):
        if col.get(u, 0) == 0:
            r = dfs(u, [])
            if r:
                return r
    return None


EDITED = ["Causal.GXStructure", "Causal.TimelikeHomotopy", "Causal.Remarks.MassiveManifold",
          "Causal.Flat.CauchyComplete", "Causal.ChronalNeighbourBridge",
          "Causal.CausallyPlainLocZ", "Causal.Model.E0ChronalNeighbour"]
rc, cc = closure(R, imports), closure(CES, imports)
print("Rules closure:", len(rc), "modules; CurvesExtendSecondCountable closure:", len(cc))
for m in EDITED:
    f = os.path.join("lean-causal", *m.split(".")) + ".lean"
    src = open(f, encoding="utf-8").read()
    print("==", m)
    print("   imports:", imports.get(m))
    print("   model path:", ladder.model_path(m, imports))
    print("   reaches Rules:", ladder.import_chain(m, imports, R))
    print("   in Rules closure:", m in rc, "; in CurvesExtendSecondCountable closure:", m in cc)
    print("   mentions causal_ladder:", "causal_ladder" in ladder._code(src))

# citer -> home of the cited lemma (after the hoist)
CITES = [
    ("Causal.TimelikeHomotopy", "Causal.GXStructure"),
    ("Causal.Remarks.MassiveManifold", "Causal.GXStructure"),
    ("Causal.Flat.CauchyComplete", "Causal.GXStructure"),
    ("Causal.Port.SFALine", "Causal.GXStructure"),
    ("Causal.Port.SFAMassiveLine", "Causal.GXStructure"),
    ("Causal.Model.E0ChronalNeighbour", "Causal.ChronalNeighbourBridge"),
    ("Causal.Model.E0ChronalNeighbour", "Causal.CausallyPlainLocZ"),
]
for a, b in CITES:
    print("cite", a, "->", b, ": imported via", ladder.import_chain(a, imports, b))
print("cycle in the import graph:", has_cycle(imports))
