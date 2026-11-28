# Import checks for T-abs-sc-open-hoist (reads sources only; writes nothing).
# For each module that received or lost a declaration: model_path (None = ETT layer) and
# import_chain to Causal.Ladder.Rules (None = no cycle risk for Rules importing it), with HEAD's
# index beside the working tree's. Then Rules' import closure as emitted today and with
# Causal.SCOpenWithoutTarentin replaced by Causal.StrongCausalityHull (what emit-lean will write).
# Run: python3 -I imports_probe.py [HEAD_SRC_ROOT]
import sys
sys.path.insert(0, "/home/maxbrain/Dropbox/LeanArticles/tools")
import ladder
ROOT = "/home/maxbrain/Dropbox/LeanArticles/lean-causal"
idx = ladder._lean_index(ROOT)
imp = idx["imports"]
mods = ["Causal.StrongCausalityHull", "Causal.SCOpenWithoutTarentin", "Causal.CauchyExtension",
        "Causal.TimelikeHomotopy", "Causal.C0ExtensionSkeleton", "Causal.CurvesExtendSecondCountable",
        "Causal.ErsSecondCountable", "Causal.CauchySeparation", "Causal.FlrwType",
        "Causal.FlrwTypeClosedAmbient", "Causal.Model.FlatSpaceCylinder",
        "Causal.ChronalNeighbourBridge", "Causal.CurvesExtend"]
for m in mods:
    print(m, "imports", imp.get(m))
    print("   model_path", ladder.model_path(m, imp))
    print("   chain to Rules", ladder.import_chain(m, imp, ladder.RULES_MODULE))

def closure(roots, imp):
    seen, st = set(), list(roots)
    while st:
        m = st.pop()
        if m in seen: continue
        seen.add(m); st.extend(imp.get(m, []))
    return seen

rules = imp[ladder.RULES_MODULE]
now = closure([ladder.RULES_MODULE], imp)
alt = dict(imp)
alt[ladder.RULES_MODULE] = [("Causal.StrongCausalityHull" if x == "Causal.SCOpenWithoutTarentin" else x) for x in rules]
after = closure([ladder.RULES_MODULE], alt)
print("Rules closure (Causal modules) today:", len(now), " after the switch:", len(after))
print("leave the closure:", sorted(now - after))
print("enter the closure:", sorted(after - now))
print("model in closure after:", sorted(m for m in after if ladder.is_model(m)))
# causal_ladder users in Rules' closure (kb/0221)
import re, os
users = []
for m in sorted(after):
    f = os.path.join(ROOT, *m.split(".")) + ".lean"
    if os.path.exists(f) and re.search(r"\bcausal_ladder\b", ladder._code(open(f, encoding="utf-8").read())):
        users.append(m)
print("modules of the new closure whose code mentions causal_ladder:", users)
# the decl index: where each moved name now lives
for n in ["Causal.Causality.StronglyCausal.stronglyCausalOpen_of_causallyOpen",
          "Causal.Causality.StronglyCausal.exists_not_isOpen_hull",
          "Causal.IsEMorphismOn.chronalCurveOn_comp",
          "Causal.Causality.ChronalHomotopyOn.homotopicRel",
          "Causal.IsEMorphismOn.pastInextensible_invComp",
          "Causal.IsSpacetimeExtension.isEMorphismOn",
          "Causal.Causality.IsCauchySurfaceOn.mem_Jplus_union_Jminus",
          "Causal.oneWayMembrane_hull_not_isOpen"]:
    print(n, "->", idx["decls"].get(n))
