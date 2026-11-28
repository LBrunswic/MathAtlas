# Byte-for-byte check of T-abs-sc-open-hoist's moves: each moved block of HEAD's source (docstring
# through proof) must occur verbatim in its new home, after the one stated substitution (the name's
# namespace prefix, now the enclosing namespace; the split's twin sentence). Writes nothing.
# Run: python3 -I verbatim_check.py   (needs /tmp/T-abs-sc-open-hoist/headsrc from git archive HEAD)
import pathlib
OLD = pathlib.Path("/tmp/T-abs-sc-open-hoist/headsrc/lean-causal/Causal")
NEW = pathlib.Path("/home/maxbrain/Dropbox/LeanArticles/lean-causal/Causal")

def block(text, start, end):
    a = text.index(start); b = text.index(end, a)
    return text[a:b]

ok = True
def check(label, old_file, start, end, new_file, subs=()):
    global ok
    old = (OLD / old_file).read_text(encoding="utf-8")
    new = (NEW / new_file).read_text(encoding="utf-8")
    blk = block(old, start, end)
    for x, y in subs:
        assert blk.count(x) == 1, (label, x)
        blk = blk.replace(x, y, 1)
    here = new.count(blk)
    gone = (NEW / old_file).read_text(encoding="utf-8").count(blk) if old_file != new_file else None
    print(f"{label}: {len(blk)} bytes, verbatim in {new_file}: {here == 1}; left in {old_file}: {gone}")
    ok &= here == 1 and not gone

check("(a) hull, open form, counterexample shape", "SCOpenWithoutTarentin.lean",
      "/-! ### The causal hull `J⁺_M(A) ∩ J⁻_M(A)` -/", "end Causality", "StrongCausalityHull.lean")
check("(a) witnesses stay", "SCOpenWithoutTarentin.lean", "/-! ### Witnesses -/", "end Causal\n",
      "SCOpenWithoutTarentin.lean")
check("(b) chronalCurveOn_comp", "Model/FlatSpaceCylinder.lean", "/-- **Push-forward of a chronal curve**",
      "/-- **A chronal homotopy is", "CauchyExtension.lean",
      [("theorem IsEMorphismOn.chronalCurveOn_comp ", "theorem chronalCurveOn_comp ")])
check("(b) homotopicRel", "Model/FlatSpaceCylinder.lean", "/-- **A chronal homotopy is a homotopy",
      "namespace Flat", "TimelikeHomotopy.lean",
      [("theorem Causality.ChronalHomotopyOn.homotopicRel ", "theorem homotopicRel ")])
check("(d) pastInextensible_invComp (with FlrwType's variable line)", "FlrwType.lean",
      "namespace IsEMorphismOn\n", "end IsEMorphismOn\n", "CauchyExtension.lean")
check("(d) isEMorphismOn", "FlrwType.lean", "/-- **An extension is an abstract `𝕄≥0`-morphism**",
      "/-- **Cauchy surfaces are pushed forward**", "C0ExtensionSkeleton.lean")
TWIN_OLD = (" The\ntwin of `splitBy_of_t1_secondCountable` (`Causal/ErsSecondCountable.lean:158`), which lies outside\n"
            "`Causal.FlrwType`'s import closure. -/\n")
TWIN_NEW = ("\n`splitBy_of_t1_secondCountable` (`Causal.ErsSecondCountable`) is this statement, and\n"
            "`IsCauchySurface.cover_of_t1_secondCountable` (`Causal.CauchySeparation`) its case `W = ⊤`:\n"
            "both are proved from it. Moved here from `Causal.FlrwTypeClosedAmbient` by T-abs-sc-open-hoist.\n"
            "-/\n")
check("(e) mem_Jplus_union_Jminus (docstring's twin sentence replaced)", "FlrwTypeClosedAmbient.lean",
      "/-- **A Cauchy surface splits its open set**", "/-! ### The closing step -/",
      "CurvesExtendSecondCountable.lean", [(TWIN_OLD, TWIN_NEW)])
# the proof alone, with no substitution
check("(e) mem_Jplus_union_Jminus, statement and proof", "FlrwTypeClosedAmbient.lean",
      "theorem IsCauchySurfaceOn.mem_Jplus_union_Jminus", "/-! ### The closing step -/",
      "CurvesExtendSecondCountable.lean")
print("ALL VERBATIM:", ok)
