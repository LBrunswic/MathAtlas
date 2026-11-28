# Part (e) of T-abs-sc-open-hoist: move Causality.IsCauchySurfaceOn.mem_Jplus_union_Jminus out of
# Causal/FlrwTypeClosedAmbient.lean into Causal/CurvesExtendSecondCountable.lean, after
# exists_inextensible_of_t1_secondCountable, in a section carrying the variables it used
# ({C : Causality M} {W : Opens M}, after {M : Type u} [TopologicalSpace M]: same binder order).
# The proof moves byte for byte; the docstring's twin sentence is replaced (the twins are now
# proved from it). Asserts every edit. Run once: python3 -I move_e.py
import pathlib
R = pathlib.Path("/home/maxbrain/Dropbox/LeanArticles/lean-causal/Causal")
fp = R / "FlrwTypeClosedAmbient.lean"
src = fp.read_text(encoding="utf-8")
a = src.index("/-- **A Cauchy surface splits its open set**, on a T1, second countable space")
b = src.index("/-! ### The closing step -/", a)
block = src[a:b]
assert block.count("theorem IsCauchySurfaceOn.mem_Jplus_union_Jminus ") == 1 and block.endswith("\n\n")
twin = ("(`exists_inextensible_of_t1_secondCountable`, the constant curve extended), and it meets `S`. The\n"
        "twin of `splitBy_of_t1_secondCountable` (`Causal/ErsSecondCountable.lean:158`), which lies outside\n"
        "`Causal.FlrwType`'s import closure. -/\n")
assert block.count(twin) == 1
new_twin = ("(`exists_inextensible_of_t1_secondCountable`, the constant curve extended), and it meets `S`.\n"
            "`splitBy_of_t1_secondCountable` (`Causal.ErsSecondCountable`) is this statement, and\n"
            "`IsCauchySurface.cover_of_t1_secondCountable` (`Causal.CauchySeparation`) its case `W = ⊤`:\n"
            "both are proved from it. Moved here from `Causal.FlrwTypeClosedAmbient` by T-abs-sc-open-hoist.\n"
            "-/\n")
moved = block.replace(twin, new_twin, 1)
hdr_old = "/-! ### Two general lemmas -/\n"
assert src.count(hdr_old) == 1
new_src = src[:a] + src[b:]
new_src = new_src.replace(hdr_old, "/-! ### A general lemma -/\n", 1)
fp.write_text(new_src, encoding="utf-8")

ce = R / "CurvesExtendSecondCountable.lean"
s = ce.read_text(encoding="utf-8")
anchor = "  rw [hf.2.2]\n  exact hρc t ht\n\n"
assert s.count(anchor) == 1
i = s.index(anchor) + len(anchor)
assert s[i:].startswith("/-- **The target**: `CurvesExtendOn W`")
ins = ("section CauchySplit\n\nvariable {C : Causality M} {W : Opens M}\n\n" + moved + "end CauchySplit\n\n")
s = s[:i] + ins + s[i:]
ce.write_text(s, encoding="utf-8")
print("ok", len(block))
