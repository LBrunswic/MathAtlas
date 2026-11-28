# Part (d) of T-abs-sc-open-hoist: move IsEMorphismOn.pastInextensible_invComp and
# IsSpacetimeExtension.isEMorphismOn out of Causal/FlrwType.lean, byte for byte, same full names.
# pastInextensible_invComp goes to Causal/CauchyExtension.lean in a block after its `end Causal`
# that reopens FlrwType's scope (binder order M, [TopologicalSpace M], N, ...; kb/0255), since
# CauchyExtension's own scope orders M, N, [TopologicalSpace M], [TopologicalSpace N].
# isEMorphismOn goes into C0ExtensionSkeleton's namespace IsSpacetimeExtension, whose variables are
# FlrwType's in the same order. Asserts every edit. Run once: python3 -I move_d.py
import pathlib
R = pathlib.Path("/home/maxbrain/Dropbox/LeanArticles/lean-causal/Causal")
fp = R / "FlrwType.lean"
src = fp.read_text(encoding="utf-8")

# pastInextensible_invComp: docstring to the end of its proof
a = src.index("/-- **Past-inextensibility is pulled back** along a morphism injective on `W`")
b = src.index("end IsEMorphismOn\n", a)
block_pi = src[a:b]
assert block_pi.count("theorem pastInextensible_invComp ") == 1 and block_pi.endswith("\n\n")
# the whole namespace IsEMorphismOn of FlrwType holds only this lemma
ns_open = ("namespace IsEMorphismOn\n\nvariable {N : Type v} [TopologicalSpace N] {C : Causality M} "
           "{D : Causality N} {W : Opens M}\n  {φ : M → N}\n\n")
assert src[a - len(ns_open):a] == ns_open
ns_close = "end IsEMorphismOn\n\n"
assert src[b:b + len(ns_close)] == ns_close

# isEMorphismOn: docstring to the end of its proof
c = src.index("/-- **An extension is an abstract `𝕄≥0`-morphism** on `N`")
d = src.index("/-- **Cauchy surfaces are pushed forward**", c)
block_em = src[c:d]
assert block_em.count("theorem isEMorphismOn ") == 1 and block_em.endswith("\n\n")
ext_open = ("namespace IsSpacetimeExtension\n\nvariable {N : Type v} [TopologicalSpace N] [Nonempty N] "
            "{CN : Causality N} {C : Causality M}\n  {ι : N → M}\n\n")
assert src[c - len(ext_open):c] == ext_open

new = src[:a - len(ns_open)] + src[b + len(ns_close):c] + src[d:]
assert new.count("pastInextensible_invComp") == src.count("pastInextensible_invComp") - 1
fp.write_text(new, encoding="utf-8")

# CauchyExtension: append a block reopening FlrwType's scope
ce = R / "CauchyExtension.lean"
s = ce.read_text(encoding="utf-8")
assert s.endswith("\nend Causal\n")
tail = ("\n/-! ### Past-inextensibility pulled back\n\n"
        "Moved here from `Causal.FlrwType` by T-abs-sc-open-hoist, byte for byte under the same full\n"
        "name. The block reopens the scope it was proved in: there `M` and its topology come before `N`\n"
        "(`universe u v`, `variable {M : Type u} [TopologicalSpace M]`), and this module's own `variable`\n"
        "line orders `M`, `N`, then their topologies, which would reorder the binders of the statement\n"
        "(kb/0255). -/\n\n"
        "namespace Causal\n\n"
        "open Set Function TopologicalSpace Topology Filter\n\n"
        "universe u v\n\n"
        "variable {M : Type u} [TopologicalSpace M]\n\n"
        "open Causality\n\n"
        + ns_open + block_pi + "end IsEMorphismOn\n\nend Causal\n")
s = s + tail
ce.write_text(s, encoding="utf-8")

# C0ExtensionSkeleton: after `dual`, inside namespace IsSpacetimeExtension
sk = R / "C0ExtensionSkeleton.lean"
t = sk.read_text(encoding="utf-8")
anchor = ("    fun U hU x hx y hy => ⟨(hι.chartIso U hU y hy x hx).1, (hι.chartIso U hU y hy x hx).2⟩⟩\n\n")
assert t.count(anchor) == 1
t = t.replace(anchor, anchor + block_em, 1)
sk.write_text(t, encoding="utf-8")
print("ok", len(block_pi), len(block_em))
