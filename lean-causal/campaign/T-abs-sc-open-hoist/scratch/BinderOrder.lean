import Causal.CauchyExtension

/-! Why `IsEMorphismOn.pastInextensible_invComp` sits in a last block of `Causal.CauchyExtension`:
the same text elaborated under that module's own `variable` line (`{M} {N} [TopM] [TopN]`) gives a
different statement (binder order) from the one first proved in `Causal.FlrwType`
(`{M} [TopM] {N} [TopN]`). Run: `lake env lean campaign/T-abs-sc-open-hoist/scratch/BinderOrder.lean`. -/

namespace Causal

open Set Function TopologicalSpace Topology Filter

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
variable {C : Causality M} {D : Causality N} {W : Opens M} {φ : M → N}

namespace IsEMorphismOn

theorem pastInextensible_invComp_inside (h : IsEMorphismOn C D W φ) (hinj : InjOn φ W) {g : N → M}
    (hg : LeftInvOn g φ W) {V : Opens M} (hVW : V ≤ W) {U : Opens N}
    (hU : (U : Set N) = φ '' V) {I : Set ℝ} {e : ℝ → N} (he : D.PastInextensible U I e) :
    C.PastInextensible V I (g ∘ e) := h.pastInextensible_invComp hinj hg hVW hU he

end IsEMorphismOn

end Causal

open Lean in
#eval show CoreM Unit from do
  let a ← getConstInfo ``Causal.IsEMorphismOn.pastInextensible_invComp
  let b ← getConstInfo ``Causal.IsEMorphismOn.pastInextensible_invComp_inside
  IO.println s!"same type: {a.type == b.type}; levels {a.levelParams} / {b.levelParams}"
  IO.println s!"hoisted: {← Meta.MetaM.run' (Meta.ppExpr a.type)}"
  IO.println s!"inside : {← Meta.MetaM.run' (Meta.ppExpr b.type)}"
