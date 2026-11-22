import Causal.GluingModels.Tools
import Causal.PushoutCausal
import Causal.CBG.FamilyGluing

/-!
# Gluing inventory (DEC-167), ETT layer: the gluing of two spacetimes glues

No paper label is certified by this file. **A local copy of a generic construction** of the
sibling target `T-abs-gluing-generic` ("the family gluing and pushout"), proved here because the
inventory needs it for one concrete object, the branching line (`Causal.CBG.Geometry`,
`branchingCausality`, model layer): the master merges duplicates at graduation.

* `hereditary_of_reads`: on an open `N ⊆ e(X)`, `e` continuous, a causality reading on the open
  subsets of `N` the relations of `D` pulled back along `e` glues hereditarily on `N` when `D`
  does.
* `Gluing.causality_minimal`, `Gluing.causality_hereditary`: the causality of the gluing of two
  spacetimes (`Causal.PushoutCausal`, `defi:ppcm`'s topological counterpart) glues on `M` when
  both pieces do, and hereditarily when both pieces do hereditarily and agree along the common
  open set (`Gluing.CompatibleAlong`).

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff | ⚠ weakened: not used (the branching line is not Hausdorff) |

## SCOPE (disclosed)

* No definition changes; OQ-95 and OQ-96 are not decided here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace GluingModels

open Set TopologicalSpace Topology Relation

/-- **Gluing passes to a causality reading pulled-back relations.** If on every open `V ≤ N`
the relations of `C` between points `e x`, `e y` are those of `D` on `e⁻¹ V`, and `N ⊆ e(X)`,
then `C` glues on every open subset of `N` when `D` glues hereditarily. -/
theorem hereditary_of_reads {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X]
    {C : Causality Z} {D : Causality X} {e : X → Z} (he : Continuous e) {N : Opens Z}
    (hN : (N : Set Z) ⊆ range e)
    (hrel : ∀ V : Opens Z, V ≤ N → ∀ x y : X,
      (C.le V (e x) (e y) ↔ D.le (preimageOpens he V) x y) ∧
        (C.lt V (e x) (e y) ↔ D.lt (preimageOpens he V) x y))
    (hD : ∀ W : Opens X, D.AbsolutelyMinimalOn W) :
    ∀ W : Opens Z, W ≤ N → C.AbsolutelyMinimalOn W := by
  intro W hW S hS V hV a b
  have hVN : V ≤ N := hV.trans hW
  let S' : Set (Opens X) := (preimageOpens he) '' S
  have hS' : ∀ x ∈ preimageOpens he W, ∃ O' ∈ S', x ∈ O' := fun x hx => by
    obtain ⟨O, hO, hxO⟩ := hS (e x) hx
    exact ⟨_, ⟨O, hO, rfl⟩, hxO⟩
  have hpre : preimageOpens he V ≤ preimageOpens he W := fun x hx => hV hx
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · obtain ⟨x, rfl⟩ := hN (hVN (C.le_mem_left hab))
    obtain ⟨y, rfl⟩ := hN (hVN (C.le_mem_right hab))
    have hc := ((hD _) S' hS' _ hpre x y).1 ((hrel V hVN x y).1.1 hab)
    refine TransGen.lift e (fun c d hcd => ?_) hc
    obtain ⟨_, ⟨O, hO, rfl⟩, hcd⟩ := hcd
    exact ⟨O, hO, (hrel (V ⊓ O) (inf_le_left.trans hVN) c d).1.2 hcd⟩
  · obtain ⟨x, rfl⟩ := hN (hVN (C.lt_mem_left hab))
    obtain ⟨y, rfl⟩ := hN (hVN (C.lt_mem_right hab))
    have hc := ((hD _) S' hS' _ hpre x y).2 ((hrel V hVN x y).2.1 hab)
    refine TransGen.lift e (fun c d hcd => ?_) hc
    obtain ⟨_, ⟨O, hO, rfl⟩, hcd⟩ := hcd
    exact ⟨O, hO, (hrel (V ⊓ O) (inf_le_left.trans hVN) c d).2.2 hcd⟩

namespace Gluing

open Causal.Gluing

variable {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
  {j₁ : W → X} {j₂ : W → Y} {hj₁ : IsOpenEmbedding j₁} {hj₂ : IsOpenEmbedding j₂}
  {C₁ : Causality X} {C₂ : Causality Y}

/-- **The causality of a gluing glues on `M`** when both pieces do (`lem:precausalite_engendre_minimale`
through `Causality.absolutelyMinimalOn_pushLocal_extend`). -/
theorem causality_minimal (h₁ : C₁.AbsolutelyMinimal) (h₂ : C₂.AbsolutelyMinimal) :
    (causality hj₁ hj₂ C₁ C₂).AbsolutelyMinimal := by
  refine Causality.generated_absolutelyMinimal _ fun b => ?_
  cases b
  · exact Causality.absolutelyMinimalOn_pushLocal_extend C₂ (isOpenEmbedding_ι₂ hj₁ hj₂) h₂
  · exact Causality.absolutelyMinimalOn_pushLocal_extend C₁ (isOpenEmbedding_ι₁ hj₁ hj₂) h₁

/-- **The causality of a gluing glues hereditarily** when both pieces do and agree along the
common open set. -/
theorem causality_hereditary (hC : CompatibleAlong j₁ j₂ C₁ C₂)
    (h₁ : ∀ W : Opens X, C₁.AbsolutelyMinimalOn W) (h₂ : ∀ W : Opens Y, C₂.AbsolutelyMinimalOn W) :
    ∀ V : Opens (Gluing j₁ j₂), (causality hj₁ hj₂ C₁ C₂).AbsolutelyMinimalOn V := by
  refine absolutelyMinimalOn_of_locally
    (causality_minimal (absolutelyMinimal_of_forall h₁) (absolutelyMinimal_of_forall h₂))
    fun z => ?_
  obtain ⟨b, hb⟩ := mem_cover hj₁ hj₂ z
  cases b
  · exact ⟨O₂ hj₁ hj₂, hb, hereditary_of_reads continuous_ι₂ le_rfl
      (isGluingCausality_causality hC).2 h₂⟩
  · exact ⟨O₁ hj₁ hj₂, hb, hereditary_of_reads continuous_ι₁ le_rfl
      (isGluingCausality_causality hC).1 h₁⟩

end Gluing

end GluingModels

end Causal
