import Causal.GluingGeneric.Generated

/-!
# Gluing in its hereditary form, generic constructions (6): local gluing and `(G,X)`-structures

No label of `ETT.tex` is marked by this file (target `T-abs-gluing-generic`, DEC-167 step 1a).
Cited, unmarked: `theo:causalite_engendre` — `ETT.tex:514`, `prop:GX_espace_temps_topo` —
`ETT.tex:589`.

> Let $(G,X)$ be an analytic structure and let $(M,\A)$ be a $(G,X)$-manifold. If $X$ is a
> causally arc-connected Baire topological spacetime on which $G$ acts by morphisms of topological
> spacetimes, then $M$ admits a unique topological spacetime structure such that for every chart
> $(\U,\V,\phi)\in\A$ the map $\phi:\U\rightarrow \V$ is an isomorphism of topological spacetimes.
> (`ETT.tex:589–593`)

DEC-167 says the uniqueness of `prop:GX_espace_temps_topo` holds as printed under gluing. The
library proves existence of an absolutely minimal causality and uniqueness among absolutely minimal
ones (`existsUnique_causality_GX_maximal`). This file adds that the causality is hereditarily
minimal, so that the statement holds under either form of the gluing field.

## What is proved (no `sorry` in this file)

* `existsUnique_absolutelyMinimalOn_all_of_agree_locally`: the hereditary strengthening of the
  library's `existsUnique_absolutelyMinimal_of_agree_locally` (`theo:causalite_engendre` with (B)
  asked locally): the glued causality is absolutely minimal on every open set, and unique among the
  (merely) absolutely minimal ones.
* `existsUnique_causality_GX_absolutelyMinimalOn_all`: `prop:GX_espace_temps_topo` over the maximal
  atlas with a hereditarily minimal causality, unique among the absolutely minimal ones; so the
  uniqueness holds among hereditarily minimal causalities too (the first reading of OQ-95) and
  among absolutely minimal ones (the second).
* The general principle behind it is the library's `Causal.absolutelyMinimalOn_of_locally`
  (`Causal.GXStructure`): **M-only + hereditary on the members of an open cover ⇒ hereditary**.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `X` causally arc-connected | ✓ carried |
| `X` Baire, `M` second countable Hausdorff | ⚠ weakened: not used (as in the library) |
| `G` acts by morphisms | ✓ carried (DEC-12): strong morphisms |

## SCOPE (disclosed)

* `prop:GX_espace_temps_topo` is not marked here: the library's anchor is
  `Causal.GXStructure`, whose ledger row the master curates. This file only adds the hereditary
  conclusion for the field switch.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

universe u v w

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]

section Gluing

variable {ι : Type w} {U : ι → Opens M} {C : ι → Causality M}

/-- `theo:causalite_engendre` with (B) asked locally, **hereditary form**: causalities absolutely
minimal on every open subset of their domain and agreeing near every point of the overlaps glue to
a causality absolutely minimal on every open set, the only absolutely minimal one restricting to
them. -/
theorem existsUnique_absolutelyMinimalOn_all_of_agree_locally (hU : ∀ x : M, ∃ i, x ∈ U i)
    (hA : ∀ i, ∀ W : Opens M, W ≤ U i → (C i).AbsolutelyMinimalOn W)
    (hB : ∀ i j, ∀ x ∈ U i ⊓ U j, ∃ O : Opens M, x ∈ O ∧ AgreeOn (C i) (C j) O) :
    ∃ C₀ : Causality M, (∀ i, AgreeOn C₀ (C i) (U i)) ∧
      (∀ W : Opens M, C₀.AbsolutelyMinimalOn W) ∧
      ∀ C' : Causality M, (∀ i, AgreeOn C' (C i) (U i)) → C'.AbsolutelyMinimal → C' = C₀ := by
  obtain ⟨C₀, hC₀, -, huniq⟩ := existsUnique_absolutelyMinimal_of_agree_locally hU hA hB
  have hcompat := compatible_of_agree_locally hA hB
  have hgen : ∀ i, AgreeOn (Causality.generated U hU C) (C i) (U i) := fun i V hV x y =>
    ⟨Precausality.generated_le_iff (hU := hU) hcompat hV,
      Precausality.generated_lt_iff (hU := hU) hcompat hV⟩
  have hgenmin := Causality.generated_absolutelyMinimalOn_all hU hA
  have heq : Causality.generated U hU C = C₀ :=
    huniq _ hgen (Precausality.absolutelyMinimal_iff.2 (hgenmin ⊤))
  refine ⟨C₀, hC₀, ?_, huniq⟩
  rw [← heq]
  exact hgenmin

end Gluing

section GX

variable {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X] [ChartedSpace X M]
  [HasGroupoid M (gxGroupoid G X)]

/-- **`prop:GX_espace_temps_topo` over the maximal atlas, hereditary form.** The causality of a
`(G,X)`-manifold modelled on a causally arc-connected `X` is absolutely minimal on every open set,
and it is the only absolutely minimal causality for which every chart is an isomorphism. -/
theorem existsUnique_causality_GX_absolutelyMinimalOn_all (D : Causality X)
    (hD : D.CausallyArcConnected) (hG : ∀ g : G, StrongMorphism D D fun p => g • p) :
    ∃ C : Causality M, (∀ e ∈ (gxGroupoid G X).maximalAtlas M, ChartIso C D e) ∧
      (∀ W : Opens M, C.AbsolutelyMinimalOn W) ∧
      ∀ C' : Causality M, (∀ e ∈ (gxGroupoid G X).maximalAtlas M, ChartIso C' D e) →
        C'.AbsolutelyMinimal → C' = C := by
  obtain ⟨C, hC, hmin, huniq⟩ := existsUnique_causality_GX_maximal (M := M) D hD hG
  refine ⟨C, hC, absolutelyMinimalOn_of_locally hmin fun x => ⟨chartSource (chartAt X x),
    mem_chart_source X x, fun W hW => (hC _ ((gxGroupoid G X).subset_maximalAtlas
      (chart_mem_atlas X x))).absolutelyMinimalOn hW (hD.absolutelyMinimalOn_all _)⟩, huniq⟩

end GX

end Causal
