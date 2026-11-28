import CausalScaffold.ErsEtaleGluing
import Causal.Ers482Solution

/-! Probe of T-abs-ers-etale-gluing: the type and the axioms of every declaration of
`CausalScaffold.ErsEtaleGluing`, and one check by the kernel: the planner's optional form of
(4), the factor of `glue_eq_ite_comp_proj` is `Causal.glueSolutions ⟨U₁, hU₁⟩ u₁ u₂`
(`Causal.Ers482Solution`), definitionally. The probe imports `Causal.Ers482Solution` for that
check only; the module does not. -/

#check @Causal.EtaleGluing
#check @Causal.EtaleGluing.proj
#check @Causal.EtaleGluing.glue
#check @Causal.EtaleGluing.proj_ι₁
#check @Causal.EtaleGluing.proj_ι₂
#check @Causal.EtaleGluing.proj_comp_ι₁
#check @Causal.EtaleGluing.proj_comp_ι₂
#check @Causal.EtaleGluing.range_proj
#check @Causal.EtaleGluing.ι₁_eq_ι₂_iff
#check @Causal.EtaleGluing.isOpenEmbedding_inclusion
#check @Causal.EtaleGluing.continuous_proj
#check @Causal.EtaleGluing.isLocalHomeomorph_proj
#check @Causal.EtaleGluing.isLocalHomeomorph_codRestrict_proj
#check @Causal.EtaleGluing.secondCountableTopology
#check @Causal.EtaleGluing.eq_of_proj_eq
#check @Causal.EtaleGluing.injective_proj_iff
#check @Causal.EtaleGluing.ι₁_ne_ι₂
#check @Causal.EtaleGluing.preimage_proj_singleton_of_mem_inter
#check @Causal.EtaleGluing.encard_preimage_proj_singleton_of_notMem
#check @Causal.EtaleGluing.preimage_proj_singleton_of_mem
#check @Causal.EtaleGluing.preimage_proj_singleton_of_notMem_union
#check @Causal.EtaleGluing.preimage_proj_eq_union
#check @Causal.EtaleGluing.disjoint_image_ι₁_image_ι₂
#check @Causal.EtaleGluing.isOpenEmbedding_proj
#check @Causal.EtaleGluing.exists_homeomorph
#check @Causal.EtaleGluing.isCorrespondingBoundaryPair_of_mem
#check @Causal.EtaleGluing.subset_of_t2Space
#check @Causal.EtaleGluing.isCorrespondingBoundaryPair_iff
#check @Causal.EtaleGluing.t2Space_iff
#check @Causal.EtaleGluing.t2Space_iff_isClosed
#check @Causal.EtaleGluing.t2Space_iff_eq_connectedComponentIn
#check @Causal.EtaleGluing.t2Space_connectedComponentIn
#check @Causal.EtaleGluing.eq_inter_of_t2Space
#check @Causal.EtaleGluing.glue_ι₁
#check @Causal.EtaleGluing.glue_ι₂
#check @Causal.EtaleGluing.glue_comp_ι₁
#check @Causal.EtaleGluing.glue_comp_ι₂
#check @Causal.EtaleGluing.continuous_glue
#check @Causal.EtaleGluing.glue_eq_ite_comp_proj
#check @Causal.EtaleGluing.exists_glue_eq_comp_proj_iff
#check @Causal.EtaleGluing.not_injective_and_not_descends
#check @Causal.EtaleGluing.not_isPreconnected_inter
#check @Causal.EtaleGluing.Ioi_subset_compl_zero
#check @Causal.EtaleGluing.Punctured
#check @Causal.EtaleGluing.eqOn_zero_indicator
#check @Causal.EtaleGluing.punctured_witness
#check @Causal.EtaleGluing.punctured_not_isPreconnected
#check @Causal.EtaleGluing.Branching
#check @Causal.EtaleGluing.branching_witness

open Causal Causal.EtaleGluing in
/-- (4) with `Causal.glueSolutions`: when `u₁ = u₂` on `U₁ ∩ U₂`,
`ũ = glueSolutions U₁ u₁ u₂ ∘ π`. -/
example {M : Type*} [TopologicalSpace M] {U₁ U₂ A : Set M} (hU₁ : IsOpen U₁) (h₁ : A ⊆ U₁)
    (h₂ : A ⊆ U₂) {β : Type*} {u₁ u₂ : M → β} (hu : Set.EqOn u₁ u₂ A)
    (h : Set.EqOn u₁ u₂ (U₁ ∩ U₂)) :
    glue h₁ h₂ u₁ u₂ hu = glueSolutions ⟨U₁, hU₁⟩ u₁ u₂ ∘ proj h₁ h₂ :=
  glue_eq_ite_comp_proj h

#print axioms Causal.EtaleGluing
#print axioms Causal.EtaleGluing.proj
#print axioms Causal.EtaleGluing.glue
#print axioms Causal.EtaleGluing.proj_ι₁
#print axioms Causal.EtaleGluing.proj_ι₂
#print axioms Causal.EtaleGluing.proj_comp_ι₁
#print axioms Causal.EtaleGluing.proj_comp_ι₂
#print axioms Causal.EtaleGluing.range_proj
#print axioms Causal.EtaleGluing.ι₁_eq_ι₂_iff
#print axioms Causal.EtaleGluing.isOpenEmbedding_inclusion
#print axioms Causal.EtaleGluing.continuous_proj
#print axioms Causal.EtaleGluing.isLocalHomeomorph_proj
#print axioms Causal.EtaleGluing.isLocalHomeomorph_codRestrict_proj
#print axioms Causal.EtaleGluing.secondCountableTopology
#print axioms Causal.EtaleGluing.eq_of_proj_eq
#print axioms Causal.EtaleGluing.injective_proj_iff
#print axioms Causal.EtaleGluing.ι₁_ne_ι₂
#print axioms Causal.EtaleGluing.preimage_proj_singleton_of_mem_inter
#print axioms Causal.EtaleGluing.encard_preimage_proj_singleton_of_notMem
#print axioms Causal.EtaleGluing.preimage_proj_singleton_of_mem
#print axioms Causal.EtaleGluing.preimage_proj_singleton_of_notMem_union
#print axioms Causal.EtaleGluing.preimage_proj_eq_union
#print axioms Causal.EtaleGluing.disjoint_image_ι₁_image_ι₂
#print axioms Causal.EtaleGluing.isOpenEmbedding_proj
#print axioms Causal.EtaleGluing.exists_homeomorph
#print axioms Causal.EtaleGluing.isCorrespondingBoundaryPair_of_mem
#print axioms Causal.EtaleGluing.subset_of_t2Space
#print axioms Causal.EtaleGluing.isCorrespondingBoundaryPair_iff
#print axioms Causal.EtaleGluing.t2Space_iff
#print axioms Causal.EtaleGluing.t2Space_iff_isClosed
#print axioms Causal.EtaleGluing.t2Space_iff_eq_connectedComponentIn
#print axioms Causal.EtaleGluing.t2Space_connectedComponentIn
#print axioms Causal.EtaleGluing.eq_inter_of_t2Space
#print axioms Causal.EtaleGluing.glue_ι₁
#print axioms Causal.EtaleGluing.glue_ι₂
#print axioms Causal.EtaleGluing.glue_comp_ι₁
#print axioms Causal.EtaleGluing.glue_comp_ι₂
#print axioms Causal.EtaleGluing.continuous_glue
#print axioms Causal.EtaleGluing.glue_eq_ite_comp_proj
#print axioms Causal.EtaleGluing.exists_glue_eq_comp_proj_iff
#print axioms Causal.EtaleGluing.not_injective_and_not_descends
#print axioms Causal.EtaleGluing.not_isPreconnected_inter
#print axioms Causal.EtaleGluing.Ioi_subset_compl_zero
#print axioms Causal.EtaleGluing.Punctured
#print axioms Causal.EtaleGluing.eqOn_zero_indicator
#print axioms Causal.EtaleGluing.punctured_witness
#print axioms Causal.EtaleGluing.punctured_not_isPreconnected
#print axioms Causal.EtaleGluing.Branching
#print axioms Causal.EtaleGluing.branching_witness
