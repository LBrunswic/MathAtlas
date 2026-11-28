import CausalScaffold.ErsEtaleMghd

/-! Probe of T-abs-ers-etale-mghd: the type and the axioms of every declaration of
`CausalScaffold.ErsEtaleMghd`, and three checks by the kernel. (1) The glued causality is
`Causal.Gluing.causality` of the two subtype pieces, by `rfl`. (2) The subtype piece and the
pullback along `Subtype.val` agree (`Causal.Causality.pullback_val_agree`), so the choice of
`toSubtype` loses nothing. (3) The development form composes with the topological half: under
`ers_etale_development`'s hypotheses, `π` injective gives `u₁ = u₂` on all of `U₁ ∩ U₂`. The probe
is not a copy of the module; it imports it. -/

#check @Causal.Causality.isEMorphism_restrict_toSubtype_val
#check @Causal.Causality.isCauchySurfaceOn_iff_restrict_toSubtype
#check @Causal.Causality.causallyConvexIn_and_le_iff_of_agreeOn
#check @Causal.Causality.isPreconnected_inter_of_isCauchySurfaceOn_sup
#check @Causal.EtaleGluing.sheet₁
#check @Causal.EtaleGluing.sheet₂
#check @Causal.EtaleGluing.gluedCausality
#check @Causal.EtaleGluing.lift
#check @Causal.EtaleGluing.ι₁_mem_sheet₂_iff
#check @Causal.EtaleGluing.ι₂_mem_sheet₁_iff
#check @Causal.EtaleGluing.lift_eq_image_ι₂
#check @Causal.EtaleGluing.proj_image_lift
#check @Causal.EtaleGluing.compatibleAlong_iff_agreeOn
#check @Causal.EtaleGluing.gluedCausality_le_sheet₁_iff
#check @Causal.EtaleGluing.gluedCausality_le_sheet₂_iff
#check @Causal.EtaleGluing.twoPiece
#check @Causal.EtaleGluing.isCausal_gluedCausality
#check @Causal.EtaleGluing.isEtaleDevelopment
#check @Causal.EtaleGluing.eqOn_inter_of_injective_proj
#check @Causal.EtaleGluing.isOpenEmbedding_proj_of_isCauchySurfaceOn_inf
#check @Causal.CausalityFollowsLt
#check @Causal.CausalityFollows.agreeOn
#check @Causal.ers_etale_development
#check @Causal.ers_theorem_3_45_etale
#check @Causal.ers_corollary_4_68_etale
#check @Causal.componentOpens_inf_subset_left
#check @Causal.componentOpens_inf_subset_right
#check @Causal.ers_etale_development_component
#check @Causal.ers_isPreconnected_inter_of_eqOn
#check @Causal.ers_isOpenEmbedding_proj_of_eqOn
#check @Causal.EtaleGluing.lineU₁
#check @Causal.EtaleGluing.lineU₂
#check @Causal.EtaleGluing.lineA
#check @Causal.EtaleGluing.lineA_subset₁
#check @Causal.EtaleGluing.lineA_subset₂
#check @Causal.EtaleGluing.lineP₁
#check @Causal.EtaleGluing.lineP₂
#check @Causal.EtaleGluing.timelikeLine_etale_witness
#check @Causal.EtaleGluing.timelikeLine_isEtaleDevelopment
#check @Causal.EtaleGluing.timelikeLine_ers_etale_witness

open Causal Causal.EtaleGluing in
example {M : Type*} [TopologicalSpace M] {U₁ U₂ A : TopologicalSpace.Opens M}
    (h₁ : (A : Set M) ⊆ U₁) (h₂ : (A : Set M) ⊆ U₂) (C₁ C₂ : Causality M) :
    gluedCausality h₁ h₂ C₁ C₂ =
      Gluing.causality (isOpenEmbedding_inclusion h₁ A.isOpen)
        (isOpenEmbedding_inclusion h₂ A.isOpen) ((C₁.restrict U₁).toSubtype)
        ((C₂.restrict U₂).toSubtype) := rfl

open Causal in
example {M : Type*} [TopologicalSpace M] (C : Causality M) (W : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens W) (x y : W) :
    (C.pullback continuous_subtype_val).le V x y ↔ ((C.restrict W).toSubtype).le V x y :=
  (C.pullback_val_agree W V x y).1

open Causal Causal.EtaleGluing in
example {M : Type*} [TopologicalSpace M] {β : Type*} {U₁ U₂ A : TopologicalSpace.Opens M}
    {u₁ u₂ : M → β} (h₁ : (A : Set M) ⊆ U₁) (h₂ : (A : Set M) ⊆ U₂) (hu : Set.EqOn u₁ u₂ A)
    (hinj : Function.Injective (proj h₁ h₂)) : Set.EqOn u₁ u₂ ((U₁ : Set M) ∩ U₂) :=
  eqOn_inter_of_injective_proj hu hinj

#print axioms Causal.Causality.isEMorphism_restrict_toSubtype_val
#print axioms Causal.Causality.isCauchySurfaceOn_iff_restrict_toSubtype
#print axioms Causal.Causality.causallyConvexIn_and_le_iff_of_agreeOn
#print axioms Causal.Causality.isPreconnected_inter_of_isCauchySurfaceOn_sup
#print axioms Causal.EtaleGluing.sheet₁
#print axioms Causal.EtaleGluing.sheet₂
#print axioms Causal.EtaleGluing.gluedCausality
#print axioms Causal.EtaleGluing.lift
#print axioms Causal.EtaleGluing.ι₁_mem_sheet₂_iff
#print axioms Causal.EtaleGluing.ι₂_mem_sheet₁_iff
#print axioms Causal.EtaleGluing.lift_eq_image_ι₂
#print axioms Causal.EtaleGluing.proj_image_lift
#print axioms Causal.EtaleGluing.compatibleAlong_iff_agreeOn
#print axioms Causal.EtaleGluing.gluedCausality_le_sheet₁_iff
#print axioms Causal.EtaleGluing.gluedCausality_le_sheet₂_iff
#print axioms Causal.EtaleGluing.twoPiece
#print axioms Causal.EtaleGluing.isCausal_gluedCausality
#print axioms Causal.EtaleGluing.isEtaleDevelopment
#print axioms Causal.EtaleGluing.eqOn_inter_of_injective_proj
#print axioms Causal.EtaleGluing.isOpenEmbedding_proj_of_isCauchySurfaceOn_inf
#print axioms Causal.CausalityFollowsLt
#print axioms Causal.CausalityFollows.agreeOn
#print axioms Causal.ers_etale_development
#print axioms Causal.ers_theorem_3_45_etale
#print axioms Causal.ers_corollary_4_68_etale
#print axioms Causal.componentOpens_inf_subset_left
#print axioms Causal.componentOpens_inf_subset_right
#print axioms Causal.ers_etale_development_component
#print axioms Causal.ers_isPreconnected_inter_of_eqOn
#print axioms Causal.ers_isOpenEmbedding_proj_of_eqOn
#print axioms Causal.EtaleGluing.lineU₁
#print axioms Causal.EtaleGluing.lineU₂
#print axioms Causal.EtaleGluing.lineA
#print axioms Causal.EtaleGluing.lineA_subset₁
#print axioms Causal.EtaleGluing.lineA_subset₂
#print axioms Causal.EtaleGluing.lineP₁
#print axioms Causal.EtaleGluing.lineP₂
#print axioms Causal.EtaleGluing.timelikeLine_etale_witness
#print axioms Causal.EtaleGluing.timelikeLine_isEtaleDevelopment
#print axioms Causal.EtaleGluing.timelikeLine_ers_etale_witness
