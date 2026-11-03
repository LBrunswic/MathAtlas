import GXScaffold.BTZ.Rigid
import GXScaffold.BTZ.Causality

/-!
# WP-41c: the discharge of `E0TASegLt` for the model causality (not a scaffold module)

Checked with `taskset -c 0-11 lake env lean campaign/WP-41c/TypeAgreementD.lean`. It cannot live
in `GXScaffold.BTZ.Rigid`: `GXScaffold.BTZ.Causality` (WP-41e round 2) imports Rigid. For the
assembly (WP-41f's `GXScaffold.BTZ.LocalModel`, or Causality itself), it gives
`E0TypeAgreementTendsto E0.causalityYBTZ`: the convergence form of `typeAgreement`. Rigid's
`GX.e0_typeAgreementTendsto_of` reduces it to the two segment hypotheses proved here. Also:
`GX.e0_typeAgreement_inl_D` (the field verbatim at the tips in `𝕄`) and **`GX.e0_not_typeAgreement_D`
(the field is false for the model causality, DEC-27)**, from Rigid's `GX.e0_not_typeAgreement_of`
and the diamond lemma `GX.e0TAD_diam` proved here.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

attribute [local instance] btzE0Structure

theorem e0TAD_toPaper_btzDevInv {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv v)) = E0.unlift v := by
  have h := E0.toPaper_posEmb hv (-(v.2.2 / v.2.1)) ((v.1 + v.2.1 - v.2.2 ^ 2 / v.2.1) / 2)
  have e1 : btzDevInv v = (DInfty.posEmb ⟨(v.2.1, -(-(v.2.2 / v.2.1))), hv⟩,
      2 * ((v.1 + v.2.1 - v.2.2 ^ 2 / v.2.1) / 2)) := by
    rw [btzDevInv, dif_pos hv, neg_neg]
    congr 1; ring
  rw [e1, h]
  simp only [E0.unlift]
  refine Prod.ext ?_ rfl
  ring

theorem e0TAD_segLt_inl : E0TASegLt E0.causalityYBTZ e0TAInl univ := by
  intro O V hVo hVc _ hVO v hv w hw h
  show (Causal.minkowski 2).lt (E0.leftOpens (E0.opensImage E0.toPaperY O))
    (nullToMink v) (nullToMink w)
  set V' : Opens (Causal.Minkowski 2) := ⟨nullToMink '' V, by
    rw [← coe_nullToMinkHomeomorph]; exact nullToMinkHomeomorph.isOpenMap V hVo⟩
  have hV'c : Convex ℝ (V' : Set (Causal.Minkowski 2)) :=
    hVc.linear_image nullToMink.toLinearMap
  have hle : V' ≤ E0.leftOpens (E0.opensImage E0.toPaperY O) := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨Sum.inl (nullToMink u), hVO u hu, rfl⟩
  exact (Causal.minkowski 2).lt_mono hle ((Causal.Flat.lt_iff_of_convex hV'c).2
    ⟨⟨v, hv, rfl⟩, ⟨w, hw, rfl⟩, h⟩)

theorem e0TAD_segLt_inr : E0TASegLt E0.causalityYBTZ e0TAInr {v | 0 < v.2.1} := by
  intro O V _ hVc hVb hVO v hv w hw h
  have hVb' : ∀ u ∈ V, 0 < u.2.1 := fun u hu => hVb hu
  show E0.CLt (E0.rightOpens (E0.opensImage E0.toPaperY O))
    (E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv v)))
    (E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv w)))
  rw [e0TAD_toPaper_btzDevInv (hVb' v hv), e0TAD_toPaper_btzDevInv (hVb' w hw)]
  have hv' := E0.lift_unlift (Or.inl (hVb' v hv))
  have hw' := E0.lift_unlift (Or.inl (hVb' w hw))
  refine E0.clt_of_seg (E0.polar_unlift (hVb' v hv).le) (E0.polar_unlift (hVb' w hw).le)
    (by rw [hv', hw']; exact (E0.minkowski_lt_nullToMink v w).1 h) fun s hs => ?_
  rw [hv', hw']
  have hm : E0.seg v w s ∈ V := hVc.add_smul_sub_mem hv hw hs
  refine ⟨e0TAInr (E0.seg v w s), hVO _ hm, ?_⟩
  show Sum.inr (E0.toPaper _) = Sum.inr _
  rw [e0TAD_toPaper_btzDevInv (hVb' _ hm)]

/-- **`typeAgreement`, convergence form, for `𝕄 ⊕ 𝔼₀` with the model causality.** -/
theorem e0_typeAgreementTendsto_D : E0TypeAgreementTendsto E0.causalityYBTZ :=
  e0_typeAgreementTendsto_of _ e0TAD_segLt_inl e0TAD_segLt_inr

/-- **`typeAgreement` verbatim at the tips in `𝕄`, for the model causality.** -/
theorem e0_typeAgreement_inl_D : E0TypeAgreementInl E0.causalityYBTZ :=
  e0_typeAgreement_inl_of E0.causalityYBTZ e0TAD_segLt_inl

/-- **The diamond of the counterexample, for the model causality**: a point chronologically below
the tip `y₀ = [D⁻¹(0,1,0)]` in `O = [D⁻¹ B(v₀, 1/5)]` is `[D⁻¹ w]` with `w` in the past cone of
`v₀` (`E0.Lt.of_polar`: the developments at nearby angles are chronologically related). -/
theorem e0TAD_diam : ∀ x : E0Y, E0.causalityYBTZ.lt e0CEO x e0CEy → x ∈ e0TAInr '' e0CEA := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := E0.causalityYBTZ.lt_mem_left hx
  have hb := e0CE_ball_b hw
  have hb₀ : (0 : ℝ) < e0CEv.2.1 := by simp [e0CEv]
  have h1 : E0.CLt (E0.rightOpens (E0.opensImage E0.toPaperY e0CEO))
      (E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv w)))
      (E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv e0CEv))) := hx
  rw [e0TAD_toPaper_btzDevInv hb, e0TAD_toPaper_btzDevInv hb₀] at h1
  have h2 := h1.lt
  have hθ : |-(e0CEv.2.2 / e0CEv.2.1) - -(w.2.2 / w.2.1)| ≤ π := by
    obtain ⟨-, hb', hc'⟩ := e0CE_abs_lt_of_dist hw
    simp only [e0CEv, sub_zero] at hb' hc' ⊢
    rw [abs_lt] at hb'
    have hw4 : 4 / 5 < w.2.1 := by linarith
    have : |w.2.2 / w.2.1| ≤ 1 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < w.2.1), div_le_one (by linarith)]
      linarith
    have hπ := Real.pi_gt_three
    simp only [zero_div, neg_zero, zero_sub, abs_neg]
    linarith
  have h3 := E0.Lt.of_polar h2 (E0.polar_unlift hb.le) (E0.polar_unlift hb₀.le) hθ
  rw [E0.lift_unlift (Or.inl hb), E0.lift_unlift (Or.inl hb₀)] at h3
  exact ⟨w, ⟨hw, h3⟩, rfl⟩

/-- **`typeAgreement` is false for the model causality** (DEC-27 counterexample). -/
theorem e0_not_typeAgreement_D : ¬ E0TypeAgreement E0.causalityYBTZ :=
  e0_not_typeAgreement_of _ e0TAD_segLt_inr e0TAD_diam

end GX

#print axioms GX.e0_typeAgreementTendsto_D
#print axioms GX.e0_typeAgreement_inl_D
#print axioms GX.e0_typeAgreementTendsto_of
#print axioms GX.e0_typeAgreement_inl_of
#print axioms GX.e0_not_typeAgreement_D
