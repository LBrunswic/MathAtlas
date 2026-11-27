import Causal.PlainnessModels.LipschitzModel
import Causal.Subdivision
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Push-up and causal plainness at a locally Lipschitz Lorentzian metric

Target `T-ett-plainness-models` (DEC-168: « keep plainness; prove it for … Lipschitz metrics »,
layer 3). No label is marked here; the consumer is `Causal.PlainnessModels.Lorentzian`
(`cor:K_lorentzien`).

> Local Lipschitz continuity of the metric is the threshold below which causal theory
> degenerates: light cones cease to be hypersurfaces and \emph{bubble up}
> (`rem:pas_plat` (i), `ETT.tex:293`)

## What is here

* `GoodBall`, `exists_goodBall`: about every point `p` of an open `U`, a closed ball in `U` on which
  `g` is `Lg`-Lipschitz, `e = T p` is future timelike with `g(e, e) ≤ −c₂`, and every future
  causal `v` has `g(v, e) ≤ −c₁‖v‖` (compactness of the unit future causal vectors over the ball).
* `GoodBall.shift`, **the shift lemma**: a future causal vector at `x`, plus `μ e` with
  `Lg ‖x − y‖ ‖v‖ ≤ c₁ μ`, `μ > 0`, is future timelike at `y`. This is where the Lipschitz bound
  enters, linearly in `‖x − y‖`.
* `GoodBall.chord`: the chords of `σ + φ e`, `σ` a causal path in the ball and `φ` affine of slope
  `λ = (4A + 1)θ`, are timelike segments once short (the integral of `g_q(σ' + m e, w)` against
  every future causal `w` at the point `q` of the chord, `AbsolutelyContinuousOnInterval`, then
  self-duality of the cone).
* `GoodBall.push_past`, `GoodBall.push_future`: push-up along one short causal path in a good
  ball; `causalStep_push`: along any causal path (a subdivision, `exists_subdivision_Icc`);
  `pushUp`: **`L.causality` has the push-up property**; `causallyPlain`: **it is causally
  plain** (`Causality.causallyPlain_of_locZ` with `locZplus`, `locZminus`).

## SCOPE (disclosed)

* The argument is the classical one for Lipschitz metrics and cone fields (Chruściel–Grant,
  `MR2949547`, cited at `ETT.tex:293`): shifting a causal curve along a fixed timelike direction
  with a growing amplitude (here affine on short pieces) makes it timelike, the Lipschitz constant
  paying, linearly, for the change of base point. It is written out here in full, not cited.
* No `sorry` in this file.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace Metric Relation MeasureTheory

open scoped NNReal

namespace LipschitzMetric

variable {n : ℕ} {L : LipschitzMetric n}

/-- **A good ball** about `p` in `U`: the constants of the shift lemma. -/
structure GoodBall (L : LipschitzMetric n) (U : Set (Minkowski n)) (p : Minkowski n)
    (r Lg c₁ c₂ : ℝ) : Prop where
  r_pos : 0 < r
  Lg_nonneg : 0 ≤ Lg
  c₁_pos : 0 < c₁
  c₂_pos : 0 < c₂
  sub : closedBall p r ⊆ U
  lip : ∀ x ∈ closedBall p r, ∀ y ∈ closedBall p r, ‖L.g x - L.g y‖ ≤ Lg * ‖x - y‖
  pair : ∀ x ∈ closedBall p r, ∀ v, L.FC x v → L.g x v (L.T p) ≤ -c₁ * ‖v‖
  ft : ∀ x ∈ closedBall p r, L.FT x (L.T p)
  ee : ∀ x ∈ closedBall p r, L.g x (L.T p) (L.T p) ≤ -c₂
  small : 4 * r * Lg * ‖L.T p‖ ≤ c₁

/-- **Good balls exist** about every point of an open set. -/
theorem exists_goodBall {U : Set (Minkowski n)} (hU : IsOpen U) {p : Minkowski n} (hp : p ∈ U) :
    ∃ r Lg c₁ c₂ : ℝ, GoodBall L U p r Lg c₁ c₂ := by
  set e := L.T p with he_def
  obtain ⟨K₀, t, ht, hlip⟩ := L.locallyLipschitz p
  have hf₁ : Continuous fun x => L.g x e e :=
    (continuous_g.clm_apply continuous_const).clm_apply continuous_const
  have hf₂ : Continuous fun x => L.g x e (L.T x) :=
    (continuous_g.clm_apply continuous_const).clm_apply L.continuous_T
  set c₂ : ℝ := -(L.g p e e) / 2 with hc₂_def
  have hc₂ : 0 < c₂ := by have := L.timelike p; rw [hc₂_def]; linarith
  have hA₁ : {x | L.g x e e < -c₂} ∈ 𝓝 p :=
    (isOpen_lt hf₁ continuous_const).mem_nhds (by show L.g p e e < -c₂; rw [hc₂_def]; linarith)
  have hA₂ : {x | L.g x e (L.T x) < 0} ∈ 𝓝 p :=
    (isOpen_lt hf₂ continuous_const).mem_nhds (by show L.g p e (L.T p) < 0; exact L.timelike p)
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.mem_nhds_iff.1 (inter_mem (inter_mem (inter_mem (hU.mem_nhds hp) ht) hA₁) hA₂)
  set r₀ := ρ / 2
  have hr₀ : 0 < r₀ := half_pos hρ
  have hsub₀ : closedBall p r₀ ⊆ U ∩ t ∩ {x | L.g x e e < -c₂} ∩ {x | L.g x e (L.T x) < 0} :=
    (closedBall_subset_ball (half_lt_self hρ)).trans hball
  have hft : ∀ x ∈ closedBall p r₀, L.FT x e := fun x hx => by
    have h1 : L.g x e e < -c₂ := (hsub₀ hx).1.2
    exact ⟨by linarith, (hsub₀ hx).2⟩
  -- the unit future causal vectors over the ball
  set S : Set (Minkowski n × Minkowski n) :=
    {q | q.1 ∈ closedBall p r₀ ∧ ‖q.2‖ = 1 ∧ L.FC q.1 q.2} with hS_def
  have hSc : IsCompact S := by
    refine (isCompact_closedBall p r₀ |>.prod (isCompact_closedBall (0 : Minkowski n) 1)).of_isClosed_subset
      ?_ ?_
    · refine (isClosed_closedBall.preimage continuous_fst).inter
        ((isClosed_eq (continuous_norm.comp continuous_snd) continuous_const).inter ?_)
      exact (isClosed_le continuous_pair continuous_const).inter
        (isClosed_le continuous_pairT continuous_const)
    · rintro q ⟨h1, h2, -⟩
      exact ⟨h1, by rw [mem_closedBall, dist_zero_right, h2]⟩
  have hF : Continuous fun q : Minkowski n × Minkowski n => L.g q.1 q.2 e :=
    ((continuous_g.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_const
  have hneg : ∀ q ∈ S, L.g q.1 q.2 e < 0 := by
    rintro q ⟨h1, h2, h3⟩
    refine Lorentz.FC.pairing_neg (L.lorentzian q.1) (L.timelike q.1) h3 ?_ (hft q.1 h1)
    intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
  obtain ⟨M, hM, hMS⟩ : ∃ M < 0, ∀ q ∈ S, L.g q.1 q.2 e ≤ M := by
    by_cases hne : S.Nonempty
    · obtain ⟨q₀, hq₀, hmax⟩ := hSc.exists_isMaxOn hne hF.continuousOn
      exact ⟨_, hneg q₀ hq₀, fun q hq => hmax hq⟩
    · exact ⟨-1, by norm_num, fun q hq => absurd ⟨q, hq⟩ hne⟩
  set c₁ := -M
  have hc₁ : 0 < c₁ := neg_pos.2 hM
  have hpair : ∀ x ∈ closedBall p r₀, ∀ v, L.FC x v → L.g x v e ≤ -c₁ * ‖v‖ := by
    intro x hx v hv
    rcases eq_or_ne v 0 with rfl | h0
    · simp
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 h0
      have hq : (x, ‖v‖⁻¹ • v) ∈ S :=
        ⟨hx, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'],
          Lorentz.FC.smul hv (inv_nonneg.2 hn.le)⟩
      have := hMS _ hq
      simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at this
      have h' : L.g x v e = ‖v‖ * (‖v‖⁻¹ * L.g x v e) := by field_simp
      rw [h']
      have := mul_le_mul_of_nonneg_left this hn.le
      linarith
  set Lg : ℝ := (K₀ : ℝ)
  have hLg : 0 ≤ Lg := K₀.2
  set r := min r₀ (c₁ / (4 * Lg * ‖e‖ + 1))
  have hr : 0 < r := lt_min hr₀ (div_pos hc₁ (by positivity))
  have hrr₀ : closedBall p r ⊆ closedBall p r₀ := closedBall_subset_closedBall (min_le_left _ _)
  refine ⟨r, Lg, c₁, c₂, hr, hLg, hc₁, hc₂, fun x hx => (hsub₀ (hrr₀ hx)).1.1.1,
    fun x hx y hy => ?_, fun x hx => hpair x (hrr₀ hx), fun x hx => hft x (hrr₀ hx),
    fun x hx => ((hsub₀ (hrr₀ hx)).1.2).le, ?_⟩
  · have := hlip.dist_le_mul x (hsub₀ (hrr₀ hx)).1.1.2 y (hsub₀ (hrr₀ hy)).1.1.2
    rwa [dist_eq_norm, dist_eq_norm] at this
  · have h1 : r ≤ c₁ / (4 * Lg * ‖e‖ + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith

namespace GoodBall

variable {U : Set (Minkowski n)} {p : Minkowski n} {r Lg c₁ c₂ : ℝ}

/-- **The shift lemma.** -/
theorem shift (hB : GoodBall L U p r Lg c₁ c₂) {x y v : Minkowski n} (hx : x ∈ closedBall p r)
    (hy : y ∈ closedBall p r) (hv : L.FC x v) {μ : ℝ} (hμ : 0 < μ)
    (h : Lg * ‖x - y‖ * ‖v‖ ≤ c₁ * μ) : L.FT y (v + μ • L.T p) := by
  set e := L.T p
  set G := L.g y
  set F := L.g x
  have hd : ‖x - y‖ ≤ 2 * r := by
    rw [← dist_eq_norm]
    have := dist_triangle x p y
    rw [mem_closedBall] at hx hy
    rw [dist_comm] at hy
    linarith
  have hGF : ‖G - F‖ ≤ Lg * ‖x - y‖ := by
    rw [norm_sub_rev x y]; exact hB.lip y hy x hx
  have hb := hB.Lg_nonneg
  have hsmall : Lg * ‖x - y‖ * ‖e‖ ≤ c₁ / 2 := by
    have := hB.small
    have h2 : Lg * ‖x - y‖ * ‖e‖ ≤ Lg * (2 * r) * ‖e‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hb) (norm_nonneg _)
    linarith
  have hsym : G e v = G v e := (L.lorentzian y).symm e v
  have hvv : G v v ≤ Lg * ‖x - y‖ * ‖v‖ * ‖v‖ := by
    have h1 : G v v = F v v + (G - F) v v := by simp
    have h2 := ContinuousLinearMap.le_opNorm₂ (G - F) v v
    have h3 : (G - F) v v ≤ ‖(G - F) v v‖ := Real.le_norm_self _
    have h4 : ‖G - F‖ * ‖v‖ * ‖v‖ ≤ Lg * ‖x - y‖ * ‖v‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGF (norm_nonneg _)) (norm_nonneg _)
    linarith [hv.1]
  have hve : G v e ≤ -c₁ * ‖v‖ / 2 := by
    have h1 : G v e = F v e + (G - F) v e := by simp
    have h2 := ContinuousLinearMap.le_opNorm₂ (G - F) v e
    have h3 : (G - F) v e ≤ ‖(G - F) v e‖ := Real.le_norm_self _
    have h4 : ‖G - F‖ * ‖v‖ * ‖e‖ ≤ Lg * ‖x - y‖ * ‖v‖ * ‖e‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGF (norm_nonneg _)) (norm_nonneg _)
    have h5 := hB.pair x hx v hv
    have h6 : Lg * ‖x - y‖ * ‖v‖ * ‖e‖ ≤ c₁ / 2 * ‖v‖ := by
      have := mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)
      linarith
    linarith
  have hee : G e e ≤ -c₂ := hB.ee y hy
  have hc₁ := hB.c₁_pos
  have hc₂ := hB.c₂_pos
  have hQ : G (v + μ • e) (v + μ • e) < 0 := by
    have hexp : G (v + μ • e) (v + μ • e) = G v v + 2 * μ * G v e + μ ^ 2 * G e e := by
      simp only [map_add, map_smul, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul]
      rw [hsym]; ring
    rw [hexp]
    have h7 : Lg * ‖x - y‖ * ‖v‖ * ‖v‖ ≤ c₁ * μ * ‖v‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    have h8 : 2 * μ * G v e ≤ 2 * μ * (-c₁ * ‖v‖ / 2) := mul_le_mul_of_nonneg_left hve (by positivity)
    have h9 : μ ^ 2 * G e e ≤ μ ^ 2 * (-c₂) := mul_le_mul_of_nonneg_left hee (by positivity)
    nlinarith [sq_pos_of_pos hμ]
  have hP : G (v + μ • e) e < 0 := by
    simp only [map_add, map_smul, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    have h9 : μ * G e e ≤ μ * (-c₂) := mul_le_mul_of_nonneg_left hee hμ.le
    nlinarith [norm_nonneg v]
  exact Lorentz.ft_of_pairing_neg (L.lorentzian y) (L.timelike y) hQ (hB.ft y hy) hP

/-- The constant `A = Lg K ‖e‖ / c₁` of the chord estimate. -/
noncomputable def cA (L : LipschitzMetric n) (p : Minkowski n) (Lg c₁ : ℝ) (K : ℝ≥0) : ℝ :=
  Lg * K * ‖L.T p‖ / c₁

/-- **A chord of the shifted path is a timelike segment.** `σ` is a causal path in the half ball,
`φ(s) = φ₀ + λ (s − c)` with `λ = (4A + 1) θ` and `|φ| ≤ 2θ`; the chord from `s₁` to `s₂` is
short. -/
theorem chord (hB : GoodBall L U p r Lg c₁ c₂) {σ : ℝ → Minkowski n} {K : ℝ≥0}
    (hK : LipschitzWith K σ) {c d : ℝ}
    (hae : ∀ᵐ s, s ∈ Ioo c d → ∃ v, HasDerivAt σ v s ∧ L.FC (σ s) v)
    (hσ : ∀ s ∈ Icc c d, σ s ∈ closedBall p (r / 2)) {θ : ℝ} (hθ : 0 < θ)
    (hθr : 2 * θ * ‖L.T p‖ ≤ r / 2) {φ₀ : ℝ}
    (hφ : ∀ s ∈ Icc c d, |φ₀ + (4 * cA L p Lg c₁ K + 1) * θ * (s - c)| ≤ 2 * θ)
    {s₁ s₂ : ℝ} (hs₁ : c ≤ s₁) (h12 : s₁ < s₂) (hs₂ : s₂ ≤ d)
    (hh : (2 * Lg * K ^ 2 / c₁ + cA L p Lg c₁ K * ((4 * cA L p Lg c₁ K + 1) * θ)) * (s₂ - s₁)
      < θ / 2) :
    let τ := fun s => σ s + (φ₀ + (4 * cA L p Lg c₁ K + 1) * θ * (s - c)) • L.T p
    L.IsTimelikePath U (fun t => τ s₁ + t • (τ s₂ - τ s₁)) 0 1 := by
  intro τ
  set e := L.T p
  set A := cA L p Lg c₁ K with hA_def
  set lam := (4 * A + 1) * θ with hlam
  set h := s₂ - s₁ with hh_def
  have hc₁ := hB.c₁_pos
  have hLg := hB.Lg_nonneg
  have hA0 : 0 ≤ A := by rw [hA_def, cA]; positivity
  have hh0 : 0 < h := sub_pos.2 h12
  set m := 2 * Lg * K ^ 2 * h / c₁ + 2 * A * θ + A * lam * h + θ / 2 with hm_def
  have hm0 : 0 < m := by
    have : 0 ≤ 2 * Lg * K ^ 2 * h / c₁ := by positivity
    have : 0 ≤ A * lam * h := by positivity
    have : 0 ≤ 2 * A * θ := by positivity
    rw [hm_def]; linarith
  have hmlam : m < lam := by
    have : 2 * Lg * K ^ 2 * h / c₁ + A * lam * h = (2 * Lg * K ^ 2 / c₁ + A * lam) * h := by ring
    rw [hlam] at this ⊢
    nlinarith
  have hs₁' : s₁ ∈ Icc c d := ⟨hs₁, h12.le.trans hs₂⟩
  have hs₂' : s₂ ∈ Icc c d := ⟨hs₁.trans h12.le, hs₂⟩
  -- the shifted path stays in the ball
  have hτ : ∀ s ∈ Icc c d, τ s ∈ closedBall p r := by
    intro s hs
    have h1 := hσ s hs
    rw [mem_closedBall, dist_eq_norm] at h1 ⊢
    calc ‖τ s - p‖ = ‖(σ s - p) + (φ₀ + lam * (s - c)) • e‖ := by
          simp only [τ]; congr 1; abel
      _ ≤ ‖σ s - p‖ + |φ₀ + lam * (s - c)| * ‖e‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_eq_abs]
      _ ≤ r / 2 + 2 * θ * ‖e‖ :=
          add_le_add h1 (mul_le_mul_of_nonneg_right (hφ s hs) (norm_nonneg _))
      _ ≤ r := by linarith
  have hΔ : τ s₂ - τ s₁ = (σ s₂ - σ s₁ + (m * h) • e) + ((lam - m) * h) • e := by
    simp only [τ, hh_def]
    rw [add_assoc, ← add_smul]
    have : φ₀ + lam * (s₂ - c) - (φ₀ + lam * (s₁ - c)) = m * (s₂ - s₁) + (lam - m) * (s₂ - s₁) := by
      ring
    rw [show σ s₂ + (φ₀ + lam * (s₂ - c)) • e - (σ s₁ + (φ₀ + lam * (s₁ - c)) • e)
        = σ s₂ - σ s₁ + (φ₀ + lam * (s₂ - c) - (φ₀ + lam * (s₁ - c))) • e by
          rw [sub_smul]; abel, this]
  have hσ12 : ‖σ s₂ - σ s₁‖ ≤ K * h := by
    rw [← dist_eq_norm]
    have := hK.dist_le_mul s₂ s₁
    rwa [Real.dist_eq, abs_of_pos (sub_pos.2 h12)] at this
  refine isTimelikePath_segment one_pos (fun t ht => hB.sub ?_) (fun t ht => ?_)
  · exact (convex_closedBall p r).add_smul_sub_mem (hτ s₁ hs₁') (hτ s₂ hs₂') ht
  set q := τ s₁ + t • (τ s₂ - τ s₁) with hq_def
  have hq : q ∈ closedBall p r := (convex_closedBall p r).add_smul_sub_mem (hτ s₁ hs₁') (hτ s₂ hs₂') ht
  -- the distance from the base points of `σ'` to `q`
  have hdist : ∀ s ∈ Icc s₁ s₂, ‖σ s - q‖ ≤ 2 * K * h + 2 * θ * ‖e‖ + lam * h * ‖e‖ := by
    intro s hs
    have h1 : ‖σ s - σ s₁‖ ≤ K * h := by
      rw [← dist_eq_norm]
      refine (hK.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ K.2)
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    have h2 : ‖(φ₀ + lam * (s₁ - c)) • e‖ ≤ 2 * θ * ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hφ s₁ hs₁') (norm_nonneg _)
    have h3 : ‖t • (τ s₂ - τ s₁)‖ ≤ K * h + lam * h * ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have : τ s₂ - τ s₁ = (σ s₂ - σ s₁) + (lam * h) • e := by
        simp only [τ, hh_def]
        rw [show σ s₂ + (φ₀ + lam * (s₂ - c)) • e - (σ s₁ + (φ₀ + lam * (s₁ - c)) • e)
          = σ s₂ - σ s₁ + (φ₀ + lam * (s₂ - c) - (φ₀ + lam * (s₁ - c))) • e by
            rw [sub_smul]; abel]
        congr 2; ring
      have h4 : ‖τ s₂ - τ s₁‖ ≤ K * h + lam * h * ‖e‖ := by
        rw [this]
        refine (norm_add_le _ _).trans (add_le_add hσ12 ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc t * ‖τ s₂ - τ s₁‖ ≤ 1 * ‖τ s₂ - τ s₁‖ :=
            mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h4
    have : σ s - q = (σ s - σ s₁) - (φ₀ + lam * (s₁ - c)) • e - t • (τ s₂ - τ s₁) := by
      simp only [hq_def, τ]; abel
    rw [this]
    calc ‖(σ s - σ s₁) - (φ₀ + lam * (s₁ - c)) • e - t • (τ s₂ - τ s₁)‖
        ≤ ‖σ s - σ s₁‖ + ‖(φ₀ + lam * (s₁ - c)) • e‖ + ‖t • (τ s₂ - τ s₁)‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ K * h + 2 * θ * ‖e‖ + (K * h + lam * h * ‖e‖) := add_le_add (add_le_add h1 h2) h3
      _ = _ := by ring
  -- the shifted derivatives are future timelike at `q`
  have hshift : ∀ s ∈ Ioo s₁ s₂, ∀ v, HasDerivAt σ v s → L.FC (σ s) v → L.FT q (v + m • e) := by
    intro s hs v hv hfc
    have hvK : ‖v‖ ≤ K := hv.le_of_lipschitz hK
    have hsI : s ∈ Icc c d := ⟨hs₁.trans hs.1.le, hs.2.le.trans hs₂⟩
    have hσs : σ s ∈ closedBall p r :=
      closedBall_subset_closedBall (half_le_self hB.r_pos.le) (hσ s hsI)
    refine hB.shift hσs hq hfc hm0 ?_
    have hd := hdist s (Ioo_subset_Icc_self hs)
    calc Lg * ‖σ s - q‖ * ‖v‖ ≤ Lg * (2 * K * h + 2 * θ * ‖e‖ + lam * h * ‖e‖) * K :=
          mul_le_mul (mul_le_mul_of_nonneg_left hd hLg) hvK (norm_nonneg _) (by positivity)
      _ = c₁ * (2 * Lg * K ^ 2 * h / c₁ + 2 * A * θ + A * lam * h) := by
          rw [hA_def, cA]; field_simp; ring
      _ ≤ c₁ * m := by rw [hm_def]; nlinarith
  -- self-duality: the chord of `σ + m s e` is future causal at `q`
  have hfcq : L.FC q (σ s₂ - σ s₁ + (m * h) • e) := by
    refine Lorentz.fc_of_forall_pairing_nonpos (L.lorentzian q) (L.timelike q) fun w hw => ?_
    set ℓ : Minkowski n →L[ℝ] ℝ := (L.g q).flip w
    set ψ : ℝ → ℝ := fun s => -(ℓ (σ s) + m * s * L.g q e w)
    have hψlip : LipschitzWith (‖ℓ‖₊ * K + ‖m * L.g q e w‖₊) ψ := by
      have h1 : LipschitzWith (‖ℓ‖₊ * K) (fun s => ℓ (σ s)) := ℓ.lipschitz.comp hK
      have h2 : LipschitzWith ‖m * L.g q e w‖₊ (fun s : ℝ => m * s * L.g q e w) := by
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
        exact le_of_eq (by congr 1; ring)
      exact (h1.add h2).neg
    have hac := (hψlip.lipschitzOnWith (s := uIcc s₁ s₂)).absolutelyContinuousOnInterval
    have hftc := hac.integral_deriv_eq_sub
    have hderiv : ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)), 0 ≤ deriv ψ s := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hae] with s hs hs12
      obtain ⟨v, hv, hfc⟩ := hs ⟨hs₁.trans_lt hs12.1, hs12.2.trans_le hs₂⟩
      have hd : HasDerivAt ψ (-(ℓ v + m * L.g q e w)) s := by
        have h1 : HasDerivAt (fun s => ℓ (σ s)) (ℓ v) s := ℓ.hasFDerivAt.comp_hasDerivAt s hv
        have h2 : HasDerivAt (fun s : ℝ => m * s * L.g q e w) (m * L.g q e w) s := by
          simpa using ((hasDerivAt_id s).const_mul m).mul_const (L.g q e w)
        exact (h1.add h2).neg
      rw [hd.deriv]
      have := Lorentz.FC.pairing_nonpos (L.lorentzian q) (L.timelike q)
        (hshift s hs12 v hv hfc).fc hw
      have hlin : L.g q (v + m • e) w = ℓ v + m * L.g q e w := by
        simp [ℓ]
      linarith
    have hint := intervalIntegral.integral_nonneg_of_ae_restrict h12.le hderiv
    rw [hftc] at hint
    have : L.g q (σ s₂ - σ s₁ + (m * h) • e) w = -(ψ s₂ - ψ s₁) := by
      simp only [ψ, ℓ, hh_def, map_add, map_sub, map_smul, FunLike.coe_add, FunLike.coe_sub,
        Pi.add_apply, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
        ContinuousLinearMap.flip_apply]
      ring
    linarith
  have hft2 : L.FT q (((lam - m) * h) • e) := Lorentz.FT.smul (hB.ft q hq) (by
    have := sub_pos.2 hmlam; positivity)
  rw [hΔ]
  exact Lorentz.FC.add_ft (L.lorentzian q) (L.timelike q) hfcq hft2

/-- A point of the half ball moved by `α e`, `|α| ≤ 2θ`, stays in the ball. -/
theorem _root_.Causal.LipschitzMetric.mem_ball_shift {p : Minkowski n} {r : ℝ} {y : Minkowski n}
    (hy : y ∈ closedBall p (r / 2)) {α θ : ℝ} (hα : |α| ≤ 2 * θ) (hθr : 2 * θ * ‖L.T p‖ ≤ r / 2) :
    y + α • L.T p ∈ closedBall p r := by
  rw [mem_closedBall, dist_eq_norm] at hy ⊢
  calc ‖y + α • L.T p - p‖ = ‖(y - p) + α • L.T p‖ := by congr 1; abel
    _ ≤ ‖y - p‖ + |α| * ‖L.T p‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_eq_abs]
    _ ≤ r / 2 + 2 * θ * ‖L.T p‖ :=
        add_le_add hy (mul_le_mul_of_nonneg_right hα (norm_nonneg _))
    _ ≤ r := by linarith

/-- **A segment along `e = T p`** inside the ball is a timelike path. -/
theorem timeStep_e (hB : GoodBall L U p r Lg c₁ c₂) {y : Minkowski n} {θ : ℝ} (hθ : 0 < θ)
    (hy : ∀ s ∈ Icc (0 : ℝ) 1, y + s • (θ • L.T p) ∈ closedBall p r) :
    L.TimeStep U y (y + θ • L.T p) :=
  ⟨_, 0, 1, isTimelikePath_segment one_pos (fun s hs => hB.sub (hy s hs))
    (fun s hs => Lorentz.FT.smul (hB.ft _ (hy s hs)) hθ), by simp, by simp⟩

/-- **The polygon**: the shifted path `σ + φ e` goes chronologically from its start to its end. -/
theorem polygon (hB : GoodBall L U p r Lg c₁ c₂) {σ : ℝ → Minkowski n} {K : ℝ≥0}
    (hK : LipschitzWith K σ) {c d : ℝ} (hcd : c < d)
    (hae : ∀ᵐ s, s ∈ Ioo c d → ∃ v, HasDerivAt σ v s ∧ L.FC (σ s) v)
    (hσ : ∀ s ∈ Icc c d, σ s ∈ closedBall p (r / 2)) {θ : ℝ} (hθ : 0 < θ)
    (hθr : 2 * θ * ‖L.T p‖ ≤ r / 2) {φ₀ : ℝ}
    (hφ : ∀ s ∈ Icc c d, |φ₀ + (4 * cA L p Lg c₁ K + 1) * θ * (s - c)| ≤ 2 * θ) :
    TransGen (L.TimeStep U)
      (σ c + (φ₀ + (4 * cA L p Lg c₁ K + 1) * θ * (c - c)) • L.T p)
      (σ d + (φ₀ + (4 * cA L p Lg c₁ K + 1) * θ * (d - c)) • L.T p) := by
  set A := cA L p Lg c₁ K with hA_def
  set X := 2 * Lg * K ^ 2 / c₁ + A * ((4 * A + 1) * θ) with hX
  have hc₁ := hB.c₁_pos
  have hA0 : 0 ≤ A := by rw [hA_def, cA]; have := hB.Lg_nonneg; positivity
  have hX0 : 0 ≤ X := by have := hB.Lg_nonneg; rw [hX]; positivity
  obtain ⟨N', hN'⟩ := exists_nat_gt (2 * X * (d - c) / θ)
  set N : ℕ := N' + 1
  have hN : (0 : ℝ) < N := by positivity
  have hNgt : 2 * X * (d - c) / θ < N := hN'.trans (by simp [N])
  set h := (d - c) / N with hh
  have hh0 : 0 < h := div_pos (sub_pos.2 hcd) hN
  have hXh : X * h < θ / 2 := by
    rw [div_lt_iff₀ hθ] at hNgt
    rw [hh, mul_div_assoc', div_lt_iff₀ hN]
    nlinarith
  set sk : ℕ → ℝ := fun k => c + k * h
  have hsk_le : ∀ k : ℕ, k ≤ N → sk k ≤ d := by
    intro k hk
    have : (k : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh0.le
    have hNh : (N : ℝ) * h = d - c := by rw [hh]; field_simp
    simp only [sk]; linarith
  have hstep : ∀ k : ℕ, k < N → L.TimeStep U
      (σ (sk k) + (φ₀ + (4 * A + 1) * θ * (sk k - c)) • L.T p)
      (σ (sk (k + 1)) + (φ₀ + (4 * A + 1) * θ * (sk (k + 1) - c)) • L.T p) := by
    intro k hk
    have h1 : c ≤ sk k := by simp only [sk]; have : 0 ≤ (k : ℝ) * h := by positivity
                             linarith
    have h2 : sk k < sk (k + 1) := by simp only [sk]; push_cast; linarith
    have h3 : sk (k + 1) ≤ d := hsk_le (k + 1) hk
    have h4 : X * (sk (k + 1) - sk k) < θ / 2 := by
      have : sk (k + 1) - sk k = h := by simp only [sk]; push_cast; ring
      rwa [this]
    refine ⟨_, 0, 1, hB.chord hK hae hσ hθ hθr hφ h1 h2 h3 h4, by simp [hA_def], ?_⟩
    simp [hA_def]
  have key : ∀ k : ℕ, k < N → TransGen (L.TimeStep U)
      (σ (sk 0) + (φ₀ + (4 * A + 1) * θ * (sk 0 - c)) • L.T p)
      (σ (sk (k + 1)) + (φ₀ + (4 * A + 1) * θ * (sk (k + 1) - c)) • L.T p) := by
    intro k
    induction k with
    | zero => exact fun h0 => TransGen.single (hstep 0 h0)
    | succ k ih => exact fun hk => (ih (by omega)).tail (hstep (k + 1) hk)
  have h0 : sk 0 = c := by simp [sk]
  have hN' : sk N = d := by
    simp only [sk, hh]; field_simp; ring
  have := key N' (by simp [N])
  rw [h0] at this
  rw [show N' + 1 = N from rfl, hN'] at this
  exact this

/-- **Push-up in the past along a short causal path in a good ball**: `σ d ≪ z ⇒ σ c ≪ z`. -/
theorem push_past {W : Opens (Minkowski n)} (hB : GoodBall L W p r Lg c₁ c₂) {σ : ℝ → Minkowski n}
    {K : ℝ≥0} (hK : LipschitzWith K σ) {c d : ℝ} (hcd : c < d)
    (hae : ∀ᵐ s, s ∈ Ioo c d → ∃ v, HasDerivAt σ v s ∧ L.FC (σ s) v)
    (hσ : ∀ s ∈ Icc c d, σ s ∈ closedBall p (r / 2))
    (hlen : (4 * cA L p Lg c₁ K + 1) * (d - c) ≤ 1) {z : Minkowski n}
    (hz : L.causality.lt W (σ d) z) : L.causality.lt W (σ c) z := by
  set e := L.T p
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (L.causality.isOpen_lt_left W z) (σ d) hz
  set θ := min ε (r / 2) / (2 * (‖e‖ + 1)) with hθ_def
  have hr := hB.r_pos
  have hθ : 0 < θ := div_pos (lt_min hε (half_pos hr)) (by positivity)
  have hθe : 2 * θ * ‖e‖ < min ε (r / 2) := by
    rw [hθ_def]
    have hm : 0 < min ε (r / 2) := lt_min hε (half_pos hr)
    rw [show 2 * (min ε (r / 2) / (2 * (‖e‖ + 1))) * ‖e‖ = min ε (r / 2) * (‖e‖ / (‖e‖ + 1)) by
      field_simp]
    have : ‖e‖ / (‖e‖ + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  have hθr : 2 * θ * ‖e‖ ≤ r / 2 := (hθe.trans_le (min_le_right _ _)).le
  set A := cA L p Lg c₁ K
  have hA0 : 0 ≤ A := by simp only [A, cA]; have := hB.Lg_nonneg; have := hB.c₁_pos; positivity
  have hφ : ∀ s ∈ Icc c d, |θ + (4 * A + 1) * θ * (s - c)| ≤ 2 * θ := by
    intro s hs
    have h1 : 0 ≤ (4 * A + 1) * θ * (s - c) := by
      have := hs.1; have : 0 ≤ s - c := by linarith
      positivity
    have h2 : (4 * A + 1) * θ * (s - c) ≤ θ := by
      have : (4 * A + 1) * (s - c) ≤ 1 :=
        (mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity)).trans hlen
      nlinarith
    rw [abs_of_nonneg (by linarith)]; linarith
  have hpoly := hB.polygon hK hcd hae hσ hθ hθr hφ
  simp only [sub_self, mul_zero, add_zero] at hpoly
  have hfirst : L.causality.lt W (σ c) (σ c + θ • e) := by
    refine TransGen.single (hB.timeStep_e hθ fun s hs => ?_)
    rw [smul_smul]
    refine mem_ball_shift (hσ c ⟨le_rfl, hcd.le⟩) ?_ hθr
    rw [abs_of_nonneg (mul_nonneg hs.1 hθ.le)]; nlinarith [hs.2]
  have hlast : L.causality.lt W (σ d + (θ + (4 * A + 1) * θ * (d - c)) • e) z := by
    refine hball ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |θ + (4 * A + 1) * θ * (d - c)| * ‖e‖ ≤ 2 * θ * ‖e‖ :=
          mul_le_mul_of_nonneg_right (hφ d ⟨hcd.le, le_rfl⟩) (norm_nonneg _)
      _ < ε := hθe.trans_le (min_le_left _ _)
  exact (hfirst.trans hpoly).trans hlast

/-- **Push-up in the future along a short causal path in a good ball**: `x ≪ σ c ⇒ x ≪ σ d`. -/
theorem push_future {W : Opens (Minkowski n)} (hB : GoodBall L W p r Lg c₁ c₂)
    {σ : ℝ → Minkowski n} {K : ℝ≥0} (hK : LipschitzWith K σ) {c d : ℝ} (hcd : c < d)
    (hae : ∀ᵐ s, s ∈ Ioo c d → ∃ v, HasDerivAt σ v s ∧ L.FC (σ s) v)
    (hσ : ∀ s ∈ Icc c d, σ s ∈ closedBall p (r / 2))
    (hlen : (4 * cA L p Lg c₁ K + 1) * (d - c) ≤ 1) {x : Minkowski n}
    (hx : L.causality.lt W x (σ c)) : L.causality.lt W x (σ d) := by
  set e := L.T p
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (L.causality.isOpen_lt_right W x) (σ c) hx
  set θ := min ε (r / 2) / (2 * (‖e‖ + 1)) with hθ_def
  have hr := hB.r_pos
  have hθ : 0 < θ := div_pos (lt_min hε (half_pos hr)) (by positivity)
  have hθe : 2 * θ * ‖e‖ < min ε (r / 2) := by
    rw [hθ_def]
    have hm : 0 < min ε (r / 2) := lt_min hε (half_pos hr)
    rw [show 2 * (min ε (r / 2) / (2 * (‖e‖ + 1))) * ‖e‖ = min ε (r / 2) * (‖e‖ / (‖e‖ + 1)) by
      field_simp]
    have : ‖e‖ / (‖e‖ + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  have hθr : 2 * θ * ‖e‖ ≤ r / 2 := (hθe.trans_le (min_le_right _ _)).le
  set A := cA L p Lg c₁ K
  have hA0 : 0 ≤ A := by simp only [A, cA]; have := hB.Lg_nonneg; have := hB.c₁_pos; positivity
  set φ₀ := -θ - (4 * A + 1) * θ * (d - c)
  have hφ : ∀ s ∈ Icc c d, |φ₀ + (4 * A + 1) * θ * (s - c)| ≤ 2 * θ := by
    intro s hs
    have h1 : 0 ≤ (4 * A + 1) * θ * (d - s) := by
      have := hs.2; have : 0 ≤ d - s := by linarith
      positivity
    have h2 : (4 * A + 1) * θ * (d - s) ≤ θ := by
      have : (4 * A + 1) * (d - s) ≤ 1 :=
        (mul_le_mul_of_nonneg_left (by linarith [hs.1]) (by positivity)).trans hlen
      nlinarith
    have : φ₀ + (4 * A + 1) * θ * (s - c) = -(θ + (4 * A + 1) * θ * (d - s)) := by
      simp only [φ₀]; ring
    rw [this, abs_neg, abs_of_nonneg (by linarith)]; linarith
  have hpoly := hB.polygon hK hcd hae hσ hθ hθr hφ
  have hend : φ₀ + (4 * A + 1) * θ * (d - c) = -θ := by simp only [φ₀]; ring
  simp only [sub_self, mul_zero, add_zero] at hpoly
  rw [hend] at hpoly
  have hfirst : L.causality.lt W x (σ c + φ₀ • e) := by
    refine hball ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have := hφ c ⟨le_rfl, hcd.le⟩
    simp only [sub_self, mul_zero, add_zero] at this
    calc |φ₀| * ‖e‖ ≤ 2 * θ * ‖e‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ < ε := hθe.trans_le (min_le_left _ _)
  have hlast : L.causality.lt W (σ d + (-θ) • e) (σ d) := by
    have := hB.timeStep_e (y := σ d + (-θ) • e) hθ fun s hs => by
      rw [add_assoc, smul_smul, ← add_smul]
      refine mem_ball_shift (hσ d ⟨hcd.le, le_rfl⟩) ?_ hθr
      rw [abs_le]; constructor <;> nlinarith [hs.1, hs.2]
    rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero] at this
    exact TransGen.single this
  exact (hfirst.trans hpoly).trans hlast

end GoodBall

/-- **Push-up along one causal path**, in both directions. -/
theorem causalStep_push {U : Opens (Minkowski n)} {γ : ℝ → Minkowski n} {a b : ℝ}
    (hγ : L.IsCausalPath U γ a b) :
    (∀ z, L.causality.lt U (γ b) z → L.causality.lt U (γ a) z) ∧
      (∀ x, L.causality.lt U x (γ a) → L.causality.lt U x (γ b)) := by
  obtain ⟨hab, ⟨K, hK⟩, hmaps, hae⟩ := hγ
  have hgb : ∀ q ∈ (U : Set (Minkowski n)), ∃ r Lg c₁ c₂ : ℝ, GoodBall L U q r Lg c₁ c₂ :=
    fun q hq => exists_goodBall U.isOpen hq
  choose! R Lgf C1 C2 hR using hgb
  set δf : Minkowski n → ℝ := fun q => 1 / (4 * GoodBall.cA L q (Lgf q) (C1 q) K + 1) with hδf
  have hδpos : ∀ q ∈ (U : Set (Minkowski n)), 0 < δf q := by
    intro q hq
    have hB := hR q hq
    have : 0 ≤ GoodBall.cA L q (Lgf q) (C1 q) K := by
      simp only [GoodBall.cA]; have := hB.Lg_nonneg; have := hB.c₁_pos; positivity
    simp only [hδf]; positivity
  set O : Icc a b → Set ℝ := fun i =>
    γ ⁻¹' ball (γ i) (R (γ i) / 2) ∩ Ioo (i - δf (γ i) / 2) (i + δf (γ i) / 2) with hO
  have hOopen : ∀ i, IsOpen (O i) := fun i =>
    (isOpen_ball.preimage hK.continuous).inter isOpen_Ioo
  have hcover : Icc a b ⊆ ⋃ i, O i := by
    intro s hs
    refine mem_iUnion.2 ⟨⟨s, hs⟩, ?_, ?_⟩
    · exact mem_ball_self (half_pos (hR _ (hmaps hs)).r_pos)
    · have := hδpos _ (hmaps hs)
      constructor <;> simp <;> linarith
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, htI, hpiece⟩ := exists_subdivision_Icc hab hOopen hcover
  have hstep : ∀ j : ℕ,
      (∀ z, L.causality.lt U (γ (t (j + 1))) z → L.causality.lt U (γ (t j)) z) ∧
        (∀ x, L.causality.lt U x (γ (t j)) → L.causality.lt U x (γ (t (j + 1)))) := by
    intro j
    rcases (hmono (Nat.le_succ j)).eq_or_lt with heq | hlt
    · rw [heq]; exact ⟨fun _ h => h, fun _ h => h⟩
    obtain ⟨i, hi⟩ := hpiece j
    have hB := hR _ (hmaps i.2)
    have hσ : ∀ s ∈ Icc (t j) (t (j + 1)), γ s ∈ closedBall (γ i) (R (γ i) / 2) :=
      fun s hs => ball_subset_closedBall (hi hs).1
    have hae' : ∀ᵐ s, s ∈ Ioo (t j) (t (j + 1)) → ∃ v, HasDerivAt γ v s ∧ L.FC (γ s) v := by
      filter_upwards [hae] with s hs hs'
      exact hs ⟨(htI j).1.trans_lt hs'.1, hs'.2.trans_le (htI (j + 1)).2⟩
    have hlen : (4 * GoodBall.cA L (γ i) (Lgf (γ i)) (C1 (γ i)) K + 1) * (t (j + 1) - t j) ≤ 1 := by
      have h1 := (hi ⟨le_rfl, hlt.le⟩).2
      have h2 := (hi ⟨hlt.le, le_rfl⟩).2
      have hd : t (j + 1) - t j ≤ δf (γ i) := by linarith [h1.1, h2.2]
      have hpos : 0 < 4 * GoodBall.cA L (γ i) (Lgf (γ i)) (C1 (γ i)) K + 1 := by
        have : 0 ≤ GoodBall.cA L (γ i) (Lgf (γ i)) (C1 (γ i)) K := by
          simp only [GoodBall.cA]; have := hB.Lg_nonneg; have := hB.c₁_pos; positivity
        positivity
      calc _ ≤ (4 * GoodBall.cA L (γ i) (Lgf (γ i)) (C1 (γ i)) K + 1) * δf (γ i) :=
            mul_le_mul_of_nonneg_left hd hpos.le
        _ = 1 := by simp only [hδf]; field_simp
    exact ⟨fun z hz => hB.push_past hK hlt hae' hσ hlen hz,
      fun x hx => hB.push_future hK hlt hae' hσ hlen hx⟩
  have ha : t 0 = a := ht0
  have hb : t m = b := hm m le_rfl
  refine ⟨fun z hz => ?_, fun x hx => ?_⟩
  · have key : ∀ k, k ≤ m → L.causality.lt U (γ (t (m - k))) z := by
      intro k
      induction k with
      | zero => intro _; rw [Nat.sub_zero, hb]; exact hz
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have : m - k = (m - (k + 1)) + 1 := by omega
        rw [this] at h1
        exact (hstep _).1 z h1
    have := key m le_rfl
    rwa [Nat.sub_self, ha] at this
  · have key : ∀ k, L.causality.lt U x (γ (t k)) := by
      intro k
      induction k with
      | zero => rw [ha]; exact hx
      | succ k ih => exact (hstep k).2 x ih
    have := key m
    rwa [hb] at this

/-- **A locally Lipschitz Lorentzian metric has the push-up property.** -/
theorem pushUp : L.causality.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  refine ⟨fun hxy hyz => ?_, fun hxy hyz => ?_⟩
  · obtain ⟨-, h⟩ := hyz
    induction h with
    | refl => exact hxy
    | tail _ hst ih =>
      obtain ⟨γ, a, b, hγ, rfl, rfl⟩ := hst
      exact (causalStep_push hγ).2 _ ih
  · obtain ⟨-, h⟩ := hxy
    induction h using ReflTransGen.head_induction_on with
    | refl => exact hyz
    | head hst _ ih =>
      obtain ⟨γ, a, b, hγ, rfl, rfl⟩ := hst
      exact (causalStep_push hγ).1 _ ih

/-- **A locally Lipschitz Lorentzian metric is causally plain** (DEC-168). -/
theorem causallyPlain : L.causality.CausallyPlain :=
  Causality.causallyPlain_of_locZ pushUp locZplus locZminus interior_empty

end LipschitzMetric

end Causal
