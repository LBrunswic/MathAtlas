import GXScaffold.Branched.GaloisExamples

open Set Function Topology unitInterval

noncomputable section

namespace GX

/-! ### The collar of a link: coordinates -/

/-- The square radius `ρ = max(|x|, |y|)`. -/
def antoineRho (p : ℝ × ℝ × ℝ) : ℝ := max |p.1| |p.2.1|

/-- The longitudinal coordinate `x + i y` of the collar. -/
def antoineAng (p : ℝ × ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I

/-- The meridional coordinate `(ρ - 7/8) + i z` of the collar. -/
def antoineW (p : ℝ × ℝ × ℝ) : ℂ := ((antoineRho p - 7 / 8 : ℝ) : ℂ) + (p.2.2 : ℂ) * Complex.I

/-- The collar `N ∖ L` of the link, in `ℝ³`. -/
def antoineA0 : Set (ℝ × ℝ × ℝ) := antoineNbhd \ antoineLink

theorem continuous_antoineRho : Continuous antoineRho := by unfold antoineRho; fun_prop
theorem continuous_antoineAng : Continuous antoineAng := by unfold antoineAng; fun_prop
theorem continuous_antoineW : Continuous antoineW := by
  unfold antoineW; have := continuous_antoineRho; fun_prop

theorem antoineW_normSq (p : ℝ × ℝ × ℝ) :
    ‖antoineW p‖ ^ 2 = (antoineRho p - 7 / 8) ^ 2 + p.2.2 ^ 2 := by
  rw [Complex.sq_norm, antoineW, Complex.normSq_add_mul_I]

theorem antoineAng_normSq (p : ℝ × ℝ × ℝ) : ‖antoineAng p‖ ^ 2 = p.1 ^ 2 + p.2.1 ^ 2 := by
  rw [Complex.sq_norm, antoineAng, Complex.normSq_add_mul_I]

theorem mem_antoineNbhd_iff (p : ℝ × ℝ × ℝ) : p ∈ antoineNbhd ↔ ‖antoineW p‖ ^ 2 < 1 / 16 := by
  rw [antoineW_normSq]; rfl

/-- A point of the tube is in the link iff its meridional coordinate is in the square
`[-1/8, 1/8]²`. -/
theorem mem_antoineLink_iff (p : ℝ × ℝ × ℝ) :
    p ∈ antoineLink ↔ |antoineRho p - 7 / 8| ≤ 1 / 8 ∧ |p.2.2| ≤ 1 / 8 := by
  show (|p.2.2| ≤ 1 / 8 ∧ antoineRho p ≤ 1 ∧ 3 / 4 ≤ antoineRho p) ↔ _
  rw [abs_le (a := antoineRho p - 7 / 8)]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, by linarith, by linarith⟩

theorem antoineRho_nonneg (p : ℝ × ℝ × ℝ) : 0 ≤ antoineRho p :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem antoineRho_gt_of_mem_nbhd {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) : 5 / 8 < antoineRho p := by
  rw [mem_antoineNbhd_iff, antoineW_normSq] at hp
  nlinarith [sq_nonneg p.2.2]

theorem antoineW_norm_gt_of_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) : 1 / 8 < ‖antoineW p‖ := by
  obtain ⟨-, hp⟩ := hp
  rw [mem_antoineLink_iff] at hp
  by_contra hc
  push Not at hc
  have h2 := antoineW_normSq p
  have hn : ‖antoineW p‖ ^ 2 ≤ 1 / 64 := by
    have := norm_nonneg (antoineW p); nlinarith
  have ha : (antoineRho p - 7 / 8) ^ 2 ≤ 1 / 64 := by nlinarith [sq_nonneg p.2.2]
  have hb : p.2.2 ^ 2 ≤ 1 / 64 := by nlinarith [sq_nonneg (antoineRho p - 7 / 8)]
  exact hp ⟨abs_le.2 ⟨by nlinarith, by nlinarith⟩, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩


/-- `max(|cos α|, |sin α|)`, the square radius of the unit vector of angle `α`. -/
def antoineM (α : ℝ) : ℝ := max |Real.cos α| |Real.sin α|

theorem antoineM_pos (α : ℝ) : 0 < antoineM α := by
  by_contra h
  push Not at h
  have h1 : |Real.cos α| ≤ 0 := (le_max_left _ _).trans h
  have h2 : |Real.sin α| ≤ 0 := (le_max_right _ _).trans h
  have := Real.sin_sq_add_cos_sq α
  have e1 : Real.cos α = 0 := abs_nonpos_iff.1 h1
  have e2 : Real.sin α = 0 := abs_nonpos_iff.1 h2
  rw [e1, e2] at this; norm_num at this

theorem continuous_antoineM : Continuous antoineM := by unfold antoineM; fun_prop

/-- The parametrisation of the torus `|W| = 3/14` of the collar by the two angles. -/
def antoineE (α β : ℝ) : ℝ × ℝ × ℝ :=
  ((7 / 8 + 3 / 14 * Real.cos β) / antoineM α * Real.cos α,
    (7 / 8 + 3 / 14 * Real.cos β) / antoineM α * Real.sin α, 3 / 14 * Real.sin β)

theorem antoineRho_smul (r α : ℝ) (hr : 0 ≤ r) :
    max |r * Real.cos α| |r * Real.sin α| = r * antoineM α := by
  rw [abs_mul, abs_mul, abs_of_nonneg hr, antoineM, mul_max_of_nonneg _ _ hr]

theorem antoineRho_E (α β : ℝ) : antoineRho (antoineE α β) = 7 / 8 + 3 / 14 * Real.cos β := by
  have hm := antoineM_pos α
  have hr : 0 ≤ (7 / 8 + 3 / 14 * Real.cos β) / antoineM α := by
    have := Real.neg_one_le_cos β
    exact div_nonneg (by linarith) hm.le
  show max |_ * Real.cos α| |_ * Real.sin α| = _
  rw [antoineRho_smul _ _ hr, div_mul_cancel₀ _ hm.ne']

theorem antoineW_E (α β : ℝ) :
    antoineW (antoineE α β) = (3 / 14 : ℂ) * Complex.exp (β * Complex.I) := by
  rw [antoineW, antoineRho_E, Complex.exp_mul_I]
  apply Complex.ext <;> simp [antoineE]

theorem antoineE_mem (α β : ℝ) : antoineE α β ∈ antoineA0 := by
  have hW : ‖antoineW (antoineE α β)‖ = 3 / 14 := by
    rw [antoineW_E, norm_mul, Complex.norm_exp_ofReal_mul_I]; norm_num
  refine ⟨?_, fun hL => ?_⟩
  · rw [mem_antoineNbhd_iff, hW]; norm_num
  · rw [mem_antoineLink_iff] at hL
    have h2 := antoineW_normSq (antoineE α β)
    rw [hW] at h2
    obtain ⟨h3, h4⟩ := hL
    have h5 : (antoineRho (antoineE α β) - 7 / 8) ^ 2 ≤ 1 / 64 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (antoineRho (antoineE α β) - 7 / 8)]
    have h6 : (antoineE α β).2.2 ^ 2 ≤ 1 / 64 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (antoineE α β).2.2]
    nlinarith

theorem continuous_antoineE : Continuous fun q : ℝ × ℝ => antoineE q.1 q.2 := by
  have hm : Continuous fun q : ℝ × ℝ => antoineM q.1 := continuous_antoineM.comp continuous_fst
  have hd : Continuous fun q : ℝ × ℝ => (7 / 8 + 3 / 14 * Real.cos q.2) / antoineM q.1 :=
    (by fun_prop : Continuous fun q : ℝ × ℝ => 7 / 8 + 3 / 14 * Real.cos q.2).div hm
      fun q => (antoineM_pos q.1).ne'
  unfold antoineE
  fun_prop

/-- A point with longitudinal polar coordinates `r e^{iα}` (`r > 0`) and meridional coordinate
`(3/14) e^{iβ}` is `antoineE α β`. -/
theorem antoineE_eq_of {q : ℝ × ℝ × ℝ} {r α β : ℝ} (hr : 0 < r) (h1 : q.1 = r * Real.cos α)
    (h2 : q.2.1 = r * Real.sin α) (h3 : antoineRho q = 7 / 8 + 3 / 14 * Real.cos β)
    (h4 : q.2.2 = 3 / 14 * Real.sin β) : antoineE α β = q := by
  have hρ : antoineRho q = r * antoineM α := by
    show max |q.1| |q.2.1| = _
    rw [h1, h2, antoineRho_smul _ _ hr.le]
  have hm := antoineM_pos α
  have e : (7 / 8 + 3 / 14 * Real.cos β) / antoineM α = r := by
    rw [← h3, hρ, mul_div_cancel_right₀ _ hm.ne']
  obtain ⟨q1, q2, q3⟩ := q
  simp only at h1 h2 h4
  simp only [antoineE, e, h1, h2, h4]

/-- Scaling the meridional coordinate by `λ`, keeping the longitudinal direction. -/
def antoineScale (p : ℝ × ℝ × ℝ) (l : ℝ) : ℝ × ℝ × ℝ :=
  (p.1 * ((7 / 8 + l * (antoineRho p - 7 / 8)) / antoineRho p),
    p.2.1 * ((7 / 8 + l * (antoineRho p - 7 / 8)) / antoineRho p), l * p.2.2)

theorem antoineRho_scale {p : ℝ × ℝ × ℝ} (hp : 0 < antoineRho p) {l : ℝ}
    (hl : 0 ≤ 7 / 8 + l * (antoineRho p - 7 / 8)) :
    antoineRho (antoineScale p l) = 7 / 8 + l * (antoineRho p - 7 / 8) := by
  have hσ : 0 ≤ (7 / 8 + l * (antoineRho p - 7 / 8)) / antoineRho p := div_nonneg hl hp.le
  show max |p.1 * _| |p.2.1 * _| = _
  rw [abs_mul, abs_mul, abs_of_nonneg hσ, ← max_mul_of_nonneg _ _ hσ]
  show antoineRho p * _ = _
  field_simp

theorem antoineW_scale {p : ℝ × ℝ × ℝ} (hp : 0 < antoineRho p) {l : ℝ}
    (hl : 0 ≤ 7 / 8 + l * (antoineRho p - 7 / 8)) :
    antoineW (antoineScale p l) = (l : ℂ) * antoineW p := by
  rw [antoineW, antoineRho_scale hp hl, antoineW]
  apply Complex.ext <;> simp [antoineScale]

theorem antoineScale_one {p : ℝ × ℝ × ℝ} (hp : 0 < antoineRho p) : antoineScale p 1 = p := by
  obtain ⟨a, b, c⟩ := p
  simp only [antoineScale, one_mul, add_sub_cancel, div_self hp.ne', mul_one]

theorem antoineScale_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) {l : ℝ} (hl : 0 < l)
    (hl1 : l * ‖antoineW p‖ < 1 / 4) (hl2 : 1 ≤ l ∨ 3 / 14 ≤ l * ‖antoineW p‖) :
    antoineScale p l ∈ antoineA0 := by
  have hρ := antoineRho_gt_of_mem_nbhd hp.1
  have hW := antoineW_norm_gt_of_mem hp
  have hu : |antoineRho p - 7 / 8| ≤ ‖antoineW p‖ := by
    have := antoineW_normSq p
    exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg p.2.2]) (norm_nonneg _) |>.elim
      (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
  have hpos : 0 ≤ 7 / 8 + l * (antoineRho p - 7 / 8) := by
    have : |l * (antoineRho p - 7 / 8)| < 1 / 4 := by
      rw [abs_mul, abs_of_pos hl]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hu hl.le) hl1
    rw [abs_lt] at this; linarith
  have hWs : ‖antoineW (antoineScale p l)‖ = l * ‖antoineW p‖ := by
    rw [antoineW_scale (by linarith) hpos, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hl]
  refine ⟨?_, fun hL => ?_⟩
  · rw [mem_antoineNbhd_iff, hWs]
    have := mul_nonneg hl.le (norm_nonneg (antoineW p))
    nlinarith
  · rw [mem_antoineLink_iff, antoineRho_scale (by linarith) hpos] at hL
    obtain ⟨h3, h4⟩ := hL
    simp only [antoineScale] at h4
    rw [add_sub_cancel_left] at h3
    rcases hl2 with hl2 | hl2
    · -- `λ ≥ 1`: the unscaled point was in the square already
      refine hp.2 ((mem_antoineLink_iff p).2 ⟨?_, ?_⟩)
      · rw [abs_mul, abs_of_pos hl] at h3
        nlinarith [abs_nonneg (antoineRho p - 7 / 8)]
      · rw [abs_mul, abs_of_pos hl] at h4
        nlinarith [abs_nonneg p.2.2]
    · have h2 := antoineW_normSq (antoineScale p l)
      rw [hWs, antoineRho_scale (by linarith) hpos, add_sub_cancel_left] at h2
      simp only [antoineScale] at h2
      have h5 : (l * (antoineRho p - 7 / 8)) ^ 2 ≤ 1 / 64 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (l * (antoineRho p - 7 / 8))]
      have h6 : (l * p.2.2) ^ 2 ≤ 1 / 64 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (l * p.2.2)]
      nlinarith

/-- The meridional factor `3/14 / |W|` retracting the collar onto the torus `|W| = 3/14`. -/
def antoineK (p : ℝ × ℝ × ℝ) : ℝ := 3 / 14 / ‖antoineW p‖

theorem antoineScale_K_eq {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) :
    antoineE (Complex.arg (antoineAng p)) (Complex.arg (antoineW p)) =
      antoineScale p (antoineK p) := by
  have hρ := antoineRho_gt_of_mem_nbhd hp.1
  have hW := antoineW_norm_gt_of_mem hp
  have hW0 : antoineW p ≠ 0 := fun h => by rw [h, norm_zero] at hW; norm_num at hW
  have hA0 : antoineAng p ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [antoineAng] at h1 h2
    have : antoineRho p = 0 := by simp [antoineRho, h1, h2]
    linarith
  have hk : 0 < antoineK p := div_pos (by norm_num) (by linarith)
  have hkW : antoineK p * ‖antoineW p‖ = 3 / 14 := div_mul_cancel₀ _ (by linarith)
  have hu : |antoineRho p - 7 / 8| ≤ ‖antoineW p‖ := by
    have := antoineW_normSq p
    exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg p.2.2]) (norm_nonneg _) |>.elim
      (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
  have hku : |antoineK p * (antoineRho p - 7 / 8)| ≤ 3 / 14 := by
    rw [abs_mul, abs_of_pos hk, ← hkW]; exact mul_le_mul_of_nonneg_left hu hk.le
  rw [abs_le] at hku
  have hpos : 0 ≤ 7 / 8 + antoineK p * (antoineRho p - 7 / 8) := by linarith
  have hσ : 0 < (7 / 8 + antoineK p * (antoineRho p - 7 / 8)) / antoineRho p :=
    div_pos (by linarith) (by linarith)
  have hWn : 0 < ‖antoineW p‖ := by linarith
  refine antoineE_eq_of (r := ‖antoineAng p‖ * ((7 / 8 + antoineK p * (antoineRho p - 7 / 8)) /
    antoineRho p)) (mul_pos (norm_pos_iff.2 hA0) hσ) ?_ ?_ ?_ ?_
  · show p.1 * _ = _
    rw [mul_comm ‖antoineAng p‖, mul_assoc, Complex.norm_mul_cos_arg]
    simp [antoineAng]; ring
  · show p.2.1 * _ = _
    rw [mul_comm ‖antoineAng p‖, mul_assoc, Complex.norm_mul_sin_arg]
    simp [antoineAng]; ring
  · rw [antoineRho_scale (by linarith) hpos, Complex.cos_arg hW0]
    simp only [antoineW, antoineK, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
    field_simp
  · rw [Complex.sin_arg]
    simp only [antoineScale, antoineW, antoineK, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
      add_zero]
    field_simp


theorem antoineK_pos {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) : 0 < antoineK p :=
  div_pos (by norm_num) ((antoineW_norm_gt_of_mem hp).trans' (by norm_num))

theorem antoineK_mul {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) : antoineK p * ‖antoineW p‖ = 3 / 14 :=
  div_mul_cancel₀ _ ((antoineW_norm_gt_of_mem hp).trans' (by norm_num)).ne'

/-- The interpolation `(1 - s) + s K` between `1` and the retraction factor keeps a point of the
collar in the collar. -/
theorem antoineScale_interp_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : antoineScale p (1 - s + s * antoineK p) ∈ antoineA0 := by
  have hk := antoineK_pos hp
  have hkW := antoineK_mul hp
  have hW := antoineW_norm_gt_of_mem hp
  have hWlt : ‖antoineW p‖ < 1 / 4 := by
    have h := (mem_antoineNbhd_iff p).1 hp.1
    nlinarith [norm_nonneg (antoineW p)]
  have e : (1 - s + s * antoineK p) * ‖antoineW p‖ = (1 - s) * ‖antoineW p‖ + s * (3 / 14) := by
    rw [← hkW]; ring
  refine antoineScale_mem hp (by nlinarith) (by rw [e]; nlinarith) ?_
  rcases le_or_gt 1 (antoineK p) with h | h
  · left; nlinarith
  · right
    rw [e]
    have : 3 / 14 < ‖antoineW p‖ := by
      by_contra hc; push Not at hc
      have : 1 ≤ antoineK p := by
        rw [antoineK, le_div_iff₀ (by linarith)]; linarith
      linarith
    nlinarith

/-- The collar `N ∖ L` is path-connected: every point joins the torus `|W| = 3/14` by scaling
`W`, and the torus is the image of `ℝ²` (`GX.antoineE`). -/
theorem isPathConnected_antoineA0 : IsPathConnected antoineA0 := by
  have hR : IsPathConnected (range fun q : ℝ × ℝ => antoineE q.1 q.2) :=
    isPathConnected_range continuous_antoineE
  have hRA : (range fun q : ℝ × ℝ => antoineE q.1 q.2) ⊆ antoineA0 := by
    rintro _ ⟨q, rfl⟩; exact antoineE_mem _ _
  refine ⟨antoineE 0 0, antoineE_mem 0 0, fun y hy => ?_⟩
  have hρ := antoineRho_gt_of_mem_nbhd hy.1
  let γ : Path y (antoineScale y (antoineK y)) :=
    { toFun := fun s => antoineScale y (1 - (s : ℝ) + (s : ℝ) * antoineK y)
      continuous_toFun := by unfold antoineScale; fun_prop
      source' := by simp only [Icc.coe_zero, sub_zero, zero_mul, add_zero]; exact antoineScale_one (by linarith)
      target' := by simp only [Icc.coe_one, sub_self, one_mul, zero_add] }
  have h1 : JoinedIn antoineA0 y (antoineScale y (antoineK y)) :=
    ⟨γ, fun s => antoineScale_interp_mem hy s.2.1 s.2.2⟩
  have h2 : JoinedIn antoineA0 (antoineE 0 0) (antoineScale y (antoineK y)) := by
    rw [← antoineScale_K_eq hy]
    exact (hR.joinedIn _ ⟨(0, 0), rfl⟩ _ ⟨(_, _), rfl⟩).mono hRA
  exact h2.trans h1.symm

/-- The collar of the `j`-th link is the image of `GX.antoineA0`. -/
theorem antoineA1_eq (j : Fin 64) :
    antoineA1 j = (antoineStereo ∘ antoineMap j) '' antoineA0 := by
  rw [antoineA1, antoineN1, antoineL1, ← image_comp, ← image_comp, antoineA0,
    image_sdiff (antoineStereo_injective.comp (antoineMap_injective j))]

/-- `collar_conn` of `GX.AntoineFirstGeneration`. -/
theorem antoine_collar_conn (j : Fin 64) : IsPathConnected (antoineA1 j) := by
  rw [antoineA1_eq]
  exact isPathConnected_antoineA0.image (continuous_antoineStereo.comp (continuous_antoineMap j))


/-! ### The collar: classification of loops by the two windings -/

/-- `f` has an `exp`-lift whose total increment is `n · 2πi`. -/
def AntoineLiftWind (f : I → ℂ) (n : ℤ) : Prop :=
  ∃ Γ : C(I, ℂ), (∀ t, Complex.exp (Γ t) = f t) ∧ Γ 1 = Γ 0 + n * (2 * Real.pi * Complex.I)

theorem antoineLiftWind_cWinding {z : CStar} (γ : Path z z) :
    AntoineLiftWind (fun t => (γ t : ℂ)) (cWinding γ) := by
  obtain ⟨Γ, hΓ⟩ := exists_expLift γ.toContinuousMap
  exact ⟨Γ, hΓ, cWinding_spec γ hΓ⟩

theorem AntoineLiftWind.congr {f g : I → ℂ} {n : ℤ} (h : AntoineLiftWind f n) (e : ∀ t, f t = g t) :
    AntoineLiftWind g n := by
  obtain ⟨Γ, h1, h2⟩ := h
  exact ⟨Γ, fun t => (h1 t).trans (e t), h2⟩

/-- Two lifts of loops with equal winding, through the same base value, can be chosen with
equal ends. -/
theorem AntoineLiftWind.align {f g : I → ℂ} {n : ℤ} (hf : AntoineLiftWind f n)
    (hg : AntoineLiftWind g n) (h0 : f 0 = g 0) :
    ∃ Γf Γg : C(I, ℂ), (∀ t, Complex.exp (Γf t) = f t) ∧ (∀ t, Complex.exp (Γg t) = g t) ∧
      Γf 0 = Γg 0 ∧ Γf 1 = Γg 1 := by
  obtain ⟨Γ₁, h1, e1⟩ := hf
  obtain ⟨Γ₂, h2, e2⟩ := hg
  refine ⟨Γ₁, ⟨fun t => Γ₂ t + (Γ₁ 0 - Γ₂ 0), by fun_prop⟩, h1, fun t => ?_, ?_, ?_⟩
  · show Complex.exp (Γ₂ t + (Γ₁ 0 - Γ₂ 0)) = g t
    have hne : Complex.exp (Γ₂ 0) ≠ 0 := Complex.exp_ne_zero _
    rw [Complex.exp_add, Complex.exp_sub, h1, h2, h2, h0, div_self (h2 0 ▸ hne), mul_one]
  · show Γ₁ 0 = Γ₂ 0 + (Γ₁ 0 - Γ₂ 0); ring
  · show Γ₁ 1 = Γ₂ 1 + (Γ₁ 0 - Γ₂ 0); rw [e1, e2]; ring

theorem antoineAng_ne_zero {p : ℝ × ℝ × ℝ} (hp : 0 < antoineRho p) : antoineAng p ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [antoineAng] at h1 h2
  have : antoineRho p = 0 := by simp [antoineRho, h1, h2]
  linarith

theorem antoineW_ne_zero {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) : antoineW p ≠ 0 := fun h => by
  have := antoineW_norm_gt_of_mem hp; rw [h, norm_zero] at this; norm_num at this

/-- The retraction of the collar onto the torus, in polar form (any angles). -/
theorem antoineScale_K_eq_of {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineA0) {α β : ℝ}
    (hα1 : p.1 = ‖antoineAng p‖ * Real.cos α) (hα2 : p.2.1 = ‖antoineAng p‖ * Real.sin α)
    (hβ1 : antoineRho p - 7 / 8 = ‖antoineW p‖ * Real.cos β)
    (hβ2 : p.2.2 = ‖antoineW p‖ * Real.sin β) :
    antoineE α β = antoineScale p (antoineK p) := by
  have hρ := antoineRho_gt_of_mem_nbhd hp.1
  have hW := antoineW_norm_gt_of_mem hp
  have hk := antoineK_pos hp
  have hkW := antoineK_mul hp
  have hu : |antoineRho p - 7 / 8| ≤ ‖antoineW p‖ := by
    have := antoineW_normSq p
    exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg p.2.2]) (norm_nonneg _) |>.elim
      (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
  have hku : |antoineK p * (antoineRho p - 7 / 8)| ≤ 3 / 14 := by
    rw [abs_mul, abs_of_pos hk, ← hkW]; exact mul_le_mul_of_nonneg_left hu hk.le
  rw [abs_le] at hku
  have hpos : 0 ≤ 7 / 8 + antoineK p * (antoineRho p - 7 / 8) := by linarith
  have hσ : 0 < (7 / 8 + antoineK p * (antoineRho p - 7 / 8)) / antoineRho p :=
    div_pos (by linarith) (by linarith)
  refine antoineE_eq_of (r := ‖antoineAng p‖ * ((7 / 8 + antoineK p * (antoineRho p - 7 / 8)) /
    antoineRho p)) (mul_pos (norm_pos_iff.2 (antoineAng_ne_zero (by linarith))) hσ) ?_ ?_ ?_ ?_
  · show p.1 * _ = _
    rw [hα1]; ring
  · show p.2.1 * _ = _
    rw [hα2]; ring
  · rw [antoineRho_scale (by linarith) hpos, hβ1, ← mul_assoc, hkW]
  · show antoineK p * p.2.2 = _
    rw [hβ2, ← mul_assoc, hkW]

theorem antoine_polar_of_exp {w : ℂ} {Γ : ℂ} (h : Complex.exp Γ = w) :
    w.re = ‖w‖ * Real.cos Γ.im ∧ w.im = ‖w‖ * Real.sin Γ.im := by
  rw [← h, Complex.norm_exp, Complex.exp_re, Complex.exp_im]
  exact ⟨rfl, rfl⟩

/-- The retracted loop `R ∘ δ` of a loop of the collar based on the torus `|W| = 3/14`. -/
def antoineRetr (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := antoineScale p (antoineK p)

theorem antoineW_merPt : antoineW antoineMerPt = 3 / 14 := by
  have : antoineRho antoineMerPt = 61 / 56 := by
    simp only [antoineRho, antoineMerPt, abs_zero]
    rw [abs_of_pos (by norm_num), max_eq_right (by norm_num)]; norm_num
  rw [antoineW, this]; simp [antoineMerPt]; norm_num

theorem antoineK_merPt : antoineK antoineMerPt = 1 := by
  rw [antoineK, antoineW_merPt]; norm_num

theorem antoineRho_merPt : antoineRho antoineMerPt = 61 / 56 := by
  simp only [antoineRho, antoineMerPt, abs_zero]
  rw [abs_of_pos (by norm_num), max_eq_right (by norm_num)]; norm_num

theorem antoineMerPt_mem : antoineMerPt ∈ antoineA0 := by
  have := antoineMeridian_mem_nbhd 0
  refine ⟨by simpa using this, fun h => ?_⟩
  have := antoineMeridian_not_mem 0
  simp at this
  exact this h

theorem antoineRetr_merPt : antoineRetr antoineMerPt = antoineMerPt := by
  rw [antoineRetr, antoineK_merPt]; exact antoineScale_one (by rw [antoineRho_merPt]; norm_num)

/-- Continuity of the scaling along a loop of the collar. -/
theorem antoine_continuous_scale_along {δ : C(I, ℝ × ℝ × ℝ)} (hδ : ∀ t, δ t ∈ antoineA0)
    {l : I × I → ℝ} (hl : Continuous l) :
    Continuous fun z : I × I => antoineScale (δ z.2) (l z) := by
  have hρ : Continuous fun z : I × I => antoineRho (δ z.2) :=
    continuous_antoineRho.comp (δ.continuous.comp continuous_snd)
  have hρ0 : ∀ z : I × I, antoineRho (δ z.2) ≠ 0 := fun z =>
    (antoineRho_gt_of_mem_nbhd (hδ z.2).1).trans' (by norm_num) |>.ne'
  have hσ : Continuous fun z : I × I =>
      (7 / 8 + l z * (antoineRho (δ z.2) - 7 / 8)) / antoineRho (δ z.2) :=
    (continuous_const.add (hl.mul (hρ.sub continuous_const))).div hρ hρ0
  have hd : Continuous fun z : I × I => δ z.2 := δ.continuous.comp continuous_snd
  exact ((continuous_fst.comp hd).mul hσ).prodMk
    (((continuous_fst.comp (continuous_snd.comp hd)).mul hσ).prodMk
      (hl.mul (continuous_snd.comp (continuous_snd.comp hd))))

theorem antoine_continuous_K_along {δ : C(I, ℝ × ℝ × ℝ)} (hδ : ∀ t, δ t ∈ antoineA0) :
    Continuous fun t => antoineK (δ t) :=
  continuous_const.div (continuous_norm.comp (continuous_antoineW.comp δ.continuous))
    fun t => ((antoineW_norm_gt_of_mem (hδ t)).trans' (by norm_num)).ne'

theorem antoine_continuous_retr_along {δ : C(I, ℝ × ℝ × ℝ)} (hδ : ∀ t, δ t ∈ antoineA0) :
    Continuous fun t => antoineRetr (δ t) := by
  have hK := antoine_continuous_K_along hδ
  have := antoine_continuous_scale_along hδ (l := fun z => antoineK (δ z.2))
    (hK.comp (continuous_snd : Continuous fun z : I × I => z.2))
  exact this.comp ((continuous_const : Continuous fun _ : I => (0 : I)).prodMk continuous_id)

/-- The retracted loop `R ∘ δ`, on the torus `|W| = 3/14`. -/
def antoineRetrLoop (δ : Path antoineMerPt antoineMerPt) (hδ : ∀ t, δ t ∈ antoineA0) :
    Path antoineMerPt antoineMerPt where
  toFun t := antoineRetr (δ t)
  continuous_toFun := antoine_continuous_retr_along (δ := δ.toContinuousMap) hδ
  source' := by simp [antoineRetr_merPt]
  target' := by simp [antoineRetr_merPt]

/-- `δ ≃ R ∘ δ` in the collar. -/
theorem antoine_homotopicIn_retr {δ : Path antoineMerPt antoineMerPt}
    (hδ : ∀ t, δ t ∈ antoineA0) : HomotopicIn antoineA0 δ (antoineRetrLoop δ hδ) := by
  have hK := antoine_continuous_K_along (δ := δ.toContinuousMap) hδ
  have hc := antoine_continuous_scale_along (δ := δ.toContinuousMap) hδ
    (l := fun z => 1 - (z.1 : ℝ) + (z.1 : ℝ) * antoineK (δ z.2))
    (by have := hK.comp (continuous_snd : Continuous fun z : I × I => z.2); fun_prop)
  refine ⟨{ toFun := fun z => antoineScale (δ z.2) (1 - (z.1 : ℝ) + (z.1 : ℝ) * antoineK (δ z.2))
            continuous_toFun := hc
            map_zero_left := fun t => ?_
            map_one_left := fun t => ?_
            prop' := fun s t ht => ?_ }, fun z => ?_⟩
  · simp only [Icc.coe_zero, sub_zero, zero_mul, add_zero]
    exact antoineScale_one ((antoineRho_gt_of_mem_nbhd (hδ t).1).trans' (by norm_num))
  · simp only [Icc.coe_one, sub_self, one_mul, zero_add]; rfl
  · rcases ht with rfl | rfl
    · show antoineScale (δ 0) _ = δ 0
      rw [δ.source, antoineK_merPt, mul_one, sub_add_cancel]
      exact antoineScale_one (by rw [antoineRho_merPt]; norm_num)
    · show antoineScale (δ 1) _ = δ 1
      rw [δ.target, antoineK_merPt, mul_one, sub_add_cancel]
      exact antoineScale_one (by rw [antoineRho_merPt]; norm_num)
  · exact antoineScale_interp_mem (hδ z.2) z.1.2.1 z.1.2.2

/-- The retracted loop through lifts of its two coordinates. -/
theorem antoineRetrLoop_eq {δ : Path antoineMerPt antoineMerPt} (hδ : ∀ t, δ t ∈ antoineA0)
    {ΓA ΓW : C(I, ℂ)} (hA : ∀ t, Complex.exp (ΓA t) = antoineAng (δ t))
    (hW : ∀ t, Complex.exp (ΓW t) = antoineW (δ t)) (t : I) :
    antoineRetrLoop δ hδ t = antoineE (ΓA t).im (ΓW t).im := by
  obtain ⟨a1, a2⟩ := antoine_polar_of_exp (hA t)
  obtain ⟨b1, b2⟩ := antoine_polar_of_exp (hW t)
  simp only [antoineAng, antoineW, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, Complex.add_im,
    Complex.mul_im, mul_one, zero_add, add_zero] at a1 a2 b1 b2
  exact (antoineScale_K_eq_of (hδ t) a1 a2 b1 b2).symm

/-- **The collar is classified by the two windings**: two loops of the collar `N ∖ L` based at the
meridian's base point, with equal longitudinal and equal meridional windings, are homotopic in
the collar (`π₁(T² × I) = ℤ²`). -/
theorem antoine_collar_classify {δ₁ δ₂ : Path antoineMerPt antoineMerPt}
    (h₁ : ∀ t, δ₁ t ∈ antoineA0) (h₂ : ∀ t, δ₂ t ∈ antoineA0) {a b : ℤ}
    (hA₁ : AntoineLiftWind (fun t => antoineAng (δ₁ t)) a)
    (hA₂ : AntoineLiftWind (fun t => antoineAng (δ₂ t)) a)
    (hW₁ : AntoineLiftWind (fun t => antoineW (δ₁ t)) b)
    (hW₂ : AntoineLiftWind (fun t => antoineW (δ₂ t)) b) : HomotopicIn antoineA0 δ₁ δ₂ := by
  obtain ⟨A₁, A₂, eA₁, eA₂, A0, A1⟩ := hA₁.align hA₂ (by simp)
  obtain ⟨W₁, W₂, eW₁, eW₂, W0, W1⟩ := hW₁.align hW₂ (by simp)
  refine (antoine_homotopicIn_retr h₁).trans (HomotopicIn.trans ?_
    (antoine_homotopicIn_retr h₂).symm)
  have hg : Continuous fun z : I × I =>
      ((1 - (z.1 : ℝ)) * (A₁ z.2).im + (z.1 : ℝ) * (A₂ z.2).im,
        (1 - (z.1 : ℝ)) * (W₁ z.2).im + (z.1 : ℝ) * (W₂ z.2).im) := by fun_prop
  have hc := continuous_antoineE.comp hg
  refine ⟨{ toFun := fun z => antoineE ((1 - (z.1 : ℝ)) * (A₁ z.2).im + (z.1 : ℝ) * (A₂ z.2).im)
              ((1 - (z.1 : ℝ)) * (W₁ z.2).im + (z.1 : ℝ) * (W₂ z.2).im)
            continuous_toFun := hc
            map_zero_left := fun t => ?_
            map_one_left := fun t => ?_
            prop' := fun s t ht => ?_ }, fun z => antoineE_mem _ _⟩
  · simp only [Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact (antoineRetrLoop_eq h₁ eA₁ eW₁ t).symm
  · simp only [Icc.coe_one, sub_self, one_mul, zero_mul, zero_add]
    exact (antoineRetrLoop_eq h₂ eA₂ eW₂ t).symm
  · rcases ht with rfl | rfl
    · show antoineE _ _ = antoineRetrLoop δ₁ h₁ 0
      rw [antoineRetrLoop_eq h₁ eA₁ eW₁, ← A0, ← W0]; congr 1 <;> ring
    · show antoineE _ _ = antoineRetrLoop δ₁ h₁ 1
      rw [antoineRetrLoop_eq h₁ eA₁ eW₁, ← A1, ← W1]; congr 1 <;> ring


/-! ### Windings: uniqueness, existence, homotopy invariance, powers -/

theorem AntoineLiftWind.unique {f : I → ℂ} {n m : ℤ} (hn : AntoineLiftWind f n)
    (hm : AntoineLiftWind f m) : n = m := by
  obtain ⟨Γ, h1, e1⟩ := hn
  obtain ⟨Γ', h2, e2⟩ := hm
  have h := expLift_sub_const (Γ := Γ) (Γ' := Γ') (fun t => by rw [h1, h2]) 1
  rw [e2, e1] at h
  have h' : ((m : ℂ) - n) * (2 * Real.pi * Complex.I) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h'' | h''
  · exact_mod_cast (sub_eq_zero.1 h'').symm
  · exact absurd h'' Complex.two_pi_I_ne_zero

theorem antoine_exists_liftWind {f : I → ℂ} (hf : Continuous f) (h0 : ∀ t, f t ≠ 0)
    (h01 : f 1 = f 0) : ∃ n, AntoineLiftWind f n := by
  obtain ⟨Γ, hΓ⟩ := exists_expLift ⟨fun t => (⟨f t, h0 t⟩ : CStar), hf.subtype_mk _⟩
  have e : Complex.exp (Γ 1) = Complex.exp (Γ 0) := by
    have a := hΓ 1; have b := hΓ 0
    simp only [ContinuousMap.coe_mk] at a b
    rw [a, b, h01]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
  exact ⟨n, Γ, fun t => hΓ t, hn⟩

/-- The winding of `F` along a loop null-homotopic in a set where `F` is continuous and nonzero
is `0`. -/
theorem antoineLiftWind_of_homotopicIn_refl {X : Type*} [TopologicalSpace X] {O : Set X} {x : X}
    {δ : Path x x} (h : HomotopicIn O δ (Path.refl x)) {F : X → ℂ} (hF : ContinuousOn F O)
    (hF0 : ∀ y ∈ O, F y ≠ 0) : AntoineLiftWind (fun t => F (δ t)) 0 := by
  rw [homotopicIn_iff] at h
  obtain ⟨h1, h2, hom⟩ := h
  let Θ : C(O, CStar) := ⟨fun y => ⟨F y, hF0 y y.2⟩, hF.restrict.subtype_mk _⟩
  have hw := cWinding_homotopic (Path.Homotopic.map hom Θ)
  have e2 : (pathToSub (Path.refl x) h2).map Θ.continuous = Path.refl _ := by ext; rfl
  rw [e2, cWinding_pathRefl] at hw
  have := antoineLiftWind_cWinding ((pathToSub δ h1).map Θ.continuous)
  rw [hw] at this
  exact this

/-- Windings of powers of a loop. -/
theorem antoineLiftWind_loopZPow {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    {γ : Path x x} (hγ : ∀ t, γ t ∈ S) {F : X → ℂ} (hF : ContinuousOn F S)
    (hF0 : ∀ y ∈ S, F y ≠ 0) {n : ℤ} (hn : AntoineLiftWind (fun t => F (γ t)) n) (a : ℤ) :
    AntoineLiftWind (fun t => F (loopZPow γ a t)) (a * n) := by
  let Θ : C(S, CStar) := ⟨fun y => ⟨F y, hF0 y y.2⟩, hF.restrict.subtype_mk _⟩
  have hc := antoineLiftWind_cWinding ((pathToSub γ hγ).map Θ.continuous)
  have e := hc.unique hn
  have hγ' := loopZPow_mem hγ a
  have h2 := antoineLiftWind_cWinding ((pathToSub (loopZPow γ a) hγ').map Θ.continuous)
  rw [pathToSub_loopZPow hγ a hγ', loopZPow_map, cWinding_loopZPow, e] at h2
  refine h2.congr fun t => ?_
  rw [← loopZPow_map, ← pathToSub_loopZPow hγ a hγ']
  rfl

/-! ### The meridian in collar coordinates -/

theorem antoineRho_meridian (t : I) :
    antoineRho (antoineMeridian t) = 7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t) := by
  have hc1 : -1 ≤ Real.cos (2 * Real.pi * t) := Real.neg_one_le_cos _
  have hpos : 0 ≤ 7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t) := by linarith
  rw [antoineRho, antoineMeridian_apply]
  simp only [abs_zero]
  rw [abs_of_nonneg hpos, max_eq_right hpos]

theorem antoineW_meridian (t : I) :
    antoineW (antoineMeridian t) = (3 / 14 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t) := by
  rw [antoineW, antoineRho_meridian]
  have : (2 * Real.pi * Complex.I * (t : ℝ)) = ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I]
  apply Complex.ext <;> simp [antoineMeridian_apply] <;> ring

theorem antoineMeridian_mem_A0 (t : I) : antoineMeridian t ∈ antoineA0 :=
  ⟨antoineMeridian_mem_nbhd t, antoineMeridian_not_mem t⟩

theorem antoineAng_ne_zero_of_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) : antoineAng p ≠ 0 :=
  antoineAng_ne_zero ((antoineRho_gt_of_mem_nbhd hp).trans' (by norm_num))

theorem antoineLiftWind_meridian_W : AntoineLiftWind (fun t => antoineW (antoineMeridian t)) 1 := by
  refine ⟨⟨fun t => Complex.log (3 / 14) + 2 * Real.pi * Complex.I * (t : ℝ), by fun_prop⟩,
    fun t => ?_, ?_⟩
  · show Complex.exp (Complex.log (3 / 14) + _) = antoineW (antoineMeridian t)
    rw [Complex.exp_add, Complex.exp_log (by norm_num), antoineW_meridian]
  · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, add_zero, Int.cast_one, one_mul]

theorem antoineLiftWind_meridian_Ang :
    AntoineLiftWind (fun t => antoineAng (antoineMeridian t)) 0 := by
  have hslit : ∀ t, antoineAng (antoineMeridian t) ∈ Complex.slitPlane := fun t => by
    have hc1 : -1 ≤ Real.cos (2 * Real.pi * t) := Real.neg_one_le_cos _
    refine Or.inr ?_
    simp only [antoineAng, antoineMeridian_apply, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    linarith
  have hc : Continuous fun t => antoineAng (antoineMeridian t) :=
    continuous_antoineAng.comp antoineMeridian.continuous
  refine ⟨⟨fun t => Complex.log (antoineAng (antoineMeridian t)),
    continuous_iff_continuousAt.2 fun t => (hc.continuousAt).clog (hslit t)⟩,
    fun t => Complex.exp_log (antoineAng_ne_zero_of_mem (antoineMeridian_mem_nbhd t)), ?_⟩
  simp only [ContinuousMap.coe_mk, Path.source, Path.target, Int.cast_zero, zero_mul, add_zero]

/-! ### Pulling a collar loop of `S³` back to `ℝ³` -/

/-- The chart of the `j`-th tube, `(stereo ∘ g_j)⁻¹`. -/
def antoineChart (j : Fin 64) (y : Sphere3) : ℝ × ℝ × ℝ := antoineMapInv j (antoineStereoInv y)

theorem antoineChart_of_mem {j : Fin 64} {O : Set (ℝ × ℝ × ℝ)} {y : Sphere3}
    (hy : y ∈ antoineStereo '' (antoineMap j '' O)) :
    antoineChart j y ∈ O ∧ antoineStereo (antoineMap j (antoineChart j y)) = y := by
  obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hy
  simp only [antoineChart, antoineStereoInv_stereo, antoineMapInv_map]
  exact ⟨hq, trivial⟩

theorem continuousOn_antoineChart (j : Fin 64) (O : Set (ℝ × ℝ × ℝ)) :
    ContinuousOn (antoineChart j) (antoineStereo '' (antoineMap j '' O)) := by
  rintro _ ⟨q, -, rfl⟩
  exact ((continuous_antoineMapInv j).continuousAt.comp
    (continuousAt_antoineStereoInv (antoineStereo_three_lt q))).continuousWithinAt

/-- The pulled-back loop. -/
def antoinePull (j : Fin 64) (δ : Path (antoineX1 j) (antoineX1 j))
    (hδ : ∀ t, δ t ∈ antoineA1 j) : Path antoineMerPt antoineMerPt where
  toFun t := antoineChart j (δ t)
  continuous_toFun := by
    have h : ∀ t, δ t ∈ antoineStereo '' (antoineMap j '' antoineA0) := fun t => by
      rw [image_image]; exact (antoineA1_eq j) ▸ hδ t
    exact (continuousOn_antoineChart j antoineA0).comp_continuous δ.continuous h
  source' := by
    show antoineChart j (δ 0) = _
    rw [δ.source]; simp [antoineChart, antoineX1, antoineStereoInv_stereo, antoineMapInv_map]
  target' := by
    show antoineChart j (δ 1) = _
    rw [δ.target]; simp [antoineChart, antoineX1, antoineStereoInv_stereo, antoineMapInv_map]

theorem antoinePull_spec (j : Fin 64) (δ : Path (antoineX1 j) (antoineX1 j))
    (hδ : ∀ t, δ t ∈ antoineA1 j) (t : I) :
    antoinePull j δ hδ t ∈ antoineA0 ∧
      antoineStereo (antoineMap j (antoinePull j δ hδ t)) = δ t := by
  have h : δ t ∈ antoineStereo '' (antoineMap j '' antoineA0) := by
    rw [image_image]; exact (antoineA1_eq j) ▸ hδ t
  exact antoineChart_of_mem h

theorem antoineMu1_eq (j : Fin 64) :
    antoineMeridian.map (continuous_antoineStereo.comp (continuous_antoineMap j)) = antoineMu1 j := by
  rfl

/-- `collar_mer` of `GX.AntoineFirstGeneration`: a loop of the collar `Aⱼ` which is
null-homotopic in the tube `Nⱼ` is, in `Aⱼ`, a power of the meridian. -/
theorem antoine_collar_mer (j : Fin 64) (O : Set Sphere3) (hO : O ⊆ antoineN1 j)
    (δ : Path (antoineX1 j) (antoineX1 j)) (hδ : ∀ t, δ t ∈ antoineA1 j)
    (hnull : HomotopicIn O δ (Path.refl _)) :
    ∃ a : ℤ, HomotopicIn (antoineA1 j) δ (loopZPow (antoineMu1 j) a) := by
  set δ' := antoinePull j δ hδ
  have hδ' : ∀ t, δ' t ∈ antoineA0 := fun t => (antoinePull_spec j δ hδ t).1
  -- the longitudinal winding vanishes: `δ` is null in the tube
  have hA : AntoineLiftWind (fun t => antoineAng (δ' t)) 0 := by
    refine antoineLiftWind_of_homotopicIn_refl hnull (F := fun y => antoineAng (antoineChart j y))
      ?_ ?_
    · exact (continuous_antoineAng.comp_continuousOn
        (continuousOn_antoineChart j antoineNbhd)).mono hO
    · intro y hy
      exact antoineAng_ne_zero_of_mem (antoineChart_of_mem (hO hy)).1
  obtain ⟨b, hW⟩ := antoine_exists_liftWind (f := fun t => antoineW (δ' t))
    (continuous_antoineW.comp δ'.continuous) (fun t => antoineW_ne_zero (hδ' t))
    (by simp only [Path.source, Path.target])
  have hμ := antoineMeridian_mem_A0
  have hμA := antoineLiftWind_loopZPow hμ continuous_antoineAng.continuousOn
    (fun y hy => antoineAng_ne_zero_of_mem hy.1) antoineLiftWind_meridian_Ang b
  have hμW := antoineLiftWind_loopZPow hμ continuous_antoineW.continuousOn
    (fun y hy => antoineW_ne_zero hy) antoineLiftWind_meridian_W b
  rw [mul_zero] at hμA
  rw [mul_one] at hμW
  have hcl := antoine_collar_classify hδ' (loopZPow_mem hμ b) hA hμA hW hμW
  refine ⟨b, ?_⟩
  have hg := continuous_antoineStereo.comp (continuous_antoineMap j)
  have hmap := hcl.map hg (V := antoineA1 j) (fun q hq => by rw [antoineA1_eq]; exact ⟨q, hq, rfl⟩)
  refine hmap.of_eq ?_ ?_
  · exact Path.ext (funext fun t => (antoinePull_spec j δ hδ t).2)
  · rw [loopZPow_map, antoineMu1_eq]; rfl


/-! ### Windings under free homotopies -/

/-- **Free homotopy invariance** of the winding: a continuous family of loops of `ℂ ∖ 0` (the base
point may move) has constant winding (homotopy lifting through `exp`). -/
theorem AntoineLiftWind.of_freeHomotopy {G : I × I → ℂ} (hG : Continuous G)
    (hG0 : ∀ z, G z ≠ 0) (hloop : ∀ s, G (s, 1) = G (s, 0)) {n : ℤ}
    (h : AntoineLiftWind (fun t => G (0, t)) n) : AntoineLiftWind (fun t => G (1, t)) n := by
  obtain ⟨Γ, hΓ, e⟩ := h
  let H : C(I × I, CStar) := ⟨fun z => ⟨G z, hG0 z⟩, hG.subtype_mk _⟩
  have H_0 : ∀ a, H (0, a) = cExp (Γ a) := fun a => Subtype.ext (by
    show G (0, a) = Complex.exp (Γ a); rw [hΓ a])
  set Λ := isCoveringMap_cExp.liftHomotopy H Γ H_0
  have hΛ : ∀ z, Complex.exp (Λ z) = G z := fun z =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftHomotopy_lifts H Γ H_0) z)
  have hΛ0 : ∀ a, Λ (0, a) = Γ a := isCoveringMap_cExp.liftHomotopy_zero H Γ H_0
  have hd : (fun s : I => Λ (s, 1) - Λ (s, 0)) = fun _ => Λ (0, 1) - Λ (0, 0) := by
    refine isCoveringMap_cExp.eq_of_comp_eq (by fun_prop) continuous_const ?_ 0 rfl
    funext s
    refine Subtype.ext ?_
    simp only [comp_apply, cExp_apply, Complex.exp_sub, hΛ, hloop]
    rw [div_self (hG0 _), div_self (hG0 _)]
  refine ⟨⟨fun t => Λ (1, t), by fun_prop⟩, fun t => hΛ _, ?_⟩
  have := congrFun hd 1
  simp only [ContinuousMap.coe_mk]
  rw [hΛ0, hΛ0, e] at this
  linear_combination this

/-- Straight-line version: two loops of `ℂ` whose joining segments avoid `0` have equal
windings. -/
theorem AntoineLiftWind.of_segment {f g : I → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hf1 : f 1 = f 0) (hg1 : g 1 = g 0)
    (hne : ∀ t : I, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (1 - s) * f t + s * g t ≠ 0) {n : ℤ}
    (h : AntoineLiftWind f n) : AntoineLiftWind g n := by
  have := AntoineLiftWind.of_freeHomotopy (G := fun z : I × I => (1 - ((z.1 : ℝ) : ℂ)) * f z.2 +
      ((z.1 : ℝ) : ℂ) * g z.2) (by fun_prop)
    (fun z => by
      exact hne z.2 z.1 z.1.2.1 z.1.2.2)
    (fun s => by simp only [hf1, hg1]) (h.congr fun t => by simp)
  exact this.congr fun t => by simp

/-- Homotopy invariance of windings along a homotopy in a set where `F` is continuous and
nonzero. -/
theorem AntoineLiftWind.of_homotopicIn {X : Type*} [TopologicalSpace X] {O : Set X} {x : X}
    {γ γ' : Path x x} (h : HomotopicIn O γ γ') {F : X → ℂ} (hF : ContinuousOn F O)
    (hF0 : ∀ y ∈ O, F y ≠ 0) {n : ℤ} (hn : AntoineLiftWind (fun t => F (γ t)) n) :
    AntoineLiftWind (fun t => F (γ' t)) n := by
  rw [homotopicIn_iff] at h
  obtain ⟨h1, h2, hom⟩ := h
  let Θ : C(O, CStar) := ⟨fun y => ⟨F y, hF0 y y.2⟩, hF.restrict.subtype_mk _⟩
  have hw := cWinding_homotopic (Path.Homotopic.map hom Θ)
  have e1 := (antoineLiftWind_cWinding ((pathToSub γ h1).map Θ.continuous)).unique hn
  have := antoineLiftWind_cWinding ((pathToSub γ' h2).map Θ.continuous)
  rw [← hw, e1] at this
  exact this

/-! ### `Ψ` and `W` agree near the link -/

theorem antoinePsi_eq_W {p : ℝ × ℝ × ℝ} (hp : antoineSq p ≤ 2) : antoinePsi p = antoineW p := by
  have hρ0 := antoineRho_nonneg p
  have hS : antoineSq p = antoineRho p ^ 2 + p.2.2 ^ 2 := rfl
  have hρ2 : antoineRho p < 2 := by nlinarith [sq_nonneg p.2.2]
  have e1 : min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) = antoineRho p := by
    rw [max_eq_left (show antoineSq p - 2 ≤ 0 by linarith), add_zero]
    exact min_eq_right hρ2.le
  have e2 : max 0 (min 1 (3 - antoineSq p)) = 1 := by
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  rw [antoinePsi, e1, e2, mul_one, antoineW]

/-- Where `z² ≤ 6/5`, the segment from `Ψ p` to `W p` avoids `0` when `W p ≠ 0`. -/
theorem antoine_segment_Psi_W {p : ℝ × ℝ × ℝ} (hz : p.2.2 ^ 2 ≤ 6 / 5) (hW : antoineW p ≠ 0)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (1 - s) * antoinePsi p + s * antoineW p ≠ 0 := by
  rcases le_or_gt (antoineSq p) 2 with h | h
  · rw [antoinePsi_eq_W h]
    have : (1 - (s : ℂ)) * antoineW p + s * antoineW p = antoineW p := by ring
    rw [this]; exact hW
  · -- both real parts are positive
    have hS : antoineSq p = antoineRho p ^ 2 + p.2.2 ^ 2 := rfl
    have hρ0 := antoineRho_nonneg p
    have hρ : 7 / 8 < antoineRho p := by nlinarith
    intro h0
    have hre := congrArg Complex.re h0
    have hPre : (antoinePsi p).re =
        min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) - 7 / 8 := by simp [antoinePsi]
    have h1 : 0 < (antoinePsi p).re := by
      have : antoineRho p ≤ max |p.1| |p.2.1| + max 0 (antoineSq p - 2) :=
        le_add_of_nonneg_right (le_max_left _ _)
      have h2 : 7 / 8 < min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) :=
        lt_min (by norm_num) (by linarith)
      linarith
    have h2 : (antoineW p).re = antoineRho p - 7 / 8 := by simp [antoineW]
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.one_im, zero_mul, sub_zero, Complex.zero_re] at hre
    rw [h2] at hre
    have hb : 0 < antoineRho p - 7 / 8 := by linarith
    have hm : 0 < min (antoinePsi p).re (antoineRho p - 7 / 8) := lt_min h1 hb
    have e1 : (1 - s) * min (antoinePsi p).re (antoineRho p - 7 / 8) ≤ (1 - s) * (antoinePsi p).re :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have e2 : s * min (antoinePsi p).re (antoineRho p - 7 / 8) ≤ s * (antoineRho p - 7 / 8) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hs0
    linarith


/-! ### A longitude of the collar -/

/-- The angle `π/2 - 2πt` of the longitude. -/
def antoineLonAngle (t : I) : ℝ := Real.pi / 2 - 2 * Real.pi * t

theorem antoineM_lonAngle_one : antoineM (antoineLonAngle 1) = antoineM (antoineLonAngle 0) := by
  simp only [antoineM, antoineLonAngle, Icc.coe_one, Icc.coe_zero, mul_one, mul_zero, sub_zero,
    Real.cos_sub_two_pi, Real.sin_sub_two_pi]

theorem continuous_antoineLonAngle : Continuous antoineLonAngle := by
  unfold antoineLonAngle; fun_prop

theorem continuous_antoineE_comp {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => antoineE (f x) (g x) := by
  have h := continuous_antoineE.comp (hf.prodMk hg)
  exact h

theorem antoineE_pi_div_two : antoineE (Real.pi / 2) 0 = antoineMerPt := by
  have hM : antoineM (Real.pi / 2) = 1 := by
    rw [antoineM, Real.cos_pi_div_two, Real.sin_pi_div_two, abs_zero, abs_one]
    exact max_eq_right zero_le_one
  rw [antoineE, hM, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero,
    antoineMerPt]
  simp only [div_one, mul_zero, mul_one]

theorem antoineLonAngle_zero : antoineLonAngle 0 = Real.pi / 2 := by
  simp [antoineLonAngle]

theorem antoineE_lonAngle_one (β : ℝ) : antoineE (antoineLonAngle 1) β = antoineE (Real.pi / 2) β := by
  have e : antoineLonAngle 1 = Real.pi / 2 - 2 * Real.pi := by simp [antoineLonAngle]
  simp only [antoineE, antoineM, e, Real.cos_sub_two_pi, Real.sin_sub_two_pi]

/-- The longitude `t ↦ antoineE (π/2 - 2πt) 0` of the collar, based at the meridian's base point
(Ang-winding `-1`, W-winding `0`). -/
def antoineLon : Path antoineMerPt antoineMerPt where
  toFun t := antoineE (antoineLonAngle t) 0
  continuous_toFun := continuous_antoineE_comp continuous_antoineLonAngle continuous_const
  source' := by rw [antoineLonAngle_zero, antoineE_pi_div_two]
  target' := by rw [antoineE_lonAngle_one, antoineE_pi_div_two]

theorem antoineLon_apply (t : I) : antoineLon t =
    ((7 / 8 + 3 / 14) / antoineM (antoineLonAngle t) * Real.cos (antoineLonAngle t),
      (7 / 8 + 3 / 14) / antoineM (antoineLonAngle t) * Real.sin (antoineLonAngle t), 0) := by
  show antoineE _ 0 = _
  simp only [antoineE, Real.cos_zero, Real.sin_zero, mul_one, mul_zero]

theorem antoineLon_mem (t : I) : antoineLon t ∈ antoineA0 := antoineE_mem _ _

theorem antoine_cM_pos (t : I) : 0 < (7 / 8 + 3 / 14 : ℝ) / antoineM (antoineLonAngle t) :=
  div_pos (by norm_num) (antoineM_pos _)

theorem antoine_cM_ge (t : I) : (7 / 8 + 3 / 14 : ℝ) ≤ (7 / 8 + 3 / 14) / antoineM (antoineLonAngle t) := by
  have hm := antoineM_pos (antoineLonAngle t)
  have hm1 : antoineM (antoineLonAngle t) ≤ 1 :=
    max_le (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
  rw [le_div_iff₀ hm]; nlinarith

theorem continuous_antoine_cM : Continuous fun t : I =>
    (7 / 8 + 3 / 14 : ℝ) / antoineM (antoineLonAngle t) :=
  continuous_const.div (continuous_antoineM.comp continuous_antoineLonAngle)
    fun t => (antoineM_pos _).ne'

theorem antoineLiftWind_lon_Ang : AntoineLiftWind (fun t => antoineAng (antoineLon t)) (-1) := by
  have hc := continuous_antoine_cM
  refine ⟨⟨fun t => (Real.log ((7 / 8 + 3 / 14 : ℝ) / antoineM (antoineLonAngle t)) : ℂ) +
      (antoineLonAngle t : ℂ) * Complex.I, ?_⟩, fun t => ?_, ?_⟩
  · have := hc.log fun t => (antoine_cM_pos t).ne'
    have := continuous_antoineLonAngle
    fun_prop
  · show Complex.exp (_ + _) = antoineAng (antoineLon t)
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (antoine_cM_pos t), Complex.exp_mul_I,
      antoineLon_apply, antoineAng]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  · simp only [ContinuousMap.coe_mk]
    rw [antoineM_lonAngle_one]
    simp only [antoineLonAngle, Icc.coe_one, Icc.coe_zero, mul_one, mul_zero, sub_zero]
    push_cast; ring

theorem antoineLiftWind_lon_W : AntoineLiftWind (fun t => antoineW (antoineLon t)) 0 := by
  refine ⟨ContinuousMap.const _ (Complex.log (3 / 14)), fun t => ?_, by simp⟩
  show Complex.exp (Complex.log (3 / 14)) = antoineW (antoineE _ 0)
  rw [Complex.exp_log (by norm_num), antoineW_E]; simp


/-! ### The longitude of a link links its successor once -/

/-- The radius factor `c / M(α)` of the longitude. -/
def antoineCM (t : I) : ℝ := (7 / 8 + 3 / 14 : ℝ) / antoineM (antoineLonAngle t)

theorem antoineCM_one : antoineCM 1 = antoineCM 0 := by rw [antoineCM, antoineCM, antoineM_lonAngle_one]

theorem antoineCM_pos (t : I) : 0 < antoineCM t := antoine_cM_pos t

theorem antoineCM_ge (t : I) : (7 / 8 + 3 / 14 : ℝ) ≤ antoineCM t := antoine_cM_ge t

theorem antoineCM_abs_cos_le (t : I) : |antoineCM t * Real.cos (antoineLonAngle t)| ≤ 7 / 8 + 3 / 14 := by
  have hm := antoineM_pos (antoineLonAngle t)
  have h : |Real.cos (antoineLonAngle t)| ≤ antoineM (antoineLonAngle t) := le_max_left _ _
  rw [abs_mul, abs_of_pos (antoineCM_pos t), antoineCM, div_mul_eq_mul_div, div_le_iff₀ hm]
  nlinarith

theorem antoineCM_abs_sin_le (t : I) : |antoineCM t * Real.sin (antoineLonAngle t)| ≤ 7 / 8 + 3 / 14 := by
  have hm := antoineM_pos (antoineLonAngle t)
  have h : |Real.sin (antoineLonAngle t)| ≤ antoineM (antoineLonAngle t) := le_max_right _ _
  rw [abs_mul, abs_of_pos (antoineCM_pos t), antoineCM, div_mul_eq_mul_div, div_le_iff₀ hm]
  nlinarith

/-- The winding of `Ψ` along the image of the longitude under an affine chart change `T`, from the
explicit form `W(T(λ t)) - 3/8 = (c/M) κ e^{i ε α}`. -/
theorem antoine_lon_psi_wind {T : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ} (hT : Continuous T) {κ : ℂ} {θ : ℝ}
    (hκ : Complex.exp ((θ : ℂ) * Complex.I) = κ) {ε : ℤ}
    (hW : ∀ t, antoineW (T (antoineLon t)) - 3 / 8 =
      ((antoineCM t : ℝ) : ℂ) * κ * Complex.exp ((((ε : ℝ) * antoineLonAngle t : ℝ) : ℂ) * Complex.I))
    (hz : ∀ t, (T (antoineLon t)).2.2 ^ 2 ≤ 6 / 5) :
    AntoineLiftWind (fun t => antoinePsi (T (antoineLon t))) (-ε) := by
  have hκ1 : ‖κ‖ = 1 := by rw [← hκ, Complex.norm_exp_ofReal_mul_I]
  have hZn : ∀ t, ‖antoineW (T (antoineLon t)) - 3 / 8‖ = antoineCM t := fun t => by
    rw [hW, norm_mul, norm_mul, hκ1, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (antoineCM_pos t)]; ring
  have hCM := antoineCM_ge
  have hc : Continuous fun t => antoineW (T (antoineLon t)) :=
    continuous_antoineW.comp (hT.comp antoineLon.continuous)
  have hcP : Continuous fun t => antoinePsi (T (antoineLon t)) :=
    continuous_antoinePsi.comp (hT.comp antoineLon.continuous)
  have hloop : ∀ {f : ℝ × ℝ × ℝ → ℂ}, f (T (antoineLon 1)) = f (T (antoineLon 0)) := by
    intro f; simp only [Path.source, Path.target]
  -- (A) the explicit lift
  have hA : AntoineLiftWind (fun t => antoineW (T (antoineLon t)) - 3 / 8) (-ε) := by
    have hl := (continuous_antoine_cM.log fun t => (antoine_cM_pos t).ne')
    refine ⟨⟨fun t => (Real.log (antoineCM t) : ℂ) + (θ : ℂ) * Complex.I +
        (((ε : ℝ) * antoineLonAngle t : ℝ) : ℂ) * Complex.I, ?_⟩, fun t => ?_, ?_⟩
    · have := continuous_antoineLonAngle
      unfold antoineCM
      fun_prop
    · show Complex.exp (_ + _ + _) = antoineW (T (antoineLon t)) - 3 / 8
      rw [hW, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp,
        Real.exp_log (antoineCM_pos t), hκ]
    · simp only [ContinuousMap.coe_mk]
      rw [antoineCM_one]
      simp only [antoineLonAngle, Icc.coe_one, Icc.coe_zero, mul_one, mul_zero, sub_zero]
      push_cast; ring
  -- (B) add back `3/8`
  have hB : AntoineLiftWind (fun t => antoineW (T (antoineLon t))) (-ε) := by
    refine (AntoineLiftWind.of_segment (hc.sub continuous_const) hc (hloop (f := fun q => antoineW q - 3 / 8))
      hloop ?_ hA)
    intro t s hs0 hs1 h0
    have e : (1 - (s : ℂ)) * (antoineW (T (antoineLon t)) - 3 / 8) + s * antoineW (T (antoineLon t)) =
        (antoineW (T (antoineLon t)) - 3 / 8) + (s * (3 / 8) : ℝ) := by push_cast; ring
    rw [e] at h0
    have h1 := congrArg norm h0
    rw [norm_zero] at h1
    have h2 := norm_add_le (antoineW (T (antoineLon t)) - 3 / 8 + ((s * (3 / 8) : ℝ) : ℂ))
      (-((s * (3 / 8) : ℝ) : ℂ))
    rw [add_neg_cancel_right, h1, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), hZn] at h2
    have := hCM t
    nlinarith
  -- (C) `Ψ` against `W`
  refine AntoineLiftWind.of_segment hc hcP hloop hloop ?_ hB
  intro t s hs0 hs1
  have hWne : antoineW (T (antoineLon t)) ≠ 0 := by
    intro h0
    have := hZn t
    rw [h0, zero_sub, norm_neg] at this
    have := hCM t
    norm_num at *; linarith
  have := antoine_segment_Psi_W (hz t) hWne (s := 1 - s) (by linarith) (by linarith)
  have e : (1 - ((1 - s : ℝ) : ℂ)) * antoinePsi (T (antoineLon t)) +
      ((1 - s : ℝ) : ℂ) * antoineW (T (antoineLon t)) =
      (1 - (s : ℂ)) * antoineW (T (antoineLon t)) + s * antoinePsi (T (antoineLon t)) := by
    push_cast; ring
  rw [e] at this
  exact this

/-- The two shapes of the chart change between consecutive links. -/
def antoineTX (sg : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1 - sg * (5 / 4), p.2.2, p.2.1)

def antoineTY (sg : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.2.2, p.2.1 - sg * (5 / 4), p.1)

theorem continuous_antoineTX (sg : ℝ) : Continuous (antoineTX sg) := by unfold antoineTX; fun_prop
theorem continuous_antoineTY (sg : ℝ) : Continuous (antoineTY sg) := by unfold antoineTY; fun_prop

theorem antoineLon_coords (t : I) : antoineLon t =
    (antoineCM t * Real.cos (antoineLonAngle t), antoineCM t * Real.sin (antoineLonAngle t), 0) := by
  rw [antoineLon_apply]; rfl

theorem antoine_lon_wind_TX (sg : ℝ) (hsg : sg = 1 ∨ sg = -1) : ∃ w : ℤ, w ≠ 0 ∧
    AntoineLiftWind (fun t => antoinePsi (antoineTX sg (antoineLon t))) w := by
  have hb := antoineCM_abs_cos_le
  have hs := antoineCM_abs_sin_le
  have hz : ∀ t, (antoineTX sg (antoineLon t)).2.2 ^ 2 ≤ 6 / 5 := fun t => by
    rw [antoineLon_coords]
    show (antoineCM t * Real.sin (antoineLonAngle t)) ^ 2 ≤ 6 / 5
    have := hs t
    rw [← sq_abs]; nlinarith [abs_nonneg (antoineCM t * Real.sin (antoineLonAngle t))]
  rcases hsg with rfl | rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    have := antoine_lon_psi_wind (continuous_antoineTX 1) (θ := Real.pi) (κ := -1)
      (by rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi,
        Real.sin_pi]; simp) (ε := -1) (fun t => ?_) hz
    · simpa using this
    · rw [antoineLon_coords]
      have hb' := hb t
      rw [abs_le] at hb'
      have hρ : antoineRho (antoineTX 1 (antoineCM t * Real.cos (antoineLonAngle t),
          antoineCM t * Real.sin (antoineLonAngle t), 0)) =
          5 / 4 - antoineCM t * Real.cos (antoineLonAngle t) := by
        simp only [antoineRho, antoineTX, abs_zero, one_mul]
        rw [abs_of_neg (by linarith), max_eq_left (by linarith)]; ring
      rw [antoineW, hρ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext <;> simp [antoineTX, Real.cos_neg, Real.sin_neg] <;> ring
  · refine ⟨-1, by norm_num, ?_⟩
    have := antoine_lon_psi_wind (continuous_antoineTX (-1)) (θ := 0) (κ := 1)
      (by simp) (ε := 1) (fun t => ?_) hz
    · simpa using this
    · rw [antoineLon_coords]
      have hb' := hb t
      rw [abs_le] at hb'
      have hρ : antoineRho (antoineTX (-1) (antoineCM t * Real.cos (antoineLonAngle t),
          antoineCM t * Real.sin (antoineLonAngle t), 0)) =
          antoineCM t * Real.cos (antoineLonAngle t) + 5 / 4 := by
        simp only [antoineRho, antoineTX, abs_zero]
        rw [abs_of_pos (by linarith), max_eq_left (by linarith)]; ring
      rw [antoineW, hρ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext <;> simp [antoineTX] <;> ring

theorem antoine_lon_wind_TY (sg : ℝ) (hsg : sg = 1 ∨ sg = -1) : ∃ w : ℤ, w ≠ 0 ∧
    AntoineLiftWind (fun t => antoinePsi (antoineTY sg (antoineLon t))) w := by
  have hb := antoineCM_abs_cos_le
  have hs := antoineCM_abs_sin_le
  have hz : ∀ t, (antoineTY sg (antoineLon t)).2.2 ^ 2 ≤ 6 / 5 := fun t => by
    rw [antoineLon_coords]
    show (antoineCM t * Real.cos (antoineLonAngle t)) ^ 2 ≤ 6 / 5
    have := hb t
    rw [← sq_abs]; nlinarith [abs_nonneg (antoineCM t * Real.cos (antoineLonAngle t))]
  rcases hsg with rfl | rfl
  · refine ⟨-1, by norm_num, ?_⟩
    have := antoine_lon_psi_wind (continuous_antoineTY 1) (θ := Real.pi / 2) (κ := Complex.I)
      (by rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
        Real.sin_pi_div_two]; simp) (ε := 1) (fun t => ?_) hz
    · simpa using this
    · rw [antoineLon_coords]
      have hs' := hs t
      rw [abs_le] at hs'
      have hρ : antoineRho (antoineTY 1 (antoineCM t * Real.cos (antoineLonAngle t),
          antoineCM t * Real.sin (antoineLonAngle t), 0)) =
          5 / 4 - antoineCM t * Real.sin (antoineLonAngle t) := by
        simp only [antoineRho, antoineTY, abs_zero, one_mul]
        rw [abs_of_neg (by linarith), max_eq_right (by linarith)]; ring
      rw [antoineW, hρ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext <;> simp [antoineTY] <;> ring
  · refine ⟨1, one_ne_zero, ?_⟩
    have := antoine_lon_psi_wind (continuous_antoineTY (-1)) (θ := Real.pi / 2) (κ := Complex.I)
      (by rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
        Real.sin_pi_div_two]; simp) (ε := -1) (fun t => ?_) hz
    · simpa using this
    · rw [antoineLon_coords]
      have hs' := hs t
      rw [abs_le] at hs'
      have hρ : antoineRho (antoineTY (-1) (antoineCM t * Real.cos (antoineLonAngle t),
          antoineCM t * Real.sin (antoineLonAngle t), 0)) =
          antoineCM t * Real.sin (antoineLonAngle t) + 5 / 4 := by
        simp only [antoineRho, antoineTY, abs_zero]
        rw [abs_of_pos (by linarith), max_eq_right (by linarith)]; ring
      rw [antoineW, hρ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      apply Complex.ext <;> simp [antoineTY, Real.cos_neg, Real.sin_neg] <;> ring


/-- The chart change from the `j`-th link to the `(j+1)`-st is one of the four shapes. -/
theorem antoine_succ_form (j : Fin 64) :
    (∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ p, antoineMapInv (j + 1) (antoineMap j p) = antoineTX sg p) ∨
    (∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ p, antoineMapInv (j + 1) (antoineMap j p) = antoineTY sg p) := by
  rcases antoine_adj_succ j with ⟨hy, hx, ht⟩ | ⟨hx, hy, ht⟩
  · left
    have hy' : ((antoineZ j).2 : ℝ) = (antoineZ (j + 1)).2 := by exact_mod_cast hy
    refine ⟨(((antoineZ (j + 1)).1 : ℝ) - (antoineZ j).1) / 70, ?_, fun p => ?_⟩
    · rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hx with h | h
      · right; have : ((antoineZ j).1 : ℝ) - (antoineZ (j + 1)).1 = 70 := by exact_mod_cast h
        linarith [show (((antoineZ (j + 1)).1 : ℝ) - (antoineZ j).1) / 70 = -1 by
          rw [div_eq_iff (by norm_num)]; linarith]
      · left; have : ((antoineZ j).1 : ℝ) - (antoineZ (j + 1)).1 = -70 := by exact_mod_cast h
        rw [div_eq_iff (by norm_num)]; linarith
    · rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩ <;>
        simp only [antoineMapInv, antoineMap, ti, tj, antoinePerm, antoineTX, Prod.mk.injEq] <;>
        refine ⟨by ring, by rw [hy']; ring, by rw [hy']; ring⟩
  · right
    have hx' : ((antoineZ j).1 : ℝ) = (antoineZ (j + 1)).1 := by exact_mod_cast hx
    refine ⟨(((antoineZ (j + 1)).2 : ℝ) - (antoineZ j).2) / 70, ?_, fun p => ?_⟩
    · rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hy with h | h
      · right; have : ((antoineZ j).2 : ℝ) - (antoineZ (j + 1)).2 = 70 := by exact_mod_cast h
        rw [div_eq_iff (by norm_num)]; linarith
      · left; have : ((antoineZ j).2 : ℝ) - (antoineZ (j + 1)).2 = -70 := by exact_mod_cast h
        rw [div_eq_iff (by norm_num)]; linarith
    · rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩ <;>
        simp only [antoineMapInv, antoineMap, ti, tj, antoinePerm, antoineTY, Prod.mk.injEq] <;>
        refine ⟨by rw [hx']; ring, by ring, by ring⟩

/-- The longitude of the `j`-th link has nonzero winding with respect to the `(j+1)`-st. -/
theorem antoine_succ_wind (j : Fin 64) : ∃ w : ℤ, w ≠ 0 ∧
    AntoineLiftWind (fun t => antoinePsi (antoineMapInv (j + 1) (antoineMap j (antoineLon t)))) w := by
  rcases antoine_succ_form j with ⟨sg, hsg, hT⟩ | ⟨sg, hsg, hT⟩
  · obtain ⟨w, hw, h⟩ := antoine_lon_wind_TX sg hsg
    exact ⟨w, hw, h.congr fun t => by rw [hT]⟩
  · obtain ⟨w, hw, h⟩ := antoine_lon_wind_TY sg hsg
    exact ⟨w, hw, h.congr fun t => by rw [hT]⟩

theorem antoineTheta_one_stereo (i : Fin 64) (q : ℝ × ℝ × ℝ) :
    antoineTheta (fun _ => i) 1 (antoineStereo q) = antoinePsi (antoineMapInv i q) := by
  rw [antoineTheta, if_pos (antoineStereo_three_lt _), antoineStereoInv_stereo]; rfl

theorem antoineTheta_ne_zero_of_compl {i : Fin 64} {y : Sphere3}
    (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) : antoineTheta (fun _ => i) 1 y ≠ 0 := by
  refine antoineTheta_ne_zero _ _ fun h => hy ?_
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨q, ?_, rfl⟩
  rw [antoineStage_one_eq]
  exact mem_iUnion.2 ⟨i, hq⟩

/-- Points of the collar `Aⱼ` are off the first stage. -/
theorem antoineA1_subset_compl (j : Fin 64) : antoineA1 j ⊆ (antoineStereo '' antoineStage 1)ᶜ := by
  rintro y ⟨hyN, hyL⟩ ⟨q, hq, rfl⟩
  rw [antoineStage_one_eq] at hq
  obtain ⟨i, hi⟩ := mem_iUnion.1 hq
  by_cases e : i = j
  · exact hyL (e ▸ ⟨q, hi, rfl⟩)
  · obtain ⟨p, hp, hpq⟩ := hyN
    have := antoineStereo_injective hpq
    exact Set.disjoint_left.1 (antoineTube_disjoint i j e) (this ▸ hp) hi

theorem antoineSq_lt_of_mem_nbhd {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) : antoineSq p ≤ 2 := by
  obtain ⟨hx, hy, hz⟩ := antoineNbhd_bounds hp
  have hρ : max |p.1| |p.2.1| < 9 / 8 := max_lt hx hy
  have hρ0 : 0 ≤ max |p.1| |p.2.1| := (abs_nonneg _).trans (le_max_left _ _)
  have hz2 : p.2.2 ^ 2 < 1 / 16 := by
    rw [← sq_abs]; nlinarith [abs_nonneg p.2.2]
  show (max |p.1| |p.2.1|) ^ 2 + p.2.2 ^ 2 ≤ 2
  nlinarith

/-- `collar_inj` of `GX.AntoineFirstGeneration`: a loop of the collar `Aⱼ` null-homotopic in
`S³ ∖ C₁` is null-homotopic in `Aⱼ`. Its meridional winding is read by `Θⱼ`, its longitudinal
winding by `Θⱼ₊₁` (the longitude of `Lⱼ` links `Lⱼ₊₁` once, `GX.antoine_succ_wind`), and the
collar is classified by the two windings (`GX.antoine_collar_classify`). -/
theorem antoine_collar_inj (j : Fin 64) (δ : Path (antoineX1 j) (antoineX1 j))
    (hδ : ∀ t, δ t ∈ antoineA1 j)
    (hnull : HomotopicIn (antoineStereo '' antoineStage 1)ᶜ δ (Path.refl _)) :
    HomotopicIn (antoineA1 j) δ (Path.refl _) := by
  set X := (antoineStereo '' antoineStage 1)ᶜ
  set δ' := antoinePull j δ hδ
  have hδ' : ∀ t, δ' t ∈ antoineA0 := fun t => (antoinePull_spec j δ hδ t).1
  have hg := continuous_antoineStereo.comp (continuous_antoineMap j)
  have hgA : MapsTo (antoineStereo ∘ antoineMap j) antoineA0 (antoineA1 j) := fun q hq => by
    rw [antoineA1_eq]; exact ⟨q, hq, rfl⟩
  -- the meridional winding vanishes (`Θⱼ`)
  have hW : AntoineLiftWind (fun t => antoineW (δ' t)) 0 := by
    refine (antoineLiftWind_of_homotopicIn_refl hnull (F := antoineTheta (fun _ => j) 1)
      (continuous_antoineTheta _ _).continuousOn fun y hy => antoineTheta_ne_zero_of_compl hy).congr
      fun t => ?_
    rw [← (antoinePull_spec j δ hδ t).2]
    show antoineTheta (fun _ => j) 1 (antoineStereo (antoineMap j (δ' t))) = _
    rw [antoineTheta_one_stereo, antoineMapInv_map, antoinePsi_eq_W (antoineSq_lt_of_mem_nbhd (hδ' t).1)]
  obtain ⟨a, hA⟩ := antoine_exists_liftWind (f := fun t => antoineAng (δ' t))
    (continuous_antoineAng.comp δ'.continuous) (fun t => antoineAng_ne_zero_of_mem (hδ' t).1)
    (by simp only [Path.source, Path.target])
  -- classification against a power of the longitude
  have hλ := antoineLon_mem
  have hλA := antoineLiftWind_loopZPow hλ continuous_antoineAng.continuousOn
    (fun y hy => antoineAng_ne_zero_of_mem hy.1) antoineLiftWind_lon_Ang (-a)
  have hλW := antoineLiftWind_loopZPow hλ continuous_antoineW.continuousOn
    (fun y hy => antoineW_ne_zero hy) antoineLiftWind_lon_W (-a)
  rw [show -a * -1 = a by ring] at hλA
  rw [mul_zero] at hλW
  have hcl := antoine_collar_classify hδ' (loopZPow_mem hλ (-a)) hA hλA hW hλW
  have hmap := hcl.map hg (V := antoineA1 j) hgA
  have hδeq : δ'.map hg = δ := Path.ext (funext fun t => (antoinePull_spec j δ hδ t).2)
  rw [hδeq, loopZPow_map] at hmap
  -- the longitudinal winding vanishes (`Θⱼ₊₁`)
  set Λ := antoineLon.map hg
  have hΛ : ∀ t, Λ t ∈ antoineA1 j := fun t => hgA (hλ t)
  obtain ⟨w, hw, hwind⟩ := antoine_succ_wind j
  have hΘ : ContinuousOn (antoineTheta (fun _ => j + 1) 1) (antoineA1 j) :=
    (continuous_antoineTheta _ _).continuousOn
  have hΘ0 : ∀ y ∈ antoineA1 j, antoineTheta (fun _ => j + 1) 1 y ≠ 0 := fun y hy =>
    antoineTheta_ne_zero_of_compl (antoineA1_subset_compl j hy)
  have h1 : AntoineLiftWind (fun t => antoineTheta (fun _ => j + 1) 1 (δ t)) 0 :=
    antoineLiftWind_of_homotopicIn_refl hnull (continuous_antoineTheta _ _).continuousOn
      fun y hy => antoineTheta_ne_zero_of_compl hy
  have h2 := AntoineLiftWind.of_homotopicIn hmap hΘ hΘ0 h1
  have hΛw : AntoineLiftWind (fun t => antoineTheta (fun _ => j + 1) 1 (Λ t)) w :=
    hwind.congr fun t => (antoineTheta_one_stereo _ _).symm
  have h3 := antoineLiftWind_loopZPow hΛ hΘ hΘ0 hΛw (-a)
  have e := h2.unique h3
  have ha : a = 0 := by
    rcases mul_eq_zero.1 e.symm with h | h
    · exact neg_eq_zero.1 h
    · exact absurd h hw
  rw [ha] at hmap
  exact hmap

end GX

end