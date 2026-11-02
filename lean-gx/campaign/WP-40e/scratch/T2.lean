import GXScaffold.Branched.GaloisExamples

noncomputable section
open Set Filter Topology Function unitInterval
namespace GX
attribute [local instance] Classical.propDecidable

/-- The inverse of the similarity `GX.antoineMap i`. -/
def antoineMapInv (i : Fin 64) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  antoinePerm (antoineT i) ((q.1 - (antoineZ i).1 / 640) * (80 / 7),
    (q.2.1 - (antoineZ i).2 / 640) * (80 / 7), q.2.2 * (80 / 7))

theorem antoineMapInv_map (i : Fin 64) (p : ℝ × ℝ × ℝ) : antoineMapInv i (antoineMap i p) = p := by
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMapInv, antoineMap, h, antoinePerm] <;>
    ext <;> ring

theorem antoineMap_mapInv (i : Fin 64) (q : ℝ × ℝ × ℝ) : antoineMap i (antoineMapInv i q) = q := by
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMapInv, antoineMap, h, antoinePerm] <;>
    ext <;> ring

theorem continuous_antoineMapInv (i : Fin 64) : Continuous (antoineMapInv i) := by
  show Continuous fun q => antoineMapInv i q
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMapInv, h, antoinePerm] <;> fun_prop

/-- The inverse of `GX.antoineComp w n`. -/
def antoineCompInv (w : ℕ → Fin 64) : ℕ → ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | 0 => id
  | n + 1 => antoineMapInv (w n) ∘ antoineCompInv w n

theorem antoineCompInv_comp (w : ℕ → Fin 64) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    antoineCompInv w n (antoineComp w n p) = p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    show antoineMapInv (w n) (antoineCompInv w n (antoineComp w n (antoineMap (w n) p))) = p
    rw [ih, antoineMapInv_map]

theorem antoineComp_compInv (w : ℕ → Fin 64) (n : ℕ) (q : ℝ × ℝ × ℝ) :
    antoineComp w n (antoineCompInv w n q) = q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    show antoineComp w n (antoineMap (w n) (antoineMapInv (w n) (antoineCompInv w n q))) = q
    rw [antoineMap_mapInv, ih]

theorem continuous_antoineCompInv (w : ℕ → Fin 64) (n : ℕ) : Continuous (antoineCompInv w n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => exact (continuous_antoineMapInv _).comp ih

/-- `ρ² + z²`, `ρ = max(|x|, |y|)`. -/
def antoineSq (p : ℝ × ℝ × ℝ) : ℝ := (max |p.1| |p.2.1|) ^ 2 + p.2.2 ^ 2

theorem continuous_antoineSq : Continuous antoineSq := by unfold antoineSq; fun_prop

theorem antoineMap_sq_lt (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : antoineSq p < 4) :
    antoineSq (antoineMap i p) < 4 := by
  have hm : max |p.1| |p.2.1| < 2 := by
    unfold antoineSq at hp
    nlinarith [abs_nonneg p.1, le_max_left |p.1| |p.2.1|, sq_nonneg p.2.2]
  have hz : |p.2.2| < 2 := by
    unfold antoineSq at hp
    have : p.2.2 ^ 2 < 4 := by nlinarith [sq_nonneg (max |p.1| |p.2.1|)]
    rw [← sq_abs] at this; nlinarith [abs_nonneg p.2.2]
  have hx : |p.1| < 2 := (le_max_left _ _).trans_lt hm
  have hy : |p.2.1| < 2 := (le_max_right _ _).trans_lt hm
  have hc : |((antoineZ i).1 : ℝ)| ≤ 560 ∧ |((antoineZ i).2 : ℝ)| ≤ 560 := by
    rcases antoine_centre_mem i with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · exact ⟨by exact_mod_cast c1.le, by exact_mod_cast c2⟩
    · exact ⟨by exact_mod_cast c2, by exact_mod_cast c1.le⟩
  rw [abs_lt] at hx hy hz
  obtain ⟨hc1, hc2⟩ := hc
  rw [abs_le] at hc1 hc2
  have key : ∀ a b c : ℝ, |a| < 11 / 10 → |b| < 11 / 10 → |c| < 11 / 10 →
      (max |a| |b|) ^ 2 + c ^ 2 < 4 := by
    intro a b c ha hb hc
    have h1 : max |a| |b| < 11 / 10 := max_lt ha hb
    have h0 : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
    have h2 : c ^ 2 < (11 / 10) ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg c]
    nlinarith
  unfold antoineSq
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm] <;>
    refine key _ _ _ ?_ ?_ ?_ <;> rw [abs_lt] <;> constructor <;> linarith

theorem antoineComp_sq_lt (w : ℕ → Fin 64) (n : ℕ) {p : ℝ × ℝ × ℝ} (hp : antoineSq p < 4) :
    antoineSq (antoineComp w n p) < 4 := by
  induction n generalizing p with
  | zero => exact hp
  | succ n ih => exact ih (antoineMap_sq_lt _ hp)

theorem antoineCompInv_sq_ge (w : ℕ → Fin 64) (n : ℕ) {q : ℝ × ℝ × ℝ} (hq : 4 ≤ antoineSq q) :
    4 ≤ antoineSq (antoineCompInv w n q) := by
  by_contra h
  push Not at h
  have := antoineComp_sq_lt w n h
  rw [antoineComp_compInv] at this
  linarith

/-- An invariant of `ℝ³ ∖ L` with values in `ℂ ∖ 0`: `(ρ - 7/8) + i z` near the core square,
cut off to the constant `9/8` where `ρ² + z² ≥ 4`. -/
def antoinePsi (p : ℝ × ℝ × ℝ) : ℂ :=
  ((min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) - 7 / 8 : ℝ) : ℂ) +
    ((p.2.2 * max 0 (min 1 (3 - antoineSq p)) : ℝ) : ℂ) * Complex.I

theorem continuous_antoinePsi : Continuous antoinePsi := by
  unfold antoinePsi
  have := continuous_antoineSq
  fun_prop

theorem antoinePsi_eq_of_sq_ge {p : ℝ × ℝ × ℝ} (hp : 4 ≤ antoineSq p) : antoinePsi p = 9 / 8 := by
  have h1 : min 2 (max |p.1| |p.2.1| + max 0 (antoineSq p - 2)) = 2 := by
    refine min_eq_left ?_
    rw [max_eq_right (show (0 : ℝ) ≤ antoineSq p - 2 by linarith)]
    linarith [(abs_nonneg p.1).trans (le_max_left |p.1| |p.2.1|)]
  have h2 : max 0 (min 1 (3 - antoineSq p)) = 0 :=
    max_eq_left ((min_le_right _ _).trans (by linarith))
  simp only [antoinePsi, h1, h2, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
  push_cast; norm_num

theorem antoinePsi_mem_of_eq_zero {p : ℝ × ℝ × ℝ} (h : antoinePsi p = 0) : p ∈ antoineLink := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [antoinePsi, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, Complex.zero_re,
    Complex.add_im, Complex.mul_im, zero_add, Complex.zero_im, zero_mul, add_zero] at hre him
  set ρ := max |p.1| |p.2.1| with hρ
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans (le_max_left _ _)
  have hS : antoineSq p = ρ ^ 2 + p.2.2 ^ 2 := rfl
  have hm : min 2 (ρ + max 0 (antoineSq p - 2)) = 7 / 8 := by linarith
  have hlt : ρ + max 0 (antoineSq p - 2) = 7 / 8 := by
    rcases min_choice 2 (ρ + max 0 (antoineSq p - 2)) with e | e <;> rw [e] at hm
    · norm_num at hm
    · exact hm
  have hmx := le_max_right 0 (antoineSq p - 2)
  have hmx0 := le_max_left 0 (antoineSq p - 2)
  -- the imaginary part: `z = 0` or `S ≥ 3`
  have hz : p.2.2 = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact h'
    · exfalso
      have h3 : 3 ≤ antoineSq p := by
        by_contra hc
        push Not at hc
        have : 0 < min 1 (3 - antoineSq p) := lt_min one_pos (by linarith)
        have := le_max_right 0 (min 1 (3 - antoineSq p))
        linarith
      linarith
  have hSρ : antoineSq p = ρ ^ 2 := by rw [hS, hz]; ring
  have hρ1 : ρ ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 2 < antoineSq p := by rw [hSρ]; nlinarith
    linarith
  have hS2 : antoineSq p ≤ 2 := by rw [hSρ]; nlinarith
  rw [max_eq_left (by linarith)] at hlt
  refine ⟨by rw [hz]; norm_num, ?_, ?_⟩
  · show ρ ≤ 1; linarith
  · show 3 / 4 ≤ ρ; linarith

/-- On the meridian, `GX.antoinePsi` is exactly the circle `(3/14) e^{2πit}`. -/
theorem antoinePsi_meridian (t : I) :
    antoinePsi (antoineMeridian t) = (3 / 14 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t) := by
  rw [antoineMeridian_apply]
  set c := Real.cos (2 * Real.pi * t)
  set s := Real.sin (2 * Real.pi * t)
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc1 : -1 ≤ c := Real.neg_one_le_cos _
  have hc2 : c ≤ 1 := Real.cos_le_one _
  have hpos : 0 ≤ 7 / 8 + 3 / 14 * c := by linarith
  have hρ : max |(0 : ℝ)| |7 / 8 + 3 / 14 * c| = 7 / 8 + 3 / 14 * c := by
    rw [abs_zero, abs_of_nonneg hpos, max_eq_right hpos]
  have hS : antoineSq (0, 7 / 8 + 3 / 14 * c, 3 / 14 * s) =
      (7 / 8 + 3 / 14 * c) ^ 2 + (3 / 14 * s) ^ 2 := by
    simp only [antoineSq, hρ]
  have hS2 : antoineSq (0, 7 / 8 + 3 / 14 * c, 3 / 14 * s) ≤ 2 := by rw [hS]; nlinarith
  have e1 : min 2 (max |(0 : ℝ)| |7 / 8 + 3 / 14 * c| +
      max 0 (antoineSq (0, 7 / 8 + 3 / 14 * c, 3 / 14 * s) - 2)) = 7 / 8 + 3 / 14 * c := by
    rw [hρ, max_eq_left (by linarith), add_zero, min_eq_right (by linarith)]
  have e2 : max 0 (min 1 (3 - antoineSq (0, 7 / 8 + 3 / 14 * c, 3 / 14 * s))) = 1 := by
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  simp only [antoinePsi, e1, e2, mul_one]
  have : (2 * Real.pi * Complex.I * (t : ℝ)) = ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [c, s] <;> ring

theorem sphere3_sum_sq (y : Sphere3) :
    (y : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 + (y : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 +
      (y : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 + (y : EuclideanSpace ℝ (Fin 4)) 3 ^ 2 = 1 := by
  have h := real_inner_self_eq_norm_sq (y : EuclideanSpace ℝ (Fin 4))
  rw [mem_sphere_zero_iff_norm.1 y.2] at h
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial] at h
  nlinarith

/-- Stereographic projection `S³ ∖ {N} → ℝ³`, the inverse of `GX.antoineStereo`. -/
def antoineStereoInv (y : Sphere3) : ℝ × ℝ × ℝ :=
  ((y : EuclideanSpace ℝ (Fin 4)) 0 / (1 - (y : EuclideanSpace ℝ (Fin 4)) 3),
    (y : EuclideanSpace ℝ (Fin 4)) 1 / (1 - (y : EuclideanSpace ℝ (Fin 4)) 3),
    (y : EuclideanSpace ℝ (Fin 4)) 2 / (1 - (y : EuclideanSpace ℝ (Fin 4)) 3))

theorem antoineStereo_apply (p : ℝ × ℝ × ℝ) :
    (antoineStereo p : EuclideanSpace ℝ (Fin 4)) =
      !₂[2 * p.1 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1),
        2 * p.2.1 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1),
        2 * p.2.2 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1),
        (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1)] := rfl

theorem antoineStereo_three_lt (p : ℝ × ℝ × ℝ) :
    (antoineStereo p : EuclideanSpace ℝ (Fin 4)) 3 < 1 := by
  rw [antoineStereo_apply]
  have hN : 0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1 := by positivity
  simp only [PiLp.toLp_apply, Matrix.cons_val_three, Matrix.cons_val_two, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons]
  rw [div_lt_one hN]; linarith

theorem antoineStereoInv_stereo (p : ℝ × ℝ × ℝ) : antoineStereoInv (antoineStereo p) = p := by
  have hN : 0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1 := by positivity
  simp only [antoineStereoInv, antoineStereo_apply, PiLp.toLp_apply, Matrix.cons_val_three,
    Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons,
    Matrix.head_cons]
  have hd : 1 - (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - 1) / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1) =
      2 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1) := by field_simp; ring
  rw [hd]
  ext <;> simp only <;> field_simp

theorem antoineStereo_stereoInv {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    antoineStereo (antoineStereoInv y) = y := by
  have hs := sphere3_sum_sq y
  obtain ⟨w, hw⟩ := y
  simp only at hy hs ⊢
  have hd : 0 < 1 - w 3 := by linarith
  have hd' : 1 - w 3 ≠ 0 := hd.ne'
  have hN : (w 0 / (1 - w 3)) ^ 2 + (w 1 / (1 - w 3)) ^ 2 + (w 2 / (1 - w 3)) ^ 2 + 1 =
      2 / (1 - w 3) := by
    field_simp
    nlinarith
  have hN' : (w 0 / (1 - w 3)) ^ 2 + (w 1 / (1 - w 3)) ^ 2 + (w 2 / (1 - w 3)) ^ 2 - 1 =
      2 * w 3 / (1 - w 3) := by
    field_simp
    nlinarith
  apply Subtype.ext
  rw [antoineStereo_apply]
  simp only [antoineStereoInv]
  rw [hN, hN']
  have e0 : 2 * (w 0 / (1 - w 3)) / (2 / (1 - w 3)) = w 0 := by field_simp
  have e1 : 2 * (w 1 / (1 - w 3)) / (2 / (1 - w 3)) = w 1 := by field_simp
  have e2 : 2 * (w 2 / (1 - w 3)) / (2 / (1 - w 3)) = w 2 := by field_simp
  have e3 : 2 * w 3 / (1 - w 3) / (2 / (1 - w 3)) = w 3 := by field_simp
  rw [e0, e1, e2, e3]
  ext i
  fin_cases i <;> rfl

theorem antoineStereoInv_sq_ge {y : Sphere3} (hy : 19 / 20 < (y : EuclideanSpace ℝ (Fin 4)) 3)
    (hy1 : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) : 4 ≤ antoineSq (antoineStereoInv y) := by
  have hs := sphere3_sum_sq y
  set y0 := (y : EuclideanSpace ℝ (Fin 4)) 0
  set y1 := (y : EuclideanSpace ℝ (Fin 4)) 1
  set y2 := (y : EuclideanSpace ℝ (Fin 4)) 2
  set y3 := (y : EuclideanSpace ℝ (Fin 4)) 3
  have hd : 0 < 1 - y3 := by linarith
  simp only [antoineSq, antoineStereoInv]
  set a := y0 / (1 - y3)
  set b := y1 / (1 - y3)
  set c := y2 / (1 - y3)
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 = (1 + y3) / (1 - y3) := by
    simp only [a, b, c]; field_simp; nlinarith
  have hbig : 39 ≤ (1 + y3) / (1 - y3) := by rw [le_div_iff₀ hd]; linarith
  have ha : a ^ 2 ≤ (max |a| |b|) ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) (le_max_left _ _) 2
  have hb : b ^ 2 ≤ (max |a| |b|) ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) (le_max_right _ _) 2
  nlinarith [sq_nonneg c]

/-- The invariant of `S³ ∖ L_{v,n}`, `L_{v,n}` the link of generation `n` with word `v`:
`GX.antoinePsi ∘ (g_v)⁻¹` in the stereographic chart, the constant `9/8` near the pole. -/
def antoineTheta (v : ℕ → Fin 64) (n : ℕ) (y : Sphere3) : ℂ :=
  if (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 then antoinePsi (antoineCompInv v n (antoineStereoInv y))
  else 9 / 8

theorem antoineTheta_stereo (v : ℕ → Fin 64) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    antoineTheta v n (antoineStereo (antoineComp v n p)) = antoinePsi p := by
  rw [antoineTheta, if_pos (antoineStereo_three_lt _), antoineStereoInv_stereo,
    antoineCompInv_comp]

theorem continuousAt_antoineStereoInv {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    ContinuousAt antoineStereoInv y := by
  have hc : ∀ i : Fin 4, Continuous fun z : Sphere3 => (z : EuclideanSpace ℝ (Fin 4)) i :=
    fun i => (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
  have hd : (1 - (y : EuclideanSpace ℝ (Fin 4)) 3) ≠ 0 := by linarith
  have hden : ContinuousAt (fun z : Sphere3 => 1 - (z : EuclideanSpace ℝ (Fin 4)) 3) y :=
    (continuous_const.sub (hc 3)).continuousAt
  exact ((hc 0).continuousAt.div hden hd).prodMk
    (((hc 1).continuousAt.div hden hd).prodMk ((hc 2).continuousAt.div hden hd))

theorem continuous_antoineTheta (v : ℕ → Fin 64) (n : ℕ) : Continuous (antoineTheta v n) := by
  have hc3 : Continuous fun z : Sphere3 => (z : EuclideanSpace ℝ (Fin 4)) 3 :=
    (PiLp.continuous_apply 2 _ 3).comp continuous_subtype_val
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1
  · have hG : ContinuousAt (fun z => antoinePsi (antoineCompInv v n (antoineStereoInv z))) y :=
      (continuous_antoinePsi.comp (continuous_antoineCompInv v n)).continuousAt.comp
        (continuousAt_antoineStereoInv hy)
    refine hG.congr (Filter.eventually_of_mem ((isOpen_lt hc3 continuous_const).mem_nhds hy)
      fun z hz => ?_)
    simp only [antoineTheta, if_pos (show (z : EuclideanSpace ℝ (Fin 4)) 3 < 1 from hz)]
  · push Not at hy
    refine (continuousAt_const (y := (9 / 8 : ℂ))).congr (Filter.eventually_of_mem
      ((isOpen_lt continuous_const hc3).mem_nhds (show (19 / 20 : ℝ) < _ by linarith))
      fun z hz => ?_)
    simp only [antoineTheta]
    split_ifs with h
    · exact (antoinePsi_eq_of_sq_ge (antoineCompInv_sq_ge v n
        (antoineStereoInv_sq_ge hz h))).symm
    · rfl

theorem antoineTheta_ne_zero (v : ℕ → Fin 64) (n : ℕ) {y : Sphere3}
    (hy : y ∉ antoineStereo '' (antoineComp v n '' antoineLink)) : antoineTheta v n y ≠ 0 := by
  intro h
  unfold antoineTheta at h
  split_ifs at h with h3
  · apply hy
    refine ⟨antoineStereoInv y, ⟨antoineCompInv v n (antoineStereoInv y),
      antoinePsi_mem_of_eq_zero h, antoineComp_compInv _ _ _⟩, antoineStereo_stereoInv h3⟩
  · norm_num at h

/-- (placeholder for scratch) -/
def AntoineMeridianEssentialStrict : Prop :=
  ∀ (v : ℕ → Fin 64) (n m : ℕ), n < m →
    ¬ HomotopicIn (antoineStereo '' (antoineStage m ∩ antoineComp v n '' antoineLink))ᶜ
      ((antoineMeridian.map (continuous_antoineComp v n)).map continuous_antoineStereo)
      (Path.refl _)

/-- **Antoine's lemma at equal generations** (the abelian case of the residual, proved): the
meridian of a link `L_{v,n}` of generation `n` is not null-homotopic in `S³ ∖ L_{v,n}` — the
invariant `GX.antoineTheta` carries it to the circle `(3/14) e^{2πit}` of `ℂ ∖ 0`, of winding
number `1`. -/
theorem antoineMeridianEssential_self (v : ℕ → Fin 64) (n : ℕ) :
    ¬ HomotopicIn (antoineStereo '' (antoineStage n ∩ antoineComp v n '' antoineLink))ᶜ
      ((antoineMeridian.map (continuous_antoineComp v n)).map continuous_antoineStereo)
      (Path.refl _) := by
  set K := antoineStereo '' (antoineStage n ∩ antoineComp v n '' antoineLink) with hKdef
  set μ' := (antoineMeridian.map (continuous_antoineComp v n)).map continuous_antoineStereo
  rw [homotopicIn_iff]
  rintro ⟨h1, h2, hom⟩
  have hK : ∀ y : (Kᶜ : Set Sphere3), antoineTheta v n y ≠ 0 := fun y => by
    refine antoineTheta_ne_zero v n fun hy => y.2 ?_
    obtain ⟨q, hq, e⟩ := hy
    exact ⟨q, ⟨mem_iUnion.2 ⟨v, hq⟩, hq⟩, e⟩
  let Θ' : C((Kᶜ : Set Sphere3), CStar) :=
    ⟨fun y => ⟨antoineTheta v n y, hK y⟩,
      ((continuous_antoineTheta v n).comp continuous_subtype_val).subtype_mk _⟩
  have hw := cWinding_homotopic (Path.Homotopic.map hom Θ')
  have e1 : cWinding ((pathToSub μ' h1).map Θ'.continuous) = 1 := by
    refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (3 / 14) +
      2 * Real.pi * Complex.I * (t : ℝ), by fun_prop⟩) (fun t => ?_) ?_
    · show Complex.exp (Complex.log (3 / 14) + _) =
        antoineTheta v n (antoineStereo (antoineComp v n (antoineMeridian t)))
      rw [Complex.exp_add, Complex.exp_log (by norm_num), antoineTheta_stereo,
        antoinePsi_meridian]
    · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
        Complex.ofReal_zero, mul_one, mul_zero, add_zero, Int.cast_one, one_mul]
  have e2 : cWinding ((pathToSub (Path.refl (antoineStereo (antoineComp v n antoineMerPt)))
      h2).map Θ'.continuous) = 0 := by
    refine cWinding_eq _ (Γ := ContinuousMap.const I
      (Complex.log (antoineTheta v n (antoineStereo (antoineComp v n antoineMerPt)))))
      (fun t => ?_) (by simp)
    show Complex.exp (Complex.log _) = antoineTheta v n _
    exact Complex.exp_log (hK ⟨_, h2 0⟩)
  rw [e1, e2] at hw
  exact one_ne_zero hw

/-! ### Reduction of the strict residual to the top link (self-similarity) -/

/-- The word `v₀ ⋯ v_{n-1} w₀ w₁ ⋯`. -/
def antoineCat (v : ℕ → Fin 64) (n : ℕ) (w : ℕ → Fin 64) : ℕ → Fin 64 :=
  fun j => if j < n then v j else w (j - n)

theorem antoineComp_cat (v : ℕ → Fin 64) (n : ℕ) (w : ℕ → Fin 64) (k : ℕ) :
    antoineComp (antoineCat v n w) (n + k) = antoineComp v n ∘ antoineComp w k := by
  induction k with
  | zero =>
    rw [Nat.add_zero, antoineComp_congr (w' := v) fun j hj => by simp [antoineCat, hj]]
    rfl
  | succ k ih =>
    show antoineComp (antoineCat v n w) (n + k) ∘ antoineMap (antoineCat v n w (n + k)) = _
    rw [ih]
    simp only [antoineCat, show ¬ (n + k < n) by omega, if_false, Nat.add_sub_cancel_left]
    rfl

/-- The links of generation `k` inside `L`, carried by `g_v`, are links of generation `n + k`
inside `L_{v,n}`. -/
theorem antoineComp_image_stage_subset (v : ℕ → Fin 64) (n k : ℕ) :
    antoineComp v n '' antoineStage k ⊆ antoineStage (n + k) ∩ antoineComp v n '' antoineLink := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨w, hw⟩ := mem_iUnion.1 hq
  obtain ⟨p, hp, rfl⟩ := hw
  have e : antoineComp v n (antoineComp w k p) = antoineComp (antoineCat v n w) (n + k) p := by
    rw [antoineComp_cat]; rfl
  refine ⟨mem_iUnion.2 ⟨antoineCat v n w, e ▸ ⟨p, hp, rfl⟩⟩, ?_⟩
  have h1 := antoineComp_antitone (antoineCat v n w) (Nat.le_add_right n k) ⟨p, hp, e.symm⟩
  rwa [antoineComp_congr (w' := v) fun j hj => by simp [antoineCat, hj]] at h1

theorem antoineCompInv_dist_ge (w : ℕ → Fin 64) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    dist p 0 - 2 ≤ dist (antoineCompInv w n p) 0 := by
  have h0 : antoineSq (antoineComp w n 0) < 4 := antoineComp_sq_lt w n (by simp [antoineSq])
  have hf0 : dist (antoineComp w n 0) 0 < 2 := by
    set a := antoineComp w n 0
    have hm : max |a.1| |a.2.1| < 2 := by
      unfold antoineSq at h0
      nlinarith [abs_nonneg a.1, le_max_left |a.1| |a.2.1|, sq_nonneg a.2.2]
    have hz : |a.2.2| < 2 := by
      unfold antoineSq at h0
      have : a.2.2 ^ 2 < 4 := by nlinarith [sq_nonneg (max |a.1| |a.2.1|)]
      rw [← sq_abs] at this; nlinarith [abs_nonneg a.2.2]
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
    exact max_lt ((le_max_left _ _).trans_lt hm) (max_lt ((le_max_right _ _).trans_lt hm) hz)
  have h1 : dist p (antoineComp w n 0) ≤ dist (antoineCompInv w n p) 0 := by
    have := antoineComp_dist_le w n (antoineCompInv w n p) 0
    rw [antoineComp_compInv] at this
    have hr : (7 / 80 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [dist_nonneg (x := antoineCompInv w n p) (y := 0)]
  linarith [dist_triangle p (antoineComp w n 0) 0]

theorem antoine_dist_zero_sq_le (q : ℝ × ℝ × ℝ) :
    dist q 0 ^ 2 ≤ q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
  rcases max_choice |q.1| (max |q.2.1| |q.2.2|) with h | h <;> rw [h]
  · rw [sq_abs]; nlinarith [sq_nonneg q.2.1, sq_nonneg q.2.2]
  · rcases max_choice |q.2.1| |q.2.2| with h' | h' <;> rw [h', sq_abs] <;>
      nlinarith [sq_nonneg q.1, sq_nonneg q.2.1, sq_nonneg q.2.2]

theorem antoineStereoInv_dist_sq {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    (1 + (y : EuclideanSpace ℝ (Fin 4)) 3) / (3 * (1 - (y : EuclideanSpace ℝ (Fin 4)) 3)) ≤
      dist (antoineStereoInv y) 0 ^ 2 := by
  have hs := sphere3_sum_sq y
  obtain ⟨w, hw⟩ := y
  simp only at hy hs ⊢
  have hd : 0 < 1 - w 3 := by linarith
  simp only [antoineStereoInv, Prod.dist_eq, Real.dist_eq, Prod.fst_zero, Prod.snd_zero, sub_zero]
  set a := w 0 / (1 - w 3)
  set b := w 1 / (1 - w 3)
  set c := w 2 / (1 - w 3)
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 = (1 + w 3) / (1 - w 3) := by
    simp only [a, b, c]; field_simp; nlinarith
  set M := max |a| (max |b| |c|)
  have ha : a ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) (le_max_left _ _) 2
  have hb : b ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg b) ((le_max_left _ _).trans (le_max_right _ _)) 2
  have hc : c ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs c]
    exact pow_le_pow_left₀ (abs_nonneg c) ((le_max_right _ _).trans (le_max_right _ _)) 2
  rw [div_le_iff₀ (by positivity)]
  have : (1 + w 3) / (1 - w 3) * (1 - w 3) = 1 + w 3 := div_mul_cancel₀ _ hd.ne'
  nlinarith

theorem sphere3_eq_north {y : Sphere3} (hy : 1 ≤ (y : EuclideanSpace ℝ (Fin 4)) 3) :
    (y : EuclideanSpace ℝ (Fin 4)) 0 = 0 ∧ (y : EuclideanSpace ℝ (Fin 4)) 1 = 0 ∧
      (y : EuclideanSpace ℝ (Fin 4)) 2 = 0 ∧ (y : EuclideanSpace ℝ (Fin 4)) 3 = 1 := by
  have hs := sphere3_sum_sq y
  have h3 : (y : EuclideanSpace ℝ (Fin 4)) 3 = 1 := by
    nlinarith [sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 0),
      sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 1), sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 2)]
  rw [h3] at hs
  refine ⟨?_, ?_, ?_, h3⟩ <;>
    nlinarith [sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 0),
      sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 1), sq_nonneg ((y : EuclideanSpace ℝ (Fin 4)) 2)]

theorem sphere3_dist_north_sq {a y : Sphere3} (hy : 1 ≤ (y : EuclideanSpace ℝ (Fin 4)) 3) :
    dist a y ^ 2 = 2 - 2 * (a : EuclideanSpace ℝ (Fin 4)) 3 := by
  obtain ⟨h0, h1, h2, h3⟩ := sphere3_eq_north hy
  rw [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real, mem_sphere_zero_iff_norm.1 a.2,
    mem_sphere_zero_iff_norm.1 y.2]
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial, h0, h1, h2, h3]
  ring

/-- The similarity `(g_v)⁻¹`, conjugated by the stereographic chart, fixing the pole. -/
def antoinePhi (v : ℕ → Fin 64) (n : ℕ) (y : Sphere3) : Sphere3 :=
  if (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 then antoineStereo (antoineCompInv v n (antoineStereoInv y))
  else y

theorem antoineStereo_three (q : ℝ × ℝ × ℝ) :
    (antoineStereo q : EuclideanSpace ℝ (Fin 4)) 3 =
      (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 - 1) / (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 + 1) := by
  rw [antoineStereo_apply]; rfl

theorem continuous_antoinePhi (v : ℕ → Fin 64) (n : ℕ) : Continuous (antoinePhi v n) := by
  have hc3 : Continuous fun z : Sphere3 => (z : EuclideanSpace ℝ (Fin 4)) 3 :=
    (PiLp.continuous_apply 2 _ 3).comp continuous_subtype_val
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1
  · have hG : ContinuousAt
        (fun z => antoineStereo (antoineCompInv v n (antoineStereoInv z))) y :=
      (continuous_antoineStereo.comp (continuous_antoineCompInv v n)).continuousAt.comp
        (continuousAt_antoineStereoInv hy)
    refine hG.congr (Filter.eventually_of_mem ((isOpen_lt hc3 continuous_const).mem_nhds hy)
      fun z hz => ?_)
    simp only [antoinePhi, if_pos (show (z : EuclideanSpace ℝ (Fin 4)) 3 < 1 from hz)]
  · push Not at hy
    rw [Metric.continuousAt_iff]
    intro ε hε
    set Λ : ℝ := 4 / ε ^ 2 with hΛ
    have hΛ0 : 0 < Λ := by positivity
    set R : ℝ := Λ + 3 with hR
    set η : ℝ := min (1 / (3 * R ^ 2)) (1 / 2) with hη
    have hη0 : 0 < η := by positivity
    refine ⟨min ε (Real.sqrt (2 * η)), lt_min hε (Real.sqrt_pos.2 (by positivity)), fun z hz => ?_⟩
    have hPy : antoinePhi v n y = y := by simp [antoinePhi, not_lt.2 hy]
    rw [hPy]
    by_cases hz3 : (z : EuclideanSpace ℝ (Fin 4)) 3 < 1
    · simp only [antoinePhi, if_pos hz3]
      have hd := sphere3_dist_north_sq (a := z) hy
      have hzy : dist z y < Real.sqrt (2 * η) := lt_of_lt_of_le hz (min_le_right _ _)
      have hzy2 : dist z y ^ 2 < 2 * η := by
        have := pow_lt_pow_left₀ hzy dist_nonneg (two_ne_zero)
        rwa [Real.sq_sqrt (by positivity)] at this
      have h1z : 1 - (z : EuclideanSpace ℝ (Fin 4)) 3 < η := by linarith
      have hz0 : 1 / 2 < (z : EuclideanSpace ℝ (Fin 4)) 3 := by
        linarith [min_le_right (1 / (3 * R ^ 2)) (1 / 2)]
      -- the chart point is far out
      set p := antoineStereoInv z
      set q := antoineCompInv v n p
      have hp2 := antoineStereoInv_dist_sq hz3
      have hpR : R ^ 2 ≤ dist p 0 ^ 2 := by
        refine le_trans ?_ hp2
        have hpos : 0 < 1 - (z : EuclideanSpace ℝ (Fin 4)) 3 := by linarith
        rw [le_div_iff₀ (by positivity)]
        have : 1 - (z : EuclideanSpace ℝ (Fin 4)) 3 < 1 / (3 * R ^ 2) :=
          lt_of_lt_of_le h1z (min_le_left _ _)
        rw [lt_div_iff₀ (by positivity)] at this
        nlinarith
      have hpR' : R ≤ dist p 0 := by
        have hR0 : 0 ≤ R := by positivity
        nlinarith [dist_nonneg (x := p) (y := 0)]
      have hq := antoineCompInv_dist_ge v n p
      have hqd : Λ + 1 ≤ dist q 0 := by linarith
      have hq2 := antoine_dist_zero_sq_le q
      set N := q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 with hN
      have hNΛ : Λ < N := by nlinarith
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have hN1 : N + 1 ≠ 0 := by positivity
      have hd' : dist (antoineStereo q) y ^ 2 = 4 / (N + 1) := by
        rw [sphere3_dist_north_sq hy, antoineStereo_three, ← hN]
        rw [eq_div_iff hN1]; field_simp; ring
      have hlt : dist (antoineStereo q) y ^ 2 < ε ^ 2 := by
        rw [hd', div_lt_iff₀ (by positivity)]
        rw [hΛ, div_lt_iff₀ (by positivity)] at hNΛ
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
    · simp only [antoinePhi, if_neg hz3]
      exact lt_of_lt_of_le hz (min_le_left _ _)

theorem antoinePhi_stereo (v : ℕ → Fin 64) (n : ℕ) (p : ℝ × ℝ × ℝ) :
    antoinePhi v n (antoineStereo (antoineComp v n p)) = antoineStereo p := by
  rw [antoinePhi, if_pos (antoineStereo_three_lt _), antoineStereoInv_stereo, antoineCompInv_comp]

theorem antoinePhi_mapsTo (v : ℕ → Fin 64) (n k : ℕ) {y : Sphere3}
    (hy : y ∉ antoineStereo '' (antoineStage (n + k) ∩ antoineComp v n '' antoineLink)) :
    antoinePhi v n y ∉ antoineStereo '' antoineStage k := by
  rintro ⟨q, hq, e⟩
  unfold antoinePhi at e
  split_ifs at e with h3
  · apply hy
    have hq' : antoineCompInv v n (antoineStereoInv y) = q := (antoineStereo_injective e).symm
    refine ⟨antoineStereoInv y, antoineComp_image_stage_subset v n k ⟨q, hq, ?_⟩,
      antoineStereo_stereoInv h3⟩
    rw [← hq', antoineComp_compInv]
  · exact h3 (e ▸ antoineStereo_three_lt q)

/-- A null-homotopy pushed forward by a continuous map carrying `U` into `U'`. -/
theorem antoine_homotopicIn_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} {U' : Set Y} {x : X} {γ : Path x x} {f : X → Y} (hf : Continuous f)
    (hfU : ∀ y ∈ U, f y ∈ U') (h : HomotopicIn U γ (Path.refl x)) :
    HomotopicIn U' (γ.map hf) (Path.refl (f x)) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨(F.map ⟨f, hf⟩).cast rfl (by ext; simp), fun z => hfU _ (hF z)⟩

/-- **Antoine's lemma for the top link**, the canonical form of the residual: for `k ≥ 1` the
meridian of `L` is not null-homotopic in `S³ ∖ C_k`, `C_k` the `64^k` links of generation
`k`. -/
def AntoineMeridianEssentialTop : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ¬ HomotopicIn (antoineStereo '' antoineStage k)ᶜ (antoineMeridian.map continuous_antoineStereo)
      (Path.refl _)

/-- The strict residual from the top-link form, by self-similarity (`GX.antoinePhi`). -/
theorem antoineMeridianEssentialStrict_of_top (h : AntoineMeridianEssentialTop) :
    AntoineMeridianEssentialStrict := by
  intro v n m hnm hhom
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  refine h k (by omega) ?_
  have h1 := antoine_homotopicIn_map (U' := (antoineStereo '' antoineStage k)ᶜ)
    (continuous_antoinePhi v n)
    (fun y hy => antoinePhi_mapsTo v n k hy) hhom
  refine antoine_homotopicIn_refl_congr ?_ (fun t => ?_) h1
  · exact antoinePhi_stereo v n _
  · show antoinePhi v n (antoineStereo (antoineComp v n (antoineMeridian t))) =
      antoineStereo (antoineMeridian t)
    exact antoinePhi_stereo v n _

end GX
