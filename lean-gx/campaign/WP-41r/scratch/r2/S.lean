import GXScaffold.Branched.GaloisExamples

noncomputable section
open Set Filter Topology Function unitInterval
namespace GX
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

/-- The modulus `ρ = max(|x|,|y|)` and `ρ² + z²` of `GX.antoinePsi`, read off. -/
theorem antoineD_psi_re (q : ℝ × ℝ × ℝ) :
    (antoinePsi q).re = min 2 (max |q.1| |q.2.1| + max 0 (antoineSq q - 2)) - 7 / 8 := by
  simp [antoinePsi]

theorem antoineD_psi_im (q : ℝ × ℝ × ℝ) :
    (antoinePsi q).im = q.2.2 * max 0 (min 1 (3 - antoineSq q)) := by
  simp [antoinePsi]

theorem antoineD_sq_eq (q : ℝ × ℝ × ℝ) : antoineSq q = (max |q.1| |q.2.1|) ^ 2 + q.2.2 ^ 2 := rfl

/-- Where `Re Ψ < 0`: near the core, and the imaginary part is `z` times a positive factor. -/
theorem antoineD_psi_re_neg {q : ℝ × ℝ × ℝ} (h : (antoinePsi q).re < 0) :
    max |q.1| |q.2.1| < 7 / 8 ∧ antoineSq q < 23 / 8 ∧ 0 < max 0 (min 1 (3 - antoineSq q)) := by
  rw [antoineD_psi_re] at h
  have h1 : max |q.1| |q.2.1| + max 0 (antoineSq q - 2) < 7 / 8 := by
    by_contra hc; push Not at hc
    have : min 2 (max |q.1| |q.2.1| + max 0 (antoineSq q - 2)) ≥ 7 / 8 := le_min (by norm_num) hc
    linarith
  have h2 : 0 ≤ max |q.1| |q.2.1| := (abs_nonneg _).trans (le_max_left _ _)
  have h3 : antoineSq q - 2 ≤ max 0 (antoineSq q - 2) := le_max_right _ _
  have h4 : 0 ≤ max 0 (antoineSq q - 2) := le_max_left _ _
  refine ⟨by linarith, by linarith, lt_max_of_lt_right (lt_min one_pos (by linarith))⟩

theorem antoineD_psi_re_pos {q : ℝ × ℝ × ℝ} (h : 7 / 8 < max |q.1| |q.2.1| ∨ 23 / 8 < antoineSq q) :
    0 < (antoinePsi q).re := by
  rw [antoineD_psi_re]
  have h2 : 0 ≤ max |q.1| |q.2.1| := (abs_nonneg _).trans (le_max_left _ _)
  have h3 : antoineSq q - 2 ≤ max 0 (antoineSq q - 2) := le_max_right _ _
  have h4 : 0 ≤ max 0 (antoineSq q - 2) := le_max_left _ _
  have : 7 / 8 < min 2 (max |q.1| |q.2.1| + max 0 (antoineSq q - 2)) :=
    lt_min (by norm_num) (by rcases h with h | h <;> linarith)
  linarith

theorem antoineD_psi_re_gt {q : ℝ × ℝ × ℝ} (h : 1 < max |q.1| |q.2.1|) :
    1 / 8 < (antoinePsi q).re := by
  rw [antoineD_psi_re]
  have h4 : 0 ≤ max 0 (antoineSq q - 2) := le_max_left _ _
  have : 1 < min 2 (max |q.1| |q.2.1| + max 0 (antoineSq q - 2)) :=
    lt_min (by norm_num) (by linarith)
  linarith

theorem antoineD_psi_re_le {q : ℝ × ℝ × ℝ} (h : (antoinePsi q).re ≤ 1 / 8) :
    max |q.1| |q.2.1| ≤ 1 ∧ antoineSq q ≤ 3 := by
  rw [antoineD_psi_re] at h
  have h1 : max |q.1| |q.2.1| + max 0 (antoineSq q - 2) ≤ 1 := by
    by_contra hc; push Not at hc
    have : min 2 (max |q.1| |q.2.1| + max 0 (antoineSq q - 2)) > 1 := lt_min (by norm_num) hc
    linarith
  have h3 : antoineSq q - 2 ≤ max 0 (antoineSq q - 2) := le_max_right _ _
  have h4 : 0 ≤ max 0 (antoineSq q - 2) := le_max_left _ _
  have h2 : 0 ≤ max |q.1| |q.2.1| := (abs_nonneg _).trans (le_max_left _ _)
  exact ⟨by linarith, by linarith⟩

/-- On the plane of the link and near the centre, `Ψ` is a negative real. -/
theorem antoineD_psi_negReal {q : ℝ × ℝ × ℝ} (hz : q.2.2 = 0) (hρ : max |q.1| |q.2.1| < 1 / 4) :
    (antoinePsi q).im = 0 ∧ (antoinePsi q).re < 0 := by
  refine ⟨by rw [antoineD_psi_im, hz, zero_mul], ?_⟩
  rw [antoineD_psi_re]
  have h2 : 0 ≤ max |q.1| |q.2.1| := (abs_nonneg _).trans (le_max_left _ _)
  have hs : antoineSq q - 2 < 0 := by rw [antoineD_sq_eq, hz]; nlinarith
  rw [max_eq_left hs.le, add_zero, min_eq_right (by linarith)]
  linarith

/-! ### A square root with the slit on the negative axis -/

/-- The principal square root `exp(log w / 2)`. -/
def antoineDSq (w : ℂ) : ℂ := Complex.exp (Complex.log w / 2)

theorem antoineDSq_sq {w : ℂ} (hw : w ≠ 0) : antoineDSq w ^ 2 = w := by
  rw [antoineDSq, sq, ← Complex.exp_add, add_halves, Complex.exp_log hw]

theorem antoineDSq_ne_zero (w : ℂ) : antoineDSq w ≠ 0 := Complex.exp_ne_zero _

theorem continuousAt_antoineDSq {w : ℂ} (hw : w ∈ Complex.slitPlane) : ContinuousAt antoineDSq w :=
  Complex.continuous_exp.continuousAt.comp ((continuousAt_clog hw).div_const 2)

theorem antoineD_exp_half_pi (L a : ℝ) :
    Complex.exp (((L : ℂ) + ((a + Real.pi : ℝ) : ℂ) * Complex.I) / 2) =
      Complex.exp (((L : ℂ) + (a : ℂ) * Complex.I) / 2) * Complex.I := by
  have e : ((L : ℂ) + ((a + Real.pi : ℝ) : ℂ) * Complex.I) / 2 =
      ((L : ℂ) + (a : ℂ) * Complex.I) / 2 + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-- Across the negative axis: `sign(Im w) · √w = i √(-w)` for `Re w < 0`. -/
theorem antoineDSq_neg_axis {w : ℂ} (hw : w.re < 0) :
    (if 0 ≤ w.im then (1 : ℂ) else -1) * antoineDSq w = Complex.I * antoineDSq (-w) := by
  have hn : ‖-w‖ = ‖w‖ := norm_neg w
  have hlog : ∀ z : ℂ, Complex.log z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I :=
    fun z => by apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  simp only [antoineDSq, hlog, hn]
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · rw [if_neg (not_le.2 hi), Complex.arg_neg_eq_arg_add_pi_of_im_neg hi]
    rw [show ((Complex.arg w + Real.pi : ℝ) : ℂ) = ((Complex.arg w + Real.pi : ℝ) : ℂ) from rfl,
      antoineD_exp_half_pi]
    ring_nf; rw [Complex.I_sq]; ring
  · rw [if_pos hi.ge]
    have h1 : Complex.arg w = Real.pi := Complex.arg_eq_pi_iff.2 ⟨hw, hi⟩
    have h2 : Complex.arg (-w) = 0 :=
      Complex.arg_eq_zero_iff.2 ⟨by simp; linarith, by simp [hi]⟩
    rw [h1, h2]
    have := antoineD_exp_half_pi (Real.log ‖w‖) 0
    rw [zero_add] at this
    rw [this]; push_cast; ring
  · rw [if_pos hi.le, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi]
    have := antoineD_exp_half_pi (Real.log ‖w‖) (Complex.arg w - Real.pi)
    rw [sub_add_cancel] at this
    rw [this]; push_cast; ring

/-! ### Combinatorial data of the vertical links -/

/-- The orientation of the vertical link `i`: conjugate `Θᵢ` on the sides `y = -7/8` and
`x = -7/8` (so that `Im Θ'ᵢ ≥ 0` is the outer side of the core square near the link). -/
def AntoineDCj (i : Fin 64) : Prop := i.val / 16 = 0 ∨ i.val / 16 = 3

instance (i : Fin 64) : Decidable (AntoineDCj i) := by unfold AntoineDCj; infer_instance

set_option maxRecDepth 100000 in
theorem antoineD_vert_data : ∀ i : Fin 64,
    (antoineT i = 1 → ((antoineZ i).2 = 560 ∧ ¬ AntoineDCj i ∨ (antoineZ i).2 = -560 ∧ AntoineDCj i) ∧
      |(antoineZ i).1| ≤ 490) ∧
    (antoineT i = 2 → ((antoineZ i).1 = 560 ∧ ¬ AntoineDCj i ∨ (antoineZ i).1 = -560 ∧ AntoineDCj i) ∧
      |(antoineZ i).2| ≤ 490) := by
  decide

/-- Half-widths of the gap boxes of the vertical links. -/
def antoineDGx (i : Fin 64) : ℤ := if antoineT i = 1 then 49 else 0
def antoineDGy (i : Fin 64) : ℤ := if antoineT i = 2 then 49 else 0

set_option maxRecDepth 100000 in
theorem antoineD_gap_sep : ∀ v w : Fin 64, v ≠ w → antoineT v ≠ 0 → antoineT w ≠ 0 →
    antoineDGx v + antoineDGx w < |(antoineZ v).1 - (antoineZ w).1| ∨
      antoineDGy v + antoineDGy w < |(antoineZ v).2 - (antoineZ w).2| := by
  decide

set_option maxRecDepth 100000 in
theorem antoineD_side_h : ∀ m : Fin 9, (∃ i : Fin 64, antoineT i = 0 ∧
    antoineZ i = (140 * (m : ℤ) - 560, 560)) ∧ (∃ i : Fin 64, antoineT i = 0 ∧
    antoineZ i = (140 * (m : ℤ) - 560, -560)) ∧ (∃ i : Fin 64, antoineT i = 0 ∧
    antoineZ i = (560, 140 * (m : ℤ) - 560)) ∧ (∃ i : Fin 64, antoineT i = 0 ∧
    antoineZ i = (-560, 140 * (m : ℤ) - 560)) := by
  decide

set_option maxRecDepth 100000 in
theorem antoineD_side_v : ∀ m : Fin 8, (∃ i : Fin 64, antoineT i = 1 ∧
    antoineZ i = (140 * (m : ℤ) - 490, 560)) ∧ (∃ i : Fin 64, antoineT i = 1 ∧
    antoineZ i = (140 * (m : ℤ) - 490, -560)) ∧ (∃ i : Fin 64, antoineT i = 2 ∧
    antoineZ i = (560, 140 * (m : ℤ) - 490)) ∧ (∃ i : Fin 64, antoineT i = 2 ∧
    antoineZ i = (-560, 140 * (m : ℤ) - 490)) := by
  decide

set_option maxRecDepth 100000 in
theorem antoineD_tube_links : ∀ i : Fin 64, i ≠ 40 →
    antoineEx (antoineT i) + 7 ≤ |(antoineZ i).1| ∨ antoineEy (antoineT i) + 183 ≤ |(antoineZ i).2 - 560| := by
  decide

theorem antoineD_forty : antoineT 40 = 0 ∧ antoineZ 40 = (0, 560) := by decide

set_option maxRecDepth 100000 in
theorem antoineD_tube_horiz : ∀ i : Fin 64, antoineT i = 0 → i ≠ 40 →
    140 ≤ |(antoineZ i).1| ∨ 1000 ≤ |(antoineZ i).2 - 560| := by
  decide

set_option maxRecDepth 100000 in
theorem antoineD_tube_vert : ∀ i : Fin 64, antoineT i = 1 → (antoineZ i).2 = 560 →
    70 ≤ |(antoineZ i).1| := by
  decide

/-! ### The inverse similarities in coordinates -/

theorem antoineD_mapInv0 {i : Fin 64} (h : antoineT i = 0) (p : ℝ × ℝ × ℝ) :
    antoineMapInv i p = ((p.1 - (antoineZ i).1 / 640) * (80 / 7),
      (p.2.1 - (antoineZ i).2 / 640) * (80 / 7), p.2.2 * (80 / 7)) := by
  simp only [antoineMapInv, h, antoinePerm]

theorem antoineD_mapInv1 {i : Fin 64} (h : antoineT i = 1) (p : ℝ × ℝ × ℝ) :
    antoineMapInv i p = ((p.1 - (antoineZ i).1 / 640) * (80 / 7), p.2.2 * (80 / 7),
      (p.2.1 - (antoineZ i).2 / 640) * (80 / 7)) := by
  simp only [antoineMapInv, h, antoinePerm]

theorem antoineD_mapInv2 {i : Fin 64} (h : antoineT i = 2) (p : ℝ × ℝ × ℝ) :
    antoineMapInv i p = (p.2.2 * (80 / 7), (p.2.1 - (antoineZ i).2 / 640) * (80 / 7),
      (p.1 - (antoineZ i).1 / 640) * (80 / 7)) := by
  simp only [antoineMapInv, h, antoinePerm]

theorem antoineD_theta_eq (i : Fin 64) {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    antoineTheta (fun _ => i) 1 y = antoinePsi (antoineMapInv i (antoineStereoInv y)) := by
  simp only [antoineTheta, if_pos hy, antoineCompInv]; rfl

theorem antoineD_theta_pole (i : Fin 64) {y : Sphere3} (hy : ¬ (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    antoineTheta (fun _ => i) 1 y = 9 / 8 := by
  simp only [antoineTheta, if_neg hy]

/-- The slab: `|2z/(|p|²+1)| < 10⁻⁴` with `x² + y² ≤ 8` forces `z` tiny or large. -/
theorem antoineD_slab {x y z : ℝ} (h : |2 * z / (x ^ 2 + y ^ 2 + z ^ 2 + 1)| < 1 / 10000)
    (hxy : x ^ 2 + y ^ 2 ≤ 8) : |z| < 1 / 200 ∨ 3 < |z| := by
  by_contra hc; push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have hN : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 1 := by positivity
  rw [abs_div, abs_of_pos hN, div_lt_iff₀ hN, abs_mul, abs_two] at h
  have hz2 : z ^ 2 ≤ 9 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
  nlinarith

/-! ### The dihedral invariant: definitions -/

/-- The height coordinate of `S³ ⊆ ℝ⁴`: on `antoineStereo p` it is `2z/(|p|²+1)`; it vanishes
exactly on the sphere `{z = 0} ∪ {∞}`. -/
def antoineDTau (y : Sphere3) : ℝ := (y : EuclideanSpace ℝ (Fin 4)) 2

/-- The crossing profile: `0` below the slab `|τ| < 10⁻⁴`, `2` above it, linear in between. -/
def antoineDPhi (τ : ℝ) : ℝ := max 0 (min 2 (1 + 10000 * τ))

/-- `Θ'ᵢ`: the winding invariant of the vertical link `i`, conjugated on two sides. -/
def antoineDTh (i : Fin 64) (y : Sphere3) : ℂ :=
  if AntoineDCj i then starRingEnd ℂ (antoineTheta (fun _ => i) 1 y)
  else antoineTheta (fun _ => i) 1 y

/-- The `32` vertical links. -/
def antoineDV : Finset (Fin 64) := Finset.univ.filter fun i => antoineT i ≠ 0

/-- The product of the `Θ'ᵢ` over the vertical links: its square root defines the double cover
on which the dihedral invariant lives. -/
def antoineDP (y : Sphere3) : ℂ := ∏ i ∈ antoineDV, antoineDTh i y

/-- The product of the principal square roots of the `Θ'ᵢ`. -/
def antoineDQ (y : Sphere3) : ℂ := ∏ i ∈ antoineDV, antoineDSq (antoineDTh i y)

/-- The side of the core square: `-1` strictly inside it and near the plane `z = 0`, `1`
otherwise. -/
def antoineDChi (y : Sphere3) : ℂ :=
  if (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 ∧
      max |(antoineStereoInv y).1| |(antoineStereoInv y).2.1| < 7 / 8 ∧
      |(antoineStereoInv y).2.2| < 1 then -1 else 1

/-- The square root of `GX.antoineDP` on the slab: the sides of the core square swap the sheets,
and so do the cuts of the principal roots in the gaps; the two swaps cancel. -/
def antoineDR (y : Sphere3) : ℂ := antoineDChi y * antoineDQ y

/-- The slab around the sphere `{z = 0} ∪ {∞}`, off the first stage and off the closed holes of
the horizontal links. -/
def antoineDN : Set Sphere3 :=
  {y | y ∈ (antoineStereo '' antoineStage 1)ᶜ ∧ |antoineDTau y| < 1 / 10000 ∧
    ∀ h : Fin 64, antoineT h = 0 → 1 / 8 < (antoineTheta (fun _ => h) 1 y).re}

/-- The dihedral invariant on the double cover `{(y, s) : s² = P y}`: crossing the slab on the
sheet `s = σ R y` turns by `σ · 2π`. -/
def antoineDg (y : Sphere3) (s : ℂ) : ℂ :=
  if y ∈ antoineDN then
    Complex.exp (Real.pi * Complex.I * (s / antoineDR y) * (antoineDPhi (antoineDTau y) : ℂ))
  else 1

/-! ### Basic properties -/

theorem continuous_antoineDTau : Continuous antoineDTau :=
  (PiLp.continuous_apply 2 _ 2).comp continuous_subtype_val

theorem continuous_antoineDPhi : Continuous antoineDPhi := by unfold antoineDPhi; fun_prop

theorem continuous_antoineDTh (i : Fin 64) : Continuous (antoineDTh i) := by
  unfold antoineDTh
  split_ifs
  · exact Complex.continuous_conj.comp (continuous_antoineTheta _ _)
  · exact continuous_antoineTheta _ _

theorem antoineDTh_re (i : Fin 64) (y : Sphere3) :
    (antoineDTh i y).re = (antoineTheta (fun _ => i) 1 y).re := by
  unfold antoineDTh; split_ifs <;> simp

theorem antoineDTh_im (i : Fin 64) (y : Sphere3) :
    (antoineDTh i y).im = if AntoineDCj i then -(antoineTheta (fun _ => i) 1 y).im
      else (antoineTheta (fun _ => i) 1 y).im := by
  unfold antoineDTh; split_ifs <;> simp

theorem antoineDTh_ne_zero (i : Fin 64) {y : Sphere3} (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) :
    antoineDTh i y ≠ 0 := by
  unfold antoineDTh
  have := antoineTheta_ne_zero_of_compl (i := i) hy
  split_ifs
  · exact (map_ne_zero _).2 this
  · exact this

theorem continuous_antoineDP : Continuous antoineDP := by
  unfold antoineDP
  exact continuous_finsetProd _ fun i _ => continuous_antoineDTh i

theorem antoineDP_ne_zero {y : Sphere3} (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) :
    antoineDP y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => antoineDTh_ne_zero i hy

theorem antoineDQ_sq {y : Sphere3} (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) :
    antoineDQ y ^ 2 = antoineDP y := by
  unfold antoineDQ antoineDP
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => antoineDSq_sq (antoineDTh_ne_zero i hy)

theorem antoineDQ_ne_zero (y : Sphere3) : antoineDQ y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => antoineDSq_ne_zero _

theorem antoineDChi_sq (y : Sphere3) : antoineDChi y ^ 2 = 1 := by
  unfold antoineDChi; split_ifs <;> norm_num

theorem antoineDR_sq {y : Sphere3} (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) :
    antoineDR y ^ 2 = antoineDP y := by
  rw [antoineDR, mul_pow, antoineDChi_sq, one_mul, antoineDQ_sq hy]

theorem antoineDR_ne_zero (y : Sphere3) : antoineDR y ≠ 0 :=
  mul_ne_zero (fun h => by have := antoineDChi_sq y; rw [h] at this; norm_num at this)
    (antoineDQ_ne_zero y)

theorem isOpen_antoineDX : IsOpen (antoineStereo '' antoineStage 1)ᶜ :=
  ((antoineStage_isCompact 1).image continuous_antoineStereo).isClosed.isOpen_compl

theorem isOpen_antoineDN : IsOpen antoineDN := by
  have e : antoineDN = (antoineStereo '' antoineStage 1)ᶜ ∩ {y | |antoineDTau y| < 1 / 10000} ∩
      ⋂ h : Fin 64, {y | antoineT h = 0 → 1 / 8 < (antoineTheta (fun _ => h) 1 y).re} := by
    ext y; simp [antoineDN, and_assoc]
  rw [e]
  refine (isOpen_antoineDX.inter (isOpen_lt (continuous_abs.comp continuous_antoineDTau)
    continuous_const)).inter (isOpen_iInter_of_finite fun h => ?_)
  by_cases hh : antoineT h = 0
  · simp only [hh, true_implies]
    exact isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_antoineTheta _ _))
  · simp only [hh, false_implies, setOf_true, isOpen_univ]

theorem antoineD_tau_eq {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    antoineDTau y = 2 * (antoineStereoInv y).2.2 / ((antoineStereoInv y).1 ^ 2 +
      (antoineStereoInv y).2.1 ^ 2 + (antoineStereoInv y).2.2 ^ 2 + 1) := by
  conv_lhs => rw [← antoineStereo_stereoInv hy]
  rfl

/-! ### Local geometry of the vertical links (in `ℝ³`) -/

theorem antoineD_abs_k {a b : ℝ} (h : |a * (80 / 7)| < b) : |a| < b * (7 / 80) := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 80 / 7)] at h; linarith

theorem antoineD_vert_cases {w : Fin 64} (hw : antoineT w ≠ 0) : antoineT w = 1 ∨ antoineT w = 2 := by
  rcases antoineT_cases w with h | h | h
  · exact absurd h hw
  · exact Or.inl h
  · exact Or.inr h

/-- Where `Re Θ_w < 0` (`w` vertical): near the core of `w`, and `Im Θ_w` is the transverse
coordinate `ζ` times a positive factor. -/
theorem antoineD_vert_local {w : Fin 64} (hw : antoineT w ≠ 0) (p : ℝ × ℝ × ℝ)
    (hre : (antoinePsi (antoineMapInv w p)).re < 0) : ∃ κ : ℝ, 0 < κ ∧ |p.2.2| < 49 / 640 ∧
    ((antoineT w = 1 ∧ |p.1 - (antoineZ w).1 / 640| < 49 / 640 ∧
        |p.2.1 - (antoineZ w).2 / 640| < 96 / 640 ∧
        (antoinePsi (antoineMapInv w p)).im = (p.2.1 - (antoineZ w).2 / 640) * (80 / 7) * κ) ∨
      (antoineT w = 2 ∧ |p.2.1 - (antoineZ w).2 / 640| < 49 / 640 ∧
        |p.1 - (antoineZ w).1 / 640| < 96 / 640 ∧
        (antoinePsi (antoineMapInv w p)).im = (p.1 - (antoineZ w).1 / 640) * (80 / 7) * κ)) := by
  obtain ⟨hρ, hsq, hκ⟩ := antoineD_psi_re_neg hre
  refine ⟨_, hκ, ?_⟩
  rw [antoineD_psi_im]
  rcases antoineD_vert_cases hw with h | h
  · rw [antoineD_mapInv1 h] at hρ hsq ⊢
    rw [antoineD_sq_eq] at hsq
    simp only at hρ hsq ⊢
    obtain ⟨h1, h2⟩ := max_lt_iff.1 hρ
    have h3 := antoineD_abs_k h1
    have h4 := antoineD_abs_k h2
    have h0 : 0 ≤ max |(p.1 - (antoineZ w).1 / 640) * (80 / 7)| |p.2.2 * (80 / 7)| :=
      (abs_nonneg _).trans (le_max_left _ _)
    have h5 : ((p.2.1 - (antoineZ w).2 / 640) * (80 / 7)) ^ 2 < 23 / 8 := by nlinarith
    have h6 : |p.2.1 - (antoineZ w).2 / 640| < 96 / 640 := by
      rw [abs_lt]; constructor <;> nlinarith
    refine ⟨by linarith, Or.inl ⟨h, by linarith, h6, by first | rfl | trivial⟩⟩
  · rw [antoineD_mapInv2 h] at hρ hsq ⊢
    rw [antoineD_sq_eq] at hsq
    simp only at hρ hsq ⊢
    obtain ⟨h1, h2⟩ := max_lt_iff.1 hρ
    have h3 := antoineD_abs_k h1
    have h4 := antoineD_abs_k h2
    have h0 : 0 ≤ max |p.2.2 * (80 / 7)| |(p.2.1 - (antoineZ w).2 / 640) * (80 / 7)| :=
      (abs_nonneg _).trans (le_max_left _ _)
    have h5 : ((p.1 - (antoineZ w).1 / 640) * (80 / 7)) ^ 2 < 23 / 8 := by nlinarith
    have h6 : |p.1 - (antoineZ w).1 / 640| < 96 / 640 := by
      rw [abs_lt]; constructor <;> nlinarith
    refine ⟨by linarith, Or.inr ⟨h, by linarith, h6, by first | rfl | trivial⟩⟩

/-- A cut point of `Θ_w` lies in the gap box of `w`. -/
theorem antoineD_cut_box {w : Fin 64} (hw : antoineT w ≠ 0) (p : ℝ × ℝ × ℝ)
    (hre : (antoinePsi (antoineMapInv w p)).re < 0) (him : (antoinePsi (antoineMapInv w p)).im = 0) :
    |p.1 - (antoineZ w).1 / 640| ≤ (antoineDGx w : ℝ) / 640 ∧
      |p.2.1 - (antoineZ w).2 / 640| ≤ (antoineDGy w : ℝ) / 640 := by
  obtain ⟨κ, hκ, -, h⟩ := antoineD_vert_local hw p hre
  rcases h with ⟨h, h1, -, h3⟩ | ⟨h, h1, -, h3⟩
  · rw [him] at h3
    have : p.2.1 - (antoineZ w).2 / 640 = 0 := by
      rcases mul_eq_zero.1 h3.symm with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact h''
        · norm_num at h''
      · exact absurd h' hκ.ne'
    simp only [antoineDGx, antoineDGy, h, if_true, show (1 : Fin 3) ≠ 2 by decide, if_false]
    push_cast
    rw [this, abs_zero]; exact ⟨by linarith, by norm_num⟩
  · rw [him] at h3
    have : p.1 - (antoineZ w).1 / 640 = 0 := by
      rcases mul_eq_zero.1 h3.symm with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact h''
        · norm_num at h''
      · exact absurd h' hκ.ne'
    simp only [antoineDGx, antoineDGy, h, if_true, show (2 : Fin 3) ≠ 1 by decide, if_false]
    push_cast
    rw [this, abs_zero]; exact ⟨by norm_num, by linarith⟩

/-- At most one vertical `Θ_w` is cut at a point. -/
theorem antoineD_cut_unique {v w : Fin 64} (hv : antoineT v ≠ 0) (hw : antoineT w ≠ 0)
    (p : ℝ × ℝ × ℝ) (hrv : (antoinePsi (antoineMapInv v p)).re < 0)
    (hiv : (antoinePsi (antoineMapInv v p)).im = 0) (hrw : (antoinePsi (antoineMapInv w p)).re < 0)
    (hiw : (antoinePsi (antoineMapInv w p)).im = 0) : v = w := by
  by_contra hvw
  obtain ⟨a1, a2⟩ := antoineD_cut_box hv p hrv hiv
  obtain ⟨b1, b2⟩ := antoineD_cut_box hw p hrw hiw
  rcases antoineD_gap_sep v w hvw hv hw with h | h
  · have h' : ((antoineDGx v + antoineDGx w : ℤ) : ℝ) < |((antoineZ v).1 : ℝ) - (antoineZ w).1| := by
      exact_mod_cast h
    push_cast at h'
    rw [lt_abs] at h'; rw [abs_le] at a1 b1
    rcases h' with h' | h' <;> linarith [a1.1, a1.2, b1.1, b1.2]
  · have h' : ((antoineDGy v + antoineDGy w : ℤ) : ℝ) < |((antoineZ v).2 : ℝ) - (antoineZ w).2| := by
      exact_mod_cast h
    push_cast at h'
    rw [lt_abs] at h'; rw [abs_le] at a2 b2
    rcases h' with h' | h' <;> linarith [a2.1, a2.2, b2.1, b2.2]

theorem antoineD_neg_iff {a κ : ℝ} (hκ : 0 < κ) : a * (80 / 7) * κ < 0 ↔ a < 0 := by
  constructor
  · intro h; by_contra h'; push Not at h'
    have := mul_nonneg (mul_nonneg h' (by norm_num : (0 : ℝ) ≤ 80 / 7)) hκ.le; linarith
  · intro h; have := mul_pos (mul_pos (neg_pos.2 h) (by norm_num : (0 : ℝ) < 80 / 7)) hκ; linarith

theorem antoineD_side_aux {a b c s : ℝ} (hs : s = 1 ∨ s = -1) (ha : |a| ≤ 539 / 640)
    (hb : |b - s * (7 / 8)| < 96 / 640) (hc : |c| < 49 / 640) :
    (max |a| |b| < 7 / 8 ∧ |c| < 1) ↔ s * (b - s * (7 / 8)) < 0 := by
  rw [abs_le] at ha; rw [abs_lt] at hb hc
  rcases hs with rfl | rfl
  · rw [max_lt_iff, abs_lt, abs_lt, abs_lt]
    constructor
    · rintro ⟨⟨-, -, h⟩, -⟩; linarith
    · intro h; refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by linarith, by linarith⟩
  · rw [max_lt_iff, abs_lt, abs_lt, abs_lt]
    constructor
    · rintro ⟨⟨-, h, -⟩, -⟩; linarith
    · intro h; refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Near a cut of a vertical `Θ'_w`, the side of the core square is read by `Im Θ'_w`. -/
theorem antoineD_side_of_cut {w : Fin 64} (hw : antoineT w ≠ 0) (p : ℝ × ℝ × ℝ)
    (hre : (antoinePsi (antoineMapInv w p)).re < 0) :
    (max |p.1| |p.2.1| < 7 / 8 ∧ |p.2.2| < 1) ↔
      (if AntoineDCj w then -(antoinePsi (antoineMapInv w p)).im
        else (antoinePsi (antoineMapInv w p)).im) < 0 := by
  obtain ⟨κ, hκ, hz, h⟩ := antoineD_vert_local hw p hre
  obtain ⟨d1, d2⟩ := antoineD_vert_data w
  rcases h with ⟨h, h1, h2, h3⟩ | ⟨h, h1, h2, h3⟩
  · obtain ⟨hc, hc1⟩ := d1 h
    have hc1' : |((antoineZ w).1 : ℝ)| ≤ 490 := by exact_mod_cast hc1
    have ha : |p.1| ≤ 539 / 640 := by
      rw [abs_le] at hc1' ⊢; rw [abs_lt] at h1; constructor <;> linarith [h1.1, h1.2]
    rw [h3]
    rcases hc with ⟨hc, hcj⟩ | ⟨hc, hcj⟩
    · have e : ((antoineZ w).2 : ℝ) / 640 = 1 * (7 / 8) := by rw [hc]; norm_num
      rw [if_neg hcj, antoineD_neg_iff hκ]
      rw [e] at h2 ⊢
      have := antoineD_side_aux (a := p.1) (c := p.2.2) (Or.inl rfl) ha h2 hz
      rw [this, one_mul]
    · have e : ((antoineZ w).2 : ℝ) / 640 = -1 * (7 / 8) := by rw [hc]; norm_num
      rw [if_pos hcj, show -((p.2.1 - (antoineZ w).2 / 640) * (80 / 7) * κ) =
        (-(p.2.1 - (antoineZ w).2 / 640)) * (80 / 7) * κ by ring, antoineD_neg_iff hκ]
      rw [e] at h2 ⊢
      have := antoineD_side_aux (a := p.1) (c := p.2.2) (Or.inr rfl) ha h2 hz
      rw [this, neg_one_mul]
  · obtain ⟨hc, hc1⟩ := d2 h
    have hc1' : |((antoineZ w).2 : ℝ)| ≤ 490 := by exact_mod_cast hc1
    have ha : |p.2.1| ≤ 539 / 640 := by
      rw [abs_le] at hc1' ⊢; rw [abs_lt] at h1; constructor <;> linarith [h1.1, h1.2]
    rw [h3, max_comm]
    rcases hc with ⟨hc, hcj⟩ | ⟨hc, hcj⟩
    · have e : ((antoineZ w).1 : ℝ) / 640 = 1 * (7 / 8) := by rw [hc]; norm_num
      rw [if_neg hcj, antoineD_neg_iff hκ]
      rw [e] at h2 ⊢
      have := antoineD_side_aux (a := p.2.1) (c := p.2.2) (Or.inl rfl) ha h2 hz
      rw [this, one_mul]
    · have e : ((antoineZ w).1 : ℝ) / 640 = -1 * (7 / 8) := by rw [hc]; norm_num
      rw [if_pos hcj, show -((p.1 - (antoineZ w).1 / 640) * (80 / 7) * κ) =
        (-(p.1 - (antoineZ w).1 / 640)) * (80 / 7) * κ by ring, antoineD_neg_iff hκ]
      rw [e] at h2 ⊢
      have := antoineD_side_aux (a := p.2.1) (c := p.2.2) (Or.inr rfl) ha h2 hz
      rw [this, neg_one_mul]

/-- One side of the core square is covered by the `9` horizontal links and the `8` gaps. -/
theorem antoineD_gap1D {u : ℝ} (hu : |u| ≤ 560)
    (h : ∀ m : Fin 9, 56 < |u - (140 * ((m : ℕ) : ℝ) - 560)|) :
    ∃ m : Fin 8, |u - (140 * ((m : ℕ) : ℝ) - 490)| < 14 := by
  rw [abs_le] at hu
  set n := ⌊(u + 560) / 140⌋ with hn
  have hf1 : (n : ℝ) ≤ (u + 560) / 140 := Int.floor_le _
  have hf2 : (u + 560) / 140 < n + 1 := Int.lt_floor_add_one _
  have hn0 : 0 ≤ n := by
    have : (-1 : ℝ) < n := by have : 0 ≤ (u + 560) / 140 := by apply div_nonneg <;> linarith
                              linarith
    have : (-1 : ℤ) < n := by exact_mod_cast this
    omega
  have hn8 : n ≤ 8 := by
    have : (n : ℝ) ≤ 8 := by
      have : (u + 560) / 140 ≤ 8 := by rw [div_le_iff₀ (by norm_num)]; linarith
      linarith
    exact_mod_cast this
  have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    rw [show ((n.toNat : ℕ) : ℝ) = ((n.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg hn0]
  rw [le_div_iff₀ (by norm_num)] at hf1
  rw [div_lt_iff₀ (by norm_num)] at hf2
  have hm := h ⟨n.toNat, by omega⟩
  simp only [hcast] at hm
  by_cases h8 : n = 8
  · exfalso
    have : (n : ℝ) = 8 := by exact_mod_cast h8
    rw [this] at hm hf1
    have hu' : u = 560 := by linarith
    rw [hu'] at hm; norm_num at hm
  have hm' := h ⟨n.toNat + 1, by omega⟩
  simp only [Nat.cast_add, Nat.cast_one, hcast] at hm'
  refine ⟨⟨n.toNat, by omega⟩, ?_⟩
  simp only [hcast]
  rw [lt_abs] at hm hm'
  rw [abs_lt]
  constructor
  · rcases hm with hm | hm <;> linarith
  · rcases hm' with hm' | hm' <;> linarith

theorem antoineD_abs_scale (a v : ℝ) : |(a - v / 640) * (80 / 7)| = |640 * a - v| / 56 := by
  rw [show (a - v / 640) * (80 / 7) = (640 * a - v) / 56 by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 56)]

theorem antoineD_side1 (p : ℝ × ℝ × ℝ) (c : ℤ) (hyc : p.2.1 = (c : ℝ) / 640) (hx : |p.1| ≤ 7 / 8)
    (hz : |p.2.2| < 1 / 200)
    (hH : ∀ m : Fin 9, ∃ i, antoineT i = 0 ∧ antoineZ i = (140 * ((m : ℕ) : ℤ) - 560, c))
    (hV : ∀ m : Fin 8, ∃ i, antoineT i = 1 ∧ antoineZ i = (140 * ((m : ℕ) : ℤ) - 490, c))
    (hN : ∀ h : Fin 64, antoineT h = 0 → 1 < max |(p.1 - (antoineZ h).1 / 640) * (80 / 7)|
      |(p.2.1 - (antoineZ h).2 / 640) * (80 / 7)|) :
    ∃ w, antoineT w ≠ 0 ∧ (antoinePsi (antoineMapInv w p)).re < 0 ∧
      (antoinePsi (antoineMapInv w p)).im = 0 := by
  have hu : |640 * p.1| ≤ 560 := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 640)]; linarith
  obtain ⟨m, hm⟩ := antoineD_gap1D hu fun m => by
    obtain ⟨i, hi0, hiZ⟩ := hH m
    have := hN i hi0
    rw [hiZ, hyc] at this
    simp only [sub_self, zero_mul, abs_zero] at this
    rw [max_eq_left (abs_nonneg _), antoineD_abs_scale] at this
    push_cast at this
    rw [lt_div_iff₀ (by norm_num)] at this
    linarith
  obtain ⟨w, hw1, hwZ⟩ := hV m
  refine ⟨w, by rw [hw1]; decide, ?_⟩
  rw [antoineD_mapInv1 hw1, hwZ]
  refine and_comm.1 (antoineD_psi_negReal ?_ ?_)
  · dsimp only; rw [hyc]; ring
  dsimp only
  rw [max_lt_iff, antoineD_abs_scale]
  push_cast
  constructor
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 80 / 7)]; linarith

theorem antoineD_side2 (p : ℝ × ℝ × ℝ) (c : ℤ) (hxc : p.1 = (c : ℝ) / 640) (hy : |p.2.1| ≤ 7 / 8)
    (hz : |p.2.2| < 1 / 200)
    (hH : ∀ m : Fin 9, ∃ i, antoineT i = 0 ∧ antoineZ i = (c, 140 * ((m : ℕ) : ℤ) - 560))
    (hV : ∀ m : Fin 8, ∃ i, antoineT i = 2 ∧ antoineZ i = (c, 140 * ((m : ℕ) : ℤ) - 490))
    (hN : ∀ h : Fin 64, antoineT h = 0 → 1 < max |(p.1 - (antoineZ h).1 / 640) * (80 / 7)|
      |(p.2.1 - (antoineZ h).2 / 640) * (80 / 7)|) :
    ∃ w, antoineT w ≠ 0 ∧ (antoinePsi (antoineMapInv w p)).re < 0 ∧
      (antoinePsi (antoineMapInv w p)).im = 0 := by
  have hu : |640 * p.2.1| ≤ 560 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 640)]; linarith
  obtain ⟨m, hm⟩ := antoineD_gap1D hu fun m => by
    obtain ⟨i, hi0, hiZ⟩ := hH m
    have := hN i hi0
    rw [hiZ, hxc] at this
    simp only [sub_self, zero_mul, abs_zero] at this
    rw [max_eq_right (abs_nonneg _), antoineD_abs_scale] at this
    push_cast at this
    rw [lt_div_iff₀ (by norm_num)] at this
    linarith
  obtain ⟨w, hw1, hwZ⟩ := hV m
  refine ⟨w, by rw [hw1]; decide, ?_⟩
  rw [antoineD_mapInv2 hw1, hwZ]
  refine and_comm.1 (antoineD_psi_negReal ?_ ?_)
  · dsimp only; rw [hxc]; ring
  dsimp only
  rw [max_lt_iff, antoineD_abs_scale]
  push_cast
  constructor
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 80 / 7)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **The gaps carry the cuts**: a point of the core square near the plane `z = 0`, outside the
closed holes of the horizontal links, is a cut point of the root of some vertical `Θ_w`. -/
theorem antoineD_square_cut (p : ℝ × ℝ × ℝ) (hz : |p.2.2| < 1 / 200) (hρ : max |p.1| |p.2.1| = 7 / 8)
    (hN : ∀ h : Fin 64, antoineT h = 0 → 1 < max |(p.1 - (antoineZ h).1 / 640) * (80 / 7)|
      |(p.2.1 - (antoineZ h).2 / 640) * (80 / 7)|) :
    ∃ w, antoineT w ≠ 0 ∧ (antoinePsi (antoineMapInv w p)).re < 0 ∧
      (antoinePsi (antoineMapInv w p)).im = 0 := by
  rcases max_eq_iff.1 hρ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at h2
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 7 / 8)).1 h1 with e | e
    · exact antoineD_side2 p 560 (by rw [e]; norm_num) h2 hz (fun m => (antoineD_side_h m).2.2.1)
        (fun m => (antoineD_side_v m).2.2.1) hN
    · exact antoineD_side2 p (-560) (by rw [e]; norm_num) h2 hz (fun m => (antoineD_side_h m).2.2.2)
        (fun m => (antoineD_side_v m).2.2.2) hN
  · rw [h1] at h2
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 7 / 8)).1 h1 with e | e
    · exact antoineD_side1 p 560 (by rw [e]; norm_num) h2 hz (fun m => (antoineD_side_h m).1)
        (fun m => (antoineD_side_v m).1) hN
    · exact antoineD_side1 p (-560) (by rw [e]; norm_num) h2 hz (fun m => (antoineD_side_h m).2.1)
        (fun m => (antoineD_side_v m).2.1) hN

/-! ### The horizontal links in the slab -/

theorem antoineD_horiz_out {h : Fin 64} (hT : antoineT h = 0) (p : ℝ × ℝ × ℝ) (hz : |p.2.2| < 1 / 200)
    (hre : 1 / 8 < (antoinePsi (antoineMapInv h p)).re) :
    1 < max |(p.1 - (antoineZ h).1 / 640) * (80 / 7)| |(p.2.1 - (antoineZ h).2 / 640) * (80 / 7)| := by
  by_contra hle; push Not at hle
  rw [antoineD_mapInv0 hT, antoineD_psi_re] at hre
  rw [antoineD_sq_eq] at hre
  simp only at hre
  set m := max |(p.1 - (antoineZ h).1 / 640) * (80 / 7)| |(p.2.1 - (antoineZ h).2 / 640) * (80 / 7)|
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (le_max_left _ _)
  have hz2 : (p.2.2 * (80 / 7)) ^ 2 < 1 := by
    rw [← sq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 80 / 7)]; nlinarith [abs_nonneg p.2.2]
  rw [max_eq_left (by nlinarith), add_zero, min_eq_right (by linarith)] at hre
  linarith

theorem antoineD_horiz_strict {h : Fin 64} (hT : antoineT h = 0) {p : ℝ × ℝ × ℝ}
    (hp : p ∉ antoineStage 1) (hz : |p.2.2| < 1 / 200)
    (hre : (antoinePsi (antoineMapInv h p)).re ≤ 1 / 8) : (antoinePsi (antoineMapInv h p)).re < 1 / 8 := by
  obtain ⟨hρ, -⟩ := antoineD_psi_re_le hre
  have hzk : |(antoineMapInv h p).2.2| ≤ 1 / 8 := by
    rw [antoineD_mapInv0 hT]; simp only
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 80 / 7)]; linarith
  by_cases h34 : 3 / 4 ≤ max |(antoineMapInv h p).1| |(antoineMapInv h p).2.1|
  · exfalso; apply hp
    rw [antoineStage_one_eq]
    exact mem_iUnion.2 ⟨h, antoineMapInv h p, ⟨hzk, hρ, h34⟩, antoineMap_mapInv h p⟩
  · push Not at h34
    rw [antoineD_psi_re, antoineD_sq_eq]
    set m := max |(antoineMapInv h p).1| |(antoineMapInv h p).2.1|
    have hm0 : 0 ≤ m := (abs_nonneg _).trans (le_max_left _ _)
    have hz2 : (antoineMapInv h p).2.2 ^ 2 ≤ 1 / 64 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (antoineMapInv h p).2.2]
    rw [max_eq_left (by nlinarith), add_zero, min_eq_right (by linarith)]
    linarith

/-! ### The slab in `S³` -/

theorem antoineD_mem_X_iff {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1) :
    y ∈ (antoineStereo '' antoineStage 1)ᶜ ↔ antoineStereoInv y ∉ antoineStage 1 := by
  constructor
  · intro h h'; exact h ⟨_, h', antoineStereo_stereoInv hy⟩
  · rintro h ⟨q, hq, rfl⟩; rw [antoineStereoInv_stereo] at h; exact h hq

theorem antoineD_slab_y {y : Sphere3} (hy : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1)
    (hτ : |antoineDTau y| < 1 / 10000)
    (hxy : (antoineStereoInv y).1 ^ 2 + (antoineStereoInv y).2.1 ^ 2 ≤ 8) :
    |(antoineStereoInv y).2.2| < 1 / 200 ∨ 3 < |(antoineStereoInv y).2.2| := by
  rw [antoineD_tau_eq hy] at hτ
  exact antoineD_slab hτ hxy

/-- In the slab, a point where `Re Θ_h ≤ 1/8` (`h` horizontal) has `Re Θ_h < 1/8`: the slab is
cut by the closed holes along the first stage only. -/
theorem antoineD_horiz_strict_y {h : Fin 64} (hT : antoineT h = 0) {y : Sphere3}
    (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) (hτ : |antoineDTau y| < 1 / 10000)
    (hre : (antoineTheta (fun _ => h) 1 y).re ≤ 1 / 8) : (antoineTheta (fun _ => h) 1 y).re < 1 / 8 := by
  by_cases h3 : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1
  · rw [antoineD_theta_eq h h3] at hre ⊢
    set p := antoineStereoInv y
    obtain ⟨hρ, hsq⟩ := antoineD_psi_re_le hre
    rw [antoineD_mapInv0 hT] at hρ hsq
    rw [antoineD_sq_eq] at hsq
    simp only at hρ hsq
    obtain ⟨h1, h2⟩ := max_le_iff.1 hρ
    rw [antoineD_abs_scale, div_le_one (by norm_num)] at h1 h2
    have hc := antoine_centre_mem h
    have hc' : |((antoineZ h).1 : ℝ)| ≤ 560 ∧ |((antoineZ h).2 : ℝ)| ≤ 560 := by
      rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
      · exact ⟨by exact_mod_cast c1.le, by exact_mod_cast c2⟩
      · exact ⟨by exact_mod_cast c2, by exact_mod_cast c1.le⟩
    have hx : |p.1| ≤ 1 := by
      have := hc'.1; rw [abs_le] at this h1 ⊢; constructor <;> linarith [h1.1, h1.2]
    have hy' : |p.2.1| ≤ 1 := by
      have := hc'.2; rw [abs_le] at this h2 ⊢; constructor <;> linarith [h2.1, h2.2]
    have hxy : p.1 ^ 2 + p.2.1 ^ 2 ≤ 8 := by
      have := sq_abs p.1; have := sq_abs p.2.1
      nlinarith [abs_nonneg p.1, abs_nonneg p.2.1]
    have hm0 : 0 ≤ max |(p.1 - (antoineZ h).1 / 640) * (80 / 7)| |(p.2.1 - (antoineZ h).2 / 640) * (80 / 7)| :=
      (abs_nonneg _).trans (le_max_left _ _)
    have hz3 : |p.2.2| ≤ 3 := by
      have : (p.2.2 * (80 / 7)) ^ 2 ≤ 3 := by nlinarith
      nlinarith [sq_abs p.2.2, abs_nonneg p.2.2]
    rcases antoineD_slab_y h3 hτ hxy with hz | hz
    · exact antoineD_horiz_strict hT ((antoineD_mem_X_iff h3).1 hy) hz (by
        rw [← antoineD_theta_eq h h3]; rw [antoineD_theta_eq h h3]; exact hre)
    · linarith
  · rw [antoineD_theta_pole h h3] at hre; norm_num at hre

/-! ### The root `GX.antoineDR` is continuous on the slab -/

theorem antoineD_mem_V {w : Fin 64} : w ∈ antoineDV ↔ antoineT w ≠ 0 := by
  simp [antoineDV]

theorem antoineD_cut_of_not_slit {w : Fin 64} {y : Sphere3}
    (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) (h : antoineDTh w y ∉ Complex.slitPlane) :
    (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 ∧
      (antoinePsi (antoineMapInv w (antoineStereoInv y))).re < 0 ∧
      (antoinePsi (antoineMapInv w (antoineStereoInv y))).im = 0 := by
  rw [Complex.mem_slitPlane_iff] at h; push Not at h
  obtain ⟨h1, h2⟩ := h
  have h3 : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 := by
    by_contra h3
    rw [antoineDTh_re, antoineD_theta_pole w h3] at h1; norm_num at h1
  rw [antoineDTh_re, antoineD_theta_eq w h3] at h1
  rw [antoineDTh_im, antoineD_theta_eq w h3] at h2
  have h2' : (antoinePsi (antoineMapInv w (antoineStereoInv y))).im = 0 := by
    split_ifs at h2 <;> linarith
  refine ⟨h3, lt_of_le_of_ne h1 fun h0 => ?_, h2'⟩
  apply antoineDTh_ne_zero w hy
  apply Complex.ext
  · rw [antoineDTh_re, antoineD_theta_eq w h3, h0]; rfl
  · rw [antoineDTh_im, antoineD_theta_eq w h3, h2']; simp

theorem antoineD_not_slit_of_cut {w : Fin 64} {y : Sphere3} (h3 : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1)
    (hre : (antoinePsi (antoineMapInv w (antoineStereoInv y))).re < 0)
    (him : (antoinePsi (antoineMapInv w (antoineStereoInv y))).im = 0) :
    antoineDTh w y ∉ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, antoineDTh_re, antoineDTh_im, antoineD_theta_eq w h3, him]
  push Not
  exact ⟨hre.le, by split_ifs <;> simp⟩

theorem antoineD_N_horiz {y : Sphere3} (hN : y ∈ antoineDN) (h3 : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1)
    (hz : |(antoineStereoInv y).2.2| < 1 / 200) (h : Fin 64) (hT : antoineT h = 0) :
    1 < max |((antoineStereoInv y).1 - (antoineZ h).1 / 640) * (80 / 7)|
      |((antoineStereoInv y).2.1 - (antoineZ h).2 / 640) * (80 / 7)| := by
  have := hN.2.2 h hT
  rw [antoineD_theta_eq h h3] at this
  exact antoineD_horiz_out hT _ hz this

theorem antoineD_chi_eventually {y₀ : Sphere3} (hN : y₀ ∈ antoineDN)
    (hs : ∀ v ∈ antoineDV, antoineDTh v y₀ ∈ Complex.slitPlane) :
    ∀ᶠ y in 𝓝 y₀, antoineDChi y = antoineDChi y₀ := by
  have hc3 : Continuous fun z : Sphere3 => (z : EuclideanSpace ℝ (Fin 4)) 3 :=
    (PiLp.continuous_apply 2 _ 3).comp continuous_subtype_val
  by_cases h3 : (y₀ : EuclideanSpace ℝ (Fin 4)) 3 < 1
  · have hcs := continuousAt_antoineStereoInv h3
    have hcm : ContinuousAt (fun y => max |(antoineStereoInv y).1| |(antoineStereoInv y).2.1|) y₀ :=
      ((continuous_abs.comp continuous_fst).max
        (continuous_abs.comp (continuous_fst.comp continuous_snd))).continuousAt.comp hcs
    have hcz : ContinuousAt (fun y => |(antoineStereoInv y).2.2|) y₀ :=
      (continuous_abs.comp (continuous_snd.comp continuous_snd)).continuousAt.comp hcs
    have e3 : ∀ᶠ y : Sphere3 in 𝓝 y₀, (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 :=
      hc3.continuousAt.eventually_lt continuousAt_const h3
    by_cases hc : max |(antoineStereoInv y₀).1| |(antoineStereoInv y₀).2.1| < 7 / 8 ∧
        |(antoineStereoInv y₀).2.2| < 1
    · filter_upwards [e3, hcm.eventually_lt continuousAt_const hc.1,
        hcz.eventually_lt continuousAt_const hc.2] with y a b c
      unfold antoineDChi; rw [if_pos ⟨a, b, c⟩, if_pos ⟨h3, hc⟩]
    · have hχ : antoineDChi y₀ = 1 := by unfold antoineDChi; rw [if_neg fun h => hc h.2]
      rw [hχ]
      by_cases hm : 7 / 8 < max |(antoineStereoInv y₀).1| |(antoineStereoInv y₀).2.1|
      · filter_upwards [continuousAt_const.eventually_lt hcm hm] with y hy
        unfold antoineDChi; rw [if_neg fun h => by linarith [h.2.1]]
      by_cases hz : 1 < |(antoineStereoInv y₀).2.2|
      · filter_upwards [continuousAt_const.eventually_lt hcz hz] with y hy
        unfold antoineDChi; rw [if_neg fun h => by linarith [h.2.2]]
      exfalso
      push Not at hm hz
      have hm0 : 0 ≤ max |(antoineStereoInv y₀).1| |(antoineStereoInv y₀).2.1| :=
        (abs_nonneg _).trans (le_max_left _ _)
      have hxy : (antoineStereoInv y₀).1 ^ 2 + (antoineStereoInv y₀).2.1 ^ 2 ≤ 8 := by
        have a := le_max_left |(antoineStereoInv y₀).1| |(antoineStereoInv y₀).2.1|
        have b := le_max_right |(antoineStereoInv y₀).1| |(antoineStereoInv y₀).2.1|
        nlinarith [sq_abs (antoineStereoInv y₀).1, sq_abs (antoineStereoInv y₀).2.1,
          abs_nonneg (antoineStereoInv y₀).1, abs_nonneg (antoineStereoInv y₀).2.1]
      rcases antoineD_slab_y h3 hN.2.1 hxy with hz' | hz'
      · have hm' : max |(antoineStereoInv y₀).1| |(antoineStereoInv y₀).2.1| = 7 / 8 := by
          by_contra hne
          exact hc ⟨lt_of_le_of_ne hm hne, by linarith⟩
        obtain ⟨w, hw, hre, him⟩ :=
          antoineD_square_cut _ hz' hm' (antoineD_N_horiz hN h3 hz')
        exact antoineD_not_slit_of_cut h3 hre him (hs w (antoineD_mem_V.2 hw))
      · linarith
  · have hχ : antoineDChi y₀ = 1 := by unfold antoineDChi; rw [if_neg fun h => h3 h.1]
    rw [hχ]
    push Not at h3
    filter_upwards [continuousAt_const.eventually_lt hc3.continuousAt
      (show (19 / 20 : ℝ) < (y₀ : EuclideanSpace ℝ (Fin 4)) 3 by linarith)] with y hy
    unfold antoineDChi
    rw [if_neg]
    rintro ⟨a, b, c⟩
    have h4 := antoineStereoInv_sq_ge hy a
    unfold antoineSq at h4
    have hm0 : 0 ≤ max |(antoineStereoInv y).1| |(antoineStereoInv y).2.1| :=
      (abs_nonneg _).trans (le_max_left _ _)
    nlinarith [sq_abs (antoineStereoInv y).2.2, abs_nonneg (antoineStereoInv y).2.2]

theorem antoineD_chi_cut {w : Fin 64} (hw : w ∈ antoineDV) {y : Sphere3}
    (hre : (antoineTheta (fun _ => w) 1 y).re < 0) :
    antoineDChi y * antoineDSq (antoineDTh w y) = Complex.I * antoineDSq (-antoineDTh w y) := by
  have h3 : (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 := by
    by_contra h3; rw [antoineD_theta_pole w h3] at hre; norm_num at hre
  have hre' : (antoineDTh w y).re < 0 := by rw [antoineDTh_re]; exact hre
  rw [← antoineDSq_neg_axis hre']
  congr 1
  rw [antoineD_theta_eq w h3] at hre
  have hside := antoineD_side_of_cut (antoineD_mem_V.1 hw) _ hre
  unfold antoineDChi
  simp only [h3, true_and]
  rw [antoineDTh_im, antoineD_theta_eq w h3]
  by_cases hc : max |(antoineStereoInv y).1| |(antoineStereoInv y).2.1| < 7 / 8 ∧
      |(antoineStereoInv y).2.2| < 1
  · rw [if_pos hc, if_neg (not_le.2 (hside.1 hc))]
  · rw [if_neg hc, if_pos (not_lt.1 fun h => hc (hside.2 h))]

/-- **The root is continuous on the slab**: where a vertical root is cut, the side of the core
square flips with it (`GX.antoineD_chi_cut`); elsewhere the side is locally constant, because
the core square meets the slab only in the gaps, where a root is cut
(`GX.antoineD_square_cut`). This is where the closing of the chain enters. -/
theorem continuousAt_antoineDR {y₀ : Sphere3} (hN : y₀ ∈ antoineDN) : ContinuousAt antoineDR y₀ := by
  by_cases hA : ∃ w ∈ antoineDV, antoineDTh w y₀ ∉ Complex.slitPlane
  · obtain ⟨w, hwV, hw⟩ := hA
    obtain ⟨h3, hre, him⟩ := antoineD_cut_of_not_slit hN.1 hw
    have hother : ∀ v ∈ antoineDV.erase w, antoineDTh v y₀ ∈ Complex.slitPlane := by
      intro v hv
      obtain ⟨hvw, hvV⟩ := Finset.mem_erase.1 hv
      by_contra hc
      obtain ⟨-, hre', him'⟩ := antoineD_cut_of_not_slit hN.1 hc
      exact hvw (antoineD_cut_unique (antoineD_mem_V.1 hvV) (antoineD_mem_V.1 hwV) _ hre' him' hre him)
    have hre0 : (antoineTheta (fun _ => w) 1 y₀).re < 0 := by rw [antoineD_theta_eq w h3]; exact hre
    have hU : ∀ᶠ y in 𝓝 y₀, (antoineTheta (fun _ => w) 1 y).re < 0 :=
      (Complex.continuous_re.comp (continuous_antoineTheta _ _)).continuousAt.eventually_lt
        continuousAt_const hre0
    have hneg : -antoineDTh w y₀ ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      rw [Complex.neg_re, antoineDTh_re]; linarith
    have h1 : ContinuousAt (fun y => antoineDSq (-antoineDTh w y)) y₀ :=
      (continuousAt_antoineDSq hneg).comp (f := fun y => -antoineDTh w y)
        (continuous_antoineDTh w).neg.continuousAt
    have h2 : ContinuousAt (fun y => ∏ v ∈ antoineDV.erase w, antoineDSq (antoineDTh v y)) y₀ :=
      tendsto_finsetProd (f := fun v y => antoineDSq (antoineDTh v y))
        (a := fun v => antoineDSq (antoineDTh v y₀)) _ fun v hv =>
          (continuousAt_antoineDSq (hother v hv)).comp (continuous_antoineDTh v).continuousAt
    have hF : ContinuousAt (fun y => Complex.I * antoineDSq (-antoineDTh w y) *
        ∏ v ∈ antoineDV.erase w, antoineDSq (antoineDTh v y)) y₀ :=
      (continuousAt_const.mul h1).mul h2
    refine hF.congr ?_
    filter_upwards [hU] with y hy
    unfold antoineDR antoineDQ
    rw [← Finset.mul_prod_erase _ _ hwV, ← mul_assoc, antoineD_chi_cut hwV hy]
  · push Not at hA
    have hχ : ContinuousAt antoineDChi y₀ :=
      continuousAt_const.congr (Filter.EventuallyEq.symm (antoineD_chi_eventually hN hA))
    have h2 : ContinuousAt antoineDQ y₀ :=
      tendsto_finsetProd (f := fun v y => antoineDSq (antoineDTh v y))
        (a := fun v => antoineDSq (antoineDTh v y₀)) _ fun v hv =>
          (continuousAt_antoineDSq (hA v hv)).comp (continuous_antoineDTh v).continuousAt
    exact hχ.mul h2

/-! ### The invariant is continuous on the double cover -/

theorem antoineD_sigma_sq {y : Sphere3} (hy : y ∈ (antoineStereo '' antoineStage 1)ᶜ) {s : ℂ}
    (hs : s ^ 2 = antoineDP y) : (s / antoineDR y) ^ 2 = 1 := by
  rw [div_pow, hs, antoineDR_sq hy, div_self (antoineDP_ne_zero hy)]

theorem antoineD_sigma_cases {e : ℂ} (h : e ^ 2 = 1) : e = 1 ∨ e = -1 := by
  rw [sq] at h; exact mul_self_eq_one_iff.1 h

theorem antoineD_phi_ends {τ : ℝ} (h : 1 / 10000 ≤ |τ|) : antoineDPhi τ = 0 ∨ antoineDPhi τ = 2 := by
  unfold antoineDPhi
  rcases le_abs'.1 h with h | h
  · left; exact max_eq_left ((min_le_right _ _).trans (by linarith))
  · right; rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem antoineD_exp_ends {e : ℂ} (he : e = 1 ∨ e = -1) {φ : ℝ} (hφ : φ = 0 ∨ φ = 2) :
    Complex.exp (Real.pi * Complex.I * e * (φ : ℂ)) = 1 := by
  rcases hφ with rfl | rfl
  · simp
  · rcases he with rfl | rfl
    · rw [show (Real.pi : ℂ) * Complex.I * 1 * ((2 : ℝ) : ℂ) = 2 * Real.pi * Complex.I by push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    · rw [show (Real.pi : ℂ) * Complex.I * (-1) * ((2 : ℝ) : ℂ) = -(2 * Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

theorem antoineD_norm_exp_sub_one {e : ℂ} (he : e = 1 ∨ e = -1) (φ : ℝ) :
    ‖Complex.exp (Real.pi * Complex.I * e * (φ : ℂ)) - 1‖ =
      ‖Complex.exp (Real.pi * Complex.I * (φ : ℂ)) - 1‖ := by
  rcases he with rfl | rfl
  · rw [mul_one]
  · have e : Complex.exp (Real.pi * Complex.I * (-1) * (φ : ℂ)) =
        starRingEnd ℂ (Complex.exp (Real.pi * Complex.I * (φ : ℂ))) := by
      rw [← Complex.exp_conj]; congr 1
      simp [Complex.conj_ofReal]
    rw [e, show starRingEnd ℂ (Complex.exp (Real.pi * Complex.I * (φ : ℂ))) - 1 =
      starRingEnd ℂ (Complex.exp (Real.pi * Complex.I * (φ : ℂ)) - 1) by simp, Complex.norm_conj]

/-- **The invariant on the double cover is continuous**: along any continuous `F` into
`S³ ∖ C₁` with a continuous square root `S` of `P ∘ F`, `z ↦ g (F z) (S z)` is continuous. -/
theorem continuous_antoineDg {Z : Type*} [TopologicalSpace Z] {F : Z → Sphere3} (hF : Continuous F)
    (hFX : ∀ z, F z ∈ (antoineStereo '' antoineStage 1)ᶜ) {S : Z → ℂ} (hS : Continuous S)
    (hSq : ∀ z, S z ^ 2 = antoineDP (F z)) : Continuous fun z => antoineDg (F z) (S z) := by
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  by_cases hN : F z₀ ∈ antoineDN
  · have hev : ∀ᶠ z in 𝓝 z₀, F z ∈ antoineDN :=
      hF.continuousAt.preimage_mem_nhds (isOpen_antoineDN.mem_nhds hN)
    have hR : ContinuousAt (fun z => antoineDR (F z)) z₀ :=
      (continuousAt_antoineDR hN).comp hF.continuousAt
    have hc : ContinuousAt (fun z => Complex.exp (Real.pi * Complex.I * (S z / antoineDR (F z)) *
        (antoineDPhi (antoineDTau (F z)) : ℂ))) z₀ := by
      have h1 : ContinuousAt (fun z => S z / antoineDR (F z)) z₀ :=
        hS.continuousAt.div hR (antoineDR_ne_zero _)
      have h2 : Continuous fun z => (antoineDPhi (antoineDTau (F z)) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_antoineDPhi.comp (continuous_antoineDTau.comp hF))
      exact Complex.continuous_exp.continuousAt.comp ((continuousAt_const.mul h1).mul h2.continuousAt)
    refine hc.congr ?_
    filter_upwards [hev] with z hz
    simp only [antoineDg, if_pos hz]
  · have hg0 : antoineDg (F z₀) (S z₀) = 1 := by simp only [antoineDg, if_neg hN]
    by_cases hτ : |antoineDTau (F z₀)| < 1 / 10000
    · -- in the slab, off `N`: some horizontal `Re Θ_h ≤ 1/8`, hence `< 1/8` nearby
      have : ¬ ∀ h : Fin 64, antoineT h = 0 → 1 / 8 < (antoineTheta (fun _ => h) 1 (F z₀)).re :=
        fun h => hN ⟨hFX z₀, hτ, h⟩
      push Not at this
      obtain ⟨h, hT, hle⟩ := this
      have hlt := antoineD_horiz_strict_y hT (hFX z₀) hτ hle
      have hev : ∀ᶠ z in 𝓝 z₀, (antoineTheta (fun _ => h) 1 (F z)).re < 1 / 8 :=
        ((Complex.continuous_re.comp (continuous_antoineTheta _ _)).comp hF).continuousAt.eventually_lt
          continuousAt_const hlt
      refine (continuousAt_const (y := (1 : ℂ))).congr ?_
      filter_upwards [hev] with z hz
      simp only [antoineDg]
      rw [if_neg fun hN' => by linarith [hN'.2.2 h hT]]
    · -- off the slab: squeeze against `exp(iπφ)`, which is `1` at `z₀`
      push Not at hτ
      have hG' : Continuous fun z => Complex.exp (Real.pi * Complex.I *
          (antoineDPhi (antoineDTau (F z)) : ℂ)) :=
        Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_antoineDPhi.comp (continuous_antoineDTau.comp hF))))
      have hG'0 : Complex.exp (Real.pi * Complex.I * (antoineDPhi (antoineDTau (F z₀)) : ℂ)) = 1 := by
        have := antoineD_exp_ends (e := 1) (Or.inl rfl) (antoineD_phi_ends hτ)
        rwa [mul_one] at this
      have ht : Tendsto (fun z => Complex.exp (Real.pi * Complex.I *
          (antoineDPhi (antoineDTau (F z)) : ℂ))) (𝓝 z₀) (𝓝 1) := by
        have := hG'.continuousAt (x := z₀); rwa [ContinuousAt, hG'0] at this
      show Tendsto _ (𝓝 z₀) (𝓝 (antoineDg (F z₀) (S z₀)))
      rw [hg0, tendsto_iff_norm_sub_tendsto_zero]
      have ht' := (tendsto_iff_norm_sub_tendsto_zero.1 ht)
      refine squeeze_zero (fun _ => norm_nonneg _) (fun z => ?_) ht'
      by_cases hz : F z ∈ antoineDN
      · simp only [antoineDg, if_pos hz]
        rw [antoineD_norm_exp_sub_one (antoineD_sigma_cases (antoineD_sigma_sq (hFX z) (hSq z)))]
      · simp only [antoineDg, if_neg hz, sub_self, norm_zero]; exact norm_nonneg _

/-! ### A tube around the meridian -/

section Tube

variable {p : ℝ × ℝ × ℝ} (hx : |p.1| < 1 / 100) (hlo : 1 / 49 < (p.2.1 - 7 / 8) ^ 2 + p.2.2 ^ 2)
  (hhi : (p.2.1 - 7 / 8) ^ 2 + p.2.2 ^ 2 < 4 / 49)
include hx hlo hhi

theorem antoineD_tube_b1 : |p.2.1 - 7 / 8| < 2 / 7 := by
  have : (p.2.1 - 7 / 8) ^ 2 < (2 / 7) ^ 2 := by nlinarith [sq_nonneg p.2.2]
  exact abs_lt_of_sq_lt_sq this (by norm_num)

theorem antoineD_tube_b2 : |p.2.2| < 2 / 7 := by
  have : p.2.2 ^ 2 < (2 / 7) ^ 2 := by nlinarith [sq_nonneg (p.2.1 - 7 / 8)]
  exact abs_lt_of_sq_lt_sq this (by norm_num)

theorem antoineD_tube_xy : p.1 ^ 2 + p.2.1 ^ 2 ≤ 8 := by
  have h1 := antoineD_tube_b1 hx hlo hhi
  rw [abs_lt] at hx h1
  nlinarith

theorem antoineD_tube_notMem : p ∉ antoineStage 1 := by
  have h1 := antoineD_tube_b1 hx hlo hhi
  have h2 := antoineD_tube_b2 hx hlo hhi
  intro hp
  rw [antoineStage_one_eq] at hp
  obtain ⟨i, q, hq, rfl⟩ := mem_iUnion.1 hp
  obtain ⟨b1, b2, b3⟩ := antoineMap_bounds i hq
  by_cases hi : i = 40
  · subst hi
    obtain ⟨hT, hZ⟩ := antoineD_forty
    have hz : |(antoineMap 40 q).2.2| ≤ 7 / 640 := by
      have := hq.1
      simp only [antoineMap, hT, antoinePerm]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 80)]; nlinarith [abs_nonneg q.2.2]
    rw [hT, hZ] at b2
    simp only [antoineEy] at b2
    push_cast at b2
    have e : ((antoineMap 40 q).2.1 - 7 / 8) ^ 2 + (antoineMap 40 q).2.2 ^ 2 ≤
        (56 / 640) ^ 2 + (7 / 640) ^ 2 := by
      have a1 : |(antoineMap 40 q).2.1 - 7 / 8| ≤ 56 / 640 := by
        convert b2 using 2; norm_num
      nlinarith [sq_abs ((antoineMap 40 q).2.1 - 7 / 8), sq_abs (antoineMap 40 q).2.2,
        abs_nonneg ((antoineMap 40 q).2.1 - 7 / 8), abs_nonneg (antoineMap 40 q).2.2]
    linarith
  · rcases antoineD_tube_links i hi with h | h
    · have h' : ((antoineEx (antoineT i) + 7 : ℤ) : ℝ) ≤ |((antoineZ i).1 : ℝ)| := by exact_mod_cast h
      push_cast at h'
      rw [abs_le] at b1; rw [abs_lt] at hx
      rcases le_abs'.1 h' with h' | h' <;> linarith [b1.1, b1.2]
    · have h' : ((antoineEy (antoineT i) + 183 : ℤ) : ℝ) ≤ |((antoineZ i).2 : ℝ) - 560| := by
        exact_mod_cast h
      push_cast at h'
      rw [abs_le] at b2; rw [abs_lt] at h1
      rcases le_abs'.1 h' with h' | h' <;> linarith [b2.1, b2.2]

theorem antoineD_tube_vert_re {v : Fin 64} (hv : antoineT v ≠ 0) :
    0 < (antoinePsi (antoineMapInv v p)).re := by
  have h1 := antoineD_tube_b1 hx hlo hhi
  rw [abs_lt] at hx h1
  obtain ⟨d1, d2⟩ := antoineD_vert_data v
  apply antoineD_psi_re_pos
  rcases antoineD_vert_cases hv with h | h
  · rw [antoineD_mapInv1 h, antoineD_sq_eq]
    simp only
    rcases (d1 h).1 with ⟨hc, -⟩ | ⟨hc, -⟩
    · left
      have h70 : (70 : ℝ) ≤ |((antoineZ v).1 : ℝ)| := by exact_mod_cast antoineD_tube_vert v h hc
      refine lt_of_lt_of_le ?_ (le_max_left _ _)
      rw [antoineD_abs_scale, lt_div_iff₀ (by norm_num)]
      rcases le_abs'.1 h70 with h' | h'
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    · right
      have hc' : ((antoineZ v).2 : ℝ) = -560 := by exact_mod_cast hc
      rw [hc']
      have hm0 : 0 ≤ max |(p.1 - (antoineZ v).1 / 640) * (80 / 7)| |p.2.2 * (80 / 7)| :=
        (abs_nonneg _).trans (le_max_left _ _)
      nlinarith
  · rw [antoineD_mapInv2 h, antoineD_sq_eq]
    simp only
    right
    rcases (d2 h).1 with ⟨hc, -⟩ | ⟨hc, -⟩
    · have hc' : ((antoineZ v).1 : ℝ) = 560 := by exact_mod_cast hc
      rw [hc']
      have hm0 : 0 ≤ max |p.2.2 * (80 / 7)| |(p.2.1 - (antoineZ v).2 / 640) * (80 / 7)| :=
        (abs_nonneg _).trans (le_max_left _ _)
      nlinarith
    · have hc' : ((antoineZ v).1 : ℝ) = -560 := by exact_mod_cast hc
      rw [hc']
      have hm0 : 0 ≤ max |p.2.2 * (80 / 7)| |(p.2.1 - (antoineZ v).2 / 640) * (80 / 7)| :=
        (abs_nonneg _).trans (le_max_left _ _)
      nlinarith


theorem antoineD_tube_far (hz : |p.2.2| < 1 / 200) : 1 / 8 < |p.2.1 - 7 / 8| := by
  have : (1 / 8 : ℝ) ^ 2 < (p.2.1 - 7 / 8) ^ 2 := by nlinarith [sq_abs p.2.2, abs_nonneg p.2.2]
  have := sq_lt_sq.1 this
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] at this

theorem antoineD_tube_slab (hτ : |2 * p.2.2 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1)| < 1 / 10000) :
    |p.2.2| < 1 / 200 := by
  rcases antoineD_slab hτ (antoineD_tube_xy hx hlo hhi) with h | h
  · exact h
  · linarith [antoineD_tube_b2 hx hlo hhi]

theorem antoineD_tube_horiz_re (hz : |p.2.2| < 1 / 200) {h : Fin 64} (hT : antoineT h = 0) :
    1 / 8 < (antoinePsi (antoineMapInv h p)).re := by
  have hf := antoineD_tube_far hx hlo hhi hz
  have h1 := antoineD_tube_b1 hx hlo hhi
  apply antoineD_psi_re_gt
  rw [antoineD_mapInv0 hT]
  simp only
  by_cases hi : h = 40
  · subst hi
    rw [antoineD_forty.2]
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    rw [antoineD_abs_scale, lt_div_iff₀ (by norm_num)]
    push_cast
    rw [show 640 * p.2.1 - 560 = 640 * (p.2.1 - 7 / 8) by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 640)]
    linarith
  · rcases antoineD_tube_horiz h hT hi with hc | hc
    · have hc' : (140 : ℝ) ≤ |((antoineZ h).1 : ℝ)| := by exact_mod_cast hc
      refine lt_of_lt_of_le ?_ (le_max_left _ _)
      rw [antoineD_abs_scale, lt_div_iff₀ (by norm_num)]
      rw [abs_lt] at hx
      rcases le_abs'.1 hc' with h' | h'
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    · have hc' : (1000 : ℝ) ≤ |((antoineZ h).2 : ℝ) - 560| := by exact_mod_cast hc
      refine lt_of_lt_of_le ?_ (le_max_right _ _)
      rw [antoineD_abs_scale, lt_div_iff₀ (by norm_num)]
      rw [abs_lt] at h1
      rcases le_abs'.1 hc' with h' | h'
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith

theorem antoineD_tube_side (hz : |p.2.2| < 1 / 200) :
    (max |p.1| |p.2.1| < 7 / 8 ∧ |p.2.2| < 1) ↔ ¬ 7 / 8 < p.2.1 := by
  have hf := antoineD_tube_far hx hlo hhi hz
  have h1 := antoineD_tube_b1 hx hlo hhi
  rw [abs_lt] at h1 hx
  constructor
  · rintro ⟨h, -⟩ h'
    have := (max_lt_iff.1 h).2
    rw [abs_lt] at this; linarith
  · intro h; push Not at h
    have h2 : p.2.1 < 7 / 8 - 1 / 8 := by
      rcases lt_abs.1 hf with h' | h' <;> linarith
    refine ⟨max_lt_iff.2 ⟨?_, ?_⟩, by rw [abs_lt] at hz ⊢; constructor <;> linarith [hz.1, hz.2]⟩
    · rw [abs_lt]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith

theorem antoineD_tube_mid (h : p.2.1 = 7 / 8) :
    1 / 10000 < |2 * p.2.2 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1)| := by
  have hz2 : 1 / 49 < p.2.2 ^ 2 := by rw [h] at hlo; linarith
  have hz : 1 / 8 < |p.2.2| := by
    have := sq_lt_sq.1 (show (1 / 8 : ℝ) ^ 2 < p.2.2 ^ 2 by nlinarith)
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] at this
  have hxy := antoineD_tube_xy hx hlo hhi
  have hb := antoineD_tube_b2 hx hlo hhi
  have hN : 0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1 := by positivity
  rw [abs_div, abs_of_pos hN, lt_div_iff₀ hN, abs_mul, abs_two]
  have : p.2.2 ^ 2 ≤ 4 / 49 := by nlinarith [sq_abs p.2.2, abs_nonneg p.2.2]
  nlinarith

end Tube

/-- The tube around the meridian `μ` of `L`, in the stereographic chart. -/
def antoineDT : Set Sphere3 :=
  {y | (y : EuclideanSpace ℝ (Fin 4)) 3 < 1 ∧ |(antoineStereoInv y).1| < 1 / 100 ∧
    1 / 49 < ((antoineStereoInv y).2.1 - 7 / 8) ^ 2 + (antoineStereoInv y).2.2 ^ 2 ∧
    ((antoineStereoInv y).2.1 - 7 / 8) ^ 2 + (antoineStereoInv y).2.2 ^ 2 < 4 / 49}

theorem antoineDT_X {y : Sphere3} (hy : y ∈ antoineDT) : y ∈ (antoineStereo '' antoineStage 1)ᶜ :=
  (antoineD_mem_X_iff hy.1).2 (antoineD_tube_notMem hy.2.1 hy.2.2.1 hy.2.2.2)

theorem antoineDT_N {y : Sphere3} (hy : y ∈ antoineDT) (hτ : |antoineDTau y| < 1 / 10000) :
    y ∈ antoineDN := by
  have hz : |(antoineStereoInv y).2.2| < 1 / 200 := by
    rw [antoineD_tau_eq hy.1] at hτ
    exact antoineD_tube_slab hy.2.1 hy.2.2.1 hy.2.2.2 hτ
  refine ⟨antoineDT_X hy, hτ, fun h hT => ?_⟩
  rw [antoineD_theta_eq h hy.1]
  exact antoineD_tube_horiz_re hy.2.1 hy.2.2.1 hy.2.2.2 hz hT

theorem antoineDT_chi {y : Sphere3} (hy : y ∈ antoineDT) (hτ : |antoineDTau y| < 1 / 10000) :
    antoineDChi y = if 7 / 8 < (antoineStereoInv y).2.1 then 1 else -1 := by
  have hz : |(antoineStereoInv y).2.2| < 1 / 200 := by
    rw [antoineD_tau_eq hy.1] at hτ
    exact antoineD_tube_slab hy.2.1 hy.2.2.1 hy.2.2.2 hτ
  have hs := antoineD_tube_side hy.2.1 hy.2.2.1 hy.2.2.2 hz
  unfold antoineDChi
  simp only [hy.1, true_and]
  by_cases h : 7 / 8 < (antoineStereoInv y).2.1
  · rw [if_pos h, if_neg fun h' => hs.1 h' h]
  · rw [if_neg h, if_pos (hs.2 h)]

theorem antoineDT_slit {y : Sphere3} (hy : y ∈ antoineDT) {v : Fin 64} (hv : v ∈ antoineDV) :
    antoineDTh v y ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, antoineDTh_re, antoineD_theta_eq v hy.1]
  exact Or.inl (antoineD_tube_vert_re hy.2.1 hy.2.2.1 hy.2.2.2 (antoineD_mem_V.1 hv))

theorem antoineDT_mid {y : Sphere3} (hy : y ∈ antoineDT) (h : (antoineStereoInv y).2.1 = 7 / 8) :
    1 / 10000 < |antoineDTau y| := by
  rw [antoineD_tau_eq hy.1]
  exact antoineD_tube_mid hy.2.1 hy.2.2.1 hy.2.2.2 h

theorem antoineMuS_mem_DT (t : I) : antoineMuS t ∈ antoineDT := by
  show antoineStereo (antoineMeridian t) ∈ antoineDT
  refine ⟨antoineStereo_three_lt _, ?_⟩
  rw [antoineStereoInv_stereo, antoineMeridian_apply]
  simp only [abs_zero]
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  refine ⟨by norm_num, ?_, ?_⟩ <;> nlinarith

/-! ### The invariant along the meridian -/

/-- The side of the core square along the tube. -/
def antoineDSide (y : Sphere3) : ℂ := if 7 / 8 < (antoineStereoInv y).2.1 then 1 else -1

/-- The invariant on the sheet `s = e · Q` over the tube, in closed form. -/
def antoineDF (e : ℂ) (y : Sphere3) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (e * antoineDSide y) * (antoineDPhi (antoineDTau y) : ℂ))

theorem antoineDSide_cases (y : Sphere3) : antoineDSide y = 1 ∨ antoineDSide y = -1 := by
  unfold antoineDSide; split_ifs <;> simp

theorem antoineD_pm_mul {e f : ℂ} (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1) :
    e * f = 1 ∨ e * f = -1 := by
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;> norm_num

theorem antoineDT_eqOn {e : ℂ} (he : e = 1 ∨ e = -1) :
    EqOn (fun y => antoineDg y (e * antoineDQ y)) (antoineDF e) antoineDT := by
  intro y hy
  simp only [antoineDg, antoineDF]
  by_cases hτ : |antoineDTau y| < 1 / 10000
  · rw [if_pos (antoineDT_N hy hτ)]
    congr 3
    rw [antoineDR, antoineDT_chi hy hτ]
    have hQ := antoineDQ_ne_zero y
    unfold antoineDSide
    split_ifs
    · field_simp
    · field_simp
  · rw [if_neg fun h => hτ h.2.1]
    push Not at hτ
    exact (antoineD_exp_ends (antoineD_pm_mul he (antoineDSide_cases y))
      (antoineD_phi_ends hτ)).symm

theorem antoineDT_contOn {e : ℂ} (he : e = 1 ∨ e = -1) : ContinuousOn (antoineDF e) antoineDT := by
  intro y hy
  apply ContinuousAt.continuousWithinAt
  have hcs := continuousAt_antoineStereoInv hy.1
  have hcy : ContinuousAt (fun y => (antoineStereoInv y).2.1) y :=
    (continuous_fst.comp continuous_snd).continuousAt.comp hcs
  have hF : ∀ c : ℂ, Continuous fun y => Complex.exp (Real.pi * Complex.I * (e * c) *
      (antoineDPhi (antoineDTau y) : ℂ)) := fun c =>
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_antoineDPhi.comp continuous_antoineDTau)))
  by_cases hm : (antoineStereoInv y).2.1 = 7 / 8
  · have hτ := antoineDT_mid hy hm
    have hev : ∀ᶠ z in 𝓝 y, 1 / 10000 < |antoineDTau z| :=
      continuousAt_const.eventually_lt (continuous_abs.comp continuous_antoineDTau).continuousAt hτ
    have h1 : antoineDF e y = 1 :=
      antoineD_exp_ends (antoineD_pm_mul he (antoineDSide_cases y)) (antoineD_phi_ends hτ.le)
    refine (continuousAt_const (y := (1 : ℂ))).congr ?_
    filter_upwards [hev] with z hz
    exact (antoineD_exp_ends (antoineD_pm_mul he (antoineDSide_cases z)) (antoineD_phi_ends hz.le)).symm
  · rcases lt_or_gt_of_ne hm with hlt | hgt
    · refine (hF (-1)).continuousAt.congr ?_
      filter_upwards [hcy.eventually_lt continuousAt_const hlt] with z hz
      simp only [antoineDF, antoineDSide, if_neg (not_lt.2 hz.le)]
    · refine (hF 1).continuousAt.congr ?_
      filter_upwards [continuousAt_const.eventually_lt hcy hgt] with z hz
      simp only [antoineDF, antoineDSide, if_pos hz]

theorem antoineDTau_stereo (p : ℝ × ℝ × ℝ) :
    antoineDTau (antoineStereo p) = 2 * p.2.2 / (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 + 1) := by
  have := antoineD_tau_eq (antoineStereo_three_lt p); rwa [antoineStereoInv_stereo] at this

/-- `τ` along the meridian. -/
def antoineDTm (t : I) : ℝ := 2 * (3 / 14 * Real.sin (2 * Real.pi * t)) /
  (0 ^ 2 + (7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t)) ^ 2 +
    (3 / 14 * Real.sin (2 * Real.pi * t)) ^ 2 + 1)

theorem antoineDTau_muS (t : I) : antoineDTau (antoineMuS t) = antoineDTm t := by
  show antoineDTau (antoineStereo (antoineMeridian t)) = _
  rw [antoineDTau_stereo, antoineMeridian_apply]; rfl

theorem continuous_antoineDTm : Continuous antoineDTm := by
  have : antoineDTm = fun t => antoineDTau (antoineMuS t) := funext fun t => (antoineDTau_muS t).symm
  rw [this]; exact continuous_antoineDTau.comp antoineMuS.continuous

theorem antoineDSide_muS (t : I) : antoineDSide (antoineMuS t) =
    if 0 < Real.cos (2 * Real.pi * t) then 1 else -1 := by
  show antoineDSide (antoineStereo (antoineMeridian t)) = _
  simp only [antoineDSide, antoineStereoInv_stereo, antoineMeridian_apply]
  congr 1
  apply propext; constructor <;> intro h <;> nlinarith

theorem antoineDTm_small {t : I} (h : |antoineDTm t| < 1 / 10000) :
    |Real.sin (2 * Real.pi * t)| < 1 / 2 := by
  unfold antoineDTm at h
  set sn := Real.sin (2 * Real.pi * t)
  set cs := Real.cos (2 * Real.pi * t)
  have hcs : sn ^ 2 + cs ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc1 : cs ≤ 1 := Real.cos_le_one _
  have hc2 : -1 ≤ cs := Real.neg_one_le_cos _
  have hN : 0 < 0 ^ 2 + (7 / 8 + 3 / 14 * cs) ^ 2 + (3 / 14 * sn) ^ 2 + 1 := by positivity
  have hN2 : 0 ^ 2 + (7 / 8 + 3 / 14 * cs) ^ 2 + (3 / 14 * sn) ^ 2 + 1 ≤ 3 := by nlinarith
  rw [abs_div, abs_of_pos hN, div_lt_iff₀ hN] at h
  rw [abs_mul, abs_two, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 14)] at h
  nlinarith [abs_nonneg sn]

theorem antoineD_cos_of_small {t : I} (h : |Real.sin (2 * Real.pi * t)| < 1 / 2) :
    Real.cos (2 * Real.pi * t) ≠ 0 := by
  intro h0
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  rw [h0] at hcs
  nlinarith [sq_abs (Real.sin (2 * Real.pi * t)), abs_nonneg (Real.sin (2 * Real.pi * t))]

theorem antoineD_cos_sign (t : I) :
    ((t : ℝ) ≤ 1 / 4 → 0 ≤ Real.cos (2 * Real.pi * t)) ∧
      (1 / 4 < (t : ℝ) → (t : ℝ) ≤ 3 / 4 → Real.cos (2 * Real.pi * t) ≤ 0) ∧
      (3 / 4 < (t : ℝ) → 0 ≤ Real.cos (2 * Real.pi * t)) := by
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hpi := Real.pi_pos
  refine ⟨fun h => Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩, fun h h' =>
    Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) (by nlinarith), fun h => ?_⟩
  rw [← Real.cos_sub_two_pi]
  exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩

theorem antoineD_exp_four {e : ℂ} (he : e = 1 ∨ e = -1) (x : ℝ) :
    Complex.exp (Real.pi * Complex.I * e * (((4 + x : ℝ)) : ℂ)) =
      Complex.exp (Real.pi * Complex.I * e * (x : ℂ)) ∧
    Complex.exp (Real.pi * Complex.I * e * (((4 - x : ℝ)) : ℂ)) =
      Complex.exp (Real.pi * Complex.I * (e * -1) * (x : ℂ)) := by
  have h4 : Complex.exp (Real.pi * Complex.I * e * 4) = 1 := by
    rcases he with rfl | rfl
    · rw [show (Real.pi : ℂ) * Complex.I * 1 * 4 = ((2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I 2
    · rw [show (Real.pi : ℂ) * Complex.I * (-1) * 4 = ((-2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-2)
  constructor
  · rw [show (Real.pi : ℂ) * Complex.I * e * (((4 + x : ℝ)) : ℂ) =
      Real.pi * Complex.I * e * 4 + Real.pi * Complex.I * e * (x : ℂ) by push_cast; ring,
      Complex.exp_add, h4, one_mul]
  · rw [show (Real.pi : ℂ) * Complex.I * e * (((4 - x : ℝ)) : ℂ) =
      Real.pi * Complex.I * e * 4 + Real.pi * Complex.I * (e * -1) * (x : ℂ) by push_cast; ring,
      Complex.exp_add, h4, one_mul]

theorem antoineDTm_quarter {t : I} (ht : (t : ℝ) = 1 / 4) : antoineDPhi (antoineDTm t) = 2 := by
  unfold antoineDTm antoineDPhi
  rw [ht, show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [min_eq_left (by norm_num), max_eq_right (by norm_num)]

theorem antoineDTm_three_quarter {t : I} (ht : (t : ℝ) = 3 / 4) : antoineDPhi (antoineDTm t) = 0 := by
  unfold antoineDTm antoineDPhi
  rw [ht, show 2 * Real.pi * (3 / 4) = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
    Real.cos_add_pi, Real.sin_pi_div_two, Real.cos_pi_div_two]
  norm_num

theorem antoineDTm_zero : antoineDTm 0 = 0 := by simp [antoineDTm]

theorem antoineDTm_one : antoineDTm 1 = 0 := by simp [antoineDTm]

/-- The lift of the invariant along the meridian, divided by `iπ e`: `φ` on `[0, 1/4]`, then
`4 - φ`, then `4 + φ`. -/
def antoineDXi (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 4 then antoineDPhi (antoineDTm t)
  else if (t : ℝ) ≤ 3 / 4 then 4 - antoineDPhi (antoineDTm t) else 4 + antoineDPhi (antoineDTm t)

theorem continuous_antoineDXi : Continuous antoineDXi := by
  have hφ : Continuous fun t : I => antoineDPhi (antoineDTm t) :=
    continuous_antoineDPhi.comp continuous_antoineDTm
  have hin : Continuous fun t : I => if (t : ℝ) ≤ 3 / 4 then 4 - antoineDPhi (antoineDTm t)
      else 4 + antoineDPhi (antoineDTm t) :=
    Continuous.if_le (continuous_const.sub hφ) (continuous_const.add hφ) continuous_subtype_val
      continuous_const fun t ht => by rw [antoineDTm_three_quarter ht]; ring
  exact Continuous.if_le hφ hin continuous_subtype_val continuous_const fun t ht => by
    rw [if_pos (by rw [ht]; norm_num), antoineDTm_quarter ht]; norm_num

/-- **The meridian crosses the slab twice, on opposite sheets**: the invariant winds `2e`
times along it. -/
theorem antoineDF_wind {ez : ℤ} (hez : ez = 1 ∨ ez = -1) :
    AntoineLiftWind (fun t => antoineDF (ez : ℂ) (antoineMuS t)) (2 * ez) := by
  have he : (ez : ℂ) = 1 ∨ (ez : ℂ) = -1 := by rcases hez with rfl | rfl <;> simp
  refine ⟨⟨fun t => Real.pi * Complex.I * (ez : ℂ) * ((antoineDXi t : ℝ) : ℂ), by
    have := continuous_antoineDXi; fun_prop⟩, fun t => ?_, ?_⟩
  · simp only [ContinuousMap.coe_mk, antoineDF, antoineDTau_muS, antoineDSide_muS]
    obtain ⟨c1, c2, c3⟩ := antoineD_cos_sign t
    by_cases hsm : |antoineDTm t| < 1 / 10000
    · have hc := antoineD_cos_of_small (antoineDTm_small hsm)
      rcases le_or_gt (t : ℝ) (1 / 4) with h1 | h1
      · rw [if_pos (lt_of_le_of_ne (c1 h1) (Ne.symm hc))]
        unfold antoineDXi; rw [if_pos h1, mul_one]
      · rcases le_or_gt (t : ℝ) (3 / 4) with h3 | h3
        · rw [if_neg (not_lt.2 (c2 h1 h3))]
          unfold antoineDXi; rw [if_neg (not_le.2 h1), if_pos h3]
          exact (antoineD_exp_four he _).2
        · rw [if_pos (lt_of_le_of_ne (c3 h3) (Ne.symm hc))]
          unfold antoineDXi; rw [if_neg (not_le.2 h1), if_neg (not_le.2 h3), mul_one]
          exact (antoineD_exp_four he _).1
    · push Not at hsm
      have hends := antoineD_phi_ends hsm
      have hsd : (if 0 < Real.cos (2 * Real.pi * t) then (1 : ℂ) else -1) = 1 ∨
          (if 0 < Real.cos (2 * Real.pi * t) then (1 : ℂ) else -1) = -1 := by
        split_ifs <;> simp
      rw [antoineD_exp_ends (antoineD_pm_mul he hsd) hends]
      unfold antoineDXi
      rcases le_or_gt (t : ℝ) (1 / 4) with h1 | h1
      · rw [if_pos h1]; exact antoineD_exp_ends he hends
      · rcases le_or_gt (t : ℝ) (3 / 4) with h3 | h3
        · rw [if_neg (not_le.2 h1), if_pos h3, (antoineD_exp_four he _).2]
          exact antoineD_exp_ends (antoineD_pm_mul he (Or.inr rfl)) hends
        · rw [if_neg (not_le.2 h1), if_neg (not_le.2 h3), (antoineD_exp_four he _).1]
          exact antoineD_exp_ends he hends
  · simp only [ContinuousMap.coe_mk, antoineDXi]
    rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num), antoineDTm_one,
      antoineDTm_zero]
    simp only [antoineDPhi]
    push_cast
    ring

/-! ### Antoine's lemma at the first generation -/

theorem continuousAt_antoineDQ {y : Sphere3} (hs : ∀ v ∈ antoineDV, antoineDTh v y ∈ Complex.slitPlane) :
    ContinuousAt antoineDQ y :=
  tendsto_finsetProd (f := fun v y => antoineDSq (antoineDTh v y))
    (a := fun v => antoineDSq (antoineDTh v y)) _ fun v hv =>
      (continuousAt_antoineDSq (hs v hv)).comp (continuous_antoineDTh v).continuousAt

theorem antoineD_base_mem : antoineStereo antoineMerPt ∈ antoineDN := by
  have hT : antoineStereo antoineMerPt ∈ antoineDT := by
    have := antoineMuS_mem_DT 0; rwa [Path.source] at this
  refine antoineDT_N hT ?_
  rw [antoineDTau_stereo]; simp [antoineMerPt]

theorem antoineD_base_tau : antoineDTau (antoineStereo antoineMerPt) = 0 := by
  rw [antoineDTau_stereo]; simp [antoineMerPt]

/-- At the base point, on the slab's middle sphere, the invariant is `-1` on both sheets. -/
theorem antoineD_g_base {s : ℂ} (hs : s ^ 2 = antoineDP (antoineStereo antoineMerPt)) :
    antoineDg (antoineStereo antoineMerPt) s = -1 := by
  have hX := antoineD_base_mem.1
  simp only [antoineDg, if_pos antoineD_base_mem, antoineD_base_tau]
  have h1 : antoineDPhi 0 = 1 := by simp [antoineDPhi]
  rw [h1]
  rcases antoineD_sigma_cases (antoineD_sigma_sq hX hs) with h | h
  · rw [h]; push_cast; rw [mul_one, mul_one, Complex.exp_pi_mul_I]
  · rw [h]; push_cast
    rw [show (Real.pi : ℂ) * Complex.I * (-1) * 1 = -(Real.pi * Complex.I) by ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; norm_num

/-- **Antoine's lemma at the first generation, proved**: no nonzero power of the meridian of `L`
is null-homotopic in `S³ ∖ C₁`. A null-homotopy `H` lifts to the double cover `s² = P` (`P` the
product of the vertical `Θ'ᵢ`, `GX.antoineDP`); the invariant `GX.antoineDg` is continuous
along the lift (`GX.continuous_antoineDg`), equal to `-1` on three edges of the square
(`GX.antoineD_g_base`), and winds `2ea` times along the fourth (`GX.antoineDF_wind`): the
meridian crosses the slab twice, on opposite sheets, because the sides of the core square are
joined only through the gaps of the closed chain. -/
theorem antoineChainEssential_proof : AntoineChainEssential := by
  intro a ha hnull
  obtain ⟨H, hH⟩ := hnull
  -- the lift of `P ∘ H` through `exp`
  let PH : C(I × I, CStar) := ⟨fun z => ⟨antoineDP (H z), antoineDP_ne_zero (hH z)⟩,
    (continuous_antoineDP.comp H.continuous).subtype_mk _⟩
  obtain ⟨Γ₀, hΓ₀⟩ := exists_expLift ⟨fun t => PH (0, t), by fun_prop⟩
  have H_0 : ∀ t, PH (0, t) = cExp (Γ₀ t) := fun t => Subtype.ext (by
    show antoineDP (H (0, t)) = Complex.exp (Γ₀ t); rw [hΓ₀ t]; rfl)
  set Λ := isCoveringMap_cExp.liftHomotopy PH Γ₀ H_0
  have hΛ : ∀ z, Complex.exp (Λ z) = antoineDP (H z) := fun z =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftHomotopy_lifts PH Γ₀ H_0) z)
  set S : I × I → ℂ := fun z => Complex.exp (Λ z / 2)
  have hS : Continuous S := by fun_prop
  have hSq : ∀ z, S z ^ 2 = antoineDP (H z) := fun z => by
    simp only [S]; rw [sq, ← Complex.exp_add, add_halves, hΛ]
  set G : I × I → ℂ := fun z => antoineDg (H z) (S z)
  have hG : Continuous G := continuous_antoineDg H.continuous hH hS hSq
  have hG0 : ∀ z, G z ≠ 0 := fun z => by
    simp only [G, antoineDg]; split_ifs
    · exact Complex.exp_ne_zero _
    · exact one_ne_zero
  have hGb : ∀ z, H z = antoineStereo antoineMerPt → G z = -1 := fun z hz => by
    simp only [G]; rw [hz]; exact antoineD_g_base (hz ▸ hSq z)
  have hloop : ∀ s, G (s, 1) = G (s, 0) := fun s => by
    rw [hGb _ (H.target s), hGb _ (H.source s)]
  have hw1 : AntoineLiftWind (fun t => G (1, t)) 0 := by
    refine ⟨⟨fun _ => Real.pi * Complex.I, continuous_const⟩, fun t => ?_, by simp⟩
    show Complex.exp (Real.pi * Complex.I) = G (1, t)
    rw [hGb (1, t) (by rw [H.apply_one]; rfl)]; exact Complex.exp_pi_mul_I
  -- the sheet along the bottom edge
  have hmem : ∀ t, loopZPow antoineMuS a t ∈ antoineDT := loopZPow_mem antoineMuS_mem_DT a
  have hQc : Continuous fun t => antoineDQ (loopZPow antoineMuS a t) :=
    continuous_iff_continuousAt.2 fun t =>
      (continuousAt_antoineDQ fun v hv => antoineDT_slit (hmem t) hv).comp
        (loopZPow antoineMuS a).continuous.continuousAt
  have hH0 : ∀ t, H (0, t) = loopZPow antoineMuS a t := fun t => H.apply_zero t
  set f : I → ℂ := fun t => S (0, t) / antoineDQ (loopZPow antoineMuS a t)
  have hf : Continuous f := (hS.comp (Continuous.prodMk continuous_const continuous_id)).div hQc
    fun t => antoineDQ_ne_zero _
  have hf2 : ∀ t, f t = 1 ∨ f t = -1 := fun t => by
    apply antoineD_sigma_cases
    simp only [f]
    rw [div_pow, hSq, hH0, antoineDQ_sq (antoineDT_X (hmem t)),
      div_self (antoineDP_ne_zero (antoineDT_X (hmem t)))]
  have hfc : ∀ t, f t = f 0 := by
    intro t
    by_contra hne
    have hre : Continuous fun t => (f t).re := Complex.continuous_re.comp hf
    rcases hf2 0 with h0 | h0 <;> rcases hf2 t with ht | ht
    · exact hne (ht.trans h0.symm)
    · obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hre
        (show (0 : ℝ) ∈ Set.Icc (f t).re (f 0).re by rw [h0, ht]; norm_num)
      have hu' : (f u).re = 0 := hu
      rcases hf2 u with h | h <;> rw [h] at hu' <;> norm_num at hu'
    · obtain ⟨u, hu⟩ := intermediate_value_univ 0 t hre
        (show (0 : ℝ) ∈ Set.Icc (f 0).re (f t).re by rw [h0, ht]; norm_num)
      have hu' : (f u).re = 0 := hu
      rcases hf2 u with h | h <;> rw [h] at hu' <;> norm_num at hu'
    · exact hne (ht.trans h0.symm)
  obtain ⟨ez, hez, hfe⟩ : ∃ ez : ℤ, (ez = 1 ∨ ez = -1) ∧ f 0 = ez := by
    rcases hf2 0 with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
  have he : (ez : ℂ) = 1 ∨ (ez : ℂ) = -1 := by rcases hez with rfl | rfl <;> simp
  have hbot : ∀ t, G (0, t) = antoineDF (ez : ℂ) (loopZPow antoineMuS a t) := fun t => by
    have hSt : S (0, t) = (ez : ℂ) * antoineDQ (loopZPow antoineMuS a t) := by
      have := hfc t
      simp only [f] at this hfe
      rw [hfe, div_eq_iff (antoineDQ_ne_zero _)] at this
      exact this
    simp only [G]
    rw [hH0, hSt]
    exact antoineDT_eqOn he (hmem t)
  -- the winding along the bottom edge, and the contradiction
  have hw0 : AntoineLiftWind (fun t => antoineDF (ez : ℂ) (loopZPow antoineMuS a t)) (a * (2 * ez)) :=
    antoineLiftWind_loopZPow antoineMuS_mem_DT (antoineDT_contOn he)
      (fun _ _ => Complex.exp_ne_zero _) (antoineDF_wind hez) a
  have hw0' : AntoineLiftWind (fun t => G (0, t)) (a * (2 * ez)) :=
    hw0.congr fun t => (hbot t).symm
  have hw1' := AntoineLiftWind.of_freeHomotopy hG hG0 hloop hw0'
  have := hw1'.unique hw1
  rcases hez with rfl | rfl <;> omega

end GX
