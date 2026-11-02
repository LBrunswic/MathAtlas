import GXScaffold.Branched.GaloisExamples

noncomputable section
open Set Filter Topology Function unitInterval
namespace GX
attribute [local instance] Classical.propDecidable

/-- The vector `(0, 0, d₁, d₂)` of `ℝ⁴`. -/
def gcEmb (d : ℝ × ℝ) : EuclideanSpace ℝ (Fin 4) := !₂[0, 0, d.1, d.2]

@[simp] theorem gcEmb_two (d : ℝ × ℝ) : gcEmb d 2 = d.1 := by simp [gcEmb]
@[simp] theorem gcEmb_three (d : ℝ × ℝ) : gcEmb d 3 = d.2 := by simp [gcEmb]

theorem norm_gcEmb_le (d : ℝ × ℝ) : ‖gcEmb d‖ ≤ |d.1| + |d.2| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp [gcEmb, Fin.sum_univ_four]
  nlinarith [abs_nonneg d.1, abs_nonneg d.2, sq_abs d.1, sq_abs d.2, abs_mul_abs_self d.1]

theorem inner_gcEmb_of_mem {x : Sphere3} (hx : x ∈ greatCircle3) (d : ℝ × ℝ) :
    inner ℝ (gcEmb d) (x : EuclideanSpace ℝ (Fin 4)) = 0 := by
  obtain ⟨h2, h3⟩ := hx
  simp [gcEmb, PiLp.inner_apply, Fin.sum_univ_four, h2, h3]

theorem sphere3_inner_self (x : Sphere3) :
    inner ℝ (x : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) = 1 := by
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.1 x.2]; norm_num

/-- The cap `{y ∈ S³ : c < ⟨y, x⟩}`. -/
def gcCap (x : Sphere3) (c : ℝ) : Set Sphere3 :=
  {y | c < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4))}

/-- Pushing `w` into the half-space `⟨·, x⟩ ≥ 1/2`. -/
def gcLift (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  w + (max 0 (1 / 2 - inner ℝ w (x : EuclideanSpace ℝ (Fin 4)))) • (x : EuclideanSpace ℝ (Fin 4))

theorem gcLift_inner (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) :
    1 / 2 ≤ inner ℝ (gcLift x w) (x : EuclideanSpace ℝ (Fin 4)) := by
  simp only [gcLift, inner_add_left, real_inner_smul_left, sphere3_inner_self, mul_one]
  linarith [le_max_right 0 (1 / 2 - inner ℝ w (x : EuclideanSpace ℝ (Fin 4)))]

theorem gcLift_ne_zero (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) : gcLift x w ≠ 0 := by
  intro h; have := gcLift_inner x w; rw [h, inner_zero_left] at this; norm_num at this

theorem continuous_gcLift (x : Sphere3) : Continuous (gcLift x) :=
  continuous_id.add
    ((continuous_const.max (continuous_const.sub (continuous_id.inner continuous_const))).smul
      continuous_const)

theorem gcLift_of_le {x : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) : gcLift x w = w := by
  simp only [gcLift, max_eq_left (by linarith : 1 / 2 - inner ℝ w (x : EuclideanSpace ℝ (Fin 4)) ≤ 0),
    zero_smul, add_zero]

theorem norm_gcLift_smul (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) :
    ‖‖gcLift x w‖⁻¹ • gcLift x w‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (gcLift_ne_zero x w))]

/-- The radial projection onto `S³`, centred at `x` (continuous on all of `ℝ⁴`). -/
def gcF (x : Sphere3) (w : EuclideanSpace ℝ (Fin 4)) : Sphere3 :=
  ⟨‖gcLift x w‖⁻¹ • gcLift x w, mem_sphere_zero_iff_norm.2 (norm_gcLift_smul x w)⟩

theorem continuous_gcF (x : Sphere3) : Continuous (gcF x) :=
  Continuous.subtype_mk (((continuous_norm.comp (continuous_gcLift x)).inv₀
    fun w => norm_ne_zero_iff.2 (gcLift_ne_zero x w)).smul (continuous_gcLift x)) _

theorem gcF_coe_of_le {x : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) :
    (gcF x w : EuclideanSpace ℝ (Fin 4)) = ‖w‖⁻¹ • w := by
  change ‖gcLift x w‖⁻¹ • gcLift x w = _
  rw [gcLift_of_le h]

theorem gcF_sphere {x y : Sphere3}
    (h : 1 / 2 ≤ inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4))) :
    gcF x y = y := by
  apply Subtype.ext
  rw [gcF_coe_of_le h, mem_sphere_zero_iff_norm.1 y.2, inv_one, one_smul]

theorem gcF_self (x : Sphere3) : gcF x x = x :=
  gcF_sphere (by rw [sphere3_inner_self]; norm_num)

theorem ne_zero_of_half_le {x : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) : w ≠ 0 := by
  rintro rfl; rw [inner_zero_left] at h; norm_num at h

/-- `gcF x w` lies on the great circle iff the last two coordinates of `w` vanish. -/
theorem gcF_mem_iff {x : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) :
    gcF x w ∈ greatCircle3 ↔ w 2 = 0 ∧ w 3 = 0 := by
  have hn : ‖w‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 (ne_zero_of_half_le h))
  change (gcF x w : EuclideanSpace ℝ (Fin 4)) 2 = 0 ∧ (gcF x w : EuclideanSpace ℝ (Fin 4)) 3 = 0 ↔ _
  rw [gcF_coe_of_le h]
  simp [PiLp.smul_apply, hn]

theorem gcF_dist_le {x y : Sphere3} {w : EuclideanSpace ℝ (Fin 4)}
    (h : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4))) :
    dist (gcF x w) y ≤ 2 * ‖w - (y : EuclideanSpace ℝ (Fin 4))‖ := by
  have hw : w ≠ 0 := ne_zero_of_half_le h
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hy : ‖(y : EuclideanSpace ℝ (Fin 4))‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
  rw [Subtype.dist_eq, dist_eq_norm, gcF_coe_of_le h]
  have e : ‖w‖⁻¹ • w - (y : EuclideanSpace ℝ (Fin 4)) =
      (‖w‖⁻¹ - 1) • w + (w - (y : EuclideanSpace ℝ (Fin 4))) := by
    rw [sub_smul, one_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : |‖w‖⁻¹ - 1| * ‖w‖ = |1 - ‖w‖| := by
    rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos, sub_mul, inv_mul_cancel₀ hpos.ne', one_mul]
  rw [h1]
  have h2 : |1 - ‖w‖| ≤ ‖w - (y : EuclideanSpace ℝ (Fin 4))‖ := by
    have := abs_norm_sub_norm_le w (y : EuclideanSpace ℝ (Fin 4))
    rw [hy] at this; rwa [abs_sub_comm]
  linarith

theorem isOpen_gcCap (x : Sphere3) (c : ℝ) : IsOpen (gcCap x c) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

theorem mem_gcCap_self {x : Sphere3} {c : ℝ} (hc : c < 1) : x ∈ gcCap x c := by
  show c < _; rw [sphere3_inner_self]; exact hc

theorem gcCap_mono {x : Sphere3} {c c' : ℝ} (h : c ≤ c') : gcCap x c' ⊆ gcCap x c :=
  fun _ hy => lt_of_le_of_lt h hy

/-- The caps around `x` form a basis of neighbourhoods. -/
theorem exists_gcCap_subset {x : Sphere3} {W : Set Sphere3} (hW : W ∈ 𝓝 x) (c₀ : ℝ) (hc₀ : c₀ < 1) :
    ∃ c, c₀ ≤ c ∧ c < 1 ∧ gcCap x c ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  refine ⟨max c₀ (1 - ε ^ 2 / 4), le_max_left _ _, max_lt hc₀ (by nlinarith), fun y hy => ?_⟩
  apply hball
  have hy' : 1 - ε ^ 2 / 4 < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) :=
    lt_of_le_of_lt (le_max_right _ _) hy
  rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
  have hsq : ‖(y : EuclideanSpace ℝ (Fin 4)) - x‖ ^ 2 < ε ^ 2 := by
    rw [norm_sub_sq_real, mem_sphere_zero_iff_norm.1 y.2, mem_sphere_zero_iff_norm.1 x.2]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- The convex body over a cap. -/
def gcBody (x : Sphere3) (c : ℝ) : Set (EuclideanSpace ℝ (Fin 4)) :=
  {w | ‖w‖ ≤ 1 ∧ c < inner ℝ w (x : EuclideanSpace ℝ (Fin 4))}

theorem convex_gcBody (x : Sphere3) (c : ℝ) : Convex ℝ (gcBody x c) := by
  have h1 : Convex ℝ {w : EuclideanSpace ℝ (Fin 4) | ‖w‖ ≤ 1} := by
    simpa [Metric.closedBall, dist_zero_right] using
      convex_closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1
  have h2 : Convex ℝ {w : EuclideanSpace ℝ (Fin 4) | c < inner ℝ w (x : EuclideanSpace ℝ (Fin 4))} :=
    convex_halfSpace_gt
      ⟨fun a b => inner_add_left a b _, fun r a => real_inner_smul_left a _ r⟩ c
  exact h1.inter h2

theorem coe_mem_gcBody {x y : Sphere3} {c : ℝ} (hy : y ∈ gcCap x c) :
    (y : EuclideanSpace ℝ (Fin 4)) ∈ gcBody x c :=
  ⟨(mem_sphere_zero_iff_norm.1 y.2).le, hy⟩

theorem gcF_mem_gcCap {x : Sphere3} {c : ℝ} (hc : 1 / 2 ≤ c) {w : EuclideanSpace ℝ (Fin 4)}
    (hw : w ∈ gcBody x c) : gcF x w ∈ gcCap x c := by
  have h12 : 1 / 2 ≤ inner ℝ w (x : EuclideanSpace ℝ (Fin 4)) := hc.trans hw.2.le
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 (ne_zero_of_half_le h12)
  show c < inner ℝ (gcF x w : EuclideanSpace ℝ (Fin 4)) _
  rw [gcF_coe_of_le h12, real_inner_smul_left]
  have : inner ℝ w (x : EuclideanSpace ℝ (Fin 4)) ≤
      ‖w‖⁻¹ * inner ℝ w (x : EuclideanSpace ℝ (Fin 4)) := by
    have h1 : 1 ≤ ‖w‖⁻¹ := (one_le_inv₀ hpos).2 hw.1
    nlinarith
  linarith [hw.2]

theorem gcCap_eq_image {x : Sphere3} {c : ℝ} (hc : 1 / 2 ≤ c) :
    gcCap x c = gcF x '' gcBody x c := by
  ext y
  refine ⟨fun hy => ⟨_, coe_mem_gcBody hy, gcF_sphere (hc.trans hy.le)⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  exact gcF_mem_gcCap hc hw

theorem isPreconnected_gcCap (x : Sphere3) {c : ℝ} (hc : 1 / 2 ≤ c) :
    IsPreconnected (gcCap x c) := by
  rw [gcCap_eq_image hc]
  exact (convex_gcBody x c).isPreconnected.image _ (continuous_gcF x).continuousOn

/-- Two paths of a cap (`c ≥ 1/2`) with the same ends are homotopic in the cap. -/
theorem gcCap_homotopicIn {x : Sphere3} {c : ℝ} (hc : 1 / 2 ≤ c) {a b : Sphere3}
    (ρ₁ ω : Path a b) (hρ₁ : ∀ t, ρ₁ t ∈ gcCap x c) (hω : ∀ t, ω t ∈ gcCap x c) :
    HomotopicIn (gcCap x c) ρ₁ ω := by
  have ha0 : a ∈ gcCap x c := by simpa using hρ₁ 0
  have hb1 : b ∈ gcCap x c := by simpa using hρ₁ 1
  have ha : gcF x a = a := gcF_sphere (hc.trans ha0.le)
  have hb : gcF x b = b := gcF_sphere (hc.trans hb1.le)
  have key := homotopicIn_map_of_convex (U := gcCap x c) (ρ₁.map continuous_subtype_val)
    (ω.map continuous_subtype_val) (convex_gcBody x c) (fun t => coe_mem_gcBody (hρ₁ t))
    (fun t => coe_mem_gcBody (hω t)) (continuous_gcF x) fun e he => gcF_mem_gcCap hc he
  refine (key.cast ha.symm hb.symm).of_eq ?_ ?_
  · refine Path.ext (funext fun t => ?_)
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact gcF_sphere (hc.trans (hρ₁ t).le)
  · refine Path.ext (funext fun t => ?_)
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact gcF_sphere (hc.trans (hω t).le)

/-- `det(u, w)` in `ℝ²`. -/
def gcDet (u w : ℝ × ℝ) : ℝ := u.1 * w.2 - u.2 * w.1

/-- Three directions: any two nonzero vectors of `ℝ²` are both transverse to one of them. -/
theorem gc_exists_dir (u v : ℝ × ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ d : ℝ × ℝ, d ≠ 0 ∧ |d.1| ≤ s ∧ |d.2| ≤ s ∧ (u ≠ 0 → gcDet u d ≠ 0) ∧
      (v ≠ 0 → gcDet v d ≠ 0) := by
  have hs' : s ≠ 0 := hs.ne'
  have habs : |s| = s := abs_of_pos hs
  by_cases h1 : (u = 0 ∨ u.2 ≠ 0) ∧ (v = 0 ∨ v.2 ≠ 0)
  · refine ⟨(s, 0), fun h => hs' (congrArg Prod.fst h), by simp [habs], by simp [hs.le], ?_, ?_⟩
    · intro hu; rcases h1.1 with h | h
      · exact absurd h hu
      · simp [gcDet, h, hs']
    · intro hv; rcases h1.2 with h | h
      · exact absurd h hv
      · simp [gcDet, h, hs']
  by_cases h2 : (u = 0 ∨ u.1 ≠ 0) ∧ (v = 0 ∨ v.1 ≠ 0)
  · refine ⟨(0, s), fun h => hs' (congrArg Prod.snd h), by simp [hs.le], by simp [habs], ?_, ?_⟩
    · intro hu; rcases h2.1 with h | h
      · exact absurd h hu
      · simp [gcDet, h, hs']
    · intro hv; rcases h2.2 with h | h
      · exact absurd h hv
      · simp [gcDet, h, hs']
  refine ⟨(s, s), fun h => hs' (congrArg Prod.fst h), by simp [habs], by simp [habs], ?_, ?_⟩
  · intro hu
    simp only [gcDet]
    intro he
    have he' : u.1 = u.2 := by
      have : (u.1 - u.2) * s = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h hs'
    apply hu
    push Not at h1 h2
    by_cases hu1 : u.1 = 0
    · exact Prod.ext hu1 (he' ▸ hu1)
    · have hv : v ≠ 0 ∧ v.1 = 0 := h2 (Or.inr hu1)
      have hu2 : u.2 ≠ 0 := he' ▸ hu1
      have hv2 : v ≠ 0 ∧ v.2 = 0 := h1 (Or.inr hu2)
      exact absurd (Prod.ext hv.2 hv2.2) hv.1
  · intro hv
    simp only [gcDet]
    intro he
    have he' : v.1 = v.2 := by
      have : (v.1 - v.2) * s = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h hs'
    apply hv
    push Not at h1 h2
    by_cases hv1 : v.1 = 0
    · exact Prod.ext hv1 (he' ▸ hv1)
    · have hv2 : v.2 ≠ 0 := he' ▸ hv1
      have hu : ¬ (u = 0 ∨ u.2 ≠ 0) := fun h => hv2 (h1 h).2
      push Not at hu
      have hu1 : u.1 ≠ 0 := fun h => hu.1 (Prod.ext h hu.2)
      exact absurd (h2 (Or.inr hu1)).2 hv1

/-- The core transversality computation: `(1-r) a + r d = 0` with `d ≠ 0` transverse to `a`
(when `a ≠ 0`) forces `r = 0` and `a = 0`. -/
theorem gc_seg_avoid {a d : ℝ × ℝ} (hd : d ≠ 0) (had : a ≠ 0 → gcDet a d ≠ 0) {r : ℝ}
    (h1 : (1 - r) * a.1 + r * d.1 = 0) (h2 : (1 - r) * a.2 + r * d.2 = 0) : r = 0 ∧ a = 0 := by
  by_cases ha : a = 0
  · subst ha
    simp at h1 h2
    refine ⟨?_, rfl⟩
    by_contra hr
    exact hd (Prod.ext (by simpa [hr] using h1) (by simpa [hr] using h2))
  · have hdet := had ha
    have : r * gcDet a d = 0 := by
      simp only [gcDet]; linear_combination a.1 * h2 - a.2 * h1
    rcases mul_eq_zero.1 this with hr | hr
    · subst hr
      exact absurd (Prod.ext (by simpa using h1) (by simpa using h2)) ha
    · exact absurd hr hdet

/-- A segment of the body over a cap whose only possible points over the great circle are its
ends maps, by the radial projection, into the cap and off any `C ⊆ greatCircle3` missing the
images of its ends. -/
theorem gc_segment_mem {x : Sphere3} {c : ℝ} (hc : 1 / 2 ≤ c) {C : Set Sphere3}
    (hC : C ⊆ greatCircle3) {u w : EuclideanSpace ℝ (Fin 4)} (hu : u ∈ gcBody x c)
    (hw : w ∈ gcBody x c) (huC : gcF x u ∉ C) (hwC : gcF x w ∉ C)
    (H : ∀ r : I, (AffineMap.lineMap u w (r : ℝ) : EuclideanSpace ℝ (Fin 4)) 2 = 0 →
      (AffineMap.lineMap u w (r : ℝ) : EuclideanSpace ℝ (Fin 4)) 3 = 0 →
      AffineMap.lineMap u w (r : ℝ) = u ∨ AffineMap.lineMap u w (r : ℝ) = w) (t : I) :
    gcF x (Path.segment u w t) ∈ gcCap x c ∧ gcF x (Path.segment u w t) ∉ C := by
  have hmem : Path.segment u w t ∈ gcBody x c :=
    (convex_gcBody x c).lineMap_mem hu hw t.2
  refine ⟨gcF_mem_gcCap hc hmem, fun hC' => ?_⟩
  have h12 : 1 / 2 ≤ inner ℝ (Path.segment u w t) (x : EuclideanSpace ℝ (Fin 4)) :=
    hc.trans hmem.2.le
  obtain ⟨e2, e3⟩ := (gcF_mem_iff h12).1 (hC hC')
  rcases H t e2 e3 with h | h
  · exact huC (by rw [← h]; exact hC')
  · exact hwC (by rw [← h]; exact hC')

theorem gc_lineMap_apply (u w : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (i : Fin 4) :
    (AffineMap.lineMap u w r : EuclideanSpace ℝ (Fin 4)) i = (1 - r) * u i + r * w i := by
  simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- **Local joining off `C`.** In a cap around a point of the great circle, any two points off a
subset `C` of the great circle are joined by a path of the cap off `C`: through a midpoint pushed
off the great circle in a direction transverse to both. -/
theorem gc_join {x : Sphere3} (hx : x ∈ greatCircle3) {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1)
    {C : Set Sphere3} (hC : C ⊆ greatCircle3) {a b : Sphere3} (ha : a ∈ gcCap x c)
    (hb : b ∈ gcCap x c) (haC : a ∉ C) (hbC : b ∉ C) :
    ∃ ω : Path a b, ∀ t, ω t ∈ gcCap x c ∧ ω t ∉ C := by
  set η : ℝ := (1 - c) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η ≤ 1 / 4 := by rw [hη]; linarith
  obtain ⟨d, hd0, hd1, hd2, hda, hdb⟩ := gc_exists_dir ((a : EuclideanSpace ℝ (Fin 4)) 2,
    (a : EuclideanSpace ℝ (Fin 4)) 3) ((b : EuclideanSpace ℝ (Fin 4)) 2,
    (b : EuclideanSpace ℝ (Fin 4)) 3) (show 0 < η / 2 by linarith)
  set m : EuclideanSpace ℝ (Fin 4) := (1 - η) • (x : EuclideanSpace ℝ (Fin 4)) + gcEmb d with hm
  have hx2 : (x : EuclideanSpace ℝ (Fin 4)) 2 = 0 := hx.1
  have hx3 : (x : EuclideanSpace ℝ (Fin 4)) 3 = 0 := hx.2
  have hm2 : m 2 = d.1 := by simp [hm, hx2]
  have hm3 : m 3 = d.2 := by simp [hm, hx3]
  have hmx : inner ℝ m (x : EuclideanSpace ℝ (Fin 4)) = 1 - η := by
    rw [hm, inner_add_left, real_inner_smul_left, sphere3_inner_self, inner_gcEmb_of_mem hx]; ring
  have hmB : m ∈ gcBody x c := by
    refine ⟨?_, by rw [hmx, hη]; linarith⟩
    have he : ‖gcEmb d‖ ≤ η := (norm_gcEmb_le d).trans (by linarith)
    have hsq : ‖m‖ ^ 2 ≤ 1 := by
      rw [hm, norm_add_sq_real, norm_smul, real_inner_smul_left,
        real_inner_comm, inner_gcEmb_of_mem hx, mem_sphere_zero_iff_norm.1 x.2,
        Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - η)]
      have : ‖gcEmb d‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he 2
      nlinarith
    nlinarith [norm_nonneg m]
  have hmC : gcF x m ∉ C := fun h => by
    obtain ⟨e2, e3⟩ := (gcF_mem_iff (hc.trans hmB.2.le)).1 (hC h)
    exact hd0 (Prod.ext (hm2 ▸ e2) (hm3 ▸ e3))
  have hFa : gcF x a = a := gcF_sphere (hc.trans ha.le)
  have hFb : gcF x b = b := gcF_sphere (hc.trans hb.le)
  have haC' : gcF x a ∉ C := hFa.symm ▸ haC
  have hbC' : gcF x b ∉ C := hFb.symm ▸ hbC
  have h1 := gc_segment_mem hc hC (coe_mem_gcBody ha) hmB haC' hmC (fun r e2 e3 => by
    rw [gc_lineMap_apply, hm2] at e2
    rw [gc_lineMap_apply, hm3] at e3
    obtain ⟨hr, -⟩ := gc_seg_avoid hd0 hda e2 e3
    left; rw [hr]; simp)
  have h2 := gc_segment_mem hc hC hmB (coe_mem_gcBody hb) hmC hbC' (fun r e2 e3 => by
    rw [gc_lineMap_apply, hm2] at e2
    rw [gc_lineMap_apply, hm3] at e3
    obtain ⟨hr, -⟩ := gc_seg_avoid (r := 1 - r) hd0 hdb (by linarith) (by linarith)
    right; rw [show (r : ℝ) = 1 by linarith]; simp)
  refine ⟨(((Path.segment (a : EuclideanSpace ℝ (Fin 4)) m).map (continuous_gcF x)).cast
    hFa.symm rfl).trans (((Path.segment m (b : EuclideanSpace ℝ (Fin 4))).map
    (continuous_gcF x)).cast rfl hFb.symm), fun t => ?_⟩
  rw [Path.trans_apply]
  split_ifs
  · exact h1 _
  · exact h2 _

/-- The straight-line homotopy, pushed by `F`, with a pointwise membership condition. -/
theorem gc_homotopicIn_map_line {X : Type*} [TopologicalSpace X] {U : Set X}
    {a b : EuclideanSpace ℝ (Fin 4)} (α β : Path a b) {F : EuclideanSpace ℝ (Fin 4) → X}
    (hF : Continuous F) (h : ∀ s t : I, F (AffineMap.lineMap (α t) (β t) (s : ℝ)) ∈ U) :
    HomotopicIn U (α.map hF) (β.map hF) :=
  ⟨(lineHomotopy α β).map ⟨F, hF⟩, fun w => h w.1 w.2⟩

/-- The hat function `max 0 (1 - |u|)`. -/
def gcHat (u : ℝ) : ℝ := max 0 (1 - |u|)

theorem continuous_gcHat : Continuous gcHat := by unfold gcHat; fun_prop

/-- On `[i, i+1]` the hat functions interpolate linearly between `v i` and `v (i+1)`. -/
theorem gc_sum_hat {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ℕ → E) {N i : ℕ} (hi : i < N)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ j ∈ Finset.range (N + 1), gcHat (i + r - j) • v j = (1 - r) • v i + r • v (i + 1) := by
  rw [Finset.sum_eq_add_of_mem i (i + 1) (by simp; omega) (by simp; omega) (by omega)]
  · congr 1
    · simp [gcHat, abs_of_nonneg hr0, max_eq_right (by linarith : 0 ≤ 1 - r)]
    · push_cast
      rw [show (i : ℝ) + r - (i + 1) = r - 1 by ring, gcHat, abs_of_nonpos (by linarith),
        max_eq_right (by linarith)]
      congr 1; ring
  · intro j _ hj
    have h1 : 1 ≤ |(i : ℝ) + r - j| := by
      rcases lt_or_gt_of_ne hj.1 with h | h
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (i : ℝ) + 2 ≤ j := by
          have : i + 2 ≤ j := by omega
          exact_mod_cast this
        rw [abs_of_nonpos (by linarith)]; linarith
    simp [gcHat, max_eq_left (by linarith : 1 - |(i : ℝ) + r - j| ≤ 0)]

/-- Every `t ∈ [0,1]` is `(i + r)/N` with `i < N`, `0 ≤ r ≤ 1`. -/
theorem gc_exists_piece {N : ℕ} (hN : 1 ≤ N) (t : I) :
    ∃ i : ℕ, i < N ∧ ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ (N : ℝ) * t = i + r := by
  have h0 : 0 ≤ (N : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) t.2.1
  have hle : (N : ℝ) * t ≤ N := by
    have := t.2.2; nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  set q := ⌊(N : ℝ) * t⌋₊ with hq
  have hq1 : (q : ℝ) ≤ N * t := Nat.floor_le h0
  have hq2 : (N : ℝ) * t < q + 1 := Nat.lt_floor_add_one _
  by_cases hqN : q < N
  · exact ⟨q, hqN, N * t - q, by linarith, by linarith, by ring⟩
  · refine ⟨N - 1, by omega, 1, zero_le_one, le_rfl, ?_⟩
    have : (N : ℝ) ≤ q := by exact_mod_cast (not_lt.1 hqN)
    rw [Nat.cast_sub hN]; push_cast; linarith

/-- The perturbation step: `κ • u⊥` with `κ` one of two small values, transverse to `u`. -/
def gcPick (u c : ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  if gcDet u (c + (s / (|u.1| + |u.2| + 1)) • (-u.2, u.1)) ≠ 0 then
    (s / (|u.1| + |u.2| + 1)) • (-u.2, u.1) else (s / (|u.1| + |u.2| + 1) / 2) • (-u.2, u.1)

theorem gcPick_bound (u c : ℝ × ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |(gcPick u c s).1| ≤ s ∧ |(gcPick u c s).2| ≤ s := by
  have hA : 0 < |u.1| + |u.2| + 1 := by positivity
  set τ := s / (|u.1| + |u.2| + 1) with hτ
  have hτ0 : 0 ≤ τ := div_nonneg hs hA.le
  have hτA : τ * (|u.1| + |u.2| + 1) = s := div_mul_cancel₀ s hA.ne'
  have key : ∀ κ, 0 ≤ κ → κ ≤ τ → |(κ • (-u.2, u.1)).1| ≤ s ∧ |(κ • (-u.2, u.1)).2| ≤ s := by
    intro κ hκ hκτ
    simp only [Prod.smul_mk, smul_eq_mul, abs_mul, abs_neg, abs_of_nonneg hκ]
    constructor <;> nlinarith [abs_nonneg u.1, abs_nonneg u.2]
  unfold gcPick
  split_ifs
  · exact key τ hτ0 le_rfl
  · exact key (τ / 2) (by positivity) (by linarith)

theorem gcDet_add_smul_perp (u c : ℝ × ℝ) (κ : ℝ) :
    gcDet u (c + κ • (-u.2, u.1)) = gcDet u c + κ * (u.1 ^ 2 + u.2 ^ 2) := by
  simp only [gcDet, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]; ring

theorem gcPick_det {u : ℝ × ℝ} (hu : u ≠ 0) (c : ℝ × ℝ) {s : ℝ} (hs : 0 < s) :
    gcDet u (c + gcPick u c s) ≠ 0 := by
  have hQ : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    by_contra h
    push Not at h
    have h1 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    have h2 : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    exact hu (Prod.ext h1 h2)
  have hA : 0 < |u.1| + |u.2| + 1 := by positivity
  have hτ : 0 < s / (|u.1| + |u.2| + 1) := div_pos hs hA
  unfold gcPick
  split_ifs with h
  · exact h
  · push Not at h
    rw [gcDet_add_smul_perp] at h ⊢
    intro h'
    nlinarith

/-- The projections of the perturbed vertices, chosen successively transverse. -/
def gcSeq (c : ℕ → ℝ × ℝ) (s : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | j + 1 => c (j + 1) + gcPick (gcSeq c s j) (c (j + 1)) s

theorem gcDet_zero_right (u : ℝ × ℝ) : gcDet u 0 = 0 := by simp [gcDet]

theorem gcSeq_spec (c : ℕ → ℝ × ℝ) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    gcSeq c s j ≠ 0 ∧ gcDet (gcSeq c s j) (gcSeq c s (j + 1)) ≠ 0 := by
  induction j with
  | zero =>
    have h0 : gcSeq c s 0 ≠ 0 := fun h => by simpa [gcSeq] using congrArg Prod.fst h
    exact ⟨h0, gcPick_det h0 _ hs⟩
  | succ j ih =>
    have h0 : gcSeq c s (j + 1) ≠ 0 := fun h => ih.2 (by rw [h, gcDet_zero_right])
    exact ⟨h0, gcPick_det h0 _ hs⟩

/-- **General position, the key lemma of tameness.** If `K` is a closed subset of the great
circle and `x` a point of the great circle off `K`, every loop at `x` in the cap `⟨·, x⟩ > 3/4`
off `K` is null-homotopic in `S³ ∖ K`: approximate it by a polygon whose vertices are pushed off
the great circle successively transversally (`GX.gcSeq`), so that the polygon meets the plane of
the great circle only at `x`; then cone the polygon off to `x`. -/
theorem gc_loop_null {K : Set Sphere3} (hK : IsClosed K) (hKΓ : K ⊆ greatCircle3) {x : Sphere3}
    (hx : x ∈ greatCircle3) (hxK : x ∉ K) (α : Path x x) (hα : ∀ t, α t ∈ gcCap x (3 / 4))
    (hαK : ∀ t, α t ∉ K) : HomotopicIn Kᶜ α (Path.refl x) := by
  -- a uniform distance from `K`
  obtain ⟨d, hd, hdK⟩ : ∃ d > 0, ∀ t k, k ∈ K → d ≤ dist (α t) k := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, fun _ _ h => h.elim⟩
    · have hcont : Continuous fun t => Metric.infDist (α t) K :=
        (Metric.continuous_infDist_pt K).comp α.continuous
      obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hcont.continuousOn
      exact ⟨Metric.infDist (α t₀) K, (hK.notMem_iff_infDist_pos hne).1 (hαK t₀),
        fun t k hk => (ht₀ (mem_univ t)).trans (Metric.infDist_le_dist_of_mem hk)⟩
  set ε : ℝ := min d 1 / 8 with hεdef
  have hε : 0 < ε := by positivity
  have hεd : 4 * ε < d := by
    have := min_le_left d 1; rw [hεdef]; linarith
  have hε1 : ε ≤ 1 / 8 := by
    have := min_le_right d 1; rw [hεdef]; linarith
  obtain ⟨δ, hδ, hδα⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous α.continuous) ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  set N : ℕ := M + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNδ : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    have : (M : ℝ) + 2 = N := by rw [hNdef]; push_cast; ring
    rw [div_lt_iff₀ hδ] at hM
    nlinarith
  -- vertices
  set tN : ℕ → I := fun j => Set.projIcc 0 1 zero_le_one ((j : ℝ) / N) with htN
  have htN_le : ∀ j, j ≤ N → ((tN j : I) : ℝ) = j / N := fun j hj => by
    simp only [htN, Set.coe_projIcc]
    have h1 : (j : ℝ) / N ≤ 1 := by
      rw [div_le_one hNpos]; exact_mod_cast hj
    rw [min_eq_right h1, max_eq_right (by positivity)]
  have htN_ge : ∀ j, N ≤ j → tN j = 1 := fun j hj => by
    apply Subtype.ext
    simp only [htN, Set.coe_projIcc]
    have h1 : 1 ≤ (j : ℝ) / N := by
      rw [le_div_iff₀ hNpos, one_mul]; exact_mod_cast hj
    rw [min_eq_left h1, max_eq_right zero_le_one]; rfl
  have htN0 : tN 0 = 0 := Subtype.ext (by rw [htN_le 0 (by omega)]; simp)
  set cc : ℕ → ℝ × ℝ := fun j =>
    ((α (tN j) : EuclideanSpace ℝ (Fin 4)) 2, (α (tN j) : EuclideanSpace ℝ (Fin 4)) 3) with hcc
  have hs : 0 < ε / 4 := by positivity
  set u : ℕ → ℝ × ℝ := gcSeq cc (ε / 4) with hu
  have hu_spec := gcSeq_spec cc hs
  have hu_succ : ∀ k, u (k + 1) - cc (k + 1) = gcPick (u k) (cc (k + 1)) (ε / 4) := fun k => by
    simp [hu, gcSeq]
  set v : ℕ → EuclideanSpace ℝ (Fin 4) := fun j => if j = 0 ∨ N ≤ j then (x : EuclideanSpace ℝ (Fin 4))
    else (α (tN j) : EuclideanSpace ℝ (Fin 4)) + gcEmb (u j - cc j) with hv
  have hx2 : (x : EuclideanSpace ℝ (Fin 4)) 2 = 0 := hx.1
  have hx3 : (x : EuclideanSpace ℝ (Fin 4)) 3 = 0 := hx.2
  -- vertices are close to the loop
  have hv_close : ∀ j, ‖v j - (α (tN j) : EuclideanSpace ℝ (Fin 4))‖ ≤ ε / 2 := fun j => by
    by_cases hj : j = 0 ∨ N ≤ j
    · have : α (tN j) = x := by
        rcases hj with rfl | hj
        · rw [htN0, α.source]
        · rw [htN_ge j hj, α.target]
      simp only [hv, if_pos hj, this, sub_self, norm_zero]; positivity
    · simp only [hv, if_neg hj, add_sub_cancel_left]
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [hu_succ]
      obtain ⟨b1, b2⟩ := gcPick_bound (u k) (cc (k + 1)) hs.le
      exact (norm_gcEmb_le _).trans (by linarith)
  -- projections of the vertices
  have hv_proj_end : ∀ j, (j = 0 ∨ N ≤ j) → v j 2 = 0 ∧ v j 3 = 0 := fun j hj => by
    simp only [hv, if_pos hj]; exact ⟨hx2, hx3⟩
  have hv_proj_mid : ∀ j, ¬ (j = 0 ∨ N ≤ j) → (v j 2, v j 3) = u j := fun j hj => by
    simp only [hv, if_neg hj, PiLp.add_apply, gcEmb_two, gcEmb_three, hcc, Prod.fst_sub,
      Prod.snd_sub]
    ext <;> simp
  -- the polygon
  let P : Path (x : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) :=
    { toFun := fun t => ∑ j ∈ Finset.range (N + 1), gcHat (N * (t : ℝ) - j) • v j
      continuous_toFun := by
        refine continuous_finsetSum _ fun j _ => ?_
        exact (continuous_gcHat.comp ((continuous_const.mul continuous_subtype_val).sub
          continuous_const)).smul continuous_const
      source' := by
        have := gc_sum_hat v (N := N) (i := 0) (by omega) le_rfl zero_le_one
        simp only [Nat.cast_zero, zero_add] at this
        simp only [Icc.coe_zero, mul_zero]
        rw [this]; simp [hv]
      target' := by
        have := gc_sum_hat v (N := N) (i := N - 1) (by omega) zero_le_one le_rfl
        rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.sub_add_cancel (by omega : 1 ≤ N)] at this
        simp only [Icc.coe_one, mul_one]
        push_cast at this
        rw [show (N : ℝ) = N - 1 + 1 by ring]
        rw [this]; simp [hv] }
  have hP : ∀ t : I, ∀ i : ℕ, i < N → ∀ r : ℝ, 0 ≤ r → r ≤ 1 → (N : ℝ) * t = i + r →
      P t = (1 - r) • v i + r • v (i + 1) := by
    intro t i hi r hr0 hr1 he
    show ∑ j ∈ Finset.range (N + 1), gcHat (N * (t : ℝ) - j) • v j = _
    rw [he]; exact gc_sum_hat v hi hr0 hr1
  -- the polygon is close to the loop
  have hPclose : ∀ t : I, ‖P t - (α t : EuclideanSpace ℝ (Fin 4))‖ ≤ 2 * ε := by
    intro t
    obtain ⟨i, hi, r, hr0, hr1, he⟩ := gc_exists_piece (by omega : 1 ≤ N) t
    have hvt : ∀ j, (j = i ∨ j = i + 1) →
        ‖v j - (α t : EuclideanSpace ℝ (Fin 4))‖ ≤ 2 * ε := by
      intro j hj
      have hjN : j ≤ N := by omega
      have hdt : dist (tN j) t < δ := by
        rw [Subtype.dist_eq, htN_le j hjN, Real.dist_eq]
        have ht : (t : ℝ) = (i + r) / N := by field_simp; linarith
        rw [ht, ← sub_div, abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
        rw [div_lt_iff₀ hNpos] at hNδ
        rcases hj with rfl | rfl
        · rw [abs_of_nonpos (by linarith)]; nlinarith
        · push_cast; rw [abs_of_nonneg (by linarith)]; nlinarith
      have h1 := hδα hdt
      rw [Subtype.dist_eq, dist_eq_norm] at h1
      calc ‖v j - (α t : EuclideanSpace ℝ (Fin 4))‖
          = ‖(v j - (α (tN j) : EuclideanSpace ℝ (Fin 4))) +
              ((α (tN j) : EuclideanSpace ℝ (Fin 4)) - α t)‖ := by congr 1; abel
        _ ≤ ε / 2 + ε := (norm_add_le _ _).trans (add_le_add (hv_close j) h1.le)
        _ ≤ 2 * ε := by linarith
    rw [hP t i hi r hr0 hr1 he]
    have e : (1 - r) • v i + r • v (i + 1) - (α t : EuclideanSpace ℝ (Fin 4)) =
        (1 - r) • (v i - α t) + r • (v (i + 1) - α t) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul]; simp
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg hr0]
    nlinarith [hvt i (Or.inl rfl), hvt (i + 1) (Or.inr rfl)]
  -- the polygon meets the plane of the great circle only at `x`
  have hPplane : ∀ t : I, P t 2 = 0 → P t 3 = 0 → P t = x := by
    intro t h2 h3
    obtain ⟨i, hi, r, hr0, hr1, he⟩ := gc_exists_piece (by omega : 1 ≤ N) t
    rw [hP t i hi r hr0 hr1 he] at h2 h3 ⊢
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h2 h3
    by_cases hi0 : i = 0
    · subst hi0
      have hm : ¬ (1 = 0 ∨ N ≤ 1) := by omega
      have hp := hv_proj_mid 1 hm
      obtain ⟨e2, e3⟩ := hv_proj_end 0 (Or.inl rfl)
      rw [e2] at h2; rw [e3] at h3
      have e2' : v 1 2 = (u 1).1 := congrArg Prod.fst hp
      have e3' : v 1 3 = (u 1).2 := congrArg Prod.snd hp
      rw [e2'] at h2; rw [e3'] at h3
      obtain ⟨hr, -⟩ := gc_seg_avoid (a := 0) (hu_spec 1).1 (fun h => absurd rfl h)
        (by simpa using h2) (by simpa using h3)
      rw [hr]; simp [hv]
    by_cases hiN : i + 1 = N
    · have hm : ¬ (i = 0 ∨ N ≤ i) := by omega
      have hp := hv_proj_mid i hm
      obtain ⟨e2, e3⟩ := hv_proj_end (i + 1) (Or.inr hiN.ge)
      rw [e2] at h2; rw [e3] at h3
      have e2' : v i 2 = (u i).1 := congrArg Prod.fst hp
      have e3' : v i 3 = (u i).2 := congrArg Prod.snd hp
      rw [e2'] at h2; rw [e3'] at h3
      obtain ⟨hr, -⟩ := gc_seg_avoid (a := 0) (r := 1 - r) (hu_spec i).1 (fun h => absurd rfl h)
        (by simp only [Prod.fst_zero, mul_zero, zero_add]; linarith)
        (by simp only [Prod.snd_zero, mul_zero, zero_add]; linarith)
      rw [show r = 1 by linarith]; simp [hv, hiN]
    · have hm : ¬ (i = 0 ∨ N ≤ i) := by omega
      have hm' : ¬ (i + 1 = 0 ∨ N ≤ i + 1) := by omega
      have hp := hv_proj_mid i hm
      have hp' := hv_proj_mid (i + 1) hm'
      rw [show v i 2 = (u i).1 from congrArg Prod.fst hp,
        show v (i + 1) 2 = (u (i + 1)).1 from congrArg Prod.fst hp'] at h2
      rw [show v i 3 = (u i).2 from congrArg Prod.snd hp,
        show v (i + 1) 3 = (u (i + 1)).2 from congrArg Prod.snd hp'] at h3
      obtain ⟨-, h0⟩ := gc_seg_avoid (hu_spec (i + 1)).1 (fun _ => (hu_spec i).2) h2 h3
      exact absurd h0 (hu_spec i).1
  -- inner products
  have hαx : ∀ t, 3 / 4 < inner ℝ (α t : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) :=
    fun t => hα t
  have hinner_le : ∀ w : EuclideanSpace ℝ (Fin 4),
      |inner ℝ w (x : EuclideanSpace ℝ (Fin 4))| ≤ ‖w‖ := fun w => by
    have := abs_real_inner_le_norm w (x : EuclideanSpace ℝ (Fin 4))
    rwa [mem_sphere_zero_iff_norm.1 x.2, mul_one] at this
  have hPx : ∀ t : I, 1 / 2 ≤ inner ℝ (P t) (x : EuclideanSpace ℝ (Fin 4)) := fun t => by
    have e : inner ℝ (P t) (x : EuclideanSpace ℝ (Fin 4)) =
        inner ℝ (α t : EuclideanSpace ℝ (Fin 4)) x +
          inner ℝ (P t - (α t : EuclideanSpace ℝ (Fin 4))) x := by
      rw [inner_sub_left]; ring
    have h1 := hinner_le (P t - (α t : EuclideanSpace ℝ (Fin 4)))
    rw [abs_le] at h1
    linarith [hαx t, hPclose t]
  have hFx : gcF x x = x := gcF_self x
  -- first homotopy: the loop to the polygon
  have H1 : HomotopicIn Kᶜ ((α.map continuous_subtype_val).map (continuous_gcF x))
      (P.map (continuous_gcF x)) := by
    refine gc_homotopicIn_map_line _ _ (continuous_gcF x) fun s t hK' => ?_
    set z := AffineMap.lineMap ((α.map continuous_subtype_val) t) (P t) (s : ℝ) with hz
    have hz' : z = (α t : EuclideanSpace ℝ (Fin 4)) +
        (s : ℝ) • (P t - (α t : EuclideanSpace ℝ (Fin 4))) := by
      rw [hz, AffineMap.lineMap_apply_module]
      simp only [Path.map_coe, Function.comp_apply]
      rw [smul_sub, sub_smul, one_smul]; abel
    have hzx : 1 / 2 ≤ inner ℝ z (x : EuclideanSpace ℝ (Fin 4)) := by
      rw [hz', inner_add_left, real_inner_smul_left]
      have h1 := hinner_le (P t - (α t : EuclideanSpace ℝ (Fin 4)))
      rw [abs_le] at h1
      have hs0 := s.2.1; have hs1 := s.2.2
      nlinarith [hαx t, hPclose t]
    have hzα : ‖z - (α t : EuclideanSpace ℝ (Fin 4))‖ ≤ 2 * ε := by
      rw [hz', add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.2.1]
      nlinarith [hPclose t, s.2.2, norm_nonneg (P t - (α t : EuclideanSpace ℝ (Fin 4)))]
    have := hdK t _ hK'
    have h2 := gcF_dist_le (y := α t) hzx
    rw [dist_comm] at this
    linarith
  -- second homotopy: the polygon to the constant loop (the cone on `x`)
  have H2 : HomotopicIn Kᶜ (P.map (continuous_gcF x))
      ((Path.refl (x : EuclideanSpace ℝ (Fin 4))).map (continuous_gcF x)) := by
    refine gc_homotopicIn_map_line _ _ (continuous_gcF x) fun s t hK' => ?_
    set z := AffineMap.lineMap (P t) ((Path.refl (x : EuclideanSpace ℝ (Fin 4))) t) (s : ℝ)
      with hz
    have hz2 : ∀ i : Fin 4, z i = (1 - s) * P t i + s * (x : EuclideanSpace ℝ (Fin 4)) i :=
      fun i => by rw [hz, gc_lineMap_apply]; rfl
    have hzx : 1 / 2 ≤ inner ℝ z (x : EuclideanSpace ℝ (Fin 4)) := by
      rw [hz, AffineMap.lineMap_apply_module, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, Path.refl_apply, sphere3_inner_self]
      have := hPx t; have hs0 := s.2.1; have hs1 := s.2.2
      nlinarith
    obtain ⟨e2, e3⟩ := (gcF_mem_iff hzx).1 (hKΓ hK')
    rw [hz2, hx2] at e2; rw [hz2, hx3] at e3
    simp only [mul_zero, add_zero] at e2 e3
    have hzx' : z = x := by
      by_cases hs1 : (s : ℝ) = 1
      · rw [hz, hs1, AffineMap.lineMap_apply_one]; rfl
      · have hs' : (1 - (s : ℝ)) ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
        have h2 : P t 2 = 0 := (mul_eq_zero.1 e2).resolve_left hs'
        have h3 : P t 3 = 0 := (mul_eq_zero.1 e3).resolve_left hs'
        rw [hz, hPplane t h2 h3, Path.refl_apply, AffineMap.lineMap_same_apply]
    rw [hzx', hFx] at hK'
    exact hxK hK'
  have H := H1.trans H2
  refine (H.cast hFx.symm hFx.symm).of_eq ?_ ?_
  · refine Path.ext (funext fun t => ?_)
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact gcF_sphere (by linarith [hαx t])
  · refine Path.ext (funext fun t => ?_)
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.refl_apply]
    exact hFx

/-- A Cantor subset of the great circle misses points of the great circle arbitrarily close to
any point of it. -/
theorem gc_exists_off {C : Set Sphere3} (hC : IsCantorSubset C) {x : Sphere3}
    (hx : x ∈ greatCircle3) {c : ℝ} (hc : c < 1) :
    ∃ p ∈ greatCircle3, p ∈ gcCap x c ∧ p ∉ C := by
  by_cases hxC : x ∉ C
  · exact ⟨x, hx, mem_gcCap_self hc, hxC⟩
  push Not at hxC
  obtain ⟨e⟩ := hC
  haveI : TotallyDisconnectedSpace C :=
    (e.trans cantorSetHomeomorphNatToBool).symm.totallyDisconnectedSpace
  have htd : IsTotallyDisconnected C := totallyDisconnectedSpace_subtype_iff.1 this
  set x₀ : EuclideanSpace ℝ (Fin 4) := (x : EuclideanSpace ℝ (Fin 4)) with hx₀def
  have hx₀x₀ : inner ℝ x₀ x₀ = 1 := sphere3_inner_self x
  set u := sphere3Perp x₀
  have hxu : inner ℝ x₀ u = 0 := inner_sphere3Perp_self x₀
  have huu : inner ℝ u u = 1 := by rw [inner_sphere3Perp_sphere3Perp, hx₀x₀]
  have hx2' : x₀ 2 = 0 := hx.1
  have hx3' : x₀ 3 = 0 := hx.2
  have hu2 : u 2 = 0 := by simp [u, sphere3Perp, hx3']
  have hu3 : u 3 = 0 := by simp [u, sphere3Perp, hx2']
  set f : ℝ → EuclideanSpace ℝ (Fin 4) := fun θ => Real.cos θ • x₀ + Real.sin θ • u with hfdef
  have hfu : ∀ θ, inner ℝ (f θ) u = Real.sin θ := fun θ => by
    simp only [hfdef, inner_add_left, real_inner_smul_left, hxu, huu]; ring
  have hfx : ∀ θ, inner ℝ (f θ) x₀ = Real.cos θ := fun θ => by
    simp only [hfdef, inner_add_left, real_inner_smul_left, hx₀x₀, real_inner_comm x₀ u, hxu]
    ring
  have hff : ∀ θ, inner ℝ (f θ) (f θ) = 1 := fun θ => by
    simp only [hfdef, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hxu, huu, hx₀x₀, real_inner_comm x₀ u]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hfn : ∀ θ, ‖f θ‖ = 1 := fun θ => by
    have h := hff θ
    rw [real_inner_self_eq_norm_sq] at h
    have h0 := norm_nonneg (f θ)
    nlinarith
  let g : ℝ → Sphere3 := fun θ => ⟨f θ, mem_sphere_zero_iff_norm.2 (hfn θ)⟩
  have hg : Continuous g := Continuous.subtype_mk
    ((Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)) _
  have hg0 : g 0 = x := Subtype.ext (by
    change Real.cos 0 • x₀ + Real.sin 0 • u = x₀
    simp)
  have hgΓ : ∀ θ, g θ ∈ greatCircle3 := fun θ => by
    refine ⟨?_, ?_⟩ <;> simp [g, hfdef, hu2, hu3, hx.1, hx.2, x₀]
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1
    (hg.continuousAt.preimage_mem_nhds (hg0 ▸ (isOpen_gcCap x c).mem_nhds (mem_gcCap_self hc) :
      gcCap x c ∈ 𝓝 (g 0)))
  set s : ℝ := min (r / 2) 1 with hsdef
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcap : ∀ θ ∈ Icc 0 s, g θ ∈ gcCap x c := fun θ hθ => hrsub (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2])
  by_contra hne
  push Not at hne
  have hsub : g '' Icc 0 s ⊆ C := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact hne _ (hgΓ θ) (hcap θ hθ)
  have hss := htd _ hsub (isPreconnected_Icc.image _ hg.continuousOn)
  have heq : g s = g 0 := hss ⟨s, ⟨hs0.le, le_rfl⟩, rfl⟩ ⟨0, ⟨le_rfl, hs0.le⟩, rfl⟩
  have h1 : inner ℝ (f s) u = inner ℝ (f 0) u := by
    have := congrArg (fun y : Sphere3 => inner ℝ (y : EuclideanSpace ℝ (Fin 4)) u) heq
    exact this
  rw [hfu, hfu, Real.sin_zero] at h1
  have : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0
    (lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_gt_three]))
  linarith

/-- A small cap around `x` lies in the cap `⟨·, p⟩ > 3/4` around any of its points `p`. -/
theorem gcCap_subset_of_mem {x p : Sphere3} (hp : p ∈ gcCap x (999 / 1000)) :
    gcCap x (999 / 1000) ⊆ gcCap p (3 / 4) := by
  intro y hy
  have hsq : ‖(p : EuclideanSpace ℝ (Fin 4)) - x‖ ^ 2 < (1 / 10) ^ 2 := by
    rw [norm_sub_sq_real, mem_sphere_zero_iff_norm.1 p.2, mem_sphere_zero_iff_norm.1 x.2]
    have : (999 / 1000 : ℝ) < inner ℝ (p : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) := hp
    nlinarith
  have hn : ‖(p : EuclideanSpace ℝ (Fin 4)) - x‖ < 1 / 10 :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have h1 := abs_real_inner_le_norm (y : EuclideanSpace ℝ (Fin 4)) ((p : EuclideanSpace ℝ (Fin 4)) - x)
  rw [mem_sphere_zero_iff_norm.1 y.2, one_mul, abs_le] at h1
  change (3 / 4 : ℝ) < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (p : EuclideanSpace ℝ (Fin 4))
  have e : inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (p : EuclideanSpace ℝ (Fin 4)) =
      inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) +
        inner ℝ (y : EuclideanSpace ℝ (Fin 4)) ((p : EuclideanSpace ℝ (Fin 4)) - x) := by
    rw [inner_sub_right]; ring
  have hy' : (999 / 1000 : ℝ) < inner ℝ (y : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 4)) := hy
  linarith

theorem gc_homotopicIn_of_trans_symm {X : Type*} [TopologicalSpace X] {U : Set X} {a b : X}
    {ρ₁ ρ₂ : Path a b} (h₁ : ∀ t, ρ₁ t ∈ U) (h₂ : ∀ t, ρ₂ t ∈ U)
    (h : HomotopicIn U (ρ₁.trans ρ₂.symm) (Path.refl a)) : HomotopicIn U ρ₁ ρ₂ := by
  have ha : a ∈ U := ρ₁.source ▸ h₁ 0
  have hRa : ∀ t, (Path.refl a) t ∈ U := fun _ => ha
  rw [homotopicIn_iff_mk (path_trans_mem h₁ (path_symm_mem h₂)) hRa,
    pathToSub_trans _ _ h₁ (path_symm_mem h₂), pathToSub_symm _ h₂,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at h
  have e1 : pathToSub (Path.refl a) hRa = Path.refl (⟨a, ha⟩ : U) := by ext; rfl
  rw [e1, Path.Homotopic.Quotient.mk_refl] at h
  rw [homotopicIn_iff_mk h₁ h₂]
  have h2 := congrArg (fun q => Path.Homotopic.Quotient.trans q
    (Path.Homotopic.Quotient.mk (pathToSub ρ₂ h₂))) h
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] at h2
  exact h2

/-- **Paths in a small cap around a point of the great circle, off a Cantor subset `C` of it, are
homotopic in `S³ ∖ C`** (conjugate to a loop at a point of the great circle off `C`, then
`GX.gc_loop_null`). -/
theorem gc_paths_homotopicIn {C : Set Sphere3} (hC : IsCantorSubset C) (hCΓ : C ⊆ greatCircle3)
    {x : Sphere3} (hx : x ∈ greatCircle3) {a b : Sphere3} (ρ₁ ρ₂ : Path a b)
    (h₁ : ∀ t, ρ₁ t ∈ gcCap x (999 / 1000) ∧ ρ₁ t ∉ C)
    (h₂ : ∀ t, ρ₂ t ∈ gcCap x (999 / 1000) ∧ ρ₂ t ∉ C) : HomotopicIn Cᶜ ρ₁ ρ₂ := by
  obtain ⟨p, hpΓ, hpV, hpC⟩ := gc_exists_off hC hx (show (999 / 1000 : ℝ) < 1 by norm_num)
  have ha : a ∈ gcCap x (999 / 1000) ∧ a ∉ C := by simpa using h₁ 0
  obtain ⟨δ, hδ⟩ := gc_join hx (by norm_num) (by norm_num) hCΓ hpV ha.1 hpC ha.2
  set S : Set Sphere3 := gcCap x (999 / 1000) ∩ Cᶜ
  have hδS : ∀ t, δ t ∈ S := fun t => hδ t
  have h₁S : ∀ t, ρ₁ t ∈ S := fun t => h₁ t
  have h₂S : ∀ t, ρ₂ t ∈ S := fun t => h₂ t
  have hM : ∀ t, (ρ₁.trans ρ₂.symm) t ∈ S := path_trans_mem h₁S (path_symm_mem h₂S)
  have hL : ∀ t, ((δ.trans (ρ₁.trans ρ₂.symm)).trans δ.symm) t ∈ S :=
    path_trans_mem (path_trans_mem hδS hM) (path_symm_mem hδS)
  have hnull := gc_loop_null (IsCantorSubset.isClosed hC) hCΓ hpΓ hpC
    ((δ.trans (ρ₁.trans ρ₂.symm)).trans δ.symm) (fun t => gcCap_subset_of_mem hpV (hL t).1)
    (fun t => (hL t).2)
  have hδC : ∀ t, δ t ∈ Cᶜ := fun t => (hδ t).2
  have hMC : ∀ t, (ρ₁.trans ρ₂.symm) t ∈ Cᶜ := fun t => (hM t).2
  exact gc_homotopicIn_of_trans_symm (fun t => (h₁ t).2) (fun t => (h₂ t).2)
    (antoine_homotopicIn_conj hδC hMC hnull)

/-- **Tame Cantor sets.** The complement of a Cantor subset of a great circle of `S³` is
semi-locally simply connected in `S³`. -/
theorem tameCantorSLSC : TameCantorSLSC := by
  intro C hCΓ hC
  have hCc : IsClosed C := IsCantorSubset.isClosed hC
  refine ⟨dense_compl_of_isCantorSubset hC, fun x => ?_⟩
  by_cases hxC : x ∈ C
  · have hx : x ∈ greatCircle3 := hCΓ hxC
    refine ⟨gcCap x (999 / 1000), isOpen_gcCap x _, isPreconnected_gcCap x (by norm_num),
      mem_gcCap_self (by norm_num), fun γ hγ => ?_⟩
    have hγU : MemOmega Cᶜ γ := fun t h0 h1 => (hγ t h0 h1).2
    refine ⟨hγU, fun W hW => ?_⟩
    obtain ⟨c, hc0, hc1, hcW⟩ := exists_gcCap_subset hW (999 / 1000) (by norm_num)
    have hW' : gcCap x c ∈ 𝓝 x := (isOpen_gcCap x c).mem_nhds (mem_gcCap_self hc1)
    obtain ⟨t₀, h00, h0c, hhead⟩ := exists_head_mem γ hW' (c := 1 / 2) (by norm_num)
    obtain ⟨t₁, h1c, h11, htail⟩ := exists_tail_mem γ hW' (c := 1 / 2) (by norm_num)
    have h01 : (t₀ : ℝ) < t₁ := by linarith
    have ha : γ t₀ ∈ gcCap x c := hhead t₀ le_rfl
    have hb : γ t₁ ∈ gcCap x c := htail t₁ le_rfl
    have haC : γ t₀ ∉ C := hγU t₀ h00 (by linarith)
    have hbC : γ t₁ ∉ C := hγU t₁ (by linarith) h11
    obtain ⟨ω, hω⟩ := gc_join hx (by linarith) hc1 hCΓ ha hb haC hbC
    have hsub : ∀ t, subpath γ t₀ t₁ t ∈ gcCap x (999 / 1000) ∧ subpath γ t₀ t₁ t ∉ C :=
      fun t => by
        obtain ⟨s, hs1, hs2, hs⟩ := subpath_mem γ t₀ t₁ t
        rw [min_eq_left h01.le] at hs1
        rw [max_eq_right h01.le] at hs2
        rw [hs]
        exact hγ s (by linarith) (by linarith)
    have hωV : ∀ t, ω t ∈ gcCap x (999 / 1000) ∧ ω t ∉ C :=
      fun t => ⟨gcCap_mono hc0 (hω t).1, (hω t).2⟩
    refine ⟨splice γ t₀ t₁ h01 ω, fun t ht0 ht1 => ?_, splice_omegaHomotopic hγU h01 h11
      (gc_paths_homotopicIn hC hCΓ hx _ _ hsub hωV)⟩
    rcases splice_mem γ h01 ω t with ⟨hle, he⟩ | ⟨hge, he⟩ | ⟨s, hs⟩
    · rw [he]; exact ⟨hcW (hhead t hle), hγU t ht0 ht1⟩
    · rw [he]; exact ⟨hcW (htail t hge), hγU t ht0 ht1⟩
    · rw [← hs]; exact ⟨hcW (hω s).1, (hω s).2⟩
  · obtain ⟨c, hc0, hc1, hcW⟩ := exists_gcCap_subset (hCc.isOpen_compl.mem_nhds hxC) (1 / 2)
      (by norm_num)
    refine ⟨gcCap x c, isOpen_gcCap x _, isPreconnected_gcCap x hc0, mem_gcCap_self hc1,
      fun γ hγ => ?_⟩
    have hγV : ∀ t, γ t ∈ gcCap x c := fun t => by
      rcases eq_or_lt_of_le t.2.1 with h0 | h0
      · rw [show t = 0 from Subtype.ext h0.symm, γ.source]; exact mem_gcCap_self hc1
      rcases eq_or_lt_of_le t.2.2 with h1 | h1
      · rw [show t = 1 from Subtype.ext h1, γ.target]; exact mem_gcCap_self hc1
      exact (hγ t h0 h1).1
    refine ⟨fun t h0 h1 => (hγ t h0 h1).2, fun W hW => ⟨Path.refl x,
      fun _ _ _ => ⟨mem_of_mem_nhds hW, hxC⟩, ?_⟩⟩
    exact ((gcCap_homotopicIn hc0 γ (Path.refl x) hγV fun _ => mem_gcCap_self hc1).mono
      hcW).omegaHomotopic

end GX
#print axioms GX.tameCantorSLSC
