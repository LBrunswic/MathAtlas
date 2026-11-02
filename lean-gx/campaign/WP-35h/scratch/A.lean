import GXScaffold.Branched.GaloisExamples

open Set Filter Topology Function

noncomputable section
namespace GX

/-- Half-extent along `z` of a link of type `t`, in units of `1/640`. -/
def antoineEz : Fin 3 → ℤ
  | 0 => 7
  | 1 => 56
  | 2 => 56

theorem antoineMap_bounds_z (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) :
    |(antoineMap i p).2.2| ≤ antoineEz (antoineT i) / 640 := by
  obtain ⟨hz, hm, -⟩ := hp
  have hx : |p.1| ≤ 1 := (le_max_left _ _).trans hm
  have hy : |p.2.1| ≤ 1 := (le_max_right _ _).trans hm
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm, antoineEz, abs_mul,
      abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] <;> push_cast <;> linarith

theorem antoineComp_succ' (w : ℕ → Fin 64) (n : ℕ) :
    antoineComp w (n + 1) = antoineMap (w 0) ∘ antoineComp (fun k => w (k + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show antoineComp w (n + 1) ∘ antoineMap (w (n + 1)) = _
    rw [ih]; rfl

theorem antoineComp_mem_link (w : ℕ → Fin 64) (n : ℕ) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) :
    antoineComp w n p ∈ antoineLink := by
  have := antoineComp_antitone w (Nat.zero_le n) ⟨p, hp, rfl⟩
  simpa [antoineComp] using this

theorem antoine_mem_stage_of_map {i : Fin 64} {q : ℝ × ℝ × ℝ} (hq : q ∈ antoineLink) {j : ℕ}
    (h : antoineMap i q ∈ antoineStage (j + 1)) : q ∈ antoineStage j := by
  obtain ⟨w, hw⟩ := mem_iUnion.1 h
  obtain ⟨r, hr, hrq⟩ := hw
  rw [antoineComp_succ'] at hrq
  have hr' := antoineComp_mem_link (fun k => w (k + 1)) j hr
  by_cases hi : w 0 = i
  · subst hi
    exact mem_iUnion.2 ⟨_, r, hr, antoineMap_injective _ hrq⟩
  · exact absurd (Set.disjoint_left.1 (antoineMap_disjoint hi) ⟨_, hr', hrq⟩ ⟨q, hq, rfl⟩) id

theorem antoine_mem_stage_of_comp (u : ℕ → Fin 64) (k : ℕ) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ antoineLink) {j : ℕ} (h : antoineComp u k q ∈ antoineStage (j + k)) :
    q ∈ antoineStage j := by
  induction k generalizing q j with
  | zero => simpa [antoineComp] using h
  | succ k ih =>
    have h' : antoineComp u k (antoineMap (u k) q) ∈ antoineStage ((j + 1) + k) := by
      rw [show j + 1 + k = j + (k + 1) by omega]; exact h
    exact antoine_mem_stage_of_map hq (ih (antoineMap_mem _ hq) h')

theorem antoine_mem_necklace_of_comp (u : ℕ → Fin 64) (k : ℕ) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ antoineLink) (h : antoineComp u k q ∈ antoineNecklaceR3) : q ∈ antoineNecklaceR3 :=
  mem_iInter.2 fun j => antoine_mem_stage_of_comp u k hq (mem_iInter.1 h (j + k))

theorem antoineNecklaceR3_subset_stage (n : ℕ) : antoineNecklaceR3 ⊆ antoineStage n :=
  iInter_subset _ n

theorem antoine_mem_stage_one {p : ℝ × ℝ × ℝ} (h : p ∈ antoineStage 1) :
    ∃ i : Fin 64, ∃ q ∈ antoineLink, antoineMap i q = p := by
  obtain ⟨w, q, hq, e⟩ := mem_iUnion.1 h
  exact ⟨w 0, q, hq, e⟩

theorem antoineZ_zero : antoineZ 0 = (-560, -560) := by decide
theorem antoineT_zero : antoineT 0 = 0 := by decide
theorem antoineZ_one : antoineZ 1 = (-490, -560) := by decide
theorem antoineT_one : antoineT 1 = 1 := by decide

/-- The fixed point of `g₀`, a point of the necklace. -/
def antoineP0 : ℝ × ℝ × ℝ := (-(70 / 73), -(70 / 73), 0)

theorem antoineMap_zero_p0 : antoineMap 0 antoineP0 = antoineP0 := by
  simp only [antoineMap, antoineZ_zero, antoineT_zero, antoinePerm, antoineP0]
  ext <;> push_cast <;> ring

theorem antoineP0_mem : antoineP0 ∈ antoineLink := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [antoineP0] <;> norm_num

theorem antoineComp_zero_p0 (k : ℕ) : antoineComp (fun _ => 0) k antoineP0 = antoineP0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show antoineComp _ k (antoineMap 0 antoineP0) = _
    rw [antoineMap_zero_p0, ih]

theorem antoineP0_mem_comp (k : ℕ) : antoineP0 ∈ antoineComp (fun _ => 0) k '' antoineLink :=
  ⟨_, antoineP0_mem, antoineComp_zero_p0 k⟩

theorem antoineP0_mem_necklace : antoineP0 ∈ antoineNecklaceR3 :=
  mem_iInter.2 fun k => mem_iUnion.2 ⟨_, antoineP0_mem_comp k⟩


theorem antoine_sep_p0 : ∀ i : Fin 64, i ≠ 0 →
    73 * antoineEx (antoineT i) < |-44800 - 73 * (antoineZ i).1| ∨
      73 * antoineEy (antoineT i) < |-44800 - 73 * (antoineZ i).2| := by decide

theorem antoine_sep_mer : ∀ i : Fin 64, i ≠ 1 →
    antoineEx (antoineT i) < |-490 - (antoineZ i).1| ∨
      antoineEy (antoineT i) + 12 < |-560 - (antoineZ i).2| := by decide

theorem antoineEz_le (t : Fin 3) : antoineEz t ≤ 56 := by fin_cases t <;> decide

/-- Points of the link above the plane `z = 56/640` are off the first stage. -/
theorem antoine_not_mem_stage_one_of_z {p : ℝ × ℝ × ℝ} (hp : 56 / 640 < |p.2.2|) :
    p ∉ antoineStage 1 := by
  intro h
  obtain ⟨i, q, hq, rfl⟩ := antoine_mem_stage_one h
  have := (antoineMap_bounds i hq).2.2
  linarith

/-- The vertical segment above `p₀`. -/
def antoineVert (z : ℝ) : ℝ × ℝ × ℝ := (-(70 / 73), -(70 / 73), z)

theorem antoineVert_zero : antoineVert 0 = antoineP0 := rfl

theorem antoineVert_mem {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 8) : antoineVert z ∈ antoineLink := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [antoineVert, abs_neg]
  · rw [abs_of_nonneg h0]; exact h1
  · rw [max_self, abs_of_pos (by norm_num : (0:ℝ) < 70 / 73)]; norm_num
  · rw [max_self, abs_of_pos (by norm_num : (0:ℝ) < 70 / 73)]; norm_num

theorem antoineVert_not_mem_stage_one {z : ℝ} (hz : 7 / 640 < z) : antoineVert z ∉ antoineStage 1 := by
  intro h
  obtain ⟨i, q, hq, hiq⟩ := antoine_mem_stage_one h
  have hb := antoineMap_bounds i hq
  rw [hiq] at hb
  by_cases hi : i = 0
  · subst hi
    have := antoineMap_bounds_z 0 hq
    rw [hiq, antoineT_zero] at this
    simp only [antoineVert, antoineEz] at this
    rw [abs_of_pos (by linarith)] at this
    push_cast at this; linarith
  · simp only [antoineVert] at hb
    rcases antoine_sep_p0 i hi with h | h
    · have e : (-(70 / 73 : ℝ)) - ((antoineZ i).1 : ℝ) / 640 =
          ((-44800 - 73 * (antoineZ i).1 : ℤ) : ℝ) / 46720 := by push_cast; ring
      have h' := (Int.cast_lt (R := ℝ)).2 h
      have hb1 := hb.1
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 46720), div_le_div_iff₀ (by norm_num)
        (by norm_num)] at hb1
      push_cast at h' hb1
      linarith
    · have e : (-(70 / 73 : ℝ)) - ((antoineZ i).2 : ℝ) / 640 =
          ((-44800 - 73 * (antoineZ i).2 : ℤ) : ℝ) / 46720 := by push_cast; ring
      have h' := (Int.cast_lt (R := ℝ)).2 h
      have hb1 := hb.2.1
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 46720), div_le_div_iff₀ (by norm_num)
        (by norm_num)] at hb1
      push_cast at h' hb1
      linarith

theorem antoineMap_zero_vert (z : ℝ) : antoineMap 0 (antoineVert z) = antoineVert (7 / 80 * z) := by
  simp only [antoineMap, antoineZ_zero, antoineT_zero, antoinePerm, antoineVert]
  ext <;> push_cast <;> ring

theorem antoineStage_antitone {n m : ℕ} (h : n ≤ m) : antoineStage m ⊆ antoineStage n := by
  induction m, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ m _ ih => exact (antoineStage_succ_subset m).trans ih

theorem antoineVert_not_mem_stage (k : ℕ) : ∀ z : ℝ, (7 / 80) ^ (k + 1) / 8 < z → z ≤ 1 / 8 →
    antoineVert z ∉ antoineStage (k + 1) := by
  induction k with
  | zero =>
    intro z hz _
    exact antoineVert_not_mem_stage_one (by norm_num at hz; linarith)
  | succ k ih =>
    intro z hz hz1
    by_cases hbig : 7 / 640 < z
    · exact fun h => antoineVert_not_mem_stage_one hbig (antoineStage_antitone (by omega) h)
    · replace hbig := not_lt.1 hbig
      have hz' : (7 / 80) ^ (k + 1) / 8 < 80 / 7 * z := by
        rw [pow_succ] at hz; nlinarith
      have hz'1 : 80 / 7 * z ≤ 1 / 8 := by nlinarith
      have hpos : 0 ≤ 80 / 7 * z := le_trans (by positivity) hz'.le
      intro h
      have e : antoineVert z = antoineMap 0 (antoineVert (80 / 7 * z)) := by
        rw [antoineMap_zero_vert]; congr 1; ring
      rw [e] at h
      exact ih _ hz' hz'1 (antoine_mem_stage_of_map (antoineVert_mem hpos hz'1) h)

theorem antoineVert_not_mem_necklace {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1 / 8) :
    antoineVert z ∉ antoineNecklaceR3 := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < 8 * z by positivity)
    (show (7 / 80 : ℝ) < 1 by norm_num)
  refine fun h => antoineVert_not_mem_stage k z ?_ h1 (antoineNecklaceR3_subset_stage _ h)
  have : (7 / 80 : ℝ) ^ (k + 1) ≤ (7 / 80) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
  linarith

/-- The base point of the meridian of the link `L`. -/
def antoineMerPt : ℝ × ℝ × ℝ := (0, 7 / 8 + 3 / 14, 0)

/-- The meridian of the link `L`: the circle of radius `3/14` around the point `(0, 7/8, 0)` of
the core square, in the plane `x = 0` (it links the core of `L` once). -/
def antoineMeridian : Path antoineMerPt antoineMerPt where
  toFun t := (0, 7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t), 3 / 14 * Real.sin (2 * Real.pi * t))
  continuous_toFun := by fun_prop
  source' := by simp [antoineMerPt]
  target' := by simp [antoineMerPt]

theorem antoineMeridian_apply (t : unitInterval) : antoineMeridian t =
    (0, 7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t), 3 / 14 * Real.sin (2 * Real.pi * t)) := rfl

/-- The meridian misses the link. -/
theorem antoineMeridian_not_mem (t : unitInterval) : antoineMeridian t ∉ antoineLink := by
  rintro ⟨hz, hm, hm'⟩
  rw [antoineMeridian_apply] at hz hm hm'
  simp only [abs_zero] at hm hm'
  set c := Real.cos (2 * Real.pi * t)
  set s := Real.sin (2 * Real.pi * t)
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc1 : -1 ≤ c := Real.neg_one_le_cos _
  have hpos : 0 ≤ 7 / 8 + 3 / 14 * c := by linarith
  rw [max_eq_right (abs_nonneg _), abs_of_nonneg hpos] at hm hm'
  rw [abs_le] at hz
  nlinarith

/-- The meridian of the first link `g₁(L)`, inside `L`. -/
def antoineMer1 : Path (antoineMap 1 antoineMerPt) (antoineMap 1 antoineMerPt) :=
  antoineMeridian.map (continuous_antoineMap 1)

theorem antoineMer1_apply (t : unitInterval) : antoineMer1 t =
    (-(490 / 640), -(560 / 640) + 7 / 80 * (3 / 14 * Real.sin (2 * Real.pi * t)),
      7 / 80 * (7 / 8 + 3 / 14 * Real.cos (2 * Real.pi * t))) := by
  show antoineMap 1 (antoineMeridian t) = _
  simp only [antoineMeridian_apply, antoineMap, antoineZ_one, antoineT_one, antoinePerm]
  ext <;> push_cast <;> ring

theorem antoineMer1_mem (t : unitInterval) : antoineMer1 t ∈ antoineLink := by
  rw [antoineMer1_apply]
  have hs1 := Real.sin_le_one (2 * Real.pi * t)
  have hs2 := Real.neg_one_le_sin (2 * Real.pi * t)
  have hc1 := Real.cos_le_one (2 * Real.pi * t)
  have hc2 := Real.neg_one_le_cos (2 * Real.pi * t)
  refine ⟨?_, ?_, ?_⟩ <;> dsimp only
  · rw [abs_le]; constructor <;> nlinarith
  · rw [max_le_iff, abs_le, abs_le]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · exact le_max_of_le_right (by rw [abs_of_neg (by nlinarith)]; nlinarith)

theorem antoineMer1_not_mem_stage_one (t : unitInterval) : antoineMer1 t ∉ antoineStage 1 := by
  intro h
  obtain ⟨i, q, hq, hiq⟩ := antoine_mem_stage_one h
  by_cases hi : i = 1
  · subst hi
    exact antoineMeridian_not_mem t (antoineMap_injective 1 hiq ▸ hq)
  · have hb := antoineMap_bounds i hq
    rw [hiq, antoineMer1_apply] at hb
    have hs1 := Real.sin_le_one (2 * Real.pi * t)
    have hs2 := Real.neg_one_le_sin (2 * Real.pi * t)
    obtain ⟨hb1, hb2, -⟩ := hb
    dsimp only at hb1 hb2
    rcases antoine_sep_mer i hi with h | h
    · have h' := (Int.cast_lt (R := ℝ)).2 h
      push_cast at h'
      have e : -(490 / 640 : ℝ) - ((antoineZ i).1 : ℝ) / 640 = (-490 - ((antoineZ i).1 : ℝ)) / 640 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 640), div_le_div_iff_of_pos_right (by norm_num)] at hb1
      linarith
    · have h' := (Int.cast_lt (R := ℝ)).2 h
      push_cast at h'
      have e : -(560 / 640 : ℝ) + 7 / 80 * (3 / 14 * Real.sin (2 * Real.pi * t)) -
          ((antoineZ i).2 : ℝ) / 640 = ((-560 - ((antoineZ i).2 : ℝ)) + 12 * Real.sin (2 * Real.pi * t)) / 640 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 640), div_le_div_iff_of_pos_right (by norm_num)] at hb2
      have := abs_sub_abs_le_abs_sub (-560 - ((antoineZ i).2 : ℝ)) (-(12 * Real.sin (2 * Real.pi * t)))
      rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 12)] at this
      have hsa : |Real.sin (2 * Real.pi * t)| ≤ 1 := Real.abs_sin_le_one _
      linarith

/-- A straight segment of `ℝ³`. -/
def antoineSeg (a b : ℝ × ℝ × ℝ) : Path a b where
  toFun t := a + (t : ℝ) • (b - a)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem antoineSeg_apply (a b : ℝ × ℝ × ℝ) (t : unitInterval) : antoineSeg a b t =
    (a.1 + t * (b.1 - a.1), a.2.1 + t * (b.2.1 - a.2.1), a.2.2 + t * (b.2.2 - a.2.2)) := by
  simp only [antoineSeg, Path.coe_mk_mk]
  ext <;> simp

/-- The vertical segment from `p₀` up to the top face of `L`. -/
def antoineUp : Path antoineP0 (antoineVert (1 / 8)) where
  toFun t := antoineVert ((t : ℝ) / 8)
  continuous_toFun := by unfold antoineVert; fun_prop
  source' := by simp [antoineVert, antoineP0]
  target' := by simp [antoineVert]

theorem antoineUp_apply (t : unitInterval) : antoineUp t = antoineVert ((t : ℝ) / 8) := rfl

/-- The segment from the top of `antoineUp` to the base point of the meridian of `g₁(L)`, at
heights `> 56/640`, above the first stage. -/
def antoineAcross : Path (antoineVert (1 / 8)) (antoineMap 1 antoineMerPt) :=
  antoineSeg _ _

theorem antoineMap_one_merPt :
    antoineMap 1 antoineMerPt = (-(49 / 64), -(7 / 8), 61 / 640) := by
  simp only [antoineMap, antoineZ_one, antoineT_one, antoinePerm, antoineMerPt]
  ext <;> push_cast <;> ring

theorem antoineAcross_apply (t : unitInterval) : antoineAcross t =
    (-(70 / 73) + (t : ℝ) * (-(49 / 64) + 70 / 73), -(70 / 73) + (t : ℝ) * (-(7 / 8) + 70 / 73),
      1 / 8 + (t : ℝ) * (61 / 640 - 1 / 8)) := by
  rw [antoineAcross, antoineSeg_apply, antoineMap_one_merPt]
  simp only [antoineVert]
  ext <;> ring

theorem antoineAcross_mem (t : unitInterval) :
    antoineAcross t ∈ antoineLink ∧ antoineAcross t ∉ antoineStage 1 := by
  rw [antoineAcross_apply]
  have h0 := t.2.1
  have h1 := t.2.2
  refine ⟨⟨?_, ?_, ?_⟩, antoine_not_mem_stage_one_of_z ?_⟩ <;> dsimp only
  · rw [abs_le]; constructor <;> nlinarith
  · rw [max_le_iff, abs_le, abs_le]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · exact le_max_of_le_right (by rw [abs_of_neg (by nlinarith)]; nlinarith)
  · rw [abs_of_pos (by nlinarith)]; nlinarith

/-- From `p₀` to the base point of the meridian of `g₁(L)`. -/
def antoineTail : Path antoineP0 (antoineMap 1 antoineMerPt) := antoineUp.trans antoineAcross

/-- The based loop at `p₀`: up, across, the meridian of `g₁(L)`, back. -/
def antoineLoop0 : Path antoineP0 antoineP0 := (antoineTail.trans antoineMer1).trans antoineTail.symm

theorem antoine_memOmega_trans {X : Type*} [TopologicalSpace X] {U : Set X} {x y z : X}
    {p : Path x y} {q : Path y z} (hp : MemOmega U p) (hq : MemOmega U q) (hy : y ∈ U) :
    MemOmega U (p.trans q) := by
  intro t h0 h1
  rw [Path.trans_apply]
  split_ifs with h
  · rcases eq_or_lt_of_le h with h' | h'
    · convert hy using 1
      convert p.target using 2
      ext; simp [h']
    · exact hp _ (show (0:ℝ) < 2 * (t:ℝ) by linarith) (show 2 * (t:ℝ) < 1 by linarith)
  · push Not at h
    exact hq _ (show (0:ℝ) < 2 * (t:ℝ) - 1 by linarith) (show 2 * (t:ℝ) - 1 < 1 by linarith)

theorem antoine_memOmega_symm {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    {p : Path x y} (hp : MemOmega U p) : MemOmega U p.symm := fun t h0 h1 => by
  rw [Path.symm_apply]
  exact hp _ (by rw [unitInterval.coe_symm_eq]; linarith) (by rw [unitInterval.coe_symm_eq]; linarith)

theorem antoine_memOmega_of_forall {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    {p : Path x y} (hp : ∀ t, p t ∈ U) : MemOmega U p := fun t _ _ => hp t

/-- Points of `L` off the necklace, and `p₀`. -/
def antoineGood : Set (ℝ × ℝ × ℝ) := {q | q ∈ antoineLink ∧ q ∉ antoineNecklaceR3}

theorem antoineTail_mem (t : unitInterval) :
    antoineTail t ∈ antoineLink ∧ (antoineTail t = antoineP0 ∨ antoineTail t ∉ antoineNecklaceR3) := by
  have hU : ∀ s, antoineUp s ∈ antoineLink ∧ (antoineUp s = antoineP0 ∨
      antoineUp s ∉ antoineNecklaceR3) := fun s => by
    rw [antoineUp_apply]
    have h0 := s.2.1
    have h1 := s.2.2
    refine ⟨antoineVert_mem (by positivity) (by linarith), ?_⟩
    rcases eq_or_lt_of_le h0 with h | h
    · left; rw [← h]; simp [antoineVert, antoineP0]
    · right; exact antoineVert_not_mem_necklace (by positivity) (by linarith)
  have hA : ∀ s, antoineAcross s ∈ antoineLink ∧ (antoineAcross s = antoineP0 ∨
      antoineAcross s ∉ antoineNecklaceR3) := fun s =>
    ⟨(antoineAcross_mem s).1, Or.inr fun h => (antoineAcross_mem s).2
      (antoineNecklaceR3_subset_stage 1 h)⟩
  exact path_trans_mem (W := {q | q ∈ antoineLink ∧ (q = antoineP0 ∨ q ∉ antoineNecklaceR3)})
    hU hA t

theorem antoineTail_memOmega : MemOmega antoineGood antoineTail := by
  refine antoine_memOmega_trans (fun s h0 _ => ?_) (antoine_memOmega_of_forall fun s =>
    ⟨(antoineAcross_mem s).1, fun h => (antoineAcross_mem s).2
      (antoineNecklaceR3_subset_stage 1 h)⟩) ⟨antoineVert_mem (by norm_num) le_rfl,
        antoineVert_not_mem_necklace (by norm_num) le_rfl⟩
  rw [antoineUp_apply]
  exact ⟨antoineVert_mem (by positivity) (by linarith [s.2.2]),
    antoineVert_not_mem_necklace (by positivity) (by linarith [s.2.2])⟩

theorem antoineMer1_good (t : unitInterval) : antoineMer1 t ∈ antoineGood :=
  ⟨antoineMer1_mem t, fun h => antoineMer1_not_mem_stage_one t (antoineNecklaceR3_subset_stage 1 h)⟩

theorem antoineLoop0_memOmega : MemOmega antoineGood antoineLoop0 :=
  antoine_memOmega_trans (antoine_memOmega_trans antoineTail_memOmega
    (antoine_memOmega_of_forall antoineMer1_good) (by simpa using antoineMer1_good 0))
    (antoine_memOmega_symm antoineTail_memOmega) (by simpa using antoineMer1_good 0)

open Path.Homotopic.Quotient in
/-- A conjugate `T M T⁻¹` of a loop `M` null-homotopic in `U` makes `M` null-homotopic in `U`. -/
theorem antoine_homotopicIn_conj {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    {T : Path x y} {M : Path y y} (hT : ∀ t, T t ∈ U) (hM : ∀ t, M t ∈ U)
    (h : HomotopicIn U ((T.trans M).trans T.symm) (Path.refl x)) :
    HomotopicIn U M (Path.refl y) := by
  have hx : x ∈ U := T.source ▸ hT 0
  have hy : y ∈ U := T.target ▸ hT 1
  have hRx : ∀ t, (Path.refl x) t ∈ U := fun _ => hx
  have hRy : ∀ t, (Path.refl y) t ∈ U := fun _ => hy
  rw [homotopicIn_iff_mk (path_trans_mem (path_trans_mem hT hM) (path_symm_mem hT)) hRx,
    pathToSub_trans _ _ (path_trans_mem hT hM) (path_symm_mem hT), pathToSub_trans _ _ hT hM,
    pathToSub_symm _ hT, mk_trans, mk_trans, mk_symm] at h
  rw [homotopicIn_iff_mk hM hRy]
  have e1 : pathToSub (Path.refl x) hRx = Path.refl (⟨x, hx⟩ : U) := by ext; rfl
  have e2 : pathToSub (Path.refl y) hRy = Path.refl (⟨y, hy⟩ : U) := by ext; rfl
  rw [e1, mk_refl] at h
  rw [e2, mk_refl]
  have h2 := congrArg (fun q => trans (symm (mk (pathToSub T hT))) (trans q (mk (pathToSub T hT)))) h
  simp only [trans_assoc, symm_trans, trans_refl, refl_trans] at h2
  rw [← trans_assoc, symm_trans, refl_trans] at h2
  exact h2

/-- Transport of null-homotopy along a pointwise equality of loops. -/
theorem antoine_homotopicIn_refl_congr {X : Type*} [TopologicalSpace X] {U : Set X} {x y : X}
    {P : Path x x} {Q : Path y y} (hxy : x = y) (hPQ : ∀ t, P t = Q t)
    (h : HomotopicIn U P (Path.refl x)) : HomotopicIn U Q (Path.refl y) := by
  subst hxy
  obtain rfl : P = Q := Path.ext (funext hPQ)
  exact h

/-- The stage `n` is a FINITE union of links, hence compact. -/
theorem antoineStage_isCompact (n : ℕ) : IsCompact (antoineStage n) := by
  have e : antoineStage n = ⋃ u : Fin n → Fin 64,
      antoineComp (fun j => if h : j < n then u ⟨j, h⟩ else 0) n '' antoineLink := by
    apply Subset.antisymm
    · refine iUnion_subset fun w => ?_
      refine subset_iUnion_of_subset (fun j => w j) ?_
      rw [antoineComp_congr (w' := fun j => if h : j < n then w j else 0) fun k hk => by
        simp [hk]]
    · exact iUnion_subset fun u => subset_iUnion_of_subset _ subset_rfl
  rw [e]
  exact isCompact_iUnion fun u => antoineLink_isCompact.image (continuous_antoineComp _ n)

/-- **The compactness reduction.** A null-homotopy in the complement of `C ∩ L` (`L` closed) has
compact image, which misses `C_m ∩ L` for some (every large) finite stage `m`. -/
theorem antoine_homotopicIn_stage {L : Set (ℝ × ℝ × ℝ)} (hL : IsClosed L) {x : Sphere3}
    {γ : Path x x} (h : HomotopicIn (antoineStereo '' (antoineNecklaceR3 ∩ L))ᶜ γ (Path.refl x))
    (n : ℕ) : ∃ m, n ≤ m ∧
      HomotopicIn (antoineStereo '' (antoineStage m ∩ L))ᶜ γ (Path.refl x) := by
  obtain ⟨F, hF⟩ := h
  set A := range F
  have hA : IsCompact A := isCompact_range F.continuous
  set t : ℕ → Set Sphere3 := fun i => A ∩ antoineStereo '' (antoineStage (i + n) ∩ L)
  have hK : ∀ i, IsClosed (antoineStereo '' (antoineStage (i + n) ∩ L)) := fun i =>
    (((antoineStage_isCompact _).inter_right hL).image continuous_antoineStereo).isClosed
  have hcl : ∀ i, IsClosed (t i) := fun i => hA.isClosed.inter (hK i)
  have hdec : ∀ i, t (i + 1) ⊆ t i := fun i => inter_subset_inter_right _ (image_mono
    (inter_subset_inter_left _ (by
      rw [show i + 1 + n = i + n + 1 by omega]; exact antoineStage_succ_subset _)))
  by_cases hne : ∀ i, (t i).Nonempty
  · exfalso
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec
      hne (hA.inter_right (hK 0)) hcl
    have hy' : ∀ i, y ∈ t i := mem_iInter.1 hy
    obtain ⟨z, hz⟩ := (hy' 0).1
    obtain ⟨p, hp, hpy⟩ := (hy' 0).2
    have hpC : p ∈ antoineNecklaceR3 := mem_iInter.2 fun j => by
      obtain ⟨q, hq, hqy⟩ := (hy' j).2
      have : q = p := antoineStereo_injective (hqy.trans hpy.symm)
      exact antoineStage_antitone (Nat.le_add_right j n) (this ▸ hq.1)
    exact hF z (hz ▸ hpy ▸ ⟨p, ⟨hpC, hp.2⟩, rfl⟩)
  · push Not at hne
    obtain ⟨i, hi⟩ := hne
    refine ⟨i + n, Nat.le_add_left n i, F, fun z hz => ?_⟩
    exact (Set.eq_empty_iff_forall_notMem.1 hi) (F z) ⟨mem_range_self z, hz⟩

/-- **The residual of Antoine's theorem**, exactly: for `n ≤ m`, the meridian of a link `L` of
generation `n` (the image of `GX.antoineMeridian` under `g_{v₀} ∘ ⋯ ∘ g_{v_{n-1}}`, carried into
`S³`) is not null-homotopic in the complement in `S³` of the links of generation `m` inside `L`. -/
def AntoineMeridianEssential : Prop :=
  ∀ (v : ℕ → Fin 64) (n m : ℕ), n ≤ m →
    ¬ HomotopicIn (antoineStereo '' (antoineStage m ∩ antoineComp v n '' antoineLink))ᶜ
      ((antoineMeridian.map (continuous_antoineComp v n)).map continuous_antoineStereo)
      (Path.refl _)

/-- The word `0ᵏ 1 0 0 ⋯`: its generation-`(k+1)` link is `g₀ᵏ(g₁(L))`. -/
def antoineWord (k : ℕ) : ℕ → Fin 64 := fun j => if j = k then 1 else 0

theorem antoineComp_word (k : ℕ) :
    antoineComp (antoineWord k) (k + 1) = antoineComp (fun _ => 0) k ∘ antoineMap 1 := by
  show antoineComp (antoineWord k) k ∘ antoineMap (antoineWord k k) = _
  rw [antoineComp_congr (w' := fun _ => 0) fun j hj => by simp [antoineWord, hj.ne]]
  simp [antoineWord]

theorem antoineP0_not_mem_word_link (k : ℕ) :
    antoineP0 ∉ antoineComp (antoineWord k) (k + 1) '' antoineLink := by
  rintro ⟨q, hq, e⟩
  rw [antoineComp_word] at e
  have := antoineComp_injective _ k (e.trans (antoineComp_zero_p0 k).symm)
  exact Set.disjoint_left.1 (antoineMap_disjoint (show (1 : Fin 64) ≠ 0 by decide)) ⟨q, hq, rfl⟩
    ⟨antoineP0, antoineP0_mem, antoineMap_zero_p0.trans this.symm⟩

/-- **Antoine's essential loops, from the residual alone.** At the point `x₀ = antoineStereo p₀`
of the necklace (`p₀` the fixed point of `g₀`), in every neighbourhood `V`: the closed piece
`K = C ∩ L`, `L = g₀ᵏ(g₁(L))` (link selection by `GX.antoineComp_diam`), misses `x₀`, and the
loop `g₀ᵏ(up · across · meridian · across⁻¹ · up⁻¹)` (accessibility: the vertical segment above
`p₀` meets the necklace only at `p₀`, `GX.antoineVert_not_mem_necklace`) lies in `V` off the
necklace and is essential in `S³ ∖ K` (by conjugation, the compactness reduction
`GX.antoine_homotopicIn_stage` and the residual `GX.AntoineMeridianEssential`). -/
theorem antoine_essential_loops (hres : AntoineMeridianEssential) :
    ∀ V ∈ 𝓝 (antoineStereo antoineP0), ∃ K : Set Sphere3, K ⊆ antoineNecklace ∧ IsClosed K ∧
      antoineStereo antoineP0 ∉ K ∧ ∃ γ : Path (antoineStereo antoineP0) (antoineStereo antoineP0),
        MemOmega (V ∩ antoineNecklaceᶜ) γ ∧ ¬ HomotopicIn Kᶜ γ (Path.refl _) := by
  intro V hV
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.1 (continuous_antoineStereo.continuousAt.preimage_mem_nhds hV)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
    (show (7 / 80 : ℝ) < 1 by norm_num)
  set f := antoineComp (fun _ => (0 : Fin 64)) k with hfdef
  set L := antoineComp (antoineWord k) (k + 1) '' antoineLink with hLdef
  have hfV : ∀ q ∈ antoineLink, antoineStereo (f q) ∈ V := fun q hq => hball (by
    rw [Metric.mem_ball]
    have := antoineComp_diam ⟨q, hq, rfl⟩ (antoineP0_mem_comp k)
    linarith)
  have hLc : IsClosed L := (antoineLink_isCompact.image (continuous_antoineComp _ _)).isClosed
  set K := antoineStereo '' (antoineNecklaceR3 ∩ L) with hKdef
  have hKmem : ∀ q ∈ antoineLink, (q = antoineP0 ∨ q ∉ antoineNecklaceR3) →
      antoineStereo (f q) ∉ K := by
    rintro q hq hq' ⟨p, ⟨hpC, hpL⟩, e⟩
    have hp : p = f q := antoineStereo_injective e
    rcases hq' with rfl | hq'
    · have e' : p = antoineP0 := hp.trans (antoineComp_zero_p0 k)
      exact antoineP0_not_mem_word_link k (e' ▸ hpL)
    · exact hq' (antoine_mem_necklace_of_comp _ k hq (hp ▸ hpC))
  refine ⟨K, image_mono inter_subset_left,
    ((isCompact_antoineNecklaceR3.inter_right hLc).image continuous_antoineStereo).isClosed,
    fun h => hKmem _ antoineP0_mem (Or.inl rfl) (by
      have e : f antoineP0 = antoineP0 := antoineComp_zero_p0 k
      rwa [e]), ?_⟩
  have hF : Continuous (antoineStereo ∘ f) :=
    continuous_antoineStereo.comp (continuous_antoineComp _ k)
  have hFp0 : (antoineStereo ∘ f) antoineP0 = antoineStereo antoineP0 := by
    simp [f, antoineComp_zero_p0]
  refine ⟨(antoineLoop0.map hF).cast hFp0.symm hFp0.symm, fun t h0 h1 => ?_, fun hhom => ?_⟩
  · have hg := antoineLoop0_memOmega t h0 h1
    refine ⟨hfV _ hg.1, ?_⟩
    rintro ⟨p, hp, e⟩
    have : p = f (antoineLoop0 t) := antoineStereo_injective e
    exact hg.2 (antoine_mem_necklace_of_comp _ k hg.1 (this ▸ hp))
  have h1 : HomotopicIn Kᶜ (antoineLoop0.map hF) (Path.refl _) :=
    antoine_homotopicIn_refl_congr hFp0.symm (fun _ => rfl) hhom
  rw [antoineLoop0, Path.map_trans, Path.map_trans, ← Path.map_symm] at h1
  have h2 := antoine_homotopicIn_conj (fun t => hKmem _ (antoineTail_mem t).1 (antoineTail_mem t).2)
    (fun t => hKmem _ (antoineMer1_good t).1 (Or.inr (antoineMer1_good t).2)) h1
  obtain ⟨m, hm, h3⟩ := antoine_homotopicIn_stage hLc h2 (k + 1)
  refine hres (antoineWord k) (k + 1) m hm (antoine_homotopicIn_refl_congr ?_ (fun t => ?_) h3)
  · simp [antoineComp_word, f]
  · simp only [Path.map_coe, Function.comp_apply, antoineComp_word, antoineMer1]
    rfl

section HomeoInvariance

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem antoine_almostTrivial_congr {U : Set X} {x y : X} {P : Path x x} {Q : Path y y}
    (hxy : x = y) (hPQ : ∀ t, P t = Q t) (h : AlmostTrivial U P) : AlmostTrivial U Q := by
  subst hxy
  obtain rfl : P = Q := Path.ext (funext hPQ)
  exact h

/-- Almost triviality is carried by a homeomorphism. -/
theorem AlmostTrivial.map_homeomorph (h : X ≃ₜ Y) {U : Set X} {x : X} {γ : Path x x}
    (hγ : AlmostTrivial U γ) : AlmostTrivial (h '' U) (γ.map h.continuous) := by
  obtain ⟨hm, hW⟩ := hγ
  refine ⟨fun t h0 h1 => ⟨_, hm t h0 h1, rfl⟩, fun W hW' => ?_⟩
  obtain ⟨γ', hγ', F, hF⟩ := hW _ (h.continuous.continuousAt.preimage_mem_nhds hW')
  refine ⟨γ'.map h.continuous, fun t h0 h1 => ⟨(hγ' t h0 h1).1, _, (hγ' t h0 h1).2, rfl⟩,
    F.map ⟨h, h.continuous⟩, fun s t h0 h1 => ⟨_, hF s t h0 h1, rfl⟩⟩

/-- Semi-local simple connectedness (homotopy form) is carried by a homeomorphism. -/
theorem IsSLSCIn.map_homeomorph (h : X ≃ₜ Y) {U : Set X} (hU : IsSLSCIn U) :
    IsSLSCIn (h '' U) := by
  refine ⟨h.surjective.denseRange.dense_image h.continuous hU.1, fun y => ?_⟩
  obtain ⟨V, hV, hVc, hxV, hloop⟩ := hU.2 (h.symm y)
  refine ⟨h '' V, h.isOpenMap V hV, hVc.image _ h.continuous.continuousOn,
    ⟨_, hxV, h.apply_symm_apply y⟩, fun γ hγ => ?_⟩
  have hδ : MemOmega (V ∩ U) (γ.map h.symm.continuous) := fun t h0 h1 => by
    obtain ⟨⟨a, ha, ea⟩, ⟨b, hb, eb⟩⟩ := hγ t h0 h1
    refine ⟨?_, ?_⟩
    · show h.symm (γ t) ∈ V
      rw [← ea, h.symm_apply_apply]; exact ha
    · show h.symm (γ t) ∈ U
      rw [← eb, h.symm_apply_apply]; exact hb
  exact antoine_almostTrivial_congr (h.apply_symm_apply y)
    (fun t => h.apply_symm_apply (γ t)) ((hloop _ hδ).map_homeomorph h)

end HomeoInvariance

end GX
end
