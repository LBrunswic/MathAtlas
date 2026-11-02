import GXScaffold.Branched.GaloisExamples

open Set Function Topology unitInterval

namespace GX

theorem antoine_notMem_link_of_box (i : Fin 64) {p : ℝ × ℝ × ℝ}
    (h : (antoineEx (antoineT i) : ℝ) / 640 < |p.1 - (antoineZ i).1 / 640| ∨
      (antoineEy (antoineT i) : ℝ) / 640 < |p.2.1 - (antoineZ i).2 / 640|) :
    p ∉ antoineMap i '' antoineLink := by
  rintro ⟨q, hq, rfl⟩
  obtain ⟨b1, b2, -⟩ := antoineMap_bounds i hq
  rcases h with h | h <;> linarith

theorem antoine_notMem_link_hole0 (i : Fin 64) (hT : antoineT i = 0) {p : ℝ × ℝ × ℝ}
    (h1 : |p.1 - (antoineZ i).1 / 640| < 42 / 640) (h2 : |p.2.1 - (antoineZ i).2 / 640| < 42 / 640) :
    p ∉ antoineMap i '' antoineLink := by
  rintro ⟨q, ⟨-, -, hq⟩, rfl⟩
  simp only [antoineMap, hT, antoinePerm, add_sub_cancel_left, abs_mul,
    abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] at h1 h2
  have : max |q.1| |q.2.1| < 3 / 4 := max_lt (by linarith) (by linarith)
  linarith

theorem antoine_notMem_link_hole2 (i : Fin 64) (hT : antoineT i = 2) {p : ℝ × ℝ × ℝ}
    (h1 : |p.2.2| < 42 / 640) (h2 : |p.2.1 - (antoineZ i).2 / 640| < 42 / 640) :
    p ∉ antoineMap i '' antoineLink := by
  rintro ⟨q, ⟨-, -, hq⟩, rfl⟩
  simp only [antoineMap, hT, antoinePerm, add_sub_cancel_left, abs_mul,
    abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] at h1 h2
  have : max |q.1| |q.2.1| < 3 / 4 := max_lt (by linarith) (by linarith)
  linarith

theorem antoine_mem_stage_one_bounds {p : ℝ × ℝ × ℝ} (h : p ∈ antoineStage 1) :
    |p.2.1| ≤ 616 / 640 := by
  obtain ⟨i, q, hq, rfl⟩ := antoine_mem_stage_one h
  have hm := antoineMap_mem i hq
  have := (le_max_right _ _).trans hm.2.1
  have hb := (antoineMap_bounds i hq).2.1
  have e2 : (antoineEy (antoineT i) : ℝ) ≤ 56 := by
    rcases antoineT_cases i with h | h | h <;> simp [h, antoineEy]; norm_num
  have hc : |((antoineZ i).2 : ℝ)| ≤ 560 := by
    rcases antoine_centre_mem i with ⟨-, c2⟩ | ⟨c1, -⟩
    · exact_mod_cast c2
    · exact_mod_cast c1.le
  rw [abs_le] at hb hc ⊢
  constructor <;> linarith

theorem antoine_notMem_stage_one_of (p : ℝ × ℝ × ℝ) (h : ∀ i : Fin 64, p ∉ antoineMap i '' antoineLink) :
    p ∉ antoineStage 1 := by
  intro hp
  obtain ⟨i, q, hq, rfl⟩ := antoine_mem_stage_one hp
  exact h i ⟨q, hq, rfl⟩

set_option maxRecDepth 100000 in
theorem antoine_joined_vert_cert : ∀ j i : Fin 64, antoineT j ≠ 1 →
    (antoineEx (antoineT i) < |(antoineZ j).1 + 35 - (antoineZ i).1| ∨
      antoineEy (antoineT i) < |(antoineZ j).2 + 61 - (antoineZ i).2|) ∨
    (antoineT i = 0 ∧ |(antoineZ j).1 + 35 - (antoineZ i).1| < 42 ∧
      |(antoineZ j).2 + 61 - (antoineZ i).2| < 42) := by
  decide

set_option maxRecDepth 100000 in
theorem antoine_joined_shift_cert : ∀ j i : Fin 64, antoineT j ≠ 1 →
    (antoineEx (antoineT i) < (antoineZ j).1 - (antoineZ i).1 ∨
      (antoineZ j).1 + 35 - (antoineZ i).1 < -antoineEx (antoineT i) ∨
      antoineEy (antoineT i) < |(antoineZ j).2 + 61 - (antoineZ i).2|) ∨
    (antoineT i = 0 ∧ |(antoineZ j).1 - (antoineZ i).1| < 42 ∧
      |(antoineZ j).1 + 35 - (antoineZ i).1| < 42 ∧ |(antoineZ j).2 + 61 - (antoineZ i).2| < 42) ∨
    (antoineT i = 2 ∧ |(antoineZ j).2 + 61 - (antoineZ i).2| < 42) := by
  decide

/-- A segment of `ℝ³` all of whose points lie in `F` joins its ends in `F`. -/
theorem antoine_joinedIn_seg {F : Set (ℝ × ℝ × ℝ)} {a b : ℝ × ℝ × ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → a + t • (b - a) ∈ F) : JoinedIn F a b :=
  ⟨antoineSeg a b, fun t => h t t.2.1 t.2.2⟩

theorem antoine_int_abs_cast {a : ℤ} : (|(a : ℝ)|) = ((|a| : ℤ) : ℝ) := by push_cast; rfl

theorem antoine_abs_div640 (a b : ℝ) : |a / 640 - b / 640| = |a - b| / 640 := by
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 640)]

theorem antoine_vert_notMem (j : Fin 64) (hT : antoineT j ≠ 1) (z : ℝ) :
    ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, z) ∉ antoineStage 1 := by
  refine antoine_notMem_stage_one_of _ fun i => ?_
  rcases antoine_joined_vert_cert j i hT with (h | h) | ⟨hi, h1, h2⟩
  · refine antoine_notMem_link_of_box i (Or.inl ?_)
    have h' : ((antoineEx (antoineT i) : ℤ) : ℝ) < |((antoineZ j).1 : ℝ) + 35 - (antoineZ i).1| := by
      exact_mod_cast h
    show _ < |(((antoineZ j).1 : ℝ) + 35) / 640 - _|
    rw [antoine_abs_div640]; linarith
  · refine antoine_notMem_link_of_box i (Or.inr ?_)
    have h' : ((antoineEy (antoineT i) : ℤ) : ℝ) < |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| := by
      exact_mod_cast h
    show _ < |(((antoineZ j).2 : ℝ) + 61) / 640 - _|
    rw [antoine_abs_div640]; linarith
  · have h1' : |((antoineZ j).1 : ℝ) + 35 - (antoineZ i).1| < 42 := by exact_mod_cast h1
    have h2' : |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| < 42 := by exact_mod_cast h2
    refine antoine_notMem_link_hole0 i hi ?_ ?_
    · show |(((antoineZ j).1 : ℝ) + 35) / 640 - _| < _
      rw [antoine_abs_div640]; linarith
    · show |(((antoineZ j).2 : ℝ) + 61) / 640 - _| < _
      rw [antoine_abs_div640]; linarith

theorem antoine_shift_notMem (j : Fin 64) (hT : antoineT j ≠ 1) {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 35) :
    ((((antoineZ j).1 : ℝ) + d) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) ∉
      antoineStage 1 := by
  refine antoine_notMem_stage_one_of _ fun i => ?_
  have hE : (0 : ℝ) ≤ (antoineEx (antoineT i) : ℝ) := by
    rcases antoineT_cases i with h | h | h <;> simp [h, antoineEx]
  rcases antoine_joined_shift_cert j i hT with (h | h | h) | ⟨hi, h1, h1', h2⟩ | ⟨hi, h2⟩
  · refine antoine_notMem_link_of_box i (Or.inl ?_)
    have h' : ((antoineEx (antoineT i) : ℤ) : ℝ) < ((antoineZ j).1 : ℝ) - (antoineZ i).1 := by
      exact_mod_cast h
    show _ < |(((antoineZ j).1 : ℝ) + d) / 640 - _|
    rw [antoine_abs_div640, abs_of_pos (by linarith)]; linarith
  · refine antoine_notMem_link_of_box i (Or.inl ?_)
    have h' : ((antoineZ j).1 : ℝ) + 35 - (antoineZ i).1 < -((antoineEx (antoineT i) : ℤ) : ℝ) := by
      exact_mod_cast h
    show _ < |(((antoineZ j).1 : ℝ) + d) / 640 - _|
    rw [antoine_abs_div640, abs_of_neg (by linarith)]; linarith
  · refine antoine_notMem_link_of_box i (Or.inr ?_)
    have h' : ((antoineEy (antoineT i) : ℤ) : ℝ) < |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| := by
      exact_mod_cast h
    show _ < |(((antoineZ j).2 : ℝ) + 61) / 640 - _|
    rw [antoine_abs_div640]; linarith
  · have h1a : |((antoineZ j).1 : ℝ) - (antoineZ i).1| < 42 := by exact_mod_cast h1
    have h1b : |((antoineZ j).1 : ℝ) + 35 - (antoineZ i).1| < 42 := by exact_mod_cast h1'
    have h2' : |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| < 42 := by exact_mod_cast h2
    refine antoine_notMem_link_hole0 i hi ?_ ?_
    · show |(((antoineZ j).1 : ℝ) + d) / 640 - _| < _
      rw [antoine_abs_div640, div_lt_div_iff_of_pos_right (by norm_num), abs_lt]
      rw [abs_lt] at h1a h1b
      constructor <;> linarith
    · show |(((antoineZ j).2 : ℝ) + 61) / 640 - _| < _
      rw [antoine_abs_div640]; linarith
  · have h2' : |((antoineZ j).2 : ℝ) + 61 - (antoineZ i).2| < 42 := by exact_mod_cast h2
    refine antoine_notMem_link_hole2 i hi (by simp) ?_
    show |(((antoineZ j).2 : ℝ) + 61) / 640 - _| < _
    rw [antoine_abs_div640]; linarith

theorem antoineMap_merPt_of_ne (j : Fin 64) (hT : antoineT j ≠ 1) :
    antoineMap j antoineMerPt =
      (((antoineZ j).1 : ℝ) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) := by
  rcases antoineT_cases j with h | h | h
  · simp only [antoineMap, h, antoinePerm, antoineMerPt, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  · exact absurd h hT
  · simp only [antoineMap, h, antoinePerm, antoineMerPt, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

theorem antoineMap_merPt_of_eq (j : Fin 64) (hT : antoineT j = 1) :
    antoineMap j antoineMerPt =
      (((antoineZ j).1 : ℝ) / 640, ((antoineZ j).2 : ℝ) / 640, (61 / 640 : ℝ)) := by
  simp only [antoineMap, hT, antoinePerm, antoineMerPt, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

/-- `S³ ∖ C₁` joins the base point of the top meridian to the base point of the meridian of
every first-generation link (`joined` of `GX.AntoineFirstGeneration`), in `ℝ³`: up to the plane
`z = 1`, across, and down (after a shift of `35/640` along `x` for the links of types `0` and
`2`). -/
theorem antoine_joined_R3 (j : Fin 64) :
    JoinedIn (antoineStage 1)ᶜ antoineMerPt (antoineMap j antoineMerPt) := by
  have hhigh : ∀ p : ℝ × ℝ × ℝ, 56 / 640 < p.2.2 → p ∈ (antoineStage 1)ᶜ := fun p hp =>
    antoine_not_mem_stage_one_of_z (by rw [abs_of_pos (by linarith)]; exact hp)
  have h0 : JoinedIn (antoineStage 1)ᶜ antoineMerPt (0, 61 / 56, 1) := by
    refine antoine_joinedIn_seg fun t _ _ => fun hp => ?_
    have := antoine_mem_stage_one_bounds hp
    simp only [antoineMerPt, Prod.fst_add, Prod.snd_add, Prod.smul_mk, Prod.mk_sub_mk,
      smul_eq_mul] at this
    rw [abs_le] at this
    norm_num at this
  have hacross : ∀ a b : ℝ, JoinedIn (antoineStage 1)ᶜ (0, 61 / 56, 1) (a, b, 1) := fun a b =>
    antoine_joinedIn_seg fun t _ _ => hhigh _ (by
      simp only [Prod.snd_add, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul]; norm_num)
  by_cases hT : antoineT j = 1
  · rw [antoineMap_merPt_of_eq j hT]
    refine (h0.trans (hacross (((antoineZ j).1 : ℝ) / 640) (((antoineZ j).2 : ℝ) / 640))).trans
      (antoine_joinedIn_seg fun t _ ht1 => hhigh _ ?_)
    simp only [Prod.snd_add, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul]
    nlinarith
  · rw [antoineMap_merPt_of_ne j hT]
    refine ((h0.trans (hacross ((((antoineZ j).1 : ℝ) + 35) / 640)
      ((((antoineZ j).2 : ℝ) + 61) / 640))).trans
      (antoine_joinedIn_seg fun t _ _ => ?_)).trans (antoine_joinedIn_seg fun t ht0 ht1 => ?_)
      (y := ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)))
    · have e : ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (1 : ℝ)) +
          t • (((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) -
            ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (1 : ℝ))) =
          ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, 1 - t) := by
        simp only [Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
        refine ⟨by ring, by ring, by ring⟩
      rw [e]; exact antoine_vert_notMem j hT _
    · have e : ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) +
          t • ((((antoineZ j).1 : ℝ) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ)) -
            ((((antoineZ j).1 : ℝ) + 35) / 640, (((antoineZ j).2 : ℝ) + 61) / 640, (0 : ℝ))) =
          ((((antoineZ j).1 : ℝ) + 35 * (1 - t)) / 640, (((antoineZ j).2 : ℝ) + 61) / 640,
            (0 : ℝ)) := by
        simp only [Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
        refine ⟨by ring, by ring, by ring⟩
      rw [e]; exact antoine_shift_notMem j hT (by nlinarith) (by nlinarith)

/-- `joined` of `GX.AntoineFirstGeneration`, in `S³`. -/
theorem antoine_joined (j : Fin 64) :
    JoinedIn (antoineStereo '' antoineStage 1)ᶜ (antoineStereo antoineMerPt) (antoineX1 j) := by
  refine ((antoine_joined_R3 j).map continuous_antoineStereo).mono ?_
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, e⟩
  exact hp (antoineStereo_injective e ▸ hq)

end GX
