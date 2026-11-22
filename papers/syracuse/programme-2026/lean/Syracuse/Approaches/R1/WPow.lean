import Syracuse.Approaches.R1.Decide
import Syracuse.Approaches.CycleGcd

/-!
# Uniform classification of the families `w^a w'`

The simplest r = 1 families have one growing block `w` and a fixed tail `w'`. For them the
classification of `Decide.lean` holds **uniformly in `(w, w')`**, with the core
`C(w, w') = D(w) S(w') - D(w') S(w)` (`CocycleCombine.wedge`) playing the role of the resultant.
Everything rests on one identity, valid in any commutative ring (`wpow_append_identity`):

  `D(w) · S(w^a w') - S(w) · D(w^a w') = X^{a|w|} · C(w, w')`.

* **`C ≠ 0`.** Every cycle word `w^a w'` has `D(w^a w') ∣ C(w, w')`, so `|D| ≤ |C|`
  (`wpow_append_dvd`, `wpow_append_ceiling`), and only finitely many `a` give cycles
  (`wpow_append_finite`).
* **`C = 0`.** The fixed point is `S(w)/D(w)` for every member, so `w^a w'` is a cycle word iff `w`
  is (`wpow_append_const`).

`wpow_append_classification` packages the two cases. For a concrete pair, `decideR1` on the family
`⟨|w|, len w, [.grow w 1 1 0, .fixed w']⟩` returns the exact cycle set.
-/

namespace Syracuse.R1

open Syracuse Syracuse.CocycleCombine Filter

/-- The core `C(w, w')` at `(2, 3)`. -/
abbrev Cw (w w' : Word) : ℤ := wedge (2 : ℤ) 3 w w'

/-- **The identity**, in any commutative ring. -/
theorem wpow_append_identity {R : Type*} [CommRing R] (X Y : R) (w w' : Word) (a : ℕ) :
    D X Y w * S X Y (wpow w a ++ w') - S X Y w * D X Y (wpow w a ++ w') =
      X ^ (a * w.sum) * wedge X Y w w' := by
  have key : D X Y w * S X Y (wpow w a) = S X Y w * (X ^ (a * w.sum) - Y ^ (a * w.length)) := by
    rw [S_wpow, show X ^ (a * w.sum) - Y ^ (a * w.length) = D X Y (wpow w a) by
      simp [D, wpow_sum, wpow_length], D_wpow]
    ring
  rw [S_append]
  simp only [wedge, D, List.sum_append, List.length_append, wpow_sum, wpow_length, pow_add] at key ⊢
  linear_combination (Y ^ w'.length) * key

lemma wpow_append_pos {w w' : Word} (hw : w.Pos) (hw' : w'.Pos) (a : ℕ) : (wpow w a ++ w').Pos := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · exact wpow_pos hw a d h
  · exact hw' d h

/-- **Ceiling.** A cycle word `w^a w'` has `D(w^a w') ∣ C(w, w')`. -/
theorem wpow_append_dvd {w w' : Word} (hw : w.Pos) (hw' : w'.Pos) {a : ℕ}
    (hc : IsCycleWord (wpow w a ++ w')) : Dz (wpow w a ++ w') ∣ Cw w w' := by
  obtain ⟨hne, hdvd⟩ := hc
  have hid := wpow_append_identity (2 : ℤ) 3 w w' a
  have h : Dz (wpow w a ++ w') ∣ 2 ^ (a * w.sum) * 3 ^ 0 * Cw w w' := by
    rw [pow_zero, mul_one, Cw, ← hid]
    exact dvd_sub (dvd_mul_of_dvd_right hdvd _) (dvd_mul_left _ _)
  exact dvd_of_isCoprime_six_of_dvd (cop6 (wpow_append_pos hw hw' a) hne) _ _ h

/-- **`a`-independent bound.** If `C(w, w') ≠ 0`, every cycle word `w^a w'` has `|D| ≤ |C|`. -/
theorem wpow_append_ceiling {w w' : Word} (hw : w.Pos) (hw' : w'.Pos) (hC : Cw w w' ≠ 0) {a : ℕ}
    (hc : IsCycleWord (wpow w a ++ w')) : |Dz (wpow w a ++ w')| ≤ |Cw w w'| :=
  Int.le_of_dvd (abs_pos.mpr hC) ((abs_dvd_abs _ _).mpr (wpow_append_dvd hw hw' hc))

/-- **Finiteness.** If `C(w, w') ≠ 0`, only finitely many `w^a w'` are cycle words. -/
theorem wpow_append_finite {w w' : Word} (hw : w.Pos) (hw0 : w ≠ []) (hw' : w'.Pos)
    (hC : Cw w w' ≠ 0) : {a | IsCycleWord (wpow w a ++ w')}.Finite := by
  have hD : ∀ a, ((Dz (wpow w a ++ w') : ℤ) : ℝ) =
      2 ^ w'.sum * ((2 : ℝ) ^ w.sum) ^ a - 3 ^ w'.length * ((3 : ℝ) ^ w.length) ^ a := by
    intro a
    simp only [Dz, D, List.sum_append, List.length_append, wpow_sum, wpow_length]
    push_cast; ring
  have hne : (2 : ℝ) ^ w.sum ≠ 3 ^ w.length := by
    have hs : 1 ≤ w.sum := by have := sum_ne_zero hw hw0; omega
    have : (2 : ℤ) ^ w.sum ≠ 3 ^ w.length := by
      intro h
      have h2 : (2 : ℤ) ∣ 3 ^ w.length := h ▸ dvd_pow_self 2 (by omega)
      have := Int.Prime.dvd_pow' (p := 2) (by norm_num) h2
      omega
    exact_mod_cast this
  have ht := CycleGcd.tendsto_abs_sub_pow (A := 2 ^ w'.sum) (B := 3 ^ w'.length) (by positivity)
    (by positivity) (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) hne
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually_gt_atTop ((|Cw w w'| : ℤ) : ℝ))
  refine (Set.finite_Iio N).subset fun a ha => ?_
  by_contra hlt
  simp only [Set.mem_Iio, not_lt] at hlt
  have h1 := hN a hlt
  rw [← hD, ← Int.cast_abs] at h1
  have : ((|Dz (wpow w a ++ w')| : ℤ) : ℝ) ≤ ((|Cw w w'| : ℤ) : ℝ) := by
    exact_mod_cast wpow_append_ceiling hw hw' hC ha
  linarith

/-- **Constant fixed point.** If `C(w, w') = 0`, then for every nonempty member, `w^a w'` is a cycle
word iff `w` is (`D(w) ∣ S(w)`): the fixed point is `S(w)/D(w)` throughout. -/
theorem wpow_append_const {w w' : Word} (hw : w.Pos) (hw0 : w ≠ []) (hw' : w'.Pos)
    (hC : Cw w w' = 0) {a : ℕ} (hne : wpow w a ++ w' ≠ []) :
    IsCycleWord (wpow w a ++ w') ↔ Dz w ∣ Sz w := by
  have hid := wpow_append_identity (2 : ℤ) 3 w w' a
  rw [show wedge (2 : ℤ) 3 w w' = 0 from hC, mul_zero, sub_eq_zero] at hid
  -- hid : Dz w * Sz W = Sz w * Dz W
  have hDw : Dz w ≠ 0 := Dz_ne_zero hw hw0
  have hDW : Dz (wpow w a ++ w') ≠ 0 := Dz_ne_zero (wpow_append_pos hw hw' a) hne
  constructor
  · rintro ⟨-, k, hk⟩
    refine ⟨k, ?_⟩
    have : Dz (wpow w a ++ w') * Sz w = Dz (wpow w a ++ w') * (Dz w * k) := by
      have h' : Dz w * Sz (wpow w a ++ w') = Sz w * Dz (wpow w a ++ w') := hid
      rw [hk] at h'
      linear_combination -h'
    exact mul_left_cancel₀ hDW this
  · rintro ⟨k, hk⟩
    refine ⟨hne, k, ?_⟩
    have : Dz w * Sz (wpow w a ++ w') = Dz w * (Dz (wpow w a ++ w') * k) := by
      have h' : Dz w * Sz (wpow w a ++ w') = Sz w * Dz (wpow w a ++ w') := hid
      rw [h', hk]; ring
    exact mul_left_cancel₀ hDw this

/-- **Classification of `w^a w'`, uniform in `(w, w')`.** Either `C(w, w') ≠ 0`, the cycle set is
finite, and every cycle member has `|D| ≤ |C|`. Or `C(w, w') = 0`, and every nonempty member is a
cycle word exactly when `w` is. -/
theorem wpow_append_classification {w w' : Word} (hw : w.Pos) (hw0 : w ≠ []) (hw' : w'.Pos) :
    (Cw w w' ≠ 0 ∧ {a | IsCycleWord (wpow w a ++ w')}.Finite ∧
        ∀ a, IsCycleWord (wpow w a ++ w') → |Dz (wpow w a ++ w')| ≤ |Cw w w'|) ∨
      (Cw w w' = 0 ∧ ∀ a, wpow w a ++ w' ≠ [] →
        (IsCycleWord (wpow w a ++ w') ↔ Dz w ∣ Sz w)) := by
  by_cases hC : Cw w w' = 0
  · exact Or.inr ⟨hC, fun a hne => wpow_append_const hw hw0 hw' hC hne⟩
  · exact Or.inl ⟨hC, wpow_append_finite hw hw0 hw' hC,
      fun a ha => wpow_append_ceiling hw hw' hC ha⟩

/-- **The family as an r = 1 `Family`**, so `decideR1` gives its exact cycle set. -/
def wpowFamily (w w' : Word) : Family := ⟨w.sum, w.length, [.grow w 1 1 0, .fixed w']⟩

theorem wpowFamily_word (w w' : Word) (a : ℕ) : (wpowFamily w w').word a = wpow w a ++ w' := by
  simp [wpowFamily, Family.word, segsWord, Seg.word]

/-- Example: `(1,2)^a 4` has `C = -66 = -2·3·11 ≠ 0`. A cycle would need `|D| ∣ 11`; it has none. -/
example : Cw [1, 2] [4] = -66 := by decide
example : ∀ a, IsCycleWord (wpow [1, 2] a ++ [4]) ↔ a ∈ ([] : List ℕ) := by
  intro a
  rw [← wpowFamily_word]
  exact decideR1_iff (F := wpowFamily [1, 2] [4]) (v := .finite []) (by decide) (by decide +kernel) a

/-- Example: `(1,2)^a (1,2)` has `C = 0`: a cycle for every `a` (the `-5` cycle). -/
example : Cw [1, 2] [1, 2] = 0 := by decide

end Syracuse.R1
