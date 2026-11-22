import Syracuse.Approaches.R1.WPow

/-!
# Shared support for generated skeleton files

`approaches/places-elimination/skeleton.py compile SHAPE NAME` emits a file `R1/Skel/NAME.lean`.
That file proves, uniformly in the block and spacer words, a closed form, a universal resultant
certificate, a ceiling `D ∣ c · R'(data)`, and finiteness whenever the ceiling is nonzero. This
file holds the two lemmas every such file uses.
-/

namespace Syracuse.R1

open Syracuse Syracuse.CocycleCombine Filter

/-- The block relation `D(β) S(β^n) = S(β) (X^{n|β|} - Y^{n len β})`. -/
theorem wpow_rel {R : Type*} [CommRing R] (X Y : R) (β : Word) (n : ℕ) :
    D X Y β * S X Y (wpow β n) = S X Y β * (X ^ (n * β.sum) - Y ^ (n * β.length)) := by
  rw [S_wpow, show X ^ (n * β.sum) - Y ^ (n * β.length) = D X Y (wpow β n) by
    simp [D, wpow_sum, wpow_length], D_wpow]
  ring

/-- **Finiteness from a ceiling.** If `D(W(a)) = 2^{E₀} (2^α)^a - 3^{o₀} (3^β)^a` with `α ≥ 1`,
and every cycle member has `D ∣ c` with `c ≠ 0`, then only finitely many `a` give cycles. -/
theorem finite_of_ceiling {W : ℕ → Word} {c : ℤ} (hc : c ≠ 0) {E₀ o₀ α β : ℕ} (hα : 1 ≤ α)
    (_hβ : 1 ≤ β) (hD : ∀ a, Dz (W a) = 2 ^ E₀ * (2 ^ α) ^ a - 3 ^ o₀ * (3 ^ β) ^ a)
    (hceil : ∀ a, IsCycleWord (W a) → Dz (W a) ∣ c) : {a | IsCycleWord (W a)}.Finite := by
  have hne : (2 : ℝ) ^ α ≠ 3 ^ β := by
    have : (2 : ℤ) ^ α ≠ 3 ^ β := by
      intro h
      have h2 : (2 : ℤ) ∣ 3 ^ β := h ▸ dvd_pow_self 2 (by omega)
      have := Int.Prime.dvd_pow' (p := 2) (by norm_num) h2
      omega
    exact_mod_cast this
  have ht := CycleGcd.tendsto_abs_sub_pow (A := 2 ^ E₀) (B := 3 ^ o₀) (by positivity)
    (by positivity) (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) hne
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually_gt_atTop ((|c| : ℤ) : ℝ))
  refine (Set.finite_Iio N).subset fun a ha => ?_
  by_contra hlt
  simp only [Set.mem_Iio, not_lt] at hlt
  have h1 := hN a hlt
  have hle : |Dz (W a)| ≤ |c| := Int.le_of_dvd (abs_pos.mpr hc) ((abs_dvd_abs _ _).mpr (hceil a ha))
  have hcast : ((Dz (W a) : ℤ) : ℝ) = 2 ^ E₀ * ((2 : ℝ) ^ α) ^ a - 3 ^ o₀ * ((3 : ℝ) ^ β) ^ a := by
    rw [hD a]; push_cast; ring
  rw [← hcast, ← Int.cast_abs] at h1
  have : ((|Dz (W a)| : ℤ) : ℝ) ≤ ((|c| : ℤ) : ℝ) := by exact_mod_cast hle
  linarith

end Syracuse.R1
