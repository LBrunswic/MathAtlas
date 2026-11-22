import Syracuse.Approaches.CycleLiterature

/-!
# Cycle length from the verification bound alone (Eliahou's method, with Barina's `2^71`)

On a nontrivial positive cycle every point is at least `2^71` (Barina), so
`0 < E log 2 − o log 3 = Σ_k log(1 + 1/(3x_k)) ≤ o/(3·2^71)` (`CycleLiterature.barina_sandwich`).
So `E/o` lies in the tiny interval `(log₂3, log₂3 + 1/(3·2^71 ln 2))`. Two consecutive convergents
of `log₂3`,

`p/q = 103768467013/65470613321 < log₂3 < log₂3 + 1/(3·2^71 ln 2) < p'/q' = 10439860591/6586818670`,

bracket it, and `p'q − pq' = 1`. A fraction strictly between two Farey neighbours has denominator at
least `q + q'` (`farey`). Hence (`cycle_length_ge`)

> every nontrivial positive cycle has `o ≥ 72 057 431 991` odd steps and `E ≥ 114 208 327 604` halvings,

the mediant `(p + p')/(q + q')`. No literature input beyond `Barina2025` is used: the two inequalities
between `log 2` and `log 3` are certified from the series of `log(1 − x)` at `x = 1/9` and `x = 13/256`
(`log_two_three`, `30` digits; `log_bounds`).

This is Eliahou's 1993 argument with today's verification bound. Hercher's Corollary 29
(`o > 1.375·10^{11}`, stated as `CycleLiterature.Hercher2023Cor29`) is stronger by a factor `1.9`; the
bound here is weaker but fully proved, so the frontier theorems can drop that literature input
(`CycleBounds`, `cycleBounds_barina`).

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `log 2` and `log 3` to `30` digits | `log_two_three` | proved |
| `65470613321 log 3 > 103768467013 log 2` and `10439860591 log 2 − 6586818670 log 3 > 6586818670/(3·2^71)` | `log_bounds` | proved |
| fractions between Farey neighbours have denominator `≥ q + q'` | `farey` | proved |
| **`o ≥ 72 057 431 991` and `E ≥ 114 208 327 604`** on a nontrivial positive cycle | `cycle_length_ge` | proved (conditional on `Barina2025` only) |
| the same bounds packaged for the frontier theorems | `cycleBounds_barina`, `cycleBounds_hercher` | proved |
-/

namespace Syracuse.CycleLength

open Finset Syracuse

/-- **`log 2` and `log 3` to `30` digits.** From the series of `log(1 − x)` at `x = 1/9`
(`log(8/9) = 3 log 2 − 2 log 3`, `31` terms) and `x = 13/256` (`log(243/256) = 5 log 3 − 8 log 2`,
`23` terms), each with error below `10^{-30}`. -/
lemma log_two_three :
    (693147180559945309417232121451 : ℝ) / 10 ^ 30 < Real.log 2 ∧
      Real.log 2 < (693147180559945309417232121466 : ℝ) / 10 ^ 30 ∧
      (1098612288668109691395245236911 : ℝ) / 10 ^ 30 < Real.log 3 ∧
      Real.log 3 < (1098612288668109691395245236934 : ℝ) / 10 ^ 30 := by
  have e1 := Real.abs_log_sub_add_sum_range_le (show |(1 / 9 : ℝ)| < 1 by
    rw [abs_of_pos (by norm_num)]; norm_num) 31
  have e2 := Real.abs_log_sub_add_sum_range_le (show |(13 / 256 : ℝ)| < 1 by
    rw [abs_of_pos (by norm_num)]; norm_num) 23
  rw [show (1 : ℝ) - 1 / 9 = 2 ^ 3 / 3 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 9)] at e1
  rw [show (1 : ℝ) - 13 / 256 = 3 ^ 5 / 2 ^ 8 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, abs_of_pos (by norm_num : (0 : ℝ) < 13 / 256)] at e2
  set S1 := ∑ i ∈ range 31, (1 / 9 : ℝ) ^ (i + 1) / (i + 1) with hS1
  set S2 := ∑ i ∈ range 23, (13 / 256 : ℝ) ^ (i + 1) / (i + 1) with hS2
  have b1 : (1 / 9 : ℝ) ^ (31 + 1) / (1 - 1 / 9) ≤ 1 / 10 ^ 30 := by norm_num
  have b2 : (13 / 256 : ℝ) ^ (23 + 1) / (1 - 13 / 256) ≤ 1 / 10 ^ 30 := by norm_num
  have s1 : (1177830356563834545387941094705115 : ℝ) / 10 ^ 34 ≤ S1 ∧
      S1 ≤ (1177830356563834545387941094705116 : ℝ) / 10 ^ 34 := by
    rw [hS1]; simp only [sum_range_succ, sum_range_zero]; norm_num
  have s2 : (521160011390140183616307870527802 : ℝ) / 10 ^ 34 ≤ S2 ∧
      S2 ≤ (521160011390140183616307870527803 : ℝ) / 10 ^ 34 := by
    rw [hS2]; simp only [sum_range_succ, sum_range_zero]; norm_num
  obtain ⟨l1, u1⟩ := abs_le.1 (e1.trans b1)
  obtain ⟨l2, u2⟩ := abs_le.1 (e2.trans b2)
  simp only [Nat.cast_ofNat] at l1 u1 l2 u2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [s1.1, s1.2, s2.1, s2.2]

/-- **Two certified inequalities between `log 2` and `log 3`**, for the Farey neighbours of
`cycle_length_ge`. -/
lemma log_bounds :
    (0 : ℝ) < 65470613321 * Real.log 3 - 103768467013 * Real.log 2 ∧
      (6586818670 : ℝ) / (3 * 2 ^ 71) < 10439860591 * Real.log 2 - 6586818670 * Real.log 3 := by
  obtain ⟨a1, a2, b1, b2⟩ := log_two_three
  constructor <;> linarith

/-- **Farey neighbours.** If `p'q − pq' = 1` and `p/q < E/o < p'/q'` (in cross-multiplied form), then
`o ≥ q + q'`. -/
lemma farey {p q p' q' E o : ℤ} (hdet : p' * q - p * q' = 1) (h1 : 0 < E * q - p * o)
    (h2 : 0 < p' * o - E * q') (hq : 0 < q) (hq' : 0 < q') : q + q' ≤ o := by
  have hid : o = q * (p' * o - E * q') + q' * (E * q - p * o) := by linear_combination (-o) * hdet
  nlinarith

/-- **Cycle length from Barina alone.** Every nontrivial positive cycle has at least
`72 057 431 991` odd steps and `114 208 327 604` halvings. -/
theorem cycle_length_ge (hB : CycleLiterature.Barina2025) {a : ℤ} {o : ℕ} (h : IsSyrCycle a o)
    (ha : 0 < a) (h1 : a ≠ 1) : 72057431991 ≤ o ∧ 114208327604 ≤ (gapWord a o).sum := by
  obtain ⟨s1, -, s3⟩ := CycleLiterature.barina_sandwich hB h ha h1
  obtain ⟨K1, K2⟩ := log_bounds
  set E := (gapWord a o).sum
  have ho : (0 : ℝ) < o := by exact_mod_cast h.1
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Real.log_div_log] at s1 s3
  -- `o log 3 < E log 2`
  have t1 : (o : ℝ) * Real.log 3 < E * Real.log 2 := by
    rw [div_lt_div_iff₀ hl2 ho] at s1; linarith
  -- `E log 2 − o log 3 < o/(3·2^71)`
  have t2 : (E : ℝ) * Real.log 2 - o * Real.log 3 < o / (3 * 2 ^ 71) := by
    have := mul_lt_mul_of_pos_right s3 hl2
    have e : ((E : ℝ) - o * (Real.log 3 / Real.log 2)) * Real.log 2 =
        E * Real.log 2 - o * Real.log 3 := by
      field_simp
    have e' : (o : ℝ) / (3 * 2 ^ 71 * Real.log 2) * Real.log 2 = o / (3 * 2 ^ 71) := by
      field_simp
    linarith
  have X1 : (0 : ℤ) < (E : ℤ) * 65470613321 - 103768467013 * (o : ℤ) := by
    have hr : (0 : ℝ) <
        (((E : ℤ) * 65470613321 - 103768467013 * (o : ℤ) : ℤ) : ℝ) * Real.log 2 := by
      push_cast
      linarith [mul_pos ho K1]
    have : (0 : ℝ) < (((E : ℤ) * 65470613321 - 103768467013 * (o : ℤ) : ℤ) : ℝ) :=
      (pos_iff_pos_of_mul_pos hr).2 hl2
    exact Int.cast_pos.mp this
  have X2 : (0 : ℤ) < 10439860591 * (o : ℤ) - (E : ℤ) * 6586818670 := by
    have hr : (0 : ℝ) < ((10439860591 * (o : ℤ) - (E : ℤ) * 6586818670 : ℤ) : ℝ) * Real.log 2 := by
      push_cast
      linarith [mul_lt_mul_of_pos_left K2 ho]
    have : (0 : ℝ) < ((10439860591 * (o : ℤ) - (E : ℤ) * 6586818670 : ℤ) : ℝ) :=
      (pos_iff_pos_of_mul_pos hr).2 hl2
    exact Int.cast_pos.mp this
  have hf := farey (by norm_num) X1 X2 (by norm_num) (by norm_num)
  refine ⟨by omega, by omega⟩

/-- Lower bounds on the number of odd steps `o` and halvings `E` of every nontrivial positive
cycle. -/
def CycleBounds (No NE : ℕ) : Prop :=
  ∀ a : ℤ, ∀ o : ℕ, 0 < a → IsSyrCycle a o → a ≠ 1 → No < o ∧ NE < (gapWord a o).sum

/-- **The bounds from Barina alone** (`cycle_length_ge`). -/
theorem cycleBounds_barina (hB : CycleLiterature.Barina2025) :
    CycleBounds 72057431990 114208327603 := fun a o ha h h1 => by
  have := cycle_length_ge hB h ha h1
  omega

/-- **The bounds with Hercher's Corollary 29.** -/
theorem cycleBounds_hercher (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) : CycleBounds 137500000000 137500000000 :=
  fun a o ha h h1 => by
    have ho := CycleLiterature.hercher_odd_steps_of_barina hH29 hB h ha h1
    have hl := CycleLiterature.length_le_sum (gapWord_pos h.2.1 o)
    rw [gapWord_length] at hl
    omega

end Syracuse.CycleLength
