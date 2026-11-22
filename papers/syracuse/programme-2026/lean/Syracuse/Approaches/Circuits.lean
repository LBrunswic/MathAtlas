import Syracuse.Approaches.TwoBackground
import Syracuse.Approaches.Limits

/-!
# Two growing runs for every letter pair, and Steiner's circuit theorem from Ellison

`TwoBackground.no_cycle_one_two` excludes positive cycles on `1^a 2^b`. Here we exclude every
two-letter cyclic word `1^a d^b` with `d ≥ 3` (`no_cycle_one_d`), so **no positive Syracuse cycle has a
cyclic gap word with two growing runs of letters** (`no_cycle_two_letters`; a positive cycle needs one
letter below `log₂ 3`, i.e. `1`). The case `b = 1` is a **circuit**, so we also obtain **Steiner's
theorem** (`Steiner1977`: no nontrivial positive `1`-cycle) **conditional on Ellison 1971**
(`steiner_of_ellison`).

The argument for `d ≥ 3`, with `E = a + db`, `o = a + b`:
* on a cycle `D ∣ (2^{d-1} - 1)·(2^{db} - 3^b)` (`TwoBackground.dvd_of_cycle`, a `2` stripped), so
  `D < 2^{d - 1 + db}`;
* Ellison (`E ≥ 28`): `D > 2^E e^{-E/10}`. With the previous bullet: `(a - d + 1)·log 2 < E/10`, so
  `6931471803·(a - d + 1) < 10⁹·E` (`log 2 > 0.6931471803`, Mathlib);
* the ratio sandwich for a nontrivial positive cycle, `2^E 3^o ≤ 10^o` (`Limits`), gives
  `1000·E < 1740·o` because `2^{1740}·3^{1000} > 10^{1000}`;
* these force `a ≥ d`, then `b = 1` (for `b ≥ 2` they contradict outright), then `a ≤ 110` with `d` in
  a window of width < 1: 35 explicit words, none a cycle (`window_check`). The cases `E ≤ 27` are a
  finite check (`small_check`).

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `2^E 3^o ≤ 10^o ⇒ 1000 E < 1740 o` | `sandwich_linear` | proved |
| `D < 2^{d-1+db}` on a cycle with word `1^a d^b` | `D_lt_of_cycle` | proved |
| Ellison ⇒ `6931471803 (a - d + 1) < 10⁹ E` | `ellison_linear` | proved (conditional on `Ellison1971`) |
| no positive cycle on `1^a d^b`, `d ≥ 3` | `no_cycle_one_d` | proved (conditional on `Ellison1971`) |
| no positive cycle on any two-letter-run word `1^a d^b`, `d ≥ 2` | `no_cycle_two_letters` | proved (conditional on `Ellison1971`) |
| **Steiner 1977**: no nontrivial positive circuit | `steiner_of_ellison` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.Circuits

open Syracuse Syracuse.TwoBackground

/-- `S` and `D` of `1^a d^b` as numbers: sum and length. -/
lemma two_sum (d a b : ℕ) : (two 1 d a b).sum = a + d * b := by
  simp [two, List.sum_replicate, mul_comm]

lemma two_length (d a b : ℕ) : (two 1 d a b).length = a + b := by simp [two]

/-- **Sandwich, linearised.** `2^E·3^o ≤ 10^o` with `o > 0` forces `1000·E < 1740·o`. -/
theorem sandwich_linear {E o : ℕ} (ho : 0 < o) (h : 2 ^ E * 3 ^ o ≤ 10 ^ o) : 1000 * E < 1740 * o := by
  by_contra hc
  replace hc := not_lt.mp hc
  have key : (2 ^ 1740 * 3 ^ 1000) ^ o ≤ (10 ^ 1000) ^ o := by
    calc (2 ^ 1740 * 3 ^ 1000) ^ o = 2 ^ (1740 * o) * 3 ^ (1000 * o) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ 2 ^ (1000 * E) * 3 ^ (1000 * o) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hc) le_rfl
      _ = (2 ^ E * 3 ^ o) ^ 1000 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm E, mul_comm o]
      _ ≤ (10 ^ o) ^ 1000 := by gcongr
      _ = (10 ^ 1000) ^ o := by rw [← pow_mul, ← pow_mul, mul_comm]
  have := (Nat.pow_le_pow_iff_left (by omega)).1 key
  exact absurd this (by decide +kernel)

/-- On a cycle whose gap word is a rotation of `1^a d^b` (`d ≥ 2`, `a + b ≥ 1`):
`D ∣ (2^{d-1} - 1)·(2^{db} - 3^b)`. -/
theorem dvd_cV {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b d : ℕ} (hd : 2 ≤ d) (hab : 1 ≤ a + b)
    (hw : gapWord x o ~r two 1 d a b) :
    Dz (two 1 d a b) ∣ (2 ^ (d - 1) - 1) * (2 ^ (d * b) - 3 ^ b) := by
  have hne : two 1 d a b ≠ [] := by
    intro h0; have := congrArg List.length h0; simp [two] at this; omega
  have hE : (two 1 d a b).sum ≠ 0 := by
    rw [two_sum]
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0; omega
    · have := Nat.mul_pos (show 0 < d by omega) hb0; omega
  obtain ⟨hV, -⟩ := dvd_of_cycle h hw hne hE
  have hc := isCoprime_six hne hE
  have : Dz (two 1 d a b) ∣ 2 ^ 1 * 3 ^ 0 * (-((2 ^ (d - 1) - 1) * (2 ^ (d * b) - 3 ^ b))) := by
    have e : (2 : ℤ) ^ 1 * 3 ^ 0 * (-((2 ^ (d - 1) - 1) * (2 ^ (d * b) - 3 ^ b))) =
        (2 ^ 1 - 2 ^ d) * (2 ^ (b * d) - 3 ^ b) := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      rw [Nat.add_sub_cancel, mul_comm b, pow_succ]; ring
    rw [e]; exact hV
  have := CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this
  rwa [dvd_neg] at this

/-- **Upper bound.** On such a positive cycle, `D < 2^{d - 1 + db}`. -/
theorem D_lt_of_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) {a b d : ℕ} (hd : 2 ≤ d)
    (hb : 1 ≤ b) (hw : gapWord x o ~r two 1 d a b) :
    Dz (two 1 d a b) < 2 ^ (d - 1 + d * b) := by
  have hdv := dvd_cV h hd (by omega) hw
  have hDeq : Dz (two 1 d a b) = Dz (gapWord x o) := by
    obtain ⟨n, hn⟩ := hw; rw [← hn]; exact D_rotate _ _ _ _
  have hD : 0 < Dz (two 1 d a b) := hDeq ▸ CycleLiterature.cycle_Dz_pos h hx
  have hc1 : (1 : ℤ) ≤ 2 ^ (d - 1) - 1 := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ (d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hV : (0 : ℤ) < 2 ^ (d * b) - 3 ^ b := by
    have : (3 : ℤ) ^ b < 4 ^ b := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have : (4 : ℤ) ^ b ≤ 2 ^ (d * b) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right b hd)
    linarith
  have hle := Int.le_of_dvd (mul_pos (by linarith) hV) hdv
  calc Dz (two 1 d a b) ≤ (2 ^ (d - 1) - 1) * (2 ^ (d * b) - 3 ^ b) := hle
    _ < 2 ^ (d - 1) * 2 ^ (d * b) := by
        have h3 : (0 : ℤ) < 3 ^ b := by positivity
        nlinarith
    _ = 2 ^ (d - 1 + d * b) := by rw [pow_add]

/-- **Ellison, linearised.** If `|2^E - 3^o| > 2^E e^{-E/10}` and `|2^E - 3^o| < 2^{d - 1 + db}` with
`E = a + db` and `a ≥ d`, then `6931471803·(a - d + 1) < 10⁹·E`. -/
theorem ellison_linear {a b d o : ℕ} (hd : 1 ≤ d) (had : d ≤ a)
    (hEl : (2 : ℝ) ^ (a + d * b) * Real.exp (-((a + d * b : ℕ) : ℝ) / 10) < |(2 : ℝ) ^ (a + d * b) - 3 ^ o|)
    (hup : |(2 : ℝ) ^ (a + d * b) - 3 ^ o| < 2 ^ (d - 1 + d * b)) :
    6931471803 * ((a : ℤ) - d + 1) < 1000000000 * (a + d * b) := by
  have h := hEl.trans hup
  have hpos : 0 < (2 : ℝ) ^ (a + d * b) * Real.exp (-((a + d * b : ℕ) : ℝ) / 10) := by positivity
  have hlog := Real.log_lt_log hpos h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow, Real.log_pow] at hlog
  have hl2 := Real.log_two_gt_d9
  -- `(a - d + 1) log 2 < E/10`
  have h1 : ((a : ℝ) - d + 1) * Real.log 2 < ((a + d * b : ℕ) : ℝ) / 10 := by
    push_cast at hlog ⊢
    rw [Nat.cast_sub hd] at hlog
    push_cast at hlog
    nlinarith
  have hnn : (0 : ℝ) ≤ (a : ℝ) - d + 1 := by
    have : (d : ℝ) ≤ a := by exact_mod_cast had
    linarith
  have h2 : ((a : ℝ) - d + 1) * 0.6931471803 ≤ ((a : ℝ) - d + 1) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le hnn
  have h3 : (6931471803 : ℝ) * ((a : ℝ) - d + 1) < 1000000000 * ((a : ℝ) + d * b) := by
    push_cast at h1; nlinarith
  exact_mod_cast h3

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Small cases** (`E ≤ 27`, below Ellison's range): no `1^a d^b` (`d ≥ 3`) is a positive cycle word. -/
theorem small_check : ∀ a : ℕ, a < 28 → ∀ b : ℕ, b < 14 → ∀ d : ℕ, d < 28 →
    (1 ≤ a ∧ 1 ≤ b ∧ 3 ≤ d ∧ a + d * b ≤ 27) →
    ¬ (0 < Dz (two 1 d a b) ∧ Sz (two 1 d a b) % Dz (two 1 d a b) = 0) := by
  decide +kernel

/-- **The `b = 1` window** (`E ≥ 28`): the 35 circuits left by Ellison and the sandwich are not cycles. -/
theorem window_check : ∀ a : ℕ, a < 111 → ∀ d : ℕ, d < 85 →
    (3 ≤ d ∧ 28 ≤ a + d ∧ 1000 * d < 740 * a + 1740 ∧ 5931471803 * a + 6931471803 < 7931471803 * d) →
    ¬ (0 < Dz (two 1 d a 1) ∧ Sz (two 1 d a 1) % Dz (two 1 d a 1) = 0) := by
  decide +kernel

/-- The trivial cycle's gap word consists of `2`s only. -/
lemma gapWord_one (o : ℕ) : ∀ g ∈ gapWord 1 o, g = 2 := by
  induction o with
  | zero => simp [gapWord]
  | succ o ih =>
    intro g hg
    obtain ⟨hgap, hsyr⟩ := CycleLiterature.gap_syr_one
    simp only [gapWord, hsyr, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact hgap
    · exact ih g hg

/-- **No positive cycle on `1^a d^b` with `d ≥ 3`**, conditional on Ellison. -/
theorem no_cycle_one_d (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hx : 0 < x) {a b d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 3 ≤ d)
    (hw : gapWord x o ~r two 1 d a b) : False := by
  have hS := dvd_S_of_rotated h hw
  have hDeq : Dz (two 1 d a b) = Dz (gapWord x o) := by
    obtain ⟨n, hn⟩ := hw; rw [← hn]; exact D_rotate _ _ _ _
  have hD : 0 < Dz (two 1 d a b) := hDeq ▸ CycleLiterature.cycle_Dz_pos h hx
  have hlen : o = a + b := by
    have := hw.perm.length_eq; rw [gapWord_length, two_length] at this; exact this
  have hsumw : (gapWord x o).sum = a + d * b := by rw [hw.perm.sum_eq, two_sum]
  by_cases hE : a + d * b ≤ 27
  · exact small_check a (by omega) b (by nlinarith) d (by nlinarith) ⟨ha, hb, hd, hE⟩
      ⟨hD, Int.emod_eq_zero_of_dvd hS⟩
  replace hE := not_le.mp hE
  -- `x ≠ 1`: the trivial cycle has no gap `1`
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : 1 ∈ two 1 d a b := by simp [two]; omega
    have := gapWord_one o 1 (hw.symm.perm.subset h1)
    omega
  -- sandwich
  have hsand := Limits.two_pow_mul_three_pow_le h hx hx1
  rw [hsumw] at hsand
  have hS1 := sandwich_linear (by omega) hsand
  rw [hlen] at hS1
  -- `D < 2^{d-1+db}` and `D = 2^E - 3^o`
  have hup := D_lt_of_cycle h hx (by omega) hb hw
  have hDf : Dz (two 1 d a b) = 2 ^ (a + d * b) - 3 ^ (a + b) := by
    simp only [Dz, D, two_sum, two_length]
  -- `a ≥ d`
  have hbd : (1000 * d - 1740 : ℤ) ≤ (1000 * d - 1740) * b := by
    have : (0 : ℤ) ≤ (1000 * d - 1740) * (b - 1) := mul_nonneg (by omega) (by omega)
    nlinarith
  have had : d ≤ a := by
    by_contra hlt; replace hlt := not_le.mp hlt
    have : (1000 * (a + d * b) : ℤ) < 1740 * (a + b) := by exact_mod_cast hS1
    nlinarith
  -- Ellison
  have hnot : a + d * b ∉ CycleLiterature.ellisonExceptions := by
    simp only [CycleLiterature.ellisonExceptions, Finset.mem_insert, Finset.mem_singleton]; omega
  have hEl' := hEl (a + d * b) (a + b) (by omega) (by omega) hnot
  have habs : |(2 : ℝ) ^ (a + d * b) - 3 ^ (a + b)| < 2 ^ (d - 1 + d * b) := by
    rw [abs_of_pos (by rw [hDf] at hD; exact_mod_cast hD)]
    rw [hDf] at hup; exact_mod_cast hup
  have hL := ellison_linear (by omega) had hEl' habs
  have hSz : (1000 * (a + d * b) : ℤ) < 1740 * (a + b) := by exact_mod_cast hS1
  -- `b ≥ 2` is impossible; `b = 1` leaves the window
  rcases Nat.lt_or_ge b 2 with hb1 | hb2
  · obtain rfl : b = 1 := by omega
    simp only [Nat.cast_one, mul_one] at hL hSz
    have hwin : 5931471803 * a + 6931471803 < 7931471803 * d := by
      have : (5931471803 * a + 6931471803 : ℤ) < 7931471803 * d := by linarith
      exact_mod_cast this
    have hwin2 : 1000 * d < 740 * a + 1740 := by
      have : (1000 * d : ℤ) < 740 * a + 1740 := by linarith
      exact_mod_cast this
    have ha110 : a < 111 := by omega
    exact window_check a ha110 d (by omega) ⟨hd, by omega, hwin2, hwin⟩
      ⟨hD, Int.emod_eq_zero_of_dvd hS⟩
  · have hprod : (2 * b + 2 * d - 4 : ℤ) ≤ d * b :=
      by nlinarith [mul_nonneg (show (0 : ℤ) ≤ b - 2 by omega) (show (0 : ℤ) ≤ d - 2 by omega)]
    nlinarith

/-- **No positive cycle with two growing runs of letters** (any `1^a d^b`, `a, b ≥ 1`, `d ≥ 2`),
conditional on Ellison. -/
theorem no_cycle_two_letters (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hx : 0 < x) {a b d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 2 ≤ d)
    (hw : gapWord x o ~r two 1 d a b) : False := by
  rcases Nat.lt_or_ge d 3 with h2 | h3
  · obtain rfl : d = 2 := by omega
    exact no_cycle_one_two hEl h hx ha hb hw
  · exact no_cycle_one_d hEl h hx ha hb h3 hw

/-- A positive word with exactly one gap `≥ 2` is a rotation of `1^{n-1} d`. -/
lemma isRotated_circuit {w : Word} (hw : w.Pos) (h1 : CycleLiterature.numBlocks w = 1) :
    ∃ d, 2 ≤ d ∧ w ~r two 1 d (w.length - 1) 1 := by
  unfold CycleLiterature.numBlocks at h1
  obtain ⟨d, hdw, hd⟩ := List.countP_pos_iff.1 (by omega : 0 < w.countP fun d => decide (2 ≤ d))
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hdw
  have hd2 : 2 ≤ d := by simpa using hd
  rw [List.countP_append, List.countP_cons] at h1
  simp only [hd2, decide_true, ite_true] at h1
  have c1 : l₁.countP (fun d => decide (2 ≤ d)) = 0 := by omega
  have c2 : l₂.countP (fun d => decide (2 ≤ d)) = 0 := by omega
  have one_of : ∀ l : Word, (∀ g ∈ l, 1 ≤ g) → l.countP (fun d => decide (2 ≤ d)) = 0 →
      l = List.replicate l.length 1 := by
    intro l hpos hc
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun g hg => ?_⟩
    have := List.countP_eq_zero.1 hc g hg
    have := hpos g hg
    simp at *; omega
  have e1 := one_of l₁ (fun g hg => hw g (by simp [hg])) c1
  have e2 := one_of l₂ (fun g hg => hw g (by simp [hg])) c2
  refine ⟨d, hd2, ?_⟩
  have hrot : (l₁ ++ d :: l₂) ~r (l₂ ++ l₁ ++ [d]) := by
    have := List.isRotated_append (l := l₁ ++ [d]) (l' := l₂)
    simpa [List.append_assoc] using this
  have heq : l₂ ++ l₁ ++ [d] = two 1 d ((l₁ ++ d :: l₂).length - 1) 1 := by
    rw [two, List.replicate_one]
    congr 1
    rw [List.length_append, List.length_cons,
      show l₁.length + (l₂.length + 1) - 1 = l₂.length + l₁.length by omega,
      ← List.replicate_append_replicate, ← e2, ← e1]
  exact heq ▸ hrot

/-- **Steiner 1977 from Ellison 1971**: there is no nontrivial positive circuit (`1`-cycle). -/
theorem steiner_of_ellison (hEl : CycleLiterature.Ellison1971) : CycleLiterature.Steiner1977 := by
  intro x hm
  obtain ⟨hx, o, ⟨h, -⟩, hblocks⟩ := hm
  obtain ⟨d, hd, hrot⟩ := isRotated_circuit (CocycleCombine.IsSyrCycle.pos h) hblocks
  rcases Nat.lt_or_ge o 2 with ho | ho
  · have : o = 1 := by have := h.1; omega
    subst this
    exact (CycleLiterature.period_one_pos hx h).1
  · exfalso
    rw [gapWord_length] at hrot
    exact no_cycle_two_letters hEl h hx (by omega) le_rfl hd hrot

end Syracuse.Circuits
