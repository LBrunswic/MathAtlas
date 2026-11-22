import Syracuse.Approaches.SignedCycles
import Syracuse.Approaches.Repeat

/-!
# Two-block cycles with equal big gaps (Simons 2-cycles, `l₁ = l₂`)

A cycle with exactly two gaps `≥ 2` has a gap word that is a rotation of `1^{a₁} d₁ 1^{a₂} d₂`
(`isRotated_two_blocks`). These are Simons's 2-cycles. The `-17` cycle is one, with `d₁ = 2`,
`d₂ = 4`. Here the case of **equal big gaps** `d₁ = d₂ = d` is closed on all of `ℤ`, given Ellison
only:

> The cycles of the accelerated `3x+1` map on `ℤ` with two big gaps, both equal, are `1` and
> `-5 → -7` (`equal_two_blocks`).

**Why it is elementary.** For `a₁ > a₂` re-bracket:
`1^{a₁} d 1^{a₂} d = 1^{a₁ - a₂} · (1^{a₂} d)²`. This is a two-run word over the pair `(1, Z)`,
`Z = 1^m d`, `m = a₂`, whose wedge core is `C(1, Z) = -2^{m+1}(2^{d-1} - 1)` (`core_blk`). It is not
6-smooth for `d ≥ 4`, so `StdPairs` does not apply. But it is small: the two-block divisibilities give
`D ∣ (2^{d-1} - 1)(2^k - 3^k)` and `D ∣ (2^{d-1} - 1)(2^{2(m+d)} - 3^{2(m+1)})`, `k = a₁ - a₂`. With
Ellison these give
`85573 E < 100000 (d-1) + 158500 k` and either `85573 E < 100000 (d - 1 + 2(m+d))` or
`85573 E < 100000 (d-1) + 317000 (m+1)` (`lin_of_lt`). Together with the sign bound
(`1584 o < 1000 E < 1740 o` for positive cycles, `1000 E < 1585 o` for negative ones) they contradict
`E ≥ 28` by linear integer arithmetic. There is no window. `E ≤ 27` is a kernel check
(`small_check`), `a₁ = a₂` is a power of a circuit, and `d = 2` is a level-`(1,2)` two-cycle.

The distinct-gap case `d₁ ≠ d₂` admits no re-bracketing. Its single two-block divisibility
`D ∣ C(B₁, B₂)` restates `D ∣ S`, and `-17` lives there. That case is Simons's 2005 theorem, which
uses linear forms in logarithms and lattice reduction.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `S(1^m d) = 3^{m+1} - 2^{m+1}`, `D(1^m d) = 2^{m+d} - 3^{m+1}` | `S_blk`, `D_blk` | proved |
| `C(1, 1^m d) = -2^{m+1}(2^{d-1} - 1)` | `core_blk` | proved |
| re-bracketing `1^{k+m} d 1^m d = 1^k (1^m d)²` | `tc_eq` | proved |
| Ellison, linearised: `2^E e^{-E/10} < 2^p 3^q ⇒ 85573 E < 100000 p + 158500 q` | `lin_of_lt` | proved |
| `3^o < 2^E ⇒ 1584 o < 1000 E` | `pos_sign_linear` | proved |
| no `1^{k+m} d 1^m d` (`d ≥ 3`, `E ≤ 27`) has `D ∣ S` | `small_check` | proved (`decide +kernel`) |
| no cycle (either sign) on `1^{a₁} d 1^{a₂} d`, `a₁ ≠ a₂`, `d ≥ 3` | `no_cycle_unequal` | proved (conditional on `Ellison1971`) |
| the only cycle on `1^{a₁} d 1^{a₂} d` (`a₁, a₂ ≥ 1`, `d ≥ 2`) is `-5 → -7` | `equal_two_cycles` | proved (conditional on `Ellison1971`) |
| a positive word with two gaps `≥ 2` is a rotation of `1^{a₁} d₁ 1^{a₂} d₂` | `isRotated_two_blocks` | proved |
| two big gaps, equal: only `1` and `-5 → -7` | `equal_two_blocks` | proved (conditional on `Ellison1971`) |
| the closed classes, enlarged by equal-gap two-block words: only `1, -1, -5, -7` | `closed_classes₂` | proved (conditional on `Ellison1971`) |
| `-17` is outside the enlarged union | `neg_seventeen_outside₂` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.EqualTwoCycles

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

/-- The circuit block `1^m d`. -/
abbrev blk (m d : ℕ) : Word := List.replicate m 1 ++ [d]

/-- The equal-gap two-block word `1^{a₁} d 1^{a₂} d`. -/
def tc (d a₁ a₂ : ℕ) : Word := blk a₁ d ++ blk a₂ d

lemma tc_sum (d a₁ a₂ : ℕ) : (tc d a₁ a₂).sum = a₁ + a₂ + 2 * d := by
  simp [tc, List.sum_replicate]; ring

lemma tc_length (d a₁ a₂ : ℕ) : (tc d a₁ a₂).length = a₁ + a₂ + 2 := by
  simp [tc]; ring

lemma S_blk (m d : ℕ) : Sz (blk m d) = 3 ^ (m + 1) - 2 ^ (m + 1) := by
  have h := BoundedDefectLever.S_replicate_mul (2 : ℤ) 3 1 m
  simp only [Sz, blk, S_append, S_singleton, List.length_singleton, List.sum_replicate,
    smul_eq_mul, mul_one, pow_one] at h ⊢
  linear_combination (-3) * h

lemma D_blk (m d : ℕ) : Dz (blk m d) = 2 ^ (m + d) - 3 ^ (m + 1) := by
  simp [Dz, D, blk, List.sum_replicate]

/-- **The core of `(1, 1^m d)`** is `-2^{m+1}(2^{d-1} - 1)`. -/
lemma core_blk (m j : ℕ) : core (2 : ℤ) 3 [1] (blk m (j + 1)) = -(2 ^ (m + 1) * (2 ^ j - 1)) := by
  have hS := S_blk m (j + 1)
  have hD := D_blk m (j + 1)
  simp only [Sz, Dz] at hS hD
  simp only [core]
  rw [hS, hD]
  simp only [D, S_singleton, List.sum_singleton, List.length_singleton]
  ring

/-- **Re-bracketing.** `1^{k+m} d 1^m d = 1^k (1^m d)²`. -/
lemma tc_eq (k m d : ℕ) : tc d (k + m) m = bpow [1] k ++ bpow (blk m d) 2 := by
  rw [tc, Renormalize.bpow_two, SignedCycles.bpow_singleton, blk, blk,
    ← List.replicate_append_replicate]
  simp only [List.append_assoc]

/-! ## Linear forms -/

/-- **Ellison, linearised.** `2^E e^{-E/10} < 2^p 3^q` forces `85573·E < 100000·p + 158500·q`. -/
lemma lin_of_lt {E p q : ℕ} (hE : 0 < E)
    (h : (2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10) < 2 ^ p * 3 ^ q) :
    85573 * E < 100000 * p + 158500 * q := by
  have hpos : (0 : ℝ) < 2 ^ E * Real.exp (-(E : ℝ) / 10) := by positivity
  have hl := Real.log_lt_log hpos h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow] at hl
  obtain ⟨l3, -⟩ := Repeat.log_three_bounds
  have hl2 := Real.log_two_gt_d9
  have hEr : (0 : ℝ) < E := by exact_mod_cast hE
  have hq : (q : ℝ) * Real.log 3 ≤ q * (1.585 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h10 : (E : ℝ) / 10 < 0.14427 * E * Real.log 2 := by nlinarith
  have key : (0.85573 * E : ℝ) * Real.log 2 < ((p : ℝ) + 1.585 * q) * Real.log 2 := by nlinarith
  have := lt_of_mul_lt_mul_right key (by linarith)
  have : (85573 * E : ℝ) < 100000 * p + 158500 * q := by linarith
  exact_mod_cast this

/-- **Positive sign, linearised.** `3^o < 2^E` forces `1584·o < 1000·E`. -/
lemma pos_sign_linear {E o : ℕ} (h : 3 ^ o < 2 ^ E) : 1584 * o < 1000 * E := by
  by_contra hc
  replace hc := not_lt.mp hc
  have e1 : 2 ^ (1000 * E) ≤ 2 ^ (1584 * o) := Nat.pow_le_pow_right (by norm_num) hc
  have e2 : 3 ^ (1000 * o) < 2 ^ (1000 * E) := by
    rw [mul_comm 1000 o, mul_comm 1000 E, pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left h (by norm_num)
  have e3 : 2 ^ (1584 * o) ≤ 3 ^ (1000 * o) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by decide +kernel) o
  exact absurd (lt_of_lt_of_le e2 (e1.trans e3)) (lt_irrefl _)

/-- `|P - Q| < max P Q` for positive `P, Q`, as two cases. -/
lemma abs_sub_lt_cases {P Q : ℤ} (hP : 0 < P) (hQ : 0 < Q) :
    (Q ≤ P ∧ |P - Q| < P) ∨ (P < Q ∧ |P - Q| < Q) := by
  rcases le_or_gt Q P with h | h
  · left; refine ⟨h, ?_⟩; rw [abs_of_nonneg (by linarith)]; linarith
  · right; refine ⟨h, ?_⟩; rw [abs_of_neg (by linarith)]; linarith

/-! ## The unequal case -/

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Small cases** (`E ≤ 27`): no `1^{k+m} d 1^m d` with `k, m ≥ 1`, `d ≥ 3` satisfies `D ∣ S`. -/
theorem small_check : ∀ k : ℕ, k < 28 → ∀ m : ℕ, m < 28 → ∀ d : ℕ, d < 28 →
    (1 ≤ k ∧ 1 ≤ m ∧ 3 ≤ d ∧ k + 2 * m + 2 * d ≤ 27) →
    Sz (tc d (k + m) m) % Dz (tc d (k + m) m) ≠ 0 := by
  decide +kernel

/-- **No cycle on `1^{a₁} d 1^{a₂} d` with `a₁ ≠ a₂` and `d ≥ 3`**, of either sign, given Ellison. -/
theorem no_cycle_unequal (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {k m d : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hd : 3 ≤ d) (hw : gapWord x o ~r tc d (k + m) m) :
    False := by
  set w := tc d (k + m) m with hw_def
  have hsum : w.sum = k + 2 * m + 2 * d := by rw [tc_sum]; ring
  have hlen : o = k + 2 * m + 2 := by
    have := hw.perm.length_eq; rw [gapWord_length, tc_length] at this; omega
  have hS := dvd_S_of_rotated h hw
  by_cases hE : k + 2 * m + 2 * d ≤ 27
  · exact small_check k (by omega) m (by omega) d (by omega) ⟨hk, hm, hd, hE⟩
      (Int.emod_eq_zero_of_dvd hS)
  replace hE := not_le.mp hE
  -- the two block divisibilities
  have heq := tc_eq k m d
  have hw' : gapWord x o ~r bpow [1] k ++ bpow (blk m d) 2 := heq ▸ hw
  have hne : bpow [1] k ++ bpow (blk m d) 2 ≠ [] := by rw [← heq]; simp [tc]
  have hE0 : (bpow [1] k ++ bpow (blk m d) 2).sum ≠ 0 := by rw [← heq, tc_sum]; omega
  obtain ⟨hV, hU⟩ := dvd_of_cycle_block h hw' hne hE0
  rw [← heq] at hV hU
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  rw [core_blk] at hV hU
  have hDZ2 : Dz (bpow (blk m (j + 1)) 2) = 2 ^ (2 * (m + (j + 1))) - 3 ^ (2 * (m + 1)) := by
    rw [Renormalize.bpow_two]; simp [Dz, D, blk, List.sum_replicate]; ring
  have hD1 : Dz (bpow [1] k) = 2 ^ k - 3 ^ k := by
    rw [SignedCycles.bpow_singleton]; simp [Dz, D, List.sum_replicate]
  rw [hDZ2] at hV
  rw [hD1] at hU
  have hc := isCoprime_six (w := w) (by simp [w, tc]) (by rw [hsum]; omega)
  have strip : ∀ X : ℤ, Dz w ∣ -(2 ^ (m + 1) * (2 ^ j - 1)) * X → Dz w ∣ (2 ^ j - 1) * X := by
    intro X hX
    have : Dz w ∣ 2 ^ (m + 1) * 3 ^ 0 * (-((2 ^ j - 1) * X)) := by
      have e : (2 : ℤ) ^ (m + 1) * 3 ^ 0 * (-((2 ^ j - 1) * X)) =
          -(2 ^ (m + 1) * (2 ^ j - 1)) * X := by ring
      rw [e]; exact hX
    have := CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this
    rwa [dvd_neg] at this
  have hV' := strip _ hV
  have hU' := strip _ hU
  -- sizes
  have hj : (3 : ℤ) ≤ 2 ^ j := by
    have : (2 : ℤ) ^ 2 ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have h23k : (2 : ℤ) ^ k < 3 ^ k := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have hDne : Dz w ≠ 0 := Dz_ne_zero (by simp [w, tc])
  have hU2 : |Dz w| < 2 ^ j * 3 ^ k := by
    have hpos : 0 < (2 ^ j - 1) * (3 ^ k - 2 ^ k : ℤ) := mul_pos (by linarith) (by linarith)
    have hdv : |Dz w| ∣ (2 ^ j - 1) * (3 ^ k - 2 ^ k) := by
      have : (2 ^ j - 1) * (3 ^ k - 2 ^ k : ℤ) = -((2 ^ j - 1) * (2 ^ k - 3 ^ k)) := by ring
      rw [this, dvd_neg]; exact (abs_dvd _ _).2 hU'
    have := Int.le_of_dvd hpos hdv
    have h2 : (0 : ℤ) < 2 ^ k := by positivity
    nlinarith
  set P : ℤ := 2 ^ (2 * (m + (j + 1)))
  set Q : ℤ := 3 ^ (2 * (m + 1))
  have hPQ : P - Q ≠ 0 := by
    intro h0
    have hPe : Even P := by
      simp only [P]; exact (Int.even_pow' (by omega)).2 (by decide)
    have hQo : Odd Q := by simp only [Q]; exact Odd.pow (by decide)
    rw [sub_eq_zero] at h0; rw [h0] at hPe
    exact (Int.not_even_iff_odd.2 hQo) hPe
  have hV2 : |Dz w| ≤ (2 ^ j - 1) * |P - Q| := by
    have hpos : 0 < (2 ^ j - 1) * |P - Q| := mul_pos (by linarith) (abs_pos.2 hPQ)
    have hdv : |Dz w| ∣ (2 ^ j - 1) * |P - Q| := by
      have : (2 ^ j - 1) * |P - Q| = |(2 ^ j - 1) * (P - Q)| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℤ) < 2 ^ j - 1)]
      rw [this]; exact (abs_dvd_abs _ _).2 hV'
    exact Int.le_of_dvd hpos hdv
  -- the cycle's `D` and Ellison
  have hDf : Dz w = 2 ^ (k + 2 * m + 2 * (j + 1)) - 3 ^ o := by
    simp only [Dz, D, hsum, tc_length, hlen, w]
    rw [show k + m + m + 2 = k + 2 * m + 2 by ring]
  have hnot : k + 2 * m + 2 * (j + 1) ∉ CycleLiterature.ellisonExceptions :=
    Frontier.not_mem_exceptions (by omega)
  have hEl' := hEl (k + 2 * m + 2 * (j + 1)) o (by omega) (by omega) hnot
  have hcast : (|Dz w| : ℝ) = |(2 : ℝ) ^ (k + 2 * m + 2 * (j + 1)) - 3 ^ o| := by
    rw [hDf]; push_cast; rfl
  rw [← hcast] at hEl'
  have hI : 85573 * (k + 2 * m + 2 * (j + 1)) < 100000 * j + 158500 * k := by
    refine lin_of_lt (by omega) (hEl'.trans ?_)
    exact_mod_cast hU2
  have hP0 : (0 : ℤ) < P := by positivity
  have hQ0 : (0 : ℤ) < Q := by positivity
  have hII : 85573 * (k + 2 * m + 2 * (j + 1)) < 100000 * (j + 2 * (m + (j + 1))) ∨
      85573 * (k + 2 * m + 2 * (j + 1)) < 100000 * j + 317000 * (m + 1) := by
    rcases abs_sub_lt_cases hP0 hQ0 with ⟨-, hlt⟩ | ⟨-, hlt⟩
    · left
      have hb : |Dz w| < 2 ^ (j + 2 * (m + (j + 1))) * 3 ^ 0 := by
        rw [pow_add, pow_zero, mul_one]
        calc |Dz w| ≤ (2 ^ j - 1) * |P - Q| := hV2
          _ < 2 ^ j * P := by nlinarith [abs_nonneg (P - Q)]
      have := lin_of_lt (q := 0) (by omega) (hEl'.trans (by exact_mod_cast hb))
      omega
    · right
      have hb : |Dz w| < 2 ^ j * 3 ^ (2 * (m + 1)) := by
        calc |Dz w| ≤ (2 ^ j - 1) * |P - Q| := hV2
          _ < 2 ^ j * Q := by nlinarith [abs_nonneg (P - Q)]
      have hb' : |((Dz w : ℤ) : ℝ)| < 2 ^ j * 3 ^ (2 * (m + 1)) := by
        have := (Int.cast_lt (R := ℝ)).2 hb
        push_cast at this; exact this
      have := lin_of_lt (p := j) (q := 2 * (m + 1)) (by omega) (hEl'.trans hb')
      rwa [show 158500 * (2 * (m + 1)) = 317000 * (m + 1) by ring] at this
  -- the sign
  have hsign : (1584 * o < 1000 * (k + 2 * m + 2 * (j + 1)) ∧
      1000 * (k + 2 * m + 2 * (j + 1)) < 1740 * o) ∨
      1000 * (k + 2 * m + 2 * (j + 1)) < 1585 * o := by
    have hsw : (gapWord x o).sum = k + 2 * m + 2 * (j + 1) := by rw [hw.perm.sum_eq, hsum]
    have hDeq : Dz w = Dz (gapWord x o) := by
      obtain ⟨n, hn⟩ := hw; rw [← hn]; exact D_rotate _ _ _ _
    rcases lt_or_gt_of_ne (SignedCycles.ne_zero_of_cycle h) with hneg | hpos
    · right
      have hD := SignedCycles.Dz_neg h hneg
      rw [← hDeq, hDf] at hD
      have h' : (2 : ℤ) ^ (k + 2 * m + 2 * (j + 1)) < 3 ^ o := by linarith
      exact SignedCycles.sign_linear (by exact_mod_cast h')
    · left
      have hD := CycleLiterature.cycle_Dz_pos h hpos
      rw [← hDeq, hDf] at hD
      have hx1 : x ≠ 1 := by
        rintro rfl
        have h1 : 1 ∈ w := by simp [w, tc, blk]; omega
        have := Circuits.gapWord_one o 1 (hw.symm.perm.subset h1)
        omega
      have hsand := Limits.two_pow_mul_three_pow_le h hpos hx1
      rw [hsw] at hsand
      refine ⟨pos_sign_linear ?_, Circuits.sandwich_linear (by omega) hsand⟩
      have h' : (3 : ℤ) ^ o < 2 ^ (k + 2 * m + 2 * (j + 1)) := by linarith
      exact_mod_cast h'
  omega

/-! ## The classification -/

/-- **Equal big gaps.** Given Ellison, the only cycle on `ℤ` whose gap word is a rotation of
`1^{a₁} d 1^{a₂} d` (`a₁, a₂ ≥ 1`, `d ≥ 2`) is `-5 → -7`. -/
theorem equal_two_cycles (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {a₁ a₂ d : ℕ} (h1 : 1 ≤ a₁) (h2 : 1 ≤ a₂) (hd : 2 ≤ d) (hw : gapWord x o ~r tc d a₁ a₂) :
    x = -5 ∨ x = -7 := by
  rcases Nat.lt_or_ge d 3 with hd2 | hd3
  · obtain rfl : d = 2 := by omega
    refine SignedCycles.two_cycle_classification hEl StdPair.base h h1 h2 ?_
    simpa [tc, blk, SignedCycles.bpow_singleton] using hw
  rcases lt_trichotomy a₂ a₁ with hlt | heq | hgt
  · obtain ⟨k, rfl⟩ : ∃ k, a₁ = k + a₂ := ⟨a₁ - a₂, by omega⟩
    exact (no_cycle_unequal hEl h (by omega) h2 hd3 hw).elim
  · subst heq
    have hZpos : Word.Pos (blk a₂ d) := fun e he => by
      simp only [blk, List.mem_append, List.mem_replicate, List.mem_singleton] at he; omega
    have hZ0 : blk a₂ d ≠ [] := by simp [blk]
    have hw2 : gapWord x o ~r bpow (blk a₂ d) 2 := by rwa [Renormalize.bpow_two]
    obtain ⟨Z', hZ'r, hcyc, hgw⟩ := SignedCycles.cycle_of_pow h hZpos hZ0 (by norm_num) hw2
    refine SignedCycles.two_letter_cycles hEl hcyc h2 le_rfl hd ?_
    rw [hgw]
    simpa [two, blk] using hZ'r
  · obtain ⟨k, rfl⟩ : ∃ k, a₂ = k + a₁ := ⟨a₂ - a₁, by omega⟩
    exact (no_cycle_unequal hEl h (by omega) h1 hd3 (hw.trans List.isRotated_append)).elim

/-- A positive word with exactly two gaps `≥ 2` is a rotation of `1^{a₁} d₁ 1^{a₂} d₂`. -/
lemma isRotated_two_blocks {w : Word} (hw : w.Pos) (h2 : CycleLiterature.numBlocks w = 2) :
    ∃ d₁ d₂ a₁ a₂ : ℕ, 2 ≤ d₁ ∧ 2 ≤ d₂ ∧
      w ~r (List.replicate a₁ 1 ++ [d₁]) ++ (List.replicate a₂ 1 ++ [d₂]) := by
  unfold CycleLiterature.numBlocks at h2
  have one_of : ∀ l : Word, (∀ g ∈ l, 1 ≤ g) → l.countP (fun d => decide (2 ≤ d)) = 0 →
      l = List.replicate l.length 1 := by
    intro l hpos hc
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun g hg => ?_⟩
    have := List.countP_eq_zero.1 hc g hg
    have := hpos g hg
    simp at *; omega
  obtain ⟨d, hdw, hd⟩ := List.countP_pos_iff.1 (by omega : 0 < w.countP fun d => decide (2 ≤ d))
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hdw
  have hd2 : 2 ≤ d := by simpa using hd
  rw [List.countP_append, List.countP_cons] at h2
  simp only [hd2, decide_true, ite_true] at h2
  set L := l₂ ++ l₁ with hL
  have hLc : L.countP (fun d => decide (2 ≤ d)) = 1 := by rw [hL, List.countP_append]; omega
  have hLpos : ∀ g ∈ L, 1 ≤ g := fun g hg => hw g (by
    simp only [hL, List.mem_append] at hg; simp only [List.mem_append, List.mem_cons]; tauto)
  obtain ⟨e, heL, he⟩ := List.countP_pos_iff.1 (by omega : 0 < L.countP fun d => decide (2 ≤ d))
  obtain ⟨p, q, hpq⟩ := List.append_of_mem heL
  have he2 : 2 ≤ e := by simpa using he
  rw [hpq, List.countP_append, List.countP_cons] at hLc
  simp only [he2, decide_true, ite_true] at hLc
  have ep := one_of p (fun g hg => hLpos g (by rw [hpq]; simp [hg])) (by omega)
  have eq := one_of q (fun g hg => hLpos g (by rw [hpq]; simp [hg])) (by omega)
  refine ⟨e, d, p.length, q.length, he2, hd2, ?_⟩
  have hrot : (l₁ ++ d :: l₂) ~r (l₂ ++ l₁ ++ [d]) := by
    have := List.isRotated_append (l := l₁ ++ [d]) (l' := l₂)
    simpa [List.append_assoc] using this
  have heq : l₂ ++ l₁ ++ [d] = (List.replicate p.length 1 ++ [e]) ++ (List.replicate q.length 1 ++ [d]) := by
    rw [← ep, ← eq, ← hL, hpq]; simp [List.append_assoc]
  exact heq ▸ hrot

/-- **Two big gaps, equal.** Given Ellison, every cycle on `ℤ` whose gap word has exactly two gaps
`≥ 2`, both equal, is the cycle through `1` or `-5 → -7`. -/
theorem equal_two_blocks (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (h2 : CycleLiterature.numBlocks (gapWord x o) = 2)
    (heq : ∀ d ∈ gapWord x o, ∀ e ∈ gapWord x o, 2 ≤ d → 2 ≤ e → d = e) :
    x = 1 ∨ x = -5 ∨ x = -7 := by
  obtain ⟨d₁, d₂, a₁, a₂, hd₁, hd₂, hrot⟩ := isRotated_two_blocks (CocycleCombine.IsSyrCycle.pos h) h2
  have hmem : ∀ g ∈ (List.replicate a₁ 1 ++ [d₁]) ++ (List.replicate a₂ 1 ++ [d₂]), g ∈ gapWord x o :=
    fun g hg => hrot.symm.perm.subset hg
  obtain rfl : d₁ = d₂ := heq d₁ (hmem d₁ (by simp)) d₂ (hmem d₂ (by simp)) hd₁ hd₂
  rcases Nat.eq_zero_or_pos a₁ with ha₁ | ha₁ <;> rcases Nat.eq_zero_or_pos a₂ with ha₂ | ha₂
  · -- `d d`: a power of the one-letter circuit `d`
    subst ha₁ ha₂
    have hw2 : gapWord x o ~r bpow [d₁] 2 := by simpa [Renormalize.bpow_two] using hrot
    obtain ⟨Z', hZ'r, hcyc, hgw⟩ := SignedCycles.cycle_of_pow h (fun e he => by simp at he; omega)
      (by simp) (by norm_num) hw2
    have hZ' : Z' = [d₁] := by
      obtain ⟨n, hn⟩ := hZ'r.symm; rw [← hn]; simp
    subst hZ'
    have hb : CycleLiterature.numBlocks (gapWord x [d₁].length) ≤ 1 := by
      rw [hgw]; simp [CycleLiterature.numBlocks, hd₁]
    rcases SignedCycles.few_blocks_cycles hEl hcyc hb with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exfalso; subst h1
      have := CycleLiterature.isSyrCycle_neg_one.2
      simp only [List.length_singleton] at hgw
      rw [this] at hgw; simp at hgw; omega
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · -- `d 1^{a₂} d`: two letter runs `1^{a₂} d²`
    subst ha₁
    have hw' : gapWord x o ~r two 1 d₁ a₂ 2 := by
      refine hrot.trans ?_
      have := List.isRotated_append (l := [d₁]) (l' := List.replicate a₂ 1 ++ [d₁])
      simpa [two, List.append_assoc, List.replicate_succ] using this
    have := SignedCycles.two_letter_cycles hEl h ha₂ (by norm_num) hd₁ hw'
    tauto
  · -- `1^{a₁} d d`: two letter runs `1^{a₁} d²`
    subst ha₂
    have hw' : gapWord x o ~r two 1 d₁ a₁ 2 := by
      simpa [two, List.append_assoc, List.replicate_succ] using hrot
    have := SignedCycles.two_letter_cycles hEl h ha₁ (by norm_num) hd₁ hw'
    tauto
  · have := equal_two_cycles hEl h ha₁ ha₂ hd₁ hrot
    tauto

/-! ## The enlarged statement -/

/-- The closed classes of `SignedCycles`, together with the two-block words whose big gaps are equal. -/
def ClosedClass₂ (w : Word) : Prop :=
  SignedCycles.ClosedClass w ∨
    (CycleLiterature.numBlocks w = 2 ∧ ∀ d ∈ w, ∀ e ∈ w, 2 ≤ d → 2 ≤ e → d = e)

/-- **The enlarged closed classes on `ℤ`.** Given Ellison, every cycle whose gap word lies in
`ClosedClass₂` is the cycle through `1`, `-1`, `-5` or `-7`. -/
theorem closed_classes₂ (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hc : ClosedClass₂ (gapWord x o)) : x = 1 ∨ x = -1 ∨ x = -5 ∨ x = -7 := by
  rcases hc with hc | ⟨h2, heq⟩
  · exact SignedCycles.closed_classes hEl h hc
  · have := equal_two_blocks hEl h h2 heq; tauto

/-- **`-17` is still outside.** Among the two-block cycles, equal big gaps are closed; `-17`, with big
gaps `2` and `4`, is the smallest cycle with distinct ones. -/
theorem neg_seventeen_outside₂ (hEl : CycleLiterature.Ellison1971) :
    ¬ ClosedClass₂ (gapWord (-17) 7) := by
  intro hc
  have := closed_classes₂ hEl CycleLiterature.isSyrCycle_neg_seventeen.1 hc
  omega

end Syracuse.EqualTwoCycles
