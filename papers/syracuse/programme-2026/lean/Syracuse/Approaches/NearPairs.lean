import Syracuse.Approaches.EqualTwoCycles

/-!
# Two runs over the near-standard pairs `(1, 1^m d)`

`EqualTwoCycles` re-bracketed `1^{k+m} d 1^m d` as `1^k (1^m d)²`. Here the exponent of the block
`Z = 1^m d` is arbitrary. The family

`1^k (1^m d)^b`   (`k ≥ 1`, `m ≥ 0`, `b ≥ 1`, `d ≥ 2`)

consists of the equal-big-gap words `1^{a₁} d ⋯ 1^{a_b} d` in which every run of `1`s has the same length
`m`, except one longer run. On all of `ℤ`, given Ellison only, its only cycle is `-5 → -7`
(`near_pair_cycles`). Its special cases are:

* `m = 0`: two letter runs `1^k d^b` (`SignedCycles.two_letter_cycles`);
* `d = 2`: `(1, 1^m 2)` is a standard pair (`StdClass.std_pair_cycles`);
* `b = 1`: a circuit `1^{k+m} d`;
* `b = 2`: `EqualTwoCycles.no_cycle_unequal`, which needed the sign bound;
* `b ≥ 3`, `m ≥ 1`, `d ≥ 3`: new here (`no_cycle_near`). **Ellison alone suffices**: no sign bound and no
  window. The core `C(1, Z) = -2^{m+1}(2^{d-1} - 1)` gives `D ∣ (2^{d-1} - 1)(2^k - 3^k)` and
  `D ∣ (2^{d-1} - 1)(2^{b(m+d)} - 3^{b(m+1)})`. With Ellison, the first forces `k` large against
  `b(m+d)`. The second forces it small once `b(m+d) ≥ 3(d+1)`, or, in the other size case, once
  `b(d-1) ≥ 3(d-1)`.

The cases `E ≤ 27` are a kernel check (`small_check`).

**What stays open among equal big gaps.** Three blocks `1^{a₁} d 1^{a₂} d 1^{a₃} d` are in the family
when two runs are equal and the third is longer. When the odd run is *shorter*,
`1^M d (1^m d)²` with `M < m` re-brackets to `1^c Z 1^c Z²` over `(1, 1^M d)`, `c = m - M`. That is
two blocks at level `(1, Z)` with distinct big letters `Z` and `Z²`, the analogue of `-17`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| sums and lengths of `1^k (1^m d)^b` | `nw_sum`, `nw_length` | proved |
| no `1^k (1^m d)^b` (`b, d ≥ 3`, `k, m ≥ 1`, `E ≤ 27`) has `D ∣ S` | `small_check` | proved (`decide +kernel`) |
| no cycle (either sign) on `1^k (1^m d)^b`, `b ≥ 3`, `d ≥ 3`, `k, m ≥ 1` | `no_cycle_near` | proved (conditional on `Ellison1971`) |
| the only cycle on `1^k (1^m d)^b` (`k, b ≥ 1`, `d ≥ 2`) is `-5 → -7` | `near_pair_cycles` | proved (conditional on `Ellison1971`) |
| the closed classes enlarged by this family: only `1, -1, -5, -7`; `-17` outside | `closed_classes₃`, `neg_seventeen_outside₃` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.NearPairs

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs Syracuse.EqualTwoCycles

/-- The word `1^k (1^m d)^b`. -/
abbrev nw (k m d b : ℕ) : Word := bpow [1] k ++ bpow (blk m d) b

lemma bpow_blk_sum (m d b : ℕ) : (bpow (blk m d) b).sum = b * (m + d) := by
  simp [bpow, CocycleCombine.wpow_sum, blk, List.sum_replicate]

lemma bpow_blk_length (m d b : ℕ) : (bpow (blk m d) b).length = b * (m + 1) := by
  simp [bpow, CocycleCombine.wpow_length, blk]

lemma nw_sum (k m d b : ℕ) : (nw k m d b).sum = k + b * (m + d) := by
  rw [nw, List.sum_append, bpow_blk_sum, SignedCycles.bpow_singleton]; simp [List.sum_replicate]

lemma nw_length (k m d b : ℕ) : (nw k m d b).length = k + b * (m + 1) := by
  rw [nw, List.length_append, bpow_blk_length, SignedCycles.bpow_singleton, List.length_replicate]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Small cases** (`E ≤ 27`): no `1^k (1^m d)^b` with `k, m ≥ 1` and `b, d ≥ 3` satisfies `D ∣ S`. -/
theorem small_check : ∀ k : ℕ, k < 16 → ∀ m : ℕ, m < 7 → ∀ d : ℕ, d < 10 → ∀ b : ℕ, b < 7 →
    (1 ≤ k ∧ 1 ≤ m ∧ 3 ≤ d ∧ 3 ≤ b ∧ k + b * (m + d) ≤ 27) →
    Sz (nw k m d b) % Dz (nw k m d b) ≠ 0 := by
  decide +kernel

/-- **No cycle on `1^k (1^m d)^b`** with `b ≥ 3`, `d ≥ 3`, `k, m ≥ 1`, of either sign, given Ellison. -/
theorem no_cycle_near (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {k m d b : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hd : 3 ≤ d) (hb : 3 ≤ b)
    (hw : gapWord x o ~r nw k m d b) : False := by
  set w := nw k m d b with hw_def
  have hsum : w.sum = k + b * (m + d) := nw_sum k m d b
  have hlen : o = k + b * (m + 1) := by
    have := hw.perm.length_eq; rw [gapWord_length, nw_length] at this; exact this
  have hS := dvd_S_of_rotated h hw
  have h3 : 3 * (m + d) ≤ b * (m + d) := Nat.mul_le_mul_right _ hb
  by_cases hE : k + b * (m + d) ≤ 27
  · have h4 : b * 4 ≤ b * (m + d) := Nat.mul_le_mul_left _ (by omega)
    exact small_check k (by omega) m (by omega) d (by omega) b (by omega) ⟨hk, hm, hd, hb, by omega⟩
      (Int.emod_eq_zero_of_dvd hS)
  replace hE := not_le.mp hE
  -- the two block divisibilities
  have hne : w ≠ [] := by
    intro h0; have := congrArg List.sum h0; rw [hsum] at this; simp at this; omega
  have hE0 : w.sum ≠ 0 := by rw [hsum]; omega
  obtain ⟨hV, hU⟩ := dvd_of_cycle_block h hw hne hE0
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  rw [core_blk] at hV hU
  have hDZb : Dz (bpow (blk m (j + 1)) b) = 2 ^ (b * (m + (j + 1))) - 3 ^ (b * (m + 1)) := by
    simp only [Dz, D, bpow_blk_sum, bpow_blk_length]
  have hD1 : Dz (bpow [1] k) = 2 ^ k - 3 ^ k := by
    rw [SignedCycles.bpow_singleton]; simp [Dz, D, List.sum_replicate]
  rw [hDZb] at hV
  rw [hD1] at hU
  have hc := isCoprime_six hne hE0
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
  have hU2 : |Dz w| < 2 ^ j * 3 ^ k := by
    have hpos : 0 < (2 ^ j - 1) * (3 ^ k - 2 ^ k : ℤ) := mul_pos (by linarith) (by linarith)
    have hdv : |Dz w| ∣ (2 ^ j - 1) * (3 ^ k - 2 ^ k) := by
      have : (2 ^ j - 1) * (3 ^ k - 2 ^ k : ℤ) = -((2 ^ j - 1) * (2 ^ k - 3 ^ k)) := by ring
      rw [this, dvd_neg]; exact (abs_dvd _ _).2 hU'
    have := Int.le_of_dvd hpos hdv
    have h2 : (0 : ℤ) < 2 ^ k := by positivity
    nlinarith
  set P : ℤ := 2 ^ (b * (m + (j + 1)))
  set Q : ℤ := 3 ^ (b * (m + 1))
  have hPQ : P - Q ≠ 0 := by
    intro h0
    have hPe : Even P := by
      simp only [P]; exact (Int.even_pow' (by positivity)).2 (by decide)
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
  have hDf : Dz w = 2 ^ (k + b * (m + (j + 1))) - 3 ^ o := by
    simp only [Dz, D, hsum, nw_length, hlen, w]
  have hnot : k + b * (m + (j + 1)) ∉ CycleLiterature.ellisonExceptions :=
    Frontier.not_mem_exceptions (by omega)
  have hEl' := hEl (k + b * (m + (j + 1))) o (by omega) (by rw [hlen]; omega) hnot
  have hcast : (|Dz w| : ℝ) = |(2 : ℝ) ^ (k + b * (m + (j + 1))) - 3 ^ o| := by
    rw [hDf]; push_cast; rfl
  rw [← hcast] at hEl'
  have hI : 85573 * (k + b * (m + (j + 1))) < 100000 * j + 158500 * k := by
    refine lin_of_lt (by omega) (hEl'.trans ?_)
    exact_mod_cast hU2
  have hP0 : (0 : ℤ) < P := by positivity
  have hQ0 : (0 : ℤ) < Q := by positivity
  have hII : 85573 * (k + b * (m + (j + 1))) < 100000 * (j + b * (m + (j + 1))) ∨
      85573 * (k + b * (m + (j + 1))) < 100000 * j + 158500 * (b * (m + 1)) := by
    rcases abs_sub_lt_cases hP0 hQ0 with ⟨-, hlt⟩ | ⟨-, hlt⟩
    · left
      have hb' : |Dz w| < 2 ^ (j + b * (m + (j + 1))) * 3 ^ 0 := by
        rw [pow_add, pow_zero, mul_one]
        calc |Dz w| ≤ (2 ^ j - 1) * |P - Q| := hV2
          _ < 2 ^ j * P := by nlinarith [abs_nonneg (P - Q)]
      have hbr : |((Dz w : ℤ) : ℝ)| < 2 ^ (j + b * (m + (j + 1))) * 3 ^ 0 := by
        have := (Int.cast_lt (R := ℝ)).2 hb'
        push_cast at this; exact this
      have := lin_of_lt (p := j + b * (m + (j + 1))) (q := 0) (by omega) (hEl'.trans hbr)
      rwa [mul_zero, add_zero] at this
    · right
      have hb' : |Dz w| < 2 ^ j * 3 ^ (b * (m + 1)) := by
        calc |Dz w| ≤ (2 ^ j - 1) * |P - Q| := hV2
          _ < 2 ^ j * Q := by nlinarith [abs_nonneg (P - Q)]
      have hbr : |((Dz w : ℤ) : ℝ)| < 2 ^ j * 3 ^ (b * (m + 1)) := by
        have := (Int.cast_lt (R := ℝ)).2 hb'
        push_cast at this; exact this
      exact lin_of_lt (p := j) (q := b * (m + 1)) (by omega) (hEl'.trans hbr)
  -- linear arithmetic with the products as atoms
  have hsplit : b * (m + (j + 1)) = b * (m + 1) + b * j := by ring
  have hT : 3 * j ≤ b * j := Nat.mul_le_mul_right _ hb
  have hPl : 3 * (m + (j + 1)) ≤ b * (m + (j + 1)) := Nat.mul_le_mul_right _ hb
  generalize b * (m + (j + 1)) = P' at hI hII hsplit hPl
  generalize b * (m + 1) = R' at hII hsplit
  generalize b * j = T' at hsplit hT
  omega

/-! ## The classification -/

/-- **Two runs over `(1, 1^m d)`.** Given Ellison, the only cycle on `ℤ` whose gap word is a rotation
of `1^k (1^m d)^b` (`k, b ≥ 1`, `m ≥ 0`, `d ≥ 2`) is `-5 → -7`. -/
theorem near_pair_cycles (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {k m d b : ℕ} (hk : 1 ≤ k) (hb : 1 ≤ b) (hd : 2 ≤ d) (hw : gapWord x o ~r nw k m d b) :
    x = -5 ∨ x = -7 := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · -- two letter runs `1^k d^b`
    subst hm0
    refine SignedCycles.two_letter_cycles hEl h hk hb hd ?_
    simpa [nw, blk, SignedCycles.bpow_singleton, two] using hw
  rcases Nat.lt_or_ge d 3 with hd2 | hd3
  · -- `d = 2`: the standard pair `(1, 1^m 2)`
    obtain rfl : d = 2 := by omega
    have hst : StdPair [1] (blk m 2) := by
      simpa [SignedCycles.bpow_singleton, blk] using Renormalize.stdPair_left_pow StdPair.base m
    exact StdClass.std_pair_cycles hEl hst h hk hb hw
  rcases Nat.lt_or_ge b 3 with hb2 | hb3
  · rcases Nat.lt_or_ge b 2 with hb1 | hb2'
    · -- `b = 1`: the circuit `1^{k+m} d`
      obtain rfl : b = 1 := by omega
      refine SignedCycles.two_letter_cycles (a := k + m) (b := 1) hEl h (by omega) le_rfl hd ?_
      have e : nw k m d 1 = two 1 d (k + m) 1 := by
        rw [nw, Renormalize.bpow_one, SignedCycles.bpow_singleton, two,
          ← List.replicate_append_replicate, List.replicate_one, blk, List.append_assoc]
      rwa [e] at hw
    · -- `b = 2`: `EqualTwoCycles`
      obtain rfl : b = 2 := by omega
      exact (no_cycle_unequal hEl h hk hm hd3 (by rw [tc_eq]; exact hw)).elim
  · exact (no_cycle_near hEl h hk hm hd3 hb3 hw).elim

/-! ## The enlarged statement -/

/-- `ClosedClass₂` together with the family `1^k (1^m d)^b`. -/
def ClosedClass₃ (w : Word) : Prop :=
  ClosedClass₂ w ∨ ∃ k m d b : ℕ, 1 ≤ k ∧ 1 ≤ b ∧ 2 ≤ d ∧ w ~r nw k m d b

/-- **The closed classes on `ℤ`, third enlargement.** Given Ellison, every cycle whose gap word lies
in `ClosedClass₃` is the cycle through `1`, `-1`, `-5` or `-7`. -/
theorem closed_classes₃ (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hc : ClosedClass₃ (gapWord x o)) : x = 1 ∨ x = -1 ∨ x = -5 ∨ x = -7 := by
  rcases hc with hc | ⟨k, m, d, b, hk, hb, hd, hw⟩
  · exact closed_classes₂ hEl h hc
  · have := near_pair_cycles hEl h hk hb hd hw; tauto

/-- **`-17` is still outside.** -/
theorem neg_seventeen_outside₃ (hEl : CycleLiterature.Ellison1971) :
    ¬ ClosedClass₃ (gapWord (-17) 7) := by
  intro hc
  have := closed_classes₃ hEl CycleLiterature.isSyrCycle_neg_seventeen.1 hc
  omega

end Syracuse.NearPairs
