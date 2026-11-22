import Syracuse.Approaches.MRunsDichotomy

/-!
# Every number of runs, with Rhin's bound

Ellison's separation exponent `θ_E ≈ 0.856` exceeds the reach `c_m` only for `m ≤ 3`. Rhin's bound, as
Simons–de Weger's Lemma 12 for nontrivial positive cycles, loses only `o^{13.3}`:

`|D| ≥ 2^{max(E, o log₂3) - 10 - 14ℓ}`, `ℓ = ⌊log₂ o⌋ + 1` (`rhin_sep`).

This is a separation with `θ = 1 > c_m` for **every** `m`. So (`mruns_rhin`):

> Given Lemma 12, a nontrivial positive cycle on `p₀^{a₀} ⋯ p_{m-1}^{a_{m-1}}` (`m ≥ 1`, positive nonempty
> base blocks of total weight `B`) either has an orbit point on a base block's cycle, or satisfies
> `max(E, o log₂3)/σ_m ≤ 6B + 11 + 14ℓ + log₂ m`, `σ_m = Σ_{i<m} (log₂3)^i`.

With Barina and Hercher (`E > o > 1.375·10^{11}`), the logarithm is absorbed by a linear bound
(`log_lin`), giving a frontier for each `m` (`frontier_rhin`). Two instances (`frontier_ten`,
`frontier_twenty`):

> No nontrivial positive cycle is a word of at most `10` runs over base blocks of total weight `≤ 5·10^7`,
> nor of at most `20` runs over base weight `≤ 6·10^5`.

The cost grows like `σ_m ≈ (log₂3)^m / 0.585`, so the admissible base weight shrinks geometrically in `m`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| Rhin as a separation `|D| ≥ 2^{max - 10 - 14ℓ}` | `rhin_sep` | proved (conditional on `SimonsDeWegerLemma12`) |
| **all-`m` dichotomy** | `mruns_rhin` | proved (conditional on `SimonsDeWegerLemma12`) |
| `c (⌊log₂ o⌋ + 1) ≤ o + c (2⌊log₂ c⌋ + 6)` | `log_lin` | proved |
| frontier for each `m` under a numerical condition | `frontier_rhin` | proved (conditional on Lemma 12 + Barina + Hercher Cor. 29) |
| `≤ 10` runs, `B ≤ 5·10^7`; `≤ 20` runs, `B ≤ 6·10^5` | `frontier_ten`, `frontier_twenty` | proved (same) |
| the same for any cycle bounds with `NE ≤ 12 No` and any base-weight cap | `frontier_rhin_of`, `frontier_ten_of`, `frontier_twenty_of` | proved (Barina-only instances in `BarinaFrontier`) |
-/

namespace Syracuse.MRunsRhin

open Finset Syracuse.MRuns Syracuse.MRunsExplicit Syracuse.MRunsDichotomy

/-- **Rhin as a separation**, for nontrivial positive cycles. -/
theorem rhin_sep (hR : CycleLiterature.SimonsDeWegerLemma12) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hx : 0 < x) (hx1 : x ≠ 1) :
    (2 : ℝ) ^ (1 * max ((gapWord x o).sum : ℝ) (Real.logb 2 3 * o) -
        (10 + 14 * ((Nat.log 2 o + 1 : ℕ) : ℝ))) ≤ |((Dz (gapWord x o) : ℤ) : ℝ)| := by
  set E := (gapWord x o).sum
  set ℓ := Nat.log 2 o + 1
  have ho : 1 ≤ o := h.1
  have hDpos := CycleLiterature.cycle_Dz_pos h hx
  have hDf : ((Dz (gapWord x o) : ℤ) : ℝ) = (2 : ℝ) ^ E - 3 ^ o := by
    simp [Dz, D, E, gapWord_length]
  have hDr : (0 : ℝ) < (2 : ℝ) ^ E - 3 ^ o := by rw [← hDf]; exact_mod_cast hDpos
  rw [hDf, abs_of_pos hDr, one_mul]
  have hrh := CycleLiterature.sdw12_Dz_gt hR h hx hx1
  rw [hDf] at hrh
  have hrp := FourRuns.rhin_pow ho
  -- `3^o < 2^{9+14ℓ}·D`
  have h3 : (0 : ℝ) < 3 ^ o := by positivity
  have hR3 : (3 : ℝ) ^ o < 2 ^ (9 + 14 * ℓ) * ((2 : ℝ) ^ E - 3 ^ o) := by
    calc (3 : ℝ) ^ o ≤ 3 ^ o * (2 ^ (9 + 14 * ℓ) * Real.exp (-13.3 * (0.46057 + Real.log o))) :=
          le_mul_of_one_le_right h3.le hrp
      _ = 2 ^ (9 + 14 * ℓ) * (3 ^ o * Real.exp (-13.3 * (0.46057 + Real.log o))) := by ring
      _ < 2 ^ (9 + 14 * ℓ) * ((2 : ℝ) ^ E - 3 ^ o) := mul_lt_mul_of_pos_left hrh (by positivity)
  have e3 : (3 : ℝ) ^ o = (2 : ℝ) ^ (Real.logb 2 3 * o) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_natCast]
  have e2 : (2 : ℝ) ^ E = (2 : ℝ) ^ (E : ℝ) := (Real.rpow_natCast 2 E).symm
  set lo := Real.logb 2 3 * o
  have mono : ∀ a b : ℝ, a ≤ b → (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
    fun a b hab => Real.rpow_le_rpow_of_exponent_le (by norm_num) hab
  have eL : (2 : ℝ) ^ ((9 + 14 * ℓ : ℕ) : ℝ) = 2 ^ (9 + 14 * ℓ) := Real.rpow_natCast 2 _
  by_cases A : 2 * (3 : ℝ) ^ o ≤ 2 ^ E
  · have hlo : lo ≤ E := by
      have : (2 : ℝ) ^ lo ≤ 2 ^ (E : ℝ) := by rw [← e3, ← e2]; linarith
      exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 this
    rw [max_eq_left hlo]
    calc (2 : ℝ) ^ ((E : ℝ) - (10 + 14 * ((ℓ : ℕ) : ℝ))) ≤ (2 : ℝ) ^ ((E : ℝ) - 1) :=
          mono _ _ (by have : (0 : ℝ) ≤ ((ℓ : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
      _ = 2 ^ E / 2 := by rw [Real.rpow_sub (by norm_num), Real.rpow_one, ← e2]
      _ ≤ 2 ^ E - 3 ^ o := by linarith
  · push_neg at A
    have hlo : (E : ℝ) < lo + 1 := by
      have : (2 : ℝ) ^ (E : ℝ) < 2 ^ (lo + 1) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one, ← e3, ← e2]; linarith
      exact (Real.rpow_lt_rpow_left_iff (by norm_num)).1 this
    have hmax : max (E : ℝ) lo ≤ lo + 1 := max_le hlo.le (by linarith)
    calc (2 : ℝ) ^ (max (E : ℝ) lo - (10 + 14 * ((ℓ : ℕ) : ℝ)))
        ≤ (2 : ℝ) ^ (lo - ((9 + 14 * ℓ : ℕ) : ℝ)) := mono _ _ (by push_cast; linarith)
      _ = 3 ^ o / 2 ^ (9 + 14 * ℓ) := by rw [Real.rpow_sub (by norm_num), ← e3, eL]
      _ ≤ 2 ^ E - 3 ^ o := by
          rw [div_le_iff₀ (by positivity)]; linarith [hR3]

/-- **All-`m` dichotomy**, given Rhin (Simons–de Weger Lemma 12). -/
theorem mruns_rhin (hR : CycleLiterature.SimonsDeWegerLemma12) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hx : 0 < x) (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    (hrot : gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) :
    (∃ R : ℕ, ∃ y : ℤ, IsSyrCycle y o ∧ (∃ j, y = syr^[j] x) ∧ Dz (p R) * y = Sz (p R)) ∨
      (1 / Reach.σ (Real.logb 2 3) m) *
        max ((cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum : ℝ)
          (Real.logb 2 3 * (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length) ≤
        (6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) + (10 + 14 * ((Nat.log 2 o + 1 : ℕ) : ℝ)) +
          Real.logb 2 m := by
  set Q : ℕ → Word := fun i => TwoBackground.bpow (p i) (a i)
  have hQ : ∀ i, Q (i + m) = Q i := fun i => by simp only [Q, hp, ha]
  have hQpos : ∀ i, (Q i).Pos := fun i => StdPairs.pos_bpow (hpos i) (a i)
  by_cases hall : ∀ R, T (2 : ℤ) 3 (fun k => Q (R + k)) (fun k => Acoef p m (R + k)) m ≠ 0
  · right
    have hm2 : 2 ≤ m := by
      by_contra hc
      obtain rfl : m = 1 := by omega
      apply hall 0
      simp [T, Nat.mod_one]
    -- the separation, transferred to `cat Q m`
    have hsep := rhin_sep hR h hx hx1
    have hsum : (gapWord x o).sum = (cat Q m).sum := hrot.perm.sum_eq
    have hlen : o = (cat Q m).length := by rw [← hrot.perm.length_eq, gapWord_length]
    have hDeq : Dz (gapWord x o) = Dz (cat Q m) := by
      simp only [Dz, D]; rw [hsum, hrot.perm.length_eq]
    rw [hsum, hDeq] at hsep
    rw [hlen] at hsep
    have hb := mruns_bounded h hm hQ hQpos hne' hrot (fun i => Acoef_spec (a := a) hm hp i)
      (Acoef_period hp) (Acoef_diff_le hm2 hp hpos) hall hsep
    have hσ : (1 : ℝ) - (1 - 1 / Reach.σ (Real.logb 2 3) m) = 1 / Reach.σ (Real.logb 2 3) m := by ring
    rw [hσ] at hb
    rw [← hlen] at hb
    rw [← hlen]
    exact hb
  · left
    push_neg at hall
    obtain ⟨R, hR'⟩ := hall
    have hrotR : gapWord x o ~r cat (fun k => Q (R + k)) m := hrot.trans (rot_cat Q hm hQ R).symm
    exact ⟨R, T_zero_alt h hm hp hne hne' R hrotR hR'⟩

/-- **A linear bound on `⌊log₂ o⌋`.** `c·(⌊log₂ o⌋ + 1) ≤ o + c·(2⌊log₂ c⌋ + 6)`. -/
lemma log_lin (c o : ℕ) (ho : 1 ≤ o) : c * (Nat.log 2 o + 1) ≤ o + c * (2 * Nat.log 2 c + 6) := by
  set n := Nat.log 2 o
  set L := Nat.log 2 c
  have hpo : 2 ^ n ≤ o := Nat.pow_log_le_self 2 (by omega)
  rcases Nat.lt_or_ge n (2 * L + 6) with hn | hn
  · have : c * (n + 1) ≤ c * (2 * L + 6) := Nat.mul_le_mul_left c (by omega)
    omega
  · -- `c < 2^{L+1}` and `n + 1 ≤ 2^{n-L-1}`
    have hc : c < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) c
    set k := n - L - 1
    have hk : n = k + L + 1 := by omega
    have h2k : ∀ t : ℕ, 2 * t ≤ 2 ^ t ∨ t = 0 := by
      intro t
      induction t with
      | zero => right; rfl
      | succ t ih =>
        left
        rcases ih with ih | ih
        · rw [pow_succ]
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · subst h0; norm_num
          · have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
            omega
        · subst ih; norm_num
    have hk2 : n + 1 ≤ 2 ^ k := by
      rcases h2k k with h | h
      · omega
      · omega
    have : c * (n + 1) ≤ 2 ^ (L + 1) * 2 ^ k := Nat.mul_le_mul hc.le hk2
    rw [← pow_add, show L + 1 + k = n by omega] at this
    omega

/-- **Frontier for `m` runs, given Rhin, for any cycle bounds** `CycleBounds No NE` with
`NE ≤ 12 No`, under a numerical condition. -/
theorem frontier_rhin_of (hR : CycleLiterature.SimonsDeWegerLemma12) {No NE : ℕ}
    (hCB : CycleLength.CycleBounds No NE) (hNo : NE ≤ 12 * No)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    {c : ℕ} (hc : 28 * Reach.σ (Real.logb 2 3) m ≤ c)
    (hsmall : 2 * Reach.σ (Real.logb 2 3) m * (((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 +
      14 * ((2 * Nat.log 2 c + 6 : ℕ) : ℝ) + Real.logb 2 m) < NE) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) := by
  intro hrot
  set B := ∑ k ∈ range m, (p k).sum
  set σ := Reach.σ (Real.logb 2 3) m
  have hlam1 : 1 ≤ Real.logb 2 3 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
  have hσ1 : 1 ≤ σ := by
    have : (∑ i ∈ range 1, Real.logb 2 3 ^ i) ≤ σ :=
      sum_le_sum_of_subset_of_nonneg (range_mono hm)
        (fun i _ _ => pow_nonneg (by linarith) i)
    simpa using this
  have hlogm : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  have hE := (hCB x o hx h hx1).2
  rcases mruns_rhin hR h hx hx1 hm hp ha hpos hne hne' hrot with ⟨R, y, hy, ⟨j, rfl⟩, hDy⟩ | hb
  · -- a base block's cycle has period `≤ B < NE/12 ≤ No`
    have hy0 : 0 < syr^[j] x := CycleLiterature.syr_iterate_pos hx j
    have hdvd : Dz (p R) ∣ Sz (p R) := ⟨_, hDy.symm⟩
    obtain ⟨hcyc, -⟩ := CycleLiterature.isSyrCycle_of_dvd (hpos R) (hne R) hdvd
    have hval : Sz (p R) / Dz (p R) = syr^[j] x := by
      rw [← hDy, Int.mul_ediv_cancel_left _ (StdPairs.Dz_ne_zero (hne R))]
    rw [hval] at hcyc
    have hy1 : syr^[j] x ≠ 1 := by
      intro h1
      have hfix : ∀ t, syr^[t] (1 : ℤ) = 1 := fun t =>
        Function.iterate_fixed CycleLiterature.gap_syr_one.2 t
      have hback : syr^[o * (j + 1) - j] (syr^[j] x) = x := by
        rw [← Function.iterate_add_apply, show o * (j + 1) - j + j = o * (j + 1) by
          have : j ≤ o * (j + 1) := by nlinarith [h.1]
          omega]
        rw [Function.iterate_mul]
        exact Function.iterate_fixed h.2.2 _
      rw [h1, hfix] at hback
      exact hx1 hback.symm
    have hper := (hCB _ _ hy0 hcyc hy1).1
    have hlen : (p R).length ≤ (p R).sum := CycleLiterature.length_le_sum (hpos R)
    have hsumR : (p R).sum ≤ B := by
      rw [p_mod hm hp R]
      exact single_le_sum (f := fun k => (p k).sum) (fun _ _ => Nat.zero_le _)
        (mem_range.2 (Nat.mod_lt _ (by omega)))
    have hBr : (B : ℝ) < NE / 12 := by
      have h6 : (6 * (B : ℝ)) ≤ ((6 * B + 1 : ℕ) : ℝ) := by push_cast; linarith
      have h14 : (0 : ℝ) ≤ 14 * ((2 * Nat.log 2 c + 6 : ℕ) : ℝ) := by positivity
      nlinarith
    have : ((12 * B : ℕ) : ℝ) < NE := by push_cast; linarith
    have : 12 * B < NE := by exact_mod_cast this
    omega
  · -- the bound
    set M := max ((cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum : ℝ)
      (Real.logb 2 3 * (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length)
    rw [hrot.perm.sum_eq] at hE
    have hMo : (o : ℝ) ≤ M := by
      have hl : o = (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length := by
        rw [← hrot.perm.length_eq, gapWord_length]
      have hle := CycleLiterature.length_le_sum (CocycleCombine.IsSyrCycle.pos h)
      rw [gapWord_length, hrot.perm.sum_eq] at hle
      exact le_trans (by exact_mod_cast hle) (le_max_left _ _)
    have hME : (NE : ℝ) < M := lt_of_lt_of_le (by exact_mod_cast hE) (le_max_left _ _)
    -- `14ℓ ≤ o/(2σ) + 14(2⌊log₂ c⌋ + 6)`
    have hll := log_lin c o h.1
    have hcpos : (0 : ℝ) < c := by linarith
    have hℓ : 14 * ((Nat.log 2 o + 1 : ℕ) : ℝ) ≤ M / (2 * σ) + 14 * ((2 * Nat.log 2 c + 6 : ℕ) : ℝ) := by
      have hllr : (c : ℝ) * ((Nat.log 2 o + 1 : ℕ) : ℝ) ≤ o + c * ((2 * Nat.log 2 c + 6 : ℕ) : ℝ) := by
        exact_mod_cast hll
      have : ((Nat.log 2 o + 1 : ℕ) : ℝ) ≤ o / c + ((2 * Nat.log 2 c + 6 : ℕ) : ℝ) := by
        rw [div_add' _ _ _ hcpos.ne', le_div_iff₀ hcpos]; linarith
      have h1 : 14 * ((o : ℝ) / c) ≤ M / (2 * σ) := by
        have hσpos : 0 < σ := by linarith
        rw [mul_div_assoc', div_le_div_iff₀ hcpos (by positivity)]
        have hmul : (o : ℝ) * (28 * σ) ≤ M * c := mul_le_mul hMo hc (by positivity) (by linarith)
        have e : 14 * (o : ℝ) * (2 * σ) = o * (28 * σ) := by ring
        rw [e]; exact hmul
      linarith
    have hb' : M / σ ≤ ((6 * B + 1 : ℕ) : ℝ) + (10 + 14 * ((Nat.log 2 o + 1 : ℕ) : ℝ)) + Real.logb 2 m := by
      rw [div_eq_mul_inv, mul_comm, ← one_div]; exact hb
    have : M / (2 * σ) ≤ ((6 * B + 1 : ℕ) : ℝ) + 10 + 14 * ((2 * Nat.log 2 c + 6 : ℕ) : ℝ) +
        Real.logb 2 m := by
      have e : M / σ = 2 * (M / (2 * σ)) := by field_simp
      rw [e] at hb'; linarith
    have hfin : M ≤ 2 * σ * (((6 * B + 1 : ℕ) : ℝ) + 10 + 14 * ((2 * Nat.log 2 c + 6 : ℕ) : ℝ) +
        Real.logb 2 m) := by
      rw [div_le_iff₀ (by positivity)] at this; linarith
    linarith

/-- **Frontier for `m` runs, given Rhin, Barina and Hercher**, under a numerical condition. -/
theorem frontier_rhin (hR : CycleLiterature.SimonsDeWegerLemma12) (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    {c : ℕ} (hc : 28 * Reach.σ (Real.logb 2 3) m ≤ c)
    (hsmall : 2 * Reach.σ (Real.logb 2 3) m * (((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 +
      14 * ((2 * Nat.log 2 c + 6 : ℕ) : ℝ) + Real.logb 2 m) < 137500000000) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) :=
  frontier_rhin_of hR (CycleLength.cycleBounds_hercher hB hH29) (by norm_num) h hx hx1 hm hp ha hpos
    hne hne' hc hsmall

/-- `σ_m ≤ σ_n` for `m ≤ n`. -/
lemma σ_mono {m n : ℕ} (h : m ≤ n) : Reach.σ (Real.logb 2 3) m ≤ Reach.σ (Real.logb 2 3) n :=
  sum_le_sum_of_subset_of_nonneg (range_mono h)
    (fun i _ _ => pow_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) i)

/-- `σ_n ≤ Σ_{i<n} 1.585^i`. -/
lemma σ_le (n : ℕ) : Reach.σ (Real.logb 2 3) n ≤ ∑ i ∈ range n, (1.585 : ℝ) ^ i := by
  obtain ⟨l3a, -⟩ := Repeat.log_three_bounds
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhi : Real.logb 2 3 ≤ 1.585 := by
    show Real.log 3 / Real.log 2 ≤ 1.585
    rw [div_le_iff₀ hl2p]; linarith
  exact sum_le_sum (fun i _ => pow_le_pow_left₀ (Real.logb_nonneg (by norm_num) (by norm_num)) hhi i)

/-- **At most 10 runs, for any cycle bounds** `CycleBounds No NE` (`NE ≤ 12 No`) and any
base-weight cap `Bmax` with `2σ(10)·(6 Bmax + const) < NE`. -/
theorem frontier_ten_of (hR : CycleLiterature.SimonsDeWegerLemma12) {No NE : ℕ}
    (hCB : CycleLength.CycleBounds No NE) (hNo : NE ≤ 12 * No)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm10 : m ≤ 10)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    {Bmax : ℕ} (hsmall : ∑ k ∈ range m, (p k).sum ≤ Bmax)
    (hNE : 2 * 170 * (6 * Bmax + 435) < NE) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) := by
  have hσ : Reach.σ (Real.logb 2 3) m ≤ 170 := by
    refine (σ_mono hm10).trans ((σ_le 10).trans ?_)
    norm_num [sum_range_succ]
  have hσ0 : 0 ≤ Reach.σ (Real.logb 2 3) m := Reach.σ_pos (by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num) hm |>.le
  have hlog : Nat.log 2 4760 = 12 := by
    rw [Nat.log_eq_iff (by norm_num)]; norm_num
  have hlm : Real.logb 2 m ≤ 4 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hm)]
    have : (m : ℝ) ≤ 10 := by exact_mod_cast hm10
    norm_num; linarith
  have hBr : ((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) ≤ 6 * Bmax + 1 := by
    exact_mod_cast (show 6 * (∑ k ∈ range m, (p k).sum) + 1 ≤ 6 * Bmax + 1 by omega)
  have hlm0 : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  have hc30 : ((2 * Nat.log 2 4760 + 6 : ℕ) : ℝ) = 2 * 12 + 6 := by rw [hlog]; push_cast; ring
  have hcond : 2 * Reach.σ (Real.logb 2 3) m * (((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 +
      14 * ((2 * Nat.log 2 4760 + 6 : ℕ) : ℝ) + Real.logb 2 m) < NE := by
    rw [hc30]
    have hX : ((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 + 14 * (2 * 12 + 6) + Real.logb 2 m ≤
        6 * Bmax + 1 + 10 + 14 * (2 * 12 + 6) + 4 := by linarith
    have hX0 : 0 ≤ ((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 + 14 * (2 * 12 + 6) +
        Real.logb 2 m := by positivity
    calc 2 * Reach.σ (Real.logb 2 3) m * (((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 +
          14 * (2 * 12 + 6) + Real.logb 2 m)
        ≤ 2 * 170 * (6 * Bmax + 1 + 10 + 14 * (2 * 12 + 6) + 4) :=
          mul_le_mul (by linarith) hX hX0 (by norm_num)
      _ < NE := by
          have : ((2 * 170 * (6 * Bmax + 435) : ℕ) : ℝ) < NE := by exact_mod_cast hNE
          push_cast at this; linarith
  exact frontier_rhin_of hR hCB hNo h hx hx1 hm hp ha hpos hne hne' (c := 4760)
    (by push_cast; linarith) hcond

/-- **At most ten runs, base weight `≤ 5·10^7`.** -/
theorem frontier_ten (hR : CycleLiterature.SimonsDeWegerLemma12) (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm10 : m ≤ 10)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    (hsmall : ∑ k ∈ range m, (p k).sum ≤ 50000000) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) :=
  frontier_ten_of hR (CycleLength.cycleBounds_hercher hB hH29) (by norm_num) h hx hx1 hm hm10 hp ha
    hpos hne hne' hsmall (by norm_num)

/-- **At most 20 runs, for any cycle bounds** `CycleBounds No NE` (`NE ≤ 12 No`) and any
base-weight cap `Bmax` with `2σ(20)·(6 Bmax + const) < NE`. -/
theorem frontier_twenty_of (hR : CycleLiterature.SimonsDeWegerLemma12) {No NE : ℕ}
    (hCB : CycleLength.CycleBounds No NE) (hNo : NE ≤ 12 * No)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm20 : m ≤ 20)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    {Bmax : ℕ} (hsmall : ∑ k ∈ range m, (p k).sum ≤ Bmax)
    (hNE : 2 * 17200 * (6 * Bmax + 604) < NE) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) := by
  have hσ : Reach.σ (Real.logb 2 3) m ≤ 17200 := by
    refine (σ_mono hm20).trans ((σ_le 20).trans ?_)
    norm_num [sum_range_succ]
  have hσ0 : 0 ≤ Reach.σ (Real.logb 2 3) m := Reach.σ_pos (by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num) hm |>.le
  have hlog : Nat.log 2 481600 = 18 := by
    rw [Nat.log_eq_iff (by norm_num)]; norm_num
  have hlm : Real.logb 2 m ≤ 5 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hm)]
    have : (m : ℝ) ≤ 20 := by exact_mod_cast hm20
    norm_num; linarith
  have hBr : ((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) ≤ 6 * Bmax + 1 := by
    exact_mod_cast (show 6 * (∑ k ∈ range m, (p k).sum) + 1 ≤ 6 * Bmax + 1 by omega)
  have hlm0 : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  have hc30 : ((2 * Nat.log 2 481600 + 6 : ℕ) : ℝ) = 2 * 18 + 6 := by rw [hlog]; push_cast; ring
  have hcond : 2 * Reach.σ (Real.logb 2 3) m * (((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 +
      14 * ((2 * Nat.log 2 481600 + 6 : ℕ) : ℝ) + Real.logb 2 m) < NE := by
    rw [hc30]
    have hX : ((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 + 14 * (2 * 18 + 6) + Real.logb 2 m ≤
        6 * Bmax + 1 + 10 + 14 * (2 * 18 + 6) + 5 := by linarith
    have hX0 : 0 ≤ ((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 + 14 * (2 * 18 + 6) +
        Real.logb 2 m := by positivity
    calc 2 * Reach.σ (Real.logb 2 3) m * (((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 10 +
          14 * (2 * 18 + 6) + Real.logb 2 m)
        ≤ 2 * 17200 * (6 * Bmax + 1 + 10 + 14 * (2 * 18 + 6) + 5) :=
          mul_le_mul (by linarith) hX hX0 (by norm_num)
      _ < NE := by
          have : ((2 * 17200 * (6 * Bmax + 604) : ℕ) : ℝ) < NE := by exact_mod_cast hNE
          push_cast at this; linarith
  exact frontier_rhin_of hR hCB hNo h hx hx1 hm hp ha hpos hne hne' (c := 481600)
    (by push_cast; linarith) hcond

/-- **At most twenty runs, base weight `≤ 6·10^5`.** -/
theorem frontier_twenty (hR : CycleLiterature.SimonsDeWegerLemma12) (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm20 : m ≤ 20)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    (hsmall : ∑ k ∈ range m, (p k).sum ≤ 600000) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) :=
  frontier_twenty_of hR (CycleLength.cycleBounds_hercher hB hH29) (by norm_num) h hx hx1 hm hm20 hp ha
    hpos hne hne' hsmall (by norm_num)

end Syracuse.MRunsRhin
