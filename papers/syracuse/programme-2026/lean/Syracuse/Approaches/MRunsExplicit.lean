import Syracuse.Approaches.MRuns

/-!
# `m ≤ 3` runs of any blocks, with no nonvanishing hypothesis

`MRuns.mruns_ellison` assumes every rotated `T` is nonzero. This file removes that hypothesis for words
whose runs are long.

* **`2`-adic nonvanishing** (`T_ne_zero`). In `T` the first term is `(A₀ - A₁)·3^{…}`, and every other
  term is divisible by `2^{E₁}`, `E₁` the weight of the run after the excluded one. So
  `2^{E₁} ∤ A₀ - A₁` forces `T ≠ 0`.
* **Product coefficients** `A_i = S(p_i) Π_{k≠i} D(p_k)` (`Acoef`).
  - `A_i - A_{i+1} = -(Π_{k∉{i,i+1}} D(p_k))·C(p_i, p_{i+1})` (`Acoef_diff`), nonzero when adjacent
    cores are (`Acoef_diff_ne`).
  - `|A_i - A_{i+1}| ≤ 2^{6B+1}`, `B` the total weight of the base blocks (`Acoef_diff_le`).

Hence (`mruns_explicit`):

> Given Ellison, let `p₀, …, p_{m-1}` (`2 ≤ m ≤ 3`) be positive nonempty blocks with nonzero adjacent
> cores, of total weight `B`, and let every run `p_i^{a_i}` have weight above `6B + 1`. A cycle of either
> sign whose gap word is a rotation of `p₀^{a₀} ⋯ p_{m-1}^{a_{m-1}}`, with `E` outside Ellison's exceptions,
> has `(θ_E - c_3)·max(E, o log₂ 3) ≤ 6B + 2 + log₂ 3`, `θ_E - c_3 > 0`.

So for fixed base blocks only finitely many exponent tuples with all runs long can carry a cycle, and the
bound is explicit.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `2^{E₁} ∤ A₀ - A₁ ⇒ T ≠ 0` | `T_ne_zero` | proved |
| `S(w) ≤ 3^{E(w)}` for positive words | `Sz_le` | proved |
| product coefficients satisfy `D'·S(Q_i) = A_i·D(Q_i)`, periodic | `Acoef_spec`, `Acoef_period` | proved |
| `A_i - A_{i+1} = -(Π_{k∉{i,i+1}} D_k)·C(p_i, p_{i+1})` | `Acoef_diff` | proved |
| `|A_i - A_{i+1}| ≤ 2^{6B+1}`; `≠ 0` when the core is nonzero | `Acoef_diff_le`, `Acoef_diff_ne` | proved |
| **`m ≤ 3`, any blocks, long runs, explicit bound** | `mruns_explicit` | proved (conditional on `Ellison1971`) |
| `θ_E - c_3 > 1/20` | `margin` | proved |
| no nontrivial positive cycle on such words with base weight `B ≤ 10^9` | `frontier_mruns` | proved (conditional on Ellison + Barina + Hercher Cor. 29) |
| the same for any cycle bounds: `120 B + 80 ≤ NE` | `frontier_mruns_of` | proved |
-/

namespace Syracuse.MRunsExplicit

open Finset Syracuse.MRuns

/-! ## `2`-adic nonvanishing -/

/-- **`T ≠ 0` from one `2`-adic condition.** -/
theorem T_ne_zero {Q : ℕ → Word} {A : ℕ → ℤ} {m : ℕ} (hm : 2 ≤ m)
    (h : ¬ (2 : ℤ) ^ (Q 1).sum ∣ A 0 - A 1) : T (2 : ℤ) 3 Q A m ≠ 0 := by
  intro h0
  unfold T at h0
  rw [sum_eq_sum_Ico_succ_bot (by omega : 1 < m + 1)] at h0
  have h1m : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  have hfirst : (A (1 - 1) - A (1 % m)) * ((2 : ℤ) ^ Es Q 1 1 * 3 ^ Os Q 1 m) =
      (A 0 - A 1) * 3 ^ Os Q 1 m := by simp [Es, h1m]
  rw [hfirst] at h0
  set rest := ∑ j ∈ Ico (1 + 1) (m + 1), (A (j - 1) - A (j % m)) * ((2 : ℤ) ^ Es Q 1 j * 3 ^ Os Q j m)
  have hrest : (2 : ℤ) ^ (Q 1).sum ∣ rest := by
    apply dvd_sum
    intro j hj
    rw [mem_Ico] at hj
    apply dvd_mul_of_dvd_right
    apply dvd_mul_of_dvd_left
    apply pow_dvd_pow
    unfold Es
    exact single_le_sum (f := fun i => (Q i).sum) (fun _ _ => Nat.zero_le _) (by simp; omega)
  have hd : (2 : ℤ) ^ (Q 1).sum ∣ (A 0 - A 1) * 3 ^ Os Q 1 m := by
    have e : (A 0 - A 1) * 3 ^ Os Q 1 m = -rest := by linarith
    rw [e]; exact dvd_neg.2 hrest
  have hcop : IsCoprime ((2 : ℤ) ^ (Q 1).sum) (3 ^ Os Q 1 m) := by
    apply IsCoprime.pow; rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  exact h (hcop.dvd_of_dvd_mul_right hd)

/-! ## Sizes of `S`, `D`, cores -/

/-- `S(w) ≤ 3^{E(w)}` for a positive word. -/
lemma Sz_le {w : Word} (hw : w.Pos) : Sz w ≤ 3 ^ w.sum := by
  have hb := Repeat.two_pow_mul_S_le hw
  have hl := CycleLiterature.length_le_sum hw
  obtain ⟨t, ht⟩ : ∃ t, w.sum = w.length + t := ⟨w.sum - w.length, by omega⟩
  rw [ht] at hb ⊢
  have h2 : (0 : ℤ) < 2 ^ w.length := by positivity
  have hS : 0 ≤ Sz w := CycleLiterature.Sz_nonneg w
  have : (2 : ℤ) ^ (w.length + t) * (3 ^ w.length - 2 ^ w.length) ≤ 2 ^ w.length * 3 ^ (w.length + t) := by
    rw [pow_add, pow_add]
    have h23 : (2 : ℤ) ^ t ≤ 3 ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
    have hA : (3 : ℤ) ^ w.length - 2 ^ w.length ≤ 3 ^ w.length := by
      linarith [pow_pos (show (0 : ℤ) < 2 by norm_num) w.length]
    calc (2 : ℤ) ^ w.length * 2 ^ t * (3 ^ w.length - 2 ^ w.length)
        ≤ 2 ^ w.length * 2 ^ t * 3 ^ w.length := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 2 ^ w.length * (3 ^ w.length * 2 ^ t) := by ring
      _ ≤ 2 ^ w.length * (3 ^ w.length * 3 ^ t) := by gcongr
  have := hb.trans this
  exact le_of_mul_le_mul_left this h2

/-- `|C(u,v)| ≤ 2·3^{E(u)+E(v)}` for positive words. -/
lemma abs_core_le {u v : Word} (hu : u.Pos) (hv : v.Pos) :
    |TwoBackground.core (2 : ℤ) 3 u v| ≤ 2 * 3 ^ (u.sum + v.sum) := by
  have du := (StdPairs.abs_Dz_lt hu).le
  have dv := (StdPairs.abs_Dz_lt hv).le
  have su := Sz_le hu
  have sv := Sz_le hv
  have su0 : 0 ≤ Sz u := CycleLiterature.Sz_nonneg u
  have sv0 : 0 ≤ Sz v := CycleLiterature.Sz_nonneg v
  unfold TwoBackground.core
  calc |D (2 : ℤ) 3 u * S 2 3 v - D 2 3 v * S 2 3 u|
      ≤ |D (2 : ℤ) 3 u| * S 2 3 v + |D 2 3 v| * S 2 3 u := by
        have := abs_sub (D (2 : ℤ) 3 u * S 2 3 v) (D 2 3 v * S 2 3 u)
        rw [abs_mul, abs_mul, abs_of_nonneg sv0, abs_of_nonneg su0] at this
        exact this
    _ ≤ 3 ^ u.sum * 3 ^ v.sum + 3 ^ v.sum * 3 ^ u.sum := by
        gcongr
    _ = 2 * 3 ^ (u.sum + v.sum) := by rw [pow_add]; ring

/-! ## Product coefficients -/

/-- `A_i = S(p_i)·Π_{k<m, k ≠ i mod m} D(p_k)`. -/
def Acoef (p : ℕ → Word) (m i : ℕ) : ℤ :=
  S (2 : ℤ) 3 (p i) * ∏ k ∈ (range m).erase (i % m), D (2 : ℤ) 3 (p k)

lemma p_mod {p : ℕ → Word} {m : ℕ} (hm : 1 ≤ m) (hp : ∀ i, p (i + m) = p i) (i : ℕ) :
    p i = p (i % m) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.lt_or_ge i m with hi | hi
    · rw [Nat.mod_eq_of_lt hi]
    · have := ih (i - m) (by omega)
      rw [show i = (i - m) + m by omega, hp, this, Nat.add_mod_right]

lemma Acoef_spec {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hp : ∀ i, p (i + m) = p i)
    (i : ℕ) : (∏ k ∈ range m, D (2 : ℤ) 3 (p k)) * Sz (TwoBackground.bpow (p i) (a i)) =
      Acoef p m i * Dz (TwoBackground.bpow (p i) (a i)) := by
  have hmem : i % m ∈ range m := mem_range.2 (Nat.mod_lt _ (by omega))
  rw [← mul_prod_erase _ _ hmem, ← p_mod hm hp i]
  have := TwoBackground.D_mul_S_bpow (2 : ℤ) 3 (p i) (a i)
  simp only [Sz, Dz, Acoef] at this ⊢
  linear_combination (∏ k ∈ (range m).erase (i % m), D (2 : ℤ) 3 (p k)) * this

lemma Acoef_period {p : ℕ → Word} {m : ℕ} (hp : ∀ i, p (i + m) = p i) (i : ℕ) :
    Acoef p m (i + m) = Acoef p m i := by
  simp only [Acoef, hp, Nat.add_mod_right]

/-- `A_i - A_{i+1} = -(Π_{k∉{i,i+1}} D_k)·C(p_i, p_{i+1})`. -/
lemma Acoef_diff {p : ℕ → Word} {m : ℕ} (hm : 2 ≤ m) (hp : ∀ i, p (i + m) = p i) (i : ℕ) :
    Acoef p m i - Acoef p m (i + 1) =
      -((∏ k ∈ ((range m).erase (i % m)).erase ((i + 1) % m), D (2 : ℤ) 3 (p k)) *
        TwoBackground.core (2 : ℤ) 3 (p i) (p (i + 1))) := by
  have ha : i % m ∈ range m := mem_range.2 (Nat.mod_lt _ (by omega))
  have hb : (i + 1) % m ∈ range m := mem_range.2 (Nat.mod_lt _ (by omega))
  have hab : (i + 1) % m ≠ i % m := by
    intro h
    have := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [show i + 1 - i = 1 by omega, Nat.mod_eq_of_lt (by omega : 1 < m)] at this
    omega
  have hb' : (i + 1) % m ∈ (range m).erase (i % m) := mem_erase.2 ⟨hab, hb⟩
  have ha' : i % m ∈ (range m).erase ((i + 1) % m) := mem_erase.2 ⟨hab.symm, ha⟩
  unfold Acoef
  rw [← mul_prod_erase _ _ hb', ← mul_prod_erase _ _ ha', erase_right_comm,
    ← p_mod (by omega) hp i, ← p_mod (by omega) hp (i + 1)]
  unfold TwoBackground.core
  ring

lemma Acoef_diff_ne {p : ℕ → Word} {m : ℕ} (hm : 2 ≤ m) (hp : ∀ i, p (i + m) = p i)
    (hne : ∀ i, p i ≠ []) (hC : ∀ i, TwoBackground.core (2 : ℤ) 3 (p i) (p (i + 1)) ≠ 0) (i : ℕ) :
    Acoef p m i - Acoef p m (i + 1) ≠ 0 := by
  rw [Acoef_diff hm hp i, neg_ne_zero]
  refine mul_ne_zero ?_ (hC i)
  rw [prod_ne_zero_iff]
  exact fun k _ => StdPairs.Dz_ne_zero (hne k)

/-- `|A_i - A_{i+1}| ≤ 2^{6B+1}`, `B = Σ_{k<m} E(p_k)`. -/
lemma Acoef_diff_le {p : ℕ → Word} {m : ℕ} (hm : 2 ≤ m) (hp : ∀ i, p (i + m) = p i)
    (hpos : ∀ i, (p i).Pos) (i : ℕ) :
    |Acoef p m i - Acoef p m (i + 1)| ≤ 2 ^ (6 * (∑ k ∈ range m, (p k).sum) + 1) := by
  set B := ∑ k ∈ range m, (p k).sum
  rw [Acoef_diff hm hp i, abs_neg, abs_mul]
  -- the product
  set T := ((range m).erase (i % m)).erase ((i + 1) % m)
  have hT : T ⊆ range m := (erase_subset _ _).trans (erase_subset _ _)
  have hprod : |∏ k ∈ T, D (2 : ℤ) 3 (p k)| ≤ 3 ^ B := by
    rw [abs_prod]
    calc ∏ k ∈ T, |D (2 : ℤ) 3 (p k)| ≤ ∏ k ∈ T, (3 : ℤ) ^ (p k).sum :=
          Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) (fun k _ => (StdPairs.abs_Dz_lt (hpos k)).le)
      _ = 3 ^ (∑ k ∈ T, (p k).sum) := prod_pow_eq_pow_sum _ _ _
      _ ≤ 3 ^ B := pow_le_pow_right₀ (by norm_num)
          (sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => Nat.zero_le _))
  -- the core
  have hsi : (p i).sum ≤ B := by
    rw [p_mod (by omega) hp i]
    exact single_le_sum (f := fun k => (p k).sum) (fun _ _ => Nat.zero_le _)
      (mem_range.2 (Nat.mod_lt _ (by omega)))
  have hsj : (p (i + 1)).sum ≤ B := by
    rw [p_mod (by omega) hp (i + 1)]
    exact single_le_sum (f := fun k => (p k).sum) (fun _ _ => Nat.zero_le _)
      (mem_range.2 (Nat.mod_lt _ (by omega)))
  have hcore := abs_core_le (hpos i) (hpos (i + 1))
  have hcore' : |TwoBackground.core (2 : ℤ) 3 (p i) (p (i + 1))| ≤ 2 * 3 ^ (2 * B) :=
    hcore.trans (by gcongr; norm_num; omega)
  calc |∏ k ∈ T, D (2 : ℤ) 3 (p k)| * |TwoBackground.core (2 : ℤ) 3 (p i) (p (i + 1))|
      ≤ 3 ^ B * (2 * 3 ^ (2 * B)) := mul_le_mul hprod hcore' (abs_nonneg _) (by positivity)
    _ = 2 * 3 ^ (3 * B) := by rw [show 3 * B = B + 2 * B by ring, pow_add]; ring
    _ ≤ 2 * 4 ^ (3 * B) := by gcongr; norm_num
    _ = 2 ^ (6 * B + 1) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]; ring_nf

/-! ## The explicit theorem -/

/-- **`m ≤ 3` runs of any blocks, long runs, given Ellison.** -/
theorem mruns_explicit (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hC : ∀ i, TwoBackground.core (2 : ℤ) 3 (p i) (p (i + 1)) ≠ 0)
    (hlong : ∀ i, 6 * (∑ k ∈ range m, (p k).sum) + 1 < (TwoBackground.bpow (p i) (a i)).sum)
    (hrot : gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m)
    (hx : (cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum ∉ CycleLiterature.ellisonExceptions) :
    0 < (1 - 1 / (10 * Real.log 2)) - (1 - 1 / Reach.σ (Real.logb 2 3) 3) ∧
      ((1 - 1 / (10 * Real.log 2)) - (1 - 1 / Reach.σ (Real.logb 2 3) 3)) *
        max ((cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum : ℝ)
          (Real.logb 2 3 * (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length) ≤
        (6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) + 1 + Real.logb 2 3 := by
  set Q : ℕ → Word := fun i => TwoBackground.bpow (p i) (a i)
  set B := ∑ k ∈ range m, (p k).sum
  have hQ : ∀ i, Q (i + m) = Q i := fun i => by simp only [Q, hp, ha]
  have hQpos : ∀ i, (Q i).Pos := fun i => StdPairs.pos_bpow (hpos i) (a i)
  have hQne : ∀ i, Q i ≠ [] := fun i h0 => by
    have := hlong i
    rw [show (TwoBackground.bpow (p i) (a i)) = Q i from rfl, h0] at this
    simp at this
  have hdiff_ne := Acoef_diff_ne hm hp hne hC
  have hdiff_le := Acoef_diff_le hm hp hpos
  -- every rotated `T` is nonzero
  have hT : ∀ R, T (2 : ℤ) 3 (fun k => Q (R + k)) (fun k => Acoef p m (R + k)) m ≠ 0 := by
    intro R
    apply T_ne_zero hm
    simp only [add_zero]
    intro hdvd
    have hlt : |Acoef p m R - Acoef p m (R + 1)| < (2 : ℤ) ^ (Q (R + 1)).sum :=
      lt_of_le_of_lt (hdiff_le R) (pow_lt_pow_right₀ (by norm_num) (hlong (R + 1)))
    exact hdiff_ne R (Int.eq_zero_of_abs_lt_dvd hdvd hlt)
  exact MRuns.mruns_ellison hEl h (by omega) hm3 hQ hQpos hQne hrot
    (fun i => Acoef_spec (a := a) (by omega) hp i) (Acoef_period hp) hdiff_le hT hx

/-- `θ_E - c_3 > 1/20`. -/
lemma margin : (1 : ℝ) / 20 < (1 - 1 / (10 * Real.log 2)) - (1 - 1 / Reach.σ (Real.logb 2 3) 3) := by
  obtain ⟨l3a, l3b⟩ := Repeat.log_three_bounds
  have hl2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  have hlb : Real.logb 2 3 = Real.log 3 / Real.log 2 := rfl
  have hhi : Real.logb 2 3 < 1.585 := by rw [hlb, div_lt_iff₀ hl2p]; linarith
  have hlo : 1 < Real.logb 2 3 := by rw [hlb, lt_div_iff₀ hl2p]; linarith
  have s3 : Reach.σ (Real.logb 2 3) 3 = 1 + Real.logb 2 3 + Real.logb 2 3 ^ 2 := by
    simp [Reach.σ, sum_range_succ]
  have hσ : Reach.σ (Real.logb 2 3) 3 < 5.1 := by rw [s3]; nlinarith
  have hσ0 : 0 < Reach.σ (Real.logb 2 3) 3 := by rw [s3]; positivity
  have h1 : 1 / 5.1 < 1 / Reach.σ (Real.logb 2 3) 3 := one_div_lt_one_div_of_lt hσ0 hσ
  have h2 : 1 / (10 * Real.log 2) < 1 / 6.93 :=
    one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  norm_num at h1 h2 ⊢
  linarith

/-- **Frontier for two and three runs, for any cycle bounds** `CycleBounds No NE`: base weight `B`
with `120 B + 80 ≤ NE`. -/
theorem frontier_mruns_of (hEl : CycleLiterature.Ellison1971) {No NE : ℕ}
    (hCB : CycleLength.CycleBounds No NE)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hC : ∀ i, TwoBackground.core (2 : ℤ) 3 (p i) (p (i + 1)) ≠ 0)
    (hlong : ∀ i, 6 * (∑ k ∈ range m, (p k).sum) + 1 < (TwoBackground.bpow (p i) (a i)).sum)
    (hsmall : 120 * (∑ k ∈ range m, (p k).sum) + 80 ≤ NE) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) := by
  intro hrot
  have hE := (hCB x o hx h hx1).2
  rw [hrot.perm.sum_eq] at hE
  obtain ⟨-, hb⟩ := mruns_explicit hEl h hm hm3 hp ha hpos hne hC hlong hrot
    (Frontier.not_mem_exceptions (by omega))
  have hmg := margin
  set M := max ((cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum : ℝ)
    (Real.logb 2 3 * (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length)
  have hM : (NE : ℝ) < M := lt_of_lt_of_le (by exact_mod_cast hE) (le_max_left _ _)
  have hl3 : Real.logb 2 3 < 2 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]; norm_num
  have hBr : 20 * (((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 3) ≤ NE := by
    exact_mod_cast (show 20 * ((6 * (∑ k ∈ range m, (p k).sum) + 1) + 3) ≤ NE by omega)
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.cast_nonneg _) hM
  have := mul_lt_mul_of_pos_right hmg hMpos
  linarith

/-- **Frontier for two and three runs.** Given Ellison, Barina and Hercher's Corollary 29, no nontrivial
positive cycle is a rotation of `p₀^{a₀} ⋯ p_{m-1}^{a_{m-1}}` (`2 ≤ m ≤ 3`) over positive nonempty base
blocks with nonzero adjacent cores, total weight `B ≤ 10^9` and every run of weight above `6B + 1`. -/
theorem frontier_mruns (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hC : ∀ i, TwoBackground.core (2 : ℤ) 3 (p i) (p (i + 1)) ≠ 0)
    (hlong : ∀ i, 6 * (∑ k ∈ range m, (p k).sum) + 1 < (TwoBackground.bpow (p i) (a i)).sum)
    (hsmall : ∑ k ∈ range m, (p k).sum ≤ 1000000000) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) :=
  frontier_mruns_of hEl (CycleLength.cycleBounds_hercher hB hH29) h hx hx1 hm hm3 hp ha hpos hne hC
    hlong (by omega)

end Syracuse.MRunsExplicit
