import Syracuse.Approaches.RunsFrontier

/-!
# The exact reach of wedge-core certificates

For a word of `m` runs, the cocycle gives one divisibility `D ∣ T_R` per excluded run `R`
(`ThreeRuns`, `FourRuns`). In `log₂` units, `T_R` is a sum of `m` monomials, the "splits"
`f_R(s) = Σ_{s runs after R} x + Σ_{remaining runs} y`, where `x = E` and `y = o·log₂ 3` per run. Since
`o ≤ E`, `y ≤ λ x` with `λ = log₂ 3`. A certificate needs a lower bound `log₂|D| ≥ θ·max(X, Y)` with `θ`
above `min_R max_s f_R(s) / max(X, Y)`. This file computes that quantity exactly, abstractly, for every
`m` and every cap `λ ≥ 1`:

> `min_R max_s f_R(s) ≤ (1 - 1/σ_m)·max(X, Y)`, `σ_m = Σ_{i<m} λ^i` (`reach_upper`),

and the bound is attained (`reach_tight`). For `λ = log₂ 3` this is `c_m = 1 - (λ-1)/(λ^m - 1)`:
`0.613, 0.804, 0.890, 0.935, 0.961, …`. With Ellison's exponent `0.8557` wedge-core certificates
therefore reach exactly three runs (`ThreeRuns.three_runs_bounded`). With Rhin's bound they reach each fixed
`m` (`FourRuns.four_runs_bounded` for `m = 4`), at a size cost growing like `λ^m`.

**Proof of the upper bound.** Write `f_R(s) = Y - y_R + Φ(R+1+s) - Φ(R+1)` with the walk
`Φ(j) = Σ_{i<j}(x_i - y_i)` (`f_eq`).
* **`Y ≥ X`:** the walk drifts down. Take `p` maximising `Φ` over one period and `h_k = Φ(p) - Φ(p+k)`.
  If every `R` had a split above `(1 - 1/σ)Y`, then `y_{p-1+k} < h_k + τ` with `τ = Y/σ`. A step can
  drop by at most `(1 - 1/λ)y`, so `h_{k+1} + τ ≤ λ(h_k + τ)`, hence `y_{p-1+k} < λ^k τ`. Summing over a
  period gives `Y < τσ = Y`.
* **`X > Y`:** raising `y` towards `λx` until `Y = X` only increases every `f`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| window sums over a period | `window_sum` | proved |
| `f_R(s) = Y - y_R + Φ(R+1+s) - Φ(R+1)` | `f_eq` | proved |
| `Φ(j + m) = Φ(j) + X - Y` | `Φ_period` | proved |
| **upper bound** `∃ R, ∀ s < m, f_R(s) ≤ (1 - 1/σ_m)·max(X, Y)` | `reach_upper` | proved |
| **tightness**: a profile with `f_R(s) = (1 - 1/σ_m)·max(X, Y)` at the best split of every `R` | `reach_tight` | proved |
| Ellison's exponent `1 - 1/(10 ln 2)` lies strictly between `c_3` and `c_4` (`λ = log₂ 3`) | `ellison_reach` | proved |
-/

namespace Syracuse.Reach

open Finset

/-- Prefix sums. -/
noncomputable def P (z : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, z i

/-- The split bound for excluded run `R` at split `s` (period `m`). -/
noncomputable def f (x y : ℕ → ℝ) (m R s : ℕ) : ℝ :=
  (∑ i ∈ Ico (R + 1) (R + 1 + s), x i) + ∑ i ∈ Ico (R + 1 + s) (R + m), y i

/-- The walk `Φ(j) = Σ_{i<j} (x_i - y_i)`. -/
noncomputable def Φ (x y : ℕ → ℝ) (j : ℕ) : ℝ := P x j - P y j

/-- `σ_m = Σ_{i<m} λ^i`. -/
noncomputable def σ (lam : ℝ) (m : ℕ) : ℝ := ∑ i ∈ range m, lam ^ i

lemma sum_Ico_P (z : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) : ∑ i ∈ Ico a b, z i = P z b - P z a := by
  rw [P, P, sum_Ico_eq_sub _ h]

/-- **Window sums.** For an `m`-periodic `z`, `P(R + m) = P(R) + P(m)`. -/
lemma window_sum {z : ℕ → ℝ} {m : ℕ} (pz : ∀ i, z (i + m) = z i) (R : ℕ) :
    P z (R + m) = P z R + P z m := by
  induction R with
  | zero => simp [P]
  | succ R ih =>
    have e1 : P z (R + 1 + m) = P z (R + m) + z (R + m) := by
      rw [show R + 1 + m = (R + m) + 1 by omega]; simp [P, sum_range_succ]
    have e2 : P z (R + 1) = P z R + z R := by simp [P, sum_range_succ]
    rw [e1, e2, ih, pz R]; ring

lemma f_eq {x y : ℕ → ℝ} {m : ℕ} (py : ∀ i, y (i + m) = y i) (R s : ℕ)
    (hs : s < m) : f x y m R s = P y m - y R + Φ x y (R + 1 + s) - Φ x y (R + 1) := by
  unfold f Φ
  rw [sum_Ico_P x (by omega), sum_Ico_P y (by omega), window_sum py R]
  have : P y (R + 1) = P y R + y R := by rw [P, P, sum_range_succ]
  rw [this]; ring

lemma Φ_period {x y : ℕ → ℝ} {m : ℕ} (px : ∀ i, x (i + m) = x i) (py : ∀ i, y (i + m) = y i)
    (j : ℕ) : Φ x y (j + m) = Φ x y j + (P x m - P y m) := by
  unfold Φ; rw [window_sum px, window_sum py]; ring

lemma σ_pos {lam : ℝ} (hlam : 1 ≤ lam) {m : ℕ} (hm : 1 ≤ m) : 0 < σ lam m := by
  unfold σ
  have : (0 : ℝ) < lam ^ 0 := by norm_num
  calc (0 : ℝ) < ∑ i ∈ range 1, lam ^ i := by simp
    _ ≤ ∑ i ∈ range m, lam ^ i :=
        sum_le_sum_of_subset_of_nonneg (range_mono hm) (fun i _ _ => by positivity)

/-- The case `X ≤ Y`. -/
theorem reach_upper_le {lam : ℝ} (hlam : 1 ≤ lam) {m : ℕ} (hm : 1 ≤ m) {x y : ℕ → ℝ}
    (hcap : ∀ i, y i ≤ lam * x i)
    (px : ∀ i, x (i + m) = x i) (py : ∀ i, y (i + m) = y i) (hXY : P x m ≤ P y m) :
    ∃ R : ℕ, ∀ s < m, f x y m R s ≤ (1 - 1 / σ lam m) * P y m := by
  set X := P x m
  set Y := P y m
  have hσ := σ_pos hlam hm
  set τ := Y / σ lam m with hτ
  -- the peak of the walk over `[1, m]`
  obtain ⟨p, hpmem, hpmax⟩ := (Finset.Icc 1 m).exists_max_image (Φ x y) ⟨1, by simp; omega⟩
  rw [Finset.mem_Icc] at hpmem
  have below : ∀ j, 1 ≤ j → Φ x y j ≤ Φ x y p := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases Nat.lt_or_ge m j with hjm | hjm
      · have := ih (j - m) (by omega) (by omega)
        have hper := Φ_period px py (j - m)
        rw [Nat.sub_add_cancel hjm.le] at hper
        rw [hper]; linarith
      · exact hpmax j (Finset.mem_Icc.2 ⟨hj, hjm⟩)
  by_contra H
  push_neg at H
  -- `y_{p-1+k} < h_k + τ`
  set h : ℕ → ℝ := fun k => Φ x y p - Φ x y (p + k)
  have key : ∀ k, y (p - 1 + k) < h k + τ := by
    intro k
    obtain ⟨s, hs, hlt⟩ := H (p - 1 + k)
    rw [f_eq py _ s hs] at hlt
    have e1 : p - 1 + k + 1 = p + k := by omega
    rw [e1] at hlt
    have hb := below (p + k + s) (by omega)
    have : (1 - 1 / σ lam m) * Y = Y - τ := by rw [hτ]; field_simp
    rw [this] at hlt
    simp only [h]
    linarith
  -- the chain `h_{k+1} + τ ≤ λ(h_k + τ)`
  have hlam0 : (0 : ℝ) < lam := by linarith
  have chain : ∀ k, h (k + 1) + τ ≤ lam * (h k + τ) := by
    intro k
    have hstep : h (k + 1) - h k = y (p + k) - x (p + k) := by
      simp only [h, Φ, P]
      rw [show p + (k + 1) = p + k + 1 by omega, sum_range_succ, sum_range_succ]; ring
    have hk1 := key (k + 1)
    rw [show p - 1 + (k + 1) = p + k by omega] at hk1
    have hc := hcap (p + k)
    -- `x ≥ y/λ`, so `h_{k+1} ≤ h_k + (1 - 1/λ)·y`
    have : lam * h (k + 1) ≤ lam * h k + (lam - 1) * y (p + k) := by nlinarith
    nlinarith
  have grow : ∀ k, h k + τ ≤ lam ^ k * τ := by
    intro k
    induction k with
    | zero => simp [h]
    | succ k ih =>
      calc h (k + 1) + τ ≤ lam * (h k + τ) := chain k
        _ ≤ lam * (lam ^ k * τ) := mul_le_mul_of_nonneg_left ih hlam0.le
        _ = lam ^ (k + 1) * τ := by ring
  -- sum over one period
  have hsum : ∑ k ∈ range m, y (p - 1 + k) < ∑ k ∈ range m, lam ^ k * τ := by
    apply sum_lt_sum_of_nonempty ⟨0, by simp; omega⟩
    intro k _
    exact lt_of_lt_of_le (key k) (grow k)
  have hwin : ∑ k ∈ range m, y (p - 1 + k) = Y := by
    have := window_sum py (p - 1)
    have e : ∑ k ∈ range m, y (p - 1 + k) = P y (p - 1 + m) - P y (p - 1) := by
      rw [P, P, sum_range_add_sub_sum_range]
    rw [e, this]; ring
  have hrhs : ∑ k ∈ range m, lam ^ k * τ = Y := by
    rw [← sum_mul]; change σ lam m * τ = Y; rw [hτ]; field_simp
  rw [hwin, hrhs] at hsum
  exact lt_irrefl _ hsum

/-- **Upper bound on the reach.** For every `m ≥ 1`, cap `λ ≥ 1` and `m`-periodic size profile with
`0 ≤ y ≤ λx`, some excluded run `R` has every split `f_R(s) ≤ (1 - 1/σ_m)·max(X, Y)`. -/
theorem reach_upper {lam : ℝ} (hlam : 1 ≤ lam) {m : ℕ} (hm : 1 ≤ m) {x y : ℕ → ℝ}
    (hy0 : ∀ i, 0 ≤ y i) (hcap : ∀ i, y i ≤ lam * x i)
    (px : ∀ i, x (i + m) = x i) (py : ∀ i, y (i + m) = y i) :
    ∃ R : ℕ, ∀ s < m, f x y m R s ≤ (1 - 1 / σ lam m) * max (P x m) (P y m) := by
  rcases le_or_gt (P x m) (P y m) with hXY | hXY
  · obtain ⟨R, hR⟩ := reach_upper_le hlam hm hcap px py hXY
    exact ⟨R, fun s hs => by rw [max_eq_right hXY]; exact hR s hs⟩
  · -- raise `y` towards `λx` until `Y = X`
    set X := P x m
    set Y := P y m
    have hY0 : 0 ≤ Y := sum_nonneg (fun i _ => hy0 i)
    have hden : 0 < lam * X - Y := by nlinarith
    set θ := (X - Y) / (lam * X - Y)
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
    have hθ1 : θ ≤ 1 := (div_le_one hden).2 (by nlinarith)
    set y' : ℕ → ℝ := fun i => y i + θ * (lam * x i - y i)
    have hcap' : ∀ i, y' i ≤ lam * x i := fun i => by
      have := hcap i; simp only [y']; nlinarith
    have py' : ∀ i, y' (i + m) = y' i := fun i => by simp only [y', px i, py i]
    have hY' : P y' m = X := by
      have e : P y' m = P y m + θ * (lam * P x m - P y m) := by
        simp only [P, y']
        rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, ← mul_sum]
      rw [e]
      change Y + θ * (lam * X - Y) = X
      simp only [θ]; rw [div_mul_cancel₀ _ hden.ne']; ring
    obtain ⟨R, hR⟩ := reach_upper_le hlam hm hcap' px py' (by rw [hY'])
    refine ⟨R, fun s hs => ?_⟩
    have hmono : f x y m R s ≤ f x y' m R s := by
      unfold f
      gcongr with i
      simp only [y']; have := hcap i; nlinarith
    rw [max_eq_left hXY.le]
    calc f x y m R s ≤ f x y' m R s := hmono
      _ ≤ (1 - 1 / σ lam m) * P y' m := hR s hs
      _ = (1 - 1 / σ lam m) * X := by rw [hY']

/-! ## Tightness -/

/-- The extremal profile: run `0` has `x = λ^{m-1}`, `y = 1`; run `i ≥ 1` has `x = λ^{i-1}`, `y = λ^i`. -/
noncomputable def xt (lam : ℝ) (m i : ℕ) : ℝ := if i % m = 0 then lam ^ (m - 1) else lam ^ (i % m - 1)

noncomputable def yt (lam : ℝ) (m i : ℕ) : ℝ := lam ^ (i % m)

lemma Φt_formula {lam : ℝ} {m : ℕ} :
    ∀ r, 1 ≤ r → r ≤ m → Φ (xt lam m) (yt lam m) r = lam ^ (m - 1) - lam ^ (r - 1) := by
  intro r hr1 hrm
  induction r with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      simp [Φ, P, xt, yt]
    · have ih' := ih hpos (by omega)
      have hrm' : r < m := by omega
      unfold Φ at ih' ⊢
      rw [P, P, sum_range_succ, sum_range_succ, ← P, ← P]
      have hx : xt lam m r = lam ^ (r - 1) := by
        simp [xt, Nat.mod_eq_of_lt hrm', show r ≠ 0 by omega]
      have hy : yt lam m r = lam ^ r := by simp [yt, Nat.mod_eq_of_lt hrm']
      rw [hx, hy, show r + 1 - 1 = r by omega]
      have : lam ^ r = lam ^ (r - 1) * lam := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      linarith [ih']

lemma xt_period (lam : ℝ) (m i : ℕ) : xt lam m (i + m) = xt lam m i := by
  simp [xt, Nat.add_mod_right]

lemma yt_period (lam : ℝ) (m i : ℕ) : yt lam m (i + m) = yt lam m i := by
  simp [yt, Nat.add_mod_right]

lemma Pyt {lam : ℝ} (m : ℕ) : P (yt lam m) m = σ lam m := by
  unfold P σ yt
  refine sum_congr rfl (fun i hi => ?_)
  rw [Nat.mod_eq_of_lt (mem_range.1 hi)]

lemma Pxt {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) : P (xt lam m) m = σ lam m := by
  have hΦ := Φt_formula (lam := lam) m hm le_rfl
  unfold Φ at hΦ
  rw [Pyt] at hΦ
  linarith

/-- **Tightness.** For the extremal profile, `X = Y = σ_m`, and every excluded run `R < m` has a split
with `f_R(s) = σ_m - 1 = (1 - 1/σ_m)·max(X, Y)`. -/
theorem reach_tight {lam : ℝ} (hlam : 1 ≤ lam) {m : ℕ} (hm : 1 ≤ m) :
    P (xt lam m) m = σ lam m ∧ P (yt lam m) m = σ lam m ∧
      ∀ R < m, ∃ s < m, f (xt lam m) (yt lam m) m R s =
        (1 - 1 / σ lam m) * max (P (xt lam m) m) (P (yt lam m) m) := by
  have hσ := σ_pos hlam hm
  refine ⟨Pxt hm, Pyt m, fun R hR => ?_⟩
  rw [Pxt hm, Pyt m, max_self, show (1 - 1 / σ lam m) * σ lam m = σ lam m - 1 by field_simp]
  have hf := fun s hs => f_eq (x := xt lam m) (yt_period lam m) R s hs
  rw [Pyt m] at hf
  have hyR : yt lam m R = lam ^ R := by simp [yt, Nat.mod_eq_of_lt hR]
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    refine ⟨0, hm, ?_⟩
    rw [hf 0 hm, hyR]; simp
  · refine ⟨m - R, by omega, ?_⟩
    rw [hf (m - R) (by omega), hyR, show R + 1 + (m - R) = 1 + m by omega,
      Φ_period (xt_period lam m) (yt_period lam m), Pxt hm, Pyt m,
      Φt_formula 1 le_rfl hm, Φt_formula (R + 1) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero]
    ring
/-- **Ellison reaches exactly three runs.** With `λ = log₂ 3`, Ellison's exponent `1 - 1/(10 ln 2)`
(from `2^E e^{-E/10} = 2^{E(1 - 1/(10 ln 2))}`) lies strictly between `c_3 = 1 - 1/σ_3` and
`c_4 = 1 - 1/σ_4`. -/
theorem ellison_reach :
    1 - 1 / σ (Real.log 3 / Real.log 2) 3 < 1 - 1 / (10 * Real.log 2) ∧
      1 - 1 / (10 * Real.log 2) < 1 - 1 / σ (Real.log 3 / Real.log 2) 4 := by
  obtain ⟨l3a, l3b⟩ := Repeat.log_three_bounds
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  set lam := Real.log 3 / Real.log 2
  have hlo : 1.584 < lam := by rw [lt_div_iff₀ hl2p]; linarith
  have hhi : lam < 1.585 := by rw [div_lt_iff₀ hl2p]; linarith
  have s3 : σ lam 3 = 1 + lam + lam ^ 2 := by simp [σ, sum_range_succ]
  have s4 : σ lam 4 = 1 + lam + lam ^ 2 + lam ^ 3 := by simp [σ, sum_range_succ]
  have h3 : σ lam 3 < 10 * Real.log 2 := by rw [s3]; nlinarith
  have h4 : 10 * Real.log 2 < σ lam 4 := by rw [s4]; nlinarith
  have hσ3 : 0 < σ lam 3 := by rw [s3]; nlinarith
  constructor
  · have : 1 / (10 * Real.log 2) < 1 / σ lam 3 := one_div_lt_one_div_of_lt hσ3 h3
    linarith
  · have : 1 / σ lam 4 < 1 / (10 * Real.log 2) := one_div_lt_one_div_of_lt (by positivity) h4
    linarith

end Syracuse.Reach
