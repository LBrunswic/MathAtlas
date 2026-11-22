import Syracuse.Approaches.ThreeRuns

/-!
# Four runs: the wedge-core method with Rhin's bound

`ThreeRuns` showed that Ellison's exponent `0.8557` makes the wedge-core method effective for three runs
and not for four: the supremum of the four-run linear programs is `0.890`. Simons and de Weger's
Lemma 12 (Rhin's bound for `|E log 2 - o log 3|`, stated as `CycleLiterature.SimonsDeWegerLemma12`) loses
only a factor `o^{13.3}` instead of `e^{E/10}`. That is enough:

> Given `SimonsDeWegerLemma12`, for any positive blocks `p₁, …, p₄` whose four wedge coefficients are at
> most `2^K` and whose four sums `T_R` are nonzero, no nontrivial positive cycle has a gap word that is
> a rotation of `p₁^{a₁} p₂^{a₂} p₃^{a₃} p₄^{a₄}` with `E ≥ 3500 + 16K` (`four_runs_bounded`).

The algebra is the four-core identity (`four_run_identity`). As for three runs, it gives
`D(W) ∣ T₁ = D₂D₃c₄₁ 2^{E₂+E₃+E₄} + D₃D₄c₁₂ 3^{o₂+o₃+o₄} + D₁D₄c₂₃ 2^{E₂}3^{o₃+o₄} + D₁D₂c₃₄ 2^{E₂+E₃}3^{o₄}`
(`dvd_four_runs`); the other three come from rotations. For the sizes there are two cases:
* `2·3^o ≤ 2^E`, where `D ≥ 2^{E-1}`;
* near-critical, where Rhin gives `3^o < 2^{9 + 14ℓ}·D` with `ℓ = ⌊log₂ o⌋ + 1` (`rhin_pow`) and
  `200ℓ ≤ o + 3000` (`log_bound`).

Each monomial bound is linearised (`ThreeRuns.lin2`), and the `2 × 4⁴` cases close by `omega`. The
threshold `3500 + 16K` comes from the integer linear programs, maximum `≈ 3412 + 15.3K` (computed with
scipy, not in Lean).

The same scheme works for every fixed number of runs, with suprema `0.935, 0.961, …` below `1`; each
`m` needs its own `m^m`-case check.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| the four-core identity | `four_run_identity` | proved |
| `D(W) ∣ T₁` on a cycle | `dvd_four_runs` | proved |
| `1 ≤ 2^{9+14ℓ} e^{-13.3(0.46057 + log o)}`, `ℓ = ⌊log₂ o⌋ + 1` | `rhin_pow` | proved |
| `200ℓ ≤ o + 3000` | `log_bound` | proved |
| `|Σ cᵢmᵢ| < 2^{K+3}·mᵢ` for some `i` | `abs_lt_some4` | proved |
| **four runs, any blocks:** no nontrivial positive cycle once `E ≥ 3500 + 16K`, `T`s nonzero | `four_runs_bounded` | proved (conditional on `SimonsDeWegerLemma12`) |
-/

namespace Syracuse.FourRuns

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs Syracuse.ThreeRuns

section Generic

variable {R : Type*} [CommRing R] (X Y : R)

/-- **The four-core identity.** -/
theorem four_run_identity (p₁ p₂ p₃ p₄ : Word) (a₁ a₂ a₃ a₄ : ℕ) :
    D X Y p₁ * D X Y p₂ * D X Y p₃ * D X Y p₄ *
        S X Y (bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄) =
      -(D X Y p₂ * D X Y p₃ * core X Y p₄ p₁ *
            Y ^ ((bpow p₁ a₁).length + (bpow p₂ a₂).length + (bpow p₃ a₃).length +
              (bpow p₄ a₄).length)
        + D X Y p₃ * D X Y p₄ * core X Y p₁ p₂ * X ^ (bpow p₁ a₁).sum *
            Y ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length + (bpow p₄ a₄).length)
        + D X Y p₁ * D X Y p₄ * core X Y p₂ p₃ * X ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum) *
            Y ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length)
        + D X Y p₁ * D X Y p₂ * core X Y p₃ p₄ *
            X ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum + (bpow p₃ a₃).sum) * Y ^ (bpow p₄ a₄).length)
      + S X Y p₄ * D X Y p₁ * D X Y p₂ * D X Y p₃ *
          D X Y (bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄) := by
  have h1 := D_mul_S_bpow X Y p₁ a₁
  have h2 := D_mul_S_bpow X Y p₂ a₂
  have h3 := D_mul_S_bpow X Y p₃ a₃
  have h4 := D_mul_S_bpow X Y p₄ a₄
  rw [show D X Y (bpow p₁ a₁) = X ^ (bpow p₁ a₁).sum - Y ^ (bpow p₁ a₁).length from rfl] at h1
  rw [show D X Y (bpow p₂ a₂) = X ^ (bpow p₂ a₂).sum - Y ^ (bpow p₂ a₂).length from rfl] at h2
  rw [show D X Y (bpow p₃ a₃) = X ^ (bpow p₃ a₃).sum - Y ^ (bpow p₃ a₃).length from rfl] at h3
  rw [show D X Y (bpow p₄ a₄) = X ^ (bpow p₄ a₄).sum - Y ^ (bpow p₄ a₄).length from rfl] at h4
  have eW : D X Y (bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄) =
      X ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum + (bpow p₃ a₃).sum + (bpow p₄ a₄).sum) -
        Y ^ ((bpow p₁ a₁).length + (bpow p₂ a₂).length + (bpow p₃ a₃).length +
          (bpow p₄ a₄).length) := by
    simp only [D, List.sum_append, List.length_append]
  rw [eW, S_append, S_append, S_append]
  simp only [core, List.sum_append, List.length_append]
  linear_combination
    (D X Y p₂ * D X Y p₃ * D X Y p₄ * Y ^ (bpow p₂ a₂).length * Y ^ (bpow p₃ a₃).length *
      Y ^ (bpow p₄ a₄).length) * h1 +
    (D X Y p₁ * D X Y p₃ * D X Y p₄ * X ^ (bpow p₁ a₁).sum * Y ^ (bpow p₃ a₃).length *
      Y ^ (bpow p₄ a₄).length) * h2 +
    (D X Y p₁ * D X Y p₂ * D X Y p₄ * X ^ (bpow p₁ a₁).sum * X ^ (bpow p₂ a₂).sum *
      Y ^ (bpow p₄ a₄).length) * h3 +
    (D X Y p₁ * D X Y p₂ * D X Y p₃ * X ^ (bpow p₁ a₁).sum * X ^ (bpow p₂ a₂).sum *
      X ^ (bpow p₃ a₃).sum) * h4

end Generic

/-- **Four-run divisibility.** -/
theorem dvd_four_runs {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {p₁ p₂ p₃ p₄ : Word} {a₁ a₂ a₃ a₄ : ℕ}
    (hw : gapWord x o ~r bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄)
    (hne : bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄ ≠ [])
    (hE : (bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄).sum ≠ 0) :
    Dz (bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄) ∣
      D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum + (bpow p₄ a₄).sum) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          3 ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₄ * core (2 : ℤ) 3 p₂ p₃ * 2 ^ (bpow p₂ a₂).sum *
          3 ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum) * 3 ^ (bpow p₄ a₄).length := by
  have hS := dvd_S_of_rotated h hw
  have hc := isCoprime_six hne hE
  have hid := four_run_identity (2 : ℤ) 3 p₁ p₂ p₃ p₄ a₁ a₂ a₃ a₄
  set W := bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄ with hW
  set T := D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum + (bpow p₄ a₄).sum) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          3 ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₄ * core (2 : ℤ) 3 p₂ p₃ * 2 ^ (bpow p₂ a₂).sum *
          3 ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum) * 3 ^ (bpow p₄ a₄).length
  have key : (2 : ℤ) ^ (bpow p₁ a₁).sum * 3 ^ 0 * T =
      -(D (2 : ℤ) 3 p₁ * D 2 3 p₂ * D 2 3 p₃ * D 2 3 p₄ * Sz W) +
        S (2 : ℤ) 3 p₄ * D 2 3 p₁ * D 2 3 p₂ * D 2 3 p₃ * Dz W +
        D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ * Dz W := by
    rw [Sz, hid]
    simp only [Dz, D, hW, List.sum_append, List.length_append, pow_add, T]
    ring
  have : Dz W ∣ (2 : ℤ) ^ (bpow p₁ a₁).sum * 3 ^ 0 * T := by
    rw [key]
    exact dvd_add (dvd_add (dvd_neg.2 (dvd_mul_of_dvd_right hS _)) (dvd_mul_left _ _))
      (dvd_mul_left _ _)
  exact CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this

/-! ## Sizes -/

/-- Four terms: `|Σ cᵢmᵢ| < 2^{K+3}·mᵢ` for the largest `mᵢ`. -/
lemma abs_lt_some4 {c₁ c₂ c₃ c₄ m₁ m₂ m₃ m₄ : ℤ} {K : ℕ} (h1 : |c₁| ≤ 2 ^ K) (h2 : |c₂| ≤ 2 ^ K)
    (h3 : |c₃| ≤ 2 ^ K) (h4 : |c₄| ≤ 2 ^ K) (n1 : 0 < m₁) (n2 : 0 < m₂) (n3 : 0 < m₃) (n4 : 0 < m₄) :
    |c₁ * m₁ + c₂ * m₂ + c₃ * m₃ + c₄ * m₄| < 2 ^ (K + 3) * m₁ ∨
      |c₁ * m₁ + c₂ * m₂ + c₃ * m₃ + c₄ * m₄| < 2 ^ (K + 3) * m₂ ∨
      |c₁ * m₁ + c₂ * m₂ + c₃ * m₃ + c₄ * m₄| < 2 ^ (K + 3) * m₃ ∨
      |c₁ * m₁ + c₂ * m₂ + c₃ * m₃ + c₄ * m₄| < 2 ^ (K + 3) * m₄ := by
  set M := max m₁ (max m₂ (max m₃ m₄))
  have l1 : m₁ ≤ M := le_max_left _ _
  have l2 : m₂ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have l3 : m₃ ≤ M := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have l4 : m₄ ≤ M := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hK : (0 : ℤ) < 2 ^ K := by positivity
  have hM : 0 < M := lt_of_lt_of_le n1 l1
  have e : ∀ {c m : ℤ}, |c| ≤ 2 ^ K → 0 < m → m ≤ M → |c * m| ≤ 2 ^ K * M := by
    intro c m hc hm hmM
    rw [abs_mul, abs_of_pos hm]; exact mul_le_mul hc hmM hm.le hK.le
  have hb : |c₁ * m₁ + c₂ * m₂ + c₃ * m₃ + c₄ * m₄| < 2 ^ (K + 3) * M := by
    have s1 := abs_add_le (c₁ * m₁ + c₂ * m₂ + c₃ * m₃) (c₄ * m₄)
    have s2 := abs_add_le (c₁ * m₁ + c₂ * m₂) (c₃ * m₃)
    have s3 := abs_add_le (c₁ * m₁) (c₂ * m₂)
    have := e h1 n1 l1; have := e h2 n2 l2; have := e h3 n3 l3; have := e h4 n4 l4
    rw [pow_add]; nlinarith [mul_pos hK hM]
  have hMdef : M = max m₁ (max m₂ (max m₃ m₄)) := rfl
  rcases max_choice m₁ (max m₂ (max m₃ m₄)) with h | h <;> rw [← hMdef] at h <;> rw [h] at hb
  · exact Or.inl hb
  · rcases max_choice m₂ (max m₃ m₄) with h' | h' <;> rw [h'] at hb
    · exact Or.inr (Or.inl hb)
    · rcases max_choice m₃ m₄ with h'' | h'' <;> rw [h''] at hb
      · exact Or.inr (Or.inr (Or.inl hb))
      · exact Or.inr (Or.inr (Or.inr hb))

/-! ## Rhin's bound, linearised -/

/-- `1 ≤ 2^{9+14ℓ} e^{-13.3 (0.46057 + log o)}` with `ℓ = ⌊log₂ o⌋ + 1`. -/
lemma rhin_pow {o : ℕ} (ho : 1 ≤ o) :
    1 ≤ (2 : ℝ) ^ (9 + 14 * (Nat.log 2 o + 1)) * Real.exp (-13.3 * (0.46057 + Real.log o)) := by
  set ℓ := Nat.log 2 o + 1
  have hlt : o < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by norm_num) o
  have hltR : (o : ℝ) < 2 ^ ℓ := by exact_mod_cast hlt
  have hlog : Real.log o < ℓ * Real.log 2 := by
    have := Real.log_lt_log (by exact_mod_cast ho) hltR
    rwa [Real.log_pow] at this
  have hl2 := Real.log_two_gt_d9
  have e2 : (2 : ℝ) ^ (9 + 14 * ℓ) = Real.exp ((9 + 14 * ℓ : ℕ) * Real.log 2) := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e2, ← Real.exp_add]
  apply Real.one_le_exp
  have hℓ : (0 : ℝ) ≤ ℓ := by positivity
  push_cast
  nlinarith [mul_nonneg hℓ (show (0 : ℝ) ≤ Real.log 2 by linarith)]

/-- `200·(⌊log₂ o⌋ + 1) ≤ o + 3000`. -/
lemma log_bound {o : ℕ} (ho : 1 ≤ o) : 200 * (Nat.log 2 o + 1) ≤ o + 3000 := by
  have hp := Nat.pow_log_le_self 2 (show o ≠ 0 by omega)
  have key : ∀ n : ℕ, 200 * (n + 1) ≤ 2 ^ n + 3000 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rcases Nat.lt_or_ge (2 ^ n) 200 with h | h
      · have : n < 8 := by
          by_contra hc
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 8 ≤ n by omega)
          omega
        rw [pow_succ]; omega
      · rw [pow_succ]; omega
  have := key (Nat.log 2 o)
  omega

/-! ## The theorem -/

set_option maxHeartbeats 20000000 in
/-- **Four runs, any blocks, with Rhin's bound.** -/
theorem four_runs_bounded (hR : CycleLiterature.SimonsDeWegerLemma12) {p₁ p₂ p₃ p₄ : Word}
    (hp₁ : p₁.Pos) (hp₂ : p₂.Pos) (hp₃ : p₃.Pos) (hp₄ : p₄.Pos) {a₁ a₂ a₃ a₄ K : ℕ}
    (hK1 : |D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁| ≤ 2 ^ K)
    (hK2 : |D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂| ≤ 2 ^ K)
    (hK3 : |D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃| ≤ 2 ^ K)
    (hK4 : |D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄| ≤ 2 ^ K)
    (hT1 : D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum + (bpow p₄ a₄).sum) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          3 ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₄ * core (2 : ℤ) 3 p₂ p₃ * 2 ^ (bpow p₂ a₂).sum *
          3 ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum) * 3 ^ (bpow p₄ a₄).length ≠ 0)
    (hT2 : D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          2 ^ ((bpow p₃ a₃).sum + (bpow p₄ a₄).sum + (bpow p₁ a₁).sum) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          3 ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length + (bpow p₁ a₁).length) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₁ * core (2 : ℤ) 3 p₃ p₄ * 2 ^ (bpow p₃ a₃).sum *
          3 ^ ((bpow p₄ a₄).length + (bpow p₁ a₁).length) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          2 ^ ((bpow p₃ a₃).sum + (bpow p₄ a₄).sum) * 3 ^ (bpow p₁ a₁).length ≠ 0)
    (hT3 : D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          2 ^ ((bpow p₄ a₄).sum + (bpow p₁ a₁).sum + (bpow p₂ a₂).sum) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          3 ^ ((bpow p₄ a₄).length + (bpow p₁ a₁).length + (bpow p₂ a₂).length) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₂ * core (2 : ℤ) 3 p₄ p₁ * 2 ^ (bpow p₄ a₄).sum *
          3 ^ ((bpow p₁ a₁).length + (bpow p₂ a₂).length) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          2 ^ ((bpow p₄ a₄).sum + (bpow p₁ a₁).sum) * 3 ^ (bpow p₂ a₂).length ≠ 0)
    (hT4 : D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          2 ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum + (bpow p₃ a₃).sum) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          3 ^ ((bpow p₁ a₁).length + (bpow p₂ a₂).length + (bpow p₃ a₃).length) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₃ * core (2 : ℤ) 3 p₁ p₂ * 2 ^ (bpow p₁ a₁).sum *
          3 ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          2 ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum) * 3 ^ (bpow p₃ a₃).length ≠ 0)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) (hx1 : x ≠ 1)
    (hrot : gapWord x o ~r bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄)
    (hE : 3500 + 16 * K ≤ (bpow p₁ a₁).sum + (bpow p₂ a₂).sum + (bpow p₃ a₃).sum + (bpow p₄ a₄).sum) :
    False := by
  set E₁ := (bpow p₁ a₁).sum
  set E₂ := (bpow p₂ a₂).sum
  set E₃ := (bpow p₃ a₃).sum
  set E₄ := (bpow p₄ a₄).sum
  set o₁ := (bpow p₁ a₁).length
  set o₂ := (bpow p₂ a₂).length
  set o₃ := (bpow p₃ a₃).length
  set o₄ := (bpow p₄ a₄).length
  have l1 : o₁ ≤ E₁ := CycleLiterature.length_le_sum (pos_bpow hp₁ a₁)
  have l2 : o₂ ≤ E₂ := CycleLiterature.length_le_sum (pos_bpow hp₂ a₂)
  have l3 : o₃ ≤ E₃ := CycleLiterature.length_le_sum (pos_bpow hp₃ a₃)
  have l4 : o₄ ≤ E₄ := CycleLiterature.length_le_sum (pos_bpow hp₄ a₄)
  -- rotations
  have hr2 : gapWord x o ~r bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄ ++ bpow p₁ a₁ := by
    refine hrot.trans ?_
    have := List.isRotated_append (l := bpow p₁ a₁) (l' := bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄)
    simpa [List.append_assoc] using this
  have hr3 : gapWord x o ~r bpow p₃ a₃ ++ bpow p₄ a₄ ++ bpow p₁ a₁ ++ bpow p₂ a₂ := by
    refine hr2.trans ?_
    have := List.isRotated_append (l := bpow p₂ a₂) (l' := bpow p₃ a₃ ++ bpow p₄ a₄ ++ bpow p₁ a₁)
    simpa [List.append_assoc] using this
  have hr4 : gapWord x o ~r bpow p₄ a₄ ++ bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ := by
    refine hr3.trans ?_
    have := List.isRotated_append (l := bpow p₃ a₃) (l' := bpow p₄ a₄ ++ bpow p₁ a₁ ++ bpow p₂ a₂)
    simpa [List.append_assoc] using this
  set E := E₁ + E₂ + E₃ + E₄
  set oo := o₁ + o₂ + o₃ + o₄
  have hsum4 : ∀ P Q R T : Word, (P ++ Q ++ R ++ T).sum = P.sum + Q.sum + R.sum + T.sum := by
    intro P Q R T; simp only [List.sum_append]
  have hlen4 : ∀ P Q R T : Word,
      (P ++ Q ++ R ++ T).length = P.length + Q.length + R.length + T.length := by
    intro P Q R T; simp only [List.length_append]
  have hDv : ∀ W : Word, W.sum = E → W.length = oo → Dz W = 2 ^ E - 3 ^ oo := by
    intro W hs hl; simp only [Dz, D, hs, hl]
  have ne4 : ∀ P Q R T : Word, (P ++ Q ++ R ++ T).sum = E → P ++ Q ++ R ++ T ≠ [] := by
    intro P Q R T hs h0; rw [h0] at hs; simp at hs; omega
  have d1 := dvd_four_runs h hrot (ne4 _ _ _ _ (hsum4 _ _ _ _)) (by rw [hsum4]; omega)
  have d2 := dvd_four_runs h hr2 (ne4 _ _ _ _ (by rw [hsum4]; ring)) (by rw [hsum4]; omega)
  have d3 := dvd_four_runs h hr3 (ne4 _ _ _ _ (by rw [hsum4]; ring)) (by rw [hsum4]; omega)
  have d4 := dvd_four_runs h hr4 (ne4 _ _ _ _ (by rw [hsum4]; ring)) (by rw [hsum4]; omega)
  rw [hDv _ (hsum4 _ _ _ _) (hlen4 _ _ _ _)] at d1
  rw [hDv _ (by rw [hsum4]; ring) (by rw [hlen4]; ring)] at d2
  rw [hDv _ (by rw [hsum4]; ring) (by rw [hlen4]; ring)] at d3
  rw [hDv _ (by rw [hsum4]; ring) (by rw [hlen4]; ring)] at d4
  -- the cycle's `D`
  have hlen : o = oo := by
    have := hrot.perm.length_eq; rw [gapWord_length, hlen4] at this; exact this
  have hsw : (gapWord x o).sum = E := by rw [hrot.perm.sum_eq, hsum4]
  have hDcyc : Dz (gapWord x o) = 2 ^ E - 3 ^ oo := by
    rw [show Dz (gapWord x o) = 2 ^ (gapWord x o).sum - 3 ^ (gapWord x o).length from rfl, hsw,
      gapWord_length, hlen]
  have hDpos : (0 : ℤ) < 2 ^ E - 3 ^ oo := hDcyc ▸ CycleLiterature.cycle_Dz_pos h hx
  have hrh := CycleLiterature.sdw12_Dz_gt hR h hx hx1
  rw [hDcyc, hlen] at hrh
  -- the four bounds `|D| < 2^{K+3}·(monomial)`
  have p2 : ∀ n : ℕ, (0 : ℤ) < 2 ^ n := fun n => by positivity
  have p3 : ∀ n : ℕ, (0 : ℤ) < 3 ^ n := fun n => by positivity
  have lt_of : ∀ {T : ℤ}, T ≠ 0 → (2 : ℤ) ^ E - 3 ^ oo ∣ T → ∀ {M : ℤ}, |T| < M →
      (2 : ℤ) ^ E - 3 ^ oo < M := fun hT hdv _ hM => by
    have := lt_of_le_of_lt (Int.le_of_dvd (abs_pos.2 hT) ((abs_dvd_abs _ _).2 hdv)) hM
    rwa [abs_of_pos hDpos] at this
  have mono : ∀ α β : ℕ, (2 : ℤ) ^ (K + 3) * (2 ^ α * 3 ^ β) = 2 ^ (K + 3 + α) * 3 ^ β := by
    intro α β; rw [pow_add]; ring
  set c₁ := D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁
  set c₂ := D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂
  set c₃ := D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃
  set c₄ := D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄
  have B1 : (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + (E₂ + E₃ + E₄)) * 3 ^ 0 ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + 0) * 3 ^ (o₂ + o₃ + o₄) ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + E₂) * 3 ^ (o₃ + o₄) ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + (E₂ + E₃)) * 3 ^ o₄ := by
    have eT : c₁ * 2 ^ (E₂ + E₃ + E₄) + c₂ * 3 ^ (o₂ + o₃ + o₄) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₄ * core (2 : ℤ) 3 p₂ p₃ * 2 ^ E₂ * 3 ^ (o₃ + o₄) +
        c₄ * 2 ^ (E₂ + E₃) * 3 ^ o₄ =
        c₁ * (2 ^ (E₂ + E₃ + E₄) * 3 ^ 0) + c₂ * (2 ^ 0 * 3 ^ (o₂ + o₃ + o₄)) +
          c₃ * (2 ^ E₂ * 3 ^ (o₃ + o₄)) + c₄ * (2 ^ (E₂ + E₃) * 3 ^ o₄) := by ring
    rw [eT] at hT1 d1
    rcases abs_lt_some4 (m₁ := 2 ^ (E₂ + E₃ + E₄) * 3 ^ 0) (m₂ := 2 ^ 0 * 3 ^ (o₂ + o₃ + o₄))
        (m₃ := 2 ^ E₂ * 3 ^ (o₃ + o₄)) (m₄ := 2 ^ (E₂ + E₃) * 3 ^ o₄) hK1 hK2 hK3 hK4
        (by positivity) (by positivity) (by positivity) (by positivity) with hh | hh | hh | hh
    · left; rw [← mono]; exact lt_of hT1 d1 hh
    · right; left; rw [← mono]; exact lt_of hT1 d1 hh
    · right; right; left; rw [← mono]; exact lt_of hT1 d1 hh
    · right; right; right; rw [← mono]; exact lt_of hT1 d1 hh
  have B2 : (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + (E₃ + E₄ + E₁)) * 3 ^ 0 ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + 0) * 3 ^ (o₃ + o₄ + o₁) ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + E₃) * 3 ^ (o₄ + o₁) ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + (E₃ + E₄)) * 3 ^ o₁ := by
    have eT : c₂ * 2 ^ (E₃ + E₄ + E₁) + c₃ * 3 ^ (o₃ + o₄ + o₁) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₁ * core (2 : ℤ) 3 p₃ p₄ * 2 ^ E₃ * 3 ^ (o₄ + o₁) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ * 2 ^ (E₃ + E₄) * 3 ^ o₁ =
        c₂ * (2 ^ (E₃ + E₄ + E₁) * 3 ^ 0) + c₃ * (2 ^ 0 * 3 ^ (o₃ + o₄ + o₁)) +
          c₄ * (2 ^ E₃ * 3 ^ (o₄ + o₁)) + c₁ * (2 ^ (E₃ + E₄) * 3 ^ o₁) := by ring
    rw [eT] at hT2 d2
    rcases abs_lt_some4 (m₁ := 2 ^ (E₃ + E₄ + E₁) * 3 ^ 0) (m₂ := 2 ^ 0 * 3 ^ (o₃ + o₄ + o₁))
        (m₃ := 2 ^ E₃ * 3 ^ (o₄ + o₁)) (m₄ := 2 ^ (E₃ + E₄) * 3 ^ o₁) hK2 hK3 hK4 hK1
        (by positivity) (by positivity) (by positivity) (by positivity) with hh | hh | hh | hh
    · left; rw [← mono]; exact lt_of hT2 d2 hh
    · right; left; rw [← mono]; exact lt_of hT2 d2 hh
    · right; right; left; rw [← mono]; exact lt_of hT2 d2 hh
    · right; right; right; rw [← mono]; exact lt_of hT2 d2 hh
  have B3 : (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + (E₄ + E₁ + E₂)) * 3 ^ 0 ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + 0) * 3 ^ (o₄ + o₁ + o₂) ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + E₄) * 3 ^ (o₁ + o₂) ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + (E₄ + E₁)) * 3 ^ o₂ := by
    have eT : c₃ * 2 ^ (E₄ + E₁ + E₂) + c₄ * 3 ^ (o₄ + o₁ + o₂) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₂ * core (2 : ℤ) 3 p₄ p₁ * 2 ^ E₄ * 3 ^ (o₁ + o₂) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ * 2 ^ (E₄ + E₁) * 3 ^ o₂ =
        c₃ * (2 ^ (E₄ + E₁ + E₂) * 3 ^ 0) + c₄ * (2 ^ 0 * 3 ^ (o₄ + o₁ + o₂)) +
          c₁ * (2 ^ E₄ * 3 ^ (o₁ + o₂)) + c₂ * (2 ^ (E₄ + E₁) * 3 ^ o₂) := by ring
    rw [eT] at hT3 d3
    rcases abs_lt_some4 (m₁ := 2 ^ (E₄ + E₁ + E₂) * 3 ^ 0) (m₂ := 2 ^ 0 * 3 ^ (o₄ + o₁ + o₂))
        (m₃ := 2 ^ E₄ * 3 ^ (o₁ + o₂)) (m₄ := 2 ^ (E₄ + E₁) * 3 ^ o₂) hK3 hK4 hK1 hK2
        (by positivity) (by positivity) (by positivity) (by positivity) with hh | hh | hh | hh
    · left; rw [← mono]; exact lt_of hT3 d3 hh
    · right; left; rw [← mono]; exact lt_of hT3 d3 hh
    · right; right; left; rw [← mono]; exact lt_of hT3 d3 hh
    · right; right; right; rw [← mono]; exact lt_of hT3 d3 hh
  have B4 : (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + (E₁ + E₂ + E₃)) * 3 ^ 0 ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + 0) * 3 ^ (o₁ + o₂ + o₃) ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + E₁) * 3 ^ (o₂ + o₃) ∨
      (2 : ℤ) ^ E - 3 ^ oo < 2 ^ (K + 3 + (E₁ + E₂)) * 3 ^ o₃ := by
    have eT : c₄ * 2 ^ (E₁ + E₂ + E₃) + c₁ * 3 ^ (o₁ + o₂ + o₃) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₃ * core (2 : ℤ) 3 p₁ p₂ * 2 ^ E₁ * 3 ^ (o₂ + o₃) +
        c₃ * 2 ^ (E₁ + E₂) * 3 ^ o₃ =
        c₄ * (2 ^ (E₁ + E₂ + E₃) * 3 ^ 0) + c₁ * (2 ^ 0 * 3 ^ (o₁ + o₂ + o₃)) +
          c₂ * (2 ^ E₁ * 3 ^ (o₂ + o₃)) + c₃ * (2 ^ (E₁ + E₂) * 3 ^ o₃) := by ring
    rw [eT] at hT4 d4
    rcases abs_lt_some4 (m₁ := 2 ^ (E₁ + E₂ + E₃) * 3 ^ 0) (m₂ := 2 ^ 0 * 3 ^ (o₁ + o₂ + o₃))
        (m₃ := 2 ^ E₁ * 3 ^ (o₂ + o₃)) (m₄ := 2 ^ (E₁ + E₂) * 3 ^ o₃) hK4 hK1 hK2 hK3
        (by positivity) (by positivity) (by positivity) (by positivity) with hh | hh | hh | hh
    · left; rw [← mono]; exact lt_of hT4 d4 hh
    · right; left; rw [← mono]; exact lt_of hT4 d4 hh
    · right; right; left; rw [← mono]; exact lt_of hT4 d4 hh
    · right; right; right; rw [← mono]; exact lt_of hT4 d4 hh
  -- two regimes
  have ho : 1 ≤ oo := by rw [← hlen]; exact h.1
  have hsign := lin2 (p := 0) (q := oo) (r := E) (s := 0) (by linarith)
  by_cases R1 : 2 * 3 ^ oo ≤ (2 : ℤ) ^ E
  · have reg := lin2_le (p := 1) (q := oo) (r := E) (s := 0) (by simpa [pow_one] using R1)
    have conv : ∀ {p q : ℕ}, (2 : ℤ) ^ E - 3 ^ oo < 2 ^ p * 3 ^ q →
        1000 * E < 1000 * (p + 1) + 1585 * q := by
      intro p q hh
      have : (2 : ℤ) ^ E * 3 ^ 0 < 2 ^ (p + 1) * 3 ^ q := by
        rw [pow_succ]; nlinarith [p3 oo]
      have := lin2 this; omega
    replace B1 := B1.imp conv (Or.imp conv (Or.imp conv conv))
    replace B2 := B2.imp conv (Or.imp conv (Or.imp conv conv))
    replace B3 := B3.imp conv (Or.imp conv (Or.imp conv conv))
    replace B4 := B4.imp conv (Or.imp conv (Or.imp conv conv))
    clear * - l1 l2 l3 l4 hE reg B1 B2 B3 B4
    rcases B1 with i1 | i1 | i1 | i1 <;> rcases B2 with i2 | i2 | i2 | i2 <;>
      rcases B3 with i3 | i3 | i3 | i3 <;> rcases B4 with i4 | i4 | i4 | i4 <;> omega
  · push_neg at R1
    have regB := lin2 (p := E) (q := 0) (r := 1) (s := oo) (by linarith)
    set ℓ := Nat.log 2 oo + 1
    have hlb := log_bound ho
    -- Rhin: `3^o < 2^{9+14ℓ}·D`
    have hrp := rhin_pow ho
    have hR3 : (3 : ℝ) ^ oo < 2 ^ (9 + 14 * ℓ) * ((2 : ℝ) ^ E - 3 ^ oo) := by
      have hDr : (0 : ℝ) < (2 : ℝ) ^ E - 3 ^ oo := by exact_mod_cast hDpos
      have h3 : (0 : ℝ) < 3 ^ oo := by positivity
      push_cast at hrh
      calc (3 : ℝ) ^ oo ≤ 3 ^ oo * (2 ^ (9 + 14 * ℓ) * Real.exp (-13.3 * (0.46057 + Real.log oo))) :=
            le_mul_of_one_le_right h3.le hrp
        _ = 2 ^ (9 + 14 * ℓ) * (3 ^ oo * Real.exp (-13.3 * (0.46057 + Real.log oo))) := by ring
        _ < 2 ^ (9 + 14 * ℓ) * ((2 : ℝ) ^ E - 3 ^ oo) := mul_lt_mul_of_pos_left hrh (by positivity)
    have conv : ∀ {p q : ℕ}, (2 : ℤ) ^ E - 3 ^ oo < 2 ^ p * 3 ^ q →
        1584 * oo < 1000 * (9 + 14 * ℓ + p) + 1585 * q := by
      intro p q hh
      have hhR : (2 : ℝ) ^ E - 3 ^ oo < 2 ^ p * 3 ^ q := by exact_mod_cast hh
      have : (2 : ℝ) ^ 0 * 3 ^ oo < 2 ^ (9 + 14 * ℓ + p) * 3 ^ q := by
        rw [pow_zero, one_mul, show (2 : ℝ) ^ (9 + 14 * ℓ + p) = 2 ^ (9 + 14 * ℓ) * 2 ^ p from
          pow_add _ _ _, mul_assoc]
        exact hR3.trans (mul_lt_mul_of_pos_left hhR (by positivity))
      have hZ : (2 : ℤ) ^ 0 * 3 ^ oo < 2 ^ (9 + 14 * ℓ + p) * 3 ^ q := by exact_mod_cast this
      have := lin2 hZ
      omega
    replace B1 := B1.imp conv (Or.imp conv (Or.imp conv conv))
    replace B2 := B2.imp conv (Or.imp conv (Or.imp conv conv))
    replace B3 := B3.imp conv (Or.imp conv (Or.imp conv conv))
    replace B4 := B4.imp conv (Or.imp conv (Or.imp conv conv))
    clear * - l1 l2 l3 l4 hE regB hsign hlb B1 B2 B3 B4
    rcases B1 with i1 | i1 | i1 | i1 <;> rcases B2 with i2 | i2 | i2 | i2 <;>
      rcases B3 with i3 | i3 | i3 | i3 <;> rcases B4 with i4 | i4 | i4 | i4 <;> omega

end Syracuse.FourRuns
