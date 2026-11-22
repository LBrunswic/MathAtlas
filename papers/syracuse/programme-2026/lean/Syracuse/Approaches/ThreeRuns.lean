import Syracuse.Approaches.Trees

/-!
# Three runs: the three-core identity and an effective bound for three letter runs

For a word `W = U V Z` with `U = u^a`, `V = v^b`, `Z = w^c`, the cocycle gives one identity
(`three_run_identity`), with `c_{pq} = C(p, q)` the wedge cores:

`D(u)D(v)D(w)·S(W) = -(D(v)c_{wu} Y^{o} + D(w)c_{uv} X^{E_U}Y^{o_V+o_Z} + D(u)c_{vw} X^{E_U+E_V}Y^{o_Z})
  + S(w)D(u)D(v)·D(W)`.

On a cycle, `X^E ≡ Y^o (mod D(W))` lets the factor `X^{E_U}` be removed, so
(`dvd_three_runs`)

`D(W) ∣ T_U := D(v)c_{wu} 2^{E_V+E_Z} + D(w)c_{uv} 3^{o_V+o_Z} + D(u)c_{vw} 2^{E_V}3^{o_Z}`.

`T_U` does not involve the size of the run `U`. The rotations `V Z U` and `Z U V` give `T_V` and `T_Z`.
When `w = u` (two runs) this collapses to `-c_{uv}D(u)Y^{o_Z}D(V)`, the two-block divisibility.

**Every block triple** (`three_runs_bounded`). Each `T_R` is at most `2^{K+2}` times one of its three
monomials. In `log₂` units these are `x`-prefix plus `y`-suffix sums over the other two runs
(`x = E`, `y = o log₂ 3`). The largest of the three bounds (one per excluded run) never exceeds
`0.80381·max(E, o log₂ 3)`: this is the exact supremum of 27 linear programs, computed with scipy and
not part of the proof. `|D|` is at least `2^{E-1}`, at least `3^o/2`, or near-critical and then Ellison's
`2^{0.8557 E}`. In each case the three bounds are incompatible once `E ≥ 20(K + 2)`. The Lean proof
linearises every monomial bound (`lin2`, `EqualTwoCycles.lin_of_lt`) and closes all `3 × 27` cases by
`omega`. Its hypotheses are that the three coefficients `D(·)C(·,·)` are at most `2^K` and that
`T_U, T_V, T_Z ≠ 0`.

**Where the method stops.** The same linear programs for `m` runs give suprema `0.613` (`m = 2`),
`0.804` (`m = 3`), `0.890` (`m = 4`), `0.935`, `0.961`. Ellison's exponent `0.8557` therefore makes the
wedge-core method effective for two and three runs and **not for four**. A Baker/Rhin bound
`|D| ≥ 2^E·E^{-C}` would push the effective range to every fixed `m`.

**Three letter runs** `1^a d^b e^c` (`d ≠ e`, `d, e ≥ 2`). Only the `1`-run has slope below `log₂ 3`. Each
`T_R` is nonzero by a `2`-adic count (`T_U, T_Z ≡ 2 (mod 4)`, and `T_V = 2^{min(d,e)}·odd + 2^{min+1}·K`).
With `κ = d + e + 2`, Ellison gives `85573E < 100000(κ + E - a)`,
`85573E < 100000(κ + ec) + 158500a` and `85573E < 100000(κ + db) + 158500a`, impossible once
`E ≥ 11κ`. Hence (`three_letter_runs`):

> Given Ellison, no cycle of either sign lies on a rotation of `1^a d^b e^c` with `E ≥ 11(d + e + 2)`.

This is an effective bound on the three-run rung for letters. No sign bound is used. A numerical scan
(not in Lean) finds no cycle on `1^a d^b e^c` with `d, e ≤ 11`, `E ≤ 120`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| the three-core identity | `three_run_identity` | proved |
| `D(W) ∣ T_U` on a cycle | `dvd_three_runs` | proved |
| letter evaluations of `D` and cores | `D_one`, `D_letter`, `core_e1`, `core_1d`, `core_de` | proved |
| `T_U, T_V, T_Z ≠ 0` for `1^a d^b e^c` | `TU_ne`, `TV_ne`, `TZ_ne` | proved |
| no cycle (either sign) on `1^a d^b e^c` once `E ≥ 11(d + e + 2)` | `three_letter_runs` | proved (conditional on `Ellison1971`) |
| monomial comparison, linearised | `lin2`, `lin2_le` | proved |
| `|T| < 2^{K+2}·(largest monomial)` | `abs_lt_some` | proved |
| **any three blocks**: no cycle (either sign) on `u^a v^b w^c` once `E ≥ 20(K + 2)`, given the `T`s nonzero | `three_runs_bounded` | proved (conditional on `Ellison1971`) |
| LP suprema `0.613, 0.804, 0.890, …` for `m = 2, 3, 4, …` runs | — | computed (scipy), not in Lean |
-/

namespace Syracuse.ThreeRuns

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

section Generic

variable {R : Type*} [CommRing R] (X Y : R)

/-- **The three-core identity.** -/
theorem three_run_identity (u v w : Word) (a b c : ℕ) :
    D X Y u * D X Y v * D X Y w * S X Y (bpow u a ++ bpow v b ++ bpow w c) =
      -(D X Y v * core X Y w u * Y ^ ((bpow u a).length + (bpow v b).length + (bpow w c).length)
        + D X Y w * core X Y u v * X ^ (bpow u a).sum *
            Y ^ ((bpow v b).length + (bpow w c).length)
        + D X Y u * core X Y v w * X ^ ((bpow u a).sum + (bpow v b).sum) * Y ^ (bpow w c).length)
      + S X Y w * D X Y u * D X Y v * D X Y (bpow u a ++ bpow v b ++ bpow w c) := by
  have h1 := D_mul_S_bpow X Y u a
  have h2 := D_mul_S_bpow X Y v b
  have h3 := D_mul_S_bpow X Y w c
  rw [show D X Y (bpow u a) = X ^ (bpow u a).sum - Y ^ (bpow u a).length from rfl] at h1
  rw [show D X Y (bpow v b) = X ^ (bpow v b).sum - Y ^ (bpow v b).length from rfl] at h2
  rw [show D X Y (bpow w c) = X ^ (bpow w c).sum - Y ^ (bpow w c).length from rfl] at h3
  have eW : D X Y (bpow u a ++ bpow v b ++ bpow w c) =
      X ^ ((bpow u a).sum + (bpow v b).sum + (bpow w c).sum) -
        Y ^ ((bpow u a).length + (bpow v b).length + (bpow w c).length) := by
    simp only [D, List.sum_append, List.length_append]
  rw [eW, S_append, S_append]
  simp only [core, List.sum_append]
  linear_combination
    (D X Y v * D X Y w * Y ^ (bpow v b).length * Y ^ (bpow w c).length) * h1 +
    (D X Y u * D X Y w * X ^ (bpow u a).sum * Y ^ (bpow w c).length) * h2 +
    (D X Y u * D X Y v * X ^ (bpow u a).sum * X ^ (bpow v b).sum) * h3

end Generic

/-- **Three-run divisibility.** On a cycle whose gap word is a rotation of `W = u^a v^b w^c`,
`D(W) ∣ D(v)c_{wu} 2^{E_V+E_Z} + D(w)c_{uv} 3^{o_V+o_Z} + D(u)c_{vw} 2^{E_V}3^{o_Z}`. -/
theorem dvd_three_runs {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {u v w : Word} {a b c : ℕ}
    (hw : gapWord x o ~r bpow u a ++ bpow v b ++ bpow w c)
    (hne : bpow u a ++ bpow v b ++ bpow w c ≠ []) (hE : (bpow u a ++ bpow v b ++ bpow w c).sum ≠ 0) :
    Dz (bpow u a ++ bpow v b ++ bpow w c) ∣
      D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 2 ^ ((bpow v b).sum + (bpow w c).sum) +
      D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 3 ^ ((bpow v b).length + (bpow w c).length) +
      D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 2 ^ (bpow v b).sum * 3 ^ (bpow w c).length := by
  have hS := dvd_S_of_rotated h hw
  have hc := isCoprime_six hne hE
  have hid := three_run_identity (2 : ℤ) 3 u v w a b c
  set W := bpow u a ++ bpow v b ++ bpow w c with hW
  set T := D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 2 ^ ((bpow v b).sum + (bpow w c).sum) +
      D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 3 ^ ((bpow v b).length + (bpow w c).length) +
      D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 2 ^ (bpow v b).sum * 3 ^ (bpow w c).length
  have key : (2 : ℤ) ^ (bpow u a).sum * 3 ^ 0 * T =
      -(D (2 : ℤ) 3 u * D 2 3 v * D 2 3 w * Sz W) + S (2 : ℤ) 3 w * D 2 3 u * D 2 3 v * Dz W +
        D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * Dz W := by
    rw [Sz, hid]
    simp only [Dz, D, hW, List.sum_append, List.length_append, pow_add, T]
    ring
  have : Dz W ∣ (2 : ℤ) ^ (bpow u a).sum * 3 ^ 0 * T := by
    rw [key]
    exact dvd_add (dvd_add (dvd_neg.2 (dvd_mul_of_dvd_right hS _)) (dvd_mul_left _ _))
      (dvd_mul_left _ _)
  exact CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this

/-! ## Three letter runs `1^a d^b e^c` -/

lemma D_letter (d : ℕ) : D (2 : ℤ) 3 [d] = 2 ^ d - 3 := by simp [D]

lemma D_one : D (2 : ℤ) 3 [1] = -1 := by norm_num [D]

lemma core_e1 (e : ℕ) : core (2 : ℤ) 3 [e] [1] = 2 ^ e - 2 := by simp [core, D]; ring

lemma core_1d (d : ℕ) : core (2 : ℤ) 3 [1] [d] = 2 - 2 ^ d := by simp [core, D]; ring

lemma core_de (d e : ℕ) : core (2 : ℤ) 3 [d] [e] = 2 ^ d - 2 ^ e := by simp [core, D]

lemma bpow_letter_sum (x n : ℕ) : (bpow [x] n).sum = n * x := by
  rw [SignedCycles.bpow_singleton]; simp [List.sum_replicate]

lemma bpow_letter_length (x n : ℕ) : (bpow [x] n).length = n := by
  rw [SignedCycles.bpow_singleton]; simp

/-- `2`-adic nonvanishing: `T ≡ 2^μ·(odd) (mod 2^{μ+1})` forces `T ≠ 0`. -/
lemma ne_zero_of_two_adic {T m : ℤ} {μ : ℕ} (hm : Odd m) (hT : (2 : ℤ) ^ (μ + 1) ∣ T - 2 ^ μ * m) :
    T ≠ 0 := by
  rintro rfl
  obtain ⟨K, hK⟩ := hT
  rw [pow_succ] at hK
  have h : (2 : ℤ) ^ μ * (m + 2 * K) = 0 := by linear_combination -hK
  have h2 : (2 : ℤ) ^ μ ≠ 0 := by positivity
  have := (mul_eq_zero.1 h).resolve_left h2
  obtain ⟨k, hk⟩ := hm
  omega

lemma odd_two_pow_sub_three {e : ℕ} (he : 1 ≤ e) : Odd ((2 : ℤ) ^ e - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  exact ⟨2 ^ k - 2, by rw [pow_succ]; ring⟩

lemma four_dvd_two_pow {n : ℕ} (hn : 2 ≤ n) : (4 : ℤ) ∣ 2 ^ n := by
  have := pow_dvd_pow (2 : ℤ) hn
  simpa using this

lemma two_dvd_two_sub_two_pow {d : ℕ} (hd : 1 ≤ d) : (2 : ℤ) ∣ 2 - 2 ^ d := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  exact ⟨1 - 2 ^ k, by rw [pow_succ]; ring⟩

lemma two_dvd_two_pow_sub_two {e : ℕ} (he : 1 ≤ e) : (2 : ℤ) ∣ 2 ^ e - 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  exact ⟨2 ^ k - 1, by rw [pow_succ]; ring⟩

/-- `T_U ≠ 0` (it is `≡ 2 (mod 4)`). -/
lemma TU_ne {b c d e : ℕ} (hb : 1 ≤ b) (hd : 2 ≤ d) (he : 2 ≤ e) :
    (2 ^ d - 3) * (2 ^ e - 2) * 2 ^ (b * d + c * e) + (2 ^ e - 3) * (2 - 2 ^ d) * 3 ^ (b + c) +
      (-(2 ^ d - 2 ^ e)) * (2 ^ (b * d) * 3 ^ c) ≠ (0 : ℤ) := by
  apply ne_zero_of_two_adic (μ := 1) (m := (2 ^ e - 3) * 3 ^ (b + c))
    ((odd_two_pow_sub_three (by omega)).mul (Odd.pow (by decide)))
  have e1 : (2 : ℤ) ^ (1 + 1) = 4 := by norm_num
  rw [e1]
  have h1 := four_dvd_two_pow (n := b * d + c * e) (by nlinarith)
  have h2 := four_dvd_two_pow (n := d) hd
  have h3 := four_dvd_two_pow (n := b * d) (by nlinarith)
  have : ((2 : ℤ) ^ d - 3) * (2 ^ e - 2) * 2 ^ (b * d + c * e) + (2 ^ e - 3) * (2 - 2 ^ d) * 3 ^ (b + c) +
      (-(2 ^ d - 2 ^ e)) * (2 ^ (b * d) * 3 ^ c) - 2 ^ 1 * ((2 ^ e - 3) * 3 ^ (b + c)) =
      ((2 ^ d - 3) * (2 ^ e - 2)) * 2 ^ (b * d + c * e) - ((2 ^ e - 3) * 3 ^ (b + c)) * 2 ^ d -
        ((2 ^ d - 2 ^ e) * 3 ^ c) * 2 ^ (b * d) := by ring
  rw [this]
  exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _))
    (dvd_mul_of_dvd_right h3 _)

/-- `T_Z ≠ 0` (it is `≡ 2 (mod 4)`). -/
lemma TZ_ne {a b d e : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 2 ≤ d) (he : 2 ≤ e) :
    (-(2 ^ d - 2 ^ e)) * 2 ^ (a + b * d) + (2 ^ d - 3) * (2 ^ e - 2) * 3 ^ (a + b) +
      (2 ^ e - 3) * (2 - 2 ^ d) * (2 ^ a * 3 ^ b) ≠ (0 : ℤ) := by
  apply ne_zero_of_two_adic (μ := 1) (m := -((2 ^ d - 3) * 3 ^ (a + b)))
    (((odd_two_pow_sub_three (by omega)).mul (Odd.pow (by decide))).neg)
  have e1 : (2 : ℤ) ^ (1 + 1) = 4 := by norm_num
  rw [e1]
  have h1 := four_dvd_two_pow (n := a + b * d) (by nlinarith)
  have h2 := four_dvd_two_pow (n := e) he
  have h3 : (4 : ℤ) ∣ (2 - 2 ^ d) * 2 ^ a := by
    have := mul_dvd_mul (two_dvd_two_sub_two_pow (d := d) (by omega))
      (dvd_pow_self (2 : ℤ) (show a ≠ 0 by omega))
    simpa [show (2 : ℤ) * 2 = 4 by norm_num] using this
  have : (-(2 ^ d - 2 ^ e) : ℤ) * 2 ^ (a + b * d) + (2 ^ d - 3) * (2 ^ e - 2) * 3 ^ (a + b) +
      (2 ^ e - 3) * (2 - 2 ^ d) * (2 ^ a * 3 ^ b) - 2 ^ 1 * (-((2 ^ d - 3) * 3 ^ (a + b))) =
      (-(2 ^ d - 2 ^ e)) * 2 ^ (a + b * d) + ((2 ^ d - 3) * 3 ^ (a + b)) * 2 ^ e +
        ((2 ^ e - 3) * 3 ^ b) * ((2 - 2 ^ d) * 2 ^ a) := by ring
  rw [this]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _))
    (dvd_mul_of_dvd_right h3 _)

/-- `T_V ≠ 0` (it is `2^{min(d,e)}·odd` modulo `2^{min(d,e)+1}`). -/
lemma TV_ne {a c d e : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e) (hde : d ≠ e) :
    (2 ^ e - 3) * (2 - 2 ^ d) * 2 ^ (c * e + a) + (-(2 ^ d - 2 ^ e)) * 3 ^ (c + a) +
      (2 ^ d - 3) * (2 ^ e - 2) * (2 ^ (c * e) * 3 ^ a) ≠ (0 : ℤ) := by
  rcases lt_or_gt_of_ne hde with hlt | hgt
  · -- `d < e`: `μ = d`
    obtain ⟨s, rfl⟩ : ∃ s, e = d + s + 1 := ⟨e - d - 1, by omega⟩
    apply ne_zero_of_two_adic (μ := d) (m := (2 ^ (s + 1) - 1) * 3 ^ (c + a))
      ((show Odd ((2 : ℤ) ^ (s + 1) - 1) from ⟨2 ^ s - 1, by rw [pow_succ]; ring⟩).mul
        (Odd.pow (by decide)))
    have h1 : (2 : ℤ) ^ (d + 1) ∣ 2 ^ (c * (d + s + 1) + a) := pow_dvd_pow 2 (by nlinarith)
    have h3 : (2 : ℤ) ^ (d + 1) ∣ 2 ^ (c * (d + s + 1)) * (2 ^ (d + s + 1) - 2) := by
      rw [pow_succ]
      exact mul_dvd_mul (pow_dvd_pow 2 (by nlinarith)) (two_dvd_two_pow_sub_two (by omega))
    have : ((2 : ℤ) ^ (d + s + 1) - 3) * (2 - 2 ^ d) * 2 ^ (c * (d + s + 1) + a) +
        (-(2 ^ d - 2 ^ (d + s + 1))) * 3 ^ (c + a) +
        (2 ^ d - 3) * (2 ^ (d + s + 1) - 2) * (2 ^ (c * (d + s + 1)) * 3 ^ a) -
        2 ^ d * ((2 ^ (s + 1) - 1) * 3 ^ (c + a)) =
        ((2 ^ (d + s + 1) - 3) * (2 - 2 ^ d)) * 2 ^ (c * (d + s + 1) + a) +
          ((2 ^ d - 3) * 3 ^ a) * (2 ^ (c * (d + s + 1)) * (2 ^ (d + s + 1) - 2)) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h3 _)
  · -- `e < d`: `μ = e`
    obtain ⟨s, rfl⟩ : ∃ s, d = e + s + 1 := ⟨d - e - 1, by omega⟩
    apply ne_zero_of_two_adic (μ := e) (m := -((2 ^ (s + 1) - 1) * 3 ^ (c + a)))
      (((show Odd ((2 : ℤ) ^ (s + 1) - 1) from ⟨2 ^ s - 1, by rw [pow_succ]; ring⟩).mul
        (Odd.pow (by decide))).neg)
    have h1 : (2 : ℤ) ^ (e + 1) ∣ 2 ^ (c * e + a) := pow_dvd_pow 2 (by nlinarith)
    have h3 : (2 : ℤ) ^ (e + 1) ∣ 2 ^ (c * e) * (2 ^ e - 2) := by
      rw [pow_succ]
      exact mul_dvd_mul (pow_dvd_pow 2 (by nlinarith)) (two_dvd_two_pow_sub_two (by omega))
    have : ((2 : ℤ) ^ e - 3) * (2 - 2 ^ (e + s + 1)) * 2 ^ (c * e + a) +
        (-(2 ^ (e + s + 1) - 2 ^ e)) * 3 ^ (c + a) +
        (2 ^ (e + s + 1) - 3) * (2 ^ e - 2) * (2 ^ (c * e) * 3 ^ a) -
        2 ^ e * (-((2 ^ (s + 1) - 1) * 3 ^ (c + a))) =
        ((2 ^ e - 3) * (2 - 2 ^ (e + s + 1))) * 2 ^ (c * e + a) +
          ((2 ^ (e + s + 1) - 3) * 3 ^ a) * (2 ^ (c * e) * (2 ^ e - 2)) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h3 _)

/-- Size: `|c₁m₁ + c₂m₂ + c₃m₃| < 4KM` when `|cᵢ| ≤ K` and `0 ≤ mᵢ ≤ M`. -/
lemma abs_three_lt {c₁ c₂ c₃ m₁ m₂ m₃ K M : ℤ} (h1 : |c₁| ≤ K) (h2 : |c₂| ≤ K) (h3 : |c₃| ≤ K)
    (n1 : 0 ≤ m₁) (n2 : 0 ≤ m₂) (n3 : 0 ≤ m₃) (l1 : m₁ ≤ M) (l2 : m₂ ≤ M) (l3 : m₃ ≤ M)
    (hK : 0 < K) (hM : 0 < M) : |c₁ * m₁ + c₂ * m₂ + c₃ * m₃| < 4 * K * M := by
  have e1 : |c₁ * m₁| ≤ K * M := by
    rw [abs_mul, abs_of_nonneg n1]; exact mul_le_mul h1 l1 n1 hK.le
  have e2 : |c₂ * m₂| ≤ K * M := by
    rw [abs_mul, abs_of_nonneg n2]; exact mul_le_mul h2 l2 n2 hK.le
  have e3 : |c₃ * m₃| ≤ K * M := by
    rw [abs_mul, abs_of_nonneg n3]; exact mul_le_mul h3 l3 n3 hK.le
  calc |c₁ * m₁ + c₂ * m₂ + c₃ * m₃| ≤ |c₁ * m₁ + c₂ * m₂| + |c₃ * m₃| := abs_add_le _ _
    _ ≤ |c₁ * m₁| + |c₂ * m₂| + |c₃ * m₃| := by linarith [abs_add_le (c₁ * m₁) (c₂ * m₂)]
    _ < 4 * K * M := by nlinarith [mul_pos hK hM]

/-- The three coefficients are at most `2^d 2^e` in absolute value. -/
lemma coef_bounds {d e : ℕ} (hd : 2 ≤ d) (he : 2 ≤ e) :
    |((2 : ℤ) ^ d - 3) * (2 ^ e - 2)| ≤ 2 ^ d * 2 ^ e ∧
    |((2 : ℤ) ^ e - 3) * (2 - 2 ^ d)| ≤ 2 ^ d * 2 ^ e ∧
    |(-((2 : ℤ) ^ d - 2 ^ e))| ≤ 2 ^ d * 2 ^ e := by
  have hD : (4 : ℤ) ≤ 2 ^ d := by
    have := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by norm_num) hd; simpa using this
  have hE : (4 : ℤ) ≤ 2 ^ e := by
    have := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by norm_num) he; simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_nonneg (by nlinarith)]; nlinarith
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_neg, abs_le]; constructor <;> nlinarith

lemma three_pow_le_two_pow {d n : ℕ} (hd : 2 ≤ d) : (3 : ℤ) ^ n ≤ 2 ^ (n * d) := by
  calc (3 : ℤ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    _ = 2 ^ (n * 2) := by rw [pow_mul']; norm_num
    _ ≤ 2 ^ (n * d) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left n hd)

lemma two_pow_le_three_pow (n : ℕ) : (2 : ℤ) ^ n ≤ 3 ^ n :=
  pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- **Three letter runs.** Given Ellison, no cycle of either sign has a gap word that is a rotation of
`1^a d^b e^c` (`a, b, c ≥ 1`, `d, e ≥ 2`, `d ≠ e`) once `E = a + bd + ce ≥ 11(d + e + 2)`. -/
theorem three_letter_runs (hEl : CycleLiterature.Ellison1971) {d e : ℕ} (hd : 2 ≤ d) (he : 2 ≤ e)
    (hde : d ≠ e) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c)
    (hw : gapWord x o ~r List.replicate a 1 ++ List.replicate b d ++ List.replicate c e)
    (hE : 11 * (d + e + 2) ≤ a + b * d + c * e) : False := by
  have hw1 : gapWord x o ~r bpow [1] a ++ bpow [d] b ++ bpow [e] c := by
    rw [SignedCycles.bpow_singleton, SignedCycles.bpow_singleton, SignedCycles.bpow_singleton]
    exact hw
  have hw2 : gapWord x o ~r bpow [d] b ++ bpow [e] c ++ bpow [1] a := by
    refine hw1.trans ?_
    have := List.isRotated_append (l := bpow [1] a) (l' := bpow [d] b ++ bpow [e] c)
    simpa [List.append_assoc] using this
  have hw3 : gapWord x o ~r bpow [e] c ++ bpow [1] a ++ bpow [d] b := by
    refine hw2.trans ?_
    have := List.isRotated_append (l := bpow [d] b) (l' := bpow [e] c ++ bpow [1] a)
    simpa [List.append_assoc] using this
  have hsU := bpow_letter_sum 1 a
  have hsV := bpow_letter_sum d b
  have hsZ := bpow_letter_sum e c
  have hlU := bpow_letter_length 1 a
  have hlV := bpow_letter_length d b
  have hlZ := bpow_letter_length e c
  simp only [mul_one] at hsU
  set E := a + b * d + c * e with hE_def
  set o' := a + b + c with ho'
  have hlen : o = o' := by
    have := hw1.perm.length_eq
    simp only [gapWord_length, List.length_append, hlU, hlV, hlZ] at this
    omega
  -- `D` of each rotation is `2^E - 3^o`
  have hDval : ∀ W : Word, W.sum = E → W.length = o' → Dz W = 2 ^ E - 3 ^ o' := by
    intro W hs hl; simp only [Dz, D, hs, hl]
  have hsum3 : ∀ P Q R : Word, (P ++ Q ++ R).sum = P.sum + Q.sum + R.sum := by
    intro P Q R; simp only [List.sum_append]
  have hlen3 : ∀ P Q R : Word, (P ++ Q ++ R).length = P.length + Q.length + R.length := by
    intro P Q R; simp only [List.length_append]
  have hEpos : 0 < E := by omega
  -- the three divisibilities, in explicit form
  have ne3 : ∀ P Q R : Word, (P ++ Q ++ R).sum = E → P ++ Q ++ R ≠ [] := by
    intro P Q R hs h0; rw [h0] at hs; simp at hs; omega
  have d1 := dvd_three_runs h hw1 (ne3 _ _ _ (by rw [hsum3, hsU, hsV, hsZ])) (by rw [hsum3]; omega)
  have d2 := dvd_three_runs h hw2 (ne3 _ _ _ (by rw [hsum3, hsU, hsV, hsZ]; ring))
    (by rw [hsum3]; omega)
  have d3 := dvd_three_runs h hw3 (ne3 _ _ _ (by rw [hsum3, hsU, hsV, hsZ]; ring))
    (by rw [hsum3]; omega)
  rw [D_letter, D_letter, D_one, core_e1, core_1d, core_de, hsV, hsZ, hlV, hlZ,
    hDval _ (by rw [hsum3, hsU, hsV, hsZ]) (by rw [hlen3, hlU, hlV, hlZ])] at d1
  rw [D_one, D_letter, D_letter, core_e1, core_1d, core_de, hsZ, hsU, hlZ, hlU,
    hDval _ (by rw [hsum3, hsU, hsV, hsZ]; ring) (by rw [hlen3, hlU, hlV, hlZ]; ring)] at d2
  rw [D_one, D_letter, D_letter, core_e1, core_1d, core_de, hsU, hsV, hlU, hlV,
    hDval _ (by rw [hsum3, hsU, hsV, hsZ]; ring) (by rw [hlen3, hlU, hlV, hlZ]; ring)] at d3
  -- explicit forms
  have eU : ((2 : ℤ) ^ d - 3) * (2 ^ e - 2) * 2 ^ (b * d + c * e) +
      (2 ^ e - 3) * (2 - 2 ^ d) * 3 ^ (b + c) + -1 * (2 ^ d - 2 ^ e) * 2 ^ (b * d) * 3 ^ c =
      ((2 : ℤ) ^ d - 3) * (2 ^ e - 2) * 2 ^ (b * d + c * e) +
      (2 ^ e - 3) * (2 - 2 ^ d) * 3 ^ (b + c) + (-(2 ^ d - 2 ^ e)) * (2 ^ (b * d) * 3 ^ c) := by ring
  have eV : ((2 : ℤ) ^ e - 3) * (2 - 2 ^ d) * 2 ^ (c * e + a) + -1 * (2 ^ d - 2 ^ e) * 3 ^ (c + a) +
      (2 ^ d - 3) * (2 ^ e - 2) * 2 ^ (c * e) * 3 ^ a =
      ((2 : ℤ) ^ e - 3) * (2 - 2 ^ d) * 2 ^ (c * e + a) + (-(2 ^ d - 2 ^ e)) * 3 ^ (c + a) +
      (2 ^ d - 3) * (2 ^ e - 2) * (2 ^ (c * e) * 3 ^ a) := by ring
  have eZ : -1 * ((2 : ℤ) ^ d - 2 ^ e) * 2 ^ (a + b * d) + (2 ^ d - 3) * (2 ^ e - 2) * 3 ^ (a + b) +
      (2 ^ e - 3) * (2 - 2 ^ d) * 2 ^ a * 3 ^ b =
      (-((2 : ℤ) ^ d - 2 ^ e)) * 2 ^ (a + b * d) + (2 ^ d - 3) * (2 ^ e - 2) * 3 ^ (a + b) +
      (2 ^ e - 3) * (2 - 2 ^ d) * (2 ^ a * 3 ^ b) := by ring
  rw [eU] at d1
  rw [eV] at d2
  rw [eZ] at d3
  -- sizes
  obtain ⟨k1, k2, k3⟩ := coef_bounds hd he
  have hK : (0 : ℤ) < 2 ^ d * 2 ^ e := by positivity
  have p2 : ∀ n : ℕ, (0 : ℤ) ≤ 2 ^ n := fun n => by positivity
  have p3 : ∀ n : ℕ, (0 : ℤ) ≤ 3 ^ n := fun n => by positivity
  have t3b := three_pow_le_two_pow (n := b) hd
  have t3c := three_pow_le_two_pow (n := c) he
  have t2a := two_pow_le_three_pow a
  have bU : |((2 : ℤ) ^ d - 3) * (2 ^ e - 2) * 2 ^ (b * d + c * e) +
      (2 ^ e - 3) * (2 - 2 ^ d) * 3 ^ (b + c) + (-(2 ^ d - 2 ^ e)) * (2 ^ (b * d) * 3 ^ c)| <
      4 * (2 ^ d * 2 ^ e) * 2 ^ (b * d + c * e) := by
    refine abs_three_lt k1 k2 k3 (p2 _) (p3 _) (by positivity) le_rfl ?_ ?_ hK (by positivity)
    · rw [pow_add, pow_add]; exact mul_le_mul t3b t3c (p3 _) (p2 _)
    · rw [pow_add]; exact mul_le_mul_of_nonneg_left t3c (p2 _)
  have bV : |((2 : ℤ) ^ e - 3) * (2 - 2 ^ d) * 2 ^ (c * e + a) + (-(2 ^ d - 2 ^ e)) * 3 ^ (c + a) +
      (2 ^ d - 3) * (2 ^ e - 2) * (2 ^ (c * e) * 3 ^ a)| < 4 * (2 ^ d * 2 ^ e) * (2 ^ (c * e) * 3 ^ a) := by
    refine abs_three_lt k2 k3 k1 (p2 _) (p3 _) (by positivity) ?_ ?_ le_rfl hK (by positivity)
    · rw [pow_add]; exact mul_le_mul_of_nonneg_left t2a (p2 _)
    · rw [pow_add]; exact mul_le_mul t3c le_rfl (p3 _) (p2 _)
  have bZ : |(-((2 : ℤ) ^ d - 2 ^ e)) * 2 ^ (a + b * d) + (2 ^ d - 3) * (2 ^ e - 2) * 3 ^ (a + b) +
      (2 ^ e - 3) * (2 - 2 ^ d) * (2 ^ a * 3 ^ b)| < 4 * (2 ^ d * 2 ^ e) * (2 ^ (b * d) * 3 ^ a) := by
    refine abs_three_lt k3 k1 k2 (p2 _) (p3 _) (by positivity) ?_ ?_ ?_ hK (by positivity)
    · rw [pow_add, mul_comm]; exact mul_le_mul_of_nonneg_left t2a (p2 _)
    · rw [pow_add, mul_comm]; exact mul_le_mul_of_nonneg_right t3b (p3 _)
    · rw [mul_comm]; exact mul_le_mul t3b t2a (p2 _) (p2 _)
  -- `|D| < 4·2^d·2^e·M` for each
  have lt_of : ∀ {T M : ℤ}, T ≠ 0 → (2 : ℤ) ^ E - 3 ^ o' ∣ T → |T| < M → |(2 : ℤ) ^ E - 3 ^ o'| < M :=
    fun hT hdv hM => lt_of_le_of_lt (Int.le_of_dvd (abs_pos.2 hT) ((abs_dvd_abs _ _).2 hdv)) hM
  have LU := lt_of (TU_ne (c := c) hb hd he) d1 bU
  have LV := lt_of (TV_ne ha hc hd he hde) d2 bV
  have LZ := lt_of (TZ_ne ha hb hd he) d3 bZ
  -- Ellison
  have hnot : E ∉ CycleLiterature.ellisonExceptions := Frontier.not_mem_exceptions (by omega)
  have hEl' := hEl E o' hEpos (by omega) hnot
  have toR : ∀ {p q : ℕ}, |(2 : ℤ) ^ E - 3 ^ o'| < 2 ^ p * 3 ^ q →
      (2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10) < 2 ^ p * 3 ^ q := by
    intro p q hlt
    refine hEl'.trans ?_
    have := (Int.cast_lt (R := ℝ)).2 hlt
    push_cast at this; exact this
  have rU : |(2 : ℤ) ^ E - 3 ^ o'| < 2 ^ (d + e + 2 + (b * d + c * e)) * 3 ^ 0 := by
    have : (4 : ℤ) * (2 ^ d * 2 ^ e) * 2 ^ (b * d + c * e) = 2 ^ (d + e + 2 + (b * d + c * e)) * 3 ^ 0 := by
      rw [pow_zero, mul_one, pow_add, pow_add, pow_add]; ring
    rw [← this]; exact LU
  have rV : |(2 : ℤ) ^ E - 3 ^ o'| < 2 ^ (d + e + 2 + c * e) * 3 ^ a := by
    have : (4 : ℤ) * (2 ^ d * 2 ^ e) * (2 ^ (c * e) * 3 ^ a) = 2 ^ (d + e + 2 + c * e) * 3 ^ a := by
      rw [pow_add, pow_add, pow_add]; ring
    rw [← this]; exact LV
  have rZ : |(2 : ℤ) ^ E - 3 ^ o'| < 2 ^ (d + e + 2 + b * d) * 3 ^ a := by
    have : (4 : ℤ) * (2 ^ d * 2 ^ e) * (2 ^ (b * d) * 3 ^ a) = 2 ^ (d + e + 2 + b * d) * 3 ^ a := by
      rw [pow_add, pow_add, pow_add]; ring
    rw [← this]; exact LZ
  have iU := EqualTwoCycles.lin_of_lt hEpos (toR rU)
  have iV := EqualTwoCycles.lin_of_lt hEpos (toR rV)
  have iZ := EqualTwoCycles.lin_of_lt hEpos (toR rZ)
  omega

/-! ## Every block triple -/

/-- Linearised comparison of monomials `2^p 3^q`, using `1584 < 1000 log₂ 3 < 1585`. -/
lemma lin2 {p q r s : ℕ} (h : (2 : ℤ) ^ p * 3 ^ q < 2 ^ r * 3 ^ s) :
    1000 * p + 1584 * q < 1000 * r + 1585 * s := by
  have hr : (2 : ℝ) ^ p * 3 ^ q < 2 ^ r * 3 ^ s := by exact_mod_cast h
  have hl := Real.log_lt_log (by positivity) hr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hl
  obtain ⟨l3a, l3b⟩ := Repeat.log_three_bounds
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (0 : ℝ) ≤ q := by positivity
  have hs : (0 : ℝ) ≤ s := by positivity
  have key : ((1000 * p + 1584 * q : ℕ) : ℝ) * Real.log 2 < ((1000 * r + 1585 * s : ℕ) : ℝ) * Real.log 2 := by
    push_cast
    nlinarith [mul_nonneg hq (show (0 : ℝ) ≤ 1000 * Real.log 3 - 1584 * Real.log 2 by linarith),
      mul_nonneg hs (show (0 : ℝ) ≤ 1585 * Real.log 2 - 1000 * Real.log 3 by linarith)]
  exact_mod_cast lt_of_mul_lt_mul_right key hl2.le

/-- Non-strict version of `lin2`. -/
lemma lin2_le {p q r s : ℕ} (h : (2 : ℤ) ^ p * 3 ^ q ≤ 2 ^ r * 3 ^ s) :
    1000 * p + 1584 * q ≤ 1000 * r + 1585 * s := by
  have hr : (2 : ℝ) ^ p * 3 ^ q ≤ 2 ^ r * 3 ^ s := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) hr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hl
  obtain ⟨l3a, l3b⟩ := Repeat.log_three_bounds
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (0 : ℝ) ≤ q := by positivity
  have hs : (0 : ℝ) ≤ s := by positivity
  have key : ((1000 * p + 1584 * q : ℕ) : ℝ) * Real.log 2 ≤ ((1000 * r + 1585 * s : ℕ) : ℝ) * Real.log 2 := by
    push_cast
    nlinarith [mul_nonneg hq (show (0 : ℝ) ≤ 1000 * Real.log 3 - 1584 * Real.log 2 by linarith),
      mul_nonneg hs (show (0 : ℝ) ≤ 1585 * Real.log 2 - 1000 * Real.log 3 by linarith)]
  exact_mod_cast le_of_mul_le_mul_right key hl2

/-- `|c₁m₁ + c₂m₂ + c₃m₃| < 2^{K+2}·mᵢ` for the largest `mᵢ`. -/
lemma abs_lt_some {c₁ c₂ c₃ m₁ m₂ m₃ : ℤ} {K : ℕ} (h1 : |c₁| ≤ 2 ^ K) (h2 : |c₂| ≤ 2 ^ K)
    (h3 : |c₃| ≤ 2 ^ K) (n1 : 0 < m₁) (n2 : 0 < m₂) (n3 : 0 < m₃) :
    |c₁ * m₁ + c₂ * m₂ + c₃ * m₃| < 2 ^ (K + 2) * m₁ ∨ |c₁ * m₁ + c₂ * m₂ + c₃ * m₃| < 2 ^ (K + 2) * m₂ ∨
      |c₁ * m₁ + c₂ * m₂ + c₃ * m₃| < 2 ^ (K + 2) * m₃ := by
  have hb := abs_three_lt h1 h2 h3 n1.le n2.le n3.le (le_max_left m₁ (max m₂ m₃))
    ((le_max_left m₂ m₃).trans (le_max_right _ _)) ((le_max_right m₂ m₃).trans (le_max_right _ _))
    (by positivity) (lt_max_of_lt_left n1)
  rw [show (4 : ℤ) * 2 ^ K = 2 ^ (K + 2) by rw [pow_add]; ring] at hb
  rcases max_choice m₁ (max m₂ m₃) with h | h <;> rw [h] at hb
  · exact Or.inl hb
  · rcases max_choice m₂ m₃ with h' | h' <;> rw [h'] at hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)

/-- **Three runs, any blocks.** Given Ellison, let `u, v, w` be positive blocks and `a, b, c ∈ ℕ`,
with the three coefficients `D(v)C(w,u)`, `D(w)C(u,v)`, `D(u)C(v,w)` at most `2^K` in absolute value and
`T_U, T_V, T_Z ≠ 0`. Then no cycle of either sign has a gap word that is a rotation of `u^a v^b w^c` with
`E ≥ 20(K + 2)`. -/
theorem three_runs_bounded (hEl : CycleLiterature.Ellison1971) {u v w : Word} (hu : u.Pos)
    (hv : v.Pos) (hw' : w.Pos) {a b c K : ℕ}
    (hK1 : |D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u| ≤ 2 ^ K)
    (hK2 : |D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v| ≤ 2 ^ K)
    (hK3 : |D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w| ≤ 2 ^ K)
    (hTU : D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 2 ^ ((bpow v b).sum + (bpow w c).sum) +
      D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 3 ^ ((bpow v b).length + (bpow w c).length) +
      D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 2 ^ (bpow v b).sum * 3 ^ (bpow w c).length ≠ 0)
    (hTV : D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 2 ^ ((bpow w c).sum + (bpow u a).sum) +
      D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 3 ^ ((bpow w c).length + (bpow u a).length) +
      D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 2 ^ (bpow w c).sum * 3 ^ (bpow u a).length ≠ 0)
    (hTZ : D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 2 ^ ((bpow u a).sum + (bpow v b).sum) +
      D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 3 ^ ((bpow u a).length + (bpow v b).length) +
      D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 2 ^ (bpow u a).sum * 3 ^ (bpow v b).length ≠ 0)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hrot : gapWord x o ~r bpow u a ++ bpow v b ++ bpow w c)
    (hE : 20 * (K + 2) ≤ (bpow u a).sum + (bpow v b).sum + (bpow w c).sum) : False := by
  set EU := (bpow u a).sum
  set EV := (bpow v b).sum
  set EZ := (bpow w c).sum
  set oU := (bpow u a).length
  set oV := (bpow v b).length
  set oZ := (bpow w c).length
  set c₁ := D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u
  set c₂ := D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v
  set c₃ := D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w
  -- lengths below sums
  have lU : oU ≤ EU := CycleLiterature.length_le_sum (pos_bpow hu a)
  have lV : oV ≤ EV := CycleLiterature.length_le_sum (pos_bpow hv b)
  have lZ : oZ ≤ EZ := CycleLiterature.length_le_sum (pos_bpow hw' c)
  -- rotations
  have hr2 : gapWord x o ~r bpow v b ++ bpow w c ++ bpow u a := by
    refine hrot.trans ?_
    have := List.isRotated_append (l := bpow u a) (l' := bpow v b ++ bpow w c)
    simpa [List.append_assoc] using this
  have hr3 : gapWord x o ~r bpow w c ++ bpow u a ++ bpow v b := by
    refine hr2.trans ?_
    have := List.isRotated_append (l := bpow v b) (l' := bpow w c ++ bpow u a)
    simpa [List.append_assoc] using this
  set E := EU + EV + EZ
  set oo := oU + oV + oZ
  have hsum3 : ∀ P Q R : Word, (P ++ Q ++ R).sum = P.sum + Q.sum + R.sum := by
    intro P Q R; simp only [List.sum_append]
  have hlen3 : ∀ P Q R : Word, (P ++ Q ++ R).length = P.length + Q.length + R.length := by
    intro P Q R; simp only [List.length_append]
  have hDv : ∀ W : Word, W.sum = E → W.length = oo → Dz W = 2 ^ E - 3 ^ oo := by
    intro W hs hl; simp only [Dz, D, hs, hl]
  have ne3 : ∀ P Q R : Word, (P ++ Q ++ R).sum = E → P ++ Q ++ R ≠ [] := by
    intro P Q R hs h0; rw [h0] at hs; simp at hs; omega
  have d1 := dvd_three_runs h hrot (ne3 _ _ _ (hsum3 _ _ _)) (by rw [hsum3]; omega)
  have d2 := dvd_three_runs h hr2 (ne3 _ _ _ (by rw [hsum3]; ring)) (by rw [hsum3]; omega)
  have d3 := dvd_three_runs h hr3 (ne3 _ _ _ (by rw [hsum3]; ring)) (by rw [hsum3]; omega)
  rw [hDv _ (hsum3 _ _ _) (hlen3 _ _ _)] at d1
  rw [hDv _ (by rw [hsum3]; ring) (by rw [hlen3]; ring)] at d2
  rw [hDv _ (by rw [hsum3]; ring) (by rw [hlen3]; ring)] at d3
  -- each `T` gives a bound `|D| < 2^{K+2}·(monomial)`
  have p2 : ∀ n : ℕ, (0 : ℤ) < 2 ^ n := fun n => by positivity
  have p3 : ∀ n : ℕ, (0 : ℤ) < 3 ^ n := fun n => by positivity
  have lt_of : ∀ {T : ℤ}, T ≠ 0 → (2 : ℤ) ^ E - 3 ^ oo ∣ T → ∀ {M : ℤ}, |T| < M →
      |(2 : ℤ) ^ E - 3 ^ oo| < M :=
    fun hT hdv _ hM => lt_of_le_of_lt (Int.le_of_dvd (abs_pos.2 hT) ((abs_dvd_abs _ _).2 hdv)) hM
  have mono : ∀ α β : ℕ, (2 : ℤ) ^ (K + 2) * (2 ^ α * 3 ^ β) = 2 ^ (K + 2 + α) * 3 ^ β := by
    intro α β; rw [pow_add]; ring
  have BU : |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + (EV + EZ)) * 3 ^ 0 ∨
      |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + 0) * 3 ^ (oV + oZ) ∨
      |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + EV) * 3 ^ oZ := by
    have eT : c₁ * 2 ^ (EV + EZ) + c₂ * 3 ^ (oV + oZ) + c₃ * 2 ^ EV * 3 ^ oZ =
        c₁ * (2 ^ (EV + EZ) * 3 ^ 0) + c₂ * (2 ^ 0 * 3 ^ (oV + oZ)) + c₃ * (2 ^ EV * 3 ^ oZ) := by ring
    rw [eT] at hTU d1
    rcases abs_lt_some (m₁ := 2 ^ (EV + EZ) * 3 ^ 0) (m₂ := 2 ^ 0 * 3 ^ (oV + oZ))
        (m₃ := 2 ^ EV * 3 ^ oZ) hK1 hK2 hK3 (by positivity) (by positivity) (by positivity)
        with hh | hh | hh
    · left; rw [← mono]; exact lt_of hTU d1 hh
    · right; left; rw [← mono]; exact lt_of hTU d1 hh
    · right; right; rw [← mono]; exact lt_of hTU d1 hh
  have BV : |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + (EZ + EU)) * 3 ^ 0 ∨
      |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + 0) * 3 ^ (oZ + oU) ∨
      |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + EZ) * 3 ^ oU := by
    have eT : c₂ * 2 ^ (EZ + EU) + c₃ * 3 ^ (oZ + oU) + c₁ * 2 ^ EZ * 3 ^ oU =
        c₂ * (2 ^ (EZ + EU) * 3 ^ 0) + c₃ * (2 ^ 0 * 3 ^ (oZ + oU)) + c₁ * (2 ^ EZ * 3 ^ oU) := by ring
    rw [eT] at hTV d2
    rcases abs_lt_some (m₁ := 2 ^ (EZ + EU) * 3 ^ 0) (m₂ := 2 ^ 0 * 3 ^ (oZ + oU))
        (m₃ := 2 ^ EZ * 3 ^ oU) hK2 hK3 hK1 (by positivity) (by positivity) (by positivity)
        with hh | hh | hh
    · left; rw [← mono]; exact lt_of hTV d2 hh
    · right; left; rw [← mono]; exact lt_of hTV d2 hh
    · right; right; rw [← mono]; exact lt_of hTV d2 hh
  have BZ : |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + (EU + EV)) * 3 ^ 0 ∨
      |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + 0) * 3 ^ (oU + oV) ∨
      |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ (K + 2 + EU) * 3 ^ oV := by
    have eT : c₃ * 2 ^ (EU + EV) + c₁ * 3 ^ (oU + oV) + c₂ * 2 ^ EU * 3 ^ oV =
        c₃ * (2 ^ (EU + EV) * 3 ^ 0) + c₁ * (2 ^ 0 * 3 ^ (oU + oV)) + c₂ * (2 ^ EU * 3 ^ oV) := by ring
    rw [eT] at hTZ d3
    rcases abs_lt_some (m₁ := 2 ^ (EU + EV) * 3 ^ 0) (m₂ := 2 ^ 0 * 3 ^ (oU + oV))
        (m₃ := 2 ^ EU * 3 ^ oV) hK3 hK1 hK2 (by positivity) (by positivity) (by positivity)
        with hh | hh | hh
    · left; rw [← mono]; exact lt_of hTZ d3 hh
    · right; left; rw [← mono]; exact lt_of hTZ d3 hh
    · right; right; rw [← mono]; exact lt_of hTZ d3 hh
  -- three regimes for `|D|`
  have hEpos : 0 < E := by omega
  by_cases R1 : 2 * 3 ^ oo ≤ (2 : ℤ) ^ E
  · have reg := lin2_le (p := 1) (q := oo) (r := E) (s := 0) (by simpa [pow_one] using R1)
    have conv : ∀ {p q : ℕ}, |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ p * 3 ^ q → 1000 * E < 1000 * (p + 1) + 1585 * q := by
      intro p q hh
      rw [abs_of_nonneg (by linarith [p3 oo])] at hh
      have : (2 : ℤ) ^ E * 3 ^ 0 < 2 ^ (p + 1) * 3 ^ q := by
        rw [pow_succ]; nlinarith [p3 oo]
      have := lin2 this; omega
    replace BU := BU.imp conv (Or.imp conv conv)
    replace BV := BV.imp conv (Or.imp conv conv)
    replace BZ := BZ.imp conv (Or.imp conv conv)
    rcases BU with iU | iU | iU <;> rcases BV with iV | iV | iV <;> rcases BZ with iZ | iZ | iZ <;> omega
  by_cases R2 : 2 * (2 : ℤ) ^ E ≤ 3 ^ oo
  · have reg := lin2_le (p := E + 1) (q := 0) (r := 0) (s := oo) (by rw [pow_succ]; linarith)
    have conv : ∀ {p q : ℕ}, |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ p * 3 ^ q → 1584 * oo < 1000 * (p + 1) + 1585 * q := by
      intro p q hh
      rw [abs_of_nonpos (by linarith [p2 E])] at hh
      have : (2 : ℤ) ^ 0 * 3 ^ oo < 2 ^ (p + 1) * 3 ^ q := by
        rw [pow_succ]; nlinarith [p2 E]
      have := lin2 this; omega
    replace BU := BU.imp conv (Or.imp conv conv)
    replace BV := BV.imp conv (Or.imp conv conv)
    replace BZ := BZ.imp conv (Or.imp conv conv)
    rcases BU with iU | iU | iU <;> rcases BV with iV | iV | iV <;> rcases BZ with iZ | iZ | iZ <;> omega
  -- the near-critical regime: Ellison
  push_neg at R1 R2
  have regA := lin2 (p := 0) (q := oo) (r := E + 1) (s := 0) (by rw [pow_succ]; linarith)
  have regB := lin2 (p := E) (q := 0) (r := 1) (s := oo) (by linarith)
  have hnot : E ∉ CycleLiterature.ellisonExceptions := Frontier.not_mem_exceptions (by omega)
  have hlen : o = oo := by
    have := hrot.perm.length_eq; rw [gapWord_length, hlen3] at this; exact this
  have hEl' := hEl E oo hEpos (by omega) hnot
  have conv : ∀ {p q : ℕ}, |(2 : ℤ) ^ E - 3 ^ oo| < 2 ^ p * 3 ^ q → 85573 * E < 100000 * p + 158500 * q := by
    intro p q hh
    refine EqualTwoCycles.lin_of_lt hEpos (hEl'.trans ?_)
    have := (Int.cast_lt (R := ℝ)).2 hh
    push_cast at this; exact this
  replace BU := BU.imp conv (Or.imp conv conv)
  replace BV := BV.imp conv (Or.imp conv conv)
  replace BZ := BZ.imp conv (Or.imp conv conv)
  rcases BU with iU | iU | iU <;> rcases BV with iV | iV | iV <;> rcases BZ with iZ | iZ | iZ <;> omega

end Syracuse.ThreeRuns
