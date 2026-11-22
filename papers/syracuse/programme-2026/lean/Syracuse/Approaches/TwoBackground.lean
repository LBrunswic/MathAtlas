import Syracuse.Approaches.CocycleCombine
import Syracuse.Approaches.CycleLiterature
import Syracuse.Approaches.BoundedDefectLever

/-!
# Two growing backgrounds: the words `d₁^a d₂^b`

The fixed-slope families of the bounded-defect lever (`βd^L`, `u^pβ`) are excluded for positive
cycles by the ratio sandwich alone (`Limits.background_bound`). Two-letter cyclic words
`d₁^a d₂^b` with **both** runs growing are different: with `d₁ = 1`, `d₂ = 2` and `b/a ≈ 1.41` their
slope tends to `log₂ 3`, so they reach the critical band. The incubator's "≥ 2 growing runs" no-go
(F2/F3: unit prefactors diverge) concerned *combinations of rotations*. Through the two-term gcd
`G = gcd(S, D)` (`Limits.G_eq_gcd`) these words are tractable.

Write `c_i = X^{d_i} - Y`, `U = X^{d₁a} - Y^a`, `V = X^{d₂b} - Y^b`. Then in any commutative ring:

* `c₁·S(d₁^a) = U`, `c₂·S(d₂^b) = V` (`BoundedDefectLever.S_replicate_mul`);
* `D(d₁^a d₂^b) = X^{d₁a}·V + Y^b·U` (`D_two`);
* `c₁c₂·S - c₂·D = (c₁ - c₂)·X^{d₁a}·V` and `c₁c₂·S - c₁·D = (c₂ - c₁)·Y^b·U` (`key_V`, `key_U`).

So on a genuine cycle (`D ∣ S`, `D` prime to `6`) the cycle denominator divides
`(2^{d₁} - 2^{d₂})·V` and `(2^{d₁} - 2^{d₂})·U` (`dvd_of_cycle`). This is a gcd of two `S`-unit
differences, the Corvaja–Zannier shape `gcd(u - 1, v - 1)`, with no transcendence input.

For `{1, 2}` the factor is `-2`, so `D ∣ gcd(3^a - 2^a, 4^b - 3^b)`. On a positive cycle that forces
`D ≤ 3^a` and `D ≤ 4^b`. Ellison's bound `D > 2^E e^{-E/10}` (`E = a + 2b`) contradicts both
together, because `e^{1/5} < 4/3` and `e^{2/5} < 4`. The finitely many `E ≤ 27` are checked
directly. Result: **no positive Syracuse cycle has a cyclic gap word `1^a 2^b` with `a, b ≥ 1`**
(`no_cycle_one_two`), conditional only on Ellison 1971 (`CycleLiterature.Ellison1971`, a stated
Prop, not an axiom).

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `D(d₁^a d₂^b) = X^{d₁a}V + Y^bU` | `D_two` | proved (generic) |
| `c₁c₂S - c₂D = (c₁-c₂)X^{d₁a}V`, `c₁c₂S - c₁D = (c₂-c₁)Y^bU` | `key_V`, `key_U` | proved (generic) |
| on a cycle `D ∣ (2^{d₁}-2^{d₂})·V` and `D ∣ (2^{d₁}-2^{d₂})·U` | `dvd_of_cycle` | proved |
| `{1,2}`: `S = 3^b u + 2^a v`, `D = 2^a v - 3^b u`, `u = 3^a-2^a`, `v = 4^b-3^b` | `Sz_one_two`, `Dz_one_two` | proved |
| `{1,2}` on a cycle: `D ∣ u` and `D ∣ v` | `dvd_u_v_of_cycle` | proved |
| no positive `1^a 2^b` cycle with `E ≤ 27` | `small_cases` | proved (finite check) |
| no positive `1^a 2^b` cycle (any `a, b ≥ 1`) | `no_cycle_one_two` | proved (conditional on `Ellison1971`) |
| blocks: `D(u)D(v)S(w) - D(v)S(u)D(w) = C(u,v)X^{|u^a|}D(v^b)` and the `U` analogue | `key_block_V`, `key_block_U` | proved (generic) |
| blocks on a cycle: `D ∣ C(u,v)·D(v^b)` and `D ∣ C(u,v)·D(u^a)` | `dvd_of_cycle_block` | proved |
-/

namespace Syracuse.TwoBackground

open Syracuse

/-- The two-background word `d₁^a d₂^b`. -/
def two (d₁ d₂ a b : ℕ) : Word := List.replicate a d₁ ++ List.replicate b d₂

section Ring

variable {R : Type*} [CommRing R] (X Y : R)

/-- `D(d₁^a d₂^b) = X^{d₁a}(X^{d₂b} - Y^b) + Y^b(X^{d₁a} - Y^a)`. -/
theorem D_two (d₁ d₂ a b : ℕ) :
    D X Y (two d₁ d₂ a b) =
      X ^ (a * d₁) * (X ^ (b * d₂) - Y ^ b) + Y ^ b * (X ^ (a * d₁) - Y ^ a) := by
  simp only [D, two, List.sum_append, List.sum_replicate, List.length_append,
    List.length_replicate, smul_eq_mul, pow_add]
  ring

/-- `S(d₁^a d₂^b) = Y^b S(d₁^a) + X^{d₁a} S(d₂^b)`. -/
theorem S_two (d₁ d₂ a b : ℕ) :
    S X Y (two d₁ d₂ a b) =
      Y ^ b * S X Y (List.replicate a d₁) + X ^ (a * d₁) * S X Y (List.replicate b d₂) := by
  rw [two, S_append, List.length_replicate, List.sum_replicate, smul_eq_mul]

/-- **Key identity for `V`.** `c₁c₂S - c₂D = (c₁ - c₂)X^{d₁a}V`. -/
theorem key_V (d₁ d₂ a b : ℕ) :
    (X ^ d₁ - Y) * (X ^ d₂ - Y) * S X Y (two d₁ d₂ a b) - (X ^ d₂ - Y) * D X Y (two d₁ d₂ a b) =
      (X ^ d₁ - X ^ d₂) * X ^ (a * d₁) * (X ^ (b * d₂) - Y ^ b) := by
  have h1 := BoundedDefectLever.S_replicate_mul X Y d₁ a
  have h2 := BoundedDefectLever.S_replicate_mul X Y d₂ b
  rw [S_two, D_two]
  linear_combination (X ^ d₂ - Y) * Y ^ b * h1 + (X ^ d₁ - Y) * X ^ (a * d₁) * h2

/-- **Key identity for `U`.** `c₁c₂S - c₁D = (c₂ - c₁)Y^bU`. -/
theorem key_U (d₁ d₂ a b : ℕ) :
    (X ^ d₁ - Y) * (X ^ d₂ - Y) * S X Y (two d₁ d₂ a b) - (X ^ d₁ - Y) * D X Y (two d₁ d₂ a b) =
      (X ^ d₂ - X ^ d₁) * Y ^ b * (X ^ (a * d₁) - Y ^ a) := by
  have h1 := BoundedDefectLever.S_replicate_mul X Y d₁ a
  have h2 := BoundedDefectLever.S_replicate_mul X Y d₂ b
  rw [S_two, D_two]
  linear_combination (X ^ d₂ - Y) * Y ^ b * h1 + (X ^ d₁ - Y) * X ^ (a * d₁) * h2

end Ring

/-! ## On a genuine cycle -/

/-- If a cycle's gap word is a rotation of `w`, then `D(w)` divides `S(w)`. -/
lemma dvd_S_of_rotated {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {w : Word}
    (hw : gapWord x o ~r w) : Dz w ∣ Sz w := by
  obtain ⟨n, hn⟩ := hw
  have hS := CocycleCombine.IsSyrCycle.Dz_dvd_S_rotate h n
  rw [hn] at hS
  have hD : Dz w = Dz (gapWord x o) := by rw [← hn]; exact D_rotate _ _ _ _
  rwa [hD]

/-- `D(w)` is prime to `6` for a nonempty word with positive gap sum. -/
lemma isCoprime_six {w : Word} (hne : w ≠ []) (hE : w.sum ≠ 0) : IsCoprime (Dz w) 6 :=
  CocycleCombine.isCoprime_Dz_six hne hE

/-- **Two-background divisibility.** On a genuine cycle whose gap word is a rotation of
`d₁^a d₂^b` (nonempty, positive sum), `D` divides `(2^{d₁} - 2^{d₂})·V` and `(2^{d₁} - 2^{d₂})·U`. -/
theorem dvd_of_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {d₁ d₂ a b : ℕ}
    (hw : gapWord x o ~r two d₁ d₂ a b) (hne : two d₁ d₂ a b ≠ [])
    (hE : (two d₁ d₂ a b).sum ≠ 0) :
    Dz (two d₁ d₂ a b) ∣ (2 ^ d₁ - 2 ^ d₂) * (2 ^ (b * d₂) - 3 ^ b) ∧
      Dz (two d₁ d₂ a b) ∣ (2 ^ d₁ - 2 ^ d₂) * (2 ^ (a * d₁) - 3 ^ a) := by
  have hS := dvd_S_of_rotated h hw
  have hc := isCoprime_six hne hE
  have kV := key_V (2 : ℤ) 3 d₁ d₂ a b
  have kU := key_U (2 : ℤ) 3 d₁ d₂ a b
  constructor
  · have : Dz (two d₁ d₂ a b) ∣ 2 ^ (a * d₁) * 3 ^ 0 * ((2 ^ d₁ - 2 ^ d₂) * (2 ^ (b * d₂) - 3 ^ b)) := by
      have e : (2 : ℤ) ^ (a * d₁) * 3 ^ 0 * ((2 ^ d₁ - 2 ^ d₂) * (2 ^ (b * d₂) - 3 ^ b)) =
          (2 ^ d₁ - 3) * (2 ^ d₂ - 3) * Sz (two d₁ d₂ a b) - (2 ^ d₂ - 3) * Dz (two d₁ d₂ a b) := by
        rw [Sz, Dz, kV]; ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right hS _) (dvd_mul_left _ _)
    exact CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this
  · have : Dz (two d₁ d₂ a b) ∣ 2 ^ 0 * 3 ^ b * (-(2 ^ d₁ - 2 ^ d₂) * (2 ^ (a * d₁) - 3 ^ a)) := by
      have e : (2 : ℤ) ^ 0 * 3 ^ b * (-(2 ^ d₁ - 2 ^ d₂) * (2 ^ (a * d₁) - 3 ^ a)) =
          (2 ^ d₁ - 3) * (2 ^ d₂ - 3) * Sz (two d₁ d₂ a b) - (2 ^ d₁ - 3) * Dz (two d₁ d₂ a b) := by
        rw [Sz, Dz, kU]; ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right hS _) (dvd_mul_left _ _)
    have := CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this
    rwa [neg_mul, dvd_neg] at this

/-! ## The `{1, 2}` family -/

/-- `S(1^a 2^b) = 3^b (3^a - 2^a) + 2^a (4^b - 3^b)`. -/
theorem Sz_one_two (a b : ℕ) :
    Sz (two 1 2 a b) = 3 ^ b * (3 ^ a - 2 ^ a) + 2 ^ a * (4 ^ b - 3 ^ b) := by
  have h1 := BoundedDefectLever.S_replicate_mul (2 : ℤ) 3 1 a
  have h2 := BoundedDefectLever.S_replicate_mul (2 : ℤ) 3 2 b
  rw [Sz, S_two]
  have e1 : S (2 : ℤ) 3 (List.replicate a 1) = 3 ^ a - 2 ^ a := by
    simp only [mul_one, pow_one] at h1; linarith
  have e2 : S (2 : ℤ) 3 (List.replicate b 2) = 4 ^ b - 3 ^ b := by
    have h4 : (2 : ℤ) ^ (b * 2) = 4 ^ b := by rw [mul_comm, pow_mul]; norm_num
    rw [h4] at h2; norm_num at h2; linarith
  rw [e1, e2, mul_one]

/-- `D(1^a 2^b) = 2^a (4^b - 3^b) - 3^b (3^a - 2^a)`. -/
theorem Dz_one_two (a b : ℕ) :
    Dz (two 1 2 a b) = 2 ^ a * (4 ^ b - 3 ^ b) - 3 ^ b * (3 ^ a - 2 ^ a) := by
  have h4 : (2 : ℤ) ^ (b * 2) = 4 ^ b := by rw [mul_comm, pow_mul]; norm_num
  rw [Dz, D_two, mul_one, h4]
  ring

/-- **The `{1,2}` divisibility.** On a genuine cycle whose gap word is a rotation of `1^a 2^b`
(`a + b ≥ 1`), `D ∣ 3^a - 2^a` and `D ∣ 4^b - 3^b`. -/
theorem dvd_u_v_of_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b : ℕ} (hab : 1 ≤ a + b)
    (hw : gapWord x o ~r two 1 2 a b) :
    Dz (two 1 2 a b) ∣ 3 ^ a - 2 ^ a ∧ Dz (two 1 2 a b) ∣ 4 ^ b - 3 ^ b := by
  have hne : two 1 2 a b ≠ [] := by
    intro h0
    have := congrArg List.length h0
    simp [two] at this; omega
  have hE : (two 1 2 a b).sum ≠ 0 := by
    simp [two]; omega
  obtain ⟨hV, hU⟩ := dvd_of_cycle h hw hne hE
  have hc := isCoprime_six hne hE
  constructor
  · have : Dz (two 1 2 a b) ∣ 2 ^ 1 * 3 ^ 0 * (3 ^ a - 2 ^ a) := by
      have e : (2 : ℤ) ^ 1 * 3 ^ 0 * (3 ^ a - 2 ^ a) = (2 ^ 1 - 2 ^ 2) * (2 ^ (a * 1) - 3 ^ a) := by
        ring
      rw [e]; exact hU
    exact CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this
  · have : Dz (two 1 2 a b) ∣ 2 ^ 1 * 3 ^ 0 * (-(4 ^ b - 3 ^ b)) := by
      have e : (2 : ℤ) ^ 1 * 3 ^ 0 * (-(4 ^ b - 3 ^ b)) = (2 ^ 1 - 2 ^ 2) * (2 ^ (b * 2) - 3 ^ b) := by
        rw [mul_comm b 2, pow_mul]; ring
      rw [e]; exact hV
    have := CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this
    rwa [dvd_neg] at this

/-- **Small cases.** No `1^a 2^b` with `a, b ≥ 1` and `E = a + 2b ≤ 27` has `D > 0`, `D ∣ 3^a - 2^a`
and `D ∣ 4^b - 3^b`. -/
theorem small_cases : ∀ a : ℕ, a < 28 → ∀ b : ℕ, b < 14 → (1 ≤ a ∧ 1 ≤ b ∧ a + 2 * b ≤ 27) →
    ¬ (3 ^ (a + b) < 2 ^ (a + 2 * b) ∧ (2 ^ (a + 2 * b) - 3 ^ (a + b)) ∣ 3 ^ a - 2 ^ a ∧
      (2 ^ (a + 2 * b) - 3 ^ (a + b)) ∣ 4 ^ b - 3 ^ b) := by
  decide

/-- `D(1^a 2^b) = 2^{a+2b} - 3^{a+b}`. -/
lemma Dz_one_two' (a b : ℕ) : Dz (two 1 2 a b) = 2 ^ (a + 2 * b) - 3 ^ (a + b) := by
  simp only [Dz, D, two, List.sum_append, List.sum_replicate, List.length_append,
    List.length_replicate, smul_eq_mul]
  ring_nf

/-- The analytic step: `3^a 4^b ≤ (2^E e^{-E/10})²` for `E = a + 2b`, from `e^{1/5} < 4/3` and
`e^{2/5} < 4`. -/
lemma ellison_square (a b : ℕ) :
    (3 : ℝ) ^ a * 4 ^ b ≤ ((2 : ℝ) ^ (a + 2 * b) * Real.exp (-((a + 2 * b : ℕ) : ℝ) / 10)) ^ 2 := by
  have e1 : Real.exp (1 / 5) ≤ 4 / 3 := by
    have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 5) (by norm_num) (by norm_num)
    linarith [show (1 : ℝ) / (1 - 1 / 5) = 5 / 4 by norm_num]
  have e2 : Real.exp (2 / 5) ≤ 4 := by
    have := Real.exp_bound_div_one_sub_of_interval (x := 2 / 5) (by norm_num) (by norm_num)
    linarith [show (1 : ℝ) / (1 - 2 / 5) = 5 / 3 by norm_num]
  have hexp : Real.exp (((a + 2 * b : ℕ) : ℝ) / 5) = Real.exp (1 / 5) ^ a * Real.exp (2 / 5) ^ b := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have hsq : ((2 : ℝ) ^ (a + 2 * b) * Real.exp (-((a + 2 * b : ℕ) : ℝ) / 10)) ^ 2 *
      Real.exp (((a + 2 * b : ℕ) : ℝ) / 5) = 4 ^ a * 16 ^ b := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    have : ((2 : ℕ) : ℝ) * (-((a + 2 * b : ℕ) : ℝ) / 10) + ((a + 2 * b : ℕ) : ℝ) / 5 = 0 := by ring
    rw [this, Real.exp_zero, mul_one, ← pow_mul,
      show (a + 2 * b) * 2 = 2 * a + 4 * b by ring, pow_add, pow_mul, pow_mul]
    norm_num
  have hpos : 0 < Real.exp (((a + 2 * b : ℕ) : ℝ) / 5) := Real.exp_pos _
  have hbound : (3 : ℝ) ^ a * 4 ^ b * Real.exp (((a + 2 * b : ℕ) : ℝ) / 5) ≤ 4 ^ a * 16 ^ b := by
    rw [hexp]
    calc (3 : ℝ) ^ a * 4 ^ b * (Real.exp (1 / 5) ^ a * Real.exp (2 / 5) ^ b)
        = (3 * Real.exp (1 / 5)) ^ a * (4 * Real.exp (2 / 5)) ^ b := by rw [mul_pow, mul_pow]; ring
      _ ≤ (3 * (4 / 3)) ^ a * (4 * 4) ^ b := by
          gcongr
      _ = 4 ^ a * 16 ^ b := by norm_num
  rw [← hsq] at hbound
  exact le_of_mul_le_mul_right hbound hpos

/-- **No positive Syracuse cycle has a cyclic gap word `1^a 2^b` (`a, b ≥ 1`)**, conditional on
Ellison's bound. The two runs make the slope reach `log₂ 3`, so the ratio sandwich does not apply.
The proof uses only `G = gcd(S, D)`-type divisibility (`dvd_u_v_of_cycle`), sizes, and Ellison; the
cases `E ≤ 27` are a finite check. -/
theorem no_cycle_one_two (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hx : 0 < x) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hw : gapWord x o ~r two 1 2 a b) : False := by
  obtain ⟨hu, hv⟩ := dvd_u_v_of_cycle h (by omega) hw
  have hDeq : Dz (two 1 2 a b) = Dz (gapWord x o) := by
    obtain ⟨n, hn⟩ := hw; rw [← hn]; exact D_rotate _ _ _ _
  have hD : 0 < Dz (two 1 2 a b) := hDeq ▸ CycleLiterature.cycle_Dz_pos h hx
  rw [Dz_one_two'] at hu hv hD
  have h23 : (2 : ℤ) ^ a ≤ 3 ^ a := pow_le_pow_left₀ (by norm_num) (by norm_num) a
  have h34 : (3 : ℤ) ^ b ≤ 4 ^ b := pow_le_pow_left₀ (by norm_num) (by norm_num) b
  by_cases hE : a + 2 * b ≤ 27
  · -- finite check, transported to `ℕ`
    apply small_cases a (by omega) b (by omega) ⟨ha, hb, hE⟩
    have hlt : 3 ^ (a + b) < 2 ^ (a + 2 * b) := by exact_mod_cast (by linarith : (3 : ℤ) ^ (a + b) < 2 ^ (a + 2 * b))
    refine ⟨hlt, ?_, ?_⟩
    · have hu' : (((2 ^ (a + 2 * b) - 3 ^ (a + b) : ℕ) : ℤ)) ∣ (((3 ^ a - 2 ^ a : ℕ) : ℤ)) := by
        rw [Nat.cast_sub hlt.le, Nat.cast_sub (Nat.pow_le_pow_left (by norm_num) a)]
        push_cast; exact hu
      exact Int.natCast_dvd_natCast.mp hu'
    · have hv' : (((2 ^ (a + 2 * b) - 3 ^ (a + b) : ℕ) : ℤ)) ∣ (((4 ^ b - 3 ^ b : ℕ) : ℤ)) := by
        rw [Nat.cast_sub hlt.le, Nat.cast_sub (Nat.pow_le_pow_left (by norm_num) b)]
        push_cast; exact hv
      exact Int.natCast_dvd_natCast.mp hv'
  · -- Ellison
    have hnot : (a + 2 * b) ∉ CycleLiterature.ellisonExceptions := by
      simp only [CycleLiterature.ellisonExceptions, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcast : (((2 ^ (a + 2 * b) - 3 ^ (a + b) : ℤ)) : ℝ) = (2 : ℝ) ^ (a + 2 * b) - 3 ^ (a + b) := by
      push_cast; ring
    have hEl2 : (2 : ℝ) ^ (a + 2 * b) * Real.exp (-((a + 2 * b : ℕ) : ℝ) / 10) <
        (2 : ℝ) ^ (a + 2 * b) - 3 ^ (a + b) := by
      have := hEl (a + 2 * b) (a + b) (by omega) (by omega) hnot
      rwa [abs_of_pos (by rw [← hcast]; exact_mod_cast hD)] at this
    have hupos : (0 : ℤ) < 3 ^ a - 2 ^ a := by
      have := pow_lt_pow_left₀ (by norm_num : (2 : ℤ) < 3) (by norm_num) (by omega : a ≠ 0); linarith
    have hvpos : (0 : ℤ) < 4 ^ b - 3 ^ b := by
      have := pow_lt_pow_left₀ (by norm_num : (3 : ℤ) < 4) (by norm_num) (by omega : b ≠ 0); linarith
    have hDu := Int.le_of_dvd hupos hu
    have hDv := Int.le_of_dvd hvpos hv
    have h1 : (2 : ℝ) ^ (a + 2 * b) - 3 ^ (a + b) ≤ 3 ^ a := by
      have : ((2 ^ (a + 2 * b) - 3 ^ (a + b) : ℤ) : ℝ) ≤ ((3 ^ a - 2 ^ a : ℤ) : ℝ) := by exact_mod_cast hDu
      rw [hcast] at this; push_cast at this
      have : (0 : ℝ) < 2 ^ a := by positivity
      linarith
    have h2 : (2 : ℝ) ^ (a + 2 * b) - 3 ^ (a + b) ≤ 4 ^ b := by
      have : ((2 ^ (a + 2 * b) - 3 ^ (a + b) : ℤ) : ℝ) ≤ ((4 ^ b - 3 ^ b : ℤ) : ℝ) := by exact_mod_cast hDv
      rw [hcast] at this; push_cast at this
      have : (0 : ℝ) < 3 ^ b := by positivity
      linarith
    have hA0 : 0 ≤ (2 : ℝ) ^ (a + 2 * b) * Real.exp (-((a + 2 * b : ℕ) : ℝ) / 10) := by positivity
    have hlt := pow_lt_pow_left₀ hEl2 hA0 (by norm_num : (2 : ℕ) ≠ 0)
    have hD0 : 0 ≤ (2 : ℝ) ^ (a + 2 * b) - 3 ^ (a + b) := le_trans hA0 hEl2.le
    have : ((2 : ℝ) ^ (a + 2 * b) - 3 ^ (a + b)) ^ 2 ≤ 3 ^ a * 4 ^ b := by
      rw [sq]; exact mul_le_mul h1 h2 hD0 (by positivity)
    linarith [ellison_square a b]


/-! ## Two growing *block* backgrounds `u^a v^b` (continued-fraction renormalisation, first step)

For blocks `u`, `v` (e.g. Christoffel blocks at consecutive convergents of `log₂ 3`), the same
algebra goes through with the wedge core `C(u,v) = D(u)S(v) - D(v)S(u)` (structure.md C7) in place of
`X^{d₁} - X^{d₂}`. The letter case is `u = [d₁]`, `v = [d₂]`, where `C = X^{d₂} - X^{d₁}` up to
sign. -/

section Block

variable {R : Type*} [CommRing R] (X Y : R)

/-- The wedge core `C(u,v) = D(u)S(v) - D(v)S(u)`. -/
def core (u v : Word) : R := D X Y u * S X Y v - D X Y v * S X Y u

/-- The block power `u^a` (the same as `CocycleCombine.wpow`). -/
abbrev bpow (u : Word) (a : ℕ) : Word := CocycleCombine.wpow u a

/-- `D(u)·S(u^a) = S(u)·D(u^a)`. -/
lemma D_mul_S_bpow (u : Word) (a : ℕ) :
    D X Y u * S X Y (bpow u a) = S X Y u * D X Y (bpow u a) := by
  rw [bpow, CocycleCombine.S_wpow, CocycleCombine.D_wpow]; ring

/-- **Block key identity for `V`.** With `w = u^a v^b`:
`D(u)D(v)S(w) - D(v)S(u)D(w) = C(u,v)·X^{|u^a|}·D(v^b)`. -/
theorem key_block_V (u v : Word) (a b : ℕ) :
    D X Y u * D X Y v * S X Y (bpow u a ++ bpow v b) -
        D X Y v * S X Y u * D X Y (bpow u a ++ bpow v b) =
      core X Y u v * X ^ (bpow u a).sum * D X Y (bpow v b) := by
  have h1 := D_mul_S_bpow X Y u a
  have h2 := D_mul_S_bpow X Y v b
  rw [S_append, D_append, core]
  linear_combination D X Y v * Y ^ (bpow v b).length * h1 + D X Y u * X ^ (bpow u a).sum * h2

/-- **Block key identity for `U`.** `D(u)D(v)S(w) - D(u)S(v)D(w) = -C(u,v)·Y^{len v^b}·D(u^a)`. -/
theorem key_block_U (u v : Word) (a b : ℕ) :
    D X Y u * D X Y v * S X Y (bpow u a ++ bpow v b) -
        D X Y u * S X Y v * D X Y (bpow u a ++ bpow v b) =
      -(core X Y u v * Y ^ (bpow v b).length * D X Y (bpow u a)) := by
  have h1 := D_mul_S_bpow X Y u a
  have h2 := D_mul_S_bpow X Y v b
  rw [S_append, D_append, core]
  linear_combination D X Y v * Y ^ (bpow v b).length * h1 + D X Y u * X ^ (bpow u a).sum * h2

end Block

/-- **Two-block divisibility on a cycle.** If a genuine cycle's gap word is a rotation of `u^a v^b`
(nonempty, positive sum), then `D ∣ C(u,v)·D(v^b)` and `D ∣ C(u,v)·D(u^a)`. So
`|2^E - 3^o|` divides `C(u,v)·gcd(D(u^a), D(v^b))`. -/
theorem dvd_of_cycle_block {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {u v : Word} {a b : ℕ}
    (hw : gapWord x o ~r bpow u a ++ bpow v b) (hne : bpow u a ++ bpow v b ≠ [])
    (hE : (bpow u a ++ bpow v b).sum ≠ 0) :
    Dz (bpow u a ++ bpow v b) ∣ core (2 : ℤ) 3 u v * Dz (bpow v b) ∧
      Dz (bpow u a ++ bpow v b) ∣ core (2 : ℤ) 3 u v * Dz (bpow u a) := by
  have hS := dvd_S_of_rotated h hw
  have hc := isCoprime_six hne hE
  have kV := key_block_V (2 : ℤ) 3 u v a b
  have kU := key_block_U (2 : ℤ) 3 u v a b
  constructor
  · have : Dz (bpow u a ++ bpow v b) ∣
        2 ^ (bpow u a).sum * 3 ^ 0 * (core (2 : ℤ) 3 u v * Dz (bpow v b)) := by
      have e : (2 : ℤ) ^ (bpow u a).sum * 3 ^ 0 * (core (2 : ℤ) 3 u v * Dz (bpow v b)) =
          D (2 : ℤ) 3 u * D 2 3 v * Sz (bpow u a ++ bpow v b) -
            D (2 : ℤ) 3 v * S 2 3 u * Dz (bpow u a ++ bpow v b) := by
        rw [Sz, Dz, Dz, kV]; ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right hS _) (dvd_mul_left _ _)
    exact CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this
  · have : Dz (bpow u a ++ bpow v b) ∣
        2 ^ 0 * 3 ^ (bpow v b).length * (-(core (2 : ℤ) 3 u v * Dz (bpow u a))) := by
      have e : (2 : ℤ) ^ 0 * 3 ^ (bpow v b).length * (-(core (2 : ℤ) 3 u v * Dz (bpow u a))) =
          D (2 : ℤ) 3 u * D 2 3 v * Sz (bpow u a ++ bpow v b) -
            D (2 : ℤ) 3 u * S 2 3 v * Dz (bpow u a ++ bpow v b) := by
        rw [Sz, Dz, Dz, kU]; ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right hS _) (dvd_mul_left _ _)
    have := CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this
    rwa [dvd_neg] at this

/-- Sanity check: for single letters the block core is the letter factor,
`C([1],[2]) = 2 - 4 = -2` at `(2,3)`. -/
example : core (2 : ℤ) 3 [1] [2] = -2 := by decide

end Syracuse.TwoBackground
