import Syracuse.Approaches.Frontier
import Syracuse.Approaches.SignedCycles

/-!
# The repeat lemma (direction D7, transferred from Mahler's 3/2 problem)

If the gap word of a cycle has the same window `u` (length `ℓ`, sum `E(u)`) at two positions `i ≠ j`,
the two affine maps along `u` coincide. Subtracting them gives the **repeat identity**
(`repeat_identity`, Dubickas 2009 for Mahler's problem):

`2^{E(u)} · (x_{i+ℓ} - x_{j+ℓ}) = 3^ℓ · (x_i - x_j)`.

Since `2` and `3` are coprime, `2^{E(u)} ∣ x_i - x_j` and `3^ℓ ∣ x_{i+ℓ} - x_{j+ℓ}` (`repeat_dvd`).
On a cycle of minimal period both differences are nonzero, so a repeated window forces two cycle
points at distance at least `2^{E(u)}` and two at distance at least `3^ℓ`.

Every point `y` of a cycle of either sign is bounded by `2^o |y| |D| < 2^E 3^o`
(`abs_mul_abs_D_lt`, from `2^o S(w) ≤ 2^E (3^o - 2^o)`, `two_pow_mul_S_le`). The points of a cycle
share one sign, so `|x_i - x_j| < max |x_k|`. This gives `repeat_bound`:

`2^o · 2^{E(u)} · |D| < 2^E 3^o` and `2^o · 3^ℓ · |D| < 2^E 3^o`.

With Ellison's `|D| > 2^E e^{-E/10}` this linearises (`repeat_linear`, either sign) to
`10000·E(u) < 5850·o + 1443·E` and `15840·ℓ < 5850·o + 1443·E`. For a nontrivial positive cycle the
sandwich and Barina then give (`repeat_half`): **every window that occurs twice covers less than
`51.37 %` of the cycle's weight and less than `52.79 %` of its length.** A run `d^r` is a window repeated
at distance one, so the lemma also bounds every run, and every periodic stretch, of a cycle word.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `gapWord a (m + n) = gapWord a m ++ gapWord (syr^[m] a) n` | `gapWord_add` | proved |
| repeat identity `2^{E(u)} (y' - z') = 3^ℓ (y - z)` | `repeat_identity` | proved |
| `2^{E(u)} ∣ y - z`, `3^ℓ ∣ y' - z'` | `repeat_dvd` | proved |
| `2^o S(w) ≤ 2^E (3^o - 2^o)` for positive words | `two_pow_mul_S_le` | proved |
| every point of a cycle: `2^o |y| |D| < 2^E 3^o` | `abs_mul_abs_D_lt` | proved |
| the orbit points of a cycle are cycle points with the same `E`, `D` and sign | `isSyrCycle_iterate`, `sum_gapWord_iterate`, `same_sign` | proved |
| distinct positions of a minimal cycle carry distinct points | `iterate_ne` | proved |
| a repeated window: `2^o 2^{E(u)} |D|, 2^o 3^ℓ |D| < 2^E 3^o` | `repeat_bound` | proved |
| Ellison ⇒ `10000 E(u) < 5850 o + 1443 E`, `15840 ℓ < 5850 o + 1443 E` (either sign) | `repeat_linear` | proved (conditional on `Ellison1971`) |
| nontrivial positive cycle: repeated windows cover `< 51.37 %` of `E`, `< 52.79 %` of `o` | `repeat_half` | proved (conditional on Ellison + Barina) |
-/

namespace Syracuse.Repeat

open Syracuse

/-! ## The identity -/

/-- Splitting a gap word. -/
lemma gapWord_add (a : ℤ) (m n : ℕ) :
    gapWord a (m + n) = gapWord a m ++ gapWord (syr^[m] a) n := by
  induction m generalizing a with
  | zero => simp [gapWord]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, gapWord, gapWord, ih, Function.iterate_succ_apply]
    rfl

/-- **Repeat identity.** If `y` and `z` have the same gap word `u` for `ℓ` steps, then
`2^{E(u)}·(syr^ℓ y - syr^ℓ z) = 3^ℓ·(y - z)`. -/
theorem repeat_identity {y z : ℤ} {ℓ : ℕ} (h : gapWord y ℓ = gapWord z ℓ) :
    2 ^ (gapWord y ℓ).sum * (syr^[ℓ] y - syr^[ℓ] z) = 3 ^ ℓ * (y - z) := by
  have hy := (follows_gapWord y ℓ).closed_form
  have hz := (follows_gapWord z ℓ).closed_form
  rw [← h] at hz
  simp only [gapWord_length] at hy hz
  linear_combination hy - hz

/-- **Repeat divisibility.** `2^{E(u)} ∣ y - z` and `3^ℓ ∣ syr^ℓ y - syr^ℓ z`. -/
theorem repeat_dvd {y z : ℤ} {ℓ : ℕ} (h : gapWord y ℓ = gapWord z ℓ) :
    (2 : ℤ) ^ (gapWord y ℓ).sum ∣ y - z ∧ (3 : ℤ) ^ ℓ ∣ syr^[ℓ] y - syr^[ℓ] z := by
  have hid := repeat_identity h
  have hc : IsCoprime ((2 : ℤ) ^ (gapWord y ℓ).sum) ((3 : ℤ) ^ ℓ) := by
    apply IsCoprime.pow; rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  exact ⟨hc.dvd_of_dvd_mul_left ⟨_, hid.symm⟩, hc.symm.dvd_of_dvd_mul_left ⟨_, hid⟩⟩

/-! ## Size of cycle points -/

/-- `2^o S(w) ≤ 2^E (3^o - 2^o)` for a positive word. -/
lemma two_pow_mul_S_le {w : Word} (hw : w.Pos) :
    2 ^ w.length * Sz w ≤ 2 ^ w.sum * (3 ^ w.length - 2 ^ w.length) := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have hw' : Word.Pos w := fun e he => hw e (List.mem_cons_of_mem d he)
    have ih := ih hw'
    have hle := CycleLiterature.length_le_sum hw'
    simp only [Sz, S_cons, List.length_cons, List.sum_cons] at ih ⊢
    have hQ : (0 : ℤ) ≤ 2 ^ d := by positivity
    have hB : (0 : ℤ) ≤ 3 ^ w.length := by positivity
    have hQP : 2 * 2 ^ w.length ≤ (2 : ℤ) ^ d * 2 ^ w.sum := by
      have : (2 : ℤ) ^ (w.length + 1) ≤ 2 ^ (d + w.sum) := pow_le_pow_right₀ (by norm_num) (by omega)
      rwa [pow_succ, pow_add, mul_comm] at this
    rw [show (2 : ℤ) ^ (w.length + 1) = 2 * 2 ^ w.length by ring,
      show (3 : ℤ) ^ (w.length + 1) = 3 * 3 ^ w.length by ring,
      show (2 : ℤ) ^ (d + w.sum) = 2 ^ d * 2 ^ w.sum by ring]
    nlinarith [mul_nonneg hQ (sub_nonneg.2 ih), mul_nonneg (sub_nonneg.2 hQP) hB]

/-- **Every point of a cycle is small against `D`:** `2^o |y| |D| < 2^E 3^o`. -/
theorem abs_mul_abs_D_lt {y : ℤ} {o : ℕ} (h : IsSyrCycle y o) :
    2 ^ o * |y| * |Dz (gapWord y o)| < 2 ^ (gapWord y o).sum * 3 ^ o := by
  have hceq := h.cycle_equation
  have hS := CycleLiterature.Sz_pos (CycleLiterature.cycle_gapWord_ne_nil h)
  have hb := two_pow_mul_S_le (CocycleCombine.IsSyrCycle.pos h)
  rw [gapWord_length] at hb
  have hyD : |y| * |Dz (gapWord y o)| = Sz (gapWord y o) := by
    rw [← abs_mul, mul_comm, hceq, abs_of_pos hS]
  rw [mul_assoc, hyD]
  have : (0 : ℤ) < 2 ^ (gapWord y o).sum * 2 ^ o := by positivity
  nlinarith

/-- The orbit points of a cycle are cycle points. -/
lemma isSyrCycle_iterate {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (k : ℕ) : IsSyrCycle (syr^[k] x) o := by
  refine ⟨h.1, ?_, ?_⟩
  · cases k with
    | zero => exact h.2.1
    | succ k => rw [Function.iterate_succ_apply']; exact syr_odd _
  · rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h.2.2]

/-- The orbit points of a cycle have the same `E`. -/
lemma sum_gapWord_iterate {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (k : ℕ) :
    (gapWord (syr^[k] x) o).sum = (gapWord x o).sum := by
  have h1 := gapWord_add x k o
  have h2 := gapWord_add x o k
  rw [h.2.2, add_comm] at h2
  rw [h2] at h1
  have := congrArg List.sum h1
  simp only [List.sum_append] at this
  omega

/-- The orbit points of a cycle have the same `D`. -/
lemma Dz_iterate {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (k : ℕ) :
    Dz (gapWord (syr^[k] x) o) = Dz (gapWord x o) := by
  simp only [Dz, D, sum_gapWord_iterate h k, gapWord_length]

/-- The points of a cycle share the sign of `D`. -/
lemma same_sign {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (k : ℕ) :
    0 < syr^[k] x * Dz (gapWord x o) := by
  have hk := isSyrCycle_iterate h k
  have hS := CycleLiterature.Sz_pos (CycleLiterature.cycle_gapWord_ne_nil hk)
  rw [← hk.cycle_equation, Dz_iterate h k] at hS
  linarith [mul_comm (syr^[k] x) (Dz (gapWord x o))]

/-- Every orbit point of a cycle satisfies `2^o |y| |D| < 2^E 3^o` with the cycle's `E` and `D`. -/
lemma abs_iterate_lt {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (k : ℕ) :
    2 ^ o * |syr^[k] x| * |Dz (gapWord x o)| < 2 ^ (gapWord x o).sum * 3 ^ o := by
  have := abs_mul_abs_D_lt (isSyrCycle_iterate h k)
  rwa [Dz_iterate h k, sum_gapWord_iterate h k] at this

/-- Distinct positions of a cycle of minimal period carry distinct points. -/
lemma iterate_ne {x : ℤ} {o : ℕ} (h : CycleLiterature.IsPrimSyrCycle x o) {i j : ℕ} (hij : i < j)
    (hj : j < o) : syr^[i] x ≠ syr^[j] x := by
  intro heq
  have hx := h.1.2.2
  have e1 : syr^[j - i] x = syr^[o - i] (syr^[j] x) := by
    rw [← Function.iterate_add_apply, show o - i + j = (j - i) + o by omega,
      Function.iterate_add_apply, hx]
  have e2 : syr^[o - i] (syr^[i] x) = x := by
    rw [← Function.iterate_add_apply, show o - i + i = o by omega, hx]
  exact h.2 (j - i) (by omega) (by omega) (by rw [e1, ← heq, e2])

/-- Two distinct points of one sign: `|y - z| < max(|y|, |z|)`. -/
lemma abs_sub_lt_of_same_sign {y z D : ℤ} (hy : 0 < y * D) (hz : 0 < z * D) :
    |y - z| < max |y| |z| := by
  rcases lt_or_gt_of_ne (show D ≠ 0 by rintro rfl; simp at hy) with hD | hD
  · have hy' : y < 0 := by nlinarith
    have hz' : z < 0 := by nlinarith
    rw [abs_of_neg hy', abs_of_neg hz', abs_sub_lt_iff]
    exact ⟨lt_max_iff.2 (Or.inr (by linarith)), lt_max_iff.2 (Or.inl (by linarith))⟩
  · have hy' : 0 < y := by nlinarith
    have hz' : 0 < z := by nlinarith
    rw [abs_of_pos hy', abs_of_pos hz', abs_sub_lt_iff]
    exact ⟨lt_max_iff.2 (Or.inl (by linarith)), lt_max_iff.2 (Or.inr (by linarith))⟩

/-! ## The repeat bound -/

/-- **Repeat bound.** On a cycle of minimal period `o` (either sign), if the windows of length `ℓ` at
positions `i < j < o` coincide, then `2^o·2^{E(u)}·|D| < 2^E 3^o` and `2^o·3^ℓ·|D| < 2^E 3^o`. -/
theorem repeat_bound {x : ℤ} {o : ℕ} (h : CycleLiterature.IsPrimSyrCycle x o) {i j ℓ : ℕ}
    (hij : i < j) (hj : j < o) (hw : gapWord (syr^[i] x) ℓ = gapWord (syr^[j] x) ℓ) :
    2 ^ o * 2 ^ (gapWord (syr^[i] x) ℓ).sum * |Dz (gapWord x o)| < 2 ^ (gapWord x o).sum * 3 ^ o ∧
    2 ^ o * 3 ^ ℓ * |Dz (gapWord x o)| < 2 ^ (gapWord x o).sum * 3 ^ o := by
  have hc := h.1
  set y := syr^[i] x
  set z := syr^[j] x
  have hne : y ≠ z := iterate_ne h hij hj
  have hid := repeat_identity hw
  obtain ⟨h2, h3⟩ := repeat_dvd hw
  have hD : 0 < |Dz (gapWord x o)| := abs_pos.2 (by
    intro h0; have := same_sign hc 0; rw [h0, mul_zero] at this; exact lt_irrefl _ this)
  have h2o : (0 : ℤ) < 2 ^ o := by positivity
  -- a nonzero difference of two orbit points is below the largest of them
  have key : ∀ m n : ℕ, syr^[m] x ≠ syr^[n] x → ∀ c : ℤ, 0 < c → c ∣ syr^[m] x - syr^[n] x →
      2 ^ o * c * |Dz (gapWord x o)| < 2 ^ (gapWord x o).sum * 3 ^ o := by
    intro m n hmn c hc0 hcd
    have hle : c ≤ |syr^[m] x - syr^[n] x| :=
      Int.le_of_dvd (abs_pos.2 (sub_ne_zero.2 hmn)) ((dvd_abs _ _).2 hcd)
    have hlt := abs_sub_lt_of_same_sign (same_sign hc m) (same_sign hc n)
    have hm := abs_iterate_lt hc m
    have hn := abs_iterate_lt hc n
    have hmax : 2 ^ o * max |syr^[m] x| |syr^[n] x| * |Dz (gapWord x o)| <
        2 ^ (gapWord x o).sum * 3 ^ o := by
      rcases le_total |syr^[m] x| |syr^[n] x| with hh | hh
      · rw [max_eq_right hh]; exact hn
      · rw [max_eq_left hh]; exact hm
    calc 2 ^ o * c * |Dz (gapWord x o)| ≤ 2 ^ o * max |syr^[m] x| |syr^[n] x| * |Dz (gapWord x o)| := by
          gcongr; exact hle.trans hlt.le
      _ < _ := hmax
  constructor
  · exact key i j hne _ (by positivity) h2
  · have hne' : syr^[ℓ] y ≠ syr^[ℓ] z := by
      intro h0
      rw [h0, sub_self, mul_zero] at hid
      have : (3 : ℤ) ^ ℓ * (y - z) ≠ 0 := mul_ne_zero (by positivity) (sub_ne_zero.2 hne)
      exact this hid.symm
    rw [show syr^[ℓ] y = syr^[ℓ + i] x by rw [Function.iterate_add_apply],
      show syr^[ℓ] z = syr^[ℓ + j] x by rw [Function.iterate_add_apply]] at hne' h3
    exact key _ _ hne' _ (by positivity) h3

/-! ## Linear forms -/

/-- `log 3 < 1.585 log 2` and `1.584 log 2 < log 3`. -/
lemma log_three_bounds :
    1000 * Real.log 3 < 1585 * Real.log 2 ∧ 1584 * Real.log 2 < 1000 * Real.log 3 := by
  have h1 : (3 : ℝ) ^ 1000 < 2 ^ 1585 := by exact_mod_cast (show 3 ^ 1000 < 2 ^ 1585 by decide +kernel)
  have h2 : (2 : ℝ) ^ 1584 < 3 ^ 1000 := by exact_mod_cast (show 2 ^ 1584 < 3 ^ 1000 by decide +kernel)
  have l1 := Real.log_lt_log (by positivity) h1
  have l2 := Real.log_lt_log (by positivity) h2
  rw [Real.log_pow, Real.log_pow] at l1 l2
  push_cast at l1 l2
  exact ⟨l1, l2⟩

/-- **Repeat lemma, linear form** (either sign). Given Ellison and `E` outside its exceptional set, a
window `u` of length `ℓ` repeated at two positions of a cycle of minimal period `o` satisfies
`10000·E(u) < 5850·o + 1443·E` and `15840·ℓ < 5850·o + 1443·E`. -/
theorem repeat_linear (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ}
    (h : CycleLiterature.IsPrimSyrCycle x o)
    (hE : (gapWord x o).sum ∉ CycleLiterature.ellisonExceptions) {i j ℓ : ℕ} (hij : i < j)
    (hj : j < o) (hw : gapWord (syr^[i] x) ℓ = gapWord (syr^[j] x) ℓ) :
    10000 * (gapWord (syr^[i] x) ℓ).sum < 5850 * o + 1443 * (gapWord x o).sum ∧
    15840 * ℓ < 5850 * o + 1443 * (gapWord x o).sum := by
  obtain ⟨b1, b2⟩ := repeat_bound h hij hj hw
  set E := (gapWord x o).sum
  set Eu := (gapWord (syr^[i] x) ℓ).sum
  have hEpos : 0 < E := by
    have := CycleLiterature.length_le_sum (CocycleCombine.IsSyrCycle.pos h.1)
    rw [gapWord_length] at this; have := h.1.1; omega
  have hEl' := hEl E o hEpos h.1.1 hE
  have hDf : |Dz (gapWord x o)| = |(2 : ℤ) ^ E - 3 ^ o| := by simp only [Dz, D, gapWord_length]; rfl
  rw [hDf] at b1 b2
  have hcast : ((|(2 : ℤ) ^ E - 3 ^ o| : ℤ) : ℝ) = |(2 : ℝ) ^ E - 3 ^ o| := by push_cast; rfl
  have r1 : (2 : ℝ) ^ o * 2 ^ Eu * |(2 : ℝ) ^ E - 3 ^ o| < 2 ^ E * 3 ^ o := by
    rw [← hcast]; exact_mod_cast b1
  have r2 : (2 : ℝ) ^ o * 3 ^ ℓ * |(2 : ℝ) ^ E - 3 ^ o| < 2 ^ E * 3 ^ o := by
    rw [← hcast]; exact_mod_cast b2
  -- combine with Ellison: `2^o·c < 3^o·e^{E/10}`
  have hexp : 0 < Real.exp (-(E : ℝ) / 10) := Real.exp_pos _
  have comb : ∀ c : ℝ, 0 < c → (2 : ℝ) ^ o * c * |(2 : ℝ) ^ E - 3 ^ o| < 2 ^ E * 3 ^ o →
      Real.log c + o * Real.log 2 < o * Real.log 3 + E / 10 := by
    intro c hc hr
    have h1 : (2 : ℝ) ^ o * c * (2 ^ E * Real.exp (-(E : ℝ) / 10)) < 2 ^ E * 3 ^ o :=
      lt_of_le_of_lt (by gcongr) hr
    have h2 : (2 : ℝ) ^ o * c * Real.exp (-(E : ℝ) / 10) < 3 ^ o := by
      have h2E : (0 : ℝ) < 2 ^ E := by positivity
      nlinarith
    have h3 := Real.log_lt_log (by positivity) h2
    rw [Real.log_mul (by positivity) hexp.ne', Real.log_mul (by positivity) hc.ne', Real.log_exp,
      Real.log_pow, Real.log_pow] at h3
    linarith
  have c1 := comb _ (by positivity) r1
  have c2 := comb _ (by positivity) r2
  rw [Real.log_pow] at c1 c2
  obtain ⟨l3a, l3b⟩ := log_three_bounds
  have hl2 := Real.log_two_gt_d9
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have hE10 : (E : ℝ) / 10 < 0.1443 * E * Real.log 2 := by nlinarith
  constructor
  · have : (10000 * Eu : ℝ) < 5850 * o + 1443 * E := by
      have : (Eu : ℝ) * Real.log 2 < (0.585 * o + 0.1443 * E) * Real.log 2 := by
        have ho : (0 : ℝ) ≤ o := by positivity
        nlinarith
      have := lt_of_mul_lt_mul_right this (by linarith)
      linarith
    exact_mod_cast this
  · have : (15840 * ℓ : ℝ) < 5850 * o + 1443 * E := by
      have hl : (0 : ℝ) ≤ ℓ := by positivity
      have ho : (0 : ℝ) ≤ o := by positivity
      have : (1.584 * ℓ : ℝ) * Real.log 2 < (0.585 * o + 0.1443 * E) * Real.log 2 := by nlinarith
      have := lt_of_mul_lt_mul_right this (by linarith)
      linarith
    exact_mod_cast this

/-- **Repeat lemma for nontrivial positive cycles.** Given Ellison and Barina, every window that occurs
at two positions of a nontrivial positive cycle of minimal period `o` covers less than `51.37 %` of
the weight `E` and less than `52.79 %` of the length `o`. -/
theorem repeat_half (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025) {x : ℤ}
    {o : ℕ} (h : CycleLiterature.IsPrimSyrCycle x o) (hx : 0 < x) (hx1 : x ≠ 1) {i j ℓ : ℕ}
    (hij : i < j) (hj : j < o) (hw : gapWord (syr^[i] x) ℓ = gapWord (syr^[j] x) ℓ) :
    10000 * (gapWord (syr^[i] x) ℓ).sum < 5137 * (gapWord x o).sum ∧ 10000 * ℓ < 5279 * o := by
  have h45 := Frontier.E_ge_of_barina hB h.1 hx hx1
  have hnot := Frontier.not_mem_exceptions (E := (gapWord x o).sum) (by omega)
  obtain ⟨r1, r2⟩ := repeat_linear hEl h hnot hij hj hw
  -- the sign: `1584 o < 1000 E`
  have hD := CycleLiterature.cycle_Dz_pos h.1 hx
  have hsgn : 3 ^ o < 2 ^ (gapWord x o).sum := by
    have : (3 : ℤ) ^ o < 2 ^ (gapWord x o).sum := by
      simp only [Dz, D, gapWord_length] at hD; linarith
    exact_mod_cast this
  have hlow : 1584 * o < 1000 * (gapWord x o).sum := by
    by_contra hc
    replace hc := not_lt.mp hc
    have e1 : 2 ^ (1000 * (gapWord x o).sum) ≤ 2 ^ (1584 * o) := Nat.pow_le_pow_right (by norm_num) hc
    have e2 : 3 ^ (1000 * o) < 2 ^ (1000 * (gapWord x o).sum) := by
      rw [mul_comm 1000 o, mul_comm 1000 (gapWord x o).sum, pow_mul, pow_mul]
      exact Nat.pow_lt_pow_left hsgn (by norm_num)
    have e3 : 2 ^ (1584 * o) ≤ 3 ^ (1000 * o) := by
      rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by decide +kernel) o
    exact absurd (lt_of_lt_of_le e2 (e1.trans e3)) (lt_irrefl _)
  -- the sandwich: `1000 E < 1740 o`
  have hsand := Circuits.sandwich_linear h.1.1 (Limits.two_pow_mul_three_pow_le h.1 hx hx1)
  constructor <;> omega

end Syracuse.Repeat
