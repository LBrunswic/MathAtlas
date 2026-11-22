import Syracuse.Basic

/-!
# The Diophantine closed form (`approaches/diophantine`)

The canonical, project-wide statement of the closed form linking the `o`-th odd term of an
accelerated Syracuse trajectory to its start, in the notation locked by
`approaches/diophantine/STATUS.md`:

  `2^{e_o} a_o - 3^o a_0 = Σ_{k=0}^{o-1} 2^{e_k} 3^{o-1-k}`,

where `a_k` is the `k`-th odd term (`a_{k+1} = (3a_k+1)/2^{e_{k+1}-e_k}`) and `e_k` is the number of
even steps before the `k`-th odd term (`e_0 = 0`, `e_{k+1} - e_k = ν₂(3a_k+1)`).

The algebraic content is already in `Syracuse.Basic` (`Follows.closed_form`, `S_eq_sum`); this
file re-exports it in the notes' notation `(e_k, a_k, o)`, proves it once more by the notes'
own induction for an *arbitrary* sequence obeying the recurrence (any commutative ring, so over
`ℤ`, `ℚ`, `ℤ₂` alike, i.e. a `ℤ[X,Y]` identity), and reconciles it with the `(b_k, x_k, n)`
notation of `approaches/parity-manipulation`.

## Coverage

| Note claim (file) | Lean name | Status |
|---|---|---|
| Closed form for any sequence obeying `2^{e_{k+1}-e_k} a_{k+1} = 3a_k + 1`, "algebraic, holds over `ℤ, ℚ, ℤ₂`" (RATIONALE; CHEATSHEET "Core identity"; STATUS "Next step", induction on `o`) | `closed_form_seq` (generic `X, Y`), `closed_form_seq_int` | proved |
| Canonical statement `2^{e_o} a_o - 3^o a_0 = Σ 2^{e_k} 3^{o-1-k}` for the accelerated map (RATIONALE, STATUS) | `closed_form` (`a`, `e` = notes' `a_k`, `e_k`) | proved (for every integer start; oddness not needed) |
| `e_0 = 0`, `e_{k+1} - e_k = ν₂(3a_k+1)` (RATIONALE) | `e_zero`, `e_succ`, `step` | proved |
| odd start ⇒ all `a_k` odd, `e_{k+1} - e_k ≥ 1`, `(e_k)` strictly increasing (RATIONALE) | `odd_a`, `one_le_e_succ_sub`, `e_strictMono` | proved |
| Σ-form of the word closed form (`S(w)` as the explicit sum) | `Follows.closed_form_sum`, `e_eq_word_e`, `e_eq_sum_gapWord` | proved |
| Reconciliation with parity-manipulation's `2^{b_n}x_n - 3^n x_0 = Σ 2^{b_k}3^{n-1-k}`: `b_k ↔ e_k`, `x_k ↔ a_k`, `n ↔ o` (STATUS "Open questions"; CHEATSHEET "Equivalence") | `PM.x`, `PM.b`, `PM.x_eq`, `PM.b_eq`, `PM.closed_form` | proved (identical objects; the `ℤ₂^×` extension of `T` is not formalized) |
| parity-manipulation's `T(x) = (3x+1)·|3x+1|₂` agrees with `syr` on `ℤ` | `PM.T_eq_syr` | proved |
| Corollary: cycle equation (set `a_o = a_0`) `(2^{e_o} - 3^o) a_0 = Σ …` (STATUS) | `cycle_equation` | proved |
| Corollary: `2^{e_o} ≠ 3^o` for `o ≥ 1`, so `D ∣ S` and `a_0 = S / D` on a cycle | `two_pow_ne_three_pow`, `cycle_dvd`, `cycle_start_eq_div` | proved |
| Corollary: rational reconstruction `a_0 = 2^{e_o} a_o / 3^o - Σ_{k<o} 2^{e_k}/3^{k+1}` (STATUS: finite form of the 2-adic reconstruction) | `rational_reconstruction` | proved (finite form) |
| Corollary: 2-adic series `a_0 = -Σ_{k≥0} 2^{e_k} 3^{-(k+1)}` (STATUS) | — | not formalized (needs `ℤ₂` convergence; belongs to parity-manipulation) |
| Corollary: size bounds from the identity (STATUS, unspecified) | `three_pow_le_sum`, `three_pow_mul_lt` | proved (`3^{o-1} ≤ Σ`, hence `3^o a_0 < 2^{e_o} a_o` for `o ≥ 1`) |
-/

namespace Syracuse.Diophantine

open Finset

/-! ## The closed form for an arbitrary sequence obeying the recurrence -/

section Generic

variable {R : Type*} [CommRing R] (X Y : R)

/-- **Closed form, algebraic version** (the notes' proof by induction on `o`). Let `e : ℕ → ℕ` be
non-decreasing up to `o` with `e 0 = 0`, and let `a : ℕ → R` obey the recurrence
`X^{e_{k+1} - e_k} a_{k+1} = Y a_k + 1` for `k < o`. Then
`X^{e_o} a_o - Y^o a_0 = Σ_{k<o} X^{e_k} Y^{o-1-k}`. Being proved for arbitrary `X, Y` in an
arbitrary commutative ring, it is a `ℤ[X,Y]` identity, valid over `ℤ`, `ℚ` and `ℤ₂`. -/
theorem closed_form_seq (a : ℕ → R) (e : ℕ → ℕ) (o : ℕ) (he0 : e 0 = 0)
    (hmono : ∀ k < o, e k ≤ e (k + 1))
    (hrec : ∀ k < o, X ^ (e (k + 1) - e k) * a (k + 1) = Y * a k + 1) :
    X ^ e o * a o - Y ^ o * a 0 = ∑ k ∈ range o, X ^ e k * Y ^ (o - 1 - k) := by
  induction o with
  | zero => simp [he0]
  | succ o ih =>
    have ih := ih (fun k hk => hmono k (by omega)) (fun k hk => hrec k (by omega))
    have hstep : X ^ e (o + 1) * a (o + 1) = X ^ e o * (Y * a o + 1) := by
      rw [← hrec o (by omega), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (hmono o (by omega))]
    have hsum : ∑ k ∈ range o, X ^ e k * Y ^ (o + 1 - 1 - k) =
        Y * ∑ k ∈ range o, X ^ e k * Y ^ (o - 1 - k) := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hk : k < o := mem_range.1 hk
      rw [show o + 1 - 1 - k = (o - 1 - k) + 1 by omega, pow_succ]
      ring
    rw [sum_range_succ, hsum, ← ih, hstep, show o + 1 - 1 - o = 0 by omega]
    ring

end Generic

/-- The algebraic closed form specialised to `(X, Y) = (2, 3)` over `ℤ`. -/
theorem closed_form_seq_int (a : ℕ → ℤ) (e : ℕ → ℕ) (o : ℕ) (he0 : e 0 = 0)
    (hmono : ∀ k < o, e k ≤ e (k + 1))
    (hrec : ∀ k < o, 2 ^ (e (k + 1) - e k) * a (k + 1) = 3 * a k + 1) :
    2 ^ e o * a o - 3 ^ o * a 0 = ∑ k ∈ range o, (2 : ℤ) ^ e k * 3 ^ (o - 1 - k) :=
  closed_form_seq 2 3 a e o he0 hmono hrec

/-! ## The notes' notation `a_k`, `e_k` for the accelerated map -/

/-- `a_k`: the `k`-th odd term of the trajectory of `a₀` under the accelerated map `syr`
(so `a a₀ 0 = a₀`). -/
def a (a₀ : ℤ) (k : ℕ) : ℤ := syr^[k] a₀

/-- `e_k`: the number of even steps before the `k`-th odd term,
`e_k = Σ_{i<k} ν₂(3 a_i + 1)`. -/
def e (a₀ : ℤ) (k : ℕ) : ℕ := ∑ i ∈ range k, gap (a a₀ i)

@[simp] lemma a_zero (a₀ : ℤ) : a a₀ 0 = a₀ := rfl

/-- `a_{k+1} = syr(a_k)`. -/
lemma a_succ (a₀ : ℤ) (k : ℕ) : a a₀ (k + 1) = syr (a a₀ k) :=
  Function.iterate_succ_apply' syr k a₀

@[simp] lemma e_zero (a₀ : ℤ) : e a₀ 0 = 0 := by simp [e]

/-- `e_{k+1} = e_k + ν₂(3 a_k + 1)`. -/
lemma e_succ (a₀ : ℤ) (k : ℕ) : e a₀ (k + 1) = e a₀ k + gap (a a₀ k) := by
  simp [e, sum_range_succ]

/-- `e_{k+1} - e_k = ν₂(3 a_k + 1)`. -/
lemma e_succ_sub (a₀ : ℤ) (k : ℕ) : e a₀ (k + 1) - e a₀ k = gap (a a₀ k) := by
  rw [e_succ]; omega

/-- `(e_k)` is non-decreasing. -/
lemma e_mono (a₀ : ℤ) (k : ℕ) : e a₀ k ≤ e a₀ (k + 1) := by rw [e_succ]; omega

/-- The defining recurrence `2^{e_{k+1} - e_k} a_{k+1} = 3 a_k + 1`. -/
theorem step (a₀ : ℤ) (k : ℕ) : 2 ^ (e a₀ (k + 1) - e a₀ k) * a a₀ (k + 1) = 3 * a a₀ k + 1 := by
  rw [e_succ_sub, a_succ, two_pow_gap_mul_syr]

/-- **The canonical Diophantine closed form** (`approaches/diophantine`):
`2^{e_o} a_o - 3^o a_0 = Σ_{k=0}^{o-1} 2^{e_k} 3^{o-1-k}`. Oddness of the start is not needed. -/
theorem closed_form (a₀ : ℤ) (o : ℕ) :
    2 ^ e a₀ o * a a₀ o - 3 ^ o * a a₀ 0 = ∑ k ∈ range o, (2 : ℤ) ^ e a₀ k * 3 ^ (o - 1 - k) :=
  closed_form_seq_int (a a₀) (e a₀) o (e_zero a₀) (fun k _ => e_mono a₀ k)
    (fun k _ => step a₀ k)

/-- For an odd start every `a_k` is odd. -/
theorem odd_a {a₀ : ℤ} (h : Odd a₀) (k : ℕ) : Odd (a a₀ k) := by
  cases k with
  | zero => exact h
  | succ k => rw [a_succ]; exact syr_odd _

/-- For an odd start, `e_{k+1} - e_k = ν₂(3a_k + 1) ≥ 1`. -/
theorem one_le_e_succ_sub {a₀ : ℤ} (h : Odd a₀) (k : ℕ) : 1 ≤ e a₀ (k + 1) - e a₀ k := by
  rw [e_succ_sub]; exact one_le_gap (odd_a h k)

/-- For an odd start, `(e_k)` is strictly increasing. -/
theorem e_strictMono {a₀ : ℤ} (h : Odd a₀) : StrictMono (e a₀) :=
  strictMono_nat_of_lt_succ fun k => by have := one_le_e_succ_sub h k; omega

/-! ## Link with the word formalism of `Syracuse.Basic` -/

/-- The notes' `e_k` is the prefix sum `Syracuse.e` of the gap word, for every `k ≤ o`. -/
theorem e_eq_word_e (a₀ : ℤ) {k o : ℕ} (hk : k ≤ o) : e a₀ k = Syracuse.e (gapWord a₀ o) k := by
  induction o generalizing a₀ k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ o ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [gapWord, e_cons_succ, ← ih (syr a₀) (by omega)]
      simp only [e, a]
      rw [sum_range_succ', add_comm]
      simp [Function.iterate_succ_apply]

/-- `E = e_o` is the gap-sum `|w|` of the gap word. -/
theorem e_eq_sum_gapWord (a₀ : ℤ) (o : ℕ) : e a₀ o = (gapWord a₀ o).sum := by
  rw [e_eq_word_e a₀ le_rfl, Syracuse.e, List.take_of_length_le (by simp)]

/-- **Σ-form of the word closed form.** Along any word, at any `(X, Y)`,
`X^{e_o} b - Y^o a = Σ_{k<o} X^{e_k} Y^{o-1-k}` with `e_k` the prefix sums of `w`. -/
theorem Follows.closed_form_sum {R : Type*} [CommRing R] {X Y : R} {w : Word}
    {a b : R} (h : Follows X Y w a b) :
    X ^ Syracuse.e w w.length * b - Y ^ w.length * a =
      ∑ k ∈ range w.length, X ^ Syracuse.e w k * Y ^ (w.length - 1 - k) := by
  rw [Syracuse.e, List.take_of_length_le le_rfl, ← S_eq_sum, h.closed_form]
  ring

/-! ## Reconciliation with `parity-manipulation`'s `(b_k, x_k, n)` -/

namespace PM

/-- parity-manipulation's `x_k`: the `k`-th iterate of the accelerated map from `x₀`. -/
def x (x₀ : ℤ) (k : ℕ) : ℤ := syr^[k] x₀

/-- parity-manipulation's `b_n = Σ_{k<n} ν₂(3 x_k + 1)` (with `b_0 = 0`). -/
def b (x₀ : ℤ) (n : ℕ) : ℕ := ∑ k ∈ range n, padicValInt 2 (3 * x x₀ k + 1)

/-- `x_k ↔ a_k`: the same objects. -/
theorem x_eq : x = a := rfl

/-- `b_k ↔ e_k`: the same objects. -/
theorem b_eq : b = e := rfl

/-- parity-manipulation's closed form `2^{b_n} x_n - 3^n x_0 = Σ_{k<n} 2^{b_k} 3^{n-1-k}`; it is
literally `closed_form` under `n ↔ o`, `b ↔ e`, `x ↔ a`. -/
theorem closed_form (x₀ : ℤ) (n : ℕ) :
    2 ^ b x₀ n * x x₀ n - 3 ^ n * x x₀ 0 = ∑ k ∈ range n, (2 : ℤ) ^ b x₀ k * 3 ^ (n - 1 - k) :=
  Diophantine.closed_form x₀ n

/-- parity-manipulation's `T(x) = (3x+1)·|3x+1|₂` coincides with `syr` on `ℤ`. -/
theorem T_eq_syr (x₀ : ℤ) :
    ((3 * x₀ + 1 : ℤ) : ℚ) * padicNorm 2 ((3 * x₀ + 1 : ℤ) : ℚ) = (syr x₀ : ℚ) := by
  have hne : ((3 * x₀ + 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast three_mul_add_one_ne_zero x₀
  have hg : padicValRat 2 ((3 * x₀ + 1 : ℤ) : ℚ) = gap x₀ := by rw [padicValRat.of_int]; rfl
  rw [padicNorm.eq_zpow_of_nonzero hne, hg, zpow_neg, zpow_natCast, ← two_pow_gap_mul_syr x₀]
  push_cast
  field_simp

end PM

/-! ## Corollaries -/

/-- `2^E ≠ 3^o` for `o ≥ 1`: `3^o` is odd and `> 1`. -/
theorem two_pow_ne_three_pow (E : ℕ) {o : ℕ} (ho : 0 < o) : (2 : ℤ) ^ E ≠ 3 ^ o := by
  intro h
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · have : (3 : ℤ) ≤ 3 ^ o := le_self_pow₀ (by norm_num) ho.ne'
    rw [← h] at this; norm_num at this
  · have h2 : (2 : ℤ) ∣ 3 ^ o := h ▸ dvd_pow_self 2 hE.ne'
    have := Int.Prime.dvd_pow' (p := 2) Nat.prime_two (n := 3) (k := o) (by exact_mod_cast h2)
    norm_num at this

/-- **Cycle equation.** If the trajectory returns, `a_o = a_0`, then
`(2^{e_o} - 3^o) a_0 = Σ_{k<o} 2^{e_k} 3^{o-1-k}`. -/
theorem cycle_equation {a₀ : ℤ} {o : ℕ} (h : a a₀ o = a₀) :
    (2 ^ e a₀ o - 3 ^ o) * a₀ = ∑ k ∈ range o, (2 : ℤ) ^ e a₀ k * 3 ^ (o - 1 - k) := by
  rw [← closed_form, h, a_zero]; ring

/-- On a cycle of length `o ≥ 1`, `D = 2^{e_o} - 3^o` divides the sum. -/
theorem cycle_dvd {a₀ : ℤ} {o : ℕ} (h : a a₀ o = a₀) :
    (2 ^ e a₀ o - 3 ^ o : ℤ) ∣ ∑ k ∈ range o, (2 : ℤ) ^ e a₀ k * 3 ^ (o - 1 - k) :=
  ⟨a₀, (cycle_equation h).symm⟩

/-- On a cycle of length `o ≥ 1`, `a_0 = S / D`. -/
theorem cycle_start_eq_div {a₀ : ℤ} {o : ℕ} (ho : 0 < o) (h : a a₀ o = a₀) :
    a₀ = (∑ k ∈ range o, (2 : ℤ) ^ e a₀ k * 3 ^ (o - 1 - k)) / (2 ^ e a₀ o - 3 ^ o) := by
  have hD : (2 ^ e a₀ o - 3 ^ o : ℤ) ≠ 0 := sub_ne_zero.2 (two_pow_ne_three_pow _ ho)
  rw [← cycle_equation h, Int.mul_ediv_cancel_left _ hD]

/-- **Rational reconstruction (finite form).** In `ℚ`,
`a_0 = 2^{e_o} a_o / 3^o - Σ_{k<o} 2^{e_k} / 3^{k+1}`. -/
theorem rational_reconstruction (a₀ : ℤ) (o : ℕ) :
    (a₀ : ℚ) = 2 ^ e a₀ o * a a₀ o / 3 ^ o - ∑ k ∈ range o, (2 : ℚ) ^ e a₀ k / 3 ^ (k + 1) := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (closed_form a₀ o)
  push_cast at h
  have h3 : (3 : ℚ) ^ o ≠ 0 := by positivity
  have hs : ∑ k ∈ range o, (2 : ℚ) ^ e a₀ k / 3 ^ (k + 1) =
      (∑ k ∈ range o, (2 : ℚ) ^ e a₀ k * 3 ^ (o - 1 - k)) / 3 ^ o := by
    rw [sum_div]
    refine sum_congr rfl fun k hk => ?_
    have hk : k < o := mem_range.1 hk
    rw [eq_div_iff h3, div_mul_eq_mul_div, show o = (o - 1 - k) + (k + 1) by omega, pow_add,
      show o - 1 - k + (k + 1) - 1 - k = o - 1 - k by omega]
    field_simp
  rw [hs, ← h, a_zero]
  field_simp
  ring

/-- Size bound: for `o ≥ 1` the sum is at least its first term `3^{o-1}`. -/
theorem three_pow_le_sum (a₀ : ℤ) {o : ℕ} (ho : 0 < o) :
    (3 : ℤ) ^ (o - 1) ≤ ∑ k ∈ range o, (2 : ℤ) ^ e a₀ k * 3 ^ (o - 1 - k) := by
  obtain ⟨o, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ho.ne'
  rw [sum_range_succ']
  simp only [e_zero, pow_zero, one_mul, Nat.succ_sub_one, tsub_zero]
  have : 0 ≤ ∑ k ∈ range o, (2 : ℤ) ^ e a₀ (k + 1) * 3 ^ (o - (k + 1)) :=
    sum_nonneg fun _ _ => by positivity
  linarith

/-- Growth: for `o ≥ 1`, `3^o a_0 < 2^{e_o} a_o`. -/
theorem three_pow_mul_lt (a₀ : ℤ) {o : ℕ} (ho : 0 < o) : 3 ^ o * a₀ < 2 ^ e a₀ o * a a₀ o := by
  have h1 := closed_form a₀ o
  have h2 := three_pow_le_sum a₀ ho
  have : (0 : ℤ) < 3 ^ (o - 1) := by positivity
  rw [a_zero] at h1
  linarith

end Syracuse.Diophantine
