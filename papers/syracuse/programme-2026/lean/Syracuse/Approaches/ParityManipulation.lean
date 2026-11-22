import Syracuse.Basic

/-!
# Parity manipulation: the 2-adic reconstruction and single-block shifts

Formalizes `approaches/parity-manipulation` (`RATIONALE.md`, `STATUS.md`,
`derivation-single-shift.md`, `derivation-general-shift.md`, `circuit-manipulation.md`).

The notes' `(b_k, x_k, n)` are Basic's `(e_k, a_k, o)`. A *parity vector* is `b : ℕ → ℕ` strictly
increasing with `b 0 = 0` (`IsParityVec`); its gap word up to time `n` is
`gaps b n = (b₁ - b₀, …, b_n - b_{n-1})`, so `(gaps b n).sum = b n`. In `ℤ_[2]` we write `third`
for `1/3`, and the reconstruction is `x0 b = -∑' k, 2^{b k} third^{k+1}`. The trajectory point at
time `n` is `traj b n = x0 (k ↦ b (n+k) - b n)`.
The single-block shift `b'_k = b_k + a·1_{k>q}` is `shiftPV b q a`.

The shift formula is first proved as an identity in an arbitrary commutative ring (`shift_formula`,
from Basic's `Follows.closed_form`): it compares two orbits along `u ++ [d]` and `u ++ [d']` that
reach the same point. The 2-adic statements are then instances of it.

## Coverage

| Note claim (file) | Lean | Status |
|---|---|---|
| `x₀ = -∑ 2^{b_k}/3^{k+1}` converges in `ℤ₂` (RATIONALE, single-shift §Setup) | `summable_term`, `x0` | proved |
| a trajectory with parity vector `(b_k)` exists: `2^{b_{n+1}-b_n} x_{n+1} = 3x_n + 1`, `x_n` odd, `ν₂(3x_n+1) = b_{n+1}-b_n` (RATIONALE obs. 2) | `traj_step`, `norm_traj`, `valuation_traj`, `follows_traj`, `T_iterate_x0` | proved |
| that trajectory is unique (RATIONALE obs. 2) | `eq_x0_of_recurrence` (no oddness assumption needed) | proved |
| closed form `2^{b_n}x_n - 3^n x₀ = ∑ 2^{b_k}3^{n-1-k}` (RATIONALE) | `follows_traj` + `Follows.closed_form`, `S_eq_sum` (Basic) | proved |
| bijection "strictly increasing `(b_n)` ↔ `ℤ₂`", `T : ℤ₂^× → ℤ₂^×` (RATIONALE) | `parityEquiv`, `range_x0`, `neg_third_not_admissible`, `two_not_admissible` | corrected: the image is `Admissible` = odd `x` whose `T`-orbit never meets `-1/3` (where `3x+1 = 0` and `T` is undefined); even `x` and `-1/3` are not reached |
| Form 1 (tail) `x₀ - x'₀ = (2^a-1)∑_{k>q} 2^{b_k}/3^{k+1}` (general-shift; `a = 1` in single-shift) | `tail_form` | proved |
| reindexed tail `∑_{k>q} 2^{b_k}/3^{k+1} = -2^{b_{q+1}}x_{q+1}/3^{q+1}` (single-shift) | `tsum_tail` | proved |
| Form 2 (trajectory) `x₀ - x'₀ = -(2^a-1)2^{b_{q+1}}x_{q+1}/3^{q+1}` (general-shift, STATUS) | `trajectory_form`, `shift_formula_padic`; generic `shift_formula`, `shift_formula_add` | proved; `x'₀` is the reconstruction of `b'_k = b_k + a·1_{k>q}`, `a ≥ 0` |
| Form 3 (head) `x'₀ - 2^a x₀ = (2^a-1)∑_{k≤q} 2^{b_k}/3^{k+1}` | `head_form`; generic `head_identity` | proved |
| `3 ∤ x_n` for `n ≥ 1` on integer trajectories (single-shift) | `not_three_dvd_of_follows`, `not_three_dvd_padic` | proved |
| LTE: `ν₃(2^a-1) = 0` (`a` odd), `1 + ν₃(a)` (`a` even) (general-shift) | `padicValNat_three_two_pow_sub_one_of_odd`, `…_of_even` | proved (`a ≠ 0` in the even case, as in the note) |
| `ν₃(2^a-1) ≥ q+1 ⇔ 2·3^q ∣ a`; `ord_{3^{q+1}}(2) = 2·3^q` | `three_pow_succ_dvd_two_pow_sub_one_iff`, `two_pow_eq_one_iff`, `orderOf_two` | proved |
| integrality: `x₀ ∈ ℤ ⇒ (x₀ - x'₀ ∈ ℤ ⇔ 2·3^q ∣ a)` (general-shift, STATUS) | `integrality_padic`; generic `integrality` (any char-0 domain, hyp. `x_{q+1} ∈ ℤ`, `3 ∤ x_{q+1}`) | proved; the hypotheses are right (`3 ∤ x_{q+1}` is automatic for `x₀ ∈ ℤ`) |
| negative shifts: same condition `2·3^q ∣ |a|` | `integrality_sym` | proved |
| `a = 1` never gives an integer difference (single-shift, STATUS dead end) | `single_shift_never_integral` | proved |
| `q = 0, a = 2` is `x ↦ 4x + 1`; examples `1 ↦ 5`, `1 ↦ 113` | `predecessor_four_mul_add_one`, `example`s | proved |
| "`a ∈ 2·3^q ℤ` enumerates the depth-`(q+1)` predecessors of `x_{q+1}`" (general-shift, STATUS) | `predecessor_gap_dvd`, `example` `13 → 5 → 1` | corrected: it enumerates the predecessors that share the first `q` gaps; `13` (gaps `(3,4)`) is a depth-2 predecessor of `1` not reached from `1` at `q = 1` (first gap fixed at `2`) |
| 3-adic propagation `ν₃(x'_{q-j} - x_{q-j}) = ν₃(2^a-1) - j - 1` | `three_adic_propagation` (over `ℚ`, for the suffix of length `j+1`) | proved (`a ≠ 0`) |
| validity bound `|a| ≤ c_{q+1} - 1` for `a < 0` | — | not formalized (it is strict monotonicity of `b'`) |
| finite-support no-go: `δ = b' - b` vanishes for `k ≥ N` ⇒ `x'_k = x_k` (STATUS, general-shift) | `finite_support_nogo`; general `traj_eq_of_eventually_const`, `traj_eq_iff`, `follows_to_common_node` | corrected: as stated it does not cover the single-block shift (`δ = a·1_{k>q}` never vanishes); the right hypothesis is `δ` constant on `[N, ∞)`, and then `x'_N = x_N ⇔ δ` constant on `[N, ∞)` |
| cycle formula `x₀ = S/(2^C - 3^P)` for `b_{k+P} = b_k + C` (circuit) | `cycle_formula` (as `(2^C - 3^P)x₀ = S` in `ℤ₂`) | proved |
| difference formula for two periodic vectors (circuit) | `circuit_difference` | proved |
| unit test: `1` vs `-5`, difference `6` (circuit) | `x0_two_mul`, `x0_minus_five`, `example` | proved |
| `δ = αk + π(k)`; "full Collatz tree generated"; infinite-support programme; Baker leverage | — | not formalized (definitional, or open questions) |
-/

namespace Syracuse.ParityManipulation

open Syracuse Filter Topology

/-! ## 1. The shift formula as a ring identity -/

section Algebra

variable {R : Type*} [CommRing R] {X Y : R}

/-- `S` does not see the last gap: `S(u ++ [d]) = Y S(u) + X^{|u|}`. -/
theorem S_append_singleton (X Y : R) (u : Word) (d : ℕ) :
    S X Y (u ++ [d]) = Y * S X Y u + X ^ u.sum := by
  rw [S_append, S_singleton]; simp

/-- **Shift formula.** Two orbits along `u ++ [d]` and `u ++ [d']` that end at the same point `y`
differ by `Y^{len u + 1} (x - x') = (X^{|u|+d} - X^{|u|+d'}) y`. A `ℤ[X,Y]` identity, from the
closed form. -/
theorem shift_formula {u : Word} {d d' : ℕ} {x x' y : R}
    (h : Follows X Y (u ++ [d]) x y) (h' : Follows X Y (u ++ [d']) x' y) :
    Y ^ (u.length + 1) * (x - x') = (X ^ (u.sum + d) - X ^ (u.sum + d')) * y := by
  have c := h.closed_form
  have c' := h'.closed_form
  simp only [List.sum_append, List.sum_singleton, List.length_append, List.length_singleton,
    S_append_singleton] at c c'
  linear_combination c' - c

/-- Form 2 with denominators cleared: for the shift `d ↦ d + a` of the last gap,
`Y^{q+1} (x - x') = -(X^a - 1) X^{b_{q+1}} y`, where `q = len u` and `b_{q+1} = |u| + d`. -/
theorem shift_formula_add {u : Word} {d a : ℕ} {x x' y : R}
    (h : Follows X Y (u ++ [d]) x y) (h' : Follows X Y (u ++ [d + a]) x' y) :
    Y ^ (u.length + 1) * (x - x') = -((X ^ a - 1) * X ^ (u.sum + d) * y) := by
  rw [shift_formula h h', ← add_assoc, pow_add _ (u.sum + d)]; ring

/-- Form 3 (head identity) with denominators cleared:
`Y^{q+1} (x' - X^a x) = (X^a - 1) S(u ++ [d])`, and `S(u ++ [d]) = ∑_{k≤q} X^{b_k} Y^{q-k}`. -/
theorem head_identity {u : Word} {d a : ℕ} {x x' y : R}
    (h : Follows X Y (u ++ [d]) x y) (h' : Follows X Y (u ++ [d + a]) x' y) :
    Y ^ (u.length + 1) * (x' - X ^ a * x) = (X ^ a - 1) * S X Y (u ++ [d]) := by
  have c := h.closed_form
  have c' := h'.closed_form
  simp only [List.sum_append, List.sum_singleton, List.length_append, List.length_singleton,
    S_append_singleton, ← add_assoc, pow_add] at c c' ⊢
  linear_combination X ^ a * c - c'

/-- The minimal shift at depth `0` is the predecessor map: `[d]` versus `[d + 2]` to the same
point gives `x' = 4x + 1`. -/
theorem predecessor_four_mul_add_one {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {d : ℕ} {x x' y : R} (h : Follows (2 : R) 3 [d] x y) (h' : Follows (2 : R) 3 [d + 2] x' y) :
    x' = 4 * x + 1 := by
  have key := shift_formula_add (u := []) h h'
  have h3 : (3 : R) ≠ 0 := by exact_mod_cast (show (3 : ℕ) ≠ 0 by norm_num)
  cases h with
  | cons hs hr =>
    cases hr
    simp only [List.length_nil, zero_add, pow_one, List.sum_nil] at key
    apply mul_left_cancel₀ h3
    linear_combination -key + 3 * hs

end Algebra

/-! ## 2. The 3-adic valuation of `2^a - 1` (lifting the exponent) -/

/-- `ν₃(2^a - 1) = 0` for odd `a`. -/
theorem padicValNat_three_two_pow_sub_one_of_odd {a : ℕ} (ha : Odd a) :
    padicValNat 3 (2 ^ a - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  obtain ⟨k, rfl⟩ := ha
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  rw [pow_succ, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow]
  decide

/-- **LTE.** `ν₃(2^a - 1) = 1 + ν₃(a)` for even `a ≠ 0`. -/
theorem padicValNat_three_two_pow_sub_one_of_even {a : ℕ} (ha : Even a) (ha0 : a ≠ 0) :
    padicValNat 3 (2 ^ a - 1) = 1 + padicValNat 3 a := by
  obtain ⟨m, rfl⟩ := ha
  have hm : m ≠ 0 := by omega
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) (by decide) (by norm_num) (by norm_num)
    (by norm_num) hm
  rw [one_pow, show (4 : ℕ) - 1 = 3 by rfl, padicValNat_self] at this
  rw [← two_mul, pow_mul, show (2 : ℕ) ^ 2 = 4 by rfl, this, padicValNat.mul (by norm_num) hm,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), zero_add]

/-- `3^{q+1} ∣ 2^a - 1 ⇔ 2·3^q ∣ a` (for every `a`, including `0`). -/
theorem three_pow_succ_dvd_two_pow_sub_one_iff (q a : ℕ) :
    3 ^ (q + 1) ∣ 2 ^ a - 1 ↔ 2 * 3 ^ q ∣ a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · simp
  have hne : 2 ^ a - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha0
    omega
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [padicValNat_dvd_iff_le hne]
  rcases Nat.even_or_odd a with he | ho
  · rw [padicValNat_three_two_pow_sub_one_of_even he ha0.ne', add_comm 1, add_le_add_iff_right,
      ← padicValNat_dvd_iff_le ha0.ne']
    constructor
    · intro h
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_right _ (by norm_num))
        (even_iff_two_dvd.mp he) h
    · exact fun h => (Nat.dvd_mul_left _ _).trans h
  · rw [padicValNat_three_two_pow_sub_one_of_odd ho]
    simp only [Nat.le_zero, Nat.add_one_ne_zero, false_iff]
    intro h
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr ((Nat.dvd_mul_right _ _).trans h))

/-- The same criterion in `ℤ`. -/
theorem int_three_pow_succ_dvd_iff (q a : ℕ) :
    (3 : ℤ) ^ (q + 1) ∣ 2 ^ a - 1 ↔ 2 * 3 ^ q ∣ a := by
  rw [← three_pow_succ_dvd_two_pow_sub_one_iff]
  have : ((2 ^ a - 1 : ℕ) : ℤ) = 2 ^ a - 1 := by push_cast [Nat.one_le_two_pow]; ring
  rw [← this, show (3 : ℤ) ^ (q + 1) = ((3 ^ (q + 1) : ℕ) : ℤ) by push_cast; rfl,
    Int.natCast_dvd_natCast]

/-- `2^a = 1` in `ZMod (3^{q+1})` iff `2·3^q ∣ a`. -/
theorem two_pow_eq_one_iff (q a : ℕ) : (2 : ZMod (3 ^ (q + 1))) ^ a = 1 ↔ 2 * 3 ^ q ∣ a := by
  rw [← three_pow_succ_dvd_two_pow_sub_one_iff, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero]
  simp

/-- The multiplicative order of `2` modulo `3^{q+1}` is `2·3^q`. -/
theorem orderOf_two (q : ℕ) : orderOf (2 : ZMod (3 ^ (q + 1))) = 2 * 3 ^ q := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((two_pow_eq_one_iff q _).mpr dvd_rfl)
  · exact (two_pow_eq_one_iff q _).mp (pow_orderOf_eq_one _)

/-! ## 3. Integrality of the shift -/

/-- `3^n` is coprime to `2^B y` when `3 ∤ y`. -/
lemma isCoprime_three_pow {y : ℤ} (hy : ¬ (3 : ℤ) ∣ y) (n B : ℕ) :
    IsCoprime ((3 : ℤ) ^ n) (2 ^ B * y) := by
  apply IsCoprime.pow_left
  rw [Irreducible.coprime_iff_not_dvd Int.prime_three.irreducible]
  intro h
  rcases Int.prime_three.dvd_mul.mp h with h2 | h2
  · have := Int.prime_three.dvd_of_dvd_pow h2
    norm_num at this
  · exact hy h2

/-- **Integrality theorem.** In a domain of characteristic `0` (e.g. `ℚ` or `ℤ_[2]`), let two
orbits along `u ++ [d]` and `u ++ [d + a]` end at the same integer `y` with `3 ∤ y`. Then
`x - x'` is an integer iff `2·3^q ∣ a`, where `q = len u`. -/
theorem integrality {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {u : Word} {d a : ℕ} {x x' : R} {y : ℤ}
    (h : Follows (2 : R) 3 (u ++ [d]) x y) (h' : Follows (2 : R) 3 (u ++ [d + a]) x' y)
    (hy : ¬ (3 : ℤ) ∣ y) :
    (∃ m : ℤ, x - x' = m) ↔ 2 * 3 ^ u.length ∣ a := by
  have key := shift_formula_add h h'
  set B := u.sum + d
  have key' : (3 : R) ^ (u.length + 1) * (x - x') = ((-((2 ^ a - 1) * 2 ^ B * y) : ℤ) : R) := by
    rw [key]; push_cast; ring
  rw [← int_three_pow_succ_dvd_iff]
  constructor
  · rintro ⟨m, hm⟩
    rw [hm] at key'
    have : (3 : ℤ) ^ (u.length + 1) * m = -((2 ^ a - 1) * 2 ^ B * y) := by
      exact_mod_cast key'
    have hd : (3 : ℤ) ^ (u.length + 1) ∣ (2 ^ a - 1) * (2 ^ B * y) := by
      rw [← mul_assoc, ← dvd_neg, ← this]; exact dvd_mul_right _ _
    exact (isCoprime_three_pow hy _ B).dvd_of_dvd_mul_right hd
  · rintro ⟨t, ht⟩
    refine ⟨-(t * 2 ^ B * y), ?_⟩
    have h3 : (3 : R) ≠ 0 := by exact_mod_cast (show (3 : ℕ) ≠ 0 by norm_num)
    apply mul_left_cancel₀ (pow_ne_zero (u.length + 1) h3)
    rw [key', ht]; push_cast; ring

/-- One integer Syracuse step lands off the multiples of `3`. -/
theorem not_three_dvd_of_step {d : ℕ} {x y : ℤ} (h : 2 ^ d * y = 3 * x + 1) : ¬ (3 : ℤ) ∣ y := by
  intro h3
  have : (3 : ℤ) ∣ 3 * x + 1 := h ▸ dvd_mul_of_dvd_right h3 _
  omega

/-- On an integer orbit, `3 ∤ x_n` for every `n ≥ 1`. -/
theorem not_three_dvd_of_follows {u : Word} {d : ℕ} {x y : ℤ}
    (h : Follows (2 : ℤ) 3 (u ++ [d]) x y) : ¬ (3 : ℤ) ∣ y := by
  obtain ⟨z, -, hz⟩ := h.of_append
  cases hz with
  | cons hstep hrest =>
    cases hrest
    exact not_three_dvd_of_step hstep

/-- **Integrality, any sign.** For last gaps `d` and `d'` (so the shift is `a = d' - d ∈ ℤ`),
`x - x' ∈ ℤ ⇔ 2·3^q ∣ d' - d`. -/
theorem integrality_sym {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {u : Word} {d d' : ℕ} {x x' : R} {y : ℤ}
    (h : Follows (2 : R) 3 (u ++ [d]) x y) (h' : Follows (2 : R) 3 (u ++ [d']) x' y)
    (hy : ¬ (3 : ℤ) ∣ y) :
    (∃ m : ℤ, x - x' = m) ↔ (2 * 3 ^ u.length : ℤ) ∣ (d' : ℤ) - d := by
  rcases le_total d d' with hle | hle
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [integrality h h' hy]
    push_cast
    rw [add_sub_cancel_left]
    exact_mod_cast Iff.rfl
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hle
    have := integrality h' h hy
    have e : (∃ m : ℤ, x - x' = m) ↔ (∃ m : ℤ, x' - x = m) :=
      ⟨fun ⟨m, hm⟩ => ⟨-m, by push_cast; rw [← hm]; ring⟩,
       fun ⟨m, hm⟩ => ⟨-m, by push_cast; rw [← hm]; ring⟩⟩
    rw [e, this]
    push_cast
    rw [sub_add_cancel_left, dvd_neg]
    exact_mod_cast Iff.rfl

/-- Two integer predecessors of `y` that share the first `q` gaps have last gaps congruent modulo
`2·3^q`. So the admissible shifts enumerate exactly the predecessors with the same first `q` gaps. -/
theorem predecessor_gap_dvd {u : Word} {d d' : ℕ} {x x' y : ℤ}
    (h : Follows (2 : ℤ) 3 (u ++ [d]) x y) (h' : Follows (2 : ℤ) 3 (u ++ [d']) x' y) :
    (2 * 3 ^ u.length : ℤ) ∣ (d' : ℤ) - d :=
  (integrality_sym h h' (not_three_dvd_of_follows h)).mp ⟨x - x', by simp⟩

/-- **3-adic propagation.** Over `ℚ`, `ν₃(x - x') = ν₃(2^a - 1) - (q + 1)` for the shift `d ↦ d + a`
(`a ≠ 0`) at depth `q = len u`, when the common endpoint `y` is an integer prime to `3`. Applied to the
suffix starting at time `q - j` this is `ν₃(x'_{q-j} - x_{q-j}) = ν₃(2^a - 1) - j - 1`. -/
theorem three_adic_propagation {u : Word} {d a : ℕ} {x x' : ℚ} {y : ℤ}
    (h : Follows (2 : ℚ) 3 (u ++ [d]) x y) (h' : Follows (2 : ℚ) 3 (u ++ [d + a]) x' y)
    (hy : ¬ (3 : ℤ) ∣ y) (ha : a ≠ 0) :
    padicValRat 3 (x - x') = (padicValNat 3 (2 ^ a - 1) : ℤ) - (u.length + 1 : ℕ) := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := u.sum + d
  set n := u.length + 1
  have hA : (2 : ℤ) ^ a - 1 = ((2 ^ a - 1 : ℕ) : ℤ) := by push_cast [Nat.one_le_two_pow]; ring
  have hA0 : (2 ^ a - 1 : ℕ) ≠ 0 := by
    have : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero ha)
    omega
  have hy0 : y ≠ 0 := by rintro rfl; exact hy (dvd_zero _)
  have hK0 : ((2 : ℤ) ^ a - 1) * (2 ^ B * y) ≠ 0 := by
    rw [hA]; exact mul_ne_zero (by exact_mod_cast hA0) (mul_ne_zero (by positivity) hy0)
  have key : (3 : ℚ) ^ n * (x - x') = ((-(((2 : ℤ) ^ a - 1) * (2 ^ B * y)) : ℤ) : ℚ) := by
    rw [shift_formula_add h h']; push_cast; ring
  have hd0 : x - x' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at key
    exact hK0 (neg_eq_zero.mp (by exact_mod_cast key.symm))
  have := congrArg (padicValRat 3) key
  have h33 : padicValRat 3 (3 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 3) (by norm_num)
  rw [padicValRat.mul (by positivity) hd0, padicValRat.pow, h33, padicValRat.of_int] at this
  have e : padicValInt 3 (-(((2 : ℤ) ^ a - 1) * (2 ^ B * y))) = padicValNat 3 (2 ^ a - 1) := by
    have hneg : ∀ z : ℤ, padicValInt 3 (-z) = padicValInt 3 z := fun z => by simp [padicValInt]
    rw [hneg, padicValInt.mul (by rw [hA]; exact_mod_cast hA0) (mul_ne_zero (by positivity) hy0),
      padicValInt.mul (by positivity) hy0, hA, padicValInt.of_nat,
      padicValInt.eq_zero_of_not_dvd (z := 2 ^ B) (fun h3 => by
        have := Int.prime_three.dvd_of_dvd_pow h3; norm_num at this),
      padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hy)]
    simp
  rw [e] at this
  push_cast at this ⊢
  linarith

/-- Worked example (`q = 0, a = 2`): `5 → 1` with gap `4 = 2 + 2`. -/
example : Follows (2 : ℤ) 3 [4] 5 1 := Follows.cons (by norm_num) (Follows.nil _)

/-- Worked example (`q = 1, a = 6`): `113 → 85 → 1` with gaps `(2, 8) = (2, 2 + 6)`. -/
example : Follows (2 : ℤ) 3 [2, 8] 113 1 :=
  Follows.cons (a' := 85) (by norm_num) (Follows.cons (by norm_num) (Follows.nil _))

/-- Counterexample to "the shifts enumerate all depth-`(q+1)` predecessors": `13 → 5 → 1` has
gaps `(3, 4)`, while every `q = 1` shift of `1` (gaps `(2, 2)`) keeps the first gap `2`. -/
example : Follows (2 : ℤ) 3 [3, 4] 13 1 :=
  Follows.cons (a' := 5) (by norm_num) (Follows.cons (by norm_num) (Follows.nil _))

/-! ## 4. The 2-adic reconstruction -/

/-- `|2|₂ = 1/2`. -/
lemma norm_two : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  simpa using PadicInt.norm_p (p := 2)

/-- `|3|₂ = 1`. -/
lemma norm_three : ‖(3 : ℤ_[2])‖ = 1 := by
  have := (PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 3)).mpr (by norm_num)
  exact_mod_cast this

/-- `3` is a unit of `ℤ_[2]`. -/
lemma isUnit_three : IsUnit (3 : ℤ_[2]) := PadicInt.isUnit_iff.mpr norm_three

/-- `1/3 ∈ ℤ_[2]`. -/
noncomputable def third : ℤ_[2] := ↑(isUnit_three.unit⁻¹)

@[simp] lemma three_mul_third : (3 : ℤ_[2]) * third = 1 := isUnit_three.mul_val_inv

/-- `|1/3|₂ = 1`. -/
lemma norm_third : ‖third‖ = 1 := by
  have := congrArg norm three_mul_third
  rwa [norm_mul, norm_three, one_mul, norm_one] at this

/-- A parity vector: `b` strictly increasing with `b 0 = 0`. -/
def IsParityVec (b : ℕ → ℕ) : Prop := StrictMono b ∧ b 0 = 0

/-- A parity vector grows at least linearly. -/
lemma IsParityVec.le_apply {b : ℕ → ℕ} (hb : IsParityVec b) (k : ℕ) : k ≤ b k := hb.1.id_le k

/-- The `k`-th term `2^{b_k}/3^{k+1}` of the reconstruction series. -/
noncomputable def term (b : ℕ → ℕ) (k : ℕ) : ℤ_[2] := 2 ^ b k * third ^ (k + 1)

/-- `|2^{b_k}/3^{k+1}|₂ = 2^{-b_k}`. -/
lemma norm_term (b : ℕ → ℕ) (k : ℕ) : ‖term b k‖ = 2⁻¹ ^ b k := by
  simp [term, norm_two, norm_third]

/-- The series converges in `ℤ₂` as soon as `b_k ≥ k`. -/
lemma summable_term {b : ℕ → ℕ} (hb : ∀ k, k ≤ b k) : Summable (term b) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num))
  rw [norm_term]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hb k)

/-- **The 2-adic reconstruction** `x₀ = -∑_{k≥0} 2^{b_k}/3^{k+1}`. -/
noncomputable def x0 (b : ℕ → ℕ) : ℤ_[2] := -∑' k, term b k

/-- The parity vector seen from time `n`: `k ↦ b_{n+k} - b_n`. -/
def shiftSeq (b : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun k => b (n + k) - b n

/-- The trajectory point `x_n`: the reconstruction of the parity vector seen from time `n`. -/
noncomputable def traj (b : ℕ → ℕ) (n : ℕ) : ℤ_[2] := x0 (shiftSeq b n)

/-- A parity vector seen from time `n` is a parity vector. -/
lemma IsParityVec.shiftSeq {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) :
    IsParityVec (shiftSeq b n) := by
  refine ⟨fun k l hkl => ?_, by simp [ParityManipulation.shiftSeq]⟩
  have h1 := hb.1 (show n + k < n + l by omega)
  have h2 := hb.1.monotone (show n ≤ n + k by omega)
  simp only [ParityManipulation.shiftSeq]
  omega

/-- `x_0 = x0 b`. -/
lemma traj_zero {b : ℕ → ℕ} (hb : IsParityVec b) : traj b 0 = x0 b := by
  unfold traj
  congr 1
  funext k
  simp [shiftSeq, hb.2]

/-- The first step: `2^{b_1} x_1 = 3 x_0 + 1`. -/
theorem x0_step {b : ℕ → ℕ} (hb : IsParityVec b) :
    2 ^ b 1 * x0 (shiftSeq b 1) = 3 * x0 b + 1 := by
  have hs := summable_term hb.le_apply
  have ht : ∀ k, term b (k + 1) = 2 ^ b 1 * third * term (shiftSeq b 1) k := by
    intro k
    have hm := hb.1.monotone (show 1 ≤ 1 + k by omega)
    have : b (k + 1) = b 1 + (b (1 + k) - b 1) := by rw [add_comm k 1]; omega
    simp only [term, shiftSeq]
    rw [this, pow_add]
    ring
  unfold x0
  rw [hs.tsum_eq_zero_add]
  simp_rw [ht]
  rw [(summable_term (hb.shiftSeq 1).le_apply).tsum_mul_left]
  have h0 : term b 0 = third := by simp [term, hb.2]
  rw [h0]
  linear_combination (1 + 2 ^ b 1 * ∑' k, term (shiftSeq b 1) k) * three_mul_third

/-- **Prescribed parity, recurrence.** `2^{b_{n+1} - b_n} x_{n+1} = 3 x_n + 1`. -/
theorem traj_step {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) :
    2 ^ (b (n + 1) - b n) * traj b (n + 1) = 3 * traj b n + 1 := by
  have h := x0_step (hb.shiftSeq n)
  have e : shiftSeq (shiftSeq b n) 1 = shiftSeq b (n + 1) := by
    funext k
    have h1 := hb.1.monotone (show n ≤ n + 1 by omega)
    have h2 := hb.1.monotone (show n + 1 ≤ n + 1 + k by omega)
    simp only [shiftSeq, show n + (1 + k) = n + 1 + k by omega]
    omega
  rw [e] at h
  simpa [shiftSeq, traj] using h

/-- The reconstruction is odd: `|x₀|₂ = 1`. -/
theorem norm_x0 {b : ℕ → ℕ} (hb : IsParityVec b) : ‖x0 b‖ = 1 := by
  have h := x0_step hb
  have hb1 : 1 ≤ b 1 := by have := hb.1 Nat.zero_lt_one; rw [hb.2] at this; omega
  have hlt : ‖(2 : ℤ_[2]) ^ b 1 * x0 (shiftSeq b 1)‖ < ‖(-1 : ℤ_[2])‖ := by
    rw [norm_mul, norm_pow, norm_two, norm_neg, norm_one]
    calc (2 : ℝ)⁻¹ ^ b 1 * ‖x0 (shiftSeq b 1)‖ ≤ (2 : ℝ)⁻¹ ^ b 1 * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity)
      _ ≤ 2⁻¹ ^ 1 := by rw [mul_one]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hb1
      _ < 1 := by norm_num
  have h3 : (3 : ℤ_[2]) * x0 b = 2 ^ b 1 * x0 (shiftSeq b 1) + -1 := by rw [h]; ring
  have := congrArg norm h3
  rw [PadicInt.norm_add_eq_max_of_ne hlt.ne, max_eq_right hlt.le, norm_mul, norm_three, one_mul,
    norm_neg, norm_one] at this
  exact this

/-- **Prescribed parity, oddness.** Every trajectory point is odd: `|x_n|₂ = 1`. -/
lemma norm_traj {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) : ‖traj b n‖ = 1 :=
  norm_x0 (hb.shiftSeq n)

/-- An odd 2-adic integer has valuation `0`. -/
lemma valuation_eq_zero_of_norm {u : ℤ_[2]} (hu : ‖u‖ = 1) : u.valuation = 0 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  by_contra hne
  have := (PadicInt.norm_le_pow_iff_le_valuation u hu0 1).mpr (by omega)
  rw [hu] at this
  norm_num at this

/-- `ν₂(2^c u) = c` for odd `u`. -/
theorem valuation_two_pow_mul {u : ℤ_[2]} (hu : ‖u‖ = 1) (c : ℕ) :
    ((2 : ℤ_[2]) ^ c * u).valuation = c := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have := PadicInt.valuation_p_pow_mul (p := 2) c u hu0
  rw [valuation_eq_zero_of_norm hu, add_zero] at this
  exact_mod_cast this

/-- **Prescribed parity, gaps.** `ν₂(3 x_n + 1) = b_{n+1} - b_n`. -/
theorem valuation_traj {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) :
    (3 * traj b n + 1).valuation = b (n + 1) - b n := by
  rw [← traj_step hb n, valuation_two_pow_mul (norm_traj hb (n + 1))]

/-- The gap word `(b₁ - b₀, …, b_n - b_{n-1})` of the first `n` steps. -/
def gaps (b : ℕ → ℕ) (n : ℕ) : Word := (List.range n).map fun k => b (k + 1) - b k

/-- `gaps b (n+1) = gaps b n ++ [b_{n+1} - b_n]`. -/
lemma gaps_succ (b : ℕ → ℕ) (n : ℕ) : gaps b (n + 1) = gaps b n ++ [b (n + 1) - b n] := by
  simp [gaps, List.range_succ]

@[simp] lemma gaps_length (b : ℕ → ℕ) (n : ℕ) : (gaps b n).length = n := by simp [gaps]

/-- The prefix sums of the gap word are the parity vector: `|gaps b n| = b_n`. -/
lemma gaps_sum {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) : (gaps b n).sum = b n := by
  induction n with
  | zero => simp [gaps, hb.2]
  | succ n ih =>
    rw [gaps_succ, List.sum_append, ih, List.sum_singleton]
    have := hb.1 (show n < n + 1 by omega)
    omega

/-- The reconstruction follows its gap word to `x_n` (so Basic's closed form applies). -/
theorem follows_traj {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) :
    Follows (2 : ℤ_[2]) 3 (gaps b n) (x0 b) (traj b n) := by
  induction n with
  | zero => rw [traj_zero hb]; exact Follows.nil _
  | succ n ih =>
    rw [gaps_succ]
    exact ih.append (Follows.cons (traj_step hb n) (Follows.nil _))

/-- **Uniqueness.** Any sequence in `ℤ₂` obeying the recurrence with gaps `b_{n+1} - b_n` starts at
`x₀`. (Proof: `3^n (y₀ - x₀) = 2^{b_n}(y_n - x_n)`, so `|y₀ - x₀|₂ ≤ 2^{-n}` for all `n`.) -/
theorem eq_x0_of_recurrence {b : ℕ → ℕ} (hb : IsParityVec b) {y : ℕ → ℤ_[2]}
    (hy : ∀ n, 2 ^ (b (n + 1) - b n) * y (n + 1) = 3 * y n + 1) : y 0 = x0 b := by
  set z : ℕ → ℤ_[2] := fun n => y n - traj b n with hzdef
  have hz : ∀ n, 3 ^ n * z 0 = 2 ^ b n * z n := by
    intro n
    induction n with
    | zero => simp [hb.2]
    | succ n ih =>
      have h1 := hy n
      have h2 := traj_step hb n
      have hbn : b (n + 1) = b n + (b (n + 1) - b n) := by
        have := hb.1 (show n < n + 1 by omega); omega
      simp only [hzdef] at ih ⊢
      rw [pow_succ, hbn, pow_add]
      linear_combination 3 * ih + 2 ^ b n * (h2 - h1)
  have hnorm : ∀ n, ‖z 0‖ ≤ 2⁻¹ ^ n := by
    intro n
    have := congrArg norm (hz n)
    rw [norm_mul, norm_mul, norm_pow, norm_three, one_pow, one_mul, norm_pow, norm_two] at this
    rw [this]
    calc (2 : ℝ)⁻¹ ^ b n * ‖z n‖ ≤ 2⁻¹ ^ b n * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity)
      _ ≤ 2⁻¹ ^ n := by
          rw [mul_one]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hb.le_apply n)
  have hz0 : z 0 = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hne) (by norm_num : (2 : ℝ)⁻¹ < 1)
    linarith [hnorm n]
  simp only [hzdef, traj_zero hb, sub_eq_zero] at hz0
  exact hz0

/-- **Injectivity.** Distinct parity vectors reconstruct distinct 2-adic points. -/
theorem x0_injective {b b' : ℕ → ℕ} (hb : IsParityVec b) (hb' : IsParityVec b')
    (h : x0 b = x0 b') : b = b' := by
  have key : ∀ n, b n = b' n ∧ traj b n = traj b' n := by
    intro n
    induction n with
    | zero => exact ⟨hb.2.trans hb'.2.symm, by rw [traj_zero hb, traj_zero hb', h]⟩
    | succ n ih =>
      obtain ⟨e1, e2⟩ := ih
      have s := traj_step hb n
      have s' := traj_step hb' n
      have hs : (2 : ℤ_[2]) ^ (b (n + 1) - b n) * traj b (n + 1)
          = 2 ^ (b' (n + 1) - b' n) * traj b' (n + 1) := by rw [s, s', e2]
      have hv := congrArg PadicInt.valuation hs
      rw [valuation_two_pow_mul (norm_traj hb _), valuation_two_pow_mul (norm_traj hb' _)] at hv
      have m1 := hb.1 (show n < n + 1 by omega)
      have m2 := hb'.1 (show n < n + 1 by omega)
      refine ⟨by omega, ?_⟩
      rw [hv] at hs
      exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) hs
  funext n
  exact (key n).1

/-! ## 5. The 2-adic Syracuse map and the bijection -/

open scoped Classical in
/-- The 2-adic accelerated Syracuse map `T(x) = (3x+1)/2^{ν₂(3x+1)}`; it is undefined at
`x = -1/3`, where we put the junk value `0`. -/
noncomputable def T (x : ℤ_[2]) : ℤ_[2] :=
  if h : 3 * x + 1 = 0 then 0 else (PadicInt.unitCoeff h : ℤ_[2])

/-- `2^{ν₂(3x+1)} T(x) = 3x + 1` away from `-1/3`. -/
lemma two_pow_valuation_mul_T {x : ℤ_[2]} (h : 3 * x + 1 ≠ 0) :
    2 ^ (3 * x + 1).valuation * T x = 3 * x + 1 := by
  have e : T x = (PadicInt.unitCoeff h : ℤ_[2]) := by simp [T, h]
  rw [e, mul_comm]
  have := PadicInt.unitCoeff_spec h
  exact_mod_cast this.symm

/-- `T(x)` is odd away from `-1/3`. -/
lemma norm_T {x : ℤ_[2]} (h : 3 * x + 1 ≠ 0) : ‖T x‖ = 1 := by
  have e : T x = (PadicInt.unitCoeff h : ℤ_[2]) := by simp [T, h]
  rw [e]; exact PadicInt.norm_units _

/-- If `2^c y = 3x + 1` with `y` odd, then `T(x) = y`. -/
lemma T_eq_of {x y : ℤ_[2]} {c : ℕ} (hy : ‖y‖ = 1) (h : 2 ^ c * y = 3 * x + 1) : T x = y := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hne : 3 * x + 1 ≠ 0 := h ▸ mul_ne_zero (pow_ne_zero _ two_ne_zero) hy0
  have hv : (3 * x + 1).valuation = c := h ▸ valuation_two_pow_mul hy c
  have := two_pow_valuation_mul_T hne
  rw [hv, ← h] at this
  exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) this

/-- The reconstruction's `T`-orbit is the trajectory: `Tⁿ(x₀) = x_n`. -/
theorem T_iterate_x0 {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) : T^[n] (x0 b) = traj b n := by
  induction n with
  | zero => exact (traj_zero hb).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    exact T_eq_of (norm_traj hb _) (traj_step hb n)

/-- For odd `u` (and `3u + 1 ≠ 0`), `ν₂(3u + 1) ≥ 1`. -/
lemma one_le_valuation {u : ℤ_[2]} (hu : ‖u‖ = 1) (h : 3 * u + 1 ≠ 0) :
    1 ≤ (3 * u + 1).valuation := by
  obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range (p := 2) (x := u)
  have hunit : IsUnit u := PadicInt.isUnit_iff.mpr hu
  interval_cases n
  · simp only [Nat.cast_zero, sub_zero] at hmem
    exact absurd hunit ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  · rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hmem
    have h4 : ‖(4 : ℤ_[2])‖ < 1 := by
      rw [show (4 : ℤ_[2]) = 2 ^ 2 by norm_num, norm_pow, norm_two]; norm_num
    have hlt : ‖3 * u + 1‖ < 1 := by
      rw [show 3 * u + 1 = 3 * (u - 1) + 4 by ring]
      refine PadicInt.norm_lt_one_add ?_ h4
      rw [norm_mul, norm_three, one_mul]; simpa using hmem
    rw [PadicInt.norm_lt_one_iff_dvd] at hlt
    rw [← PadicInt.mem_span_pow_iff_le_valuation _ h, pow_one, Ideal.mem_span_singleton]
    exact hlt

/-- The starting points that have a parity vector: odd, and the `T`-orbit never meets `-1/3`. -/
def Admissible (x : ℤ_[2]) : Prop := ‖x‖ = 1 ∧ ∀ n, 3 * T^[n] x + 1 ≠ 0

/-- Every reconstruction is admissible. -/
theorem admissible_x0 {b : ℕ → ℕ} (hb : IsParityVec b) : Admissible (x0 b) := by
  refine ⟨norm_x0 hb, fun n => ?_⟩
  rw [T_iterate_x0 hb, ← traj_step hb n]
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (by
    intro h0; have := norm_traj hb (n + 1); rw [h0, norm_zero] at this; exact zero_ne_one this)

/-- Every admissible point is a reconstruction (its parity vector is read off the `T`-orbit). -/
theorem exists_x0_of_admissible {x : ℤ_[2]} (hx : Admissible x) :
    ∃ b, IsParityVec b ∧ x0 b = x := by
  set c : ℕ → ℕ := fun n => (3 * T^[n] x + 1).valuation with hc
  set b : ℕ → ℕ := fun n => ∑ k ∈ Finset.range n, c k with hbdef
  have hunit : ∀ n, ‖T^[n] x‖ = 1 := by
    intro n
    cases n with
    | zero => exact hx.1
    | succ n => rw [Function.iterate_succ_apply']; exact norm_T (hx.2 n)
  have hc1 : ∀ n, 1 ≤ c n := fun n => one_le_valuation (hunit n) (hx.2 n)
  have hstep : ∀ n, b (n + 1) - b n = c n := by
    intro n; simp only [hbdef, Finset.sum_range_succ]; omega
  have hb : IsParityVec b := by
    refine ⟨strictMono_nat_of_lt_succ fun n => ?_, by simp [hbdef]⟩
    have := hstep n; have := hc1 n; omega
  refine ⟨b, hb, ?_⟩
  have := eq_x0_of_recurrence hb (y := fun n => T^[n] x) (fun n => by
    simp only [hstep]
    rw [Function.iterate_succ_apply']
    exact two_pow_valuation_mul_T (hx.2 n))
  exact this.symm

/-- The image of the reconstruction is exactly the admissible points. -/
theorem range_x0 : {x | ∃ b, IsParityVec b ∧ x0 b = x} = {x | Admissible x} := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩; exact admissible_x0 hb
  · exact exists_x0_of_admissible

/-- **The bijection** (corrected): parity vectors `≃` admissible 2-adic starting points. -/
noncomputable def parityEquiv : {b : ℕ → ℕ // IsParityVec b} ≃ {x : ℤ_[2] // Admissible x} :=
  Equiv.ofBijective (fun b => ⟨x0 b.1, admissible_x0 b.2⟩)
    ⟨fun b b' h => Subtype.ext (x0_injective b.2 b'.2 (congrArg Subtype.val h)),
     fun x => by
      obtain ⟨b, hb, hbx⟩ := exists_x0_of_admissible x.2
      exact ⟨⟨b, hb⟩, Subtype.ext hbx⟩⟩

/-- `-1/3` is odd but has no parity vector (`3x + 1 = 0`), so the map is not onto `ℤ₂^×`. -/
theorem neg_third_not_admissible : ¬ Admissible (-third) := by
  rintro ⟨-, h⟩
  exact h 0 (by simp)

/-- Even points have no parity vector, so the map is not onto `ℤ₂`. -/
theorem two_not_admissible : ¬ Admissible 2 := by
  rintro ⟨h, -⟩
  rw [norm_two] at h; norm_num at h

/-! ## 6. The single-block shift in `ℤ₂` -/

/-- The single-block shift `b'_k = b_k + a·1_{k>q}`. -/
def shiftPV (b : ℕ → ℕ) (q a : ℕ) : ℕ → ℕ := fun k => if q < k then b k + a else b k

/-- The shifted vector is a parity vector. -/
lemma IsParityVec.shiftPV {b : ℕ → ℕ} (hb : IsParityVec b) (q a : ℕ) :
    IsParityVec (shiftPV b q a) := by
  refine ⟨strictMono_nat_of_lt_succ fun n => ?_, by simp [ParityManipulation.shiftPV, hb.2]⟩
  have := hb.1 (show n < n + 1 by omega)
  simp only [ParityManipulation.shiftPV]
  split_ifs <;> omega

/-- Past the block the shifted vector, seen from time `n > q`, is unchanged. -/
lemma shiftSeq_shiftPV (b : ℕ → ℕ) {q n : ℕ} (a : ℕ) (hn : q < n) :
    shiftSeq (shiftPV b q a) n = shiftSeq b n := by
  funext k
  simp only [shiftSeq, shiftPV, hn, show q < n + k by omega, ↓reduceIte]
  omega

/-- `x'_n = x_n` for `n > q`. -/
lemma traj_shiftPV (b : ℕ → ℕ) {q n : ℕ} (a : ℕ) (hn : q < n) :
    traj (shiftPV b q a) n = traj b n := by
  rw [traj, shiftSeq_shiftPV b a hn, traj]

/-- The shifted gap word: only the gap at index `q` changes, by `+a`. -/
lemma gaps_shiftPV {b : ℕ → ℕ} (hb : IsParityVec b) (q a : ℕ) :
    gaps (shiftPV b q a) (q + 1) = gaps b q ++ [b (q + 1) - b q + a] := by
  rw [gaps_succ]
  congr 1
  · simp only [gaps]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    simp [shiftPV, show ¬ q < k + 1 by omega, show ¬ q < k by omega]
  · have := hb.1 (show q < q + 1 by omega)
    simp only [shiftPV, show q < q + 1 by omega, lt_irrefl, ↓reduceIte]
    congr 1
    omega

/-- **Form 2 in `ℤ₂`, denominators cleared:**
`3^{q+1} (x₀ - x'₀) = -(2^a - 1) 2^{b_{q+1}} x_{q+1}`. -/
theorem shift_formula_padic {b : ℕ → ℕ} (hb : IsParityVec b) (q a : ℕ) :
    3 ^ (q + 1) * (x0 b - x0 (shiftPV b q a))
      = -((2 ^ a - 1) * 2 ^ b (q + 1) * traj b (q + 1)) := by
  have h := follows_traj hb (q + 1)
  rw [gaps_succ] at h
  have h' := follows_traj (hb.shiftPV q a) (q + 1)
  rw [gaps_shiftPV hb, traj_shiftPV b a (show q < q + 1 by omega)] at h'
  have key := shift_formula_add h h'
  have e : (gaps b q).sum + (b (q + 1) - b q) = b (q + 1) := by
    rw [gaps_sum hb]; have := hb.1 (show q < q + 1 by omega); omega
  rwa [gaps_length, e] at key

/-- Head plus tail: `x₀ = -(∑_{k<n} 2^{b_k}/3^{k+1} + ∑_{k≥n} 2^{b_k}/3^{k+1})`. -/
lemma x0_split {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) :
    x0 b = -(∑ k ∈ Finset.range n, term b k + ∑' k, term b (k + n)) := by
  rw [x0, (summable_term hb.le_apply).sum_add_tsum_nat_add n]

/-- Tails of the series converge. -/
lemma summable_term_add {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) :
    Summable fun k => term b (k + n) :=
  (summable_nat_add_iff n).mpr (summable_term hb.le_apply)

/-- **Reindexed tail.** `∑_{k≥n} 2^{b_k}/3^{k+1} = -2^{b_n} x_n / 3^n`. -/
theorem tsum_tail {b : ℕ → ℕ} (hb : IsParityVec b) (n : ℕ) :
    ∑' k, term b (k + n) = -(2 ^ b n * third ^ n * traj b n) := by
  have e : ∀ k, term b (k + n) = 2 ^ b n * third ^ n * term (shiftSeq b n) k := by
    intro k
    have := hb.1.monotone (show n ≤ n + k by omega)
    simp only [term, shiftSeq]
    rw [show b (k + n) = b n + (b (n + k) - b n) by rw [add_comm k n]; omega, pow_add,
      show k + n + 1 = n + (k + 1) by ring, pow_add]
    ring
  simp_rw [e]
  rw [(summable_term (hb.shiftSeq n).le_apply).tsum_mul_left, traj, x0]
  ring

/-- The shift leaves the head terms `k ≤ q` unchanged. -/
lemma term_shiftPV_low (b : ℕ → ℕ) {q k : ℕ} (a : ℕ) (hk : k ≤ q) :
    term (shiftPV b q a) k = term b k := by
  simp [term, shiftPV, show ¬ q < k by omega]

/-- The shift multiplies the tail terms `k > q` by `2^a`. -/
lemma term_shiftPV_high (b : ℕ → ℕ) (q a k : ℕ) :
    term (shiftPV b q a) (k + (q + 1)) = 2 ^ a * term b (k + (q + 1)) := by
  simp only [term, shiftPV, show q < k + (q + 1) by omega, ↓reduceIte, pow_add]
  ring

/-- **Form 1 (tail series).** `x₀ - x'₀ = (2^a - 1) ∑_{k>q} 2^{b_k}/3^{k+1}`. -/
theorem tail_form {b : ℕ → ℕ} (hb : IsParityVec b) (q a : ℕ) :
    x0 b - x0 (shiftPV b q a) = (2 ^ a - 1) * ∑' k, term b (k + (q + 1)) := by
  rw [x0_split hb (q + 1), x0_split (hb.shiftPV q a) (q + 1),
    Finset.sum_congr rfl fun k hk => term_shiftPV_low b a (by simp at hk; omega)]
  simp_rw [term_shiftPV_high]
  rw [(summable_term_add hb (q + 1)).tsum_mul_left]
  ring

/-- **Form 2 (trajectory form).** `x₀ - x'₀ = -(2^a - 1) 2^{b_{q+1}} x_{q+1} / 3^{q+1}`. -/
theorem trajectory_form {b : ℕ → ℕ} (hb : IsParityVec b) (q a : ℕ) :
    x0 b - x0 (shiftPV b q a)
      = -((2 ^ a - 1) * 2 ^ b (q + 1) * traj b (q + 1) * third ^ (q + 1)) := by
  rw [tail_form hb, tsum_tail hb]
  ring

/-- **Form 3 (head identity).** `x'₀ - 2^a x₀ = (2^a - 1) ∑_{k≤q} 2^{b_k}/3^{k+1}`. -/
theorem head_form {b : ℕ → ℕ} (hb : IsParityVec b) (q a : ℕ) :
    x0 (shiftPV b q a) - 2 ^ a * x0 b = (2 ^ a - 1) * ∑ k ∈ Finset.range (q + 1), term b k := by
  rw [x0_split hb (q + 1), x0_split (hb.shiftPV q a) (q + 1),
    Finset.sum_congr rfl fun k hk => term_shiftPV_low b a (by simp at hk; omega)]
  simp_rw [term_shiftPV_high]
  rw [(summable_term_add hb (q + 1)).tsum_mul_left]
  ring

/-- An orbit in `ℤ₂` that starts at an integer stays in `ℤ`. -/
theorem follows_int_of_int {w : Word} :
    ∀ {x y : ℤ_[2]} {X : ℤ}, Follows (2 : ℤ_[2]) 3 w x y → x = X → ∃ Y : ℤ, y = Y := by
  induction w with
  | nil => intro x y X h hX; cases h; exact ⟨X, hX⟩
  | cons d w ih =>
    intro x y X h hX
    cases h with
    | @cons _ _ _ a' _ hstep hrest =>
      have hd : ((2 : ℕ) : ℤ_[2]) ^ d ∣ ((3 * X + 1 : ℤ) : ℤ_[2]) :=
        ⟨a', by push_cast; rw [← hX, ← hstep]⟩
      obtain ⟨Z, hZ⟩ := (PadicInt.pow_p_dvd_int_iff d (3 * X + 1)).mp hd
      refine ih hrest (X := Z) ?_
      apply mul_left_cancel₀ (pow_ne_zero d (two_ne_zero (α := ℤ_[2])))
      rw [hstep, hX]
      have : ((3 * X + 1 : ℤ) : ℤ_[2]) = ((2 ^ d * Z : ℤ) : ℤ_[2]) := by rw [hZ]; norm_num
      push_cast at this
      exact this

/-- On a 2-adic orbit from an integer, every later point is an integer prime to `3`. -/
theorem not_three_dvd_padic {u : Word} {d : ℕ} {x : ℤ_[2]} {X Y : ℤ}
    (h : Follows (2 : ℤ_[2]) 3 (u ++ [d]) x Y) (hX : x = X) : ¬ (3 : ℤ) ∣ Y := by
  obtain ⟨z, hu, hz⟩ := h.of_append
  obtain ⟨Z, hZ⟩ := follows_int_of_int hu hX
  cases hz with
  | cons hstep hrest =>
    cases hrest
    rw [hZ] at hstep
    exact not_three_dvd_of_step (d := d) (x := Z) (by exact_mod_cast hstep)

/-- **Integrality theorem (2-adic form).** For an integer starting point `x₀`,
`x₀ - x'₀ ∈ ℤ ⇔ 2·3^q ∣ a`. -/
theorem integrality_padic {b : ℕ → ℕ} (hb : IsParityVec b) {X : ℤ} (hX : x0 b = X) (q a : ℕ) :
    (∃ m : ℤ, x0 b - x0 (shiftPV b q a) = m) ↔ 2 * 3 ^ q ∣ a := by
  have h := follows_traj hb (q + 1)
  obtain ⟨Y, hY⟩ := follows_int_of_int h hX
  rw [gaps_succ, hY] at h
  have h' := follows_traj (hb.shiftPV q a) (q + 1)
  rw [gaps_shiftPV hb, traj_shiftPV b a (show q < q + 1 by omega), hY] at h'
  have := integrality h h' (not_three_dvd_padic h hX)
  rwa [gaps_length] at this

/-- The toy shift `a = 1` never yields an integer difference on an integer trajectory. -/
theorem single_shift_never_integral {b : ℕ → ℕ} (hb : IsParityVec b) {X : ℤ} (hX : x0 b = X)
    (q : ℕ) : ¬ ∃ m : ℤ, x0 b - x0 (shiftPV b q 1) = m := by
  rw [integrality_padic hb hX]
  intro h
  have := Nat.le_of_dvd one_pos h
  have := Nat.one_le_pow q 3 (by norm_num)
  omega

/-! ## 7. The finite-support no-go -/

/-- If `δ = b' - b` is constant on `[N, ∞)`, the trajectories agree from time `N` on. -/
theorem traj_eq_of_eventually_const {b b' : ℕ → ℕ} (hb : IsParityVec b) (hb' : IsParityVec b')
    {N : ℕ} (h : ∀ k, N ≤ k → b' k - b' N = b k - b N) {k : ℕ} (hk : N ≤ k) :
    traj b' k = traj b k := by
  unfold traj
  congr 1
  funext j
  have h1 := h (k + j) (by omega)
  have h2 := h k hk
  have m1 := hb.1.monotone hk
  have m2 := hb.1.monotone (show k ≤ k + j by omega)
  have m3 := hb'.1.monotone hk
  have m4 := hb'.1.monotone (show k ≤ k + j by omega)
  simp only [shiftSeq]
  omega

/-- **No-go, sharp form.** `x'_N = x_N` iff `δ = b' - b` is constant on `[N, ∞)`. So a perturbation
leaves the original tree iff it changes infinitely many gaps. -/
theorem traj_eq_iff {b b' : ℕ → ℕ} (hb : IsParityVec b) (hb' : IsParityVec b') (N : ℕ) :
    traj b' N = traj b N ↔ ∀ k, N ≤ k → b' k - b' N = b k - b N := by
  refine ⟨fun h k hk => ?_, fun h => traj_eq_of_eventually_const hb hb' h le_rfl⟩
  have := congrFun (x0_injective (hb'.shiftSeq N) (hb.shiftSeq N) h) (k - N)
  simpa [shiftSeq, Nat.add_sub_cancel' hk] using this

/-- **No-go, as stated in the notes.** If `b'_k = b_k` for `k ≥ N`, then `x'_k = x_k` for `k ≥ N`. -/
theorem finite_support_nogo {b b' : ℕ → ℕ} (hb : IsParityVec b) (hb' : IsParityVec b')
    {N : ℕ} (h : ∀ k, N ≤ k → b' k = b k) {k : ℕ} (hk : N ≤ k) : traj b' k = traj b k :=
  traj_eq_of_eventually_const hb hb' (fun k hk' => by rw [h k hk', h N le_rfl]) hk

/-- The perturbed start is a predecessor of the shared node `x_N`: its orbit along its own first
`N` gaps reaches `x_N`. -/
theorem follows_to_common_node {b b' : ℕ → ℕ} (hb : IsParityVec b) (hb' : IsParityVec b')
    {N : ℕ} (h : ∀ k, N ≤ k → b' k - b' N = b k - b N) :
    Follows (2 : ℤ_[2]) 3 (gaps b' N) (x0 b') (traj b N) :=
  traj_eq_of_eventually_const hb hb' h le_rfl ▸ follows_traj hb' N

/-! ## 8. Periodic parity vectors (`circuit-manipulation.md`) -/

/-- **Cycle formula.** If `b_{k+P} = b_k + C`, then `(2^C - 3^P) x₀ = S` with
`S = ∑_{r<P} 2^{b_r} 3^{P-1-r}`, i.e. `x₀ = S/(2^C - 3^P)`. -/
theorem cycle_formula {b : ℕ → ℕ} (hb : IsParityVec b) {P C : ℕ}
    (hper : ∀ k, b (k + P) = b k + C) :
    ((2 : ℤ_[2]) ^ C - 3 ^ P) * x0 b = S (2 : ℤ_[2]) 3 (gaps b P) := by
  have hC : b P = C := by simpa [hb.2] using hper 0
  have hs : shiftSeq b P = b := funext fun k => by simp [shiftSeq, add_comm P k, hper, hC]
  have h := follows_traj hb P
  rw [traj, hs] at h
  have := h.cycle_equation
  rwa [D, gaps_sum hb, gaps_length, hC] at this

/-- **Difference formula** for two periodic vectors with a common period `P`. -/
theorem circuit_difference {b b' : ℕ → ℕ} (hb : IsParityVec b) (hb' : IsParityVec b')
    {P C C' : ℕ} (hper : ∀ k, b (k + P) = b k + C) (hper' : ∀ k, b' (k + P) = b' k + C') :
    ((2 : ℤ_[2]) ^ C - 3 ^ P) * (2 ^ C' - 3 ^ P) * (x0 b - x0 b')
      = (2 ^ C' - 3 ^ P) * S (2 : ℤ_[2]) 3 (gaps b P) - (2 ^ C - 3 ^ P) * S 2 3 (gaps b' P) := by
  rw [← cycle_formula hb hper, ← cycle_formula hb' hper']
  ring

/-- The trivial cycle's parity vector `b_k = 2k`. -/
lemma isParityVec_two_mul : IsParityVec (fun k => 2 * k) :=
  ⟨fun _ _ h => by dsimp only; omega, rfl⟩

/-- The `-5` cycle's parity vector `b_{2j} = 3j`, `b_{2j+1} = 3j + 1`, i.e. `b_k = k + ⌊k/2⌋`. -/
lemma isParityVec_minus_five : IsParityVec (fun k => k + k / 2) :=
  ⟨strictMono_nat_of_lt_succ fun n => by omega, rfl⟩

/-- Unit test: `b_k = 2k` reconstructs `1`. -/
theorem x0_two_mul : x0 (fun k => 2 * k) = 1 := by
  have := cycle_formula isParityVec_two_mul (P := 1) (C := 2) (fun k => by ring)
  simp [gaps] at this
  linear_combination this

/-- Unit test: `b_k = k + ⌊k/2⌋` reconstructs `-5`. -/
theorem x0_minus_five : x0 (fun k => k + k / 2) = -5 := by
  have := cycle_formula isParityVec_minus_five (P := 2) (C := 3) (fun k => by omega)
  simp [gaps, List.range_succ] at this
  linear_combination -this

/-- Unit test: the twist from the trivial cycle to the `-5` cycle has `x₀ - x'₀ = 6`. -/
example : x0 (fun k => 2 * k) - x0 (fun k => k + k / 2) = 6 := by
  rw [x0_two_mul, x0_minus_five]; norm_num

end Syracuse.ParityManipulation
