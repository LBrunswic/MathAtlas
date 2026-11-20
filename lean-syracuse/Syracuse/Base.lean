import Syracuse.Valuation

/-!
# Syracuse § 1: the maps `f_A`, `T_A`, the sequences `a_n`, `p_n`, the basic identity, `A_u^n`, `RHS_n`

`def:ring_define` — `syracuse.tex:54`; `def:ring_define_2` — `syracuse.tex:61`; `lem:base` —
`syracuse.tex:67`; **`def:define_n__n_`** — `syracuse.tex:80`; `lem:ring_maps_rhs_n_` —
`syracuse.tex:84`. Only `def:define_n__n_` is marked; the four others carry findings (SCOPE).

> **def:ring_define.** Let $A$ be a $\ZZ/2\ZZ$-ring, define
> $$ \fonctiondeux{f_A}{A}{A}{x\in 2A}{3x+1}{x\notin 2A}{x/2} \text{ and }
> \fonction{T_A}{2A+1}{2A+1}{x}{\frac{3x+1}{2^{\nu_2(3x+1)}}}.$$

> **def:ring_define_2.** Let $A$ be a $\ZZ/2\ZZ$-ring. For $n\in \NN$, define
> $$\fonction{a_n}{2A+1}{\NN}{x}{\nu_2(3 T^n_A(x)+1)}$$ and
> $$\fonction{p_n}{2A+1}{\NN}{x}{\sum_{k<n}a_k(x)}$$

> **lem:base.** Let $A$ be a $\ZZ/2\ZZ$-ring and let $x\in A$, one has :
> $$\forall n\in \NN, \quad 2^{p_n(x)}T_A^n(x)-3^n x = \sum_{k=0}^{n-1} 2^{p_k(x)}\,3^{n-1-k} .$$

> **def:define_n__n_.** Let $n\in\NN^*$ and let $a\in (\NN^*)^\ZZ$, define
> $$ A_{u}^n(a)=\sum_{k=0} ^{n-1}3^k\prod_{i=0}^{n-1-k}2^{a_{u+i}} $$

> **lem:ring_maps_rhs_n_.** Let $A$ be a $\ZZ/2\ZZ$-ring. For $n\in \NN$, the maps
> $$\fonction{RHS_n}{\{p\in \NN^n~|~ p_0=0~\wedge~p_n \nearrow\nearrow \} }{A}{p}
> {\sum_{k=0}^{n-1}2^{p_k}3^{n-1-k}} $$ are injective.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `A` a ℤ/2ℤ-ring (all five labels) | ✓ carried (`IsZ2Ring`), or ⚠ weakened (`base` needs only `CommRing`) |
| `x ∈ A` (`lem:base`, l.67) | ✓ carried: `T` is extended to `A` by the same formula |
| `T_A(x)` defined, i.e. `3x+1 ≠ 0` (implicit, l.55) | ⚠ strengthened in `base_of_orbit`, `T_odd`, `a_eq_nu2`: Finding 2; `base` itself needs none |
| `2 ≠ 0` (claimed at l.50, false for `ℤ/2ℤ`) | ⚠ strengthened in `ring_maps_rhs`: Finding 3 |
| `A` integral (l.50 reading; not in the definition l.52) | ⚠ strengthened in `ring_maps_rhs` via `IsZ2Ring`: without it the lemma fails even with `2 ≠ 0` (`rhs_zmod6_not_injOn`) |
| `p₀ = 0` (`lem:ring_maps_rhs_n_`) | ⚠ weakened: not used |
| `a ∈ (ℕ*)^ℤ`, `n ∈ ℕ*` (`def:define_n__n_`) | ⚠ weakened: `a : ℤ → ℕ`, `n : ℕ` |

## SCOPE (disclosed)

* **Finding 1 (`def:ring_define`, l.55): the cases of `f_A` are swapped.** As printed, `f_A(x) = 3x+1`
  for `x ∈ 2A` and `x/2` for `x ∉ 2A`; no `y` has `2y = x` when `x ∉ 2A`, so no such map exists in
  any ℤ/2ℤ-ring (`printed_f_not_definable`). `f` is the reading of l.46–48 (halve the even, `3x+1`
  the odd).
* **Finding 2 (`def:ring_define`, l.55): `T_A` is undefined at `x₀ = -1/3` when `3 ∈ Aˣ`** (`ℤ₂`,
  `ℤ/2ℤ`; also `ℤ_(2)`, `ℤ[1/3]`, not formalized here). Then `x₀ ∈ 2A+1`, `3x₀+1 = 0`, the set `{n | 3x₀+1 ∈ 2ⁿA}` has no
  max, and (if `2 ≠ 0`) no odd `t` and `k ∈ ℕ` have `2ᵏ t = 3x₀ + 1`
  (`T_undefined_of_isUnit_three`); in `ℤ₂` for instance (`T_undefined_padicInt`).
  This is the only defect: `3x+1 = 0` forces `3 ∈ Aˣ` (`three_mul_add_one_ne_zero`), so in `ℤ`
  every orbit is good. `T` is total here (`T x = (3x+1)/2^{v2(3x+1)}` for every `x ∈ A`, junk value
  at `x₀`); where `3x+1 ≠ 0` it is the paper's map: `T x` is odd, `2^{ν₂(3x+1)} T x = 3x+1`, and it
  is the only such odd element (`T_odd`, `pow_v2_mul_T`, `T_unique`, `nu2_three_mul_add_one`).
* `def:ring_define_2` inherits Finding 2: `a n x ∈ ℕ` is the paper's `ν₂(3Tⁿx+1)` only when
  `3Tⁿx+1 ≠ 0` (`a_eq_nu2`); on the backward orbit of `x₀` the paper's `a_n` is not a natural
  number. `a` and `p` are total here (junk where the paper's are undefined).
* `lem:base` is proved for every `x ∈ A` and `n` (`base`), an identity of the total maps. It is
  the paper's statement on every orbit avoiding `x₀` (where `T`, `a`, `p` are the paper's), hence
  for every `x` when `3 ∉ Aˣ` (`base_of_orbit`, `base_of_not_isUnit_three`, e.g. `ℤ`). At `x₀` the
  printed statement cannot hold for any values: no odd `t` and `k ∈ ℕ` satisfy its `n = 1`
  instance `2ᵏ t - 3x₀ = 1` (`base_printed_fails_padicInt`). The printed proof (l.71–77) writes
  `a_1` for `a_0 = p_1` and shifts the indices of the last two sums (`∑_{k=1}^{n} 2^{p_{k+1}}
  3^{n-1-k}` for `∑_{k=1}^{n} 2^{p_k} 3^{n-k}`); the statement is unaffected.
* **Finding 3 (`lem:ring_maps_rhs_n_`, l.84–86): false for `A = ℤ/2ℤ`, every `n ≥ 2`.** There
  `RHS₂(0,1) = 5 = 1 = 7 = RHS₂(0,2)` (`ring_maps_rhs_printed_false`), and `RHS_n` is not
  injective (in fact constant, `= 3^{n-1} = 1`) (`rhs_zmod2_not_injOn`). `ℤ/2ℤ` is the only ℤ/2ℤ-ring with `2 = 0` (`IsZ2Ring.two_eq_zero_iff`).
  The lemma holds as soon as `2 ≠ 0`, the claim of l.50 (`ring_maps_rhs`), and then on all strictly
  increasing `p` without `p₀ = 0` (`rhs_injOn_strictMono`, for any domain with `2 ≠ 0` and
  `1 ∉ 2A`). `↗↗` is read as strictly increasing. Integrality is used too: in `ZMod 6`
  (noetherian, `A/2A ≃ ℤ/2ℤ`, `2 ≠ 0`, not integral) `RHS₂(0,1) = 5 = 11 = RHS₂(0,3)`
  (`rhs_zmod6_not_injOn`).
* `A_u^n` (`Aun`) is valued in `ℕ`, defined for every `n : ℕ`, `u : ℤ`, `a : ℤ → ℕ`; on the
  paper's domain it is the paper's sum, literally.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset

variable {A : Type*} [CommRing A]

/-! ### `def:ring_define`: `f_A` -/

/-- `f_A` (`syracuse.tex:55`) in the reading of l.46–48: `x/2` on `2A`, `3x+1` off `2A`. -/
noncomputable def f (x : A) : A :=
  open scoped Classical in if (2 : A) ∣ x then divPow2 x 1 else 3 * x + 1

theorem two_mul_f_of_two_dvd {x : A} (hx : (2 : A) ∣ x) : 2 * f x = x := by
  have h' : (2 : A) ^ 1 ∣ x := by rwa [pow_one]
  have := pow_mul_divPow2 h'
  rw [pow_one] at this
  rw [f, if_pos hx]
  exact this

theorem f_of_not_two_dvd {x : A} (hx : ¬ (2 : A) ∣ x) : f x = 3 * x + 1 := by
  rw [f, if_neg hx]

/-- `f x` is the unique half of an even `x` (given `2 ≠ 0`). -/
theorem f_eq_of_two_mul [IsDomain A] (h2 : (2 : A) ≠ 0) {x y : A} (h : 2 * y = x) : f x = y := by
  have hx : (2 : A) ∣ x := ⟨y, h.symm⟩
  rw [f, if_pos hx]
  exact divPow2_unique h2 (n := 1) (by rw [pow_one]; exact h)

/-- **Finding 1.** The printed `f_A` (`3x+1` on `2A`, `x/2` off `2A`) does not exist. -/
theorem printed_f_not_definable [IsZ2Ring A] :
    ¬ ∃ g : A → A, ∀ x : A, ((2 : A) ∣ x → g x = 3 * x + 1) ∧ (¬ (2 : A) ∣ x → 2 * g x = x) := by
  rintro ⟨g, hg⟩
  have h := (hg 1).2 IsZ2Ring.not_two_dvd_one
  exact IsZ2Ring.not_two_dvd_one ⟨g 1, h.symm⟩

/-! ### `def:ring_define`: `T_A` -/

/-- `T_A(x) = (3x+1)/2^{ν₂(3x+1)}` (`syracuse.tex:55`), for every `x ∈ A` (junk at `3x+1 = 0`). -/
noncomputable def T (x : A) : A := divPow2 (3 * x + 1) (v2 (3 * x + 1))

/-- The defining identity, unconditionally (with the junk values at `3x+1 = 0`). -/
theorem pow_v2_mul_T (x : A) : (2 : A) ^ v2 (3 * x + 1) * T x = 3 * x + 1 := by
  exact pow_mul_divPow2 (pow_v2_dvd _)

/-- `3x+1 = 0` forces `3 ∈ Aˣ`: when `3` is not a unit, `T` is the paper's map everywhere. -/
theorem three_mul_add_one_ne_zero (h3 : ¬ IsUnit (3 : A)) (x : A) : 3 * x + 1 ≠ 0 := by
  intro h
  exact h3 (IsUnit.of_mul_eq_one (a := (3 : A)) (-x) (by linear_combination -h))

theorem nu2_three_mul_add_one [IsZ2Ring A] {x : A} (hx : 3 * x + 1 ≠ 0) :
    nu2 (3 * x + 1) = (v2 (3 * x + 1) : ℕ∞) := by
  exact (IsZ2Ring.v2_eq_nu2 hx).symm

/-- `T_A` maps into `2A + 1` where it is defined. -/
theorem T_odd [IsZ2Ring A] {x : A} (hx : 3 * x + 1 ≠ 0) : Odd (T x) := by
  rw [IsZ2Ring.odd_iff_not_two_dvd]
  intro h
  apply IsZ2Ring.not_pow_succ_v2_dvd hx
  have hd : (2 : A) ^ (v2 (3 * x + 1) + 1) ∣ (2 : A) ^ v2 (3 * x + 1) * T x := by
    rw [pow_succ]
    exact mul_dvd_mul_left _ h
  rwa [pow_v2_mul_T x] at hd

/-- Where defined, `T x` is the only odd `t` with `2ᵏ t = 3x+1`, and `k = ν₂(3x+1)`. -/
theorem T_unique [IsZ2Ring A] (h2 : (2 : A) ≠ 0) {x t : A} {k : ℕ} (ht : Odd t)
    (h : (2 : A) ^ k * t = 3 * x + 1) : k = v2 (3 * x + 1) ∧ T x = t := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact not_two_dvd_of_odd IsZ2Ring.not_two_dvd_one ht (dvd_zero 2)
  have hx : 3 * x + 1 ≠ 0 := by
    rw [← h]
    exact mul_ne_zero (pow_ne_zero _ h2) ht0
  obtain ⟨e1, e2⟩ := pow_two_mul_odd_inj h2 IsZ2Ring.not_two_dvd_one (T_odd hx) ht
    ((pow_v2_mul_T x).trans h.symm)
  exact ⟨e1.symm, e2⟩

/-- **Finding 2.** If `3 ∈ Aˣ`, `x₀ = -3⁻¹` is odd, `3x₀+1 = 0` has `ν₂ = ⊤` (no greatest
`n` with `3x₀+1 ∈ 2ⁿA`), and, when `2 ≠ 0`, no odd `t` and no `k ∈ ℕ` satisfy `2ᵏ t = 3x₀ + 1`:
`T_A(x₀)` is undefined. -/
theorem T_undefined_of_isUnit_three [IsZ2Ring A] (u : Aˣ) (hu : (u : A) = 3) :
    Odd (-(↑u⁻¹ : A)) ∧ 3 * (-(↑u⁻¹ : A)) + 1 = 0 ∧ nu2 (3 * (-(↑u⁻¹ : A)) + 1) = ⊤ ∧
      (¬ ∃ n : ℕ, IsGreatest {m : ℕ | 3 * (-(↑u⁻¹ : A)) + 1 ∈ Ideal.span {(2 : A) ^ m}} n) ∧
      ((2 : A) ≠ 0 → ∀ (t : A) (k : ℕ), Odd t → (2 : A) ^ k * t ≠ 3 * (-(↑u⁻¹ : A)) + 1) := by
  have h0 : 3 * (-(↑u⁻¹ : A)) + 1 = 0 := by
    rw [← hu, mul_neg, Units.mul_inv, neg_add_cancel]
  refine ⟨?_, h0, ?_, ?_, ?_⟩
  · rw [IsZ2Ring.odd_iff_not_two_dvd]
    intro h
    apply IsZ2Ring.not_two_dvd_one (A := A)
    have h1 : (1 : A) = -(3 * (-(↑u⁻¹ : A))) := by linear_combination h0
    rw [h1]
    exact (dvd_mul_of_dvd_right h 3).neg_right
  · rw [h0]
    exact nu2_zero
  · rintro ⟨n, hn⟩
    have := hn.2 (show n + 1 ∈ {m : ℕ | 3 * (-(↑u⁻¹ : A)) + 1 ∈ Ideal.span {(2 : A) ^ m}} by
      rw [Set.mem_setOf_eq, h0]
      exact Submodule.zero_mem _)
    omega
  · intro h2 t k ht h
    rw [h0] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exact h2 (pow_eq_zero_iff'.1 h').1
    · subst h'
      exact not_two_dvd_of_odd IsZ2Ring.not_two_dvd_one ht (dvd_zero 2)

/-- **Finding 2 in `ℤ₂`.** -/
theorem T_undefined_padicInt : ∃ x₀ : ℤ_[2], Odd x₀ ∧ nu2 (3 * x₀ + 1) = ⊤ ∧
    ∀ (t : ℤ_[2]) (k : ℕ), Odd t → (2 : ℤ_[2]) ^ k * t ≠ 3 * x₀ + 1 := by
  obtain ⟨hodd, -, htop, -, hno⟩ := T_undefined_of_isUnit_three isUnit_three_padicInt.unit rfl
  exact ⟨_, hodd, htop, hno two_ne_zero⟩

/-! ### `def:ring_define_2`: `a_n`, `p_n` -/

/-- `a_n(x) = ν₂(3 Tⁿ(x) + 1)` (`syracuse.tex:62`). -/
noncomputable def a (n : ℕ) (x : A) : ℕ := v2 (3 * T^[n] x + 1)

/-- `p_n(x) = ∑_{k<n} a_k(x)` (`syracuse.tex:63`). -/
noncomputable def p (n : ℕ) (x : A) : ℕ := ∑ k ∈ range n, a k x

/-- Where the paper's `a_n(x)` is defined, it is `a n x`. -/
theorem a_eq_nu2 [IsZ2Ring A] {n : ℕ} {x : A} (h : 3 * T^[n] x + 1 ≠ 0) :
    (a n x : ℕ∞) = nu2 (3 * T^[n] x + 1) := by
  exact IsZ2Ring.v2_eq_nu2 h

theorem a_succ (n : ℕ) (x : A) : a (n + 1) x = a n (T x) := by
  rw [a, a, Function.iterate_succ_apply]

theorem p_zero (x : A) : p 0 x = 0 := by
  simp [p]

theorem p_succ (n : ℕ) (x : A) : p (n + 1) x = a 0 x + p n (T x) := by
  rw [p, Finset.sum_range_succ', p, add_comm]
  simp only [a_succ]

theorem p_succ' (n : ℕ) (x : A) : p (n + 1) x = p n x + a n x := by
  rw [p, Finset.sum_range_succ, p]

/-- `a_n(x) ≥ 1` when `Tⁿ(x)` is odd. -/
theorem one_le_a [IsZ2Ring A] {n : ℕ} {x : A} (h : Odd (T^[n] x)) : 1 ≤ a n x := by
  have hy : (2 : A) ∣ 3 * T^[n] x + 1 :=
    IsZ2Ring.two_dvd_three_mul_add_one (IsZ2Ring.odd_iff_not_two_dvd.1 h)
  by_cases h0 : 3 * T^[n] x + 1 = 0
  · simp [a, v2, h0]
  · exact IsZ2Ring.le_v2_of_pow_dvd h0 (by rwa [pow_one])

/-- The orbit of an odd `x` stays odd as long as it avoids `-1/3`. -/
theorem T_iterate_odd [IsZ2Ring A] {x : A} (hx : Odd x) {n : ℕ}
    (h : ∀ k < n, 3 * T^[k] x + 1 ≠ 0) : Odd (T^[n] x) := by
  rcases n with _ | n
  · exact hx
  · rw [Function.iterate_succ_apply']
    exact T_odd (h n (Nat.lt_succ_self n))

/-! ### `lem:base` -/

/-- `lem:base` (`syracuse.tex:67`), for the total maps `T`, `a`, `p`:
`2^{p_n(x)} Tⁿ(x) - 3ⁿ x = ∑_{k<n} 2^{p_k(x)} 3^{n-1-k}` (the paper's terms on good orbits:
`base_of_orbit`). -/
theorem base (x : A) (n : ℕ) :
    (2 : A) ^ p n x * T^[n] x - 3 ^ n * x = ∑ k ∈ range n, (2 : A) ^ p k x * 3 ^ (n - 1 - k) := by
  induction n generalizing x with
  | zero => simp [p]
  | succ n ih =>
    have hT := pow_v2_mul_T x
    have ha0 : a 0 x = v2 (3 * x + 1) := rfl
    have hsum : ∑ k ∈ range (n + 1), (2 : A) ^ p k x * 3 ^ (n + 1 - 1 - k)
        = 2 ^ a 0 x * ∑ k ∈ range n, (2 : A) ^ p k (T x) * 3 ^ (n - 1 - k) + 3 ^ n := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro k _
        rw [p_succ, pow_add]
        have hk : n + 1 - 1 - (k + 1) = n - 1 - k := by omega
        rw [hk]
        ring
      · simp [p_zero]
    rw [hsum, ← ih (T x), p_succ, pow_add, Function.iterate_succ_apply, ha0]
    linear_combination (3 : A) ^ n * hT

/-- `lem:base` with every term the paper's: `3 ∉ Aˣ` (e.g. `A = ℤ`), all `x ∈ A`, all `n`. -/
theorem base_of_not_isUnit_three [IsZ2Ring A] (h3 : ¬ IsUnit (3 : A)) (x : A) (n : ℕ) :
    (∀ k, (a k x : ℕ∞) = nu2 (3 * T^[k] x + 1)) ∧
      (2 : A) ^ p n x * T^[n] x - 3 ^ n * x = ∑ k ∈ range n, (2 : A) ^ p k x * 3 ^ (n - 1 - k) := by
  exact ⟨fun k => a_eq_nu2 (three_mul_add_one_ne_zero h3 _), base x n⟩

/-- `lem:base` in the paper's own terms: on an orbit that avoids `-1/3` for `n` steps, every `a_k`
(`k < n`) is the paper's `ν₂(3Tᵏx+1)`, every `T^{k+1}x` is odd (in `2A+1`), and the identity holds.
Every `x ∈ ℤ` qualifies (`three_mul_add_one_ne_zero`). -/
theorem base_of_orbit [IsZ2Ring A] {x : A} {n : ℕ} (h : ∀ k < n, 3 * T^[k] x + 1 ≠ 0) :
    (∀ k < n, (a k x : ℕ∞) = nu2 (3 * T^[k] x + 1) ∧ Odd (T^[k + 1] x)) ∧
      (2 : A) ^ p n x * T^[n] x - 3 ^ n * x = ∑ k ∈ range n, (2 : A) ^ p k x * 3 ^ (n - 1 - k) := by
  refine ⟨fun k hk => ⟨a_eq_nu2 (h k hk), ?_⟩, base x n⟩
  rw [Function.iterate_succ_apply']
  exact T_odd (h k hk)

/-- `lem:base` at `x₀ = -1/3` in `ℤ₂`, refuted: no odd value of `T(x₀)` and no `p_1(x₀) ∈ ℕ` satisfy the
`n = 1` instance of the printed identity. -/
theorem base_printed_fails_padicInt : ∃ x₀ : ℤ_[2], Odd x₀ ∧
    ∀ (t : ℤ_[2]) (k : ℕ), Odd t →
      (2 : ℤ_[2]) ^ k * t - 3 ^ 1 * x₀ ≠ ∑ j ∈ range 1, (2 : ℤ_[2]) ^ p j x₀ * 3 ^ (1 - 1 - j) := by
  obtain ⟨x₀, hodd, -, hno⟩ := T_undefined_padicInt
  refine ⟨x₀, hodd, fun t k ht h => hno t k ht ?_⟩
  simp [p_zero] at h
  linear_combination h

/-! ### `def:define_n__n_`: `A_u^n` -/

/-- **`def:define_n__n_`** (`syracuse.tex:80`): `A_u^n(a) = ∑_{k=0}^{n-1} 3ᵏ ∏_{i=0}^{n-1-k} 2^{a_{u+i}}`. -/
def Aun (n : ℕ) (u : ℤ) (a : ℤ → ℕ) : ℕ :=
  ∑ k ∈ range n, 3 ^ k * ∏ i ∈ range (n - k), 2 ^ a (u + i)

/-- Sanity check: `A_u^1(a) = 2^{a_u}`. -/
theorem Aun_one (u : ℤ) (a : ℤ → ℕ) : Aun 1 u a = 2 ^ a u := by
  simp [Aun]

/-- Sanity check: `A_u^2(a) = 2^{a_u} 2^{a_{u+1}} + 3 · 2^{a_u}`. -/
theorem Aun_two (u : ℤ) (a : ℤ → ℕ) : Aun 2 u a = 2 ^ a u * 2 ^ a (u + 1) + 3 * 2 ^ a u := by
  simp [Aun, Finset.sum_range_succ, Finset.prod_range_succ]

/-! ### `lem:ring_maps_rhs_n_` -/

/-- The domain `{p ∈ ℕⁿ | p₀ = 0 ∧ p ↗↗}` of `RHS_n` (`syracuse.tex:85`). -/
def RHSDomain (n : ℕ) : Set (Fin n → ℕ) :=
  {q | (∀ h : 0 < n, q ⟨0, h⟩ = 0) ∧ StrictMono q}

/-- `RHS_n(p) = ∑_{k=0}^{n-1} 2^{p_k} 3^{n-1-k} ∈ A` (`syracuse.tex:85`). -/
def RHS (A : Type*) [CommRing A] (n : ℕ) (q : Fin n → ℕ) : A :=
  ∑ k : Fin n, (2 : A) ^ q k * 3 ^ (n - 1 - (k : ℕ))

/-- Peeling off the first term: `RHS_{n+1}(p) = 2^{p₀} 3ⁿ + RHS_n(p₁, …, pₙ)`. -/
theorem rhs_succ (n : ℕ) (q : Fin (n + 1) → ℕ) :
    RHS A (n + 1) q = (2 : A) ^ q 0 * 3 ^ n + RHS A n (Fin.tail q) := by
  have hk : ∀ k : Fin n, n - ((Fin.succ k : Fin (n + 1)) : ℕ) = n - 1 - (k : ℕ) := by
    intro k
    rw [Fin.val_succ]
    omega
  rw [RHS, Fin.sum_univ_succ, RHS]
  simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, hk]
  rfl

/-- For strictly increasing `p`, `RHS_{n+1}(p) = 2^{p₀} w` with `w ∈ 2A + 1`. -/
theorem rhs_succ_eq_pow_mul_odd {n : ℕ} {q : Fin (n + 1) → ℕ} (hq : StrictMono q) :
    ∃ w : A, Odd w ∧ RHS A (n + 1) q = (2 : A) ^ q 0 * w := by
  refine ⟨3 ^ n + ∑ k : Fin n, (2 : A) ^ (q k.succ - q 0) * 3 ^ (n - 1 - (k : ℕ)), ?_, ?_⟩
  · refine Odd.add_even (Odd.pow ⟨1, by norm_num⟩) (even_iff_two_dvd.2 ?_)
    refine Finset.dvd_sum (fun k _ => ?_)
    have hlt : q 0 < q k.succ := hq (Fin.succ_pos k)
    refine dvd_mul_of_dvd_left (dvd_pow_self 2 ?_) _
    omega
  · rw [rhs_succ, RHS, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have hle : q 0 ≤ q k.succ := (hq (Fin.succ_pos k)).le
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    rfl

/-- The strongest form: injective on all strictly increasing `p`, in any domain with `2 ≠ 0` and
`1 ∉ 2A`. -/
theorem rhs_injOn_strictMono [IsDomain A] (h2 : (2 : A) ≠ 0) (h1 : ¬ (2 : A) ∣ 1) (n : ℕ) :
    Set.InjOn (RHS A n) {q | StrictMono q} := by
  induction n with
  | zero =>
    intro q _ r _ _
    funext k
    exact k.elim0
  | succ n ih =>
    intro q hq r hr hqr
    obtain ⟨w, hw, hqw⟩ := rhs_succ_eq_pow_mul_odd (A := A) hq
    obtain ⟨w', hw', hrw⟩ := rhs_succ_eq_pow_mul_odd (A := A) hr
    have h0 : q 0 = r 0 := (pow_two_mul_odd_inj h2 h1 hw hw' (hqw.symm.trans (hqr.trans hrw))).1
    have htail : RHS A n (Fin.tail q) = RHS A n (Fin.tail r) := by
      have h' := hqr
      rw [rhs_succ, rhs_succ, h0] at h'
      exact add_left_cancel h'
    have htq : Fin.tail q ∈ {q : Fin n → ℕ | StrictMono q} := hq.comp Fin.strictMono_succ
    have htr : Fin.tail r ∈ {q : Fin n → ℕ | StrictMono q} := hr.comp Fin.strictMono_succ
    have ht := ih htq htr htail
    funext k
    refine Fin.cases h0 (fun j => ?_) k
    exact congrFun ht j

/-- `lem:ring_maps_rhs_n_` under `2 ≠ 0` (claimed at l.50, false only for `A ≃ ℤ/2ℤ`). -/
theorem ring_maps_rhs [IsZ2Ring A] (h2 : (2 : A) ≠ 0) (n : ℕ) : Set.InjOn (RHS A n) (RHSDomain n) := by
  exact (rhs_injOn_strictMono h2 IsZ2Ring.not_two_dvd_one n).mono (fun q hq => hq.2)

/-- **Finding 3.** In the ℤ/2ℤ-ring `ℤ/2ℤ`, `RHS₂` is not injective. -/
theorem ring_maps_rhs_printed_false : ¬ Set.InjOn (RHS (ZMod 2) 2) (RHSDomain 2) := by
  intro hinj
  have hq : (![0, 1] : Fin 2 → ℕ) ∈ RHSDomain 2 := ⟨fun _ => rfl, by decide⟩
  have hr : (![0, 2] : Fin 2 → ℕ) ∈ RHSDomain 2 := ⟨fun _ => rfl, by decide⟩
  have heq : RHS (ZMod 2) 2 ![0, 1] = RHS (ZMod 2) 2 ![0, 2] := by decide
  have := congrFun (hinj hq hr heq) 1
  simp at this

/-- **Finding 3, every `n ≥ 2`.** In `ℤ/2ℤ`, `RHS_n` is not injective on its domain (it is in fact
constant, `= 3^{n-1} = 1`: every term with `k ≥ 1` vanishes; only the non-injectivity is proved). -/
theorem rhs_zmod2_not_injOn {n : ℕ} (hn : 2 ≤ n) : ¬ Set.InjOn (RHS (ZMod 2) n) (RHSDomain n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  intro hinj
  have hzero : ∀ (k : ℕ) (s : Fin k → ℕ), (∀ j, 1 ≤ s j) → RHS (ZMod 2) k s = 0 := by
    intro k s hs
    apply Finset.sum_eq_zero
    intro j _
    have hj := hs j
    rw [show (2 : ZMod 2) = 0 from rfl, zero_pow (by omega), zero_mul]
  let q : Fin (m + 2) → ℕ := fun k => (k : ℕ)
  let r : Fin (m + 2) → ℕ := fun k => if (k : ℕ) = 0 then 0 else (k : ℕ) + 1
  have hq : q ∈ RHSDomain (m + 2) := ⟨fun _ => rfl, fun i j hij => hij⟩
  have hr : r ∈ RHSDomain (m + 2) := by
    refine ⟨fun _ => rfl, fun i j hij => ?_⟩
    have hij' : (i : ℕ) < j := hij
    simp only [r]
    split_ifs <;> omega
  have heq : RHS (ZMod 2) (m + 2) q = RHS (ZMod 2) (m + 2) r := by
    have htq : ∀ j : Fin (m + 1), 1 ≤ Fin.tail q j := fun j => by simp [Fin.tail, q]
    have htr : ∀ j : Fin (m + 1), 1 ≤ Fin.tail r j := fun j => by simp [Fin.tail, r]
    rw [rhs_succ (A := ZMod 2) (m + 1) q, rhs_succ (A := ZMod 2) (m + 1) r,
      hzero _ _ htq, hzero _ _ htr]
    simp [q, r]
  have h1 := congrFun (hinj hq hr heq) 1
  simp [q, r] at h1

/-- **Finding 3, as printed.** The statement of `lem:ring_maps_rhs_n_` — for every ℤ/2ℤ-ring `A` and
every `n`, `RHS_n` is injective on its domain — is false. -/
theorem ring_maps_rhs_printed_statement_false :
    ¬ ∀ (B : Type) [CommRing B] [IsZ2Ring B] (n : ℕ), Set.InjOn (RHS B n) (RHSDomain n) :=
  fun h => ring_maps_rhs_printed_false (h (ZMod 2) 2)

/-- **Integrality is needed (minor finding of the audit).** In `ZMod 6` — noetherian, with
`A/2A ≃ ℤ/2ℤ` and `2 ≠ 0`, but not integral — `RHS₂(0,1) = 5 = 11 = RHS₂(0,3)`: `RHS₂` is not
injective, so `lem:ring_maps_rhs_n_` also fails under the printed definition (l.52) without the
integrality of l.50. -/
theorem rhs_zmod6_not_injOn :
    IsNoetherianRing (ZMod 6) ∧ Nonempty ((ZMod 6 ⧸ Ideal.span {(2 : ZMod 6)}) ≃+* ZMod 2) ∧
      (2 : ZMod 6) ≠ 0 ∧ ¬ Set.InjOn (RHS (ZMod 6) 2) (RHSDomain 2) := by
  obtain ⟨hn, hq, -, -, h2, -⟩ := zmod6_witness
  refine ⟨hn, hq, h2, fun hinj => ?_⟩
  have hp : (![0, 1] : Fin 2 → ℕ) ∈ RHSDomain 2 := ⟨fun _ => rfl, by decide⟩
  have hr : (![0, 3] : Fin 2 → ℕ) ∈ RHSDomain 2 := ⟨fun _ => rfl, by decide⟩
  have heq : RHS (ZMod 6) 2 ![0, 1] = RHS (ZMod 6) 2 ![0, 3] := by decide
  have := congrFun (hinj hp hr heq) 1
  simp at this

end Syracuse
