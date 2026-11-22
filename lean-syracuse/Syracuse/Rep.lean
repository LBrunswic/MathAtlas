import Syracuse.Base
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Nat.Periodic

/-!
# Syracuse § 1: the 2-adic representation `x ↦ (p_n(x))` and two corollaries on periodic orbits

Every label is marked under DEC-183: `theo:rep` and `cor:ring_periodic_minimal_period` in
corrected form, `cor:ring_following_equivalent_enumerate` as printed in the readings of OQ-42
(SCOPE).

* **`theo:rep`** — `syracuse.tex:88` (l.88–91, proof l.92–95) — marked in corrected form (DEC-183,
  OQ-42 (d): the domain is `RepDomain`, the odd points whose orbit avoids `−1/3`) on
  `Syracuse.theo_rep`, which is the printed bijection onto the strictly increasing sequences from `0`,
  with the printed inverse, on `RepDomain`; the image of the printed `φ⁻¹` is exactly `RepDomain`
  (`repInv_image`). Stated in `ℤ₂`, which is `A₂` for every ℤ/2ℤ-ring with `2 ≠ 0` (OQ-42 (b);
  `completion_ringEquiv`). **False as printed** on `2ℤ₂ + 1` (`rep_printed_false`,
  `neg_inv3_not_mem_image`, `neg_third_preimage`): Finding 1.
* **`cor:ring_following_equivalent_enumerate`** — `syracuse.tex:96` (l.96–101, proof l.102–106) —
  marked under DEC-183 (OQ-42 (a): `A` integral, carried in `IsZ2Ring`, which l.52's definition
  omits; (d): the total `T`, `a`) on `Syracuse.periodic_a_iff_periodic_T`, for every `x ∈ A` and
  `n`, with no `2 ≠ 0`; the other readings of « periodic of period `n` » are
  `eventually_periodic_a_iff_periodic_T` and `minimal_period_a_iff_minimal_period_T`.
* **`cor:ring_periodic_minimal_period`** — `syracuse.tex:107` (l.107–109) — marked in corrected
  form (DEC-183, OQ-53: `i ≠ j` added; OQ-43: the printed `A_u^n`) on `Syracuse.Aun_sub_ne_zero`, in
  every ℤ/2ℤ-ring (`AunAlt_sub_ne_zero` for the other reading of OQ-43; not vacuous:
  `cycle_neg_five`). **False as printed** at `i = j` on every cycle, e.g. `(1)` in `ℤ`
  (`cor_ring_periodic_minimal_period_printed_false`): Finding 3.

> **theo:rep.** The map $$\fonction{\phi}{2A_2+1}{\{p\in \NN^\NN~|~ p_0=0 ~\wedge~ (p_n)
> \nearrow\nearrow\}}{x}{(p_n(x))_{n\in \NN}} $$ is bijective and its inverse is:
> $$\fonction{\phi^{-1}}{\{p\in \NN^\NN~|~ p_0=0 ~\wedge~ (p_n) \nearrow\nearrow\}}{2A_2+1}{p}
> { -\frac{1}{3}\sum_{n = 0}^{\infty}\frac{2^{p_n}}{3^{n}}}.$$

> **cor:ring_following_equivalent_enumerate.** Let $A$ be a $\ZZ/2\ZZ$-ring and  $x\in A$. The
> following are equivalent : (i) $\left(a_n(x)\right)_{n\in \NN}$ is periodic of period $n$;
> (ii) $\left(T^n(x)\right)_{n\in \NN}$ is periodic of period $n$.

> **cor:ring_periodic_minimal_period.** Let $A$ be a $\ZZ/2\ZZ$-ring and  $x\in A$ such that
> $\left(T^k(x)\right)_{k\in\NN}$ is $n$-periodic for some $n$.  If $n$ the minimal period then :
> $$\forall i,j\in \lsem 1,n\rsem,\quad A_i^n(a(x))-A_j^n(a(x)) \neq 0$$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `A₂`, the 2-completion, `≅ ℤ₂` (l.52) (`theo:rep`) | a reading: `ℤ_[2]` itself; `A → ℤ₂` is T-syr-completion's |
| `x ∈ 2A₂+1` (`theo:rep`) | ⚠ strengthened: `x` odd, `3Tᵏx+1 ≠ 0` for all `k` (`RepDomain`): Finding 1 |
| `p₀ = 0`, `(pₙ) ↗↗` (`theo:rep`) | ✓ carried (`RepSeq`; `↗↗` read as strictly increasing) |
| `A` a ℤ/2ℤ-ring, `x ∈ A` (both corollaries) | ⚠ strengthened via `IsZ2Ring`: a domain (OQ-42 (a)); no `2 ≠ 0` (only `cycle_avoids_neg_third` uses it) |
| "periodic of period `n`" (first corollary) | every reading: a period, eventually a period, the least period |
| `n` the minimal period (second corollary) | ✓ carried: `0 < n`, `Tⁿx = x`, no smaller positive period |
| `i, j ∈ ⟦1, n⟧` (second corollary) | ⚠ strengthened: `i ≠ j` added: Finding 3 |
| `a(x) ∈ (ℕ*)^ℤ` (second corollary) | ⚠ weakened: any `α : ℤ → ℕ` with `α k = a_k(x)` for `k ∈ ℕ` |

## SCOPE (disclosed)

* **Finding 1 (`theo:rep`, l.88–90): false on the backward orbit of `−1/3`.** `−1/3` and every
  `−(2ᵏ+3)/9`, `k ≥ 1`, lie in `2ℤ₂+1` but outside the image of the printed `φ⁻¹`
  (`neg_inv3_not_mem_image`, `neg_third_preimage`), so no map `φ` from `2ℤ₂+1` to the strictly
  increasing sequences from `0` has the printed `φ⁻¹` as a left inverse, whatever its values where
  the paper's `p_n` are undefined (`rep_printed_false`). True form (`theo_rep`): `φ` is a bijection
  from `RepDomain` (odd, orbit avoiding `−1/3`) onto `RepSeq` with the printed inverse, and the
  image of `φ⁻¹` is exactly `RepDomain` (`repInv_image`).
* **Finding 2 (`theo:rep`, proof l.92–95): only `φ⁻¹ ∘ φ = id` is argued.** Surjectivity is not.
  Here `S(q) = 1 + 2^{q₁}/3 · S(q')`, `q'ₙ = q_{n+1} − q₁` (`repSeries_eq`), gives
  `T(φ⁻¹q) = φ⁻¹q'`, `a₀(φ⁻¹q) = q₁` (`T_repInv`), hence `φ(φ⁻¹q) = q` (`rep_repInv`).
  Injectivity holds in every ℤ/2ℤ-ring, without `A₂`, by Krull (`eq_of_p_eq`, `rep_injOn`).
* **Finding 3 (`cor:ring_periodic_minimal_period`, l.108): false at `i = j`** (the difference is
  `0`) on every cycle, e.g. `(1)` in `ℤ` (`cor_ring_periodic_minimal_period_printed_false`). For
  `i ≠ j` it holds in every ℤ/2ℤ-ring for both readings of OQ-43 (`Aun_sub_ne_zero`,
  `AunAlt_sub_ne_zero`): on a cycle `A_u^n = (2^{p_n} − 3ⁿ)(3x_u + 1)` as printed and
  `(2^{p_n} − 3ⁿ) x_u` with the product to `n−2−k` (`Aun_cast_of_cycle`). No printed proof.
* The first corollary (`periodic_a_iff_periodic_T`) holds for every `x ∈ A`, ring and `n`, for
  the total `T`, `a` (junk at `−1/3`, OQ-42 (d)). If `2 ≠ 0`, either side with `n ≥ 1` makes `x` odd
  with orbit avoiding `−1/3` (`cycle_avoids_neg_third`), where `T`, `a` are the paper's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset

section General
variable {A : Type*} [CommRing A]

/-- `a_k(Tⁿx) = a_{k+n}(x)`. -/
theorem a_iterate (k n : ℕ) (x : A) : a k (T^[n] x) = a (k + n) x := by
  simp only [a, ← Function.iterate_add_apply]

/-- `p_{n+k}(x) = p_n(x) + p_k(Tⁿx)`. -/
theorem p_add (n k : ℕ) (x : A) : p (n + k) x = p n x + p k (T^[n] x) := by
  rw [p, Finset.sum_range_add, p, p]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [a_iterate, add_comm]

/-- Two points with the same `p_0, …, p_n` satisfy `3ⁿ (x − y) = 2^{p_n} (Tⁿx − Tⁿy)`: `lem:base`
twice. -/
theorem three_pow_mul_sub_eq (x y : A) (n : ℕ) (h : ∀ k ≤ n, p k x = p k y) :
    (3 : A) ^ n * (x - y) = 2 ^ p n x * (T^[n] x - T^[n] y) := by
  have hx := base x n
  have hy := base y n
  have hs : ∑ k ∈ range n, (2 : A) ^ p k x * 3 ^ (n - 1 - k) =
      ∑ k ∈ range n, (2 : A) ^ p k y * 3 ^ (n - 1 - k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [h k (by simp at hk; omega)]
  rw [← h n le_rfl] at hy
  linear_combination hy - hx - hs

end General

/-! ### Injectivity of `x ↦ (p_n(x))` in a ℤ/2ℤ-ring -/

section Z2Ring
variable {A : Type*} [CommRing A] [IsZ2Ring A]

omit [IsZ2Ring A] in
/-- `3 ∈ 2A + 1`. -/
theorem odd_three : Odd (3 : A) := ⟨1, by norm_num⟩

/-- `3 ≠ 0` in a ℤ/2ℤ-ring (`ℤ/2ℤ` included). -/
theorem three_ne_zero_of_isZ2Ring : (3 : A) ≠ 0 := by
  intro h
  exact not_two_dvd_of_odd IsZ2Ring.not_two_dvd_one odd_three (h ▸ dvd_zero 2)

/-- `2` is prime in a ℤ/2ℤ-ring with `2 ≠ 0`. -/
theorem prime_two_of_ne_zero (h2 : (2 : A) ≠ 0) : Prime (2 : A) := by
  refine ⟨h2, IsZ2Ring.not_isUnit_two, fun x y hxy => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  have hx := IsZ2Ring.odd_iff_not_two_dvd.2 hcon.1
  have hy := IsZ2Ring.odd_iff_not_two_dvd.2 hcon.2
  exact IsZ2Ring.odd_iff_not_two_dvd.1 (hx.mul hy) hxy

/-- `2ʲ ∣ 3ᵐ z → 2ʲ ∣ z` in every ℤ/2ℤ-ring (`ℤ/2ℤ` included). -/
theorem two_pow_dvd_of_dvd_three_pow_mul {j m : ℕ} {z : A} (h : (2 : A) ^ j ∣ 3 ^ m * z) :
    (2 : A) ^ j ∣ z := by
  by_cases h2 : (2 : A) = 0
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [h2, zero_pow hj.ne', zero_dvd_iff] at h ⊢
      rcases mul_eq_zero.1 h with h3 | hz
      · exact absurd (pow_eq_zero_iff'.1 h3).1 three_ne_zero_of_isZ2Ring
      · exact hz
  · exact (prime_two_of_ne_zero h2).pow_dvd_of_dvd_mul_left j
      (IsZ2Ring.odd_iff_not_two_dvd.1 (odd_three.pow)) h

/-- **Injectivity of `x ↦ (p_n(x))`** in every ℤ/2ℤ-ring: two points with the same `p`-sequence,
unbounded, are equal. Krull (l.51) replaces the convergence in `A₂` of the printed proof. -/
theorem eq_of_p_eq {x y : A} (h : ∀ k, p k x = p k y) (hunb : ∀ N, ∃ k, N ≤ p k x) : x = y := by
  by_contra hne
  have hz : x - y ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨k, hk⟩ := hunb (v2 (x - y) + 1)
  apply IsZ2Ring.not_pow_succ_v2_dvd hz
  have h1 : (2 : A) ^ p k x ∣ 3 ^ k * (x - y) := by
    rw [three_pow_mul_sub_eq x y k (fun j _ => h j)]
    exact dvd_mul_right _ _
  exact (pow_dvd_pow 2 hk).trans (two_pow_dvd_of_dvd_three_pow_mul h1)

/-- On an odd orbit avoiding `−1/3`, `n ≤ p_n(x)`. -/
theorem le_p_of_orbit {x : A} (hx : Odd x) (h : ∀ k, 3 * T^[k] x + 1 ≠ 0) (n : ℕ) : n ≤ p n x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [p_succ']
    have := one_le_a (T_iterate_odd hx (n := n) (fun k _ => h k))
    omega

/-! ### `cor:ring_following_equivalent_enumerate` -/

/-- `a₀(x) = 0` (so `x ∈ 2A`, `T x = 3x + 1` odd) forces `a₁(x) ≥ 1`. -/
theorem one_le_a_one_of_a_zero {x : A} (h : a 0 x = 0) : 1 ≤ a 1 x := by
  simp only [a, Function.iterate_zero, id_eq] at h
  rw [v2, multiplicity_eq_zero] at h
  have hx : (2 : A) ∣ x := by
    rcases IsZ2Ring.two_dvd_or_odd x with hx | hx
    · exact hx
    · exact absurd (IsZ2Ring.two_dvd_three_mul_add_one (IsZ2Ring.odd_iff_not_two_dvd.1 hx)) h
  have hT : T x = 3 * x + 1 := by
    have h0 : v2 (3 * x + 1) = 0 := by rw [v2, multiplicity_eq_zero]; exact h
    have := pow_v2_mul_T x
    rwa [h0, pow_zero, one_mul] at this
  apply one_le_a
  rw [Function.iterate_one, hT]
  obtain ⟨c, rfl⟩ := hx
  exact ⟨3 * c, by ring⟩

/-- If `(a_k(x))_k` has period `n ≥ 1`, then `p_n(x) ≥ 1`. -/
theorem one_le_p_of_periodic {x : A} {n : ℕ} (hn : 0 < n) (h : ∀ k, a (k + n) x = a k x) :
    1 ≤ p n x := by
  by_contra hlt
  have h0 : p n x = 0 := by omega
  rw [p, Finset.sum_eq_zero_iff] at h0
  have ha0 : a 0 x = 0 := h0 0 (Finset.mem_range.2 hn)
  have hper : Function.Periodic (fun k => a k x) n := h
  have ha1 : a 1 x = 0 := by
    rw [← hper.map_mod_nat 1]
    exact h0 _ (Finset.mem_range.2 (Nat.mod_lt _ hn))
  have := one_le_a_one_of_a_zero ha0
  omega

omit [IsZ2Ring A] in
/-- If `(a_k(x))_k` has period `n`, then `p_{mn}(x) = m p_n(x)`. -/
theorem p_mul_of_periodic {x : A} {n : ℕ} (h : ∀ k, a (k + n) x = a k x) (m : ℕ) :
    p (m * n) x = m * p n x := by
  have hpT : ∀ k, p k (T^[n] x) = p k x := by
    intro k
    simp only [p]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [a_iterate, h]
  induction m with
  | zero => simp [p_zero]
  | succ m ih =>
    rw [show (m + 1) * n = n + m * n by ring, p_add, hpT, ih]
    ring

/-- `cor:ring_following_equivalent_enumerate` (`syracuse.tex:96`), reading "`n` is a period": for
every ℤ/2ℤ-ring `A`, every `x ∈ A` and every `n`, `(a_k(x))_k` has period `n` iff `(Tᵏ(x))_k` has
period `n`, for the total `T`, `a`. No `2 ≠ 0`. -/
theorem periodic_a_iff_periodic_T (x : A) (n : ℕ) :
    (∀ k, a (k + n) x = a k x) ↔ (∀ k, T^[k + n] x = T^[k] x) := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · intro k; rfl
    have hpT : ∀ k, p k (T^[n] x) = p k x := by
      intro k
      simp only [p]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [a_iterate, h]
    have hfix : T^[n] x = x := by
      refine eq_of_p_eq hpT (fun N => ⟨N * n, ?_⟩)
      rw [hpT, p_mul_of_periodic h]
      have := one_le_p_of_periodic hn h
      nlinarith
    intro k
    rw [Function.iterate_add_apply, hfix]
  · intro h k
    simp only [a, h k]

/-- The first corollary, reading "eventually periodic of period `n`" (from any index `K` on). -/
theorem eventually_periodic_a_iff_periodic_T (x : A) (n K : ℕ) :
    (∀ k, K ≤ k → a (k + n) x = a k x) ↔ (∀ k, K ≤ k → T^[k + n] x = T^[k] x) := by
  have key := periodic_a_iff_periodic_T (T^[K] x) n
  simp only [a_iterate, ← Function.iterate_add_apply] at key
  constructor
  · intro h k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have := (key.1 (fun j => by rw [show j + n + K = (j + K) + n by ring]; exact h _ (by omega))) j
    rwa [show j + n + K = j + K + n by ring] at this
  · intro h k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have := (key.2 (fun j => by rw [show j + n + K = (j + K) + n by ring]; exact h _ (by omega))) j
    rwa [show j + n + K = j + K + n by ring] at this

/-- The first corollary, reading "of least period `n`". -/
theorem minimal_period_a_iff_minimal_period_T (x : A) (n : ℕ) :
    (0 < n ∧ (∀ k, a (k + n) x = a k x) ∧ ∀ m, 0 < m → m < n → ¬ ∀ k, a (k + m) x = a k x) ↔
      (0 < n ∧ (∀ k, T^[k + n] x = T^[k] x) ∧
        ∀ m, 0 < m → m < n → ¬ ∀ k, T^[k + m] x = T^[k] x) := by
  simp only [periodic_a_iff_periodic_T]

/-- When `2 ≠ 0`, a periodic orbit (`n ≥ 1`) is odd and avoids `−1/3`: on it `T`, `a` are the
paper's `T_A`, `a_n` (`T_odd`, `a_eq_nu2`). Through `−1/3` the total `T` goes to `0`, then to the
fixed point `1 ≠ −1/3`, and never returns. -/
theorem cycle_avoids_neg_third (h2 : (2 : A) ≠ 0) {x : A} {n : ℕ} (hn : 0 < n)
    (hx : T^[n] x = x) : Odd x ∧ ∀ k, 3 * T^[k] x + 1 ≠ 0 := by
  have hT0 : T (0 : A) = 1 := (T_unique h2 (t := 1) (k := 0) odd_one (by ring)).2
  have hT1 : T (1 : A) = 1 := (T_unique h2 (t := 1) (k := 2) odd_one (by norm_num)).2
  have hzero : ∀ z : A, 3 * z + 1 = 0 → T z = 0 := by
    intro z hz
    have := pow_v2_mul_T z
    rw [hz] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ h2)
  have hone : ∀ z : A, 3 * z + 1 = 0 → ∀ m, T^[m + 2] z = 1 := by
    intro z hz m
    induction m with
    | zero => simp [hzero z hz, hT0]
    | succ m ih => rw [show m + 1 + 2 = (m + 2) + 1 by ring, Function.iterate_succ_apply', ih, hT1]
  have havoid : ∀ k, 3 * T^[k] x + 1 ≠ 0 := by
    intro k hk
    have hz : T^[n + n] (T^[k] x) = T^[k] x := by
      rw [← Function.iterate_add_apply, show n + n + k = k + (n + n) by ring,
        Function.iterate_add_apply, Function.iterate_add_apply, hx, hx]
    have h1 := hone _ hk (n + n - 2)
    rw [show n + n - 2 + 2 = n + n by omega, hz] at h1
    rw [h1] at hk
    apply h2
    have h4 : (2 : A) * 2 = 0 := by linear_combination hk
    exact (mul_self_eq_zero).1 h4
  refine ⟨?_, havoid⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [← hx, zero_add, Function.iterate_succ_apply']
  exact T_odd (havoid m)

/-! ### `cor:ring_periodic_minimal_period` -/

/-- The reading of OQ-43: `A_u^n` with the product stopping at `n − 2 − k` (not the paper's
`def:define_n__n_`, which is `Syracuse.Aun`). -/
def AunAlt (n : ℕ) (u : ℤ) (α : ℤ → ℕ) : ℕ :=
  ∑ k ∈ range n, 3 ^ k * ∏ i ∈ range (n - 1 - k), 2 ^ α (u + i)

omit [IsZ2Ring A] in
/-- `∏_{i<m} 2^{a_{u+i}(x)} = 2^{p_m(Tᵘx)}`. -/
theorem prod_alpha (x : A) (α : ℤ → ℕ) (hα : ∀ k : ℕ, α k = a k x) (u m : ℕ) :
    ∏ i ∈ range m, 2 ^ α ((u : ℤ) + (i : ℤ)) = 2 ^ p m (T^[u] x) := by
  rw [Finset.prod_pow_eq_pow_sum, p]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (u : ℤ) + (i : ℤ) = ((u + i : ℕ) : ℤ) by push_cast; ring, hα, a_iterate, add_comm]

omit [IsZ2Ring A] in
/-- `A_u^n(a(x)) = 2^{p_n(x_u)} (3 x_{u+n} + 1) − 3ⁿ (3 x_u + 1)` in `A`, with `x_u = Tᵘx` (any orbit). -/
theorem Aun_cast_eq (x : A) (α : ℤ → ℕ) (hα : ∀ k : ℕ, α k = a k x) (n u : ℕ) :
    (Aun n u α : A) =
      2 ^ p n (T^[u] x) * (3 * T^[n] (T^[u] x) + 1) - 3 ^ n * (3 * T^[u] x + 1) := by
  set y := T^[u] x with hy
  have h0 : Aun n u α = ∑ k ∈ range n, 3 ^ k * 2 ^ p (n - k) y := by
    rw [Aun]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [prod_alpha x α hα u]
  have h1 : (Aun n u α : A) = ∑ k ∈ range n, (3 : A) ^ k * 2 ^ p (n - k) y := by
    rw [h0]
    push_cast
    rfl
  have h2 : ∑ k ∈ range n, (3 : A) ^ k * 2 ^ p (n - k) y =
      ∑ j ∈ range n, (2 : A) ^ p (j + 1) y * 3 ^ (n - 1 - j) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_range.1 hk
    rw [show n - (n - 1 - k) = k + 1 by omega]
    ring
  have h3 := base y (n + 1)
  rw [Finset.sum_range_succ'] at h3
  have h4 : ∑ j ∈ range n, (2 : A) ^ p (j + 1) y * 3 ^ (n + 1 - 1 - (j + 1)) =
      ∑ j ∈ range n, (2 : A) ^ p (j + 1) y * 3 ^ (n - 1 - j) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show n + 1 - 1 - (j + 1) = n - 1 - j by omega]
  rw [h4, p_zero, pow_zero, one_mul, show n + 1 - 1 - 0 = n by omega, p_succ',
    Function.iterate_succ_apply', pow_add] at h3
  have h5 := pow_v2_mul_T (T^[n] y)
  rw [h1, h2]
  have ha : a n y = v2 (3 * T^[n] y + 1) := rfl
  rw [ha] at h3
  linear_combination -h3 + 2 ^ p n y * h5

omit [IsZ2Ring A] in
/-- The reading of OQ-43: `A'_u^n(a(x)) = 2^{p_n(x_u)} x_{u+n} − 3ⁿ x_u` in `A` (`lem:base`). -/
theorem AunAlt_cast_eq (x : A) (α : ℤ → ℕ) (hα : ∀ k : ℕ, α k = a k x) (n u : ℕ) :
    (AunAlt n u α : A) = 2 ^ p n (T^[u] x) * T^[n] (T^[u] x) - 3 ^ n * T^[u] x := by
  set y := T^[u] x with hy
  have h0 : AunAlt n u α = ∑ k ∈ range n, 3 ^ k * 2 ^ p (n - 1 - k) y := by
    rw [AunAlt]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [prod_alpha x α hα u]
  have h1 : (AunAlt n u α : A) = ∑ k ∈ range n, (3 : A) ^ k * 2 ^ p (n - 1 - k) y := by
    rw [h0]
    push_cast
    rfl
  have h2 : ∑ k ∈ range n, (3 : A) ^ k * 2 ^ p (n - 1 - k) y =
      ∑ j ∈ range n, (2 : A) ^ p j y * 3 ^ (n - 1 - j) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_range.1 hk
    rw [show n - 1 - (n - 1 - k) = k by omega]
    ring
  rw [h1, h2, base y n]

omit [IsZ2Ring A] in
/-- On a cycle of length `n`: `A_u^n = (2^{p_n} − 3ⁿ)(3x_u + 1)` and `A'_u^n = (2^{p_n} − 3ⁿ) x_u`. -/
theorem Aun_cast_of_cycle {x : A} {n : ℕ} (hx : T^[n] x = x) (α : ℤ → ℕ)
    (hα : ∀ k : ℕ, α k = a k x) (u : ℕ) :
    (Aun n u α : A) = (2 ^ p n x - 3 ^ n) * (3 * T^[u] x + 1) ∧
      (AunAlt n u α : A) = (2 ^ p n x - 3 ^ n) * T^[u] x := by
  have hTu : T^[n] (T^[u] x) = T^[u] x := by
    rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hx]
  have hpu : p n (T^[u] x) = p n x := by
    have h1 := p_add u n x
    have h2 := p_add n u x
    rw [hx, add_comm n u] at h2
    omega
  refine ⟨?_, ?_⟩
  · rw [Aun_cast_eq x α hα n u, hTu, hpu]
    ring
  · rw [AunAlt_cast_eq x α hα n u, hTu, hpu]
    ring

omit [IsZ2Ring A] in
/-- On a cycle of least period `n`, the points `x_1, …, x_n` are pairwise distinct. -/
theorem iterate_ne_of_minimal {x : A} {n : ℕ} (hx : T^[n] x = x)
    (hmin : ∀ m, 0 < m → m < n → T^[m] x ≠ x) {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j)
    (hjn : j ≤ n) (hij : i ≠ j) : T^[i] x ≠ T^[j] x := by
  wlog hlt : i < j generalizing i j
  · exact fun h => this hj hjn hi hin (Ne.symm hij) (by omega) h.symm
  intro h
  apply hmin (n - j + i) (by omega) (by omega)
  have h' := congrArg (T^[n - j]) h
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
    show n - j + j = n by omega, hx] at h'
  exact h'

/-- `2^{p_n(x)} − 3ⁿ ∈ 2A + 1`, so `≠ 0`, on a cycle of length `n ≥ 1`. -/
theorem two_pow_p_sub_three_pow_ne_zero {x : A} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) :
    (2 : A) ^ p n x - 3 ^ n ≠ 0 := by
  have hper : ∀ k, a (k + n) x = a k x :=
    (periodic_a_iff_periodic_T x n).2 (fun k => by rw [Function.iterate_add_apply, hx])
  have hp := one_le_p_of_periodic hn hper
  have hodd : Odd ((2 : A) ^ p n x - 3 ^ n) := by
    refine Even.sub_odd ?_ odd_three.pow
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hp
    rw [hm, pow_succ]
    exact even_two.mul_left _
  intro h0
  exact not_two_dvd_of_odd IsZ2Ring.not_two_dvd_one hodd (h0 ▸ dvd_zero 2)

/-- `cor:ring_periodic_minimal_period` (`syracuse.tex:107`) for `i ≠ j`, with the printed `A_u^n`,
in every ℤ/2ℤ-ring; `a(x)` extended to `ℤ` in any way (only indices in `⟦1, 2n−1⟧` enter). -/
theorem Aun_sub_ne_zero {x : A} {n : ℕ} (hper : Function.IsPeriodicPt T n x) (hn : 0 < n)
    (hmin : ∀ m, 0 < m → m < n → ¬ Function.IsPeriodicPt T m x)
    (α : ℤ → ℕ) (hα : ∀ k : ℕ, α k = a k x) :
    ∀ i j : ℤ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → (Aun n i α : ℤ) - Aun n j α ≠ 0 := by
  intro i j hi hin hj hjn hij
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ i)
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ j)
  have hx : T^[n] x = x := hper
  intro h
  have hN : Aun n i α = Aun n j α := by omega
  have hA : (Aun n i α : A) = (Aun n j α : A) := by rw [hN]
  rw [(Aun_cast_of_cycle hx α hα i).1, (Aun_cast_of_cycle hx α hα j).1] at hA
  have h3 := mul_left_cancel₀ (two_pow_p_sub_three_pow_ne_zero hn hx) hA
  have h4 : (3 : A) * T^[i] x = 3 * T^[j] x := by linear_combination h3
  exact iterate_ne_of_minimal hx hmin (by omega) (by omega) (by omega) (by omega) (by omega)
    (mul_left_cancel₀ three_ne_zero_of_isZ2Ring h4)

/-- The same for `i ≠ j` in the reading of OQ-43 (`A_u^n` with the product to `n − 2 − k`). -/
theorem AunAlt_sub_ne_zero {x : A} {n : ℕ} (hper : Function.IsPeriodicPt T n x) (hn : 0 < n)
    (hmin : ∀ m, 0 < m → m < n → ¬ Function.IsPeriodicPt T m x)
    (α : ℤ → ℕ) (hα : ∀ k : ℕ, α k = a k x) :
    ∀ i j : ℤ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j →
      (AunAlt n i α : ℤ) - AunAlt n j α ≠ 0 := by
  intro i j hi hin hj hjn hij
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ i)
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ j)
  have hx : T^[n] x = x := hper
  intro h
  have hN : AunAlt n i α = AunAlt n j α := by omega
  have hA : (AunAlt n i α : A) = (AunAlt n j α : A) := by rw [hN]
  rw [(Aun_cast_of_cycle hx α hα i).2, (Aun_cast_of_cycle hx α hα j).2] at hA
  exact iterate_ne_of_minimal hx hmin (by omega) (by omega) (by omega) (by omega) (by omega)
    (mul_left_cancel₀ (two_pow_p_sub_three_pow_ne_zero hn hx) hA)

end Z2Ring

/-! ### Witnesses in `ℤ` -/

/-- The cycle `(−5, −7)` of `ℤ`, of least period `2`: the corrected corollary is not vacuous. -/
theorem cycle_neg_five :
    Function.IsPeriodicPt T 2 (-5 : ℤ) ∧ ¬ Function.IsPeriodicPt T 1 (-5 : ℤ) := by
  have h5 : T (-5 : ℤ) = -7 :=
    (T_unique (A := ℤ) two_ne_zero (x := -5) (t := -7) (k := 1) ⟨-4, by norm_num⟩ (by norm_num)).2
  have h7 : T (-7 : ℤ) = -5 :=
    (T_unique (A := ℤ) two_ne_zero (x := -7) (t := -5) (k := 2) ⟨-3, by norm_num⟩ (by norm_num)).2
  refine ⟨?_, ?_⟩
  · show T^[2] (-5 : ℤ) = -5
    simp [h5, h7]
  · intro h
    have h' : T^[1] (-5 : ℤ) = -5 := h
    simp [h5] at h'

/-- **Finding 3.** `cor:ring_periodic_minimal_period` as printed (all `i, j ∈ ⟦1, n⟧`) is false:
the cycle `(1)` of `ℤ`, `n = 1`, `i = j = 1`. -/
theorem cor_ring_periodic_minimal_period_printed_false :
    ¬ ∀ (B : Type) [CommRing B] [IsZ2Ring B] (x : B) (n : ℕ), Function.IsPeriodicPt T n x →
      0 < n → (∀ m, 0 < m → m < n → ¬ Function.IsPeriodicPt T m x) →
      ∀ α : ℤ → ℕ, (∀ k : ℕ, α k = a k x) →
      ∀ i j : ℤ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → (Aun n i α : ℤ) - Aun n j α ≠ 0 := by
  intro h
  have hT1 : T (1 : ℤ) = 1 :=
    (T_unique (A := ℤ) two_ne_zero (x := 1) (t := 1) (k := 2) odd_one (by norm_num)).2
  have hper : Function.IsPeriodicPt T 1 (1 : ℤ) := by
    show T^[1] (1 : ℤ) = 1
    simp [hT1]
  exact h ℤ 1 1 hper one_pos (fun m hm hm1 => absurd hm1 (by omega))
    (fun u => a u.toNat (1 : ℤ)) (fun k => by simp) 1 1 le_rfl le_rfl le_rfl le_rfl (sub_self _)

/-! ### `theo:rep` in `ℤ₂` -/

/-- `1/3 ∈ ℤ₂` (`3 ∈ ℤ₂ˣ`, l.92). -/
noncomputable def inv3 : ℤ_[2] := ↑(isUnit_three_padicInt.unit⁻¹)

/-- `3 · (1/3) = 1`. -/
theorem three_mul_inv3 : (3 : ℤ_[2]) * inv3 = 1 := isUnit_three_padicInt.mul_val_inv

/-- `‖1/3‖ = 1`. -/
theorem norm_inv3 : ‖inv3‖ = 1 := PadicInt.norm_units _

/-- `‖2‖ = 1/2` in `ℤ₂`. -/
theorem norm_two_padicInt : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  simpa using PadicInt.norm_p (p := 2)

/-- `1/3 ∈ 2ℤ₂ + 1`. -/
theorem odd_inv3 : Odd inv3 := by
  rcases IsZ2Ring.two_dvd_or_odd inv3 with h | h
  · exact absurd (three_mul_inv3 ▸ dvd_mul_of_dvd_right h 3) IsZ2Ring.not_two_dvd_one
  · exact h

/-- The map `φ : x ↦ (p_n(x))_n` (`syracuse.tex:88`), on any ring. -/
noncomputable def rep {B : Type*} [CommRing B] (x : B) : ℕ → ℕ := fun n => p n x

/-- The codomain `{p ∈ ℕ^ℕ | p₀ = 0 ∧ (pₙ) ↗↗}` (`syracuse.tex:88`); `↗↗`: strictly increasing. -/
def RepSeq : Set (ℕ → ℕ) := {q | q 0 = 0 ∧ StrictMono q}

/-- The odd points whose orbit avoids `−1/3` (`3Tᵏx + 1 ≠ 0` for every `k`): in `ℤ₂`, `2ℤ₂+1` minus
the backward `T`-orbit of `−1/3` (Finding 1); in `ℤ`, all of `2ℤ+1` (`three_mul_add_one_ne_zero`). -/
def RepDomain (B : Type*) [CommRing B] : Set B := {x | Odd x ∧ ∀ k, 3 * T^[k] x + 1 ≠ 0}

/-- The printed inverse `φ⁻¹(q) = −(1/3) ∑ₙ 2^{qₙ}/3ⁿ` (`syracuse.tex:90`). -/
noncomputable def repInv (q : ℕ → ℕ) : ℤ_[2] := -inv3 * ∑' n, (2 : ℤ_[2]) ^ q n * inv3 ^ n

/-- `S(q) = ∑ₙ 2^{qₙ}/3ⁿ`. -/
noncomputable def repSeries (q : ℕ → ℕ) : ℤ_[2] := ∑' n, (2 : ℤ_[2]) ^ q n * inv3 ^ n

/-- `φ⁻¹(q) = −(1/3) S(q)`. -/
theorem repInv_eq (q : ℕ → ℕ) : repInv q = -inv3 * repSeries q := rfl

/-- `q ↦ (q_{n+1} − q₁)_n`: the representation of `T(x)` from that of `x`. -/
def repShift (q : ℕ → ℕ) : ℕ → ℕ := fun n => q (n + 1) - q 1

/-- `q ↦ (q_{m+n} − q_n)_m`: the representation of `Tⁿ(x)`. -/
def repShiftN (q : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun m => q (m + n) - q n

/-- `∑ 2^{qₙ}/3ⁿ` converges in `ℤ₂` when `qₙ ≥ n`: its terms have norm `≤ 2⁻ⁿ`. -/
theorem summable_rep {q : ℕ → ℕ} (hq : ∀ n, n ≤ q n) :
    Summable (fun n => (2 : ℤ_[2]) ^ q n * inv3 ^ n) := by
  refine Summable.of_norm_bounded summable_geometric_two (fun n => ?_)
  rw [norm_mul, norm_pow, norm_pow, norm_inv3, one_pow, mul_one, norm_two_padicInt, one_div]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hq n)

/-- A strictly increasing `q : ℕ → ℕ` has `n ≤ qₙ`. -/
theorem le_of_mem_repSeq {q : ℕ → ℕ} (hq : q ∈ RepSeq) (n : ℕ) : n ≤ q n := hq.2.id_le n

/-- The shift preserves `RepSeq`. -/
theorem repShift_mem {q : ℕ → ℕ} (hq : q ∈ RepSeq) : repShift q ∈ RepSeq := by
  refine ⟨by simp [repShift], fun m k hmk => ?_⟩
  simp only [repShift]
  have h1 := hq.2 (show m + 1 < k + 1 by omega)
  have h2 := hq.2.monotone (show 1 ≤ m + 1 by omega)
  omega

/-- `S(q) = 1 + (1/3) 2^{q₁} S(q')`, `q' = repShift q`. -/
theorem repSeries_eq {q : ℕ → ℕ} (hq : q ∈ RepSeq) :
    repSeries q = 1 + inv3 * 2 ^ q 1 * repSeries (repShift q) := by
  rw [repSeries, (summable_rep (le_of_mem_repSeq hq)).tsum_eq_zero_add, hq.1, pow_zero, pow_zero,
    one_mul, repSeries, ← (summable_rep (le_of_mem_repSeq (repShift_mem hq))).tsum_mul_left]
  congr 1
  refine tsum_congr (fun n => ?_)
  have h := hq.2.monotone (show 1 ≤ n + 1 by omega)
  have h2 : (2 : ℤ_[2]) ^ q (n + 1) = 2 ^ q 1 * 2 ^ repShift q n := by
    rw [← pow_add, repShift, Nat.add_sub_cancel' h]
  rw [h2, pow_succ]
  ring

/-- `φ⁻¹(q) ∈ 2ℤ₂ + 1`. -/
theorem repInv_odd {q : ℕ → ℕ} (hq : q ∈ RepSeq) : Odd (repInv q) := by
  have hS := repSeries_eq hq
  have h1 : 1 ≤ q 1 := by have := hq.2 (show 0 < 1 by omega); rw [hq.1] at this; omega
  have hSodd : Odd (repSeries q) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' h1
    refine ⟨inv3 * 2 ^ m * repSeries (repShift q), ?_⟩
    rw [hS, hm, pow_succ]
    ring
  rw [repInv_eq]
  exact odd_inv3.neg.mul hSodd

/-- `3 φ⁻¹(q) + 1 = 2^{q₁} φ⁻¹(q')`. -/
theorem three_mul_repInv_add_one {q : ℕ → ℕ} (hq : q ∈ RepSeq) :
    3 * repInv q + 1 = 2 ^ q 1 * repInv (repShift q) := by
  have hS := repSeries_eq hq
  rw [repInv_eq, repInv_eq]
  linear_combination (-(repSeries q)) * three_mul_inv3 - hS

/-- `T(φ⁻¹q) = φ⁻¹q'`, `a₀(φ⁻¹q) = q₁`, `3φ⁻¹(q) + 1 ≠ 0`. -/
theorem T_repInv_aux {q : ℕ → ℕ} (hq : q ∈ RepSeq) :
    T (repInv q) = repInv (repShift q) ∧ a 0 (repInv q) = q 1 ∧ 3 * repInv q + 1 ≠ 0 := by
  obtain ⟨e1, e2⟩ := T_unique (A := ℤ_[2]) two_ne_zero (x := repInv q) (t := repInv (repShift q))
    (k := q 1) (repInv_odd (repShift_mem hq)) (three_mul_repInv_add_one hq).symm
  refine ⟨e2, e1.symm, ?_⟩
  rw [three_mul_repInv_add_one hq]
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) (fun h => ?_)
  exact not_two_dvd_of_odd IsZ2Ring.not_two_dvd_one (repInv_odd (repShift_mem hq)) (h ▸ dvd_zero 2)

/-- `repShiftN q 0 = q` when `q₀ = 0`. -/
theorem repShiftN_zero {q : ℕ → ℕ} (hq0 : q 0 = 0) : repShiftN q 0 = q := by
  funext m
  simp [repShiftN, hq0]

/-- `repShiftN q (n+1) = repShift (repShiftN q n)`. -/
theorem repShiftN_succ {q : ℕ → ℕ} (hq : StrictMono q) (n : ℕ) :
    repShiftN q (n + 1) = repShift (repShiftN q n) := by
  funext m
  simp only [repShiftN, repShift]
  rw [show m + (n + 1) = m + 1 + n by ring, show 1 + n = n + 1 by ring]
  have h1 := hq.monotone (show n ≤ n + 1 by omega)
  have h2 := hq.monotone (show n + 1 ≤ m + 1 + n by omega)
  omega

/-- `repShiftN q n ∈ RepSeq`. -/
theorem repShiftN_mem {q : ℕ → ℕ} (hq : q ∈ RepSeq) (n : ℕ) : repShiftN q n ∈ RepSeq := by
  induction n with
  | zero => rwa [repShiftN_zero hq.1]
  | succ n ih => rw [repShiftN_succ hq.2]; exact repShift_mem ih

/-- `Tⁿ(φ⁻¹q) = φ⁻¹(repShiftN q n)`. -/
theorem T_iterate_repInv {q : ℕ → ℕ} (hq : q ∈ RepSeq) (n : ℕ) :
    T^[n] (repInv q) = repInv (repShiftN q n) := by
  induction n with
  | zero => rw [repShiftN_zero hq.1]; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, (T_repInv_aux (repShiftN_mem hq n)).1, repShiftN_succ hq.2]

/-- `a_n(φ⁻¹q) = q_{n+1} − q_n`. -/
theorem a_repInv {q : ℕ → ℕ} (hq : q ∈ RepSeq) (n : ℕ) : a n (repInv q) = q (n + 1) - q n := by
  have h := a_iterate 0 n (repInv q)
  rw [zero_add] at h
  rw [← h, T_iterate_repInv hq, (T_repInv_aux (repShiftN_mem hq n)).2.1, repShiftN, add_comm 1 n]

/-- `p_n(φ⁻¹q) = q_n`. -/
theorem p_repInv {q : ℕ → ℕ} (hq : q ∈ RepSeq) (n : ℕ) : p n (repInv q) = q n := by
  induction n with
  | zero => rw [p_zero, hq.1]
  | succ n ih =>
    rw [p_succ', ih, a_repInv hq]
    have := hq.2.monotone (show n ≤ n + 1 by omega)
    omega

/-- `φ⁻¹(q) ∈ RepDomain`, `T(φ⁻¹ q) = φ⁻¹(q')` and `a₀(φ⁻¹ q) = q₁`. -/
theorem T_repInv {q : ℕ → ℕ} (hq : q ∈ RepSeq) :
    repInv q ∈ RepDomain ℤ_[2] ∧ T (repInv q) = repInv (repShift q) ∧ a 0 (repInv q) = q 1 := by
  refine ⟨⟨repInv_odd hq, fun k => ?_⟩, (T_repInv_aux hq).1, (T_repInv_aux hq).2.1⟩
  rw [T_iterate_repInv hq]
  exact (T_repInv_aux (repShiftN_mem hq k)).2.2

/-- `φ` maps `RepDomain` into `RepSeq`, in every ℤ/2ℤ-ring. -/
theorem rep_mapsTo {B : Type*} [CommRing B] [IsZ2Ring B] :
    Set.MapsTo rep (RepDomain B) RepSeq := by
  intro x hx
  refine ⟨p_zero x, strictMono_nat_of_lt_succ (fun n => ?_)⟩
  show p n x < p (n + 1) x
  rw [p_succ']
  have := one_le_a (T_iterate_odd hx.1 (n := n) (fun k _ => hx.2 k))
  omega

/-- `φ` is injective on `RepDomain`, in every ℤ/2ℤ-ring. -/
theorem rep_injOn {B : Type*} [CommRing B] [IsZ2Ring B] : Set.InjOn rep (RepDomain B) :=
  fun _ hx _ _ hxy => eq_of_p_eq (fun k => congrFun hxy k) (fun N => ⟨N, le_p_of_orbit hx.1 hx.2 N⟩)

/-- `φ⁻¹` maps `RepSeq` into `RepDomain`. -/
theorem repInv_mapsTo : Set.MapsTo repInv RepSeq (RepDomain ℤ_[2]) := fun _ hq => (T_repInv hq).1

/-- `φ ∘ φ⁻¹ = id` on `RepSeq` (the surjectivity of `φ`, Finding 2). -/
theorem rep_repInv {q : ℕ → ℕ} (hq : q ∈ RepSeq) : rep (repInv q) = q := funext (p_repInv hq)

/-- `φ⁻¹ ∘ φ = id` on `RepDomain` (the printed proof's half). -/
theorem repInv_rep {x : ℤ_[2]} (hx : x ∈ RepDomain ℤ_[2]) : repInv (rep x) = x :=
  rep_injOn (repInv_mapsTo (rep_mapsTo hx)) hx (rep_repInv (rep_mapsTo hx))

/-- `theo:rep` (`syracuse.tex:88`), its strongest true form in `ℤ₂`: `φ` is a bijection from the
odd points whose orbit avoids `−1/3` onto the strictly increasing sequences from `0`, its inverse
is the printed `φ⁻¹`, and `φ⁻¹` is a bijection back. -/
theorem theo_rep :
    Set.BijOn rep (RepDomain ℤ_[2]) RepSeq ∧ Set.InvOn repInv rep (RepDomain ℤ_[2]) RepSeq ∧
      Set.BijOn repInv RepSeq (RepDomain ℤ_[2]) := by
  have hinv : Set.InvOn repInv rep (RepDomain ℤ_[2]) RepSeq :=
    ⟨fun _ hx => repInv_rep hx, fun _ hq => rep_repInv hq⟩
  exact ⟨hinv.bijOn rep_mapsTo repInv_mapsTo, hinv, hinv.symm.bijOn repInv_mapsTo rep_mapsTo⟩

/-- The image of the printed `φ⁻¹` is exactly `RepDomain`, not `2ℤ₂ + 1`. -/
theorem repInv_image : repInv '' RepSeq = RepDomain ℤ_[2] := theo_rep.2.2.image_eq

/-- **Finding 1.** `−1/3 ∈ 2ℤ₂ + 1` is outside the image of the printed `φ⁻¹`. -/
theorem neg_inv3_not_mem_image : Odd (-inv3) ∧ -inv3 ∉ repInv '' RepSeq := by
  have h0 : 3 * (-inv3) + 1 = 0 := by linear_combination -three_mul_inv3
  refine ⟨odd_inv3.neg, ?_⟩
  rw [repInv_image]
  exact fun h => h.2 0 h0

/-- **Finding 1, beyond `−1/3`.** For every `k ≥ 1`, `y = −(2ᵏ + 3)/9 ∈ 2ℤ₂ + 1` has `T(y) = −1/3`
(the proof computes `ν₂(3y + 1) = k`; not stated), so it too is outside the image of the printed
`φ⁻¹`. -/
theorem neg_third_preimage (k : ℕ) (hk : 1 ≤ k) :
    Odd (-(2 ^ k + 3) * inv3 ^ 2) ∧ T (-(2 ^ k + 3) * inv3 ^ 2) = -inv3 ∧
      -(2 ^ k + 3) * inv3 ^ 2 ∉ repInv '' RepSeq := by
  have h3 := three_mul_inv3
  have hT := (T_unique (A := ℤ_[2]) two_ne_zero (x := -(2 ^ k + 3) * inv3 ^ 2) (t := -inv3) (k := k)
    odd_inv3.neg (by linear_combination (2 ^ k * inv3 + 3 * inv3 + 1) * h3)).2
  refine ⟨?_, hT, ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have hodd : Odd (-(2 ^ (m + 1) + 3) : ℤ_[2]) := by
      refine Odd.neg ⟨2 ^ m + 1, ?_⟩
      ring
    exact hodd.mul (odd_inv3.pow)
  · rw [repInv_image]
    intro h
    apply h.2 1
    rw [Function.iterate_one, hT]
    linear_combination -h3

/-- **Finding 1, as printed.** No map `φ` from `2ℤ₂ + 1` into the strictly increasing sequences
from `0` has the printed `φ⁻¹` as a left inverse, whatever its values where the paper's `p_n` are
undefined: `theo:rep` is false on `2A₂ + 1`. -/
theorem rep_printed_false :
    ¬ ∃ φ : ℤ_[2] → ℕ → ℕ, Set.MapsTo φ {x | Odd x} RepSeq ∧ Set.LeftInvOn repInv φ {x | Odd x} := by
  rintro ⟨φ, hmaps, hinv⟩
  have hodd : Odd (-inv3) := odd_inv3.neg
  exact neg_inv3_not_mem_image.2 ⟨φ (-inv3), hmaps hodd, hinv hodd⟩

end Syracuse
