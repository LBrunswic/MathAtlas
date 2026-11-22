import Syracuse.Base
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Syracuse § 1 over ℤ: bounds on `p_n(x) log 2 - n log 3`, divergent orbits and cycles

**`lem:one_has`** — `syracuse.tex:114` and **`cor:corollary_2`** — `syracuse.tex:140` are marked as
printed. The two others are false as printed and marked in corrected form under DEC-183 (OQ-54):

* **`lem:itemize_furthermore_itemize`** — `syracuse.tex:127` (l.127–136, proof l.137–139) — marked
  in corrected form (DEC-183, OQ-54 (a): `n ≥ 1` in the first bullet; (b): the bound
  `n log(1 + 1/(3x))` in the second) on `Syracuse.itemize_first` and `Syracuse.itemize_second`; the
  constant `1/3` is sharp (`itemize_second_sharp`). **False as printed**: the first bullet at `n = 0`
  for every `x` (`itemize_first_printed_false`), the second at `x = 1` for every `n ≥ 1`
  (`itemize_second_printed_false`).
* **`cor:bounds`** — `syracuse.tex:142` (l.142–143) — marked in corrected form (DEC-183, OQ-54 (c):
  the two bounds exchanged, each with the factor `3`) on `Syracuse.bounds`:
  `log₂(1 + 1/(3 max)) ≤ p_n/n − log₂ 3 ≤ log₂(1 + 1/(3 min))` on every cycle of `ℤ*`, of either sign
  (`cycle_mean`). **False as printed** at `x = 1`, `n = 1` (`bounds_printed_false`); its lower bound
  fails on every positive cycle (`bounds_printed_lower_false`).

> We now concentrate on  $A=\ZZ$ case.

> **lem:one_has.** Let $x\in \ZZ^*$ such that $\forall n\in\NN, |T^n(x)|\geq |x|$, one has :
> $$p_n(x) \log(2) - n \log(3)\leq n\log\left(1+ \frac{1}{|x|}\right)  $$

> **lem:itemize_furthermore_itemize.** Let $x\in \NN^*$.
> * If $n\in\NN$ is such that $T^n(x)\leq x$ then $$p_n(x)\log(2)-n\log(3) >0$$
> * If furthermore $\forall n\in\NN,~T^n(x)\leq x $ then
>   $$\forall n\in \NN,\quad  p_n(x)\log(2)-n\log(3) \geq n \log\left(1+\frac{1}{x} \right).$$

> **cor:corollary_2.** Let $x\in \NN$ such that $T^n(x) \xrightarrow{n\rightarrow +\infty} +\infty$,
> then $$\limsup_{n\rightarrow+\infty} \frac{p_n}{n}\leq \log_2(3) $$

> **cor:bounds.** Let $x\in \NN$ such that $\exists n\in \NN^*,~ T^n(x) = x$, then for such a
> $n\in \NN^*$, $$\log_2\left(1+\frac{1}{\min_{k\in \NN}(T^k(x))}\right)  \leq \frac{p_n}{n}-\log_2(3)
> \leq  \log_2\left(1+\frac{1}{\max_{k\in \NN}(T^k(x))}\right) $$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `x ∈ ℤ*` (`lem:one_has`) | ✓ carried (`x : ℤ`, `x ≠ 0`) |
| `∀ n, abs(Tⁿ x) ≥ abs(x)` (`lem:one_has`) | ✓ carried in `one_has`; ⚠ weakened to `k ≤ n` in `one_has_of_le`, `one_has_sharp` |
| `x ∈ ℕ*` (`lem:itemize_furthermore_itemize`) | ✓ carried (`x : ℤ`, `0 < x`) |
| `n ∈ ℕ` (first bullet) | ⚠ strengthened: `1 ≤ n` in `itemize_first`, a finding (false at `n = 0`) |
| `∀ n, Tⁿ x ≤ x` (second bullet) | ⚠ weakened to `k ≤ n`; the conclusion is corrected, a finding |
| `x ∈ ℕ` (`cor:corollary_2`) | ⚠ weakened: `x ∈ ℤ` |
| `Tⁿ(x) → +∞` (`cor:corollary_2`) | ✓ carried (`Tendsto (T^[·] x) atTop atTop`) |
| `x ∈ ℕ`, `n ∈ ℕ*`, `Tⁿ x = x` (`cor:bounds`) | ⚠ weakened: any cycle of `ℤ` (`x ≠ 0` is derived); the conclusion is corrected, a finding |
| `T` on `2ℤ + 1` (`def:ring_define`, l.55) | ⚠ weakened: `Syracuse.T` is total; even `x` are allowed (SCOPE) |

## SCOPE (disclosed)

* The method is the product form of `lem:base` (`pow_p_mul_T_iterate_eq_prod`): for `x ∈ ℤ*`,
  `2^{p_n(x)} Tⁿ(x) = 3ⁿ x ∏_{k<n} (1 + 1/(3Tᵏ(x)))`, from `2^{a_k} T^{k+1} = 3Tᵏ + 1`; its log
  form is `log_identity_int`. Every factor is positive (`one_add_one_div_three_mul_pos`) since the
  orbit avoids `0` (`T_iterate_ne_zero_int`). It replaces the Grönwall step of l.123.
* `lem:one_has` holds as printed (`one_has`), in the sharper form `n log(1 + 1/(3|x|))`
  (`one_has_sharp`), and with the hypothesis only for `k ≤ n` (`one_has_of_le`). Its printed
  proof has three slips, none touching the statement: l.119 drops the factor `1/3` of `lem:base`
  divided by `3ⁿ`, so the displayed equation is false (at `x = 1`, `n = 1`: `1/3 ≠ 1`,
  `one_has_proof_l119_false`), harmless since l.121 only gets weaker; l.123 defines `u_k` with
  `n log 3` for `k log 3`; l.124 has `(1 + 1/x)ⁿ`, false at `x = -1`, `n = 1`
  (`one_has_proof_l124_false`), where the statement's `abs(x)` is right.
* Finding (`lem:itemize_furthermore_itemize`, first bullet, l.130–131): false at `n = 0` for
  every `x`, where it asks `0 > 0` (`itemize_first_fails_at_zero`, `itemize_first_printed_false`).
  It holds for `n ≥ 1` (`itemize_first`).
* Finding (second bullet, l.132): false at `x = 1` for every `n ≥ 1`. There `T(1) = 1`,
  `a_k(1) = 2`, `p_n(1) = 2n` (`T_one_int`, `a_one_int`, `p_one_int`), and
  `n log(4/3) < n log 2` (`itemize_second_fails_at_one`, `itemize_second_printed_false`). The true
  bound is `n log(1 + 1/(3x))` (`itemize_second`), attained at `x = 1` for every `n`
  (`itemize_second_sharp`). Whether the printed bound holds for every `x ≥ 2` is not decided here.
* `cor:corollary_2` holds as printed (`corollary_2`), for every `x ∈ ℤ`. The `limsup` is in `ℝ`, and
  the conclusion includes that `p_n/n` is bounded above, so it is not a junk value. The `ε` form is
  `corollary_2_eventually`. The proof is the product form with Cesàro: eventually `Tⁿ(x) ≥ abs(x)`,
  and the mean of `log(1 + 1/(3Tᵏ(x))) ≤ 1/(3Tᵏ(x)) → 0` tends to `0`.
* Finding (`cor:bounds`, l.142): false at `x = 1`, `n = 1`, where it asks `log₂ 2 ≤ 2 - log₂ 3`
  (`bounds_printed_false`). Its lower bound fails on every positive cycle
  (`bounds_printed_lower_false`), and its two bounds are in decreasing order (`1/min ≥ 1/max`).
  True form, for every cycle of `ℤ*`, positive or negative: `p_n/n - log₂ 3` is the mean of
  `log₂(1 + 1/(3Tᵏ(x)))` (`cycle_mean`), hence lies between `log₂(1 + 1/(3 max))` and
  `log₂(1 + 1/(3 min))` (`bounds`); min and max exist (`exists_isLeast_isGreatest_of_cycle`).
* Reading: `T` on even integers. The paper's `T_ℤ` is defined on `2ℤ + 1` (l.55), while the
  statements take `x ∈ ℤ*`, `ℕ*`, `ℕ`. `Syracuse.T` is total (for even `x`, `T x = 3x + 1`,
  `a_0(x) = 0`), and every statement is proved for all such `x`. That contains the `2ℤ + 1` reading,
  and every counterexample here is odd (`x = 1`, `x = -1`). Over `ℤ` there is no junk value: on
  `2ℤ + 1`, `T`, `a`, `p` are the paper's maps (`not_isUnit_three_int`,
  `Syracuse.base_of_not_isUnit_three`); on even `x` they follow the printed formula, which `lem:base`
  (l.67) forces anyway.
* `cor:bounds` reads "for such a `n`" as every `n ∈ ℕ*` with `Tⁿ(x) = x`, not only the minimal
  period. Min and max over `k ∈ ℕ` are `IsLeast` and `IsGreatest` of the orbit.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset Filter Real

/-- `3` is not a unit of `ℤ`: over `ℤ` the maps `T`, `a`, `p` are the paper's everywhere. -/
theorem not_isUnit_three_int : ¬ IsUnit (3 : ℤ) := by
  rw [Int.isUnit_iff]; omega

/-- `T` never vanishes on `ℤ` (`3y + 1 ≠ 0`). -/
theorem T_ne_zero_int (y : ℤ) : T y ≠ 0 := by
  intro h
  have := pow_v2_mul_T y
  rw [h, mul_zero] at this
  exact three_mul_add_one_ne_zero not_isUnit_three_int y this.symm

/-- The orbit of a nonzero integer avoids `0`. -/
theorem T_iterate_ne_zero_int {x : ℤ} (hx : x ≠ 0) (k : ℕ) : T^[k] x ≠ 0 := by
  rcases k with _ | k
  · exact hx
  · rw [Function.iterate_succ_apply']
    exact T_ne_zero_int _

/-- The step identity `2^{a_k(x)} T^{k+1}(x) = 3 Tᵏ(x) + 1`, in any commutative ring. -/
theorem two_pow_a_mul_T_iterate_succ {A : Type*} [CommRing A] (x : A) (k : ℕ) :
    (2 : A) ^ a k x * T^[k + 1] x = 3 * T^[k] x + 1 := by
  rw [Function.iterate_succ_apply']
  exact pow_v2_mul_T _

/-- `T` maps `ℕ` into `ℕ*`. -/
theorem T_pos_of_nonneg_int {y : ℤ} (hy : 0 ≤ y) : 0 < T y := by
  have h := pow_v2_mul_T y
  have h2 : (0 : ℤ) < 2 ^ v2 (3 * y + 1) := by positivity
  by_contra hc
  have hc' := not_lt.1 hc
  nlinarith

/-- `T` maps negative integers to negative integers. -/
theorem T_neg_of_neg_int {y : ℤ} (hy : y < 0) : T y < 0 := by
  have h := pow_v2_mul_T y
  have h2 : (0 : ℤ) < 2 ^ v2 (3 * y + 1) := by positivity
  by_contra hc
  have hc' := not_lt.1 hc
  nlinarith

theorem T_iterate_pos_int {x : ℤ} (hx : 0 < x) (k : ℕ) : 0 < T^[k] x := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact T_pos_of_nonneg_int ih.le

theorem T_iterate_neg_int {x : ℤ} (hx : x < 0) (k : ℕ) : T^[k] x < 0 := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact T_neg_of_neg_int ih

/-- The factor `1 + 1/(3y)` is positive for a nonzero integer `y`. -/
theorem one_add_one_div_three_mul_pos {y : ℤ} (hy : y ≠ 0) : 0 < 1 + 1 / (3 * (y : ℝ)) := by
  rcases lt_or_gt_of_ne hy with h | h
  · have h' : (y : ℝ) ≤ -1 := by exact_mod_cast (show y ≤ -1 by omega)
    have h3 : (3 * (y : ℝ)) < 0 := by linarith
    rw [show 1 + 1 / (3 * (y : ℝ)) = (3 * y + 1) / (3 * y) by field_simp]
    exact div_pos_of_neg_of_neg (by linarith) h3
  · have h' : (0 : ℝ) < y := by exact_mod_cast h
    positivity

/-- The product form of `lem:base` over `ℤ`: for `x ∈ ℤ*`,
`2^{p_n(x)} Tⁿ(x) = 3ⁿ x ∏_{k<n} (1 + 1/(3Tᵏ(x)))`. -/
theorem pow_p_mul_T_iterate_eq_prod {x : ℤ} (hx : x ≠ 0) (n : ℕ) :
    (2 : ℝ) ^ p n x * ((T^[n] x : ℤ) : ℝ) =
      3 ^ n * (x : ℝ) * ∏ k ∈ range n, (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) := by
  induction n with
  | zero => simp [p_zero]
  | succ n ih =>
    have hstep : (2 : ℝ) ^ a n x * ((T^[n + 1] x : ℤ) : ℝ) = 3 * ((T^[n] x : ℤ) : ℝ) + 1 := by
      exact_mod_cast two_pow_a_mul_T_iterate_succ x n
    have hne : ((T^[n] x : ℤ) : ℝ) ≠ 0 := by exact_mod_cast T_iterate_ne_zero_int hx n
    rw [p_succ', pow_add, prod_range_succ, pow_succ, mul_assoc, hstep]
    calc (2 : ℝ) ^ p n x * (3 * ((T^[n] x : ℤ) : ℝ) + 1)
        = (2 : ℝ) ^ p n x * ((T^[n] x : ℤ) : ℝ) * (3 * (1 + 1 / (3 * ((T^[n] x : ℤ) : ℝ)))) := by
          field_simp
      _ = _ := by rw [ih]; ring

/-- The log form of `pow_p_mul_T_iterate_eq_prod`, for `x ∈ ℤ*`:
`p_n(x) log 2 - n log 3 = log|x| - log|Tⁿ(x)| + ∑_{k<n} log(1 + 1/(3Tᵏ(x)))`. -/
theorem log_identity_int {x : ℤ} (hx : x ≠ 0) (n : ℕ) :
    ((p n x : ℕ) : ℝ) * log 2 - n * log 3 =
      log |(x : ℝ)| - log |((T^[n] x : ℤ) : ℝ)| +
        ∑ k ∈ range n, log (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) := by
  have h := congrArg Real.log (pow_p_mul_T_iterate_eq_prod hx n)
  have hxn : ((T^[n] x : ℤ) : ℝ) ≠ 0 := by exact_mod_cast T_iterate_ne_zero_int hx n
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hf : ∀ k ∈ range n, (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) ≠ 0 :=
    fun k _ => (one_add_one_div_three_mul_pos (T_iterate_ne_zero_int hx k)).ne'
  rw [Real.log_mul (by positivity) hxn, Real.log_mul (by positivity) (prod_ne_zero_iff.2 hf),
    Real.log_mul (by positivity) hx', Real.log_prod hf, Real.log_pow, Real.log_pow] at h
  rw [Real.log_abs, Real.log_abs]
  linarith

/-- `1 + 1/(3y) ≤ 1 + 1/(3|x|)` when `0 < |x| ≤ |y|`. -/
theorem one_add_one_div_three_mul_le {x y : ℤ} (hx : x ≠ 0) (hxy : |x| ≤ |y|) :
    1 + 1 / (3 * (y : ℝ)) ≤ 1 + 1 / (3 * |(x : ℝ)|) := by
  have hx' : (0 : ℝ) < |(x : ℝ)| := by positivity
  have hxy' : |(x : ℝ)| ≤ |(y : ℝ)| := by exact_mod_cast hxy
  have h1 : 1 / (3 * (y : ℝ)) ≤ 1 / (3 * |(y : ℝ)|) := by
    rcases le_or_gt 0 (y : ℝ) with h | h
    · rw [abs_of_nonneg h]
    · have : 1 / (3 * (y : ℝ)) < 0 := by
        rw [one_div_neg]; linarith
      have : 0 ≤ 1 / (3 * |(y : ℝ)|) := by positivity
      linarith
  have h2 : 1 / (3 * |(y : ℝ)|) ≤ 1 / (3 * |(x : ℝ)|) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-! ### `lem:one_has` -/

/-- `lem:one_has`, sharper: the bound `n log(1 + 1/(3|x|))`, the hypothesis only for `k ≤ n`. -/
theorem one_has_sharp {x : ℤ} (hx : x ≠ 0) {n : ℕ} (h : ∀ k ≤ n, |x| ≤ |T^[k] x|) :
    ((p n x : ℕ) : ℝ) * log 2 - n * log 3 ≤ n * log (1 + 1 / (3 * |(x : ℝ)|)) := by
  rw [log_identity_int hx n]
  have hx' : (0 : ℝ) < |(x : ℝ)| := by positivity
  have h1 : log |(x : ℝ)| - log |((T^[n] x : ℤ) : ℝ)| ≤ 0 := by
    have : |(x : ℝ)| ≤ |((T^[n] x : ℤ) : ℝ)| := by exact_mod_cast h n le_rfl
    linarith [Real.log_le_log hx' this]
  have h2 : ∑ k ∈ range n, log (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) ≤
      ∑ k ∈ range n, log (1 + 1 / (3 * |(x : ℝ)|)) := by
    refine sum_le_sum fun k hk => ?_
    exact Real.log_le_log (one_add_one_div_three_mul_pos (T_iterate_ne_zero_int hx k))
      (one_add_one_div_three_mul_le hx (h k (mem_range.1 hk).le))
  rw [sum_const, card_range, nsmul_eq_mul] at h2
  linarith

/-- `lem:one_has` with the hypothesis only for `k ≤ n`. -/
theorem one_has_of_le {x : ℤ} (hx : x ≠ 0) {n : ℕ} (h : ∀ k ≤ n, |x| ≤ |T^[k] x|) :
    ((p n x : ℕ) : ℝ) * log 2 - n * log 3 ≤ n * log (1 + 1 / |(x : ℝ)|) := by
  refine (one_has_sharp hx h).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  have hx' : (0 : ℝ) < |(x : ℝ)| := by positivity
  refine Real.log_le_log (by positivity) ?_
  have : 1 / (3 * |(x : ℝ)|) ≤ 1 / |(x : ℝ)| :=
    one_div_le_one_div_of_le hx' (by linarith)
  linarith

/-- **`lem:one_has`** (`syracuse.tex:114`), as printed: for `x ∈ ℤ*` with `|Tⁿ(x)| ≥ |x|` for
every `n`, `p_n(x) log 2 - n log 3 ≤ n log(1 + 1/|x|)`. -/
theorem one_has {x : ℤ} (hx : x ≠ 0) (h : ∀ n : ℕ, |x| ≤ |T^[n] x|) (n : ℕ) :
    ((p n x : ℕ) : ℝ) * log 2 - n * log 3 ≤ n * log (1 + 1 / |(x : ℝ)|) :=
  one_has_of_le hx fun k _ => h k

/-! ### The orbit of `1` (and of `0`, `-1`) -/

/-- `T(1) = 1` and `a_0(1) = ν₂(4) = 2`. -/
theorem T_one_int : T (1 : ℤ) = 1 ∧ v2 (3 * (1 : ℤ) + 1) = 2 := by
  obtain ⟨h1, h2⟩ := T_unique (A := ℤ) two_ne_zero (x := 1) (t := 1) (k := 2) odd_one (by norm_num)
  exact ⟨h2, h1.symm⟩

theorem T_zero_int : T (0 : ℤ) = 1 := by
  exact (T_unique (A := ℤ) two_ne_zero (x := 0) (t := 1) (k := 0) odd_one (by norm_num)).2

/-- `T(-1) = -1` and `a_0(-1) = ν₂(-2) = 1`. -/
theorem T_neg_one_int : T (-1 : ℤ) = -1 ∧ v2 (3 * (-1 : ℤ) + 1) = 1 := by
  obtain ⟨h1, h2⟩ := T_unique (A := ℤ) two_ne_zero (x := -1) (t := -1) (k := 1)
    (by decide) (by norm_num)
  exact ⟨h2, h1.symm⟩

theorem T_iterate_one_int (k : ℕ) : T^[k] (1 : ℤ) = 1 :=
  Function.iterate_fixed T_one_int.1 k

theorem T_iterate_neg_one_int (k : ℕ) : T^[k] (-1 : ℤ) = -1 :=
  Function.iterate_fixed T_neg_one_int.1 k

theorem a_one_int (k : ℕ) : a k (1 : ℤ) = 2 := by
  rw [a, T_iterate_one_int]; exact T_one_int.2

/-- `p_n(1) = 2n`. -/
theorem p_one_int (n : ℕ) : p n (1 : ℤ) = 2 * n := by
  simp [p, a_one_int, mul_comm]

theorem a_neg_one_int (k : ℕ) : a k (-1 : ℤ) = 1 := by
  rw [a, T_iterate_neg_one_int]; exact T_neg_one_int.2

theorem p_neg_one_int (n : ℕ) : p n (-1 : ℤ) = n := by
  simp [p, a_neg_one_int]

theorem T_iterate_zero_succ_int (k : ℕ) : T^[k + 1] (0 : ℤ) = 1 := by
  rw [Function.iterate_succ_apply, T_zero_int, T_iterate_one_int]

/-! ### `lem:itemize_furthermore_itemize` -/

/-- `lem:itemize_furthermore_itemize`, first bullet, for `n ≥ 1` (false at `n = 0`:
`itemize_first_fails_at_zero`). -/
theorem itemize_first {x : ℤ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) (h : T^[n] x ≤ x) :
    0 < ((p n x : ℕ) : ℝ) * log 2 - n * log 3 := by
  rw [log_identity_int hx.ne' n]
  have hxn : (0 : ℝ) < ((T^[n] x : ℤ) : ℝ) := by exact_mod_cast T_iterate_pos_int hx n
  have h1 : 0 ≤ log |(x : ℝ)| - log |((T^[n] x : ℤ) : ℝ)| := by
    have : ((T^[n] x : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
    rw [abs_of_pos hxn, abs_of_pos (by exact_mod_cast hx)]
    linarith [Real.log_le_log hxn this]
  have h2 : 0 < ∑ k ∈ range n, log (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) := by
    refine sum_pos (fun k _ => Real.log_pos ?_) (nonempty_range_iff.2 (by omega))
    have : (0 : ℝ) < ((T^[k] x : ℤ) : ℝ) := by exact_mod_cast T_iterate_pos_int hx k
    have : 0 < 1 / (3 * ((T^[k] x : ℤ) : ℝ)) := by positivity
    linarith
  linarith

/-- `lem:itemize_furthermore_itemize`, second bullet, in its true form: the bound
`n log(1 + 1/(3x))` (the printed `n log(1 + 1/x)` fails at `x = 1`), the hypothesis only for `k ≤ n`. -/
theorem itemize_second {x : ℤ} (hx : 0 < x) {n : ℕ} (h : ∀ k ≤ n, T^[k] x ≤ x) :
    n * log (1 + 1 / (3 * (x : ℝ))) ≤ ((p n x : ℕ) : ℝ) * log 2 - n * log 3 := by
  rw [log_identity_int hx.ne' n]
  have hxn : (0 : ℝ) < ((T^[n] x : ℤ) : ℝ) := by exact_mod_cast T_iterate_pos_int hx n
  have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have h1 : 0 ≤ log |(x : ℝ)| - log |((T^[n] x : ℤ) : ℝ)| := by
    have : ((T^[n] x : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h n le_rfl
    rw [abs_of_pos hxn, abs_of_pos hx']
    linarith [Real.log_le_log hxn this]
  have h2 : ∑ k ∈ range n, log (1 + 1 / (3 * (x : ℝ))) ≤
      ∑ k ∈ range n, log (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) := by
    refine sum_le_sum fun k hk => Real.log_le_log (by positivity) ?_
    have hk0 : (0 : ℝ) < ((T^[k] x : ℤ) : ℝ) := by exact_mod_cast T_iterate_pos_int hx k
    have hkx : ((T^[k] x : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h k (mem_range.1 hk).le
    have : 1 / (3 * (x : ℝ)) ≤ 1 / (3 * ((T^[k] x : ℤ) : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  rw [sum_const, card_range, nsmul_eq_mul] at h2
  linarith

/-- The lower bound of `itemize_second` is attained at `x = 1`, for every `n`: the constant `1/3` is
sharp. -/
theorem itemize_second_sharp (n : ℕ) :
    ((p n (1 : ℤ) : ℕ) : ℝ) * log 2 - n * log 3 = n * log (1 + 1 / (3 * ((1 : ℤ) : ℝ))) := by
  rw [p_one_int]
  have : (1 : ℝ) + 1 / (3 * ((1 : ℤ) : ℝ)) = 2 ^ 2 / 3 := by norm_num
  rw [this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  ring

/-- The first bullet, as printed, fails at `n = 0` for every `x`: it asks `0 > 0`. -/
theorem itemize_first_fails_at_zero (x : ℤ) :
    T^[0] x ≤ x ∧ ¬ 0 < ((p 0 x : ℕ) : ℝ) * log 2 - ((0 : ℕ) : ℝ) * log 3 := by
  simp [p_zero]

/-- The first bullet of `lem:itemize_furthermore_itemize`, as printed, is false. -/
theorem itemize_first_printed_false :
    ¬ ∀ x : ℕ, 0 < x → ∀ n : ℕ, T^[n] (x : ℤ) ≤ x →
      0 < ((p n (x : ℤ) : ℕ) : ℝ) * log 2 - n * log 3 := by
  intro h
  exact (itemize_first_fails_at_zero (1 : ℤ)).2 (by exact_mod_cast h 1 one_pos 0 le_rfl)

/-- At `x = 1` the printed second bullet fails for every `n ≥ 1`: `Tᵏ(1) = 1 ≤ 1` for all `k`, and
`p_n(1) log 2 - n log 3 = n log(4/3) < n log 2 = n log(1 + 1/1)`. -/
theorem itemize_second_fails_at_one {n : ℕ} (hn : 1 ≤ n) :
    (∀ k : ℕ, T^[k] (1 : ℤ) ≤ 1) ∧
      ((p n (1 : ℤ) : ℕ) : ℝ) * log 2 - n * log 3 < n * log (1 + 1 / ((1 : ℤ) : ℝ)) := by
  refine ⟨fun k => (T_iterate_one_int k).le, ?_⟩
  rw [p_one_int]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h23 : log 2 < log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  push_cast
  norm_num
  nlinarith [mul_lt_mul_of_pos_left h23 hn']

/-- The second bullet of `lem:itemize_furthermore_itemize`, as printed, is false (at `x = 1`, `n = 1`). -/
theorem itemize_second_printed_false :
    ¬ ∀ x : ℕ, 0 < x → (∀ n : ℕ, T^[n] (x : ℤ) ≤ x) →
      ∀ n : ℕ, n * log (1 + 1 / (x : ℝ)) ≤ ((p n (x : ℤ) : ℕ) : ℝ) * log 2 - n * log 3 := by
  intro h
  have h1 := h 1 one_pos (fun n => by rw [Nat.cast_one, T_iterate_one_int]) 1
  simp only [Nat.cast_one, p_one_int] at h1
  norm_num at h1
  have : log 2 < log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ### Two lines of the printed proof of `lem:one_has` -/

/-- `syracuse.tex:119` as printed (`e^{p_n log 2 - n log 3} Tⁿ(x) - x = ∑_{k<n} e^{p_k log 2 - k log 3}`)
fails at `x = 1`, `n = 1`: the left side is `1/3`, the right side `1`. -/
theorem one_has_proof_l119_false :
    exp (((p 1 (1 : ℤ) : ℕ) : ℝ) * log 2 - (1 : ℕ) * log 3) * ((T^[1] (1 : ℤ) : ℤ) : ℝ) - ((1 : ℤ) : ℝ) ≠
      ∑ k ∈ range 1, exp (((p k (1 : ℤ) : ℕ) : ℝ) * log 2 - k * log 3) := by
  rw [p_one_int, T_iterate_one_int]
  simp only [sum_range_one, p_zero]
  norm_num
  rw [Real.exp_sub, show 2 * log 2 = log ((2 : ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  norm_num

/-- `syracuse.tex:124` as printed (`e^{p_n log 2 - n log 3} ≤ (1 + 1/x)ⁿ`) fails at `x = -1`, `n = 1`,
although `x = -1` satisfies the hypothesis of `lem:one_has` (`|Tⁿ(-1)| = 1`). -/
theorem one_has_proof_l124_false :
    (∀ n : ℕ, |(-1 : ℤ)| ≤ |T^[n] (-1 : ℤ)|) ∧
      ¬ exp (((p 1 (-1 : ℤ) : ℕ) : ℝ) * log 2 - (1 : ℕ) * log 3) ≤ (1 + 1 / ((-1 : ℤ) : ℝ)) ^ 1 := by
  refine ⟨fun n => by rw [T_iterate_neg_one_int], ?_⟩
  rw [p_neg_one_int]
  norm_num
  exact Real.exp_pos _

/-! ### `cor:corollary_2` -/

/-- A divergent orbit does not start at `0` (`T(0) = 1 = T(1)`). -/
theorem ne_zero_of_tendsto_T_iterate {x : ℤ} (h : Tendsto (fun n : ℕ => T^[n] x) atTop atTop) : x ≠ 0 := by
  rintro rfl
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually_ge_atTop 2)
  have := hN (N + 1) (by omega)
  rw [T_iterate_zero_succ_int] at this
  omega

/-- `cor:corollary_2`, the `ε` form: if `Tⁿ(x) → +∞`, then for every `ε > 0`, eventually
`p_n(x)/n ≤ log₂ 3 + ε`. -/
theorem corollary_2_eventually {x : ℤ} (h : Tendsto (fun n : ℕ => T^[n] x) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, ((p n x : ℕ) : ℝ) / n ≤ logb 2 3 + ε := by
  have hx := ne_zero_of_tendsto_T_iterate h
  have hyt : Tendsto (fun k : ℕ => ((T^[k] x : ℤ) : ℝ)) atTop atTop :=
    tendsto_intCast_atTop_iff.2 h
  have hc : Tendsto (fun k : ℕ => 1 / (3 * ((T^[k] x : ℤ) : ℝ))) atTop (nhds 0) := by
    have := tendsto_inv_atTop_zero.comp (hyt.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
    simpa [one_div, Function.comp_def] using this
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (n⁻¹ : ℝ) * ∑ k ∈ range n, 1 / (3 * ((T^[k] x : ℤ) : ℝ)) < ε * log 2 :=
    hc.cesaro.eventually (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ n : ℕ in atTop, |x| ≤ T^[n] x := h.eventually_ge_atTop |x|
  filter_upwards [hev1, hev2, eventually_ge_atTop 1] with n h1 h2 hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hid := log_identity_int hx n
  have hA : log |(x : ℝ)| - log |((T^[n] x : ℤ) : ℝ)| ≤ 0 := by
    have hx' : (0 : ℝ) < |(x : ℝ)| := by positivity
    have h2' : |(x : ℝ)| ≤ |((T^[n] x : ℤ) : ℝ)| := by
      have : |(x : ℝ)| ≤ ((T^[n] x : ℤ) : ℝ) := by exact_mod_cast h2
      exact this.trans (le_abs_self _)
    linarith [Real.log_le_log hx' h2']
  have hB : ∑ k ∈ range n, log (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) ≤
      ∑ k ∈ range n, 1 / (3 * ((T^[k] x : ℤ) : ℝ)) :=
    sum_le_sum fun k _ => by
      have := Real.log_le_sub_one_of_pos (one_add_one_div_three_mul_pos (T_iterate_ne_zero_int hx k))
      linarith
  have hC : ∑ k ∈ range n, 1 / (3 * ((T^[k] x : ℤ) : ℝ)) < n * (ε * log 2) := by
    rwa [inv_mul_lt_iff₀ hn'] at h1
  have hE : (logb 2 3 + ε) * n * log 2 = n * log 3 + n * (ε * log 2) := by
    rw [Real.logb]; field_simp
  have key : ((p n x : ℕ) : ℝ) * log 2 ≤ (logb 2 3 + ε) * n * log 2 := by
    rw [hE]; linarith
  rw [div_le_iff₀ hn']
  exact le_of_mul_le_mul_right key hlog2

/-- **`cor:corollary_2`** (`syracuse.tex:140`): if `Tⁿ(x) → +∞` then `limsup p_n(x)/n ≤ log₂ 3`, for
every `x ∈ ℤ` (the paper's `x ∈ ℕ` included). The `limsup` is taken in `ℝ`; the conclusion also
states that `p_n(x)/n` is bounded above, so it is the true `limsup`, not a junk value. -/
theorem corollary_2 {x : ℤ} (h : Tendsto (fun n : ℕ => T^[n] x) atTop atTop) :
    IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => ((p n x : ℕ) : ℝ) / n) ∧
      limsup (fun n : ℕ => ((p n x : ℕ) : ℝ) / n) atTop ≤ logb 2 3 := by
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => ((p n x : ℕ) : ℝ) / n) :=
    isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  refine ⟨isBoundedUnder_of_eventually_le (corollary_2_eventually h one_pos), ?_⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact limsup_le_of_le hcob (corollary_2_eventually h hε)

/-! ### `cor:bounds` -/

/-- `0` is on no cycle. -/
theorem ne_zero_of_T_cycle_int {x : ℤ} {n : ℕ} (hn : 1 ≤ n) (hcyc : T^[n] x = x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [T_iterate_zero_succ_int] at hcyc
  exact one_ne_zero hcyc

/-- On a cycle, `min_k Tᵏ(x)` and `max_k Tᵏ(x)` exist. -/
theorem exists_isLeast_isGreatest_of_cycle {x : ℤ} {n : ℕ} (hn : 1 ≤ n) (hcyc : T^[n] x = x) :
    ∃ m M : ℤ, IsLeast (Set.range fun k : ℕ => T^[k] x) m ∧
      IsGreatest (Set.range fun k : ℕ => T^[k] x) M := by
  have hper : Function.IsPeriodicPt T n x := hcyc
  set S : Finset ℤ := (range n).image fun k => T^[k] x with hSdef
  have hS : (S : Set ℤ) = Set.range fun k : ℕ => T^[k] x := by
    ext y
    simp only [S, coe_image, coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range]
    constructor
    · rintro ⟨k, -, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k % n, Nat.mod_lt _ (by omega), hper.iterate_mod_apply k⟩
  have hne : S.Nonempty := (nonempty_range_iff.2 (by omega)).image _
  exact ⟨S.min' hne, S.max' hne, hS ▸ S.isLeast_min' hne, hS ▸ S.isGreatest_max' hne⟩

/-- On a cycle, `p_n(x) log 2 - n log 3 = ∑_{k<n} log(1 + 1/(3Tᵏ(x)))`. -/
theorem cycle_log_identity {x : ℤ} {n : ℕ} (hn : 1 ≤ n) (hcyc : T^[n] x = x) :
    ((p n x : ℕ) : ℝ) * log 2 - n * log 3 =
      ∑ k ∈ range n, log (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) := by
  rw [log_identity_int (ne_zero_of_T_cycle_int hn hcyc) n, hcyc]
  ring

/-- On a cycle, `p_n/n - log₂ 3 = (1/n) ∑_{k<n} log₂(1 + 1/(3Tᵏ(x)))`. -/
theorem cycle_mean {x : ℤ} {n : ℕ} (hn : 1 ≤ n) (hcyc : T^[n] x = x) :
    ((p n x : ℕ) : ℝ) / n - logb 2 3 =
      (1 / n) * ∑ k ∈ range n, logb 2 (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) := by
  have h := cycle_log_identity hn hcyc
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb]
  rw [← sum_div, ← h]
  field_simp

/-- `cor:bounds` in its true form, for every cycle of `ℤ*` (both signs):
`log₂(1 + 1/(3 max)) ≤ p_n/n - log₂ 3 ≤ log₂(1 + 1/(3 min))`. -/
theorem bounds {x : ℤ} {n : ℕ} (hn : 1 ≤ n) (hcyc : T^[n] x = x) {m M : ℤ}
    (hm : IsLeast (Set.range fun k : ℕ => T^[k] x) m)
    (hM : IsGreatest (Set.range fun k : ℕ => T^[k] x) M) :
    logb 2 (1 + 1 / (3 * (M : ℝ))) ≤ ((p n x : ℕ) : ℝ) / n - logb 2 3 ∧
      ((p n x : ℕ) : ℝ) / n - logb 2 3 ≤ logb 2 (1 + 1 / (3 * (m : ℝ))) := by
  have hx := ne_zero_of_T_cycle_int hn hcyc
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cycle_mean hn hcyc]
  obtain ⟨i, hi⟩ := hm.1
  obtain ⟨j, hj⟩ := hM.1
  simp only at hi hj
  have key : ∀ k, logb 2 (1 + 1 / (3 * (M : ℝ))) ≤ logb 2 (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) ∧
      logb 2 (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) ≤ logb 2 (1 + 1 / (3 * (m : ℝ))) := by
    intro k
    have hmk : (m : ℝ) ≤ ((T^[k] x : ℤ) : ℝ) := by exact_mod_cast hm.2 ⟨k, rfl⟩
    have hkM : ((T^[k] x : ℤ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM.2 ⟨k, rfl⟩
    have hfM := one_add_one_div_three_mul_pos (hj ▸ T_iterate_ne_zero_int hx j)
    have hfk := one_add_one_div_three_mul_pos (T_iterate_ne_zero_int hx k)
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hMn : (M : ℝ) < 0 := by rw [← hj]; exact_mod_cast T_iterate_neg_int hneg j
      have hkn : ((T^[k] x : ℤ) : ℝ) < 0 := by exact_mod_cast T_iterate_neg_int hneg k
      constructor
      · refine Real.logb_le_logb_of_le (by norm_num) hfM ?_
        have := one_div_le_one_div_of_neg_of_le (a := 3 * ((T^[k] x : ℤ) : ℝ)) (b := 3 * (M : ℝ))
          (by linarith) (by linarith)
        linarith
      · refine Real.logb_le_logb_of_le (by norm_num) hfk ?_
        have := one_div_le_one_div_of_neg_of_le (a := 3 * (m : ℝ)) (b := 3 * ((T^[k] x : ℤ) : ℝ))
          (by linarith) (by linarith)
        linarith
    · have hmp : (0 : ℝ) < m := by rw [← hi]; exact_mod_cast T_iterate_pos_int hpos i
      have hkp : (0 : ℝ) < ((T^[k] x : ℤ) : ℝ) := by exact_mod_cast T_iterate_pos_int hpos k
      constructor
      · refine Real.logb_le_logb_of_le (by norm_num) hfM ?_
        have := one_div_le_one_div_of_le (a := 3 * ((T^[k] x : ℤ) : ℝ)) (b := 3 * (M : ℝ))
          (by linarith) (by linarith)
        linarith
      · refine Real.logb_le_logb_of_le (by norm_num) hfk ?_
        have := one_div_le_one_div_of_le (a := 3 * (m : ℝ)) (b := 3 * ((T^[k] x : ℤ) : ℝ))
          (by linarith) (by linarith)
        linarith
  have hlow := sum_le_sum fun k (_ : k ∈ range n) => (key k).1
  have hup := sum_le_sum fun k (_ : k ∈ range n) => (key k).2
  rw [sum_const, card_range, nsmul_eq_mul] at hlow hup
  constructor
  · calc logb 2 (1 + 1 / (3 * (M : ℝ))) = (1 / n) * (n * logb 2 (1 + 1 / (3 * (M : ℝ)))) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  · calc _ ≤ (1 / (n : ℝ)) * (n * logb 2 (1 + 1 / (3 * (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = _ := by field_simp

/-- `cor:bounds` as printed is false (at `x = 1`, `n = 1`, where `min = max = 1`: it asks
`log₂ 2 ≤ 2 - log₂ 3`). -/
theorem bounds_printed_false :
    ¬ ∀ (x : ℕ) (n : ℕ), 1 ≤ n → T^[n] (x : ℤ) = x → ∀ m M : ℤ,
      IsLeast (Set.range fun k : ℕ => T^[k] (x : ℤ)) m →
      IsGreatest (Set.range fun k : ℕ => T^[k] (x : ℤ)) M →
      logb 2 (1 + 1 / (m : ℝ)) ≤ ((p n (x : ℤ) : ℕ) : ℝ) / n - logb 2 3 ∧
        ((p n (x : ℤ) : ℕ) : ℝ) / n - logb 2 3 ≤ logb 2 (1 + 1 / (M : ℝ)) := by
  intro h
  have hrange : (Set.range fun k : ℕ => T^[k] (((1 : ℕ) : ℤ))) = {1} := by
    ext y
    simp [T_iterate_one_int]
  have h1 := (h 1 1 le_rfl (by simpa using T_iterate_one_int 1) 1 1 (by rw [hrange]; exact isLeast_singleton)
    (by rw [hrange]; exact isGreatest_singleton)).1
  simp only [Nat.cast_one, p_one_int] at h1
  norm_num at h1
  have h3 : 1 < logb 2 3 := by
    rw [Real.logb, one_lt_div (Real.log_pos (by norm_num))]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- The printed lower bound of `cor:bounds` fails on every positive cycle: by `bounds`, the
mean is at most `log₂(1 + 1/(3 min)) < log₂(1 + 1/min)`. -/
theorem bounds_printed_lower_false {x : ℤ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) (hcyc : T^[n] x = x)
    {m : ℤ} (hm : IsLeast (Set.range fun k : ℕ => T^[k] x) m) :
    ((p n x : ℕ) : ℝ) / n - logb 2 3 < logb 2 (1 + 1 / (m : ℝ)) := by
  obtain ⟨-, M, -, hM⟩ := exists_isLeast_isGreatest_of_cycle hn hcyc
  have hb := (bounds hn hcyc hm hM).2
  obtain ⟨i, hi⟩ := hm.1
  have hmp : (0 : ℝ) < m := by rw [← hi]; exact_mod_cast T_iterate_pos_int hx i
  refine hb.trans_lt (Real.logb_lt_logb (by norm_num) (by positivity) ?_)
  have : 1 / (3 * (m : ℝ)) < 1 / (m : ℝ) := one_div_lt_one_div_of_lt hmp (by linarith)
  linarith

end Syracuse
