import Syracuse.UpperBounds

/-!
# Syracuse § 3: `theo:steiner_2`, one descending index per period, and the paper's own steps

`theo:steiner_2` — `syracuse.tex:294` (proof l.297–303). Not marked. In the per-period reading (the
proof's, l.298) it is false over `ℤ` (the cycle `(−5, −7)`); read literally its hypothesis is never
met, so it holds vacuously. On positive cycles it rests
on two cited steps of l.302: the corollary to Matveev's theorem (`cor:property_defined_cycles_gcd`)
and a computer check. Both are T-syr-cited's question. Everything between those inputs is proved,
and the reduction to them is shown to be exact (SCOPE).

> **theo:steiner_2** (Steiner). Let $\Gamma$ be a Syracuse n-cycle.
> If $\#\D_\Gamma=1$ then $\Gamma = (\cdots,1,\cdots)$.
>
> *Proof.* Assume $\D=n\ZZ$, from the preceding corollary,
> $m = A_0 \wedge \Delta_{-1}$. We write $\alpha = a_0-1 = \frac{1}{2}(|a(\Gamma)|-n)$
> In particular we have~:
> $$\Delta_1 \sim_S  2^{\alpha}-1$$
> But since $2^\alpha = 2^{|\Gamma|-n}\leq 2^{|\Gamma|(1-\log_3(2))}$ the hypothesis to the
> corollary to Matveev Theorem are satisfied (effectively) and the finitely many cycle $\Gamma$
> such that $\#\D_\Gamma=1$ can be effectively determined. With the aid of a computer, one  can
> check that the only one is $(\cdots,1,\cdots)$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` a Syracuse `n`-cycle | ✓ `x : ℤ`, `0 < n`, `T^[n] x = x` (`n` need not be minimal); `a_i = a_i(x_0)` extended `n`-periodically to `ℤ`, i.e. any periodic `α` with `α k = a_k(x)` (OQ-68 (a)) |
| "`#𝒟_Γ = 1`" (l.295) | ⚠ a reading: per period, `#(𝒟 ∩ ⟦0, n−1⟧) = 1`. Every window gives the same count (`card_filter_desc_window`). The literal `encard` reading is vacuous (Finding 1) |
| "`Γ = (⋯,1,⋯)`" | read as "`1` is a term of the cycle", which is `x = 1` (`exists_iterate_eq_one_iff_of_cycle`) |
| the sign of `Γ` (OQ-63 (a)) | both: refuted over `ℤ` (Finding 2); for `x > 0`, reduced exactly to the cited steps; ⚠ strengthened in the true forms (`x > 0`, `n ≤ 100`, `n = 1`) |
| "Assume `𝒟 = nℤ`" (l.298) | ✓ the base point moves to the point after the descending index (`steiner_point`). The displays are stated for every `n`-periodic `α` with `𝒟 ∩ ⟦1, n−1⟧ = ∅` |
| `A_i` (OQ-43) | both readings: `Aun` (printed) and `AunAlt` |
| the index of `a_i` (OQ-63 (b)) | the displays on sequences need no convention. On a cycle both conventions are covered: `steiner_m_cycle` (l.62) and `steiner_m_cycle_shift` (l.71, the OQ-43 reading) |
| `∼_S` (l.301; OQ-68 (c)) | `SEquiv`, with the factor in `S` given explicitly (`steiner_delta`), so every reading of "up to a factor in `S`" is covered |
| `|a(Γ)|`, `|Γ|` (l.299, l.302) | read as `p_n(x_0) = ∑_{t<n} a_t`, the sum over one period (l.167 counts cycles by `(|Γ|, n)`) |
| the corollary to Matveev's theorem, the computer check (l.302) | neither is stated nor assumed. The bound the corollary consumes is proved. The theorem on positive cycles is shown equivalent to `SteinerArithStmt`, the statement these two steps settle. The check runs in the kernel for `n ≤ 100` |

## SCOPE (disclosed)

* **Finding 1 (l.295): the literal hypothesis `#𝒟_Γ = 1` is never met.** An `n`-periodic subset
  of `ℤ` is empty or infinite (`encard_descIdx_ne_one`), so the literal statement holds vacuously
  (`steinerTwoLiteral_vacuous`). The count is per period, as the proof's « Assume 𝒟 = nℤ » (l.298)
  and the `#(𝒟_Γ ∩ ⟦1, n⟧)` of l.306 read it.
* **Finding 2 (l.294–295): false over `ℤ` in the per-period reading.** The cycle `(−5, −7)` has `a = (1, 2)`, so one
  descending index per period, and no term is `1` (`steinerTwo_neg_five`, `steinerTwo_printed_false`).
  Whether § 3's cycles are positive is OQ-63 (a). Three true forms are proved: for `n = 1` over `ℤ`
  (`steinerTwo_period_one`); for `n ≤ 100` over `ℤ`, where the cycles are `(1)` and `(−5, −7)`
  (`steinerTwo_int_of_le`); for positive cycles with `n ≤ 100`, where the cycle is `(1)`
  (`steinerTwo_pos_of_le`).
* **The exact reduction.** Let `d` be the descending index and `y = T^{d+1}(x_0)`. Then
  `a_0(y) = ⋯ = a_{n−2}(y) = 1` and `a_{n−1}(y) = α + 1` (`steiner_point`), which is
  `theo:steiner`'s `∀ k < n, p_k(y) = k` (`p_eq_self_of_a_eq_one`). By `lem:base`, `p_n = n + α`,
  `y (2^{n+α} − 3ⁿ) = 3ⁿ − 2ⁿ` and `2^{n+α} − 3ⁿ ∣ 2^α − 1`, for either sign
  (`steiner_reduction`). For `y > 0` also `α ≥ 1` and `3ⁿ < 2^{n+α} ≤ 3ⁿ + 2^α − 1 < 2·3ⁿ`
  (`steiner_reduction_pos`, `steiner_cycle_pos`). Conversely, every solution with `α ≥ 1` is such a
  cycle (`steiner_cycle_of_dvd`). So `theo:steiner` (l.150), this theorem on positive cycles and
  `SteinerArithStmt` are equivalent (`steiner_iff_steinerTwoPos`, `steinerTwoPos_iff_arith`;
  `steiner_eq_one_of_arith`). This confirms the planner's (c).
* **Finding 3 (l.298, `m = A_0 ∧ Δ_{−1}`).** For every `n`-periodic `α ≥ 1` with `𝒟 ⊆ nℤ`, the
  common divisors of `A_0` and `Δ_{−1}` are those of all the `A_u`, for both readings
  (`steiner_gcd_alt_iff`, `steiner_gcd_aun_iff`). On a cycle, the OQ-43 reading gives
  `A'_0 ∧ Δ'_{−1} = |2^{p_n} − 3ⁿ|`, which is the printed `m` for `x > 0`, in both index
  conventions (`steiner_m_cycle`, `steiner_m_cycle_shift`). The printed `A_u^n` gives
  `A_0 ∧ Δ_{−1} = GCD(A_u)`, which is `2 |2^{p_n} − 3ⁿ|` when `n ≥ 2` and is never
  `2^{p_n} − 3ⁿ` (`steiner_m_cycle`, `gcd_Aun_of_cycle_of_asc`). In that reading `m` is even and does
  not divide the odd `2^α − 1`, although the bound below still holds.
* **Finding 4 (l.299; the planner's (a)): the `½` is spurious.** `|a(Γ)| = n + α`
  (`steiner_sum_eq`), so `α = |a(Γ)| − n`, as l.302 writes it. The printed `α = ½(|a(Γ)| − n)`
  fails whenever `a_0 > 1` (`steiner_alpha_half_false`).
* **l.301, `Δ_1 ∼_S 2^α − 1`: exact for `n ≥ 2`, both readings, at `i = 1` and `i = −1`.**
  `Δ'_1 = 2^{n−1}(2^α − 1)`, `Δ_1 = 3·2^{n−1}(2^α − 1)`, `Δ'_{−1} = 2·3^{n−2}(2^α − 1)` and
  `Δ_{−1} = 2·3^{n−1}(2^α − 1)` (`steiner_delta`, `steiner_delta_sEquiv`). **Finding 5: it fails
  for `n = 1`.** There every `Δ_i` is `0`, and the counterexample is the cycle `(1)` itself
  (`steiner_delta_period_one_false`). Through `lem:base`, `m ∣ 2^α − 1` still holds.
* **Finding 6 (l.302; the planner's (b)): the printed inequality is reversed.**
  `2^{|Γ|−n} ≤ 2^{|Γ|(1−log₃2)}` holds on a cycle of `ℤ` iff the cycle is negative, so it fails
  on every positive cycle (`steiner_printed_bound_iff`). What holds, from `2^{p_n} < 2·3ⁿ`, is
  `2^α < 2^{log₃2}·2^{|Γ|(1−log₃2)}` (`steiner_bound`).
* **The bound the corollary consumes** (l.162, effective, `ε = log₃2`). On a positive cycle with one
  descending index per period, `GCD(A'_u) = 2^{p_n} − 3ⁿ ≤ 2^α − 1 < 2^{log₃2}·2^{|Γ|(1−ε)}` and
  `GCD(A_u) ≤ 2^{α+1}`, twice that (`steiner_gcd_bound`). The hypothesis of the corollary holds
  with `C = 2^{1+log₃2}`, for both readings (`steiner_corollary_hypothesis`). The GCD over `i ∈ ℤ`
  is the GCD over one period.
* **The cited steps are not stated.** `SteinerArithStmt` is the arithmetic statement the two steps
  of l.302 are used to settle. It is defined only to state the equivalence, and it is neither
  assumed nor proved. `SteinerStmt` is `theo:steiner` (l.150), stated for the same purpose only.
  The computer check runs in the kernel (`decide`) for `n ≤ 100`, on both sides
  (`steinerArith_check_pos`, `steinerArith_check_neg`). This confirms the planner's numerics
  (`n < 400`, scripts not archived) in that range.
* **Non-vacuity** (`steiner_instances`): the cycle of `1` meets the hypotheses of the positive
  results. `(−5, −7)` read from `−7` meets those of the displays, and read from `−5` those of the
  reduction.
* `T`, `a`, `p` are the total maps of `Syracuse.Base`; over `ℤ` they are the paper's
  (`not_isUnit_three_int`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset

/-! ### The statement and its readings -/

/-- `theo:steiner_2` in the per-period reading (`#(𝒟_Γ ∩ ⟦0, n−1⟧) = 1`), over `ℤ`, with
`Γ = (⋯,1,⋯)` read as "`1` is a term of the cycle". -/
def SteinerTwoStmt : Prop :=
  ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
    (∀ k : ℕ, α k = a k x) → ((range n).filter (fun i : ℕ => 1 < α i)).card = 1 →
    ∃ k : ℕ, T^[k] x = 1

/-- `theo:steiner_2` in its literal reading: `#𝒟_Γ = 1` for the subset `𝒟_Γ ⊆ ℤ`. -/
def SteinerTwoLiteralStmt : Prop :=
  ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
    (∀ k : ℕ, α k = a k x) → (descIdx α).encard = 1 → ∃ k : ℕ, T^[k] x = 1

/-- The per-period reading on the positive cycles (`x > 0`). -/
def SteinerTwoPosStmt : Prop :=
  ∀ x : ℤ, 0 < x → ∀ n : ℕ, 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
    (∀ k : ℕ, α k = a k x) → ((range n).filter (fun i : ℕ => 1 < α i)).card = 1 →
    ∃ k : ℕ, T^[k] x = 1

/-- The statement of `theo:steiner` (`syracuse.tex:150`, cited, T-syr-cited's question), as
printed, for the equivalence with `SteinerTwoPosStmt` only. Neither assumed nor proved here. -/
def SteinerStmt : Prop :=
  ∀ x : ℤ, 0 < x → (∃ n : ℕ, 0 < n ∧ T^[n] x = x ∧ ∀ k < n, p k x = k) → x = 1

/-- The arithmetic statement the proof of l.302 settles by its two cited steps: the only
`n ≥ 1`, `e` with `3ⁿ < 2^{n+e}` and `2^{n+e} − 3ⁿ ∣ 2^e − 1` are `n = e = 1`. Neither assumed nor
proved here; equivalent to `SteinerTwoPosStmt` (`steinerTwoPos_iff_arith`). -/
def SteinerArithStmt : Prop :=
  ∀ n e : ℕ, 0 < n → (3 : ℤ) ^ n < 2 ^ (n + e) → (2 : ℤ) ^ (n + e) - 3 ^ n ∣ 2 ^ e - 1 →
    n = 1 ∧ e = 1

/-! ### `Γ = (⋯,1,⋯)`, and the literal count -/

/-- On a cycle, `1` is a term iff `x = 1` (`T(1) = 1`). -/
theorem exists_iterate_eq_one_iff_of_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) :
    (∃ k : ℕ, T^[k] x = 1) ↔ x = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    have hq : T^[n * k] x = x := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hx k
    have hle : k ≤ n * k := Nat.le_mul_of_pos_left k hn
    rw [← hq, show n * k = (n * k - k) + k by omega, Function.iterate_add_apply, hk,
      T_iterate_one_int]
  · rintro rfl
    exact ⟨0, rfl⟩

/-- The count per period does not depend on the window: `⟦c, c + n − 1⟧` for every `c ∈ ℤ`, so
`⟦0, n−1⟧` here and `⟦1, n⟧` (`theo:syracuse_cycle`, l.306) give the same `#(𝒟_Γ ∩ ·)`. -/
theorem card_filter_desc_window {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) (c : ℤ) :
    ((range n).filter (fun t : ℕ => 1 < α (c + t))).card =
      ((range n).filter (fun i : ℕ => 1 < α i)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  have hg : Function.Periodic (fun i : ℤ => if 1 < α i then 1 else 0) n := by
    intro i
    simp only [hper i]
  exact sum_range_periodic hg c

/-- The literal count: an `n`-periodic subset of `ℤ` (`n ≥ 1`) is empty or infinite. -/
theorem encard_descIdx_ne_one {α : ℤ → ℕ} {n : ℕ} (hn : 0 < n) (hper : Function.Periodic α n) :
    (descIdx α).encard ≠ 1 := by
  intro h
  obtain ⟨i, hi⟩ := Set.encard_eq_one.1 h
  have hi' : i ∈ descIdx α := by rw [hi]; exact Set.mem_singleton i
  have hin : i + n ∈ descIdx α := by
    show 1 < α (i + n)
    rw [hper]
    exact hi'
  rw [hi, Set.mem_singleton_iff] at hin
  omega

/-- **Finding 1.** The literal reading holds vacuously: its hypothesis is never met. -/
theorem steinerTwoLiteral_vacuous : SteinerTwoLiteralStmt := by
  intro x n hn _ α hper _ h
  exact absurd h (encard_descIdx_ne_one hn hper)

/-! ### The refutation over `ℤ`: the cycle `(−5, −7)` -/

/-- The cycle `(−5, −7)`: one descending index per period (`a = (1, 2)`), and `1` is not a term. -/
theorem steinerTwo_neg_five :
    T^[2] (-5 : ℤ) = -5 ∧ ((range 2).filter (fun i : ℕ => 1 < seq12 i)).card = 1 ∧
      ∀ k : ℕ, T^[k] (-5 : ℤ) ≠ 1 := by
  refine ⟨cycle_neg_five.1, by decide, fun k hk => ?_⟩
  have := T_iterate_neg_int (show (-5 : ℤ) < 0 by norm_num) k
  rw [hk] at this
  norm_num at this

/-- **Finding 2.** `theo:steiner_2` in the per-period reading is false over `ℤ`. -/
theorem steinerTwo_printed_false : ¬ SteinerTwoStmt := by
  intro h
  obtain ⟨hx, hc, hne⟩ := steinerTwo_neg_five
  obtain ⟨k, hk⟩ := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a hc
  exact hne k hk

/-! ### The point after the descending index -/

/-- One descending index `d` per period: the point `y = T^{d+1}(x)` has `a_0(y) = ⋯ = a_{n−2}(y) = 1`
and `a_{n−1}(y) > 1`, it is on the cycle, and `x = T^{n−1−d}(y)`. -/
theorem steiner_point {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (h1 : ((range n).filter (fun i : ℕ => 1 < α i)).card = 1) :
    ∃ d : ℕ, d < n ∧ 1 < α d ∧ (∀ i : ℕ, i < n → i ≠ d → α i = 1) ∧
      T^[n] (T^[d + 1] x) = T^[d + 1] x ∧ (∀ k : ℕ, k < n - 1 → a k (T^[d + 1] x) = 1) ∧
      1 < a (n - 1) (T^[d + 1] x) ∧ T^[n - 1 - d] (T^[d + 1] x) = x := by
  have hpos := one_le_of_cycle hn hx hper hα
  obtain ⟨d, hd⟩ := Finset.card_eq_one.1 h1
  have hdmem : d ∈ (range n).filter (fun i : ℕ => 1 < α i) := by rw [hd]; exact mem_singleton_self d
  rw [Finset.mem_filter, Finset.mem_range] at hdmem
  have hother : ∀ i : ℕ, i < n → i ≠ d → α i = 1 := by
    intro i hi hid
    have hnot : i ∉ (range n).filter (fun i : ℕ => 1 < α i) := by
      rw [hd, Finset.mem_singleton]
      exact hid
    rw [Finset.mem_filter, Finset.mem_range, not_and] at hnot
    have := hnot hi
    have := hpos i
    omega
  have hperN : ∀ m : ℕ, α ((m + n : ℕ) : ℤ) = α m := by
    intro m
    push_cast
    exact hper m
  refine ⟨d, hdmem.1, hdmem.2, hother, ?_, ?_, ?_, ?_⟩
  · rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hx]
  · intro k hk
    rw [a_iterate, ← hα]
    by_cases hlt : k + (d + 1) < n
    · exact hother _ hlt (by omega)
    · have e : k + (d + 1) = (k + (d + 1) - n) + n := by omega
      rw [e, hperN]
      exact hother _ (by omega) (by omega)
  · rw [a_iterate, ← hα, show n - 1 + (d + 1) = d + n by omega, hperN]
    exact hdmem.2
  · rw [← Function.iterate_add_apply, show n - 1 - d + (d + 1) = n by omega, hx]

/-! ### The exact reduction -/

/-- **The exact reduction**, over `ℤ`, any sign: on an `n`-cycle with `a_0 = ⋯ = a_{n−2} = 1` and
`a_{n−1} = e + 1` (`theo:steiner`'s hypothesis), `p_n = n + e`, `y (2^{n+e} − 3ⁿ) = 3ⁿ − 2ⁿ`, and
`2^{n+e} − 3ⁿ ∣ 2^e − 1`. -/
theorem steiner_reduction {y : ℤ} {n e : ℕ} (hn : 0 < n) (hy : T^[n] y = y)
    (h1 : ∀ k : ℕ, k < n - 1 → a k y = 1) (he : a (n - 1) y = e + 1) :
    p n y = n + e ∧ y * ((2 : ℤ) ^ (n + e) - 3 ^ n) = 3 ^ n - 2 ^ n ∧
      (2 : ℤ) ^ (n + e) - 3 ^ n ∣ 2 ^ e - 1 := by
  have hp : ∀ k : ℕ, k ≤ n - 1 → p k y = k := by
    intro k
    induction k with
    | zero => intro _; exact p_zero y
    | succ k ih =>
      intro hk
      rw [p_succ', ih (by omega), h1 k (by omega)]
  have hpn : p n y = n + e := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [p_succ', hp m (by omega), show m + 1 - 1 = m by omega] at *
    rw [he]
    ring
  have hb := base y n
  rw [hy, hpn] at hb
  have hs : ∑ k ∈ range n, (2 : ℤ) ^ p k y * 3 ^ (n - 1 - k) =
      ∑ k ∈ range n, (2 : ℤ) ^ k * 3 ^ (n - 1 - k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hp k (by have := Finset.mem_range.1 hk; omega)]
  have hg := geom_sum₂_mul (2 : ℤ) 3 n
  have hid : y * ((2 : ℤ) ^ (n + e) - 3 ^ n) = 3 ^ n - 2 ^ n := by
    rw [hs] at hb
    linear_combination hb - hg
  refine ⟨hpn, hid, ?_⟩
  have hodd : ¬ (2 : ℤ) ∣ (2 : ℤ) ^ (n + e) - 3 ^ n := by
    intro h2
    have h3 : (2 : ℤ) ∣ (2 : ℤ) ^ (n + e) := dvd_pow_self 2 (by omega)
    have : (2 : ℤ) ∣ 3 ^ n := by
      have := dvd_sub h3 h2
      rwa [sub_sub_cancel] at this
    exact absurd (Int.prime_two.dvd_of_dvd_pow this) (by norm_num)
  have hco : IsCoprime ((2 : ℤ) ^ (n + e) - 3 ^ n) (2 ^ n) :=
    IsCoprime.pow_right ((Int.prime_two.coprime_iff_not_dvd).2 hodd).symm
  refine hco.dvd_of_dvd_mul_left ?_
  have e1 : (2 : ℤ) ^ n * (2 ^ e - 1) = y * ((2 : ℤ) ^ (n + e) - 3 ^ n) + ((2 : ℤ) ^ (n + e) - 3 ^ n) := by
    rw [hid, pow_add]
    ring
  rw [e1]
  exact dvd_add (dvd_mul_left _ _) dvd_rfl

/-- **The exact reduction, `y > 0`**: `e ≥ 1`, `3ⁿ < 2^{n+e} ≤ 3ⁿ + 2^e − 1`, hence `2^{n+e} < 2·3ⁿ`. -/
theorem steiner_reduction_pos {y : ℤ} (hy0 : 0 < y) {n e : ℕ} (hn : 0 < n) (hy : T^[n] y = y)
    (h1 : ∀ k : ℕ, k < n - 1 → a k y = 1) (he : a (n - 1) y = e + 1) :
    1 ≤ e ∧ (3 : ℤ) ^ n < 2 ^ (n + e) ∧ (2 : ℤ) ^ (n + e) ≤ 3 ^ n + 2 ^ e - 1 ∧
      (2 : ℤ) ^ (n + e) < 2 * 3 ^ n := by
  obtain ⟨hpn, hid, hdvd⟩ := steiner_reduction hn hy h1 he
  have hpos := two_pow_p_sub_three_pow_mul_pos hn hy
  rw [hpn] at hpos
  have hD : 0 < (2 : ℤ) ^ (n + e) - 3 ^ n := pos_of_mul_pos_left hpos hy0.le
  have h23 : (2 : ℤ) ^ n ≤ 3 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have he1 : 1 ≤ e := by
    by_contra h0
    have : e = 0 := by omega
    subst this
    simp only [add_zero] at hD
    linarith
  have h2e : (2 : ℤ) ≤ 2 ^ e := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he1
  have hle : (2 : ℤ) ^ (n + e) - 3 ^ n ≤ 2 ^ e - 1 := Int.le_of_dvd (by linarith) hdvd
  have h2n : (2 : ℤ) ≤ 2 ^ n := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  refine ⟨he1, by linarith, by linarith, ?_⟩
  rw [pow_add] at hle ⊢
  nlinarith

/-- **`theo:steiner_2` for `n = 1`, over `ℤ`, any sign**: a fixed point with `a_0 > 1` is `1`. -/
theorem steinerTwo_period_one {x : ℤ} (hx : T^[1] x = x) {α : ℤ → ℕ}
    (hα : ∀ k : ℕ, α k = a k x) (h1 : ((range 1).filter (fun i : ℕ => 1 < α i)).card = 1) :
    x = 1 := by
  have hc : 1 < α 0 := by
    have hmem : (0 : ℕ) ∈ (range 1).filter (fun i : ℕ => 1 < α i) := by
      obtain ⟨d, hd⟩ := Finset.card_eq_one.1 h1
      have hd' : d ∈ (range 1).filter (fun i : ℕ => 1 < α i) := by rw [hd]; exact mem_singleton_self d
      have : d = 0 := by have := (Finset.mem_range.1 (Finset.mem_filter.1 hd').1); omega
      rwa [this] at hd'
    exact_mod_cast (Finset.mem_filter.1 hmem).2
  have ha0 : a 0 x = (a 0 x - 1) + 1 := by have := hα 0; push_cast at this; omega
  obtain ⟨-, hid, -⟩ := steiner_reduction (e := a 0 x - 1) one_pos hx (fun k hk => by omega) ha0
  have h1' : x * ((2 : ℤ) ^ (1 + (a 0 x - 1)) - 3 ^ 1) = 1 := by rw [hid]; norm_num
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1' with h | h
  · exact h
  · exfalso
    have := hα 0
    push_cast at this
    rw [h, a_neg_one_int] at this
    omega

/-- `p_n` is the same at every point of an `n`-cycle. -/
theorem p_iterate_eq_of_cycle {x : ℤ} {n : ℕ} (hx : T^[n] x = x) (u : ℕ) : p n (T^[u] x) = p n x := by
  have h1 := p_add u n x
  have h2 := p_add n u x
  rw [hx, add_comm n u] at h2
  omega

/-- Steiner's hypothesis `∀ k < n, p_k = k` (l.152) is `a_0 = ⋯ = a_{n−2} = 1`. -/
theorem p_eq_self_of_a_eq_one {y : ℤ} {n : ℕ} (h1 : ∀ k : ℕ, k < n - 1 → a k y = 1) :
    ∀ k : ℕ, k < n → p k y = k := by
  intro k
  induction k with
  | zero => intro _; exact p_zero y
  | succ k ih =>
    intro hk
    rw [p_succ', ih (by omega), h1 k (by omega)]

/-- The reduction on a positive cycle with one descending index per period, in the cycle's own
terms (`|Γ| = p_n(x)`, `α = p_n(x) − n`). -/
theorem steiner_cycle_pos {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (h1 : ((range n).filter (fun i : ℕ => 1 < α i)).card = 1) :
    n + 1 ≤ p n x ∧ (2 : ℤ) ^ p n x - 3 ^ n ∣ 2 ^ (p n x - n) - 1 ∧ (3 : ℤ) ^ n < 2 ^ p n x ∧
      (2 : ℤ) ^ p n x ≤ 3 ^ n + 2 ^ (p n x - n) - 1 ∧ (2 : ℤ) ^ p n x < 2 * 3 ^ n := by
  obtain ⟨d, hd, -, -, hy, h1y, hgt, -⟩ := steiner_point hn hx hper hα h1
  have hey : a (n - 1) (T^[d + 1] x) = (a (n - 1) (T^[d + 1] x) - 1) + 1 := by omega
  have hy0 : 0 < T^[d + 1] x := T_iterate_pos_int hx0 _
  obtain ⟨hpn, -, hdvd⟩ := steiner_reduction hn hy h1y hey
  obtain ⟨he1, h3, hle, h2⟩ := steiner_reduction_pos hy0 hn hy h1y hey
  rw [p_iterate_eq_of_cycle hx] at hpn
  rw [hpn, show n + (a (n - 1) (T^[d + 1] x) - 1) - n = a (n - 1) (T^[d + 1] x) - 1 by omega]
  exact ⟨by omega, hdvd, h3, hle, h2⟩

/-! ### The reduction is exact: three equivalent statements -/

/-- The converse construction: every solution `(n, e)`, `e ≥ 1`, of `2^{n+e} − 3ⁿ ∣ 2^e − 1` (any
sign) is an `n`-cycle of `ℤ` with `a_0 = ⋯ = a_{n−2} = 1`, `a_{n−1} = e + 1`. -/
theorem steiner_cycle_of_dvd {n e : ℕ} (hn : 0 < n) (he : 1 ≤ e)
    (hD : (2 : ℤ) ^ (n + e) - 3 ^ n ∣ 2 ^ e - 1) :
    ∃ y : ℤ, y * ((2 : ℤ) ^ (n + e) - 3 ^ n) = 3 ^ n - 2 ^ n ∧ T^[n] y = y ∧
      (∀ k : ℕ, k < n - 1 → a k y = 1) ∧ a (n - 1) y = e + 1 := by
  set D : ℤ := (2 : ℤ) ^ (n + e) - 3 ^ n with hDdef
  -- the sequence `(1, …, 1, e + 1)`, descending at `n − 1`
  set β : ℤ → ℕ := fun i => if (i + 1) % (n : ℤ) = 0 then e + 1 else 1 with hβ
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hper : Function.Periodic β n := by
    intro i
    simp only [hβ]
    rw [show i + (n : ℤ) + 1 = (i + 1) + n by ring, Int.add_emod_right]
  have hpos : ∀ k, 1 ≤ β k := by
    intro k
    simp only [hβ]
    split_ifs <;> omega
  have hlow : ∀ t : ℕ, t < n - 1 → β t = 1 := by
    intro t ht
    simp only [hβ]
    rw [if_neg]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  have htop : β ((n - 1 : ℕ) : ℤ) = e + 1 := by
    simp only [hβ]
    rw [if_pos]
    rw [show ((n - 1 : ℕ) : ℤ) + 1 = n by push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring]
    exact Int.emod_self
  have hP : ∑ t ∈ range n, β t = n + e := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun t ht => hlow t (by
      have := Finset.mem_range.1 ht; omega))]
    rw [show m + 1 - 1 = m by omega] at htop
    rw [htop]
    simp
    ring
  have hA0 : (AunAlt n 0 β : ℤ) = 3 ^ n - 2 ^ n := by
    rw [AunAlt_eq_sum]
    push_cast
    have e1 : ∀ k ∈ range n, (3 : ℤ) ^ k * 2 ^ (∑ t ∈ range (n - 1 - k), β (0 + t)) =
        3 ^ k * 2 ^ (n - 1 - k) := by
      intro k hk
      have hsum : ∑ t ∈ range (n - 1 - k), β (0 + (t : ℤ)) = ∑ t ∈ range (n - 1 - k), 1 :=
        Finset.sum_congr rfl (fun t ht => by
          rw [zero_add]; exact hlow t (by have := Finset.mem_range.1 ht; omega))
      rw [hsum]
      simp
    rw [Finset.sum_congr rfl e1]
    have := geom_sum₂_mul (3 : ℤ) 2 n
    linear_combination this
  have hδ : D ∣ (2 : ℤ) ^ (∑ t ∈ range n, β t) - 3 ^ n := by rw [hP]
  have hD0 : D ∣ (AunAlt n 0 β : ℤ) := by
    rw [hA0]
    have e2 : (3 : ℤ) ^ n - 2 ^ n = 2 ^ n * (2 ^ e - 1) - D := by rw [hDdef, pow_add]; ring
    rw [e2]
    exact dvd_sub (dvd_mul_of_dvd_right hD _) dvd_rfl
  have hall := dvd_AunAlt_of_dvd_delta hpos hn hper hδ hD0
  have hDodd : Odd D := by
    have := (delta_odd_not_three_dvd hpos hn).1
    rwa [hP] at this
  have hDne : D ≠ 0 := fun h => by rw [h] at hDodd; exact absurd hDodd (by decide)
  -- the points `X_u = A'_u / D`
  set X : ℤ → ℤ := fun u => (AunAlt n u β : ℤ) / D with hX
  have hXD : ∀ u, X u * D = AunAlt n u β := fun u => Int.ediv_mul_cancel (hall u)
  have hXodd : ∀ u, Odd (X u) := by
    intro u
    have h : Odd ((AunAlt n u β : ℕ) : ℤ) := (AunAlt_odd hpos hn u).natCast
    rw [← hXD u] at h
    exact (Int.odd_mul.1 h).1
  have hstep : ∀ u, (2 : ℤ) ^ β u * X (u + 1) = 3 * X u + 1 := by
    intro u
    have e3 := two_pow_mul_AunAlt_succ hper u
    rw [hP, ← hDdef, ← hXD (u + 1), ← hXD u] at e3
    apply mul_right_cancel₀ hDne
    linear_combination e3
  have hT : ∀ u, T (X u) = X (u + 1) ∧ v2 (3 * X u + 1) = β u := by
    intro u
    obtain ⟨h1, h2⟩ := T_unique (A := ℤ) two_ne_zero (hXodd (u + 1)) (hstep u)
    exact ⟨h2, h1.symm⟩
  have hiter : ∀ k : ℕ, T^[k] (X 0) = X k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, (hT k).1]
      push_cast
      rfl
  have ha : ∀ k : ℕ, a k (X 0) = β k := by
    intro k
    rw [a, hiter]
    exact (hT k).2
  refine ⟨X 0, by rw [hXD, hA0], ?_, fun k hk => by rw [ha]; exact hlow k hk, by rw [ha]; exact htop⟩
  rw [hiter]
  simp only [hX]
  have hp0 := (AunAlt_periodic hper) 0
  simp only at hp0
  rw [show ((n : ℕ) : ℤ) = 0 + n by ring, hp0]

/-- The paper's steps on a positive cycle with one descending index per period: if the arithmetic
statement holds at its `n`, then `x = 1`. -/
theorem steiner_eq_one_of_arith {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (h1 : ((range n).filter (fun i : ℕ => 1 < α i)).card = 1)
    (hA : ∀ e : ℕ, (3 : ℤ) ^ n < 2 ^ (n + e) → (2 : ℤ) ^ (n + e) - 3 ^ n ∣ 2 ^ e - 1 →
      n = 1 ∧ e = 1) : x = 1 := by
  obtain ⟨d, hd, -, -, hy, h1y, hgt, hback⟩ := steiner_point hn hx hper hα h1
  have hey : a (n - 1) (T^[d + 1] x) = (a (n - 1) (T^[d + 1] x) - 1) + 1 := by omega
  have hy0 : 0 < T^[d + 1] x := T_iterate_pos_int hx0 _
  obtain ⟨-, hid, hdvd⟩ := steiner_reduction hn hy h1y hey
  obtain ⟨-, h3, -, -⟩ := steiner_reduction_pos hy0 hn hy h1y hey
  obtain ⟨rfl, he⟩ := hA _ h3 hdvd
  rw [he] at hid
  have hy1 : T^[d + 1] x = 1 := by
    norm_num at hid
    exact hid
  rw [← hback, hy1, T_iterate_one_int]

/-- **(c) of the planner.** `theo:steiner` (l.150) and `theo:steiner_2` on positive cycles are the
same statement. -/
theorem steiner_iff_steinerTwoPos : SteinerStmt ↔ SteinerTwoPosStmt := by
  constructor
  · intro hS x hx0 n hn hx α hper hα h1
    obtain ⟨d, hd, -, -, hy, h1y, -, hback⟩ := steiner_point hn hx hper hα h1
    have hy1 : T^[d + 1] x = 1 :=
      hS _ (T_iterate_pos_int hx0 _) ⟨n, hn, hy, p_eq_self_of_a_eq_one h1y⟩
    refine ⟨0, ?_⟩
    rw [Function.iterate_zero_apply, ← hback, hy1, T_iterate_one_int]
  · rintro hS2 x hx0 ⟨n, hn, hx, hp⟩
    have h1x : ∀ k : ℕ, k < n - 1 → a k x = 1 := by
      intro k hk
      have := p_succ' k x
      rw [hp (k + 1) (by omega), hp k (by omega)] at this
      omega
    have hgt : 1 < a (n - 1) x := by
      by_contra hle
      have hge : 1 ≤ a (n - 1) x := by
        have hper : Function.Periodic (aPer n x) n := aPer_periodic n x
        have := one_le_of_cycle hn hx hper (aPer_natCast hx) ((n - 1 : ℕ) : ℤ)
        rwa [aPer_natCast hx] at this
      have hpn : p n x = n := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [p_succ', hp m (by omega)]
        rw [show m + 1 - 1 = m by omega] at hle hge
        omega
      have hpos := two_pow_p_sub_three_pow_mul_pos hn hx
      rw [hpn] at hpos
      have h23 : (2 : ℤ) ^ n ≤ 3 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      nlinarith
    have hcard : ((range n).filter (fun i : ℕ => 1 < aPer n x i)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨n - 1, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, aPer_natCast hx]
      constructor
      · rintro ⟨hi, hgt'⟩
        by_contra hne
        have := h1x i (by omega)
        omega
      · rintro rfl
        exact ⟨by omega, hgt⟩
    obtain ⟨k, hk⟩ := hS2 x hx0 n hn hx (aPer n x) (aPer_periodic n x) (aPer_natCast hx) hcard
    exact (exists_iterate_eq_one_iff_of_cycle hn hx).1 ⟨k, hk⟩

/-- **The reduction is exact**: `theo:steiner_2` on positive cycles is equivalent to the arithmetic
statement that the cited steps of l.302 settle. -/
theorem steinerTwoPos_iff_arith : SteinerTwoPosStmt ↔ SteinerArithStmt := by
  constructor
  · intro hS2 n e hn h3 hD
    have h23 : (2 : ℤ) ^ n ≤ 3 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have he : 1 ≤ e := by
      by_contra h0
      have : e = 0 := by omega
      subst this
      simp only [add_zero] at h3
      linarith
    obtain ⟨y, hyD, hy, h1y, hey⟩ := steiner_cycle_of_dvd hn he hD
    have h32 : (2 : ℤ) ^ n < 3 ^ n := pow_lt_pow_left₀ (by norm_num) (by norm_num) hn.ne'
    have hy0 : 0 < y := by
      have : 0 < y * ((2 : ℤ) ^ (n + e) - 3 ^ n) := by rw [hyD]; linarith
      exact pos_of_mul_pos_left this (by linarith)
    have hcard : ((range n).filter (fun i : ℕ => 1 < aPer n y i)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨n - 1, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, aPer_natCast hy]
      constructor
      · rintro ⟨hi, hgt'⟩
        by_contra hne
        have := h1y i (by omega)
        omega
      · rintro rfl
        exact ⟨by omega, by omega⟩
    obtain ⟨k, hk⟩ := hS2 y hy0 n hn hy (aPer n y) (aPer_periodic n y) (aPer_natCast hy) hcard
    have hy1 := (exists_iterate_eq_one_iff_of_cycle hn hy).1 ⟨k, hk⟩
    rw [hy1, one_mul] at hyD
    -- `2^{n+e} + 2ⁿ = 2·3ⁿ` forces `n = 1`, then `e = 1`
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m = 0 := by
      by_contra hm0
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hodd : Odd ((3 : ℤ) ^ (m' + 1 + 1)) := Odd.pow (by decide)
      have hev : Even ((3 : ℤ) ^ (m' + 1 + 1)) := by
        refine ⟨2 ^ (m' + e) + 2 ^ m', ?_⟩
        have : (3 : ℤ) ^ (m' + 1 + 1) * 2 = 2 ^ (m' + 1 + 1 + e) + 2 ^ (m' + 1 + 1) := by
          linear_combination -hyD
        have e4 : (2 : ℤ) ^ (m' + 1 + 1 + e) = 4 * 2 ^ (m' + e) := by
          rw [show m' + 1 + 1 + e = (m' + e) + 2 by ring, pow_add]; ring
        have e5 : (2 : ℤ) ^ (m' + 1 + 1) = 4 * 2 ^ m' := by
          rw [pow_add]; ring
        rw [e4, e5] at this
        linarith
      exact (Int.not_even_iff_odd.2 hodd) hev
    subst hm
    refine ⟨rfl, ?_⟩
    have h2e : (2 : ℤ) ^ e = 2 := by
      have : (2 : ℤ) ^ (0 + 1 + e) = 2 * 2 ^ e := by rw [show 0 + 1 + e = e + 1 by ring, pow_succ]; ring
      rw [this] at hyD
      simp only [zero_add, pow_one] at hyD
      linarith
    rcases e with _ | _ | e
    · norm_num at h2e
    · rfl
    · exfalso
      have : (2 : ℤ) ^ (e + 1 + 1) = 4 * 2 ^ e := by rw [pow_add]; ring
      have h1 : (1 : ℤ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
      rw [this] at h2e
      linarith
  · intro hA x hx0 n hn hx α hper hα h1
    refine ⟨0, ?_⟩
    rw [Function.iterate_zero_apply]
    exact steiner_eq_one_of_arith hx0 hn hx hper hα h1 (fun e h3 hD => hA n e hn h3 hD)

/-! ### The computer check of l.302, for periods `n ≤ 100` -/

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
set_option exponentiation.threshold 1024 in
/-- The kernel check (`decide`) of the arithmetic statement for `n ≤ 100`, `e < 2n`, positive side. -/
theorem steinerArith_check_pos : ∀ n : ℕ, n < 101 → ∀ e : ℕ, e < 2 * n → 0 < n →
    3 ^ n < 2 ^ (n + e) → (2 ^ e - 1) % (2 ^ (n + e) - 3 ^ n) = 0 → n = 1 ∧ e = 1 := by
  decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
set_option exponentiation.threshold 1024 in
/-- The same check on the negative side (`2^{n+e} < 3ⁿ`, `e ≥ 1`): only `n = 2`, `e = 1`. -/
theorem steinerArith_check_neg : ∀ n : ℕ, n < 101 → ∀ e : ℕ, e < 2 * n → 0 < e →
    2 ^ (n + e) < 3 ^ n → (2 ^ e - 1) % (3 ^ n - 2 ^ (n + e)) = 0 → n = 2 ∧ e = 1 := by
  decide

/-- `SteinerArithStmt` for `n ≤ 100`. -/
theorem steinerArith_of_le {n e : ℕ} (hn : 0 < n) (hN : n ≤ 100) (h3 : (3 : ℤ) ^ n < 2 ^ (n + e))
    (hD : (2 : ℤ) ^ (n + e) - 3 ^ n ∣ 2 ^ e - 1) : n = 1 ∧ e = 1 := by
  have h23 : (2 : ℤ) ^ n ≤ 3 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have he : 1 ≤ e := by
    by_contra h0
    have : e = 0 := by omega
    subst this
    simp only [add_zero] at h3
    linarith
  have h2e : (2 : ℤ) ≤ 2 ^ e := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he
  have h2n : (2 : ℤ) ≤ 2 ^ n := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hle : (2 : ℤ) ^ (n + e) - 3 ^ n ≤ 2 ^ e - 1 := Int.le_of_dvd (by linarith) hD
  -- `2^e ≤ 3ⁿ < 4ⁿ`, so `e < 2n`
  have he2 : (2 : ℤ) ^ e < 2 ^ (2 * n) := by
    have h34 : (3 : ℤ) ^ n < 4 ^ n := pow_lt_pow_left₀ (by norm_num) (by norm_num) hn.ne'
    rw [pow_mul, show (2 : ℤ) ^ 2 = 4 by norm_num]
    rw [pow_add] at hle
    nlinarith
  have he2n : e < 2 * n := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 he2
  have h3' : 3 ^ n < 2 ^ (n + e) := by exact_mod_cast h3
  have hD' : 2 ^ (n + e) - 3 ^ n ∣ 2 ^ e - 1 := by
    have e1 : (((2 ^ (n + e) - 3 ^ n : ℕ) : ℤ)) = (2 : ℤ) ^ (n + e) - 3 ^ n := by
      push_cast [Nat.cast_sub h3'.le]; ring
    have e2 : (((2 ^ e - 1 : ℕ) : ℤ)) = (2 : ℤ) ^ e - 1 := by
      push_cast [Nat.cast_sub (Nat.one_le_two_pow)]; ring
    rw [← e1, ← e2] at hD
    exact Int.natCast_dvd_natCast.1 hD
  exact steinerArith_check_pos n (by omega) e he2n hn h3' (Nat.mod_eq_zero_of_dvd hD')

/-- **`theo:steiner_2` on positive cycles of period `n ≤ 100`**, proved: the reduction and the
kernel check, no cited input. -/
theorem steinerTwo_pos_of_le {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hN : n ≤ 100)
    (hx : T^[n] x = x) {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (h1 : ((range n).filter (fun i : ℕ => 1 < α i)).card = 1) : x = 1 :=
  steiner_eq_one_of_arith hx0 hn hx hper hα h1 (fun _ h3 hD => steinerArith_of_le hn hN h3 hD)

/-- **The corrected `theo:steiner_2` over `ℤ`, for periods `n ≤ 100`**: an `n`-cycle with one
descending index per period is the cycle of `1` or the cycle `(−5, −7)`. -/
theorem steinerTwo_int_of_le {x : ℤ} {n : ℕ} (hn : 0 < n) (hN : n ≤ 100) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (h1 : ((range n).filter (fun i : ℕ => 1 < α i)).card = 1) : x = 1 ∨ x = -5 ∨ x = -7 := by
  rcases lt_trichotomy x 0 with hneg | h0 | hpos
  · right
    obtain ⟨d, hd, -, -, hy, h1y, hgt, hback⟩ := steiner_point hn hx hper hα h1
    set y := T^[d + 1] x with hydef
    set e := a (n - 1) y - 1 with hedef
    have hey : a (n - 1) y = e + 1 := by omega
    have he : 0 < e := by omega
    have hy0 : y < 0 := T_iterate_neg_int hneg _
    obtain ⟨hpn, hid, hdvd⟩ := steiner_reduction hn hy h1y hey
    have hsgn := two_pow_p_sub_three_pow_mul_pos hn hy
    rw [hpn] at hsgn
    have hD : (2 : ℤ) ^ (n + e) - 3 ^ n < 0 := by nlinarith
    have h2e : (2 : ℤ) ≤ 2 ^ e := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he
    have hle : (3 : ℤ) ^ n - 2 ^ (n + e) ≤ 2 ^ e - 1 :=
      Int.le_of_dvd (by linarith) (by rw [show (3 : ℤ) ^ n - 2 ^ (n + e) =
        -((2 : ℤ) ^ (n + e) - 3 ^ n) by ring]; exact (neg_dvd).2 hdvd)
    have he2 : (2 : ℤ) ^ (n + e) < 2 ^ (2 * n) := by
      have h34 : (3 : ℤ) ^ n < 4 ^ n := pow_lt_pow_left₀ (by norm_num) (by norm_num) hn.ne'
      rw [pow_mul, show (2 : ℤ) ^ 2 = 4 by norm_num]
      linarith
    have he2n : e < 2 * n := by
      have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 he2
      omega
    have h3' : 2 ^ (n + e) < 3 ^ n := by exact_mod_cast (by linarith : (2 : ℤ) ^ (n + e) < 3 ^ n)
    have hD' : 3 ^ n - 2 ^ (n + e) ∣ 2 ^ e - 1 := by
      have e1 : (((3 ^ n - 2 ^ (n + e) : ℕ) : ℤ)) = (3 : ℤ) ^ n - 2 ^ (n + e) := by
        push_cast [Nat.cast_sub h3'.le]; ring
      have e2 : (((2 ^ e - 1 : ℕ) : ℤ)) = (2 : ℤ) ^ e - 1 := by
        push_cast [Nat.cast_sub (Nat.one_le_two_pow)]; ring
      have h := (neg_dvd).2 hdvd
      rw [show -((2 : ℤ) ^ (n + e) - 3 ^ n) = (3 : ℤ) ^ n - 2 ^ (n + e) by ring, ← e1, ← e2] at h
      exact Int.natCast_dvd_natCast.1 h
    obtain ⟨rfl, he1⟩ :=
      steinerArith_check_neg n (by omega) e he2n he h3' (Nat.mod_eq_zero_of_dvd hD')
    rw [he1] at hid
    have hy5 : y = -5 := by norm_num at hid; linarith
    have h5 : T (-5 : ℤ) = -7 :=
      (T_unique (A := ℤ) two_ne_zero (x := -5) (t := -7) (k := 1) ⟨-4, by norm_num⟩
        (by norm_num)).2
    rw [hy5] at hback
    rcases Nat.lt_or_ge d 1 with hd0 | hd1
    · right
      rw [show 2 - 1 - d = 1 by omega, Function.iterate_one, h5] at hback
      exact hback.symm
    · left
      rw [show 2 - 1 - d = 0 by omega, Function.iterate_zero_apply] at hback
      exact hback.symm
  · exact absurd h0 (ne_zero_of_T_cycle_int hn hx)
  · left
    exact steinerTwo_pos_of_le hpos hn hN hx hper hα h1

/-! ### The printed displays of the proof -/

/-- `|a(Γ)| = n + e` when `𝒟 = nℤ` with `a_0 = e + 1` (l.299, `α = a_0 − 1 = |a(Γ)| − n`). -/
theorem steiner_sum_eq {α : ℤ → ℕ} {n e : ℕ} (hn : 0 < n) (h0 : α 0 = e + 1)
    (h1 : ∀ i : ℕ, 1 ≤ i → i < n → α i = 1) : ∑ t ∈ range n, α t = n + e := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_congr rfl (fun i hi => h1 (i + 1) (by omega)
    (by have := Finset.mem_range.1 hi; omega))]
  simp [h0]
  ring

/-- **Finding 4 ((a) of the planner).** `α = ½(|a(Γ)| − n)` (l.299) fails whenever `a_0 > 1`. -/
theorem steiner_alpha_half_false {α : ℤ → ℕ} {n e : ℕ} (hn : 0 < n) (he : 1 ≤ e)
    (h0 : α 0 = e + 1) (h1 : ∀ i : ℕ, 1 ≤ i → i < n → α i = 1) :
    ((α 0 : ℚ) - 1) ≠ (((∑ t ∈ range n, α t : ℕ) : ℚ) - n) / 2 := by
  rw [steiner_sum_eq hn h0 h1, h0]
  push_cast
  intro h
  have : (1 : ℚ) ≤ e := by exact_mod_cast he
  linarith

/-- With `𝒟 ∩ ⟦1, n−1⟧ = ∅` (`𝒟 ⊆ nℤ`), every `f (i − 1)`, `i ∈ 𝒟`, of an `n`-periodic `f` is
`f (−1)`. -/
theorem periodic_sub_one_of_desc {α : ℤ → ℕ} {n : ℕ} (hn : 0 < n) (hper : Function.Periodic α n)
    (hD : ∀ i : ℕ, 1 ≤ i → i < n → α i = 1) {f : ℤ → ℤ} (hf : Function.Periodic f n) {i : ℤ}
    (hi : 1 < α i) : f (i - 1) = f (-1) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hr : (((i % n).toNat : ℕ) : ℤ) = i % n := Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')
  have h0 : i % (n : ℤ) = 0 := by
    by_contra hne
    have hlt := Int.emod_lt_of_pos i hn'
    have hge := Int.emod_nonneg i hn'.ne'
    have := hD (i % n).toNat (by omega) (by omega)
    rw [hr, ← periodic_emod hper i] at this
    omega
  obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero h0
  have h := (hf.int_mul q) (-1)
  simp only [Int.cast_id] at h
  rw [show i - 1 = -1 + q * n by rw [hq]; ring]
  exact h

/-- **l.298, `m = A_0 ∧ Δ_{−1}`, OQ-43 reading**, for every `n`-periodic `α ≥ 1` with `𝒟 = nℤ`:
the common divisors of `A'_0` and `Δ'_{−1}` are those of every `A'_u`. -/
theorem steiner_gcd_alt_iff {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) (hD : ∀ i : ℕ, 1 ≤ i → i < n → α i = 1) (d : ℤ) :
    (d ∣ (AunAlt n 0 α : ℤ) ∧ d ∣ DeltaAlt n α (-1)) ↔ ∀ u : ℤ, d ∣ (AunAlt n u α : ℤ) := by
  constructor
  · rintro ⟨h0, h1⟩
    refine (intertwined_alt hpos hn hper 0 d).1 ⟨h0, fun i hi => ?_⟩
    rw [periodic_sub_one_of_desc hn hper hD (DeltaAlt_periodic hper) hi]
    exact h1
  · intro hall
    exact ⟨hall 0, by simp only [DeltaAlt]; exact dvd_sub (hall _) (hall _)⟩

/-- **l.298, printed `A_u^n`**: the common divisors of `A_0` and `Δ_{−1}` are those of every `A_u`. -/
theorem steiner_gcd_aun_iff {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) (hD : ∀ i : ℕ, 1 ≤ i → i < n → α i = 1) (d : ℤ) :
    (d ∣ (Aun n 0 α : ℤ) ∧ d ∣ Delta n α (-1)) ↔ ∀ u : ℤ, d ∣ (Aun n u α : ℤ) := by
  constructor
  · rintro ⟨h0, h1⟩
    refine (intertwined_aun hpos hn hper 0 d).1 ⟨h0, fun i hi => ?_⟩
    rw [periodic_sub_one_of_desc hn hper hD (Delta_periodic hper) hi]
    exact h1
  · intro hall
    exact ⟨hall 0, by simp only [Delta]; exact dvd_sub (hall _) (hall _)⟩

/-- On a cycle of `ℤ` with an ascending index, `GCD(A_u : u ∈ ⟦0, n−1⟧) = 2 |2^{p_n} − 3ⁿ|` for the
printed `A_u^n`. -/
theorem gcd_Aun_of_cycle_of_asc {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (hA : ∃ j : ℕ, j < n ∧ α j = 1) :
    (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) = 2 * |(2 : ℤ) ^ p n x - 3 ^ n| := by
  set m : ℤ := (2 : ℤ) ^ p n x - 3 ^ n with hm
  set G := (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) with hG
  have hG0 : 0 ≤ G := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  obtain ⟨hodd, havoid⟩ := cycle_avoids_neg_third (A := ℤ) two_ne_zero hn hx
  have hcast : ∀ u : ℕ, (Aun n u α : ℤ) = m * (3 * T^[u] x + 1) :=
    fun u => (Aun_cast_of_cycle hx α hα u).1
  -- `2m` divides every `A_u`
  have h2m : ∀ u : ℕ, 2 * m ∣ (Aun n u α : ℤ) := by
    intro u
    rw [hcast]
    have hou : Odd (T^[u] x) := T_iterate_odd hodd (fun k _ => havoid k)
    obtain ⟨r, hr⟩ := hou
    exact ⟨r * 3 + 2, by rw [hr]; ring⟩
  have hmG : 2 * |m| ∣ G := by
    refine Finset.dvd_gcd (fun u _ => ?_)
    rcases abs_choice m with h | h
    · rw [h]; exact h2m u
    · rw [h, mul_neg, neg_dvd]; exact h2m u
  -- `G` divides every `A_v`, `v ∈ ℕ`
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hGall : ∀ v : ℕ, G ∣ (Aun n v α : ℤ) := by
    intro v
    have e := periodic_emod (Aun_periodic hper) (v : ℤ)
    rw [e, show (v : ℤ) % (n : ℤ) = (((v : ℤ) % n).toNat : ℕ) from
      (Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')).symm]
    exact Finset.gcd_dvd (Finset.mem_range.2 (by have := Int.emod_lt_of_pos (v : ℤ) hn'; omega))
  -- an ascending index `j`: `3A_j − 2A_{j+1} = −2m`
  obtain ⟨j, -, hj⟩ := hA
  have hs := two_pow_a_mul_T_iterate_succ x j
  rw [← hα, hj, pow_one] at hs
  have hkey : 3 * (Aun n j α : ℤ) - 2 * (Aun n ((j + 1 : ℕ) : ℤ) α : ℤ) = -(2 * m) := by
    rw [hcast j, hcast (j + 1)]
    linear_combination (3 * m) * hs.symm + 0 * hs
  have hGm : G ∣ 2 * m := by
    have := dvd_sub (dvd_mul_of_dvd_right (hGall j) 3) (dvd_mul_of_dvd_right (hGall (j + 1)) 2)
    rw [hkey] at this
    exact (dvd_neg).1 this
  have hGm' : G ∣ 2 * |m| := by
    rcases abs_choice m with h | h
    · rw [h]; exact hGm
    · rw [h, mul_neg, dvd_neg]; exact hGm
  exact Int.dvd_antisymm hG0 (by positivity) hGm' hmG

/-- **Finding 3. l.298 on a cycle** (`𝒟 ⊆ nℤ`, convention of l.62): `A'_0 ∧ Δ'_{−1} = |2^{p_n} − 3ⁿ|`, which
is `m = 2^{p_n} − 3ⁿ` for `x > 0`; for the printed `A_u^n`, `A_0 ∧ Δ_{−1} = GCD(A_u)`, which is
`2 |m|` when `n ≥ 2`, so never `m`. -/
theorem steiner_m_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (hD : ∀ i : ℕ, 1 ≤ i → i < n → α i = 1) :
    GCDMonoid.gcd (AunAlt n 0 α : ℤ) (DeltaAlt n α (-1)) = |(2 : ℤ) ^ p n x - 3 ^ n| ∧
      (0 < x → GCDMonoid.gcd (AunAlt n 0 α : ℤ) (DeltaAlt n α (-1)) = (2 : ℤ) ^ p n x - 3 ^ n) ∧
      GCDMonoid.gcd (Aun n 0 α : ℤ) (Delta n α (-1)) = (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) ∧
      (2 ≤ n → GCDMonoid.gcd (Aun n 0 α : ℤ) (Delta n α (-1)) = 2 * |(2 : ℤ) ^ p n x - 3 ^ n|) ∧
      GCDMonoid.gcd (Aun n 0 α : ℤ) (Delta n α (-1)) ≠ (2 : ℤ) ^ p n x - 3 ^ n := by
  have hpos := one_le_of_cycle hn hx hper hα
  set m : ℤ := (2 : ℤ) ^ p n x - 3 ^ n with hm
  have hGalt : GCDMonoid.gcd (AunAlt n 0 α : ℤ) (DeltaAlt n α (-1)) = |m| := by
    set G := GCDMonoid.gcd (AunAlt n 0 α : ℤ) (DeltaAlt n α (-1)) with hG
    have hG0 : 0 ≤ G := Int.gcd_nonneg _ _
    have hGm : G ∣ m := (dvd_iff_dvd_AunAlt_of_cycle hn hx hper hα G).2
      ((steiner_gcd_alt_iff hpos hn hper hD G).1 ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩)
    have hmG : m ∣ G := by
      obtain ⟨h0, h1⟩ := (steiner_gcd_alt_iff hpos hn hper hD m).2
        ((dvd_iff_dvd_AunAlt_of_cycle hn hx hper hα m).1 dvd_rfl)
      exact dvd_gcd h0 h1
    exact Int.dvd_antisymm hG0 (abs_nonneg _) ((dvd_abs _ _).2 hGm) ((abs_dvd _ _).2 hmG)
  have hGaun : GCDMonoid.gcd (Aun n 0 α : ℤ) (Delta n α (-1)) =
      (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) := by
    set G := GCDMonoid.gcd (Aun n 0 α : ℤ) (Delta n α (-1)) with hG
    set H := (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) with hH
    have hG0 : 0 ≤ G := Int.gcd_nonneg _ _
    have hH0 : 0 ≤ H := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hHall : ∀ u : ℤ, H ∣ (Aun n u α : ℤ) := by
      intro u
      have e := periodic_emod (Aun_periodic hper) u
      rw [e, show u % (n : ℤ) = (((u % n).toNat : ℕ) : ℤ) from
        (Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')).symm]
      exact Finset.gcd_dvd (Finset.mem_range.2 (by have := Int.emod_lt_of_pos u hn'; omega))
    have hHG : H ∣ G := by
      obtain ⟨h0, h1⟩ := (steiner_gcd_aun_iff hpos hn hper hD H).2 hHall
      exact dvd_gcd h0 h1
    have hGall := (steiner_gcd_aun_iff hpos hn hper hD G).1 ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
    have hGH : G ∣ H := Finset.dvd_gcd (fun u _ => hGall u)
    exact Int.dvd_antisymm hG0 hH0 hGH hHG
  refine ⟨hGalt, fun hx0 => ?_, hGaun, fun hn2 => ?_, ?_⟩
  · have hp := two_pow_p_sub_three_pow_mul_pos hn hx
    rw [hGalt, abs_of_pos (pos_of_mul_pos_left hp hx0.le)]
  · rw [hGaun]
    exact gcd_Aun_of_cycle_of_asc hn hx hper hα ⟨1, by omega, hD 1 le_rfl (by omega)⟩
  · intro h
    have hΔ2 : (2 : ℤ) ∣ Delta n α (-1) := by
      simp only [Delta]
      exact dvd_sub (two_dvd_Aun hpos n _) (two_dvd_Aun hpos n _)
    have h2 : (2 : ℤ) ∣ GCDMonoid.gcd (Aun n 0 α : ℤ) (Delta n α (-1)) :=
      dvd_gcd (two_dvd_Aun hpos n 0) hΔ2
    rw [h] at h2
    have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
    have hodd := (delta_odd_not_three_dvd hpos hn).1
    rw [← hP] at hodd
    exact Int.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 h2)

/-- `A'^n_u(i ↦ β_{i+1}) = A'^n_{u+1}(β)`. -/
theorem AunAlt_shift_one (n : ℕ) (u : ℤ) (β : ℤ → ℕ) :
    AunAlt n u (fun i => β (i + 1)) = AunAlt n (u + 1) β := by
  simp only [AunAlt]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [show u + (i : ℤ) + 1 = u + 1 + i by ring]

/-- **l.298 on a cycle, convention of l.71** (`β_{k+1} = a_k(x)`), OQ-43 reading: with `𝒟(β) = nℤ`,
`A'_0(β) ∧ Δ'_{−1}(β) = |2^{p_n} − 3ⁿ|`, as in the convention of l.62 (`steiner_m_cycle`). -/
theorem steiner_m_cycle_shift {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {β : ℤ → ℕ} (hper : Function.Periodic β n) (hβ : ∀ k : ℕ, β ((k : ℤ) + 1) = a k x)
    (hD : ∀ i : ℕ, 1 ≤ i → i < n → β i = 1) :
    GCDMonoid.gcd (AunAlt n 0 β : ℤ) (DeltaAlt n β (-1)) = |(2 : ℤ) ^ p n x - 3 ^ n| := by
  set α : ℤ → ℕ := fun i => β (i + 1) with hαdef
  have hperα : Function.Periodic α n := by
    intro i
    simp only [hαdef]
    rw [show i + (n : ℤ) + 1 = (i + 1) + n by ring, hper]
  have hα : ∀ k : ℕ, α k = a k x := fun k => hβ k
  have hposα := one_le_of_cycle hn hx hperα hα
  have hpos : ∀ k, 1 ≤ β k := by
    intro k
    have := hposα (k - 1)
    simp only [hαdef, sub_add_cancel] at this
    exact this
  have hdiv : ∀ d : ℤ, d ∣ (2 : ℤ) ^ p n x - 3 ^ n ↔ ∀ u : ℤ, d ∣ (AunAlt n u β : ℤ) := by
    intro d
    rw [dvd_iff_dvd_AunAlt_of_cycle hn hx hperα hα d]
    constructor
    · intro h u
      have := h (u - 1)
      rwa [hαdef, AunAlt_shift_one, sub_add_cancel] at this
    · intro h u
      rw [hαdef, AunAlt_shift_one]
      exact h _
  set m : ℤ := (2 : ℤ) ^ p n x - 3 ^ n with hm
  set G := GCDMonoid.gcd (AunAlt n 0 β : ℤ) (DeltaAlt n β (-1)) with hG
  have hG0 : 0 ≤ G := Int.gcd_nonneg _ _
  have hGm : G ∣ m := (hdiv G).2
    ((steiner_gcd_alt_iff hpos hn hper hD G).1 ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩)
  have hmG : m ∣ G := by
    obtain ⟨h0, h1⟩ := (steiner_gcd_alt_iff hpos hn hper hD m).2 ((hdiv m).1 dvd_rfl)
    exact dvd_gcd h0 h1
  exact Int.dvd_antisymm hG0 (abs_nonneg _) ((dvd_abs _ _).2 hGm) ((abs_dvd _ _).2 hmG)

/-- **l.301, `Δ_1 ∼_S 2^α − 1`, exactly** (`n ≥ 2`, `𝒟 = nℤ`, `a_0 = e + 1`), both readings of
OQ-43, at `i = 1` as printed and at `i = −1` (the index of l.298). -/
theorem steiner_delta {α : ℤ → ℕ} {n e : ℕ} (hn : 2 ≤ n) (hper : Function.Periodic α n)
    (h0 : α 0 = e + 1) (hD : ∀ i : ℕ, 1 ≤ i → i < n → α i = 1) :
    DeltaAlt n α 1 = 2 ^ (n - 1) * (2 ^ e - 1) ∧ Delta n α 1 = 3 * 2 ^ (n - 1) * (2 ^ e - 1) ∧
      DeltaAlt n α (-1) = 2 * 3 ^ (n - 2) * (2 ^ e - 1) ∧
      Delta n α (-1) = 2 * 3 ^ (n - 1) * (2 ^ e - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hα1 : ∀ j : ℤ, 1 ≤ j → j ≤ (m : ℤ) + 1 → α j = 1 := by
    intro j hj1 hj2
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ j)
    exact hD k (by omega) (by omega)
  have hαm1 : α (-1) = 1 := by
    have := hper (-1)
    rw [← this]
    exact hα1 _ (by push_cast; omega) (by push_cast; omega)
  have hαn : α ((m + 2 : ℕ) : ℤ) = e + 1 := by
    have := hper 0
    rw [zero_add] at this
    rw [this, h0]
  have hD1 : DeltaAlt (m + 2) α 1 = 2 ^ (m + 1) * (2 ^ e - 1) := by
    rw [DeltaAlt_eq, deltaTrue, Finset.sum_eq_single (m + 1)]
    · have hs : ∑ t ∈ range (m + 1 - 1), α (1 + 1 + t) = ∑ t ∈ range m, 1 := by
        rw [show m + 1 - 1 = m by omega]
        exact Finset.sum_congr rfl (fun t ht => hα1 _ (by omega)
          (by have := Finset.mem_range.1 ht; omega))
      rw [hs, show (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ) by push_cast; ring, hαn,
        hα1 1 le_rfl (by omega), show m + 2 - 1 - (m + 1) = 0 by omega]
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      ring
    · intro k hk hne
      have hk' := Finset.mem_Icc.1 hk
      rw [hα1 (1 + k) (by omega) (by omega), hα1 1 le_rfl (by omega), sub_self, mul_zero]
    · intro h
      exact absurd (Finset.mem_Icc.2 ⟨by omega, by omega⟩) h
  have hDm1 : DeltaAlt (m + 2) α (-1) = 2 * 3 ^ m * (2 ^ e - 1) := by
    rw [DeltaAlt_eq, deltaTrue, Finset.sum_eq_single 1]
    · rw [show (-1 : ℤ) + ((1 : ℕ) : ℤ) = 0 by norm_num, h0, hαm1,
        show m + 2 - 1 - 1 = m by omega]
      simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, pow_zero, mul_one]
      ring
    · intro k hk hne
      have hk' := Finset.mem_Icc.1 hk
      rw [hα1 (-1 + k) (by omega) (by omega), hαm1, sub_self, mul_zero]
    · intro h
      exact absurd (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  refine ⟨hD1, ?_, hDm1, ?_⟩
  · rw [Delta_eq_three_mul hper, hD1]
    ring
  · rw [Delta_eq_three_mul hper, hDm1]
    ring

/-- **l.301 in `∼_S` (`SEquiv`)**, with the factor in `S` explicit (`n ≥ 2`). -/
theorem steiner_delta_sEquiv {α : ℤ → ℕ} {n e : ℕ} (hn : 2 ≤ n) (hper : Function.Periodic α n)
    (h0 : α 0 = e + 1) (hD : ∀ i : ℕ, 1 ≤ i → i < n → α i = 1) :
    SEquiv (DeltaAlt n α 1) (2 ^ e - 1) ∧ SEquiv (Delta n α 1) (2 ^ e - 1) ∧
      SEquiv (DeltaAlt n α (-1)) (2 ^ e - 1) ∧ SEquiv (Delta n α (-1)) (2 ^ e - 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := steiner_delta hn hper h0 hD
  refine ⟨⟨2 ^ (n - 1), ⟨((n - 1 : ℕ) : ℤ), 0, by rw [zpow_natCast, zpow_zero, mul_one]⟩, ?_⟩,
    ⟨3 * 2 ^ (n - 1), ⟨((n - 1 : ℕ) : ℤ), 1, by rw [zpow_natCast, zpow_one]; ring⟩, ?_⟩,
    ⟨2 * 3 ^ (n - 2), ⟨1, ((n - 2 : ℕ) : ℤ), by rw [zpow_natCast, zpow_one]⟩, ?_⟩,
    ⟨2 * 3 ^ (n - 1), ⟨1, ((n - 1 : ℕ) : ℤ), by rw [zpow_natCast, zpow_one]⟩, ?_⟩⟩
  · rw [h1]; push_cast; ring
  · rw [h2]; push_cast; ring
  · rw [h3]; push_cast; ring
  · rw [h4]; push_cast; ring

/-- **Finding 5.** For `n = 1` the display of l.301 fails, at the cycle of `1` itself (`a ≡ 2`,
`α = 1`): every `Δ_i` is `0`, for both readings of OQ-43 and both indices `±1`. -/
theorem steiner_delta_period_one_false :
    ¬ SEquiv (DeltaAlt 1 (fun _ => 2) 1) (2 ^ 1 - 1) ∧ ¬ SEquiv (Delta 1 (fun _ => 2) 1) (2 ^ 1 - 1) ∧
      ¬ SEquiv (DeltaAlt 1 (fun _ => 2) (-1)) (2 ^ 1 - 1) ∧
      ¬ SEquiv (Delta 1 (fun _ => 2) (-1)) (2 ^ 1 - 1) := by
  have e1 : DeltaAlt 1 (fun _ => 2) 1 = 0 := by decide
  have e2 : Delta 1 (fun _ => 2) 1 = 0 := by decide
  have e3 : DeltaAlt 1 (fun _ => 2) (-1) = 0 := by decide
  have e4 : Delta 1 (fun _ => 2) (-1) = 0 := by decide
  have hz : ∀ z : ℤ, z = 0 → ¬ SEquiv z (2 ^ 1 - 1) := by
    rintro z rfl ⟨s, ⟨u, v, rfl⟩, h⟩
    norm_num at h
    rcases h with h | h <;> exact absurd h (by positivity)
  exact ⟨hz _ e1, hz _ e2, hz _ e3, hz _ e4⟩

/-- **Finding 6 ((b) of the planner).** The printed inequality of l.302,
`2^{|Γ|−n} ≤ 2^{|Γ|(1−log₃2)}` with `|Γ| = p_n`, holds on a cycle of `ℤ` iff the cycle is
negative: it is reversed on every positive cycle. -/
theorem steiner_printed_bound_iff {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) :
    (2 : ℝ) ^ ((p n x : ℝ) - n) ≤ (2 : ℝ) ^ ((p n x : ℝ) * (1 - Real.logb 3 2)) ↔ x < 0 := by
  have hpos := two_pow_p_sub_three_pow_mul_pos hn hx
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
  have key : ((p n x : ℝ) - n ≤ (p n x : ℝ) * (1 - Real.logb 3 2)) ↔
      (p n x : ℝ) * Real.log 2 ≤ n * Real.log 3 := by
    rw [← Real.log_div_log]
    constructor
    · intro h
      have : (p n x : ℝ) * (Real.log 2 / Real.log 3) ≤ n := by linarith
      rwa [mul_div_assoc', div_le_iff₀ hl3] at this
    · intro h
      have : (p n x : ℝ) * (Real.log 2 / Real.log 3) ≤ n := by
        rw [mul_div_assoc', div_le_iff₀ hl3]; exact h
      linarith
  have key2 : (p n x : ℝ) * Real.log 2 ≤ n * Real.log 3 ↔ (2 : ℝ) ^ p n x ≤ 3 ^ n := by
    rw [← Real.log_pow, ← Real.log_pow, Real.log_le_log_iff (by positivity) (by positivity)]
  have key3 : (2 : ℝ) ^ p n x ≤ 3 ^ n ↔ (2 : ℤ) ^ p n x ≤ 3 ^ n := by
    constructor <;> intro h <;> exact_mod_cast h
  rw [key, key2, key3]
  constructor
  · intro h
    by_contra hx0
    push Not at hx0
    nlinarith
  · intro hx0
    by_contra h
    push Not at h
    nlinarith

/-- **l.302, the form that holds**: on a positive cycle with one descending index per period,
`2^α < 2^{log₃2} · 2^{|Γ|(1−log₃2)}`, `α = |Γ| − n`, `|Γ| = p_n`. -/
theorem steiner_bound {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (h1 : ((range n).filter (fun i : ℕ => 1 < α i)).card = 1) :
    (2 : ℝ) ^ ((p n x : ℝ) - n) <
      (2 : ℝ) ^ Real.logb 3 2 * (2 : ℝ) ^ ((p n x : ℝ) * (1 - Real.logb 3 2)) := by
  obtain ⟨-, -, -, -, h2⟩ := steiner_cycle_pos hx0 hn hx hper hα h1
  have h2r : (2 : ℝ) ^ p n x < 2 * 3 ^ n := by exact_mod_cast h2
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : (p n x : ℝ) * Real.log 2 < Real.log 2 + n * Real.log 3 := by
    have := Real.log_lt_log (by positivity) h2r
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at this
    exact this
  have hexp : (p n x : ℝ) - n < Real.logb 3 2 + (p n x : ℝ) * (1 - Real.logb 3 2) := by
    rw [← Real.log_div_log]
    have : ((p n x : ℝ) - 1) * (Real.log 2 / Real.log 3) < n := by
      rw [mul_div_assoc', div_lt_iff₀ hl3]
      linarith
    linarith
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp

/-- **The bound the corollary to Matveev's theorem consumes** (`cor:property_defined_cycles_gcd`,
l.162, with `ε = log₃2`): on a positive cycle with one descending index per period,
`GCD(A'_u) = 2^{p_n} − 3ⁿ ≤ 2^α − 1 < 2^{log₃2} 2^{|Γ|(1−ε)}`, and `GCD(A_u) ≤ 2^{α+1}`, twice that. -/
theorem steiner_gcd_bound {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (h1 : ((range n).filter (fun i : ℕ => 1 < α i)).card = 1) :
    (range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ)) = (2 : ℤ) ^ p n x - 3 ^ n ∧
      (2 : ℤ) ^ p n x - 3 ^ n ≤ 2 ^ (p n x - n) - 1 ∧
      (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) ≤ 2 ^ (p n x - n + 1) ∧
      (((range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ)) : ℤ) : ℝ) <
        (2 : ℝ) ^ Real.logb 3 2 * (2 : ℝ) ^ ((p n x : ℝ) * (1 - Real.logb 3 2)) ∧
      (((range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) : ℤ) : ℝ) <
        2 * (2 : ℝ) ^ Real.logb 3 2 * (2 : ℝ) ^ ((p n x : ℝ) * (1 - Real.logb 3 2)) := by
  obtain ⟨hp1, hdvd, h3, -, -⟩ := steiner_cycle_pos hx0 hn hx hper hα h1
  have hGalt := gcd_AunAlt_of_pos hx0 hn hx hα
  have hm0 : 0 < (2 : ℤ) ^ p n x - 3 ^ n := by linarith
  have h2e : (2 : ℤ) ≤ 2 ^ (p n x - n) := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (p n x - n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmle : (2 : ℤ) ^ p n x - 3 ^ n ≤ 2 ^ (p n x - n) - 1 := Int.le_of_dvd (by linarith) hdvd
  have hGaun : (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) ≤ 2 ^ (p n x - n + 1) := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      have hp : p 1 x = α 0 := by
        have := hα 0
        push_cast at this
        simp [p, this]
      rw [Finset.range_one, Finset.gcd_singleton, Nat.cast_zero, Aun_one,
        show p 1 x - 1 + 1 = p 1 x by omega, hp]
      push_cast
      rw [Int.normalize_of_nonneg (by positivity)]
    · obtain ⟨d, hd, -, hother, -⟩ := steiner_point hn hx hper hα h1
      have hA : ∃ j : ℕ, j < n ∧ α j = 1 := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · exact ⟨1, by omega, hother 1 (by omega) (by omega)⟩
        · exact ⟨0, hn, hother 0 hn (by omega)⟩
      rw [gcd_Aun_of_cycle_of_asc hn hx hper hα hA, abs_of_pos hm0, pow_succ]
      linarith
  have hb := steiner_bound hx0 hn hx hper hα h1
  have hrp : (2 : ℝ) ^ ((p n x : ℝ) - n) = (2 : ℝ) ^ (p n x - n) := by
    rw [← Real.rpow_natCast, Nat.cast_sub (by omega : n ≤ p n x)]
  rw [hrp] at hb
  refine ⟨hGalt, hmle, hGaun, ?_, ?_⟩
  · rw [hGalt]
    have : (((2 : ℤ) ^ p n x - 3 ^ n : ℤ) : ℝ) ≤ (((2 : ℤ) ^ (p n x - n) - 1 : ℤ) : ℝ) := by
      exact_mod_cast hmle
    push_cast at this ⊢
    linarith
  · have : (((range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) : ℤ) : ℝ) ≤
        (((2 : ℤ) ^ (p n x - n + 1) : ℤ) : ℝ) := by exact_mod_cast hGaun
    push_cast at this
    rw [pow_succ] at this
    linarith

/-- The hypothesis of `cor:property_defined_cycles_gcd` (l.162) for `𝒫(Γ)` = "`Γ` positive with one
descending index per period", both readings of OQ-43, effective: `ε = log₃2 > 0`, `C = 2^{1+log₃2}`. -/
theorem steiner_corollary_hypothesis :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ C : ℝ, ∀ x : ℤ, 0 < x → ∀ n : ℕ, 0 < n → T^[n] x = x →
      ∀ α : ℤ → ℕ, Function.Periodic α n → (∀ k : ℕ, α k = a k x) →
      ((range n).filter (fun i : ℕ => 1 < α i)).card = 1 →
      (((range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ)) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε)) ∧
        (((range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε)) := by
  refine ⟨Real.logb 3 2, Real.logb_pos (by norm_num) (by norm_num), ?_,
    2 * 2 ^ Real.logb 3 2, ?_⟩
  · rw [← Real.log_div_log, div_lt_one (Real.log_pos (by norm_num))]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  · intro x hx0 n hn hx α hper hα h1
    obtain ⟨-, -, -, h4, h5⟩ := steiner_gcd_bound hx0 hn hx hper hα h1
    have hpos : 0 < (2 : ℝ) ^ Real.logb 3 2 * (2 : ℝ) ^ ((p n x : ℝ) * (1 - Real.logb 3 2)) := by
      positivity
    constructor
    · rw [mul_assoc]
      linarith
    · rw [mul_assoc]
      rw [mul_assoc] at h5
      linarith

/-! ### Non-vacuity: the cycle of `1` and the cycle `(−5, −7)` -/

/-- The hypotheses of the positive results hold at the cycle of `1` (`n = 1`, `a ≡ 2`), with the
values `p_1 = 2`, `GCD(A'_u) = 1`, `GCD(A_u) = 4`; those of the displays of l.298 and l.301 hold at
`(−5, −7)` read from `−7` (`a = (2, 1)`, `𝒟 = 2ℤ`, `α = 1`), with `Δ'_{±1} = 2`, `Δ_{±1} = 6`,
`A'_0 ∧ Δ'_{−1} = 1 = |2³ − 3²|`, `A_0 ∧ Δ_{−1} = 2`; those of the exact reduction hold at
Steiner's point `−5` of the same cycle (`a = (1, 2)`), where `−5 (2³ − 3²) = 3² − 2²`. -/
theorem steiner_instances :
    (T^[1] (1 : ℤ) = 1 ∧ (∀ k : ℕ, (fun _ : ℤ => (2 : ℕ)) k = a k (1 : ℤ)) ∧
      ((range 1).filter (fun i : ℕ => 1 < (fun _ : ℤ => (2 : ℕ)) i)).card = 1 ∧ p 1 (1 : ℤ) = 2 ∧
      (range 1).gcd (fun u : ℕ => (AunAlt 1 u (fun _ => 2) : ℤ)) = 1 ∧
      (range 1).gcd (fun u : ℕ => (Aun 1 u (fun _ => 2) : ℤ)) = 4) ∧
    (T^[2] (-7 : ℤ) = -7 ∧ (∀ k : ℕ, seq12 ((k : ℤ) + 1) = a k (-7 : ℤ)) ∧
      Function.Periodic (fun i : ℤ => seq12 (i + 1)) (2 : ℕ) ∧
      seq12 (0 + 1) = 1 + 1 ∧ (∀ i : ℕ, 1 ≤ i → i < 2 → seq12 ((i : ℤ) + 1) = 1) ∧
      DeltaAlt 2 (fun i => seq12 (i + 1)) 1 = 2 ∧ Delta 2 (fun i => seq12 (i + 1)) 1 = 6 ∧
      DeltaAlt 2 (fun i => seq12 (i + 1)) (-1) = 2 ∧ Delta 2 (fun i => seq12 (i + 1)) (-1) = 6 ∧
      GCDMonoid.gcd (AunAlt 2 0 (fun i => seq12 (i + 1)) : ℤ)
        (DeltaAlt 2 (fun i => seq12 (i + 1)) (-1)) = 1 ∧
      GCDMonoid.gcd (Aun 2 0 (fun i => seq12 (i + 1)) : ℤ)
        (Delta 2 (fun i => seq12 (i + 1)) (-1)) = 2) ∧
    ((∀ k : ℕ, k < 2 - 1 → a k (-5 : ℤ) = 1) ∧ a (2 - 1) (-5 : ℤ) = 1 + 1 ∧ p 2 (-5 : ℤ) = 2 + 1 ∧
      (-5 : ℤ) * (2 ^ (2 + 1) - 3 ^ 2) = 3 ^ 2 - 2 ^ 2) := by
  have h5 : T (-5 : ℤ) = -7 :=
    (T_unique (A := ℤ) two_ne_zero (x := -5) (t := -7) (k := 1) ⟨-4, by norm_num⟩ (by norm_num)).2
  have hx5 : T^[2] (-5 : ℤ) = -5 := cycle_neg_five.1
  have h7 : T^[2] (-7 : ℤ) = -7 := by
    rw [← h5, ← Function.iterate_succ_apply, Function.iterate_succ_apply', hx5]
  have ha7 : ∀ k : ℕ, seq12 ((k : ℤ) + 1) = a k (-7 : ℤ) := by
    intro k
    rw [← h5, ← Function.iterate_one T, a_iterate, ← seq12_eq_a (k + 1)]
    push_cast
    rfl
  have hp5 : p 2 (-5 : ℤ) = 3 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← seq12_eq_a 0, ← seq12_eq_a 1]
    decide
  refine ⟨⟨T_iterate_one_int 1, fun k => (a_one_int k).symm, by decide, by rw [p_one_int],
      by decide, by decide⟩,
    ⟨h7, ha7, fun i => by simp only; rw [show i + ((2 : ℕ) : ℤ) + 1 = (i + 1) + (2 : ℕ) by ring,
      seq12_periodic], by decide, by intro i hi1 hi2; interval_cases i; decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩,
    ⟨fun k hk => ?_, ?_, by rw [hp5], by norm_num⟩⟩
  · obtain rfl : k = 0 := by omega
    rw [← seq12_eq_a 0]
    decide
  · rw [← seq12_eq_a (2 - 1)]
    decide

end Syracuse
