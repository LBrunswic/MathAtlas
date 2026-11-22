import Syracuse.CycleGcd

/-!
# Syracuse § 3: ascending and descending indices, the differences `Δ_i = A_{i+1} − A_i`, and the GCD

Every label but `lem:syracuse_cycle` (OQ-101) is marked under DEC-183 (OQ-68; OQ-43: the printed `A_u^n` stands, the other reading is
proved beside it), in corrected form or in the reading of a misprint or an undefined word (SCOPE):

* **`def:syracuse_cycle_period_denote`** — `syracuse.tex:271` (l.271–274) — marked in corrected form
  (DEC-183, OQ-68 (a): `a_i = a_i(x_0) = ν₂(3Tⁱ(x_0) + 1)`, extended `n`-periodically, `aPer`) on
  `Syracuse.ascIdx` and `Syracuse.descIdx`, which partition `ℤ` on every cycle
  (`ascIdx_union_descIdx`, `disjoint_ascIdx_descIdx`, `one_le_of_cycle`). Read literally
  (`a_i := Tⁱ(x_0)`) both sets are empty on the cycle `(−1)` and every index is ascending on `(1)`
  (`literal_neg_one`, `literal_one`): Finding 1.
* **`lem:syracuse_cycle_n__n_`** — `syracuse.tex:275` (l.275–281) — marked in corrected form
  (DEC-183, OQ-68 (b): the exponent `a_{i+1} + ⋯ + a_{i+k−1}`, with `3^{n−k}` for the printed
  `A_u^n`, and `i + k ∈ 𝒟` for « `k ∈ 𝒟` ») on `Syracuse.Delta_eq` and `Syracuse.Delta_eq_asc`
  (`DeltaAlt_eq`, `DeltaAlt_eq_asc` for the other reading of OQ-43). **False as printed** under both
  readings, at every `i` for every `a ≥ 1` of minimal period `n ≥ 2` (`deltaPrinted_ne_of_minimal`;
  at `(−5, −7)`: `syracuse_cycle_n_printed_false`, `syracuse_cycle_n_asc_printed_false`): Finding 2.
* `lem:syracuse_cycle` — `syracuse.tex:283` (l.283–287) — not marked: OQ-101 (DEC-183 rules OQ-68,
  but (c) had one reading proved and one refuted, not two proved). `∼_S` is read as `SEquiv`. Read
  as notation, « let `m = …` » gives the implication as printed, `Syracuse.syracuse_cycle`, for every
  `n`-periodic `a` (`syracuse_cycle_alt` for the other reading of OQ-43). Read
  as an assertion, « `m = GCD(A_i) = 2^{p_n} − 3ⁿ` » is **false as printed**: on every cycle for the
  printed `A_u^n` (`gcd_Aun_ne_of_cycle`), and at the cycle `(−1)` for the other reading
  (`gcd_AunAlt_printed_false`): Finding 4.
* **`cor:intertwined_i_`** — `syracuse.tex:289` (l.289–292) — marked in corrected form (DEC-183,
  OQ-68 (d): `m = GCD(A_i : i ∈ ℤ)`, « intertwined » not needed, `⋀_{i=𝒟}` read as `i ∈ 𝒟`) on
  `Syracuse.corGcd_eq_gcd_Aun`, and at every base point on `intertwined_aun` (`intertwined_alt` for
  the other reading of OQ-43). **False as printed** with `m = 2^{p_n} − 3ⁿ`, at `(−5, −7)` under both
  readings (`intertwined_printed_false`): Finding 5.

> **Upper bounds.** Let $S := \{2^a3^b ~:~ a,b\in \ZZ\}$

> **def:syracuse_cycle_period_denote.** Let $\Gamma=(x_i~:~ i \in \ZZ)$ be syracuse cycle of period
> $n>0$, denote $\forall i\in\ZZ , a_i :=T^i(x_0)$. We denote by $\mathcal A_\Gamma$ the set of
> ascending term  in a give cycle $\Gamma$ and by $\mathcal D_\Gamma$ the set of descending terms :
> $$\A_\Gamma = \{i\in \ZZ~|~ a_i=1\} \quad\quad \D_\Gamma = \{i\in \ZZ~|~ a_i>1\}$$

> **lem:syracuse_cycle_n__n_.** Let $(\Gamma,a)$ be a Syracuse cycle and let $i\in\ZZ$, then
> $$ \Delta_i := A_{i+1}-A_{i} = \sum_{k=1}^{n-1}3^{n-1-k}2^{a_i+\cdots+a_{i+k-1}}
> \left(2^{a_{i+k}}-2^{a_i}\right)$$
> In particular, if $a_i=1$ then :
> $$ \Delta_i = \sum_{k=1,k\in\D}^{n-1}3^{n-1-k}2^{a_i+\cdots+a_{i+k-1}} \left(2^{a_{i+k}}-2\right)$$

> **lem:syracuse_cycle.** Let $(\Gamma,a)$ be a Syracuse cycle, let
> $m = \mathrm{GCD}(A_i ~:~ i\in \ZZ)=2^{p_n}-3^n$ and let $i\in\ZZ$, then, :
> $$a_i=a_{i+1}=1 \quad\Rightarrow \quad\Delta_{i} \sim_S \Delta_{i+1}$$

> **cor:intertwined_i_.** If $\A$ and $\D$ are intertwined.
> $$ m = A_0\bigwedge_{i=\D}\Delta_{i-1} $$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` a Syracuse cycle of period `n > 0` | ✓ `x : ℤ`, `0 < n`, `T^[n] x = x`, where a cycle enters; ⚠ weakened to any `n`-periodic `α : ℤ → ℕ` (with `α ≥ 1` where used) for the algebra, which needs no cycle |
| "`a_i := T^i(x_0)`" (l.271) | a reading: `a_i = a_i(x_0) = ν₂(3Tⁱ(x_0)+1)` (`def:ring_define_2`), extended `n`-periodically to `ℤ` (`aPer`); the literal reading is degenerate (Finding 1) |
| the index of `a_i` (OQ-63 (b)) | immaterial for the algebra (any sequence); the corollary is proved at every base point `A_c`, which covers both conventions |
| `A_i = A_i^n(a)` (OQ-43) | both readings: `Aun` (printed) and `AunAlt` (product to `n − 2 − k`) |
| `S`, "`∼_S`" (l.270, l.286; `∼_S` is not defined) | a reading: `x ∼_S y` iff `x = s y` for some `s ∈ S`, in `ℚ` (`SEquiv`, an equivalence relation) |
| "`m = GCD(A_i : i ∈ ℤ) = 2^{p_n} − 3^n`" (l.284) | stated and refuted as printed (normalized GCD); proved up to sign for `AunAlt`; false for `Aun` (Finding 4) |
| "`k ∈ 𝒟`" (l.280) | read as `i + k ∈ 𝒟` (the terms with `a_{i+k} = 1` vanish); the literal `k ∈ 𝒟` is refuted too |
| "`𝒜` and `𝒟` are intertwined" (l.290; not defined) | ⚠ weakened: the true form needs no such hypothesis; the printed form is refuted for every reading under which the alternating pattern of the cycle `(−5, −7)` is intertwined |
| `⋀_{i ∈ 𝒟}` over the infinite `𝒟` | the universal property (`∀ d, d ∣ m ↔ …`, every `i ∈ ℤ`), and the normalized `Finset.gcd` over one period |

## SCOPE (disclosed)

* **Finding 1 (`def:syracuse_cycle_period_denote`, l.271): "`a_i := T^i(x_0)`" is a misprint.** Read
  literally, `𝒜_Γ = {i | x_i = 1}`: on the cycle `(−1)` both sets are empty, on the cycle `(1)` every
  index is "ascending" though `a_i(1) = 2` (`literal_neg_one`, `literal_one`). Read as
  `a_i = a_i(x_0)`, the two sets partition `ℤ` on every cycle (`ascIdx_union_descIdx`,
  `disjoint_ascIdx_descIdx`, `one_le_of_cycle`), and the names fit: for odd `y > 0`,
  `a_0(y) = 1 ↔ y < T(y)` (`a_zero_eq_one_iff_lt_T`).
* **Finding 2 (`lem:syracuse_cycle_n__n_`, l.277): the display is off by the factor `2^{a_i}`.** For
  every `a : ℤ → ℕ`, `A'_{i+1} − A'_i = ∑_{k=1}^{n−1} 3^{n−1−k} 2^{a_{i+1}+⋯+a_{i+k−1}}
  (2^{a_{i+k}} − 2^{a_i})` (`DeltaAlt_eq`), and for `n`-periodic `a`, `Δ_i = 3Δ'_i` (`Delta_eq`,
  with `3^{n−k}`). The printed right-hand side, with the exponent `a_i + ⋯ + a_{i+k−1}`, is
  `2^{a_i} Δ'_i` (`deltaPrinted_eq`; `3 ·` it is `2^{a_i} Δ_i`, `three_mul_deltaPrinted`), so it
  equals `Δ'_i` or `Δ_i` only where `Δ'_i = 0`: it fails at every `i` for every `a ≥ 1` of minimal
  period `n ≥ 2` (`deltaPrinted_ne_of_minimal`), and holds on fixed points, where both sides vanish
  (`deltaPrinted_period_one`). The cycle `(−5, −7)`, `i = 0`: `Δ_0 = 6`, `Δ'_0 = 2`, printed `4`
  (`syracuse_cycle_n_printed_false`). The same for the case `a_i = 1` (l.280): the true form is
  `DeltaAlt_eq_asc`, `Delta_eq_asc`, the printed side is `2Δ'_i` (`deltaPrintedAsc_eq`), refuted at
  the same point under both readings of `k ∈ 𝒟` (`syracuse_cycle_n_asc_printed_false`).
* **Finding 3 (`lem:syracuse_cycle`, l.286): the implication holds, under both readings.** For
  `n`-periodic `a`, `2^{a_u} A'_{u+1} = 3A'_u + 2^{P} − 3ⁿ` (`two_pow_mul_AunAlt_succ`), so
  `a_i = a_{i+1} = b` gives `3Δ'_i = 2^b Δ'_{i+1}` and `3Δ_i = 2^b Δ_{i+1}`
  (`three_mul_DeltaAlt_of_eq`, `three_mul_Delta_of_eq`); with `b = 1`, `Δ_i = (2/3) Δ_{i+1}`,
  `2/3 ∈ S` (`syracuse_cycle_alt`, `syracuse_cycle`). No cycle is needed.
* **Finding 4 (`lem:syracuse_cycle`, l.284): "`m = GCD(A_i) = 2^{p_n} − 3^n`" is false as printed.**
  For `AunAlt` it holds up to sign on every cycle of `ℤ` (`dvd_iff_dvd_AunAlt_of_cycle`; normalized,
  `gcd_AunAlt_of_cycle` gives `|2^{p_n} − 3ⁿ|`), as printed for `x > 0` (`gcd_AunAlt_of_pos`), and
  fails at the cycle `(−1)` (`gcd_AunAlt_printed_false`), as OQ-63 (a). For `Aun` every `A_i` is
  even and `2^{p_n} − 3ⁿ` is odd, so it fails on every cycle, also up to sign
  (`gcd_Aun_ne_of_cycle`, `not_dvd_iff_dvd_Aun_of_cycle`), as OQ-43.
* **Finding 5 (`cor:intertwined_i_`, l.291): no hypothesis is needed, and the sign fails.** For every
  `n`-periodic `a ≥ 1`, `n ≥ 1`, and every base point `c ∈ ℤ`, `d ∣ A_c ∧ ∀ i ∈ 𝒟, d ∣ Δ_{i−1}` iff
  `d ∣ A_u` for every `u`, under both readings (`intertwined_alt`, `intertwined_aun`): the GCD of
  `A_c` and the `Δ_{i−1}`, `i ∈ 𝒟`, is the GCD of all the `A_u`, whatever "intertwined" means, and
  no cycle is needed. The proof (none is printed): with `X_u = A'_u` and `δ = 2^P − 3ⁿ`,
  `2^{a_u} X_{u+1} = 3X_u + δ`; an ascending step fixes `−δ`, so `d ∣ X_c` and the first `i ∈ 𝒟`
  after `c` force `d ∣ δ` (`dvd_delta_of_intertwined`); for `Aun` the odd part goes through
  `A_u = 2^{a_u} A'_{u+1}` and the `2`-part through `ν₂(A_u) = a_u`
  (`odd_dvd_Aun_of_intertwined`, `not_four_dvd_of_intertwined`). On a cycle of `ℤ` the GCD is
  `|2^{p_n} − 3ⁿ|` for `AunAlt` (`intertwined_alt_cycle`, `corGcdAlt_of_cycle`): the printed `m`
  for `x > 0`, `−m` for `x < 0` (`corGcdAlt_of_pos`, `corGcdAlt_of_neg`); for `Aun` it is the even
  `GCD(A_i)` (`corGcd_eq_gcd_Aun`). With `m = 2^{p_n} − 3ⁿ` the printed equality fails at
  `(−5, −7)` for both readings, for any reading of "intertwined" that admits its alternating
  pattern (`intertwined_printed_false`).
* **Finding 6 (the planner's numerics).** On the cycles of `1, −1, −5, −17` (sequences `(2)`, `(1)`,
  `(1, 2)`, `(1, 1, 1, 2, 1, 1, 4)`, checked against `a(x)`): `2^{p_n} − 3ⁿ = 1, −1, −1, −139`; the
  corollary's GCD is `1, 1, 1, 139` for `AunAlt` and `4, 2, 2, 278` for `Aun`, and the printed
  `GCD(A_i)` is `4, 2, 2, 278` (`four_cycles`, `cycle_neg_seventeen`). The planner's "`2m` for
  `Aun`" fails at the cycle `(1)`, where `a ≡ 2`, every `A_i = 4` and `m = 1`
  (`four_cycles_two_m_false`).
* `T`, `a`, `p` are the total maps of `Syracuse.Base`, the paper's over `ℤ` (`not_isUnit_three_int`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset

/-! ### Periodic sequences on `ℤ` -/

/-- A function of period `n` on `ℤ` takes at `i` its value at `i mod n`. -/
theorem periodic_emod {β : Type*} {g : ℤ → β} {n : ℕ} (hg : Function.Periodic g n) (i : ℤ) :
    g i = g (i % n) := by
  have h := (hg.int_mul (i / n)) (i % n)
  simp only [Int.cast_id] at h
  rw [show i % (n : ℤ) + i / (n : ℤ) * (n : ℤ) = i by rw [mul_comm]; exact Int.emod_add_mul_ediv i n] at h
  exact h

/-- On an `n`-cycle of `ℤ`, every `n`-periodic extension of `(a_k(x))_k` is `≥ 1`. -/
theorem one_le_of_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) : ∀ i, 1 ≤ α i := by
  intro i
  obtain ⟨hodd, havoid⟩ := cycle_avoids_neg_third (A := ℤ) two_ne_zero hn hx
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  rw [periodic_emod hper i,
    show i % (n : ℤ) = (((i % n).toNat : ℕ) : ℤ) from
      (Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')).symm, hα]
  exact one_le_a (T_iterate_odd hodd (fun k _ => havoid k))

/-! ### `def:syracuse_cycle_period_denote` -/

/-- `𝒜_Γ = {i ∈ ℤ | a_i = 1}`, the ascending indices (`syracuse.tex:273`), of a sequence `α`. -/
def ascIdx (α : ℤ → ℕ) : Set ℤ := {i | α i = 1}

/-- `𝒟_Γ = {i ∈ ℤ | a_i > 1}`, the descending indices (`syracuse.tex:273`). -/
def descIdx (α : ℤ → ℕ) : Set ℤ := {i | 1 < α i}

/-- `𝒜` and `𝒟` cover `ℤ` when `α ≥ 1` (on a cycle: `one_le_of_cycle`). -/
theorem ascIdx_union_descIdx {α : ℤ → ℕ} (h : ∀ i, 1 ≤ α i) :
    ascIdx α ∪ descIdx α = Set.univ := by
  ext i
  simp only [ascIdx, descIdx, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have := h i
  omega

/-- `𝒜` and `𝒟` are disjoint. -/
theorem disjoint_ascIdx_descIdx (α : ℤ → ℕ) : Disjoint (ascIdx α) (descIdx α) := by
  refine Set.disjoint_left.2 (fun i h1 h2 => ?_)
  simp only [ascIdx, descIdx, Set.mem_setOf_eq] at h1 h2
  omega

/-- The names fit: an odd `y > 0` is ascending (`a_0(y) = 1`) iff `y < T(y)`. -/
theorem a_zero_eq_one_iff_lt_T {y : ℤ} (hy : 0 < y) (hodd : Odd y) : a 0 y = 1 ↔ y < T y := by
  have hT := pow_v2_mul_T y
  have ha : a 0 y = v2 (3 * y + 1) := by simp [a]
  have hTpos : 0 < T y := T_pos_of_nonneg_int hy.le
  have h1 : 1 ≤ a 0 y := one_le_a (n := 0) (by simpa using hodd)
  rw [ha] at h1 ⊢
  constructor
  · intro h
    rw [h, pow_one] at hT
    linarith
  · intro hlt
    by_contra hne
    have h2 : 2 ≤ v2 (3 * y + 1) := by omega
    have h4 : (4 : ℤ) ≤ 2 ^ v2 (3 * y + 1) := by
      calc (4 : ℤ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ v2 (3 * y + 1) := pow_le_pow_right₀ (by norm_num) h2
    nlinarith

/-- The points `x_i = T^{i mod n}(x_0)`, `i ∈ ℤ`, of the cycle through `x_0`. -/
noncomputable def cyclePt (n : ℕ) (x : ℤ) (i : ℤ) : ℤ := T^[(i % (n : ℤ)).toNat] x

/-- The literal reading of l.271 (`a_i := T^i(x_0)`): `{i | x_i = 1}`. -/
def ascIdxLit (n : ℕ) (x : ℤ) : Set ℤ := {i | cyclePt n x i = 1}

/-- The literal reading of l.271: `{i | x_i > 1}`. -/
def descIdxLit (n : ℕ) (x : ℤ) : Set ℤ := {i | 1 < cyclePt n x i}

/-- **Finding 1.** On the cycle `(−1)` the literal sets are empty, though every index is ascending
(`a_i(−1) = 1`). -/
theorem literal_neg_one :
    ascIdxLit 1 (-1) = ∅ ∧ descIdxLit 1 (-1) = ∅ ∧ ascIdx (aPer 1 (-1 : ℤ)) = Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · ext i; simp [ascIdxLit, cyclePt, T_iterate_neg_one_int]
  · ext i; simp [descIdxLit, cyclePt, T_iterate_neg_one_int]
  · ext i; simp [ascIdx, aPer, a_neg_one_int]

/-- **Finding 1.** On the cycle `(1)` every index is literally "ascending", though `a_i(1) = 2`:
every index is descending. -/
theorem literal_one :
    ascIdxLit 1 1 = Set.univ ∧ descIdxLit 1 1 = ∅ ∧ ascIdx (aPer 1 (1 : ℤ)) = ∅ ∧
      descIdx (aPer 1 (1 : ℤ)) = Set.univ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i; simp [ascIdxLit, cyclePt, T_iterate_one_int]
  · ext i; simp [descIdxLit, cyclePt, T_iterate_one_int]
  · ext i; simp [ascIdx, aPer, a_one_int]
  · ext i; simp [descIdx, aPer, a_one_int]

/-! ### The algebra of `A_u^n` and `A'^n_u` -/

/-- `A'^n_u = ∑_{j<n} 3^{n−1−j} 2^{a_u+⋯+a_{u+j−1}}`. -/
theorem AunAlt_eq_sum_rev (n : ℕ) (u : ℤ) (α : ℤ → ℕ) :
    (AunAlt n u α : ℤ) = ∑ j ∈ range n, (3 : ℤ) ^ (n - 1 - j) * 2 ^ (∑ t ∈ range j, α (u + t)) := by
  rw [AunAlt_eq_sum]
  push_cast
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  rw [show n - 1 - (n - 1 - j) = j by omega]

/-- `A_u^n = 2^{a_u} A'^n_{u+1}`, for every `a` and `n`. -/
theorem Aun_eq_two_pow_mul (n : ℕ) (u : ℤ) (α : ℤ → ℕ) :
    Aun n u α = 2 ^ α u * AunAlt n (u + 1) α := by
  rw [Aun_eq_sum, AunAlt_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  rw [show n - k = (n - 1 - k) + 1 by omega, Finset.sum_range_succ']
  have e : ∑ t ∈ range (n - 1 - k), α (u + ((t + 1 : ℕ) : ℤ)) =
      ∑ t ∈ range (n - 1 - k), α (u + 1 + t) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    congr 1
    push_cast
    ring
  rw [e, Nat.cast_zero, add_zero, pow_add]
  ring

/-- For `n`-periodic `a`, `A_u^n = 3 A'^n_u + 2^P − 3ⁿ`, `P = ∑_{t<n} a_t`. -/
theorem Aun_eq_three_mul_add {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (u : ℤ) :
    (Aun n u α : ℤ) = 3 * AunAlt n u α + (2 ^ (∑ t ∈ range n, α t) - 3 ^ n) := by
  rw [Aun_eq_three_mul_AunAlt, sum_range_periodic h u]
  ring

/-- The step of a periodic sequence: `2^{a_u} A'_{u+1} = 3 A'_u + 2^P − 3ⁿ` (on a cycle, `2^{p_n} − 3ⁿ`
times `2^{a_u} x_{u+1} = 3x_u + 1`). -/
theorem two_pow_mul_AunAlt_succ {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (u : ℤ) :
    (2 : ℤ) ^ α u * AunAlt n (u + 1) α = 3 * AunAlt n u α + (2 ^ (∑ t ∈ range n, α t) - 3 ^ n) := by
  have h1 : ((Aun n u α : ℕ) : ℤ) = (2 : ℤ) ^ α u * AunAlt n (u + 1) α := by
    rw [Aun_eq_two_pow_mul]
    push_cast
    ring
  rw [← h1, Aun_eq_three_mul_add h]

/-- `u ↦ A'^n_u` is `n`-periodic when `a` is. -/
theorem AunAlt_periodic {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) :
    Function.Periodic (fun u : ℤ => AunAlt n u α) n := by
  intro u
  simp only [AunAlt]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [show u + (n : ℤ) + (i : ℤ) = (u + i) + n by ring, h]

/-- `u ↦ A^n_u` is `n`-periodic when `a` is. -/
theorem Aun_periodic {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) :
    Function.Periodic (fun u : ℤ => Aun n u α) n := by
  intro u
  simp only [Aun]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [show u + (n : ℤ) + (i : ℤ) = (u + i) + n by ring, h]

/-- `A'^n_u` is odd when `n ≥ 1` and `a ≥ 1`. -/
theorem AunAlt_odd {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n) (u : ℤ) :
    Odd (AunAlt n u α) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [AunAlt_eq_sum, Finset.sum_range_succ, show m + 1 - 1 - m = 0 by omega, Finset.sum_range_zero,
    pow_zero, mul_one]
  refine Even.add_odd ?_ (Odd.pow ⟨1, rfl⟩)
  rw [even_iff_two_dvd]
  refine Finset.dvd_sum (fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  refine dvd_mul_of_dvd_right (dvd_pow_self 2 ?_) _
  have h0 : 0 ∈ range (m + 1 - 1 - k) := Finset.mem_range.2 (by omega)
  have hle := Finset.single_le_sum (f := fun t : ℕ => α (u + t)) (fun _ _ => Nat.zero_le _) h0
  have h1 := hpos (u + ((0 : ℕ) : ℤ))
  omega

/-- `3 ∤ A'^n_u` when `n ≥ 1`. -/
theorem not_three_dvd_AunAlt {α : ℤ → ℕ} {n : ℕ} (hn : 0 < n) (u : ℤ) :
    ¬ (3 : ℤ) ∣ (AunAlt n u α : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h3
  rw [AunAlt_eq_sum, Finset.sum_range_succ'] at h3
  push_cast at h3
  have h1 : (3 : ℤ) ∣ ∑ k ∈ range m,
      (3 : ℤ) ^ (k + 1) * 2 ^ (∑ t ∈ range (m + 1 - 1 - (k + 1)), α (u + t)) :=
    Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_left (dvd_pow_self 3 (Nat.succ_ne_zero k)) _)
  have h2 := (dvd_add_right h1).1 h3
  rw [one_mul] at h2
  exact absurd (Int.prime_three.dvd_of_dvd_pow h2) (by norm_num)

/-- `2^P − 3ⁿ` is odd and prime to `3` when `n ≥ 1` and `a ≥ 1`. -/
theorem delta_odd_not_three_dvd {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n) :
    Odd ((2 : ℤ) ^ (∑ t ∈ range n, α t) - 3 ^ n) ∧
      ¬ (3 : ℤ) ∣ (2 : ℤ) ^ (∑ t ∈ range n, α t) - 3 ^ n := by
  have hP : 1 ≤ ∑ t ∈ range n, α t := by
    have := Finset.single_le_sum (f := fun t : ℕ => α t) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hn)
    have := hpos ((0 : ℕ) : ℤ)
    omega
  constructor
  · obtain ⟨P', hP'⟩ : ∃ P', ∑ t ∈ range n, α t = P' + 1 := ⟨∑ t ∈ range n, α t - 1, by omega⟩
    rw [hP', pow_succ]
    exact Even.sub_odd (even_two.mul_left _) (Odd.pow ⟨1, by norm_num⟩)
  · intro h
    have h3 : (3 : ℤ) ∣ 3 ^ n := dvd_pow_self 3 hn.ne'
    have h2 : (3 : ℤ) ∣ 2 ^ (∑ t ∈ range n, α t) := by
      have := dvd_add h h3
      rwa [sub_add_cancel] at this
    exact absurd (Int.prime_three.dvd_of_dvd_pow h2) (by norm_num)

/-! ### `lem:syracuse_cycle_n__n_` -/

/-- `Δ_i = A_{i+1} − A_i` (`syracuse.tex:277`), printed `A_u^n`, in `ℤ`. -/
def Delta (n : ℕ) (α : ℤ → ℕ) (i : ℤ) : ℤ := (Aun n (i + 1) α : ℤ) - Aun n i α

/-- `Δ'_i = A'_{i+1} − A'_i`, the reading of OQ-43. -/
def DeltaAlt (n : ℕ) (α : ℤ → ℕ) (i : ℤ) : ℤ := (AunAlt n (i + 1) α : ℤ) - AunAlt n i α

/-- The printed right-hand side of l.277:
`∑_{k=1}^{n−1} 3^{n−1−k} 2^{a_i+⋯+a_{i+k−1}} (2^{a_{i+k}} − 2^{a_i})`. -/
def deltaPrinted (n : ℕ) (α : ℤ → ℕ) (i : ℤ) : ℤ :=
  ∑ k ∈ Icc 1 (n - 1), (3 : ℤ) ^ (n - 1 - k) * 2 ^ (∑ t ∈ range k, α (i + t)) *
    (2 ^ α (i + k) - 2 ^ α i)

/-- The printed right-hand side of l.280 (case `a_i = 1`), reading `k ∈ 𝒟` as `i + k ∈ 𝒟`. -/
def deltaPrintedAsc (n : ℕ) (α : ℤ → ℕ) (i : ℤ) : ℤ :=
  ∑ k ∈ (Icc 1 (n - 1)).filter (fun k : ℕ => 1 < α (i + k)), (3 : ℤ) ^ (n - 1 - k) *
    2 ^ (∑ t ∈ range k, α (i + t)) * (2 ^ α (i + k) - 2)

/-- The printed right-hand side of l.280, reading `k ∈ 𝒟` literally (`a_k > 1`). -/
def deltaPrintedAscLit (n : ℕ) (α : ℤ → ℕ) (i : ℤ) : ℤ :=
  ∑ k ∈ (Icc 1 (n - 1)).filter (fun k : ℕ => 1 < α k), (3 : ℤ) ^ (n - 1 - k) *
    2 ^ (∑ t ∈ range k, α (i + t)) * (2 ^ α (i + k) - 2)

/-- The true right-hand side: `∑_{k=1}^{n−1} 3^{n−1−k} 2^{a_{i+1}+⋯+a_{i+k−1}} (2^{a_{i+k}} − 2^{a_i})`. -/
def deltaTrue (n : ℕ) (α : ℤ → ℕ) (i : ℤ) : ℤ :=
  ∑ k ∈ Icc 1 (n - 1), (3 : ℤ) ^ (n - 1 - k) * 2 ^ (∑ t ∈ range (k - 1), α (i + 1 + t)) *
    (2 ^ α (i + k) - 2 ^ α i)

/-- **`lem:syracuse_cycle_n__n_`, true form, OQ-43 reading**: `Δ'_i = deltaTrue`, for every `a : ℤ → ℕ`
and `n` (no periodicity, no cycle). -/
theorem DeltaAlt_eq (n : ℕ) (α : ℤ → ℕ) (i : ℤ) : DeltaAlt n α i = deltaTrue n α i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [DeltaAlt, deltaTrue, AunAlt]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [DeltaAlt, AunAlt_eq_sum_rev, AunAlt_eq_sum_rev, ← Finset.sum_sub_distrib,
    Finset.sum_range_succ', deltaTrue, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp only [Finset.range_zero, Finset.sum_empty, sub_self, add_zero,
    show m + 1 - 1 + 1 - 1 = m by omega]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have e : ∑ t ∈ range j, α (i + ((t + 1 : ℕ) : ℤ)) = ∑ t ∈ range j, α (i + 1 + t) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    congr 1
    push_cast
    ring
  rw [e, show 1 + j - 1 = j by omega, show i + ((1 + j : ℕ) : ℤ) = i + 1 + j by push_cast; ring,
    show m + 1 - 1 - (j + 1) = m + 1 - 1 - (1 + j) by omega, Nat.cast_zero, add_zero, pow_add, pow_add]
  ring

/-- For `n`-periodic `a`, `Δ_i = 3 Δ'_i`. -/
theorem Delta_eq_three_mul {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (i : ℤ) :
    Delta n α i = 3 * DeltaAlt n α i := by
  simp only [Delta, DeltaAlt]
  exact Aun_sub_eq_three_mul h (i + 1) i

/-- **`lem:syracuse_cycle_n__n_`, true form, printed `A_u^n`**: for `n`-periodic `a`,
`Δ_i = ∑_{k=1}^{n−1} 3^{n−k} 2^{a_{i+1}+⋯+a_{i+k−1}} (2^{a_{i+k}} − 2^{a_i})`. -/
theorem Delta_eq {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (i : ℤ) :
    Delta n α i = ∑ k ∈ Icc 1 (n - 1), (3 : ℤ) ^ (n - k) *
      2 ^ (∑ t ∈ range (k - 1), α (i + 1 + t)) * (2 ^ α (i + k) - 2 ^ α i) := by
  rw [Delta_eq_three_mul h, DeltaAlt_eq, deltaTrue, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_Icc.1 hk
  rw [show n - k = n - 1 - k + 1 by omega, pow_succ]
  ring

/-- **Finding 2.** The printed right-hand side is `2^{a_i} Δ'_i`, for every `a` (and `3 ·` it is
`2^{a_i} Δ_i` for periodic `a`). -/
theorem deltaPrinted_eq (n : ℕ) (α : ℤ → ℕ) (i : ℤ) :
    deltaPrinted n α i = 2 ^ α i * DeltaAlt n α i := by
  rw [DeltaAlt_eq, deltaPrinted, deltaTrue, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_Icc.1 hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have e : ∑ t ∈ range j, α (i + ((t + 1 : ℕ) : ℤ)) = ∑ t ∈ range j, α (i + 1 + t) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    congr 1
    push_cast
    ring
  rw [e, Nat.add_sub_cancel, Nat.cast_zero, add_zero, pow_add]
  ring

/-- **Finding 2**, printed `A_u^n`: `3 · (printed) = 2^{a_i} Δ_i` for periodic `a`. -/
theorem three_mul_deltaPrinted {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (i : ℤ) :
    3 * deltaPrinted n α i = 2 ^ α i * Delta n α i := by
  rw [deltaPrinted_eq, Delta_eq_three_mul h]
  ring

/-- On fixed points (`n = 1`) the printed display holds, trivially: both sides are `0`. -/
theorem deltaPrinted_period_one {α : ℤ → ℕ} (h : Function.Periodic α 1) (i : ℤ) :
    deltaPrinted 1 α i = 0 ∧ Delta 1 α i = 0 ∧ DeltaAlt 1 α i = 0 := by
  refine ⟨by simp [deltaPrinted], ?_, by simp [DeltaAlt, AunAlt]⟩
  have hi : α (i + 1) = α i := by simpa using h i
  simp [Delta, Aun_one, hi]

/-- **Finding 2**, everywhere: for `a ≥ 1` of minimal period `n ≥ 2` the printed display fails at
every `i ∈ ℤ`, for both readings of OQ-43. -/
theorem deltaPrinted_ne_of_minimal {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 2 ≤ n)
    (hper : Function.Periodic α n) (hmin : ∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m)
    (i : ℤ) : DeltaAlt n α i ≠ deltaPrinted n α i ∧ Delta n α i ≠ deltaPrinted n α i := by
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn0
  have hD : DeltaAlt n α i ≠ 0 := by
    intro h0
    have hP := AunAlt_periodic hper
    have e1 := periodic_emod hP (i + 1)
    have e2 := periodic_emod hP i
    have hne : (i + 1) % (n : ℤ) ≠ i % (n : ℤ) := by
      intro heq
      have hd := Int.ModEq.dvd heq
      rw [show i - (i + 1) = -1 by ring, dvd_neg] at hd
      have := Int.le_of_dvd one_pos hd
      omega
    apply AunAlt_sub_ne_zero_of_minimal hpos hper hmin (Int.emod_nonneg _ hn'.ne')
      (by have := Int.emod_lt_of_pos (i + 1) hn'; omega) (Int.emod_nonneg _ hn'.ne')
      (by have := Int.emod_lt_of_pos i hn'; omega) hne
    rw [← e1, ← e2]
    exact h0
  have hev : Even ((2 : ℤ) ^ α i) := Int.even_pow.2 ⟨even_two, by have := hpos i; omega⟩
  have h2 : (2 : ℤ) ≤ 2 ^ α i := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ α i := pow_le_pow_right₀ (by norm_num) (hpos i)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [deltaPrinted_eq] at h
    have : ((2 : ℤ) ^ α i - 1) * DeltaAlt n α i = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact hD h'
  · rw [deltaPrinted_eq, Delta_eq_three_mul hper] at h
    have : ((2 : ℤ) ^ α i - 3) * DeltaAlt n α i = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · have h3 : (2 : ℤ) ^ α i = 3 := by linarith
      rw [h3] at hev
      exact absurd hev (by decide)
    · exact hD h'

/-- **`lem:syracuse_cycle_n__n_`, the case `a_i = 1`, true form, OQ-43 reading** (`a ≥ 1`):
`Δ'_i = ∑_{k ∈ ⟦1, n−1⟧, i+k ∈ 𝒟} 3^{n−1−k} 2^{a_{i+1}+⋯+a_{i+k−1}} (2^{a_{i+k}} − 2)`. -/
theorem DeltaAlt_eq_asc {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) (n : ℕ) {i : ℤ} (hi : α i = 1) :
    DeltaAlt n α i = ∑ k ∈ (Icc 1 (n - 1)).filter (fun k : ℕ => 1 < α (i + k)), (3 : ℤ) ^ (n - 1 - k) *
      2 ^ (∑ t ∈ range (k - 1), α (i + 1 + t)) * (2 ^ α (i + k) - 2) := by
  rw [DeltaAlt_eq, deltaTrue, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hi, pow_one]
  split_ifs with hk
  · rfl
  · have : α (i + k) = 1 := by have := hpos (i + k); omega
    rw [this]
    ring

/-- The case `a_i = 1`, true form, printed `A_u^n` (periodic `a ≥ 1`), with `3^{n−k}`. -/
theorem Delta_eq_asc {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (h : Function.Periodic α n) {i : ℤ}
    (hi : α i = 1) :
    Delta n α i = ∑ k ∈ (Icc 1 (n - 1)).filter (fun k : ℕ => 1 < α (i + k)), (3 : ℤ) ^ (n - k) *
      2 ^ (∑ t ∈ range (k - 1), α (i + 1 + t)) * (2 ^ α (i + k) - 2) := by
  rw [Delta_eq h, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hi, pow_one]
  split_ifs with hk
  · rfl
  · have : α (i + k) = 1 := by have := hpos (i + k); omega
    rw [this]
    ring

/-- **Finding 2**, the case `a_i = 1`: the printed right-hand side of l.280 is `2 Δ'_i` (`a ≥ 1`). -/
theorem deltaPrintedAsc_eq {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) (n : ℕ) {i : ℤ} (hi : α i = 1) :
    deltaPrintedAsc n α i = 2 * DeltaAlt n α i := by
  have e : deltaPrintedAsc n α i = deltaPrinted n α i := by
    rw [deltaPrintedAsc, deltaPrinted, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hi, pow_one]
    split_ifs with hk
    · rfl
    · have : α (i + k) = 1 := by have := hpos (i + k); omega
      rw [this]
      ring
  rw [e, deltaPrinted_eq, hi, pow_one]

/-- The `2`-periodic sequence `(1, 2)` of the cycle `(−5, −7)`. -/
def seq12 (i : ℤ) : ℕ := if i % 2 = 0 then 1 else 2

theorem seq12_periodic : Function.Periodic seq12 (2 : ℕ) := by
  intro i
  simp [seq12]

/-- `seq12` is `a(−5)`: `a_0(−5) = ν₂(−14) = 1`, `a_1(−5) = ν₂(−20) = 2`. -/
theorem seq12_eq_a (k : ℕ) : seq12 k = a k (-5 : ℤ) := by
  have h5 := T_unique (A := ℤ) two_ne_zero (x := -5) (t := -7) (k := 1) ⟨-4, by norm_num⟩
    (by norm_num)
  have h7 := T_unique (A := ℤ) two_ne_zero (x := -7) (t := -5) (k := 2) ⟨-3, by norm_num⟩
    (by norm_num)
  have hx : T^[2] (-5 : ℤ) = -5 := cycle_neg_five.1
  have hper : ∀ k, a (k + 2) (-5 : ℤ) = a k (-5 : ℤ) :=
    (periodic_a_iff_periodic_T (-5 : ℤ) 2).2 (fun k => by rw [Function.iterate_add_apply, hx])
  have e := Function.Periodic.map_mod_nat (f := fun k => a k (-5 : ℤ)) hper k
  rw [← e]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have hk2 : (k : ℤ) % 2 = 0 := by omega
    rw [hk, seq12, if_pos hk2, a, Function.iterate_zero_apply]
    exact h5.1
  · have hk2 : ¬ (k : ℤ) % 2 = 0 := by omega
    rw [hk, seq12, if_neg hk2, a, Function.iterate_one, h5.2]
    exact h7.1

/-- **Finding 2.** `lem:syracuse_cycle_n__n_` as printed is false, for both readings of OQ-43: the cycle
`(−5, −7)`, `i = 0`, where `Δ_0 = 6`, `Δ'_0 = 2` and the printed right-hand side is `4`. -/
theorem syracuse_cycle_n_printed_false :
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → ∀ i : ℤ, Delta n α i = deltaPrinted n α i) ∧
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → ∀ i : ℤ, DeltaAlt n α i = deltaPrinted n α i) := by
  have hx : T^[2] (-5 : ℤ) = -5 := cycle_neg_five.1
  have e1 : Delta 2 seq12 0 = 6 := by decide
  have e2 : DeltaAlt 2 seq12 0 = 2 := by decide
  have e3 : deltaPrinted 2 seq12 0 = 4 := by decide
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a 0
    rw [e1, e3] at this
    norm_num at this
  · have := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a 0
    rw [e2, e3] at this
    norm_num at this

/-- **Finding 2**, the case `a_i = 1` (l.280): false as printed for both readings of OQ-43 and both
readings of `k ∈ 𝒟`, at the cycle `(−5, −7)`, `i = 0` (`a_0 = 1`). -/
theorem syracuse_cycle_n_asc_printed_false :
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → ∀ i : ℤ, α i = 1 → Delta n α i = deltaPrintedAsc n α i) ∧
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → ∀ i : ℤ, α i = 1 → DeltaAlt n α i = deltaPrintedAsc n α i) ∧
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → ∀ i : ℤ, α i = 1 → Delta n α i = deltaPrintedAscLit n α i) ∧
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → ∀ i : ℤ, α i = 1 → DeltaAlt n α i = deltaPrintedAscLit n α i) := by
  have hx : T^[2] (-5 : ℤ) = -5 := cycle_neg_five.1
  have h0 : seq12 0 = 1 := by decide
  have e1 : Delta 2 seq12 0 = 6 := by decide
  have e2 : DeltaAlt 2 seq12 0 = 2 := by decide
  have e3 : deltaPrintedAsc 2 seq12 0 = 4 := by decide
  have e4 : deltaPrintedAscLit 2 seq12 0 = 4 := by decide
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a 0 h0
    rw [e1, e3] at this
    norm_num at this
  · have := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a 0 h0
    rw [e2, e3] at this
    norm_num at this
  · have := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a 0 h0
    rw [e1, e4] at this
    norm_num at this
  · have := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a 0 h0
    rw [e2, e4] at this
    norm_num at this

/-! ### `lem:syracuse_cycle` -/

/-- `S = {2^a 3^b : a, b ∈ ℤ}` (`syracuse.tex:270`), in `ℚ`. -/
def S23 : Set ℚ := {s | ∃ u v : ℤ, s = (2 : ℚ) ^ u * 3 ^ v}

/-- `x ∼_S y` (l.286, not defined in the paper), read as `x = s y` for some `s ∈ S`. -/
def SEquiv (x y : ℚ) : Prop := ∃ s ∈ S23, x = s * y

/-- `∼_S` is an equivalence relation (`S` is a subgroup of `ℚ^×`). -/
theorem sEquiv_equivalence : Equivalence SEquiv := by
  refine ⟨fun x => ⟨1, ⟨0, 0, by norm_num⟩, by ring⟩, ?_, ?_⟩
  · rintro x y ⟨s, ⟨u, v, rfl⟩, rfl⟩
    refine ⟨2 ^ (-u) * 3 ^ (-v), ⟨-u, -v, rfl⟩, ?_⟩
    rw [zpow_neg, zpow_neg]
    field_simp
  · rintro x y z ⟨s, ⟨u, v, rfl⟩, rfl⟩ ⟨t, ⟨u', v', rfl⟩, rfl⟩
    refine ⟨2 ^ (u + u') * 3 ^ (v + v'), ⟨_, _, rfl⟩, ?_⟩
    rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
    ring

/-- `a_i = a_{i+1} = b` gives `3 Δ'_i = 2^b Δ'_{i+1}` (periodic `a`). -/
theorem three_mul_DeltaAlt_of_eq {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) {i : ℤ} {b : ℕ}
    (hi : α i = b) (hi1 : α (i + 1) = b) : 3 * DeltaAlt n α i = 2 ^ b * DeltaAlt n α (i + 1) := by
  have e1 := two_pow_mul_AunAlt_succ h i
  have e2 := two_pow_mul_AunAlt_succ h (i + 1)
  rw [hi] at e1
  rw [hi1] at e2
  simp only [DeltaAlt]
  linear_combination e1 - e2

/-- `a_i = a_{i+1} = b` gives `3 Δ_i = 2^b Δ_{i+1}` (periodic `a`, printed `A_u^n`). -/
theorem three_mul_Delta_of_eq {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) {i : ℤ} {b : ℕ}
    (hi : α i = b) (hi1 : α (i + 1) = b) : 3 * Delta n α i = 2 ^ b * Delta n α (i + 1) := by
  rw [Delta_eq_three_mul h, Delta_eq_three_mul h]
  have := three_mul_DeltaAlt_of_eq h hi hi1
  linear_combination 3 * this

/-- **The implication of `lem:syracuse_cycle`, OQ-43 reading**: `a_i = a_{i+1} = 1 ⇒ Δ'_i ∼_S Δ'_{i+1}`,
with `Δ'_i = (2/3) Δ'_{i+1}`, for every `n`-periodic `a` (every cycle). -/
theorem syracuse_cycle_alt {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) {i : ℤ}
    (hi : α i = 1) (hi1 : α (i + 1) = 1) :
    SEquiv (DeltaAlt n α i) (DeltaAlt n α (i + 1)) ∧
      (DeltaAlt n α i : ℚ) = 2 / 3 * DeltaAlt n α (i + 1) := by
  have e := three_mul_DeltaAlt_of_eq h hi hi1
  have hq : (DeltaAlt n α i : ℚ) = 2 / 3 * DeltaAlt n α (i + 1) := by
    have : (3 : ℚ) * DeltaAlt n α i = 2 ^ 1 * DeltaAlt n α (i + 1) := by exact_mod_cast e
    linarith
  exact ⟨⟨2 / 3, ⟨1, -1, by norm_num⟩, hq⟩, hq⟩

/-- **The implication of `lem:syracuse_cycle`, printed `A_u^n`**: `a_i = a_{i+1} = 1 ⇒ Δ_i ∼_S Δ_{i+1}`. -/
theorem syracuse_cycle {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) {i : ℤ}
    (hi : α i = 1) (hi1 : α (i + 1) = 1) :
    SEquiv (Delta n α i) (Delta n α (i + 1)) ∧ (Delta n α i : ℚ) = 2 / 3 * Delta n α (i + 1) := by
  have e := three_mul_Delta_of_eq h hi hi1
  have hq : (Delta n α i : ℚ) = 2 / 3 * Delta n α (i + 1) := by
    have : (3 : ℚ) * Delta n α i = 2 ^ 1 * Delta n α (i + 1) := by exact_mod_cast e
    linarith
  exact ⟨⟨2 / 3, ⟨1, -1, by norm_num⟩, hq⟩, hq⟩

/-- **"`m = GCD(A_i : i ∈ ℤ) = 2^{p_n} − 3ⁿ`", OQ-43 reading, up to sign**: on every cycle of `ℤ`,
the common divisors of all the `A'_u`, `u ∈ ℤ`, are those of `2^{p_n(x)} − 3ⁿ`. -/
theorem dvd_iff_dvd_AunAlt_of_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) (d : ℤ) :
    d ∣ (2 : ℤ) ^ p n x - 3 ^ n ↔ ∀ u : ℤ, d ∣ (AunAlt n u α : ℤ) := by
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  constructor
  · intro hd u
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have e := periodic_emod (AunAlt_periodic hper) u
    rw [e, show u % (n : ℤ) = (((u % n).toNat : ℕ) : ℤ) from
      (Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')).symm, (Aun_cast_of_cycle hx α hα _).2]
    exact dvd_mul_of_dvd_left hd _
  · intro hd
    have e := two_pow_mul_AunAlt_succ hper 0
    rw [← hP, zero_add] at e
    have : (2 : ℤ) ^ p n x - 3 ^ n = 2 ^ α 0 * AunAlt n 1 α - 3 * AunAlt n 0 α := by
      linear_combination -e
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right (hd _) _) (dvd_mul_of_dvd_right (hd _) _)

/-- The same, normalized: `GCD(A'_u : u ∈ ⟦0, n−1⟧) = |2^{p_n(x)} − 3ⁿ|` on every cycle of `ℤ`. -/
theorem gcd_AunAlt_of_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hα : ∀ k : ℕ, α k = a k x) :
    (range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ)) = |(2 : ℤ) ^ p n x - 3 ^ n| := by
  exact gcd_eq_abs_of_cycle hn hx 0 (fun l : ℕ => (AunAlt n l α : ℤ))
    (fun l => by rw [add_zero]; exact (Aun_cast_of_cycle hx α hα l).2)

/-- "`m = GCD(A_i) = 2^{p_n} − 3ⁿ`" as printed holds for the OQ-43 reading on the cycles of `x > 0`. -/
theorem gcd_AunAlt_of_pos {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hα : ∀ k : ℕ, α k = a k x) :
    (range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ)) = (2 : ℤ) ^ p n x - 3 ^ n := by
  have hpos := two_pow_p_sub_three_pow_mul_pos hn hx
  rw [gcd_AunAlt_of_cycle hn hx hα, abs_of_pos (pos_of_mul_pos_left hpos hx0.le)]

/-- **Finding 4**, OQ-43 reading: "`GCD(A_i) = 2^{p_n} − 3ⁿ`" as printed is false at the cycle `(−1)`. -/
theorem gcd_AunAlt_printed_false :
    ¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) →
      (range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ)) = (2 : ℤ) ^ p n x - 3 ^ n := by
  intro h
  have hx : T^[1] (-1 : ℤ) = -1 := T_iterate_neg_one_int 1
  have hα : ∀ k : ℕ, (fun _ : ℤ => (1 : ℕ)) (k : ℤ) = a k (-1 : ℤ) := fun k => (a_neg_one_int k).symm
  have hper : Function.Periodic (fun _ : ℤ => (1 : ℕ)) (1 : ℕ) := fun _ => rfl
  have h1 := h (-1) 1 one_pos hx _ hper hα
  rw [gcd_AunAlt_of_cycle one_pos hx hα, p_neg_one_int] at h1
  norm_num at h1

/-- Every `A_u^n` is even when `a ≥ 1` (`A_u = 2^{a_u} A'_{u+1}`). -/
theorem two_dvd_Aun {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) (n : ℕ) (u : ℤ) : (2 : ℤ) ∣ (Aun n u α : ℤ) := by
  rw [Aun_eq_two_pow_mul]
  push_cast
  exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by have := hpos u; omega)) _

/-- **Finding 4**, printed `A_u^n`: on every cycle of `ℤ`, `GCD(A_i)` is even, so it is neither
`2^{p_n} − 3ⁿ` nor `|2^{p_n} − 3ⁿ|` (both odd). -/
theorem gcd_Aun_ne_of_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    (2 : ℤ) ∣ (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) ∧
      (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) ≠ (2 : ℤ) ^ p n x - 3 ^ n ∧
      (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) ≠ |(2 : ℤ) ^ p n x - 3 ^ n| := by
  have hpos := one_le_of_cycle hn hx hper hα
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  have hodd := (delta_odd_not_three_dvd hpos hn).1
  rw [← hP] at hodd
  have hn2 : ¬ (2 : ℤ) ∣ (2 : ℤ) ^ p n x - 3 ^ n :=
    fun h2 => Int.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 h2)
  have hG : (2 : ℤ) ∣ (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) :=
    Finset.dvd_gcd (fun u _ => two_dvd_Aun hpos n u)
  refine ⟨hG, fun h => hn2 (h ▸ hG), fun h => hn2 ((dvd_abs _ _).1 (h ▸ hG))⟩

/-- **Finding 4**, printed `A_u^n`, up to sign: on every cycle, `2` divides every `A_u` and not
`2^{p_n} − 3ⁿ`. -/
theorem not_dvd_iff_dvd_Aun_of_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    ¬ ∀ d : ℤ, d ∣ (2 : ℤ) ^ p n x - 3 ^ n ↔ ∀ u : ℤ, d ∣ (Aun n u α : ℤ) := by
  intro h
  have hpos := one_le_of_cycle hn hx hper hα
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  have hodd := (delta_odd_not_three_dvd hpos hn).1
  rw [← hP] at hodd
  exact Int.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 ((h 2).2 (fun u => two_dvd_Aun hpos n u)))

/-! ### `cor:intertwined_i_` -/

/-- `i ↦ Δ'_i` is `n`-periodic when `a` is. -/
theorem DeltaAlt_periodic {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) :
    Function.Periodic (DeltaAlt n α) n := by
  intro j
  simp only [DeltaAlt]
  rw [show j + (n : ℤ) + 1 = (j + 1) + n by ring]
  have e1 : AunAlt n (j + 1 + n) α = AunAlt n (j + 1) α := (AunAlt_periodic h) (j + 1)
  have e2 : AunAlt n (j + n) α = AunAlt n j α := (AunAlt_periodic h) j
  rw [e1, e2]

/-- `i ↦ Δ_i` is `n`-periodic when `a` is. -/
theorem Delta_periodic {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) :
    Function.Periodic (Delta n α) n := by
  intro j
  simp only [Delta]
  rw [show j + (n : ℤ) + 1 = (j + 1) + n by ring]
  have e1 : Aun n (j + 1 + n) α = Aun n (j + 1) α := (Aun_periodic h) (j + 1)
  have e2 : Aun n (j + n) α = Aun n j α := (Aun_periodic h) j
  rw [e1, e2]

/-- For periodic data, the descending indices of one period stand for all of `𝒟`. -/
theorem forall_of_range {α : ℤ → ℕ} {n : ℕ} (hn : 0 < n) (hper : Function.Periodic α n)
    {f : ℤ → ℤ} (hf : Function.Periodic f n) {d : ℤ}
    (h : ∀ i ∈ (range n).filter (fun i : ℕ => 1 < α i), d ∣ f ((i : ℤ) - 1)) :
    ∀ i : ℤ, 1 < α i → d ∣ f (i - 1) := by
  intro i hi
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hr : (((i % n).toNat : ℕ) : ℤ) = i % n := Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')
  have hmem : (i % n).toNat ∈ (range n).filter (fun i : ℕ => 1 < α i) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by have := Int.emod_lt_of_pos i hn'; omega, ?_⟩
    rw [hr, ← periodic_emod hper i]
    exact hi
  have h1 := h _ hmem
  rw [hr] at h1
  have hg : Function.Periodic (fun j : ℤ => f (j - 1)) n := by
    intro j
    show f (j + n - 1) = f (j - 1)
    rw [show j + (n : ℤ) - 1 = (j - 1) + n by ring, hf]
  have e : f (i - 1) = f (i % n - 1) := periodic_emod hg i
  rwa [e]

/-- From `d ∣ f c` and steps both ways, `d ∣ f u` for all `u`. -/
theorem forall_of_step {P : ℤ → Prop} (c : ℤ) (h0 : P c) (hs : ∀ u, P u → P (u + 1))
    (hp : ∀ u, P (u + 1) → P u) : ∀ u, P u := by
  intro u
  refine Int.inductionOn' u c h0 (fun k _ hk => hs k hk) (fun k _ hk => hp (k - 1) ?_)
  rwa [sub_add_cancel]

/-- If `d ∣ 2^P − 3ⁿ` and `d ∣ A'_c`, then `d ∣ A'_u` for every `u` (periodic `a ≥ 1`, `n ≥ 1`). -/
theorem dvd_AunAlt_of_dvd_delta {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) {c d : ℤ}
    (hδ : d ∣ (2 : ℤ) ^ (∑ t ∈ range n, α t) - 3 ^ n) (hc : d ∣ (AunAlt n c α : ℤ)) :
    ∀ u : ℤ, d ∣ (AunAlt n u α : ℤ) := by
  obtain ⟨hodd, h3δ⟩ := delta_odd_not_three_dvd hpos hn
  have h2 : ¬ (2 : ℤ) ∣ d := fun h => Int.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 (h.trans hδ))
  have hco2 : ∀ k : ℕ, IsCoprime d (2 ^ k) := fun k =>
    IsCoprime.pow_right ((Int.prime_two.coprime_iff_not_dvd).2 h2).symm
  have hco3 : IsCoprime d 3 :=
    ((Int.prime_three.coprime_iff_not_dvd).2 (fun h => h3δ (h.trans hδ))).symm
  refine forall_of_step (P := fun u => d ∣ (AunAlt n u α : ℤ)) c hc (fun u hu => ?_) (fun u hu => ?_)
  · have e := two_pow_mul_AunAlt_succ hper u
    have : d ∣ (2 : ℤ) ^ α u * AunAlt n (u + 1) α := by
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right hu _) hδ
    exact (hco2 _).dvd_of_dvd_mul_left this
  · have e := two_pow_mul_AunAlt_succ hper u
    have : d ∣ 3 * (AunAlt n u α : ℤ) := by
      have : 3 * (AunAlt n u α : ℤ) =
          2 ^ α u * AunAlt n (u + 1) α - ((2 : ℤ) ^ (∑ t ∈ range n, α t) - 3 ^ n) := by
        linear_combination -e
      rw [this]
      exact dvd_sub (dvd_mul_of_dvd_right hu _) hδ
    exact hco3.dvd_of_dvd_mul_left this

/-- The core: if `d` divides `A'_c` and every `Δ'_{i−1}`, `i ∈ 𝒟`, then `d ∣ 2^P − 3ⁿ`
(periodic `a ≥ 1`, `n ≥ 1`, any base point `c`). -/
theorem dvd_delta_of_intertwined {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) (c d : ℤ) (hc : d ∣ (AunAlt n c α : ℤ))
    (hD : ∀ i : ℤ, 1 < α i → d ∣ DeltaAlt n α (i - 1)) :
    d ∣ (2 : ℤ) ^ (∑ t ∈ range n, α t) - 3 ^ n := by
  set δ := (2 : ℤ) ^ (∑ t ∈ range n, α t) - 3 ^ n with hδ
  have hrec : ∀ u, (2 : ℤ) ^ α u * AunAlt n (u + 1) α = 3 * AunAlt n u α + δ :=
    fun u => two_pow_mul_AunAlt_succ hper u
  have h3 : IsCoprime d 3 :=
    ((Int.prime_three.coprime_iff_not_dvd).2 (fun h => not_three_dvd_AunAlt hn c (h.trans hc))).symm
  -- an ascending step propagates `d ∣ A'_{u+1} + δ` back to `d ∣ A'_u + δ`
  have step : ∀ u, α u = 1 → d ∣ (AunAlt n (u + 1) α : ℤ) + δ → d ∣ (AunAlt n u α : ℤ) + δ := by
    intro u hu h
    have e := hrec u
    rw [hu, pow_one] at e
    have : 3 * ((AunAlt n u α : ℤ) + δ) = 2 * ((AunAlt n (u + 1) α : ℤ) + δ) := by
      linear_combination -e
    exact h3.dvd_of_dvd_mul_left (by rw [this]; exact dvd_mul_of_dvd_right h _)
  have back : ∀ m : ℕ, (∀ t < m, α (c + t) = 1) → d ∣ (AunAlt n (c + m) α : ℤ) + δ →
      d ∣ (AunAlt n c α : ℤ) + δ := by
    intro m
    induction m with
    | zero => intro _ h; simpa using h
    | succ m ih =>
      intro hm h
      refine ih (fun t ht => hm t (by omega)) (step (c + m) (hm m (by omega)) ?_)
      rwa [show c + (m : ℤ) + 1 = c + ((m + 1 : ℕ) : ℤ) by push_cast; ring]
  by_cases hex : ∃ j : ℕ, j < n ∧ 1 < α (c + j)
  · classical
    have hj₀ := Nat.find_spec hex
    have hmin : ∀ j < Nat.find hex, α (c + j) = 1 := fun j hj => by
      have h1 := Nat.find_min hex hj
      have h2 : ¬ 1 < α (c + j) := fun h' => h1 ⟨by omega, h'⟩
      have := hpos (c + j)
      omega
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos0
    · -- `c ∈ 𝒟`
      have hcD : 1 < α c := by
        have := hj₀.2
        rw [h0, Nat.cast_zero, add_zero] at this
        exact this
      have h1 := hD c hcD
      have hc1 : d ∣ (AunAlt n (c - 1) α : ℤ) := by
        have : (AunAlt n (c - 1) α : ℤ) = AunAlt n c α - DeltaAlt n α (c - 1) := by
          simp only [DeltaAlt, sub_add_cancel]
          ring
        rw [this]
        exact dvd_sub hc h1
      have e := hrec (c - 1)
      rw [sub_add_cancel] at e
      have : δ = 2 ^ α (c - 1) * AunAlt n c α - 3 * AunAlt n (c - 1) α := by linear_combination -e
      rw [this]
      exact dvd_sub (dvd_mul_of_dvd_right hc _) (dvd_mul_of_dvd_right hc1 _)
    · -- `c ∈ 𝒜`: the first descending index after `c` is `c + j₀`, `1 ≤ j₀ < n`
      have hiD : 1 < α (c + (Nat.find hex : ℕ)) := hj₀.2
      have hprev : α (c + ((Nat.find hex - 1 : ℕ) : ℤ)) = 1 := hmin _ (by omega)
      have hidx : c + ((Nat.find hex - 1 : ℕ) : ℤ) = c + (Nat.find hex : ℕ) - 1 := by
        push_cast [Nat.cast_sub (show 1 ≤ Nat.find hex by omega)]
        ring
      rw [hidx] at hprev
      have h1 := hD _ hiD
      have htop : d ∣ (AunAlt n (c + ((Nat.find hex - 1 : ℕ) : ℤ)) α : ℤ) + δ := by
        rw [hidx]
        have e := hrec (c + (Nat.find hex : ℕ) - 1)
        rw [hprev, pow_one, sub_add_cancel] at e
        have : (AunAlt n (c + (Nat.find hex : ℕ) - 1) α : ℤ) + δ =
            2 * DeltaAlt n α (c + (Nat.find hex : ℕ) - 1) := by
          simp only [DeltaAlt, sub_add_cancel]
          linear_combination -e
        rw [this]
        exact dvd_mul_of_dvd_right h1 _
      have := back (Nat.find hex - 1) (fun t ht => hmin t (by omega)) htop
      have := dvd_sub this hc
      simpa using this
  · -- `a ≡ 1` on `⟦c, c + n − 1⟧`, hence everywhere: `A'_c = 3ⁿ − 2ⁿ = −δ`
    push Not at hex
    have hall : ∀ j : ℕ, j < n → α (c + j) = 1 := fun j hj => by
      have := hex j hj
      have := hpos (c + j)
      omega
    have hP : ∑ t ∈ range n, α t = n := by
      rw [← sum_range_periodic hper c,
        Finset.sum_congr rfl (fun t ht => hall t (Finset.mem_range.1 ht))]
      simp
    have hXc : (AunAlt n c α : ℤ) = 3 ^ n - 2 ^ n := by
      rw [AunAlt_eq_sum]
      push_cast
      have e : ∀ k ∈ range n, (3 : ℤ) ^ k * 2 ^ (∑ t ∈ range (n - 1 - k), α (c + t)) =
          3 ^ k * 2 ^ (n - 1 - k) := by
        intro k hk
        have hk' := Finset.mem_range.1 hk
        rw [Finset.sum_congr rfl (fun t ht => hall t (by have := Finset.mem_range.1 ht; omega))]
        simp
      rw [Finset.sum_congr rfl e]
      have := geom_sum₂_mul (3 : ℤ) 2 n
      linear_combination this
    have : δ = -(AunAlt n c α : ℤ) := by
      rw [hXc, hδ, hP]
      ring
    rw [this]
    exact hc.neg_right

/-- **`cor:intertwined_i_`, true form, OQ-43 reading**: for `n`-periodic `a ≥ 1`, `n ≥ 1`, and every
base point `c`, the common divisors of `A'_c` and of the `Δ'_{i−1}`, `i ∈ 𝒟`, are the common
divisors of all the `A'_u`. No "intertwined" hypothesis. -/
theorem intertwined_alt {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) (c d : ℤ) :
    (d ∣ (AunAlt n c α : ℤ) ∧ ∀ i : ℤ, 1 < α i → d ∣ DeltaAlt n α (i - 1)) ↔
      ∀ u : ℤ, d ∣ (AunAlt n u α : ℤ) := by
  constructor
  · rintro ⟨hc, hD⟩
    exact dvd_AunAlt_of_dvd_delta hpos hn hper (dvd_delta_of_intertwined hpos hn hper c d hc hD) hc
  · intro hall
    exact ⟨hall c, fun i _ => by simp only [DeltaAlt]; exact dvd_sub (hall _) (hall _)⟩

/-- **`cor:intertwined_i_` on a cycle, OQ-43 reading**: `2^{p_n(x)} − 3ⁿ` is a GCD of `A'_c` and the
`Δ'_{i−1}`, `i ∈ 𝒟` (up to sign), on every cycle of `ℤ`, at every base point `c`. -/
theorem intertwined_alt_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) (c d : ℤ) :
    d ∣ (2 : ℤ) ^ p n x - 3 ^ n ↔
      (d ∣ (AunAlt n c α : ℤ) ∧ ∀ i : ℤ, 1 < α i → d ∣ DeltaAlt n α (i - 1)) := by
  have hpos := one_le_of_cycle hn hx hper hα
  rw [dvd_iff_dvd_AunAlt_of_cycle hn hx hper hα d]
  exact (intertwined_alt hpos hn hper c d).symm

/-- The odd part of the printed reading: an odd `o` dividing `A_c` and every `Δ_{i−1}`, `i ∈ 𝒟`,
divides every `A_u` (through the OQ-43 reading at the base point `c + 1`). -/
theorem odd_dvd_Aun_of_intertwined {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) (c o : ℤ) (ho : Odd o) (hc : o ∣ (Aun n c α : ℤ))
    (hD : ∀ i : ℤ, 1 < α i → o ∣ Delta n α (i - 1)) : ∀ u : ℤ, o ∣ (Aun n u α : ℤ) := by
  have h3 : ¬ (3 : ℤ) ∣ o := by
    intro h
    have h' := h.trans hc
    rw [Aun_eq_three_mul_add hper] at h'
    exact (delta_odd_not_three_dvd hpos hn).2 ((dvd_add_right (dvd_mul_right 3 _)).1 h')
  have hco3 : IsCoprime o 3 := ((Int.prime_three.coprime_iff_not_dvd).2 h3).symm
  have h2 : ¬ (2 : ℤ) ∣ o := fun h => Int.not_even_iff_odd.2 ho (even_iff_two_dvd.2 h)
  have hco2 : ∀ k : ℕ, IsCoprime o (2 ^ k) := fun k =>
    IsCoprime.pow_right ((Int.prime_two.coprime_iff_not_dvd).2 h2).symm
  have hc' : o ∣ (AunAlt n (c + 1) α : ℤ) := by
    have e : (Aun n c α : ℤ) = 2 ^ α c * AunAlt n (c + 1) α := by
      rw [Aun_eq_two_pow_mul]
      push_cast
      ring
    rw [e] at hc
    exact (hco2 _).dvd_of_dvd_mul_left hc
  have hD' : ∀ i : ℤ, 1 < α i → o ∣ DeltaAlt n α (i - 1) := by
    intro i hi
    have := hD i hi
    rw [Delta_eq_three_mul hper] at this
    exact hco3.dvd_of_dvd_mul_left this
  have hall := (intertwined_alt hpos hn hper (c + 1) o).1 ⟨hc', hD'⟩
  have hδ : o ∣ (2 : ℤ) ^ (∑ t ∈ range n, α t) - 3 ^ n := by
    have e := two_pow_mul_AunAlt_succ hper 0
    have : (2 : ℤ) ^ (∑ t ∈ range n, α t) - 3 ^ n =
        2 ^ α 0 * AunAlt n (0 + 1) α - 3 * AunAlt n 0 α := by linear_combination -e
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right (hall _) _) (dvd_mul_of_dvd_right (hall _) _)
  intro u
  rw [Aun_eq_three_mul_add hper]
  exact dvd_add (dvd_mul_of_dvd_right (hall u) _) hδ

/-- The `2`-adic part of the printed reading: when `𝒜 ≠ ∅`, no multiple of `4` divides `A_c` and
every `Δ_{i−1}`, `i ∈ 𝒟` (`ν₂(A_u) = a_u`, and some `i ∈ 𝒟` has `i − 1 ∈ 𝒜`). -/
theorem not_four_dvd_of_intertwined {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) (c d : ℤ) (hA : ∃ j, α j = 1) (h4 : (4 : ℤ) ∣ d)
    (hc : d ∣ (Aun n c α : ℤ)) (hD : ∀ i : ℤ, 1 < α i → d ∣ Delta n α (i - 1)) : False := by
  have eA : ∀ u, (Aun n u α : ℤ) = 2 ^ α u * AunAlt n (u + 1) α := fun u => by
    rw [Aun_eq_two_pow_mul]
    push_cast
    ring
  have hodd : ∀ u, ¬ (2 : ℤ) ∣ (AunAlt n u α : ℤ) := fun u h => by
    obtain ⟨r, hr⟩ := AunAlt_odd hpos hn u
    obtain ⟨s, hs⟩ := h
    omega
  have hc2 : 1 < α c := by
    by_contra hle
    have h1 : α c = 1 := by have := hpos c; omega
    have h4c := h4.trans hc
    rw [eA, h1, pow_one] at h4c
    obtain ⟨r, hr⟩ := h4c
    exact hodd (c + 1) ⟨r, by linarith⟩
  obtain ⟨j, hj⟩ := hA
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hex : ∃ s : ℕ, 1 < α (j + s) := by
    refine ⟨((c - j) % n).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')]
    have e : j + (c - j) % n = c - ((c - j) / n : ℤ) * n := by
      rw [Int.emod_def]
      ring
    have hq := hper.sub_int_mul_eq (x := c) ((c - j) / n)
    simp only [Int.cast_id] at hq
    rw [e, hq]
    exact hc2
  classical
  have hs₀ : 1 < α (j + (Nat.find hex : ℕ)) := Nat.find_spec hex
  have hs0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, add_zero, hj] at hs₀
    omega
  have hprev : α (j + (Nat.find hex : ℕ) - 1) = 1 := by
    have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show j + ((Nat.find hex - 1 : ℕ) : ℤ) = j + (Nat.find hex : ℕ) - 1 by
      push_cast [Nat.cast_sub (show 1 ≤ Nat.find hex by omega)]; ring] at h1
    have := hpos (j + (Nat.find hex : ℕ) - 1)
    omega
  have hΔ := h4.trans (hD _ hs₀)
  simp only [Delta, sub_add_cancel] at hΔ
  rw [eA (j + (Nat.find hex : ℕ)), eA (j + (Nat.find hex : ℕ) - 1), hprev, sub_add_cancel,
    pow_one] at hΔ
  have h4i : (4 : ℤ) ∣ 2 ^ α (j + (Nat.find hex : ℕ)) := by
    have : (2 : ℤ) ^ α (j + (Nat.find hex : ℕ)) = 4 * 2 ^ (α (j + (Nat.find hex : ℕ)) - 2) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [this]
    exact dvd_mul_right _ _
  have h4' : (4 : ℤ) ∣ 2 * AunAlt n (j + (Nat.find hex : ℕ)) α := by
    have := dvd_sub (dvd_mul_of_dvd_left h4i (AunAlt n (j + (Nat.find hex : ℕ) + 1) α : ℤ)) hΔ
    rwa [sub_sub_cancel] at this
  obtain ⟨r, hr⟩ := h4'
  exact hodd (j + (Nat.find hex : ℕ)) ⟨r, by linarith⟩

/-- **`cor:intertwined_i_`, true form, printed `A_u^n`**, with `m` read as `GCD(A_i : i ∈ ℤ)`: for
`n`-periodic `a ≥ 1`, `n ≥ 1`, every base point `c`. No "intertwined" hypothesis. -/
theorem intertwined_aun {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) (c d : ℤ) :
    (d ∣ (Aun n c α : ℤ) ∧ ∀ i : ℤ, 1 < α i → d ∣ Delta n α (i - 1)) ↔
      ∀ u : ℤ, d ∣ (Aun n u α : ℤ) := by
  constructor
  · rintro ⟨hc, hD⟩
    by_cases hall : ∀ i, 1 < α i
    · refine forall_of_step (P := fun u => d ∣ (Aun n u α : ℤ)) c hc (fun u hu => ?_)
        (fun u hu => ?_)
      · have := hD (u + 1) (hall _)
        simp only [Delta, add_sub_cancel_right] at this
        have := dvd_add this hu
        rwa [sub_add_cancel] at this
      · have := hD (u + 1) (hall _)
        simp only [Delta, add_sub_cancel_right] at this
        have := dvd_sub hu this
        rwa [sub_sub_cancel] at this
    · have hA : ∃ j, α j = 1 := by
        push Not at hall
        obtain ⟨j, hj⟩ := hall
        exact ⟨j, by have := hpos j; omega⟩
      rcases Int.even_or_odd d with ⟨o, ho⟩ | hd
      · have hod : Odd o := by
          rcases Int.even_or_odd o with ⟨q, hq⟩ | h
          · exact absurd (not_four_dvd_of_intertwined hpos hn hper c d hA ⟨q, by omega⟩ hc hD)
              not_false
          · exact h
        have hdo : d = 2 * o := by omega
        have ho1 : o ∣ d := ⟨2, by omega⟩
        have hall' := odd_dvd_Aun_of_intertwined hpos hn hper c o hod (ho1.trans hc)
          (fun i hi => ho1.trans (hD i hi))
        have h2o : IsCoprime (2 : ℤ) o :=
          (Int.prime_two.coprime_iff_not_dvd).2
            (fun h => Int.not_even_iff_odd.2 hod (even_iff_two_dvd.2 h))
        intro u
        rw [hdo]
        exact h2o.mul_dvd (two_dvd_Aun hpos n u) (hall' u)
      · exact odd_dvd_Aun_of_intertwined hpos hn hper c d hd hc hD
  · intro hall
    exact ⟨hall c, fun i _ => by simp only [Delta]; exact dvd_sub (hall _) (hall _)⟩

/-- The corollary's GCD over one period, OQ-43 reading:
`A'_0 ∧ ⋀_{i ∈ 𝒟 ∩ ⟦0, n−1⟧} Δ'_{i−1}` (normalized, `≥ 0`). -/
def corGcdAlt (n : ℕ) (α : ℤ → ℕ) : ℤ :=
  GCDMonoid.gcd (AunAlt n 0 α : ℤ)
    (((range n).filter (fun i : ℕ => 1 < α i)).gcd (fun i : ℕ => DeltaAlt n α ((i : ℤ) - 1)))

/-- The corollary's GCD over one period, printed `A_u^n`. -/
def corGcd (n : ℕ) (α : ℤ → ℕ) : ℤ :=
  GCDMonoid.gcd (Aun n 0 α : ℤ)
    (((range n).filter (fun i : ℕ => 1 < α i)).gcd (fun i : ℕ => Delta n α ((i : ℤ) - 1)))

/-- **`cor:intertwined_i_`, normalized, OQ-43 reading**: on every cycle of `ℤ`,
`A'_0 ∧ ⋀_{i ∈ 𝒟} Δ'_{i−1} = |2^{p_n(x)} − 3ⁿ|`. -/
theorem corGcdAlt_of_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    corGcdAlt n α = |(2 : ℤ) ^ p n x - 3 ^ n| := by
  have hpos := one_le_of_cycle hn hx hper hα
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  set G := corGcdAlt n α with hG
  have hG0 : 0 ≤ G := Int.gcd_nonneg _ _
  have hGc : G ∣ (AunAlt n 0 α : ℤ) := gcd_dvd_left _ _
  have hGD : ∀ i ∈ (range n).filter (fun i : ℕ => 1 < α i), G ∣ DeltaAlt n α ((i : ℤ) - 1) :=
    fun i hi => (gcd_dvd_right _ _).trans (Finset.gcd_dvd hi)
  have hGδ : G ∣ (2 : ℤ) ^ p n x - 3 ^ n := by
    rw [hP]
    exact dvd_delta_of_intertwined hpos hn hper 0 G hGc
      (forall_of_range hn hper (DeltaAlt_periodic hper) hGD)
  obtain ⟨hδc, hδD⟩ := (intertwined_alt_cycle hn hx hper hα 0 ((2 : ℤ) ^ p n x - 3 ^ n)).1 dvd_rfl
  have hδG : (2 : ℤ) ^ p n x - 3 ^ n ∣ G :=
    dvd_gcd hδc (Finset.dvd_gcd (fun i hi => hδD i (Finset.mem_filter.1 hi).2))
  exact Int.dvd_antisymm hG0 (abs_nonneg _) ((dvd_abs _ _).2 hGδ) ((abs_dvd _ _).2 hδG)

/-- `cor:intertwined_i_` as printed (`m = 2^{p_n} − 3ⁿ`, OQ-43 reading) holds on the cycles of `x > 0`. -/
theorem corGcdAlt_of_pos {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    (2 : ℤ) ^ p n x - 3 ^ n = corGcdAlt n α := by
  have hpos := two_pow_p_sub_three_pow_mul_pos hn hx
  rw [corGcdAlt_of_cycle hn hx hper hα, abs_of_pos (pos_of_mul_pos_left hpos hx0.le)]

/-- On the cycles of `x < 0` the corollary's GCD is `3ⁿ − 2^{p_n(x)} = −m` (OQ-43 reading). -/
theorem corGcdAlt_of_neg {x : ℤ} (hx0 : x < 0) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    corGcdAlt n α = 3 ^ n - 2 ^ p n x := by
  have hpos := two_pow_p_sub_three_pow_mul_pos hn hx
  have hneg : (2 : ℤ) ^ p n x - 3 ^ n < 0 := by nlinarith
  rw [corGcdAlt_of_cycle hn hx hper hα, abs_of_neg hneg]
  ring

/-- **`cor:intertwined_i_`, normalized, printed `A_u^n`**: `A_0 ∧ ⋀_{i ∈ 𝒟} Δ_{i−1} = GCD(A_i)` for
every `n`-periodic `a ≥ 1`, `n ≥ 1`. -/
theorem corGcd_eq_gcd_Aun {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} (hn : 0 < n)
    (hper : Function.Periodic α n) :
    corGcd n α = (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) := by
  set G := corGcd n α with hG
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
  have hHG : H ∣ G := dvd_gcd (hHall 0) (Finset.dvd_gcd (fun i _ => by
    simp only [Delta]
    exact dvd_sub (hHall _) (hHall _)))
  have hGc : G ∣ (Aun n 0 α : ℤ) := gcd_dvd_left _ _
  have hGD : ∀ i ∈ (range n).filter (fun i : ℕ => 1 < α i), G ∣ Delta n α ((i : ℤ) - 1) :=
    fun i hi => (gcd_dvd_right _ _).trans (Finset.gcd_dvd hi)
  have hGall := (intertwined_aun hpos hn hper 0 G).1
    ⟨hGc, forall_of_range hn hper (Delta_periodic hper) hGD⟩
  have hGH : G ∣ H := Finset.dvd_gcd (fun u _ => hGall u)
  exact Int.dvd_antisymm hG0 hH0 hGH hHG

/-- `𝒜 = 2ℤ`, `𝒟 = 2ℤ + 1` on the cycle `(−5, −7)`: they alternate. -/
theorem ascIdx_descIdx_seq12 : ascIdx seq12 = {i | Even i} ∧ descIdx seq12 = {i | Odd i} := by
  refine ⟨?_, ?_⟩
  · ext i
    simp only [ascIdx, seq12, Set.mem_setOf_eq, Int.even_iff]
    split_ifs with h <;> simp [h]
  · ext i
    simp only [descIdx, seq12, Set.mem_setOf_eq, Int.odd_iff]
    split_ifs with h <;> omega

/-- **Finding 5.** `cor:intertwined_i_` as printed (`m = 2^{p_n} − 3ⁿ`) is false for both readings of
OQ-43, for every reading `I` of "intertwined" under which the alternating `𝒜 = 2ℤ`, `𝒟 = 2ℤ + 1`
are intertwined: the cycle `(−5, −7)`, where `m = −1`, the OQ-43 GCD is `1` and the printed one `2`. -/
theorem intertwined_printed_false (I : Set ℤ → Set ℤ → Prop) (hI : I {i | Even i} {i | Odd i}) :
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → I (ascIdx α) (descIdx α) →
      (2 : ℤ) ^ p n x - 3 ^ n = corGcdAlt n α) ∧
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → I (ascIdx α) (descIdx α) →
      (2 : ℤ) ^ p n x - 3 ^ n = corGcd n α) := by
  have hx : T^[2] (-5 : ℤ) = -5 := cycle_neg_five.1
  have hp : p 2 (-5 : ℤ) = 3 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← seq12_eq_a 0, ← seq12_eq_a 1]
    decide
  have hI' : I (ascIdx seq12) (descIdx seq12) := by
    rw [ascIdx_descIdx_seq12.1, ascIdx_descIdx_seq12.2]
    exact hI
  have e1 : corGcdAlt 2 seq12 = 1 := by decide
  have e2 : corGcd 2 seq12 = 2 := by decide
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a hI'
    rw [hp, e1] at this
    norm_num at this
  · have := h (-5) 2 two_pos hx seq12 seq12_periodic seq12_eq_a hI'
    rw [hp, e2] at this
    norm_num at this

/-! ### The four known cycles of `ℤ` -/

/-- The `7`-periodic sequence `(1, 1, 1, 2, 1, 1, 4)` of the cycle of `−17`. -/
def seq17 (i : ℤ) : ℕ := if i % 7 = 3 then 2 else if i % 7 = 6 then 4 else 1

theorem seq17_periodic : Function.Periodic seq17 (7 : ℕ) := by
  intro i
  simp [seq17]

/-- The cycle `−17 → −25 → −37 → −55 → −41 → −61 → −91 → −17`, and `seq17` is `a(−17)`. -/
theorem cycle_neg_seventeen : T^[7] (-17 : ℤ) = -17 ∧ ∀ k : ℕ, seq17 k = a k (-17 : ℤ) := by
  have t1 := T_unique (A := ℤ) two_ne_zero (x := -17) (t := -25) (k := 1) ⟨-13, by norm_num⟩
    (by norm_num)
  have t2 := T_unique (A := ℤ) two_ne_zero (x := -25) (t := -37) (k := 1) ⟨-19, by norm_num⟩
    (by norm_num)
  have t3 := T_unique (A := ℤ) two_ne_zero (x := -37) (t := -55) (k := 1) ⟨-28, by norm_num⟩
    (by norm_num)
  have t4 := T_unique (A := ℤ) two_ne_zero (x := -55) (t := -41) (k := 2) ⟨-21, by norm_num⟩
    (by norm_num)
  have t5 := T_unique (A := ℤ) two_ne_zero (x := -41) (t := -61) (k := 1) ⟨-31, by norm_num⟩
    (by norm_num)
  have t6 := T_unique (A := ℤ) two_ne_zero (x := -61) (t := -91) (k := 1) ⟨-46, by norm_num⟩
    (by norm_num)
  have t7 := T_unique (A := ℤ) two_ne_zero (x := -91) (t := -17) (k := 4) ⟨-9, by norm_num⟩
    (by norm_num)
  have o1 : T^[1] (-17 : ℤ) = -25 := by rw [Function.iterate_one, t1.2]
  have o2 : T^[2] (-17 : ℤ) = -37 := by rw [Function.iterate_succ_apply', o1, t2.2]
  have o3 : T^[3] (-17 : ℤ) = -55 := by rw [Function.iterate_succ_apply', o2, t3.2]
  have o4 : T^[4] (-17 : ℤ) = -41 := by rw [Function.iterate_succ_apply', o3, t4.2]
  have o5 : T^[5] (-17 : ℤ) = -61 := by rw [Function.iterate_succ_apply', o4, t5.2]
  have o6 : T^[6] (-17 : ℤ) = -91 := by rw [Function.iterate_succ_apply', o5, t6.2]
  have hx : T^[7] (-17 : ℤ) = -17 := by rw [Function.iterate_succ_apply', o6, t7.2]
  refine ⟨hx, fun k => ?_⟩
  have hper : ∀ k, a (k + 7) (-17 : ℤ) = a k (-17 : ℤ) :=
    (periodic_a_iff_periodic_T (-17 : ℤ) 7).2 (fun k => by rw [Function.iterate_add_apply, hx])
  have e := Function.Periodic.map_mod_nat (f := fun k => a k (-17 : ℤ)) hper k
  rw [← e]
  have hk7 : k % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hcast : (k : ℤ) % 7 = ((k % 7 : ℕ) : ℤ) := by omega
  simp only [seq17, hcast]
  generalize k % 7 = r at hk7 ⊢
  interval_cases r
  · rw [a, Function.iterate_zero_apply]; exact t1.1
  · rw [a, o1]; exact t2.1
  · rw [a, o2]; exact t3.1
  · rw [a, o3]; exact t4.1
  · rw [a, o4]; exact t5.1
  · rw [a, o5]; exact t6.1
  · rw [a, o6]; exact t7.1

/-- **Finding 6.** On the cycles of `1, −1, −5, −17` (periods `1, 1, 2, 7`): `2^{p_n} − 3ⁿ`, the
corollary's GCD for both readings, and `GCD(A_i)` for the printed `A_u^n`. -/
theorem four_cycles :
    (T^[1] (1 : ℤ) = 1 ∧ (∀ k : ℕ, (fun _ : ℤ => (2 : ℕ)) k = a k (1 : ℤ)) ∧
      (2 : ℤ) ^ p 1 (1 : ℤ) - 3 ^ 1 = 1 ∧ corGcdAlt 1 (fun _ => 2) = 1 ∧
      corGcd 1 (fun _ => 2) = 4 ∧ (range 1).gcd (fun u : ℕ => (Aun 1 u (fun _ => 2) : ℤ)) = 4) ∧
    (T^[1] (-1 : ℤ) = -1 ∧ (∀ k : ℕ, (fun _ : ℤ => (1 : ℕ)) k = a k (-1 : ℤ)) ∧
      (2 : ℤ) ^ p 1 (-1 : ℤ) - 3 ^ 1 = -1 ∧ corGcdAlt 1 (fun _ => 1) = 1 ∧
      corGcd 1 (fun _ => 1) = 2 ∧ (range 1).gcd (fun u : ℕ => (Aun 1 u (fun _ => 1) : ℤ)) = 2) ∧
    (T^[2] (-5 : ℤ) = -5 ∧ (∀ k : ℕ, seq12 k = a k (-5 : ℤ)) ∧
      (2 : ℤ) ^ p 2 (-5 : ℤ) - 3 ^ 2 = -1 ∧ corGcdAlt 2 seq12 = 1 ∧ corGcd 2 seq12 = 2 ∧
      (range 2).gcd (fun u : ℕ => (Aun 2 u seq12 : ℤ)) = 2) ∧
    (T^[7] (-17 : ℤ) = -17 ∧ (∀ k : ℕ, seq17 k = a k (-17 : ℤ)) ∧
      (2 : ℤ) ^ p 7 (-17 : ℤ) - 3 ^ 7 = -139 ∧ corGcdAlt 7 seq17 = 139 ∧ corGcd 7 seq17 = 278 ∧
      (range 7).gcd (fun u : ℕ => (Aun 7 u seq17 : ℤ)) = 278) := by
  have hx1 : T^[1] (1 : ℤ) = 1 := T_iterate_one_int 1
  have hxm1 : T^[1] (-1 : ℤ) = -1 := T_iterate_neg_one_int 1
  have hp5 : p 2 (-5 : ℤ) = 3 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← seq12_eq_a 0, ← seq12_eq_a 1]
    decide
  obtain ⟨hx17, ha17⟩ := cycle_neg_seventeen
  have hp17 : p 7 (-17 : ℤ) = 11 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← ha17 0, ← ha17 1, ← ha17 2, ← ha17 3, ← ha17 4, ← ha17 5, ← ha17 6]
    decide
  refine ⟨⟨hx1, fun k => (a_one_int k).symm, by rw [p_one_int]; norm_num, by decide, by decide,
      by decide⟩,
    ⟨hxm1, fun k => (a_neg_one_int k).symm, by rw [p_neg_one_int]; norm_num, by decide, by decide,
      by decide⟩,
    ⟨cycle_neg_five.1, seq12_eq_a, by rw [hp5]; norm_num, by decide, by decide, by decide⟩,
    ⟨hx17, ha17, by rw [hp17]; norm_num, by decide, by decide, by decide⟩⟩

/-- **Finding 6.** The planner's "`2m` for `Aun`" fails at the cycle `(1)`: the corollary's GCD and
`GCD(A_i)` are `4 = 4|m|` there, with `m = 1`. -/
theorem four_cycles_two_m_false :
    corGcd 1 (fun _ => 2) ≠ 2 * |(2 : ℤ) ^ p 1 (1 : ℤ) - 3 ^ 1| := by
  have e : corGcd 1 (fun _ => 2) = 4 := by decide
  rw [e, p_one_int]
  norm_num

end Syracuse
