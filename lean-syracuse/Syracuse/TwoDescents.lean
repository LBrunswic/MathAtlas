import Syracuse.UpperBounds
import Mathlib.Tactic.NormNum.Prime

/-!
# Syracuse § 3, `theo:syracuse_cycle`: cycles with exactly two descending indices per period

`theo:syracuse_cycle` — `syracuse.tex:306`. Not marked. Read over `ℤ`, the statement is false
(the cycle of `−17`). It is also false when `n` is not the least period, even for `x > 0`
(the cycle `(1)` read as a `2`-cycle). Its proof ends on the corollary to Matveev's theorem
and a computer check (l.326), both carried here as explicit hypotheses, and it stops at the
case `k₂ = k₁ + 1` (l.328). The paper's own steps are proved in their true forms, for both
readings of OQ-43. The bound of l.323–325 is proved in every configuration, the case
`k₂ = k₁ + 1` included (SCOPE).

> **theo:syracuse_cycle.** Let $\Gamma$ be a Syracuse $n$-cycle, then
> $\#(\D_\Gamma\cap \lsem 1,n\rsem)\neq 2$.

> *Proof.* Let $k_1,k_2\in\lsem 1,n\rsem$ such that $\#\D_\Gamma=(k_1+n\ZZ)\cup(k_2+n\ZZ)$.
> Consider $\Delta_i$ and $\Delta_j$ for $i,j\in \ZZ$ in such a way that $a_i=a_j=1$,
> $k_2-n< j<k_1<i < k_2$. We have :
> $$\Delta_i=  3^{n-1-(k_1-i)}2^{k_1-i}\left(2^{a_{k_1}}-2\right)
> +3^{n-1-(k_2-i)}2^{k_2-i+a_{k_1}-1}\left(2^{a_{k_2}}-2\right)$$
> $$\Delta_j=  3^{n-1-(k_2-j)}2^{k_2-j}\left(2^{a_{k_2}}-2\right)
> +3^{n-1-(k_1+n-j)}2^{k_1+n-j+a_{k_2}-1}\left(2^{a_{k_1}}-2\right)$$
> We write $\delta_1 = k_2-k_1 $, $\delta_2 = n+k_1-k_2$, $\alpha_1 = a_{k_1}-1$ et
> $\alpha_2=a_{k_2}-1$ so that we get :
> $$\Delta_i\sim_S  3^{\delta_2}\left(2^{\alpha_1}-1\right)+2^{\delta_2+\alpha_1}\left(2^{\alpha_2}-1\right)$$
> $$\Delta_j\sim_S  3^{\delta_1}\left(2^{\alpha_2}-1\right)+2^{\delta_1+\alpha_2}\left(2^{\alpha_1}-1\right)$$
> Without loss of generality we may assumer $\delta_1\leq\delta_2$. We thus have
> $\delta_1\leq n/2$ and $\alpha_1+\alpha_2 = |\Gamma|-n$, and thus :
> $$ \Delta_j \leq 3^{n/2}2^{|\Gamma|-n}+ 2^{|\Gamma|-n}2^{n/2}\leq
> 2^{|\Gamma|-(\log_3(2)-1/2)|\Gamma|}\leq 2^{|\Gamma|(1-\varepsilon)}$$
> with $\varepsilon=\log_3(2)-1/2$.
> One can then use the corollary to Matveev Theorem and check the finitely many remaining cases.
>
> It remains to consider the case where $k_2=k_1+1$. Consider
> $$A_{k_2}-A_i = \sum_{k=0}^{n-1}3^{n-1-k}2^{a_i+\cdots a_{i+k_2-1}}$$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` a Syracuse `n`-cycle (l.306) | `x : ℤ`, `0 < n`, `T^[n] x = x`; ⚠ strengthened for the conditional theorem: `x > 0` and `n` the least period (Findings 1, 2) |
| `a_i` (l.271, OQ-68 (a)) | `α : ℤ → ℕ` `n`-periodic with `α k = a_k(x)` |
| the index convention (OQ-63 (b)) | both: `α k = a_k(x)` and `β (k + 1) = a_k(x)`; the count is shift-invariant (`twoDescCount_shift`) |
| `#𝒟_Γ = (k₁ + nℤ) ∪ (k₂ + nℤ)` (l.308) | read as `𝒟_Γ = …` (`TwoDescClasses`); equivalent to `#(𝒟 ∩ ⟦1, n⟧) = 2` (`twoDescCount_eq_two_iff`) |
| `a_i = a_j = 1`, `k₂ − n < j < k₁ < i < k₂` (l.308) | ✓ carried: the positions of l.308 (`twoDesc_delta_i`, `twoDesc_delta_j`); `a_i = a_j = 1` follows from them |
| `A_i`, `Δ_i` (OQ-43) | both readings: `Delta` (printed `A_u^n`) and `DeltaAlt`; `Δ = 3Δ'` |
| `∼_S` (OQ-68 (c)) | `SEquiv`; every `∼_S` form is also an exact equality with an explicit factor `2^u 3^v` |
| `|Γ|` (l.323) | `p_n(x) = ∑_{t<n} a_t(x)` |
| `n/2` as an exponent (l.324) | real (`Real.rpow`) |
| WLOG `δ₁ ≤ δ₂` (l.323) | not needed: both orders are proved (`twoDesc_abs_le`); the bound takes `min(δ₁, δ₂)` |
| an ascending index in each gap (l.308) | ⚠ weakened: the bound needs none (`twoDesc_key`, `twoDesc_adjacent`) |
| the corollary to Matveev's theorem, the computer check (l.326) | ⚠ strengthened: explicit hypotheses `TwoDescMatveev B`, `TwoDescCheck B` (T-syr-cited); never axioms |

## SCOPE (disclosed)

* **Finding 1 (l.306): false over `ℤ`**, with `a_i` read as `a_i(x_0)` (OQ-68 (a); under the literal
  `a_i := T^i(x_0)`, `𝒟` is empty on both witnesses of Findings 1 and 2). The cycle `−17 → −25 → −37 → −55 → −41 → −61 → −91`, of
  least period `7` (`twoDesc_neg_seventeen_minimal`), has `a = (1, 1, 1, 2, 1, 1, 4)`, so
  `𝒟 ∩ ⟦1, 7⟧ = {3, 6}` (`{4, 7}` in the other index convention): `theo_syracuse_cycle_printed_false`.
  This bears on OQ-63 (a) (the sign of the cycles); nothing is decided here.
* **Finding 2 (l.306): `n` must be the least period, even for `x > 0`.** The cycle `(1)` read as a
  `2`-cycle has `a ≡ 2` and `𝒟 ∩ ⟦1, 2⟧ = {1, 2}` (`theo_syracuse_cycle_nonminimal_false`).
* **What is proved of the statement.** For `x > 0` and `n` the least period,
  `theo_syracuse_cycle_of_cited` (`_shift` for the other index convention) derives it from two
  hypotheses: `TwoDescMatveev B`, the corollary to Matveev's theorem in effective form at the
  exponent `ε₀` and constant `2` proved here, and `TwoDescCheck B`, the computer check below
  `p_n ≤ B`. Both are T-syr-cited's question. Unmarked: the row is partial.
* **The reading of l.308** (the planner's (b)): `#𝒟_Γ = (k₁ + nℤ) ∪ (k₂ + nℤ)` equates a number with
  a set, and is read `𝒟_Γ = …`. For periodic `a` this is equivalent to `#(𝒟 ∩ ⟦1, n⟧) = 2` with
  `1 ≤ k₁ < k₂ ≤ n` (`twoDescCount_eq_two_iff`). Confirmed.
* **The key identity** (new; no ascending index needed). Seen from a base point `c`, a period is a
  run of `r₁` ascending indices, a descending one (`a = b₁ + 1`), a run of `r₂`, a descending one
  (`a = b₂ + 1`) (`TwoDescAt`). Then `A'_c + (2^P − 3ⁿ) = 2^{r₁+1} E(r₂ + 1, b₁, b₂)`, with
  `E(δ, α, β) = 3^δ(2^α − 1) + 2^{δ+α}(2^β − 1)` (`twoDesc_key`). The proof runs the step
  recursion `2^{a_u} A'_{u+1} = 3A'_u + 2^P − 3ⁿ` once around the period. In the paper's
  notation, `A'_{k₂+1} + (2^P − 3ⁿ) = 2^{δ₂} E(δ₁, α₁, α₂)`,
  `A'_{k₁+1} + (2^P − 3ⁿ) = 2^{δ₁} E(δ₂, α₂, α₁)` and `P = α₁ + α₂ + n` (`twoDesc_key_classes`). On
  a cycle `A'_u = (2^{p_n} − 3ⁿ) x_u`, so `(2^{p_n} − 3ⁿ)(x_{k₂+1} + 1) = 2^{δ₂} E(δ₁, α₁, α₂)`.
* **Finding 3 (l.310–314): the exact displays are false**, for both readings of OQ-43 and both
  readings of the positions. The true two-term form at an ascending `u` is
  `twoDesc_deltaAlt_two_terms` (`twoDesc_delta_two_terms` for the printed `A_u^n`). Its exponents
  are `s₁ − 1` and `s₂ − 2 + a`, where the displays have `s₁` and `s₂ − 1 + a`: the error of
  `lem:syracuse_cycle_n__n_` (OQ-68 (b)). The display of l.310–312 has the shape for the positions
  `k₂ − n < u < k₁`, which l.308 gives to `j`; there it is `2Δ'_u = (2/3)Δ_u`
  (`twoDesc_displayI_eq`). Symmetrically, l.313–314 is `2Δ'_u` for `k₁ < u < k₂`, the positions
  of `i` (`twoDesc_displayJ_eq`). This confirms the planner's (a). At the printed positions the
  exponent `k₁ − i` is negative. At `−17` neither display equals `Δ'_u` or `Δ_u` at any ascending
  `u` (`twoDesc_displays_printed_false`).
* **Finding 4 (l.317–321): both `∼_S` forms are false as printed.** True, at the positions of
  l.308: for `k₁ < i < k₂`, `Δ'_i = 3^{i−k₁−1} 2^{k₂−i} E(δ₂, α₂, α₁)` and
  `Δ_i = 3^{i−k₁} 2^{k₂−i} E(δ₂, α₂, α₁)` (`twoDesc_delta_i`). For `k₂ − n < j < k₁`,
  `Δ_j = 3^{j+n−k₂} 2^{k₁−j} E(δ₁, α₁, α₂)` (`twoDesc_delta_j`). The printed forms are these with
  `α₁` and `α₂` exchanged. Equivalently, they are what the displays of l.310–314 give with `δ₁`
  and `δ₂` exchanged. At `−17` (`k₁ = 3`, `k₂ = 6`, `δ₁ = 3`, `δ₂ = 4`, `α₁ = 1`, `α₂ = 3`) the
  true S-free parts are `139` and `695 = 5 · 139`, the printed ones `305 = 5 · 61` and
  `253 = 11 · 23`. No `Δ_u`, `u ∈ ℤ`, is `∼_S` to either printed one (`twoDesc_values_seq17`,
  `twoDesc_sEquiv_printed_false`).
* **Finding 5 (l.323–325): the bound holds in another form.** No WLOG is needed:
  `2^{p_n} − 3ⁿ` divides both `E(δ₁, α₁, α₂)` and `E(δ₂, α₂, α₁)`, so `|2^{p_n} − 3ⁿ|` is at most
  each (`twoDesc_abs_le`). With `E(δ, α₁, α₂) ≤ 2^{|Γ|−n}(3^δ + 2^δ)` (`twoDescE_le`) this gives
  `twoDesc_bound` with `δ = min(δ₁, δ₂) ≤ n/2`. Its real form `twoDesc_bound_rpow` is the first
  inequality of l.324 for `m = |2^{p_n} − 3ⁿ|`. Read literally on `Δ_j` that inequality fails: at
  `−17` every ascending `u` has `Δ'_u ≥ 1112 > 3^{7/2} 2⁴ + 2⁴ 2^{7/2}`
  (`twoDesc_l324_first_literal_false`). The second inequality fails whenever `3ⁿ < 2^{|Γ|}`, so on
  every cycle of `x > 0` (`twoDesc_l324_second_false`, `twoDesc_l324_second_printed_false`): it
  needs `n ≥ |Γ| log₃ 2`. What holds:
  `|Γ| ≤ 2n` on every cycle of `ℤ` (`twoDesc_p_le`), hence `(2^{p_n} − 3ⁿ)⁴ ≤ 16 · 12^{p_n}`
  (`twoDesc_bound_pow_four`), i.e. `m ≤ 2 · 2^{|Γ|(1−ε₀)}` with `ε₀ = 1/2 − (log₂ 3)/4 ≈ 0.104`
  (`twoDesc_corollary_hyp`, the corollary's GCD read as `corGcdAlt = |2^{p_n} − 3ⁿ|`). This is the
  hypothesis of `cor:property_defined_cycles_gcd`, with `ε₀` in place of `log₃ 2 − 1/2`.
* **Finding 6 (l.328): the case `k₂ = k₁ + 1` closes as the main case does.** The key identity
  needs no ascending index, so `|2^{p_n} − 3ⁿ| ≤ E(1, α₁, α₂) ≤ 5 · 2^{|Γ|−n}`
  (`twoDesc_adjacent`), and the bound of Finding 5 covers the case. It rests on the same two cited
  steps and nothing else. With `δ₁ = 1 ≤ δ₂` the paper's own `Δ_j` also exists as soon as `n ≥ 3`.
  The display of l.331 is unfinished: its `i` is not defined in this case, and its summand
  depends on `k` only through `3^{n−1−k}`. It is not formalized.
* `T`, `a`, `p` are the total maps of `Syracuse.Base`, the paper's over `ℤ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset

/-! ### The count `#(𝒟_Γ ∩ ⟦1, n⟧)` -/

/-- `#(𝒟_Γ ∩ ⟦1, n⟧)`: the number of descending indices `i ∈ ⟦1, n⟧` (`1 < α i`). -/
noncomputable def twoDescCount (n : ℕ) (α : ℤ → ℕ) : ℕ :=
  ((Icc (1 : ℤ) n).filter (fun i => 1 < α i)).card

/-- `α (i + q n) = α i` for `n`-periodic `α` on `ℤ`. -/
theorem twoDesc_per {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (i q : ℤ) :
    α (i + q * n) = α i := by
  have := h.int_mul q i
  simpa using this

/-- No multiple of `n` lies strictly between `0` and `n`. -/
theorem twoDesc_not_mul {n : ℕ} {q m : ℤ} (h : q * n = m) (h1 : 0 < m) (h2 : m < n) : False := by
  have hn0 : (0 : ℤ) ≤ n := by positivity
  rcases le_or_gt q 0 with hq | hq
  · nlinarith
  · have hq1 : 1 ≤ q := hq
    nlinarith

/-- Every `i ∈ ℤ` is `r + q n` with `r ∈ ⟦1, n⟧`. -/
theorem twoDesc_rep {n : ℕ} (hn : 0 < n) (i : ℤ) :
    ∃ r q : ℤ, 1 ≤ r ∧ r ≤ n ∧ i = r + q * n := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  refine ⟨(i - 1) % n + 1, (i - 1) / n, by have := Int.emod_nonneg (i - 1) hn'.ne'; omega,
    by have := Int.emod_lt_of_pos (i - 1) hn'; omega, ?_⟩
  have := Int.emod_add_mul_ediv (i - 1) n
  linarith [mul_comm ((i - 1) / (n : ℤ)) (n : ℤ)]

/-- The representative in `⟦1, n⟧` is unique. -/
theorem twoDesc_rep_unique {n : ℕ} {k k' q q' : ℤ} (hk : 1 ≤ k) (hkn : k ≤ n) (hk' : 1 ≤ k')
    (hk'n : k' ≤ n) (h : k + q * n = k' + q' * n) : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact (twoDesc_not_mul (q := q - q') (m := k' - k) (by linarith) (by linarith)
      (by linarith)).elim
  · exact heq
  · exact (twoDesc_not_mul (q := q' - q) (m := k - k') (by linarith) (by linarith)
      (by linarith)).elim

/-- The count is the same for every shift of a periodic sequence: both index conventions of
OQ-63 (b) give the same statement. -/
theorem twoDescCount_shift {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (c : ℤ) :
    twoDescCount n (fun i => α (i + c)) = twoDescCount n α := by
  set f : ℤ → ℕ := fun i => if 1 < α i then 1 else 0 with hf
  have hfp : Function.Periodic f n := fun i => by simp only [hf, h i]
  have key : ∀ g : ℤ → ℕ,
      twoDescCount n g = ∑ t ∈ range n, (if 1 < g (1 + t) then 1 else 0) := by
    intro g
    rw [twoDescCount, Finset.card_filter,
      show Icc (1 : ℤ) n = Ico 1 (1 + ((n : ℕ) : ℤ)) by ext; simp only [mem_Icc, mem_Ico]; omega,
      sum_Ico_int_eq_sum_range]
  rw [key, key]
  have e1 := sum_range_periodic hfp (1 + c)
  have e2 := sum_range_periodic hfp 1
  simp only [hf] at e1 e2
  rw [e2, ← e1]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [show 1 + (t : ℤ) + c = 1 + c + t by ring]

/-- `𝒟_Γ = (k₁ + nℤ) ∪ (k₂ + nℤ)` (l.308, `#𝒟_Γ = …` read as `𝒟_Γ = …`). -/
def TwoDescClasses (α : ℤ → ℕ) (n : ℕ) (k₁ k₂ : ℤ) : Prop :=
  descIdx α = {i | ∃ q : ℤ, i = k₁ + q * n} ∪ {i | ∃ q : ℤ, i = k₂ + q * n}

/-- **The reading of l.308** (the planner's (b)): for `n`-periodic `α`, exactly two descending
indices in `⟦1, n⟧` iff `𝒟 = (k₁ + nℤ) ∪ (k₂ + nℤ)` with `1 ≤ k₁ < k₂ ≤ n`. -/
theorem twoDescCount_eq_two_iff {α : ℤ → ℕ} {n : ℕ} (hn : 0 < n) (h : Function.Periodic α n) :
    twoDescCount n α = 2 ↔
      ∃ k₁ k₂ : ℤ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ k₂ ≤ n ∧ TwoDescClasses α n k₁ k₂ := by
  constructor
  · intro h2
    obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.1 h2
    have hx : x ∈ (Icc (1 : ℤ) n).filter (fun i => 1 < α i) := by rw [hs]; simp
    have hy : y ∈ (Icc (1 : ℤ) n).filter (fun i => 1 < α i) := by rw [hs]; simp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
    have main : ∀ k₁ k₂ : ℤ, (Icc (1 : ℤ) n).filter (fun i => 1 < α i) = {k₁, k₂} →
        TwoDescClasses α n k₁ k₂ := by
      intro k₁ k₂ hs'
      have hmem : ∀ k, k ∈ ({k₁, k₂} : Finset ℤ) → 1 < α k := by
        intro k hk
        rw [← hs'] at hk
        exact (Finset.mem_filter.1 hk).2
      ext i
      simp only [descIdx, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hi
        obtain ⟨r, q, hr1, hrn, rfl⟩ := twoDesc_rep hn i
        have hr : r ∈ (Icc (1 : ℤ) n).filter (fun i => 1 < α i) := by
          simp only [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hr1, hrn⟩, by rwa [twoDesc_per h] at hi⟩
        rw [hs'] at hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact Or.inl ⟨q, rfl⟩
        · exact Or.inr ⟨q, rfl⟩
      · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
        · rw [twoDesc_per h]; exact hmem _ (by simp)
        · rw [twoDesc_per h]; exact hmem _ (by simp)
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact ⟨x, y, hx.1.1, hlt, hy.1.2, main x y hs⟩
    · exact ⟨y, x, hy.1.1, hlt, hx.1.2, main y x (by rw [hs, Finset.pair_comm])⟩
  · rintro ⟨k₁, k₂, hk₁, hk, hk₂, hC⟩
    have hs : (Icc (1 : ℤ) n).filter (fun i => 1 < α i) = {k₁, k₂} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      have hiff : 1 < α i ↔ i ∈ descIdx α := Iff.rfl
      rw [hiff, hC]
      simp only [Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hi1, hin⟩, (⟨q, rfl⟩ | ⟨q, rfl⟩)⟩
        · left
          exact twoDesc_rep_unique (q := 0) (q' := q) hi1 hin hk₁ (by omega) (by ring)
        · right
          exact twoDesc_rep_unique (q := 0) (q' := q) hi1 hin (by omega) hk₂ (by ring)
      · rintro (rfl | rfl)
        · exact ⟨⟨hk₁, by omega⟩, Or.inl ⟨0, by ring⟩⟩
        · exact ⟨⟨by omega, hk₂⟩, Or.inr ⟨0, by ring⟩⟩
    rw [twoDescCount, hs, Finset.card_pair hk.ne]

/-! ### Finding 1: over `ℤ` the statement is false (the cycle of `−17`) -/

/-- The orbit of `−17`: `−25, −37, −55, −41, −61, −91`. -/
theorem twoDesc_neg_seventeen_orbit :
    T^[1] (-17 : ℤ) = -25 ∧ T^[2] (-17 : ℤ) = -37 ∧ T^[3] (-17 : ℤ) = -55 ∧
    T^[4] (-17 : ℤ) = -41 ∧ T^[5] (-17 : ℤ) = -61 ∧ T^[6] (-17 : ℤ) = -91 := by
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
  have o1 : T^[1] (-17 : ℤ) = -25 := by rw [Function.iterate_one, t1.2]
  have o2 : T^[2] (-17 : ℤ) = -37 := by rw [Function.iterate_succ_apply', o1, t2.2]
  have o3 : T^[3] (-17 : ℤ) = -55 := by rw [Function.iterate_succ_apply', o2, t3.2]
  have o4 : T^[4] (-17 : ℤ) = -41 := by rw [Function.iterate_succ_apply', o3, t4.2]
  have o5 : T^[5] (-17 : ℤ) = -61 := by rw [Function.iterate_succ_apply', o4, t5.2]
  have o6 : T^[6] (-17 : ℤ) = -91 := by rw [Function.iterate_succ_apply', o5, t6.2]
  exact ⟨o1, o2, o3, o4, o5, o6⟩

/-- The cycle of `−17` has least period `7`. -/
theorem twoDesc_neg_seventeen_minimal : ∀ m : ℕ, 0 < m → m < 7 → T^[m] (-17 : ℤ) ≠ -17 := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := twoDesc_neg_seventeen_orbit
  intro m hm0 hm7
  interval_cases m
  · rw [o1]; norm_num
  · rw [o2]; norm_num
  · rw [o3]; norm_num
  · rw [o4]; norm_num
  · rw [o5]; norm_num
  · rw [o6]; norm_num

/-- At `−17`, `𝒟 ∩ ⟦1, 7⟧ = {3, 6}` (`a = (1, 1, 1, 2, 1, 1, 4)`), and `{4, 7}` in the other
index convention: two descending indices in both. -/
theorem twoDescCount_seq17 :
    twoDescCount 7 seq17 = 2 ∧ twoDescCount 7 (fun i => seq17 (i - 1)) = 2 := by
  refine ⟨?_, ?_⟩ <;> · unfold twoDescCount; decide

/-- **Finding 1.** `theo:syracuse_cycle` is false over `ℤ`, with `n` the least period, in both
index conventions (OQ-63 (b)): the cycle `−17 → −25 → −37 → −55 → −41 → −61 → −91`. -/
theorem theo_syracuse_cycle_printed_false :
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → (∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) →
      ∀ α : ℤ → ℕ, Function.Periodic α n → (∀ k : ℕ, α k = a k x) → twoDescCount n α ≠ 2) ∧
    (¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → (∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) →
      ∀ β : ℤ → ℕ, Function.Periodic β n → (∀ k : ℕ, β (k + 1) = a k x) →
        twoDescCount n β ≠ 2) := by
  obtain ⟨hx, hα⟩ := cycle_neg_seventeen
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact h (-17) 7 (by norm_num) hx twoDesc_neg_seventeen_minimal seq17 seq17_periodic hα
      twoDescCount_seq17.1
  · refine h (-17) 7 (by norm_num) hx twoDesc_neg_seventeen_minimal (fun i => seq17 (i - 1))
      (fun i => ?_) (fun k => ?_) twoDescCount_seq17.2
    · show seq17 (i + ((7 : ℕ) : ℤ) - 1) = seq17 (i - 1)
      rw [show i + ((7 : ℕ) : ℤ) - 1 = (i - 1) + ((7 : ℕ) : ℤ) by ring, seq17_periodic]
    · show seq17 (((k + 1 : ℕ) : ℤ) - 1) = a k (-17)
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring]
      exact hα k

/-- **Finding 2.** With `n` any period, the statement fails also for `x > 0`: the cycle `(1)`
read as a `2`-cycle has `a ≡ 2`, so `𝒟 ∩ ⟦1, 2⟧ = {1, 2}`. -/
theorem theo_syracuse_cycle_nonminimal_false :
    ¬ ∀ (x : ℤ), 0 < x → ∀ (n : ℕ), 0 < n → T^[n] x = x →
      ∀ α : ℤ → ℕ, Function.Periodic α n → (∀ k : ℕ, α k = a k x) → twoDescCount n α ≠ 2 := by
  intro h
  refine h 1 one_pos 2 two_pos (T_iterate_one_int 2) (fun _ => 2) (fun _ => rfl)
    (fun k => (a_one_int k).symm) ?_
  unfold twoDescCount
  decide

/-! ### The configuration seen from a base point, and the step recursion -/

/-- The S-free two-term form `E(δ, α, β) = 3^δ (2^α − 1) + 2^{δ+α} (2^β − 1)` of l.318–321. -/
def twoDescE (δ b₁ b₂ : ℕ) : ℤ := 3 ^ δ * (2 ^ b₁ - 1) + 2 ^ (δ + b₁) * (2 ^ b₂ - 1)

/-- Two descending indices per period, seen from a base point `c`: a run of `r₁` ascending
indices, a descending index with `a = b₁ + 1`, a run of `r₂` ascending indices, a descending
index with `a = b₂ + 1` (period `r₁ + r₂ + 2`). -/
def TwoDescAt (α : ℤ → ℕ) (c : ℤ) (r₁ b₁ r₂ b₂ : ℕ) : Prop :=
  (∀ t : ℕ, t < r₁ → α (c + t) = 1) ∧ α (c + r₁) = b₁ + 1 ∧
    (∀ t : ℕ, t < r₂ → α (c + r₁ + 1 + t) = 1) ∧ α (c + r₁ + 1 + r₂) = b₂ + 1

/-- A run of ascending indices sums to its length. -/
theorem twoDesc_sum_ones {α : ℤ → ℕ} {c : ℤ} {r : ℕ} (h : ∀ t : ℕ, t < r → α (c + t) = 1) :
    ∑ t ∈ range r, α (c + t) = r := by
  rw [Finset.sum_congr rfl (fun t ht => h t (Finset.mem_range.1 ht))]
  simp

/-- `∑_{t<n} a_t = b₁ + b₂ + n`: the `α₁ + α₂ = |Γ| − n` of l.323. -/
theorem twoDesc_sum {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {c : ℤ}
    {r₁ b₁ r₂ b₂ : ℕ} (hn : n = r₁ + r₂ + 2) (h : TwoDescAt α c r₁ b₁ r₂ b₂) :
    ∑ t ∈ range n, α t = b₁ + b₂ + n := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [← sum_range_periodic hper c, show n = r₁ + (1 + (r₂ + 1)) by omega, sum_range_add_int,
    sum_range_add_int, sum_range_add_int, twoDesc_sum_ones h1]
  have e3 : ∑ t ∈ range r₂, α (c + r₁ + ((1 : ℕ) : ℤ) + t) = r₂ := by
    rw [Nat.cast_one]; exact twoDesc_sum_ones h3
  rw [e3]
  simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, Nat.cast_one]
  rw [h2, h4]
  omega

/-- The step recursion in the form `Z_u = A'_u + (2^P − 3ⁿ)`: an ascending step multiplies by
`3/2`. -/
theorem twoDesc_run {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) (u : ℤ) (r : ℕ)
    (hr : ∀ t : ℕ, t < r → α (u + t) = 1) :
    (2 : ℤ) ^ r * ((AunAlt n (u + r) α : ℤ) + (2 ^ (∑ t ∈ range n, α t) - 3 ^ n)) =
      3 ^ r * ((AunAlt n u α : ℤ) + (2 ^ (∑ t ∈ range n, α t) - 3 ^ n)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ih' := ih (fun t ht => hr t (by omega))
    have e := two_pow_mul_AunAlt_succ hper (u + r)
    rw [hr r (by omega), pow_one] at e
    rw [show u + ((r + 1 : ℕ) : ℤ) = u + r + 1 by push_cast; ring]
    linear_combination (2 : ℤ) ^ r * e + 3 * ih'

/-- **The key identity.** `A'_c + (2^P − 3ⁿ) = 2^{r₁+1} E(r₂ + 1, b₁, b₂)`, for every
configuration, with no ascending index required (so the case `k₂ = k₁ + 1` is included). On a
cycle `A'_c = (2^{p_n} − 3ⁿ) x_c`, so this is `(2^{p_n} − 3ⁿ)(x_c + 1) = 2^{r₁+1} E`. -/
theorem twoDesc_key {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {c : ℤ}
    {r₁ b₁ r₂ b₂ : ℕ} (hn : n = r₁ + r₂ + 2) (h : TwoDescAt α c r₁ b₁ r₂ b₂) :
    (AunAlt n c α : ℤ) + (2 ^ (∑ t ∈ range n, α t) - 3 ^ n) =
      2 ^ (r₁ + 1) * twoDescE (r₂ + 1) b₁ b₂ := by
  have hsum := twoDesc_sum hper hn h
  obtain ⟨h1, h2, h3, h4⟩ := h
  set D : ℤ := 2 ^ (∑ t ∈ range n, α t) - 3 ^ n with hD
  have hD' : D = 2 ^ b₁ * 2 ^ b₂ * 2 ^ r₁ * 2 ^ r₂ * 4 - 3 ^ r₁ * 3 ^ r₂ * 9 := by
    rw [hD, hsum, hn]; ring
  have hodd : Odd D := by
    rw [hD]
    exact (Int.even_pow.2 ⟨even_two, by omega⟩).sub_odd (Odd.pow ⟨1, by norm_num⟩)
  have hD0 : D ≠ 0 := by
    rintro h0
    rw [h0] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  have e1 := twoDesc_run hper c r₁ h1
  have e2 := two_pow_mul_AunAlt_succ hper (c + r₁)
  rw [h2] at e2
  have e3 := twoDesc_run hper (c + r₁ + 1) r₂ h3
  have e4 := two_pow_mul_AunAlt_succ hper (c + r₁ + 1 + r₂)
  rw [h4] at e4
  have e5 : (AunAlt n (c + r₁ + 1 + r₂ + 1) α : ℤ) = AunAlt n c α := by
    rw [show c + r₁ + 1 + r₂ + 1 = c + n by rw [hn]; push_cast; ring]
    exact_mod_cast AunAlt_periodic hper c
  rw [e5] at e4
  rw [← hD] at e1 e2 e3 e4
  have key : D * ((AunAlt n c α : ℤ) + D - 2 ^ (r₁ + 1) * twoDescE (r₂ + 1) b₁ b₂) = 0 := by
    simp only [twoDescE]
    linear_combination (2 * 2 ^ b₁ * 2 ^ r₂ * 2 ^ r₁) * e4 + (6 * 2 ^ b₁ * 2 ^ r₁) * e3 +
      (3 * 3 ^ r₂ * 2 ^ r₁) * e2 + (9 * 3 ^ r₂) * e1 + ((AunAlt n c α : ℤ) + D) * hD'
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 hD0
  · linear_combination h0

/-- The same configuration seen from the index after the first descending one. -/
theorem twoDescAt_rotate {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {c : ℤ}
    {r₁ b₁ r₂ b₂ : ℕ} (hn : n = r₁ + r₂ + 2) (h : TwoDescAt α c r₁ b₁ r₂ b₂) :
    TwoDescAt α (c + r₁ + 1) r₂ b₂ r₁ b₁ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hcn : ∀ s : ℤ, c + r₁ + 1 + r₂ + 1 + s = (c + s) + n := by
    intro s; rw [hn]; push_cast; ring
  refine ⟨h3, h4, fun t ht => ?_, ?_⟩
  · rw [hcn, hper]; exact h1 t ht
  · rw [hcn, hper]; exact h2

/-- The configuration is invariant under a shift of the base point by a multiple of `n`. -/
theorem twoDescAt_add_mul {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {c : ℤ}
    {r₁ b₁ r₂ b₂ : ℕ} (h : TwoDescAt α c r₁ b₁ r₂ b₂) (q : ℤ) :
    TwoDescAt α (c + q * n) r₁ b₁ r₂ b₂ := by
  have hp : ∀ s : ℤ, α (c + q * n + s) = α (c + s) := fun s => by
    have := hper.int_mul q (c + s)
    simp only [Int.cast_id] at this
    rw [← this]; congr 1; ring
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun t ht => by rw [hp]; exact h1 t ht, by rw [hp]; exact h2,
    fun t ht => ?_, ?_⟩
  · rw [show c + q * n + r₁ + 1 + t = c + q * n + (r₁ + 1 + t) by ring, hp,
      show c + (r₁ + 1 + t : ℤ) = c + r₁ + 1 + t by ring]
    exact h3 t ht
  · rw [show c + q * n + r₁ + 1 + r₂ = c + q * n + (r₁ + 1 + r₂) by ring, hp,
      show c + (r₁ + 1 + r₂ : ℤ) = c + r₁ + 1 + r₂ by ring]
    exact h4

/-- **The `∼_S` form, exact, OQ-43 reading**: at the ascending index `c + t` (`t < r₁`),
`Δ'_{c+t} = 3^t 2^{r₁−t} E(r₂ + 1, b₁, b₂)`. -/
theorem twoDesc_deltaAlt {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {c : ℤ}
    {r₁ b₁ r₂ b₂ : ℕ} (hn : n = r₁ + r₂ + 2) (h : TwoDescAt α c r₁ b₁ r₂ b₂) {t : ℕ}
    (ht : t < r₁) :
    DeltaAlt n α (c + t) = 3 ^ t * 2 ^ (r₁ - t) * twoDescE (r₂ + 1) b₁ b₂ := by
  have hk := twoDesc_key hper hn h
  have hr := twoDesc_run hper c t (fun t' ht' => h.1 t' (by omega))
  have e := two_pow_mul_AunAlt_succ hper (c + t)
  rw [h.1 t ht, pow_one] at e
  obtain ⟨s, hs⟩ : ∃ s, r₁ = t + 1 + s := ⟨r₁ - t - 1, by omega⟩
  rw [show r₁ - t = s + 1 by omega]
  rw [hs] at hk
  have e2 : (2 : ℤ) ^ (t + 1) * DeltaAlt n α (c + t) =
      2 ^ (t + 1) * (3 ^ t * 2 ^ (s + 1) * twoDescE (r₂ + 1) b₁ b₂) := by
    simp only [DeltaAlt]
    rw [pow_succ]
    linear_combination (2 : ℤ) ^ t * e + hr + 3 ^ t * hk
  exact mul_left_cancel₀ (by positivity) e2

/-- **The `∼_S` form, exact, printed `A_u^n`**: `Δ_{c+t} = 3^{t+1} 2^{r₁−t} E(r₂ + 1, b₁, b₂)`. -/
theorem twoDesc_delta {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {c : ℤ}
    {r₁ b₁ r₂ b₂ : ℕ} (hn : n = r₁ + r₂ + 2) (h : TwoDescAt α c r₁ b₁ r₂ b₂) {t : ℕ}
    (ht : t < r₁) :
    Delta n α (c + t) = 3 ^ (t + 1) * 2 ^ (r₁ - t) * twoDescE (r₂ + 1) b₁ b₂ := by
  rw [Delta_eq_three_mul hper, twoDesc_deltaAlt hper hn h ht]
  ring

/-- **The exact two-term form** (l.310–314 with the exponent of OQ-68 (b) corrected), OQ-43
reading: at an ascending `u` whose next descending indices are `u + s₁` and `u + s₂`,
`Δ'_u = 3^{n−1−s₁} 2^{s₁−1} (2^{a_{u+s₁}} − 2)`
`+ 3^{n−1−s₂} 2^{s₂−2+a_{u+s₁}} (2^{a_{u+s₂}} − 2)`. -/
theorem twoDesc_deltaAlt_two_terms {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {c : ℤ}
    {r₁ b₁ r₂ b₂ : ℕ} (hn : n = r₁ + r₂ + 2) (h : TwoDescAt α c r₁ b₁ r₂ b₂) {t s₁ s₂ : ℕ}
    (hs₁ : t + s₁ = r₁) (hs₂ : s₂ = s₁ + 1 + r₂) (hs : 1 ≤ s₁) :
    DeltaAlt n α (c + t) =
      3 ^ (n - 1 - s₁) * 2 ^ (s₁ - 1) * (2 ^ α (c + t + s₁) - 2) +
        3 ^ (n - 1 - s₂) * 2 ^ (s₂ - 2 + α (c + t + s₁)) * (2 ^ α (c + t + s₂) - 2) := by
  rw [twoDesc_deltaAlt hper hn h (by omega)]
  have i1 : c + (t : ℤ) + (s₁ : ℤ) = c + r₁ := by rw [← hs₁]; push_cast; ring
  have i2 : c + (t : ℤ) + (s₂ : ℤ) = c + r₁ + 1 + r₂ := by rw [hs₂, ← hs₁]; push_cast; ring
  rw [i1, i2, h.2.1, h.2.2.2]
  obtain ⟨s, rfl⟩ : ∃ s, s₁ = s + 1 := ⟨s₁ - 1, by omega⟩
  rw [show r₁ - t = s + 1 by omega, show n - 1 - (s + 1) = r₂ + 1 + t by omega,
    show n - 1 - s₂ = t by omega, show s + 1 - 1 = s by omega,
    show s₂ - 2 + (b₁ + 1) = s + r₂ + b₁ + 1 by omega]
  simp only [twoDescE]
  ring

/-- The same, printed `A_u^n`: `3^{n−s}` in place of `3^{n−1−s}`. -/
theorem twoDesc_delta_two_terms {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {c : ℤ}
    {r₁ b₁ r₂ b₂ : ℕ} (hn : n = r₁ + r₂ + 2) (h : TwoDescAt α c r₁ b₁ r₂ b₂) {t s₁ s₂ : ℕ}
    (hs₁ : t + s₁ = r₁) (hs₂ : s₂ = s₁ + 1 + r₂) (hs : 1 ≤ s₁) :
    Delta n α (c + t) =
      3 ^ (n - s₁) * 2 ^ (s₁ - 1) * (2 ^ α (c + t + s₁) - 2) +
        3 ^ (n - s₂) * 2 ^ (s₂ - 2 + α (c + t + s₁)) * (2 ^ α (c + t + s₂) - 2) := by
  rw [Delta_eq_three_mul hper, twoDesc_deltaAlt_two_terms hper hn h hs₁ hs₂ hs,
    show n - s₁ = n - 1 - s₁ + 1 by omega, show n - s₂ = n - 1 - s₂ + 1 by omega]
  ring

/-! ### The paper's configuration: `𝒟 = (k₁ + nℤ) ∪ (k₂ + nℤ)` -/

/-- From `𝒟 = (k₁ + nℤ) ∪ (k₂ + nℤ)`, the configuration seen from `k₂ + 1`:
runs of `δ₂ − 1` and `δ₁ − 1` ascending indices, with `a_{k₁}`, `a_{k₂}` between them. -/
theorem twoDescAt_of_classes {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n)
    (hpos : ∀ i, 1 ≤ α i) {k₁ k₂ : ℤ} (hk₁ : 1 ≤ k₁) (hk : k₁ < k₂) (hk₂ : k₂ ≤ n)
    (hC : TwoDescClasses α n k₁ k₂) {δ₁ δ₂ : ℕ} (hδ₁ : (δ₁ : ℤ) = k₂ - k₁)
    (hδ₂ : (δ₂ : ℤ) = n + k₁ - k₂) :
    TwoDescAt α (k₂ + 1) (δ₂ - 1) (α k₁ - 1) (δ₁ - 1) (α k₂ - 1) := by
  have hδ₁1 : 1 ≤ δ₁ := by omega
  have hδ₂1 : 1 ≤ δ₂ := by omega
  have c₁ : ((δ₁ - 1 : ℕ) : ℤ) = δ₁ - 1 := by omega
  have c₂ : ((δ₂ - 1 : ℕ) : ℤ) = δ₂ - 1 := by omega
  have hdesc : ∀ i, 1 < α i → (∃ q : ℤ, i = k₁ + q * n) ∨ (∃ q : ℤ, i = k₂ + q * n) := by
    intro i hi
    have hmem : i ∈ descIdx α := hi
    rw [hC] at hmem
    exact hmem
  have hasc : ∀ i, ¬ 1 < α i → α i = 1 := fun i hi => by have := hpos i; omega
  refine ⟨fun t ht => hasc _ (fun hi => ?_), ?_, fun t ht => hasc _ (fun hi => ?_), ?_⟩
  · rcases hdesc _ hi with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact twoDesc_not_mul (n := n) (q := q) (m := k₂ + 1 + t - k₁) (by linarith) (by omega)
        (by omega)
    · exact twoDesc_not_mul (n := n) (q := q) (m := 1 + t) (by linarith) (by omega) (by omega)
  · rw [c₂, show k₂ + 1 + ((δ₂ : ℤ) - 1) = k₁ + 1 * n by linarith, twoDesc_per hper]
    have := hpos k₁
    omega
  · rw [c₂] at hi
    rcases hdesc _ hi with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact twoDesc_not_mul (n := n) (q := q - 1) (m := 1 + t) (by linarith) (by omega) (by omega)
    · exact twoDesc_not_mul (n := n) (q := q) (m := δ₂ + 1 + t) (by linarith) (by omega) (by omega)
  · rw [c₂, c₁, show k₂ + 1 + ((δ₂ : ℤ) - 1) + 1 + ((δ₁ : ℤ) - 1) = k₂ + 1 * n by linarith,
      twoDesc_per hper]
    have := hpos k₂
    omega

/-- **The key identity in the paper's notation**, both ways round:
`A'_{k₂+1} + (2^P − 3ⁿ) = 2^{δ₂} E(δ₁, α₁, α₂)` and `A'_{k₁+1} + (2^P − 3ⁿ) = 2^{δ₁} E(δ₂, α₂, α₁)`,
with `P = α₁ + α₂ + n`. No ascending index is needed. -/
theorem twoDesc_key_classes {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n)
    (hpos : ∀ i, 1 ≤ α i) {k₁ k₂ : ℤ} (hk₁ : 1 ≤ k₁) (hk : k₁ < k₂) (hk₂ : k₂ ≤ n)
    (hC : TwoDescClasses α n k₁ k₂) {δ₁ δ₂ : ℕ} (hδ₁ : (δ₁ : ℤ) = k₂ - k₁)
    (hδ₂ : (δ₂ : ℤ) = n + k₁ - k₂) :
    ∑ t ∈ range n, α t = (α k₁ - 1) + (α k₂ - 1) + n ∧
    (AunAlt n (k₂ + 1) α : ℤ) + (2 ^ (∑ t ∈ range n, α t) - 3 ^ n) =
      2 ^ δ₂ * twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) ∧
    (AunAlt n (k₁ + 1) α : ℤ) + (2 ^ (∑ t ∈ range n, α t) - 3 ^ n) =
      2 ^ δ₁ * twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) := by
  have hδ₁1 : 1 ≤ δ₁ := by omega
  have hδ₂1 : 1 ≤ δ₂ := by omega
  have h := twoDescAt_of_classes hper hpos hk₁ hk hk₂ hC hδ₁ hδ₂
  have hn : n = (δ₂ - 1) + (δ₁ - 1) + 2 := by omega
  refine ⟨twoDesc_sum hper hn h, ?_, ?_⟩
  · have e := twoDesc_key hper hn h
    rwa [show δ₂ - 1 + 1 = δ₂ by omega, show δ₁ - 1 + 1 = δ₁ by omega] at e
  · have hn' : n = (δ₁ - 1) + (δ₂ - 1) + 2 := by omega
    have e := twoDesc_key hper hn' (twoDescAt_rotate hper hn h)
    rw [show δ₁ - 1 + 1 = δ₁ by omega, show δ₂ - 1 + 1 = δ₂ by omega,
      show k₂ + 1 + ((δ₂ - 1 : ℕ) : ℤ) + 1 = (k₁ + 1) + n by omega] at e
    have ep : AunAlt n (k₁ + 1 + n) α = AunAlt n (k₁ + 1) α := AunAlt_periodic hper (k₁ + 1)
    rwa [ep] at e

/-- **l.318 in its true form** (positions of l.308, `k₁ < i < k₂`), both readings of OQ-43:
`Δ'_i = 3^{i−k₁−1} 2^{k₂−i} E(δ₂, α₂, α₁)`, `Δ_i = 3^{i−k₁} 2^{k₂−i} E(δ₂, α₂, α₁)`, so
`Δ_i ∼_S 3^{δ₂}(2^{α₂} − 1) + 2^{δ₂+α₂}(2^{α₁} − 1)`: l.318 with `α₁` and `α₂` exchanged. -/
theorem twoDesc_delta_i {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n)
    (hpos : ∀ i, 1 ≤ α i) {k₁ k₂ : ℤ} (hk₁ : 1 ≤ k₁) (hk : k₁ < k₂) (hk₂ : k₂ ≤ n)
    (hC : TwoDescClasses α n k₁ k₂) {δ₁ δ₂ : ℕ} (hδ₁ : (δ₁ : ℤ) = k₂ - k₁)
    (hδ₂ : (δ₂ : ℤ) = n + k₁ - k₂) {i : ℤ} (hi₁ : k₁ < i) (hi₂ : i < k₂) :
    α i = 1 ∧
    (DeltaAlt n α i : ℚ) =
      (3 : ℚ) ^ (i - k₁ - 1) * 2 ^ (k₂ - i) * twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) ∧
    (Delta n α i : ℚ) = (3 : ℚ) ^ (i - k₁) * 2 ^ (k₂ - i) * twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) ∧
    SEquiv (DeltaAlt n α i) (twoDescE δ₂ (α k₂ - 1) (α k₁ - 1)) ∧
    SEquiv (Delta n α i) (twoDescE δ₂ (α k₂ - 1) (α k₁ - 1)) := by
  have hδ₁1 : 1 ≤ δ₁ := by omega
  have hδ₂1 : 1 ≤ δ₂ := by omega
  have h := twoDescAt_of_classes hper hpos hk₁ hk hk₂ hC hδ₁ hδ₂
  have hn : n = (δ₂ - 1) + (δ₁ - 1) + 2 := by omega
  have h' := twoDescAt_add_mul hper (twoDescAt_rotate hper hn h) (-1)
  rw [show k₂ + 1 + ((δ₂ - 1 : ℕ) : ℤ) + 1 + -1 * (n : ℤ) = k₁ + 1 by omega] at h'
  have hn' : n = (δ₁ - 1) + (δ₂ - 1) + 2 := by omega
  obtain ⟨t, ht⟩ : ∃ t : ℕ, i = k₁ + 1 + t := ⟨(i - k₁ - 1).toNat, by omega⟩
  have htlt : t < δ₁ - 1 := by omega
  have e1 := twoDesc_deltaAlt hper hn' h' htlt
  rw [show δ₂ - 1 + 1 = δ₂ by omega, ← ht] at e1
  have hz1 : (3 : ℚ) ^ (i - k₁ - 1) = 3 ^ t := by
    rw [show i - k₁ - 1 = (t : ℤ) by omega, zpow_natCast]
  have hz2 : (2 : ℚ) ^ (k₂ - i) = 2 ^ (δ₁ - 1 - t) := by
    rw [show k₂ - i = ((δ₁ - 1 - t : ℕ) : ℤ) by omega, zpow_natCast]
  have hz3 : (3 : ℚ) ^ (i - k₁) = 3 ^ (t + 1) := by
    rw [show i - k₁ = ((t + 1 : ℕ) : ℤ) by push_cast; omega, zpow_natCast]
  have q1 : (DeltaAlt n α i : ℚ) =
      (3 : ℚ) ^ (i - k₁ - 1) * 2 ^ (k₂ - i) * twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) := by
    rw [hz1, hz2, e1]; push_cast; ring
  have q2 : (Delta n α i : ℚ) =
      (3 : ℚ) ^ (i - k₁) * 2 ^ (k₂ - i) * twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) := by
    rw [Delta_eq_three_mul hper]; push_cast; rw [q1, hz1, hz3]; ring
  refine ⟨by rw [ht]; exact h'.1 t htlt, q1, q2, ?_, ?_⟩
  · exact ⟨2 ^ (k₂ - i) * 3 ^ (i - k₁ - 1), ⟨k₂ - i, i - k₁ - 1, rfl⟩, by rw [q1]; ring⟩
  · exact ⟨2 ^ (k₂ - i) * 3 ^ (i - k₁), ⟨k₂ - i, i - k₁, rfl⟩, by rw [q2]; ring⟩

/-- **l.320 in its true form** (positions of l.308, `k₂ − n < j < k₁`), both readings:
`Δ'_j = 3^{j+n−k₂−1} 2^{k₁−j} E(δ₁, α₁, α₂)`, so
`Δ_j ∼_S 3^{δ₁}(2^{α₁} − 1) + 2^{δ₁+α₁}(2^{α₂} − 1)`:
l.320 with `α₁` and `α₂` exchanged. -/
theorem twoDesc_delta_j {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n)
    (hpos : ∀ i, 1 ≤ α i) {k₁ k₂ : ℤ} (hk₁ : 1 ≤ k₁) (hk : k₁ < k₂) (hk₂ : k₂ ≤ n)
    (hC : TwoDescClasses α n k₁ k₂) {δ₁ δ₂ : ℕ} (hδ₁ : (δ₁ : ℤ) = k₂ - k₁)
    (hδ₂ : (δ₂ : ℤ) = n + k₁ - k₂) {j : ℤ} (hj₁ : k₂ - n < j) (hj₂ : j < k₁) :
    α j = 1 ∧
    (DeltaAlt n α j : ℚ) =
      (3 : ℚ) ^ (j + n - k₂ - 1) * 2 ^ (k₁ - j) * twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) ∧
    (Delta n α j : ℚ) = (3 : ℚ) ^ (j + n - k₂) * 2 ^ (k₁ - j) * twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) ∧
    SEquiv (DeltaAlt n α j) (twoDescE δ₁ (α k₁ - 1) (α k₂ - 1)) ∧
    SEquiv (Delta n α j) (twoDescE δ₁ (α k₁ - 1) (α k₂ - 1)) := by
  have hδ₁1 : 1 ≤ δ₁ := by omega
  have hδ₂1 : 1 ≤ δ₂ := by omega
  have h0 := twoDescAt_of_classes hper hpos hk₁ hk hk₂ hC hδ₁ hδ₂
  have hn : n = (δ₂ - 1) + (δ₁ - 1) + 2 := by omega
  have h := twoDescAt_add_mul hper h0 (-1)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, j = k₂ + 1 + -1 * (n : ℤ) + t := ⟨(j - k₂ - 1 + n).toNat, by omega⟩
  have htlt : t < δ₂ - 1 := by omega
  have e1 := twoDesc_deltaAlt hper hn h htlt
  rw [show δ₁ - 1 + 1 = δ₁ by omega, ← ht] at e1
  have hz1 : (3 : ℚ) ^ (j + n - k₂ - 1) = 3 ^ t := by
    rw [show j + n - k₂ - 1 = (t : ℤ) by omega, zpow_natCast]
  have hz2 : (2 : ℚ) ^ (k₁ - j) = 2 ^ (δ₂ - 1 - t) := by
    rw [show k₁ - j = ((δ₂ - 1 - t : ℕ) : ℤ) by omega, zpow_natCast]
  have hz3 : (3 : ℚ) ^ (j + n - k₂) = 3 ^ (t + 1) := by
    rw [show j + n - k₂ = ((t + 1 : ℕ) : ℤ) by push_cast; omega, zpow_natCast]
  have q1 : (DeltaAlt n α j : ℚ) =
      (3 : ℚ) ^ (j + n - k₂ - 1) * 2 ^ (k₁ - j) * twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) := by
    rw [hz1, hz2, e1]; push_cast; ring
  have q2 : (Delta n α j : ℚ) =
      (3 : ℚ) ^ (j + n - k₂) * 2 ^ (k₁ - j) * twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) := by
    rw [Delta_eq_three_mul hper]; push_cast; rw [q1, hz1, hz3]; ring
  refine ⟨by rw [ht]; exact h.1 t htlt, q1, q2, ?_, ?_⟩
  · exact ⟨2 ^ (k₁ - j) * 3 ^ (j + n - k₂ - 1), ⟨k₁ - j, j + n - k₂ - 1, rfl⟩, by rw [q1]; ring⟩
  · exact ⟨2 ^ (k₁ - j) * 3 ^ (j + n - k₂), ⟨k₁ - j, j + n - k₂, rfl⟩, by rw [q2]; ring⟩

/-! ### The bound of l.323–325, in the form that holds -/

/-- `E(δ, b₁, b₂) > 0` when `b₁ ≥ 1`. -/
theorem twoDescE_pos {δ b₁ b₂ : ℕ} (h : 1 ≤ b₁) : 0 < twoDescE δ b₁ b₂ := by
  have h2 : (2 : ℤ) ≤ 2 ^ b₁ := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b₁ := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h
  have h3 : (0 : ℤ) < 3 ^ δ := by positivity
  have h4 : (1 : ℤ) ≤ 2 ^ b₂ := one_le_pow₀ (by norm_num)
  have h5 : (0 : ℤ) < 2 ^ (δ + b₁) := by positivity
  simp only [twoDescE]
  nlinarith

/-- `E(δ, b₁, b₂) ≤ 2^{b₁+b₂} (3^δ + 2^δ)`: the first inequality of l.324, for the S-free part. -/
theorem twoDescE_le (δ b₁ b₂ : ℕ) : twoDescE δ b₁ b₂ ≤ 2 ^ (b₁ + b₂) * (3 ^ δ + 2 ^ δ) := by
  simp only [twoDescE]
  have h1 : (1 : ℤ) ≤ 2 ^ b₁ := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℤ) ≤ 2 ^ b₂ := one_le_pow₀ (by norm_num)
  have h3 : (0 : ℤ) ≤ 3 ^ δ := by positivity
  have h4 : (0 : ℤ) ≤ 2 ^ δ := by positivity
  have h5 : (0 : ℤ) ≤ 3 ^ δ * (2 ^ b₁ * (2 ^ b₂ - 1)) :=
    mul_nonneg h3 (mul_nonneg (by linarith) (by linarith))
  have h6 : (0 : ℤ) ≤ 2 ^ δ * 2 ^ b₁ := mul_nonneg h4 (by linarith)
  rw [pow_add, pow_add]
  nlinarith

/-- **The divisibility behind l.323–326**: on every cycle of `ℤ` with exactly two descending
indices per period, `2^{p_n} − 3ⁿ` divides both `E(δ₁, α₁, α₂)` and `E(δ₂, α₂, α₁)`, so
`|2^{p_n} − 3ⁿ|` is at most each. Every configuration, the case `k₂ = k₁ + 1` included. -/
theorem twoDesc_abs_le {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) {k₁ k₂ : ℤ} (hk₁ : 1 ≤ k₁)
    (hk : k₁ < k₂) (hk₂ : k₂ ≤ n) (hC : TwoDescClasses α n k₁ k₂) {δ₁ δ₂ : ℕ}
    (hδ₁ : (δ₁ : ℤ) = k₂ - k₁) (hδ₂ : (δ₂ : ℤ) = n + k₁ - k₂) :
    ((2 : ℤ) ^ p n x - 3 ^ n) ∣ twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) ∧
    ((2 : ℤ) ^ p n x - 3 ^ n) ∣ twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) ∧
    |(2 : ℤ) ^ p n x - 3 ^ n| ≤ twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) ∧
    |(2 : ℤ) ^ p n x - 3 ^ n| ≤ twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) := by
  have hpos := one_le_of_cycle hn hx hper hα
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  obtain ⟨-, e1, e2⟩ := twoDesc_key_classes hper hpos hk₁ hk hk₂ hC hδ₁ hδ₂
  rw [← hP] at e1 e2
  have hdvd : ∀ u : ℤ, ((2 : ℤ) ^ p n x - 3 ^ n) ∣ (AunAlt n u α : ℤ) :=
    (dvd_iff_dvd_AunAlt_of_cycle hn hx hper hα _).1 dvd_rfl
  have hodd : Odd ((2 : ℤ) ^ p n x - 3 ^ n) := by
    rw [hP]; exact (delta_odd_not_three_dvd hpos hn).1
  have h2 : ¬ (2 : ℤ) ∣ (2 : ℤ) ^ p n x - 3 ^ n :=
    fun h => Int.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 h)
  have hco : ∀ k : ℕ, IsCoprime ((2 : ℤ) ^ p n x - 3 ^ n) (2 ^ k) := fun k =>
    IsCoprime.pow_right ((Int.prime_two.coprime_iff_not_dvd).2 h2).symm
  have hdesc : ∀ k : ℤ, k = k₁ ∨ k = k₂ → 1 < α k := by
    intro k hk'
    have hmem : k ∈ descIdx α := by
      rw [hC]
      rcases hk' with rfl | rfl
      · exact Or.inl ⟨0, by ring⟩
      · exact Or.inr ⟨0, by ring⟩
    exact hmem
  have hk1 := hdesc k₁ (Or.inl rfl)
  have hk2 := hdesc k₂ (Or.inr rfl)
  have d1 : ((2 : ℤ) ^ p n x - 3 ^ n) ∣ twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) := by
    have : ((2 : ℤ) ^ p n x - 3 ^ n) ∣ 2 ^ δ₂ * twoDescE δ₁ (α k₁ - 1) (α k₂ - 1) := by
      rw [← e1]; exact dvd_add (hdvd _) dvd_rfl
    exact (hco δ₂).dvd_of_dvd_mul_left this
  have d2 : ((2 : ℤ) ^ p n x - 3 ^ n) ∣ twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) := by
    have : ((2 : ℤ) ^ p n x - 3 ^ n) ∣ 2 ^ δ₁ * twoDescE δ₂ (α k₂ - 1) (α k₁ - 1) := by
      rw [← e2]; exact dvd_add (hdvd _) dvd_rfl
    exact (hco δ₁).dvd_of_dvd_mul_left this
  refine ⟨d1, d2, Int.le_of_dvd (twoDescE_pos (by omega)) ((abs_dvd _ _).2 d1),
    Int.le_of_dvd (twoDescE_pos (by omega)) ((abs_dvd _ _).2 d2)⟩

/-- **The bound of l.323–324, integer form**: on every cycle of `ℤ` with
`#(𝒟 ∩ ⟦1, n⟧) = 2` there is `δ ≤ n/2` with `|2^{p_n} − 3ⁿ| ≤ 2^{p_n − n} (3^δ + 2^δ)`. -/
theorem twoDesc_bound {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) (hcount : twoDescCount n α = 2) :
    n ≤ p n x ∧ ∃ δ : ℕ, 2 * δ ≤ n ∧
      |(2 : ℤ) ^ p n x - 3 ^ n| ≤ 2 ^ (p n x - n) * (3 ^ δ + 2 ^ δ) := by
  obtain ⟨k₁, k₂, hk₁, hk, hk₂, hC⟩ := (twoDescCount_eq_two_iff hn hper).1 hcount
  have hpos := one_le_of_cycle hn hx hper hα
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  have hδ₁ : (((k₂ - k₁).toNat : ℕ) : ℤ) = k₂ - k₁ := by omega
  have hδ₂ : (((n + k₁ - k₂).toNat : ℕ) : ℤ) = n + k₁ - k₂ := by omega
  obtain ⟨hs, -, -⟩ := twoDesc_key_classes hper hpos hk₁ hk hk₂ hC hδ₁ hδ₂
  obtain ⟨-, -, h1, h2⟩ := twoDesc_abs_le hn hx hper hα hk₁ hk hk₂ hC hδ₁ hδ₂
  have hPn : p n x - n = (α k₁ - 1) + (α k₂ - 1) := by rw [hP, hs]; omega
  refine ⟨by rw [hP, hs]; omega, ?_⟩
  rcases le_total (k₂ - k₁).toNat (n + k₁ - k₂).toNat with hle | hle
  · refine ⟨(k₂ - k₁).toNat, by omega, ?_⟩
    rw [hPn]
    exact h1.trans (twoDescE_le _ _ _)
  · refine ⟨(n + k₁ - k₂).toNat, by omega, ?_⟩
    rw [hPn, add_comm (α k₁ - 1)]
    exact h2.trans (twoDescE_le _ _ _)

/-- **The first inequality of l.324, real form**, for `m = |2^{p_n} − 3ⁿ|`:
`m ≤ 3^{n/2} 2^{|Γ|−n} + 2^{|Γ|−n} 2^{n/2}`. -/
theorem twoDesc_bound_rpow {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) (hcount : twoDescCount n α = 2) :
    |(2 : ℝ) ^ p n x - 3 ^ n| ≤
      (3 : ℝ) ^ ((n : ℝ) / 2) * 2 ^ ((p n x : ℝ) - n) +
        2 ^ ((p n x : ℝ) - n) * 2 ^ ((n : ℝ) / 2) := by
  obtain ⟨hnP, δ, hδ, hb⟩ := twoDesc_bound hn hx hper hα hcount
  have hb' : |(2 : ℝ) ^ p n x - 3 ^ n| ≤ (2 : ℝ) ^ (p n x - n) * (3 ^ δ + 2 ^ δ) := by
    exact_mod_cast hb
  have hK : (2 : ℝ) ^ ((p n x : ℝ) - n) = 2 ^ (p n x - n) := by
    rw [← Nat.cast_sub hnP, Real.rpow_natCast]
  have hδr : (δ : ℝ) ≤ (n : ℝ) / 2 := by
    have : ((2 * δ : ℕ) : ℝ) ≤ n := by exact_mod_cast hδ
    push_cast at this
    linarith
  have h3 : (3 : ℝ) ^ δ ≤ 3 ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hδr
  have h2 : (2 : ℝ) ^ δ ≤ 2 ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hδr
  have hKpos : (0 : ℝ) < 2 ^ (p n x - n) := by positivity
  rw [hK]
  nlinarith

/-- On every cycle of `ℤ`, `p_n ≤ 2n` (`2^{p_n} ≤ 4ⁿ`): for `x > 0` from `3x_k + 1 ≤ 4x_k`, for
`x < 0` from `2^{p_n} < 3ⁿ`. -/
theorem twoDesc_p_le {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) : p n x ≤ 2 * n := by
  have hx0 : x ≠ 0 := ne_zero_of_T_cycle_int hn hx
  have hsign := two_pow_p_sub_three_pow_mul_pos hn hx
  have key : (2 : ℤ) ^ p n x ≤ 2 ^ (2 * n) := by
    rw [pow_mul]
    norm_num
    rcases lt_or_gt_of_ne hx0 with hneg | hposx
    · have hlt : (2 : ℤ) ^ p n x - 3 ^ n < 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      have h3 : (3 : ℤ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      linarith
    · have hprod := pow_p_mul_T_iterate_eq_prod hx0 n
      rw [hx] at hprod
      have hle : ∏ k ∈ range n, (1 + 1 / (3 * ((T^[k] x : ℤ) : ℝ))) ≤ (4 / 3 : ℝ) ^ n := by
        refine (Finset.prod_le_prod (g := fun _ => (4 / 3 : ℝ)) (fun k _ => ?_)
          (fun k _ => ?_)).trans (by rw [Finset.prod_const, Finset.card_range])
        · exact (one_add_one_div_three_mul_pos (T_iterate_ne_zero_int hx0 k)).le
        · have hk : (1 : ℝ) ≤ ((T^[k] x : ℤ) : ℝ) := by
            exact_mod_cast (T_iterate_pos_int hposx k)
          have : 1 / (3 * ((T^[k] x : ℤ) : ℝ)) ≤ 1 / 3 :=
            one_div_le_one_div_of_le (by norm_num) (by linarith)
          linarith
      have hxr : (0 : ℝ) < x := by exact_mod_cast hposx
      have h4 : (2 : ℝ) ^ p n x * x ≤ 4 ^ n * x := by
        rw [hprod, show (4 : ℝ) ^ n = 3 ^ n * (4 / 3) ^ n by rw [← mul_pow]; norm_num]
        have : (0 : ℝ) ≤ 3 ^ n * x := by positivity
        nlinarith
      have h5 : (2 : ℝ) ^ p n x ≤ 4 ^ n := le_of_mul_le_mul_right h4 hxr
      exact_mod_cast h5
  have key2 : (2 : ℕ) ^ p n x ≤ 2 ^ (2 * n) := by exact_mod_cast key
  exact (pow_le_pow_iff_right₀ (by norm_num)).1 key2

/-- **The bound, uniform in `n`**: on every cycle of `ℤ` with `#(𝒟 ∩ ⟦1, n⟧) = 2`,
`(2^{p_n} − 3ⁿ)⁴ ≤ 16 · 12^{p_n}`, i.e. `|2^{p_n} − 3ⁿ| ≤ 2 · 2^{p_n (1 − ε₀)}` with
`2^{1−ε₀} = 12^{1/4}`. -/
theorem twoDesc_bound_pow_four {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) (hcount : twoDescCount n α = 2) :
    ((2 : ℤ) ^ p n x - 3 ^ n) ^ 4 ≤ 16 * 12 ^ p n x := by
  obtain ⟨hnP, δ, hδ, hb⟩ := twoDesc_bound hn hx hper hα hcount
  have hP2 := twoDesc_p_le hn hx
  obtain ⟨q, hq⟩ : ∃ q, p n x = n + q := ⟨p n x - n, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, n = q + m := ⟨n - q, by omega⟩
  rw [show p n x - n = q by omega] at hb
  have h23 : (2 : ℤ) ^ δ ≤ 3 ^ δ := pow_le_pow_left₀ (by norm_num) (by norm_num) δ
  have hA : (0 : ℤ) < 2 ^ q := by positivity
  have h1 : |(2 : ℤ) ^ p n x - 3 ^ n| ≤ 2 * 2 ^ q * 3 ^ δ := by nlinarith
  have h2 : ((2 : ℤ) ^ p n x - 3 ^ n) ^ 4 ≤ (2 * 2 ^ q * 3 ^ δ) ^ 4 := by
    rw [← Even.pow_abs ⟨2, rfl⟩]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 4
  have h3 : ((3 : ℤ) ^ δ) ^ 4 ≤ (3 ^ q * 3 ^ m) ^ 2 := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hZ : (3 : ℤ) ^ m ≤ (2 ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have e12 : (16 : ℤ) * 12 ^ p n x =
      16 * ((2 ^ q) ^ 2 * 2 ^ m) ^ 2 * ((3 ^ q) ^ 2 * 3 ^ m) := by
    rw [hq, hm, show (12 : ℤ) = 2 * 2 * 3 by norm_num, mul_pow, mul_pow]
    ring
  rw [e12]
  have hC : (0 : ℤ) ≤ 16 * (2 ^ q) ^ 4 * (3 ^ q) ^ 2 * 3 ^ m := by positivity
  calc ((2 : ℤ) ^ p n x - 3 ^ n) ^ 4 ≤ (2 * 2 ^ q * 3 ^ δ) ^ 4 := h2
    _ = 16 * (2 ^ q) ^ 4 * ((3 : ℤ) ^ δ) ^ 4 := by ring
    _ ≤ 16 * (2 ^ q) ^ 4 * (3 ^ q * 3 ^ m) ^ 2 := by gcongr
    _ = (16 * (2 ^ q) ^ 4 * (3 ^ q) ^ 2 * 3 ^ m) * 3 ^ m := by ring
    _ ≤ (16 * (2 ^ q) ^ 4 * (3 ^ q) ^ 2 * 3 ^ m) * (2 ^ m) ^ 2 := by gcongr
    _ = 16 * ((2 ^ q) ^ 2 * 2 ^ m) ^ 2 * ((3 ^ q) ^ 2 * 3 ^ m) := by ring

/-- The exponent `ε₀ = 1/2 − (log₂ 3)/4 ≈ 0.104` of the bound that holds. -/
noncomputable def twoDescEps : ℝ := 1 / 2 - Real.logb 2 3 / 4

theorem twoDescEps_pos : 0 < twoDescEps := by
  have h : Real.logb 2 3 < 2 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num), Real.rpow_two]
    norm_num
  unfold twoDescEps
  linarith

/-- `2 · 2^{P(1−ε₀)}`, raised to the fourth power, is `16 · 12^P`. -/
theorem twoDesc_rpow_pow_four (P : ℕ) :
    (2 * (2 : ℝ) ^ ((P : ℝ) * (1 - twoDescEps))) ^ 4 = 16 * 12 ^ P := by
  have hL : (2 : ℝ) ^ Real.logb 2 3 = 3 := Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have e : (P : ℝ) * (1 - twoDescEps) * ((4 : ℕ) : ℝ) = ((2 * P : ℕ) : ℝ) + Real.logb 2 3 * P := by
    unfold twoDescEps; push_cast; ring
  rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ ((P : ℝ) * (1 - twoDescEps))) 4,
    ← Real.rpow_mul (by norm_num), e, Real.rpow_add (by norm_num), Real.rpow_natCast,
    Real.rpow_mul (by norm_num), hL, Real.rpow_natCast, pow_mul, ← mul_pow]
  norm_num

/-- **The hypothesis handed to `cor:property_defined_cycles_gcd`** (l.161), proved: with
`ε₀ > 0` and the constant `2`, every cycle `Γ` of `ℤ` with `#(𝒟 ∩ ⟦1, n⟧) = 2` has
`GCD(A_i(Γ)) ≤ 2 · 2^{|Γ|(1 − ε₀)}`, the GCD read as the corollary's (`corGcdAlt`, OQ-43
reading, `= |2^{p_n} − 3ⁿ|` on a cycle). -/
theorem twoDesc_corollary_hyp :
    0 < twoDescEps ∧
    ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → twoDescCount n α = 2 →
        ((corGcdAlt n α : ℤ) : ℝ) ≤ 2 * (2 : ℝ) ^ ((p n x : ℝ) * (1 - twoDescEps)) := by
  refine ⟨twoDescEps_pos, fun x n hn hx α hper hα hcount => ?_⟩
  rw [corGcdAlt_of_cycle hn hx hper hα]
  have h4 := twoDesc_bound_pow_four hn hx hper hα hcount
  have hb : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ ((p n x : ℝ) * (1 - twoDescEps)) := by positivity
  refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hb ?_
  rw [twoDesc_rpow_pow_four]
  have e : (((|(2 : ℤ) ^ p n x - 3 ^ n| : ℤ) : ℝ)) ^ 4 =
      ((((2 : ℤ) ^ p n x - 3 ^ n) ^ 4 : ℤ) : ℝ) := by
    push_cast
    exact Even.pow_abs ⟨2, rfl⟩ _
  rw [e]
  exact_mod_cast h4

/-! ### The cited steps of l.326, carried as hypotheses, and the assembly -/

/-- **The corollary to Matveev's theorem** (`theo:matveev`, `cor:property_defined_cycles_gcd`,
l.155–168), in the effective form l.326 uses, at the exponent `ε₀` and constant `2` proved here:
every `(P, n)` with `3ⁿ < 2^P` and `2^P − 3ⁿ ≤ 2 · 2^{P(1−ε₀)}` has `P ≤ B`. A hypothesis, not an
axiom: its proof is T-syr-cited's. -/
def TwoDescMatveev (B : ℕ) : Prop :=
  ∀ P n : ℕ, 0 < n → (3 : ℝ) ^ n < 2 ^ P →
    (2 : ℝ) ^ P - 3 ^ n ≤ 2 * (2 : ℝ) ^ ((P : ℝ) * (1 - twoDescEps)) → P ≤ B

/-- **The computer check of l.326**: no cycle of `x > 0` of least period `n` with `p_n ≤ B` has
exactly two descending indices in `⟦1, n⟧`. A hypothesis, not an axiom (T-syr-cited). -/
def TwoDescCheck (B : ℕ) : Prop :=
  ∀ x : ℤ, 0 < x → ∀ n : ℕ, 0 < n → T^[n] x = x → (∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) →
    p n x ≤ B → ∀ α : ℤ → ℕ, Function.Periodic α n → (∀ k : ℕ, α k = a k x) →
      twoDescCount n α ≠ 2

/-- **The statement for `x > 0` and `n` the least period, from the cited steps**
(`theo:syracuse_cycle`): the proof of l.308–326, with the corollary to Matveev's theorem and
the computer check as explicit hypotheses. -/
theorem theo_syracuse_cycle_of_cited {B : ℕ} (hM : TwoDescMatveev B) (hC : TwoDescCheck B)
    {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {α : ℤ → ℕ} (hper : Function.Periodic α n)
    (hα : ∀ k : ℕ, α k = a k x) : twoDescCount n α ≠ 2 := by
  intro hcount
  have hsign := two_pow_p_sub_three_pow_mul_pos hn hx
  have hDpos : (0 : ℤ) < 2 ^ p n x - 3 ^ n := pos_of_mul_pos_left hsign hx0.le
  have h3 : (3 : ℝ) ^ n < 2 ^ p n x := by
    have : (3 : ℤ) ^ n < 2 ^ p n x := by linarith
    exact_mod_cast this
  have hbound := twoDesc_corollary_hyp.2 x n hn hx α hper hα hcount
  rw [corGcdAlt_of_cycle hn hx hper hα, abs_of_pos hDpos] at hbound
  have hb' : (2 : ℝ) ^ p n x - 3 ^ n ≤ 2 * (2 : ℝ) ^ ((p n x : ℝ) * (1 - twoDescEps)) := by
    exact_mod_cast hbound
  exact hC x hx0 n hn hx hmin (hM (p n x) n hn h3 hb') α hper hα hcount

/-- The same in the other index convention (OQ-63 (b)), `β_{k+1} = a_k(x)`. -/
theorem theo_syracuse_cycle_of_cited_shift {B : ℕ} (hM : TwoDescMatveev B) (hC : TwoDescCheck B)
    {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {β : ℤ → ℕ} (hper : Function.Periodic β n)
    (hβ : ∀ k : ℕ, β (k + 1) = a k x) : twoDescCount n β ≠ 2 := by
  set α : ℤ → ℕ := fun i => β (i + 1) with hαdef
  have hperα : Function.Periodic α n := fun i => by
    simp only [hαdef]
    rw [show i + n + 1 = (i + 1) + n by ring, hper]
  have hα : ∀ k : ℕ, α k = a k x := fun k => by
    simp only [hαdef]
    rw [← hβ k]
  have hβα : β = fun i => α (i + -1) := by
    funext i
    show β i = β (i + -1 + 1)
    rw [neg_add_cancel_right]
  rw [hβα, twoDescCount_shift hperα]
  exact theo_syracuse_cycle_of_cited hM hC hx0 hn hx hmin hperα hα

/-! ### The case `k₂ = k₁ + 1` (l.328) -/

/-- **The case `k₂ = k₁ + 1`** (l.328), where the gap `(k₁, k₂)` holds no ascending index, so
the `Δ_i` of l.308 does not exist: the bound still holds, from the key identity at `k₂ + 1`,
`|2^{p_n} − 3ⁿ| ≤ E(1, α₁, α₂) = 3(2^{α₁} − 1) + 2^{1+α₁}(2^{α₂} − 1) ≤ 2^{p_n−n} · 5`. -/
theorem twoDesc_adjacent {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) {k₁ : ℤ} (hk₁ : 1 ≤ k₁)
    (hk₂ : k₁ + 1 ≤ n) (hC : TwoDescClasses α n k₁ (k₁ + 1)) :
    (∀ i : ℤ, k₁ < i → i < k₁ + 1 → False) ∧
    |(2 : ℤ) ^ p n x - 3 ^ n| ≤ twoDescE 1 (α k₁ - 1) (α (k₁ + 1) - 1) ∧
    |(2 : ℤ) ^ p n x - 3 ^ n| ≤ 2 ^ (p n x - n) * 5 := by
  have hpos := one_le_of_cycle hn hx hper hα
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  have hd1 : ((1 : ℕ) : ℤ) = k₁ + 1 - k₁ := by push_cast; ring
  have hd2 : (((n - 1 : ℕ)) : ℤ) = n + k₁ - (k₁ + 1) := by omega
  obtain ⟨-, -, h1, -⟩ := twoDesc_abs_le hn hx hper hα hk₁ (by omega) hk₂ hC hd1 hd2
  obtain ⟨hs, -, -⟩ := twoDesc_key_classes hper hpos hk₁ (by omega) hk₂ hC hd1 hd2
  refine ⟨fun i hi₁ hi₂ => by omega, h1, h1.trans ?_⟩
  have := twoDescE_le 1 (α k₁ - 1) (α (k₁ + 1) - 1)
  rw [show p n x - n = (α k₁ - 1) + (α (k₁ + 1) - 1) by rw [hP, hs]; omega]
  norm_num at this ⊢
  linarith

/-! ### Findings on the printed steps (l.310–325), at the cycle of `−17` -/

/-- The display of l.310–312 as printed, in `ℚ` with integer exponents
(`a₁ = a_{k₁}`, `a₂ = a_{k₂}`). -/
noncomputable def twoDescDisplayI (n : ℕ) (k₁ k₂ : ℤ) (a₁ a₂ : ℕ) (i : ℤ) : ℚ :=
  (3 : ℚ) ^ ((n : ℤ) - 1 - (k₁ - i)) * 2 ^ (k₁ - i) * (2 ^ a₁ - 2) +
    (3 : ℚ) ^ ((n : ℤ) - 1 - (k₂ - i)) * 2 ^ (k₂ - i + a₁ - 1) * (2 ^ a₂ - 2)

/-- The display of l.313–314 as printed. -/
noncomputable def twoDescDisplayJ (n : ℕ) (k₁ k₂ : ℤ) (a₁ a₂ : ℕ) (j : ℤ) : ℚ :=
  (3 : ℚ) ^ ((n : ℤ) - 1 - (k₂ - j)) * 2 ^ (k₂ - j) * (2 ^ a₂ - 2) +
    (3 : ℚ) ^ ((n : ℤ) - 1 - (k₁ + n - j)) * 2 ^ (k₁ + n - j + a₂ - 1) * (2 ^ a₁ - 2)

/-- At `−17`: `k₁ = 3`, `k₂ = 6`, `δ₁ = 3`, `δ₂ = 4`, `α₁ = 1`, `α₂ = 3`; the true S-free forms
are `E(δ₁, α₁, α₂) = 139 = |2^{11} − 3⁷|` and `E(δ₂, α₂, α₁) = 695 = 5 · 139`; the printed ones of
l.318 and l.320 are `305 = 5 · 61` and `253 = 11 · 23`. -/
theorem twoDesc_values_seq17 :
    TwoDescClasses seq17 7 3 6 ∧ seq17 3 = 2 ∧ seq17 6 = 4 ∧
    twoDescE 3 1 3 = 139 ∧ twoDescE 4 3 1 = 695 ∧ twoDescE 4 1 3 = 305 ∧ twoDescE 3 3 1 = 253 := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide, by decide⟩
  ext i
  simp only [descIdx, Set.mem_setOf_eq, Set.mem_union, seq17]
  constructor
  · intro h
    by_cases h3 : i % 7 = 3
    · exact Or.inl ⟨i / 7, by omega⟩
    · by_cases h6 : i % 7 = 6
      · exact Or.inr ⟨i / 7, by omega⟩
      · rw [if_neg h3, if_neg h6] at h; omega
  · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · rw [if_pos (by push_cast; omega)]; norm_num
    · rw [if_neg (by push_cast; omega), if_pos (by push_cast; omega)]; norm_num

/-- A multiple of `139` is `∼_S` to no nonzero non-multiple of `139`
(`v₁₃₉` of `2^u 3^v` is `0`). -/
theorem twoDesc_not_sEquiv {x y : ℤ} (hx : (139 : ℤ) ∣ x) (hy : ¬ (139 : ℤ) ∣ y) :
    ¬ SEquiv x y := by
  haveI : Fact (Nat.Prime 139) := ⟨by norm_num⟩
  rintro ⟨s, ⟨u, v, rfl⟩, hxy⟩
  have hy0 : y ≠ 0 := by rintro rfl; exact hy (dvd_zero _)
  have hs0 : (2 : ℚ) ^ u * 3 ^ v ≠ 0 := by positivity
  have hy0' : (y : ℚ) ≠ 0 := by exact_mod_cast hy0
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : (2 : ℚ) ^ u * 3 ^ v * y = 0 := by rw [← hxy]; simp
    rcases mul_eq_zero.1 h0 with h | h
    · exact hs0 h
    · exact hy0' h
  · have h1 := congrArg (padicValRat 139) hxy
    rw [padicValRat.mul hs0 hy0', padicValRat.mul (by positivity) (by positivity),
      padicValRat.zpow, padicValRat.zpow, padicValRat.of_int, padicValRat.of_int] at h1
    have h2 : padicValRat 139 2 = 0 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 139 ∣ 2)]
      simp
    have h3 : padicValRat 139 3 = 0 := by
      rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 139 ∣ 3)]
      simp
    have hvy : padicValInt 139 y = 0 :=
      padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hy)
    have hvx : 1 ≤ padicValInt 139 x := by
      have hx' : (139 : ℕ) ∣ x.natAbs := Int.natCast_dvd.1 (by exact_mod_cast hx)
      exact one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.2 hx0) hx'
    rw [h2, h3, hvy] at h1
    simp only [mul_zero, add_zero, Nat.cast_zero] at h1
    omega

/-- **Finding 4 (l.317–321).** At the cycle of `−17`, no `Δ_u` (`u ∈ ℤ`, both readings of OQ-43)
is `∼_S` to the printed form of l.318 (`305`) or of l.320 (`253`): every `Δ_u` is a multiple
of `139` and neither `305` nor `253` is. Both printed `∼_S` forms are false, whichever
positions `i, j` are read at l.308. -/
theorem twoDesc_sEquiv_printed_false (u : ℤ) :
    ¬ SEquiv (DeltaAlt 7 seq17 u) (twoDescE 4 1 3) ∧ ¬ SEquiv (Delta 7 seq17 u) (twoDescE 4 1 3) ∧
    ¬ SEquiv (DeltaAlt 7 seq17 u) (twoDescE 3 3 1) ∧
      ¬ SEquiv (Delta 7 seq17 u) (twoDescE 3 3 1) := by
  obtain ⟨hx, hα⟩ := cycle_neg_seventeen
  have hp : p 7 (-17 : ℤ) = 11 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← hα 0, ← hα 1, ← hα 2, ← hα 3, ← hα 4, ← hα 5, ← hα 6]
    decide
  have hdvd := (dvd_iff_dvd_AunAlt_of_cycle (by norm_num) hx seq17_periodic hα
    ((2 : ℤ) ^ p 7 (-17 : ℤ) - 3 ^ 7)).1 dvd_rfl
  rw [hp, show (2 : ℤ) ^ 11 - 3 ^ 7 = -139 by norm_num] at hdvd
  have h139 : ∀ v : ℤ, (139 : ℤ) ∣ (AunAlt 7 v seq17 : ℤ) := fun v => neg_dvd.1 (hdvd v)
  have hD' : (139 : ℤ) ∣ DeltaAlt 7 seq17 u := dvd_sub (h139 _) (h139 _)
  have hD : (139 : ℤ) ∣ Delta 7 seq17 u := by
    rw [Delta_eq_three_mul seq17_periodic]; exact dvd_mul_of_dvd_right hD' _
  have e305 : twoDescE 4 1 3 = 305 := by decide
  have e253 : twoDescE 3 3 1 = 253 := by decide
  rw [e305, e253]
  exact ⟨twoDesc_not_sEquiv hD' (by decide), twoDesc_not_sEquiv hD (by decide),
    twoDesc_not_sEquiv hD' (by decide), twoDesc_not_sEquiv hD (by decide)⟩

/-- **The planner's (a), in general: l.310–312 is the display for `j`, up to the factor `2`.**
At an ascending `j` with `k₂ − n < j < k₁` (the positions l.308 gives to `j`), the display printed
for `Δ_i` is `2Δ'_j = (2/3)Δ_j`: right shape, and the exponent error of `lem:syracuse_cycle_n__n_`
(OQ-68 (b)). -/
theorem twoDesc_displayI_eq {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n)
    (hpos : ∀ i, 1 ≤ α i) {k₁ k₂ : ℤ} (hk₁ : 1 ≤ k₁) (hk : k₁ < k₂) (hk₂ : k₂ ≤ n)
    (hC : TwoDescClasses α n k₁ k₂) {δ₁ δ₂ : ℕ} (hδ₁ : (δ₁ : ℤ) = k₂ - k₁)
    (hδ₂ : (δ₂ : ℤ) = n + k₁ - k₂) {j : ℤ} (hj₁ : k₂ - n < j) (hj₂ : j < k₁) :
    twoDescDisplayI n k₁ k₂ (α k₁) (α k₂) j = 2 * (DeltaAlt n α j : ℚ) ∧
    twoDescDisplayI n k₁ k₂ (α k₁) (α k₂) j = 2 / 3 * (Delta n α j : ℚ) := by
  obtain ⟨-, q1, -, -, -⟩ := twoDesc_delta_j hper hpos hk₁ hk hk₂ hC hδ₁ hδ₂ hj₁ hj₂
  have hq2 : (Delta n α j : ℚ) = 3 * (DeltaAlt n α j : ℚ) := by
    rw [Delta_eq_three_mul hper]; push_cast; ring
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = j + n - k₂ - 1 := ⟨(j + n - k₂ - 1).toNat, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = k₁ - j := ⟨(k₁ - j).toNat, by omega⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b, α k₁ = b + 1 := ⟨α k₁ - 1, by have := hpos k₁; omega⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b, α k₂ = b + 1 := ⟨α k₂ - 1, by have := hpos k₂; omega⟩
  rw [show j + (n : ℤ) - k₂ - 1 = (t : ℤ) by omega, show k₁ - j = (s : ℤ) by omega, hb₁, hb₂,
    Nat.add_sub_cancel, Nat.add_sub_cancel, zpow_natCast, zpow_natCast] at q1
  have hI : twoDescDisplayI n k₁ k₂ (α k₁) (α k₂) j = 2 * (DeltaAlt n α j : ℚ) := by
    rw [q1, twoDescDisplayI, hb₁, hb₂,
      show (n : ℤ) - 1 - (k₁ - j) = ((t + δ₁ : ℕ) : ℤ) by push_cast; omega,
      show (n : ℤ) - 1 - (k₂ - j) = (t : ℤ) by omega,
      show k₂ - j + ((b₁ + 1 : ℕ) : ℤ) - 1 = ((s + δ₁ + b₁ : ℕ) : ℤ) by push_cast; omega,
      show k₁ - j = (s : ℤ) by omega]
    simp only [zpow_natCast, twoDescE]
    push_cast
    ring
  refine ⟨hI, ?_⟩
  rw [hI, hq2]
  ring

/-- **The planner's (a), in general: l.313–314 is the display for `i`, up to the factor `2`.**
At an ascending `i` with `k₁ < i < k₂` (the positions l.308 gives to `i`), the display printed for
`Δ_j` is `2Δ'_i = (2/3)Δ_i`. -/
theorem twoDesc_displayJ_eq {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n)
    (hpos : ∀ i, 1 ≤ α i) {k₁ k₂ : ℤ} (hk₁ : 1 ≤ k₁) (hk : k₁ < k₂) (hk₂ : k₂ ≤ n)
    (hC : TwoDescClasses α n k₁ k₂) {δ₁ δ₂ : ℕ} (hδ₁ : (δ₁ : ℤ) = k₂ - k₁)
    (hδ₂ : (δ₂ : ℤ) = n + k₁ - k₂) {i : ℤ} (hi₁ : k₁ < i) (hi₂ : i < k₂) :
    twoDescDisplayJ n k₁ k₂ (α k₁) (α k₂) i = 2 * (DeltaAlt n α i : ℚ) ∧
    twoDescDisplayJ n k₁ k₂ (α k₁) (α k₂) i = 2 / 3 * (Delta n α i : ℚ) := by
  obtain ⟨-, q1, -, -, -⟩ := twoDesc_delta_i hper hpos hk₁ hk hk₂ hC hδ₁ hδ₂ hi₁ hi₂
  have hq2 : (Delta n α i : ℚ) = 3 * (DeltaAlt n α i : ℚ) := by
    rw [Delta_eq_three_mul hper]; push_cast; ring
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = i - k₁ - 1 := ⟨(i - k₁ - 1).toNat, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = k₂ - i := ⟨(k₂ - i).toNat, by omega⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b, α k₁ = b + 1 := ⟨α k₁ - 1, by have := hpos k₁; omega⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b, α k₂ = b + 1 := ⟨α k₂ - 1, by have := hpos k₂; omega⟩
  rw [show i - k₁ - 1 = (t : ℤ) by omega, show k₂ - i = (s : ℤ) by omega, hb₁, hb₂,
    Nat.add_sub_cancel, Nat.add_sub_cancel, zpow_natCast, zpow_natCast] at q1
  have hJ : twoDescDisplayJ n k₁ k₂ (α k₁) (α k₂) i = 2 * (DeltaAlt n α i : ℚ) := by
    rw [q1, twoDescDisplayJ, hb₁, hb₂,
      show (n : ℤ) - 1 - (k₂ - i) = ((t + δ₂ : ℕ) : ℤ) by push_cast; omega,
      show (n : ℤ) - 1 - (k₁ + n - i) = (t : ℤ) by omega,
      show k₁ + n - i + ((b₂ + 1 : ℕ) : ℤ) - 1 = ((s + δ₂ + b₂ : ℕ) : ℤ) by push_cast; omega,
      show k₂ - i = (s : ℤ) by omega]
    simp only [zpow_natCast, twoDescE]
    push_cast
    ring
  refine ⟨hJ, ?_⟩
  rw [hJ, hq2]
  ring

/-- **Finding 3 (l.310–314).** At the cycle of `−17`, at every ascending index `u` of a period
(`u ∈ {0, 1, 2, 4, 5}`), neither printed display equals `Δ'_u` or `Δ_u`: the exact displays are
false whichever positions are read at l.308. At the positions where each display is the
right shape (`u < k₁` for l.310, `k₁ < u` for l.313) it is `2Δ'_u` (the factor of OQ-68 (b)). -/
theorem twoDesc_displays_printed_false :
    ∀ u : ℤ, u ∈ ({0, 1, 2, 4, 5} : Finset ℤ) →
      (DeltaAlt 7 seq17 u : ℚ) ≠ twoDescDisplayI 7 3 6 2 4 u ∧
      (Delta 7 seq17 u : ℚ) ≠ twoDescDisplayI 7 3 6 2 4 u ∧
      (DeltaAlt 7 seq17 u : ℚ) ≠ twoDescDisplayJ 7 3 6 2 4 u ∧
      (Delta 7 seq17 u : ℚ) ≠ twoDescDisplayJ 7 3 6 2 4 u := by
  intro u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  · rw [show DeltaAlt 7 seq17 0 = 1112 by decide, show Delta 7 seq17 0 = 3336 by decide]
    norm_num [twoDescDisplayI, twoDescDisplayJ]
  · rw [show DeltaAlt 7 seq17 1 = 1668 by decide, show Delta 7 seq17 1 = 5004 by decide]
    norm_num [twoDescDisplayI, twoDescDisplayJ]
  · rw [show DeltaAlt 7 seq17 2 = 2502 by decide, show Delta 7 seq17 2 = 7506 by decide]
    norm_num [twoDescDisplayI, twoDescDisplayJ]
  · rw [show DeltaAlt 7 seq17 4 = 2780 by decide, show Delta 7 seq17 4 = 8340 by decide]
    norm_num [twoDescDisplayI, twoDescDisplayJ]
  · rw [show DeltaAlt 7 seq17 5 = 4170 by decide, show Delta 7 seq17 5 = 12510 by decide]
    norm_num [twoDescDisplayI, twoDescDisplayJ]

/-- The right-shape positions: `display(u) = 2Δ'_u` at `−17`, for `u ∈ {0, 1, 2}` (l.310) and
`u ∈ {4, 5}` (l.313). -/
theorem twoDesc_displays_twice_seq17 :
    (∀ u : ℤ, u ∈ ({0, 1, 2} : Finset ℤ) →
      twoDescDisplayI 7 3 6 2 4 u = 2 * (DeltaAlt 7 seq17 u : ℚ)) ∧
    (∀ u : ℤ, u ∈ ({4, 5} : Finset ℤ) →
      twoDescDisplayJ 7 3 6 2 4 u = 2 * (DeltaAlt 7 seq17 u : ℚ)) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · rw [show DeltaAlt 7 seq17 0 = 1112 by decide]; norm_num [twoDescDisplayI]
    · rw [show DeltaAlt 7 seq17 1 = 1668 by decide]; norm_num [twoDescDisplayI]
    · rw [show DeltaAlt 7 seq17 2 = 2502 by decide]; norm_num [twoDescDisplayI]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · rw [show DeltaAlt 7 seq17 4 = 2780 by decide]; norm_num [twoDescDisplayJ]
    · rw [show DeltaAlt 7 seq17 5 = 4170 by decide]; norm_num [twoDescDisplayJ]

/-- **Finding 5 (l.324, second inequality).** Whenever `3ⁿ < 2^P` (so on every cycle of `x > 0`),
`3^{n/2} 2^{P−n} > 2^{P − (log₃ 2 − 1/2) P}`: the step uses `3ⁿ ≥ 2^P`, the opposite of what
holds on a positive cycle. -/
theorem twoDesc_l324_second_false (P n : ℕ) (h : (3 : ℝ) ^ n < 2 ^ P) :
    (2 : ℝ) ^ ((P : ℝ) - (Real.logb 3 2 - 1 / 2) * P) <
      (3 : ℝ) ^ ((n : ℝ) / 2) * 2 ^ ((P : ℝ) - n) := by
  set L := Real.logb 2 3 with hLdef
  have hL0 : 0 < L := Real.logb_pos (by norm_num) (by norm_num)
  have hL2 : L < 2 := by
    rw [hLdef, Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num), Real.rpow_two]; norm_num
  have hinv : Real.logb 3 2 = L⁻¹ := (Real.inv_logb 2 3).symm
  have hnL : (n : ℝ) * L < P := by
    have h' := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) h
    rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h'
  have h3 : (3 : ℝ) ^ ((n : ℝ) / 2) = 2 ^ (L * ((n : ℝ) / 2)) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  rw [h3, ← Real.rpow_add (by norm_num), Real.rpow_lt_rpow_left_iff (by norm_num), hinv]
  have key : (P : ℝ) - (L⁻¹ - 1 / 2) * P - (L * ((n : ℝ) / 2) + (P - n)) =
      -(L⁻¹ * ((1 - L / 2) * (P - n * L))) := by
    field_simp
    ring
  have hpos : 0 < L⁻¹ * ((1 - L / 2) * (P - n * L)) := by
    apply mul_pos (inv_pos.2 hL0)
    apply mul_pos <;> linarith
  linarith

/-- **Finding 5 (l.324, second inequality), as printed**: whenever `3ⁿ < 2^P`, so on every cycle
of `x > 0`, `3^{n/2} 2^{P−n} + 2^{P−n} 2^{n/2} ≤ 2^{P − (log₃ 2 − 1/2) P}` is false. -/
theorem twoDesc_l324_second_printed_false (P n : ℕ) (h : (3 : ℝ) ^ n < 2 ^ P) :
    ¬ (3 : ℝ) ^ ((n : ℝ) / 2) * 2 ^ ((P : ℝ) - n) + 2 ^ ((P : ℝ) - n) * 2 ^ ((n : ℝ) / 2) ≤
      (2 : ℝ) ^ ((P : ℝ) - (Real.logb 3 2 - 1 / 2) * P) := by
  intro hle
  have h1 := twoDesc_l324_second_false P n h
  have h2 : (0 : ℝ) < 2 ^ ((P : ℝ) - n) * 2 ^ ((n : ℝ) / 2) := by positivity
  linarith

/-- **Finding 5 (l.324, first inequality, read literally on `Δ_j`).** At `−17`
(`n = 7`, `|Γ| = 11`), every ascending `u` has `Δ'_u ≥ 1112 > 3^{7/2} 2⁴ + 2⁴ 2^{7/2}`: the bound
holds for the S-free part `E` (`twoDesc_bound_rpow`), not for `Δ_j` itself. -/
theorem twoDesc_l324_first_literal_false :
    ∀ u : ℤ, u ∈ ({0, 1, 2, 4, 5} : Finset ℤ) →
      (3 : ℝ) ^ ((7 : ℝ) / 2) * 2 ^ ((11 : ℝ) - 7) + 2 ^ ((11 : ℝ) - 7) * 2 ^ ((7 : ℝ) / 2) <
        (DeltaAlt 7 seq17 u : ℝ) := by
  have h16 : (2 : ℝ) ^ ((11 : ℝ) - 7) = 16 := by
    rw [show (11 : ℝ) - 7 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h3 : (3 : ℝ) ^ ((7 : ℝ) / 2) < 49 := by
    have hsq : ((3 : ℝ) ^ ((7 : ℝ) / 2)) ^ 2 = 3 ^ 7 := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ ((7 : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num),
        show (7 : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ ((7 : ℝ) / 2) := by positivity
    nlinarith
  have h2 : (2 : ℝ) ^ ((7 : ℝ) / 2) < 12 := by
    have hsq : ((2 : ℝ) ^ ((7 : ℝ) / 2)) ^ 2 = 2 ^ 7 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((7 : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num),
        show (7 : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ ((7 : ℝ) / 2) := by positivity
    nlinarith
  intro u hu
  have hv : (1112 : ℤ) ≤ DeltaAlt 7 seq17 u := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide
  have hv' : (1112 : ℝ) ≤ (DeltaAlt 7 seq17 u : ℝ) := by exact_mod_cast hv
  rw [h16]
  linarith

/-! ### Non-vacuity: the cycle of `−17` -/

/-- The forms above at `−17`: `i = 4`, `j = 0`, `Δ'_4 = 2² · 695`, `Δ'_0 = 2³ · 139`; the key
identity `A'_7 + (2^{11} − 3⁷) = 2⁴ · 139`; `|2^{11} − 3⁷| = 139 ≤ 139, 695`. -/
theorem twoDesc_nonvacuous_seq17 :
    (DeltaAlt 7 seq17 4 : ℚ) = (3 : ℚ) ^ ((4 : ℤ) - 3 - 1) * 2 ^ ((6 : ℤ) - 4) * twoDescE 4 3 1 ∧
    (DeltaAlt 7 seq17 0 : ℚ) =
      (3 : ℚ) ^ ((0 : ℤ) + 7 - 6 - 1) * 2 ^ ((3 : ℤ) - 0) * twoDescE 3 1 3 ∧
    (AunAlt 7 (6 + 1) seq17 : ℤ) + (2 ^ (∑ t ∈ range 7, seq17 t) - 3 ^ 7) = 2 ^ 4 * twoDescE 3 1 3 ∧
    |(2 : ℤ) ^ p 7 (-17 : ℤ) - 3 ^ 7| ≤ twoDescE 3 1 3 ∧
    |(2 : ℤ) ^ p 7 (-17 : ℤ) - 3 ^ 7| ≤ twoDescE 4 3 1 := by
  have hpos : ∀ i, 1 ≤ seq17 i := fun i => by unfold seq17; split_ifs <;> norm_num
  obtain ⟨hC, h3, h6, -, -, -, -⟩ := twoDesc_values_seq17
  obtain ⟨hx, hα⟩ := cycle_neg_seventeen
  have hi := twoDesc_delta_i seq17_periodic hpos (k₁ := 3) (k₂ := 6) (by norm_num) (by norm_num)
    (by norm_num) hC (δ₁ := 3) (δ₂ := 4) (by norm_num) (by norm_num) (i := 4) (by norm_num)
    (by norm_num)
  have hj := twoDesc_delta_j seq17_periodic hpos (k₁ := 3) (k₂ := 6) (by norm_num) (by norm_num)
    (by norm_num) hC (δ₁ := 3) (δ₂ := 4) (by norm_num) (by norm_num) (j := 0) (by norm_num)
    (by norm_num)
  have hk := twoDesc_key_classes seq17_periodic hpos (k₁ := 3) (k₂ := 6) (by norm_num)
    (by norm_num) (by norm_num) hC (δ₁ := 3) (δ₂ := 4) (by norm_num) (by norm_num)
  have ha := twoDesc_abs_le (by norm_num) hx seq17_periodic hα (k₁ := 3) (k₂ := 6) (by norm_num)
    (by norm_num) (by norm_num) hC (δ₁ := 3) (δ₂ := 4) (by norm_num) (by norm_num)
  rw [h3, h6] at hi hj hk ha
  exact ⟨hi.2.1, hj.2.1, hk.2.1, ha.2.2.1, ha.2.2.2⟩

end Syracuse
