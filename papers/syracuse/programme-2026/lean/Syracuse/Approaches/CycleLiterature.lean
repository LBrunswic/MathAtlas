import Syracuse.Basic

/-!
# What is known about 3x+1 cycles (`approaches/cycle-literature`)

A Lean companion to `approaches/cycle-literature/SURVEY.md`. Two kinds of content:

* **Elementary literature results, proved here** from `Syracuse.Basic`: Böhm–Sontacchi (closed
  form, the divisibility *equivalence*, `D` odd and prime to `6`, `|a| < 3^E`), the Crandall–Eliahou
  loop product, both edges of the ratio sandwich (Sinisalo 2003 Lemma 1 and the AM–GM inequality
  in the proof of Hercher 2023 Thm. 16), `E ≤ 2o` and finitely many cycles of each period, the period-1
  classification, the negative cycles `-1`, `-5`, `-17`, the link from verification ranges to `N₀`,
  and the reduction of the positive cycle problem to `m`-cycles.
* **Deep literature results, only stated** as `def … : Prop` (Steiner, Simons, Simons–de Weger,
  Hercher, Rhin via Simons–de Weger Lemma 12, Ellison, Eliahou, Barina, Terras). They are neither
  proved nor assumed; they appear only as explicit hypotheses of short conditional theorems.

Dictionary: the literature's map is `T(n) = n/2, (3n+1)/2`; a cycle with `K` odd and `L` even
elements has `K = o` and `K + L = E` (`= w.sum`) in gap-word notation. `m` = number of local
minima = number of gaps `≥ 2` (`numBlocks`). "Nontrivial positive" = `0 < a`, `a ≠ 1`.

## Ledger (mirrors SURVEY.md §5)

| Survey item | Lean | Status |
|---|---|---|
| B–S closed form, `a = S/D` determined by word | `cycle_eq_S_div_D`, `cycle_eq_of_gapWord_eq` | proved |
| B–S divisibility `D ∣ S` and converse | `cycle_D_dvd_S`, `isSyrCycle_of_dvd`, `exists_cycle_iff_dvd` | proved |
| weak Collatz ⇔ no divisibility witness (Tao Conj. 3) | `noNontrivialPositiveCycle_iff_dvd` | proved |
| B–S `abs a < 3^E` | `cycle_abs_lt` | proved |
| `D` odd, `gcd(D, 6) = 1` | `cycle_D_odd_coprime`, `Dz_odd`, `isCoprime_Dz_six` | proved |
| loop product `2^E/3^o = ∏(1 + 1/(3a_k))` | `cycle_ratio_eq_prod`, `cycle_two_pow_eq_prod` | proved |
| left edge `log₂ 3 < E/o` | `cycle_three_pow_lt`, `cycle_logb_lt` | proved |
| right edge `E/o ≤ log₂(3 + 1/m)` (Sinisalo L. 1) | `cycle_two_pow_le`, `cycle_ratio_le_logb` | proved |
| `0 < E - o log₂ 3 < o/(3m ln 2)` | `cycle_excess_le` | proved |
| `2^E ≤ (3 + μ)^o` (Hercher Thm. 16 proof) | `cycle_two_pow_le_amgm` | proved (Thm. 16 itself: not formalized) |
| finitely many cycles per period | `finite_cycles`, `cycle_sum_le`, `cycle_abs_lt_nine_pow` | proved |
| only trivial cycle of period 1 | `period_one_pos`, `isSyrCycle_period_one_iff` | proved |
| `3x-1` cycles `-1`, `-5`, `-17` exist | `isSyrCycle_neg_one`, `isSyrCycle_neg_five`, `isSyrCycle_neg_seventeen` | proved |
| verification `N` ⇒ cycle elements `> N` | `cycle_gt_of_verifiedUpTo` | proved |
| smallest element `≥ 2^71`; sandwich at `2^71` | `Barina2025`; `barina_cycle_ge`, `barina_sandwich` | stated; conditional proved |
| Steiner: no nontrivial circuit | `Steiner1977`, `Steiner1977Dioph` | stated |
| Simons: no 2-cycle | `Simons2005` | stated |
| S–dW `m ≤ 68` (2005) / `m ≤ 75` (2010) | `SimonsDeWeger2005`, `SimonsDeWeger2010` | stated |
| Hercher `m ≤ 91` | `Hercher2023`; `hercher_chain`, `steiner_simons_of_sdw` | stated; nesting proved |
| Eliahou period form | `Eliahou1993`; `eliahou_of_barina` | stated; conditional proved |
| `K > 1.375·10^11` odd elements | `Hercher2023Cor29`; `hercher_odd_steps_of_barina` | stated; conditional proved |
| Baker/Rhin lower bound | `SimonsDeWegerLemma12`; `Dz_ge`, `sdw12_Dz_gt` | stated; consequence proved |
| Ellison `abs (2^x - 3^y) > 2^x e^{-x/10}` | `Ellison1971`; `ellison_cycle_lt` | stated; consequence proved |
| Terras/Lagarias 2-adic bijection | `Terras1976` | stated (elementary, not formalized) |
| **open:** no nontrivial cycle | `NoNontrivialPositiveCycle`; `noNontrivialPositiveCycle_iff`, `…_of_collatzConjecture`, `…_of_hercher` | open; reductions proved |
| **open:** finitely many cycles in total | `FinitelyManyPositiveCyclePoints`; `finitelyMany_of_noNontrivial` | open |
| **open:** exclusion of `m ≥ 92` | `NoMCyclesFrom 92` | open |
| **open:** only three negative cycles | `OnlyKnownNegativeCycles` | open |

## Corrections to the survey (checked against primary sources, 2026-10-29)

* **Rhin constant.** Simons–de Weger 2005 Lemma 12 reads `Λ > exp(-13.3 (0.46057 + log K))`. The
  `0.46057 ≈ log log₂ 3` is *inside* the exponent; it is not a multiplicative `C ≈ 0.46`. The
  multiplicative constant is `e^{-6.126} ≈ 0.00219`. The "`Λ < 2^{-0.158 o}` for `o ≥ 32`" claim is
  in neither the published version nor v1.44, so it is unverified.
* **Barina.** The 2021 paper verifies `n < 2^68`, not `1.5 · 2^70`. The 2025 bound is strict
  (`n < 2^71`).
* **Hercher Thm. 16** is `δ < (K+L)/K < δ + Σ T(n_i)/(3K log 2)`, not "verbatim" the
  `log₂(3 + 1/n_min)` form, which is Sinisalo's Lemma 1. Hercher's `X₀` is `695 · 2^60` (JIS) vs
  `704 · 2^60` (arXiv v3).
* **Simons–de Weger.** The published paper (`X₀ = 301 · 2^50`) excludes `m ≤ 68`; v1.44 (2010,
  `X₀ = 5 · 2^60`) excludes `m ≤ 75`. EXCLUDED_PATTERNS' "`m ≤ 74`" (v1.41, via Lagarias) disagrees.
* **"cycle iff `D ∣ S` with quotient > 1".** The precise statement needs a positive word. `D ∣ S`
  alone already gives a cycle with exactly that gap word (positive iff `D > 0`), and "> 1" is
  nontriviality. `D` odd needs `E ≥ 1`; `3 ∤ D` needs `o ≥ 1`.
* **"`3x-1` has three nontrivial cycles"**: existence is proved here. That there are *exactly* three
  is open.
* **Band width "∼10^{-21}"**: `1/(3 · 2^71 · ln 2) ≈ 2.0 · 10^{-22}` per odd step.
* **Eliahou** counts `T`-elements `K + L = E` of a cycle with minimum `> 2^40`.
* **Ellison's bound** is Thm. 3 of exposé 12, "On a theorem of S. Sivasankaranarayana Pillai". It is
  not in "Recipes…", and it has the exceptional set `{1,…,11, 13, 14, 16, 19, 27}`.
-/

namespace Syracuse.CycleLiterature

open Syracuse Finset

/-- Computing one Syracuse step: if `3a + 1 = 2^k m` with `m` odd, then `gap a = k` and
`syr a = m`. -/
theorem gap_syr_of_eq {a m : ℤ} {k : ℕ} (h : 3 * a + 1 = 2 ^ k * m) (hm : Odd m) :
    gap a = k ∧ syr a = m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  have hg : gap a = k := by
    have h1 : padicValInt 2 ((2 : ℤ) ^ k) = k := by
      rw [show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl, padicValInt.of_nat,
        padicValNat.prime_pow]
    have h2 : padicValInt 2 m = 0 := by
      refine padicValInt.eq_zero_of_not_dvd ?_
      rw [Nat.cast_ofNat, ← even_iff_two_dvd, Int.not_even_iff_odd]
      exact hm
    rw [gap, h, padicValInt.mul (pow_ne_zero _ two_ne_zero) hm0, h1, h2, add_zero]
  refine ⟨hg, ?_⟩
  have := two_pow_gap_mul_syr a
  rw [hg, h] at this
  exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) this

/-- `syr` preserves positivity. -/
theorem syr_pos {a : ℤ} (ha : 0 < a) : 0 < syr a := by
  have h := two_pow_gap_mul_syr a
  exact pos_of_mul_pos_right (by rw [h]; omega) (by positivity)

/-- Iterates of `syr` preserve positivity. -/
theorem syr_iterate_pos {a : ℤ} (ha : 0 < a) (k : ℕ) : 0 < syr^[k] a := by
  induction k with
  | zero => exact ha
  | succ k ih => rw [Function.iterate_succ_apply']; exact syr_pos ih

/-- Odd integers are nonzero. -/
lemma ne_zero_of_odd {a : ℤ} (ha : Odd a) : a ≠ 0 := by rintro rfl; exact absurd ha (by decide)

/-- Every element `syr^[k] a` of an orbit started at an odd integer is odd. -/
theorem syr_iterate_odd {a : ℤ} (ha : Odd a) (k : ℕ) : Odd (syr^[k] a) := by
  cases k with
  | zero => exact ha
  | succ k => rw [Function.iterate_succ_apply']; exact syr_odd _

/-- **Integer loop product.** Along any orbit, `2^E ∏_{k<o} a_{k+1} = ∏_{k<o} (3 a_k + 1)`, where
`a_k = syr^[k] a` and `E` is the sum of the gap word. -/
theorem two_pow_mul_prod_succ (a : ℤ) (o : ℕ) :
    2 ^ (gapWord a o).sum * ∏ k ∈ range o, syr^[k + 1] a =
      ∏ k ∈ range o, (3 * syr^[k] a + 1) := by
  induction o generalizing a with
  | zero => simp [gapWord]
  | succ o ih =>
    have := ih (syr a)
    rw [prod_range_succ', prod_range_succ']
    simp only [gapWord, List.sum_cons, pow_add, Function.iterate_succ_apply,
      Function.iterate_zero_apply] at this ⊢
    rw [← this, ← two_pow_gap_mul_syr a]
    ring

/-- On a cycle the shifted product `∏_{k<o} a_{k+1}` equals `∏_{k<o} a_k`. -/
theorem cycle_prod_succ {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    ∏ k ∈ range o, syr^[k + 1] a = ∏ k ∈ range o, syr^[k] a := by
  have h1 := prod_range_succ' (fun k => syr^[k] a) o
  rw [prod_range_succ, h.2.2, Function.iterate_zero_apply] at h1
  exact (mul_right_cancel₀ (ne_zero_of_odd h.2.1) h1).symm

/-- **Loop product on a cycle** (integer form): `2^E ∏ a_k = ∏ (3 a_k + 1)`. -/
theorem cycle_loop_product {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    2 ^ (gapWord a o).sum * ∏ k ∈ range o, syr^[k] a = ∏ k ∈ range o, (3 * syr^[k] a + 1) := by
  rw [← cycle_prod_succ h]; exact two_pow_mul_prod_succ a o

/-- **Crandall–Eliahou loop product.** On any cycle (positive or negative),
`2^E / 3^o = ∏_{k<o} (1 + 1/(3 a_k))`. -/
theorem cycle_ratio_eq_prod {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    (2 : ℝ) ^ (gapWord a o).sum / 3 ^ o = ∏ k ∈ range o, (1 + 1 / (3 * (syr^[k] a : ℝ))) := by
  have hne : ∀ k, (syr^[k] a : ℝ) ≠ 0 := fun k => by
    exact_mod_cast ne_zero_of_odd (syr_iterate_odd h.2.1 k)
  have hP : (∏ k ∈ range o, (syr^[k] a : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun k _ => hne k
  have hl : (2 : ℝ) ^ (gapWord a o).sum * ∏ k ∈ range o, (syr^[k] a : ℝ) =
      ∏ k ∈ range o, (3 * (syr^[k] a : ℝ) + 1) := by exact_mod_cast cycle_loop_product h
  have hf : ∀ k ∈ range o, 1 + 1 / (3 * (syr^[k] a : ℝ)) = (3 * syr^[k] a + 1) / (3 * syr^[k] a) :=
    fun k _ => by field_simp [hne k]
  rw [prod_congr rfl hf, prod_div_distrib, prod_mul_distrib, prod_const, card_range, ← hl]
  field_simp


/-! ## Böhm–Sontacchi -/

/-- `S(w) ≥ 0` at `(2, 3)`. -/
theorem Sz_nonneg (w : Word) : 0 ≤ Sz w := by
  induction w with
  | nil => simp [Sz]
  | cons d w ih => simp only [Sz, S_cons] at ih ⊢; positivity

/-- `S(w) > 0` at `(2, 3)` for a nonempty word. -/
theorem Sz_pos {w : Word} (hw : w ≠ []) : 0 < Sz w := by
  obtain ⟨d, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  have := Sz_nonneg w
  simp only [Sz, S_cons] at this ⊢
  positivity

/-- The total number of halvings is at least the number of odd steps on a positive word. -/
theorem length_le_sum {w : Word} (hw : w.Pos) : w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd := hw d List.mem_cons_self
    have := ih fun x hx => hw x (List.mem_cons_of_mem d hx)
    simp only [List.length_cons, List.sum_cons]; omega

/-- **Böhm–Sontacchi (divisibility).** On a cycle, `D = 2^E - 3^o` divides `S`. -/
theorem cycle_D_dvd_S {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : Dz (gapWord a o) ∣ Sz (gapWord a o) :=
  ⟨a, by rw [← h.cycle_equation, mul_comm]⟩

/-- `D(w) = 2^E - 3^o` is odd as soon as `E ≥ 1`. -/
theorem Dz_odd {w : Word} (hE : 1 ≤ w.sum) : Odd (Dz w) :=
  Even.sub_odd (even_two.pow_of_ne_zero (by omega)) (by decide : Odd (3 : ℤ)).pow

/-- `3 ∤ D(w)` as soon as `o ≥ 1`. -/
theorem three_not_dvd_Dz {w : Word} (ho : 1 ≤ w.length) : ¬ (3 : ℤ) ∣ Dz w := by
  intro h3
  have h : (3 : ℤ) ∣ 2 ^ w.sum := by
    have : (3 : ℤ) ∣ 3 ^ w.length := dvd_pow_self 3 (by omega)
    simpa [Dz, D] using dvd_add h3 this
  exact absurd (Int.prime_three.dvd_of_dvd_pow h) (by decide)

/-- **`gcd(D, 6) = 1`** for every word with `E ≥ 1`, `o ≥ 1`. -/
theorem isCoprime_Dz_six {w : Word} (hE : 1 ≤ w.sum) (ho : 1 ≤ w.length) : IsCoprime (Dz w) 6 := by
  have h2 : IsCoprime (2 : ℤ) (Dz w) := (Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).2
    (by rw [← even_iff_two_dvd, Int.not_even_iff_odd]; exact Dz_odd hE)
  have h3 : IsCoprime (3 : ℤ) (Dz w) :=
    (Irreducible.coprime_iff_not_dvd Int.prime_three.irreducible).2 (three_not_dvd_Dz ho)
  rw [show (6 : ℤ) = 2 * 3 by norm_num]
  exact (h2.mul_left h3).symm

/-- The gap word of a cycle has `E ≥ o ≥ 1`. -/
theorem cycle_one_le_length {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    1 ≤ (gapWord a o).length ∧ (gapWord a o).length ≤ (gapWord a o).sum :=
  ⟨by rw [gapWord_length]; exact h.1, length_le_sum (gapWord_pos h.2.1 o)⟩

/-- **Böhm–Sontacchi.** On a cycle, `D` is odd and coprime to `6` (in particular `D ≠ 0`). -/
theorem cycle_D_odd_coprime {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    Odd (Dz (gapWord a o)) ∧ IsCoprime (Dz (gapWord a o)) 6 := by
  obtain ⟨h1, h2⟩ := cycle_one_le_length h
  exact ⟨Dz_odd (by omega), isCoprime_Dz_six (by omega) h1⟩

/-- On a cycle `D ≠ 0`, so `a = S / D` is determined by the gap word. -/
theorem cycle_Dz_ne_zero {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : Dz (gapWord a o) ≠ 0 :=
  ne_zero_of_odd (cycle_D_odd_coprime h).1

/-- **Böhm–Sontacchi closed form.** `a = S(w) / D(w)` on a cycle. -/
theorem cycle_eq_S_div_D {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    a = Sz (gapWord a o) / Dz (gapWord a o) := by
  rw [← h.cycle_equation, Int.mul_ediv_cancel_left _ (cycle_Dz_ne_zero h)]

/-- **The word determines the cycle point**: two cycle points of period `o` with the same gap word
are equal. -/
theorem cycle_eq_of_gapWord_eq {a b : ℤ} {o : ℕ} (ha : IsSyrCycle a o) (hb : IsSyrCycle b o)
    (hw : gapWord a o = gapWord b o) : a = b := by
  rw [cycle_eq_S_div_D ha, cycle_eq_S_div_D hb, hw]

/-- Positive words satisfy `2^o S(w) + 2^E 2^o ≤ 2^E 3^o`, i.e. `S(w) ≤ 2^{E-o}(3^o - 2^o)`. -/
theorem two_pow_mul_Sz_le {w : Word} (hw : w.Pos) :
    2 ^ w.length * Sz w + 2 ^ w.sum * 2 ^ w.length ≤ 2 ^ w.sum * 3 ^ w.length := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd := hw d List.mem_cons_self
    have hpos : Word.Pos w := fun x hx => hw x (List.mem_cons_of_mem d hx)
    have ih := ih hpos
    have hle : (2 : ℤ) ^ (w.length + 1) ≤ 2 ^ (d + w.sum) :=
      pow_le_pow_right₀ (by norm_num) (by have := length_le_sum hpos; omega)
    simp only [Sz, S_cons, List.length_cons, List.sum_cons] at ih ⊢
    have h3 : (0 : ℤ) ≤ 3 ^ w.length := by positivity
    have h2d : (2 : ℤ) ^ d = 2 * 2 ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    calc (2 : ℤ) ^ (w.length + 1) * (3 ^ w.length + 2 ^ d * S 2 3 w) +
          2 ^ (d + w.sum) * 2 ^ (w.length + 1)
        = 2 ^ (w.length + 1) * 3 ^ w.length +
          2 * 2 ^ d * (2 ^ w.length * S 2 3 w + 2 ^ w.sum * 2 ^ w.length) := by ring
      _ ≤ 2 ^ (d + w.sum) * 3 ^ w.length + 2 * 2 ^ d * (2 ^ w.sum * 3 ^ w.length) := by
          gcongr
      _ = 2 ^ (d + w.sum) * 3 ^ (w.length + 1) := by ring

/-- Word-level size bound: a solution of `D(w) a = S(w)` with `D(w) ≠ 0` and `w` positive satisfies
`|a| < 3^E`. -/
theorem abs_lt_of_cycle_equation {w : Word} {a : ℤ} (hw : w.Pos) (hD : Dz w ≠ 0)
    (h : Dz w * a = Sz w) : |a| < 3 ^ w.sum := by
  have hS := two_pow_mul_Sz_le hw
  have hlE := length_le_sum hw
  have haS : |a| ≤ Sz w := by
    have e : |Dz w| * |a| = Sz w := by rw [← abs_mul, h, abs_of_nonneg (Sz_nonneg _)]
    nlinarith [abs_nonneg a, Int.one_le_abs hD]
  obtain ⟨t, ht⟩ : ∃ t, w.sum = w.length + t := ⟨w.sum - w.length, by omega⟩
  have h23 : (2 : ℤ) ^ t ≤ 3 ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have hpos : (0 : ℤ) < 2 ^ w.length := by positivity
  have : (2 : ℤ) ^ w.length * Sz w < 2 ^ w.length * 3 ^ w.sum := by
    calc (2 : ℤ) ^ w.length * Sz w < 2 ^ w.sum * 3 ^ w.length := by
          have : (0 : ℤ) < 2 ^ w.sum * 2 ^ w.length := by positivity
          linarith
      _ = 2 ^ w.length * (2 ^ t * 3 ^ w.length) := by rw [ht, pow_add]; ring
      _ ≤ 2 ^ w.length * (3 ^ t * 3 ^ w.length) := by gcongr
      _ = 2 ^ w.length * 3 ^ w.sum := by rw [ht, pow_add]; ring
  exact lt_of_le_of_lt haS (lt_of_mul_lt_mul_left this hpos.le)

/-- **Böhm–Sontacchi size bound.** Every element of a cycle (positive or negative) satisfies
`|a| < 3^E`, where `E` is the cycle's total number of halvings (= its length for the map
`T(n) = n/2, (3n+1)/2`). -/
theorem cycle_abs_lt {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : |a| < 3 ^ (gapWord a o).sum :=
  abs_lt_of_cycle_equation (gapWord_pos h.2.1 o) (cycle_Dz_ne_zero h) h.cycle_equation

/-! ## The ratio sandwich `log₂ 3 < E/o ≤ log₂(3 + 1/m)` -/

/-- The gap word of a cycle is nonempty. -/
lemma cycle_gapWord_ne_nil {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : gapWord a o ≠ [] :=
  List.ne_nil_of_length_pos (by rw [gapWord_length]; exact h.1)

/-- On a positive cycle `D > 0`. -/
theorem cycle_Dz_pos {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) : 0 < Dz (gapWord a o) := by
  have hS := Sz_pos (cycle_gapWord_ne_nil h)
  rw [← h.cycle_equation] at hS
  exact pos_of_mul_pos_left hS ha.le

/-- On a negative cycle `D < 0`. -/
theorem cycle_Dz_neg {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : a < 0) : Dz (gapWord a o) < 0 := by
  have hS := Sz_pos (cycle_gapWord_ne_nil h)
  rw [← h.cycle_equation] at hS
  by_contra hD
  nlinarith [not_lt.1 hD]

/-- **Left edge of the sandwich (integer form).** A positive cycle has `3^o < 2^E`. -/
theorem cycle_three_pow_lt {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    3 ^ o < 2 ^ (gapWord a o).sum := by
  have := cycle_Dz_pos h ha
  simp only [Dz, D, gapWord_length] at this
  exact_mod_cast (sub_pos.1 this)

/-- A negative cycle has `2^E < 3^o`. -/
theorem cycle_two_pow_lt_of_neg {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : a < 0) :
    2 ^ (gapWord a o).sum < 3 ^ o := by
  have := cycle_Dz_neg h ha
  simp only [Dz, D, gapWord_length] at this
  exact_mod_cast (sub_neg.1 this)

/-- **Left edge of the sandwich.** A positive cycle has `log₂ 3 < E/o`. -/
theorem cycle_logb_lt {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    Real.logb 2 3 < ((gapWord a o).sum : ℝ) / o := by
  have h1 : (3 : ℝ) ^ o < 2 ^ (gapWord a o).sum := by exact_mod_cast cycle_three_pow_lt h ha
  have ho : (0 : ℝ) < o := by exact_mod_cast h.1
  rw [Real.logb, div_lt_div_iff₀ (Real.log_pos one_lt_two) ho]
  have := Real.log_lt_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at this
  linarith

/-- **Upper edge of the sandwich (power form).** If every element of the cycle is at least
`m > 0`, then `2^E ≤ (3 + 1/m)^o`. -/
theorem cycle_two_pow_le {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ k < o, m ≤ syr^[k] a) : (2 : ℝ) ^ (gapWord a o).sum ≤ (3 + 1 / m) ^ o := by
  have hpos : ∀ k ∈ range o, (0 : ℝ) < syr^[k] a :=
    fun k hk => lt_of_lt_of_le hm (hmin k (mem_range.1 hk))
  have hP : 0 < ∏ k ∈ range o, (syr^[k] a : ℝ) := prod_pos hpos
  have hl : (2 : ℝ) ^ (gapWord a o).sum * ∏ k ∈ range o, (syr^[k] a : ℝ) =
      ∏ k ∈ range o, (3 * (syr^[k] a : ℝ) + 1) := by exact_mod_cast cycle_loop_product h
  have hle : ∏ k ∈ range o, (3 * (syr^[k] a : ℝ) + 1) ≤ ∏ k ∈ range o, ((3 + 1 / m) * syr^[k] a) := by
    refine prod_le_prod₀ (fun k hk => by have := hpos k hk; positivity) (fun k hk => ?_)
    have h1 : 1 ≤ (syr^[k] a : ℝ) / m := (one_le_div hm).2 (hmin k (mem_range.1 hk))
    have : (3 + 1 / m) * (syr^[k] a : ℝ) = 3 * syr^[k] a + syr^[k] a / m := by ring
    linarith
  rw [prod_mul_distrib, prod_const, card_range, ← hl] at hle
  exact le_of_mul_le_mul_right hle hP

/-- **Upper edge of the sandwich** (Sinisalo 2003 Lemma 1; Hercher 2023 Thm. 16): if every element of
a cycle is at least `m > 0`, then `E/o ≤ log₂(3 + 1/m)`. With `m` the smallest element this is the
sharp form. -/
theorem cycle_ratio_le_logb {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ k < o, m ≤ syr^[k] a) :
    ((gapWord a o).sum : ℝ) / o ≤ Real.logb 2 (3 + 1 / m) := by
  have h1 := cycle_two_pow_le h hm hmin
  have ho : (0 : ℝ) < o := by exact_mod_cast h.1
  rw [Real.logb, div_le_div_iff₀ ho (Real.log_pos one_lt_two)]
  have := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at this
  linarith

/-- **Linearised sandwich**: `0 < E - o log₂ 3 < o / (3 m ln 2)` when every element is `≥ m > 0`. -/
theorem cycle_excess_le {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ k < o, m ≤ syr^[k] a) :
    0 < ((gapWord a o).sum : ℝ) - o * Real.logb 2 3 ∧
      ((gapWord a o).sum : ℝ) - o * Real.logb 2 3 < o / (3 * m * Real.log 2) := by
  have ho : (0 : ℝ) < o := by exact_mod_cast h.1
  have ha : 0 < a := by
    have := hmin 0 h.1; simp only [Function.iterate_zero_apply] at this; exact_mod_cast hm.trans_le this
  have hl2 := Real.log_pos one_lt_two
  refine ⟨?_, ?_⟩
  · have := cycle_logb_lt h ha
    rw [lt_div_iff₀ ho] at this; linarith
  · have h1 := cycle_two_pow_le h hm hmin
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_pow] at h2
    have h3 : Real.log (3 + 1 / m) < Real.log 3 + 1 / (3 * m) := by
      rw [show (3 : ℝ) + 1 / m = 3 * (1 + 1 / (3 * m)) by field_simp,
        Real.log_mul (by norm_num) (by positivity)]
      have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (3 * m) by positivity)
        (by have : 0 < 1 / (3 * m) := by positivity
            linarith)
      linarith
    have h4 : (o : ℝ) * Real.log (3 + 1 / m) < o * Real.log 3 + o / (3 * m) := by
      have := mul_lt_mul_of_pos_left h3 ho
      rw [mul_add, mul_one_div] at this; exact this
    have e1 : ((gapWord a o).sum : ℝ) - o * Real.logb 2 3 =
        (((gapWord a o).sum : ℝ) * Real.log 2 - o * Real.log 3) / Real.log 2 := by
      rw [Real.logb]; field_simp
    have e2 : (o : ℝ) / (3 * m * Real.log 2) = (o / (3 * m)) / Real.log 2 := by
      rw [div_div, mul_assoc]
    rw [e1, e2]
    exact (div_lt_div_iff_of_pos_right hl2).2 (by linarith)

/-- **`2^E ≤ 4^o`**, i.e. `E ≤ 2o`, on every cycle (positive: `2^E ≤ (3 + 1)^o`; negative:
`2^E < 3^o`). -/
theorem cycle_sum_le {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : (gapWord a o).sum ≤ 2 * o := by
  have key : 2 ^ (gapWord a o).sum ≤ 2 ^ (2 * o) := by
    rw [pow_mul, show 2 ^ 2 = 4 by norm_num]
    rcases lt_or_gt_of_ne (ne_zero_of_odd h.2.1) with ha | ha
    · exact (cycle_two_pow_lt_of_neg h ha).le.trans (Nat.pow_le_pow_left (by norm_num) _)
    · have := cycle_two_pow_le h one_pos fun k _ => by
        have := syr_iterate_pos ha k; exact_mod_cast this
      norm_num at this
      exact_mod_cast this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 key

/-! ## Finitely many cycles of each period -/

/-- Every cycle point of period `o` satisfies `|a| < 9^o`. -/
theorem cycle_abs_lt_nine_pow {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : |a| < 9 ^ o := by
  calc |a| < 3 ^ (gapWord a o).sum := cycle_abs_lt h
    _ ≤ 3 ^ (2 * o) := pow_le_pow_right₀ (by norm_num) (cycle_sum_le h)
    _ = 9 ^ o := by rw [pow_mul]; norm_num

/-- **Finitely many cycles of each period** (Böhm–Sontacchi 1978): for each `o` the set of cycle
points of period `o` in `ℤ` (positive or negative) is finite. -/
theorem finite_cycles (o : ℕ) : {a : ℤ | IsSyrCycle a o}.Finite :=
  (Set.finite_Icc (-9 ^ o) (9 ^ o)).subset fun a ha => by
    have := abs_lt.1 (cycle_abs_lt_nine_pow ha)
    exact ⟨by linarith, by linarith⟩

/-! ## Period one (Steiner-type base case) and the negative cycles -/

/-- The gap of `1` is `2` (`3·1 + 1 = 2^2`). -/
lemma gap_syr_one : gap 1 = 2 ∧ syr 1 = 1 := gap_syr_of_eq (k := 2) (by norm_num) (by decide)

/-- `-1 → -1` (`3·(-1) + 1 = 2·(-1)`). -/
lemma gap_syr_neg_one : gap (-1) = 1 ∧ syr (-1) = -1 := gap_syr_of_eq (k := 1) (by norm_num) (by decide)

/-- The cycle `-1 → -1`, gap word `(1)`: `D = -1`, `S = 1`. -/
theorem isSyrCycle_neg_one : IsSyrCycle (-1) 1 ∧ gapWord (-1) 1 = [1] := by
  refine ⟨⟨Nat.one_pos, by decide, ?_⟩, ?_⟩
  · simp [gap_syr_neg_one.2]
  · simp [gapWord, gap_syr_neg_one.1]

/-- **Cycles of period one.** The only integer cycle points of period `1` are `1` (gap word `(2)`)
and `-1` (gap word `(1)`): the cycle equation for a one-letter word `(d)` reads `(2^d - 3) a = 1`. -/
theorem isSyrCycle_period_one_iff {a : ℤ} : IsSyrCycle a 1 ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    have e := h.cycle_equation
    simp only [gapWord, Dz, D, Sz, S_cons, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, S_nil] at e
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' (by simpa using e) with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  · rintro (rfl | rfl)
    exacts [isSyrCycle_one, isSyrCycle_neg_one.1]

/-- **The trivial cycle is the unique positive cycle of period one**, and its gap word is `(2)`. -/
theorem period_one_pos {a : ℤ} (ha : 0 < a) (h : IsSyrCycle a 1) : a = 1 ∧ gapWord a 1 = [2] := by
  rcases isSyrCycle_period_one_iff.1 h with rfl | rfl
  · exact ⟨rfl, by simp [gapWord, gap_syr_one.1]⟩
  · norm_num at ha

/-- The `-5` cycle `-5 → -7 → -5`, gap word `(1, 2)`: `D = 2^3 - 3^2 = -1`, `S = 5`. -/
theorem isSyrCycle_neg_five : IsSyrCycle (-5) 2 ∧ gapWord (-5) 2 = [1, 2] := by
  have h1 : gap (-5) = 1 ∧ syr (-5) = -7 := gap_syr_of_eq (k := 1) (by norm_num) (by decide)
  have h2 : gap (-7) = 2 ∧ syr (-7) = -5 := gap_syr_of_eq (k := 2) (by norm_num) (by decide)
  refine ⟨⟨by norm_num, by decide, ?_⟩, ?_⟩
  · simp [h1.2, h2.2]
  · simp [gapWord, h1, h2]

/-- The `-17` cycle `-17 → -25 → -37 → -55 → -41 → -61 → -91 → -17`, gap word
`(1, 1, 1, 2, 1, 1, 4)`: `E = 11`, `o = 7`, `D = 2^11 - 3^7 = -139`, `S = 2363 = 139 · 17`. -/
theorem isSyrCycle_neg_seventeen :
    IsSyrCycle (-17) 7 ∧ gapWord (-17) 7 = [1, 1, 1, 2, 1, 1, 4] := by
  have h1 : gap (-17) = 1 ∧ syr (-17) = -25 := gap_syr_of_eq (k := 1) (by norm_num) (by decide)
  have h2 : gap (-25) = 1 ∧ syr (-25) = -37 := gap_syr_of_eq (k := 1) (by norm_num) (by decide)
  have h3 : gap (-37) = 1 ∧ syr (-37) = -55 := gap_syr_of_eq (k := 1) (by norm_num) (by decide)
  have h4 : gap (-55) = 2 ∧ syr (-55) = -41 := gap_syr_of_eq (k := 2) (by norm_num) (by decide)
  have h5 : gap (-41) = 1 ∧ syr (-41) = -61 := gap_syr_of_eq (k := 1) (by norm_num) (by decide)
  have h6 : gap (-61) = 1 ∧ syr (-61) = -91 := gap_syr_of_eq (k := 1) (by norm_num) (by decide)
  have h7 : gap (-91) = 4 ∧ syr (-91) = -17 := gap_syr_of_eq (k := 4) (by norm_num) (by decide)
  refine ⟨⟨by norm_num, by decide, ?_⟩, ?_⟩
  · simp [h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2]
  · simp [gapWord, h1, h2, h3, h4, h5, h6, h7]

/-- Sanity check of the cycle equation on the `-17` cycle: `D = -139`, `S = 2363`, `D · (-17) = S`. -/
example : Dz [1, 1, 1, 2, 1, 1, 4] = -139 ∧ Sz [1, 1, 1, 2, 1, 1, 4] = 2363 := by
  simp [Dz, D, Sz, S]

/-! ## From the Collatz map on `ℕ` to cycles of `syr` -/

/-- A cycle point is a cycle point at every later position of its orbit. -/
theorem cycle_iterate {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (k : ℕ) : IsSyrCycle (syr^[k] a) o :=
  ⟨h.1, syr_iterate_odd h.2.1 k, by
    rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h.2.2]⟩

/-- If some point of a cycle is `1`, the cycle is the trivial one. -/
theorem cycle_eq_one_of_iterate_eq_one {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {k : ℕ}
    (hk : syr^[k] a = 1) : a = 1 := by
  have hper : Function.IsPeriodicPt syr (o * k) a := Function.IsPeriodicPt.mul_const h.2.2 k
  have hle : k ≤ o * k := Nat.le_mul_of_pos_left k h.1
  calc a = syr^[o * k] a := hper.eq.symm
    _ = syr^[o * k - k] (syr^[k] a) := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    _ = 1 := by rw [hk]; exact Function.iterate_fixed gap_syr_one.2 _

/-- Invariant: the Collatz orbit of an odd `a > 0` stays inside `{2^j · syr^[k] a}`. -/
theorem collatz_iterate_eq {a : ℤ} (hodd : Odd a) (ha : 0 < a) (i : ℕ) :
    ∃ j k : ℕ, (collatz^[i] a.toNat : ℤ) = 2 ^ j * syr^[k] a := by
  induction i with
  | zero => exact ⟨0, 0, by simp [ha.le]⟩
  | succ i ih =>
    obtain ⟨j, k, hjk⟩ := ih
    rw [Function.iterate_succ_apply']
    generalize collatz^[i] a.toNat = x at hjk
    rcases j with _ | j
    · rw [pow_zero, one_mul] at hjk
      have hx : x % 2 = 1 := Nat.odd_iff.1 (Int.odd_coe_nat x |>.1 (hjk ▸ syr_iterate_odd hodd k))
      refine ⟨gap (syr^[k] a), k + 1, ?_⟩
      rw [collatz, ite_eq_right (by omega), Function.iterate_succ_apply', two_pow_gap_mul_syr]
      push_cast; rw [hjk]
    · have hx : (x : ℤ) = 2 * (2 ^ j * syr^[k] a) := by rw [hjk, pow_succ]; ring
      have hx2 : x % 2 = 0 := by omega
      refine ⟨j, k, ?_⟩
      rw [collatz, ite_eq_left hx2, Int.natCast_ediv, hx, Nat.cast_ofNat,
        Int.mul_ediv_cancel_left _ two_ne_zero]

/-- A positive cycle point whose Collatz orbit reaches `1` is the trivial cycle point `1`. -/
theorem cycle_eq_one_of_reaches_one {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) {i : ℕ}
    (hi : collatz^[i] a.toNat = 1) : a = 1 := by
  obtain ⟨j, k, hjk⟩ := collatz_iterate_eq h.2.1 ha i
  rw [hi, Nat.cast_one] at hjk
  exact cycle_eq_one_of_iterate_eq_one h
    (Int.eq_one_of_mul_eq_one_left (syr_iterate_pos ha k).le hjk.symm)

/-- **Verification up to `N`**: every `n` with `0 < n ≤ N` reaches `1` under the Collatz map. -/
def VerifiedUpTo (N : ℕ) : Prop := ∀ n : ℕ, 0 < n → n ≤ N → ∃ k, collatz^[k] n = 1

/-- **Conditional (verification ⇒ `N₀`).** If the Collatz conjecture is verified up to `N`, every
element of a nontrivial positive cycle exceeds `N`. -/
theorem cycle_gt_of_verifiedUpTo {N : ℕ} (hN : VerifiedUpTo N) {a : ℤ} {o : ℕ}
    (h : IsSyrCycle a o) (ha : 0 < a) (h1 : a ≠ 1) (k : ℕ) : (N : ℤ) < syr^[k] a := by
  have hk := cycle_iterate h k
  have hkpos := syr_iterate_pos ha k
  by_contra hle
  obtain ⟨i, hi⟩ := hN (syr^[k] a).toNat (by omega) (by omega)
  exact h1 (cycle_eq_one_of_iterate_eq_one h (cycle_eq_one_of_reaches_one hk hkpos hi))

/-! ## `m`-cycles (circuits, 2-cycles, …) -/

/-- The number of maximal blocks of odd steps in the cyclic `T`-parity word of a gap word: gap `d`
contributes `1 0^{d-1}`, so a block of `1`s ends exactly at each gap `d ≥ 2`. -/
def numBlocks (w : Word) : ℕ := w.countP fun d => decide (2 ≤ d)

/-- A cycle point of *minimal* period `o`. -/
def IsPrimSyrCycle (a : ℤ) (o : ℕ) : Prop := IsSyrCycle a o ∧ ∀ j, 0 < j → j < o → syr^[j] a ≠ a

/-- `a` lies on a **positive `m`-cycle** (Simons–de Weger 2005, Hercher 2023): a cycle of positive
integers, taken with its minimal period, whose cyclic parity word for `T(n) = n/2, (3n+1)/2` is
`1^{k_1} 0^{l_1} ⋯ 1^{k_m} 0^{l_m}` (`k_i, l_i ≥ 1`), i.e. has exactly `m` local minima. A
*circuit* (Steiner 1977) is a `1`-cycle. -/
def IsMCycle (a : ℤ) (m : ℕ) : Prop :=
  0 < a ∧ ∃ o, IsPrimSyrCycle a o ∧ numBlocks (gapWord a o) = m

/-- No nontrivial positive `m`-cycle for `1 ≤ m ≤ M`. -/
def NoMCyclesUpTo (M : ℕ) : Prop := ∀ a : ℤ, ∀ m : ℕ, 1 ≤ m → m ≤ M → IsMCycle a m → a = 1

/-- `NoMCyclesUpTo` is antitone in `M`. -/
theorem NoMCyclesUpTo.mono {M M' : ℕ} (h : NoMCyclesUpTo M) (hM : M' ≤ M) : NoMCyclesUpTo M' :=
  fun a m h1 hm => h a m h1 (hm.trans hM)

/-- The trivial cycle is a circuit: `1` is a `1`-cycle with gap word `(2)`. -/
theorem isMCycle_one : IsMCycle 1 1 :=
  ⟨one_pos, 1, ⟨isSyrCycle_one, fun j hj hj1 => absurd hj1 (by omega)⟩, by
    rw [(period_one_pos one_pos isSyrCycle_one).2]; rfl⟩

/-- If all gaps are `≤ 1` then `E ≤ o`. -/
lemma sum_le_length_of_le_one {w : Word} (h : ∀ d ∈ w, d ≤ 1) : w.sum ≤ w.length := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have := h d List.mem_cons_self
    have := ih fun x hx => h x (List.mem_cons_of_mem d hx)
    simp only [List.sum_cons, List.length_cons]; omega

/-- A positive cycle has at least one block: some gap is `≥ 2` (otherwise `2^E = 2^o ≤ 3^o`). -/
theorem one_le_numBlocks {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    1 ≤ numBlocks (gapWord a o) := by
  by_contra h0
  have hall : ∀ d ∈ gapWord a o, d ≤ 1 := by
    have := List.countP_eq_zero.1 (show numBlocks (gapWord a o) = 0 by omega)
    intro d hd; have := this d hd; simp at this; omega
  have h1 := cycle_three_pow_lt h ha
  have h2 : 2 ^ (gapWord a o).sum ≤ 2 ^ o := by
    have := sum_le_length_of_le_one hall; rw [gapWord_length] at this
    exact Nat.pow_le_pow_right (by norm_num) this
  have h3 : 2 ^ o ≤ 3 ^ o := Nat.pow_le_pow_left (by norm_num) o
  omega

/-- Every positive cycle point lies on an `m`-cycle for some `m ≥ 1` (its minimal period). -/
theorem exists_isMCycle {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    ∃ m, 1 ≤ m ∧ IsMCycle a m := by
  have hper : Function.IsPeriodicPt syr o a := h.2.2
  set p := Function.minimalPeriod syr a
  have hp : IsSyrCycle a p :=
    ⟨hper.minimalPeriod_pos h.1, h.2.1, Function.isPeriodicPt_minimalPeriod syr a⟩
  refine ⟨numBlocks (gapWord a p), one_le_numBlocks hp ha, ha, p, ⟨hp, fun j hj hjp => ?_⟩, rfl⟩
  exact Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) hjp

/-- **The cycle half of Collatz is exactly the `m`-cycle question**: there is no nontrivial positive
cycle iff for every `M` there is no nontrivial `m`-cycle with `1 ≤ m ≤ M`. -/
theorem noNontrivialPositiveCycle_iff : NoNontrivialPositiveCycle ↔ ∀ M, NoMCyclesUpTo M := by
  constructor
  · rintro H M a m - - ⟨ha, o, ⟨hc, -⟩, -⟩
    exact H a o ha hc
  · intro H a o ha hc
    obtain ⟨m, hm, hmc⟩ := exists_isMCycle hc ha
    exact H m a m hm le_rfl hmc

/-! ## The Böhm–Sontacchi divisibility equivalence -/

/-- `S(w)` is odd for a nonempty positive word. -/
theorem Sz_odd {w : Word} (hw : w.Pos) (hne : w ≠ []) : Odd (Sz w) := by
  obtain ⟨d, w, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hd := hw d List.mem_cons_self
  simp only [Sz, S_cons]
  exact (by decide : Odd (3 : ℤ)).pow.add_even ((even_two.pow_of_ne_zero (by omega)).mul_right _)

/-- One step of the converse: a solution of `D(d :: w) a = S(d :: w)` has `gap a = d`, and `syr a`
solves the cycle equation of the rotated word `w ++ [d]`. -/
theorem step_of_cycle_equation {d : ℕ} {w : Word} {a : ℤ} (hw : Word.Pos (d :: w))
    (h : Dz (d :: w) * a = Sz (d :: w)) : gap a = d ∧ Dz (w ++ [d]) * syr a = Sz (w ++ [d]) := by
  have hpos' : Word.Pos (w ++ [d]) := fun x hx => hw x (by simp at hx ⊢; tauto)
  have hD : Odd (Dz (d :: w)) := Dz_odd (by have := length_le_sum hw; simp at this ⊢; omega)
  have hrot := rotation_recursion (2 : ℤ) 3 d w
  have hDrot : Dz (w ++ [d]) = Dz (d :: w) := by rw [← rotate_one_cons]; exact D_rotate _ _ _ 1
  have hcop : IsCoprime (Dz (d :: w)) (2 ^ d) :=
    ((Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).2
      (by rw [← even_iff_two_dvd, Int.not_even_iff_odd]; exact hD)).symm.pow_right
  obtain ⟨b, hb⟩ : Dz (d :: w) ∣ Sz (w ++ [d]) :=
    hcop.dvd_of_dvd_mul_left ⟨3 * a + 1, by rw [Sz, hrot, ← Sz, ← h]; ring⟩
  have hb' : 2 ^ d * b = 3 * a + 1 := by
    apply mul_left_cancel₀ (ne_zero_of_odd hD)
    calc Dz (d :: w) * (2 ^ d * b) = 2 ^ d * Sz (w ++ [d]) := by rw [hb]; ring
      _ = 3 * Sz (d :: w) + Dz (d :: w) := hrot
      _ = Dz (d :: w) * (3 * a + 1) := by rw [← h]; ring
  have hbodd : Odd b := by
    have hS' := Sz_odd hpos' (by simp)
    rw [hb] at hS'; exact (Int.odd_mul.1 hS').2
  obtain ⟨hg, hs⟩ := gap_syr_of_eq hb'.symm hbodd
  exact ⟨hg, by rw [hs, hDrot, hb]⟩

/-- Running the converse along a prefix `u` of `u ++ v`. -/
theorem gapWord_of_cycle_equation (u : Word) : ∀ (v : Word) (a : ℤ), Word.Pos (u ++ v) →
    Dz (u ++ v) * a = Sz (u ++ v) →
    gapWord a u.length = u ∧ Dz (v ++ u) * syr^[u.length] a = Sz (v ++ u) := by
  induction u with
  | nil => intro v a _ h; simpa [gapWord] using h
  | cons d u ih =>
    intro v a hpos h
    obtain ⟨hg, hs⟩ := step_of_cycle_equation (w := u ++ v) hpos h
    have hpos' : Word.Pos (u ++ (v ++ [d])) := fun x hx => hpos x (by simp at hx ⊢; tauto)
    obtain ⟨h1, h2⟩ := ih (v ++ [d]) (syr a) hpos' (by simpa [List.append_assoc] using hs)
    refine ⟨by simp [gapWord, hg, h1], ?_⟩
    rw [List.length_cons, Function.iterate_succ_apply]
    simpa [List.append_assoc] using h2

/-- **Böhm–Sontacchi criterion (converse).** If a nonempty positive gap word `w` has `D(w) ∣ S(w)`,
then `a = S(w)/D(w)` is a Syracuse cycle point of period `o = len w` with gap word exactly `w`. -/
theorem isSyrCycle_of_dvd {w : Word} (hw : w.Pos) (hne : w ≠ []) (hdvd : Dz w ∣ Sz w) :
    IsSyrCycle (Sz w / Dz w) w.length ∧ gapWord (Sz w / Dz w) w.length = w := by
  obtain ⟨a, ha⟩ := hdvd
  have hD : Dz w ≠ 0 := ne_zero_of_odd (Dz_odd (by
    have := length_le_sum hw; have := List.length_pos_of_ne_nil hne; omega))
  rw [ha, Int.mul_ediv_cancel_left _ hD]
  obtain ⟨h1, h2⟩ := gapWord_of_cycle_equation w [] a (by simpa using hw) (by simpa using ha.symm)
  simp only [List.nil_append] at h2
  refine ⟨⟨List.length_pos_of_ne_nil hne, ?_, mul_left_cancel₀ hD (h2.trans ha)⟩, h1⟩
  have := Sz_odd hw hne
  rw [ha] at this; exact (Int.odd_mul.1 this).2

/-- **Böhm–Sontacchi equivalence.** A nonempty positive gap word `w` is the gap word of a Syracuse
cycle iff `D(w) ∣ S(w)`. -/
theorem exists_cycle_iff_dvd {w : Word} (hw : w.Pos) (hne : w ≠ []) :
    (∃ a, IsSyrCycle a w.length ∧ gapWord a w.length = w) ↔ Dz w ∣ Sz w := by
  constructor
  · rintro ⟨a, h, hg⟩; rw [← hg]; exact cycle_D_dvd_S h
  · intro hdvd; exact ⟨_, isSyrCycle_of_dvd hw hne hdvd⟩

/-- **The divisibility form of "no nontrivial positive cycle"** (Böhm–Sontacchi 1978; Tao 2011
"Conjecture 3"): there is no nontrivial positive cycle iff every nonempty positive gap word with
`D(w) > 0` and `D(w) ∣ S(w)` has `S(w) = D(w)` (quotient `1`). -/
theorem noNontrivialPositiveCycle_iff_dvd :
    NoNontrivialPositiveCycle ↔
      ∀ w : Word, w.Pos → w ≠ [] → 0 < Dz w → Dz w ∣ Sz w → Sz w = Dz w := by
  constructor
  · intro H w hw hne hD hdvd
    obtain ⟨hc, -⟩ := isSyrCycle_of_dvd hw hne hdvd
    obtain ⟨a, ha⟩ := hdvd
    have hapos : 0 < a := pos_of_mul_pos_right (ha ▸ Sz_pos hne) hD.le
    rw [ha, Int.mul_ediv_cancel_left _ hD.ne'] at hc
    rw [ha, H a _ hapos hc, mul_one]
  · intro H a o ha hc
    have hS := H _ (gapWord_pos hc.2.1 o) (cycle_gapWord_ne_nil hc) (cycle_Dz_pos hc ha)
      (cycle_D_dvd_S hc)
    have e := hc.cycle_equation
    rw [hS] at e
    exact mul_right_eq_self₀.1 e |>.resolve_right (cycle_Dz_ne_zero hc)

/-! ## Linear form, real loop product, AM–GM edge -/

/-- For every word, `D ≥ 3^o · Λ` where `Λ = E log 2 - o log 3` is the linear form in logarithms
(`2^E = 3^o e^Λ` and `e^Λ - 1 ≥ Λ`). -/
theorem Dz_ge (w : Word) :
    (3 : ℝ) ^ w.length * ((w.sum : ℝ) * Real.log 2 - w.length * Real.log 3) ≤ Dz w := by
  have h2 : (2 : ℝ) ^ w.sum =
      3 ^ w.length * Real.exp ((w.sum : ℝ) * Real.log 2 - w.length * Real.log 3) := by
    rw [← Real.log_pow, ← Real.log_pow, ← Real.log_div (by positivity) (by positivity),
      Real.exp_log (by positivity)]
    field_simp
  have := Real.add_one_le_exp ((w.sum : ℝ) * Real.log 2 - w.length * Real.log 3)
  have h3 : (0 : ℝ) < 3 ^ w.length := by positivity
  simp only [Dz, D, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  rw [h2]
  nlinarith

/-- The real loop product: on a cycle `2^E = ∏_{k<o} (3 + 1/a_k)`. -/
theorem cycle_two_pow_eq_prod {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    (2 : ℝ) ^ (gapWord a o).sum = ∏ k ∈ range o, (3 + 1 / (syr^[k] a : ℝ)) := by
  have hne : ∀ k, (syr^[k] a : ℝ) ≠ 0 := fun k => by
    exact_mod_cast ne_zero_of_odd (syr_iterate_odd h.2.1 k)
  have hP : (∏ k ∈ range o, (syr^[k] a : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun k _ => hne k
  have hl : (2 : ℝ) ^ (gapWord a o).sum * ∏ k ∈ range o, (syr^[k] a : ℝ) =
      ∏ k ∈ range o, (3 * (syr^[k] a : ℝ) + 1) := by exact_mod_cast cycle_loop_product h
  have hf : ∀ k ∈ range o, 3 * (syr^[k] a : ℝ) + 1 = (3 + 1 / (syr^[k] a : ℝ)) * syr^[k] a :=
    fun k _ => by field_simp [hne k]
  rw [prod_congr rfl hf, prod_mul_distrib] at hl
  exact mul_right_cancel₀ hP hl

/-- **AM–GM form of the upper edge** (the inequality `2^{K+L} ≤ (3 + μ)^K` in the proof of
Hercher 2023 Thm. 16): on a positive cycle `2^E ≤ (3 + μ)^o`, `μ = (1/o) Σ_k 1/a_k`. -/
theorem cycle_two_pow_le_amgm {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    (2 : ℝ) ^ (gapWord a o).sum ≤ (3 + (∑ k ∈ range o, 1 / (syr^[k] a : ℝ)) / o) ^ o := by
  have hz : ∀ k ∈ range o, (0 : ℝ) ≤ 3 + 1 / (syr^[k] a : ℝ) := fun k _ => by
    have : (0 : ℝ) < syr^[k] a := by exact_mod_cast syr_iterate_pos ha k
    positivity
  have ho : (0 : ℝ) < o := by exact_mod_cast h.1
  have hgm := Real.geom_mean_le_arith_mean (range o) (fun _ => 1)
    (fun k => 3 + 1 / (syr^[k] a : ℝ)) (fun _ _ => zero_le_one) (by simpa using ho) hz
  simp only [Real.rpow_one, sum_const, card_range, nsmul_eq_mul, mul_one, one_mul] at hgm
  rw [cycle_two_pow_eq_prod h]
  have hP : (0 : ℝ) ≤ ∏ k ∈ range o, (3 + 1 / (syr^[k] a : ℝ)) := prod_nonneg hz
  have e : (3 + (∑ k ∈ range o, 1 / (syr^[k] a : ℝ)) / o) =
      (∑ k ∈ range o, (3 + 1 / (syr^[k] a : ℝ))) / o := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]; field_simp
  rw [e]
  calc ∏ k ∈ range o, (3 + 1 / (syr^[k] a : ℝ))
      = ((∏ k ∈ range o, (3 + 1 / (syr^[k] a : ℝ))) ^ ((o : ℝ)⁻¹)) ^ o :=
        (Real.rpow_inv_natCast_pow hP h.1.ne').symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hgm o

/-! ## Collatz conjecture ⇒ no nontrivial positive cycle -/

/-- The Collatz conjecture implies there is no nontrivial positive cycle. -/
theorem noNontrivialPositiveCycle_of_collatzConjecture (H : CollatzConjecture) :
    NoNontrivialPositiveCycle := fun a _ ha hc => by
  obtain ⟨i, hi⟩ := H a.toNat (by omega)
  exact cycle_eq_one_of_reaches_one hc ha hi

/-! ## Deep literature results — STATED, not proved, not assumed

Each of the following is a `Prop` recording a published theorem (or computation) precisely. None
is proved here and none is used as an axiom; they appear only as explicit hypotheses of the
conditional theorems further down. -/

/-- `VerifiedUpTo` is monotone: a larger verified range gives a smaller one. -/
theorem VerifiedUpTo.mono {N N' : ℕ} (h : VerifiedUpTo N) (hN : N' ≤ N) : VerifiedUpTo N' :=
  fun n hn hn' => h n hn (hn'.trans hN)

/-- **Barina 2025** (D. Barina, "Improved verification limit for the convergence of the Collatz
conjecture", J. Supercomputing 81 (2025) art. 810): every `n < 2^71` reaches `1` (strict bound, as
stated in the paper; equivalently `n ≤ 2^71 - 1`). A computation, not a proof. -/
def Barina2025 : Prop := VerifiedUpTo (2 ^ 71 - 1)

/-- **Barina 2021** (D. Barina, "Convergence verification of the Collatz problem",
J. Supercomputing 77 (2021) 2681–2688): every `n < 2^68` reaches `1`. (The `1.5 · 2^70` figure the
survey attributes to this paper is a later project-page milestone, not this paper.) -/
def Barina2021 : Prop := VerifiedUpTo (2 ^ 68 - 1)

/-- **Steiner 1977** (R. P. Steiner, "A theorem on the Syracuse problem", Proc. 7th Manitoba Conf.
Numer. Math. (1977), Congr. Numer. XX (1978) 553–559): the only circuit which is a cycle is the
trivial one; i.e. no nontrivial positive `1`-cycle. -/
def Steiner1977 : Prop := ∀ a : ℤ, IsMCycle a 1 → a = 1

/-- **Steiner 1977, Diophantine form** (the statement actually proved, after Davison 1977's
reduction; Lagarias's bibliography I, entry 158): the only positive solution of
`(2^{k+l} - 3^k) h = 2^l - 1` is `(k, l, h) = (1, 1, 1)`. The reduction from `Steiner1977Dioph` to
`Steiner1977` is classical but is **not** formalized here. -/
def Steiner1977Dioph : Prop :=
  ∀ k l h : ℕ, 0 < k → 0 < l → 0 < h →
    ((2 : ℤ) ^ (k + l) - 3 ^ k) * h = 2 ^ l - 1 → k = 1 ∧ l = 1 ∧ h = 1

/-- **Simons 2005** (J. L. Simons, "On the nonexistence of 2-cycles for the 3x+1 problem",
Math. Comp. 74 (2005) 1565–1572): there is no nontrivial positive `2`-cycle. (Whether the proof uses a
verification bound could not be checked against the full text.) -/
def Simons2005 : Prop := ∀ a : ℤ, IsMCycle a 2 → a = 1

/-- **Simons–de Weger 2005** (J. L. Simons, B. M. M. de Weger, "Theoretical and computational
bounds for m-cycles of the 3n+1 problem", Acta Arith. 117 (2005) 51–70, Thm. 3(b), with verification
bound `X₀ = 301 · 2^50`): no nontrivial `m`-cycle for `1 ≤ m ≤ 68`. -/
def SimonsDeWeger2005 : Prop := NoMCyclesUpTo 68

/-- **Simons–de Weger, updated version v1.44 (2010)** (`X₀ = 5 · 2^60`): no nontrivial `m`-cycle for
`1 ≤ m ≤ 75` (Hercher's "m ≥ 76"). -/
def SimonsDeWeger2010 : Prop := NoMCyclesUpTo 75

/-- **Hercher 2023** (C. Hercher, "There are no Collatz-m-Cycles with m ≤ 91", J. Integer Seq. 26
(2023) Art. 23.3.5, Thm. 23; arXiv:2201.00406): no nontrivial `m`-cycle for `1 ≤ m ≤ 91`. Uses the
verification bound `X₀ = 695 · 2^60` (JIS) / `704 · 2^60` (arXiv v3). -/
def Hercher2023 : Prop := NoMCyclesUpTo 91

/-- **Hercher 2023, Cor. 29**: if every `n ≤ 1536 · 2^60 = 3 · 2^69` reaches `1`, then every
nontrivial cycle has `K > 1.375 · 10^11` odd elements. -/
def Hercher2023Cor29 : Prop :=
  VerifiedUpTo (3 * 2 ^ 69) →
    ∀ a : ℤ, ∀ o : ℕ, 0 < a → IsSyrCycle a o → a ≠ 1 → 137500000000 < o

/-- **Simons–de Weger 2005, Lemma 12** (from Rhin's 1987 linear-forms bound, Progr. Math. 71 (1988)
155–164, Proposition p. 160, applied with `H = K + L`, plus their Lemma 8): for every nontrivial
positive cycle with `K = o` odd and `K + L = E` total steps of `T`,
`Λ = (K+L) log 2 - K log 3 > exp(-13.3 (0.46057 + log K))`. The constant `0.46057 ≈ log log₂ 3`
sits **inside** the exponent; the multiplicative constant is `e^{-13.3 · 0.46057} ≈ 0.00219`. -/
def SimonsDeWegerLemma12 : Prop :=
  ∀ a : ℤ, ∀ o : ℕ, 0 < a → IsSyrCycle a o → a ≠ 1 →
    Real.exp (-13.3 * (0.46057 + Real.log o)) <
      ((gapWord a o).sum : ℝ) * Real.log 2 - o * Real.log 3

/-- The exceptional exponents of Ellison's bound. -/
def ellisonExceptions : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 19, 27}

/-- **Ellison 1971** (W. J. Ellison, "On a theorem of S. Sivasankaranarayana Pillai", Sém. Théorie
des Nombres de Bordeaux 1970–71, exp. 12, Thm. 3): `|2^x - 3^y| > 2^x e^{-x/10}` for all positive
integers `x, y` with `x ∉ {1,…,11, 13, 14, 16, 19, 27}` (in particular for all `x ≥ 28`). -/
def Ellison1971 : Prop :=
  ∀ x y : ℕ, 0 < x → 0 < y → x ∉ ellisonExceptions →
    (2 : ℝ) ^ x * Real.exp (-(x : ℝ) / 10) < |(2 : ℝ) ^ x - 3 ^ y|

/-- **Eliahou 1993** (S. Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle
lengths", Discrete Math. 118 (1993) 45–56): if a cycle `Ω` of `T` has `min Ω > 2^40`, then
`|Ω| = 301994 a + 17087915 b + 85137581 c` with `a, b, c ≥ 0`, `b ≥ 1`, `ac = 0`. Here `|Ω|` is the
`T`-length `K + L = E` of the cycle (with its minimal period); the minimum of a cycle is odd, so
`min Ω > 2^40` is the same as every odd element exceeding `2^40`. -/
def Eliahou1993 : Prop :=
  ∀ a : ℤ, ∀ o : ℕ, IsPrimSyrCycle a o → (∀ k, (2 : ℤ) ^ 40 < syr^[k] a) →
    ∃ x y z : ℕ, (gapWord a o).sum = 301994 * x + 17087915 * y + 85137581 * z ∧ 1 ≤ y ∧ x * z = 0

/-- The `T` map `n ↦ n/2` (even), `(3n+1)/2` (odd), for Terras's theorem. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- **Terras 1976** (R. Terras, "A stopping time problem on the positive integers", Acta Arith. 30
(1976) 241–252; also Lagarias 1985 Thm. B): for every `k`, the parity vector
`(T^i(n) mod 2)_{i<k}` depends only on `n mod 2^k`, and `n mod 2^k ↦` parity vector is a bijection
onto `{0,1}^k`. Elementary, but not formalized here. -/
def Terras1976 : Prop :=
  ∀ k : ℕ, (∀ n : ℕ, ∀ i < k, T^[i] n % 2 = T^[i] (n % 2 ^ k) % 2) ∧
    Function.Bijective fun r : Fin (2 ^ k) => fun i : Fin k => decide (T^[i] r.val % 2 = 1)

/-! ### Open problems (stated) -/

/-- **Open:** finitely many positive cycle points in total (the `3x+1` case of the `3x+d` finiteness
conjecture). Implied by `NoNontrivialPositiveCycle`. -/
def FinitelyManyPositiveCyclePoints : Prop := {a : ℤ | 0 < a ∧ ∃ o, IsSyrCycle a o}.Finite

/-- **Open:** no nontrivial `m`-cycle with `m ≥ M` (open for `M = 92`, the gap Hercher leaves). -/
def NoMCyclesFrom (M : ℕ) : Prop := ∀ a : ℤ, ∀ m : ℕ, M ≤ m → IsMCycle a m → a = 1

/-- **Open:** the negative cycles are exactly the three known ones (`-1`, `-5 → -7`, and the
seven-point `-17` cycle). Their existence is proved above; completeness is a conjecture. -/
def OnlyKnownNegativeCycles : Prop :=
  ∀ a : ℤ, ∀ o : ℕ, a < 0 → IsSyrCycle a o →
    a ∈ ({-1, -5, -7, -17, -25, -37, -55, -41, -61, -91} : Finset ℤ)

/-! ## Conditional consequences (short logical links) -/

/-- The `m`-cycle records are nested: Hercher ⇒ Simons–de Weger (2010) ⇒ Simons–de Weger (2005). -/
theorem hercher_chain (h : Hercher2023) : SimonsDeWeger2010 ∧ SimonsDeWeger2005 :=
  ⟨h.mono (by norm_num), h.mono (by norm_num)⟩

/-- Simons–de Weger 2005 contains Steiner 1977 and Simons 2005. -/
theorem steiner_simons_of_sdw (h : SimonsDeWeger2005) : Steiner1977 ∧ Simons2005 :=
  ⟨fun a ha => h a 1 le_rfl (by norm_num) ha, fun a ha => h a 2 (by norm_num) (by norm_num) ha⟩

/-- Hercher's theorem plus the open `m ≥ 92` case would settle the cycle half of Collatz. -/
theorem noNontrivialPositiveCycle_of_hercher (h : Hercher2023) (h92 : NoMCyclesFrom 92) :
    NoNontrivialPositiveCycle :=
  noNontrivialPositiveCycle_iff.2 fun _ a m h1 _ hm =>
    if h91 : m ≤ 91 then h a m h1 h91 hm else h92 a m (by omega) hm

/-- No nontrivial positive cycle ⇒ finitely many positive cycle points (only `1`). -/
theorem finitelyMany_of_noNontrivial (h : NoNontrivialPositiveCycle) :
    FinitelyManyPositiveCyclePoints :=
  (Set.finite_singleton (1 : ℤ)).subset fun a ⟨ha, o, hc⟩ => h a o ha hc

/-- **Barina ⇒ `N₀ = 2^71`.** Assuming Barina's verification, every element of a nontrivial positive
cycle is at least `2^71`. -/
theorem barina_cycle_ge (hB : Barina2025) {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a)
    (h1 : a ≠ 1) (k : ℕ) : (2 : ℤ) ^ 71 ≤ syr^[k] a := by
  have := cycle_gt_of_verifiedUpTo hB h ha h1 k
  push_cast at this
  omega

/-- **Barina ⇒ the sandwich with `N₀ = 2^71`**: for a nontrivial positive cycle,
`log₂ 3 < E/o ≤ log₂(3 + 2^{-71})` and `0 < E - o log₂ 3 < o / (3 · 2^71 · ln 2)`. -/
theorem barina_sandwich (hB : Barina2025) {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a)
    (h1 : a ≠ 1) :
    Real.logb 2 3 < ((gapWord a o).sum : ℝ) / o ∧
      ((gapWord a o).sum : ℝ) / o ≤ Real.logb 2 (3 + 1 / 2 ^ 71) ∧
      ((gapWord a o).sum : ℝ) - o * Real.logb 2 3 < o / (3 * 2 ^ 71 * Real.log 2) := by
  have hmin : ∀ k < o, (2 : ℝ) ^ 71 ≤ syr^[k] a := fun k _ => by
    exact_mod_cast barina_cycle_ge hB h ha h1 k
  exact ⟨cycle_logb_lt h ha, cycle_ratio_le_logb h (by positivity) hmin,
    (cycle_excess_le h (by positivity) hmin).2⟩

/-- **Simons–de Weger Lemma 12 ⇒ a lower bound on `D`**: for a nontrivial positive cycle,
`D = 2^E - 3^o > 3^o exp(-13.3 (0.46057 + log o)) ≈ 0.00219 · 3^o / o^{13.3}`. -/
theorem sdw12_Dz_gt (hR : SimonsDeWegerLemma12) {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a)
    (h1 : a ≠ 1) :
    (3 : ℝ) ^ o * Real.exp (-13.3 * (0.46057 + Real.log o)) < Dz (gapWord a o) := by
  have := Dz_ge (gapWord a o)
  rw [gapWord_length] at this
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_left (hR a o ha h h1) (by positivity)) this

/-- **Ellison ⇒ an upper bound on cycle elements**: if `E ∉ {1,…,11,13,14,16,19,27}` (e.g. `E ≥ 28`),
every element of a positive cycle satisfies `a < (3/2)^o e^{E/10}`. -/
theorem ellison_cycle_lt (hE : Ellison1971) {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a)
    (hx : (gapWord a o).sum ∉ ellisonExceptions) :
    (a : ℝ) < (3 / 2) ^ o * Real.exp ((gapWord a o).sum / 10) := by
  obtain ⟨h1, h2⟩ := cycle_one_le_length h
  rw [gapWord_length] at h1 h2
  have hD := cycle_Dz_pos h ha
  have hDr : ((Dz (gapWord a o) : ℤ) : ℝ) = (2 : ℝ) ^ (gapWord a o).sum - 3 ^ o := by
    simp only [Dz, D, gapWord_length, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  have hEll := hE (gapWord a o).sum o (by omega) h.1 hx
  rw [← hDr, abs_of_pos (by exact_mod_cast hD)] at hEll
  have hS : (2 : ℝ) ^ o * Sz (gapWord a o) + 2 ^ (gapWord a o).sum * 2 ^ o ≤
      2 ^ (gapWord a o).sum * 3 ^ o := by
    have := two_pow_mul_Sz_le (gapWord_pos h.2.1 o)
    rw [gapWord_length] at this; exact_mod_cast this
  have he : ((Dz (gapWord a o) : ℤ) : ℝ) * a = Sz (gapWord a o) := by
    exact_mod_cast h.cycle_equation
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  set u := Real.exp (-((gapWord a o).sum : ℝ) / 10) with hu_def
  have hu : 0 < u := Real.exp_pos _
  have h2E : (0 : ℝ) < 2 ^ (gapWord a o).sum := by positivity
  have h2o : (0 : ℝ) < 2 ^ o := by positivity
  have key : a * (2 ^ o * u) * 2 ^ (gapWord a o).sum < 3 ^ o * 2 ^ (gapWord a o).sum := by
    have h3 : (a : ℝ) * (2 ^ (gapWord a o).sum * u) < a * Dz (gapWord a o) :=
      mul_lt_mul_of_pos_left hEll har
    nlinarith
  have key' : (a : ℝ) * (2 ^ o * u) < 3 ^ o := lt_of_mul_lt_mul_right key h2E.le
  have hexp : Real.exp (((gapWord a o).sum : ℝ) / 10) * u = 1 := by
    rw [hu_def, ← Real.exp_add, show ((gapWord a o).sum : ℝ) / 10 + -((gapWord a o).sum : ℝ) / 10 = 0
      by ring, Real.exp_zero]
  have hpos : 0 < Real.exp (((gapWord a o).sum : ℝ) / 10) / 2 ^ o := by positivity
  calc (a : ℝ) = a * (2 ^ o * u) * (Real.exp ((gapWord a o).sum / 10) / 2 ^ o) := by
        rw [show (a : ℝ) * (2 ^ o * u) * (Real.exp ((gapWord a o).sum / 10) / 2 ^ o) =
          a * (Real.exp ((gapWord a o).sum / 10) * u) by field_simp, hexp, mul_one]
    _ < 3 ^ o * (Real.exp ((gapWord a o).sum / 10) / 2 ^ o) := mul_lt_mul_of_pos_right key' hpos
    _ = (3 / 2) ^ o * Real.exp ((gapWord a o).sum / 10) := by rw [div_pow]; ring

/-- **Eliahou + Barina**: assuming both, every nontrivial positive cycle (with minimal period `o`)
has `T`-length `E = 301994 a + 17087915 b + 85137581 c`, `b ≥ 1`, `ac = 0`. -/
theorem eliahou_of_barina (hEl : Eliahou1993) (hB : Barina2025) {a : ℤ} {o : ℕ}
    (h : IsPrimSyrCycle a o) (ha : 0 < a) (h1 : a ≠ 1) :
    ∃ x y z : ℕ, (gapWord a o).sum = 301994 * x + 17087915 * y + 85137581 * z ∧ 1 ≤ y ∧ x * z = 0 :=
  hEl a o h fun k => by
    have := barina_cycle_ge hB h.1 ha h1 k
    have : (2 : ℤ) ^ 40 < 2 ^ 71 := by norm_num
    omega

/-- **Hercher Cor. 29 + Barina**: assuming both, every nontrivial positive cycle has more than
`1.375 · 10^11` odd elements. -/
theorem hercher_odd_steps_of_barina (hH : Hercher2023Cor29) (hB : Barina2025) {a : ℤ} {o : ℕ}
    (h : IsSyrCycle a o) (ha : 0 < a) (h1 : a ≠ 1) : 137500000000 < o :=
  hH (hB.mono (by norm_num)) a o ha h h1

end Syracuse.CycleLiterature
