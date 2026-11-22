import Syracuse.Approaches.FourRuns
import Syracuse.Approaches.CycleLength

/-!
# The run frontier: few runs need astronomically large blocks

Barina's verification and Hercher's Corollary 29 give `o > 1.375·10^{11}` for every nontrivial positive
cycle (`CycleLiterature.hercher_odd_steps_of_barina`), hence `E > 1.375·10^{11}` (`E_gt_of_lit`). Every
effective run bound proved so far then excludes every word whose blocks have coefficients below an
astronomical size:

* **two runs over any tree** (`frontier_two_runs`, Ellison): no root with `|C(u₀, v₀)| ≤ 2^K`,
  `20K ≤ 1.375·10^{11}`;
* **three letter runs** `1^a d^b e^c` (`frontier_three_letters`, Ellison): no `d + e + 2 ≤ 1.25·10^{10}`;
* **three runs of any blocks** (`frontier_three_runs`, Ellison): no coefficients `≤ 2^K` with
  `20(K + 2) ≤ 1.375·10^{11}`, given the three `T`s nonzero;
* **four runs of any blocks** (`frontier_four_runs`, Rhin via Simons–de Weger Lemma 12): no coefficients
  `≤ 2^K` with `3500 + 16K ≤ 1.375·10^{11}`, given the four `T`s nonzero.

So a nontrivial positive cycle that is a two-, three- or four-run word needs block coefficients of more
than about `2^{6·10^9}` bits' worth (`2^{8.6·10^9}` for four runs).

**Where the method stops.** For `m` runs, the size argument needs a lower-bound exponent above
`c_m = 1 - (log₂3 - 1)/(log₂3^m - 1)` (`0.613, 0.804, 0.890, 0.935, …`; computed by linear programming,
see `FINDINGS`). Ellison's `0.8557` covers `m ≤ 3`. The four-run failure is real on actual words, for
example `6^{a₀}(1^{20}2)^{a₁}(1^{21}2)^{a₂}(1^{22}2)^{a₃}` near the critical slope, whose limiting ratio is
`0.878`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `E > 1.375·10^{11}` on a nontrivial positive cycle | `E_gt_of_lit` | proved (conditional on Barina + Hercher Cor. 29) |
| two runs over any tree, below the frontier | `frontier_two_runs` | proved (conditional on Ellison + Barina + Hercher Cor. 29) |
| three letter runs, below the frontier | `frontier_three_letters` | proved (same) |
| three runs of any blocks, below the frontier | `frontier_three_runs` | proved (same) |
| four runs of any blocks, below the frontier | `frontier_four_runs` | proved (conditional on Lemma 12 + Barina + Hercher Cor. 29) |
| the four frontiers for any cycle bounds `CycleBounds No NE` (Hercher versions are instances) | `frontier_two_runs_of`, `frontier_three_letters_of`, `frontier_three_runs_of`, `frontier_four_runs_of` | proved (Barina-only instances in `BarinaFrontier`) |
-/

namespace Syracuse.RunsFrontier

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

/-- On a nontrivial positive cycle, `E > 1.375·10^{11}` (Barina and Hercher's Corollary 29). -/
theorem E_gt_of_lit (hB : CycleLiterature.Barina2025) (hH29 : CycleLiterature.Hercher2023Cor29)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) (hx1 : x ≠ 1) :
    137500000000 < (gapWord x o).sum := by
  have ho := CycleLiterature.hercher_odd_steps_of_barina hH29 hB h hx hx1
  have hl := CycleLiterature.length_le_sum (CocycleCombine.IsSyrCycle.pos h)
  rw [gapWord_length] at hl
  omega

/-- **(General bounds.)** Two runs, frontier.** -/
theorem frontier_two_runs_of (hEl : CycleLiterature.Ellison1971)
    {No NE : ℕ} (hCB : CycleLength.CycleBounds No NE) (hN : 28 ≤ NE)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {u₀ v₀ : Word} (hu₀ : u₀.Pos) (hv₀ : v₀.Pos) (hu₀0 : u₀ ≠ []) (hv₀0 : v₀ ≠ [])
    (hC : core (2 : ℤ) 3 u₀ v₀ ≠ 0) {K : ℕ} (hK : |core (2 : ℤ) 3 u₀ v₀| ≤ 2 ^ K)
    (hK' : 20 * K ≤ NE) {u v : Word} (hst : Trees.Tree u₀ v₀ u v) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : ¬ (gapWord x o ~r bpow u a ++ bpow v b) := by
  intro hw
  have hE := (hCB x o hx h hx1).2
  refine Trees.no_cycle_tree hEl hu₀ hv₀ hu₀0 hv₀0 hC hst h ha hb hw
    (Frontier.not_mem_exceptions (by omega)) ?_
  calc |core (2 : ℤ) 3 u₀ v₀| ^ 20 ≤ (2 ^ K) ^ 20 := pow_le_pow_left₀ (abs_nonneg _) hK 20
    _ = 2 ^ (20 * K) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ (gapWord x o).sum := pow_le_pow_right₀ (by norm_num) (by omega)

/-- **Two runs, frontier.** -/
theorem frontier_two_runs (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {u₀ v₀ : Word} (hu₀ : u₀.Pos) (hv₀ : v₀.Pos) (hu₀0 : u₀ ≠ []) (hv₀0 : v₀ ≠ [])
    (hC : core (2 : ℤ) 3 u₀ v₀ ≠ 0) {K : ℕ} (hK : |core (2 : ℤ) 3 u₀ v₀| ≤ 2 ^ K)
    (hK' : 20 * K ≤ 137500000000) {u v : Word} (hst : Trees.Tree u₀ v₀ u v) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : ¬ (gapWord x o ~r bpow u a ++ bpow v b) :=
  frontier_two_runs_of hEl (CycleLength.cycleBounds_hercher hB hH29) (by norm_num) h hx hx1 hu₀
    hv₀ hu₀0 hv₀0 hC hK hK' hst ha hb

/-- **(General bounds.)** Three letter runs, frontier.** -/
theorem frontier_three_letters_of (hEl : CycleLiterature.Ellison1971)
    {No NE : ℕ} (hCB : CycleLength.CycleBounds No NE) (hN : 28 ≤ NE)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {d e : ℕ} (hd : 2 ≤ d) (he : 2 ≤ e) (hde : d ≠ e)
    (hsmall : 11 * (d + e + 2) ≤ NE) {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ¬ (gapWord x o ~r List.replicate a 1 ++ List.replicate b d ++ List.replicate c e) := by
  intro hw
  have hE := (hCB x o hx h hx1).2
  have hs : (gapWord x o).sum = a + b * d + c * e := by
    rw [hw.perm.sum_eq]; simp [List.sum_append, List.sum_replicate]; ring
  exact ThreeRuns.three_letter_runs hEl hd he hde h ha hb hc hw (by omega)

/-- **Three letter runs, frontier.** -/
theorem frontier_three_letters (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {d e : ℕ} (hd : 2 ≤ d) (he : 2 ≤ e) (hde : d ≠ e)
    (hsmall : 11 * (d + e + 2) ≤ 137500000000) {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ¬ (gapWord x o ~r List.replicate a 1 ++ List.replicate b d ++ List.replicate c e) :=
  frontier_three_letters_of hEl (CycleLength.cycleBounds_hercher hB hH29) (by norm_num) h hx hx1
    hd he hde hsmall ha hb hc

/-- **(General bounds.)** Three runs of any blocks, frontier.** -/
theorem frontier_three_runs_of (hEl : CycleLiterature.Ellison1971)
    {No NE : ℕ} (hCB : CycleLength.CycleBounds No NE) (hN : 28 ≤ NE)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {u v w : Word} (hu : u.Pos) (hv : v.Pos) (hw' : w.Pos) {a b c K : ℕ}
    (hK1 : |D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u| ≤ 2 ^ K)
    (hK2 : |D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v| ≤ 2 ^ K)
    (hK3 : |D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w| ≤ 2 ^ K)
    (hTU : D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 2 ^ ((bpow v b).sum + (bpow w c).sum) +
      D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 3 ^ ((bpow v b).length + (bpow w c).length) +
      D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 2 ^ (bpow v b).sum * 3 ^ (bpow w c).length ≠ 0)
    (hTV : D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 2 ^ ((bpow w c).sum + (bpow u a).sum) +
      D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 3 ^ ((bpow w c).length + (bpow u a).length) +
      D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 2 ^ (bpow w c).sum * 3 ^ (bpow u a).length ≠ 0)
    (hTZ : D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 2 ^ ((bpow u a).sum + (bpow v b).sum) +
      D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 3 ^ ((bpow u a).length + (bpow v b).length) +
      D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 2 ^ (bpow u a).sum * 3 ^ (bpow v b).length ≠ 0)
    (hsmall : 20 * (K + 2) ≤ NE) :
    ¬ (gapWord x o ~r bpow u a ++ bpow v b ++ bpow w c) := by
  intro hrot
  have hE := (hCB x o hx h hx1).2
  have hs : (gapWord x o).sum = (bpow u a).sum + (bpow v b).sum + (bpow w c).sum := by
    rw [hrot.perm.sum_eq]; simp only [List.sum_append]
  exact ThreeRuns.three_runs_bounded hEl hu hv hw' hK1 hK2 hK3 hTU hTV hTZ h hrot (by omega)

/-- **Three runs of any blocks, frontier.** -/
theorem frontier_three_runs (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {u v w : Word} (hu : u.Pos) (hv : v.Pos) (hw' : w.Pos) {a b c K : ℕ}
    (hK1 : |D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u| ≤ 2 ^ K)
    (hK2 : |D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v| ≤ 2 ^ K)
    (hK3 : |D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w| ≤ 2 ^ K)
    (hTU : D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 2 ^ ((bpow v b).sum + (bpow w c).sum) +
      D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 3 ^ ((bpow v b).length + (bpow w c).length) +
      D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 2 ^ (bpow v b).sum * 3 ^ (bpow w c).length ≠ 0)
    (hTV : D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 2 ^ ((bpow w c).sum + (bpow u a).sum) +
      D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 3 ^ ((bpow w c).length + (bpow u a).length) +
      D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 2 ^ (bpow w c).sum * 3 ^ (bpow u a).length ≠ 0)
    (hTZ : D (2 : ℤ) 3 u * core (2 : ℤ) 3 v w * 2 ^ ((bpow u a).sum + (bpow v b).sum) +
      D (2 : ℤ) 3 v * core (2 : ℤ) 3 w u * 3 ^ ((bpow u a).length + (bpow v b).length) +
      D (2 : ℤ) 3 w * core (2 : ℤ) 3 u v * 2 ^ (bpow u a).sum * 3 ^ (bpow v b).length ≠ 0)
    (hsmall : 20 * (K + 2) ≤ 137500000000) :
    ¬ (gapWord x o ~r bpow u a ++ bpow v b ++ bpow w c) :=
  frontier_three_runs_of hEl (CycleLength.cycleBounds_hercher hB hH29) (by norm_num) h hx hx1 hu
    hv hw' hK1 hK2 hK3 hTU hTV hTZ hsmall

/-- **(General bounds.)** Four runs of any blocks, frontier** (Rhin via Simons–de Weger Lemma 12). -/
theorem frontier_four_runs_of (hR : CycleLiterature.SimonsDeWegerLemma12)
    {No NE : ℕ} (hCB : CycleLength.CycleBounds No NE) (hN : 28 ≤ NE) {x : ℤ} {o : ℕ}
    (h : IsSyrCycle x o) (hx : 0 < x) (hx1 : x ≠ 1) {p₁ p₂ p₃ p₄ : Word}
    (hp₁ : p₁.Pos) (hp₂ : p₂.Pos) (hp₃ : p₃.Pos) (hp₄ : p₄.Pos) {a₁ a₂ a₃ a₄ K : ℕ}
    (hK1 : |D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁| ≤ 2 ^ K)
    (hK2 : |D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂| ≤ 2 ^ K)
    (hK3 : |D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃| ≤ 2 ^ K)
    (hK4 : |D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄| ≤ 2 ^ K)
    (hT1 : D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum + (bpow p₄ a₄).sum) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          3 ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₄ * core (2 : ℤ) 3 p₂ p₃ * 2 ^ (bpow p₂ a₂).sum *
          3 ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum) * 3 ^ (bpow p₄ a₄).length ≠ 0)
    (hT2 : D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          2 ^ ((bpow p₃ a₃).sum + (bpow p₄ a₄).sum + (bpow p₁ a₁).sum) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          3 ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length + (bpow p₁ a₁).length) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₁ * core (2 : ℤ) 3 p₃ p₄ * 2 ^ (bpow p₃ a₃).sum *
          3 ^ ((bpow p₄ a₄).length + (bpow p₁ a₁).length) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          2 ^ ((bpow p₃ a₃).sum + (bpow p₄ a₄).sum) * 3 ^ (bpow p₁ a₁).length ≠ 0)
    (hT3 : D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          2 ^ ((bpow p₄ a₄).sum + (bpow p₁ a₁).sum + (bpow p₂ a₂).sum) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          3 ^ ((bpow p₄ a₄).length + (bpow p₁ a₁).length + (bpow p₂ a₂).length) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₂ * core (2 : ℤ) 3 p₄ p₁ * 2 ^ (bpow p₄ a₄).sum *
          3 ^ ((bpow p₁ a₁).length + (bpow p₂ a₂).length) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          2 ^ ((bpow p₄ a₄).sum + (bpow p₁ a₁).sum) * 3 ^ (bpow p₂ a₂).length ≠ 0)
    (hT4 : D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          2 ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum + (bpow p₃ a₃).sum) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          3 ^ ((bpow p₁ a₁).length + (bpow p₂ a₂).length + (bpow p₃ a₃).length) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₃ * core (2 : ℤ) 3 p₁ p₂ * 2 ^ (bpow p₁ a₁).sum *
          3 ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          2 ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum) * 3 ^ (bpow p₃ a₃).length ≠ 0)
    (hsmall : 3500 + 16 * K ≤ NE) :
    ¬ (gapWord x o ~r bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄) := by
  intro hrot
  have hE := (hCB x o hx h hx1).2
  have hs : (gapWord x o).sum =
      (bpow p₁ a₁).sum + (bpow p₂ a₂).sum + (bpow p₃ a₃).sum + (bpow p₄ a₄).sum := by
    rw [hrot.perm.sum_eq]; simp only [List.sum_append]
  exact FourRuns.four_runs_bounded hR hp₁ hp₂ hp₃ hp₄ hK1 hK2 hK3 hK4 hT1 hT2 hT3 hT4 h hx hx1
    hrot (by omega)

/-- **Four runs of any blocks, frontier** (Rhin via Simons–de Weger Lemma 12). -/
theorem frontier_four_runs (hR : CycleLiterature.SimonsDeWegerLemma12)
    (hB : CycleLiterature.Barina2025) (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ}
    (h : IsSyrCycle x o) (hx : 0 < x) (hx1 : x ≠ 1) {p₁ p₂ p₃ p₄ : Word}
    (hp₁ : p₁.Pos) (hp₂ : p₂.Pos) (hp₃ : p₃.Pos) (hp₄ : p₄.Pos) {a₁ a₂ a₃ a₄ K : ℕ}
    (hK1 : |D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁| ≤ 2 ^ K)
    (hK2 : |D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂| ≤ 2 ^ K)
    (hK3 : |D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃| ≤ 2 ^ K)
    (hK4 : |D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄| ≤ 2 ^ K)
    (hT1 : D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum + (bpow p₄ a₄).sum) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          3 ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₄ * core (2 : ℤ) 3 p₂ p₃ * 2 ^ (bpow p₂ a₂).sum *
          3 ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          2 ^ ((bpow p₂ a₂).sum + (bpow p₃ a₃).sum) * 3 ^ (bpow p₄ a₄).length ≠ 0)
    (hT2 : D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          2 ^ ((bpow p₃ a₃).sum + (bpow p₄ a₄).sum + (bpow p₁ a₁).sum) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          3 ^ ((bpow p₃ a₃).length + (bpow p₄ a₄).length + (bpow p₁ a₁).length) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₁ * core (2 : ℤ) 3 p₃ p₄ * 2 ^ (bpow p₃ a₃).sum *
          3 ^ ((bpow p₄ a₄).length + (bpow p₁ a₁).length) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          2 ^ ((bpow p₃ a₃).sum + (bpow p₄ a₄).sum) * 3 ^ (bpow p₁ a₁).length ≠ 0)
    (hT3 : D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          2 ^ ((bpow p₄ a₄).sum + (bpow p₁ a₁).sum + (bpow p₂ a₂).sum) +
        D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          3 ^ ((bpow p₄ a₄).length + (bpow p₁ a₁).length + (bpow p₂ a₂).length) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₂ * core (2 : ℤ) 3 p₄ p₁ * 2 ^ (bpow p₄ a₄).sum *
          3 ^ ((bpow p₁ a₁).length + (bpow p₂ a₂).length) +
        D (2 : ℤ) 3 p₃ * D 2 3 p₄ * core (2 : ℤ) 3 p₁ p₂ *
          2 ^ ((bpow p₄ a₄).sum + (bpow p₁ a₁).sum) * 3 ^ (bpow p₂ a₂).length ≠ 0)
    (hT4 : D (2 : ℤ) 3 p₁ * D 2 3 p₂ * core (2 : ℤ) 3 p₃ p₄ *
          2 ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum + (bpow p₃ a₃).sum) +
        D (2 : ℤ) 3 p₂ * D 2 3 p₃ * core (2 : ℤ) 3 p₄ p₁ *
          3 ^ ((bpow p₁ a₁).length + (bpow p₂ a₂).length + (bpow p₃ a₃).length) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₃ * core (2 : ℤ) 3 p₁ p₂ * 2 ^ (bpow p₁ a₁).sum *
          3 ^ ((bpow p₂ a₂).length + (bpow p₃ a₃).length) +
        D (2 : ℤ) 3 p₄ * D 2 3 p₁ * core (2 : ℤ) 3 p₂ p₃ *
          2 ^ ((bpow p₁ a₁).sum + (bpow p₂ a₂).sum) * 3 ^ (bpow p₃ a₃).length ≠ 0)
    (hsmall : 3500 + 16 * K ≤ 137500000000) :
    ¬ (gapWord x o ~r bpow p₁ a₁ ++ bpow p₂ a₂ ++ bpow p₃ a₃ ++ bpow p₄ a₄) :=
  frontier_four_runs_of hR (CycleLength.cycleBounds_hercher hB hH29) (by norm_num) h hx hx1 hp₁
    hp₂ hp₃ hp₄ hK1 hK2 hK3 hK4 hT1 hT2 hT3 hT4 hsmall

end Syracuse.RunsFrontier
