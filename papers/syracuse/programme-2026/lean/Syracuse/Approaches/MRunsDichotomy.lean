import Syracuse.Approaches.MRunsExplicit

/-!
# Up to three runs of any blocks: a dichotomy with no side conditions

The key identity `D'·S(W) = 2^{E₀}·T + A₀·D(W)` (`MRuns.key_identity`) says that `T = 0` exactly
when the word's rational cycle point `S(W)/D(W)` equals the first block's point `S(p₀)/D(p₀)`. On a
genuine cycle the word's point is an integer orbit point `y`. So `T = 0` makes `y` a cycle point of the
base block `p₀`: `D(p₀)·y = S(p₀)` (`T_zero_alt`), and `y` has period `|p₀|`. Hence (`mruns_dichotomy`):

> Given Ellison, a cycle of either sign whose gap word is a rotation of `p₀^{a₀} ⋯ p_{m-1}^{a_{m-1}}`
> (`1 ≤ m ≤ 3`, positive nonempty base blocks of total weight `B`, `E` outside Ellison's exceptions) either
> has an orbit point on a cycle of one base block (`D(p_R)·y = S(p_R)`), or satisfies
> `(θ_E - c_3)·max(E, o log₂ 3) ≤ 6B + 2 + log₂ 3`.

There is no long-run condition and no condition on the cores. With Barina and Hercher's
`o > 1.375·10^{11}`, both branches are impossible for nontrivial positive cycles when `B ≤ 10^9`
(`frontier_le_three`):

> **No nontrivial positive cycle has a gap word that is a rotation of `p₀^{a₀} p₁^{a₁} p₂^{a₂}` (or of
> fewer runs) over positive base blocks of total weight at most `10^9`.**

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| the orbit point at rotation `k` has the rotated gap word | `gapWord_iterate` | proved |
| `T = 0` puts an orbit point on a base block's cycle | `T_zero_alt` | proved |
| **dichotomy for `m ≤ 3`, any blocks** | `mruns_dichotomy` | proved (conditional on `Ellison1971`) |
| **frontier: no nontrivial positive cycle on `≤ 3` runs over base weight `≤ 10^9`** | `frontier_le_three` | proved (conditional on Ellison + Barina + Hercher Cor. 29) |
| the same for any cycle bounds: `120 B + 80 ≤ NE`, `B ≤ No` | `frontier_le_three_of` | proved (Barina-only instance `BarinaFrontier.frontier_le_three_barina`, `B ≤ 9.5·10^8`) |
-/

namespace Syracuse.MRunsDichotomy

open Finset Syracuse.MRuns Syracuse.MRunsExplicit

/-- On a cycle, the orbit point after `k ≤ o` steps reads the gap word rotated by `k`. -/
lemma gapWord_iterate {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {k : ℕ} (hk : k ≤ o) :
    gapWord (syr^[k] x) o = (gapWord x o).rotate k := by
  have h1 := Repeat.gapWord_add x k (o - k)
  rw [Nat.add_sub_cancel' hk] at h1
  have h2 := Repeat.gapWord_add (syr^[k] x) (o - k) k
  rw [Nat.sub_add_cancel hk, ← Function.iterate_add_apply, Nat.sub_add_cancel hk, h.2.2] at h2
  have hl : (gapWord x k).length = k := gapWord_length x k
  rw [h2, h1, List.rotate_eq_drop_append_take (by simp), List.drop_left' hl, List.take_left' hl]

/-- **`T = 0` puts an orbit point on a base block's cycle.** -/
theorem T_zero_alt {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ}
    (hm : 1 ≤ m) (hp : ∀ i, p (i + m) = p i) (hne : ∀ i, p i ≠ [])
    (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ []) (R : ℕ)
    (hrot : gapWord x o ~r cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m)
    (hT : T (2 : ℤ) 3 (fun k => TwoBackground.bpow (p (R + k)) (a (R + k)))
      (fun k => Acoef p m (R + k)) m = 0) :
    ∃ y : ℤ, IsSyrCycle y o ∧ (∃ j, y = syr^[j] x) ∧ Dz (p R) * y = Sz (p R) := by
  have hk := key_identity (2 : ℤ) 3 (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) hm
    (D' := ∏ k ∈ range m, D (2 : ℤ) 3 (p k)) (A := fun k => Acoef p m (R + k))
    (fun i _ => Acoef_spec (a := a) hm hp (R + i))
  rw [hT, mul_zero, zero_add] at hk
  -- the orbit point reading `W`
  obtain ⟨n, hn⟩ := hrot
  have ho : 0 < o := h.1
  set y := syr^[n % o] x
  have hy : IsSyrCycle y o := Repeat.isSyrCycle_iterate h _
  have hgy : gapWord y o = cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m := by
    have hmod := List.rotate_mod (gapWord x o) n
    rw [gapWord_length] at hmod
    rw [gapWord_iterate h (Nat.mod_lt _ ho).le, hmod, hn]
  have hceq := hy.cycle_equation
  rw [hgy] at hceq
  -- `D(W) ≠ 0`
  have hWne : cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m ≠ [] := by
    intro h0
    have hl : (TwoBackground.bpow (p (R + 0)) (a (R + 0))).length ≤
        (cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m).length := by
      rw [cat_length, Os]
      exact single_le_sum (f := fun i => (TwoBackground.bpow (p (R + i)) (a (R + i))).length)
        (fun _ _ => Nat.zero_le _) (by simp; omega)
    rw [h0, List.length_nil] at hl
    have := List.length_pos_of_ne_nil (hne' (R + 0))
    omega
  have hDW := StdPairs.Dz_ne_zero hWne
  -- `D'·y = A_R`
  have hDy : (∏ k ∈ range m, D (2 : ℤ) 3 (p k)) * y = Acoef p m R := by
    have e : Dz (cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m) *
        ((∏ k ∈ range m, D (2 : ℤ) 3 (p k)) * y - Acoef p m (R + 0)) = 0 := by
      have : (∏ k ∈ range m, D (2 : ℤ) 3 (p k)) *
          Sz (cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m) =
          Acoef p m (R + 0) * Dz (cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m) := hk
      rw [← hceq] at this
      linear_combination this
    have := (mul_eq_zero.1 e).resolve_left hDW
    simpa using sub_eq_zero.1 this
  -- cancel the other `D`s
  have hmem : R % m ∈ range m := mem_range.2 (Nat.mod_lt _ (by omega))
  rw [← mul_prod_erase _ _ hmem, Acoef, ← p_mod hm hp R] at hDy
  have hP : ∏ k ∈ (range m).erase (R % m), D (2 : ℤ) 3 (p k) ≠ 0 :=
    prod_ne_zero_iff.2 (fun k _ => StdPairs.Dz_ne_zero (hne k))
  refine ⟨y, hy, ⟨n % o, rfl⟩, ?_⟩
  have e : (∏ k ∈ (range m).erase (R % m), D (2 : ℤ) 3 (p k)) * (Dz (p R) * y - Sz (p R)) = 0 := by
    simp only [Dz, Sz]; linear_combination hDy
  have := (mul_eq_zero.1 e).resolve_left hP
  linarith

/-- **Dichotomy for up to three runs of any blocks**, given Ellison. -/
theorem mruns_dichotomy (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    (hrot : gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m)
    (hx : (cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum ∉ CycleLiterature.ellisonExceptions) :
    (∃ R : ℕ, ∃ y : ℤ, IsSyrCycle y o ∧ (∃ j, y = syr^[j] x) ∧ Dz (p R) * y = Sz (p R)) ∨
      ((1 - 1 / (10 * Real.log 2)) - (1 - 1 / Reach.σ (Real.logb 2 3) 3)) *
        max ((cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum : ℝ)
          (Real.logb 2 3 * (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length) ≤
        (6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) + 1 + Real.logb 2 3 := by
  set Q : ℕ → Word := fun i => TwoBackground.bpow (p i) (a i)
  have hQ : ∀ i, Q (i + m) = Q i := fun i => by simp only [Q, hp, ha]
  have hQpos : ∀ i, (Q i).Pos := fun i => StdPairs.pos_bpow (hpos i) (a i)
  by_cases hall : ∀ R, T (2 : ℤ) 3 (fun k => Q (R + k)) (fun k => Acoef p m (R + k)) m ≠ 0
  · right
    -- `m = 1` has `T ≡ 0`
    have hm2 : 2 ≤ m := by
      by_contra hc
      obtain rfl : m = 1 := by omega
      apply hall 0
      simp [T, Nat.mod_one]
    exact (MRuns.mruns_ellison hEl h hm hm3 hQ hQpos hne' hrot
      (fun i => Acoef_spec (a := a) hm hp i) (Acoef_period hp) (Acoef_diff_le hm2 hp hpos) hall hx).2
  · left
    push_neg at hall
    obtain ⟨R, hR⟩ := hall
    have hrotR : gapWord x o ~r cat (fun k => Q (R + k)) m := hrot.trans (rot_cat Q hm hQ R).symm
    exact ⟨R, T_zero_alt h hm hp hne hne' R hrotR hR⟩

/-- **Frontier: at most three runs, for any cycle bounds** `CycleBounds No NE`: base weight `B` with
`120 B + 80 ≤ NE` and `B ≤ No`. -/
theorem frontier_le_three_of (hEl : CycleLiterature.Ellison1971) {No NE : ℕ}
    (hCB : CycleLength.CycleBounds No NE)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    (hsmall : 120 * (∑ k ∈ range m, (p k).sum) + 80 ≤ NE)
    (hBo : ∑ k ∈ range m, (p k).sum ≤ No) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) := by
  intro hrot
  have hE := (hCB x o hx h hx1).2
  rw [hrot.perm.sum_eq] at hE
  rcases mruns_dichotomy hEl h hm hm3 hp ha hpos hne hne' hrot
    (Frontier.not_mem_exceptions (by omega)) with ⟨R, y, hy, ⟨j, rfl⟩, hDy⟩ | hb
  · -- an orbit point on a base block's cycle: its period is at most `B`
    have hy0 : 0 < syr^[j] x := CycleLiterature.syr_iterate_pos hx j
    have hdvd : Dz (p R) ∣ Sz (p R) := ⟨_, hDy.symm⟩
    obtain ⟨hc, -⟩ := CycleLiterature.isSyrCycle_of_dvd (hpos R) (hne R) hdvd
    have hval : Sz (p R) / Dz (p R) = syr^[j] x := by
      rw [← hDy, Int.mul_ediv_cancel_left _ (StdPairs.Dz_ne_zero (hne R))]
    rw [hval] at hc
    have hy1 : syr^[j] x ≠ 1 := by
      intro h1
      -- `x` lies on the orbit of `syr^[j] x = 1`
      have hfix : ∀ t, syr^[t] (1 : ℤ) = 1 := fun t =>
        Function.iterate_fixed CycleLiterature.gap_syr_one.2 t
      have hback : syr^[o * (j + 1) - j] (syr^[j] x) = x := by
        rw [← Function.iterate_add_apply, show o * (j + 1) - j + j = o * (j + 1) by
          have : j ≤ o * (j + 1) := by nlinarith [h.1]
          omega]
        rw [Function.iterate_mul]
        exact Function.iterate_fixed h.2.2 _
      rw [h1, hfix] at hback
      exact hx1 hback.symm
    have hper := (hCB _ _ hy0 hc hy1).1
    have hlen : (p R).length ≤ (p R).sum := CycleLiterature.length_le_sum (hpos R)
    have hsumR : (p R).sum ≤ ∑ k ∈ range m, (p k).sum := by
      rw [p_mod hm hp R]
      exact single_le_sum (f := fun k => (p k).sum) (fun _ _ => Nat.zero_le _)
        (mem_range.2 (Nat.mod_lt _ (by omega)))
    omega
  · -- the bound
    have hmg := margin
    set M := max ((cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum : ℝ)
      (Real.logb 2 3 * (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length)
    have hM : (NE : ℝ) < M := lt_of_lt_of_le (by exact_mod_cast hE) (le_max_left _ _)
    have hl3 : Real.logb 2 3 < 2 := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]; norm_num
    have hBr : 20 * (((6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) : ℝ) + 3) ≤ NE := by
      exact_mod_cast (show 20 * ((6 * (∑ k ∈ range m, (p k).sum) + 1) + 3) ≤ NE by omega)
    have hMpos : 0 < M := lt_of_le_of_lt (Nat.cast_nonneg _) hM
    have := mul_lt_mul_of_pos_right hmg hMpos
    linarith

/-- **Frontier: at most three runs.** Given Ellison, Barina and Hercher's Corollary 29, no nontrivial
positive cycle is a rotation of `p₀^{a₀} ⋯ p_{m-1}^{a_{m-1}}` (`1 ≤ m ≤ 3`) over positive nonempty base
blocks of total weight `B ≤ 10^9`. -/
theorem frontier_le_three (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    (hH29 : CycleLiterature.Hercher2023Cor29) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hx1 : x ≠ 1) {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    (hsmall : ∑ k ∈ range m, (p k).sum ≤ 1000000000) :
    ¬ (gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m) :=
  frontier_le_three_of hEl (CycleLength.cycleBounds_hercher hB hH29) h hx hx1 hm hm3 hp ha hpos hne
    hne' (by omega) (by omega)

end Syracuse.MRunsDichotomy
