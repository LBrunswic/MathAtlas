import Syracuse.Approaches.NegTwoCycles

/-!
# Closing the `{1, d}` trees one `d` at a time

`DPairs.no_cycle_dpair` leaves, for each `d`, only the two-run words over `d`-pairs with
`E < 20(d - 1)`. This file turns that finite region into a single Boolean check per `d`:

* `pairOk N u v` tests every `u^a v^b` with `a, b ≥ 1` and `E ≤ N`, looping only over admissible
  exponents (`a ≤ N / |u|`, `b ≤ (N - a|u|)/|v|`). Its soundness is `pairOk_sound`.
* `treeOk N d` runs `pairOk` over the enumeration `DPairs.genD` of all `d`-pairs with total sum
  `≤ N`, which is complete (`DPairs.mem_genD`).
* `dpair_cycles_of_check`: if `treeOk (20(d-1)) d = true` (`d ≥ 3`), then, given Ellison, no cycle of
  either sign lies on any two-run word over a `d`-pair.

The checks for `d = 4, 5, 6, 7` run in the kernel (`decide +kernel`). Together with
`DPairs.dpair_three_cycles` this closes the **trees over `{1,3}`, …, `{1,7}`** for both signs
(`dpair_cycles_le_seven`).

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| the exponent-bounded check is sound | `pairOk_sound` | proved |
| a passing tree check closes the `{1,d}` tree (given Ellison) | `dpair_cycles_of_check` | proved (conditional on `Ellison1971`) |
| the checks for `d = 4, 5, 6, 7` | `check_four`, …, `check_seven` | proved (`decide +kernel`) |
| no cycle (either sign) on two-run words over `d`-pairs, `3 ≤ d ≤ 7` | `dpair_cycles_le_seven` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.DTreeChecks

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs Syracuse.DPairs

/-- Every `u^a v^b` with `a, b ≥ 1` and `E ≤ N` has `D ∤ S` (exponents looped only where admissible). -/
def pairOk (N : ℕ) (u v : Word) : Bool :=
  (List.range (N / u.sum + 1)).all fun a =>
    (List.range ((N - a * u.sum) / v.sum + 1)).all fun b =>
      a == 0 || b == 0 || Sz (bpow u a ++ bpow v b) % Dz (bpow u a ++ bpow v b) != 0

/-- **Soundness of `pairOk`.** -/
lemma pairOk_sound {N : ℕ} {u v : Word} (h : pairOk N u v = true) (hu : 1 ≤ u.sum)
    (hv : 1 ≤ v.sum) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hE : a * u.sum + b * v.sum ≤ N) :
    Sz (bpow u a ++ bpow v b) % Dz (bpow u a ++ bpow v b) ≠ 0 := by
  simp only [pairOk, List.all_eq_true, List.mem_range] at h
  have ha' : a < N / u.sum + 1 := by
    have : a ≤ N / u.sum := (Nat.le_div_iff_mul_le hu).2 (by omega)
    omega
  have hb' : b < (N - a * u.sum) / v.sum + 1 := by
    have : b ≤ (N - a * u.sum) / v.sum := (Nat.le_div_iff_mul_le hv).2 (by omega)
    omega
  have := h a ha' b hb'
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  rcases this with (h0 | h0) | h0
  · omega
  · omega
  · exact h0

/-- `pairOk` over every `d`-pair with total sum `≤ N`. -/
def treeOk (N d : ℕ) : Bool := (genD N N [1] [d]).all fun pq => pairOk N pq.1 pq.2

/-- **A passing check closes the `{1, d}` tree.** Given Ellison and `treeOk (20(d-1)) d = true`
(`d ≥ 3`), no cycle of either sign has a gap word that is a rotation of `u^a v^b` for a `d`-pair. -/
theorem dpair_cycles_of_check (hEl : CycleLiterature.Ellison1971) {d : ℕ} (hd : 3 ≤ d)
    (hchk : treeOk (20 * (d - 1)) d = true) {u v : Word} (hst : DPair d u v) {x : ℤ} {o : ℕ}
    (h : IsSyrCycle x o) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hw : gapWord x o ~r bpow u a ++ bpow v b) : False := by
  obtain ⟨hus, hvs⟩ := dpair_sums (by omega) hst
  have hsw : (gapWord x o).sum = a * u.sum + b * v.sum := by
    rw [hw.perm.sum_eq, List.sum_append]; simp [bpow, CocycleCombine.wpow_sum]
  have hau : u.sum ≤ a * u.sum := Nat.le_mul_of_pos_left _ (by omega)
  have hbv : v.sum ≤ b * v.sum := Nat.le_mul_of_pos_left _ (by omega)
  by_cases hE : (gapWord x o).sum < 20 * (d - 1)
  · have hle : u.sum + v.sum ≤ 20 * (d - 1) := by omega
    have hmem := genD_mono (20 * (d - 1)) hle _ _ (mem_genD (by omega) hst hle)
    have hpair : pairOk (20 * (d - 1)) u v = true := by
      simp only [treeOk, List.all_eq_true] at hchk
      exact hchk (u, v) hmem
    exact pairOk_sound hpair hus hvs ha hb (by omega)
      (Int.emod_eq_zero_of_dvd (dvd_S_of_rotated h hw))
  · obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
    exact no_cycle_dpair hEl (j := j) (by omega) hst h ha hb hw
      (Frontier.not_mem_exceptions (by omega)) (by omega)

theorem check_four : treeOk (20 * (4 - 1)) 4 = true := by decide +kernel
theorem check_five : treeOk (20 * (5 - 1)) 5 = true := by decide +kernel
theorem check_six : treeOk (20 * (6 - 1)) 6 = true := by decide +kernel
theorem check_seven : treeOk (20 * (7 - 1)) 7 = true := by decide +kernel

/-- **The trees over `{1,3}`, …, `{1,7}` are closed.** Given Ellison, no cycle of either sign has a gap
word that is a rotation of `u^a v^b` for a `d`-pair with `3 ≤ d ≤ 7`. -/
theorem dpair_cycles_le_seven (hEl : CycleLiterature.Ellison1971) {d : ℕ} (hd3 : 3 ≤ d)
    (hd7 : d ≤ 7) {u v : Word} (hst : DPair d u v) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hw : gapWord x o ~r bpow u a ++ bpow v b) : False := by
  interval_cases d
  · exact dpair_three_cycles hEl hst h ha hb hw
  · exact dpair_cycles_of_check hEl (by norm_num) check_four hst h ha hb hw
  · exact dpair_cycles_of_check hEl (by norm_num) check_five hst h ha hb hw
  · exact dpair_cycles_of_check hEl (by norm_num) check_six hst h ha hb hw
  · exact dpair_cycles_of_check hEl (by norm_num) check_seven hst h ha hb hw

end Syracuse.DTreeChecks
