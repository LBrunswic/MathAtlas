import Syracuse.Approaches.DPairs

/-!
# The `{1, d}` trees for every `d`: positive side closed, negative side bounded

`DPairs.no_cycle_dpair` excludes two-run cycle words over a `d`-pair once `E ≥ 20(d - 1)`. Below that
bound the word has few big gaps. All its letters are `1` or `d` (`DPair.letters`), so with `t` gaps equal
to `d`, `E = o + (d-1)t` (`sum_add_numBlocks`). Then:

* **positive cycles:** the sandwich `1000 E < 1740 o` and `E < 20(d-1) + 28` force `t ≤ 20`. Simons and
  de Weger exclude positive `m`-cycles for `m ≤ 68`, so **no nontrivial positive cycle lies on a two-run
  word over any `d`-pair, for any `d`** (`pos_dpair_cycles`, given Ellison and Simons–de Weger 2005).
  Only `t ≤ 20` is used, so `NoMCyclesUpTo 20` suffices (`pos_dpair_cycles_of`);
* **negative cycles:** the sign bound `1000 E < 1585 o` forces `t ≤ 7`. `t ≤ 1` (circuits) and `t = 2`
  (equal big gaps) are closed, and for `d ≥ 3` they would need the letter `2`. So a negative cycle on a
  two-run word over a `d`-pair (`d ≥ 3`) has **between 3 and 7 big gaps, all equal to `d`, and
  `E < 20(d - 1)`** (`neg_dpair_residual`). For `d = 3` the tree is closed outright
  (`DPairs.dpair_three_cycles`).

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| letters of a `d`-pair are `1` or `d`; `1 ∈ u`, `d ∈ v` | `DPair.letters` | proved |
| a word over `{1, d}` with `t` letters `d` has `E + t = o + d t` | `sum_add_numBlocks` | proved |
| the minimal-period word has at most as many blocks | `numBlocks_minimal_le` | proved |
| a positive cycle with at most `M` blocks is trivial, given `NoMCyclesUpTo M` | `eq_one_of_numBlocks_le` | proved |
| no nontrivial positive cycle on a two-run word over any `d`-pair | `pos_dpair_cycles_of`, `pos_dpair_cycles` | proved (conditional on Ellison + `NoMCyclesUpTo 20` / Simons–de Weger 2005) |
| `-5`, `-7` cycles use the letter `2`; `-1` uses only `1` | `two_mem_of_neg_five_seven`, `gapWord_neg_one` | proved |
| negative cycles on two-run words over a `d`-pair (`d ≥ 3`): `3 ≤ t ≤ 7`, `E < 20(d-1)` | `neg_dpair_residual` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.DTrees

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs Syracuse.DPairs

/-- **Letters of a `d`-pair.** Every letter is `1` or `d`; `u` contains `1` and `v` contains `d`. -/
theorem DPair.letters {d : ℕ} {u v : Word} (h : DPair d u v) :
    (∀ e ∈ u, e = 1 ∨ e = d) ∧ (∀ e ∈ v, e = 1 ∨ e = d) ∧ 1 ∈ u ∧ d ∈ v := by
  induction h with
  | base => exact ⟨by simp, by simp, by simp, by simp⟩
  | @left u v _ ih =>
    obtain ⟨hu, hv, h1, hd⟩ := ih
    refine ⟨hu, fun e he => ?_, h1, by simp [hd]⟩
    simp only [List.mem_append] at he; rcases he with he | he
    · exact hu e he
    · exact hv e he
  | @right u v _ ih =>
    obtain ⟨hu, hv, h1, hd⟩ := ih
    refine ⟨fun e he => ?_, hv, by simp [h1], hd⟩
    simp only [List.mem_append] at he; rcases he with he | he
    · exact hu e he
    · exact hv e he

/-- Letters of a power are letters of the word. -/
lemma mem_of_mem_bpow {u : Word} {a e : ℕ} (he : e ∈ bpow u a) : e ∈ u := by
  simp only [bpow, CocycleCombine.wpow, List.mem_flatten, List.mem_replicate] at he
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := he
  exact hl

/-- A letter of `u` is a letter of `u^a` for `a ≥ 1`. -/
lemma mem_bpow_of_mem {u : Word} {a e : ℕ} (ha : 1 ≤ a) (he : e ∈ u) : e ∈ bpow u a := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  rw [Renormalize.bpow_succ]; exact List.mem_append_left _ he

/-- **Counting.** A word over `{1, d}` (`d ≥ 2`) with `t` letters `d` has `E + t = o + d·t`. -/
theorem sum_add_numBlocks {d : ℕ} (hd : 2 ≤ d) {w : Word} (hw : ∀ e ∈ w, e = 1 ∨ e = d) :
    w.sum + CycleLiterature.numBlocks w = w.length + d * CycleLiterature.numBlocks w := by
  induction w with
  | nil => simp [CycleLiterature.numBlocks]
  | cons e w ih =>
    have ih := ih (fun f hf => hw f (List.mem_cons_of_mem e hf))
    simp only [CycleLiterature.numBlocks, List.sum_cons, List.length_cons, List.countP_cons] at ih ⊢
    rcases hw e List.mem_cons_self with rfl | rfl
    · simp; omega
    · simp [show 2 ≤ e from hd]; rw [Nat.mul_add, Nat.mul_one]; omega

/-- The word over the minimal period has at most as many blocks as the word over any period. -/
theorem numBlocks_minimal_le {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    CycleLiterature.numBlocks (gapWord a (Function.minimalPeriod syr a)) ≤
      CycleLiterature.numBlocks (gapWord a o) := by
  set p := Function.minimalPeriod syr a
  have hpo : p ≤ o := Function.IsPeriodicPt.minimalPeriod_le h.1 h.2.2
  have hsplit := Repeat.gapWord_add a p (o - p)
  rw [Nat.add_sub_cancel' hpo] at hsplit
  rw [hsplit]
  simp only [CycleLiterature.numBlocks, List.countP_append]
  omega

/-- **From an `m`-cycle bound.** Given `NoMCyclesUpTo M`, a positive cycle whose gap word has at most
`M` gaps `≥ 2` is the trivial cycle. -/
theorem eq_one_of_numBlocks_le {M : ℕ} (hM : CycleLiterature.NoMCyclesUpTo M) {a : ℤ} {o : ℕ}
    (h : IsSyrCycle a o) (ha : 0 < a) (hb : CycleLiterature.numBlocks (gapWord a o) ≤ M) : a = 1 := by
  have hper : Function.IsPeriodicPt syr o a := h.2.2
  set p := Function.minimalPeriod syr a
  have hp : IsSyrCycle a p :=
    ⟨hper.minimalPeriod_pos h.1, h.2.1, Function.isPeriodicPt_minimalPeriod syr a⟩
  have hm : CycleLiterature.IsMCycle a (CycleLiterature.numBlocks (gapWord a p)) :=
    ⟨ha, p, ⟨hp, fun j hj hjp =>
      Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) hjp⟩, rfl⟩
  exact hM a _ (CycleLiterature.one_le_numBlocks hp ha) ((numBlocks_minimal_le h).trans hb) hm

/-- The gap word of a cycle on a two-run word over a `d`-pair uses only the letters `1` and `d`, and
contains both. -/
lemma word_letters {d : ℕ} {u v : Word} (hst : DPair d u v) {x : ℤ} {o : ℕ} {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hw : gapWord x o ~r bpow u a ++ bpow v b) :
    (∀ e ∈ gapWord x o, e = 1 ∨ e = d) ∧ 1 ∈ gapWord x o ∧ d ∈ gapWord x o := by
  obtain ⟨hu, hv, h1, hd⟩ := DPair.letters hst
  refine ⟨fun e he => ?_, ?_, ?_⟩
  · have := hw.perm.subset he
    simp only [List.mem_append] at this; rcases this with h' | h'
    · exact hu e (mem_of_mem_bpow h')
    · exact hv e (mem_of_mem_bpow h')
  · exact hw.symm.perm.subset (List.mem_append_left _ (mem_bpow_of_mem ha h1))
  · exact hw.symm.perm.subset (List.mem_append_right _ (mem_bpow_of_mem hb hd))

/-! ## Positive cycles: every `d` -/

/-- **Positive cycles, every `d`.** Given Ellison and `NoMCyclesUpTo 20`, no positive cycle has a gap
word that is a rotation of `u^a v^b` for a `d`-pair (`d ≥ 2`, `a, b ≥ 1`). -/
theorem pos_dpair_cycles_of (hEl : CycleLiterature.Ellison1971) (hM : CycleLiterature.NoMCyclesUpTo 20)
    {d : ℕ} (hd : 2 ≤ d) {u v : Word} (hst : DPair d u v) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hx : 0 < x) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hw : gapWord x o ~r bpow u a ++ bpow v b) :
    False := by
  obtain ⟨hlet, h1, -⟩ := word_letters hst ha hb hw
  have hx1 : x ≠ 1 := by
    rintro rfl
    have := Circuits.gapWord_one o 1 h1
    omega
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  set E := (gapWord x o).sum
  by_cases hbig : 20 * j ≤ E ∧ 28 ≤ E
  · exact no_cycle_dpair hEl (by omega) hst h ha hb hw (Frontier.not_mem_exceptions hbig.2) hbig.1
  have hsmall : E < 20 * j + 28 := by omega
  -- counting
  have hcnt := sum_add_numBlocks hd hlet
  rw [gapWord_length] at hcnt
  set t := CycleLiterature.numBlocks (gapWord x o)
  have hEo : E = o + j * t := by
    have : E + t = o + (j + 1) * t := hcnt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  -- the sandwich
  have hsand := Circuits.sandwich_linear h.1 (Limits.two_pow_mul_three_pow_le h hx hx1)
  have ht : t ≤ 20 := by
    by_contra hc
    have hjt : j * 21 ≤ j * t := Nat.mul_le_mul_left j (by omega)
    have hj1 : 1 ≤ j := by omega
    generalize j * t = P at hEo hjt
    omega
  exact hx1 (eq_one_of_numBlocks_le hM h hx ht)

/-- **Positive cycles, every `d`, from the literature.** Given Ellison and Simons–de Weger 2005
(no nontrivial positive `m`-cycle for `m ≤ 68`), no positive cycle lies on a two-run word over any
`d`-pair. -/
theorem pos_dpair_cycles (hEl : CycleLiterature.Ellison1971)
    (hSdW : CycleLiterature.SimonsDeWeger2005) {d : ℕ} (hd : 2 ≤ d) {u v : Word} (hst : DPair d u v)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hw : gapWord x o ~r bpow u a ++ bpow v b) : False :=
  pos_dpair_cycles_of hEl (CycleLiterature.NoMCyclesUpTo.mono hSdW (by norm_num)) hd hst h hx ha hb hw

/-! ## Negative cycles: the residual -/

/-- The cycles `-5 → -7` use the letter `2`. -/
lemma two_mem_of_neg_five_seven {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : x = -5 ∨ x = -7) :
    2 ∈ gapWord x o := by
  have h5 : gap (-5) = 1 ∧ syr (-5) = -7 :=
    CycleLiterature.gap_syr_of_eq (k := 1) (by norm_num) (by decide)
  have h7 : gap (-7) = 2 ∧ syr (-7) = -5 :=
    CycleLiterature.gap_syr_of_eq (k := 2) (by norm_num) (by decide)
  obtain ⟨n, rfl⟩ : ∃ n, o = n + 1 := ⟨o - 1, by have := h.1; omega⟩
  rcases hx with rfl | rfl
  · -- `o ≥ 2`, since `syr (-5) = -7 ≠ -5`
    rcases n with _ | n
    · exfalso; have := h.2.2; simp [h5.2] at this
    · simp [gapWord, h5.1, h5.2, h7.1]
  · simp [gapWord, h7.1]

/-- The fixed point `-1` uses only the letter `1`. -/
lemma gapWord_neg_one (o : ℕ) : ∀ e ∈ gapWord (-1) o, e = 1 := by
  induction o with
  | zero => simp [gapWord]
  | succ o ih =>
    intro e he
    simp only [gapWord, CycleLiterature.gap_syr_neg_one.2, List.mem_cons] at he
    rcases he with rfl | he
    · exact CycleLiterature.gap_syr_neg_one.1
    · exact ih e he

/-- **The negative residual.** Given Ellison, a negative cycle on a two-run word over a `d`-pair
(`d ≥ 3`) has between `3` and `7` gaps `≥ 2`, all equal to `d`, and `E < 20(d - 1)`. -/
theorem neg_dpair_residual (hEl : CycleLiterature.Ellison1971) {d : ℕ} (hd : 3 ≤ d) {u v : Word}
    (hst : DPair d u v) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : x < 0) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hw : gapWord x o ~r bpow u a ++ bpow v b) :
    3 ≤ CycleLiterature.numBlocks (gapWord x o) ∧ CycleLiterature.numBlocks (gapWord x o) ≤ 7 ∧
      (gapWord x o).sum < 20 * (d - 1) := by
  obtain ⟨hlet, h1, hdm⟩ := word_letters hst ha hb hw
  -- the known small cycles are impossible: `-1` has no letter `d`, `-5`, `-7` need the letter `2`
  have known : ¬ (x = -1 ∨ x = -5 ∨ x = -7) := by
    rintro (rfl | hx')
    · have := gapWord_neg_one o d hdm; omega
    · have := hlet 2 (two_mem_of_neg_five_seven h hx'); omega
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  set E := (gapWord x o).sum
  have hE : E < 20 * j := by
    by_contra hc
    exact no_cycle_dpair hEl (by omega) hst h ha hb hw (Frontier.not_mem_exceptions (by omega))
      (by omega)
  have hcnt := sum_add_numBlocks (by omega) hlet
  rw [gapWord_length] at hcnt
  set t := CycleLiterature.numBlocks (gapWord x o) with ht_def
  have hEo : E = o + j * t := by
    have : E + t = o + (j + 1) * t := hcnt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  -- the sign
  have hDn := SignedCycles.Dz_neg h hx
  have hsgn : 1000 * E < 1585 * o := by
    apply SignedCycles.sign_linear
    have : (2 : ℤ) ^ E < 3 ^ o := by
      simp only [Dz, D, gapWord_length] at hDn; linarith
    exact_mod_cast this
  refine ⟨?_, ?_, by simpa using hE⟩
  · by_contra hc
    rcases Nat.lt_or_ge t 2 with ht1 | ht2
    · rcases SignedCycles.few_blocks_cycles hEl h (by omega) with h' | h'
      · omega
      · exact known h'
    · -- `t = 2`: both big gaps equal `d`
      have heq : ∀ e ∈ gapWord x o, ∀ f ∈ gapWord x o, 2 ≤ e → 2 ≤ f → e = f := by
        intro e he f hf h2e h2f
        rcases hlet e he with rfl | rfl <;> rcases hlet f hf with rfl | rfl <;> omega
      rcases EqualTwoCycles.equal_two_blocks hEl h (by omega) heq with h' | h'
      · omega
      · exact known (Or.inr h')
  · by_contra hc
    have hjt : j * 8 ≤ j * t := Nat.mul_le_mul_left j (by omega)
    generalize j * t = P at hEo hjt
    omega

end Syracuse.DTrees
