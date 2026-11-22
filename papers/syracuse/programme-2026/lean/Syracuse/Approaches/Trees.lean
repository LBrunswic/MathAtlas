import Syracuse.Approaches.DTreeChecks

/-!
# Two runs over any Christoffel-type tree: an effective bound

The Stern–Brocot moves `(u, v) ↦ (u, uv), (uv, v)` multiply the wedge core
`C(u, v) = D(u)S(v) - D(v)S(u)` by `X^{|u|}` or `Y^{len v}`, from **any** root
(`StdPairs.core_left`, `core_right`). So in the tree grown from a root pair `(u₀, v₀)` every core is
`2^i 3^k C(u₀, v₀)` (`core_tree`). The two block divisibilities then give
`|D|² ≤ C(u₀,v₀)² |D(u^a)| |D(v^b)| < C(u₀,v₀)² 3^E`, and Ellison makes this impossible once
`|C(u₀, v₀)|^{20} ≤ 2^E` (`no_cycle_tree`):

> Given Ellison, for every root pair of positive nonempty words with `C(u₀, v₀) ≠ 0`, a cycle of either
> sign on a two-run word `u^a v^b` over the tree from `(u₀, v₀)` has `E < 20 log₂ |C(u₀, v₀)|`, or `E` is
> one of Ellison's exceptions.

This is an **effective** two-run rung for arbitrary blocks. Levin's gcd theorem gives the `m`-run rung
only ineffectively. The root itself is in its tree, so for any fixed non-commuting blocks `u₀, v₀` only
the finitely many words `u₀^a v₀^b` with `E < 20 log₂ |C|` can carry a cycle (`no_cycle_two_blocks`). The
standard pairs (`C = -2`), the `{1,d}` trees (`C = -2(2^{d-1} - 1)`) and the blocks `(1112, 114)` of
`-17` (`C = -3336`, so `E < 234` on `(1112)^a (114)^b`) are instances.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| the tree grown from a root pair | `Tree` | definition |
| every core in the tree is `2^i 3^k C(u₀, v₀)` | `core_tree` | proved |
| trees of positive nonempty roots consist of positive nonempty words | `Tree.pos` | proved |
| no cycle (either sign) on `u^a v^b` over the tree once `|C(u₀,v₀)|^{20} ≤ 2^E`, `E` not exceptional | `no_cycle_tree` | proved (conditional on `Ellison1971`) |
| fixed blocks: no cycle on `u₀^a v₀^b` once `|C|^{20} ≤ 2^E` | `no_cycle_two_blocks` | proved (conditional on `Ellison1971`) |
| the core of the `-17` blocks | `core_neg_seventeen_blocks` | proved (`decide`) |
-/

namespace Syracuse.Trees

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

/-- The tree grown from the root pair `(u₀, v₀)` by the Stern–Brocot moves. -/
inductive Tree (u₀ v₀ : Word) : Word → Word → Prop
  | base : Tree u₀ v₀ u₀ v₀
  | left {u v : Word} : Tree u₀ v₀ u v → Tree u₀ v₀ u (u ++ v)
  | right {u v : Word} : Tree u₀ v₀ u v → Tree u₀ v₀ (u ++ v) v

/-- **Cores along the tree.** Every core is `2^i 3^k` times the root core. -/
theorem core_tree {u₀ v₀ u v : Word} (h : Tree u₀ v₀ u v) :
    ∃ i k : ℕ, core (2 : ℤ) 3 u v = 2 ^ i * 3 ^ k * core (2 : ℤ) 3 u₀ v₀ := by
  induction h with
  | base => exact ⟨0, 0, by ring⟩
  | @left u v _ ih =>
    obtain ⟨i, k, hik⟩ := ih
    exact ⟨i + u.sum, k, by rw [core_left, hik]; ring⟩
  | @right u v _ ih =>
    obtain ⟨i, k, hik⟩ := ih
    exact ⟨i, k + v.length, by rw [core_right, hik]; ring⟩

/-- Trees of positive nonempty roots consist of positive nonempty words. -/
theorem Tree.pos {u₀ v₀ : Word} (hu₀ : u₀.Pos) (hv₀ : v₀.Pos) (hu₀0 : u₀ ≠ []) (hv₀0 : v₀ ≠ [])
    {u v : Word} (h : Tree u₀ v₀ u v) : u.Pos ∧ v.Pos ∧ u ≠ [] ∧ v ≠ [] := by
  induction h with
  | base => exact ⟨hu₀, hv₀, hu₀0, hv₀0⟩
  | @left u v _ ih =>
    obtain ⟨hu, hv, hu0, -⟩ := ih
    exact ⟨hu, fun d hd => by simp only [List.mem_append] at hd; rcases hd with hd | hd
                              · exact hu d hd
                              · exact hv d hd, hu0, by simp [hu0]⟩
  | @right u v _ ih =>
    obtain ⟨hu, hv, hu0, hv0⟩ := ih
    exact ⟨fun d hd => by simp only [List.mem_append] at hd; rcases hd with hd | hd
                          · exact hu d hd
                          · exact hv d hd, hv, by simp [hu0], hv0⟩

/-- **Two runs over any tree.** Given Ellison, no cycle of either sign has a gap word that is a rotation
of `u^a v^b` (`(u, v)` in the tree of a positive nonempty root with nonzero core, `a, b ≥ 1`) once
`|C(u₀, v₀)|^{20} ≤ 2^E` and `E` is outside Ellison's exceptional set. -/
theorem no_cycle_tree (hEl : CycleLiterature.Ellison1971) {u₀ v₀ : Word} (hu₀ : u₀.Pos)
    (hv₀ : v₀.Pos) (hu₀0 : u₀ ≠ []) (hv₀0 : v₀ ≠ []) (hC : core (2 : ℤ) 3 u₀ v₀ ≠ 0) {u v : Word}
    (hst : Tree u₀ v₀ u v) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hw : gapWord x o ~r bpow u a ++ bpow v b)
    (hx : (gapWord x o).sum ∉ CycleLiterature.ellisonExceptions)
    (hE : |core (2 : ℤ) 3 u₀ v₀| ^ 20 ≤ 2 ^ (gapWord x o).sum) : False := by
  obtain ⟨hu, hv, hu0, hv0⟩ := hst.pos hu₀ hv₀ hu₀0 hv₀0
  set C := core (2 : ℤ) 3 u₀ v₀ with hC_def
  set w := bpow u a ++ bpow v b with hw_def
  have hua : (bpow u a).Pos := pos_bpow hu a
  have hvb : (bpow v b).Pos := pos_bpow hv b
  have hua0 : bpow u a ≠ [] := by
    intro h0; have := congrArg List.length h0
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hu0 h1
  have hvb0 : bpow v b ≠ [] := by
    intro h0; have := congrArg List.length h0
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hv0 h1
  have hne : w ≠ [] := by simp [w, hua0]
  have hwpos : w.Pos := fun d hd => by
    simp only [w, List.mem_append] at hd; rcases hd with hd | hd
    · exact hua d hd
    · exact hvb d hd
  have hsum0 : w.sum ≠ 0 := by
    have := CycleLiterature.length_le_sum hwpos
    have : 0 < w.length := List.length_pos_of_ne_nil hne
    omega
  obtain ⟨hV, hU⟩ := dvd_of_cycle_block h hw hne hsum0
  obtain ⟨i, k, hc⟩ := core_tree hst
  have hcop := isCoprime_six hne hsum0
  have strip : ∀ c : ℤ, Dz w ∣ core (2 : ℤ) 3 u v * c → Dz w ∣ C * c := by
    intro c hdc
    rw [hc, mul_assoc] at hdc
    exact CocycleCombine.dvd_of_isCoprime_six_of_dvd hcop _ _ hdc
  have dU := strip _ hU
  have dV := strip _ hV
  have hCpos : 0 < |C| := abs_pos.2 hC
  have bound : ∀ y : Word, y.Pos → y ≠ [] → Dz w ∣ C * Dz y → |Dz w| < |C| * 3 ^ y.sum := by
    intro y hy hy0 hdy
    have hy1 := Dz_ne_zero hy0
    have hpos : 0 < |C| * |Dz y| := mul_pos hCpos (abs_pos.2 hy1)
    have hle : |Dz w| ≤ |C| * |Dz y| := by
      have hdv : |Dz w| ∣ |C| * |Dz y| := by
        rw [← abs_mul]; exact (abs_dvd_abs _ _).2 hdy
      exact Int.le_of_dvd hpos hdv
    calc |Dz w| ≤ |C| * |Dz y| := hle
      _ < |C| * 3 ^ y.sum := mul_lt_mul_of_pos_left (abs_Dz_lt hy) hCpos
  have bU := bound _ hua hua0 dU
  have bV := bound _ hvb hvb0 dV
  have hEw : w.sum = (bpow u a).sum + (bpow v b).sum := List.sum_append
  have hsq : |Dz w| ^ 2 < |C| ^ 2 * 3 ^ w.sum := by
    rw [hEw, sq, sq, pow_add]
    calc |Dz w| * |Dz w| < (|C| * 3 ^ (bpow u a).sum) * (|C| * 3 ^ (bpow v b).sum) :=
          mul_lt_mul'' bU bV (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  -- Ellison
  have hsw : (gapWord x o).sum = w.sum := hw.perm.sum_eq
  set E := w.sum
  have hEpos : 0 < E := Nat.pos_of_ne_zero hsum0
  have hopos : 0 < w.length := List.length_pos_of_ne_nil hne
  rw [hsw] at hx hE
  have hEl' := hEl E w.length hEpos hopos hx
  have hDr : |(2 : ℝ) ^ E - 3 ^ w.length| = ((|Dz w| : ℤ) : ℝ) := by
    simp only [Dz, D]; push_cast; rfl
  rw [hDr] at hEl'
  have hA0 : 0 ≤ (2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10) := by positivity
  have hlt := pow_lt_pow_left₀ hEl' hA0 (by norm_num : (2 : ℕ) ≠ 0)
  have hsqR : ((|Dz w| : ℤ) : ℝ) ^ 2 < ((|C| : ℤ) : ℝ) ^ 2 * 3 ^ E := by exact_mod_cast hsq
  have h1 := hlt.trans hsqR
  have hCr : (0 : ℝ) < ((|C| : ℤ) : ℝ) := by exact_mod_cast hCpos
  have hl := Real.log_lt_log (by positivity) h1
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hl
  have hER : ((|C| : ℤ) : ℝ) ^ 20 ≤ (2 : ℝ) ^ E := by exact_mod_cast hE
  have hlC := Real.log_le_log (by positivity) hER
  rw [Real.log_pow, Real.log_pow] at hlC
  obtain ⟨l3, -⟩ := Repeat.log_three_bounds
  have hl2 := Real.log_two_gt_d9
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have hB : 0 < (E : ℝ) * (1585 * Real.log 2 - 1000 * Real.log 3) := mul_pos hEr (by linarith)
  have hC2 : 0 < (E : ℝ) * (Real.log 2 - 0.6931471803) := mul_pos hEr (by linarith)
  push_cast at hl hlC
  nlinarith

/-- **Fixed blocks.** Given Ellison, for positive nonempty blocks `u₀, v₀` with nonzero core, no cycle
of either sign lies on a rotation of `u₀^a v₀^b` (`a, b ≥ 1`) once `|C(u₀, v₀)|^{20} ≤ 2^E`, `E` not
exceptional. -/
theorem no_cycle_two_blocks (hEl : CycleLiterature.Ellison1971) {u₀ v₀ : Word} (hu₀ : u₀.Pos)
    (hv₀ : v₀.Pos) (hu₀0 : u₀ ≠ []) (hv₀0 : v₀ ≠ []) (hC : core (2 : ℤ) 3 u₀ v₀ ≠ 0) {x : ℤ}
    {o : ℕ} (h : IsSyrCycle x o) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hw : gapWord x o ~r bpow u₀ a ++ bpow v₀ b)
    (hx : (gapWord x o).sum ∉ CycleLiterature.ellisonExceptions)
    (hE : |core (2 : ℤ) 3 u₀ v₀| ^ 20 ≤ 2 ^ (gapWord x o).sum) : False :=
  no_cycle_tree hEl hu₀ hv₀ hu₀0 hv₀0 hC Tree.base h ha hb hw hx hE

/-- The core of the `-17` cycle's blocks: `C(1112, 114) = -3336 = -2³·3·139`. -/
theorem core_neg_seventeen_blocks : core (2 : ℤ) 3 [1, 1, 1, 2] [1, 1, 4] = -3336 := by decide

end Syracuse.Trees
