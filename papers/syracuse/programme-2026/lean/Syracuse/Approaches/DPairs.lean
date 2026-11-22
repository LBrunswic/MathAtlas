import Syracuse.Approaches.NearPairs

/-!
# The Christoffel tree over `{1, d}`: finitely many two-run cycle words for each `d`

`StdPairs` grows standard pairs from `([1], [2])` by `(u, v) ↦ (u, uv), (uv, v)`, and their wedge core
stays `6`-smooth. The same moves multiply the core by `X^{|u|}` or `Y^{len v}` from **any** root
(`StdPairs.core_left`, `core_right`). So in the tree grown from `([1], [d])`, a *`d`-pair*, the core is
always `6`-smooth times the root's core `C([1],[d]) = -2(2^{d-1} - 1)` (`core_dpair`).

On a cycle whose word is a rotation of `u^a v^b` for a `d`-pair, the two block divisibilities then give
`|D| < 2^{d-1} 3^{E(u^a)}` and `|D| < 2^{d-1} 3^{E(v^b)}`, so `|D|² < 4^{d-1} 3^E`. Ellison's
`|D| > 2^E e^{-E/10}` contradicts this once `E ≥ 20(d - 1)`, because `1.9 log 2 - log 3 > 0.2`. Hence
(`no_cycle_dpair`):

> Given Ellison, a cycle of either sign on a two-run word `u^a v^b` over a `d`-pair has
> `E < 20(d - 1)`, or `E` is one of Ellison's exceptions (`E ≤ 27`).

For `d = 2` the `d`-pairs are the standard pairs (`DPair.of_std`), and the bound is the `StdPairs`
theorem. For each `d` only finitely many words remain, and the left spine `(1, 1^m d)` is closed for
every `d` (`NearPairs`). The other branches of the `d`-tree are not settled for large `E` relative to
`d`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `d`-pairs (tree from `([1],[d])`) | `DPair` | definition |
| the core of a `d`-pair is `-2^{i+1} 3^k (2^{d-1} - 1)` | `core_dpair` | proved |
| standard pairs are `2`-pairs; the spine `(1, 1^m d)` consists of `d`-pairs | `DPair.of_std`, `DPair.spine` | proved |
| `d`-pairs are positive, nonempty words (`d ≥ 1`) | `DPair.pos` | proved |
| no cycle (either sign) on `u^a v^b` over a `d`-pair once `E ≥ 20(d-1)`, `E` not exceptional | `no_cycle_dpair` | proved (conditional on `Ellison1971`) |
| the enumeration `genD` of `d`-pairs with total sum `≤ N` is complete | `mem_genD` | proved |
| no two-run word over a `3`-pair with `E < 40` has `D ∣ S` | `small_check_three` | proved (`decide +kernel`) |
| **the `{1,3}` tree is closed:** no cycle of either sign on any `u^a v^b` over a `3`-pair | `dpair_three_cycles` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.DPairs

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

/-- The Christoffel tree over `{1, d}`: pairs grown from `([1], [d])`. -/
inductive DPair (d : ℕ) : Word → Word → Prop
  | base : DPair d [1] [d]
  | left {u v : Word} : DPair d u v → DPair d u (u ++ v)
  | right {u v : Word} : DPair d u v → DPair d (u ++ v) v

/-- **The core of a `d`-pair** is `6`-smooth times `2^{d-1} - 1`. -/
theorem core_dpair {j : ℕ} {u v : Word} (h : DPair (j + 1) u v) :
    ∃ i k : ℕ, core (2 : ℤ) 3 u v = -(2 ^ (i + 1) * 3 ^ k * (2 ^ j - 1)) := by
  induction h with
  | base => exact ⟨0, 0, by simp [core, D]; ring⟩
  | @left u v _ ih =>
    obtain ⟨i, k, hik⟩ := ih
    exact ⟨i + u.sum, k, by rw [core_left, hik]; ring⟩
  | @right u v _ ih =>
    obtain ⟨i, k, hik⟩ := ih
    exact ⟨i, k + v.length, by rw [core_right, hik]; ring⟩

/-- Standard pairs are the `2`-pairs. -/
theorem DPair.of_std {u v : Word} (h : StdPair u v) : DPair 2 u v := by
  induction h with
  | base => exact DPair.base
  | left _ ih => exact DPair.left ih
  | right _ ih => exact DPair.right ih

/-- The left spine `(1, 1^m d)` consists of `d`-pairs. -/
theorem DPair.spine (d m : ℕ) : DPair d [1] (List.replicate m 1 ++ [d]) := by
  induction m with
  | zero => exact DPair.base
  | succ m ih =>
    have := DPair.left ih
    simpa [List.replicate_succ] using this

/-- `d`-pairs consist of positive, nonempty words. -/
theorem DPair.pos {d : ℕ} (hd : 1 ≤ d) {u v : Word} (h : DPair d u v) :
    u.Pos ∧ v.Pos ∧ u ≠ [] ∧ v ≠ [] := by
  induction h with
  | base =>
    exact ⟨by simp [Word.Pos], fun e he => by simp at he; omega, by simp, by simp⟩
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

/-- **Two runs over a `d`-pair.** Given Ellison, no cycle of either sign has a gap word that is a
rotation of `u^a v^b` (`(u, v)` a `d`-pair, `d ≥ 2`, `a, b ≥ 1`) with `E ≥ 20(d - 1)` outside Ellison's
exceptional set. -/
theorem no_cycle_dpair (hEl : CycleLiterature.Ellison1971) {j : ℕ} (hj : 1 ≤ j) {u v : Word}
    (hst : DPair (j + 1) u v) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hw : gapWord x o ~r bpow u a ++ bpow v b)
    (hx : (gapWord x o).sum ∉ CycleLiterature.ellisonExceptions)
    (hE : 20 * j ≤ (gapWord x o).sum) : False := by
  obtain ⟨hu, hv, hu0, hv0⟩ := hst.pos (by omega)
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
  obtain ⟨i, k, hc⟩ := core_dpair hst
  have hcop := isCoprime_six hne hsum0
  have strip : ∀ c : ℤ, Dz w ∣ core (2 : ℤ) 3 u v * c → Dz w ∣ (2 ^ j - 1) * c := by
    intro c hdc
    rw [hc, show -(2 ^ (i + 1) * 3 ^ k * (2 ^ j - 1)) * c =
      2 ^ (i + 1) * 3 ^ k * (-((2 ^ j - 1) * c)) by ring] at hdc
    have := CocycleCombine.dvd_of_isCoprime_six_of_dvd hcop _ _ hdc
    rwa [dvd_neg] at this
  have dU := strip _ hU
  have dV := strip _ hV
  -- sizes
  have hc1 : (1 : ℤ) ≤ 2 ^ j - 1 := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
    linarith
  have bound : ∀ y : Word, y.Pos → y ≠ [] → Dz w ∣ (2 ^ j - 1) * Dz y →
      |Dz w| < 2 ^ j * 3 ^ y.sum := by
    intro y hy hy0 hdy
    have hy1 := Dz_ne_zero hy0
    have hpos : 0 < (2 ^ j - 1) * |Dz y| := mul_pos (by linarith) (abs_pos.2 hy1)
    have hle : |Dz w| ≤ (2 ^ j - 1) * |Dz y| := by
      have hdv : |Dz w| ∣ (2 ^ j - 1) * |Dz y| := by
        have : (2 ^ j - 1) * |Dz y| = |(2 ^ j - 1) * Dz y| := by
          rw [abs_mul, abs_of_pos (by linarith : (0 : ℤ) < 2 ^ j - 1)]
        rw [this]; exact (abs_dvd_abs _ _).2 hdy
      exact Int.le_of_dvd hpos hdv
    have hlt := abs_Dz_lt hy
    calc |Dz w| ≤ (2 ^ j - 1) * |Dz y| := hle
      _ < 2 ^ j * 3 ^ y.sum :=
          mul_lt_mul'' (by linarith) hlt (by linarith) (abs_nonneg _)
  have bU := bound _ hua hua0 dU
  have bV := bound _ hvb hvb0 dV
  have hEw : w.sum = (bpow u a).sum + (bpow v b).sum := List.sum_append
  have hsq : |Dz w| ^ 2 < 2 ^ (2 * j) * 3 ^ w.sum := by
    rw [hEw, sq, pow_add, show (2 : ℤ) ^ (2 * j) = 2 ^ j * 2 ^ j by rw [two_mul, pow_add]]
    calc |Dz w| * |Dz w| < (2 ^ j * 3 ^ (bpow u a).sum) * (2 ^ j * 3 ^ (bpow v b).sum) :=
          mul_lt_mul'' bU bV (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  -- Ellison
  have hsw : (gapWord x o).sum = w.sum := hw.perm.sum_eq
  have hlw : (gapWord x o).length = w.length := hw.perm.length_eq
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
  have hsqR : ((|Dz w| : ℤ) : ℝ) ^ 2 < 2 ^ (2 * j) * 3 ^ E := by exact_mod_cast hsq
  have h1 := hlt.trans hsqR
  have hl := Real.log_lt_log (by positivity) h1
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hl
  obtain ⟨l3, -⟩ := Repeat.log_three_bounds
  have hl2 := Real.log_two_gt_d9
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have hjE : (20 * j : ℝ) ≤ E := by exact_mod_cast hE
  have hA : 0 ≤ ((E : ℝ) - 20 * j) * Real.log 2 := mul_nonneg (by linarith) (by positivity)
  have hB : 0 < (E : ℝ) * (1585 * Real.log 2 - 1000 * Real.log 3) := mul_pos hEr (by linarith)
  have hC : 0 < (E : ℝ) * (Real.log 2 - 0.6931471803) := mul_pos hEr (by linarith)
  push_cast at hl
  nlinarith

/-! ## Closing the tree over `{1, 3}` -/

/-- The Christoffel tree from `(u, v)` while the total sum is at most `N`, with fuel `f`. -/
def genD (N : ℕ) : ℕ → Word → Word → List (Word × Word)
  | 0, _, _ => []
  | f + 1, u, v =>
    if u.sum + v.sum ≤ N then (u, v) :: (genD N f u (u ++ v) ++ genD N f (u ++ v) v) else []

lemma genD_mono (N : ℕ) {f f' : ℕ} (hf : f ≤ f') (u v : Word) {p : Word × Word}
    (hp : p ∈ genD N f u v) : p ∈ genD N f' u v := by
  induction f generalizing f' u v with
  | zero => simp [genD] at hp
  | succ f ih =>
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [genD] at hp ⊢
    split_ifs at hp ⊢ with hs
    · simp only [List.mem_cons, List.mem_append] at hp ⊢
      rcases hp with hp | hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inl (ih (by omega) _ _ hp))
      · exact Or.inr (Or.inr (ih (by omega) _ _ hp))
    · simp at hp

lemma genD_child (N f : ℕ) (u v : Word) {p q : Word} (hp : (p, q) ∈ genD N f u v) :
    (p.sum + (p ++ q).sum ≤ N → (p, p ++ q) ∈ genD N (f + 1) u v) ∧
    ((p ++ q).sum + q.sum ≤ N → (p ++ q, q) ∈ genD N (f + 1) u v) := by
  induction f generalizing u v with
  | zero => simp [genD] at hp
  | succ f ih =>
    rw [genD] at hp
    split_ifs at hp with hs
    · simp only [List.mem_cons, List.mem_append] at hp
      rcases hp with hp | hp | hp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        constructor
        · intro hc
          rw [genD, if_pos hs]
          simp only [List.mem_cons, List.mem_append]
          right; left
          rw [genD, if_pos hc]; exact List.mem_cons_self
        · intro hc
          rw [genD, if_pos hs]
          simp only [List.mem_cons, List.mem_append]
          right; right
          rw [genD, if_pos hc]; exact List.mem_cons_self
      · obtain ⟨h1, h2⟩ := ih _ _ hp
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · rw [genD, if_pos hs]; simp only [List.mem_cons, List.mem_append]; right; left; exact h1 hc
        · rw [genD, if_pos hs]; simp only [List.mem_cons, List.mem_append]; right; left; exact h2 hc
      · obtain ⟨h1, h2⟩ := ih _ _ hp
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · rw [genD, if_pos hs]; simp only [List.mem_cons, List.mem_append]; right; right; exact h1 hc
        · rw [genD, if_pos hs]; simp only [List.mem_cons, List.mem_append]; right; right; exact h2 hc
    · simp at hp

/-- `d`-pairs have positive sums. -/
lemma dpair_sums {d : ℕ} (hd : 1 ≤ d) {u v : Word} (h : DPair d u v) : 1 ≤ u.sum ∧ 1 ≤ v.sum := by
  obtain ⟨hu, hv, hu0, hv0⟩ := h.pos hd
  constructor
  · have := CycleLiterature.length_le_sum hu; have := List.length_pos_of_ne_nil hu0; omega
  · have := CycleLiterature.length_le_sum hv; have := List.length_pos_of_ne_nil hv0; omega

/-- **Completeness of the enumeration** of `d`-pairs. -/
theorem mem_genD {d N : ℕ} (hd : 1 ≤ d) {p q : Word} (h : DPair d p q) (hs : p.sum + q.sum ≤ N) :
    (p, q) ∈ genD N (p.sum + q.sum) [1] [d] := by
  induction h with
  | base =>
    rw [show [1].sum + [d].sum = d + 1 by simp; omega, genD, if_pos (by simpa using hs)]
    exact List.mem_cons_self
  | @left u v hst ih =>
    obtain ⟨hus, hvs⟩ := dpair_sums hd hst
    have hs' : u.sum + v.sum ≤ N := by simp at hs; omega
    have hchild := (genD_child _ _ _ _ (ih hs')).1 hs
    exact genD_mono _ (by simp; omega) _ _ hchild
  | @right u v hst ih =>
    obtain ⟨hus, hvs⟩ := dpair_sums hd hst
    have hs' : u.sum + v.sum ≤ N := by simp at hs; omega
    have hchild := (genD_child _ _ _ _ (ih hs')).2 hs
    exact genD_mono _ (by simp; omega) _ _ hchild

/-- **Small cases over `{1, 3}`** (`E < 40`): no two-run word over a `3`-pair satisfies `D ∣ S`. -/
theorem small_check_three : ∀ pq ∈ genD 39 39 [1] [3], ∀ a : ℕ, a < 40 → ∀ b : ℕ, b < 40 →
    (1 ≤ a ∧ 1 ≤ b ∧ a * pq.1.sum + b * pq.2.sum ≤ 39) →
    Sz (bpow pq.1 a ++ bpow pq.2 b) % Dz (bpow pq.1 a ++ bpow pq.2 b) ≠ 0 := by
  decide +kernel

/-- **The Christoffel tree over `{1, 3}` is closed.** Given Ellison, no cycle of either sign has a gap
word that is a rotation of `u^a v^b` for a `3`-pair `(u, v)` and `a, b ≥ 1`. -/
theorem dpair_three_cycles (hEl : CycleLiterature.Ellison1971) {u v : Word} (hst : DPair 3 u v)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hw : gapWord x o ~r bpow u a ++ bpow v b) : False := by
  obtain ⟨hus, hvs⟩ := dpair_sums (by norm_num) hst
  have hsw : (gapWord x o).sum = a * u.sum + b * v.sum := by
    rw [hw.perm.sum_eq, List.sum_append]; simp [bpow, CocycleCombine.wpow_sum]
  by_cases hE : (gapWord x o).sum < 40
  · have hau : u.sum ≤ a * u.sum := Nat.le_mul_of_pos_left _ (by omega)
    have hbv : v.sum ≤ b * v.sum := Nat.le_mul_of_pos_left _ (by omega)
    have hle : u.sum + v.sum ≤ 39 := by omega
    have hmem := genD_mono 39 (by omega : u.sum + v.sum ≤ 39) _ _ (mem_genD (by norm_num) hst hle)
    have ha' : a ≤ a * u.sum := Nat.le_mul_of_pos_right a (by omega)
    have hb' : b ≤ b * v.sum := Nat.le_mul_of_pos_right b (by omega)
    have ha40 : a < 40 := by omega
    have hb40 : b < 40 := by omega
    exact small_check_three (u, v) hmem a ha40 b hb40 ⟨ha, hb, show a * u.sum + b * v.sum ≤ 39 by omega⟩
      (Int.emod_eq_zero_of_dvd (dvd_S_of_rotated h hw))
  · exact no_cycle_dpair hEl (j := 2) (by norm_num) hst h ha hb hw
      (Frontier.not_mem_exceptions (by omega)) (by omega)

end Syracuse.DPairs
