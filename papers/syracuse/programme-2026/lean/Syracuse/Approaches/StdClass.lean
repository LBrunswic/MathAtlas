import Syracuse.Approaches.StdPairs

/-!
# Classification of cycles on standard-pair two-run words (both signs)

`StdPairs.no_cycle_std_pair` excludes cycles (either sign) on `u^a v^b` for a standard pair, outside
Ellison's finite exceptional set of `E` (all `E ≤ 27`). Here the exceptional `E` are checked by
enumeration, so the result needs no Barina hypothesis and holds for both signs:

> Given Ellison, the only cycle of the accelerated `3x+1` map on `ℤ` whose gap word is a rotation of
> `u^a v^b` (`(u, v)` standard, `a, b ≥ 1`) is `-5 → -7` (`std_pair_cycles`).

The enumeration `gen` walks the Stern–Brocot tree of standard pairs from `((1),(2))` while the total
sum is at most `27`. `mem_gen_of_std` proves that every standard pair with total sum `≤ 27` occurs in
it. A kernel-checked `decide` then verifies that among all `u^a v^b` with `E ≤ 27`, the only word with
`D ∣ S` is `(1,2)`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| every standard pair of total sum `≤ 27` is in the enumeration | `mem_gen_of_std` | proved |
| among standard-pair two-run words with `E ≤ 27`, only `(1,2)` satisfies `D ∣ S` | `small_check` | proved (`decide +kernel`) |
| the only cycle on a standard-pair two-run word is `-5 → -7` | `std_pair_cycles` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.StdClass

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

/-- The Stern–Brocot enumeration of standard pairs with total sum `≤ 27`, with fuel `f`. -/
def gen : ℕ → Word → Word → List (Word × Word)
  | 0, _, _ => []
  | f + 1, u, v =>
    if u.sum + v.sum ≤ 27 then (u, v) :: (gen f u (u ++ v) ++ gen f (u ++ v) v) else []

lemma gen_mono {f f' : ℕ} (hf : f ≤ f') (u v : Word) {p : Word × Word} (hp : p ∈ gen f u v) :
    p ∈ gen f' u v := by
  induction f generalizing f' u v with
  | zero => simp [gen] at hp
  | succ f ih =>
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [gen] at hp ⊢
    split_ifs at hp ⊢ with hs
    · simp only [List.mem_cons, List.mem_append] at hp ⊢
      rcases hp with hp | hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inl (ih (by omega) _ _ hp))
      · exact Or.inr (Or.inr (ih (by omega) _ _ hp))
    · simp at hp

/-- Children of an enumerated pair are enumerated with one more unit of fuel. -/
lemma gen_child (f : ℕ) (u v : Word) {p q : Word} (hp : (p, q) ∈ gen f u v) :
    (p.sum + (p ++ q).sum ≤ 27 → (p, p ++ q) ∈ gen (f + 1) u v) ∧
    ((p ++ q).sum + q.sum ≤ 27 → (p ++ q, q) ∈ gen (f + 1) u v) := by
  induction f generalizing u v with
  | zero => simp [gen] at hp
  | succ f ih =>
    rw [gen] at hp
    split_ifs at hp with hs
    · simp only [List.mem_cons, List.mem_append] at hp
      rcases hp with hp | hp | hp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        constructor
        · intro hc
          rw [gen, if_pos hs]
          simp only [List.mem_cons, List.mem_append]
          right; left
          rw [gen, if_pos hc]; exact List.mem_cons_self
        · intro hc
          rw [gen, if_pos hs]
          simp only [List.mem_cons, List.mem_append]
          right; right
          rw [gen, if_pos hc]; exact List.mem_cons_self
      · obtain ⟨h1, h2⟩ := ih _ _ hp
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · rw [gen, if_pos hs]; simp only [List.mem_cons, List.mem_append]; right; left; exact h1 hc
        · rw [gen, if_pos hs]; simp only [List.mem_cons, List.mem_append]; right; left; exact h2 hc
      · obtain ⟨h1, h2⟩ := ih _ _ hp
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · rw [gen, if_pos hs]; simp only [List.mem_cons, List.mem_append]; right; right; exact h1 hc
        · rw [gen, if_pos hs]; simp only [List.mem_cons, List.mem_append]; right; right; exact h2 hc
    · simp at hp

/-- Standard pairs have positive sums. -/
lemma std_sums {u v : Word} (h : StdPair u v) : 1 ≤ u.sum ∧ 1 ≤ v.sum := by
  obtain ⟨hu, hv, hu0, hv0⟩ := h.pos
  constructor
  · have := CycleLiterature.length_le_sum hu; have := List.length_pos_of_ne_nil hu0; omega
  · have := CycleLiterature.length_le_sum hv; have := List.length_pos_of_ne_nil hv0; omega

/-- **Completeness of the enumeration.** -/
theorem mem_gen_of_std {p q : Word} (h : StdPair p q) (hs : p.sum + q.sum ≤ 27) :
    (p, q) ∈ gen (p.sum + q.sum - 2) [1] [2] := by
  induction h with
  | base => simp [gen]
  | @left u v hst ih =>
    obtain ⟨hus, hvs⟩ := std_sums hst
    have hs' : u.sum + v.sum ≤ 27 := by simp at hs; omega
    have hchild := (gen_child _ _ _ (ih hs')).1 hs
    exact gen_mono (by simp; omega) _ _ hchild
  | @right u v hst ih =>
    obtain ⟨hus, hvs⟩ := std_sums hst
    have hs' : u.sum + v.sum ≤ 27 := by simp at hs; omega
    have hchild := (gen_child _ _ _ (ih hs')).2 hs
    exact gen_mono (by simp; omega) _ _ hchild

/-- **Small cases.** Among all `u^a v^b` with `(u,v)` enumerated and `E = a|u| + b|v| ≤ 27`, only
`(1,2)` satisfies `D ∣ S`. -/
theorem small_check : ∀ pq ∈ gen 25 [1] [2], ∀ a : ℕ, a < 28 → ∀ b : ℕ, b < 28 →
    (1 ≤ a ∧ 1 ≤ b ∧ a * pq.1.sum + b * pq.2.sum ≤ 27) →
    Sz (bpow pq.1 a ++ bpow pq.2 b) % Dz (bpow pq.1 a ++ bpow pq.2 b) = 0 →
    bpow pq.1 a ++ bpow pq.2 b = [1, 2] := by
  decide +kernel

/-- **Classification.** Given Ellison, the only cycle (of either sign) whose gap word is a rotation
of `u^a v^b` for a standard pair `(u, v)` and `a, b ≥ 1` is the cycle `-5 → -7`. -/
theorem std_pair_cycles (hEl : CycleLiterature.Ellison1971) {u v : Word} (hst : StdPair u v)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hw : gapWord x o ~r bpow u a ++ bpow v b) : x = -5 ∨ x = -7 := by
  by_cases hx : (gapWord x o).sum ∈ CycleLiterature.ellisonExceptions
  · -- `E ≤ 27`: enumerate
    have hE27 : (gapWord x o).sum ≤ 27 := by
      simp only [CycleLiterature.ellisonExceptions, Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    obtain ⟨hu, hv, hu0, hv0⟩ := hst.pos
    have hus : 1 ≤ u.sum := by
      have := CycleLiterature.length_le_sum hu; have := List.length_pos_of_ne_nil hu0; omega
    have hvs : 1 ≤ v.sum := by
      have := CycleLiterature.length_le_sum hv; have := List.length_pos_of_ne_nil hv0; omega
    have hsw : (gapWord x o).sum = a * u.sum + b * v.sum := by
      rw [hw.perm.sum_eq, List.sum_append]; simp [bpow, CocycleCombine.wpow_sum]
    have hle : u.sum + v.sum ≤ 27 := by
      have : u.sum ≤ a * u.sum := Nat.le_mul_of_pos_left _ (by omega)
      have : v.sum ≤ b * v.sum := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hmem := gen_mono (by omega : u.sum + v.sum - 2 ≤ 25) _ _ (mem_gen_of_std hst hle)
    have hdvd := dvd_S_of_rotated h hw
    have hau : a * u.sum ≤ 27 := by rw [hsw] at hE27; omega
    have hbv : b * v.sum ≤ 27 := by rw [hsw] at hE27; omega
    have ha28 : a < 28 := lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right a (by omega)) hau) (by norm_num)
    have hb28 : b < 28 := lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right b (by omega)) hbv) (by norm_num)
    have hword := small_check (u, v) hmem a ha28 b hb28
      ⟨ha, hb, show a * u.sum + b * v.sum ≤ 27 by omega⟩
      (Int.emod_eq_zero_of_dvd hdvd)
    rw [hword] at hw
    -- `gapWord x o` is `[1,2]` or `[2,1]`
    obtain ⟨n, hn⟩ := hw.symm
    have hcases : gapWord x o = [1, 2] ∨ gapWord x o = [2, 1] := by
      rw [← hn, ← List.rotate_mod]
      have : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
      interval_cases (n % 2) <;> simp [List.rotate]
    have hceq := h.cycle_equation
    rcases hcases with hc | hc <;> rw [hc] at hceq <;> norm_num [Dz, Sz, D, S] at hceq <;> omega
  · exact absurd (no_cycle_std_pair hEl hst h ha hb hw hx) id

end Syracuse.StdClass
