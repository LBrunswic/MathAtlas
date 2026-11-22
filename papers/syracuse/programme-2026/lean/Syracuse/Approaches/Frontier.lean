import Syracuse.Approaches.StdPairs
import Syracuse.Approaches.Circuits
import Syracuse.Approaches.BalancedPow

/-!
# The frontier: what a nontrivial positive Syracuse cycle must look like

This file combines the exclusions proved during the cocycle-program review into one statement
(`frontier`). The only literature inputs are two named Props from `CycleLiterature`, each entering as
an explicit hypothesis:

* `Ellison1971`: `|2^x - 3^y| > 2^x e^{-x/10}` outside a finite exceptional set of `x`;
* `Barina2025`: every `n < 2^71` reaches `1`.

Barina removes the small-`E` exceptions. Every element of a nontrivial positive cycle exceeds
`2^71 - 1` (`cycle_gt_of_verifiedUpTo`), while `|x| < 3^E` (Böhm–Sontacchi, `cycle_abs_lt`). Hence
`E ≥ 45` (`E_ge_of_barina`), which is beyond all of Ellison's exceptions.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| Barina ⇒ `E ≥ 45` for a nontrivial positive cycle | `E_ge_of_barina` | proved (conditional on `Barina2025`) |
| standard pairs over `{1,2}` always contain a `1` | `StdPair.one_mem` | proved |
| no positive cycle on `u^a v^b` (standard pair), no exceptional-`E` hypothesis | `no_pos_cycle_std_pair` | proved (conditional on Ellison + Barina) |
| the frontier: every property below holds for a nontrivial positive cycle | `frontier` | proved (conditional on Ellison + Barina where marked) |
-/

namespace Syracuse.Frontier

open Syracuse Syracuse.StdPairs Syracuse.TwoBackground Syracuse.Balanced

/-- **Barina ⇒ `E ≥ 45`.** A nontrivial positive cycle has gap-word sum at least `45`. -/
theorem E_ge_of_barina (hB : CycleLiterature.Barina2025) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hx : 0 < x) (hx1 : x ≠ 1) : 45 ≤ (gapWord x o).sum := by
  have h1 := CycleLiterature.cycle_gt_of_verifiedUpTo hB h hx hx1 0
  have h2 := CycleLiterature.cycle_abs_lt h
  simp only [Function.iterate_zero, id] at h1
  rw [abs_of_pos hx] at h2
  by_contra hlt
  replace hlt := not_le.mp hlt
  have : (3 : ℤ) ^ (gapWord x o).sum ≤ 3 ^ 44 := pow_le_pow_right₀ (by norm_num) (by omega)
  have : ((2 ^ 71 - 1 : ℕ) : ℤ) = 2 ^ 71 - 1 := by norm_num
  norm_num at h1
  linarith

/-- `E ≥ 28` puts `E` outside Ellison's exceptional set. -/
lemma not_mem_exceptions {E : ℕ} (hE : 28 ≤ E) : E ∉ CycleLiterature.ellisonExceptions := by
  simp only [CycleLiterature.ellisonExceptions, Finset.mem_insert, Finset.mem_singleton]; omega

/-- The first word of a standard pair contains the letter `1`. -/
theorem StdPair.one_mem {u v : Word} (h : StdPair u v) : 1 ∈ u := by
  induction h with
  | base => simp
  | left _ ih => exact ih
  | right _ ih => exact List.mem_append_left _ ih

/-- **No positive cycle on two runs of a standard pair**, with no exceptional-`E` hypothesis
(conditional on Ellison and Barina). -/
theorem no_pos_cycle_std_pair (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    {u v : Word} (hst : StdPair u v) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hw : gapWord x o ~r bpow u a ++ bpow v b) : False := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : 1 ∈ bpow u a ++ bpow v b := by
      apply List.mem_append_left
      simp only [bpow, CocycleCombine.wpow, List.mem_flatten, List.mem_replicate]
      exact ⟨u, ⟨by omega, rfl⟩, StdPair.one_mem hst⟩
    have := Circuits.gapWord_one o 1 (hw.symm.perm.subset h1)
    omega
  exact no_cycle_std_pair hEl hst h ha hb hw (not_mem_exceptions (by
    have := E_ge_of_barina hB h hx hx1; omega))

/-- **The frontier.** Given Ellison 1971 and Barina 2025, a nontrivial positive Syracuse cycle with
gap word `w = gapWord x o` satisfies all of the following:
1. every element exceeds `2^71 - 1`, and `E = Σw ≥ 45`;
2. `3^o < 2^E` and `2^E·3^o ≤ 10^o` (the ratio sandwich, `log₂3 < E/o ≤ log₂(10/3)`);
3. its parity vector is **not** circularly balanced (unconditional);
4. `w` is not a rotation of a two-letter-run word `1^a d^b` (`a, b ≥ 1`, `d ≥ 2`; Ellison);
5. `w` is not a rotation of `u^a v^b` for a standard Christoffel pair (`a, b ≥ 1`);
6. if `w` is a rotation of `β d^L` (one long run of a single letter), then `L ≤ 2|β| + 3 len β`
   (unconditional). -/
theorem frontier (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) (hx1 : x ≠ 1) :
    (∀ k, ((2 ^ 71 - 1 : ℕ) : ℤ) < syr^[k] x) ∧ 45 ≤ (gapWord x o).sum ∧
    (3 : ℤ) ^ o < 2 ^ (gapWord x o).sum ∧ 2 ^ (gapWord x o).sum * 3 ^ o ≤ 10 ^ o ∧
    ¬ CircBalanced (CocycleCombine.pv (gapWord x o)) ∧
    (∀ a b d : ℕ, 1 ≤ a → 1 ≤ b → 2 ≤ d → ¬ (gapWord x o ~r two 1 d a b)) ∧
    (∀ u v : Word, ∀ a b : ℕ, StdPair u v → 1 ≤ a → 1 ≤ b → ¬ (gapWord x o ~r bpow u a ++ bpow v b)) ∧
    (∀ (β : Word) (d L : ℕ), gapWord x o ~r (β ++ List.replicate L d) → L ≤ 2 * β.sum + 3 * β.length) :=
  ⟨fun k => CycleLiterature.cycle_gt_of_verifiedUpTo hB h hx hx1 k,
   E_ge_of_barina hB h hx hx1,
   Program.three_pow_lt_two_pow h hx,
   Limits.two_pow_mul_three_pow_le h hx hx1,
   fun hb => hx1 (BalancedPow.no_balanced_cycle_all h hx hb),
   fun _ _ _ ha hb hd hw => Circuits.no_cycle_two_letters hEl h hx ha hb hd hw,
   fun _ _ _ _ hst ha hb hw => no_pos_cycle_std_pair hEl hB hst h hx ha hb hw,
   fun _ _ _ hw => Limits.background_bound h hx hx1 hw⟩

end Syracuse.Frontier
