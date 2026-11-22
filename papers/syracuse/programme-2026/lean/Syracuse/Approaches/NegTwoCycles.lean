import Syracuse.Approaches.DTrees

/-!
# Negative cycles with at most two big gaps (Simons 2007, negative side)

The last section of Simons 2007 sketches a proof that the `3x - 1` map on the positive integers has a
single 2-cycle, with minimal element `17`. Equivalently, the only negative 2-cycle of the `3x + 1` map
is the one through `-17` (Lagarias, annotated bibliography II, entry 95). It is stated here as a
hypothesis, `Simons2007Neg`, faithful to the source: a cycle of negative integers taken with its
minimal period and having exactly two gaps `≥ 2`.

Combined with Steiner on `ℤ` (`SignedCycles.few_blocks_cycles`, given Ellison), it settles the open
statement `CycleLiterature.OnlyKnownNegativeCycles` for every negative cycle with at most two big gaps
(`only_known_of_few_blocks`). `EqualTwoCycles` already proves the equal-gap half of Simons's claim from
Ellison alone. The `-17` cycle has gaps `2` and `4`, consistent with that.

Related literature on the two-letter family `1^a d^b` (Lagarias, entries 74 and 68):
* Mimuro 2001 proves finiteness of positive cycles with parity sequence `1^i (1 0^j)^k`, gap word
  `1^i (j+1)^k`, by linear forms in logarithms;
* Luca 2005 improves this to "at least `C₁ log n` ascents in any cycle".

`Circuits.no_cycle_two_letters` (none at all, positive) and `SignedCycles.two_letter_cycles` (only
`-5 → -7`, both signs) need only Ellison 1971.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| negative `m`-cycles | `IsNegMCycle` | definition |
| Simons 2007 (sketch): the only negative 2-cycle is the `-17` cycle | `Simons2007Neg` | stated |
| negative cycles with at most two big gaps are among the known ones | `only_known_of_few_blocks` | proved (conditional on Ellison + `Simons2007Neg`) |
-/

namespace Syracuse.NegTwoCycles

open Syracuse

/-- `x` lies on a **negative `m`-cycle**: a cycle of negative integers, taken with its minimal period,
whose gap word has exactly `m` gaps `≥ 2` (Simons's blocks). -/
def IsNegMCycle (x : ℤ) (m : ℕ) : Prop :=
  x < 0 ∧ ∃ o, CycleLiterature.IsPrimSyrCycle x o ∧ CycleLiterature.numBlocks (gapWord x o) = m

/-- The points of the `-17` cycle. -/
def negSeventeenCycle : Finset ℤ := {-17, -25, -37, -55, -41, -61, -91}

/-- **Simons 2007** (J. L. Simons, "A simple (inductive) proof for the non-existence of 2-cycles for
the 3x+1 problem", J. Number Theory 123 (2007) 10–17, last section, a sketch; Lagarias's annotated
bibliography II, entry 95): the only negative 2-cycle of the `3x + 1` map is the cycle through `-17`. -/
def Simons2007Neg : Prop := ∀ x : ℤ, IsNegMCycle x 2 → x ∈ negSeventeenCycle

/-- **Negative cycles with at most two big gaps.** Given Ellison and Simons 2007, every negative cycle
whose gap word has at most two gaps `≥ 2` is one of the known negative cycles `-1`, `-5 → -7`, `-17`. -/
theorem only_known_of_few_blocks (hEl : CycleLiterature.Ellison1971) (hS : Simons2007Neg) {x : ℤ}
    {o : ℕ} (h : IsSyrCycle x o) (hx : x < 0)
    (hb : CycleLiterature.numBlocks (gapWord x o) ≤ 2) :
    x ∈ ({-1, -5, -7, -17, -25, -37, -55, -41, -61, -91} : Finset ℤ) := by
  have hper : Function.IsPeriodicPt syr o x := h.2.2
  set p := Function.minimalPeriod syr x
  have hp : IsSyrCycle x p :=
    ⟨hper.minimalPeriod_pos h.1, h.2.1, Function.isPeriodicPt_minimalPeriod syr x⟩
  have hprim : CycleLiterature.IsPrimSyrCycle x p :=
    ⟨hp, fun j hj hjp => Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) hjp⟩
  have hbp : CycleLiterature.numBlocks (gapWord x p) ≤ 2 := (DTrees.numBlocks_minimal_le h).trans hb
  rcases Nat.lt_or_ge (CycleLiterature.numBlocks (gapWord x p)) 2 with h1 | h2
  · rcases SignedCycles.few_blocks_cycles hEl hp (by omega) with rfl | rfl | rfl | rfl
    · omega
    all_goals simp
  · have hm := hS x ⟨hx, p, hprim, by omega⟩
    simp only [negSeventeenCycle, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end Syracuse.NegTwoCycles
