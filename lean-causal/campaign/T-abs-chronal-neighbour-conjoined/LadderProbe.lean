import Causal.NotchedPlane

/-! Scratch probe (not built by lake): what `causal_ladder` does with `has_chronal_neighbour`
for the two models of T-abs-chronal-neighbour-conjoined. -/

open Causal

-- across time reversal (the Dual rule pair `hasChronalNeighbourEverywhere_dual`)
example (h : notchedCausality.HasChronalNeighbourEverywhere) :
    notchedCausality.dual.HasChronalNeighbourEverywhere := by
  causal_ladder

-- ChronalPastNeighbours is no node: no rule gives the node from it
example : notchedCausality.HasChronalNeighbourEverywhere := by
  have := notchedCausality_chronalPastNeighbours
  fail_if_success causal_ladder
  exact fun x => Or.inr (this.Iminus_nonempty x)

-- NonemptyChronalCones is no node either
example : globalLine.HasChronalNeighbourEverywhere := by
  have := globalLine_nonemptyChronalCones
  fail_if_success causal_ladder
  exact this.hasChronalNeighbourEverywhere
