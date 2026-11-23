import Causal.Ladder.Rules

-- scratch (T-tac-dual-has-chronal-neighbour), not built by lake: each example must FAIL, by
-- exhaustive search (run with -DmaxErrors=100; read the messages).

section
universe u
variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M)
open Causal Causal.Causality

-- idle: no C.dual in sight, nothing transported (refuted: the notched plane)
example (h : C.HasChronalNeighbourEverywhere) : C.Tarentin := by causal_ladder
-- deep reversal, refuted (the closed half-line)
example (h : C.HasChronalNeighbourEverywhere) : C.dual.dual.dual.dual.dual.ChronalNeighbours := by
  causal_ladder
-- the 16 facts with has_chronal_neighbour dropped and chronal_neighbours dropped: refuted
-- (the lightlike line has none of the chronal properties)
example (h1 : C.IsCausal) (h4 : C.GloballyHyperbolic) (h12 : C.HasTimeFunction) :
    C.dual.dual.dual.HasChronalNeighbourEverywhere := by
  causal_ladder
-- not nodes, so not read: the unfolded form across time reversal, non-empty chronal cones
example (h : ∀ p, C.HasChronalNeighbour p) : C.dual.HasChronalNeighbourEverywhere := by
  causal_ladder
example (h : C.NonemptyChronalCones) : C.dual.HasChronalNeighbourEverywhere := by causal_ladder

end
