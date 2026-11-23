import Causal.Ladder.Rules

-- scratch (T-tac-dual-has-chronal-neighbour), not built by lake: positives across time reversal
-- for has_chronal_neighbour, nested reversals and a large context.

section
universe u
variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M)
open Causal Causal.Causality

-- needs the pair (it fails with the pair erased): h transported to C.dual, C.dual³ is C.dual by rfl
set_option profiler true in
example (h : C.HasChronalNeighbourEverywhere) : C.dual.dual.dual.HasChronalNeighbourEverywhere := by
  causal_ladder
set_option profiler true in
example (h : C.ChronalNeighbours) : C.dual.dual.dual.HasChronalNeighbourEverywhere := by
  causal_ladder
-- C.dual⁴ is C by rfl: the builtin assumption closes this, no rule of the pair is needed
set_option profiler true in
example (h : C.dual.dual.dual.dual.HasChronalNeighbourEverywhere) :
    C.HasChronalNeighbourEverywhere := by
  causal_ladder
-- the half-lit line's seven facts with a chronal neighbour everywhere: eleven + one goals on C.dual
set_option profiler true in
example (hM : C.AbsolutelyMinimal) (hK : C.CausallyArcConnected) (hG : C.GloballyHyperbolic)
    (hP : C.PushUp) (hS : C.StronglyCausalOpen) (hT : C.HasTimeFunction)
    (_hF : C.CausallyOpenFuture) (hH : C.HasChronalNeighbourEverywhere) :
    C.dual.AbsolutelyMinimal ∧ C.dual.CausallyArcConnected ∧ C.dual.GloballyHyperbolic ∧
      C.dual.PushUp ∧ C.dual.LocallyPushUp ∧ C.dual.StronglyCausalOpen ∧
      C.dual.StronglyCausal ∧ C.dual.HasTimeFunction ∧ C.dual.CurvesExtend ∧ C.dual.IsCausal ∧
      C.dual.CausallyCompact ∧ C.dual.HasChronalNeighbourEverywhere := by
  causal_ladder
-- 16 facts of C (every two-sided node but curves_extend's derivable ones), goal on C.dual³
set_option profiler true in
example (h1 : C.IsCausal) (h2 : C.StronglyCausal) (h3 : C.StronglyCausalOpen)
    (h4 : C.GloballyHyperbolic) (h5 : C.CausallyCompact) (h6 : C.PushUp) (h7 : C.CausallyOpen)
    (h8 : C.AbsolutelyMinimal) (h9 : C.CausallyArcConnected) (h10 : C.CausallyPlain)
    (h11 : C.Tarentin) (h12 : C.HasTimeFunction) (h13 : C.LocallyPushUp)
    (h14 : C.LocallyCausallyOpen) (h15 : C.ChronalNeighbours)
    (h16 : C.HasChronalNeighbourEverywhere) :
    C.dual.dual.dual.HasChronalNeighbourEverywhere := by
  causal_ladder
-- the unfolded form closes a goal about C itself by the builtin assumption (definitional unfolding)
example (h : ∀ p, C.HasChronalNeighbour p) : C.HasChronalNeighbourEverywhere := by causal_ladder
-- the point predicate of C.dual: h is transported (C.dual in sight), then the builtin applyHyps
-- applies it at p (apply unfolds the definition to its ∀)
example (h : C.HasChronalNeighbourEverywhere) (p : M) : C.dual.HasChronalNeighbour p := by
  causal_ladder

end
