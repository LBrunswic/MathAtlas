import Causal.Ladder.Rules

-- scratch (T-tac-dual-future-one-connected), not built by lake: positives the new rule pairs
-- futureOneConnected_of_dual / _dual and locallyStronglyCausal_of_dual / _dual should close.

section
universe u
variable {M : Type u} [TopologicalSpace M] (C CN : Causal.Causality M)
open Causal Causal.Causality

-- an odd number of reversals, so the builtin assumption (C.dual.dual is C by rfl) cannot close it
example (_h : C.dual.dual.dual.FutureOneConnected) : C.FutureOneConnected := by causal_ladder
example (_h : C.FutureOneConnected) : C.dual.dual.dual.FutureOneConnected := by causal_ladder
example (_h : C.dual.dual.dual.LocallyStronglyCausal) : C.LocallyStronglyCausal := by causal_ladder
example (_h : C.LocallyStronglyCausal) : C.dual.dual.dual.LocallyStronglyCausal := by causal_ladder
-- the generated edge strongly_causal ⇒ locally_strongly_causal on a reversal
example (_h : C.dual.dual.dual.StronglyCausal) : C.LocallyStronglyCausal := by causal_ladder
example (_h : C.StronglyCausalOpen) : C.dual.dual.dual.LocallyStronglyCausal := by causal_ladder
-- the fact curves_extend (T1, second countable) on the reversal, with the new node in context
example [T1Space M] [SecondCountableTopology M] (_h : C.FutureOneConnected) :
    C.dual.CurvesExtend := by
  causal_ladder
-- the shape of Causal.C0ExtensionSkeleton.exists_c0_skeleton (C0ExtensionSkeleton.lean:492-495):
-- the three facts of C and CN transported to C.dual, CN.dual as arguments of a key lemma
example (_hlsc : C.LocallyStronglyCausal) (_hcac : CN.CausallyArcConnected)
    (_hfoc : CN.FutureOneConnected)
    (key : C.dual.LocallyStronglyCausal → CN.dual.CausallyArcConnected →
      CN.dual.FutureOneConnected → False) : False :=
  key (by causal_ladder) (by causal_ladder) (by causal_ladder)
-- a conjunction about C.dual from facts about C
example (_hS : C.StronglyCausal) (_hF : C.FutureOneConnected) (_hK : C.CausallyArcConnected) :
    C.dual.LocallyStronglyCausal ∧ C.dual.FutureOneConnected ∧ C.dual.StronglyCausal ∧
      C.dual.AbsolutelyMinimal ∧ C.dual.CausallyArcConnected := by
  causal_ladder
-- a large context: sixteen facts of C, a goal about C.dual³
example (_h1 : C.IsCausal) (_h2 : C.StronglyCausal) (_h3 : C.GloballyHyperbolic)
    (_h4 : C.CausallyCompact) (_h5 : C.PushUp) (_h6 : C.CausallyOpen) (_h7 : C.AbsolutelyMinimal)
    (_h8 : C.CausallyArcConnected) (_h9 : C.CausallyPlain) (_h10 : C.Tarentin)
    (_h11 : C.HasTimeFunction) (_h12 : C.LocallyPushUp) (_h13 : C.ChronalNeighbours)
    (_h14 : C.HasChronalNeighbourEverywhere) (_h15 : C.FutureOneConnected)
    (_h16 : C.LocallyStronglyCausal) :
    C.dual.dual.dual.FutureOneConnected := by
  causal_ladder
example (_h1 : C.IsCausal) (_h2 : C.StronglyCausal) (_h3 : C.GloballyHyperbolic)
    (_h4 : C.CausallyCompact) (_h5 : C.PushUp) (_h6 : C.CausallyOpen) (_h7 : C.AbsolutelyMinimal)
    (_h8 : C.CausallyArcConnected) (_h9 : C.CausallyPlain) (_h10 : C.Tarentin)
    (_h11 : C.HasTimeFunction) (_h12 : C.LocallyPushUp) (_h13 : C.ChronalNeighbours)
    (_h14 : C.HasChronalNeighbourEverywhere) (_h15 : C.FutureOneConnected)
    (_h16 : C.LocallyStronglyCausal) :
    C.dual.dual.dual.LocallyStronglyCausal := by
  causal_ladder
-- negations read backwards (kb/0080)
example (hn : ¬ C.dual.LocallyStronglyCausal) : ¬ C.StronglyCausal ∧ ¬ C.dual.StronglyCausalOpen :=
  ⟨fun _ => hn (by causal_ladder), fun _ => hn (by causal_ladder)⟩
example (hn : ¬ C.dual.FutureOneConnected) : ¬ C.FutureOneConnected :=
  fun _ => hn (by causal_ladder)

end
