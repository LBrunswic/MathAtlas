import Causal.Ladder.Rules

-- scratch (T-tac-dual-future-one-connected), not built by lake: goals causal_ladder must not close.
-- Run with `lake env lean -DmaxErrors=100` and read the errors: each must be
-- "failed to prove the goal after exhaustive search", none at a depth, application or heartbeat
-- limit.

section
universe u
variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M) (W : TopologicalSpace.Opens M)
open Causal Causal.Causality

-- the `…On W` forms are not nodes: no rule transports them
example (h : C.FutureOneConnectedOn W) : C.dual.FutureOneConnectedOn W := by causal_ladder
example (h : C.StronglyCausalOn W) : C.dual.StronglyCausalOn W := by causal_ladder
-- the unfolded form of the node is not read across time reversal
example (h : ∀ p : M, ∃ V : TopologicalSpace.Opens M, p ∈ V ∧ C.StronglyCausalOn V) :
    C.dual.LocallyStronglyCausal := by
  causal_ladder
-- idle: no C.dual in sight, a refuted pair (locally_strongly_causal ⇏ strongly_causal)
example (h : C.LocallyStronglyCausal) (h' : C.FutureOneConnected) : C.StronglyCausal := by
  causal_ladder
-- refuted across time reversal
example (h : C.LocallyStronglyCausal) : C.dual.StronglyCausal := by causal_ladder
example (h : C.FutureOneConnected) : C.dual.LocallyStronglyCausal := by causal_ladder
-- nested reversals, refuted
example (h : C.FutureOneConnected) (h' : C.LocallyStronglyCausal) :
    C.dual.dual.dual.dual.dual.Tarentin := by
  causal_ladder
-- strong causality on ⊤ is strong causality, but StronglyCausalOn ⊤ is not a node either
example (h : C.StronglyCausalOn ⊤) : C.dual.LocallyStronglyCausal := by causal_ladder

end
