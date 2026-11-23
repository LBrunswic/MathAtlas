/- T-abs-one-sided-future-base: the #check of the added declarations, the six bodies, and the
   definitional bridges to the bodies before the refactor. Run from lean-causal/ with
   `lake env lean campaign/T-abs-one-sided-future-base/probe.lean`; output in checks-new.txt. -/
import Causal
set_option pp.universes true
set_option pp.fullNames true
#check @Causal.Causality.AbsolutelyMinimal.chronalFutureNeighbours_iff
#check @Causal.Causality.CausallyArcConnected.chronalFutureNeighbours_iff
#check @Causal.Causality.ChronalFutureNeighbours
#check @Causal.Causality.ChronalFutureNeighbours.Iplus_nonempty
#check @Causal.Causality.ChronalFutureNeighbours.Iplus_nonempty_of_mem
#check @Causal.Causality.ChronalFutureNeighbours.mem_Zplus
#check @Causal.Causality.NoFutureEndpoint
#check @Causal.Causality.chronalNeighbours_iff_future
#check @Causal.Causality.chronalPastNeighbours_def
#check @Causal.Causality.dual_chronalFutureNeighbours
#check @Causal.Causality.dual_chronalPastNeighbours
#check @Causal.Causality.dual_noFutureEndpoint
#check @Causal.Causality.dual_noPastEndpoint
#check @Causal.Causality.noCausalEndpoint_iff_future
#check @Causal.Causality.noFutureEndpoint_iff
#check @Causal.Causality.noPastEndpoint_def
#check @Causal.IsCausalIso.chronalFutureNeighbours_iff
#check @Causal.IsCausalIso.noFutureEndpoint_iff
#print Causal.Causality.ChronalFutureNeighbours
#print Causal.Causality.ChronalPastNeighbours
#print Causal.Causality.ChronalNeighbours
#print Causal.Causality.NoFutureEndpoint
#print Causal.Causality.NoPastEndpoint
#print Causal.Causality.NoCausalEndpoint

open Causal Causal.Causality TopologicalSpace in
section
universe u
variable {M : Type u} [TopologicalSpace M] (C : Causality M)
-- the old bodies, definitionally
example : C.ChronalPastNeighbours ↔ ∀ (V : Opens M), ∀ v ∈ V, ∃ p ∈ V, C.lt V p v := Iff.rfl
example : C.ChronalNeighbours ↔ C.ChronalPastNeighbours ∧ C.dual.ChronalPastNeighbours := Iff.rfl
example : C.ChronalNeighbours ↔ (∀ (V : Opens M), ∀ v ∈ V, ∃ p ∈ V, C.lt V p v) ∧
    (∀ (V : Opens M), ∀ v ∈ V, ∃ p ∈ V, C.lt V v p) := Iff.rfl
example : C.NoPastEndpoint ↔ ∀ x : M, C.Jminus ⊤ {x} ≠ {x} := Iff.rfl
example : C.NoCausalEndpoint ↔ C.NoPastEndpoint ∧ C.dual.NoPastEndpoint := Iff.rfl
example : C.NoCausalEndpoint ↔ (∀ x : M, C.Jminus ⊤ {x} ≠ {x}) ∧ (∀ x : M, C.Jplus ⊤ {x} ≠ {x}) :=
  Iff.rfl
-- the old second conjuncts, by the projections users write
example (h : C.ChronalNeighbours) : C.dual.ChronalPastNeighbours := h.2
example (h : C.NoCausalEndpoint) : C.dual.NoPastEndpoint := h.2
example (h : C.ChronalPastNeighbours) (h' : C.dual.ChronalPastNeighbours) : C.ChronalNeighbours :=
  ⟨h, h'⟩
example (h : C.NoPastEndpoint) (h' : C.dual.NoPastEndpoint) : C.NoCausalEndpoint := ⟨h, h'⟩
-- the hypotheses hZm, hZp of Lemma K (Causal.LemmaK), by the projections
example (hp : C.PushUp) (h : C.ChronalNeighbours) : C.CausallyOpen :=
  causallyOpen_of_pushUp hp h.1 h.2
end
