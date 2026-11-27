import CausalScaffold.DensSeparates

/-! Probe for T-abs-dens-separates (2026-11-27). It runs `#check` and `#print axioms` on every
declaration of `CausalScaffold.DensSeparates`, and the output is `axioms.txt`. The `example`s read
off the one witness the conjunctions an entry would need: the proposed `[[fails]]`
`[globally_hyperbolic, tarentin] ⇏ causally_arc_connected`, the target's nine assertions, and the
three `[[open]]` pairs the full form settles in the no-gluing reading. Not built by lake. -/

open Causal Causal.DensWitness

#check @densCausality_lt_of_timelike
#check @densCausality_pushUp
#check @chronalNeighbours_of_timelike
#check @chronalCurveOn_iff_timelike
#check @futureOneConnectedOn_of_timelike
#check @densCausality_separates

#print axioms densCausality_lt_of_timelike
#print axioms densCausality_pushUp
#print axioms chronalNeighbours_of_timelike
#print axioms chronalCurveOn_iff_timelike
#print axioms futureOneConnectedOn_of_timelike
#print axioms densCausality_separates

-- the proposed entry: from [globally_hyperbolic, tarentin], to causally_arc_connected
example : densCausality.GloballyHyperbolic ∧ densCausality.Tarentin ∧
    ¬ densCausality.CausallyArcConnected :=
  let ⟨hGH, hT, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hNAC, _, _⟩ :=
    densCausality_separates
  ⟨hGH, hT, hNAC⟩

-- the three pieces it conjoins, in the forms the ladder comment cites
example : densCausality.GloballyHyperbolicOn ⊤ ∧ densCausality.TarentinOn ⊤ ∧
    ¬ densCausality.CausallyArcConnectedOn ⊤ :=
  let ⟨hGH, hT, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hNAC, _, _⟩ :=
    densCausality_separates
  ⟨hGH, Causality.tarentinOn_top.2 hT, hNAC⟩

-- the target's nine assertions
example : densCausality.GloballyHyperbolic ∧ densCausality.Tarentin ∧ densCausality.IsCausal ∧
    densCausality.CausallyCompact ∧ densCausality.StronglyCausal ∧
    densCausality.HasTimeFunction ∧ densCausality.CurvesExtend ∧
    ¬ densCausality.CausallyArcConnected ∧ ¬ densCausality.AbsolutelyMinimal :=
  let ⟨hGH, hT, hC, hCC, hSC, hTF, hCE, _, _, _, _, _, _, _, _, _, _, _, _, hNAC, hNAM, _⟩ :=
    densCausality_separates
  ⟨hGH, hT, hC, hCC, hSC, hTF, hCE, hNAC, hNAM⟩

-- the [[open]] pairs the full form settles, no-gluing reading only
example : densCausality.ChronalNeighbours ∧ ¬ densCausality.AbsolutelyMinimal :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCN, _, _, _, _, hNAM, _⟩ :=
    densCausality_separates
  ⟨hCN, hNAM⟩

example : densCausality.FutureOneConnected ∧ ¬ densCausality.AbsolutelyMinimal ∧
    ¬ densCausality.CausallyArcConnected :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hF, _, hNAC, hNAM, _⟩ :=
    densCausality_separates
  ⟨hF, hNAM, hNAC⟩
