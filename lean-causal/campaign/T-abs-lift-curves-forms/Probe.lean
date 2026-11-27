import CausalScaffold.StrongCausalityLiftsCurves

/-! Probe for `T-abs-lift-curves-forms`: run from `lean-causal/` with
`taskset -c 0-11 lake env lean campaign/T-abs-lift-curves-forms/Probe.lean`
after `lake build CausalScaffold.StrongCausalityLiftsCurves`. -/

open Causal

/-! The auditor's probe (AUDIT-1 of T-abs-strong-causality-lifts, F1_minimal_repair), typed by the
harc forms' own types: each is the one-line composition of the general forms with the bridges. -/

example : type_of% @Causality.stronglyCausal_lift_of_le_realised := by
  intro M X _ _ CM CX N τc _ C p D hτ harc hp hD hM hX hB
  exact Causality.stronglyCausal_of_lift τc
    (Causality.mem_connectedComponentIn_diamond_of_curves τc hτ harc)
    (Causality.le_top_map_of_curves harc hp) (Causality.le_top_map_of_curves harc hD) hM hX hB

example : type_of% @Causality.stronglyCausalOpen_lift_of_le_realised := by
  intro M X _ _ CM CX N τc _ C p D hτ harc hp hD hM hX hB
  exact Causality.stronglyCausalOpen_of_lift τc
    (Causality.mem_connectedComponentIn_diamond_of_curves τc hτ harc)
    (Causality.le_top_map_of_curves harc hp) (Causality.le_top_map_of_curves harc hD) hM hX hB

example : type_of% @Causality.alexandrovTopology_eq_lift_of_le_realised := by
  intro M X _ _ CM CX N τc _ C p D hτ harc hT hp hD hM hX hB
  exact Causality.StronglyCausal.alexandrovTopology_eq hT (Causality.stronglyCausal_of_lift τc
    (Causality.mem_connectedComponentIn_diamond_of_curves τc hτ harc)
    (Causality.le_top_map_of_curves harc hp) (Causality.le_top_map_of_curves harc hD) hM hX hB)

/-! Non-vacuity of the harc forms on the timelike line (harc from causal arc-connectedness),
with `τc` the indiscrete topology, strictly coarser than that of `ℝ`. -/

example : timelikeLine.StronglyCausal := by
  obtain ⟨hcac, -, -, hsc, -⟩ := timelikeLine_strongCausalityLift
  exact Causality.stronglyCausal_lift_of_le_realised ⊤ le_top
    (Causality.CausallyArcConnected.exists_causalCurveOn_top hcac) (fun _ hc => hc)
    (fun _ hc => hc) hsc hsc real_hasBasis_connectedComponentIn_top_inter

/-! The declarations. -/

#check @Causality.stronglyCausal_lift_of_le_realised
#check @Causality.alexandrovTopology_eq_lift_of_le_realised
#check @Causality.stronglyCausalOpen_lift_of_le_realised
#check @Causality.stronglyCausal_lift_of_weakMorphism_of_le_realised
#check @Causality.stronglyCausal_lift_self_of_le_realised
#check @orderLine_causalCurveOn_of_timelikeLine
#check @timelikeLine_causalCurveOn_of_orderLine
#check @orderLine_le_realised
#check @orderLine_not_causallyArcConnected
#check @orderLine_strongCausalityLift_of_le_realised
#check @symmRationalLine_not_isCausal
#check @symmRationalLine_not_tarentin
#check @symmRationalLine_not_le_realised
#check @symmRationalLine_separates_lift_glued
#check @not_stronglyCausal_lift_of_curves_glued

#print axioms Causal.Causality.stronglyCausal_lift_of_le_realised
#print axioms Causal.Causality.alexandrovTopology_eq_lift_of_le_realised
#print axioms Causal.Causality.stronglyCausalOpen_lift_of_le_realised
#print axioms Causal.Causality.stronglyCausal_lift_of_weakMorphism_of_le_realised
#print axioms Causal.Causality.stronglyCausal_lift_self_of_le_realised
#print axioms Causal.orderLine_causalCurveOn_of_timelikeLine
#print axioms Causal.timelikeLine_causalCurveOn_of_orderLine
#print axioms Causal.orderLine_le_realised
#print axioms Causal.orderLine_not_causallyArcConnected
#print axioms Causal.orderLine_strongCausalityLift_of_le_realised
#print axioms Causal.symmRationalLine_not_isCausal
#print axioms Causal.symmRationalLine_not_tarentin
#print axioms Causal.symmRationalLine_not_le_realised
#print axioms Causal.symmRationalLine_separates_lift_glued
#print axioms Causal.not_stronglyCausal_lift_of_curves_glued
