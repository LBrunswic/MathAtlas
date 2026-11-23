import CausalScaffold.TimelikeHomotopy

/-! Probe for T-abs-timelike-homotopy: the statements and the axioms of the main declarations of
`CausalScaffold.TimelikeHomotopy`. Run with
`taskset -c 0-11 lake env lean campaign/T-abs-timelike-homotopy/Probe.lean`. -/

open Causal

#check @Causal.Causality.ChronalHomotopyOn
#check @Causal.Causality.ChronallyHomotopicOn
#check @Causal.Causality.FutureOneConnectedOn
#check @Causal.Causality.FutureOneConnected
#print Causal.Causality.FutureOneConnectedOn
#print axioms Causal.Causality.ChronalCurveOn.lt_self_of_eq
#print axioms Causal.Causality.ChronalCurveOn.injOn
#print axioms Causal.Causality.ChronalHomotopyOn.mapsTo
#print axioms Causal.Causality.ChronalHomotopyOn.chronalCurveOn_left
#print axioms Causal.Causality.ChronalHomotopyOn.chronalCurveOn_right
#print axioms Causal.Causality.ChronalHomotopyOn.right_zero
#print axioms Causal.Causality.ChronalHomotopyOn.right_one
#print axioms Causal.Causality.ChronalHomotopyOn.congr_left
#print axioms Causal.Causality.ChronalHomotopyOn.congr_right
#print axioms Causal.Causality.ChronalHomotopyOn.mono_opens
#print axioms Causal.Causality.ChronalHomotopyOn.restrict
#print axioms Causal.Causality.ChronalHomotopyOn.refl
#print axioms Causal.Causality.ChronalHomotopyOn.symm
#print axioms Causal.Causality.ChronalHomotopyOn.trans
#print axioms Causal.Causality.ChronalHomotopyOn.dual
#print axioms Causal.Causality.ChronalHomotopyOn.dual_symm
#print axioms Causal.Causality.ChronalHomotopyOn.congr_lt
#print axioms Causal.Causality.ChronallyHomotopicOn.chronalCurveOn_left
#print axioms Causal.Causality.ChronallyHomotopicOn.chronalCurveOn_right
#print axioms Causal.Causality.ChronallyHomotopicOn.right_zero
#print axioms Causal.Causality.ChronallyHomotopicOn.right_one
#print axioms Causal.Causality.ChronallyHomotopicOn.refl
#print axioms Causal.Causality.ChronallyHomotopicOn.symm
#print axioms Causal.Causality.ChronallyHomotopicOn.trans
#print axioms Causal.Causality.ChronallyHomotopicOn.of_eqOn
#print axioms Causal.Causality.ChronallyHomotopicOn.mono_opens
#print axioms Causal.Causality.ChronallyHomotopicOn.dual
#print axioms Causal.Causality.ChronallyHomotopicOn.comp_reparam
#print axioms Causal.Causality.chronallyHomotopicOn_equivalence
#print axioms Causal.Causality.chronalHomotopySetoid
#print axioms Causal.Causality.dual_chronallyHomotopicOn_iff
#print axioms Causal.Causality.FutureOneConnectedOn.dual
#print axioms Causal.Causality.dual_futureOneConnectedOn
#print axioms Causal.Causality.dual_futureOneConnected
#print axioms Causal.Causality.futureOneConnectedOn_congr_lt
#print axioms Causal.IsCausalIso.chronalHomotopyOn
#print axioms Causal.IsCausalIso.chronallyHomotopicOn_iff
#print axioms Causal.IsCausalIso.futureOneConnectedOn
#print axioms Causal.IsCausalIso.futureOneConnectedOn_iff
#print axioms Causal.IsCausalIso.futureOneConnected_iff
#print axioms Causal.chartImage_subset_target
#print axioms Causal.ChartIso.chronalCurveOn_image
#print axioms Causal.ChartIso.chronalCurveOn_symm_image
#print axioms Causal.ChartIso.chronalHomotopyOn
#print axioms Causal.ChartIso.chronalHomotopyOn_symm
#print axioms Causal.ChartIso.chronallyHomotopicOn_iff
#print axioms Causal.ChartIso.futureOneConnectedOn_iff
#print axioms Causal.timelikeLine_chronalCurveOn_iff
#print axioms Causal.timelikeLine_futureOneConnectedOn
#print axioms Causal.timelikeLine_futureOneConnected
#print axioms Causal.timelikeLine_dual_futureOneConnected
#print axioms Causal.timelikeLine_chronallyHomotopicOn_sq
#print axioms Causal.timelikeLine_not_chronalCurveOn_pause
