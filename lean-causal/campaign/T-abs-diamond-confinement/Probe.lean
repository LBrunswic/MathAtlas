import CausalScaffold.DiamondConfinement

/-! Probe of `CausalScaffold.DiamondConfinement` (T-abs-diamond-confinement): the type and the
axioms of every declaration of the module. Output: `axioms.txt`. -/

open Causal

#check @Causal.CurveOn.exists_concat_mid
#check @Causal.Causality.ChronalHomotopyOn.mapsTo_of_closure_subset
#check @Causal.Causality.ChronalHomotopyOn.inf_of_closure_subset
#check @Causal.Causality.ChronalHomotopyOn.mem_Iplus_inter_Iminus_of_closure_subset
#check @Causal.Causality.closure_Iplus_inter_Iminus_subset_of_lt
#check @Causal.Causality.ChronalHomotopyOn.mapsTo_of_closure_subset_of_lt
#check @Causal.Causality.FutureOneConnectedOn.chronalCurveOn_inf_of_closure_subset
#check @Causal.Causality.Iplus_inter_Iminus_subset_inf_of_futureOneConnectedOn
#check @Causal.Causality.Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn
#check @Causal.Causality.Iplus_inter_Iminus_subset_of_futureOneConnectedOn
#check @Causal.Causality.Iplus_inter_Iminus_subset_of_futureOneConnectedOn_of_lt
#check @Causal.Causality.Iplus_inter_Iminus_eq_of_futureOneConnected
#check @Causal.Causality.StronglyCausalOn
#check @Causal.Causality.LocallyStronglyCausal
#check @Causal.Causality.stronglyCausalOn_top
#check @Causal.Causality.StronglyCausalOn.mono
#check @Causal.Causality.dual_stronglyCausalOn
#check @Causal.Causality.dual_locallyStronglyCausal
#check @Causal.Causality.StronglyCausal.locallyStronglyCausal
#check @Causal.Causality.locallyStronglyCausal_iff_nhds
#check @Causal.Causality.diamond_subset_of_causallyConvexIn
#check @Causal.Causality.StronglyCausalOn.exists_closure_subset
#check @Causal.Causality.StronglyCausalOn.exists_isCompact_closure
#check @Causal.Causality.LocallyStronglyCausal.exists_isCompact_closure
#check @Causal.Causality.LocallyStronglyCausal.exists_diamond_identification
#check @Causal.timelikeLine_confinement
#check @Causal.timelikeLine_diamond_identification
#check @Causal.timelikeLine_locallyStronglyCausal
#check @Causal.timelikeLine_exists_isCompact_closure
#check @Causal.exists_confining_not_locallyStronglyCausal

#print axioms Causal.CurveOn.exists_concat_mid
#print axioms Causal.Causality.ChronalHomotopyOn.mapsTo_of_closure_subset
#print axioms Causal.Causality.ChronalHomotopyOn.inf_of_closure_subset
#print axioms Causal.Causality.ChronalHomotopyOn.mem_Iplus_inter_Iminus_of_closure_subset
#print axioms Causal.Causality.closure_Iplus_inter_Iminus_subset_of_lt
#print axioms Causal.Causality.ChronalHomotopyOn.mapsTo_of_closure_subset_of_lt
#print axioms Causal.Causality.FutureOneConnectedOn.chronalCurveOn_inf_of_closure_subset
#print axioms Causal.Causality.Iplus_inter_Iminus_subset_inf_of_futureOneConnectedOn
#print axioms Causal.Causality.Iplus_inter_Iminus_eq_inf_of_futureOneConnectedOn
#print axioms Causal.Causality.Iplus_inter_Iminus_subset_of_futureOneConnectedOn
#print axioms Causal.Causality.Iplus_inter_Iminus_subset_of_futureOneConnectedOn_of_lt
#print axioms Causal.Causality.Iplus_inter_Iminus_eq_of_futureOneConnected
#print axioms Causal.Causality.StronglyCausalOn
#print axioms Causal.Causality.LocallyStronglyCausal
#print axioms Causal.Causality.stronglyCausalOn_top
#print axioms Causal.Causality.StronglyCausalOn.mono
#print axioms Causal.Causality.dual_stronglyCausalOn
#print axioms Causal.Causality.dual_locallyStronglyCausal
#print axioms Causal.Causality.StronglyCausal.locallyStronglyCausal
#print axioms Causal.Causality.locallyStronglyCausal_iff_nhds
#print axioms Causal.Causality.diamond_subset_of_causallyConvexIn
#print axioms Causal.Causality.StronglyCausalOn.exists_closure_subset
#print axioms Causal.Causality.StronglyCausalOn.exists_isCompact_closure
#print axioms Causal.Causality.LocallyStronglyCausal.exists_isCompact_closure
#print axioms Causal.Causality.LocallyStronglyCausal.exists_diamond_identification
#print axioms Causal.timelikeLine_confinement
#print axioms Causal.timelikeLine_diamond_identification
#print axioms Causal.timelikeLine_locallyStronglyCausal
#print axioms Causal.timelikeLine_exists_isCompact_closure
#print axioms Causal.exists_confining_not_locallyStronglyCausal
