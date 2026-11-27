import Lean
import CausalScaffold.Ers464WithoutArc

/-! T-abs-ers-4-64-without-arc: the statements and axioms of the module's declarations, and the
layer-1 check of its compiled import closure. Run from lean-causal/:
    lake env lean campaign/T-abs-ers-4-64-without-arc/Probe.lean -/

open Lean Elab Command in
/-- The modules of the environment under a model prefix (tools/ladder.py MODEL_LAYER). -/
elab "#modelModules" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let pre := ["Causal.Minkowski", "Causal.Static", "Causal.SingularFlat", "Causal.Flat",
    "Causal.Model", "Causal.Port"]
  let bad := mods.filter fun m =>
    pre.any fun p => m.toString == p || m.toString.startsWith (p ++ ".")
  logInfo m!"modules in the closure: {mods.size}; under a model prefix: {bad.size} {bad.toList}"

#modelModules

open Causal

#check @Causal.Causality.isCommonDevelopment_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable
#check @Causal.Causality.ers_theorem_4_64_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.Causality.ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.Causality.ers_theorem_4_64_of_localUniqueness_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.Causality.ers_remark_4_67_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.Causality.ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.Causality.ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.Causality.ers_corollary_4_69_of_isCauchySurface_secondCountable_noArc
#check @Causal.Causality.ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.Causality.ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.IsMDevelopment.isUniqueDevelopment_secondCountable_noArc
#check @Causal.ErsNoArcWitness.clampAgree
#check @Causal.ErsNoArcWitness.agreementGlues_clampAgree
#check @Causal.ErsNoArcWitness.clampAgree_of_subset
#check @Causal.ErsNoArcWitness.coe_top_inf_ersWitnessIoo
#check @Causal.ErsNoArcWitness.le_top_iff
#check @Causal.ErsNoArcWitness.data
#check @Causal.ErsNoArcWitness.conclusions
#check @Causal.ErsNoArcWitness.corollaries
#check @Causal.timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc
#check @Causal.densCausality_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc

#print axioms Causal.Causality.isCommonDevelopment_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.Causality.ers_theorem_4_64_maxCommonDevelopment_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.Causality.ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.Causality.ers_theorem_4_64_of_localUniqueness_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.Causality.ers_remark_4_67_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.Causality.ers_corollary_4_68_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.Causality.ers_corollary_4_68_eqOn_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.Causality.ers_corollary_4_69_of_isCauchySurface_secondCountable_noArc
#print axioms Causal.Causality.ers_corollary_4_71_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.Causality.ers_corollary_4_73_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.IsMDevelopment.isUniqueDevelopment_secondCountable_noArc
#print axioms Causal.ErsNoArcWitness.agreementGlues_clampAgree
#print axioms Causal.ErsNoArcWitness.clampAgree_of_subset
#print axioms Causal.ErsNoArcWitness.coe_top_inf_ersWitnessIoo
#print axioms Causal.ErsNoArcWitness.le_top_iff
#print axioms Causal.ErsNoArcWitness.data
#print axioms Causal.ErsNoArcWitness.conclusions
#print axioms Causal.ErsNoArcWitness.corollaries
#print axioms Causal.timelikeLine_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc
#print axioms Causal.densCausality_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc
