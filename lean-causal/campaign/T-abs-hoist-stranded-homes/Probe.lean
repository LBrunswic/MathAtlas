import Causal

/-! T-abs-hoist-stranded-homes: the moved and new declarations resolve under their full names, in
their new modules, and depend on the standard axioms only. The citers' axioms are listed too. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for n in [``Causal.ChartIso.curveOn_symm, ``Causal.chartImage_subset_target,
      ``Causal.ChartIso.chronalCurveOn_image, ``Causal.ChartIso.chronalCurveOn_symm_image,
      ``Causal.Causality.hasChronalNeighbourEverywhere_of_forall_mem_Zplus,
      ``Causal.E0LM.LocZplus.chronalFutureNeighbours, ``Causal.Flat.curveOn_chart_symm,
      ``Causal.Causality.SingularFlatAxioms.hasChronalNeighbourEverywhere,
      ``Causal.E0.chronalFutureNeighbours, ``Causal.SFALocal.hasChronalNeighbourEverywhere,
      ``Causal.SFALocal.chronalFutureNeighbours, ``Causal.SFALocalE0.hasChronalNeighbourEverywhere,
      ``Causal.SFALocalE0.chronalFutureNeighbours] do
    let some idx := env.getModuleIdxFor? n | IO.println s!"{n}: not found"
    IO.println s!"{n}: {env.header.moduleNames[idx.toNat]!}"

-- moved
#print axioms Causal.ChartIso.curveOn_symm
#print axioms Causal.chartImage_subset_target
#print axioms Causal.ChartIso.chronalCurveOn_image
#print axioms Causal.ChartIso.chronalCurveOn_symm_image
-- new
#print axioms Causal.Causality.hasChronalNeighbourEverywhere_of_forall_mem_Zplus
#print axioms Causal.E0LM.LocZplus.chronalFutureNeighbours
-- citers
#print axioms Causal.Flat.curveOn_chart_symm
#print axioms Causal.Causality.SingularFlatAxioms.hasChronalNeighbourEverywhere
#print axioms Causal.E0.chronalFutureNeighbours
#print axioms Causal.SFALocal.hasChronalNeighbourEverywhere
#print axioms Causal.SFALocal.chronalFutureNeighbours
#print axioms Causal.SFALocalE0.hasChronalNeighbourEverywhere
#print axioms Causal.SFALocalE0.chronalFutureNeighbours

-- the statements of the two new lemmas
#check @Causal.Causality.hasChronalNeighbourEverywhere_of_forall_mem_Zplus
#check @Causal.E0LM.LocZplus.chronalFutureNeighbours
