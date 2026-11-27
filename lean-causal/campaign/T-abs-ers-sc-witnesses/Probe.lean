import CausalScaffold.ErsSCWitnesses

/-! Probe for T-abs-ers-sc-witnesses: the axioms of every declaration of
`CausalScaffold.ErsSCWitnesses`, and, for each witness, which of the seven (eight) forms its
proof term uses (`USES` lines, read off the constants of the proof's value). -/

open Lean Elab Command in
elab "#uses " w:ident " : " fs:ident* : command => do
  let env ← getEnv
  let wn := w.getId
  let some ci := env.find? wn | throwError "no {wn}"
  let v := match ci with
    | .thmInfo t => t.value
    | _ => default
  -- the constants reachable from the value through declarations of this module (ErsSCWitness.*)
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  for c in v.getUsedConstants do todo := todo.push c
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if (`Causal.ErsSCWitness).isPrefixOf c then
      if let some (.thmInfo t) := env.find? c then
        for d in t.value.getUsedConstants do todo := todo.push d
  for f in fs do
    logInfo m!"USES {wn} {f.getId}: {seen.contains f.getId}"

#uses Causal.timelikeLine_eq_of_mem_of_t1_secondCountable :
  Causal.Causality.eq_of_mem_of_t1_secondCountable
#uses Causal.timelikeLine_isCauchySurfaceOn_of_subset_of_t1_secondCountable :
  Causal.Causality.IsCauchySurfaceOn.of_subset_of_t1_secondCountable
#uses Causal.timelikeLine_isCauchySurfaceOn_sSup_of_secondCountable :
  Causal.Causality.isCauchySurfaceOn_sSup_of_secondCountable
#uses Causal.timelikeLine_globallyHyperbolicOn_sSup_of_pieces_secondCountable :
  Causal.Causality.globallyHyperbolicOn_sSup_of_pieces_secondCountable
#uses Causal.timelikeLine_ers_theorem_4_79_4_80_secondCountable :
  Causal.ers_theorem_4_79_secondCountable Causal.ers_theorem_4_80_secondCountable
  Causal.ers_theorem_4_79 Causal.ers_theorem_4_80
#uses Causal.timelikeLine_isUniqueDevelopment_secondCountable :
  Causal.IsMDevelopment.isUniqueDevelopment_secondCountable
#uses Causal.timelikeLine_isUniqueDevelopment_secondCountable_noArc :
  Causal.IsMDevelopment.isUniqueDevelopment_secondCountable_noArc

#check @Causal.timelikeLine_eq_of_mem_of_t1_secondCountable
#check @Causal.timelikeLine_isCauchySurfaceOn_of_subset_of_t1_secondCountable
#check @Causal.timelikeLine_isCauchySurfaceOn_sSup_of_secondCountable
#check @Causal.timelikeLine_globallyHyperbolicOn_sSup_of_pieces_secondCountable
#check @Causal.timelikeLine_ers_theorem_4_79_4_80_secondCountable
#check @Causal.timelikeLine_isUniqueDevelopment_secondCountable
#check @Causal.timelikeLine_isUniqueDevelopment_secondCountable_noArc

#print axioms Causal.timelikeLine_eq_of_mem_of_t1_secondCountable
#print axioms Causal.timelikeLine_isCauchySurfaceOn_of_subset_of_t1_secondCountable
#print axioms Causal.timelikeLine_isCauchySurfaceOn_sSup_of_secondCountable
#print axioms Causal.timelikeLine_globallyHyperbolicOn_sSup_of_pieces_secondCountable
#print axioms Causal.timelikeLine_ers_theorem_4_79_4_80_secondCountable
#print axioms Causal.timelikeLine_isUniqueDevelopment_secondCountable
#print axioms Causal.timelikeLine_isUniqueDevelopment_secondCountable_noArc
#print axioms Causal.ErsSCWitness.isCauchySurfaceOn_Ioo_center
#print axioms Causal.ErsSCWitness.tarentinOn
#print axioms Causal.ErsSCWitness.antisymm_twoIntervals
#print axioms Causal.ErsSCWitness.isAcausalOn_twoIntervals
#print axioms Causal.ErsSCWitness.isCauchySurfaceOn_twoIntervals
#print axioms Causal.ErsSCWitness.pieces_le
#print axioms Causal.ErsSCWitness.pieces_cauchy
#print axioms Causal.ErsSCWitness.subset_sSup_pieces
#print axioms Causal.ErsSCWitness.sSup_pieces_notMem
#print axioms Causal.ErsSCWitness.isPreconnected_of_isDevelopment
#print axioms Causal.ErsSCWitness.isCommonDevelopment_inf
#print axioms Causal.ErsSCWitness.frontierStaysIn
#print axioms Causal.ErsSCWitness.sliceRestart
#print axioms Causal.ErsSCWitness.mughdData
#print axioms Causal.ErsSCWitness.two_mDevelopments
