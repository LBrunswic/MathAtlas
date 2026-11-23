import GXScaffold.BBS.HSSingularities
open Lean Elab Command

/-- Every declaration of the module `GXScaffold.BBS.HSSingularities`, with the axioms outside
`propext`, `Classical.choice`, `Quot.sound` it depends on (expected: none). -/
elab "#sweep" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `GXScaffold.BBS.HSSingularities | throwError "no module"
  let mut n := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (c, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? c == some idx then
      n := n + 1
      let axs ← liftCoreM (Lean.collectAxioms c)
      let extra := axs.filter fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]
      if !extra.isEmpty then bad := bad.push (c, extra)
  logInfo m!"{n} declarations; non-standard axioms: {bad}"

#sweep
#print axioms GX.GammaLinkCircle.IsLiftedDev.isElliptic_of_timelike
#print axioms GX.GammaLinkCircle.IsLiftedDev.isParabolic_of_null
#print axioms GX.GammaLinkCircle.IsLiftedDev.spacelike_degree_zero
#print axioms GX.GammaLinkCircle.IsLiftedDev.spacelike_degree_zero_misner
#print axioms GX.GammaLinkCircle.IsLiftedDev.null_degree_zero
#print axioms GX.GammaLinkCircle.IsLiftedDev.bdPlus_degree_zero
#print axioms GX.GammaLinkCircle.IsLiftedDev.bdMinus_degree_zero
#print axioms GX.GammaLinkCircle.IsLiftedDev.null_degree_zero_ne
#print axioms GX.GammaLinkCircle.IsLiftedDev.iPlus_components
#print axioms GX.connectedComponentIn_iUnion_Ioo_two
