import GXScaffold.BBS.HSDegree
open Lean Elab Command

/-- Every declaration of the module `GXScaffold.BBS.HSDegree`, with the axioms outside
`propext`, `Classical.choice`, `Quot.sound` it depends on (expected: none). -/
elab "#sweep" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `GXScaffold.BBS.HSDegree | throwError "no module"
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
#print axioms GX.bbsrem_degk_link_hs
#print axioms GX.GammaLinkCircle.IsLiftedDev.exists_degree_two_cover
#print axioms GX.GammaLinkCircle.IsLiftedDev.exists_kfold_cover_of_degree_two
#print axioms GX.GammaLinkCircle.IsLiftedDev.kfold_sign
#print axioms GX.susp_kfold_branched_cover
#print axioms GX.exists_spacelike_degree_two_mul
#print axioms GX.exists_lightlike_degree_two_mul
