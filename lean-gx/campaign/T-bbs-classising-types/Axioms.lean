import GXScaffold.BBS.HSClassification
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mod := `GXScaffold.BBS.HSClassification
  let some idx := env.getModuleIdx? mod | throwError "no module"
  let mut n := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (c, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? c == some idx && !c.isInternal then
      n := n + 1
      let axs ← liftCoreM (Lean.collectAxioms c)
      let nonstd := axs.filter fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]
      if nonstd.size > 0 then bad := bad.push (c, nonstd)
  logInfo m!"{n} declarations; non-standard: {bad}"
#print axioms GX.GammaLinkCircle.bbsprop_classising_types
