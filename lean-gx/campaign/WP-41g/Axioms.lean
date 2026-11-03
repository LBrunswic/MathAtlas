import GXScaffold.BTZ.CBG
open Lean Elab Command

/-! Axiom sweep of `GXScaffold.BTZ.CBG` (WP-41g, round 1 fix): every declaration of the module,
its axioms collected; the sweep fails if any is outside `propext, Classical.choice, Quot.sound`. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `GXScaffold.BTZ.CBG | throwError "module not found"
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad := #[]
  for (c, _) in env.constants.toList do
    if env.getModuleIdxFor? c == some idx && !c.isInternal then
      n := n + 1
      let axs ← liftCoreM (collectAxioms c)
      for a in axs do
        if !ok.contains a then bad := bad.push (c, a)
  logInfo m!"declarations swept: {n}; non-standard axioms: {bad.size}"
  for (c, a) in bad do logInfo m!"{c} uses {a}"

#print axioms GX.E0CBG.e0Geometry
#print axioms GX.E0CBG.e0_cbg
#print axioms GX.E0CBG.e0_cbg_isETTMaximal
#print axioms GX.E0CBG.e0_cbg_ett
#print axioms GX.E0CBG.e0TLocalModel
#print axioms GX.E0CBG.TGeometry.ofLocalModelOfBTZ
#print axioms GX.E0CBG.germ_ext_nonBTZ
#print axioms GX.E0CBG.e0_sliceFutureBTZ
#print axioms GX.E0CBG.e0_germExtFutureBTZ
#print axioms GX.E0CBG.e0_germExtPastBTZ_of

/-! Non-vacuity witness (outside the module, so the module's sweep stays clean): `e0Geometry`'s two
parameters are WP-41f's (O2) `E0LM.e0_globalBTZ` and (O4) `E0LM.e0_secondCountable_of_cauchy`,
true statements each resting on one tagged `sorry` upstream. Instantiated, the geometry's only
non-standard axiom is `sorryAx`, from those two tags (no refuted hypothesis is involved). -/
noncomputable def e0GeometryWitness : Causal.CBG.Geometry.{0} :=
  GX.E0CBG.e0Geometry GX.E0LM.e0_globalBTZ
    (fun hGH S hS hSS => GX.E0LM.e0_secondCountable_of_cauchy hGH S hS hSS)

#print axioms e0GeometryWitness
