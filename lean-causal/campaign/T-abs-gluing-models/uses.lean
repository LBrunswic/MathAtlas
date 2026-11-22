import Causal
open Lean Meta Elab Command

/-- For every declaration listed in `/tmp/gm_decls.txt` (ledger rows, ladder witnesses), the
inventory objects its type or value names directly. -/
elab "#gm_uses" : command => do
  let env ← getEnv
  let objs : List Name := [`Causal.timelikeLine, `Causal.lightlikeLine, `Causal.spacelikeLine,
    `Causal.halfChronoLine, `Causal.pointedLine, `Causal.puncturedPlane, `Causal.halfLightLine,
    `Causal.rationalLine, `Causal.isolatedLine, `Causal.closedHalfLine, `Causal.cutLine,
    `Causal.transparentLine, `Causal.rationalJumpPlane, `Causal.notchedCausality,
    `Causal.oneWayMembrane, `Causal.chronalMembrane, `Causal.arcCausality, `Causal.forkCausality,
    `Causal.loopFan, `Causal.veeCausality, `Causal.sierpinskiCausality, `Causal.diagonalCausality,
    `Causal.pointSpace, `Causal.gateLine, `Causal.jumpLine, `Causal.globalLine, `Causal.deuxPushup,
    `Causal.timelikeLineTop, `Causal.pointedLineMR, `Causal.orderLine, `Causal.totalLine,
    `Causal.bowtie, `Causal.fan, `Causal.linearCausality, `Causal.doubledLine,
    `Causal.LineDevelopment.allRelated, `Causal.galileoOn, `Causal.galileo,
    `Causal.DensWitness.densCausality, `Causal.DensWitness.bigCausality,
    `Causal.DensWitness.wideCausality, `Causal.DensWitness.far2Causality,
    `Causal.Causality.topEnlarge, `Causal.SFATransfer.topTotal, `Causal.minkowski,
    `Causal.staticCausality, `Causal.massive, `Causal.cosmicString, `Causal.Flat.flatCausality,
    `Causal.Flat.timeCylinder, `Causal.Flat.isomTransport, `Causal.slopeCone,
    `Causal.spokesCausality, `Causal.AESupportCounterexample.segCausality, `Causal.E0.causality,
    `Causal.CupCapBTZCounterexample.natCausality, `Causal.massiveOf, `Causal.massAModelCausality,
    `Causal.sourceLine, `Causal.radialLine, `Causal.CBG.branchingCausality,
    `Causal.CBG.chartedCausality, `Causal.Causality.withoutChronology,
    `Causal.Causality.SingularFlatAxioms]
  let lines ← IO.FS.lines "/tmp/gm_decls.txt"
  for l in lines do
    match l.splitOn "\t" with
    | [n, labels] =>
      let nm := n.toName
      match env.find? nm with
      | none => pure ()
      | some ci =>
        let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
        let hit := objs.filter fun o => used.contains o
        unless hit.isEmpty do
          IO.println s!"{n}\t{hit}\t{labels}"
    | _ => pure ()

#gm_uses
