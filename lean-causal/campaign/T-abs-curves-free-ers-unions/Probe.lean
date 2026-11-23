import Lean
import Causal.AbstractDev
import Causal.ArcConnected
import Causal.CBG.CausalConvex
import Causal.CBG.FamilyGluing
import Causal.CBG.Injective
import Causal.CBG.SubExtensionAbstract
import Causal.CExtConnexeCauchy.Basic
import Causal.CExtConnexeCauchy.SubArc
import Causal.CExtConnexeSecondCountable
import Causal.Cauchy
import Causal.CauchyDiamond
import Causal.CauchyDual
import Causal.CauchyExtension
import Causal.CauchySeparation
import Causal.CausalIsoInvariance
import Causal.Causality
import Causal.CausallyPlainLocZ
import Causal.Chains
import Causal.ChronalNeighbourBridge
import Causal.ChronalNeighbourConjoined
import Causal.ChronalTarentin
import Causal.CompactCauchy
import Causal.CompactMinimal
import Causal.CorrespondingPoints
import Causal.CorrespondingSpacelike
import Causal.CurveComponents
import Causal.Curves
import Causal.CurvesExtend
import Causal.CurvesExtendSecondCountable
import Causal.CurvesFreeCauchy.Basic
import Causal.CurvesFreeCauchy.CausalConvex
import Causal.CurvesFreeCauchy.CompactCauchy
import Causal.CurvesFreeLemmaK.Bare
import Causal.CurvesFreeLemmaK.Local
import Causal.CurvesFreeLemmaK.Reduction
import Causal.CurvesFreeLemmaK.SC
import Causal.CutLineInextensible
import Causal.Dec8MinimalWitness
import Causal.DependenceDomain
import Causal.DeuxPushup
import Causal.Ers464SecondCountable
import Causal.Ers475CauchyForm
import Causal.ErsMughd
import Causal.ErsSecondCountable
import Causal.ErsUnions
import Causal.ErsUniqueness
import Causal.GHWithoutTarentin
import Causal.GXSingular
import Causal.GXStructure
import Causal.Galileo
import Causal.GateLineLocal
import Causal.Generated
import Causal.Geroch
import Causal.GlobalHyperbolicity
import Causal.GluingCompact
import Causal.GluingGeneric.Basic
import Causal.GluingGeneric.GX
import Causal.GluingGeneric.Generated
import Causal.GluingGeneric.Linear
import Causal.GluingGeneric.OfRelation
import Causal.GluingGeneric.Pullback
import Causal.GluingHausdorff
import Causal.GluingModels.Minimal
import Causal.GluingModels.NonMinimal
import Causal.GluingModels.Pushout
import Causal.GluingModels.Tools
import Causal.HalfLitDual
import Causal.Inextensible
import Causal.InextensibleNestedBasics
import Causal.InextensiblePiece
import Causal.Ladder.Basic
import Causal.Ladder.Dual
import Causal.Ladder.DualTest
import Causal.Ladder.Rules
import Causal.Ladder.Test
import Causal.LadderLocal
import Causal.LemmaK
import Causal.LemmaKBare
import Causal.LemmaKLocal
import Causal.LemmaKObstruction
import Causal.LemmaKReduction
import Causal.LemmaKSC
import Causal.LemmaKSCLocal
import Causal.LevinTimeFunction
import Causal.LevinUtility
import Causal.LineDevelopment
import Causal.Lines
import Causal.LinesCurves
import Causal.LinesReachable
import Causal.Local
import Causal.LocateExtension
import Causal.MaximalZorn
import Causal.Measure
import Causal.MeasureLocal
import Causal.MeasureRemarks
import Causal.MeasureSum
import Causal.Minimal
import Causal.Morphism
import Causal.NestedCausalities
import Causal.NestedConverse
import Causal.NestedTransfer
import Causal.NotchedPlane
import Causal.OmegaOneConstant
import Causal.OneWayMembrane
import Causal.OneWayMembraneChronal
import Causal.Properties
import Causal.PushUp
import Causal.PushUpNotOpen
import Causal.PushUpOfMinimalLocal
import Causal.Pushout
import Causal.PushoutCausal
import Causal.RationalJumpPlane
import Causal.RationalLineExtras
import Causal.Reachable
import Causal.SCOpenWithoutTarentin
import Causal.SFATransfer
import Causal.SbierskiProp37
import Causal.SchwCausalLemmas
import Causal.StrongCausality
import Causal.SubExtension
import Causal.Subdivision
import Causal.TimelikeHomotopy
import Causal.TransparentLine

/-!
# T-abs-curves-free-ers-unions: the curve-binder scan of the ETT layer, and the pair check

Imports every ETT-layer module of `lean-causal` (the 123 `Causal.*` modules with
`tools/ladder.py`'s `model_path` = None on 2026-11-23). Run from `lean-causal/`:

    taskset -c 0-11 lake env lean campaign/T-abs-curves-free-ers-unions/Probe.lean > /tmp/probe.out

`#curve_scan` (kb/0259) runs `forallTelescope` on the type of every declaration of every
imported `Causal.*` module and prints one `BINDERS {json}` line for each declaration that has a
binder whose elaborated type mentions `Causality.CurvesExtend`, `CurvesExtendOn`,
`InextensibleThrough`, `SplitBy`, or (inline) `Inextensible`, `Extensible`,
`FutureInextensible`, `PastInextensible`; or a `[SecondCountableTopology _]` binder (the
candidate forms); or, for a definition, a body that mentions one of the flagged constants.
The `name`/`binders`/`concl` keys are kb/0227's format, so
`campaign/T-abs-curves-free-cauchy/binders_diff.py` reads the output unchanged.
`scan_table.py` (beside this file) turns the `BINDERS` lines into `scan.json`: each flagged
declaration with its covering form, if any.

Then, for the 13 pairs of `binders_pairs.json` (the 10 originals of `Causal.ErsUnions` and
`Causal.ErsMughd` with a `CurvesExtend(On)` binder and their forms, and the 3 `SplitBy`
originals with their trade siblings): `#binders_explicit` (`EXPLICIT` lines, the same check
under `pp.explicit`; output with the default one in `binders_diff.txt`), `#used_by` (`USEDBY`
lines: where each form and each original is used), and `#print axioms` of the 10 covering forms
(`axioms.txt`).
-/

open Lean Meta Elab Command

/-- The constants whose mention in a binder's elaborated type flags the binder (kb/0259). -/
def curveFlagNames : Array Name :=
  #[``Causal.Causality.CurvesExtend, ``Causal.Causality.CurvesExtendOn,
    ``Causal.Causality.InextensibleThrough, ``Causal.Causality.SplitBy,
    ``Causal.Causality.Inextensible, ``Causal.Causality.Extensible,
    ``Causal.Causality.FutureInextensible, ``Causal.Causality.PastInextensible]

def biStr : BinderInfo → String
  | .default => "()" | .implicit => "{}" | .strictImplicit => "⦃⦄" | .instImplicit => "[]"

/-- `s` is `pre` followed by digits only (`match_1`, `proof_2`, `eq_1`). -/
def numbered (pre s : String) : Bool :=
  let t := (s.drop pre.length).toString
  s.startsWith pre && !t.isEmpty && t.all Char.isDigit

/-- Auxiliary declarations the scan skips: internal names, recursors, matchers, generated
equation and injectivity lemmas, auxiliary proofs. -/
def skipName (env : Environment) (n : Name) : Bool :=
  n.isInternal || isAuxRecursor env n || isNoConfusion env n || Meta.isMatcherCore env n ||
  match n with
  | .str _ s => numbered "match_" s || numbered "proof_" s || numbered "eq_" s || s == "eq_def" ||
      ["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow",
        "noConfusionType", "noConfusion", "injEq", "inj", "sizeOf_spec", "ctorIdx",
        "toCtorIdx", "ctorElim", "ctorElimType"].contains s
  | _ => false

def kindStr : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .ctorInfo _ => "ctor"
  | .inductInfo _ => "inductive" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
  | _ => "other"

/-- The record of one declaration, or `none` when it has no flagged binder, no second countable
instance binder and (for a definition) no flagged constant in its body. -/
def declRecord (mod n : Name) (ci : ConstantInfo) : MetaM (Option Json) := do
  let bodyHits : Array Name := match ci with
    | .defnInfo d => curveFlagNames.filter d.value.getUsedConstants.contains
    | _ => #[]
  let pre ← forallTelescope ci.type fun xs _ => do
    let mut hit := false
    for x in xs do
      let d ← x.fvarId!.getDecl
      let used := d.type.getUsedConstants
      if curveFlagNames.any used.contains then hit := true
      if d.binderInfo == .instImplicit && used.contains ``SecondCountableTopology then hit := true
    return hit
  unless pre || !bodyHits.isEmpty do return none
  let line ← match ← findDeclarationRanges? n with
    | some r => pure (Json.num r.selectionRange.pos.line)
    | none => pure Json.null
  forallTelescope ci.type fun xs body => do
    let mut arr : Array Json := #[]
    let mut flagged : Array Json := #[]
    let mut sc := false
    for x in xs do
      let d ← x.fvarId!.getDecl
      let bi := biStr d.binderInfo
      let nm := if d.binderInfo == .instImplicit then "_inst"
        else d.userName.eraseMacroScopes.toString
      let ty := toString (← ppExpr d.type)
      let used := d.type.getUsedConstants
      let hits := curveFlagNames.filter used.contains
      if d.binderInfo == .instImplicit && used.contains ``SecondCountableTopology then sc := true
      unless hits.isEmpty do
        flagged := flagged.push <| Json.mkObj [("index", Json.num arr.size), ("bi", Json.str bi),
          ("name", Json.str d.userName.eraseMacroScopes.toString), ("type", Json.str ty),
          ("flags", Json.arr (hits.map fun h => Json.str h.toString))]
      arr := arr.push (Json.arr #[Json.str bi, Json.str nm, Json.str ty])
    let concl := toString (← ppExpr body)
    return some <| Json.mkObj [("name", Json.str n.toString), ("module", Json.str mod.toString),
      ("line", line), ("kind", Json.str (kindStr ci)),
      ("levelParams", Json.arr (ci.levelParams.toArray.map fun l => Json.str l.toString)),
      ("binders", Json.arr arr), ("concl", Json.str concl), ("flagged", Json.arr flagged),
      ("secondCountable", Json.bool sc),
      ("bodyFlags", Json.arr (bodyHits.map fun h => Json.str h.toString))]

/-- `#curve_scan`: one `BINDERS` line per recorded declaration of every imported `Causal.*`
module, then one `SCANNED` line with the module and declaration counts. -/
elab "#curve_scan" : command => do
  let env ← getEnv
  let mut nmods := 0
  let mut ndecls := 0
  for i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    unless (`Causal).isPrefixOf mod do continue
    nmods := nmods + 1
    for n in env.header.moduleData[i]!.constNames do
      if skipName env n then continue
      let some ci := env.find? n | continue
      ndecls := ndecls + 1
      let r ← liftTermElabM <| declRecord mod n ci
      if let some j := r then logInfo m!"BINDERS {j.compress}"
  logInfo m!"SCANNED {nmods} modules, {ndecls} declarations"

#curve_scan

/-! ### The pair check with every argument shown (`pp.explicit`)

`#binders_explicit n` prints one `EXPLICIT {json}` line in kb/0227's format, with `pp.explicit`
on and each instance binder renamed to its own type, so that an inserted instance does not
renumber the `inst✝` names of the binders after it. -/

elab "#binders_explicit " n:ident : command => do
  let some ci := (← getEnv).find? n.getId | throwError "unknown {n.getId}"
  let s ← liftTermElabM <| withOptions (fun o => o.setBool `pp.explicit true) <|
    forallTelescope ci.type fun xs body => do
      let mut lctx ← getLCtx
      let mut arr : Array Json := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        let ty := toString (← withLCtx lctx (← getLocalInstances) (ppExpr d.type))
        if d.binderInfo == .instImplicit then
          lctx := lctx.setUserName x.fvarId! (Name.mkSimple s!"inst[{ty}]")
        let nm := if d.binderInfo == .instImplicit then "_inst"
          else d.userName.eraseMacroScopes.toString
        arr := arr.push (Json.arr #[Json.str (biStr d.binderInfo), Json.str nm, Json.str ty])
      let concl := toString (← withLCtx lctx (← getLocalInstances) (ppExpr body))
      return (Json.mkObj [("name", Json.str n.getId.toString), ("binders", Json.arr arr),
        ("concl", Json.str concl),
        ("levelParams", Json.arr (ci.levelParams.toArray.map fun l => Json.str l.toString))]).compress
  logInfo m!"EXPLICIT {s}"

#binders_explicit Causal.Causality.eq_of_mem_of_curvesExtendOn
#binders_explicit Causal.Causality.eq_of_mem_of_t1_secondCountable
#binders_explicit Causal.Causality.IsCauchySurfaceOn.of_subset_of_curvesExtendOn
#binders_explicit Causal.Causality.IsCauchySurfaceOn.of_subset_of_t1_secondCountable
#binders_explicit Causal.Causality.isCauchySurfaceOn_sSup_of_curvesExtendOn
#binders_explicit Causal.Causality.isCauchySurfaceOn_sSup_of_secondCountable
#binders_explicit Causal.Causality.globallyHyperbolicOn_sSup_of_pieces
#binders_explicit Causal.Causality.globallyHyperbolicOn_sSup_of_pieces_secondCountable
#binders_explicit Causal.Causality.IsCommonDevelopment.globallyHyperbolicOn
#binders_explicit Causal.Causality.IsCommonDevelopment.globallyHyperbolicOn_secondCountable
#binders_explicit Causal.Causality.ers_remark_4_67_globallyHyperbolicOn
#binders_explicit Causal.Causality.ers_remark_4_67_globallyHyperbolicOn_secondCountable
#binders_explicit Causal.Causality.ers_prop_4_63_globallyHyperbolicOn
#binders_explicit Causal.Causality.ers_prop_4_63_globallyHyperbolicOn_secondCountable
#binders_explicit Causal.IsMDevelopment.isUniqueDevelopment
#binders_explicit Causal.IsMDevelopment.isUniqueDevelopment_secondCountable
#binders_explicit Causal.ers_theorem_4_79
#binders_explicit Causal.ers_theorem_4_79_secondCountable
#binders_explicit Causal.ers_theorem_4_80
#binders_explicit Causal.ers_theorem_4_80_secondCountable
#binders_explicit Causal.Causality.ers_theorem_4_64_of_localUniqueness
#binders_explicit Causal.Causality.ers_theorem_4_64_of_localUniqueness_of_isCauchySurfaceOn_secondCountable
#binders_explicit Causal.Causality.maxDevelopmentIn_eq
#binders_explicit Causal.Causality.maxDevelopmentIn_eq_of_isCauchySurfaceOn_secondCountable
#binders_explicit Causal.Causality.ers_theorem_4_64_in
#binders_explicit Causal.Causality.ers_theorem_4_64_in_of_isCauchySurfaceOn_secondCountable

/-! ### Where each covering form is used

`#used_by n` prints one `USEDBY` line: the declarations of the imported `Causal.*` modules whose
proof term mentions `n` directly (a witness on the timelike line, or a form built on it). -/

elab "#used_by " n:ident : command => do
  let env ← getEnv
  let mut users : Array String := #[]
  for i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    unless (`Causal).isPrefixOf mod do continue
    for c in env.header.moduleData[i]!.constNames do
      if skipName env c then continue
      let some ci := env.find? c | continue
      let v? : Option Expr := match ci with
        | .thmInfo t => some t.value | .defnInfo d => some d.value
        | .opaqueInfo o => some o.value | _ => none
      if let some v := v? then
        if v.getUsedConstants.contains n.getId then users := users.push s!"{c} ({mod})"
  logInfo m!"USEDBY {n.getId}: {users.toList}"

#used_by Causal.Causality.eq_of_mem_of_t1_secondCountable
#used_by Causal.Causality.IsCauchySurfaceOn.of_subset_of_t1_secondCountable
#used_by Causal.Causality.isCauchySurfaceOn_sSup_of_secondCountable
#used_by Causal.Causality.globallyHyperbolicOn_sSup_of_pieces_secondCountable
#used_by Causal.Causality.IsCommonDevelopment.globallyHyperbolicOn_secondCountable
#used_by Causal.Causality.ers_remark_4_67_globallyHyperbolicOn_secondCountable
#used_by Causal.Causality.ers_prop_4_63_globallyHyperbolicOn_secondCountable
#used_by Causal.IsMDevelopment.isUniqueDevelopment_secondCountable
#used_by Causal.ers_theorem_4_79_secondCountable
#used_by Causal.ers_theorem_4_80_secondCountable

-- the originals, for comparison
#used_by Causal.Causality.eq_of_mem_of_curvesExtendOn
#used_by Causal.Causality.IsCauchySurfaceOn.of_subset_of_curvesExtendOn
#used_by Causal.Causality.isCauchySurfaceOn_sSup_of_curvesExtendOn
#used_by Causal.Causality.globallyHyperbolicOn_sSup_of_pieces
#used_by Causal.Causality.IsCommonDevelopment.globallyHyperbolicOn
#used_by Causal.Causality.ers_remark_4_67_globallyHyperbolicOn
#used_by Causal.Causality.ers_prop_4_63_globallyHyperbolicOn
#used_by Causal.IsMDevelopment.isUniqueDevelopment
#used_by Causal.ers_theorem_4_79
#used_by Causal.ers_theorem_4_80

/-! The covering forms of `Causal.ErsUnions`' and `Causal.ErsMughd`'s curve binders. -/

#print axioms Causal.Causality.eq_of_mem_of_t1_secondCountable
#print axioms Causal.Causality.IsCauchySurfaceOn.of_subset_of_t1_secondCountable
#print axioms Causal.Causality.isCauchySurfaceOn_sSup_of_secondCountable
#print axioms Causal.Causality.globallyHyperbolicOn_sSup_of_pieces_secondCountable
#print axioms Causal.Causality.IsCommonDevelopment.globallyHyperbolicOn_secondCountable
#print axioms Causal.Causality.ers_remark_4_67_globallyHyperbolicOn_secondCountable
#print axioms Causal.Causality.ers_prop_4_63_globallyHyperbolicOn_secondCountable
#print axioms Causal.IsMDevelopment.isUniqueDevelopment_secondCountable
#print axioms Causal.ers_theorem_4_79_secondCountable
#print axioms Causal.ers_theorem_4_80_secondCountable
