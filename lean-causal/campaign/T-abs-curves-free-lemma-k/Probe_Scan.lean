import Lean
import Causal.LemmaKBare
import Causal.LemmaKReduction
import Causal.LemmaKSC
import Causal.LemmaKLocal
import Causal.LemmaKSCLocal
import Causal.LemmaK
import Causal.LemmaKObstruction
import Causal.LevinUtility
open Lean Meta Elab Command

/-! kb/0259's scan, for the Lemma K family: every public constant of the eight modules, its
elaborated binders, and a flag on each binder whose type mentions a curve notion
(`CurvesExtend`, `CurvesExtendOn`, `InextensibleThrough`, `SplitBy`, `Inextensible`). One JSON
line per constant with at least one flagged binder. Run from lean-causal/:
    lake env lean campaign/T-abs-curves-free-lemma-k/Probe_Scan.lean > /tmp/cflk/scan.out 2>&1 -/

def curveNames : List Name :=
  [`Causal.Causality.CurvesExtend, `Causal.Causality.CurvesExtendOn,
   `Causal.Causality.InextensibleThrough, `Causal.Causality.SplitBy,
   `Causal.Causality.Inextensible]

elab "#scanCurves" : command => do
  let env ← getEnv
  let mods : List Name := [`Causal.LemmaKBare, `Causal.LemmaKReduction, `Causal.LemmaKSC,
    `Causal.LemmaKLocal, `Causal.LemmaKSCLocal, `Causal.LemmaK, `Causal.LemmaKObstruction,
    `Causal.LevinUtility]
  let idxs := mods.filterMap fun m => env.getModuleIdx? m
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless idxs.contains mi do continue
    if n.isInternal then continue
    if (`match_).isPrefixOf n then continue
    let s? ← liftTermElabM <| forallTelescope ci.type fun xs body => do
      let mut arr : Array Json := #[]
      let mut flagged := false
      for x in xs do
        let d ← x.fvarId!.getDecl
        let bi := match d.binderInfo with
          | .default => "()" | .implicit => "{}" | .strictImplicit => "⦃⦄" | .instImplicit => "[]"
        let nm := if d.binderInfo == .instImplicit then "_inst" else d.userName.eraseMacroScopes.toString
        let ty := toString (← ppExpr d.type)
        let ty' ← instantiateMVars d.type
        let hits := curveNames.filter fun c => ty'.getUsedConstants.contains c
        if !hits.isEmpty then flagged := true
        arr := arr.push (Json.arr #[Json.str bi, Json.str nm, Json.str ty,
          Json.arr (hits.toArray.map fun h => Json.str h.toString)])
      let concl := toString (← ppExpr body)
      if flagged then
        let modName := env.header.moduleNames[mi.toNat]!
        return some (Json.mkObj [("name", Json.str n.toString), ("module", Json.str modName.toString),
          ("kind", Json.str (if ci.isThm then "thm" else "def")),
          ("binders", Json.arr arr), ("concl", Json.str concl)]).compress
      else return none
    if let some s := s? then out := out.push s
  for s in out do logInfo m!"SCAN {s}"
  logInfo m!"SCANNED {out.size}"

#scanCurves
