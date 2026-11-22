import Causal
open Lean Meta Elab Command

/-- Every constant of a `Causal.*` module whose type concludes in `Causal.Causality _`. -/
elab "#enum_causalities" : command => do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      unless (`Causal).isPrefixOf mod do continue
      let ty := ci.type
      let concl ← liftTermElabM <| forallTelescopeReducing ty fun _ b => pure b
      let b := concl.getAppFn
      if b.isConstOf ``Causal.Causality then
        let kind := match ci with
          | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "ax"
          | .opaqueInfo _ => "opaque" | _ => "other"
        let nargs := (← liftTermElabM <| forallTelescopeReducing ty fun xs _ => pure xs.size)
        out := out.push s!"{mod}\t{n}\t{kind}\t{nargs}"
  for s in out.qsort (· < ·) do
    IO.println s

#enum_causalities
