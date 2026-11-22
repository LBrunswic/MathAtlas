import Causal
import CausalScaffold.GluingModels.Minimal
import CausalScaffold.GluingModels.NonMinimal
import CausalScaffold.GluingModels.ModelStatic
import CausalScaffold.GluingModels.ModelSingular
import CausalScaffold.GluingModels.ModelScaffold
open Lean Meta Elab Command

/-- The module and line of every declaration named in `/tmp/gm_names.txt`; `MISSING` otherwise. -/
elab "#gm_locate" : command => do
  let env ← getEnv
  for l in ← IO.FS.lines "/tmp/gm_names.txt" do
    if l.isEmpty then continue
    let n := l.toName
    match env.getModuleIdxFor? n with
    | none => IO.println s!"{l}\tMISSING"
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      let line ← match ← liftCoreM (findDeclarationRanges? n) with
        | some r => pure (toString r.range.pos.line)
        | none => pure "?"
      IO.println s!"{l}\t{mod}\t{line}"

#gm_locate
