import CausalScaffold.GluingModels.Tools
import CausalScaffold.GluingModels.Minimal
import CausalScaffold.GluingModels.NonMinimal
import CausalScaffold.GluingModels.Pushout
import CausalScaffold.GluingModels.ModelStatic
import CausalScaffold.GluingModels.ModelSingular
import CausalScaffold.GluingModels.ModelScaffold
open Lean Meta Elab Command

/-- Every declaration of `Causal.GluingModels`, with its axioms; flags `sorryAx`. -/
elab "#gm_axioms" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (`Causal.GluingModels).isPrefixOf n && !n.isInternal then names := names.push n
  let mut bad := 0
  for n in names.qsort (·.toString < ·.toString) do
    let ax ← liftCoreM <| Lean.collectAxioms n
    let s := ax.toList.map toString
    if s.contains "sorryAx" then bad := bad + 1
    IO.println s!"{n}\t{s}"
  IO.println s!"TOTAL {names.size} SORRY {bad}"

#gm_axioms
