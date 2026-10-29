import Causal
import CausalScaffold

/-!
# The axiom sweep

Sweeps **every** declaration of every `Causal.*` and `CausalScaffold.*` module and fails (a
thrown error, hence a non-zero exit) if one of them depends on an axiom outside `propext`,
`Classical.choice`, `Quot.sound` — `sorryAx` included. Run by `make check` through
`lake env lean scripts/AxiomSweep.lean`, after the build. Lifted from the GFN library's
`scripts/AxiomSweep.lean`; the two libraries are swept separately, so that a `sorry` admitted in
the scaffold is reported against the scaffold.
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name × Array Name) := #[]
  for (root, label) in [(`Causal, "strict"), (`CausalScaffold, "scaffold")] do
    let mut total := 0
    let mut mods := 0
    for idx in [0:env.header.moduleNames.size] do
      let modName := env.header.moduleNames[idx]!
      unless root.isPrefixOf modName do continue
      mods := mods + 1
      for n in env.header.moduleData[idx]!.constNames do
        if (env.find? n).isSome then
          total := total + 1
          let axs ← collectAxioms n
          let extra := axs.filter (fun a => !(std.contains a))
          if !extra.isEmpty then bad := bad.push (modName, n, extra)
    IO.println s!"axiom sweep ({label}): {total} declarations in {mods} modules"
  for (m, n, ax) in bad do IO.println s!"AXIOM SWEEP FAIL: {m}: {n} depends on {ax}"
  if !bad.isEmpty then
    throwError m!"axiom sweep: {bad.size} declaration(s) outside the standard axioms"
  IO.println "axiom sweep: all within propext/Classical.choice/Quot.sound"
