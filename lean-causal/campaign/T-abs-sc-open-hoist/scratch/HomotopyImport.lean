import Causal.Ladder.Rules
import Causal.TimelikeHomotopy

/-! What the new import `Mathlib.Topology.Homotopy.Basic` of `Causal.TimelikeHomotopy` adds to the
import closures of `Causal.TimelikeHomotopy` and of `Causal.Ladder.Rules`: the closures with and
without that one edge, read off the compiled environment.
Run: `lake env lean campaign/T-abs-sc-open-hoist/scratch/HomotopyImport.lean`. -/

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let idxOf (m : Name) : Option Nat := names.findIdx? (· == m)
  let closure (root : Name) (skip : Name × Name) : Std.HashSet Name := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut stack : List Name := [root]
    while !stack.isEmpty do
      let m := stack.head!
      stack := stack.tail!
      if seen.contains m then continue
      seen := seen.insert m
      if let some i := idxOf m then
        for imp in env.header.moduleData[i]!.imports do
          unless (m, imp.module) == skip do stack := imp.module :: stack
    return seen
  let edge := (`Causal.TimelikeHomotopy, `Mathlib.Topology.Homotopy.Basic)
  for root in [`Causal.TimelikeHomotopy, `Causal.Ladder.Rules] do
    let withE := closure root (`x, `x)
    let without := closure root edge
    let added := withE.toList.filter (!without.contains ·)
    IO.println s!"{root}: {withE.size} modules with the import, {without.size} without; added: {(added.map toString).toArray.qsort (· < ·)}"
