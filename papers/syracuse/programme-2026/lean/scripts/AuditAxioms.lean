import Syracuse

/-!
# Axiom audit

Walks every declaration under the `Syracuse` namespace and lists any axiom other than Lean's three
standard ones (`propext`, `Classical.choice`, `Quot.sound`). A `sorry` shows up as `sorryAx`, and
`native_decide` as `Lean.ofReduceBool`, so both are caught.
Run after `lake build`: `lake env lean scripts/AuditAxioms.lean`.
-/

open Lean Elab Command

elab "#audit_syracuse_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (name, _) in env.constants.map₁.toList do
    if (`Syracuse).isPrefixOf name && !name.isInternal then
      count := count + 1
      for ax in ← collectAxioms name do
        unless allowed.contains ax do bad := bad.push (name, ax)
  if bad.isEmpty then
    logInfo m!"axiom audit: {count} declarations under `Syracuse`, all within [propext, Classical.choice, Quot.sound]"
  else
    logError m!"axiom audit FAILED: {bad.toList}"

#audit_syracuse_axioms
