import Causal.FlrwTypeClosedAmbient
/-! Scratch for T-abs-flrw-future-a-witness: every non-internal constant of `Causal.FlrwType` and
`Causal.FlrwTypeClosedAmbient`, with its type's `Expr` hash and its pretty-printed type (full
names, proofs elided, one line). Run on the oleans before the edit (`types_before.txt`) and after
the build (`types_after.txt`). The metaprogram is T-abs-flrw-future-extension's, with an unbounded
format width. -/
open Lean Meta Elab Command

elab "#dump_module_types " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "no module"
  let mut acc : Array (String × String × UInt64) := #[]
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      if n.isInternal then continue
      let s ← liftTermElabM <| withOptions (fun o => ((o.setBool `pp.proofs false).set
          `format.width (100000 : Nat)).setBool `pp.fullNames true) do
        return toString (← ppExpr ci.type)
      acc := acc.push (n.toString, s, ci.type.hash)
  let sorted := acc.qsort (fun a b => a.1 < b.1)
  for (n, s, h) in sorted do
    logInfo m!"{n} #{h} : {s}"

#dump_module_types Causal.FlrwType
#dump_module_types Causal.FlrwTypeClosedAmbient
