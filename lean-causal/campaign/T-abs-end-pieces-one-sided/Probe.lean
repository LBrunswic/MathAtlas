import Causal.CExtConnexeCauchy.SubArc
import Causal.PastInextensibleMeetsCauchy

/-!
# Probe for T-abs-end-pieces-one-sided: the moved names resolve, in `Causal.CExtConnexeCauchy.SubArc`,
to the same constants, and `Extensible.of_top_tail` keeps its statement

The record below was taken before any edit, from the oleans of HEAD `31bc63e7` (lean-causal clean,
`lake build --no-build` up to date), where the five lemmas were in
`Causal.PastInextensibleMeetsCauchy`. For each moved constant (the five declarations and the
term-mode matcher `PastInextensible.of_retraction.match_1_1`) the probe checks four things: it
resolves, its module is now `Causal.CExtConnexeCauchy.SubArc`, and its universe parameters and the
`Expr.hash` of its type and of its value are as recorded.

`Extensible.of_top_tail` is checked to keep its module, universe parameters and type hash. Its value
is checked to have changed, and to cite `extensible_iff`, the two one-sided lemmas and the two
`….extensible` read-backs. It must not cite `pauseTop` or `exists_compress`. Then, over the whole
environment, the only constants outside § 1 of SubArc whose proof term cites `pauseTop` must be
`FutureExtensible.of_top_tail`, which shows that the pause construction is written once. The
neighbours `Extensible.of_bottom_tail` and `Inextensible.of_retraction` are checked unchanged, type
and value. Then `#check @` prints each statement and `#print axioms` its axioms (`axioms.txt`).
-/

open Lean in
/-- name, universe parameters, type hash, value hash, recorded from HEAD `31bc63e7` before the
move (all in `Causal.PastInextensibleMeetsCauchy` then). -/
def recordMoved : List (Name × List Name × UInt64 × UInt64) := [
  (`Causal.Causality.PastExtensible.of_top_tail, [`u], 2975726331, 2107910111),
  (`Causal.Causality.FutureExtensible.of_top_tail, [`u], 1085155926, 3537694027),
  (`Causal.Causality.PastExtensible.of_bottom_tail, [`u], 866244712, 213252198),
  (`Causal.Causality.PastInextensible.of_retraction, [`u], 3189547148, 4166674618),
  (`Causal.Causality.PastInextensible.of_retraction.match_1_1, [], 1826226788, 3111014960),
  (`Causal.Causality.pastExtensible_of_subArc, [`u], 248471968, 2992384261)
]

open Lean in
/-- Declarations of `Causal.CExtConnexeCauchy.SubArc` that the target does not touch: name,
universe parameters, type hash, value hash at HEAD `31bc63e7`. -/
def recordUnchanged : List (Name × List Name × UInt64 × UInt64) := [
  (`Causal.Causality.Extensible.of_bottom_tail, [`u], 2737194388, 1127225987),
  (`Causal.Causality.Inextensible.of_retraction, [`u], 2819639025, 1185598282)
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let subArc := `Causal.CExtConnexeCauchy.SubArc
  let valueOf (ci : ConstantInfo) : Option Expr := match ci with
    | .defnInfo d => some d.value | .thmInfo d => some d.value | _ => none
  -- the moved constants
  for (n, lvls, th, vh) in recordMoved ++ recordUnchanged do
    let some ci := env.find? n | throwError "{n}: not found"
    unless moduleOf n == some subArc do throwError "{n}: in {moduleOf n}, not {subArc}"
    unless ci.levelParams == lvls do throwError "{n}: universe parameters {ci.levelParams}, recorded {lvls}"
    unless ci.type.hash == th do throwError "{n}: type hash {ci.type.hash}, recorded {th}"
    let some v := valueOf ci | throwError "{n}: no value"
    unless v.hash == vh do throwError "{n}: value hash {v.hash}, recorded {vh}"
  -- the rewritten proof: same statement, a new proof term, the corollary of the one-sided lemmas
  let n := `Causal.Causality.Extensible.of_top_tail
  let some ci := env.find? n | throwError "{n}: not found"
  unless moduleOf n == some subArc do throwError "{n}: in {moduleOf n}, not {subArc}"
  unless ci.levelParams == [`u] do throwError "{n}: universe parameters {ci.levelParams}"
  unless ci.type.hash == 3241684421 do throwError "{n}: type hash {ci.type.hash}, recorded 3241684421"
  let some v := valueOf ci | throwError "{n}: no value"
  if v.hash == 4167501621 then throwError "{n}: the proof term is the old one"
  let used := v.getUsedConstants
  for m in [`Causal.Causality.extensible_iff, `Causal.Causality.PastExtensible.of_top_tail,
      `Causal.Causality.FutureExtensible.of_top_tail, `Causal.Causality.PastExtensible.extensible,
      `Causal.Causality.FutureExtensible.extensible] do
    unless used.contains m do throwError "{n}: its proof does not cite {m}"
  for m in [`Causal.pauseTop, `Causal.exists_compress] do
    if used.contains m then throwError "{n}: its proof still cites {m}"
  -- the pause construction is written once
  let pauseLemmas : List Name := [`Causal.pauseTop, `Causal.pauseTop.eq_1, `Causal.pauseTop_of_le,
    `Causal.pauseTop_of_mem_Icc, `Causal.pauseTop_of_ge, `Causal.monotone_pauseTop,
    `Causal.continuous_pauseTop]
  let mut users : Array Name := #[]
  for (m, cm) in env.constants.map₁.toList do
    if let some w := valueOf cm then
      if w.getUsedConstants.contains `Causal.pauseTop && !pauseLemmas.contains m then
        users := users.push m
  unless users.toList == [`Causal.Causality.FutureExtensible.of_top_tail] do
    throwError "constants citing pauseTop outside § 1: {users}"
  logInfo m!"{recordMoved.length} moved constants: module {subArc}, universe parameters, type and value hashes as recorded; {recordUnchanged.length} neighbours unchanged; Extensible.of_top_tail: same type hash, new proof through extensible_iff and the one-sided lemmas; pauseTop cited outside § 1 only by {users}"

set_option pp.funBinderTypes true
#check @Causal.Causality.PastExtensible.of_top_tail
#check @Causal.Causality.FutureExtensible.of_top_tail
#check @Causal.Causality.PastExtensible.of_bottom_tail
#check @Causal.Causality.PastInextensible.of_retraction
#check @Causal.Causality.pastExtensible_of_subArc
#check @Causal.Causality.Extensible.of_top_tail

#print axioms Causal.Causality.PastExtensible.of_top_tail
#print axioms Causal.Causality.FutureExtensible.of_top_tail
#print axioms Causal.Causality.PastExtensible.of_bottom_tail
#print axioms Causal.Causality.PastInextensible.of_retraction
#print axioms Causal.Causality.pastExtensible_of_subArc
#print axioms Causal.Causality.Extensible.of_top_tail
#print axioms Causal.Causality.Extensible.of_bottom_tail
#print axioms Causal.Causality.Inextensible.of_retraction
#print axioms Causal.Causality.PastInextensible.exists_mem_of_mem_Jplus
