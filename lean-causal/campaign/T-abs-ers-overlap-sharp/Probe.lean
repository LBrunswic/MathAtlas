import Causal.ErsEtaleMghd
import Causal.ErsEtaleMghdWitnesses

/-!
# Probe for T-abs-ers-overlap-sharp: the moved name resolves in `Causal.ErsEtaleMghd` to the same
constant, and `ers_isOpenEmbedding_proj_of_eqOn` keeps its statement with a corollary proof

The record below was taken before any edit, from the oleans of HEAD `2ac55d8c` (lean-causal clean,
`lake build --no-build` up to date on both modules), where `ers_coe_eq_inter_of_eqOn` was in
`Causal.ErsEtaleMghdWitnesses`. The old proof's value hash was also reproduced by re-elaborating
the old text of `Causal/ErsEtaleMghd.lean`.

* `ers_coe_eq_inter_of_eqOn` resolves, its module is now `Causal.ErsEtaleMghd`, and its universe
  parameters and the `Expr.hash` of its type and of its value are as recorded (a verbatim move).
* `ers_isOpenEmbedding_proj_of_eqOn` keeps its module, universe parameters and type hash; its value
  has changed, cites `ers_coe_eq_inter_of_eqOn`, `EtaleGluing.isOpenEmbedding_proj` and
  `Eq.superset`, and no longer cites the steps the old proof repeated (`eq_inter_of_t2Space`,
  `t2Space_iff`, `inextensibleThrough_of_t1_secondCountable`, `IsDevelopment.cauchy`,
  `ers_isPreconnected_inter_of_eqOn`).
* Over the whole environment, the only constant whose proof term cites both
  `inextensibleThrough_of_t1_secondCountable` and `EtaleGluing.eq_inter_of_t2Space` is
  `ers_coe_eq_inter_of_eqOn`: the steps are written once (before the move there were two).
* The neighbours `ers_isPreconnected_inter_of_eqOn`, `real_eqOn_inter_of_isDevelopment` and the
  witness `ErsEtaleWitness.timelikeLine_ers_isOpenEmbedding_proj_of_eqOn` are unchanged, type and
  value.

Then `#check @` prints each statement and `#print axioms` its axioms (`axioms.txt`).
-/

open Lean in
/-- name, module after the move, universe parameters, type hash, value hash, recorded from HEAD
`2ac55d8c` before the move (`ers_coe_eq_inter_of_eqOn` then in `Causal.ErsEtaleMghdWitnesses`). -/
def recordSame : List (Name × Name × List Name × UInt64 × UInt64) := [
  (`Causal.ers_coe_eq_inter_of_eqOn, `Causal.ErsEtaleMghd, [`u, `v], 2787989698, 3326407128),
  (`Causal.ers_isPreconnected_inter_of_eqOn, `Causal.ErsEtaleMghd, [`u, `v], 192577136,
    3175181676),
  (`Causal.real_eqOn_inter_of_isDevelopment, `Causal.ErsEtaleMghdWitnesses, [`v], 3511626714,
    3851863617),
  (`Causal.ErsEtaleWitness.timelikeLine_ers_isOpenEmbedding_proj_of_eqOn,
    `Causal.ErsEtaleMghdWitnesses, [], 1307260372, 2275342226)
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let valueOf (ci : ConstantInfo) : Option Expr := match ci with
    | .defnInfo d => some d.value | .thmInfo d => some d.value | _ => none
  -- the moved constant and the untouched neighbours: same everything but (for one) the module
  for (n, mod, lvls, th, vh) in recordSame do
    let some ci := env.find? n | throwError "{n}: not found"
    unless moduleOf n == some mod do throwError "{n}: in {moduleOf n}, not {mod}"
    unless ci.levelParams == lvls do
      throwError "{n}: universe parameters {ci.levelParams}, recorded {lvls}"
    unless ci.type.hash == th do throwError "{n}: type hash {ci.type.hash}, recorded {th}"
    let some v := valueOf ci | throwError "{n}: no value"
    unless v.hash == vh do throwError "{n}: value hash {v.hash}, recorded {vh}"
  -- the reproved theorem: same statement, a new proof term, the corollary of the sharp form
  let n := `Causal.ers_isOpenEmbedding_proj_of_eqOn
  let some ci := env.find? n | throwError "{n}: not found"
  unless moduleOf n == some `Causal.ErsEtaleMghd do throwError "{n}: in {moduleOf n}"
  unless ci.levelParams == [`u, `v] do throwError "{n}: universe parameters {ci.levelParams}"
  unless ci.type.hash == 1652221829 do
    throwError "{n}: type hash {ci.type.hash}, recorded 1652221829"
  let some v := valueOf ci | throwError "{n}: no value"
  if v.hash == 3562832028 then throwError "{n}: the proof term is the old one"
  let used := v.getUsedConstants
  for m in [`Causal.ers_coe_eq_inter_of_eqOn, `Causal.EtaleGluing.isOpenEmbedding_proj,
      `Eq.superset] do
    unless used.contains m do throwError "{n}: its proof does not cite {m}"
  let steps := [`Causal.EtaleGluing.eq_inter_of_t2Space, `Causal.EtaleGluing.t2Space_iff,
    `Causal.Causality.inextensibleThrough_of_t1_secondCountable, `Causal.IsDevelopment.cauchy,
    `Causal.ers_isPreconnected_inter_of_eqOn]
  for m in steps do
    if used.contains m then throwError "{n}: its proof still cites {m}"
  -- the sharp form carries every one of those steps
  let some sharp := env.find? `Causal.ers_coe_eq_inter_of_eqOn | throwError "sharp form"
  let some sv := valueOf sharp | throwError "sharp form: no value"
  for m in steps do
    unless sv.getUsedConstants.contains m do throwError "the sharp form does not cite {m}"
  -- the steps are written once in the environment
  let mut users : Array Name := #[]
  for (m, cm) in env.constants.map₁.toList do
    if let some w := valueOf cm then
      let u := w.getUsedConstants
      if u.contains `Causal.Causality.inextensibleThrough_of_t1_secondCountable &&
          u.contains `Causal.EtaleGluing.eq_inter_of_t2Space then
        users := users.push m
  unless users.toList == [`Causal.ers_coe_eq_inter_of_eqOn] do
    throwError "constants citing both inextensibleThrough_of_t1_secondCountable and \
      eq_inter_of_t2Space: {users}"
  logInfo m!"ers_coe_eq_inter_of_eqOn: module Causal.ErsEtaleMghd, universe parameters, type and \
    value hashes as recorded; {recordSame.length - 1} neighbours unchanged; \
    ers_isOpenEmbedding_proj_of_eqOn: same type hash, new proof through ers_coe_eq_inter_of_eqOn \
    and isOpenEmbedding_proj, none of the {steps.length} repeated steps; constants citing both \
    inextensibleThrough_of_t1_secondCountable and eq_inter_of_t2Space: {users}"

set_option pp.funBinderTypes true
#check @Causal.ers_coe_eq_inter_of_eqOn
#check @Causal.ers_isOpenEmbedding_proj_of_eqOn

#print axioms Causal.ers_coe_eq_inter_of_eqOn
#print axioms Causal.ers_isOpenEmbedding_proj_of_eqOn
#print axioms Causal.ers_isPreconnected_inter_of_eqOn
#print axioms Causal.real_eqOn_inter_of_isDevelopment
#print axioms Causal.ErsEtaleWitness.timelikeLine_ers_isOpenEmbedding_proj_of_eqOn
