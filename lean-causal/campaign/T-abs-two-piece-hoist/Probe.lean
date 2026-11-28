import Causal.TwoPiece
import Causal.CBG.Ppcm

/-!
# Probe for T-abs-two-piece-hoist: the moved names resolve, in `Causal.TwoPiece`, to the same
constants

Every constant the move took out of `Causal.CBG.Ppcm` (the twelve declarations of the section
`TwoPiece` and the witness `timelikeLine_twoPiece`, with their auxiliary constants: a structure's
`mk`, `mk._flat_ctor`, `rec`, `recOn`, `casesOn` and field projections, a theorem's `_simp_1_1`) is
checked against the record taken from `Causal.CBG.Ppcm` at HEAD before the move: it resolves, its
module is `Causal.TwoPiece`, and its universe parameters, the `Expr.hash` of its type and the
`Expr.hash` of its value are those recorded. The declarations that stay are checked to be in
`Causal.CBG.Ppcm`. Then `#check @` prints each principal statement and `#print axioms` its axioms
(`axioms.txt`).
-/

open Lean in
/-- name, universe parameters, type hash, value hash (none for an inductive, a constructor or a
recursor), recorded from `Causal.CBG.Ppcm` before the move. -/
def recordBefore : List (Name × List Name × UInt64 × Option UInt64) := [
  (`Causal.Causality.TwoPiece, [`u], 3387236925, none),
  (`Causal.Causality.TwoPiece.absolutelyMinimalOn, [`u], 321118890, some 3656816052),
  (`Causal.Causality.TwoPiece.agree, [`u], 1068719570, some 1624188552),
  (`Causal.Causality.TwoPiece.casesOn, [`u_1, `u], 1617766336, some 732476074),
  (`Causal.Causality.TwoPiece.convex_left, [`u], 1569933792, some 3188751568),
  (`Causal.Causality.TwoPiece.convex_right, [`u], 1652455701, some 1183911897),
  (`Causal.Causality.TwoPiece.cover, [`u], 3307434029, some 218630419),
  (`Causal.Causality.TwoPiece.diamond_top_eq, [`u], 1754818586, some 2987521097),
  (`Causal.Causality.TwoPiece.exists_mid, [`u], 3859265356, some 2385016748),
  (`Causal.Causality.TwoPiece.isCauchySurface, [`u], 1513245023, some 482963852),
  (`Causal.Causality.TwoPiece.isCausal, [`u], 3465066400, some 3963427686),
  (`Causal.Causality.TwoPiece.le_of_le_top, [`u], 757516342, some 916599792),
  (`Causal.Causality.TwoPiece.le_top_iff, [`u], 1836288177, some 3066293485),
  (`Causal.Causality.TwoPiece.mem_of_le_top, [`u], 735312295, some 2147754777),
  (`Causal.Causality.TwoPiece.mk, [`u], 2375462904, none),
  (`Causal.Causality.TwoPiece.mk._flat_ctor, [`u], 2375462904, some 1865075919),
  (`Causal.Causality.TwoPiece.rec, [`u_1, `u], 2740209280, none),
  (`Causal.Causality.TwoPiece.recOn, [`u_1, `u], 1617766336, some 727626710),
  (`Causal.Causality.TwoPiece.rel_trans, [`u], 4205736595, some 3327716025),
  (`Causal.Causality.TwoPiece.symm, [`u], 1869490175, some 3527771321),
  (`Causal.Causality.timelikeLine_twoPiece, [], 3049359152, some 3904938791),
  (`Causal.Causality.timelikeLine_twoPiece._simp_1_1, [], 988966899, some 2829426000),
  (`Causal.Causality.twoPieceRel, [`u], 972791432, some 4143632371)
]

open Lean in
/-- The declarations that stay in `Causal.CBG.Ppcm`. -/
def stayInPpcm : List Name := [`Causal.Causality.TwoPiece.globallyHyperbolic, `Causal.Causality.TwoPiece.isCompact_diamond_mixed, `Causal.Causality.timelikeLine_twoPiece_globallyHyperbolic, `Causal.Causality.timelikeLine_cauchySide, `Causal.Causality.CauchySide, `Causal.Causality.PieceChart, `Causal.Causality.exists_mem_cauchy_between, `Causal.CBG.ppcm_twoPiece, `Causal.CBG.ppcm_isCauchySurface]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  for (n, lvls, th, vh) in recordBefore do
    let some ci := env.find? n | throwError "{n}: not found"
    unless moduleOf n == some `Causal.TwoPiece do throwError "{n}: in {moduleOf n}, not Causal.TwoPiece"
    unless ci.levelParams == lvls do throwError "{n}: universe parameters {ci.levelParams}, recorded {lvls}"
    unless ci.type.hash == th do throwError "{n}: type hash {ci.type.hash}, recorded {th}"
    let v := match ci with
      | .defnInfo d => some d.value.hash | .thmInfo d => some d.value.hash | _ => none
    unless v == vh do throwError "{n}: value hash {v}, recorded {vh}"
  for n in stayInPpcm do
    unless moduleOf n == some `Causal.CBG.Ppcm do throwError "{n}: in {moduleOf n}, not Causal.CBG.Ppcm"
  logInfo m!"{recordBefore.length} moved constants: module Causal.TwoPiece, universe parameters, type and value hashes as recorded; {stayInPpcm.length} constants still in Causal.CBG.Ppcm"

#check @Causal.Causality.TwoPiece
#check @Causal.Causality.twoPieceRel
#check @Causal.Causality.TwoPiece.symm
#check @Causal.Causality.TwoPiece.rel_trans
#check @Causal.Causality.TwoPiece.le_top_iff
#check @Causal.Causality.TwoPiece.le_of_le_top
#check @Causal.Causality.TwoPiece.mem_of_le_top
#check @Causal.Causality.TwoPiece.exists_mid
#check @Causal.Causality.TwoPiece.diamond_top_eq
#check @Causal.Causality.TwoPiece.isCausal
#check @Causal.Causality.TwoPiece.isCauchySurface
#check @Causal.Causality.timelikeLine_twoPiece

#print axioms Causal.Causality.TwoPiece
#print axioms Causal.Causality.twoPieceRel
#print axioms Causal.Causality.TwoPiece.symm
#print axioms Causal.Causality.TwoPiece.rel_trans
#print axioms Causal.Causality.TwoPiece.le_top_iff
#print axioms Causal.Causality.TwoPiece.le_of_le_top
#print axioms Causal.Causality.TwoPiece.mem_of_le_top
#print axioms Causal.Causality.TwoPiece.exists_mid
#print axioms Causal.Causality.TwoPiece.diamond_top_eq
#print axioms Causal.Causality.TwoPiece.isCausal
#print axioms Causal.Causality.TwoPiece.isCauchySurface
#print axioms Causal.Causality.timelikeLine_twoPiece
