import Causal.StrongCausalityHull
import Causal.SCOpenWithoutTarentin
import Causal.CauchyExtension
import Causal.TimelikeHomotopy
import Causal.C0ExtensionSkeleton
import Causal.CurvesExtendSecondCountable
import Causal.ErsSecondCountable
import Causal.CauchySeparation
import Causal.FlrwType
import Causal.FlrwTypeClosedAmbient
import Causal.Model.FlatSpaceCylinder

/-!
Probe for T-abs-sc-open-hoist. Run with
`cd lean-causal && taskset -c 0-11 lake env lean campaign/T-abs-sc-open-hoist/Probe.lean`.

1. Each moved or re-proved declaration: the module it is declared in now.
2. The import closure of `Causal.StrongCausalityHull`, read off the compiled environment: no model
   module (`tools/ladder.py`'s MODEL_LAYER), no `Causal.Ladder.*`, none of the witnesses' modules.
3. The re-proved twins are the split: `splitBy_of_t1_secondCountable` is
   `IsCauchySurfaceOn.mem_Jplus_union_Jminus` with `SplitBy` unfolded, and
   `IsCauchySurface.cover_of_t1_secondCountable` its case `W = ⊤`, both by `rfl`-level terms.
4. The axioms of every moved and re-proved declaration (`axioms.txt`).
-/

open Lean

def probeNames : List Name :=
  [`Causal.Causality.subset_Jplus_top_inter_Jminus_top,
   `Causal.Causality.causallyConvexIn_Jplus_top_inter_Jminus_top,
   `Causal.Causality.causallyConvexIn_top_iff,
   `Causal.Causality.CausallyConvexIn.Jplus_top_inter_Jminus_top_subset,
   `Causal.Causality.exists_opens_causallyConvexIn_of_isOpen_hull,
   `Causal.Causality.StronglyCausal.stronglyCausalOpen_of_isOpen_hull,
   `Causal.Causality.StronglyCausal.stronglyCausalOpen_of_isOpen_Jplus_Jminus,
   `Causal.Causality.CausallyOpen.isOpen_Jplus_top_Jminus_top,
   `Causal.Causality.StronglyCausal.stronglyCausalOpen_of_causallyOpen,
   `Causal.Causality.stronglyCausalOpen_iff_stronglyCausal_of_causallyOpen,
   `Causal.Causality.GloballyHyperbolic.stronglyCausalOpen_of_isOpen_Jplus_Jminus,
   `Causal.Causality.StronglyCausal.exists_not_isOpen_hull,
   `Causal.Causality.StronglyCausal.not_causallyOpen_of_not_stronglyCausalOpen,
   `Causal.timelikeLine_scOpen_of_causallyOpen,
   `Causal.spacelikeLine_scOpen_without_tarentin,
   `Causal.isolatedLine_scOpen_without_tarentin,
   `Causal.oneWayMembrane_hull_not_isOpen,
   `Causal.IsEMorphismOn.chronalCurveOn_comp,
   `Causal.Causality.ChronalHomotopyOn.homotopicRel,
   `Causal.IsEMorphismOn.pastInextensible_invComp,
   `Causal.IsSpacetimeExtension.isEMorphismOn,
   `Causal.Causality.IsCauchySurfaceOn.mem_Jplus_union_Jminus,
   `Causal.Causality.splitBy_of_t1_secondCountable,
   `Causal.Causality.IsCauchySurface.cover_of_t1_secondCountable]

-- 1. where each declaration lives now
#eval show CoreM Unit from do
  let env ← getEnv
  for n in probeNames do
    match env.getModuleIdxFor? n with
    | some i => IO.println s!"{n} : {env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"{n} : NOT FOUND"

-- 2. the import closure of the light module, from the compiled environment
#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let idxOf (m : Name) : Option Nat := names.findIdx? (· == m)
  let some root := idxOf `Causal.StrongCausalityHull | throwError "no Causal.StrongCausalityHull"
  let mut seen : Std.HashSet Nat := {}
  let mut stack : List Nat := [root]
  while !stack.isEmpty do
    let i := stack.head!
    stack := stack.tail!
    if seen.contains i then continue
    seen := seen.insert i
    for imp in env.header.moduleData[i]!.imports do
      if let some j := idxOf imp.module then stack := j :: stack
  let causal := seen.toList.filterMap fun i =>
    let m := names[i]!
    if (`Causal).isPrefixOf m then some m else none
  let models := [`Causal.Minkowski, `Causal.Static, `Causal.SingularFlat, `Causal.Flat,
    `Causal.Model, `Causal.Port]
  let bad := causal.filter fun m =>
    models.any (fun p => p.isPrefixOf m) || (`Causal.Ladder).isPrefixOf m ||
      [`Causal.SCOpenWithoutTarentin, `Causal.Lines, `Causal.LadderLocal, `Causal.NestedTransfer,
        `Causal.LocateExtension, `Causal.OneWayMembrane].contains m
  IO.println s!"Causal.StrongCausalityHull: {seen.size} modules in its closure, {causal.length} of them Causal.*"
  IO.println s!"  Causal.* closure: {(causal.map toString).toArray.qsort (· < ·)}"
  IO.println s!"  model / Ladder / witness modules in it: {bad}"

-- 3. the re-proved twins are the split
open Causal Causality in
example {M : Type*} [TopologicalSpace M] [T1Space M] [SecondCountableTopology M] {C : Causality M}
    {W : TopologicalSpace.Opens M} {S : Set M} (hS : C.IsCauchySurfaceOn W S) :
    splitBy_of_t1_secondCountable hS = fun _ hq => hS.mem_Jplus_union_Jminus hq := rfl

open Causal Causality in
example {M : Type*} [TopologicalSpace M] [T1Space M] [SecondCountableTopology M] {C : Causality M}
    {S : Set M} (hS : C.IsCauchySurface S) (x : M) :
    hS.cover_of_t1_secondCountable x =
      IsCauchySurfaceOn.mem_Jplus_union_Jminus (W := ⊤) hS trivial := rfl

-- 4. axioms
#print axioms Causal.Causality.subset_Jplus_top_inter_Jminus_top
#print axioms Causal.Causality.causallyConvexIn_Jplus_top_inter_Jminus_top
#print axioms Causal.Causality.causallyConvexIn_top_iff
#print axioms Causal.Causality.CausallyConvexIn.Jplus_top_inter_Jminus_top_subset
#print axioms Causal.Causality.exists_opens_causallyConvexIn_of_isOpen_hull
#print axioms Causal.Causality.StronglyCausal.stronglyCausalOpen_of_isOpen_hull
#print axioms Causal.Causality.StronglyCausal.stronglyCausalOpen_of_isOpen_Jplus_Jminus
#print axioms Causal.Causality.CausallyOpen.isOpen_Jplus_top_Jminus_top
#print axioms Causal.Causality.StronglyCausal.stronglyCausalOpen_of_causallyOpen
#print axioms Causal.Causality.stronglyCausalOpen_iff_stronglyCausal_of_causallyOpen
#print axioms Causal.Causality.GloballyHyperbolic.stronglyCausalOpen_of_isOpen_Jplus_Jminus
#print axioms Causal.Causality.StronglyCausal.exists_not_isOpen_hull
#print axioms Causal.Causality.StronglyCausal.not_causallyOpen_of_not_stronglyCausalOpen
#print axioms Causal.timelikeLine_scOpen_of_causallyOpen
#print axioms Causal.spacelikeLine_scOpen_without_tarentin
#print axioms Causal.isolatedLine_scOpen_without_tarentin
#print axioms Causal.oneWayMembrane_hull_not_isOpen
#print axioms Causal.IsEMorphismOn.chronalCurveOn_comp
#print axioms Causal.Causality.ChronalHomotopyOn.homotopicRel
#print axioms Causal.IsEMorphismOn.pastInextensible_invComp
#print axioms Causal.IsSpacetimeExtension.isEMorphismOn
#print axioms Causal.Causality.IsCauchySurfaceOn.mem_Jplus_union_Jminus
#print axioms Causal.Causality.splitBy_of_t1_secondCountable
#print axioms Causal.Causality.IsCauchySurface.cover_of_t1_secondCountable
#print axioms Causal.Flat.spaceCylinder_not_futureOneConnected
#print axioms Causal.IsSpacetimeExtension.not_pastBoundaryChart_of_flrwType
#print axioms Causal.Causality.not_pastBoundaryChart_of_flrwTypeB_of_isClosed_le
