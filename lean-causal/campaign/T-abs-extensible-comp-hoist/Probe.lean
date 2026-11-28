import Causal.ExtensibleAlongCurve
import Causal.MeetsCauchyAntisymmetrySharp
import Causal.Remarks.SingularRowsCauchyExt

/-!
Probe for T-abs-extensible-comp-hoist. Run, after
`taskset -c 12-23 lake build Causal.ExtensibleAlongCurve Causal.MeetsCauchyAntisymmetrySharp`, with
`cd lean-causal && taskset -c 12-23 lake env lean campaign/T-abs-extensible-comp-hoist/Probe.lean`.
(`Causal.Remarks.SingularRowsCauchyExt` is imported for check 4 only; it is not upstream of either
module.)

1. Each moved declaration: the module it is declared in now; the two old names are gone.
2. The import closure of `Causal.ExtensibleAlongCurve`, read off the compiled environment: no
   model module (`tools/ladder.py`'s MODEL_LAYER), no `Causal.Ladder.*`, not
   `Causal.MeetsCauchyAntisymmetrySharp`.
3. The four statements, written out as `#check @` printed them in
   `Causal.MeetsCauchyAntisymmetrySharp` at HEAD (old names), are the types of the new constants,
   by `example … := @new_name`: the binder order and every binder's type are checked by the
   elaborator's definitional equality (kb/0335). Definitional equality ignores binder kinds and
   names and `Type _` hides the universe name, so those three are read off the constant dump
   (kb/0063, kb/0255; REPORT.json `type_check`), and printed in 3' for the record.
4. The module docstring's claim that `Causality.extensible_of_timeGraph_openEnd` (model layer) is
   the case `h = T ∘ c` of `extensible_of_eq_comp_monotoneOn`, without its `hbdd` and `hnomax`.
5. The axioms (`axioms.txt`).
-/

open Lean

def probeNames : List Name :=
  [`Causal.Causality.CausalCurveIn.continuousOn_interval,
   `Causal.Causality.causalCurveIn_top_of_pieces,
   `Causal.Causality.extensible_of_eq_comp_monotoneOn_of_bddAbove,
   `Causal.Causality.extensible_of_eq_comp_monotoneOn,
   `Causal.rayCircle_extensible_of_forall_ne,
   `Causal.rayCircle_isCauchySurface_Y,
   `Causal.rayCircle_separates_pastInextensible_meets,
   `Causal.not_pastInextensible_exists_mem_of_mem_Jplus_bare]

-- 1. where each declaration lives now; the old names resolve to nothing
#eval show CoreM Unit from do
  let env ← getEnv
  for n in probeNames do
    match env.getModuleIdxFor? n with
    | some i => IO.println s!"{n} : {env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"{n} : NOT FOUND"
  for n in [`Causal.Causality.extensible_of_graph,
      `Causal.Causality.extensible_of_graph_of_bddAbove] do
    IO.println s!"{n} (old name) in the environment: {env.contains n}"

-- 2. the import closure of the light module, from the compiled environment
#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let idxOf (m : Name) : Option Nat := names.findIdx? (· == m)
  let some root := idxOf `Causal.ExtensibleAlongCurve | throwError "no Causal.ExtensibleAlongCurve"
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
    `Causal.Model, `Causal.Port, `Causal.Remarks, `Causal.PlainnessModels]
  let bad := causal.filter fun m =>
    models.any (fun p => p.isPrefixOf m) || (`Causal.Ladder).isPrefixOf m ||
      m == `Causal.MeetsCauchyAntisymmetrySharp
  IO.println s!"Causal.ExtensibleAlongCurve: {seen.size} modules in its closure, {causal.length} of them Causal.*"
  IO.println s!"  direct imports: {env.header.moduleData[root]!.imports.map (·.module)}"
  IO.println s!"  model / Remarks / Ladder / MeetsCauchyAntisymmetrySharp modules in it: {bad}"

-- 3. the HEAD statements (old names, printed by `#check @` at HEAD) are the new constants' types
section HeadStatements

open Set TopologicalSpace Causal Causal.Causality

/-- HEAD `Causal.Causality.CausalCurveIn.continuousOn_interval`. -/
example : ∀ {M : Type _} [TopologicalSpace M] {C : Causal.Causality M} {W : Opens M}
    {I : Set ℝ} {c : ℝ → M}, C.CausalCurveIn W I c → ContinuousOn c I :=
  @Causal.Causality.CausalCurveIn.continuousOn_interval

/-- HEAD `Causal.Causality.causalCurveIn_top_of_pieces`. -/
example : ∀ {M : Type _} [TopologicalSpace M] {C : Causal.Causality M} {γ : ℝ → M}
    {J : Set ℝ}, Continuous γ → J.Nonempty → J.OrdConnected →
      (∀ s ∈ J, ∀ s' ∈ J, s ≤ s' → ∀ (N : Opens M), γ '' Icc s s' ⊆ ↑N →
        C.le N (γ s) (γ s')) → C.CausalCurveIn ⊤ J γ :=
  @Causal.Causality.causalCurveIn_top_of_pieces

/-- HEAD `Causal.Causality.extensible_of_graph_of_bddAbove`. -/
example : ∀ {M : Type _} [TopologicalSpace M] {C : Causal.Causality M} {W : Opens M}
    {I J : Set ℝ} {c γ : ℝ → M} {h : ℝ → ℝ} {t' : ℝ},
    C.CausalCurveIn W J γ → C.CausalCurveIn W I c → BddAbove I → MonotoneOn h I →
      ContinuousOn h I → MapsTo h I J → (∀ t ∈ I, γ (h t) = c t) → t' ∈ J →
        (∀ t ∈ I, h t ≤ t') → (∀ t ∈ I, γ t' ≠ c t) → C.Extensible W I c :=
  @Causal.Causality.extensible_of_eq_comp_monotoneOn_of_bddAbove

/-- HEAD `Causal.Causality.extensible_of_graph`. -/
example : ∀ {M : Type _} [TopologicalSpace M] {C : Causal.Causality M} {W : Opens M}
    {I J : Set ℝ} {c γ : ℝ → M} {h : ℝ → ℝ} {t' : ℝ},
    C.CausalCurveIn W J γ → C.CausalCurveIn W I c → MonotoneOn h I →
      ContinuousOn h I → MapsTo h I J → (∀ t ∈ I, γ (h t) = c t) → t' ∈ J →
        (∀ t ∈ I, h t ≤ t') → (∀ t ∈ I, γ t' ≠ c t) → C.Extensible W I c :=
  @Causal.Causality.extensible_of_eq_comp_monotoneOn

end HeadStatements

-- 3'. the same, as data: universe parameters, binder telescope and type of each new constant
#eval show MetaM Unit from do
  for n in [`Causal.Causality.CausalCurveIn.continuousOn_interval,
      `Causal.Causality.causalCurveIn_top_of_pieces,
      `Causal.Causality.extensible_of_eq_comp_monotoneOn_of_bddAbove,
      `Causal.Causality.extensible_of_eq_comp_monotoneOn] do
    let ci ← getConstInfo n
    IO.println s!"{n} {ci.levelParams} :\n  {← Meta.ppExpr ci.type}\n"

-- 4. the model-layer twin is a case of the hoisted lemma, without `hbdd` and `hnomax`
open Causal Causality TopologicalSpace in
example {X : Type} [TopologicalSpace X] {C : Causality X} {W : Opens X} {T : X → ℝ}
    {J I : Set ℝ} {γ c : ℝ → X} (hγ : C.CausalCurveIn W J γ) (hTγ : ∀ τ ∈ J, T (γ τ) = τ)
    (hc : C.CausalCurveIn W I c) (hcγ : ∀ t ∈ I, T (c t) ∈ J ∧ γ (T (c t)) = c t)
    (hmono : MonotoneOn (T ∘ c) I) (hTcont : ContinuousOn (T ∘ c) I) {t' : ℝ} (ht' : t' ∈ J)
    (hlt : ∀ t ∈ I, T (c t) < t') : C.Extensible W I c :=
  extensible_of_eq_comp_monotoneOn hγ hc hmono hTcont (fun t ht => (hcγ t ht).1)
    (fun t ht => (hcγ t ht).2) ht' (fun t ht => (hlt t ht).le)
    (fun t ht he => by
      have := hTγ t' ht'
      rw [he] at this
      exact (hlt t ht).ne this)

-- and the twin's own statement, for comparison: it asks `hbdd` and `hnomax` besides
#check @Causal.Causality.extensible_of_timeGraph_openEnd

-- 5. axioms
#print axioms Causal.Causality.CausalCurveIn.continuousOn_interval
#print axioms Causal.Causality.causalCurveIn_top_of_pieces
#print axioms Causal.Causality.extensible_of_eq_comp_monotoneOn_of_bddAbove
#print axioms Causal.Causality.extensible_of_eq_comp_monotoneOn
#print axioms Causal.rayCircle_extensible_of_forall_ne
#print axioms Causal.rayCircle_isCauchySurface_Y
#print axioms Causal.rayCircle_separates_pastInextensible_meets
#print axioms Causal.not_pastInextensible_exists_mem_of_mem_Jplus_bare
