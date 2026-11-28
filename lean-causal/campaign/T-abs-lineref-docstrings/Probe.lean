import Causal.Model.MinkowskiPastBoundaryChart
import Causal.FlrwTypeClosedAmbient
import Causal.CurvesExtendSecondCountable
import Causal.CurvesExtend
import Causal.ChainsCurves
import Causal.LevinUtility
import Causal.Flat.CauchyComplete
import Causal.CExtConnexeCauchy.SubArc
import Causal.IsolatedLineConjoined
import Causal.Model.MinkowskiFutureOneConnected

/-!
Probe for T-abs-lineref-docstrings. Run, before and after the docstring edits, with
`cd lean-causal && DUMP_OUT=<file> DOC_OUT=<file> taskset -c 0-11 lake env lean
campaign/T-abs-lineref-docstrings/Probe.lean`; compare the two `DUMP_OUT` files with `cmp`.

1. **The constant dump** (kb/0063): every constant of every `Causal.*` module in the import
   closure of the nine edited modules, with its module, kind, universe parameters, type hash,
   binder telescope (macro scopes erased), value hash, reducibility, protection, noncomputability
   and internality, sorted by name. A docstring-only edit leaves it byte-identical.
2. **The docstring dump** (`DOC_OUT`): the hash of each declaration docstring of the nine modules,
   and of each module docstring. It is expected to differ exactly where the edits are.
3. **The names cited** in place of the 16 line references: each exists, in the module cited.
4. **Item 7's sentence** (`Causal.FlrwTypeClosedAmbient`): `Causal.minkowski_pastBoundaryChart`,
   read at `(minkowski n).dual` through `Causality.dual_dual` (`rfl`), has type
   `(minkowski n).dual.FutureBoundaryChart (minkowskiPosHalfSpace n) (minkowskiChartBox n) 0`, so
   the time reversals of items 4 and 5 are not vacuous; and the globally hyperbolic forms of items
   4 and 5, applied to `(minkowski n).dual`, refute the time-reversed (A) and (B) at that
   half-space.
-/

open Lean Meta

/-- The binder telescope of a type: names with macro scopes erased, binder infos. -/
partial def telescope (e : Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .forallE n _ b bi =>
    let tag := match bi with
      | .default => "()" | .implicit => "{}" | .strictImplicit => "⦃⦄" | .instImplicit => "[]"
    telescope b (acc.push s!"{n.eraseMacroScopes}{tag}")
  | .mdata _ b => telescope b acc
  | _ => acc

/-- The nine modules edited by the target. -/
def editedModules : List Name :=
  [`Causal.FlrwTypeClosedAmbient, `Causal.CurvesExtendSecondCountable, `Causal.CurvesExtend,
   `Causal.ChainsCurves, `Causal.LevinUtility, `Causal.Flat.CauchyComplete,
   `Causal.CExtConnexeCauchy.SubArc, `Causal.IsolatedLineConjoined,
   `Causal.Model.MinkowskiFutureOneConnected]

-- 1. the constant dump; 2. the docstring dump
#eval show CoreM Unit from do
  let env ← getEnv
  let out := (← IO.getEnv "DUMP_OUT").getD "/tmp/T-abs-lineref-docstrings/dump.txt"
  let docOut := (← IO.getEnv "DOC_OUT").getD "/tmp/T-abs-lineref-docstrings/docs.txt"
  let mut rows : Array String := #[]
  let mut docs : Array String := #[]
  let mut nEdited := 0
  for (name, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`Causal).isPrefixOf modName do continue
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    let red := match getReducibilityStatusCore env name with
      | .reducible => "reducible" | .semireducible => "semi" | .irreducible => "irred"
      | _ => "other"
    let vhash := match ci with
      | .defnInfo d => toString d.value.hash
      | .thmInfo d => toString d.value.hash
      | .opaqueInfo d => toString d.value.hash
      | _ => "-"
    let tel := String.intercalate "," (telescope ci.type).toList
    let prot := if isProtected env name then "prot" else "-"
    let nc := if isNoncomputable env name then "nc" else "-"
    rows := rows.push
      s!"{name}\t{modName}\t{kind}\t{ci.levelParams}\t{ci.type.hash}\t{tel}\t{vhash}\t{red}\t{prot}\t{nc}\t{name.isInternal}"
    if editedModules.contains modName then
      nEdited := nEdited + 1
      if let some d ← findDocString? env name then
        docs := docs.push s!"{name}\t{modName}\t{hash d}"
  for m in editedModules do
    let mds := getModuleDoc? env m |>.getD #[]
    let mut i := 0
    for md in mds do
      docs := docs.push s!"<module doc {i}>\t{m}\t{hash md.doc}"
      i := i + 1
  let sortedRows := rows.qsort (· < ·)
  let sortedDocs := docs.qsort (· < ·)
  IO.FS.writeFile out (String.intercalate "\n" sortedRows.toList ++ "\n")
  IO.FS.writeFile docOut (String.intercalate "\n" sortedDocs.toList ++ "\n")
  IO.println s!"dumped {rows.size} constants of Causal.* modules ({nEdited} in the nine edited) to {out}"
  IO.println s!"dumped {docs.size} docstring hashes to {docOut}"

-- 3. the names cited in place of the line references, with their modules
#eval show CoreM Unit from do
  let env ← getEnv
  let cited : List (Name × Name) :=
    [(`Causal.Causality.not_pastBoundaryChart_of_flrwType, `Causal.FlrwType),
     (`Causal.Causality.not_futureBoundaryChart_of_flrwType, `Causal.FlrwType),
     (`Causal.Causality.CurvesExtend, `Causal.CauchyExtension),
     (`Causal.Causality.IsCauchySurface.isAcausal, `Causal.CauchyExtension),
     (`Causal.Causality.exists_inextensible_of_t1_secondCountable,
       `Causal.CurvesExtendSecondCountable),
     (`Causal.isolatedLine_scOpen_without_tarentin, `Causal.SCOpenWithoutTarentin),
     (`Causal.timelikeLine_chronalCurveOn_iff, `Causal.TimelikeHomotopy),
     (`Causal.minkowski_pastBoundaryChart, `Causal.Model.MinkowskiPastBoundaryChart),
     (`Causal.Causality.dual_dual, `Causal.Causality),
     (`Causal.Causality.FutureBoundaryChart, `Causal.FlrwType)]
  for (n, m) in cited do
    match env.getModuleIdxFor? n with
    | some i =>
      let m' := env.header.moduleNames[i.toNat]!
      IO.println s!"{n} : {m'} {if m' == m then "(as cited)" else s!"(cited as {m}: MISMATCH)"}"
    | none => IO.println s!"{n} : NOT FOUND"
  -- the binder names `hA`, `hB` that items (A), (B) of the checklist cite
  let some ci := env.find? `Causal.Causality.not_pastBoundaryChart_of_flrwType | throwError "no"
  IO.println s!"binders of not_pastBoundaryChart_of_flrwType: {telescope ci.type}"

-- 4. item 7's sentence
section Item7

open Causal Causality

/-- The type claim, as the target states it. -/
example (n : ℕ) (hn : 0 < n) :
    (minkowski n).dual.FutureBoundaryChart (minkowskiPosHalfSpace n) (minkowskiChartBox n) 0 :=
  minkowski_pastBoundaryChart hn

/-- The same, through `FutureBoundaryChart`'s definition and `Causality.dual_dual` explicitly. -/
example (n : ℕ) (hn : 0 < n) :
    (minkowski n).dual.FutureBoundaryChart (minkowskiPosHalfSpace n) (minkowskiChartBox n) 0 := by
  rw [FutureBoundaryChart, Causality.dual_dual]
  exact minkowski_pastBoundaryChart hn

/-- `Causality.dual_dual` is `rfl`. -/
example (n : ℕ) : (minkowski n).dual.dual = minkowski n := rfl

/-- Item 4's globally hyperbolic form at `(minkowski n).dual`: the time-reversed (A) fails at the
half-space, so the time reversal's conclusion is not vacuous there. -/
example (n : ℕ) (hn : 0 < n) :
    ¬ ∀ (I : Set ℝ) (γ : ℝ → Minkowski n),
      (minkowski n).dual.FutureInextensible (minkowskiPosHalfSpace n) I γ →
      (∀ a ∈ I, ∀ b ∈ I, (minkowski n).dual.ChronalCurveOn (minkowskiPosHalfSpace n) γ a b) →
      ⋃ t ∈ I, (minkowski n).dual.Iminus (minkowskiPosHalfSpace n) {γ t} =
        minkowskiPosHalfSpace n :=
  fun hA => GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeA
    (dual_tarentin.2 minkowski_tarentin) (dual_globallyHyperbolic.2 minkowski_globallyHyperbolic)
    hA (minkowskiChartBox n) 0 (minkowski_pastBoundaryChart hn)

/-- Item 5's globally hyperbolic time reversal at `(minkowski n).dual`: the time-reversed (B), with
`S ⊆ I⁺(x, W)`, fails at the half-space, which is causally arc-connected for `C.dual` as for `C`. -/
example (n : ℕ) (hn : 0 < n) :
    ¬ ∀ x ∈ minkowskiPosHalfSpace n, ∃ S : Set (Minkowski n),
      (minkowski n).dual.IsCauchySurfaceOn (minkowskiPosHalfSpace n) S ∧
        S ⊆ (minkowski n).dual.Iplus (minkowskiPosHalfSpace n) {x} :=
  fun hB => GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeB
    (dual_tarentin.2 minkowski_tarentin) (dual_globallyHyperbolic.2 minkowski_globallyHyperbolic)
    (dual_causallyArcConnectedOn.2 (minkowski_posHalfSpace_flrwType_check hn).2.2.2.1)
    hB (minkowskiChartBox n) 0 (minkowski_pastBoundaryChart hn)

end Item7
