import Causal.GluingModels.Tools
import Causal.GluingModels.Pushout
import Causal.SingularFlat
import Causal.SingularGeroch
import Causal.Port.E0Axioms
import Causal.Port.ModelRowsE0
import Causal.Port.SFALocalE0
import Causal.Port.SFALocal
import Causal.Port.CupCapBTZCounterexample
import Causal.Remarks.MassiveManifold
import Causal.Remarks.MassADEC25
import Causal.Remarks.Tarentin
import Causal.MaximalAEAtlasIso
import Causal.CBG.Geometry
import Causal.CBG.FromModel
import Causal.LemmaKObstruction

/-!
# Gluing inventory (DEC-167), model layer: E₀, the singular flat spacetimes, the Remarks and Port

No paper label is certified by this file. The model objects of the inventory of
`T-abs-gluing-models` beyond the static ones (`GluingModels.ModelStatic`):

* **glue hereditarily** (hence on `M`):
  - every `SingularFlatAxioms` causality (its field `causallyArcConnected`, `cor:massA_cac`), so
    every `SingularFlatSpacetime`;
  - the natural causality of `E₀ ∖ {w}` (`CupCapBTZCounterexample.natCausality`, the witness
    against `lem:cup_cap_BTZ` as printed), from `SFALocalE0.causallyArcConnected`;
  - `massiveOf κ` and every model of the family `massAModelCausality o` (`E₀` at `none`, `E_κ`
    at `some κ`);
  - the branching line (`CBG.branchingCausality`, non-Hausdorff), the gluing of two timelike
    lines (`GluingModels.Gluing.causality_hereditary`);
  - `withoutChronology C` whenever `C` glues hereditarily.
* **do not glue** (not absolutely minimal on `M`): the `ofRelation` witnesses of
  `Causal.Remarks.Tarentin`, `sourceLine` and `radialLine` (their own docstrings say "not local").
* cited, not restated: `E0.absolutelyMinimalOn` (every open), `e0_absolutelyMinimal`,
  `AESupportCounterexample.absolutelyMinimalOn_segCausality`, `CBG.PreGeometry.absolutelyMinimalOn`
  (a field: every causality of a CBG geometry glues hereditarily),
  `CBG.chartedCausality_absolutelyMinimalOn`.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff | ⚠ weakened: not used |

## SCOPE (disclosed)

* No definition changes; OQ-95 and OQ-96 are not decided here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace GluingModels

open Set TopologicalSpace Topology Relation

/-! ### Singular flat spacetimes -/

/-- **Every causality with the singular-flat axioms glues hereditarily** (its field
`causallyArcConnected`). -/
theorem singularFlatAxioms_hereditary {M : Type*} [TopologicalSpace M] {C : Causality M}
    {sing : ℝ → Set M} (h : C.SingularFlatAxioms sing) : ∀ W : Opens M, C.AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected h.causallyArcConnected

theorem singularFlatSpacetime_hereditary {M : Type*} [TopologicalSpace M] {C : Causality M}
    {sing : ℝ → Set M} (h : C.SingularFlatSpacetime sing) :
    ∀ W : Opens M, C.AbsolutelyMinimalOn W :=
  singularFlatAxioms_hereditary h.toSingularFlatAxioms

section Puncture

attribute [local instance] E0GX.singularGX

/-- **The natural causality of `E₀ ∖ {w}` glues hereditarily** (`SFALocalE0.causallyArcConnected`). -/
theorem natCausality_hereditary :
    ∀ W : Opens CupCapBTZCounterexample.puncture,
      CupCapBTZCounterexample.natCausality.AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected (SFALocalE0.causallyArcConnected
    CupCapBTZCounterexample.e0Covered CupCapBTZCounterexample.isE0Natural_natCausality)

theorem natCausality_minimal : CupCapBTZCounterexample.natCausality.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall natCausality_hereditary

end Puncture

/-! ### `E≥0`-manifolds -/

section EManifold

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- **On an `E≥0`-manifold, the causality of a DEC-25 iso-charts cover glues hereditarily as soon as
it glues on `M`** (`SFALocal.causallyArcConnected`, `cor:massA_cac`): for these objects the two
forms of OQ-95 coincide. -/
theorem eManifold_hereditary_of_minimal (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    ∀ W : Opens M, C.AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected (SFALocal.causallyArcConnected hmin hC)

/-- The natural causality of an `E₀`-manifold glues hereditarily. -/
theorem e0Manifold_hereditary (hcov : SFALocalE0.E0Covered M) (hC : SFALocalE0.IsE0Natural C) :
    ∀ W : Opens M, C.AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected (SFALocalE0.causallyArcConnected hcov hC)

end EManifold

/-- `massiveOf κ` glues hereditarily. -/
theorem massiveOf_hereditary (κ : {κ : ℝ // 0 < κ}) :
    ∀ W : Opens (Massive κ.1), (massiveOf κ).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected (@massive_causallyArcConnected κ.1 ⟨κ.2⟩)

/-- Every model of the `E≥0` family glues hereditarily (`massAModel_facts`). -/
theorem massAModelCausality_hereditary (o : Option {κ : ℝ // 0 < κ}) :
    ∀ W : Opens (MassAModel o), (massAModelCausality o).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected (massAModel_facts o).1

/-! ### The branching line -/

/-- **The branching line glues hereditarily**: the gluing of two timelike lines along
`]-∞, 0[`, though it is not Hausdorff. -/
theorem branchingCausality_hereditary :
    ∀ W : Opens CBG.BranchingLine, CBG.branchingCausality.AbsolutelyMinimalOn W :=
  Gluing.causality_hereditary CBG.branchingLine_compatibleAlong timelikeLine_absolutelyMinimalOn
    timelikeLine_absolutelyMinimalOn

theorem branchingCausality_minimal : CBG.branchingCausality.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall branchingCausality_hereditary

/-! ### Without chronology -/

/-- `C` without chronology glues on `W` when `C` does: the causal half is that of `C`, the
chronological half is empty. -/
theorem withoutChronology_absolutelyMinimalOn {M : Type*} [TopologicalSpace M] {C : Causality M}
    {W : Opens M} (h : C.AbsolutelyMinimalOn W) : C.withoutChronology.AbsolutelyMinimalOn W :=
  fun S hS V hV x y => ⟨(h S hS V hV x y).1, fun hxy => hxy.elim⟩

theorem withoutChronology_hereditary {M : Type*} [TopologicalSpace M] {C : Causality M}
    (h : ∀ W : Opens M, C.AbsolutelyMinimalOn W) :
    ∀ W : Opens M, C.withoutChronology.AbsolutelyMinimalOn W := fun W =>
  withoutChronology_absolutelyMinimalOn (h W)

/-! ### The non-local witnesses of `Causal.Remarks.Tarentin` -/

/-- `sourceLine` (`y ≤ z ↔ y = z ∨ 0 ≤ y < z` in every open set) is not absolutely minimal. -/
theorem sourceLine_not_minimal : ¬ sourceLine.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_le_of_ne zero_ne_one fun V h0 h1 => by
    unfold sourceLine; exact ⟨h0, h1, Or.inr ⟨le_rfl, zero_lt_one⟩⟩

theorem sourceLine_not_hereditary : ¬ ∀ W, sourceLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal sourceLine_not_minimal

/-- `radialLine` (`y ≤ z ↔ y = z ∨ |y| < |z|` in every open set) is not absolutely minimal. -/
theorem radialLine_not_minimal : ¬ radialLine.AbsolutelyMinimal :=
  not_absolutelyMinimal_of_le_of_ne zero_ne_one fun V h0 h1 => by
    unfold radialLine; exact ⟨h0, h1, Or.inr (by norm_num)⟩

theorem radialLine_not_hereditary : ¬ ∀ W, radialLine.AbsolutelyMinimalOn W :=
  not_forall_of_not_absolutelyMinimal radialLine_not_minimal

end GluingModels

end Causal
