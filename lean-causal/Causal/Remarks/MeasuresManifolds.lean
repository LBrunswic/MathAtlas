import Causal.Port.MeasuresE0
import Causal.Model.MeasuresEAlpha
import Causal.Remarks.MassAModelsInstance
import Causal.Port.SFALocalE0
import Causal.MeasureTransfer

/-!
# Admissible measures at every strongly causal `E_{≥0}`-manifold, through isomorphic charts

Target `T-ett-measures-manifolds` (no `sorry`; its model-free half is `Causal.MeasureTransfer`). Cited, **unmarked** (SCOPE (a)):
`prop:mesure_admissible` — `ETT.tex:1726`; `rem:singular_flat_spacetime_therefore` —
`ETT.tex:1508`. Hypothesis (i) of the proof of `prop:mesure_admissible` is proved at every strongly
causal `E_{≥0}`-manifold, for every absolutely minimal causality with an isomorphic chart at each
point (`ModelMeasures`, in local form); both rows then follow from `SingularFlatAxioms` alone.

> Let $M$ be a strongly causal $\mass{\geq 0}$-manifold. Then $M$ carries a measure $\mu_-$
> admissible in the past and a measure $\mu_+$ admissible in the future. (`ETT.tex:1726–1727`)

> Strong causality provides a relatively compact open neighbourhood $\U_p$ of $p$, causally
> convex in $M$ and contained in a chart with model $\mass{\kappa}$. [...] Restricted to the
> relatively compact $\U_p$ these measures are finite, so property $2$ holds too, and Lemma
> \ref{lem:restriction_convexe} turns properties $3$ and $4$ of the model into properties $3$ and
> $4$ of $\U_p$. (`ETT.tex:1734–1743`)

> A singular flat spacetime is therefore a differential manifold and satisfies all the
> hypotheses of Geroch's Theorem \ref{theo:geroch}. (`ETT.tex:1509–1510`)

## What is proved (no `sorry`)

* **The transfer, model-free** (sections `Local` to `Cover`, ETT-layer declarations only).
  `ChartIso.admissiblePastOn` / `admissibleFutureOn`: a measure admissible on `e(U)` comes back
  to an admissible measure on `U`, for every open `U` in the source of a chart isomorphism `e`;
  properties 1.–4. pass through the homeomorphism `U ≃ e(U)` and the subtype reading
  (`admissiblePastOn_map_subtype_iff`), with the transport of `J⁻` and `K⁻`
  (`ChartIso.symm_mem_Jminus_iff`, `ChartIso.symm_mem_Kminus_iff`, from
  `mem_Kminus_of_intertwine`). No causal convexity enters the transfer itself.
* **The model's set first** (SCOPE (b)). `ChartIso.exists_admissiblePastOn`: inside every
  neighbourhood `N` of `p`, `U = e⁻¹(U')` with `U'` causally convex in the model inside
  `e(V)`, `V ⊆ e.source ∩ N` causally convex in `M` (DEC-7's `StronglyCausal`); `U` is causally
  convex in `M` (`ChartIso.causallyConvexIn_source_inter_preimage`, through
  `le_of_causallyConvexIn_of_subset`, a variant of `le_iff_of_causallyConvexIn`), and `e(U) = U'`
  is causally convex in the model.
* **A cover by isomorphic charts**: `isoChartsCover_modelMeasuresLocal`,
  `isoChartsCover_modelMeasures` (`SFATransfer.IsoChartsCover`). The models in local form
  (`ModelMeasuresLocal`): `minkowski_modelMeasuresLocal`, `e0_modelMeasuresLocal`,
  `massive_modelMeasuresLocal`, `massAModel_modelMeasuresLocal`, with the family instances
  `instMeasurableSpaceMassAModel`, `instBorelSpaceMassAModel` (by cases, reducing to `E₀`'s and
  `E_κ`'s).
* **`E_{≥0}`-manifolds** (`IsoChartsCoverDEC25`, any `G`, any singular structures of the models):
  `massA_modelMeasuresLocal`, `massA_modelMeasures`, `massA_modelMeasures_of_natural`; the
  conditionals `massA_mesure_admissible` (`prop:mesure_admissible`) and `massA_geroch_hypotheses`
  (`rem:singular_flat_spacetime_therefore`, DEC-18), from `SingularFlatAxioms`.
  **`E₀`-manifolds**: `e0Manifold_modelMeasures(Local)`, and `e0Manifold_mesure_admissible`,
  `e0Manifold_geroch_hypotheses` from the three BTZ fields `SFALocalE0.singularFlatAxioms_iff`
  leaves.
* **Witnesses with a singular point**: `e0_nonvacuous` (every hypothesis of
  `massA_mesure_admissible` at `E₀`), `e0Manifold_nonvacuous`, `epi_nonvacuous`.
* **Why the model's set comes first** (finding): `cutDiamond_separates`. In `M = E^{1,2} ∖ {0}`
  the cut diamond is open, causally convex in `M` and inside the chart (the inclusion, a chart
  isomorphism), with compact closure in `E^{1,2}` (not relatively compact in `M`: its closure misses
  the centre), and its image is not causally convex in the model `E^{1,2}`. A relatively compact
  example in `M` exists (by hand, not formalized): remove the closed disc `{t = 0, |x| ≤ 3}` and
  take `I((−1.1,0),(−0.9,0)) ∪ I((0.9,0),(1.1,0))`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` an `E_{≥0}`-manifold (l.1726) | ⚠ reading (DEC-25, OQ-18): an absolutely minimal causality with an isomorphic chart at each point (`IsoChartsCoverDEC25`), the natural one included (`massA_modelMeasures_of_natural`); for the two rows, `SingularFlatAxioms` ⚠ strengthened |
| strongly causal (l.1726) | ✓ carried, DEC-7's `StronglyCausal` (a neighbourhood, not necessarily open); used for `V`, not the open form |
| strongly causal, in `rem:singular_flat_spacetime_therefore` (l.1508–1510) | ⚠ strengthened: assumed (DEC-18); the remark as printed does not |
| topological spacetime: Hausdorff (`ETT.tex:254`) | ⚠ weakened: `R1Space M` (regularity of the measure carried back); second countable not used by `ModelMeasures` (`SingularFlatAxioms` carries both for the rows) |
| causally arc-connected (`cor:massA_cac`, l.1731) | ✓ discharged: `massA_dec25_models_of_isoChartsCover`, `SFALocalE0.causallyArcConnected` |
| `U_p` relatively compact, in a chart (l.1734–1736) | ⚠ weakened: `U ⊆ e.source` inside any neighbourhood; compactness not needed (finite model measures) |
| `λ₃`, `λ₃ + λ₁` on the models (l.1736–1741) | ✓ as in `Causal.Port.MeasuresE0`, `Causal.Model.MeasuresEAlpha` (their `modelMeasures_local`); on `E^{1,2}` a finite measure in the class of `λ₃` |
| hypothesis (ii), `prop:K_monotone` | not here: `SingularFlatAxioms.K_monotone`, inside `mesure_admissible` |
| « a differential manifold » (l.1509) | not formalized |

## SCOPE (disclosed)

* **(a) Unmarked.** Both rows are conditional on `SingularFlatAxioms` for every
  `E_{≥0}`-manifold (T-ett-singular-sfa); `E_{≥0}`-manifold and « natural » are readings (DEC-25,
  OQ-18, OQ-82), `E₀` is read as in OQ-34/OQ-35; « a differential manifold » is not formalized.
* **(b) The chart image.** The paper's `U_p` is causally convex in `M`; `lem:restriction_convexe`
  applied in the model needs its image causally convex in the model, which convexity in `M` does
  not give (`cutDiamond_separates`). Here the model's set `U'` is chosen first and
  `U = e⁻¹(U')` is proved convex in `M`. The measure on `U'` comes from the model's local form
  (property 3. through `pos_past_inter`, kb/0148).
* **(c) Layers.** The model-free sections (`Local` to `Cover`) are the ETT-layer module
  `Causal.MeasureTransfer` (split at graduation, kb 0047; same full names). `CutDiamond` needs
  `Causal.Minkowski`, a metric model, and stays here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace MeasuresManifolds

open Set Filter Topology TopologicalSpace MeasureTheory SFATransfer

universe u v w y z


/-! ### The models in local form -/

section Models

/-- **Minkowski space `ℝ^{1,n}` in local form.** -/
theorem minkowski_modelMeasuresLocal (n : ℕ) : ModelMeasuresLocal (minkowski n) := by
  have hpos : ∀ O : Set (Minkowski n), IsOpen O → O.Nonempty →
      0 < ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin n)))).toFinite O :=
    fun O hO hne => pos_iff_ne_zero.2 fun h0 =>
      (hO.measure_pos ((volume : Measure ℝ).prod volume) hne).ne'
        (absolutelyContinuous_toFinite _ h0)
  refine ModelMeasuresLocal.of_forall fun p N hN => ?_
  obtain ⟨U, hpU, hUN, hU⟩ := staticCausality.stronglyCausalOpen p N hN
  exact ⟨U, hpU, hUN, hU,
    ⟨_, MeasuresEAlpha.static_admissiblePastOn_restrict_of
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (toFinite_absolutelyContinuous _) hpos hU⟩,
    ⟨_, MeasuresEAlpha.static_admissibleFutureOn_restrict_of
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (toFinite_absolutelyContinuous _) hpos hU⟩⟩

/-- **`E₀` in local form** (`E0.modelMeasures_local`). -/
theorem e0_modelMeasuresLocal : ModelMeasuresLocal E0.causality :=
  ModelMeasuresLocal.of_forall fun p _ hN => E0.modelMeasures_local p hN

/-- **`E_κ`, `κ > 0`, in local form** (`MeasuresEAlpha.modelMeasures_local`). -/
theorem massive_modelMeasuresLocal (κ : ℝ) [Fact (0 < κ)] : ModelMeasuresLocal (massive κ) :=
  ModelMeasuresLocal.of_forall fun p _ hN => MeasuresEAlpha.modelMeasures_local p hN

/-- **The Borel σ-algebras of the models of `E_{≥0}`**, by cases: `E₀ = ℝ × ℂ`'s and
`E_κ = ℝ × C_κ`'s (`MeasuresEAlpha.instMeasurableSpaceCone`). -/
noncomputable instance instMeasurableSpaceMassAModel : ∀ o, MeasurableSpace (MassAModel o)
  | none => inferInstanceAs (MeasurableSpace E0)
  | some κ => inferInstanceAs (MeasurableSpace (Massive κ.1))

/-- They are Borel. -/
instance instBorelSpaceMassAModel : ∀ o, BorelSpace (MassAModel o)
  | none => inferInstanceAs (BorelSpace E0)
  | some κ => inferInstanceAs (BorelSpace (Massive κ.1))

/-- **Every model of `E_{≥0}` in local form.** -/
theorem massAModel_modelMeasuresLocal :
    ∀ o, ModelMeasuresLocal (massAModelCausality o)
  | none => e0_modelMeasuresLocal
  | some κ => @massive_modelMeasuresLocal κ.1 ⟨κ.2⟩

end Models

/-! ### `E_{≥0}`-manifolds -/

section Manifolds

variable {G : Type w} [Group G] [MulAction G (Minkowski 2)] {M : Type u} [TopologicalSpace M]
  [SingularGXStructure G (Minkowski 2) M] [∀ o, SingularGXStructure G (Minkowski 2) (MassAModel o)]
  [MeasurableSpace M] [BorelSpace M] {C : Causality M}

/-- **Hypothesis (i) of `prop:mesure_dieckmann_topo` in local form at every strongly causal
`E_{≥0}`-manifold**, for every absolutely minimal causality with an isomorphic chart at each point
(into `E^{1,2}` or into some `E_κ`, `κ ≥ 0`): every neighbourhood of every point contains an open
neighbourhood, causally convex in `M`, carrying a measure admissible in the past, and one carrying
a measure admissible in the future. -/
theorem massA_modelMeasuresLocal [R1Space M] (hmin : C.AbsolutelyMinimal)
    (hcover : IsoChartsCoverDEC25 G C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) : ModelMeasuresLocal C :=
  isoChartsCover_modelMeasuresLocal (SFALocalE0.isoChartsCover_of_dec25 hcover)
    (massA_dec25_models_of_isoChartsCover hmin hcover).1 hSC (minkowski_modelMeasuresLocal 2)
    massAModel_modelMeasuresLocal

/-- **`ModelMeasures` at every strongly causal `E_{≥0}`-manifold**, for every absolutely minimal
causality with an isomorphic chart at each point (into `E^{1,2}` or into some `E_κ`, `κ ≥ 0`). -/
theorem massA_modelMeasures [R1Space M] (hmin : C.AbsolutelyMinimal)
    (hcover : IsoChartsCoverDEC25 G C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) : C.ModelMeasures :=
  (massA_modelMeasuresLocal hmin hcover hSC).modelMeasures

/-- **`ModelMeasures` for the natural causality** of a strongly causal `E_{≥0}`-manifold (DEC-25),
its singular points in `X_A`-charts. -/
theorem massA_modelMeasures_of_natural [R1Space M]
    (hcov : ∀ x ∈ Sing G (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart G (Minkowski 2) e ∧ x ∈ e.source)
    (hC : IsAtlasCausalityDEC25 G C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) : C.ModelMeasures :=
  massA_modelMeasures hC.2.2 (hC.isoChartsCover hcov) hSC

/-- **`prop:mesure_admissible` at every strongly causal `E_{≥0}`-manifold satisfying
`SingularFlatAxioms`.** -/
theorem massA_mesure_admissible {sing : ℝ → Set M} (hSFA : C.SingularFlatAxioms sing)
    (hcover : IsoChartsCoverDEC25 G C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) :
    (∃ μ : Measure M, C.AdmissiblePast μ) ∧ ∃ μ : Measure M, C.AdmissibleFuture μ := by
  haveI := hSFA.t2
  exact hSFA.mesure_admissible hSC.isCausal (massA_modelMeasures hSFA.absolutelyMinimal hcover hSC)

/-- **`rem:singular_flat_spacetime_therefore` at every strongly causal `E_{≥0}`-manifold satisfying
`SingularFlatAxioms`**: every hypothesis of `theo:geroch`. -/
theorem massA_geroch_hypotheses {sing : ℝ → Set M} (hSFA : C.SingularFlatAxioms sing)
    (hcover : IsoChartsCoverDEC25 G C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) :
    MetrizableSpace M ∧ LocallyCompactSpace M ∧ C.Tarentin ∧ C.CausallyArcConnected ∧
      C.StronglyCausal ∧ (∀ p : M, C.Jminus ⊤ {p} ≠ {p}) ∧ (∀ p : M, C.Jplus ⊤ {p} ≠ {p}) ∧
      ∃ μp μm : Measure M, C.AdmissibleFuture μp ∧ C.AdmissiblePast μm := by
  haveI := hSFA.t2
  exact hSFA.geroch_hypotheses hSC (massA_modelMeasures hSFA.absolutelyMinimal hcover hSC)

end Manifolds

/-! ### `E₀`-manifolds with their natural causality -/

section E0Manifolds

attribute [local instance] E0GX.singularGX

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  [MeasurableSpace M] [BorelSpace M] {C : Causality M}

/-- **Hypothesis (i) in local form at every strongly causal `E₀`-manifold** with its natural
causality (`SFALocalE0.IsE0Natural`). -/
theorem e0Manifold_modelMeasuresLocal [R1Space M] (hcov : SFALocalE0.E0Covered M)
    (hC : SFALocalE0.IsE0Natural C) (hSC : C.StronglyCausal) : ModelMeasuresLocal C :=
  isoChartsCover_modelMeasuresLocal (SFALocalE0.isoChartsCover hcov hC)
    (SFALocalE0.causallyArcConnected hcov hC) hSC (minkowski_modelMeasuresLocal 2)
    fun _ => e0_modelMeasuresLocal

/-- **`ModelMeasures` at every strongly causal `E₀`-manifold** with its natural causality. -/
theorem e0Manifold_modelMeasures [R1Space M] (hcov : SFALocalE0.E0Covered M)
    (hC : SFALocalE0.IsE0Natural C) (hSC : C.StronglyCausal) : C.ModelMeasures :=
  (e0Manifold_modelMeasuresLocal hcov hC hSC).modelMeasures

/-- **`prop:mesure_admissible` at every Hausdorff, second countable, strongly causal
`E₀`-manifold**, given the three BTZ fields of `SingularFlatAxioms` that
`SFALocalE0.singularFlatAxioms_iff` leaves (T-ett-singular-sfa). -/
theorem e0Manifold_mesure_admissible [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocalE0.E0Covered M) (hC : SFALocalE0.IsE0Natural C) (hSC : C.StronglyCausal)
    (hpast : ∀ p ∈ SFALocalE0.sing M 0, C.SingularPastAt p)
    (hlt : ∀ p ∈ SFALocalE0.sing M 0, ∀ p' ∈ SFALocalE0.sing M 0, C.le ⊤ p p' → p ≠ p' →
      C.Jplus ⊤ {p'} \ SFALocalE0.sing M 0 ⊆ C.Iplus ⊤ {p})
    (hline : ∀ p ∈ SFALocalE0.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧
      (C.IsCausal → IsClosedEmbedding γ) ∧ C.Inextensible ⊤ univ γ ∧
        range γ = connectedComponentIn (SFALocalE0.sing M 0) p) :
    (∃ μ : Measure M, C.AdmissiblePast μ) ∧ ∃ μ : Measure M, C.AdmissibleFuture μ :=
  ((SFALocalE0.singularFlatAxioms_iff hcov hC).2 ⟨hpast, hlt, hline⟩).mesure_admissible
    hSC.isCausal (e0Manifold_modelMeasures hcov hC hSC)

/-- **`rem:singular_flat_spacetime_therefore` at every Hausdorff, second countable, strongly causal
`E₀`-manifold**, given the same three BTZ fields. -/
theorem e0Manifold_geroch_hypotheses [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocalE0.E0Covered M) (hC : SFALocalE0.IsE0Natural C) (hSC : C.StronglyCausal)
    (hpast : ∀ p ∈ SFALocalE0.sing M 0, C.SingularPastAt p)
    (hlt : ∀ p ∈ SFALocalE0.sing M 0, ∀ p' ∈ SFALocalE0.sing M 0, C.le ⊤ p p' → p ≠ p' →
      C.Jplus ⊤ {p'} \ SFALocalE0.sing M 0 ⊆ C.Iplus ⊤ {p})
    (hline : ∀ p ∈ SFALocalE0.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧
      (C.IsCausal → IsClosedEmbedding γ) ∧ C.Inextensible ⊤ univ γ ∧
        range γ = connectedComponentIn (SFALocalE0.sing M 0) p) :
    MetrizableSpace M ∧ LocallyCompactSpace M ∧ C.Tarentin ∧ C.CausallyArcConnected ∧
      C.StronglyCausal ∧ (∀ p : M, C.Jminus ⊤ {p} ≠ {p}) ∧ (∀ p : M, C.Jplus ⊤ {p} ≠ {p}) ∧
      ∃ μp μm : Measure M, C.AdmissibleFuture μp ∧ C.AdmissiblePast μm :=
  ((SFALocalE0.singularFlatAxioms_iff hcov hC).2 ⟨hpast, hlt, hline⟩).geroch_hypotheses hSC
    (e0Manifold_modelMeasures hcov hC hSC)

end E0Manifolds

/-! ### Non-vacuity: models with a singular point, as manifolds -/

section Witnesses

section E0Witness

attribute [local instance] E0GX.singularGX

/-- **Witness at `E₀` over the whole family**: `E₀` (singular locus the axis, non-empty) with
`E0.causality` satisfies every hypothesis of `massA_modelMeasures`, and of `massA_mesure_admissible`
with `SingularFlatAxioms` (`E0.singularFlatAxioms`), whose conclusion it then has. -/
theorem e0_nonvacuous :
    (Sing (Flat.isom 2) (Minkowski 2) E0).Nonempty ∧
      IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      E0.causality.AbsolutelyMinimal ∧ E0.causality.StronglyCausal ∧
      E0.causality.SingularFlatAxioms E0.singE0 ∧ ModelMeasuresLocal E0.causality ∧
      E0.causality.ModelMeasures ∧
      ((∃ μ : Measure E0, E0.causality.AdmissiblePast μ) ∧
        ∃ μ : Measure E0, E0.causality.AdmissibleFuture μ) := by
  obtain ⟨hne, hcover, -, -⟩ := MassAModelsInstance.e0_witness
  have hmin := E0.causallyArcConnected.absolutelyMinimal
  exact ⟨hne, hcover, hmin, E0.stronglyCausal, E0.singularFlatAxioms,
    massA_modelMeasuresLocal hmin hcover E0.stronglyCausal,
    massA_modelMeasures hmin hcover E0.stronglyCausal,
    massA_mesure_admissible E0.singularFlatAxioms hcover E0.stronglyCausal⟩

/-- **Witness at `E₀` as an `E₀`-manifold**: `E₀` with its natural causality satisfies every
hypothesis of `e0Manifold_mesure_admissible`, its BTZ fields included. -/
theorem e0Manifold_nonvacuous :
    SFALocalE0.E0Covered E0 ∧ SFALocalE0.IsE0Natural E0.causality ∧
      (SFALocalE0.sing E0 0).Nonempty ∧ E0.causality.ModelMeasures ∧
      ((∃ μ : Measure E0, E0.causality.AdmissiblePast μ) ∧
        ∃ μ : Measure E0, E0.causality.AdmissibleFuture μ) := by
  obtain ⟨hcov, hC, -, hne⟩ := SFALocalE0.nonvacuous
  obtain ⟨h1, h2, h3⟩ :=
    (SFALocalE0.singularFlatAxioms_iff hcov hC).1 SFALocalE0.e0_singularFlatAxioms
  exact ⟨hcov, hC, hne, e0Manifold_modelMeasures hcov hC E0.stronglyCausal,
    e0Manifold_mesure_admissible hcov hC E0.stronglyCausal h1 h2 h3⟩

end E0Witness

section EPiWitness

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- **Witness at `E_π` over the whole family**: `E_π` (singular locus the line, non-empty) with
`massive π` satisfies every hypothesis of `massA_modelMeasures`. -/
theorem epi_nonvacuous :
    (Sing (Flat.isom 2) (Minkowski 2) (Massive Real.pi)).Nonempty ∧
      IsoChartsCoverDEC25 (Flat.isom 2) (massive Real.pi) (minkowski 2) massAModelCausality ∧
      (massive Real.pi).AbsolutelyMinimal ∧ (massive Real.pi).StronglyCausal ∧
      ModelMeasuresLocal (massive Real.pi) ∧ (massive Real.pi).ModelMeasures := by
  obtain ⟨hne, hcover, -, -⟩ := MassAModelsInstance.epi_witness
  exact ⟨hne, hcover, massive_absolutelyMinimal, massive_stronglyCausal,
    massA_modelMeasuresLocal massive_absolutelyMinimal hcover massive_stronglyCausal,
    massA_modelMeasures massive_absolutelyMinimal hcover massive_stronglyCausal⟩

end EPiWitness

end Witnesses

/-! ### Why the model's set comes first: `E^{1,2}` minus a point -/

section CutDiamond

/-- The point `(t, 0)` of `E^{1,2}`. -/
noncomputable abbrev tpt (t : ℝ) : Minkowski 2 := (t, 0)

/-- **The cut diamond**: the open diamond `I((-2, 0), (2, 0))` of `E^{1,2}` with its centre removed. -/
def cutDiamond : Set (Minkowski 2) :=
  {x | (minkowski 2).lt ⊤ (tpt (-2)) x ∧ (minkowski 2).lt ⊤ x (tpt 2) ∧ x ≠ tpt 0}

/-- `E^{1,2}` minus the point `(0, 0)`, an open set: the spacetime `M` of the example. -/
def puncture : Opens (Minkowski 2) := ⟨{tpt 0}ᶜ, isOpen_compl_singleton⟩

/-- **The cut diamond is causally convex in `E^{1,2}` minus its centre.** -/
theorem cutDiamond_causallyConvexIn_puncture :
    (minkowski 2).CausallyConvexIn cutDiamond puncture := by
  refine ⟨fun x hx => hx.2.2, fun x hx z hz y hy => ?_⟩
  obtain ⟨hxy, hyz⟩ := Causality.mem_diamond.1 hy
  have hy0 : y ≠ tpt 0 := (minkowski 2).le_mem_right hxy
  have hxy' := (minkowski 2).le_mono le_top hxy
  have hyz' := (minkowski 2).le_mono le_top hyz
  rw [minkowski_le_top_iff] at hxy' hyz'
  have ha := hx.1
  have hb := hz.2.1
  rw [minkowski_lt_top_iff] at ha hb
  refine ⟨?_, ?_, hy0⟩
  · rw [minkowski_lt_top_iff]
    calc ‖y.2 - (tpt (-2)).2‖ ≤ ‖y.2 - x.2‖ + ‖x.2 - (tpt (-2)).2‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < (y.1 - x.1) + (x.1 - (tpt (-2)).1) := add_lt_add_of_le_of_lt hxy' ha
      _ = y.1 - (tpt (-2)).1 := by ring
  · rw [minkowski_lt_top_iff]
    calc ‖(tpt 2).2 - y.2‖ ≤ ‖(tpt 2).2 - z.2‖ + ‖z.2 - y.2‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ((tpt 2).1 - z.1) + (z.1 - y.1) := add_lt_add_of_lt_of_le hb hyz'
      _ = (tpt 2).1 - y.1 := by ring

/-- **The cut diamond is not causally convex in `E^{1,2}`**: `(0, 0)` lies between `(-1, 0)` and
`(1, 0)`. -/
theorem not_cutDiamond_causallyConvexIn_top : ¬ (minkowski 2).CausallyConvexIn cutDiamond ⊤ := by
  intro h
  have hx : tpt (-1) ∈ cutDiamond := ⟨by rw [minkowski_lt_top_iff]; norm_num,
    by rw [minkowski_lt_top_iff]; norm_num, by simp [tpt]⟩
  have hz : tpt 1 ∈ cutDiamond := ⟨by rw [minkowski_lt_top_iff]; norm_num,
    by rw [minkowski_lt_top_iff]; norm_num, by simp [tpt]⟩
  have h0 : tpt 0 ∈ (minkowski 2).diamond ⊤ (tpt (-1)) (tpt 1) :=
    Causality.mem_diamond.2 ⟨by rw [minkowski_le_top_iff]; norm_num,
      by rw [minkowski_le_top_iff]; norm_num⟩
  exact (h.2 _ hx _ hz h0).2.2 rfl

/-- **The step `lem:restriction_convexe` in the model needs the image convex in the model**
(`ETT.tex:1734–1743`): `M = E^{1,2} ∖ {0}` (the open set `puncture`), the inclusion a chart
isomorphism into the model `E^{1,2}`, and an open `U_p` (the cut diamond, with compact closure in
`E^{1,2}`, not relatively compact in `M`), causally convex in `M`, inside the chart, whose image is
not causally convex in the model. -/
theorem cutDiamond_separates :
    ChartIso (minkowski 2) (minkowski 2)
        ((OpenPartialHomeomorph.refl (Minkowski 2)).restrOpen _ puncture.isOpen) ∧
      IsOpen cutDiamond ∧ IsCompact (closure cutDiamond) ∧ cutDiamond ⊆ (puncture : Set _) ∧
      (minkowski 2).CausallyConvexIn cutDiamond puncture ∧
      ¬ (minkowski 2).CausallyConvexIn cutDiamond ⊤ := by
  have hopen : IsOpen cutDiamond :=
    ((minkowski 2).isOpen_lt_right ⊤ _).inter (((minkowski 2).isOpen_lt_left ⊤ _).inter isOpen_ne)
  have hsub : cutDiamond ⊆ Metric.closedBall (0 : Minkowski 2) 2 := fun x hx => by
    have ha := hx.1
    have hb := hx.2.1
    rw [minkowski_lt_top_iff] at ha hb
    simp only [sub_zero, zero_sub, norm_neg] at ha hb
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs]
    exact max_le (abs_le.2 ⟨by linarith [norm_nonneg x.2], by linarith [norm_nonneg x.2]⟩)
      (by linarith)
  exact ⟨SFATransfer.chartIso_restrOpen_refl (minkowski 2) puncture.isOpen, hopen,
    (isCompact_closedBall (0 : Minkowski 2) 2).of_isClosed_subset isClosed_closure
      (closure_minimal hsub Metric.isClosed_closedBall),
    fun x hx => hx.2.2, cutDiamond_causallyConvexIn_puncture, not_cutDiamond_causallyConvexIn_top⟩

end CutDiamond

end MeasuresManifolds

end Causal
