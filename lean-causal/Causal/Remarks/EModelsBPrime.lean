import Causal.Remarks.MassAModelsInstance
import Causal.Model.BPrimeEAlpha

/-!
# (b′) between the models of `E^{1,2}_{≥0}`, and the three corollaries at every `E_{≥0}`-manifold

Target `T-ett-e-models-bprime` (2026-11-21), with the scope of `T-ett-singular-instance` folded in.
Cited, **unmarked** (SCOPE): `cor:massA_causalite` — `ETT.tex:1396`, `cor:massA_cac` —
`ETT.tex:1408`, `cor:pushup_sing` — `ETT.tex:1419`, `defi:causal_Ealpha` — `ETT.tex:1335`.
An assembly: (b′) between every two models of `E_{≥0}` (`E₀ → E₀`: `Causal.Port.BPrimeE0`;
`E₀ ↔ E_κ`: `Causal.Remarks.MassAModelsInstance`; `E_κ → E_κ'`: `BPrimeEAlpha.hiso_family`), fed
with `hreg` (`MassAModelsInstance.hreg_massAModel`) into `massA_singular_dec25_models`: the three
corollaries at every `E_{≥0}`-manifold, no model hypothesis left.

> Every $\mass{\geq 0}$-manifold carries a natural absolutely minimal causality. (`ETT.tex:1396`)

> Every $\mass{\geq 0}$-manifold is causally arc-connected. (`ETT.tex:1408`)

> Every $\mass{\geq0}$-manifold has the push-up property. (`ETT.tex:1419–1420`)

> On any $\mass{\geq0}$-manifold $M$ there is then a unique causal structure inducing that
> of $\mass{\alpha}$ in every chart, and $I^\pm(x)$ is always an open --- possibly empty --- subset
> of $M$. For $\alpha>0$ the singular line is timelike, hence locally chronal. (`ETT.tex:1339–1341`)

## What is proved (no `sorry` in this file)

* **(b′) between every two models** (`hiso_massAModel`): every a.e. isomorphism chart
  `ψ : E_κ ⇀ E_κ'`, `κ, κ' ≥ 0` (`IsAEChart` under `massAModelSingularGX`), its source meeting a
  singular line or not, is a `ChartIso`. By cases: `hiso_row_none`, `hiso_column_none`,
  `chartIso_models_some_some` (`BPrimeEAlpha.hiso_family` over the family). The hypothesis of
  `hiso_massAModel_of_sing`: `hiso_massAModel_sing`, not vacuous
  (`hiso_massAModel_sing_nonvacuous`, at `E_π`).
* **The three corollaries at every `E_{≥0}`-manifold** (DEC-25: singular points in `X_A`-charts).
  Assembled: `massA_singular_all` (a natural causality, unique among absolutely minimal ones with an
  isomorphic chart at each point, causally arc-connected, push-up). One theorem per row:
  `massA_causalite_models`, `existsUnique_isAtlasCausalityDEC25` (`cor:massA_causalite`);
  `massA_cac_models` (`cor:massA_cac`); `pushup_sing_models` (`cor:pushup_sing`). Existence for
  every manifold at once: `forall_exists_massA_models` (`forall_exists_massA_models_iff.2`).
* **`defi:causal_Ealpha`'s `(G,X)` sentence at every `E_{≥0}`-manifold**: `causal_Ealpha_manifolds`
  (the unique natural causality, `I^±_U(x)` open); « possibly empty » at `E₀`
  (`causal_Ealpha_e0_Iminus_eq_empty`); « timelike, hence locally chronal », read through an
  `X_A`-chart into an `E_κ`, `κ > 0` (`causal_Ealpha_lt_singLine`); at a model, « unique » outright,
  with no minimality (`eq_massAModelCausality_of_chartIso`).
* **Sub-families**: at an `E₀`-manifold the natural causality over `E_{≥0}` is that over `E₀`
  alone, `BPrimeE0.existsUnique_causality_e0`'s (`isAtlasCausalityDEC25_iff_e0`); at an
  `E_{>0}`-manifold, `BPrimeEAlpha.existsUnique_causality_ealpha`'s
  (`isAtlasCausalityDEC25_iff_ealpha`).
* **Witnesses with a singular point, over the whole family**: every model
  (`isAtlasCausalityDEC25_model`, `massA_singular_model`), `E₀` (`massA_dec25_models_e0_sing`),
  `E_π` (`massA_dec25_models_epi`, uniqueness included).

## Hypothesis checklist

| paper | here |
|---|---|
| `E_{≥0}`-manifold | ⚠ reading (DEC-25): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, singular points in `X_A`-charts into the models (`hcov`); models' structures `massAModelSingularGX` (`E₀` read as in OQ-34/OQ-35) |
| `Isom(E^{1,2})` (l.1333, 1401) | ⚠ reading (OQ-82): `Flat.isom 2` = SO₀(1,2) ⋉ ℝ³ |
| « natural », « unique » (l.1396, 1339) | ⚠ reading (OQ-18): `IsAtlasCausalityDEC25`, unique among absolutely minimal causalities with an isomorphic chart at each point |
| « isomorphisms of the model spaces » (l.631–632) | ⚠ reading (OQ-64): `IsAEChart`; (b′) proved, not assumed |
| models cac, push-up, `hreg` | ✓ discharged (`massAModel_facts`, `hreg_massAModel`) |
| (b′) at the models | ✓ discharged (`hiso_massAModel`) |
| Baire, locally compact Hausdorff (l.1402) | ⚠ weakened: not used (OQ-10) |
| second countable Hausdorff (l.255) | ⚠ weakened: not used |

## SCOPE (disclosed)

* **Why unmarked.** OQ-18, OQ-82, OQ-34/OQ-35 are open readings, and OQ-64 as the reading of
  « isomorphism ». No hypothesis is added: (b′), which the existence half needs and the proof
  (l.1399–1406) does not check, is proved at every pair of models.
* **Uniqueness** is among absolutely minimal causalities (OQ-18); outright at the models.
* **Not here.** (i) O↑(1,2) ⋉ ℝ³ (OQ-82's other reading): the reflections are chart isomorphisms
  (`BPrimeE0.chartIso_conjE0`, `BPrimeEAlpha.chartIso_conjE`), the theorem for that group is not
  stated. (ii) BTZ_1's `prop:isom` in global form. (iii) `SingularFlatAxioms` at every
  `E_{≥0}`-manifold, which is `Causal.SFAManifolds.singularFlatAxioms`.
* **Instances.** `massAModelSingularGX` fires for a variable index only (kb/0154); sections at a
  fixed model use `EAlphaGX.singularGXFamily`, `EAlphaGX.singularGX`, `E0GX.singularGX`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace EModelsBPrime

open Set TopologicalSpace Topology Real MassAModelsInstance

/-! ### (b′) between every two models of `E_{≥0}` -/

section SomeSome

attribute [local instance] EAlphaGX.singularGXFamily

/-- **(b′) at `E_κ → E_κ'`, `κ, κ' > 0`, over the family**, every source:
`BPrimeEAlpha.hiso_family` read at `MassAModel (some κ)`, whose structure is
`EAlphaGX.singularGXFamily κ` by `rfl` (`massAModelSingularGX_some`). -/
theorem chartIso_models_some_some (κ κ' : {κ : ℝ // 0 < κ})
    {ψ : OpenPartialHomeomorph (MassAModel (some κ)) (MassAModel (some κ'))}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ChartIso (massAModelCausality (some κ)) (massAModelCausality (some κ')) ψ :=
  BPrimeEAlpha.hiso_family κ κ' ψ hψ

end SomeSome

/-- **(b′) between every two models of `E_{≥0}`**: every a.e. isomorphism chart
`ψ : E_κ ⇀ E_κ'`, `κ, κ' ≥ 0`, its source meeting a singular line or not, is an isomorphism of
topological spacetimes between open subsets of the models. This is the hypothesis `hiso` of
`massA_singular_dec25_models` over `massAModelSingularGX`, and of `forall_exists_massA_models_iff`;
by cases: from `E₀` (`hiso_row_none`), into `E₀` (`hiso_column_none`), between massive models
(`chartIso_models_some_some`). -/
theorem hiso_massAModel : ∀ o o' (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
    IsAEChart (Flat.isom 2) (Minkowski 2) ψ →
      ChartIso (massAModelCausality o) (massAModelCausality o') ψ
  | none, o', ψ, hψ => hiso_row_none o' ψ hψ
  | some κ, none, ψ, hψ => hiso_column_none (some κ) ψ hψ
  | some κ, some κ', _, hψ => chartIso_models_some_some κ κ' hψ

/-- **The hypothesis of `hiso_massAModel_of_sing`, proved**: every a.e. isomorphism chart between
two massive models whose source meets `Sing` is a chart isomorphism. -/
theorem hiso_massAModel_sing : ∀ o o' (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
    IsAEChart (Flat.isom 2) (Minkowski 2) ψ → o ≠ none → o' ≠ none →
      (ψ.source ∩ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o)).Nonempty →
        ChartIso (massAModelCausality o) (massAModelCausality o') ψ :=
  fun o o' ψ hψ _ _ _ => hiso_massAModel o o' ψ hψ

section NonVacuous

attribute [local instance] EAlphaGX.singularGXFamily

/-- **That case is not vacuous** (kb/0011): at `E_π` the identity rotation-translation is an a.e.
isomorphism chart whose source meets `Sing(E_π)` (`BPrimeEAlpha.nonvacuous`, `EAlphaGX.sing_eq`). -/
theorem hiso_massAModel_sing_nonvacuous :
    ∃ κ : {κ : ℝ // 0 < κ}, ∃ ψ : OpenPartialHomeomorph (MassAModel (some κ)) (MassAModel (some κ)),
      IsAEChart (Flat.isom 2) (Minkowski 2) ψ ∧
        (ψ.source ∩ Sing (Flat.isom 2) (Minkowski 2) (MassAModel (some κ))).Nonempty := by
  haveI := EAlphaGX.fact_pi_pos
  letI := EAlphaGX.singularGX π
  have hπ : π ≠ 2 * π := by linarith [pi_pos]
  obtain ⟨h1, h2, -⟩ := BPrimeEAlpha.nonvacuous 0 0
  refine ⟨⟨π, pi_pos⟩, (BPrimeEAlpha.rotShift (α := π) 0 0).toOpenPartialHomeomorph, h1, ?_⟩
  have hS : Sing (Flat.isom 2) (Minkowski 2) (Massive π) = singLine π := EAlphaGX.sing_eq hπ
  obtain ⟨p, hp, hps⟩ := h2
  exact ⟨p, hp, by rw [hS]; exact hps⟩

end NonVacuous

/-! ### The three corollaries at every `E_{≥0}`-manifold -/

section Manifolds

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]

/-- **`cor:massA_causalite`, `cor:massA_cac` and `cor:pushup_sing` at every `E_{≥0}`-manifold,
assembled, no model hypothesis left**: a singular `(Isom(E^{1,2}), E^{1,2})`-manifold whose singular
points lie in `X_A`-charts into the models `E_κ`, `κ ≥ 0`, carries a natural causality (every chart
of its maximal a.e. atlas and every `X_A`-chart an isomorphism; absolutely minimal), the only
absolutely minimal causality with an isomorphic chart at every point; it is causally arc-connected
and has the push-up property. `massA_singular_dec25_models` with `hreg_massAModel` and
`hiso_massAModel`. -/
theorem massA_singular_all
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) :
    ∃ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ∧
      (∀ C' : Causality M, C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality → C' = C) ∧
      C.CausallyArcConnected ∧ C.PushUp :=
  massA_singular_models hiso_massAModel hcov

/-- **`cor:massA_causalite` at every `E_{≥0}`-manifold**: « every `E_{≥0}`-manifold carries a
natural absolutely minimal causality », natural read as in OQ-18 (`IsAtlasCausalityDEC25`, unique
among absolutely minimal causalities with an isomorphic chart at each point). -/
theorem massA_causalite_models
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) :
    ∃ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ∧
      C.AbsolutelyMinimal ∧
      ∀ C' : Causality M, C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality → C' = C := by
  obtain ⟨C, hC, huniq, -⟩ := massA_singular_all hcov
  exact ⟨C, hC, hC.2.2, huniq⟩

/-- **`cor:massA_causalite`, unique existence**: every `E_{≥0}`-manifold has exactly one natural
causality (`IsAtlasCausalityDEC25.eq` for uniqueness). -/
theorem existsUnique_isAtlasCausalityDEC25
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) :
    ∃! C : Causality M,
      IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality := by
  obtain ⟨C, hC, -⟩ := massA_singular_all hcov
  exact ⟨C, hC, fun C' hC' => hC'.eq hcov hC |>.symm⟩

/-- **`cor:massA_cac` at every `E_{≥0}`-manifold**: « every `E_{≥0}`-manifold is causally
arc-connected »: its natural causality exists, and every natural causality is causally
arc-connected. -/
theorem massA_cac_models
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) :
    (∃ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) ∧
      ∀ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality →
        C.CausallyArcConnected := by
  obtain ⟨C, hC, -⟩ := massA_singular_all hcov
  exact ⟨⟨C, hC⟩, fun C' hC' => (massA_dec25_models hcov hC').1⟩

/-- **`cor:pushup_sing` at every `E_{≥0}`-manifold**: « every `E_{≥0}`-manifold has the push-up
property »: its natural causality exists, and every natural causality has push-up. -/
theorem pushup_sing_models
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) :
    (∃ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) ∧
      ∀ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality →
        C.PushUp := by
  obtain ⟨C, hC, -⟩ := massA_singular_all hcov
  exact ⟨⟨C, hC⟩, fun C' hC' => (massA_dec25_models hcov hC').2.1⟩

/-- **`defi:causal_Ealpha`'s `(G,X)` sentence (l.1339–1340) at every `E_{≥0}`-manifold**: « there
is then a unique causal structure inducing that of `E_α` in every chart, and `I^±(x)` is always an
open [...] subset of `M` », unique read as in OQ-18. -/
theorem causal_Ealpha_manifolds
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) :
    ∃ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ∧
      (∀ C' : Causality M, C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality → C' = C) ∧
      ∀ (U : Opens M) (x : M), IsOpen (C.Iplus U {x}) ∧ IsOpen (C.Iminus U {x}) := by
  obtain ⟨C, hC, huniq, -⟩ := massA_singular_all hcov
  exact ⟨C, hC, huniq, fun _ _ => ⟨C.isOpen_Iplus, C.isOpen_Iminus⟩⟩

section Chronal

attribute [local instance] EAlphaGX.singularGXFamily

/-- **« For `α > 0` the singular line is timelike, hence locally chronal » (`defi:causal_Ealpha`,
l.1341), at every `E_{≥0}`-manifold**: if an `X_A`-chart `e` into `E_κ`, `κ > 0`, sends `x` to the
singular line, then in every open `W ∋ x` the points `e⁻¹(s, apex)`, `s` near the time of `e x`, are
chronologically ordered by `s` for the natural causality (`singLine_locallyChronal` through the
chart isomorphism `e`). -/
theorem causal_Ealpha_lt_singLine {C : Causality M}
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {κ : {κ : ℝ // 0 < κ}} {e : OpenPartialHomeomorph M (Massive κ.1)}
    (he : IsAEChart (Flat.isom 2) (Minkowski 2) e) {x : M} (hx : x ∈ e.source)
    (hxs : e x ∈ singLine κ.1) {W : Opens M} (hxW : x ∈ W) :
    ∃ ε > 0, ∀ s ∈ Icc ((e x).1 - ε) ((e x).1 + ε), ∀ s' ∈ Icc ((e x).1 - ε) ((e x).1 + ε),
      s < s' → C.lt W (e.symm (s, Cone.apex)) (e.symm (s', Cone.apex)) := by
  haveI : Fact (0 < κ.1) := ⟨κ.2⟩
  have hiso : ChartIso C (massiveOf κ) e := hC.2.1 (some κ) e he
  set V : Opens M := W ⊓ chartSource e
  have hVs : V ≤ chartSource e := inf_le_right
  have hxV : x ∈ V := ⟨hxW, hx⟩
  have hex : ((e x).1, Cone.apex) ∈ chartImage e V := by
    have h := mem_chartImage_of_mem hx hxV
    rwa [show e x = ((e x).1, Cone.apex) from Prod.ext rfl hxs] at h
  obtain ⟨ε, hε, -, hlt⟩ := singLine_locallyChronal (W := chartImage e V) hex
  refine ⟨ε, hε, fun s hs s' hs' hss => ?_⟩
  have h := hlt s hs s' hs' hss
  obtain ⟨a, ⟨haS, haV⟩, hea⟩ := (massive κ.1).lt_mem_left h
  obtain ⟨b, ⟨hbS, hbV⟩, heb⟩ := (massive κ.1).lt_mem_right h
  rw [← hea, ← heb, e.left_inv haS, e.left_inv hbS]
  have hab : C.lt V a b := ((hiso V hVs a haV b hbV).2).2 (by rw [hea, heb]; exact h)
  exact C.lt_mono inf_le_left hab

end Chronal

section E0Sub

attribute [local instance] E0GX.singularGX

/-- **At an `E₀`-manifold the family and the model `E₀` alone give the same natural causality**:
for singular points in charts into `E₀`, a causality is natural over `E_{≥0}` iff it is natural over
`{E₀}` (the properties `BPrimeE0.existsUnique_causality_e0` gives its causality). -/
theorem isAtlasCausalityDEC25_iff_e0
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ e : OpenPartialHomeomorph M E0,
      IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source) (C : Causality M) :
    IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ↔
      (∀ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, ChartIso C (minkowski 2) e) ∧
      (∀ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e →
        ChartIso C E0.causality e) ∧
      C.AbsolutelyMinimal := by
  refine ⟨fun hC => ⟨hC.1, fun e he => hC.2.1 none e he, hC.2.2⟩, ?_⟩
  rintro ⟨hCX, hC0, hmin⟩
  obtain ⟨C₁, hC₁, huniq, -⟩ := massA_singular_all fun x hx => by
    obtain ⟨e, he, hxe⟩ := hcov x hx
    exact ⟨none, e, he, hxe⟩
  have hcover : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality := by
    intro x
    by_cases hx : x ∈ Reg (Flat.isom 2) (Minkowski 2) M
    · obtain ⟨e, he, hxe⟩ := mem_support.1 hx
      exact Or.inl ⟨e, he, hxe, hCX e he⟩
    · obtain ⟨e, he, hxe⟩ := hcov x hx
      exact Or.inr ⟨none, e, he, hxe, hC0 e he⟩
  rw [huniq C hmin hcover]
  exact hC₁

end E0Sub

section EAlphaSub

attribute [local instance] EAlphaGX.singularGXFamily

/-- **At an `E_{>0}`-manifold the family and the sub-family `E_{>0}` give the same natural
causality**: for singular points in charts into massive models, a causality is natural over
`E_{≥0}` iff it is natural over `{E_κ}_{κ > 0}` (the properties
`BPrimeEAlpha.existsUnique_causality_ealpha` gives its causality). -/
theorem isAtlasCausalityDEC25_iff_ealpha
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ κ : {κ : ℝ // 0 < κ},
      ∃ e : OpenPartialHomeomorph M (Massive κ.1), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) (C : Causality M) :
    IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ↔
      (∀ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, ChartIso C (minkowski 2) e) ∧
      (∀ (κ : {κ : ℝ // 0 < κ}) (e : OpenPartialHomeomorph M (Massive κ.1)),
        IsAEChart (Flat.isom 2) (Minkowski 2) e → ChartIso C (massiveOf κ) e) ∧
      C.AbsolutelyMinimal := by
  refine ⟨fun hC => ⟨hC.1, fun κ e he => hC.2.1 (some κ) e he, hC.2.2⟩, ?_⟩
  rintro ⟨hCX, hCκ, hmin⟩
  obtain ⟨C₁, hC₁, huniq, -⟩ := massA_singular_all fun x hx => by
    obtain ⟨κ, e, he, hxe⟩ := hcov x hx
    exact ⟨some κ, e, he, hxe⟩
  have hcover : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality := by
    intro x
    by_cases hx : x ∈ Reg (Flat.isom 2) (Minkowski 2) M
    · obtain ⟨e, he, hxe⟩ := mem_support.1 hx
      exact Or.inl ⟨e, he, hxe, hCX e he⟩
    · obtain ⟨κ, e, he, hxe⟩ := hcov x hx
      exact Or.inr ⟨some κ, e, he, hxe, hCκ κ e he⟩
  rw [huniq C hmin hcover]
  exact hC₁

end EAlphaSub

end Manifolds

/-- **The existence half of `cor:massA_causalite` for every `E_{≥0}`-manifold at once**, the right
side of `forall_exists_massA_models_iff` being `hiso_massAModel`. -/
theorem forall_exists_massA_models :
    ∀ (N : Type) [TopologicalSpace N] [SingularGXStructure (Flat.isom 2) (Minkowski 2) N],
      (∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) N, ∃ o,
        ∃ e : OpenPartialHomeomorph N (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
          x ∈ e.source) →
      ∃ C : Causality N, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality :=
  forall_exists_massA_models_iff.2 hiso_massAModel

/-! ### Every model, and witnesses with a singular point -/

/-- **The causality of every model is natural over the whole family**: (b′) holds from every model
(`isAtlasCausalityDEC25_model_iff`). -/
theorem isAtlasCausalityDEC25_model (o : Option {κ : ℝ // 0 < κ}) :
    IsAtlasCausalityDEC25 (Flat.isom 2) (massAModelCausality o) (minkowski 2)
      massAModelCausality :=
  (isAtlasCausalityDEC25_model_iff o).2 (hiso_massAModel o)

/-- **Every model `E_κ`, `κ ≥ 0`, is an `E_{≥0}`-manifold to which the corollaries apply, its own
causality being the one they give**: its singular points lie in its identity `X_A`-chart, its
causality is natural, causally arc-connected, push-up, and the only absolutely minimal causality
with an isomorphic chart at each point. A singular point at every model but `E_{2π}`
(`sing_massAModel_nonempty_iff`). -/
theorem massA_singular_model (o : Option {κ : ℝ // 0 < κ}) :
    (∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o), ∃ o',
      ∃ e : OpenPartialHomeomorph (MassAModel o) (MassAModel o'),
        IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source) ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) (massAModelCausality o) (minkowski 2)
        massAModelCausality ∧
      (massAModelCausality o).CausallyArcConnected ∧ (massAModelCausality o).PushUp ∧
      ∀ C' : Causality (MassAModel o), C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality →
          C' = massAModelCausality o := by
  have hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o), ∃ o',
      ∃ e : OpenPartialHomeomorph (MassAModel o) (MassAModel o'),
        IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source := fun x _ =>
    ⟨o, OpenPartialHomeomorph.refl _, isAEChart_refl, mem_univ x⟩
  exact ⟨hcov, isAtlasCausalityDEC25_model o,
    massA_dec25_models hcov (isAtlasCausalityDEC25_model o)⟩

/-- **At a model, « unique » holds outright** (`defi:causal_Ealpha`, l.1339): a causality on
`E_κ`, `κ ≥ 0`, for which every `X_A`-chart is an isomorphism, absolutely minimal or not, is the
model's own, the identity being such a chart. -/
theorem eq_massAModelCausality_of_chartIso (o : Option {κ : ℝ // 0 < κ})
    {C' : Causality (MassAModel o)}
    (h : ∀ o' (e : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
      IsAEChart (Flat.isom 2) (Minkowski 2) e → ChartIso C' (massAModelCausality o') e) :
    C' = massAModelCausality o :=
  eq_of_chartIso_refl (h o _ isAEChart_refl)

section EPi

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- **Witness with a singular point over the whole family: `E_π`**, with `EAlphaGX.singularGX π`
and `massive π`. Its singular locus is the line, nonempty; its singular points lie in an
`X_A`-chart (the identity, into the model `E_π`); `massive π` is its natural causality over all of
`E_{≥0}`, every a.e. isomorphism chart from `E_π` into every model, through the line included,
being an isomorphism (`hiso_massAModel`); it is causally arc-connected, has push-up, and is the
only absolutely minimal causality with an isomorphic chart at each point. So the three corollaries
apply at `E_π`, and the causality they give there is `massive π`. -/
theorem massA_dec25_models_epi :
    (Sing (Flat.isom 2) (Minkowski 2) (Massive π)).Nonempty ∧
      (∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) (Massive π), ∃ o,
        ∃ e : OpenPartialHomeomorph (Massive π) (MassAModel o),
          IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source) ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) (massive π) (minkowski 2) massAModelCausality ∧
      (massive π).CausallyArcConnected ∧ (massive π).PushUp ∧
      ∀ C' : Causality (Massive π), C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality →
          C' = massive π := by
  have hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) (Massive π), ∃ o,
      ∃ e : OpenPartialHomeomorph (Massive π) (MassAModel o),
        IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source := fun x _ =>
    ⟨some ⟨π, pi_pos⟩, OpenPartialHomeomorph.refl (Massive π), isAEChart_refl, mem_univ x⟩
  have hC : IsAtlasCausalityDEC25 (Flat.isom 2) (massive π) (minkowski 2) massAModelCausality :=
    isAtlasCausalityDEC25_model (some ⟨π, pi_pos⟩)
  exact ⟨EAlphaGX.sing_nonempty (by linarith [pi_pos] : π < 2 * π).ne, hcov, hC,
    massA_dec25_models hcov hC⟩

end EPi

section E0

attribute [local instance] E0GX.singularGX

/-- **Witness with a singular point over the whole family: `E₀`**, with `E0GX.singularGX` and
`E0.causality`, in the shape of `massA_dec25_models_epi`: its singular locus is the axis, nonempty,
covered by the identity `X_A`-chart, and `E0.causality` is its natural causality over all of
`E_{≥0}` (`massA_dec25_models_e0`), causally arc-connected, push-up, unique. -/
theorem massA_dec25_models_e0_sing :
    (Sing (Flat.isom 2) (Minkowski 2) E0).Nonempty ∧
      (∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) E0, ∃ o,
        ∃ e : OpenPartialHomeomorph E0 (MassAModel o),
          IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source) ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      E0.causality.CausallyArcConnected ∧ E0.causality.PushUp ∧
      ∀ C' : Causality E0, C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality →
          C' = E0.causality :=
  ⟨E0GX.sing_nonempty, fun x _ => ⟨none, OpenPartialHomeomorph.refl E0, isAEChart_refl, mem_univ x⟩,
    massA_dec25_models_e0⟩

/-- **« possibly empty » (`defi:causal_Ealpha`, l.1340), witnessed**: at `E₀`, whose natural
causality over the whole family is `E0.causality`, `I⁻_U(p) = ∅` at every singular point `p` and
every open `U` (`E0.Iminus_axis`, `defi:causal_E0`). -/
theorem causal_Ealpha_e0_Iminus_eq_empty :
    IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      ∃ p, p ∈ Sing (Flat.isom 2) (Minkowski 2) E0 ∧
        ∀ U : Opens E0, E0.causality.Iminus U {p} = ∅ := by
  obtain ⟨p, hp⟩ := E0GX.sing_nonempty
  refine ⟨isAtlasCausalityDEC25_e0, p, hp, fun U => ?_⟩
  rw [E0GX.sing_eq] at hp
  exact E0.Iminus_axis hp U

end E0

end EModelsBPrime

end Causal
