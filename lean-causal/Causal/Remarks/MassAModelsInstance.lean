import Causal.Remarks.MassADEC25
import Causal.Port.E0GXStructure
import Causal.Port.BPrimeE0
import Causal.Model.EAlphaGX

/-!
# The models of `E^{1,2}_{≥0}` as one family of singular `(Isom(E^{1,2}), E^{1,2})`-manifolds

Target `T-ett-massa-models-instance` (2026-11-21). Cited, **unmarked** (SCOPE):
`cor:massA_causalite` — `ETT.tex:1396`, `cor:massA_cac` — `ETT.tex:1408`,
`cor:pushup_sing` — `ETT.tex:1419`. The singular structures of `E₀` and of the `E_κ`, `κ > 0`,
packaged as the instance `∀ o, SingularGXStructure (Flat.isom 2) (Minkowski 2) (MassAModel o)`
that the four model-level theorems of `Causal.Remarks.MassADEC25` take; `hreg` at every model;
(b′) wherever no line of an `E_κ` is involved; witnesses with a singular point.

> Every $\mass{\geq 0}$-manifold carries a natural absolutely minimal causality. (`ETT.tex:1396`)

> Every $\mass{\geq 0}$-manifold is causally arc-connected. (`ETT.tex:1408`)

> Every $\mass{\geq0}$-manifold has the push-up property. (`ETT.tex:1419`)

> For $\alpha=0$ the singular line is lightlike: locally causal, but not locally chronal. More
> precisely [...], for a singular point $p\in \sing(\mass{0})$, $I^-(p)=\emptyset$ and
> $J^-(p)=\{\r=0,~\tau\leq \tau(p)\}$ (`ETT.tex:1344–1348`)

## What is proved (no `sorry` in this file)

* **The family** `massAModelSingularGX` (instance, by cases on `o`): `E0GX.singularGX` at `E₀` and
  `EAlphaGX.singularGXFamily κ` at `E_κ`, both by `rfl`. **`hreg`**: `hreg_massAModel`. Every
  model but `E_{2π}` has a singular point: `sing_massAModel_nonempty_iff`.
* **(b′) at the models.** Regular sources, every pair: `chartIso_models_of_subset_reg`; from or
  into `E_{2π}`: `chartIso_models_of_sing_eq_empty_left`, `_right`; `E₀ → E₀`:
  `chartIso_models_none_none`. **`E₀ ↔ E_κ`, every source**: no a.e. isomorphism chart
  `E_κ ⇀ E₀` reaches the axis (`notMem_axis_of_isAEChart`, by causality: `J⁻` of a BTZ point is on
  the axis, every point of `E_κ` is a limit of regular points of one causal future, `J⁺` is closed
  in `E₀`), so such charts have regular sources (`source_subset_reg_of_isAEChart_e0_massive`,
  `_massive_e0`): `chartIso_models_none_some`, `_some_none`, `hiso_row_none`, `hiso_column_none`.
* **What (b′) owes**: only `E_κ ⇀ E_κ'` at sources meeting the line (`hiso_massAModel_of_sing`).
  Existence at every manifold ⇔ (b′) (`forall_exists_massA_models_iff`, `hreg` discharged) ⇔
  that case alone (`forall_exists_massA_models_iff_sing`); conditional: `massA_singular_models`.
* **Each model as a manifold**: `isoChartsCoverDEC25_model`, `massA_dec25_models_model` (cac,
  push-up); its causality is natural over the family iff (b′) holds from it
  (`isAtlasCausalityDEC25_model_iff`): at `E₀` (`isAtlasCausalityDEC25_e0`), at `E_{2π}`.
* **Witnesses with a singular point.** `E₀`: `e0_witness` (local form), `massA_dec25_models_e0`
  (`massA_dec25_models`, uniqueness included, over the whole family), `e0_unique_witness` (one
  model). `E_π`: `epi_witness` (local form). `E^{1,2}` over the whole family:
  `isAtlasCausalityDEC25_minkowski_models`, `massA_dec25_models_minkowski`.
* **`E₀`-manifolds, the whole family**: `massA_dec25_e0_manifolds`: singular points in charts into
  `E₀` give a natural causality over all of `E_{≥0}`, unique, cac, push-up. No hypothesis left.

## Hypothesis checklist

| paper | here |
|---|---|
| `E_{≥0}`-manifold | ⚠ reading (DEC-25), as in `Causal.Remarks.MassADEC25`; the models' structures now concrete (`E₀` read as in OQ-34/OQ-35); `massA_dec25_e0_manifolds`: singular points in charts into `E₀` |
| `Isom(E^{1,2})` | ⚠ reading: `Flat.isom 2` = SO₀(1,2) ⋉ ℝ³ (OQ-82) |
| « natural » | ⚠ reading (OQ-18): `IsAtlasCausalityDEC25`, unique among absolutely minimal causalities |
| models cac, push-up, `hreg` | ✓ discharged (`massAModel_facts`, `hreg_massAModel`) |
| (none) | ⚠ strengthened, existence at a general manifold only: (b′) between massive models at the line (OQ-64) |
| Baire, locally compact Hausdorff (l.1402) | ⚠ weakened: not used (OQ-10) |

## SCOPE (disclosed)

* **Why unmarked.** OQ-18, OQ-82, OQ-34/OQ-35 (readings). The existence half at a general
  `E_{≥0}`-manifold, which rested on (b′) between `E_κ`, `E_κ'` at sources meeting the line, is
  proved in `Causal.Remarks.EModelsBPrime` (`massA_singular_all`, from
  `Causal.Model.BPrimeEAlpha`, `hiso_family`). For `E₀`-manifolds nothing was left.
* **The instance** fires for a variable `o` only: at `none` or `some κ` the type `MassAModel o`
  reduces to `E0` or `Massive κ.1` before instance search, so sections at a fixed model use the
  local instances `E0GX.singularGX`, `EAlphaGX.singularGX`, `EAlphaGX.singularGXFamily`, all
  definitionally the family's values.
* **`E_π`**: local form here. Its causality is natural over the family iff (b′) holds from `E_π`
  (`isAtlasCausalityDEC25_model_iff`); that is proved through the line in
  `Causal.Model.BPrimeEAlpha`, and `Causal.Remarks.EModelsBPrime` states the models' rows at `E_π`
  (`massA_dec25_models_epi`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace MassAModelsInstance

open Set TopologicalSpace Topology Real

/-! ### The family -/

/-- **The singular `(Isom(E^{1,2}), E^{1,2})`-structures of the models of `E_{≥0}`**, by cases on
`o`: `E0GX.singularGX` at `E₀`, `EAlphaGX.singularGXFamily κ` at `E_κ`. -/
noncomputable instance massAModelSingularGX :
    ∀ o, SingularGXStructure (Flat.isom 2) (Minkowski 2) (MassAModel o)
  | none => E0GX.singularGX
  | some κ => EAlphaGX.singularGXFamily κ

/-- At `E₀` the family is `E0GX.singularGX` **by `rfl`**: the hypothesis `h0` of
`BPrimeE0.hiso_massAModel_none`. -/
theorem massAModelSingularGX_none : massAModelSingularGX none = E0GX.singularGX := rfl

/-- At `E_κ` the family is `EAlphaGX.singularGXFamily κ`, by `rfl`. -/
theorem massAModelSingularGX_some (κ : {κ : ℝ // 0 < κ}) :
    massAModelSingularGX (some κ) = EAlphaGX.singularGXFamily κ := rfl

/-- `E_{2π}` as an index of the family. -/
noncomputable abbrev twoPi : {κ : ℝ // 0 < κ} := ⟨2 * π, two_pi_pos⟩

/-! ### `hreg` at every model -/

/-- **`hreg` at every model of `E_{≥0}`**, in the form of `massA_singular_dec25_models` and
`forall_exists_massA_dec25_models_iff`: every chart of the maximal a.e. atlas of `E_κ`, `κ ≥ 0`, is
a chart isomorphism onto `E^{1,2}` (`E0GX.chartIso_of_mem_aeAtlas`, `EAlphaGX.hreg_family`). -/
theorem hreg_massAModel : ∀ o, ∀ r ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (MassAModel o),
    ChartIso (massAModelCausality o) (minkowski 2) r
  | none => E0GX.chartIso_of_mem_aeAtlas
  | some κ => EAlphaGX.hreg_family κ

section TwoPi

attribute [local instance] EAlphaGX.singularGX

/-- **Every model but `E_{2π}` has a singular point**: `Sing(E₀)` is the axis, `Sing(E_κ)` the
line for `κ ≠ 2π`, and `Sing(E_{2π}) = ∅` (DEC-74). -/
theorem sing_massAModel_nonempty_iff (o : Option {κ : ℝ // 0 < κ}) :
    (Sing (Flat.isom 2) (Minkowski 2) (MassAModel o)).Nonempty ↔ o ≠ some twoPi := by
  rcases o with _ | ⟨κ, hκ⟩
  · exact ⟨fun _ h => Option.some_ne_none _ h.symm, fun _ => E0GX.sing_nonempty⟩
  · constructor
    · rintro hne heq
      have hκ2 : κ = 2 * π := congrArg Subtype.val (Option.some.inj heq)
      subst hκ2
      have h3 : ¬ (Sing (Flat.isom 2) (Minkowski 2) (Massive (2 * π))).Nonempty := by
        rw [EAlphaGX.sing_eq_empty_two_pi]; exact not_nonempty_empty
      exact h3 hne
    · intro hne
      have hκ2 : κ ≠ 2 * π := fun h => hne (by subst h; rfl)
      exact @EAlphaGX.sing_nonempty κ ⟨hκ⟩ hκ2

end TwoPi

/-! ### (b′) at the models, where `hreg` gives it -/

/-- **(b′) at regular sources, between any two models of `E_{≥0}`**, `E₀ ↔ E_κ` included: an a.e.
isomorphism chart `E_κ ⇀ E_κ'`, `κ, κ' ≥ 0`, whose source is regular is a chart isomorphism
(`chartIso_model_of_subset_reg`, from `hreg_massAModel`). -/
theorem chartIso_models_of_subset_reg {o o' : Option {κ : ℝ // 0 < κ}}
    {ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ)
    (hsub : ψ.source ⊆ Reg (Flat.isom 2) (Minkowski 2) (MassAModel o)) :
    ChartIso (massAModelCausality o) (massAModelCausality o') ψ :=
  chartIso_model_of_subset_reg (Xα := MassAModel) (minkowski 2) massAModelCausality
    Flat.isom_strongMorphism (fun o => (massAModel_facts o).1) hreg_massAModel hψ hsub

/-- (b′) from a model without singular point (`E_{2π}`), every source. -/
theorem chartIso_models_of_sing_eq_empty_left {o o' : Option {κ : ℝ // 0 < κ}}
    (h : Sing (Flat.isom 2) (Minkowski 2) (MassAModel o) = ∅)
    {ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ChartIso (massAModelCausality o) (massAModelCausality o') ψ :=
  chartIso_models_of_subset_reg hψ fun x _ => by
    by_contra hx
    have hxs : x ∈ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o) := hx
    rw [h] at hxs
    exact hxs

/-- (b′) into a model without singular point (`E_{2π}`), every source: an a.e. isomorphism chart
maps singular points to singular points (`IsAEChart.mem_reg_iff`), so its source is regular. -/
theorem chartIso_models_of_sing_eq_empty_right {o o' : Option {κ : ℝ // 0 < κ}}
    (h : Sing (Flat.isom 2) (Minkowski 2) (MassAModel o') = ∅)
    {ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ChartIso (massAModelCausality o) (massAModelCausality o') ψ :=
  chartIso_models_of_subset_reg hψ fun x hx => by
    refine (hψ.mem_reg_iff hx).2 ?_
    by_contra hy
    have hys : ψ x ∈ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o') := hy
    rw [h] at hys
    exact hys

section NoneNone

attribute [local instance] E0GX.singularGX

/-- **(b′) at `E₀ → E₀`**, every source (`BPrimeE0.hiso_massAModel_none` with `h0 := rfl`). -/
theorem chartIso_models_none_none {ψ : OpenPartialHomeomorph (MassAModel none) (MassAModel none)}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ChartIso (massAModelCausality none) (massAModelCausality none) ψ :=
  BPrimeE0.hiso_massAModel_none (inst := massAModelSingularGX) rfl ψ hψ

end NoneNone

/-! ### (b′) between `E₀` and the `E_κ`: no a.e. isomorphism chart joins `E₀`'s axis to an `E_κ` -/

/-- The restriction of an a.e. isomorphism chart to an open set is one. -/
theorem isAEChart_restrOpen {G : Type*} {X : Type*} [TopologicalSpace X] [Group G]
    [MulAction G X] {M : Type*} [TopologicalSpace M] [SingularGXStructure G X M] {N : Type*}
    [TopologicalSpace N] [SingularGXStructure G X N] {e : OpenPartialHomeomorph M N}
    (he : IsAEChart G X e) {s : Set M} (hs : IsOpen s) : IsAEChart G X (e.restrOpen s hs) :=
  ⟨he.regularOn.mono (inter_subset_inter_left _ inter_subset_left)
      ((e.restrOpen s hs).open_source.inter (isOpen_reg G X M)),
    he.regularOn_symm.mono (inter_subset_inter_left _ inter_subset_left)
      ((e.restrOpen s hs).open_target.inter (isOpen_reg G X N))⟩

section CrossType

attribute [local instance] E0GX.singularGX EAlphaGX.singularGXFamily

/-- **No a.e. isomorphism chart `E_κ ⇀ E₀`, `κ > 0`, sends a point to the axis of `E₀`.** If
`φ q` were a BTZ point, `q` would be singular, so on the line of `E_κ`. The regular points
`g(u) = (τ(q) − u, (u/2)·e^{i0})`, `0 < u ≤ ε`, tend to `q` and satisfy `g(ε) ≤ g(u)` along a radial
curve inside the regular part of the source, where `φ` is a chart isomorphism
(`chartIso_of_isAEChart_of_subset_reg`). So `φ(g(ε)) ≤ φ(g(u))` in `E₀`, and since `J⁺` is closed in
`E₀` (`E0.isClosed_Jplus`), `φ(g(ε)) ≤ φ q`: a regular point in the causal past of a BTZ point,
against `J⁻(p) = {r = 0, τ ≤ τ(p)}` (`E0.le_axis_iff'`, `defi:causal_E0`). -/
theorem notMem_axis_of_isAEChart {κ : {κ : ℝ // 0 < κ}}
    {φ : OpenPartialHomeomorph (Massive κ.1) E0} (hφ : IsAEChart (Flat.isom 2) (Minkowski 2) φ)
    {q : Massive κ.1} (hq : q ∈ φ.source) : φ q ∉ E0.axis := by
  intro hpa
  have hRκ : regPart κ.1 ⊆ Reg (Flat.isom 2) (Minkowski 2) (Massive κ.1) :=
    @EAlphaGX.regPart_subset_reg κ.1 ⟨κ.2⟩
  -- `q` is a point of the singular line
  have hqs : q.2 = Cone.apex := by
    by_contra hne
    have h1 := (hφ.mem_reg_iff hq).1 (hRκ hne)
    rw [E0GX.reg_eq] at h1
    exact h1 hpa
  -- the restriction of `φ` to the regular part of its source is a chart isomorphism
  have hRo : IsOpen (regPart κ.1) := EAlphaGX.isClosed_singLine.isOpen_compl
  have hφW : IsAEChart (Flat.isom 2) (Minkowski 2) (φ.restrOpen (regPart κ.1) hRo) :=
    isAEChart_restrOpen hφ hRo
  have hiso : ChartIso (massiveOf κ) E0.causality (φ.restrOpen (regPart κ.1) hRo) :=
    chartIso_of_isAEChart_of_subset_reg Flat.isom_strongMorphism E0.causallyArcConnected
      E0GX.chartIso_of_mem_aeAtlas (EAlphaGX.hreg_family κ) hφW
      ((@massive_causallyArcConnected κ.1 ⟨κ.2⟩).absolutelyMinimalOn_all _)
      (fun x hx => hRκ hx.2)
  -- the radial curve `u ↦ (τ(q) - u, (u/2) e^{i0})`, chronological towards `q`
  let g : ℝ → Massive κ.1 := fun u => (q.1 - u, Cone.polar (u / 2, 0))
  have hg : Continuous g := by
    refine continuous_const.sub continuous_id |>.prodMk (Cone.continuous_polar.comp ?_)
    exact (continuous_id.div_const 2).prodMk continuous_const
  have hrad : ∀ u, 0 ≤ u → Cone.rad (Cone.polar ((u / 2, 0) : ℝ × AddCircle κ.1)) = u / 2 :=
    fun u hu => by
      rw [Cone.polar, Cone.rad_mk, ConePoint.of_r (by linarith)]
  have hg0 : g 0 = q := by
    refine Prod.ext (by simp [g]) ?_
    show Cone.polar ((0 / 2, 0) : ℝ × AddCircle κ.1) = q.2
    rw [hqs, ← Cone.rad_eq_zero, hrad 0 le_rfl, zero_div]
  have hgreg : ∀ u, 0 < u → g u ∈ regPart κ.1 := fun u hu h => by
    have h' : Cone.polar ((u / 2, 0) : ℝ × AddCircle κ.1) = Cone.apex := h
    rw [← Cone.rad_eq_zero, hrad u hu.le] at h'
    linarith
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ u, |u| < ε → g u ∈ φ.source := by
    have hn : g ⁻¹' φ.source ∈ 𝓝 (0 : ℝ) :=
      hg.continuousAt.preimage_mem_nhds (by rw [hg0]; exact φ.open_source.mem_nhds hq)
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hn
    exact ⟨ε, hε, fun u hu => hb (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hu)⟩
  have hε2 : 0 < ε / 2 := by linarith
  have hmemW : ∀ u, 0 < u → u ≤ ε / 2 → g u ∈ (φ.restrOpen (regPart κ.1) hRo).source :=
    fun u hu hu' => ⟨hball u (by rw [abs_of_pos hu]; linarith), hgreg u hu⟩
  -- along the curve, `g (ε/2) ≤ g s` inside the regular part of the source
  have hle : ∀ s ∈ Ioo (0 : ℝ) (ε / 2),
      (massiveOf κ).le (chartSource (φ.restrOpen (regPart κ.1) hRo)) (g (ε / 2)) (g s) := by
    intro s hs
    refine ⟨show q.1 - ε / 2 ≤ q.1 - s by linarith [hs.2],
      fun τ => Cone.polar (((q.1 - τ) / 2, 0) : ℝ × AddCircle κ.1), ?_, ?_, ?_, ?_⟩
    · show Cone.polar (((q.1 - (q.1 - ε / 2)) / 2, 0) : ℝ × AddCircle κ.1) =
        Cone.polar ((ε / 2 / 2, 0) : ℝ × AddCircle κ.1)
      congr 2; ring
    · show Cone.polar (((q.1 - (q.1 - s)) / 2, 0) : ℝ × AddCircle κ.1) =
        Cone.polar ((s / 2, 0) : ℝ × AddCircle κ.1)
      congr 2; ring
    · intro τ hτ τ' hτ'
      have h2 : τ ≤ q.1 - s := hτ.2
      have h2' : τ' ≤ q.1 - s := hτ'.2
      have hτ0 : 0 ≤ (q.1 - τ) / 2 := by linarith [hs.1]
      have hτ0' : 0 ≤ (q.1 - τ') / 2 := by linarith [hs.1]
      show dist (Cone.mk (ConePoint.of ((q.1 - τ) / 2) 0))
        (Cone.mk (ConePoint.of ((q.1 - τ') / 2) 0)) ≤ 1 * |τ - τ'|
      rw [Cone.dist_mk, Cone.dist_of_same_dir hτ0 hτ0', one_mul,
        show (q.1 - τ) / 2 - (q.1 - τ') / 2 = (τ' - τ) / 2 by ring, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
      linarith [abs_nonneg (τ - τ')]
    · intro τ hτ
      have h1 : q.1 - ε / 2 ≤ τ := hτ.1
      have h2 : τ ≤ q.1 - s := hτ.2
      have he : ((τ, Cone.polar (((q.1 - τ) / 2, 0) : ℝ × AddCircle κ.1)) : Massive κ.1) =
          g (q.1 - τ) := Prod.ext (by simp [g]) rfl
      rw [he]
      exact hmemW _ (by linarith [hs.1]) (by linarith)
  have hJ : ∀ s ∈ Ioo (0 : ℝ) (ε / 2), φ (g s) ∈ E0.causality.Jplus ⊤ {φ (g (ε / 2))} := by
    intro s hs
    rw [Precausality.mem_Jplus_singleton]
    have h1 := ((hiso (chartSource (φ.restrOpen (regPart κ.1) hRo)) le_rfl (g (ε / 2))
      (hmemW _ hε2 le_rfl) (g s) (hmemW _ hs.1 hs.2.le)).1).1 (hle s hs)
    exact E0.causality.le_mono le_top h1
  have htend : Filter.Tendsto (fun s => φ (g s)) (𝓝[>] (0 : ℝ)) (𝓝 (φ q)) := by
    have h1 : Filter.Tendsto g (𝓝 0) (𝓝 q) := by rw [← hg0]; exact hg.tendsto 0
    exact ((φ.continuousAt hq).tendsto.comp h1).mono_left nhdsWithin_le_nhds
  have hmem := (E0.isClosed_Jplus (φ (g (ε / 2)))).mem_of_tendsto htend
    (Filter.mem_of_superset (Ioo_mem_nhdsGT hε2) hJ)
  rw [Precausality.mem_Jplus_singleton, E0.le_top_iff, E0.le_axis_iff' hpa] at hmem
  -- but `g (ε/2)` is regular, so its image is off the axis
  have hr := (hφ.mem_reg_iff (hmemW _ hε2 le_rfl).1).1 (hRκ (hgreg _ hε2))
  rw [E0GX.reg_eq] at hr
  exact hr hmem.1

/-- Every a.e. isomorphism chart `E_κ ⇀ E₀` has a regular source. -/
theorem source_subset_reg_of_isAEChart_massive_e0 {κ : {κ : ℝ // 0 < κ}}
    {φ : OpenPartialHomeomorph (Massive κ.1) E0} (hφ : IsAEChart (Flat.isom 2) (Minkowski 2) φ) :
    φ.source ⊆ Reg (Flat.isom 2) (Minkowski 2) (Massive κ.1) := fun q hq =>
  (hφ.mem_reg_iff hq).2 (by rw [E0GX.reg_eq]; exact notMem_axis_of_isAEChart hφ hq)

/-- **Every a.e. isomorphism chart `E₀ ⇀ E_κ` has a regular source**: no such chart meets the
axis of `E₀`. -/
theorem source_subset_reg_of_isAEChart_e0_massive {κ : {κ : ℝ // 0 < κ}}
    {ψ : OpenPartialHomeomorph E0 (Massive κ.1)} (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ψ.source ⊆ Reg (Flat.isom 2) (Minkowski 2) E0 := fun p hp => by
  have h := notMem_axis_of_isAEChart hψ.symm (ψ.map_source hp)
  rw [ψ.left_inv hp] at h
  rw [E0GX.reg_eq]
  exact h

/-- **(b′) at `E₀ → E_κ`, every source.** -/
theorem chartIso_models_none_some (κ : {κ : ℝ // 0 < κ})
    {ψ : OpenPartialHomeomorph (MassAModel none) (MassAModel (some κ))}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ChartIso (massAModelCausality none) (massAModelCausality (some κ)) ψ :=
  chartIso_models_of_subset_reg hψ (source_subset_reg_of_isAEChart_e0_massive hψ)

/-- **(b′) at `E_κ → E₀`, every source.** -/
theorem chartIso_models_some_none (κ : {κ : ℝ // 0 < κ})
    {ψ : OpenPartialHomeomorph (MassAModel (some κ)) (MassAModel none)}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ChartIso (massAModelCausality (some κ)) (massAModelCausality none) ψ :=
  chartIso_models_of_subset_reg hψ (source_subset_reg_of_isAEChart_massive_e0 hψ)

end CrossType

section RowNone

attribute [local instance] E0GX.singularGX

/-- **(b′) from `E₀`, to every model.** -/
theorem hiso_row_none : ∀ o' (ψ : OpenPartialHomeomorph (MassAModel none) (MassAModel o')),
    IsAEChart (Flat.isom 2) (Minkowski 2) ψ →
      ChartIso (massAModelCausality none) (massAModelCausality o') ψ
  | none, _, hψ => chartIso_models_none_none hψ
  | some κ, _, hψ => chartIso_models_none_some κ hψ

/-- **(b′) into `E₀`, from every model.** -/
theorem hiso_column_none : ∀ o (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel none)),
    IsAEChart (Flat.isom 2) (Minkowski 2) ψ →
      ChartIso (massAModelCausality o) (massAModelCausality none) ψ
  | none, _, hψ => chartIso_models_none_none hψ
  | some κ, _, hψ => chartIso_models_some_none κ hψ

end RowNone

/-- **What (b′) over the family still owes**: it holds between every two models of `E_{≥0}` as soon
as it holds between two massive models `E_κ ⇀ E_κ'`, `κ, κ' > 0`, at sources meeting the singular
line. Every other case is proved here: regular sources, `E₀ → E₀`, `E₀ ↔ E_κ`. -/
theorem hiso_massAModel_of_sing
    (h : ∀ o o' (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
      IsAEChart (Flat.isom 2) (Minkowski 2) ψ → o ≠ none → o' ≠ none →
        (ψ.source ∩ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o)).Nonempty →
          ChartIso (massAModelCausality o) (massAModelCausality o') ψ) :
    ∀ o o' (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
      IsAEChart (Flat.isom 2) (Minkowski 2) ψ →
        ChartIso (massAModelCausality o) (massAModelCausality o') ψ := by
  intro o o' ψ hψ
  by_cases ho : o = none
  · subst ho
    exact hiso_row_none o' ψ hψ
  by_cases ho' : o' = none
  · subst ho'
    exact hiso_column_none o ψ hψ
  by_cases hs : (ψ.source ∩ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o)).Nonempty
  · exact h o o' ψ hψ ho ho' hs
  · exact chartIso_models_of_subset_reg hψ fun x hx => by
      by_contra hxr
      exact hs ⟨x, hx, hxr⟩

/-! ### Existence over the family, with `hreg` discharged -/

/-- **The existence half of `cor:massA_causalite` over the family is exactly (b′) at the models**,
`hreg` discharged (`forall_exists_massA_dec25_models_iff` with `hreg_massAModel`): no hypothesis
is left on either side. -/
theorem forall_exists_massA_models_iff :
    (∀ (N : Type) [TopologicalSpace N] [SingularGXStructure (Flat.isom 2) (Minkowski 2) N],
      (∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) N, ∃ o,
        ∃ e : OpenPartialHomeomorph N (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
          x ∈ e.source) →
      ∃ C : Causality N, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) ↔
      ∀ o o' (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
        IsAEChart (Flat.isom 2) (Minkowski 2) ψ →
          ChartIso (massAModelCausality o) (massAModelCausality o') ψ :=
  forall_exists_massA_dec25_models_iff hreg_massAModel

/-- **The existence half of `cor:massA_causalite` over the family, reduced**: every singular
`(Isom(E^{1,2}), E^{1,2})`-manifold whose singular points lie in `X_A`-charts carries a natural
causality iff every a.e. isomorphism chart `E_κ ⇀ E_κ'` between massive models whose source meets
the line is a chart isomorphism. -/
theorem forall_exists_massA_models_iff_sing :
    (∀ (N : Type) [TopologicalSpace N] [SingularGXStructure (Flat.isom 2) (Minkowski 2) N],
      (∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) N, ∃ o,
        ∃ e : OpenPartialHomeomorph N (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
          x ∈ e.source) →
      ∃ C : Causality N, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) ↔
      ∀ o o' (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
        IsAEChart (Flat.isom 2) (Minkowski 2) ψ → o ≠ none → o' ≠ none →
          (ψ.source ∩ Sing (Flat.isom 2) (Minkowski 2) (MassAModel o)).Nonempty →
            ChartIso (massAModelCausality o) (massAModelCausality o') ψ := by
  rw [forall_exists_massA_models_iff]
  exact ⟨fun h o o' ψ hψ _ _ _ => h o o' ψ hψ, hiso_massAModel_of_sing⟩

/-- **The three corollaries over the family**, `hreg` discharged, (b′) named:
`massA_singular_dec25_models` with `hreg_massAModel`. -/
theorem massA_singular_models {M : Type*} [TopologicalSpace M]
    [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
    (hiso : ∀ o o' (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
      IsAEChart (Flat.isom 2) (Minkowski 2) ψ →
        ChartIso (massAModelCausality o) (massAModelCausality o') ψ)
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) :
    ∃ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ∧
      (∀ C' : Causality M, C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality → C' = C) ∧
      C.CausallyArcConnected ∧ C.PushUp :=
  massA_singular_dec25_models hreg_massAModel hiso hcov

/-! ### Each model as an `E_{≥0}`-manifold -/

/-- **Each model is covered by an isomorphic `X_A`-chart**: its identity, into itself. -/
theorem isoChartsCoverDEC25_model (o : Option {κ : ℝ // 0 < κ}) :
    IsoChartsCoverDEC25 (Flat.isom 2) (massAModelCausality o) (minkowski 2)
      massAModelCausality := fun x =>
  Or.inr ⟨o, OpenPartialHomeomorph.refl _, isAEChart_refl, mem_univ x, chartIso_refl _⟩

/-- **`massA_dec25_models_of_isoChartsCover` at every model of `E_{≥0}`**, with its own singular
structure and causality (a singular point at every model but `E_{2π}`). -/
theorem massA_dec25_models_model (o : Option {κ : ℝ // 0 < κ}) :
    (massAModelCausality o).CausallyArcConnected ∧ (massAModelCausality o).PushUp :=
  massA_dec25_models_of_isoChartsCover (G := Flat.isom 2) (M := MassAModel o)
    (massAModel_facts o).1.absolutelyMinimal (isoChartsCoverDEC25_model o)

/-- **The causality of a model is natural over the family iff (b′) holds from that model**: the first
clause of `IsAtlasCausalityDEC25` is `hreg`, the third the model's absolute minimality, the second
is (b′) from it. -/
theorem isAtlasCausalityDEC25_model_iff (o : Option {κ : ℝ // 0 < κ}) :
    IsAtlasCausalityDEC25 (Flat.isom 2) (massAModelCausality o) (minkowski 2)
        massAModelCausality ↔
      ∀ o' (ψ : OpenPartialHomeomorph (MassAModel o) (MassAModel o')),
        IsAEChart (Flat.isom 2) (Minkowski 2) ψ →
          ChartIso (massAModelCausality o) (massAModelCausality o') ψ :=
  ⟨fun h => h.2.1, fun h => ⟨hreg_massAModel o, h, (massAModel_facts o).1.absolutelyMinimal⟩⟩

section TwoPiManifold

attribute [local instance] EAlphaGX.singularGX

/-- `E_{2π}` is natural over the whole family (no singular point). -/
theorem isAtlasCausalityDEC25_twoPi :
    IsAtlasCausalityDEC25 (Flat.isom 2) (massAModelCausality (some twoPi)) (minkowski 2)
      massAModelCausality :=
  (isAtlasCausalityDEC25_model_iff (some twoPi)).2 fun _ _ hψ =>
    chartIso_models_of_sing_eq_empty_left (o := some twoPi) EAlphaGX.sing_eq_empty_two_pi hψ

end TwoPiManifold

/-! ### Witness with a singular point: `E₀` -/

section E0Witness

attribute [local instance] E0GX.singularGX

/-- **Witness with a singular point, local form**: `E₀` with `E0GX.singularGX` and `E0.causality`.
Its singular locus is the axis; its identity is an `X_A`-chart into `E₀` and a chart isomorphism,
so `massA_dec25_models_of_isoChartsCover` applies. -/
theorem e0_witness :
    (Sing (Flat.isom 2) (Minkowski 2) E0).Nonempty ∧
      IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      E0.causality.CausallyArcConnected ∧ E0.causality.PushUp := by
  have hcover : IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2)
      massAModelCausality := fun x =>
    Or.inr ⟨none, OpenPartialHomeomorph.refl E0, isAEChart_refl, mem_univ x, chartIso_refl _⟩
  exact ⟨E0GX.sing_nonempty, hcover,
    massA_dec25_models_of_isoChartsCover E0.causallyArcConnected.absolutelyMinimal hcover⟩

/-- **Witness of `massA_causalite_unique_dec25` with a singular point, one model**: `E₀` over the
single model `E₀`. -/
theorem e0_unique_witness :
    IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2)
        (fun _ : Unit => massAModelCausality none) ∧
      ∀ C' : Causality E0, C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2)
          (fun _ : Unit => massAModelCausality none) → C' = E0.causality := by
  have hC : IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2)
      (fun _ : Unit => massAModelCausality none) :=
    ⟨E0GX.chartIso_of_mem_aeAtlas, fun _ _ he => BPrimeE0.chartIso_of_isAEChart he,
      E0.causallyArcConnected.absolutelyMinimal⟩
  exact ⟨hC, fun _ hmin' hcover' => massA_causalite_unique_dec25 hC hmin' hcover'⟩

/-- **`E0.causality` is natural over the whole family `E_{≥0}`** on `E₀`: (b′) from `E₀` holds in
full (`hiso_row_none`). -/
theorem isAtlasCausalityDEC25_e0 :
    IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality :=
  (isAtlasCausalityDEC25_model_iff none).2 hiso_row_none

/-- **Witness of `massA_dec25_models` (hence of `massA_causalite_unique_dec25`) over the whole
family, at a manifold with a singular point**: `E₀`. -/
theorem massA_dec25_models_e0 :
    IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      E0.causality.CausallyArcConnected ∧ E0.causality.PushUp ∧
      ∀ C' : Causality E0, C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality →
          C' = E0.causality :=
  ⟨isAtlasCausalityDEC25_e0, massA_dec25_models (fun x _ =>
    ⟨none, OpenPartialHomeomorph.refl E0, isAEChart_refl, mem_univ x⟩) isAtlasCausalityDEC25_e0⟩

end E0Witness

/-! ### `E₀`-manifolds over the whole family -/

section E0Manifolds

attribute [local instance] E0GX.singularGX

/-- **`cor:massA_causalite`, `cor:massA_cac` and `cor:pushup_sing` at `E₀`-manifolds, over the whole
family `E_{≥0}`, no hypothesis left**: a singular `(Isom(E^{1,2}), E^{1,2})`-manifold whose singular
points lie in a.e. isomorphism charts into `E₀` carries an absolutely minimal causality for which
every chart of its maximal a.e. atlas and every a.e. isomorphism chart into every `E_κ`, `κ ≥ 0`, is
an isomorphism; it is causally arc-connected, has push-up, and is the only absolutely minimal
causality with an isomorphic chart at every point. The causality is
`BPrimeE0.existsUnique_causality_e0`'s; a chart into an `E_κ`, `κ > 0`, has a regular source, by
`source_subset_reg_of_isAEChart_e0_massive` read through a chart into `E₀`. -/
theorem massA_dec25_e0_manifolds {M : Type*} [TopologicalSpace M]
    [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ e : OpenPartialHomeomorph M E0,
      IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source) :
    ∃ C : Causality M, IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality ∧
      C.CausallyArcConnected ∧ C.PushUp ∧
      ∀ C' : Causality M, C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality → C' = C := by
  obtain ⟨C, hCX, hC0, hmin, -⟩ := BPrimeE0.existsUnique_causality_e0 hcov
  have hcov' : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ o,
      ∃ e : OpenPartialHomeomorph M (MassAModel o), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source := fun x hx => by
    obtain ⟨e, he, hxe⟩ := hcov x hx
    exact ⟨none, e, he, hxe⟩
  -- the charts of the maximal atlas and into `E₀` cover: `C` is causally arc-connected
  have hcover : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality := by
    intro x
    by_cases hx : x ∈ Reg (Flat.isom 2) (Minkowski 2) M
    · obtain ⟨e, he, hxe⟩ := mem_support.1 hx
      exact Or.inl ⟨e, he, hxe, hCX e he⟩
    · obtain ⟨e, he, hxe⟩ := hcov x hx
      exact Or.inr ⟨none, e, he, hxe, hC0 e he⟩
  have hcac := (massA_dec25_models_of_isoChartsCover hmin hcover).1
  -- every chart into an `E_κ` has a regular source, hence is an isomorphism
  have hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality := by
    refine ⟨hCX, ?_, hmin⟩
    rintro (_ | κ) e he
    · exact hC0 e he
    · letI : SingularGXStructure (Flat.isom 2) (Minkowski 2) (MassAModel (some κ)) :=
        massAModelSingularGX (some κ)
      refine chartIso_of_isAEChart_of_subset_reg Flat.isom_strongMorphism
        (massAModel_facts (some κ)).1 (hreg_massAModel (some κ)) hCX he
        (hcac.absolutelyMinimalOn_all _) fun x hx => ?_
      by_contra hxs
      obtain ⟨f, hf, hxf⟩ := hcov x hxs
      have hχ := hf.symm.trans he
      have hfx : f x ∈ (f.symm.trans e).source := by
        rw [OpenPartialHomeomorph.trans_source]
        refine ⟨f.map_source hxf, ?_⟩
        show f.symm (f x) ∈ e.source
        rw [f.left_inv hxf]
        exact hx
      exact hxs ((hf.mem_reg_iff hxf).2 (source_subset_reg_of_isAEChart_e0_massive hχ hfx))
  exact ⟨C, hC, massA_dec25_models hcov' hC⟩

end E0Manifolds

/-! ### Witness with a singular point: `E_π` -/

section EPiWitness

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- **Witness with a singular point, local form**: `E_π` with `EAlphaGX.singularGX π` and
`massive π`. Its singular locus is the line; its identity is an `X_A`-chart into `E_π`, so
`massA_dec25_models_of_isoChartsCover` applies. -/
theorem epi_witness :
    (Sing (Flat.isom 2) (Minkowski 2) (Massive π)).Nonempty ∧
      IsoChartsCoverDEC25 (Flat.isom 2) (massive π) (minkowski 2) massAModelCausality ∧
      (massive π).CausallyArcConnected ∧ (massive π).PushUp := by
  have hcover : IsoChartsCoverDEC25 (Flat.isom 2) (massive π) (minkowski 2)
      massAModelCausality := fun x =>
    Or.inr ⟨some ⟨π, pi_pos⟩, OpenPartialHomeomorph.refl (Massive π), isAEChart_refl, mem_univ x,
      chartIso_refl _⟩
  exact ⟨EAlphaGX.sing_nonempty (by linarith [pi_pos] : π < 2 * π).ne, hcover,
    massA_dec25_models_of_isoChartsCover massive_absolutelyMinimal hcover⟩

end EPiWitness

/-! ### Witness at `E^{1,2}` over the whole family -/

section MinkowskiWitness

attribute [local instance] minkowskiSingularGX

/-- **`E^{1,2}` is natural over the whole family `E_{≥0}`**: its `X_A`-charts have regular sources
(`Reg(E^{1,2}) = E^{1,2}`), so they are isomorphisms (`chartIso_of_isAEChart_of_subset_reg`). -/
theorem isAtlasCausalityDEC25_minkowski_models :
    IsAtlasCausalityDEC25 (Flat.isom 2) (minkowski 2) (minkowski 2) massAModelCausality := by
  have hX := massA_dec25_minkowski.1.1
  have hR : Reg (Flat.isom 2) (Minkowski 2) (Minkowski 2) = univ := by
    rw [Reg]
    exact support_maximalAtlas
  refine ⟨hX, fun o e he => ?_, minkowski_absolutelyMinimal⟩
  exact chartIso_of_isAEChart_of_subset_reg Flat.isom_strongMorphism (massAModel_facts o).1
    (hreg_massAModel o) hX he (minkowski_causallyArcConnected.absolutelyMinimalOn_all _)
    (by rw [hR]; exact subset_univ _)

/-- **Witness of `massA_dec25_models` at `E^{1,2}` over the whole family** (`massA_dec25_minkowski`
is the one-model form). -/
theorem massA_dec25_models_minkowski :
    (minkowski 2).CausallyArcConnected ∧ (minkowski 2).PushUp ∧
      ∀ C' : Causality (Minkowski 2), C'.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C' (minkowski 2) massAModelCausality →
          C' = minkowski 2 := by
  have hR : Reg (Flat.isom 2) (Minkowski 2) (Minkowski 2) = univ := by
    rw [Reg]
    exact support_maximalAtlas
  refine massA_dec25_models (fun x hx => ?_) isAtlasCausalityDEC25_minkowski_models
  have : x ∈ Reg (Flat.isom 2) (Minkowski 2) (Minkowski 2) := by rw [hR]; exact mem_univ x
  exact absurd this hx

end MinkowskiWitness

end MassAModelsInstance

end Causal
