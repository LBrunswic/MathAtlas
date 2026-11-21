import Causal.Port.SFABTZ
import Causal.LineDevelopment

/-!
# `SingularFlatAxioms`' field `line` at the BTZ points of every `E_{≥0}`-manifold

Target `T-ett-sfa-line-e0`. Cited, **unmarked** (SCOPE): `lem:past_BTZ` — `ETT.tex:1515`, its (a)
at `α = 0`; as a corollary beyond the target, `defi:causal_E0` — `ETT.tex:1344` (its
`J⁻(p) = {r = 0, τ ≤ τ(p)}` read at a causal `M`). For a singular `(Isom(𝐌³), 𝐌³)`-manifold `M`
(DEC-25), Hausdorff, and every causality `C` with an isomorphic chart at each point over the family
`E_{≥0}` (`IsoChartsCoverDEC25 … massAModelCausality`), the field
`Causal.Causality.BTZAxioms.line`: through every BTZ point `p ∈ sing₀(M)` an inextensible causal
curve `γ : ℝ → M`, `γ 0 = p`, onto the connected component of `sing₀(M)` through `p`, a closed
embedding when `C` is causal. With `Causal.SFABTZ` this gives `BTZAxioms` at every such `M` (`C`
absolutely minimal), and `SingularFlatAxioms` at every Hausdorff, second countable `E₀`-manifold
with its natural causality.

> `lem:past_BTZ` (a). For every $\alpha\in \RR_+$, each connected component of
> $\sing_\alpha(M)$ is an inextensible causal curve; if $\alpha>0$, such a connected component is
> moreover chronal. (`ETT.tex:1518–1519`)

> Proof of (a). Let $\alpha \in \RR_+$ and let $\Delta$ be a connected component of
> $\sing_\alpha(M)$. By Property \ref{prop:GX_sing_dec} it is a connected $1$-dimensional
> submanifold; since $M$ is a differential manifold, it is parametrisable by $\RR$. Moreover it is
> locally chronal by Definition \ref{defi:causal_Ealpha} if $\alpha>0$, and locally causal by
> Definition \ref{defi:causal_E0} if $\alpha=0$. Consequently it is a chronal curve if $\alpha>0$
> and a causal curve if $\alpha=0$. Finally, $\Delta$ is inextensible, being a closed submanifold
> without boundary. (`ETT.tex:1529–1533`)

## What is proved (no `sorry` in this file)

* **The translation atlas of `sing₀(M)`** (`isTranslationAtlas`): for any family of `X_A`-charts
  `e i : M ⇀ E₀` covering `sing₀(M)`, the charts `x ↦ τ(e i x)` of `sing₀(M) ∩ source`, onto
  `J i = {r | (r, 0) ∈ target}` (`axisParams`), with inverses `r ↦ (e i)⁻¹(r, 0)` (`axisInv`).
  Each transition is a translation, by one application of `BPrimeE0.exists_eqOn_rotE0_tauShift`
  to `(e i)⁻¹ ≫ e j` at the axis point `e i x` (`trans_tau`: `τ ∘ e j = τ ∘ e i + t` near `x`).
* **The inverse charts are causal** (`causalCurveOn_symm_axis`): through a chart isomorphism into
  `E₀`, every segment of the axis inside the target is a future causal curve of `M`
  (`E0.axis_causalCurveOn`, `ChartIso.curveOn_symm`).
* **The field `line`** (`line`), through `LineDevelopment.exists_line`, with `M` Hausdorff and
  `sing₀(M)` closed (`isClosed_sing_zero`, from `SFALocal.isClosed_sing`); the atlas of the chart
  isomorphisms (`IsoChart`, `isTranslationAtlas_isoChart`) and the development itself, causal over
  every segment (`exists_isLineDevelopment`).
* **Assemblies**: `btzAxioms` (`BTZAxioms (sing₀ M)` at every Hausdorff `E_{≥0}`-manifold, `C`
  absolutely minimal); `singularFlatAxioms_iff_massive_line` (Hausdorff, second countable:
  `SingularFlatAxioms` iff the field `massive_line`). `E₀`-manifolds: `line_e0`, `btzAxioms_e0`,
  `singularFlatAxioms_e0` (`SingularFlatAxioms` at every Hausdorff, second countable `E₀`-manifold
  with its natural causality, no field left).
* **Beyond the field** (unmarked): at a causal Hausdorff `E_{≥0}`-manifold, `J⁻(p)` is the
  half-line `γ(]-∞, 0])` of the line below the BTZ point `p` (`Jminus_eq_image`), hence closed
  (`isClosed_Jminus`).
* **Witnesses** (kb/0011): `nonvacuous_e0` (`M = E₀`, `sing₀ = axis ≠ ∅`, `SingularFlatAxioms`
  out of `singularFlatAxioms_e0`, not of `E0.singularFlatAxioms`); `nonvacuous_e0_family` (the
  hypotheses of `line`, `btzAxioms`, `Jminus_eq_image` at `E₀`, `C` causal, `BTZAxioms` out of
  `btzAxioms`); `line_e0_axis` (at `E₀` the line through an axis point is the whole axis).

## Hypothesis checklist (`line`)

| paper | here |
|---|---|
| `M` a singular spacetime (`def:singular_spacetime`, l.1500–1505): a connected `E_A`-manifold with the generated causality | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `C` any causality with an isomorphic chart at each point (`IsoChartsCoverDEC25`); ⚠ weakened: neither connectedness nor absolute minimality is used by `line` (minimality enters `btzAxioms` through `Causal.SFABTZ`) |
| « `M` is a differential manifold » (l.1530; `rem:singular_flat_spacetime_therefore`, l.1508) | ✓ carried: `[T2Space M]` (the « manifold » reading, DEC-25, `RamcovGX.tex:474`); ⚠ weakened: no second countability, no smoothness (`line`, `btzAxioms`); second countability carried only by the `SingularFlatAxioms` assemblies, whose structure has it as a field |
| `sing_0(M)` (`α = 0`) | ⚠ read: `SFALocal.sing M 0`, the points an `X_A`-chart into `E₀` sends to the axis |
| `Δ` « a connected 1-dimensional submanifold » (`prop:GX_sing_dec`, l.1435) | ✓ derived, by another route (no hypothesis): the translation atlas of `sing₀(M)` built from the charts into `E₀` (`isTranslationAtlas`), its transitions translations by `prop:isom` of `brunswic2021cauchy` at `α = β = 0` (`BPrimeE0.exists_eqOn_rotE0_tauShift`, formalized); `sing₀(M)` closed (`SFALocal.isClosed_sing`) |
| « parametrisable by `ℝ` » | ✓ continuous `γ : ℝ → M`, `γ 0 = p`, onto the component; a closed embedding when `C` is causal; periodic allowed otherwise (DEC-6, SCOPE) |
| « locally causal by `defi:causal_E0` » | ✓ derived: the axis of `E₀` is a future causal curve (`E0.axis_causalCurveOn`), read through a `ChartIso` |
| « inextensible, being a closed submanifold without boundary » | ✓ derived: `LineDevelopment.inextensible_of_not_tendsto` (no limit at `±∞`) |
| `E₀` (l.1330), `Isom(𝔼^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2 = SO₀(1,2) ⋉ ℝ³` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** `lem:past_BTZ` is a statement about every `α ∈ ℝ₊` and every singular
  spacetime; this module proves its (a) at `α = 0` only (the `E_κ` half is T-ett-sfa-massive-line),
  in the readings OQ-18 (the causality), OQ-34/OQ-35 (`E₀`) and OQ-82 (the group). (b) is
  `Causality.SingularFlatAxioms.past_BTZ_b` (`Causal.SingularFlat`). `defi:causal_E0` is a
  statement of the model; `Jminus_eq_image` is its half-line read at a causal `M`, under the same
  readings.
* **The orientation of the line.** `γ` is future-directed: the time coordinate `τ` of the charts
  into `E₀` increases along it. This is the reading of « lightlike » (l.1331, l.1345) that
  `Causal.E0` carries (OQ-35), not a choice made here.
* **Periodic parametrisations** (DEC-6). When `C` is not causal a component may be compact (by hand,
  not formalized: `E₀` modulo a translation along the axis); `γ` is then periodic and no closed
  embedding. The field asks the closed embedding only when `C` is causal, and that is what is
  proved; `Jminus_eq_image` asks `C` causal for the half-line shape: on the circle the set equation
  `J⁻(p) = γ(]−∞, 0])` would still hold (`γ` periodic, so `J⁻(p)` is the whole component), but `γ`
  is no closed embedding there, and `J⁻(p)` is no half-line.
* **Hausdorff is used** (arc uniqueness in `LineDevelopment.exists_development`). By hand, not
  formalized: two copies of `E₀` glued along the complement of a closed upper half-axis form a
  non-Hausdorff space with charts into `E₀` whose `sing₀` component is a « Y »: two upper branches
  joined only through the lower half-axis, so no causal curve (along which `τ` cannot decrease)
  has it as image.
* **The atlas.** It is indexed by the `X_A`-charts into `E₀` that are chart isomorphisms for `C`
  (`IsoChart`), which cover `sing₀(M)` (`SFALocal.exists_chartIso_e0`); the translation structure
  itself needs no causality (`isTranslationAtlas`, any `X_A`-charts), and the transitions are read
  off one pair of charts at a time. Absolute minimality is not used by `line`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports the strict
`Causal.Port.SFABTZ` and `Causal.LineDevelopment`.
-/
namespace Causal

open Set Filter Topology TopologicalSpace

universe u v

namespace SFALine

open LineDevelopment

attribute [local instance] E0GX.singularGX

/-! ### The axis of `E₀` through a chart -/

section Axis

variable {M : Type u} [TopologicalSpace M]

/-- The parameter set of the axis inside the target of a chart into `E₀`. -/
def axisParams (e : OpenPartialHomeomorph M E0) : Set ℝ := {r | ((r, 0) : E0) ∈ e.target}

/-- The inverse chart along the axis. -/
noncomputable def axisInv (e : OpenPartialHomeomorph M E0) (r : ℝ) : M := e.symm (r, 0)

theorem isOpen_axisParams (e : OpenPartialHomeomorph M E0) : IsOpen (axisParams e) :=
  e.open_target.preimage (continuous_id.prodMk continuous_const)

/-- **Through a chart isomorphism into `E₀`, every segment of the axis inside the target is a
future causal curve of `M`** (`defi:causal_E0`, « locally causal », read through the chart). -/
theorem causalCurveOn_symm_axis {C : Causality M} {e : OpenPartialHomeomorph M E0}
    (hiso : ChartIso C E0.causality e) {a b : ℝ} (h : Icc a b ⊆ axisParams e) :
    C.CausalCurveOn ⊤ (axisInv e) a b := by
  have hmem : ∀ t ∈ Icc a b,
      E0.axisLine ((0 : ℝ), (0 : ℂ)) t ∈ chartImage e (chartSource e) := by
    intro t ht
    show E0.axisLine ((0 : ℝ), (0 : ℂ)) t ∈ (chartImage e (chartSource e) : Set E0)
    rw [coe_chartImage_of_le le_rfl, coe_chartSource, e.image_source_eq_target]
    show (((0 : ℝ) + t, (0 : ℂ)) : E0) ∈ e.target
    rw [zero_add]
    exact h ht
  have hc := E0.axis_causalCurveOn ((0 : ℝ), (0 : ℂ)) (chartImage e (chartSource e)) hmem
  have h1 := ChartIso.curveOn_symm (fun N hN x hx y hy => (hiso N hN x hx y hy).1)
    E0.causality.isRelFamily_le le_rfl hc
  have h2 := CurveOn.mono_opens C.isRelFamily_le h1 le_top
  refine CurveOn.congr h2 fun t _ => ?_
  show e.symm (((0 : ℝ) + t, (0 : ℂ)) : E0) = e.symm (t, 0)
  rw [zero_add]

end Axis

/-! ### The translation atlas of `sing₀(M)` -/

section Atlas

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]

/-- **The transitions are translations** (`prop:isom` at `α = β = 0`, one application of
`BPrimeE0.exists_eqOn_rotE0_tauShift` to `e⁻¹ ≫ e′`): near a BTZ point in both sources,
`τ ∘ e′ = τ ∘ e + t`. -/
theorem trans_tau {e e' : OpenPartialHomeomorph M E0}
    (he : IsAEChart (Flat.isom 2) (Minkowski 2) e) (he' : IsAEChart (Flat.isom 2) (Minkowski 2) e')
    {x : M} (hx : x ∈ SFALocal.sing M 0) (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) :
    ∃ t : ℝ, ∀ᶠ y in 𝓝 x, (e' y).1 = (e y).1 + t := by
  have hψ := he.symm.trans he'
  have hmem : e x ∈ (e.symm.trans e').source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨e.map_source hxe, ?_⟩
    show e.symm (e x) ∈ e'.source
    rw [e.left_inv hxe]
    exact hxe'
  have hxa : e x ∈ E0.axis := (SFABTZ.mem_sing_zero_iff he hxe).1 hx
  obtain ⟨φ, t, O, hxO, -, heq⟩ := BPrimeE0.exists_eqOn_rotE0_tauShift hψ hmem hxa
  refine ⟨t, Filter.mem_of_superset ((e.isOpen_inter_preimage O.isOpen).mem_nhds ⟨hxe, hxO⟩) ?_⟩
  rintro y ⟨hye, hyO⟩
  have h := heq (e y) hyO
  have h1 : (e.symm.trans e') (e y) = e' y := by
    show e' (e.symm (e y)) = e' y
    rw [e.left_inv hye]
  rw [h1] at h
  show (e' y).1 = (e y).1 + t
  rw [h]
  rfl

variable {ι : Type v} {ch : ι → OpenPartialHomeomorph M E0}

/-- **The translation atlas of `sing₀(M)`** from any family of `X_A`-charts into `E₀` covering
it. -/
theorem isTranslationAtlas (hch : ∀ i, IsAEChart (Flat.isom 2) (Minkowski 2) (ch i))
    (hcov : ∀ p ∈ SFALocal.sing M 0, ∃ i, p ∈ (ch i).source) :
    IsTranslationAtlas (SFALocal.sing M 0) (fun i => (ch i).source) (fun i x => (ch i x).1)
      (fun i => axisInv (ch i)) (fun i => axisParams (ch i)) where
  isOpen_V i := (ch i).open_source
  isOpen_J i := isOpen_axisParams (ch i)
  continuousOn_τ i := (continuous_fst.comp_continuousOn (ch i).continuousOn).mono
    inter_subset_right
  continuousOn_σ i :=
    (ch i).continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      fun _ hr => hr
  mapsTo_τ i x hx := by
    have hxa : ch i x ∈ E0.axis := (SFABTZ.mem_sing_zero_iff (hch i) hx.2).1 hx.1
    show (((ch i x).1, (0 : ℂ)) : E0) ∈ (ch i).target
    rw [show (((ch i x).1, (0 : ℂ)) : E0) = ch i x from Prod.ext rfl hxa.symm]
    exact (ch i).map_source hx.2
  mapsTo_σ i r hr := by
    have hs : axisInv (ch i) r ∈ (ch i).source := (ch i).map_target hr
    refine ⟨(SFABTZ.mem_sing_zero_iff (hch i) hs).2 ?_, hs⟩
    show (ch i ((ch i).symm (r, 0))).2 = 0
    rw [(ch i).right_inv hr]
  σ_τ i x hx := by
    have hxa : ch i x ∈ E0.axis := (SFABTZ.mem_sing_zero_iff (hch i) hx.2).1 hx.1
    show (ch i).symm ((ch i x).1, 0) = x
    rw [show (((ch i x).1, (0 : ℂ)) : E0) = ch i x from Prod.ext rfl hxa.symm]
    exact (ch i).left_inv hx.2
  τ_σ i r hr := by
    show (ch i ((ch i).symm (r, 0))).1 = r
    rw [(ch i).right_inv hr]
  cover p hp := hcov p hp
  trans i j x hx := by
    obtain ⟨t, ht⟩ := trans_tau (hch i) (hch j) hx.1.1 hx.1.2 hx.2
    exact ⟨t, ht.mono fun y hy _ => hy⟩

end Atlas

/-! ### The field `line` at every `E_{≥0}`-manifold -/

section Line

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

variable (C) in
/-- The `X_A`-charts into `E₀` that are chart isomorphisms for `C`. -/
def IsoChart : Type u :=
  {e : OpenPartialHomeomorph M E0 // IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
    ChartIso C E0.causality e}

/-- The chart isomorphisms into `E₀` cover `sing₀(M)` (`SFALocal.exists_chartIso_e0`). -/
theorem isTranslationAtlas_isoChart
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    IsTranslationAtlas (SFALocal.sing M 0) (fun i : IsoChart C => i.1.source)
      (fun i x => (i.1 x).1) (fun i => axisInv i.1) (fun i => axisParams i.1) :=
  isTranslationAtlas (ch := fun i : IsoChart C => i.1) (fun i => i.2.1) fun p hp => by
    obtain ⟨e, he, hpe, hiso⟩ := SFALocal.exists_chartIso_e0 hC hp
    exact ⟨⟨e, he, hiso⟩, hpe⟩

/-- `sing₀(M)` is closed. -/
theorem isClosed_sing_zero
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    IsClosed (SFALocal.sing M 0) :=
  SFALocal.isClosed_sing (SFALocal.massACovered_of_isoChartsCover hC) 0 le_rfl

/-- **The development of the BTZ line through `p`** (`LineDevelopment.exists_development`). -/
theorem exists_isLineDevelopment [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {p : M} (hp : p ∈ SFALocal.sing M 0) :
    ∃ γ : ℝ → M, IsLineDevelopment (SFALocal.sing M 0) (fun i : IsoChart C => i.1.source)
      (fun i => axisInv i.1) (fun i => axisParams i.1) p γ ∧ ∀ a b, C.CausalCurveOn ⊤ γ a b := by
  have hA := isTranslationAtlas_isoChart hC
  obtain ⟨γ, hγ⟩ := LineDevelopment.exists_development (isClosed_sing_zero hC) hA hp
  exact ⟨γ, hγ, hγ.causalCurveOn hA fun i _ _ h => causalCurveOn_symm_axis i.2.2 h⟩

/-- **`lem:past_BTZ` (a) at `α = 0`, the field `BTZAxioms.line`, at every Hausdorff
`E_{≥0}`-manifold** (unmarked): through every BTZ point `p` an inextensible causal curve
`γ : ℝ → M`, `γ 0 = p`, onto the component of `sing₀(M)` through `p`, a closed embedding when `C`
is causal. -/
theorem line [T2Space M]
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    ∀ p ∈ SFALocal.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
      C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (SFALocal.sing M 0) p :=
  fun _ hp => exists_line (isClosed_sing_zero hC) (isTranslationAtlas_isoChart hC)
    (fun i _ _ h => causalCurveOn_symm_axis i.2.2 h) hp

/-- **`BTZAxioms` at every Hausdorff `E_{≥0}`-manifold** (absolutely minimal `C`). -/
theorem btzAxioms [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.BTZAxioms (SFALocal.sing M 0) :=
  SFABTZ.btzAxioms_of_line hmin hC (line hC)

/-- **`SingularFlatAxioms` at a Hausdorff, second countable `E_{≥0}`-manifold is exactly the field
`massive_line`.** -/
theorem singularFlatAxioms_iff_massive_line [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.SingularFlatAxioms (SFALocal.sing M) ↔
      ∀ α : ℝ, 0 < α → ∀ p ∈ SFALocal.sing M α, ∃ γ : ℝ → M, γ 0 = p ∧
        (C.IsCausal → IsClosedEmbedding γ) ∧
        C.Inextensible ⊤ univ γ ∧ (∀ a b, C.ChronalCurveOn ⊤ γ a b) ∧
        range γ = connectedComponentIn (SFALocal.sing M α) p := by
  rw [SFABTZ.singularFlatAxioms_iff_lines hmin hC]
  exact ⟨fun h => h.2, fun h => ⟨line hC, h⟩⟩

/-! ### Beyond the field: the causal past of a BTZ point is the half-line below it -/

/-- **`J⁻(p)` is the half-line of the BTZ line below `p`**, at every causal Hausdorff
`E_{≥0}`-manifold (`defi:causal_E0`'s `J⁻(p) = {r = 0, τ ≤ τ(p)}` read at `M`, unmarked): the
argument of `Causality.SingularFlatAxioms.Jminus_eq_image`, whose one use of the structure,
`J⁻(p) ⊆` the component, is `SFABTZ.Jminus_subset_component`. -/
theorem Jminus_eq_image [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) {p : M} (hp : p ∈ SFALocal.sing M 0) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsClosedEmbedding γ ∧ C.Inextensible ⊤ univ γ ∧
      range γ = connectedComponentIn (SFALocal.sing M 0) p ∧ C.Jminus ⊤ {p} = γ '' Iic 0 := by
  obtain ⟨γ, hγ0, hγe, hγi, hγr⟩ := line hC p hp
  have hγ := hγe hc
  refine ⟨γ, hγ0, hγ, hγi, hγr, ?_⟩
  ext q
  constructor
  · intro hq
    have hqp : C.le ⊤ q p := Precausality.mem_Jminus_singleton.1 hq
    have hqr : q ∈ range γ := by
      rw [hγr]
      exact SFABTZ.Jminus_subset_component hmin hC hp hqp
    obtain ⟨t, rfl⟩ := hqr
    refine ⟨t, ?_, rfl⟩
    by_contra ht
    have ht' : 0 < t := not_le.1 ht
    have h0t : C.le ⊤ (γ 0) (γ t) := hγi.1.le_of_le trivial trivial ht'.le
    rw [hγ0] at h0t
    have heq : γ t = γ 0 := (hc hqp h0t).trans hγ0.symm
    exact ht'.ne' (hγ.injective heq)
  · rintro ⟨t, ht, rfl⟩
    have h := hγi.1.le_of_le trivial trivial (show t ≤ 0 from ht)
    rw [hγ0] at h
    exact Precausality.mem_Jminus_singleton.2 h

/-- At every causal Hausdorff `E_{≥0}`-manifold the causal past of a BTZ point is closed. -/
theorem isClosed_Jminus [T2Space M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) {p : M} (hp : p ∈ SFALocal.sing M 0) : IsClosed (C.Jminus ⊤ {p}) := by
  obtain ⟨γ, -, hγ, -, -, hJ⟩ := Jminus_eq_image hmin hC hc hp
  rw [hJ]
  exact hγ.isClosedMap _ isClosed_Iic

/-! ### `E₀`-manifolds: a corollary -/

/-- `line` at every Hausdorff `E₀`-manifold with its natural causality. -/
theorem line_e0 [T2Space M] (hcov : SFALocalE0.E0Covered M) (hC : SFALocalE0.IsE0Natural C) :
    ∀ p ∈ SFALocalE0.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
      C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (SFALocalE0.sing M 0) p := by
  rw [← SFALocal.sing_eq_of_e0Covered hcov]
  exact line (SFALocal.isoChartsCoverDEC25_of_e0 hcov hC)

/-- `BTZAxioms` at every Hausdorff `E₀`-manifold with its natural causality. -/
theorem btzAxioms_e0 [T2Space M] (hcov : SFALocalE0.E0Covered M)
    (hC : SFALocalE0.IsE0Natural C) : C.BTZAxioms (SFALocalE0.sing M 0) := by
  rw [← SFALocal.sing_eq_of_e0Covered hcov]
  exact btzAxioms hC.2.2 (SFALocal.isoChartsCoverDEC25_of_e0 hcov hC)

/-- **`SingularFlatAxioms` at every Hausdorff, second countable `E₀`-manifold with its natural
causality**: no field left. -/
theorem singularFlatAxioms_e0 [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocalE0.E0Covered M) (hC : SFALocalE0.IsE0Natural C) :
    C.SingularFlatAxioms (SFALocalE0.sing M) :=
  (SFABTZ.singularFlatAxioms_iff_line_e0 hcov hC).2 (line_e0 hcov hC)

end Line

/-! ### Witness: `E₀` -/

section Witness

/-- **Non-vacuity at `E₀`** (kb/0011): `E₀` is a Hausdorff, second countable `E₀`-manifold with a
BTZ point, and `SingularFlatAxioms` comes out of `singularFlatAxioms_e0`. -/
theorem nonvacuous_e0 :
    SFALocalE0.E0Covered E0 ∧ SFALocalE0.IsE0Natural E0.causality ∧
      (SFALocalE0.sing E0 0).Nonempty ∧ E0.causality.SingularFlatAxioms (SFALocalE0.sing E0) := by
  obtain ⟨hcov, hC, -, hne⟩ := SFALocalE0.nonvacuous
  exact ⟨hcov, hC, hne, singularFlatAxioms_e0 hcov hC⟩

/-- **Non-vacuity of `line`, `btzAxioms` and `Jminus_eq_image` at `E₀`** (kb/0011):
`E0.causality` is absolutely minimal and causal, with an isomorphic chart at each point over the
family and a BTZ point, and `BTZAxioms` comes out of `btzAxioms` (not of `E0.btzAxioms`). -/
theorem nonvacuous_e0_family :
    E0.causality.AbsolutelyMinimal ∧
      IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      E0.causality.IsCausal ∧ (SFALocal.sing E0 0).Nonempty ∧
      E0.causality.BTZAxioms (SFALocal.sing E0 0) := by
  obtain ⟨hmin, hC, -, hne⟩ := SFALocal.nonvacuous_e0
  exact ⟨hmin, hC, E0.isCausal, hne, btzAxioms hmin hC⟩

/-- At `E₀` the line through an axis point is the whole axis. -/
theorem line_e0_axis {p : E0} (hp : p ∈ E0.axis) :
    ∃ γ : ℝ → E0, γ 0 = p ∧ IsClosedEmbedding γ ∧ E0.causality.Inextensible ⊤ univ γ ∧
      range γ = E0.axis := by
  obtain ⟨hcov, hC, h0, -⟩ := SFALocalE0.nonvacuous
  have hp' : p ∈ SFALocalE0.sing E0 0 := h0 ▸ hp
  obtain ⟨γ, hγ0, hemb, hinext, hrange⟩ := line_e0 hcov hC p hp'
  have hconn : IsPreconnected E0.axis := by
    rw [← E0.range_axisLine p]
    exact isPreconnected_range (E0.isometry_axisLine p).continuous
  refine ⟨γ, hγ0, hemb E0.isCausal, hinext, ?_⟩
  rw [hrange, h0]
  exact hconn.connectedComponentIn hp

end Witness

end SFALine

end Causal
