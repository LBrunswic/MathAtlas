import Causal.SFATransfer
import Causal.Port.BPrimeE0

/-!
# `SingularFlatAxioms`' chartwise fields at every `E₀`-manifold

Target `T-ett-sfa-local-e0`, scope (b) and (c). Cited, **unmarked** (SCOPE):
`rem:btz_pas_tarentin` — `ETT.tex:1358`, `rem:sing_tarentin` — `ETT.tex:1364`. For an
`E₀`-manifold `M` (a singular `(Isom(𝐌³), 𝐌³)`-manifold whose singular points lie in a.e. charts
into `E₀`, DEC-25) with its natural causality (`Causal.BPrimeE0.existsUnique_causality_e0`), the
fields of `Causal.Causality.SingularFlatAxioms` that are read in a chart, with `sing₀(M) = Sing(M)`
and `sing_α(M) = ∅` for `α ≠ 0`.

> Every point of a $\mass{\geq 0}$-manifold is strongly tarentin in the future, and the points
> which fail to be strongly tarentin in the past are exactly the BTZ points: this is immediate
> from Definitions \ref{defi:causal_Ealpha} and \ref{defi:causal_E0} read in a chart.
> (`rem:btz_pas_tarentin`, `ETT.tex:1358–1362`)

> Every $\mass{\geq0}$-manifold is a tarentin topological spacetime. (`rem:sing_tarentin`,
> `ETT.tex:1364–1366`)

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`def:category_topological_spacetimes`, `ETT.tex:254–255`)

## What is proved (no `sorry` in this file)

* **Any model family, over DEC-25** (`isoChartsCover_of_dec25` and the `…_of_dec25` forms): the
  transfer of `Causal.SFATransfer` read over `Causal.IsoChartsCoverDEC25`: `Z⁺ = M`,
  tarentin, and `Z⁻` at the points no isomorphic `X_A`-chart sends into the model's set.
* **`E₀`-manifolds.** `E0Covered M` (the `hcov` of `existsUnique_causality_e0`), `IsE0Natural C`
  (its conclusion: every chart an isomorphism, absolutely minimal), `existsUnique_isE0Natural`.
  `sing M α` is `Sing(M)` at `α = 0`, `∅` otherwise; `sing₀(M)` is the set of BTZ points read in
  any `X_A`-chart (`mem_axis_iff`, `sing_eq_btzPoints`). Then, for `M` and `C` natural:
  `rem:btz_pas_tarentin` as two theorems, `mem_Zplus` (`Z⁺ = M`) and `mem_Zminus_iff`
  (`p ∈ Z⁻ ↔ p ∉ sing₀(M)`, both directions: `mem_Zminus_of_notMem` from the charts,
  `Iminus_eq_empty` from absolute minimality); `rem:sing_tarentin` as `tarentin`, with
  `metrizableSpace` under the carried Hausdorff and second countable hypotheses. The other
  fields: `pastLocal` (`past_local`), `locallyCompactSpace`, `nhdsNE_neBot`, `isClosed_sing`,
  `interior_sing`; and `pushUp`, `causallyArcConnected` (DEC-25 corollaries), and `causallyPlain`.
  `singularFlatAxioms_iff`: for `M` T2 and second countable, `C.SingularFlatAxioms (sing M)` holds
  iff the three BTZ fields not proved here hold (`singularPastAt`, `Iplus_of_lt`, `line`).
* **Witness** (`nonvacuous`, kb/0011): `M = E₀` with `E0GX.singularGX` and `E0.causality`
  satisfies every hypothesis, with `sing₀ = axis ≠ ∅`; `sing E0 = Causal.E0.singE0`, so
  with `nonvacuous`, `e0_singularFlatAxioms` shows that the hypotheses of `singularFlatAxioms_iff`
  and both its sides hold there. **Absolute minimality is used for the BTZ half**
  (`e0_topTotal_separates`): a non-minimal causality on `E₀` with one isomorphic chart into `E₀`
  at every point (not every chart; it is not causal, kb/0014) has every point in `Z⁻`.

## Hypothesis checklist

| paper | here |
|---|---|
| `E_{≥0}`-manifold | ⚠ strengthened (instance): an `E₀`-manifold only, DEC-25 (`[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `E0Covered M`); the `E_κ` charts are `Causal.Port.SFALocal` |
| its causality | ⚠ read (OQ-18): the natural one (`IsE0Natural`, `existsUnique_causality_e0`) |
| « BTZ points » = `sing₀(M)` | ⚠ read: `Sing(M)`, every point of which every `X_A`-chart sends to the axis (`mem_axis_iff`); `sing_α(M) = ∅`, `α ≠ 0` |
| « topological spacetime »: Hausdorff, second countable (`ETT.tex:254`) | ✓ carried, `[T2Space M] [SecondCountableTopology M]`, by `metrizableSpace` and `singularFlatAxioms_iff` only: read as part of « manifold »: gx's singular `(G,X)`-manifold is « locally connected Hausdorff second countable » (`RamcovGX.tex:474`), the definition DEC-25 adopts for OQ-19, as `prop:GX_sing_dec` (`ETT.tex:1435`) and the DEC-90 precedent agree; `SingularGXStructure` gives neither |
| `E₀` (`ETT.tex:1330`), `Isom(𝔼^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2 = SO₀(1,2) ⋉ ℝ³` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** Both rows are about every `E_{≥0}`-manifold; here the models are `E₀` and
  `E^{1,2}` only (the `E_κ` charts: `Causal.Port.SFALocal`), and they wait on OQ-34/OQ-35 and OQ-82.
* **Not proved here**: the BTZ fields `singularPastAt`, `Iplus_of_lt`, `line`;
  `singularFlatAxioms_iff` shows they are all that is missing. They are proved in
  `Causal.SFABTZ.singularPastAt_e0`, `Causal.SFABTZ.Iplus_of_lt_e0` and `Causal.SFALine.line_e0`,
  and `SingularFlatAxioms` at every T2, second countable `E₀`-manifold is
  `Causal.SFALine.singularFlatAxioms_e0`.
* **Hausdorff and second countable are carried, never derived.** A `SingularGXStructure` gives
  neither (not formalized: a disjoint union of uncountably many copies of `𝐌³` is not second
  countable). They are read as part of « manifold »: gx's definition of a singular `(G,X)`-manifold,
  which DEC-25 adopts (OQ-19), reads « locally connected Hausdorff second countable »
  (`papers/gx/legacy/labeled/RamcovGX.tex:474`), as `prop:GX_sing_dec` (`ETT.tex:1435`) says, as
  DEC-90 recorded for Barbot, and as gx's own `SingGXCat` (`Causal.Port.SingularAtlas`) bundles
  them; with them, « is a topological spacetime » in `rem:sing_tarentin` is the
  hypothesis itself (`def:category_topological_spacetimes`, `ETT.tex:254`). Only
  `metrizableSpace` and `singularFlatAxioms_iff` take them; `tarentin`, `mem_Zplus` and
  `mem_Zminus_iff` hold without them.
* **`sing_α(M)`** is not defined in `ETT.tex` (it comes from `brunswic2021cauchy`). For an
  `E₀`-manifold it is read as `Sing(M)` at `α = 0` and `∅` otherwise: the only singular model is
  `E₀`, and every `X_A`-chart sends exactly the singular points of its source to the axis
  (`mem_axis_iff`, by `IsAEChart.mem_reg_iff` and `E0GX.reg_eq`), so « BTZ point » does not
  depend on the chart that reads it.
* **What each half uses.** `Z⁺ = M`, tarentin, `M ∖ sing₀(M) ⊆ Z⁻` and `past_local` are read in
  charts only (`Causal.SFATransfer`), with no absolute minimality; `Z⁻` off `sing₀(M)`
  does not even use `E0Covered` (`locZminus`: the regular points, in charts of the maximal a.e.
  atlas). `I⁻(p) = ∅` at a BTZ point is not a chart fact in general: a chart isomorphism constrains the
  relations of the open subsets of its source, hence `≪_M` only when one chart's source is all of
  `M` (on `E₀`, any causality making the identity an isomorphism has `I⁻(p) = ∅` on the axis). It uses the absolute minimality of the
  natural causality, with a cover whose members through a BTZ point are all sources of charts into
  `E₀` (the sources of charts of the maximal a.e. atlas lie in `Reg(M)`). Without minimality it
  can fail when one isomorphic chart is asked at each point (`e0_topTotal_separates`, a causality
  without gluing, not causal, for which the identity of `E₀` is not an isomorphism, kb/0014); in
  the paper's every-chart form it can fail only on an `E₀`-manifold that no single chart covers
  (two disjoint copies of `E₀`; not formalized): the paper's « immediate
  ... read in a chart » holds for the BTZ half only through the uniqueness of
  `defi:causal_Ealpha` (l.1339–1340), i.e. OQ-18.
* **Causal plainness (OQ-16).** `causallyPlain`: the natural causality of an `E₀`-manifold is
  causally plain, by `causallyPlain_of_locZ` (push-up, `Z⁺` in every open set, `Z⁻` off
  `sing₀(M)`, `interior sing₀(M) = ∅`). This shows `E₀`-manifolds are causally plain: evidence for
  OQ-16 (« are they meant to be causally plain? »), not an answer to it; the `E_κ` charts are not
  covered.
* **Over DEC-25, any family.** `IsoChartsCoverDEC25` is used as it is; the transfer lemmas take
  it through `isoChartsCover_of_dec25`, which forgets the `(G,X)` data (the ETT-layer module
  cannot import `Causal.Remarks.MassADEC25`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace

universe u v w y z

namespace SFALocalE0

open SFATransfer

/-! ### Any model family, over DEC-25 atlases -/

section DEC25

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type u} [TopologicalSpace M] [SingularGXStructure G X M]
  {A : Type z} {Xα : A → Type y} [∀ a, TopologicalSpace (Xα a)]
  [∀ a, SingularGXStructure G X (Xα a)]
  {C : Causality M} {DX : Causality X} {DY : ∀ a, Causality (Xα a)}

/-- `IsoChartsCoverDEC25` forgets to `IsoChartsCover`. -/
theorem isoChartsCover_of_dec25 (h : IsoChartsCoverDEC25 G C DX DY) : IsoChartsCover C DX DY := by
  intro x
  rcases h x with ⟨e, -, hx, he⟩ | ⟨a, e, -, hx, he⟩
  · exact Or.inl ⟨e, hx, he⟩
  · exact Or.inr ⟨a, e, hx, he⟩

/-- **`Z⁺ = M` over DEC-25**, any model family with `Z⁺` in every open set. -/
theorem mem_Zplus_of_dec25 (h : IsoChartsCoverDEC25 G C DX DY) (hX : E0LM.LocZplus DX)
    (hY : ∀ a, E0LM.LocZplus (DY a)) (p : M) : p ∈ C.Zplus := by
  exact IsoChartsCover.mem_Zplus (isoChartsCover_of_dec25 h) hX hY p

/-- **Tarentin over DEC-25**, any model family tarentin in every open set. -/
theorem tarentin_of_dec25 (h : IsoChartsCoverDEC25 G C DX DY) (hX : E0LM.LocTarentin DX)
    (hY : ∀ a, E0LM.LocTarentin (DY a)) : C.Tarentin := by
  exact IsoChartsCover.tarentin (isoChartsCover_of_dec25 h) hX hY

/-- **`Z⁻` over DEC-25** at the points no isomorphic `X_A`-chart sends into the model's set, the
regular model having `Z⁻` in every open set. -/
theorem mem_Zminus_of_dec25 {SY : ∀ a, Set (Xα a)} (h : IsoChartsCoverDEC25 G C DX DY)
    (hX : E0LM.LocZminus DX ∅) (hY : ∀ a, E0LM.LocZminus (DY a) (SY a)) {x : M}
    (hx : ∀ a (e : OpenPartialHomeomorph M (Xα a)), IsAEChart G X e → x ∈ e.source →
      ChartIso C (DY a) e → e x ∉ SY a) :
    x ∈ C.Zminus := by
  refine mem_Zminus_of_charts (T := {x | ∀ a (e : OpenPartialHomeomorph M (Xα a)),
      IsAEChart G X e → x ∈ e.source → ChartIso C (DY a) e → e x ∉ SY a}ᶜ) (SX := ∅)
    (fun y hy => ?_) hX hY (not_not.2 hx)
  have hy' := not_not.1 hy
  rcases h y with ⟨e, -, hye, he⟩ | ⟨a, e, hea, hye, he⟩
  · exact Or.inl ⟨e, hye, he, notMem_empty _⟩
  · exact Or.inr ⟨a, e, hye, he, hy' a e hea hye he⟩

end DEC25

/-! ### The local model facts of `E^{1,2}` -/

theorem minkowski_locZplus (n : ℕ) : E0LM.LocZplus (minkowski n) := by
  refine E0LM.locZplus_of minkowski_causallyArcConnected minkowski_stronglyCausal fun y => ?_
  rw [minkowski_Zplus]
  exact mem_univ y

theorem minkowski_locZminus (n : ℕ) : E0LM.LocZminus (minkowski n) ∅ := by
  refine E0LM.locZminus_of minkowski_causallyArcConnected minkowski_stronglyCausal fun y _ => ?_
  rw [minkowski_Zminus]
  exact mem_univ y

theorem minkowski_locTarentin (n : ℕ) : E0LM.LocTarentin (minkowski n) := by
  exact E0LM.locTarentin_of minkowski_causallyArcConnected minkowski_stronglyCausal
    minkowski_tarentin

/-! ### `E₀`-manifolds -/

section E0Manifold

attribute [local instance] E0GX.singularGX

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]

variable (M) in
/-- **An `E₀`-manifold** (DEC-25): its singular points lie in a.e. isomorphism charts into `E₀`
(the `hcov` of `Causal.BPrimeE0.existsUnique_causality_e0`). -/
def E0Covered : Prop :=
  ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ e : OpenPartialHomeomorph M E0,
    IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source

/-- **The natural causality of an `E₀`-manifold**: every chart of the maximal a.e. atlas an
isomorphism onto `𝐌³`, every chart into `E₀` one onto `E₀`, absolutely minimal (the conclusion of
`existsUnique_causality_e0`). -/
def IsE0Natural (C : Causality M) : Prop :=
  (∀ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, ChartIso C (minkowski 2) e) ∧
    (∀ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e →
      ChartIso C E0.causality e) ∧
    C.AbsolutelyMinimal

/-- An `E₀`-manifold has exactly one natural causality. -/
theorem existsUnique_isE0Natural (hcov : E0Covered M) : ∃! C : Causality M, IsE0Natural C := by
  obtain ⟨C, hCX, hCY, hmin, huniq⟩ := BPrimeE0.existsUnique_causality_e0 hcov
  refine ⟨C, ⟨hCX, hCY, hmin⟩, fun C' hC' => huniq C' hC'.2.2 fun x => ?_⟩
  by_cases hx : x ∈ Reg (Flat.isom 2) (Minkowski 2) M
  · obtain ⟨e, he, hxe⟩ := mem_support.1 hx
    exact Or.inl ⟨e, he, hxe, hC'.1 e he⟩
  · obtain ⟨e, he, hxe⟩ := hcov x hx
    exact Or.inr ⟨e, he, hxe, hC'.2.1 e he⟩

variable (M) in
/-- **`sing_α(M)` of an `E₀`-manifold**: `Sing(M)` at `α = 0`, empty otherwise. -/
def sing (α : ℝ) : Set M := if α = 0 then Sing (Flat.isom 2) (Minkowski 2) M else ∅

theorem sing_zero : sing M 0 = Sing (Flat.isom 2) (Minkowski 2) M := if_pos rfl

theorem sing_of_ne {α : ℝ} (hα : α ≠ 0) : sing M α = ∅ := if_neg hα

/-- **Every `X_A`-chart reads `Sing(M)` as BTZ points**: a chart into `E₀` sends a point of its
source to the axis iff the point is singular. -/
theorem mem_axis_iff {e : OpenPartialHomeomorph M E0} (he : IsAEChart (Flat.isom 2) (Minkowski 2) e)
    {x : M} (hx : x ∈ e.source) : e x ∈ E0.axis ↔ x ∈ Sing (Flat.isom 2) (Minkowski 2) M := by
  have h := he.mem_reg_iff hx
  rw [E0GX.reg_eq] at h
  show _ ↔ x ∉ Reg (Flat.isom 2) (Minkowski 2) M
  rw [h, mem_compl_iff, not_not]

/-- **`sing₀(M) = Sing(M)`**: the singular points are the points some `X_A`-chart sends to the
axis of `E₀`. -/
theorem sing_eq_btzPoints (hcov : E0Covered M) :
    sing M 0 = {x | ∃ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
      x ∈ e.source ∧ e x ∈ E0.axis} := by
  rw [sing_zero]
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, hxe⟩ := hcov x hx
    exact ⟨e, he, hxe, (mem_axis_iff he hxe).2 hx⟩
  · rintro ⟨e, he, hxe, hax⟩
    exact (mem_axis_iff he hxe).1 hax

variable {C : Causality M}

theorem isAtlasCausalityDEC25 (hC : IsE0Natural C) :
    IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) (fun _ : Unit => E0.causality) := by
  exact ⟨hC.1, fun _ e he => hC.2.1 e he, hC.2.2⟩

theorem isoChartsCoverDEC25 (hcov : E0Covered M) (hC : IsE0Natural C) :
    IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) (fun _ : Unit => E0.causality) := by
  refine (isAtlasCausalityDEC25 hC).isoChartsCover fun x hx => ?_
  obtain ⟨e, he, hxe⟩ := hcov x hx
  exact ⟨(), e, he, hxe⟩

theorem isoChartsCover (hcov : E0Covered M) (hC : IsE0Natural C) :
    IsoChartsCover C (minkowski 2) (fun _ : Unit => E0.causality) := by
  exact isoChartsCover_of_dec25 (isoChartsCoverDEC25 hcov hC)

/-- `Z⁺` in every open set of an `E₀`-manifold. -/
theorem locZplus (hcov : E0Covered M) (hC : IsE0Natural C) : E0LM.LocZplus C := by
  exact IsoChartsCover.locZplus (isoChartsCover hcov hC) (minkowski_locZplus 2)
    fun _ => E0LM.e0_locZplus

/-- `rem:btz_pas_tarentin`, first half, at `E₀`-manifolds (unmarked): every point is strongly
tarentin in the future. -/
theorem mem_Zplus (hcov : E0Covered M) (hC : IsE0Natural C) (p : M) : p ∈ C.Zplus := by
  exact IsoChartsCover.mem_Zplus (isoChartsCover hcov hC) (minkowski_locZplus 2)
    (fun _ => E0LM.e0_locZplus) p

/-- Tarentin in every open set of an `E₀`-manifold. -/
theorem locTarentin (hcov : E0Covered M) (hC : IsE0Natural C) : E0LM.LocTarentin C := by
  exact IsoChartsCover.locTarentin (isoChartsCover hcov hC) (minkowski_locTarentin 2)
    fun _ => E0LM.e0_locTarentin

/-- `rem:sing_tarentin` at `E₀`-manifolds (unmarked): tarentin; « topological spacetime » is the
carried Hausdorff and second countable hypotheses (SCOPE). -/
theorem tarentin (hcov : E0Covered M) (hC : IsE0Natural C) : C.Tarentin := by
  exact IsoChartsCover.tarentin (isoChartsCover hcov hC) (minkowski_locTarentin 2)
    fun _ => E0LM.e0_locTarentin

/-- `Z⁻` off `sing₀(M)` in every open set of an `E₀`-manifold (the regular points only: no
`E0Covered` needed). -/
theorem locZminus (hC : IsE0Natural C) : E0LM.LocZminus C (sing M 0) := by
  rw [sing_zero]
  refine locZminus_of_charts (SX := ∅) (SY := fun _ : Unit => E0.axis) (fun x hx => ?_)
    (minkowski_locZminus 2) fun _ => E0LM.e0_locZminus
  have hxr : x ∈ Reg (Flat.isom 2) (Minkowski 2) M := by
    by_contra h
    exact hx h
  obtain ⟨e, he, hxe⟩ := mem_support.1 hxr
  exact Or.inl ⟨e, hxe, hC.1 e he, notMem_empty _⟩

/-- **`M ∖ sing₀(M) ⊆ Z⁻`**. -/
theorem mem_Zminus_of_notMem (hC : IsE0Natural C) {p : M} (hp : p ∉ sing M 0) :
    p ∈ C.Zminus := by
  intro U hU
  obtain ⟨z, hzU, hz⟩ := locZminus hC ⊤ p trivial hp U hU
  exact ⟨z, Precausality.mem_Iminus_singleton.2 hz, hzU⟩

/-- **`past_local`**: at a BTZ point, the causal past in an `X_A`-chart stays in `sing₀(M)`. -/
theorem pastLocal (hcov : E0Covered M) (hC : IsE0Natural C) :
    ∀ p ∈ sing M 0, ∃ U : Opens M, p ∈ U ∧ ∀ q, C.le U q p → q ∈ sing M 0 := by
  rw [sing_zero]
  intro p hp
  obtain ⟨e, he, hpe⟩ := hcov p hp
  exact ChartIso.pastLocal (hC.2.1 e he) E0LM.e0_locPastIn
    (fun q hq hqa => (mem_axis_iff he hq).1 hqa) hpe ((mem_axis_iff he hpe).2 hp)

/-- **`I⁻(p) = ∅` at every BTZ point**, from absolute minimality and the empty past of the axis
of `E₀` in every open set. -/
theorem Iminus_eq_empty (hcov : E0Covered M) (hC : IsE0Natural C) :
    ∀ p ∈ sing M 0, C.Iminus ⊤ {p} = ∅ := by
  rw [sing_zero]
  intro p hp
  refine Iminus_eq_empty_of_cover hC.2.2
    (S := {O | (∃ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, O = chartSource e) ∨
      ∃ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        O = chartSource e}) (fun y => ?_) ?_
  · by_cases hy : y ∈ Reg (Flat.isom 2) (Minkowski 2) M
    · obtain ⟨e, he, hye⟩ := mem_support.1 hy
      exact ⟨chartSource e, Or.inl ⟨e, he, rfl⟩, hye⟩
    · obtain ⟨e, he, hye⟩ := hcov y hy
      exact ⟨chartSource e, Or.inr ⟨e, he, rfl⟩, hye⟩
  · rintro O (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) hpO z
    · exact absurd (mem_support.2 ⟨e, he, hpO⟩) hp
    · exact ChartIso.not_lt_left (hC.2.1 e he) E0LM.e0_locNoPast ((mem_axis_iff he hpO).2 hp)
        le_rfl z

/-- `rem:btz_pas_tarentin`, second half, at `E₀`-manifolds (unmarked): the points not strongly
tarentin in the past are exactly the BTZ points. -/
theorem mem_Zminus_iff (hcov : E0Covered M) (hC : IsE0Natural C) (p : M) :
    p ∈ C.Zminus ↔ p ∉ sing M 0 := by
  exact ⟨fun h hp => notMem_Zminus_of_Iminus_eq_empty (Iminus_eq_empty hcov hC p hp) h,
    mem_Zminus_of_notMem hC⟩

/-- An `E₀`-manifold is locally compact. -/
theorem locallyCompactSpace (hcov : E0Covered M) : LocallyCompactSpace M := by
  refine ⟨fun x n hn => ?_⟩
  by_cases hx : x ∈ Reg (Flat.isom 2) (Minkowski 2) M
  · obtain ⟨e, -, hxe⟩ := mem_support.1 hx
    exact exists_isCompact_nhds_of_chart e hxe hn
  · obtain ⟨e, -, hxe⟩ := hcov x hx
    exact exists_isCompact_nhds_of_chart e hxe hn

/-- An `E₀`-manifold has no isolated point. -/
theorem nhdsNE_neBot (hcov : E0Covered M) (p : M) : (𝓝[≠] p).NeBot := by
  by_cases hp : p ∈ Reg (Flat.isom 2) (Minkowski 2) M
  · obtain ⟨e, -, hpe⟩ := mem_support.1 hp
    exact nhdsNE_neBot_of_chart e hpe inferInstance
  · obtain ⟨e, -, hpe⟩ := hcov p hp
    exact nhdsNE_neBot_of_chart e hpe inferInstance

/-- A Hausdorff, second countable `E₀`-manifold is metrizable. -/
theorem metrizableSpace [T2Space M] [SecondCountableTopology M] (hcov : E0Covered M) :
    MetrizableSpace M := by
  haveI := locallyCompactSpace hcov
  exact metrizableSpace_of_locallyCompact

/-- `sing_α(M)` is closed. -/
theorem isClosed_sing : ∀ α : ℝ, 0 ≤ α → IsClosed (sing M α) := by
  intro α _
  by_cases hα : α = 0
  · subst hα
    rw [sing_zero]
    exact Causal.isClosed_sing (Flat.isom 2) (Minkowski 2) M
  · rw [sing_of_ne hα]
    exact isClosed_empty

/-- `sing_α(M)` has empty interior. -/
theorem interior_sing : ∀ α : ℝ, 0 ≤ α → interior (sing M α) = ∅ := by
  intro α _
  by_cases hα : α = 0
  · subst hα
    rw [sing_zero]
    exact (isSkeletal_sing (Flat.isom 2) (Minkowski 2) M).interior_eq_empty
  · rw [sing_of_ne hα]
    exact interior_empty

/-- `cor:pushup_sing` at `E₀`-manifolds (from `Causal.pushup_sing_dec25_of_isoChartsCover`). -/
theorem pushUp (hcov : E0Covered M) (hC : IsE0Natural C) : C.PushUp := by
  exact pushup_sing_dec25_of_isoChartsCover minkowski_causallyArcConnected
    (fun _ => E0.causallyArcConnected) minkowski_pushUp (fun _ => E0LM.e0_pushUp) hC.2.2
    (isoChartsCoverDEC25 hcov hC)

/-- `cor:massA_cac` at `E₀`-manifolds (from `Causal.massA_cac_dec25_of_isoChartsCover`). -/
theorem causallyArcConnected (hcov : E0Covered M) (hC : IsE0Natural C) :
    C.CausallyArcConnected := by
  exact massA_cac_dec25_of_isoChartsCover minkowski_causallyArcConnected
    (fun _ => E0.causallyArcConnected) hC.2.2 (isoChartsCoverDEC25 hcov hC)

/-- **An `E₀`-manifold is causally plain** (`defi:causalement_plat`; OQ-16), by
`Causality.causallyPlain_of_locZ`: push-up, `Z⁺` in every open set, `Z⁻` off `sing₀(M)`, which
has empty interior. -/
theorem causallyPlain (hcov : E0Covered M) (hC : IsE0Natural C) : C.CausallyPlain := by
  exact Causality.causallyPlain_of_locZ (pushUp hcov hC) (locZplus hcov hC) (locZminus hC)
    (interior_sing 0 le_rfl)

/-- **`SingularFlatAxioms` at a Hausdorff, second countable `E₀`-manifold is exactly the three BTZ
fields not proved here**: every other field is discharged. -/
theorem singularFlatAxioms_iff [T2Space M] [SecondCountableTopology M] (hcov : E0Covered M)
    (hC : IsE0Natural C) :
    C.SingularFlatAxioms (sing M) ↔
      (∀ p ∈ sing M 0, C.SingularPastAt p) ∧
      (∀ p ∈ sing M 0, ∀ p' ∈ sing M 0, C.le ⊤ p p' → p ≠ p' →
        C.Jplus ⊤ {p'} \ sing M 0 ⊆ C.Iplus ⊤ {p}) ∧
      (∀ p ∈ sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
        C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (sing M 0) p) := by
  constructor
  · intro h
    exact ⟨h.singularPastAt, h.Iplus_of_lt, h.line⟩
  · rintro ⟨h1, h2, h3⟩
    exact
      { singularPastAt := h1
        Iminus_eq_empty := Iminus_eq_empty hcov hC
        Iplus_of_lt := h2
        past_local := pastLocal hcov hC
        line := h3
        pushUp := pushUp hcov hC
        absolutelyMinimal := hC.2.2
        causallyArcConnected := causallyArcConnected hcov hC
        tarentin := tarentin hcov hC
        mem_Zplus := mem_Zplus hcov hC
        mem_Zminus_iff := mem_Zminus_iff hcov hC
        t2 := inferInstance
        secondCountable := inferInstance
        metrizable := metrizableSpace hcov
        locallyCompact := locallyCompactSpace hcov
        noIsolated := nhdsNE_neBot hcov
        isClosed_sing := isClosed_sing
        interior_sing := interior_sing
        massive_line := fun α hα p hp => by
          rw [sing_of_ne hα.ne'] at hp
          exact absurd hp (notMem_empty p) }

end E0Manifold

/-! ### The witness: `E₀` itself -/

section Witness

attribute [local instance] E0GX.singularGX

/-- `E₀`'s `sing` is `Causal.E0.singE0`. -/
theorem sing_e0 : sing E0 = E0.singE0 := by
  funext α
  by_cases hα : α = 0
  · subst hα
    rw [sing_zero, E0.singE0_zero, E0GX.sing_eq]
  · rw [sing_of_ne hα, E0.singE0_of_ne hα]

/-- **Non-vacuity** (kb/0011): `E₀` with `E0GX.singularGX` is an `E₀`-manifold, `E0.causality`
is its natural causality, and `sing₀(E₀)` is the axis, non-empty. -/
theorem nonvacuous :
    E0Covered E0 ∧ IsE0Natural E0.causality ∧ sing E0 0 = E0.axis ∧ (sing E0 0).Nonempty := by
  obtain ⟨-, -, -, hne, hcov, hX, hY, hmin⟩ := BPrimeE0.nonvacuous 0 0
  have h0 : sing E0 0 = E0.axis := by rw [sing_zero, E0GX.sing_eq]
  exact ⟨hcov, ⟨hX, hY, hmin⟩, h0, by rw [sing_zero]; exact hne⟩

/-- `singularFlatAxioms_iff` is satisfiable with a BTZ point: `E0.causality` is
`SingularFlatAxioms (sing E0)`. -/
theorem e0_singularFlatAxioms : E0.causality.SingularFlatAxioms (sing E0) := by
  rw [sing_e0]
  exact E0.singularFlatAxioms

/-- **Read in a chart is not enough for the BTZ half: absolute minimality is needed** (kb/0014).
`topTotal E0.causality` (`E0.causality` on every open set `≠ E₀`, every pair related at `E₀`) has
an isomorphic chart into `E₀` at every point (the identity restricted to the complement of a
point), so `Z⁺ = E₀` and it is tarentin by the transfer; yet every point, the axis included, is
strongly tarentin in the past, and it is not absolutely minimal. -/
theorem e0_topTotal_separates :
    IsoChartsCover (topTotal E0.causality) (minkowski 2) (fun _ : Unit => E0.causality) ∧
      (∀ p, p ∈ (topTotal E0.causality).Zplus) ∧ (topTotal E0.causality).Tarentin ∧
      (∀ p : E0, p ∈ (topTotal E0.causality).Zminus) ∧
      ¬ (topTotal E0.causality).AbsolutelyMinimal := by
  have hne : ∀ x : E0, ∃ y : E0, y ≠ x := fun x =>
    ⟨(x.1 + 1, x.2), fun h => by
      have h1 := congrArg Prod.fst h
      simp at h1⟩
  have hcov : IsoChartsCover (topTotal E0.causality) (minkowski 2)
      (fun _ : Unit => E0.causality) := by
    intro x
    obtain ⟨y, hyx⟩ := hne x
    refine Or.inr ⟨(), (OpenPartialHomeomorph.refl E0).restrOpen ({y}ᶜ) isOpen_compl_singleton,
      by simpa using hyx.symm, chartIso_topTotal (chartIso_restrOpen_refl E0.causality _) ?_⟩
    intro h
    have hy : y ∈ chartSource
        ((OpenPartialHomeomorph.refl E0).restrOpen ({y}ᶜ) isOpen_compl_singleton) :=
      h ▸ (trivial : y ∈ (⊤ : Opens E0))
    simp [mem_chartSource] at hy
  refine ⟨hcov, IsoChartsCover.mem_Zplus hcov (minkowski_locZplus 2) fun _ => E0LM.e0_locZplus,
    IsoChartsCover.tarentin hcov (minkowski_locTarentin 2) (fun _ => E0LM.e0_locTarentin),
    topTotal_mem_Zminus _, fun hmin => ?_⟩
  have hp : ((0 : ℝ), (0 : ℂ)) ∈ E0.axis := rfl
  refine notMem_Zminus_of_Iminus_eq_empty (Iminus_eq_empty_of_cover hmin (S := {O | O ≠ ⊤})
    (fun y => ?_) fun O hO _ z hz => E0LM.e0_locNoPast O _ hp z ((topTotal_lt_iff hO).1 hz))
    (topTotal_mem_Zminus _ _)
  obtain ⟨z, hzy⟩ := hne y
  refine ⟨⟨{z}ᶜ, isOpen_compl_singleton⟩, fun h => ?_, hzy.symm⟩
  have hz : z ∈ (⟨{z}ᶜ, isOpen_compl_singleton⟩ : Opens E0) := h ▸ (trivial : z ∈ (⊤ : Opens E0))
  exact hz rfl

end Witness

end SFALocalE0

end Causal
