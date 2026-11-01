import CausalScaffold.CBG.FromModel
import CausalScaffold.CBG.Maximal
import CausalScaffold.Flat.GerochFlat
import CausalScaffold.Flat.SecondCountable
import CausalScaffold.Flat.LipschitzGraph
import CausalScaffold.Flat.Developing
import CausalScaffold.Flat.CauchyComplete

/-!
# The flat instance of the CBG campaign: the local model `Minkowski d`, and `flat_cbg`

Package 12 of the CBG campaign (design `docs/CBG-DESIGN.md` §4 "Flat instance", §5 row 12).
**No label is marked** (`docs/CBG-DESIGN.md:5–6`: « marking ETT labels is the ETT campaign's;
rows stay partial until the singular instance discharges the model »). Cited, unmarked: `theo:CBG` —
`ETT.tex:1884`; `rem:CBG_manquant` — `ETT.tex:2343`; thesis `theo:Cauchy_ext` (`these.tex:6287`),
`prop:GX_liouville` (`these.tex:1476`); Sbierski 1309.7591, Thm 2.8, Thm 3.6 / (3.12).

> Let $M_0$ be a globally hyperbolic singular flat spacetime. Then $M_0$ admits a maximal Cauchy
> extension, and that extension is unique up to isomorphism. (`theo:CBG`, `ETT.tex:1885–1886`)

> Theorem 2.8 (Existence of MGHD). Given initial data there exists a GHD $\tilde M$ that is an
> extension of any other GHD of the same initial data. (Sbierski, p. 12)

> (Isom, 𝐌)-manifolds: `Str` = ChartedSpace + HasGroupoid; `IsMor` = `IsLocalIsometry`; A1
> `IsGXMorphism.eq_of_eqOn` + `isAnalyticAction_isom`; A3 trivial (one g on a connected V); A4
> hyperboloid level sets of τ_q(r) = √(−Q(q−r)) in a chart; A2 Minkowski facts, CurvesExtend,
> DEC-49. (design §4)

## What is proved

* **The flat local model** `flatModelOf d hJ₁ hJ₂ : LocalModel.{0}` — `Y = Minkowski d`,
  `G = gxGroupoid (isom d) (Minkowski d)`, `causalityY = minkowski d`, `singY = ∅` — with **every
  field proved** except the two compactness fields `isCompact_Jplus_inter_Jminus`,
  `isCompact_Jminus_inter_Jplus`, taken as the hypotheses `hJ₁`, `hJ₂`
  (`FlatCompactJplusJminus d`, `FlatCompactJminusJplus d`). Field by field:
  - B1 `rigid` (`flat_rigid`): an element of the isometry groupoid is one isometry on a
    preconnected subset of its source (`exists_smul_eqOn_of_eventually`, an open–closed argument
    on the rigid action `isAnalyticAction_isom`).
  - B2 `localUnique_sing`: vacuous (`singY = ∅`); `localUnique_reg` (`flat_localUnique_reg`): an
    injective local structomorphism on a connected open set is one isometry `g`, and the element
    of `G` is `isomChart g` (source `univ`); `regularChart`: `refl`.
  - B3 `absolutelyMinimalOn_Y`, `chartIso_mem` (through `flatCausality_self`, the groupoid
    inside the maximal atlas of the model), `sing_mem` (vacuous).
  - B3 `singularFlatAxioms` (`flat_singularFlatAxiomsCorr`): the corrected bundle with
    `sing = ∅` — the BTZ fields and `massive_line` are vacuous, `isClosed_sing`/`interior_sing`
    are those of `∅`, `mem_Zminus_iff` becomes `Z⁻ = M`; push-up, `Z^±`, tarentin, causal
    arc-connectedness from `Flat/Geroch/Reach`, `Flat/TheoremBInputs`, `Flat/CauchyComplete`;
    `noIsolated` and metrizability from the charts.
  - B3 `curvesExtend` (`flat_curvesExtend`): **without** global hyperbolicity, from the chronal
    causal flow (`flat_hasChronalCausalFlow`, `curvesExtend_of_isCausalFlow`).
  - B3 `secondCountable_of_cauchy`: outright, `flat_secondCountableTopology` (DEC-49).
  - B4 `slice_future`, `slice_past` (`minkowski_slice_future`, `minkowski_slice_past`): **not the
    hyperboloids of the design** — the time coordinate `∓ t` on a small diamond
    `I⁺(y − ε e₀) ∩ I⁻(y + ε e₀)`; the level set at `t = c` is a Cauchy surface of the diamond
    over it (its domain of dependence), through `isCauchySurfaceOn_graph_of_saturated`
    (`Flat/LipschitzGraph`) for the constant graph, global hyperbolicity by causal convexity
    (`GloballyHyperbolicOn.of_causallyConvexIn`).
* **The bridge** `chartedCausality_eq_flatCausality`: the causality the Level-B atlas generates is
  `flatCausality d M` (the two make the same preferred charts isomorphisms, both are absolutely
  minimal on every open set).
* **The time-function field** of interface round 2 (`Geometry.HasTimeFunctions`, design §6):
  `flat_hasTimeFunction` — the Geroch time of the admissible measures of `Flat/GerochFlat` —
  and `flatGeometryOf_hasTimeFunctions`, so the one `sorry` of `CBG/Maximal`'s `cbg_proof`
  (the missing field) does not reach the flat instance.
* **`flat_cbg_of`** (sorry-free): for a GH flat spacetime with a Cauchy surface, a universal
  Cauchy development exists in the geometry `Geometry.ofLocalModelOfGermSlice (flatModelOf d hJ₁
  hJ₂) hA3f hA3p hA4f hA4p`, i.e. **under the two compactness hypotheses and A3/A4 for the flat
  model** — via `cbg_of_hasTimeFunctions` (`CBG/Maximal`). `flat_cbg_gh_of` drops the Cauchy
  surface (it is `flatGerochGH`).
* **`flat_cbg`**, `flat_cbg_gh`: the same in `flatGeometry d := Geometry.ofLocalModel (flatModel
  d)`, resting on the two tagged compactness `sorry`s here and on `CBG/FromModel`'s four tagged
  A3/A4 `sorry`s (`LocalModel.germExtFuture`, `germExtPast`, `sliceFuture`, `slicePast`).
  Witness: `flat_cbg_minkowski` (`M₀ = Minkowski d`).
* **The ETT/Barbot reading** `flat_cbg_ett_of` (sorry-free, same hypotheses as `flat_cbg_gh_of`)
  and `flat_cbg_ett`: an ETT-maximal development exists and is unique up to unique isomorphism —
  the « unique up to isomorphism » half of `theo:CBG`, from `Dev.IsUniversal.existsUnique_iso`.
* General: `exists_smul_eqOn_of_eventually` (rigid actions), `eventually_smul_of_mem_gxGroupoid`,
  `isomChart_mem_gxGroupoid`, `isCauchySurfaceOn_congr`, the Minkowski diamonds `mdiamond`
  (causally convex, GH, sliced by `t = c` into Cauchy surfaces).

## Hypothesis checklist

| paper / design | here |
|---|---|
| `M₀` globally hyperbolic **singular** flat (`theo:CBG`, `ETT.tex:1885`) | ⚠ strengthened: **regular flat only** (`singY = ∅`); the singular `E₀` instance is gx's. Otherwise `flat_cbg_gh`: `M₀` T2, connected, an `(Isom, 𝐌)`-manifold, `flatCausality d M₀` GH (ETT's GH); the Cauchy surface is **derived** (`flatGerochGH`), second countability **derived** (DEC-49) |
| "maximal" | DEC-59: `Dev.IsUniversal`; ETT/Barbot reading `Dev.IsETTMaximal` in `flat_cbg_ett_of`/`flat_cbg_ett` |
| "unique up to isomorphism" (`ETT.tex:1886`) | ✓ `Dev.IsUniversal.unique` (`CBG/Geometry`) / `Dev.IsUniversal.existsUnique_iso` (`CBG/Maximal`), sorry-free, no rigidity; stated for the flat instance in `flat_cbg_ett_of` (sorry-free) and `flat_cbg_ett` |
| design §4 `IsMor = IsLocalIsometry` | ⚠ reading: `LocalModel.IsMor` (`LiftPropOn G.IsLocalStructomorphWithinAt`), the interface's; its identification with `IsLocalIsometry` is not proved here |
| design §4 A4 "hyperboloid level sets of `τ_q`" | ⚠ replaced: B4 only asks a local time with Cauchy level sets; the flat time `∓t` on a diamond satisfies it. The `τ_q` property Sbierski uses — « `τ_q(r)` is only greater than zero for `r ∈ J⁻(q)` » (Sbierski p. 19, pdftotext l. 983), keeping `S ⊆ Ū ∩ J⁺(ι(M))` (overline lost by pdftotext) — is used in the **proof of Thm 3.6** (not in Lemma 3.11, which only produces `q`); it is A4's (`CBG/FromModel`'s `sliceFuture`), not B4's, and the flat-time inhabitant of B4 lacks it (SCOPE: the 1+1 example) |
| design §4 A3 "trivial (one `g` on a connected `V`)" | ⚠ not derived here: A3 is `CBG/FromModel`'s `germExtFuture`/`germExtPast` (tagged `sorry` there, for every model); this file proves its B2 input (`flat_localUnique_reg`) and carries A3 as a hypothesis in `flat_cbg_of` |
| design §4 A2 `isCompact_*` ("flat GH") | ✗ not proved: `FlatCompactJplusJminus`/`FlatCompactJminusJplus`, hypotheses of `flatModelOf`, tagged `sorry` in `flatModel` |

## SCOPE (disclosed)

* **What `flat_cbg` rests on.** Two tagged `sorry`s in this file — `flat_isCompact_Jplus_inter_Jminus`,
  `flat_isCompact_Jminus_inter_Jplus` (R1: `J⁺(Σ) ∩ J⁻(p)` compact in a GH flat spacetime with
  Cauchy surface `Σ`; needs `J⁻(p) ∩ Σ` compact and a finite cover by diamonds, absent from the
  library) — and the four of `CBG/FromModel` (A3/A4 from Level B, for every local model). The
  conditional forms `flat_cbg_of`, `flat_cbg_gh_of` are sorry-free.
* **B4 carries no localisation to `J⁻(q)`** (finding, for packages 6/11). In 1+1 Minkowski take
  `U = {t < −|x|/2}`, `Σ = {t = −1 − |x|/2}`, `p = 0`, `q = (δ, 0)`. On
  `K = J⁻(q) ∩ Uᶜ ∩ J⁺(Σ)` the flat time `τ = −t` of B4 is maximal at `t = −δ`, attained at
  `x = ±2δ` on `∂U`; but the level set `{t = −δ} ∩ W` of a diamond `W ⊇ K` of radius `ε` enters
  `int(Uᶜ)` for `2δ < |x| < ε − δ`. So a derivation of A4 from B4 (`CBG/FromModel`'s `sliceFuture`)
  cannot use B4's piece `N` whole: it must take `U ∪ (N ∩ I⁻(q))`, or B4 needs a localisation
  clause. The B4 field as approved is proved correctly here; this is a caution on its use.
* **Universe.** `Minkowski d : Type`, so the model is `LocalModel.{0}` and `flat_cbg` is for
  `M₀ : Type`; every development is quantified in `Type` (`Dev`).
* **No identification of `LocalModel.IsMor` with `IsLocalIsometry`** (`Flat/FlatSpacetime`); the
  development morphisms are the interface's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace ChartedSpace StructureGroupoid Flat

namespace CBG

variable {d : ℕ}

/-! ### §1 One isometry on a preconnected set -/

section Rigid

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]

/-- **Locally one element ⇒ one element on a preconnected set**, for a rigid action: if near every
point of the preconnected `U` the map `f` is the action of some element of `G`, it is the action
of one element on all of `U`. -/
theorem exists_smul_eqOn_of_eventually [IsRigidAction G X] {f : X → X} {U : Set X}
    (hU : IsPreconnected U) (hne : U.Nonempty)
    (hloc : ∀ y ∈ U, ∃ g : G, ∀ᶠ z in 𝓝 y, f z = g • z) :
    ∃ g : G, ∀ y ∈ U, f y = g • y := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨g₀, hg₀⟩ := hloc y₀ hy₀
  let u : Set X := {y | ∀ᶠ z in 𝓝 y, f z = g₀ • z}
  let v : Set X := {y | ∃ g : G, (∀ᶠ z in 𝓝 y, f z = g • z) ∧ ∃ p : X, g • p ≠ g₀ • p}
  have hu : IsOpen u := isOpen_setOf_eventually_nhds
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨g, hg, hne⟩
    filter_upwards [hg.eventually_nhds] with y' hy' using ⟨g, hy', hne⟩
  have hcover : U ⊆ u ∪ v := by
    intro y hy
    obtain ⟨g, hg⟩ := hloc y hy
    by_cases hgg : ∀ p : X, g • p = g₀ • p
    · left
      filter_upwards [hg] with z hz
      rw [hz, hgg]
    · right
      obtain ⟨p, hp⟩ := not_forall.1 hgg
      exact ⟨g, hg, p, hp⟩
  have hdisj : U ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨_, hyu, g, hg, p, hp⟩ => hp ?_
    have hev : ∀ᶠ z in 𝓝 y, g • z = g₀ • z := by
      filter_upwards [hyu, hg] with z h1 h2
      rw [← h2]; exact h1
    obtain ⟨t, ht, hto, hyt⟩ := mem_nhds_iff.1 hev
    exact IsRigidAction.smul_eq_of_eqOn hto ⟨y, hyt⟩ (fun z hz => ht hz) p
  rcases isPreconnected_iff_subset_of_disjoint.1 hU u v hu hv hcover
    (by rw [← subset_empty_iff, ← hdisj]) with hUu | hUv
  · exact ⟨g₀, fun y hy => (hUu hy).self_of_nhds⟩
  · have : y₀ ∈ U ∩ (u ∩ v) := ⟨hy₀, hg₀, hUv hy₀⟩
    rw [hdisj] at this
    exact this.elim

end Rigid

/-- An element of `gxGroupoid` is near each point of its source the action of an element. -/
theorem eventually_smul_of_mem_gxGroupoid {G : Type*} {X : Type*} [TopologicalSpace X] [Group G]
    [MulAction G X] [ContinuousConstSMul G X] {e : OpenPartialHomeomorph X X}
    (he : e ∈ gxGroupoid G X) {x : X} (hx : x ∈ e.source) :
    ∃ g : G, ∀ᶠ z in 𝓝 x, e z = g • z := by
  obtain ⟨g, hg⟩ := (mem_gxGroupoid_iff.1 he).1 x hx
  exact ⟨g, hg⟩

/-- An isometry, as a chart defined everywhere, lies in the isometry groupoid. -/
theorem isomChart_mem_gxGroupoid (g : isom d) :
    isomChart g ∈ gxGroupoid (isom d) (Minkowski d) := by
  refine mem_gxGroupoid_iff.2 ⟨fun x _ => ⟨g, Eventually.of_forall fun _ => rfl⟩,
    fun x _ => ⟨g⁻¹, Eventually.of_forall fun y => ?_⟩⟩
  apply (isom.toHomeomorph g).injective
  show (isom.toHomeomorph g) ((isom.toHomeomorph g).symm y) = (isom.toHomeomorph g) (g⁻¹ • y)
  rw [Homeomorph.apply_symm_apply, isom.coe_toHomeomorph]
  exact (smul_inv_smul g y).symm

/-! ### §2 The fields B1, B2, B3 (model part) of the flat local model -/

section ModelFields

/-- **B1 for the isometry groupoid**: two elements of `gxGroupoid (isom d) (Minkowski d)` agreeing
on a non-empty open subset of a preconnected open set inside both sources agree on it. -/
theorem flat_rigid : ∀ e ∈ gxGroupoid (isom d) (Minkowski d),
    ∀ e' ∈ gxGroupoid (isom d) (Minkowski d), ∀ U : Set (Minkowski d), IsOpen U →
      IsPreconnected U → U ⊆ e.source → U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty →
        EqOn e e' O → EqOn e e' U := by
  intro e he e' he' U _ hUc hUe hUe' O hOU hO hOne heq
  obtain ⟨g, hg⟩ := exists_smul_eqOn_of_eventually (G := isom d) hUc (hOne.mono hOU)
    fun y hy => eventually_smul_of_mem_gxGroupoid he (hUe hy)
  obtain ⟨g', hg'⟩ := exists_smul_eqOn_of_eventually (G := isom d) hUc (hOne.mono hOU)
    fun y hy => eventually_smul_of_mem_gxGroupoid he' (hUe' hy)
  have hgg : ∀ p : Minkowski d, g • p = g' • p := IsRigidAction.smul_eq_of_eqOn hO hOne
    fun z hz => (hg z (hOU hz)).symm.trans ((heq hz).trans (hg' z (hOU hz)))
  intro y hy
  rw [hg y hy, hg' y hy, hgg]

/-- **B2 on a regular component, flat**: an injective local structomorphism of the isometry
groupoid on a connected open set is one isometry `g` there, and `isomChart g` is defined on all
of `Minkowski d`. Injectivity and the `MapsTo` hypothesis are not used. -/
theorem flat_localUnique_reg : ∀ U : Set (Minkowski d), IsOpen U → IsConnected U →
    (∀ y ∈ U, ∀ z ∈ connectedComponent y, ∀ α : ℝ, 0 ≤ α → z ∉ (fun _ => (∅ : Set (Minkowski d))) α) →
    ∀ f : Minkowski d → Minkowski d,
    (∀ y ∈ U, (gxGroupoid (isom d) (Minkowski d)).IsLocalStructomorphWithinAt f U y) → InjOn f U →
    MapsTo f U {z | ∀ w ∈ connectedComponent z, ∀ α : ℝ, 0 ≤ α →
      w ∉ (fun _ => (∅ : Set (Minkowski d))) α} →
    ∃ e ∈ gxGroupoid (isom d) (Minkowski d), (∀ y ∈ U, connectedComponent y ⊆ e.source) ∧
      EqOn f e U := by
  intro U hUo hUc _ f hf _ _
  have hloc : ∀ y ∈ U, ∃ g : isom d, ∀ᶠ z in 𝓝 y, f z = g • z := by
    intro y hy
    obtain ⟨e, he, hfe, hye⟩ := hf y hy hy
    obtain ⟨g, hg⟩ := eventually_smul_of_mem_gxGroupoid he hye
    refine ⟨g, ?_⟩
    filter_upwards [hg, hUo.mem_nhds hy, e.open_source.mem_nhds hye] with z hz hzU hze
    rw [hfe ⟨hzU, hze⟩]; exact hz
  obtain ⟨g, hg⟩ := exists_smul_eqOn_of_eventually hUc.isPreconnected hUc.nonempty hloc
  exact ⟨isomChart g, isomChart_mem_gxGroupoid g, fun _ _ => by simp, fun y hy => hg y hy⟩

/-- **B3, `absolutelyMinimalOn_Y`**: `minkowski d` is absolutely minimal on every open set. -/
theorem minkowski_absolutelyMinimalOn (W : Opens (Minkowski d)) :
    (minkowski d).AbsolutelyMinimalOn W := by
  have := flatCausality_absolutelyMinimalOn (d := d) (M := Minkowski d) W
  rwa [flatCausality_self] at this

/-- **B3, `chartIso_mem`**: every element of the isometry groupoid is a `ChartIso` of
`minkowski d` (it lies in the maximal atlas of the model, `flatCausality_self`). -/
theorem minkowski_chartIso_of_mem {e : OpenPartialHomeomorph (Minkowski d) (Minkowski d)}
    (he : e ∈ gxGroupoid (isom d) (Minkowski d)) : ChartIso (minkowski d) (minkowski d) e := by
  have := flatCausality_chartIso (d := d) (M := Minkowski d)
    ((gxGroupoid (isom d) (Minkowski d)).mem_maximalAtlas_of_mem_groupoid he)
  rwa [flatCausality_self] at this

end ModelFields

/-! ### §3 The generated causality of a flat atlas is `flatCausality` -/

section Bridge

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- **The bridge**: the causality generated by the atlas (`chartedCausality`, Level B) is
`flatCausality d M` — the preferred charts are isomorphisms for both, both are absolutely minimal
on `⊤`, so they agree near every point and hence everywhere (`imp_of_agree_locally`). -/
theorem chartedCausality_eq_flatCausality :
    chartedCausality (minkowski d) M = flatCausality d M := by
  have hGD : ∀ e ∈ gxGroupoid (isom d) (Minkowski d), ChartIso (minkowski d) (minkowski d) e :=
    fun e he => minkowski_chartIso_of_mem he
  have h1 := chartedCausality_chartIso (M := M) hGD minkowski_absolutelyMinimalOn
  have hagree : ∀ x : M, AgreeOn (chartedCausality (minkowski d) M) (flatCausality d M)
      (chartSource (chartAt (Minkowski d) x)) := fun x V hV a b =>
    (h1 x).agree (flatCausality_chartIso_chartAt x) hV a b
  have hA1 := chartedCausality_absolutelyMinimalOn (M := M) hGD minkowski_absolutelyMinimalOn ⊤
  have hA2 := flatCausality_absolutelyMinimalOn (d := d) (M := M) ⊤
  have key : ∀ V : Opens M, ∀ x y : M,
      ((chartedCausality (minkowski d) M).le V x y ↔ (flatCausality d M).le V x y) ∧
      ((chartedCausality (minkowski d) M).lt V x y ↔ (flatCausality d M).lt V x y) := by
    intro V x y
    have i1 := imp_of_agree_locally hA1 (fun z _ => ⟨_, mem_chart_source _ z, hagree z⟩)
      (le_top : V ≤ ⊤) (x := x) (y := y)
    have i2 := imp_of_agree_locally hA2 (fun z _ => ⟨_, mem_chart_source _ z, (hagree z).symm⟩)
      (le_top : V ≤ ⊤) (x := x) (y := y)
    exact ⟨⟨i1.1, i2.1⟩, ⟨i1.2, i2.2⟩⟩
  apply Causality.ext_toPrecausality
  ext V x y
  · exact (key V x y).1
  · exact (key V x y).2

end Bridge

/-! ### §4 The global fields (B3) on a flat spacetime -/

section Global

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

omit [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- The singular loci of a flat atlas are empty. -/
@[simp] theorem chartedSing_empty (α : ℝ) :
    chartedSing (fun _ => (∅ : Set (Minkowski d))) M α = ∅ := by
  ext x; simp [chartedSing]

/-- A flat spacetime has no isolated point: the chart at `x` carries `𝓝[≠] x` to `𝓝[≠]` of a
point of `Minkowski d`. -/
theorem flat_nhdsNE_neBot (d : ℕ) {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    (x : M) : (𝓝[≠] x).NeBot := by
  set e := chartAt (Minkowski d) x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hmap := e.map_nhdsWithin_eq hx ({x}ᶜ)
  have himg : e '' (e.source ∩ {x}ᶜ) = e.target ∩ {e x}ᶜ := by
    ext y
    constructor
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨e.map_source hz, fun h => hzx (e.injOn hz hx h)⟩
    · rintro ⟨hy, hyx⟩
      refine ⟨e.symm y, ⟨e.map_target hy, fun h => hyx ?_⟩, e.right_inv hy⟩
      rw [mem_singleton_iff] at h ⊢
      rw [← h, e.right_inv hy]
  rw [himg, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds
    (e.open_target.mem_nhds (e.map_source hx)))] at hmap
  have : (map e (𝓝[≠] x)).NeBot := by rw [hmap]; infer_instance
  exact (Filter.map_neBot_iff _).1 this

/-- **B3, the corrected singular flat bundle with `sing = ∅`** (`Causality.SingularFlatAxiomsCorr`):
every BTZ field and `massive_line` is vacuous; the rest is the flat library. -/
theorem flat_singularFlatAxiomsCorr [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] :
    (flatCausality d M).SingularFlatAxiomsCorr (chartedSing (fun _ => (∅ : Set (Minkowski d))) M) := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Minkowski d) M
  let N : FlatSpacetime.{0} d := FlatSpacetime.of M
  refine
    { singularPastAt := fun p hp => by simp at hp
      Iminus_eq_empty := fun p hp => by simp at hp
      Iplus_of_lt := fun p hp => by simp at hp
      past_local := fun p hp => by simp at hp
      line := fun p hp => by simp at hp
      pushUp := flatCausality_pushUp (N := N)
      absolutelyMinimal := flatCausality_absolutelyMinimal
      causallyArcConnected := flatCausality_causallyArcConnected d M
      tarentin := flatCausality_tarentin
      mem_Zplus := fun p => flatCausality_mem_Zplus (N := N) p
      mem_Zminus_iff := fun p => ⟨fun _ => by simp, fun _ => flatCausality_mem_Zminus (N := N) p⟩
      t2 := inferInstance
      secondCountable := inferInstance
      metrizable := TopologicalSpace.metrizableSpace_of_t3_secondCountable M
      locallyCompact := inferInstance
      noIsolated := flat_nhdsNE_neBot d
      isClosed_sing := fun α _ => by simp
      interior_sing := fun α _ => by simp
      massive_line := fun α _ p hp => by simp at hp }

/-- **B3, `curvesExtend`, without global hyperbolicity**: a flat spacetime (T2, second countable)
carries a chronal causal flow (`flat_hasChronalCausalFlow`), hence `CurvesExtend`
(`curvesExtend_of_isCausalFlow`). -/
theorem flat_curvesExtend [T2Space M] [SecondCountableTopology M] :
    (flatCausality d M).CurvesExtend := by
  obtain ⟨φ, hφ, -⟩ := (flat_hasChronalCausalFlow : (flatCausality d M).HasChronalCausalFlow)
  exact curvesExtend_of_isCausalFlow hφ

/-- **The time-function field** (design §6, interface round 2): a GH flat spacetime carries a
continuous function strictly increasing along `≤` — the Geroch time of the admissible measures
of `Flat/GerochFlat` (`exists_admissible_measure`, `geroch_i_imp_ii`). -/
theorem flat_hasTimeFunction [T2Space M] [ConnectedSpace M]
    (hGH : (flatCausality d M).GloballyHyperbolic) : (flatCausality d M).HasTimeFunction := by
  let N : FlatSpacetime.{0} d := FlatSpacetime.of M
  letI : MeasurableSpace N := borel N
  haveI : BorelSpace N := ⟨rfl⟩
  have hGH' : (flatCausality d N).GloballyHyperbolic := hGH
  obtain ⟨μ, hp, hm⟩ := exists_admissible_measure N hGH'
  obtain ⟨φ, hφ, -⟩ := (flat_hasChronalCausalFlow : (flatCausality d N).HasChronalCausalFlow)
  obtain ⟨T, hT, hTs⟩ := Causality.geroch_i_imp_ii hp hm flatCausality_tarentin
    (flatCausality_causallyArcConnected d N) (jminus_ne_singleton_of_isCausalFlow hφ)
    (jplus_ne_singleton_of_isCausalFlow hφ) hGH'
  exact ⟨T, hT.1.continuous, hTs⟩

end Global

/-! ### §5 The compactness fields (R1): named, not proved -/

variable (d) in
/-- **R1, future form**, for flat spacetimes (the field `isCompact_Jplus_inter_Jminus` of
`LocalModel`): in a GH flat spacetime with Cauchy surface `Σ`, `J⁺(Σ) ∩ J⁻(p)` is compact. -/
def FlatCompactJplusJminus : Prop :=
  ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
    [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))],
    (flatCausality d M).GloballyHyperbolic → ∀ S : Set M, (flatCausality d M).IsCauchySurface S →
      ∀ p : M, IsCompact ((flatCausality d M).Jplus ⊤ S ∩ (flatCausality d M).Jminus ⊤ {p})

variable (d) in
/-- **R1, past form** (no duality). -/
def FlatCompactJminusJplus : Prop :=
  ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
    [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))],
    (flatCausality d M).GloballyHyperbolic → ∀ S : Set M, (flatCausality d M).IsCauchySurface S →
      ∀ p : M, IsCompact ((flatCausality d M).Jminus ⊤ S ∩ (flatCausality d M).Jplus ⊤ {p})

theorem flat_isCompact_Jplus_inter_Jminus : FlatCompactJplusJminus d := by
  sorry -- SORRY(theo:CBG): R1 for flat spacetimes — `J⁺(Σ) ∩ J⁻(p)` compact needs `J⁻(p) ∩ Σ` compact (Σ Cauchy, M GH) and its cover by finitely many `I⁺(q_i)`, every `x` in the set lying above a point of `J⁻(p) ∩ Σ` (past-inextensible curve through `p`, `x`; CurvesExtend + acausality), and the set closed, so that it is a closed subset of the finite union of the compact diamonds `J(q_i, p)`; compactness of `J⁻(p) ∩ Σ` and closedness of `J⁺(Σ)` are not in the library (no limit-curve theorem; CompactCauchy has only `exists_not_mem_Jminus_of_isCompact`)

theorem flat_isCompact_Jminus_inter_Jplus : FlatCompactJminusJplus d := by
  sorry -- SORRY(theo:CBG): R1, past form, as `flat_isCompact_Jplus_inter_Jminus` with the time orientation reversed

/-! ### §6 B4: slices of Minkowski space by the time coordinate on small diamonds -/

section Slices

/-- A Cauchy surface of `W` may be changed outside `W`. -/
theorem isCauchySurfaceOn_congr {M : Type*} [TopologicalSpace M] {C : Causality M} {W : Opens M}
    {S S' : Set M} (h : C.IsCauchySurfaceOn W S) (hS : ∀ x ∈ W, x ∈ S ↔ x ∈ S') :
    C.IsCauchySurfaceOn W S' := by
  intro I c hc
  obtain ⟨x, ⟨hxI, hxS⟩, hu⟩ := h I c hc
  have hW : ∀ y ∈ c '' I, y ∈ W := by rintro _ ⟨t, ht, rfl⟩; exact hc.1.mem ht
  exact ⟨x, ⟨hxI, (hS x (hW x hxI)).1 hxS⟩,
    fun y ⟨hyI, hyS⟩ => hu y ⟨hyI, (hS y (hW y hyI)).2 hyS⟩⟩

variable (y : Minkowski d) (ε : ℝ)

theorem isOpen_mdiamond :
    IsOpen {r : Minkowski d | ‖r.2 - y.2‖ < r.1 - (y.1 - ε) ∧ ‖r.2 - y.2‖ < y.1 + ε - r.1} := by
  rw [setOf_and]
  exact (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))

/-- **The open diamond** `I⁺(y − ε e₀) ∩ I⁻(y + ε e₀)` of Minkowski space, written out. -/
def mdiamond : Opens (Minkowski d) :=
  ⟨{r | ‖r.2 - y.2‖ < r.1 - (y.1 - ε) ∧ ‖r.2 - y.2‖ < y.1 + ε - r.1}, isOpen_mdiamond y ε⟩

variable {y ε}

theorem mem_mdiamond {r : Minkowski d} :
    r ∈ mdiamond y ε ↔ ‖r.2 - y.2‖ < r.1 - (y.1 - ε) ∧ ‖r.2 - y.2‖ < y.1 + ε - r.1 := Iff.rfl

theorem mem_mdiamond_self (hε : 0 < ε) : y ∈ mdiamond y ε := by
  rw [mem_mdiamond, sub_self, norm_zero]; constructor <;> linarith

theorem mdiamond_subset_ball : (mdiamond y ε : Set (Minkowski d)) ⊆ Metric.ball y ε := by
  intro r hr
  rw [SetLike.mem_coe, mem_mdiamond] at hr
  have h0 := norm_nonneg (r.2 - y.2)
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm, abs_lt]
  exact ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, by linarith [hr.1, hr.2]⟩

/-- A diamond is causally convex in Minkowski space. -/
theorem mdiamond_causallyConvexIn :
    (minkowski d).CausallyConvexIn (mdiamond y ε : Set (Minkowski d)) ⊤ := by
  refine ⟨fun _ _ => trivial, fun p hp q hq z hz => ?_⟩
  rw [Causality.mem_diamond, minkowski_le_top_iff, minkowski_le_top_iff] at hz
  rw [SetLike.mem_coe, mem_mdiamond] at hp hq ⊢
  have h1 := norm_sub_le_norm_sub_add_norm_sub z.2 p.2 y.2
  have h2 := norm_sub_le_norm_sub_add_norm_sub z.2 q.2 y.2
  rw [norm_sub_rev z.2 q.2] at h2
  constructor <;> linarith [hz.1, hz.2, hp.1, hq.2]

/-- A diamond is globally hyperbolic. -/
theorem mdiamond_globallyHyperbolicOn : (minkowski d).GloballyHyperbolicOn (mdiamond y ε) :=
  Causality.GloballyHyperbolicOn.of_causallyConvexIn minkowski_causallyArcConnected
    minkowski_globallyHyperbolic mdiamond_causallyConvexIn

/-- **The equatorial slice `t = c` is a Cauchy surface of the diamond centred at time `c`**:
`isCauchySurfaceOn_graph_of_saturated` (`Flat/LipschitzGraph`) for the constant graph. -/
theorem isCauchySurfaceOn_mdiamond (c : ℝ) (x₀ : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) :
    (minkowski d).IsCauchySurfaceOn (mdiamond (c, x₀) ρ)
      (graph fun _ : EuclideanSpace ℝ (Fin d) => c) := by
  have hf : IsStrictContraction fun _ : EuclideanSpace ℝ (Fin d) => c := by
    intro x y hxy
    simpa using sub_ne_zero.2 hxy
  refine isCauchySurfaceOn_graph_of_saturated hf ?_ ?_ ?_
  · intro z _ v hv hv0
    have hn := isFutureCausal_iff_norm_le.1 hv
    have hv1 : 0 < v.1 := by
      rcases (norm_nonneg v.2).trans hn |>.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2 : v.2 = 0 := norm_eq_zero.1 (le_antisymm (h ▸ hn) (norm_nonneg _))
        exact hv0 (Prod.ext h.symm h2)
    refine ⟨(c - z.1) / v.1, ?_⟩
    show (z + ((c - z.1) / v.1) • v).1 = c
    rw [Prod.fst_add, Prod.smul_fst, smul_eq_mul, div_mul_cancel₀ _ hv1.ne']
    ring
  · intro z hz q hqz hq
    rw [minkowski_le_top_iff] at hqz
    rw [timeSub_apply] at hq
    rw [mem_mdiamond] at hz ⊢
    simp only at hz ⊢
    have h1 := norm_sub_le_norm_sub_add_norm_sub q.2 z.2 x₀
    rw [norm_sub_rev q.2 z.2] at h1
    constructor <;> linarith [hz.1, hz.2]
  · intro z hz q hzq hq
    rw [minkowski_le_top_iff] at hzq
    rw [timeSub_apply] at hq
    rw [mem_mdiamond] at hz ⊢
    simp only at hz ⊢
    have h1 := norm_sub_le_norm_sub_add_norm_sub q.2 z.2 x₀
    constructor <;> linarith [hz.1, hz.2]

/-- The slice `t = c` of a diamond lies in the diamond centred at `(c, y₂)` of radius
`ε − |c − y₁|`. -/
theorem mem_mdiamond_slice {r : Minkowski d} (hr : r ∈ mdiamond y ε) :
    r ∈ mdiamond (r.1, y.2) (ε - |r.1 - y.1|) := by
  rw [mem_mdiamond] at hr ⊢
  simp only
  rcases abs_cases (r.1 - y.1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> constructor <;>
    linarith [hr.1, hr.2]

/-- The diamond over a slice lies in the diamond. -/
theorem mdiamond_slice_le (c : ℝ) :
    mdiamond (c, y.2) (ε - |c - y.1|) ≤ mdiamond y ε := by
  intro r hr
  rw [mem_mdiamond] at hr ⊢
  simp only at hr
  rcases abs_cases (c - y.1) with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at hr <;> constructor <;>
    linarith [hr.1, hr.2]

/-- Along `≤_W` the time coordinate is strictly increasing on distinct points. -/
theorem minkowski_fst_lt_of_le {W : Opens (Minkowski d)} {x x' : Minkowski d}
    (h : (minkowski d).le W x x') (hne : x ≠ x') : x.1 < x'.1 := by
  have h' := minkowski_le_top_iff.1 ((minkowski d).le_mono le_top h)
  rcases (norm_nonneg _).trans h' |>.lt_or_eq with hlt | heq
  · linarith
  · exfalso
    have h2 : x'.2 - x.2 = 0 := norm_eq_zero.1 (le_antisymm (by linarith) (norm_nonneg _))
    exact hne (Prod.ext (by linarith) (sub_eq_zero.1 h2).symm)

/-- The common part of B4: a time-like coordinate `τ = σ · t` (`σ = ±1`) on a small diamond. -/
theorem minkowski_slice_aux (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (y : Minkowski d) {O : Set (Minkowski d)}
    (hO : O ∈ 𝓝 y) : ∃ (W : Opens (Minkowski d)) (τ : Minkowski d → ℝ), y ∈ W ∧ (W : Set _) ⊆ O ∧
      ContinuousOn τ W ∧ (τ = fun r => σ * r.1) ∧
      ∀ c ∈ τ '' W, ∃ N : Opens (Minkowski d), τ ⁻¹' {c} ∩ W ⊆ N ∧ N ≤ W ∧
        (minkowski d).GloballyHyperbolicOn N ∧ (minkowski d).IsCauchySurfaceOn N (τ ⁻¹' {c} ∩ W) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hO
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  refine ⟨mdiamond y ε, fun r => σ * r.1, mem_mdiamond_self hε,
    mdiamond_subset_ball.trans hball, by fun_prop, rfl, ?_⟩
  rintro _ ⟨r₀, hr₀, rfl⟩
  refine ⟨mdiamond (r₀.1, y.2) (ε - |r₀.1 - y.1|), ?_, mdiamond_slice_le _,
    mdiamond_globallyHyperbolicOn, ?_⟩
  · rintro r ⟨hr, hrW⟩
    have : r.1 = r₀.1 := mul_left_cancel₀ hσ0 hr
    have := mem_mdiamond_slice hrW
    rwa [‹r.1 = r₀.1›] at this
  · refine isCauchySurfaceOn_congr (isCauchySurfaceOn_mdiamond r₀.1 y.2 _) fun r hr => ?_
    have hrW : r ∈ mdiamond y ε := mdiamond_slice_le _ hr
    show r.1 = r₀.1 ↔ σ * r.1 = σ * r₀.1 ∧ r ∈ mdiamond y ε
    exact ⟨fun h => ⟨by rw [h], hrW⟩, fun h => mul_left_cancel₀ hσ0 h.1⟩

/-- **B4, future side, for Minkowski space**: `τ = −t` on a small diamond. -/
theorem minkowski_slice_future : ∀ y : Minkowski d, ∀ O ∈ 𝓝 y, ∃ (W : Opens (Minkowski d))
    (τ : Minkowski d → ℝ), y ∈ W ∧ (W : Set (Minkowski d)) ⊆ O ∧ ContinuousOn τ W ∧
    (∀ x ∈ W, ∀ x' ∈ W, (minkowski d).le W x x' → x ≠ x' → τ x' < τ x) ∧
    ∀ c ∈ τ '' W, ∃ N : Opens (Minkowski d), τ ⁻¹' {c} ∩ W ⊆ N ∧ N ≤ W ∧
      (minkowski d).GloballyHyperbolicOn N ∧ (minkowski d).IsCauchySurfaceOn N (τ ⁻¹' {c} ∩ W) := by
  intro y O hO
  obtain ⟨W, τ, hy, hWO, hc, rfl, hN⟩ := minkowski_slice_aux (-1) (Or.inr rfl) y hO
  refine ⟨W, _, hy, hWO, hc, fun x _ x' _ h hne => ?_, hN⟩
  have := minkowski_fst_lt_of_le h hne
  linarith

/-- **B4, past side, for Minkowski space**: `τ = t` on a small diamond. -/
theorem minkowski_slice_past : ∀ y : Minkowski d, ∀ O ∈ 𝓝 y, ∃ (W : Opens (Minkowski d))
    (τ : Minkowski d → ℝ), y ∈ W ∧ (W : Set (Minkowski d)) ⊆ O ∧ ContinuousOn τ W ∧
    (∀ x ∈ W, ∀ x' ∈ W, (minkowski d).le W x x' → x ≠ x' → τ x < τ x') ∧
    ∀ c ∈ τ '' W, ∃ N : Opens (Minkowski d), τ ⁻¹' {c} ∩ W ⊆ N ∧ N ≤ W ∧
      (minkowski d).GloballyHyperbolicOn N ∧ (minkowski d).IsCauchySurfaceOn N (τ ⁻¹' {c} ∩ W) := by
  intro y O hO
  obtain ⟨W, τ, hy, hWO, hc, rfl, hN⟩ := minkowski_slice_aux 1 (Or.inl rfl) y hO
  refine ⟨W, _, hy, hWO, hc, fun x _ x' _ h hne => ?_, hN⟩
  have := minkowski_fst_lt_of_le h hne
  linarith

end Slices

/-! ### §7 The flat local model -/

variable (d) in
/-- **The flat local model** (design §4): `Y = Minkowski d`, `G` the isometry groupoid
`gxGroupoid (isom d) (Minkowski d)`, `causalityY = minkowski d`, no singular locus. Every field is
proved here except the two compactness fields (R1), taken as the hypotheses `hJ₁`, `hJ₂`. -/
noncomputable def flatModelOf (hJ₁ : FlatCompactJplusJminus d) (hJ₂ : FlatCompactJminusJplus d) :
    LocalModel.{0} where
  Y := Minkowski d
  G := gxGroupoid (isom d) (Minkowski d)
  causalityY := minkowski d
  singY := fun _ => ∅
  rigid := flat_rigid
  localUnique_sing := fun _ _ _ _ _ _ _ hy₀ => by simp at hy₀
  localUnique_reg := flat_localUnique_reg
  regularChart := fun _ _ => ⟨OpenPartialHomeomorph.refl _,
    (gxGroupoid (isom d) (Minkowski d)).id_mem, trivial, fun _ _ _ _ => by simp⟩
  absolutelyMinimalOn_Y := minkowski_absolutelyMinimalOn
  chartIso_mem := fun _ he => minkowski_chartIso_of_mem he
  sing_mem := fun _ _ _ _ _ _ => by simp
  singularFlatAxioms := by
    intro M _ _ _ _ _ _
    rw [chartedCausality_eq_flatCausality]
    exact flat_singularFlatAxiomsCorr
  curvesExtend := by
    intro M _ _ _ _ _ _ _
    rw [chartedCausality_eq_flatCausality]
    exact flat_curvesExtend
  isCompact_Jplus_inter_Jminus := by
    intro M _ _ _ _ _ _ hGH S hS p
    rw [chartedCausality_eq_flatCausality] at hGH hS ⊢
    exact hJ₁ hGH S hS p
  isCompact_Jminus_inter_Jplus := by
    intro M _ _ _ _ _ _ hGH S hS p
    rw [chartedCausality_eq_flatCausality] at hGH hS ⊢
    exact hJ₂ hGH S hS p
  secondCountable_of_cauchy := by
    intro M _ _ _ _ _ _ _ _ _
    exact flat_secondCountableTopology (d := d) M
  slice_future := minkowski_slice_future
  slice_past := minkowski_slice_past

variable (d) in
/-- **The flat local model**, its two compactness fields resting on the tagged
`flat_isCompact_Jplus_inter_Jminus`, `flat_isCompact_Jminus_inter_Jplus`. -/
noncomputable def flatModel : LocalModel.{0} :=
  flatModelOf d flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus

/-! ### §8 The flat geometry and `flat_cbg` -/

section Principal

variable {hJ₁ : FlatCompactJplusJminus d} {hJ₂ : FlatCompactJminusJplus d}

/-- The structure of a flat spacetime, as a Level-B structure of the flat model. -/
def flatStr (hJ₁ : FlatCompactJplusJminus d) (hJ₂ : FlatCompactJminusJplus d) (M : Type)
    [TopologicalSpace M] [cs : ChartedSpace (Minkowski d) M]
    [hg : HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] : (flatModelOf d hJ₁ hJ₂).Str M :=
  ⟨cs, hg⟩

/-- The causality of a flat structure is `flatCausality`. -/
theorem causality_flatStr (M : Type) [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] :
    LocalModel.causality (flatStr hJ₁ hJ₂ M) = flatCausality d M := by
  show chartedCausality (minkowski d) M = flatCausality d M
  exact chartedCausality_eq_flatCausality

variable (d) in
/-- **The flat geometry, under R1 and A3/A4 for the flat model** (sorry-free). -/
noncomputable def flatGeometryOf (hJ₁ : FlatCompactJplusJminus d) (hJ₂ : FlatCompactJminusJplus d)
    (hA3f : (flatModelOf d hJ₁ hJ₂).GermExtFuture) (hA3p : (flatModelOf d hJ₁ hJ₂).GermExtPast)
    (hA4f : (flatModelOf d hJ₁ hJ₂).SliceFuture) (hA4p : (flatModelOf d hJ₁ hJ₂).SlicePast) :
    Geometry.{0} :=
  Geometry.ofLocalModelOfGermSlice (flatModelOf d hJ₁ hJ₂) hA3f hA3p hA4f hA4p

variable (d) in
/-- **The flat geometry** `Geometry.ofLocalModel (flatModel d)`: rests on the two compactness
`sorry`s here and on `CBG/FromModel`'s four A3/A4 `sorry`s. -/
noncomputable def flatGeometry : Geometry.{0} := Geometry.ofLocalModel (flatModel d)

/-- **The time-function field** (interface round 2) holds in every flat geometry: the Geroch
time (`flat_hasTimeFunction`). -/
theorem flatGeometryOf_hasTimeFunctions {hA3f : (flatModelOf d hJ₁ hJ₂).GermExtFuture}
    {hA3p : (flatModelOf d hJ₁ hJ₂).GermExtPast} {hA4f : (flatModelOf d hJ₁ hJ₂).SliceFuture}
    {hA4p : (flatModelOf d hJ₁ hJ₂).SlicePast} :
    (flatGeometryOf d hJ₁ hJ₂ hA3f hA3p hA4f hA4p).HasTimeFunctions := by
  intro M _ _ _ _ s hGH
  letI : ChartedSpace (Minkowski d) M := s.1
  haveI : HasGroupoid M (gxGroupoid (isom d) (Minkowski d)) := s.2
  change (chartedCausality (minkowski d) M).GloballyHyperbolic at hGH
  change (chartedCausality (minkowski d) M).HasTimeFunction
  rw [chartedCausality_eq_flatCausality] at hGH ⊢
  exact flat_hasTimeFunction hGH

/-- **CBG for flat spacetimes, conditional form** (sorry-free; `theo:CBG` in the universal
reading DEC-59, for `Y = Minkowski d`): a globally hyperbolic flat spacetime `M₀` with a Cauchy
surface has a universal Cauchy development, in the flat geometry built under R1 (`hJ₁`, `hJ₂`)
and A3/A4 for the flat model. Second countability of `M₀` is derived (DEC-49). -/
theorem flat_cbg_of (hA3f : (flatModelOf d hJ₁ hJ₂).GermExtFuture)
    (hA3p : (flatModelOf d hJ₁ hJ₂).GermExtPast) (hA4f : (flatModelOf d hJ₁ hJ₂).SliceFuture)
    (hA4p : (flatModelOf d hJ₁ hJ₂).SlicePast) {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀]
    [ConnectedSpace M₀] [ChartedSpace (Minkowski d) M₀]
    [HasGroupoid M₀ (gxGroupoid (isom d) (Minkowski d))]
    (hGH : (flatCausality d M₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (flatCausality d M₀).IsCauchySurface S) :
    ∃ Mbar : Dev (flatGeometryOf d hJ₁ hJ₂ hA3f hA3p hA4f hA4p).toPreGeometry
      (flatStr hJ₁ hJ₂ M₀), Mbar.IsUniversal := by
  haveI : SecondCountableTopology M₀ := flat_secondCountableTopology (d := d) M₀
  have hc : (flatGeometryOf d hJ₁ hJ₂ hA3f hA3p hA4f hA4p).causality (flatStr hJ₁ hJ₂ M₀) =
      flatCausality d M₀ := causality_flatStr M₀
  exact cbg_of_hasTimeFunctions (flatStr hJ₁ hJ₂ M₀) (hc ▸ hGH) (S := S) (hc ▸ hS)
    flatGeometryOf_hasTimeFunctions

/-- **CBG for flat spacetimes, conditional form, from global hyperbolicity alone**: the Cauchy
surface is Geroch's (`flatGerochGH`, `Flat/GerochFlat`). -/
theorem flat_cbg_gh_of (hA3f : (flatModelOf d hJ₁ hJ₂).GermExtFuture)
    (hA3p : (flatModelOf d hJ₁ hJ₂).GermExtPast) (hA4f : (flatModelOf d hJ₁ hJ₂).SliceFuture)
    (hA4p : (flatModelOf d hJ₁ hJ₂).SlicePast) {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀]
    [ConnectedSpace M₀] [ChartedSpace (Minkowski d) M₀]
    [HasGroupoid M₀ (gxGroupoid (isom d) (Minkowski d))]
    (hGH : (flatCausality d M₀).GloballyHyperbolic) :
    ∃ Mbar : Dev (flatGeometryOf d hJ₁ hJ₂ hA3f hA3p hA4f hA4p).toPreGeometry
      (flatStr hJ₁ hJ₂ M₀), Mbar.IsUniversal := by
  obtain ⟨S, hS⟩ := flatGerochGH (FlatSpacetime.of (d := d) M₀) hGH
  exact flat_cbg_of hA3f hA3p hA4f hA4p hGH hS

/-- **CBG for flat spacetimes** (`theo:CBG`, universal reading DEC-59, `Y = Minkowski d`): every
globally hyperbolic flat spacetime with a Cauchy surface has a universal Cauchy development in
`flatGeometry d`. Rests on R1 here (two tagged `sorry`s) and A3/A4 in `CBG/FromModel` (four). -/
theorem flat_cbg {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀] [ConnectedSpace M₀]
    [ChartedSpace (Minkowski d) M₀] [HasGroupoid M₀ (gxGroupoid (isom d) (Minkowski d))]
    (hGH : (flatCausality d M₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (flatCausality d M₀).IsCauchySurface S) :
    ∃ Mbar : Dev (flatGeometry d).toPreGeometry
      (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus M₀),
      Mbar.IsUniversal :=
  flat_cbg_of (flatModel d).germExtFuture (flatModel d).germExtPast (flatModel d).sliceFuture
    (flatModel d).slicePast hGH hS

/-- **CBG for flat spacetimes from global hyperbolicity alone** (the Cauchy surface is
Geroch's, `flatGerochGH`). -/
theorem flat_cbg_gh {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀] [ConnectedSpace M₀]
    [ChartedSpace (Minkowski d) M₀] [HasGroupoid M₀ (gxGroupoid (isom d) (Minkowski d))]
    (hGH : (flatCausality d M₀).GloballyHyperbolic) :
    ∃ Mbar : Dev (flatGeometry d).toPreGeometry
      (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus M₀),
      Mbar.IsUniversal :=
  flat_cbg_gh_of (flatModel d).germExtFuture (flatModel d).germExtPast (flatModel d).sliceFuture
    (flatModel d).slicePast hGH

/-- **CBG for flat spacetimes, ETT/Barbot reading, conditional form** (sorry-free; `theo:CBG` as
printed, « admits a maximal Cauchy extension, and that extension is unique up to isomorphism »,
`ETT.tex:1885–1886`, regular flat case): an ETT-maximal development exists, and every ETT-maximal
development is isomorphic to it by a unique morphism of developments
(`Dev.IsUniversal.isETTMaximal`, `Dev.IsETTMaximal.isUniversal`,
`Dev.IsUniversal.existsUnique_iso`; `M₀` is non-empty, being connected). -/
theorem flat_cbg_ett_of (hA3f : (flatModelOf d hJ₁ hJ₂).GermExtFuture)
    (hA3p : (flatModelOf d hJ₁ hJ₂).GermExtPast) (hA4f : (flatModelOf d hJ₁ hJ₂).SliceFuture)
    (hA4p : (flatModelOf d hJ₁ hJ₂).SlicePast) {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀]
    [ConnectedSpace M₀] [ChartedSpace (Minkowski d) M₀]
    [HasGroupoid M₀ (gxGroupoid (isom d) (Minkowski d))]
    (hGH : (flatCausality d M₀).GloballyHyperbolic) :
    ∃ Mbar : Dev (flatGeometryOf d hJ₁ hJ₂ hA3f hA3p hA4f hA4p).toPreGeometry
      (flatStr hJ₁ hJ₂ M₀), Mbar.IsETTMaximal ∧
      ∀ M : Dev (flatGeometryOf d hJ₁ hJ₂ hA3f hA3p hA4f hA4p).toPreGeometry (flatStr hJ₁ hJ₂ M₀),
        M.IsETTMaximal →
        ∃! f : Mbar.carrier → M.carrier, Mbar.IsMorphism M f ∧
          ∃ g : M.carrier → Mbar.carrier, M.IsMorphism Mbar g ∧ g ∘ f = id ∧ f ∘ g = id := by
  obtain ⟨Mbar, hU⟩ := flat_cbg_gh_of hA3f hA3p hA4f hA4p hGH
  exact ⟨Mbar, hU.isETTMaximal, fun M hM => hU.existsUnique_iso (hM.isUniversal hU)⟩

/-- **CBG for flat spacetimes, ETT/Barbot reading** (`theo:CBG` as printed, regular flat case):
existence of an ETT-maximal development, unique up to unique isomorphism, in `flatGeometry d`.
Rests on the same `sorry`s as `flat_cbg`. -/
theorem flat_cbg_ett {M₀ : Type} [TopologicalSpace M₀] [T2Space M₀] [ConnectedSpace M₀]
    [ChartedSpace (Minkowski d) M₀] [HasGroupoid M₀ (gxGroupoid (isom d) (Minkowski d))]
    (hGH : (flatCausality d M₀).GloballyHyperbolic) :
    ∃ Mbar : Dev (flatGeometry d).toPreGeometry
      (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus M₀),
      Mbar.IsETTMaximal ∧
      ∀ M : Dev (flatGeometry d).toPreGeometry
        (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus M₀),
        M.IsETTMaximal →
        ∃! f : Mbar.carrier → M.carrier, Mbar.IsMorphism M f ∧
          ∃ g : M.carrier → Mbar.carrier, M.IsMorphism Mbar g ∧ g ∘ f = id ∧ f ∘ g = id :=
  flat_cbg_ett_of (flatModel d).germExtFuture (flatModel d).germExtPast (flatModel d).sliceFuture
    (flatModel d).slicePast hGH

/-- **Non-vacuity** (kb/0011): `flat_cbg_gh` applies to `Minkowski d` itself
(`gh_minkowskiSpace`). -/
theorem flat_cbg_minkowski :
    ∃ Mbar : Dev (flatGeometry d).toPreGeometry
      (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus (Minkowski d)),
      Mbar.IsUniversal :=
  flat_cbg_gh (gh_minkowskiSpace (d := d))

end Principal

end CBG

end Causal
