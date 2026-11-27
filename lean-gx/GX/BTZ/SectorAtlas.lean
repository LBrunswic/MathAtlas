import GX.BTZ.Causality

/-!
# `GX.BTZ.SectorAtlas` — the sector charts of `𝔼₀` lie in its maximal a.e. atlas

Target T-btz-blunt-vertical-ray. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`), § 3.1: the
brick used by `GXScaffold.BTZ.BluntSpear` for `btzlem:blunt_spear_neighborhood` (unmarked here:
this file certifies no label, it supplies a lemma of the model).

* `GX.E0.sectorChartBTZ_mem_aeAtlas`: the sector chart `sectorChartBTZ y hy` of `𝔼₀` (the
  development with the branch angle on the slit sector around `y`) belongs to the maximal
  a.e. atlas of `BTZE0`.
* `GX.E0.sectorChartY`, `GX.E0.sectorChartY_mem_e0Atlas`: the same chart read on
  `Y = 𝕄 ⊕ 𝔼₀`, a chart of Rigid's `e0Atlas`.
* `GX.E0.sectorSmulInl`, `GX.E0.sectorSmulInl_mem`: for `g ∈ Isom(𝐌³)`, the map
  `inl ∘ (g • ·) ∘ sectorChartY` is an element of the groupoid `G = e0Groupoid` defined on the
  whole slit sector.
* `GX.E0.exists_eqOn_sectorSmulInl`: **rigidity at a regular point into `𝕄`** — a local
  `G`-structomorphism `f` on a preconnected open subset `U` of the slit sector, with values in the
  summand `𝕄`, is `inl ∘ (g • ·) ∘ sectorChartY` on all of `U` for one `g` (by
  `e0_eqOn_of_eqOn_open`).

> Such a $\V^*$ is the regular part of a unique spear $\V$ in $\mass{0}$ (l.627)

## Hypothesis checklist

| paper | here |
|---|---|
| (none: a lemma of the model `𝔼₀`) | — |

## SCOPE (disclosed)

* Nothing is assumed. The proof of the brick is the argument of `E0.chartIso_aeAtlas` (every
  chart of the maximal atlas is locally `g •` a sector chart, `btz_chart_eq_smul_btzPaperDev`),
  run for a sector centred at an arbitrary `y` rather than at the point itself, and fed to
  `IsMaximalAEAtlas.mem_of_compatible`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal (imports
`Causal.*` through `GX.BTZ.Causality`, DEC-33).
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

namespace E0

attribute [local instance] btzE0Structure

/-- **The sector chart lies in `BTZE0`'s maximal a.e. atlas**: near every point of its overlap
with a chart `c` of the maximal atlas, `c = g • sectorChartBTZ y hy` (both are, near the point,
`g •` the paper's developing map in the branch angle of the sector). -/
theorem sectorChartBTZ_mem_aeAtlas {y : E0} (hy : y.2 ≠ 0) :
    sectorChartBTZ y hy ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
  refine (isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0).mem_of_compatible
    fun c hc x hx => ?_
  have hws : toPaper x ∈ sector y := by
    have h := hx.1
    simp only [sectorChartBTZ, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage] at h
    exact h.2
  set w := toPaper x with hw
  have hwax : w ∉ axis := not_mem_axis_of_mem_sector hws
  set p : ℝ × ℝ × ℝ := (w.1, rad w, angle y w) with hp
  have hpx : orbitMk (GammaA (2 * π)) (btzPaperCyl p) = x := by
    rw [← toPaper_symm_eq_orbitMk hwax (polar_angle hy w), hw, Homeomorph.symm_apply_apply]
  obtain ⟨g, hg⟩ := btz_chart_eq_smul_btzPaperDev isBTZStructure_btzE0 hc
    (p := p) (rad_pos.2 hwax) (by rw [hpx]; exact hx.2)
  set φ : BTZE0 → ℝ × ℝ × ℝ := fun z => ((toPaper z).1, rad (toPaper z), angle y (toPaper z))
  have hφ : ContinuousAt φ x := by
    have hang : ContinuousAt (angle y) w :=
      (continuousOn_angle y).continuousAt ((isOpen_sector y).mem_nhds hws)
    have h3 : ContinuousAt (fun z => angle y (toPaper z)) x :=
      ContinuousAt.comp (g := angle y) (f := toPaper) hang toPaper.continuous.continuousAt
    exact (continuous_fst.comp toPaper.continuous).continuousAt.prodMk
      ((continuous_rad.comp toPaper.continuous).continuousAt.prodMk h3)
  refine ⟨g, ?_⟩
  have h1 : ∀ᶠ z in 𝓝 x, c (orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z))) =
      g • btzPaperDev (φ z) := hφ.eventually hg
  have h2 : ∀ᶠ z in 𝓝 x, toPaper z ∈ sector y :=
    toPaper.continuous.continuousAt.preimage_mem_nhds ((isOpen_sector y).mem_nhds hws)
  filter_upwards [h1, h2] with z hz1 hz2
  have hzax : toPaper z ∉ axis := not_mem_axis_of_mem_sector hz2
  have hz : orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z)) = z := by
    rw [← toPaper_symm_eq_orbitMk hzax (polar_angle hy (toPaper z)), Homeomorph.symm_apply_apply]
  rw [hz] at hz1
  rw [hz1]
  show g • btzPaperDev (φ z) = g • chartMap y (toPaper z)
  rw [chartMap_eq]

/-- The sector chart read on `Y = 𝕄 ⊕ 𝔼₀`. -/
noncomputable def sectorChartY (y : E0) (hy : y.2 ≠ 0) :
    OpenPartialHomeomorph E0Y (Causal.Minkowski 2) :=
  e0Inr.symm.trans (sectorChartBTZ y hy)

/-- **The sector chart is a regular chart of `Y`** (a chart of Rigid's `e0Atlas`). -/
theorem sectorChartY_mem_e0Atlas {y : E0} (hy : y.2 ≠ 0) : sectorChartY y hy ∈ e0Atlas :=
  e0InrChart_mem_e0Atlas (sectorChartBTZ_mem_aeAtlas hy)

theorem paperInY_mem_sectorChartY_source {y w : E0} (hy : y.2 ≠ 0) (hw : w ∈ sector y) :
    paperInY w ∈ (sectorChartY y hy).source := by
  rw [sectorChartY, mem_e0InrChart_source]
  refine ⟨toPaper.symm w, ?_, rfl⟩
  simp only [sectorChartBTZ, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
  refine ⟨trivial, ?_⟩
  rw [Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.apply_symm_apply]
  exact hw

theorem image_sector_subset_source {y : E0} (hy : y.2 ≠ 0) :
    paperInY '' sector y ⊆ (sectorChartY y hy).source := by
  rintro _ ⟨w, hw, rfl⟩; exact paperInY_mem_sectorChartY_source hy hw

/-- On the paper's coordinates, the sector chart is the development with the branch angle. -/
theorem sectorChartY_paperInY {y : E0} (hy : y.2 ≠ 0) (w : E0) :
    sectorChartY y hy (paperInY w) = btzPaperDev (w.1, rad w, angle y w) := by
  rw [← chartMap_eq]
  simp only [sectorChartY, sectorChartBTZ, paperInY_apply, OpenPartialHomeomorph.coe_trans,
    comp_apply, e0Inr_symm_inr, Homeomorph.toOpenPartialHomeomorph_apply,
    Homeomorph.apply_symm_apply]
  rfl

/-- **`inl ∘ (g • ·) ∘ sectorChartY`**, a map of `Y` defined on the whole slit sector. -/
noncomputable def sectorSmulInl (y : E0) (hy : y.2 ≠ 0) (g : Causal.Flat.isom 2) :
    OpenPartialHomeomorph E0Y E0Y :=
  (sectorChartY y hy).trans ((Homeomorph.smul g).toOpenPartialHomeomorph.trans e0Inl)

theorem sectorSmulInl_source {y : E0} (hy : y.2 ≠ 0) (g : Causal.Flat.isom 2) :
    (sectorSmulInl y hy g).source = (sectorChartY y hy).source := by
  simp [sectorSmulInl]

theorem sectorSmulInl_apply {y : E0} (hy : y.2 ≠ 0) (g : Causal.Flat.isom 2) (x : E0Y) :
    sectorSmulInl y hy g x = Sum.inl (g • sectorChartY y hy x) := rfl

/-- **`inl ∘ (g • ·) ∘ sectorChartY` belongs to the groupoid `G`** of the local model. -/
theorem sectorSmulInl_mem {y : E0} (hy : y.2 ≠ 0) (g : Causal.Flat.isom 2) :
    sectorSmulInl y hy g ∈ e0Groupoid := by
  refine mem_e0Groupoid_of_chart_eq (sectorChartY_mem_e0Atlas hy) e0Inl_symm_mem_e0Atlas
    (by rw [sectorSmulInl_source]) ?_ g ?_
  · intro x hx
    rw [e0Inl_symm_source]
    rw [← (sectorSmulInl y hy g).right_inv hx, sectorSmulInl_apply]
    exact ⟨_, rfl⟩
  · intro x _
    rw [sectorSmulInl_apply, e0Inl_symm_inl]

/-- **Rigidity at regular points into `𝕄`**: a local `G`-structomorphism `f` on a non-empty
preconnected open subset `U` of the slit sector around `y` (in `Y`), with values in the summand
`𝕄`, is `inl ∘ (g • ·) ∘ sectorChartY y` on all of `U`, for a single `g ∈ Isom(𝐌³)`. -/
theorem exists_eqOn_sectorSmulInl {y : E0} (hy : y.2 ≠ 0) {U : Set E0Y} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUs : U ⊆ paperInY '' sector y)
    {f : E0Y → E0Y} (hf : ∀ x ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U x)
    (hfinl : ∀ x ∈ U, f x ∈ range Sum.inl) :
    ∃ g : Causal.Flat.isom 2, EqOn f (sectorSmulInl y hy g) U := by
  obtain ⟨p₀, hp₀⟩ := hUne
  have hp₀c : p₀ ∈ (sectorChartY y hy).source := image_sector_subset_source hy (hUs hp₀)
  obtain ⟨e₀, he₀, hfe₀, hp₀e₀⟩ := hf p₀ hp₀ hp₀
  have hreg : p₀ ∈ e0Reg := mem_support.2 ⟨_, sectorChartY_mem_e0Atlas hy, hp₀c⟩
  have hfp₀ : f p₀ = e₀ p₀ := hfe₀ ⟨hp₀, hp₀e₀⟩
  have hinl : e₀ p₀ ∈ e0Inl.symm.source := by
    rw [e0Inl_symm_source, ← hfp₀]; exact hfinl p₀ hp₀
  obtain ⟨g, hg⟩ := (((mem_e0Groupoid_iff.1 he₀).1 p₀ hp₀e₀).2 hreg).2 _
    (sectorChartY_mem_e0Atlas hy) _ e0Inl_symm_mem_e0Atlas hp₀c hinl
  refine ⟨g, ?_⟩
  set O : Set E0Y := interior {x | x ∈ U ∩ e₀.source ∧ e0Inl.symm (e₀ x) = g • sectorChartY y hy x}
  have hOo : IsOpen O := isOpen_interior
  have hp₀O : p₀ ∈ O := by
    refine mem_interior_iff_mem_nhds.2 ?_
    filter_upwards [hg, (hUo.inter e₀.open_source).mem_nhds ⟨hp₀, hp₀e₀⟩] with x h1 h2
    exact ⟨h2, h1⟩
  have hOU : O ⊆ U := fun x hx => (interior_subset hx : x ∈ {x | _}).1.1
  refine e0_eqOn_of_eqOn_open hUo hUc hf (sectorSmulInl_mem hy g)
    (by rw [sectorSmulInl_source]; exact hUs.trans (image_sector_subset_source hy)) hOo
    ⟨p₀, hp₀O⟩ hOU fun x hx => ?_
  obtain ⟨⟨hxU, hxe⟩, hxg⟩ := (interior_subset hx : x ∈ {x | _})
  have hfx : f x = e₀ x := hfe₀ ⟨hxU, hxe⟩
  obtain ⟨m, hm⟩ := hfinl x hxU
  rw [sectorSmulInl_apply, ← hxg, ← hfx, ← hm, e0Inl_symm_inl]

end E0

end GX
