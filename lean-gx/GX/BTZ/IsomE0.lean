import GX.BTZ.AbsMax
import GX.BTZ.SectorAtlas
import GX.SingularII.Tame
import GX.SingularII.Models

/-!
# `GX.BTZ.IsomE0` — `btzprop:isom` in its global form for `𝔼₀`, and two corollaries

Target T-btz-isom-e0. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`), § 2.1, at
`α = β = 0`. The three rows are unmarked: the paper states them for every `α, β ∈ ℝ₊`, `α ≠ 2π`,
and only `𝔼₀` is formalized (its scope waits on T-btz-scope). **0 `sorry`**, standard axioms.

* `btzprop:isom` — `BTZ_1.tex:378–383` (at `α = β = 0`): `GX.BTZIsom.btzprop_isom_e0`.
* `btzcor:indeed_group_isometries` — `BTZ_1.tex:385–386` (at `α = 0`):
  `GX.BTZIsom.btzcor_indeed_group_isometries_e0`, with `isomE0_trans`, `isomE0_symm`,
  `isomE0_zero`.
* `btzcor:morphism_two_manifolds_local` — `BTZ_1.tex:391–393` (singular model `𝔼₀`):
  `GX.BTZIsom.btzcor_morphism_two_manifolds_local_e0`.

> We define for $\alpha\geq 0$:
> $$\isom(\E^{1,2}_\alpha) = \{(t,r,\theta)\mapsto (t+t_0,r,\theta+\theta_0): (t_0,\theta_0) \in \RR^2\}.$$
> (l.372–373)

> **Proposition** (`btzprop:isom`). Let $\alpha,\beta\in \R_+$ with $\alpha\neq 2\pi$, and let $\U$
> be an open connected subset of $\E^{1,2}_\alpha$ containing a singular point and let
> $\phi:\U\rightarrow \E^{1,2}_\beta$ be an almost everywhere $\mass{}$-morphism.
> If $\phi$ is a local homeomorphism then $\alpha=\beta$ and $\phi$ is the restriction of an
> element of $\isom(\E^{1,2}_\alpha)$.

> **Corollary** (`btzcor:indeed_group_isometries`). For $\alpha\in \RR_+$, $\isom(\mass{\alpha})$
> is indeed the group of isometries of $\mass{\alpha}$.

> **Corollary** (`btzcor:morphism_two_manifolds_local`). Let $\phi:M\rightarrow N$ an a.e.
> $\mass{}$-morphism with $M,N$ two $\mass{\geq0}$-manifolds. If $\phi$ is a local homeomorphism,
> then $\phi$ is a local diffeomorphisms.

## What is proved

* `isomE0 τ₀ θ₀ : BTZE0 ≃ₜ BTZE0`, the paper's `(τ, r, θ) ↦ (τ + τ₀, r, θ + θ₀)` read through
  `GX.E0.toPaper` (`(τ, z) ↦ (τ + τ₀, e^{iθ₀} z)`), and its group laws.
* `isomE0` is an a.e. `𝕄`-morphism of `𝔼₀` (`isAEMorphism_isomE0`) and its lift to
  `Y = 𝕄 ⊕ 𝔼₀` lies in the groupoid `G = e0Groupoid` (`e0Lift_isomE0_mem`): in the sector charts
  it is the parabolic `P_{−c}` followed by the translation `2τ₀ u` (`btzPaperDev_shift_angle`,
  `chartMap_paperIsom`).
* **The reflection is excluded** (`not_conj_localForm`): no element of `G` reads near an axis
  point as `(τ, z) ↦ (τ + a, ω z̄)` — in the sector charts it would be `(a, b, c) ↦ (a, b, −c)` in
  null coordinates, of determinant `−1` (`no_isom_reflect`), while `Isom(𝐌³) = SO₀(1,2) ⋉ ℝ³`. So
  the linear isometry `R` of `GX.E0AbsMax.e0Loop_localForm` is a rotation.
* `btzprop:isom` at `α = β = 0` (`btzprop_isom_e0`). Proof: `φ` is a `𝕄`-morphism on all of
  `reg U` (`lem:GX_sing_homeo_reg`, `isRegularOn_reg_of_isLocalHomeomorph`), hence a local
  `G`-structomorphism read on `Y` (`exists_mem_e0Groupoid_liftY`); on a connected neighbourhood of
  the singular point where `φ` is injective (the paper's « without loss of generality ») the strict
  `GX.e0_localUnique_sing` gives `e ∈ G`, `GX.E0AbsMax.e0Loop_localForm` its local form, the
  rotation case is `isomE0`; Liouville in `G` (`GX.e0_rigid`, `GX.e0_eqOn_of_eqOn_open`) on the
  connected `reg U`, and density of `reg U`, globalise.
* `btzcor:indeed_group_isometries` at `α = 0`: a homeomorphism `Ψ` of `𝔼₀` with `Ψ`, `Ψ⁻¹` a.e.
  `𝕄`-morphisms is an `isomE0`, and conversely.
* The reflection `reflE0 : (τ, r, θ) ↦ (τ, r, −θ)` is, through the developing map, the linear map
  `(a, b, c) ↦ (a, b, −c)` preserving `c² − ab` (`btzPaperDev_refl`): an isometry of the printed
  metric; it is not in `isom(𝔼₀)` (`reflE0_ne_isomE0`) and not an a.e. `𝕄`-morphism
  (`not_isAEMorphism_reflE0`). See SCOPE (b).
* `btzcor:morphism_two_manifolds_local`, `𝔼₀` the singular model: on `Reg M` the map is a
  `𝕄`-morphism into `Reg N`, `φ⁻¹(Sing N) = Sing M`, and in any two `𝔼₀`-charts at a singular `x`
  and at `φ x` it is near `x` an element of `isom(𝔼₀)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `α, β ∈ ℝ₊`, `α ≠ 2π` | ⚠ `α = β = 0` only (`𝔼₀ = GX.BTZE0`); `α = β` is then vacuous |
| `𝒰` open connected, containing a singular point | ✓ carried: `U : Opens BTZE0`, `IsConnected U`, `∃ x ∈ U, x ∉ Reg` |
| `φ` an a.e. `𝕄`-morphism (l.359) | ✓ carried: `IsAEMorphism (Isom(𝐌³)) 𝐌³ φ`, `U` with its induced structure (`GX.opensSingularGXStructure`) |
| `φ` a local homeomorphism | ✓ carried: `IsLocalHomeomorph φ` |
| `isom(𝔼₀)` (l.372–373) | ✓ the paper's set, `isomE0 τ₀ θ₀` |
| « the group of isometries of `𝔼₀` » | ⚠ read: the automorphisms of `𝔼₀` as a singular `(Isom₀(𝕄), 𝕄)`-manifold, SCOPE (b) |
| `M, N` two `𝔼_{≥0}`-manifolds | ⚠ weakened: `M, N` any singular `𝕄`-manifolds; the conclusion at singular points is stated in `𝔼₀`-charts (types `α > 0` not covered) |
| « local diffeomorphism » | ⚠ read: a local isomorphism of the `𝔼₀`-atlases, SCOPE (c) |

## SCOPE (disclosed)

* (a) `α = β = 0` only; the rows are unmarked for that reason (T-btz-scope).
* (b) « isometries of `𝔼₀` » is read as the automorphisms of `𝔼₀` as a singular
  `(Isom₀(𝕄), 𝕄)`-manifold (homeomorphisms which are a.e. `𝕄`-morphisms both ways); the
  structure group is `Isom₀(𝕄)`, orientation and time-orientation preserving (l.203). This is the
  paper's frame (l.203, l.266–270); the metric reading would also admit `reflE0`, which preserves
  `ds₀²` (`btzPaperDev_refl`) and is not in `isom(𝔼₀)` (`reflE0_ne_isomE0`) — an imprecise
  wording (« orientation- and time-orientation-preserving isometries » would be exact).
* (c) « local diffeomorphism » is read as: in the `𝔼₀`-atlas (regular charts at regular points;
  at a singular point, homeomorphisms `κ : U ≃ₜ V ⊆ 𝔼₀` which are a.e. `𝕄`-morphisms, the paper's
  « neighbourhood which embeds by an a.e. `𝔼`-morphism into `𝔼_α` », l.271), `φ` reads as an element
  of `Isom(𝐌³)` near regular points and of `isom(𝔼₀)` near singular points. No smooth structure on
  `M` is built (that is `btzcor:manifold_smooth_manifold_singular`, not in scope).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal (imports
`Causal.*` through `GX.BTZ.AbsMax`, DEC-33).
-/

namespace GX

namespace BTZIsom

open Set Filter Topology Function TopologicalSpace Complex
open scoped Real
open E0

attribute [local instance] btzE0Structure

/-! ### `isom(𝔼₀)` -/

/-- The paper's `(τ, r, θ) ↦ (τ + τ₀, r, θ + θ₀)` in the paper's coordinates `(τ, z)`. -/
noncomputable def paperIsom (τ₀ θ₀ : ℝ) : E0 ≃ₜ E0 := (tauShift τ₀).trans (rotE0 θ₀)

theorem paperIsom_apply (τ₀ θ₀ : ℝ) (w : E0) :
    paperIsom τ₀ θ₀ w = (w.1 + τ₀, cexp (θ₀ * I) * w.2) := rfl

/-- **`isom(𝔼₀)`**, an element: `(τ, r, θ) ↦ (τ + τ₀, r, θ + θ₀)` on `GX.BTZE0`. -/
noncomputable def isomE0 (τ₀ θ₀ : ℝ) : BTZE0 ≃ₜ BTZE0 :=
  toPaper.trans ((paperIsom τ₀ θ₀).trans toPaper.symm)

theorem toPaper_isomE0 (τ₀ θ₀ : ℝ) (x : BTZE0) :
    toPaper (isomE0 τ₀ θ₀ x) = paperIsom τ₀ θ₀ (toPaper x) := by
  simp [isomE0]

theorem paperIsom_symm_apply (τ₀ θ₀ : ℝ) (w : E0) :
    (paperIsom τ₀ θ₀).symm w = paperIsom (-τ₀) (-θ₀) w := by
  rw [Homeomorph.symm_apply_eq, paperIsom_apply, paperIsom_apply]
  refine Prod.ext (by simp) ?_
  simp only
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  rw [show (θ₀ : ℂ) * I + -(θ₀ : ℂ) * I = 0 by ring, Complex.exp_zero, one_mul]

theorem isomE0_symm (τ₀ θ₀ : ℝ) : (isomE0 τ₀ θ₀).symm = isomE0 (-τ₀) (-θ₀) := by
  ext x
  simp only [isomE0, Homeomorph.symm_trans_apply, Homeomorph.symm_symm, Homeomorph.trans_apply]
  rw [paperIsom_symm_apply]

theorem isomE0_trans (a b c d : ℝ) : (isomE0 a b).trans (isomE0 c d) = isomE0 (a + c) (b + d) := by
  ext x
  simp only [isomE0, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  congr 1
  rw [paperIsom_apply, paperIsom_apply, paperIsom_apply]
  refine Prod.ext (by simp only; ring) ?_
  simp only
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

theorem isomE0_zero : isomE0 0 0 = Homeomorph.refl BTZE0 := by
  ext x
  simp only [isomE0, Homeomorph.trans_apply, Homeomorph.refl_apply]
  rw [Homeomorph.symm_apply_eq, paperIsom_apply]
  simp

/-! ### `isom(𝔼₀)` in the sector charts -/

/-- The isometry `y ↦ P_{−c}(y) + (2τ₀, 0, 0)` (null coordinates) of `𝐌³`. -/
noncomputable def gShift (τ₀ c : ℝ) : Causal.Flat.isom 2 :=
  ⟨AffineEquiv.constVAdd ℝ (Causal.Minkowski 2) (nullToMink ((2 * τ₀ : ℝ), (0 : ℝ), (0 : ℝ))),
    Causal.Flat.constVAdd_mem_isom _⟩ * btzHol 0 (-c)

/-- **`D(τ + τ₀, r, θ + c) = gShift τ₀ c · D(τ, r, θ)`**. -/
theorem btzPaperDev_shift_angle (τ₀ c : ℝ) (p : ℝ × ℝ × ℝ) :
    btzPaperDev (p.1 + τ₀, p.2.1, p.2.2 + c) = gShift τ₀ c • btzPaperDev p := by
  rw [btzPaperDev_eq_nullToMink, btzPaperDev_eq_nullToMink, gShift, mul_smul]
  have h1 := btzHol_zpow_smul 0 (-c) 1 (btzPaperNull p)
  rw [zpow_one, zpow_one] at h1
  rw [h1, show parabAff 0 (-c) • btzPaperNull p = parabAff 0 (-c) (btzPaperNull p) from rfl,
    parabAff_apply]
  show _ = nullToMink ((2 * τ₀ : ℝ), (0 : ℝ), (0 : ℝ)) +ᵥ
    nullToMink (0 + parab (-c) (btzPaperNull p - 0))
  rw [vadd_eq_add, ← map_add]
  congr 1
  simp only [btzPaperNull, parab_apply, zero_add, sub_zero, Prod.mk_add_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- In the sector charts, `isom(𝔼₀)` is `gShift`. -/
theorem chartMap_paperIsom (τ₀ θ₀ : ℝ) (y w : E0) :
    chartMap (paperIsom τ₀ θ₀ y) (paperIsom τ₀ θ₀ w) =
      gShift τ₀ (arg (cexp (θ₀ * I) * y.2) - arg y.2) • chartMap y w := by
  rw [chartMap_eq, chartMap_eq, ← btzPaperDev_shift_angle]
  have hrad : rad (paperIsom τ₀ θ₀ w) = rad w := by
    rw [rad, rad, paperIsom_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hang : angle (paperIsom τ₀ θ₀ y) (paperIsom τ₀ θ₀ w) =
      angle y w + (arg (cexp (θ₀ * I) * y.2) - arg y.2) := by
    rw [angle, angle, paperIsom_apply, paperIsom_apply]
    simp only
    rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
    ring
  rw [hrad, hang, paperIsom_apply]

theorem paperIsom_snd_ne_zero (τ₀ θ₀ : ℝ) {y : E0} (hy : y.2 ≠ 0) : (paperIsom τ₀ θ₀ y).2 ≠ 0 := by
  rw [paperIsom_apply]; exact mul_ne_zero (Complex.exp_ne_zero _) hy

theorem paperIsom_mem_sector_iff (τ₀ θ₀ : ℝ) (y w : E0) :
    paperIsom τ₀ θ₀ w ∈ sector (paperIsom τ₀ θ₀ y) ↔ w ∈ sector y := by
  show (paperIsom τ₀ θ₀ w).2 / (paperIsom τ₀ θ₀ y).2 ∈ Complex.slitPlane ↔
    w.2 / y.2 ∈ Complex.slitPlane
  rw [paperIsom_apply, paperIsom_apply]
  simp only
  rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

theorem mem_sectorChartBTZ_source {y : E0} (hy : y.2 ≠ 0) {x : BTZE0} :
    x ∈ (sectorChartBTZ y hy).source ↔ toPaper x ∈ sector y := by
  simp [sectorChartBTZ, sectorChart]

theorem sectorChartBTZ_apply {y : E0} (hy : y.2 ≠ 0) (x : BTZE0) :
    sectorChartBTZ y hy x = chartMap y (toPaper x) := rfl

/-- **`isom(𝔼₀)` in the sector charts of `BTZE0`**: `gShift` on the whole sector. -/
theorem sectorChartBTZ_isomE0 (τ₀ θ₀ : ℝ) {y : E0} (hy : y.2 ≠ 0) (x : BTZE0) :
    sectorChartBTZ (paperIsom τ₀ θ₀ y) (paperIsom_snd_ne_zero τ₀ θ₀ hy) (isomE0 τ₀ θ₀ x) =
      gShift τ₀ (arg (cexp (θ₀ * I) * y.2) - arg y.2) • sectorChartBTZ y hy x := by
  rw [sectorChartBTZ_apply, sectorChartBTZ_apply, toPaper_isomE0, chartMap_paperIsom]

theorem e0RegAt_e0Lift_isomE0 (τ₀ θ₀ : ℝ) (x : BTZE0) :
    E0RegAt (e0Lift (isomE0 τ₀ θ₀)) (Sum.inr x) := by
  have hcont : ContinuousAt (e0Lift (isomE0 τ₀ θ₀)) (Sum.inr x) :=
    (e0Lift _).continuousAt (by rw [e0Lift_source]; exact ⟨x, rfl⟩)
  by_cases hx : (Sum.inr x : E0Y) ∈ e0Reg
  swap
  · exact ⟨hcont, fun h => absurd h hx⟩
  set y := toPaper x with hyx
  have hy : y.2 ≠ 0 := inr_mem_e0Reg_iff_toPaper.1 hx
  have hy' := paperIsom_snd_ne_zero τ₀ θ₀ hy
  have hsrc : (Sum.inr x : E0Y) ∈ (sectorChartY y hy).source := by
    have := paperInY_mem_sectorChartY_source hy (mem_sector_self hy)
    rwa [paperInY_apply, show toPaper.symm y = x from toPaper.symm_apply_apply x] at this
  have himg : e0Lift (isomE0 τ₀ θ₀) (Sum.inr x) = E0.paperInY (paperIsom τ₀ θ₀ y) := by
    rw [e0Lift_apply, paperInY_apply, ← toPaper_isomE0, Homeomorph.symm_apply_apply]
  refine e0RegAt_of_exists hcont ⟨sectorChartY y hy, sectorChartY_mem_e0Atlas hy,
    sectorChartY (paperIsom τ₀ θ₀ y) hy', sectorChartY_mem_e0Atlas hy', hsrc, ?_,
    gShift τ₀ (arg (cexp (θ₀ * I) * y.2) - arg y.2), ?_⟩
  · rw [himg]; exact paperInY_mem_sectorChartY_source hy' (mem_sector_self hy')
  · filter_upwards [(sectorChartY y hy).open_source.mem_nhds hsrc] with z hz
    rw [sectorChartY] at hz
    obtain ⟨x', -, rfl⟩ := mem_e0InrChart_source.1 hz
    rw [e0Lift_apply, sectorChartY, sectorChartY, e0InrChart_inr, e0InrChart_inr]
    exact sectorChartBTZ_isomE0 τ₀ θ₀ hy x'

/-- **`isom(𝔼₀)` is an a.e. `𝕄`-morphism of `𝔼₀`.** -/
theorem isAEMorphism_isomE0 (τ₀ θ₀ : ℝ) :
    IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) (isomE0 τ₀ θ₀) := by
  have hA := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
  refine (isAEMorphismOf_iff hA.1).2 ⟨(isomE0 τ₀ θ₀).continuous, _,
    isPortly_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0, ?_⟩
  refine IsRegularOn.of_exists hA.1.1 hA.1.1
    (isOpen_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) subset_rfl ?_
    (isomE0 τ₀ θ₀).continuous.continuousOn fun x hx => ?_
  · intro x hx
    show isomE0 τ₀ θ₀ x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
    rw [mem_reg_iff_toPaper] at hx ⊢
    rw [toPaper_isomE0]
    exact paperIsom_snd_ne_zero τ₀ θ₀ hx
  · have hy : (toPaper x).2 ≠ 0 := (mem_reg_iff_toPaper x).1 hx
    have hy' := paperIsom_snd_ne_zero τ₀ θ₀ hy
    refine ⟨sectorChartBTZ (toPaper x) hy, sectorChartBTZ_mem_aeAtlas hy,
      sectorChartBTZ (paperIsom τ₀ θ₀ (toPaper x)) hy', sectorChartBTZ_mem_aeAtlas hy',
      (mem_sectorChartBTZ_source hy).2 (mem_sector_self hy), ?_, _,
      Eventually.of_forall fun z => sectorChartBTZ_isomE0 τ₀ θ₀ hy z⟩
    rw [mem_sectorChartBTZ_source, toPaper_isomE0]
    exact mem_sector_self hy'

/-- **`isom(𝔼₀)` lifted to `Y = 𝕄 ⊕ 𝔼₀` lies in the groupoid `G`.** -/
theorem e0Lift_isomE0_mem (τ₀ θ₀ : ℝ) : e0Lift (isomE0 τ₀ θ₀) ∈ e0Groupoid := by
  refine mem_e0Groupoid_iff.2 ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [e0Lift_source] at hz
    obtain ⟨x, rfl⟩ := hz
    exact e0RegAt_e0Lift_isomE0 τ₀ θ₀ x
  · rw [e0Lift_target] at hz
    obtain ⟨x, rfl⟩ := hz
    refine (e0RegAt_e0Lift_isomE0 (-τ₀) (-θ₀) x).congr ?_
    filter_upwards [isOpen_range_inr.mem_nhds ⟨x, rfl⟩] with w hw
    obtain ⟨z, rfl⟩ := hw
    rw [e0Lift_symm_apply, e0Lift_apply, isomE0_symm]

/-! ### The reflection is not in `G` -/

theorem arg_exp_mul_I_of_mem {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) : arg (cexp (θ * I)) = θ := by
  rw [arg_exp_mul_I, toIocMod_eq_self]; constructor <;> linarith

/-- Coordinates `ℝ × ℝ × ℝ ≃ ℝ³`, to compute a determinant. -/
noncomputable def coords3 : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun y := ![y.1, y.2.1, y.2.2]
  invFun v := (v 0, v 1, v 2)
  map_add' y y' := by funext i; fin_cases i <;> simp
  map_smul' c y := by funext i; fin_cases i <;> simp
  left_inv y := by simp
  right_inv v := by funext i; fin_cases i <;> simp

/-- **No isometry of `𝐌³` is, near a regular point `(τ₀, ρ, 0)`, the reflection `θ ↦ −θ` read
through the developing map**: in null coordinates its linear part would be
`(a, b, c) ↦ (a, b, −c)`, of determinant `−1`. -/
theorem no_isom_reflect {τ₀ ρ : ℝ} (hρ : 0 < ρ) (h : Causal.Flat.isom 2)
    (H : ∀ᶠ p in 𝓝 ((τ₀, ρ, 0) : ℝ × ℝ × ℝ),
      btzPaperDev (p.1, p.2.1, -p.2.2) = h • btzPaperDev p) : False := by
  obtain ⟨ε, hε, hH⟩ := Metric.eventually_nhds_iff.1 H
  set s := ε / 2 with hs
  have hs0 : 0 < s := by positivity
  have hsε : s < ε := by linarith
  have hA : (h : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear ∈ Causal.Flat.lorentz 2 := h.2
  let N : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ) :=
    nullToMink.trans ((h : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear.trans nullToMink.symm)
  have hN : ∀ y, (h : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear (nullToMink y) =
      nullToMink (N y) := fun y => by
    show _ = nullToMink (nullToMink.symm _)
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have e0 : nullToMink (btzPaperNull (τ₀, ρ, -0)) = h • nullToMink (btzPaperNull (τ₀, ρ, 0)) := by
    have := hH (y := (τ₀, ρ, 0)) (by rw [dist_self]; exact hε)
    rwa [btzPaperDev_eq_nullToMink, btzPaperDev_eq_nullToMink] at this
  have key : ∀ q : ℝ × ℝ × ℝ, dist q (τ₀, ρ, 0) < ε →
      N (btzPaperNull q - btzPaperNull (τ₀, ρ, 0)) =
        btzPaperNull (q.1, q.2.1, -q.2.2) - btzPaperNull (τ₀, ρ, -0) := by
    intro q hq
    have e1 := hH hq
    rw [btzPaperDev_eq_nullToMink, btzPaperDev_eq_nullToMink] at e1
    apply nullToMink.injective
    rw [← hN, map_sub, map_sub, map_sub, e1, e0, Causal.Flat.isom_smul_def,
      Causal.Flat.isom_smul_def, Causal.Flat.isom_sub]
    exact (map_sub _ _ _).symm
  have hd1 : dist ((τ₀ + s, ρ, 0) : ℝ × ℝ × ℝ) (τ₀, ρ, 0) < ε := by
    simp [Prod.dist_eq, abs_of_pos hs0, hsε, hε]
  have hd2 : dist ((τ₀, ρ + s, 0) : ℝ × ℝ × ℝ) (τ₀, ρ, 0) < ε := by
    simp [Prod.dist_eq, abs_of_pos hs0, hsε, hε]
  have hd3 : dist ((τ₀, ρ, s) : ℝ × ℝ × ℝ) (τ₀, ρ, 0) < ε := by
    simp [Prod.dist_eq, abs_of_pos hs0, hsε, hε]
  have k1 := key _ hd1
  have k2 := key _ hd2
  have k3 := key _ hd3
  have E1 : btzPaperNull (τ₀ + s, ρ, 0) - btzPaperNull (τ₀, ρ, 0) =
      (2 * s) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [btzPaperNull, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> ring
  have F1 : btzPaperNull (((τ₀ + s, ρ, 0) : ℝ × ℝ × ℝ).1, ((τ₀ + s, ρ, 0) : ℝ × ℝ × ℝ).2.1,
      -((τ₀ + s, ρ, 0) : ℝ × ℝ × ℝ).2.2) - btzPaperNull (τ₀, ρ, -0) =
      (2 * s) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [btzPaperNull, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> ring
  have E2 : btzPaperNull (τ₀, ρ + s, 0) - btzPaperNull (τ₀, ρ, 0) =
      s • ((-1 : ℝ), (1 : ℝ), (0 : ℝ)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [btzPaperNull, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> ring
  have F2 : btzPaperNull (((τ₀, ρ + s, 0) : ℝ × ℝ × ℝ).1, ((τ₀, ρ + s, 0) : ℝ × ℝ × ℝ).2.1,
      -((τ₀, ρ + s, 0) : ℝ × ℝ × ℝ).2.2) - btzPaperNull (τ₀, ρ, -0) =
      s • ((-1 : ℝ), (1 : ℝ), (0 : ℝ)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [btzPaperNull, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] <;> ring
  have E3 : btzPaperNull (τ₀, ρ, s) - btzPaperNull (τ₀, ρ, 0) =
      (ρ * s ^ 2) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + (-(ρ * s)) • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [btzPaperNull, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, Prod.fst_add, Prod.snd_add] <;> ring
  have F3 : btzPaperNull (((τ₀, ρ, s) : ℝ × ℝ × ℝ).1, ((τ₀, ρ, s) : ℝ × ℝ × ℝ).2.1,
      -((τ₀, ρ, s) : ℝ × ℝ × ℝ).2.2) - btzPaperNull (τ₀, ρ, -0) =
      (ρ * s ^ 2) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + (ρ * s) • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [btzPaperNull, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, Prod.fst_add, Prod.snd_add] <;> ring
  rw [E1, F1, map_smul] at k1
  rw [E2, F2, map_smul] at k2
  rw [E3, F3, map_add, map_smul, map_smul] at k3
  have n1 : N ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = ((1 : ℝ), (0 : ℝ), (0 : ℝ)) :=
    smul_right_injective _ (by positivity : (2 * s : ℝ) ≠ 0) k1
  have n2' : N ((-1 : ℝ), (1 : ℝ), (0 : ℝ)) = ((-1 : ℝ), (1 : ℝ), (0 : ℝ)) :=
    smul_right_injective _ hs0.ne' k2
  have n2 : N ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = ((0 : ℝ), (1 : ℝ), (0 : ℝ)) := by
    have e : ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = ((-1 : ℝ), (1 : ℝ), (0 : ℝ)) +
        ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rw [e, map_add, n1, n2']
  have n3 : N ((0 : ℝ), (0 : ℝ), (1 : ℝ)) = ((0 : ℝ), (0 : ℝ), (-1 : ℝ)) := by
    rw [n1] at k3
    have hne : ρ * s ≠ 0 := (mul_pos hρ hs0).ne'
    have c1 := congrArg (fun w : ℝ × ℝ × ℝ => w.1) k3
    have c2 := congrArg (fun w : ℝ × ℝ × ℝ => w.2.1) k3
    have c3 := congrArg (fun w : ℝ × ℝ × ℝ => w.2.2) k3
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at c1 c2 c3
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · have : (ρ * s) * (N ((0 : ℝ), (0 : ℝ), (1 : ℝ))).1 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    · have : (ρ * s) * (N ((0 : ℝ), (0 : ℝ), (1 : ℝ))).2.1 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    · have : (ρ * s) * ((N ((0 : ℝ), (0 : ℝ), (1 : ℝ))).2.2 + 1) = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_left hne
      show _ = (-1 : ℝ)
      linarith
  have hNy : ∀ a b c : ℝ, N (a, b, c) = (a, b, -c) := by
    intro a b c
    have e : ((a, b, c) : ℝ × ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
        b • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rw [e, map_add, map_add, map_smul, map_smul, map_smul, n1, n2, n3]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  have hdet1 : LinearMap.det (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) = 1 := by
    have e : ((h : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear :
        Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) =
        (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2) ∘ₗ
        (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
          (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] _) := by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [← hN, LinearEquiv.apply_symm_apply]
    rw [← LinearMap.det_conj (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) nullToMink, ← e]
    exact Causal.Flat.lorentz.det_eq_one hA
  have hdetm : LinearMap.det (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) = -1 := by
    rw [← LinearMap.det_conj (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) coords3,
      ← LinearMap.det_toMatrix', Matrix.det_fin_three]
    simp [LinearMap.toMatrix'_apply, coords3, hNy]
  rw [hdet1] at hdetm
  norm_num at hdetm

/-- **No element of `G` reads, near an axis point, as `(τ, z) ↦ (τ + a, ω z̄)`**: in the sector
charts it would be the reflection `c ↦ −c` of the null coordinates, of determinant `−1`. -/
theorem not_conj_localForm {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid)
    {τ₀ δ a : ℝ} (hδ : 0 < δ) (ω : Circle)
    (h : ∀ u : E0, dist u (τ₀, 0) < δ → E0.paperInY u ∈ e.source ∧
      e (E0.paperInY u) = E0.paperInY (u.1 + a, (ω : ℂ) * (starRingEnd ℂ) u.2)) : False := by
  set ρ := δ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  set u₁ : E0 := (τ₀, (ρ : ℂ)) with hu₁def
  have hu₁d : dist u₁ (τ₀, 0) < δ := by
    rw [hu₁def, Prod.dist_eq, dist_self, Complex.dist_eq, sub_zero, Complex.norm_real,
      Real.norm_of_nonneg hρ.le, max_eq_right hρ.le]
    linarith
  obtain ⟨hsrc, himg⟩ := h u₁ hu₁d
  have hu₁ : u₁.2 ≠ 0 := ofReal_ne_zero.2 hρ.ne'
  set u₁' : E0 := (τ₀ + a, (ω : ℂ) * ρ) with hu₁'def
  have himg' : e (E0.paperInY u₁) = E0.paperInY u₁' := by
    rw [himg, hu₁def, hu₁'def, Complex.conj_ofReal]
  have hu₁' : u₁'.2 ≠ 0 := mul_ne_zero (Circle.coe_ne_zero ω) (ofReal_ne_zero.2 hρ.ne')
  obtain ⟨-, hreg⟩ := (mem_e0Groupoid_iff.1 he).1 _ hsrc
  obtain ⟨-, hch⟩ := hreg (paperInY_mem_e0Reg_iff.2 hu₁)
  obtain ⟨g, hg⟩ := hch _ (sectorChartY_mem_e0Atlas hu₁) _ (sectorChartY_mem_e0Atlas hu₁')
    (paperInY_mem_sectorChartY_source hu₁ (mem_sector_self hu₁))
    (by rw [himg']; exact paperInY_mem_sectorChartY_source hu₁' (mem_sector_self hu₁'))
  set P : ℝ × ℝ × ℝ → E0 := fun p => (p.1, (p.2.1 : ℂ) * cexp (p.2.2 * I)) with hPdef
  have hPc : Continuous P := by
    refine continuous_fst.prodMk ?_
    exact (continuous_ofReal.comp (continuous_fst.comp continuous_snd)).mul
      (Complex.continuous_exp.comp
        ((continuous_ofReal.comp (continuous_snd.comp continuous_snd)).mul continuous_const))
  have hP0 : P (τ₀, ρ, 0) = u₁ := by simp [P, u₁]
  have hT : Tendsto (fun p => E0.paperInY (P p)) (𝓝 ((τ₀, ρ, 0) : ℝ × ℝ × ℝ))
      (𝓝 (E0.paperInY u₁)) := by
    rw [← hP0]; exact (E0Spear.continuous_paperInY.comp hPc).continuousAt.tendsto
  have hev1 := hT.eventually hg
  have hev2 : ∀ᶠ p in 𝓝 ((τ₀, ρ, 0) : ℝ × ℝ × ℝ), dist (P p) (τ₀, 0) < δ :=
    ContinuousAt.eventually_lt (hPc.dist continuous_const).continuousAt continuousAt_const
      (show dist (P (τ₀, ρ, 0)) (τ₀, 0) < δ by rw [hP0]; exact hu₁d)
  have hev3 : ∀ᶠ p in 𝓝 ((τ₀, ρ, 0) : ℝ × ℝ × ℝ), 0 < p.2.1 :=
    ContinuousAt.eventually_lt continuousAt_const
      (continuous_fst.comp continuous_snd).continuousAt hρ
  have hev4 : ∀ᶠ p in 𝓝 ((τ₀, ρ, 0) : ℝ × ℝ × ℝ), p.2.2 < 1 :=
    ContinuousAt.eventually_lt (continuous_snd.comp continuous_snd).continuousAt
      continuousAt_const (by norm_num)
  have hev5 : ∀ᶠ p in 𝓝 ((τ₀, ρ, 0) : ℝ × ℝ × ℝ), -1 < p.2.2 :=
    ContinuousAt.eventually_lt continuousAt_const
      (continuous_snd.comp continuous_snd).continuousAt (by norm_num)
  refine no_isom_reflect (τ₀ := τ₀) hρ ((gShift a (arg ((ω : ℂ) * ρ)))⁻¹ * g) ?_
  filter_upwards [hev1, hev2, hev3, hev4, hev5] with p h1 h2 h3 h4 h5
  obtain ⟨τ, r, θ⟩ := p
  rw [(h _ h2).2, sectorChartY_paperInY, sectorChartY_paperInY] at h1
  have hpi : (1 : ℝ) < π := by linarith [Real.pi_gt_three]
  have hrP : rad (P (τ, r, θ)) = r := by
    simp only [P, rad, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_of_nonneg h3.le]
  have haP : angle u₁ (P (τ, r, θ)) = θ := by
    simp only [angle, P, u₁, arg_ofReal_of_nonneg hρ.le, zero_add]
    rw [show (r : ℂ) * cexp (θ * I) / (ρ : ℂ) = ((r / ρ : ℝ) : ℂ) * cexp (θ * I) by
      push_cast; field_simp, arg_real_mul _ (div_pos h3 hρ)]
    exact arg_exp_mul_I_of_mem (by linarith) (by linarith)
  have hconj : (starRingEnd ℂ) ((P (τ, r, θ)).2) = (r : ℂ) * cexp ((-θ : ℝ) * I) := by
    simp only [P, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    push_cast; ring_nf
  have hrQ : rad (((P (τ, r, θ)).1 + a, (ω : ℂ) * (starRingEnd ℂ) (P (τ, r, θ)).2) : E0) = r := by
    simp only [rad]
    rw [hconj, norm_mul, Circle.norm_coe, norm_mul, Complex.norm_real,
      Complex.norm_exp_ofReal_mul_I, one_mul, mul_one, Real.norm_of_nonneg h3.le]
  have haQ : angle u₁' (((P (τ, r, θ)).1 + a, (ω : ℂ) * (starRingEnd ℂ) (P (τ, r, θ)).2) : E0) =
      arg ((ω : ℂ) * ρ) + -θ := by
    simp only [angle, u₁']
    rw [hconj, show (ω : ℂ) * ((r : ℂ) * cexp ((-θ : ℝ) * I)) / ((ω : ℂ) * (ρ : ℂ)) =
      ((r / ρ : ℝ) : ℂ) * cexp ((-θ : ℝ) * I) by
      push_cast; field_simp, arg_real_mul _ (div_pos h3 hρ),
      arg_exp_mul_I_of_mem (by linarith) (by linarith)]
  rw [hrP, haP, hrQ, haQ] at h1
  rw [mul_smul, eq_inv_smul_iff, ← btzPaperDev_shift_angle]
  convert h1 using 2
  simp only [P]
  ring_nf

/-! ### Local `G`-structomorphisms from a.e. morphisms -/

section Regular

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) N]

/-- An a.e. `𝕄`-morphism which is a local homeomorphism induces a `𝕄`-morphism on the whole
regular locus (`lem:GX_sing_homeo_reg`), which it maps into the regular locus. -/
theorem isRegularOn_reg_of_isLocalHomeomorph {f : M → N}
    (hf : IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) f) (hl : IsLocalHomeomorph f) :
    IsRegularOn (Causal.Flat.isom 2) (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) N) f
      (Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M) := by
  have h1 := hf.regLocus_eq_inter_isLocalHomeomorphOn
  have h2 : regLocus (Causal.Flat.isom 2) (Causal.Minkowski 2) f =
      Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M := by
    rw [h1]
    exact inter_eq_left.2 fun x _ => hl.isLocalHomeomorphOn.mono (subset_univ _)
  rw [← h2]
  exact isRegularOn_regLocusOf _ _ _

end Regular

/-- An open partial homeomorphism of `Y` which is, near every point of its source, a translation
by `Isom(𝐌³)` between two regular charts, belongs to `G` (its source and target are then regular). -/
theorem mem_e0Groupoid_of_charts {e : OpenPartialHomeomorph E0Y E0Y}
    (h : ∀ x ∈ e.source, ∃ c ∈ e0Atlas, ∃ c' ∈ e0Atlas, x ∈ c.source ∧ e x ∈ c'.source ∧
      ∃ g : Causal.Flat.isom 2, ∀ᶠ y in 𝓝 x, c' (e y) = g • c y) : e ∈ e0Groupoid := by
  refine mem_e0Groupoid_iff.2 ⟨fun x hx => e0RegAt_of_exists (e.continuousAt hx) (h x hx),
    fun w hw => ?_⟩
  have hx := e.map_target hw
  obtain ⟨c, hc, c', hc', hxc, hexc, g, hg⟩ := h _ hx
  rw [e.right_inv hw] at hexc
  refine e0RegAt_of_exists (e.continuousAt_symm hw) ⟨c', hc', c, hc, hexc, hxc, g⁻¹, ?_⟩
  have hT : Tendsto e.symm (𝓝 w) (𝓝 (e.symm w)) := e.continuousAt_symm hw
  filter_upwards [hT.eventually hg, e.open_target.mem_nhds hw] with v hv hvt
  rw [e.right_inv hvt] at hv
  rw [hv, inv_smul_smul]

/-- `φ : U → 𝔼₀` read on `Y = 𝕄 ⊕ 𝔼₀` (the identity off `U`). -/
noncomputable def liftY (U : Opens BTZE0) (φ : U → BTZE0) : E0Y → E0Y
  | Sum.inl m => Sum.inl m
  | Sum.inr x => haveI := Classical.propDecidable (x ∈ U)
      if h : x ∈ U then Sum.inr (φ ⟨x, h⟩) else Sum.inr x

theorem liftY_inr {U : Opens BTZE0} (φ : U → BTZE0) {x : BTZE0} (hx : x ∈ U) :
    liftY U φ (Sum.inr x) = Sum.inr (φ ⟨x, hx⟩) := by
  simp [liftY, hx]

/-- **An a.e. `𝕄`-morphism `φ : U → 𝔼₀` which is a local homeomorphism is, at every regular
point of `U`, a local `G`-structomorphism** (read on `Y`). -/
theorem exists_mem_e0Groupoid_liftY {U : Opens BTZE0} {φ : U → BTZE0}
    (hφ : IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) φ) (hloc : IsLocalHomeomorph φ)
    {x : BTZE0} (hxU : x ∈ U) (hxR : x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) :
    ∃ e ∈ e0Groupoid, (Sum.inr x : E0Y) ∈ e.source ∧ EqOn (liftY U φ) e e.source := by
  have hreg := isRegularOn_reg_of_isLocalHomeomorph hφ hloc
  have hval := isRegularOn_reg_of_isLocalHomeomorph
    (isAEMorphism_opensSingular_val (G := Causal.Flat.isom 2) (X := Causal.Minkowski 2) U)
    U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hRU : ∀ {q : U}, q ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) U ↔
      (q : BTZE0) ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    intro q; rw [reg_opensSingular]; rfl
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨h, hxh, hφh⟩ := hloc ⟨x, hxU⟩
  set h' := h.restrOpen (Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) U)
    (isOpen_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) U) with hh'
  set ι := U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → BTZE0)
    with hι
  set e := e0Inr.symm.trans (ι.symm.trans (h'.trans e0Inr)) with he
  have hsrc : ∀ z ∈ e.source, ∃ q : U, q ∈ h'.source ∧ z = Sum.inr (q : BTZE0) := by
    intro z hz
    rw [he, OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [e0Inr_symm_source] at hz1
    obtain ⟨y, rfl⟩ := hz1
    rw [mem_preimage, e0Inr_symm_inr, OpenPartialHomeomorph.trans_source] at hz2
    obtain ⟨hy1, hy2⟩ := hz2
    rw [OpenPartialHomeomorph.symm_source, hι,
      IsOpenEmbedding.toOpenPartialHomeomorph_target] at hy1
    obtain ⟨q, rfl⟩ := hy1
    rw [mem_preimage, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv,
      OpenPartialHomeomorph.trans_source] at hy2
    exact ⟨q, hy2.1, rfl⟩
  have happ : ∀ q : U, e (Sum.inr (q : BTZE0)) = Sum.inr (φ q) := by
    intro q
    rw [he, hι]
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply, e0Inr_symm_inr,
      IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, e0Inr_apply]
    rw [hφh]
    rfl
  have hmem : ∀ q : U, q ∈ h'.source → (Sum.inr (q : BTZE0) : E0Y) ∈ e.source := by
    intro q hq
    rw [he, OpenPartialHomeomorph.trans_source, e0Inr_symm_source]
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [mem_preimage, e0Inr_symm_inr, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, hι, IsOpenEmbedding.toOpenPartialHomeomorph_target]
    refine ⟨⟨q, rfl⟩, ?_⟩
    rw [mem_preimage, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv,
      OpenPartialHomeomorph.trans_source, e0Inr_source]
    exact ⟨hq, trivial⟩
  have hxs : (⟨x, hxU⟩ : U) ∈ h'.source := ⟨hxh, hRU.2 hxR⟩
  refine ⟨e, mem_e0Groupoid_of_charts ?_, hmem _ hxs, ?_⟩
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := hsrc z hz
    have hqR := hq.2
    obtain ⟨a, ha, hqa⟩ := mem_support.1 hqR
    obtain ⟨c₁, hc₁, hqc₁⟩ := mem_support.1 (hRU.1 hqR)
    obtain ⟨c₂, hc₂, hqc₂⟩ := mem_support.1 (hreg.mapsTo hqR)
    obtain ⟨g₁, hg₁⟩ := hval.exists_smul_eq q hqR a ha c₁ hc₁ hqa hqc₁
    obtain ⟨g₂, hg₂⟩ := hreg.exists_smul_eq q hqR a ha c₂ hc₂ hqa hqc₂
    refine ⟨_, e0InrChart_mem_e0Atlas hc₁, _, e0InrChart_mem_e0Atlas hc₂,
      mem_e0InrChart_source.2 ⟨_, hqc₁, rfl⟩,
      by rw [happ q]; exact mem_e0InrChart_source.2 ⟨_, hqc₂, rfl⟩, g₂ * g₁⁻¹, ?_⟩
    rw [← IsOpenEmbedding.inr.map_nhds_eq, eventually_map,
      ← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq, eventually_map]
    filter_upwards [hg₁, hg₂] with q' h1 h2
    rw [happ q', e0InrChart_inr, e0InrChart_inr, h2, mul_smul, h1, inv_smul_smul]
  · intro z hz
    obtain ⟨q, -, rfl⟩ := hsrc z hz
    rw [happ q, liftY_inr φ q.2]

/-! ### `btzprop:isom` at `α = β = 0` -/

/-- **`btzprop:isom` at `α = β = 0`** (`BTZ_1.tex:378–383`): an a.e. `𝕄`-morphism
`φ : U → 𝔼₀`, `U` an open connected subset of `𝔼₀` containing a singular point, which is a local
homeomorphism, is the restriction of an element of `isom(𝔼₀)`. -/
theorem btzprop_isom_e0 (U : Opens BTZE0) (hUc : IsConnected (U : Set BTZE0))
    (hU : ∃ x ∈ U, x ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)
    (φ : U → BTZE0) (hφ : IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) φ)
    (hloc : IsLocalHomeomorph φ) :
    ∃ τ₀ θ₀ : ℝ, ∀ x : U, φ x = isomE0 τ₀ θ₀ x := by
  haveI : ConnectedSpace BTZE0 := (btz_instances btz_two_pi_ne_zero).2.2.2
  haveI : LocPathConnectedSpace BTZE0 := (btz_instances btz_two_pi_ne_zero).2.1
  haveI : T2Space BTZE0 := (btz_instances btz_two_pi_ne_zero).1
  obtain ⟨x₀, hx₀U, hx₀s⟩ := hU
  -- a connected neighbourhood `V` of `x₀` on which `φ` is injective
  obtain ⟨h₀, hx₀h, hφh₀⟩ := hloc ⟨x₀, hx₀U⟩
  set O : Set BTZE0 := Subtype.val '' h₀.source with hOdef
  have hOo : IsOpen O := U.isOpen.isOpenMap_subtype_val _ h₀.open_source
  have hx₀O : x₀ ∈ O := ⟨_, hx₀h, rfl⟩
  have hOU : O ⊆ U := by rintro _ ⟨q, -, rfl⟩; exact q.2
  set V := connectedComponentIn O x₀ with hVdef
  have hVo : IsOpen V := hOo.connectedComponentIn
  have hVO : V ⊆ O := connectedComponentIn_subset _ _
  have hx₀V : x₀ ∈ V := mem_connectedComponentIn hx₀O
  have hVc : IsConnected V := isConnected_connectedComponentIn_iff.2 hx₀O
  set VY : Set E0Y := Sum.inr '' V with hVYdef
  have hVYo : IsOpen VY := isOpenMap_inr _ hVo
  have hVYc : IsConnected VY := hVc.image _ continuous_inr.continuousOn
  have hy₀ : (Sum.inr x₀ : E0Y) ∈ e0SingY 0 := ⟨rfl, fun h => hx₀s (inr_mem_e0Reg_iff.1 h)⟩
  have hstr : ∀ W ⊆ (U : Set BTZE0), ∀ y ∈ Sum.inr '' W ∩ e0Reg,
      e0Groupoid.IsLocalStructomorphWithinAt (liftY U φ) (Sum.inr '' W ∩ e0Reg) y := by
    rintro W hW _ ⟨⟨x, hxW, rfl⟩, hxr⟩ -
    obtain ⟨e, he, hxe, heq⟩ :=
      exists_mem_e0Groupoid_liftY hφ hloc (hW hxW) (inr_mem_e0Reg_iff.1 hxr)
    exact ⟨e, he, fun z hz => heq hz.2, hxe⟩
  have hinj : InjOn (liftY U φ) (VY ∩ e0Reg) := by
    rintro _ ⟨⟨a, ha, rfl⟩, -⟩ _ ⟨⟨b, hb, rfl⟩, -⟩ hab
    obtain ⟨qa, hqa, rfl⟩ := hVO ha
    obtain ⟨qb, hqb, rfl⟩ := hVO hb
    rw [liftY_inr φ qa.2, liftY_inr φ qb.2] at hab
    have h1 : φ qa = φ qb := Sum.inr_injective hab
    rw [hφh₀] at h1
    rw [h₀.injOn hqa hqb h1]
  have hmaps : MapsTo (liftY U φ) (VY ∩ e0Reg) (connectedComponent (Sum.inr x₀)) := by
    rw [connectedComponent_inr_eq]
    rintro _ ⟨⟨a, ha, rfl⟩, -⟩
    rw [liftY_inr φ (hOU (hVO ha))]
    exact ⟨_, rfl⟩
  have key := e0_localUnique_sing VY hVYo hVYc (Sum.inr x₀) ⟨x₀, hx₀V, rfl⟩ 0 le_rfl hy₀
    (liftY U φ)
  simp only [e0RegSet_eq] at key
  obtain ⟨e, he, hsrc, heq⟩ := key (hstr V (hVO.trans hOU)) hinj hmaps
  rw [connectedComponent_inr_eq] at hsrc
  -- the local form of `e` at the axis point
  have hax : (toPaper x₀).2 = 0 := by
    by_contra hne
    exact hx₀s ((mem_reg_iff_toPaper x₀).2 hne)
  set τ₁ := (toPaper x₀).1
  have h0 : E0.paperInY ((τ₁, 0) : E0) ∈ e.source := hsrc ⟨_, rfl⟩
  obtain ⟨δ, hδ, a, R, hR⟩ := E0AbsMax.e0Loop_localForm he h0
  obtain ⟨ω, hω | hω⟩ := linear_isometry_complex R
  swap
  · exfalso
    refine not_conj_localForm (τ₀ := τ₁) (a := a) he hδ ω fun (u : E0) (hu : dist u (τ₁, 0) < δ) => ?_
    rw [← show R u.2 = (ω : ℂ) * (starRingEnd ℂ) u.2 by
      rw [hω, LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply]]
    exact hR u hu
  set θ₀ := arg (ω : ℂ)
  have hωθ : (ω : ℂ) = cexp (θ₀ * I) := by
    have := norm_mul_exp_arg_mul_I (ω : ℂ)
    rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at this
    exact this.symm
  set e' := e0Lift (isomE0 a θ₀)
  have he' := e0Lift_isomE0_mem a θ₀
  have he'src : range (Sum.inr : BTZE0 → E0Y) ⊆ e'.source := by rw [e0Lift_source]
  have hball : EqOn e e' (E0.paperInY '' Metric.ball ((τ₁, 0) : E0) δ) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [(hR u hu).2, E0.paperInY_apply, E0.paperInY_apply, e0Lift_apply]
    congr 1
    rw [Homeomorph.symm_apply_eq, toPaper_isomE0, Homeomorph.apply_symm_apply, paperIsom_apply,
      hω, rotation_apply, hωθ]
  have hee' : EqOn e e' (range (Sum.inr : BTZE0 → E0Y)) :=
    e0_rigid e he e' he' _ isOpen_range_inr (isPreconnected_range continuous_inr) hsrc he'src _
      (by rintro _ ⟨u, -, rfl⟩; exact ⟨_, rfl⟩)
      (E0Spear.isOpen_paperInY_image Metric.isOpen_ball)
      ⟨_, _, Metric.mem_ball_self hδ, rfl⟩ hball
  -- globalise on the regular part of `U`
  set SY : Set E0Y := Sum.inr '' (U : Set BTZE0) ∩ e0Reg with hSYdef
  have hSYo : IsOpen SY := (isOpenMap_inr _ U.isOpen).inter isOpen_e0Reg
  have hSYc : IsPreconnected SY :=
    isPreconnected_inter_e0Reg (isOpenMap_inr _ U.isOpen)
      (hUc.isPreconnected.image _ continuous_inr.continuousOn)
  have hW : IsOpen (VY ∩ e0Reg) := hVYo.inter isOpen_e0Reg
  have hWne : (VY ∩ e0Reg).Nonempty :=
    dense_e0Reg.inter_open_nonempty VY hVYo ⟨_, x₀, hx₀V, rfl⟩
  have hWS : VY ∩ e0Reg ⊆ SY := inter_subset_inter_left _ (image_mono (hVO.trans hOU))
  have heqW : EqOn (liftY U φ) e' (VY ∩ e0Reg) := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := hy.1
    rw [heq hy, hee' ⟨x, rfl⟩]
  have hglob := e0_eqOn_of_eqOn_open hSYo hSYc (hstr U subset_rfl) he'
    (fun y hy => he'src (image_subset_range _ _ hy.1)) hW hWne hWS heqW
  refine ⟨a, θ₀, fun q => ?_⟩
  have hext : φ = fun q : U => isomE0 a θ₀ q := by
    refine Continuous.ext_on
      (isPortly_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) U).dense
      (IsAEMorphismOf.continuous hφ) ((isomE0 a θ₀).continuous.comp continuous_subtype_val)
      fun q hq => ?_
    have hqR : (q : BTZE0) ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
      simpa [reg_opensSingular] using hq
    have := hglob ⟨⟨q, q.2, rfl⟩, inr_mem_e0Reg_iff.2 hqR⟩
    rw [liftY_inr φ q.2, e0Lift_apply] at this
    exact Sum.inr_injective this
  exact congrFun hext q

/-! ### `btzcor:indeed_group_isometries` at `α = 0` -/

/-- **`btzcor:indeed_group_isometries` at `α = 0`** (`BTZ_1.tex:385–386`): the automorphisms of
`𝔼₀` as a singular `𝕄`-manifold (homeomorphisms which are a.e. `𝕄`-morphisms both ways) are
exactly the elements of `isom(𝔼₀)`; with `isomE0_trans`, `isomE0_symm`, `isomE0_zero`, a group. -/
theorem btzcor_indeed_group_isometries_e0 (Ψ : BTZE0 ≃ₜ BTZE0) :
    (IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) Ψ ∧
      IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) Ψ.symm) ↔
      ∃ τ₀ θ₀ : ℝ, Ψ = isomE0 τ₀ θ₀ := by
  constructor
  · rintro ⟨hΨ, -⟩
    haveI : ConnectedSpace BTZE0 := (btz_instances btz_two_pi_ne_zero).2.2.2
    haveI : LocPathConnectedSpace BTZE0 := (btz_instances btz_two_pi_ne_zero).2.1
    haveI : LocallyConnectedSpace (⊤ : Opens BTZE0) :=
      (⊤ : Opens BTZE0).isOpen.locallyConnectedSpace
    have hsing : toPaper.symm ((0 : ℝ), (0 : ℂ)) ∉
        Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
      rw [mem_reg_iff_toPaper, Homeomorph.apply_symm_apply]
      exact fun h => h rfl
    obtain ⟨τ₀, θ₀, h⟩ := btzprop_isom_e0 ⊤ (by simpa using isConnected_univ)
      ⟨_, trivial, hsing⟩ (Ψ ∘ Subtype.val)
      (hΨ.comp (isAEMorphism_opensSingular_val (⊤ : Opens BTZE0)))
      (Ψ.isLocalHomeomorph.comp (⊤ : Opens BTZE0).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph)
    exact ⟨τ₀, θ₀, Homeomorph.ext fun x => h ⟨x, trivial⟩⟩
  · rintro ⟨τ₀, θ₀, rfl⟩
    exact ⟨isAEMorphism_isomE0 τ₀ θ₀, by rw [isomE0_symm]; exact isAEMorphism_isomE0 _ _⟩

/-! ### The reflection `θ ↦ −θ`: an isometry of the printed metric outside `isom(𝔼₀)` -/

/-- The reflection `(τ, r, θ) ↦ (τ, r, −θ)` of `𝔼₀`, `(τ, z) ↦ (τ, z̄)` in the paper's
coordinates. -/
noncomputable def paperRefl : E0 ≃ₜ E0 where
  toFun w := (w.1, (starRingEnd ℂ) w.2)
  invFun w := (w.1, (starRingEnd ℂ) w.2)
  left_inv w := by simp
  right_inv w := by simp
  continuous_toFun := continuous_fst.prodMk (Complex.continuous_conj.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (Complex.continuous_conj.comp continuous_snd)

/-- The reflection `θ ↦ −θ` on `GX.BTZE0`. -/
noncomputable def reflE0 : BTZE0 ≃ₜ BTZE0 := toPaper.trans (paperRefl.trans toPaper.symm)

/-- **The reflection is, through the developing map, the linear map `(a, b, c) ↦ (a, b, −c)` of
null coordinates, which preserves the Minkowski form `c² − ab`**: it is an isometry of the printed
metric `ds₀² = −2dτdr + dr² + r²dθ²` (whose developed form is `GX.btzPaperDev_pullback`). -/
theorem btzPaperDev_refl (p : ℝ × ℝ × ℝ) :
    btzPaperDev (p.1, p.2.1, -p.2.2) =
      nullToMink ((btzPaperNull p).1, (btzPaperNull p).2.1, -(btzPaperNull p).2.2) ∧
    nullQ ((btzPaperNull p).1, (btzPaperNull p).2.1, -(btzPaperNull p).2.2) =
      nullQ (btzPaperNull p) := by
  refine ⟨?_, by simp only [nullQ]; ring⟩
  rw [btzPaperDev_eq_nullToMink]
  congr 1
  simp only [btzPaperNull]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- **The reflection is not in `isom(𝔼₀)`.** -/
theorem reflE0_ne_isomE0 (τ₀ θ₀ : ℝ) : reflE0 ≠ isomE0 τ₀ θ₀ := by
  intro h
  have h1 := congrArg toPaper (congrFun (congrArg DFunLike.coe h) (toPaper.symm ((0 : ℝ), (1 : ℂ))))
  have h2 := congrArg toPaper (congrFun (congrArg DFunLike.coe h) (toPaper.symm ((0 : ℝ), I)))
  rw [toPaper_isomE0, Homeomorph.apply_symm_apply, paperIsom_apply] at h1 h2
  simp only [reflE0, Homeomorph.trans_apply, Homeomorph.apply_symm_apply] at h1 h2
  have e1 := congrArg Prod.snd h1
  have e2 := congrArg Prod.snd h2
  change (starRingEnd ℂ) 1 = cexp (θ₀ * I) * 1 at e1
  change (starRingEnd ℂ) I = cexp (θ₀ * I) * I at e2
  rw [map_one, mul_one] at e1
  rw [← e1, one_mul, Complex.conj_I] at e2
  have := congrArg Complex.im e2
  simp at this
  linarith

/-- **The reflection is not an a.e. `𝕄`-morphism of `𝔼₀`** (`btzcor_indeed_group_isometries_e0`:
`Isom(𝐌³) = SO₀(1,2) ⋉ ℝ³` preserves the orientation). -/
theorem not_isAEMorphism_reflE0 :
    ¬ IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) reflE0 := by
  intro h
  have hs : reflE0.symm = reflE0 := by
    ext x
    simp only [reflE0, Homeomorph.symm_trans_apply, Homeomorph.symm_symm, Homeomorph.trans_apply]
    rfl
  obtain ⟨τ₀, θ₀, he⟩ := (btzcor_indeed_group_isometries_e0 reflE0).1 ⟨h, hs ▸ h⟩
  exact reflE0_ne_isomE0 τ₀ θ₀ he

/-! ### `btzcor:morphism_two_manifolds_local`, with `𝔼₀` as the singular model -/

section Corollary

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) N]

/-- **`btzcor:morphism_two_manifolds_local`, `𝔼₀` the singular model** (`BTZ_1.tex:391–393`): an
a.e. `𝕄`-morphism `φ : M → N` of singular `𝕄`-manifolds which is a local homeomorphism is a local
isomorphism of their `𝔼₀`-atlases: on `Reg M` it is a `𝕄`-morphism into `Reg N`
(`lem:GX_sing_homeo_reg`), it maps `Sing M` onto `Sing N ∩ φ(M)` (`φ⁻¹ Sing N = Sing M`), and read in
any two `𝔼₀`-charts at a singular point `x` and at `φ x` (homeomorphisms `κ : U ≃ₜ V`,
`V ⊆ 𝔼₀` open, which are a.e. `𝕄`-morphisms: the paper's « neighborhood which embeds by an a.e.
`𝔼`-morphism into `𝔼₀` »), it is near `x` the restriction of an element of `isom(𝔼₀)`. -/
theorem btzcor_morphism_two_manifolds_local_e0 {φ : M → N}
    (hφ : IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) φ) (hloc : IsLocalHomeomorph φ) :
    IsRegularOn (Causal.Flat.isom 2) (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) N) φ
      (Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M) ∧
    φ ⁻¹' Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) N =
      Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M ∧
    ∀ (U : Opens M) (V : Opens BTZE0) (κ : U ≃ₜ V),
      IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) (κ : U → V) →
    ∀ (U' : Opens N) (V' : Opens BTZE0) (κ' : U' ≃ₜ V'),
      IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) (κ' : U' → V') →
    ∀ x : U, (x : M) ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M → φ x ∈ U' →
    ∃ τ₀ θ₀ : ℝ, ∃ W : Set M, IsOpen W ∧ (x : M) ∈ W ∧ ∀ y ∈ W, ∃ (hyU : y ∈ U) (hyU' : φ y ∈ U'),
      ((κ' ⟨φ y, hyU'⟩ : V') : BTZE0) = isomE0 τ₀ θ₀ (κ ⟨y, hyU⟩ : V) := by
  refine ⟨isRegularOn_reg_of_isLocalHomeomorph hφ hloc, (hφ.preimage_reg_sing hloc).2, ?_⟩
  intro U V κ hκ U' V' κ' hκ' x hxs hxU'
  haveI : LocPathConnectedSpace BTZE0 := (btz_instances btz_two_pi_ne_zero).2.1
  -- the open set of `V` where the transition is defined
  set O : Set BTZE0 := Subtype.val '' ((fun w : V => φ (κ.symm w)) ⁻¹' (U' : Set N)) with hOdef
  have hOo : IsOpen O := V.isOpen.isOpenMap_subtype_val _
    (U'.isOpen.preimage ((IsAEMorphismOf.continuous hφ).comp
      (continuous_subtype_val.comp κ.symm.continuous)))
  have hOmem : ∀ v ∈ O, ∃ hvV : v ∈ V, φ (κ.symm ⟨v, hvV⟩) ∈ U' := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  have hxO : ((κ x : V) : BTZE0) ∈ O := ⟨κ x, by simpa using hxU', rfl⟩
  set A : Opens BTZE0 := ⟨connectedComponentIn O (κ x : BTZE0), hOo.connectedComponentIn⟩
    with hAdef
  have hAO : (A : Set BTZE0) ⊆ O := connectedComponentIn_subset _ _
  have hAV : A ≤ V := fun a ha => (hOmem a (hAO ha)).1
  set inc : A → V := fun a => ⟨a, hAV a.2⟩ with hinc
  have hfmem : ∀ a : A, φ (κ.symm (inc a)) ∈ U' := fun a => (hOmem a (hAO a.2)).2
  set f : A → U' := fun a => ⟨φ (κ.symm (inc a)), hfmem a⟩ with hfdef
  set ψ : A → BTZE0 := fun a => (κ' (f a) : BTZE0) with hψdef
  -- `ψ` is an a.e. morphism and a local homeomorphism
  have h1 : IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) (Subtype.val ∘ f) :=
    hφ.comp ((isAEMorphism_opensSingular_val U).comp
      ((IsAEMorphism.symm_of_homeomorph hκ).comp (isAEMorphism_opensInclusion hAV)))
  have hf : IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) f :=
    isAEMorphism_of_val_comp U' h1
  have hψ : IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) ψ :=
    (isAEMorphism_opensSingular_val V').comp (hκ'.comp hf)
  have hincl : IsLocalHomeomorph inc :=
    IsLocalHomeomorph.of_comp (g := (Subtype.val : V → BTZE0))
      (show IsLocalHomeomorph ((Subtype.val : V → BTZE0) ∘ inc) from
        A.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph)
      V.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      (continuous_subtype_val.subtype_mk _)
  have hfl : IsLocalHomeomorph f :=
    IsLocalHomeomorph.of_comp (hloc.comp (U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
      (κ.symm.isLocalHomeomorph.comp hincl)))
      U'.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph (IsAEMorphismOf.continuous hf)
  have hψl : IsLocalHomeomorph ψ :=
    V'.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp (κ'.isLocalHomeomorph.comp hfl)
  -- `κ x` is a singular point of `𝔼₀`
  have hsing : ((κ x : V) : BTZE0) ∉ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
    intro hr
    have hrV : κ x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) V := by
      rw [reg_opensSingular]; exact hr
    have hrU : x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) U := by
      rw [← (hκ.preimage_reg_sing κ.isLocalHomeomorph).1]; exact hrV
    rw [reg_opensSingular] at hrU
    exact hxs hrU
  obtain ⟨τ₀, θ₀, hψeq⟩ := btzprop_isom_e0 A (isConnected_connectedComponentIn_iff.2 hxO)
    ⟨_, mem_connectedComponentIn hxO, hsing⟩ ψ hψ hψl
  refine ⟨τ₀, θ₀, Subtype.val '' ((fun u : U => (κ u : BTZE0)) ⁻¹' (A : Set BTZE0)),
    U.isOpen.isOpenMap_subtype_val _ (A.isOpen.preimage (continuous_subtype_val.comp κ.continuous)),
    ⟨x, mem_connectedComponentIn hxO, rfl⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  set a : A := ⟨κ u, hu⟩
  have hia : κ.symm (inc a) = u := by
    rw [show inc a = κ u from Subtype.ext rfl, Homeomorph.symm_apply_apply]
  have hu' : φ u ∈ U' := hia ▸ hfmem a
  refine ⟨u.2, hu', ?_⟩
  have hfa : f a = ⟨φ u, hu'⟩ := Subtype.ext (congrArg φ (congrArg Subtype.val hia))
  have := hψeq a
  simp only [hψdef, hfa] at this
  exact this

end Corollary

end BTZIsom

end GX
