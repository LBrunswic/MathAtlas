import Causal.Port.E0Axioms
import Causal.Flat.CBGSlice
import Causal.CurvesExtend

/-!
# `E₀`: sector charts, cone slices, strong causality, closed `J^±`, diamonds a basis

Target `T-ett-port-e0-sfa` (DEC-134), the first of two modules; the second,
`Causal.Port.E0SingularFlat`, assembles `SingularFlatAxioms` for `E₀`. **No label is
marked here**: this is the model's causal infrastructure. Rows it touches at the model `E₀`,
unmarked (the paper states them for every `E_{≥0}`-manifold, and `E₀` is read as in OQ-34/OQ-35):
`def:strongly_causal_spacetime` (`stronglyCausal`), `def:alexandrov_topology`
(`alexandrovTopology_eq`), `rem:sing_tarentin` with the localisation of a basis
(`diamonds_basis`).

> `rem:sing_tarentin`. Every $\mass{\geq0}$-manifold is a tarentin topological spacetime.
> (`ETT.tex:1364–1366`)

**Ported from `lean-gx/GX/BTZ/Causality.lean` at commit `c48aa45`**: every declaration `GX.E0.x`
of gx's l.1814–3082 and l.3094–3146 is `Causal.E0.x` here, with gx's statement and proof character
for character, except the sections about `Y = 𝕄 ⊕ 𝔼₀` (gx l.2296–2382 `YSlices`, l.3084–3092
`coneSlicePast_Y`), which are not ported. In gx's section `Bridge` (l.1814–1874) only
`minkowski_le_nullToMink` and `minkowski_lt_nullToMink` are new here: the other four
(`nullCone_iff_isFutureCausal`, `nullConeLt_iff_isFutureTimelike`, `le_iff_btzPaperDev`,
`lt_iff_btzPaperDev`) are already `Causal.E0.*` in the strict `Causal.Port.E0Model` and
`E0Causality` (T-ett-port-e0). The only other changes: the imports (strict `Causal.*` only;
lean-causal never imports `GX.*`, DEC-33), the two `variable` lines repeated, and
`nullToMinkHomeomorph` with its two `simp` lemmas **restated verbatim from
`lean-gx/GX/Lorentz/Bridge.lean` l.140–147** at `c48aa45` (gx's `GX.nullToMinkHomeomorph`, here
`Causal.E0.nullToMinkHomeomorph`, over the strict `Causal.E0.nullToMink`).

## What is proved (no `sorry` in this file)

* **Sector charts.** Off the axis, `sectorChart y` (the development with a branch of the angle,
  on the slit sector of `y`) is a chart isomorphism onto an open set of `𝐌³`
  (`chartIso_sectorChart`, `chartIso_sector`) and an injective abstract `𝕄≥0`-morphism
  (`isEMorphismOn_chartMap`): `E₀ ∖ sing₀` is locally Minkowski space as a topological spacetime.
* **Cone slices** (`SliceAt`, the shape of CBG's `LocalModel.coneSliceFuture/Past`): off the axis
  by the sector charts (`sliceAt_future_of_not_mem_axis`, `sliceAt_past_of_not_mem_axis`), and
  at a BTZ point (`sliceAt_past_of_mem_axis`) through the domain `sliceDom`, whose level
  `{τ + r = c}` is a Cauchy surface (`isCauchySurfaceOn_sliceDom`).
* **Time function, causality.** `h = τ + r` strictly increases along `≤` (`hcoord_lt_of_le`), so
  `E₀` is causal (`isCausal`) and causal curves extend (`curvesExtend`).
* **Closed cones, strong causality.** `dist x y ≤ 3(τ_y − τ_x)` along `≼` (`Le.dist_le`);
  `J^±(x)` closed (`isClosed_Jplus`, `isClosed_Jminus`); **`stronglyCausal`**.
* **Limits, local cones.** A causal curve with bounded time converges at that end
  (`exists_tendsto_of_bddAbove/Below`); `J^±_W(p) ≠ {p}` in every open `W ∋ p`.
* **Diamonds.** `diamonds_basis` (`p, q ∈ U`, `x ∈ Int J(p,q) ⊆ J(p,q) ⊆ U`, BTZ points
  included), `nhds_hasBasis_openDiamond`, `alexandrovTopology_eq`.

## Hypothesis checklist

| paper | here |
|---|---|
| `E₀`, the extreme BTZ model (l.1330) | ⚠ read: `Causal.E0` with gx's metric through `D` (OQ-34) |
| its causality from curves (`defi:causal_Ealpha`) | ⚠ read: `E0.causality` (DEC-33; OQ-34) |
| `rem:sing_tarentin` at `E₀` | ✓ tarentin (strict `E0.tarentin`), and diamonds a basis |

## SCOPE (disclosed)

* **(a) Not ported.** `Y = 𝕄 ⊕ 𝔼₀` (gx's `ModelY`, `sumCausality`, the summands as
  `𝕄≥0`-morphisms, `coneSliceFuture_Y`, `coneSlicePast_Y(_of_axis)`), and everything after
  gx l.3347 (the transport to Model's `BTZE0`, `IsoNear`, `chartIso_mem_e0Groupoid`): CBG
  interface material for gx's `LocalModel`, no ETT row asks for it.
* **(b) Model-free lemmas in a model module** (kb/0047): `SliceAt` with `SliceAt.pullback`,
  `SliceAt.pushforward`, `minkowski_sliceAt_future/past`, `norm_cexp_sub_cexp_le`,
  `abs_arg_lt_pi_of_mem_slitPlane` keep gx's names under `Causal.E0`, as a verbatim port must;
  hoisting them is a later, separate move.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Ported from
`lean-gx/GX/BTZ/Causality.lean` and `GX/Lorentz/Bridge.lean` at `c48aa45` (target
`T-ett-port-e0-sfa`, DEC-134).
-/

namespace Causal

open Set Filter Topology Function Complex
open scoped Real

namespace E0

variable {x y z : E0} {θ θ' θ₁ θ₂ θ₃ : ℝ}

variable {P Q R : ℝ × ℝ × ℝ}

/-! ### `nullToMink` as a homeomorphism (restated from gx's `GX.Lorentz.Bridge`) -/

/-- `nullToMink` as a homeomorphism. -/
noncomputable def nullToMinkHomeomorph : (ℝ × ℝ × ℝ) ≃ₜ Causal.Minkowski 2 :=
  nullToMink.toContinuousLinearEquiv.toHomeomorph

@[simp] theorem coe_nullToMinkHomeomorph : ⇑nullToMinkHomeomorph = nullToMink := rfl

@[simp] theorem coe_nullToMinkHomeomorph_symm : ⇑nullToMinkHomeomorph.symm = nullToMink.symm :=
  rfl

/-! ### `Le` is Minkowski's causality of the developments (DEC-33) -/

section Bridge

open TopologicalSpace

theorem minkowski_le_nullToMink (P Q : ℝ × ℝ × ℝ) :
    (Causal.minkowski 2).le ⊤ (nullToMink P) (nullToMink Q) ↔ NullCone (Q - P) := by
  rw [Causal.Flat.le_top_iff_minkQ, ← map_sub, nullCone_iff_isFutureCausal]

theorem minkowski_lt_nullToMink (P Q : ℝ × ℝ × ℝ) :
    (Causal.minkowski 2).lt ⊤ (nullToMink P) (nullToMink Q) ↔ NullConeLt (Q - P) := by
  rw [Causal.Flat.lt_top_iff_minkQ, ← map_sub, nullConeLt_iff_isFutureTimelike]

end Bridge

/-! ### Off the axis: the sector charts are causal isomorphisms onto open sets of `𝐌³` -/

section Sector

open TopologicalSpace

variable {y w : E0}

/-- **The slit sector around `y`**: `z / z_y ∉ ℝ≤0`; on it the angle `angle y` continues `arg z_y`. -/
def sector (y : E0) : Set E0 := {w | w.2 / y.2 ∈ Complex.slitPlane}

theorem isOpen_sector (y : E0) : IsOpen (sector y) :=
  Complex.isOpen_slitPlane.preimage (continuous_snd.div_const _)

/-- The sector as an open set. -/
def sectorOpens (y : E0) : Opens E0 := ⟨sector y, isOpen_sector y⟩

theorem mem_sector_self (hy : y.2 ≠ 0) : y ∈ sector y := by
  show y.2 / y.2 ∈ Complex.slitPlane; rw [div_self hy]; exact Complex.one_mem_slitPlane

theorem ne_zero_of_mem_sector (hw : w ∈ sector y) : w.2 ≠ 0 := fun h => by
  have := Complex.slitPlane_ne_zero hw; rw [h, zero_div] at this; exact this rfl

theorem not_mem_axis_of_mem_sector (hw : w ∈ sector y) : w ∉ axis := ne_zero_of_mem_sector hw

/-- The branch of the angle on the sector. -/
noncomputable def angle (y w : E0) : ℝ := arg y.2 + arg (w.2 / y.2)

/-- **The sector chart**: the development with the branch angle, in Minkowski coordinates
(`= btzPaperDev (τ, r, angle)`). -/
noncomputable def chartMap (y w : E0) : Causal.Minkowski 2 := nullToMink (locLift y w)

theorem chartMap_eq (y w : E0) : chartMap y w = btzPaperDev (w.1, rad w, angle y w) :=
  (btzPaperDev_eq_nullToMink _).symm

theorem polar_angle (hy : y.2 ≠ 0) (w : E0) : Polar w (angle y w) := polar_add_arg_div y w hy

theorem continuousOn_angle (y : E0) : ContinuousOn (angle y) (sector y) := fun _ hw =>
  (continuousAt_const.add (ContinuousAt.comp (f := fun w : E0 => w.2 / y.2)
    (Complex.continuousAt_arg hw) (continuousAt_snd.div_const _))).continuousWithinAt

theorem continuousOn_locLift (y : E0) : ContinuousOn (locLift y) (sector y) :=
  continuous_btzPaperNull.comp_continuousOn
    (continuous_fst.continuousOn.prodMk (continuous_rad.continuousOn.prodMk (continuousOn_angle y)))

theorem continuousOn_chartMap (y : E0) : ContinuousOn (chartMap y) (sector y) :=
  nullToMinkHomeomorph.continuous.comp_continuousOn (continuousOn_locLift y)

theorem unlift_symm_chartMap (hy : y.2 ≠ 0) (w : E0) :
    unlift (nullToMink.symm (chartMap y w)) = w := by
  rw [chartMap, LinearEquiv.symm_apply_apply]; exact unlift_lift (polar_angle hy w)

theorem injOn_chartMap (hy : y.2 ≠ 0) : InjOn (chartMap y) (sector y) := fun w _ w' _ h => by
  rw [← unlift_symm_chartMap hy w, ← unlift_symm_chartMap hy w', h]

/-- The image of the sector in null coordinates. -/
def Img (y : E0) : Set (ℝ × ℝ × ℝ) := {R | 0 < R.2.1 ∧ |-(R.2.2 / R.2.1) - arg y.2| < π}

theorem abs_arg_lt_pi_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) : |arg z| < π := by
  rw [abs_lt]
  exact ⟨Complex.neg_pi_lt_arg z, lt_of_le_of_ne (Complex.arg_le_pi z)
    (Complex.mem_slitPlane_iff_arg.1 hz).1⟩

theorem locLift_mem_Img (hw : w ∈ sector y) : locLift y w ∈ Img y := by
  have hr : 0 < rad w := norm_pos_iff.2 (ne_zero_of_mem_sector hw)
  refine ⟨hr, ?_⟩
  have : -((locLift y w).2.2 / (locLift y w).2.1) = angle y w := by
    simp only [locLift, lift, btzPaperNull]
    field_simp
    rfl
  rw [this, angle, add_sub_cancel_left]
  exact abs_arg_lt_pi_of_mem_slitPlane hw

theorem locLift_unlift (hy : y.2 ≠ 0) {R : ℝ × ℝ × ℝ} (hR : R ∈ Img y) :
    locLift y (unlift R) = R := by
  obtain ⟨hB, hθ⟩ := hR
  set θ := -(R.2.2 / R.2.1)
  have hry : 0 < rad y := norm_pos_iff.2 hy
  have hratio : (unlift R).2 / y.2 = ((R.2.1 / rad y : ℝ) : ℂ) * cexp (↑(θ - arg y.2) * I) := by
    have h1 : (unlift R).2 = (R.2.1 : ℂ) * cexp (↑θ * I) := rfl
    have h2 : y.2 = (rad y : ℂ) * cexp (↑(arg y.2) * I) := polar_arg y
    rw [h1]
    conv_lhs => rw [h2]
    have hne : (rad y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hry.ne'
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.ofReal_div]
    field_simp
  have key : ∀ φ : ℝ, φ ∈ Ioc (-π) π → arg (cexp (↑φ * I)) = φ := fun φ hφ => by
    rw [Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I hφ
  have harg : arg ((unlift R).2 / y.2) = θ - arg y.2 := by
    rw [hratio, Complex.arg_real_mul _ (div_pos hB hry)]
    rw [abs_lt] at hθ
    exact key _ ⟨hθ.1, hθ.2.le⟩
  show lift (unlift R) (arg y.2 + arg ((unlift R).2 / y.2)) = R
  rw [harg, add_sub_cancel]
  exact lift_unlift (Or.inl hB)

theorem image_chartMap (hy : y.2 ≠ 0) {V : Set E0} (hV : V ⊆ sector y) :
    chartMap y '' V = nullToMink.symm ⁻¹' (Img y ∩ unlift ⁻¹' V) := by
  ext m
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [chartMap, LinearEquiv.symm_apply_apply]; exact locLift_mem_Img (hV hw)
    · show unlift (nullToMink.symm (chartMap y w)) ∈ V
      rw [unlift_symm_chartMap hy]; exact hw
  · rintro ⟨h1, h2⟩
    refine ⟨_, h2, ?_⟩
    rw [chartMap, locLift_unlift hy h1, LinearEquiv.apply_symm_apply]

theorem isOpen_image_chartMap (hy : y.2 ≠ 0) {V : Set E0} (hV : V ⊆ sector y) (hVo : IsOpen V) :
    IsOpen (chartMap y '' V) := by
  rw [image_chartMap hy hV]
  refine IsOpen.preimage nullToMinkHomeomorph.symm.continuous ?_
  have hpos : IsOpen {R : ℝ × ℝ × ℝ | 0 < R.2.1} := isOpen_lt continuous_const continuous_snd.fst
  have hf : ContinuousOn (fun R : ℝ × ℝ × ℝ => (-(R.2.2 / R.2.1), unlift R))
      {R : ℝ × ℝ × ℝ | 0 < R.2.1} := fun R hR =>
    ((continuousAt_snd.snd.div continuousAt_snd.fst (ne_of_gt hR)).neg.prodMk
      (continuousAt_unlift (ne_of_gt hR))).continuousWithinAt
  have ht : IsOpen ({θ : ℝ | |θ - arg y.2| < π} ×ˢ V) :=
    (isOpen_lt ((continuous_id.sub continuous_const).abs) continuous_const).prod hVo
  have := hf.isOpen_inter_preimage hpos ht
  convert this using 1
  ext R
  simp only [Img, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_prod]
  tauto

/-- A curve of `𝔼₀` in the sector develops to a causal curve of `𝐌³` (`Causal.Curves`). -/
theorem curveOn_chartMap {W : Opens E0} (hW : (W : Set E0) ⊆ sector y)
    {c : ℝ → E0} {a b : ℝ} {U : Opens (Causal.Minkowski 2)}
    (hU : ∀ t ∈ Icc a b, chartMap y (c t) ∈ U) {Rel : E0 → E0 → Prop}
    {RelM : Opens (Causal.Minkowski 2) → Causal.Minkowski 2 → Causal.Minkowski 2 → Prop}
    (hRelTrans : ∀ {x y z}, Rel x y → Rel y z → Rel x z)
    (hstep : ∀ s s' : E0, Rel s s' → |angle y s' - angle y s| ≤ π →
      ∀ (B : Opens (Causal.Minkowski 2)), Convex ℝ (B : Set (Causal.Minkowski 2)) →
        chartMap y s ∈ B → chartMap y s' ∈ B → RelM B (chartMap y s) (chartMap y s'))
    (hmono : ∀ {B N : Opens (Causal.Minkowski 2)}, B ≤ N → ∀ {p q}, RelM B p q → RelM N p q)
    (hc : Causal.CurveOn (relOn Rel) W c a b) :
    Causal.CurveOn RelM U (fun t => chartMap y (c t)) a b where
  mem := hU
  rel t ht N hN htN := by
    have hcont := hc.continuousOn (isRelFamily_relOn (R := Rel) (fun h₁ h₂ => hRelTrans h₁ h₂))
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 N.isOpen _ htN
    have hct : c t ∈ sector y := hW (hc.mem t ht)
    have hsec : sector y ∈ 𝓝 (c t) := (isOpen_sector y).mem_nhds hct
    have h1 : (fun s => chartMap y (c s)) ⁻¹' Metric.ball (chartMap y (c t)) ρ ∈ 𝓝[Icc a b] t :=
      (((continuousOn_chartMap y).continuousAt hsec).comp_continuousWithinAt (hcont t ht))
        (Metric.ball_mem_nhds _ hρ)
    have h2 : (fun s => angle y (c s)) ⁻¹' Metric.ball (angle y (c t)) (π / 2) ∈ 𝓝[Icc a b] t :=
      (((continuousOn_angle y).continuousAt hsec).comp_continuousWithinAt (hcont t ht))
        (Metric.ball_mem_nhds _ (by positivity))
    obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhdsWithin_iff.1 (Filter.inter_mem h1 h2)
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht W le_rfl (hc.mem t ht)
    refine ⟨max l (t - ε), min u (t + ε), max_lt hl (by linarith), lt_min hu (by linarith),
      fun s hs s' hs' h1' h2' h3' => ?_⟩
    have hl' : l < s := (le_max_left _ _).trans_lt h1'
    have hu' : s' < u := h3'.trans_le (min_le_left _ _)
    have hsε : s ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right l (t - ε), min_le_right u (t + ε)]
    have hs'ε : s' ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right l (t - ε), min_le_right u (t + ε)]
    obtain ⟨hsB, hsA⟩ := hεb ⟨hsε, hs⟩
    obtain ⟨hs'B, hs'A⟩ := hεb ⟨hs'ε, hs'⟩
    have hR : Rel (c s) (c s') := (hrel s hs s' hs' hl' h2' hu').2.2
    have hang : |angle y (c s') - angle y (c s)| ≤ π := by
      simp only [mem_preimage, Metric.mem_ball, Real.dist_eq] at hsA hs'A
      have := abs_sub_le (angle y (c s')) (angle y (c t)) (angle y (c s))
      rw [abs_sub_comm (angle y (c t))] at this
      linarith
    let B : Opens (Causal.Minkowski 2) := ⟨Metric.ball (chartMap y (c t)) ρ, Metric.isOpen_ball⟩
    exact hmono (fun z hz => hball hz : B ≤ N) (hstep _ _ hR hang B (convex_ball _ _) hsB hs'B)

theorem curveOn_chartMap_le (hy : y.2 ≠ 0) {W : Opens E0} (hW : (W : Set E0) ⊆ sector y)
    {c : ℝ → E0} {a b : ℝ} {U : Opens (Causal.Minkowski 2)}
    (hU : ∀ t ∈ Icc a b, chartMap y (c t) ∈ U) (hc : Causal.CurveOn (relOn Le) W c a b) :
    Causal.CurveOn (Causal.minkowski 2).le U (fun t => chartMap y (c t)) a b :=
  curveOn_chartMap (Rel := Le) hW hU Le.trans (fun s s' h hang _ hB hs hs' =>
    (Causal.Flat.le_iff_of_convex hB).2 ⟨hs, hs', (minkowski_le_nullToMink _ _).2
      (h.of_polar (polar_angle hy s) (polar_angle hy s') hang)⟩)
    (fun hBN _ _ h => (Causal.minkowski 2).le_mono hBN h) hc

theorem curveOn_chartMap_lt (hy : y.2 ≠ 0) {W : Opens E0} (hW : (W : Set E0) ⊆ sector y)
    {c : ℝ → E0} {a b : ℝ} {U : Opens (Causal.Minkowski 2)}
    (hU : ∀ t ∈ Icc a b, chartMap y (c t) ∈ U) (hc : Causal.CurveOn (relOn Lt) W c a b) :
    Causal.CurveOn (Causal.minkowski 2).lt U (fun t => chartMap y (c t)) a b :=
  curveOn_chartMap (Rel := Lt) hW hU Lt.trans (fun s s' h hang _ hB hs hs' =>
    (Causal.Flat.lt_iff_of_convex hB).2 ⟨hs, hs', (minkowski_lt_nullToMink _ _).2
      (h.of_polar (polar_angle hy s) (polar_angle hy s') hang)⟩)
    (fun hBN _ _ h => (Causal.minkowski 2).lt_mono hBN h) hc

/-- A curve, continuous and locally `R`-increasing, is a curve for `relOn R`. -/
theorem curveOn_of_local {R : E0 → E0 → Prop} {W : Opens E0} {c : ℝ → E0} {a b : ℝ}
    (hc : ContinuousOn c (Icc a b)) (hmem : ∀ t ∈ Icc a b, c t ∈ W)
    (hR : ∀ t ∈ Icc a b, ∃ l u, l < t ∧ t < u ∧ ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, l < s → s < s' →
      s' < u → R (c s) (c s')) :
    Causal.CurveOn (relOn R) W c a b where
  mem := hmem
  rel t ht N _ htN := by
    have hN : c ⁻¹' N ∈ 𝓝[Icc a b] t := hc t ht (N.isOpen.mem_nhds htN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hN
    obtain ⟨l, u, hl, hu, hRl⟩ := hR t ht
    refine ⟨max l (t - ε), min u (t + ε), max_lt hl (by linarith), lt_min hu (by linarith),
      fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hsb : s ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right l (t - ε), min_le_right u (t + ε)]
    have hs'b : s' ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right l (t - ε), min_le_right u (t + ε)]
    exact ⟨hball ⟨hsb, hs⟩, hball ⟨hs'b, hs'⟩, hRl s hs s' hs'
      ((le_max_left _ _).trans_lt h1) h2 (h3.trans_le (min_le_left _ _))⟩

/-- A causal (chronological) curve of `𝐌³` in the image of the sector pulls back to `𝔼₀`. -/
theorem curveOn_pullback (hy : y.2 ≠ 0) {V : Opens E0} (hV : (V : Set E0) ⊆ sector y)
    {U : Opens (Causal.Minkowski 2)} (hU : (U : Set (Causal.Minkowski 2)) = chartMap y '' V)
    {d : ℝ → Causal.Minkowski 2} {a b : ℝ} {RelM : Opens (Causal.Minkowski 2) →
      Causal.Minkowski 2 → Causal.Minkowski 2 → Prop} (hRelM : Causal.IsRelFamily RelM)
    {Rel : E0 → E0 → Prop} (hdRel : ∀ p q : E0, RelM U (chartMap y p) (chartMap y q) → Rel p q)
    (hd : Causal.CurveOn RelM U d a b) :
    Causal.CurveOn (relOn Rel) V (fun t => unlift (nullToMink.symm (d t))) a b := by
  have hpt : ∀ t ∈ Icc a b, ∃ w ∈ V, chartMap y w = d t := fun t ht => by
    have := hd.mem t ht; rw [← SetLike.mem_coe, hU] at this; exact this
  have heq : ∀ t ∈ Icc a b, chartMap y (unlift (nullToMink.symm (d t))) = d t := fun t ht => by
    obtain ⟨w, -, hw⟩ := hpt t ht; rw [← hw, unlift_symm_chartMap hy]
  have hdc := hd.continuousOn hRelM
  refine curveOn_of_local ?_ (fun t ht => ?_) (fun t ht => ?_)
  · intro t ht
    obtain ⟨w, hwV, hw⟩ := hpt t ht
    have hB : (nullToMink.symm (d t)).2.1 ≠ 0 := by
      rw [← hw, chartMap, LinearEquiv.symm_apply_apply]
      exact (norm_pos_iff.2 (ne_zero_of_mem_sector (hV hwV))).ne'
    exact ((continuousAt_unlift hB).comp nullToMinkHomeomorph.symm.continuous.continuousAt
      |>.comp_continuousWithinAt (hdc t ht))
  · obtain ⟨w, hwV, hw⟩ := hpt t ht; rw [← hw, unlift_symm_chartMap hy]; exact hwV
  · obtain ⟨l, u, hl, hu, hrel⟩ := hd.rel t ht U le_rfl (hd.mem t ht)
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => hdRel _ _ ?_⟩
    rw [heq s hs, heq s' hs']
    exact hrel s hs s' hs' h1 h2 h3

/-- **Off the axis the causality of `𝔼₀` is Minkowski's through the sector chart**: for every open
`V` in the sector, `≤_V` and `≪_V` are carried to `≤_{D(V)}` and `≪_{D(V)}`. -/
theorem chartIso_sector (hy : y.2 ≠ 0) {V : Opens E0} (hV : (V : Set E0) ⊆ sector y)
    {U : Opens (Causal.Minkowski 2)} (hU : (U : Set (Causal.Minkowski 2)) = chartMap y '' V)
    {p q : E0} (hp : p ∈ V) (hq : q ∈ V) :
    (causality.le V p q ↔ (Causal.minkowski 2).le U (chartMap y p) (chartMap y q)) ∧
      (causality.lt V p q ↔ (Causal.minkowski 2).lt U (chartMap y p) (chartMap y q)) := by
  have hmapsU : ∀ w ∈ V, chartMap y w ∈ U := fun w hw => by
    rw [← SetLike.mem_coe, hU]; exact mem_image_of_mem _ hw
  have hdLe : ∀ p q : E0, (Causal.minkowski 2).le U (chartMap y p) (chartMap y q) → Le p q :=
    fun p q h => by
      have := (minkowski_le_nullToMink _ _).1 ((Causal.minkowski 2).le_mono le_top h)
      exact ⟨_, _, polar_angle hy p, polar_angle hy q, this⟩
  have hdLt : ∀ p q : E0, (Causal.minkowski 2).lt U (chartMap y p) (chartMap y q) → Lt p q :=
    fun p q h => by
      have := (minkowski_lt_nullToMink _ _).1 ((Causal.minkowski 2).lt_mono le_top h)
      exact ⟨_, _, polar_angle hy p, polar_angle hy q, this⟩
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    have hcM := curveOn_chartMap_le hy hV (fun t ht => hmapsU _ (hc.mem t ht)) hc
    rcases hab.lt_or_eq with hab | hab
    · exact hcM.rel_of_lt (Causal.Precausality.isRelFamily_le _) le_rfl hab le_rfl
    · rw [hab]; exact (Causal.minkowski 2).le_refl (hmapsU _ (hc.mem b ⟨hab.le, le_rfl⟩))
  · obtain ⟨d, hd, hd0, hd1⟩ := ((Causal.minkowski_causallyArcConnected U le_top _ _).1).1 h
    refine ⟨0, 1, zero_le_one, _, curveOn_pullback hy hV hU
      (Causal.Precausality.isRelFamily_le _) hdLe hd, ?_, ?_⟩
    · simp only [hd0, unlift_symm_chartMap hy]
    · simp only [hd1, unlift_symm_chartMap hy]
  · obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    exact (curveOn_chartMap_lt hy hV (fun t ht => hmapsU _ (hc.mem t ht)) hc).rel_of_lt
      (Causal.Precausality.isRelFamily_lt _) le_rfl hab le_rfl
  · obtain ⟨d, hd, hd0, hd1⟩ := ((Causal.minkowski_causallyArcConnected U le_top _ _).2).1 h
    refine ⟨0, 1, zero_lt_one, _, curveOn_pullback hy hV hU
      (Causal.Precausality.isRelFamily_lt _) hdLt hd, ?_, ?_⟩
    · simp only [hd0, unlift_symm_chartMap hy]
    · simp only [hd1, unlift_symm_chartMap hy]

/-- **The sector chart is an abstract `𝕄≥0`-morphism** (`Causal.IsEMorphismOn`), injective:
`𝔼₀ ∖ sing₀` is locally Minkowski space as a topological spacetime. -/
theorem isEMorphismOn_chartMap (hy : y.2 ≠ 0) :
    Causal.IsEMorphismOn causality (Causal.minkowski 2) (sectorOpens y) (chartMap y) where
  continuousOn := continuousOn_chartMap y
  isOpen_image V hV := isOpen_image_chartMap hy hV V.isOpen
  map_le V U hV hmaps x z h := by
    obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    have hcM := curveOn_chartMap_le hy hV (fun t ht => hmaps (hc.mem t ht)) hc
    rcases hab.lt_or_eq with hab | hab
    · exact hcM.rel_of_lt (Causal.Precausality.isRelFamily_le _) le_rfl hab le_rfl
    · rw [hab]; exact (Causal.minkowski 2).le_refl (hmaps (hc.mem b ⟨hab.le, le_rfl⟩))
  map_lt V U hV hmaps x z h := by
    obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    exact (curveOn_chartMap_lt hy hV (fun t ht => hmaps (hc.mem t ht)) hc).rel_of_lt
      (Causal.Precausality.isRelFamily_lt _) le_rfl hab le_rfl
  locally x hx := ⟨sectorOpens y, le_rfl, hx, injOn_chartMap hy, fun V' hV' U hU p hp q hq =>
    chartIso_sector hy hV' hU hp hq⟩

end Sector

/-! ### Cone slices (`LocalModel.coneSliceFuture`, `coneSlicePast`) -/

section Slices

open TopologicalSpace

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- **The cone-slice property at `y`** in the shape of `LocalModel.coneSliceFuture` /
`coneSlicePast`: in every open `O ∋ y`, a set `K ⊆ O` of points `z ≠ y` with `Q O z` such that every
open `V ⊇ K` contains a Cauchy surface `Γ` of some open `N ∋ y`, `N ⊆ O`. -/
def SliceAt (C : Causal.Causality M) (y : M) (Q : Opens M → M → Prop) : Prop :=
  ∀ O : Opens M, y ∈ O → ∃ K : Set M, K ⊆ O ∧ (∀ z ∈ K, z ≠ y ∧ Q O z) ∧
    ∀ V : Set M, IsOpen V → K ⊆ V → ∃ (N : Opens M) (Γ : Set M), y ∈ N ∧ N ≤ O ∧ Γ ⊆ N ∧
      Γ ⊆ V ∧ C.IsCauchySurfaceOn N Γ

/-- **Pull-back of cone slices** along an injective abstract `𝕄≥0`-morphism on `W ∋ y`. -/
theorem SliceAt.pullback {C : Causal.Causality M} {D : Causal.Causality N} {W : Opens M} {φ : M → N}
    (h : Causal.IsEMorphismOn C D W φ) (hinj : InjOn φ W) {y : M} (hy : y ∈ W)
    {QM : Opens M → M → Prop} {QN : Opens N → N → Prop}
    (hQmono : ∀ {O₁ O₂ : Opens M}, O₁ ≤ O₂ → ∀ z, QM O₁ z → QM O₂ z)
    (hQ : ∀ O' : Opens M, O' ≤ W → y ∈ O' → ∀ U : Opens N, (U : Set N) = φ '' O' →
      ∀ z ∈ O', QN U (φ z) → QM O' z)
    (hD : SliceAt D (φ y) QN) : SliceAt C y QM := by
  intro O hyO
  set O' : Opens M := O ⊓ W
  have hyO' : y ∈ O' := ⟨hyO, hy⟩
  set U' : Opens N := ⟨φ '' O', h.isOpen_image O' inf_le_right⟩
  obtain ⟨K', hK'U, hK'p, hK'V⟩ := hD U' (mem_image_of_mem φ hyO')
  have hcont : ContinuousOn φ W := h.continuousOn
  refine ⟨O' ∩ φ ⁻¹' K', fun z hz => hz.1.1, fun z hz => ?_, fun V hV hKV => ?_⟩
  · obtain ⟨hne, hq⟩ := hK'p _ hz.2
    exact ⟨fun hzy => hne (hzy ▸ rfl), hQmono inf_le_left z (hQ O' inf_le_right hyO' U' rfl z hz.1 hq)⟩
  · set OV : Opens M := O' ⊓ ⟨V, hV⟩
    set V' : Set N := φ '' OV
    have hV'o : IsOpen V' := h.isOpen_image OV (inf_le_left.trans inf_le_right)
    have hK'V' : K' ⊆ V' := fun k' hk' => by
      obtain ⟨k, hk, rfl⟩ := hK'U hk'
      exact ⟨k, ⟨hk, hKV ⟨hk, hk'⟩⟩, rfl⟩
    obtain ⟨N', Γ', hyN', hN'U, hΓN', hΓV', hC⟩ := hK'V V' hV'o hK'V'
    have hNo : IsOpen ((O' : Set M) ∩ φ ⁻¹' N') :=
      (hcont.mono inf_le_right).isOpen_inter_preimage O'.isOpen N'.isOpen
    set Nm : Opens M := ⟨(O' : Set M) ∩ φ ⁻¹' N', hNo⟩
    have himN : (N' : Set N) = φ '' Nm := by
      ext n'
      refine ⟨fun hn' => ?_, fun ⟨o, ho, hoe⟩ => hoe ▸ ho.2⟩
      obtain ⟨o, ho, rfl⟩ := hN'U hn'
      exact ⟨o, ⟨ho, hn'⟩, rfl⟩
    have himΓ : Γ' = φ '' ((O' : Set M) ∩ φ ⁻¹' Γ') := by
      ext n'
      refine ⟨fun hn' => ?_, fun ⟨o, ho, hoe⟩ => hoe ▸ ho.2⟩
      obtain ⟨o, ho, rfl⟩ := hN'U (hΓN' hn')
      exact ⟨o, ⟨ho, hn'⟩, rfl⟩
    refine ⟨Nm, (O' : Set M) ∩ φ ⁻¹' Γ', ⟨hyO', hyN'⟩, fun z hz => hz.1.1,
      fun z hz => ⟨hz.1, hΓN' hz.2⟩, fun z hz => ?_, ?_⟩
    · obtain ⟨v, hv, hve⟩ := hΓV' hz.2
      have : v = z := hinj (hv.1.2) (hz.1.2) hve
      exact this ▸ hv.2
    · have hNW : Nm ≤ W := fun z (hz : z ∈ (O' : Set M) ∩ φ ⁻¹' N') => hz.1.2
      have hΓN : (O' : Set M) ∩ φ ⁻¹' Γ' ⊆ Nm := fun z (hz : z ∈ (O' : Set M) ∩ φ ⁻¹' Γ') =>
        (⟨hz.1, hΓN' hz.2⟩ : z ∈ (O' : Set M) ∩ φ ⁻¹' N')
      rw [h.isCauchySurfaceOn_image_iff hinj hNW himN hΓN, ← himΓ]
      exact hC

/-- **Push-forward of cone slices** along an injective abstract `𝕄≥0`-morphism defined everywhere. -/
theorem SliceAt.pushforward {C : Causal.Causality M} {D : Causal.Causality N} {φ : M → N}
    (h : Causal.IsEMorphismOn C D ⊤ φ) (hinj : Injective φ) {y : M}
    {QM : Opens M → M → Prop} {QN : Opens N → N → Prop}
    (hQ : ∀ (O : Opens N) (hO : IsOpen (φ ⁻¹' (O : Set N))) (z : M),
      QM ⟨φ ⁻¹' (O : Set N), hO⟩ z → QN O (φ z))
    (hC : SliceAt C y QM) : SliceAt D (φ y) QN := by
  have hcont : Continuous φ := continuousOn_univ.1 (by simpa using h.continuousOn)
  intro O hyO
  have hOo : IsOpen (φ ⁻¹' (O : Set N)) := O.isOpen.preimage hcont
  obtain ⟨K, hKO, hKp, hKV⟩ := hC ⟨φ ⁻¹' O, hOo⟩ hyO
  refine ⟨φ '' K, fun _ ⟨z, hz, hze⟩ => hze ▸ hKO hz, ?_, fun V hV hKV' => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hne, hq⟩ := hKp z hz
    exact ⟨fun h' => hne (hinj h'), hQ O hOo z hq⟩
  · obtain ⟨Nm, Γ, hyN, hNO, hΓN, hΓV, hCa⟩ := hKV (φ ⁻¹' V) (hV.preimage hcont)
      fun z hz => hKV' ⟨z, hz, rfl⟩
    refine ⟨⟨φ '' Nm, h.isOpen_image Nm le_top⟩, φ '' Γ, ⟨y, hyN, rfl⟩,
      fun _ ⟨z, hz, hze⟩ => hze ▸ hNO hz, image_mono hΓN, fun _ ⟨z, hz, hze⟩ => hze ▸ hΓV hz, ?_⟩
    exact (h.isCauchySurfaceOn_image_iff hinj.injOn le_top rfl hΓN).1 hCa

/-- Minkowski's cone slices (`Causal.CBG.minkowski_coneSlice`) in the shape of `SliceAt`. -/
theorem minkowski_sliceAt_future (m : Causal.Minkowski 2) :
    SliceAt (Causal.minkowski 2) m fun O z => (Causal.minkowski 2).le O z m := by
  intro O hO
  obtain ⟨K, hK, hKp, hV⟩ := Causal.CBG.minkowski_coneSlice (Or.inl rfl) m O hO
  exact ⟨K, hK, fun z hz => ⟨(hKp z hz).1, (hKp z hz).2.1 rfl⟩, hV⟩

theorem minkowski_sliceAt_past (m : Causal.Minkowski 2) :
    SliceAt (Causal.minkowski 2) m fun O z => (Causal.minkowski 2).le O m z := by
  intro O hO
  obtain ⟨K, hK, hKp, hV⟩ := Causal.CBG.minkowski_coneSlice (Or.inr rfl) m O hO
  exact ⟨K, hK, fun z hz => ⟨(hKp z hz).1, (hKp z hz).2.2 rfl⟩, hV⟩

/-- **Cone slices of `𝔼₀` off the axis, future side** (transported from Minkowski space through the
sector chart). -/
theorem sliceAt_future_of_not_mem_axis {y : E0} (hy : y ∉ axis) :
    SliceAt causality y fun O z => z ∉ axis ∧ causality.le O z y := by
  have hy0 : y.2 ≠ 0 := hy
  refine SliceAt.pullback (isEMorphismOn_chartMap hy0) (injOn_chartMap hy0)
    (mem_sector_self hy0) (fun hO _ h => ⟨h.1, causality.le_mono hO h.2⟩) ?_
    (minkowski_sliceAt_future (chartMap y y))
  intro O' hO' hyO' U hU z hz hq
  exact ⟨not_mem_axis_of_mem_sector (hO' hz), (chartIso_sector hy0 hO' hU hz hyO').1.2 hq⟩

/-- **Cone slices of `𝔼₀` off the axis, past side.** -/
theorem sliceAt_past_of_not_mem_axis {y : E0} (hy : y ∉ axis) :
    SliceAt causality y fun O z => causality.le O y z := by
  have hy0 : y.2 ≠ 0 := hy
  refine SliceAt.pullback (isEMorphismOn_chartMap hy0) (injOn_chartMap hy0)
    (mem_sector_self hy0) (fun hO _ h => causality.le_mono hO h) ?_
    (minkowski_sliceAt_past (chartMap y y))
  intro O' hO' hyO' U hU z hz hq
  exact (chartIso_sector hy0 hO' hU hyO' hz).1.2 hq

end Slices

/-! ### `h = τ + r` is a time function; curves extend; the sector charts as charts -/

section TimeChart

open TopologicalSpace

/-- **`h = τ + r` is strictly increasing along `≤`**: a continuous time function of `𝔼₀`. -/
theorem hcoord_lt_of_le (h : causality.le ⊤ x y) (hne : x ≠ y) : hcoord x < hcoord y := by
  obtain ⟨θ₁, θ₂, hx, hy, hc⟩ := le_iff_closed.1 (le_top_iff.1 h)
  obtain ⟨hτ, hr, hq⟩ := hc
  rcases (show hcoord x ≤ hcoord y by simp only [hcoord]; linarith).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    simp only [hcoord] at h'
    have hτ' : x.1 = y.1 := by linarith
    have hr' : rad x = rad y := by linarith
    rw [hr', sub_self, zero_mul] at hq
    apply hne
    rcases (rad_nonneg y).lt_or_eq with hpos | hzero
    · have hθ : θ₂ - θ₁ = 0 := by
        have : rad y * rad y * (θ₂ - θ₁) ^ 2 = 0 :=
          le_antisymm hq (by positivity)
        have hyy : rad y * rad y ≠ 0 := by positivity
        exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this).resolve_left hyy)
      have : θ₂ = θ₁ := by linarith
      refine Prod.ext hτ' ?_
      rw [hx, hy, hr', this]
    · exact Prod.ext hτ' ((rad_eq_zero.1 (hr' ▸ hzero.symm)).trans
        (rad_eq_zero.1 hzero.symm).symm)

/-- **Causal curves of `𝔼₀` extend to inextensible ones** (`Causal.Causality.CurvesExtend`), by the
time function `h`. -/
theorem curvesExtend : causality.CurvesExtend :=
  Causal.Causality.curvesExtend_of_timeFunction continuous_hcoord fun _ _ h hne =>
    hcoord_lt_of_le h hne

/-- **`𝔼₀` is causal**: `≤` is antisymmetric. -/
theorem isCausal : causality.IsCausal := fun x y h₁ h₂ => by
  by_contra hne
  exact absurd (hcoord_lt_of_le h₁ hne) (not_lt.2 (hcoord_lt_of_le h₂ (Ne.symm hne)).le)

variable {y : E0}

/-- **The sector chart** as an open partial homeomorphism `sector y → 𝐌³`. -/
noncomputable def sectorChart (y : E0) (hy : y.2 ≠ 0) :
    OpenPartialHomeomorph E0 (Causal.Minkowski 2) where
  toFun := chartMap y
  invFun m := unlift (nullToMink.symm m)
  source := sector y
  target := chartMap y '' sector y
  map_source' _ hw := mem_image_of_mem _ hw
  map_target' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [unlift_symm_chartMap hy]; exact hw
  left_inv' w _ := unlift_symm_chartMap hy w
  right_inv' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [unlift_symm_chartMap hy]
  open_source := isOpen_sector y
  open_target := isOpen_image_chartMap hy subset_rfl (isOpen_sector y)
  continuousOn_toFun := continuousOn_chartMap y
  continuousOn_invFun := by
    rintro _ ⟨w, hw, rfl⟩
    have hB : (nullToMink.symm (chartMap y w)).2.1 ≠ 0 := by
      rw [chartMap, LinearEquiv.symm_apply_apply]
      exact (norm_pos_iff.2 (ne_zero_of_mem_sector hw)).ne'
    exact ((continuousAt_unlift hB).comp
      nullToMinkHomeomorph.symm.continuous.continuousAt).continuousWithinAt

/-- **Off the axis the sector chart is a chart isomorphism** (`Causal.ChartIso`, the `LocalModel`
field `chartIso_mem`'s content on the regular part of `𝔼₀`): for every open `U` of its source,
`≤_U` and `≪_U` are Minkowski's `≤` and `≪` on the image. -/
theorem chartIso_sectorChart (hy : y.2 ≠ 0) :
    Causal.ChartIso causality (Causal.minkowski 2) (sectorChart y hy) := by
  intro U hU p hp q hq
  have hsub : (U : Set E0) ⊆ sector y := hU
  have himg : ((Causal.chartImage (sectorChart y hy) U : Opens _) : Set (Causal.Minkowski 2)) =
      chartMap y '' U := by
    rw [Causal.coe_chartImage]
    congr 1
    exact inter_eq_right.2 hsub
  exact chartIso_sector hy hsub himg hp hq

end TimeChart

/-! ### The metric control of `≼`; closed causal cones; strong causality -/

section Closed

open TopologicalSpace

/-- `‖e^{iθ₂} − e^{iθ₁}‖ ≤ |θ₂ − θ₁|`. -/
theorem norm_cexp_sub_cexp_le (θ₁ θ₂ : ℝ) :
    ‖cexp (θ₂ * I) - cexp (θ₁ * I)‖ ≤ |θ₂ - θ₁| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ₂ - θ₁)
  have e : cexp (θ₂ * I) - cexp (θ₁ * I) = cexp (θ₁ * I) * (cexp (I * ↑(θ₂ - θ₁)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [Real.norm_eq_abs] using h

/-- **Along `≼` the displacement is controlled by the elapsed time**: `‖z_y − z_x‖ ≤ 3(τ_y − τ_x)`
(`r₁|δ| ≤ Δτ` from the closed form, and `Δr ≤ 2Δτ`). -/
theorem Le.norm_sub_le (h : Le x y) : ‖y.2 - x.2‖ ≤ 3 * (y.1 - x.1) := by
  obtain ⟨θ₁, θ₂, hx, hy, hτ, hr, hq⟩ := le_iff_closed.1 h
  have h1 := rad_nonneg x
  have h2 := rad_nonneg y
  have hτ' : 0 ≤ y.1 - x.1 := sub_nonneg.2 hτ
  have hsq : (rad x * |θ₂ - θ₁|) ^ 2 ≤ (y.1 - x.1) ^ 2 := by
    have : (rad x * |θ₂ - θ₁|) ^ 2 ≤ rad x * rad y * (θ₂ - θ₁) ^ 2 := by
      rw [mul_pow, sq_abs]
      have : rad x ^ 2 ≤ rad x * rad y := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    nlinarith [sq_nonneg ((y.1 - x.1) - (rad y - rad x))]
  have hδ : rad x * |θ₂ - θ₁| ≤ y.1 - x.1 :=
    (sq_le_sq₀ (mul_nonneg h1 (abs_nonneg _)) hτ').1 hsq
  have hd : rad y - rad x ≤ 2 * (y.1 - x.1) := (calculus_le (U := ⊤) (le_top_iff.2 h)).2.1
  have hnorm : ‖y.2 - x.2‖ ≤ (rad y - rad x) + rad x * |θ₂ - θ₁| := by
    have e : y.2 - x.2 = ((rad y - rad x : ℝ) : ℂ) * cexp (θ₂ * I) +
        (rad x : ℂ) * (cexp (θ₂ * I) - cexp (θ₁ * I)) := by
      conv_lhs => rw [hx, hy]
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 hr)]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
      exact mul_le_mul_of_nonneg_left (norm_cexp_sub_cexp_le θ₁ θ₂) h1
  linarith

/-- **`dist x y ≤ 3(τ_y − τ_x)` along `≼`.** -/
theorem Le.dist_le (h : Le x y) : dist x y ≤ 3 * (y.1 - x.1) := by
  have hτ := h.closed.1
  rw [Prod.dist_eq, Real.dist_eq, dist_comm, dist_eq_norm]
  exact max_le (by rw [abs_le]; constructor <;> linarith) h.norm_sub_le

theorem abs_fst_sub_le_dist (x y : E0) : |x.1 - y.1| ≤ dist x y := by
  rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _

/-- The distance to a point of the axis. -/
theorem dist_axis {w : E0} (hw : w ∈ axis) (z : E0) : dist z w = max |z.1 - w.1| (rad z) := by
  have hw0 : w.2 = 0 := hw
  rw [Prod.dist_eq, Real.dist_eq, hw0, dist_zero_right]; rfl

/-- **The winding can be read within `π` of the principal angle of the source.** -/
theorem le_iff_bounded : Le x y ↔ ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ ∧
    NullCone (lift y θ - lift x (arg x.2)) := by
  constructor
  · intro h
    obtain ⟨θ, hθ, hpol⟩ : ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ := by
      by_cases hx : x.2 = 0
      · refine ⟨arg y.2, ?_, polar_arg y⟩
        rw [hx, Complex.arg_zero]
        exact ⟨by linarith [Complex.neg_pi_lt_arg y.2], by linarith [Complex.arg_le_pi y.2]⟩
      · exact ⟨arg x.2 + arg (y.2 / x.2), ⟨by linarith [Complex.neg_pi_lt_arg (y.2 / x.2)],
          by linarith [Complex.arg_le_pi (y.2 / x.2)]⟩, polar_add_arg_div x y hx⟩
    refine ⟨θ, hθ, hpol, h.of_polar (polar_arg x) hpol ?_⟩
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  · rintro ⟨θ, -, hpol, h⟩
    exact ⟨_, _, polar_arg x, hpol, h⟩

/-- The same, with `x` the target. -/
theorem le_iff_bounded' : Le y x ↔ ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ ∧
    NullCone (lift x (arg x.2) - lift y θ) := by
  constructor
  · intro h
    obtain ⟨θ, hθ, hpol⟩ : ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ := by
      by_cases hx : x.2 = 0
      · refine ⟨arg y.2, ?_, polar_arg y⟩
        rw [hx, Complex.arg_zero]
        exact ⟨by linarith [Complex.neg_pi_lt_arg y.2], by linarith [Complex.arg_le_pi y.2]⟩
      · exact ⟨arg x.2 + arg (y.2 / x.2), ⟨by linarith [Complex.neg_pi_lt_arg (y.2 / x.2)],
          by linarith [Complex.arg_le_pi (y.2 / x.2)]⟩, polar_add_arg_div x y hx⟩
    refine ⟨θ, hθ, hpol, h.of_polar hpol (polar_arg x) ?_⟩
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  · rintro ⟨θ, -, hpol, h⟩
    exact ⟨_, _, hpol, polar_arg x, h⟩

theorem isClosed_nullCone : IsClosed {V : ℝ × ℝ × ℝ | NullCone V} :=
  (isClosed_le continuous_const continuous_fst).inter ((isClosed_le continuous_const
    continuous_snd.fst).inter (isClosed_le (continuous_snd.snd.pow 2)
      (continuous_fst.mul continuous_snd.fst)))

theorem continuous_lift : Continuous fun p : E0 × ℝ => lift p.1 p.2 :=
  continuous_btzPaperNull.comp ((continuous_fst.comp continuous_fst).prodMk
    ((continuous_rad.comp continuous_fst).prodMk continuous_snd))

theorem isClosed_polar : IsClosed {p : E0 × ℝ | Polar p.1 p.2} := by
  refine isClosed_eq (continuous_snd.comp continuous_fst) ?_
  exact (Complex.continuous_ofReal.comp (continuous_rad.comp continuous_fst)).mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      continuous_const))

/-- A set of the shape `{y | ∃ θ ∈ [α, β], Polar y θ ∧ NullCone (g (y, θ))}` is closed. -/
theorem isClosed_exists_polar_nullCone {g : E0 × ℝ → ℝ × ℝ × ℝ} (hg : Continuous g) (α β : ℝ) :
    IsClosed {y : E0 | ∃ θ ∈ Icc α β, Polar y θ ∧ NullCone (g (y, θ))} := by
  haveI : CompactSpace (Icc α β) := isCompact_iff_compactSpace.1 isCompact_Icc
  set F : E0 × Icc α β → E0 × ℝ := fun p => (p.1, (p.2 : ℝ))
  have hF : Continuous F := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hS : IsClosed (F ⁻¹' ({p : E0 × ℝ | Polar p.1 p.2} ∩ g ⁻¹' {V | NullCone V})) :=
    (isClosed_polar.inter (isClosed_nullCone.preimage hg)).preimage hF
  convert isClosedMap_fst_of_compactSpace _ hS using 1
  ext y
  constructor
  · rintro ⟨θ, hθ, hp, hn⟩
    exact ⟨(y, ⟨θ, hθ⟩), ⟨hp, hn⟩, rfl⟩
  · rintro ⟨⟨y', θ⟩, ⟨hp, hn⟩, rfl⟩
    exact ⟨θ, θ.2, hp, hn⟩

/-- **`J⁺(x)` is closed.** -/
theorem isClosed_Jplus (x : E0) : IsClosed (causality.Jplus ⊤ {x}) := by
  have : causality.Jplus ⊤ {x} = {y : E0 | ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ ∧
      NullCone ((fun p : E0 × ℝ => lift p.1 p.2 - lift x (arg x.2)) (y, θ))} := by
    ext y; rw [Causal.Precausality.mem_Jplus_singleton, le_top_iff, le_iff_bounded]; rfl
  rw [this]
  exact isClosed_exists_polar_nullCone (continuous_lift.sub continuous_const) _ _

/-- **`J⁻(x)` is closed.** -/
theorem isClosed_Jminus (x : E0) : IsClosed (causality.Jminus ⊤ {x}) := by
  have : causality.Jminus ⊤ {x} = {y : E0 | ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ ∧
      NullCone ((fun p : E0 × ℝ => lift x (arg x.2) - lift p.1 p.2) (y, θ))} := by
    ext y; rw [Causal.Precausality.mem_Jminus_singleton, le_top_iff, le_iff_bounded']; rfl
  rw [this]
  exact isClosed_exists_polar_nullCone (continuous_const.sub continuous_lift) _ _

/-- **`𝔼₀` is strongly causal** (`def:strongly_causal_spacetime`): `J⁺(B) ∩ J⁻(B)` for a small ball
`B` is causally convex and lies in the ball of `7` times the radius (`Le.dist_le`). -/
theorem stronglyCausal : causality.StronglyCausal := by
  intro p U hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  set B := Metric.ball p (δ / 10)
  have hBo : IsOpen B := Metric.isOpen_ball
  refine ⟨causality.Jplus ⊤ B ∩ causality.Jminus ⊤ B, ?_, ?_, ?_⟩
  · exact Filter.mem_of_superset (hBo.mem_nhds (Metric.mem_ball_self (by positivity)))
      fun z hz => ⟨⟨z, hz, causality.le_refl trivial⟩, ⟨z, hz, causality.le_refl trivial⟩⟩
  · rintro z ⟨⟨u, hu, huz⟩, ⟨v, hv, hzv⟩⟩
    apply hball
    have h1 := (le_top_iff.1 huz).dist_le
    have h2 := (le_top_iff.1 hzv).closed.1
    have hu' : dist u p < δ / 10 := hu
    have hv' : dist v p < δ / 10 := hv
    have hτu := abs_lt.1 ((abs_fst_sub_le_dist u p).trans_lt hu')
    have hτv := abs_lt.1 ((abs_fst_sub_le_dist v p).trans_lt hv')
    rw [Metric.mem_ball]
    calc dist z p ≤ dist z u + dist u p := dist_triangle _ _ _
      _ = dist u z + dist u p := by rw [dist_comm z u]
      _ < δ := by linarith [hτu.1, hτu.2, hτv.1, hτv.2]
  · refine ⟨fun _ _ => trivial, fun a ha b hb w hw => ?_⟩
    obtain ⟨⟨u, hu, hua⟩, -⟩ := ha
    obtain ⟨-, ⟨v, hv, hbv⟩⟩ := hb
    have hwb : causality.le ⊤ w b := Causal.Precausality.mem_Jminus_singleton.1 hw.1
    have haw : causality.le ⊤ a w := Causal.Precausality.mem_Jplus_singleton.1 hw.2
    exact ⟨⟨u, hu, causality.le_trans hua haw⟩, ⟨v, hv, causality.le_trans hwb hbv⟩⟩

end Closed

/-! ### Limits of causal curves; non-trivial local cones -/

section Limits

open TopologicalSpace

/-- **A causal curve of `𝔼₀` whose time is bounded above converges at its upper end**
(`𝔼₀ = ℝ × ℂ` is complete, and `dist ≤ 3Δτ` along `≼`, `Le.dist_le`). -/
theorem exists_tendsto_of_bddAbove {J : Set ℝ} {γ : ℝ → E0} {β : ℝ}
    (hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → Le (γ u) (γ u'))
    (hJ : J.Nonempty) (hJc : J.OrdConnected) (hβ : IsLUB J β) (hβJ : β ∉ J)
    (hbdd : BddAbove ((fun u => (γ u).1) '' J)) : ∃ p, Tendsto γ (𝓝[<] β) (𝓝 p) := by
  have hlt : ∀ u ∈ J, u < β := fun u hu =>
    lt_of_le_of_ne (hβ.1 hu) fun he => hβJ (he ▸ hu)
  set τ := sSup ((fun u => (γ u).1) '' J)
  have hcauchy : Cauchy (map γ (𝓝[<] β)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hτ⟩ :=
      exists_lt_of_lt_csSup (hJ.image _) (sub_lt_self τ (by positivity : 0 < ε / 3))
    have hsub := Causal.Flat.Ioo_subset_of_isLUB hJc hβ hu₁
    refine ⟨γ '' Ioo u₁ β, mem_map.2 (mem_of_superset (Ioo_mem_nhdsLT (hlt u₁ hu₁))
      (subset_preimage_image _ _)), ?_⟩
    have key : ∀ u ∈ Ioo u₁ β, ∀ u' ∈ Ioo u₁ β, u ≤ u' → dist (γ u) (γ u') < ε :=
      fun u hu u' hu' huu' => by
        have h1 := (hle u (hsub hu) u' (hsub hu') huu').dist_le
        have h2 := (hle u₁ hu₁ u (hsub hu) hu.1.le).closed.1
        have h3 : (γ u').1 ≤ τ := le_csSup hbdd ⟨u', hsub hu', rfl⟩
        linarith
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rcases le_total u u' with huu' | huu'
    · exact key u hu u' hu' huu'
    · rw [dist_comm]; exact key u' hu' u hu huu'
  obtain ⟨p, hp⟩ := CompleteSpace.complete hcauchy
  exact ⟨p, hp⟩

/-- **A causal curve of `𝔼₀` whose time is bounded below converges at its lower end.** -/
theorem exists_tendsto_of_bddBelow {J : Set ℝ} {γ : ℝ → E0} {α : ℝ}
    (hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → Le (γ u) (γ u'))
    (hJ : J.Nonempty) (hJc : J.OrdConnected) (hα : IsGLB J α) (hαJ : α ∉ J)
    (hbdd : BddBelow ((fun u => (γ u).1) '' J)) : ∃ p, Tendsto γ (𝓝[>] α) (𝓝 p) := by
  have hgt : ∀ u ∈ J, α < u := fun u hu =>
    lt_of_le_of_ne (hα.1 hu) fun he => hαJ (he ▸ hu)
  set σ := sInf ((fun u => (γ u).1) '' J)
  have hcauchy : Cauchy (map γ (𝓝[>] α)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hσ⟩ :=
      exists_lt_of_csInf_lt (hJ.image _) (lt_add_of_pos_right σ (by positivity : 0 < ε / 3))
    have hsub := Causal.Flat.Ioo_subset_of_isGLB hJc hα hu₁
    refine ⟨γ '' Ioo α u₁, mem_map.2 (mem_of_superset (Ioo_mem_nhdsGT (hgt u₁ hu₁))
      (subset_preimage_image _ _)), ?_⟩
    have key : ∀ u ∈ Ioo α u₁, ∀ u' ∈ Ioo α u₁, u ≤ u' → dist (γ u) (γ u') < ε :=
      fun u hu u' hu' huu' => by
        have h1 := (hle u (hsub hu) u' (hsub hu') huu').dist_le
        have h2 := (hle u' (hsub hu') u₁ hu₁ hu'.2.le).closed.1
        have h3 : σ ≤ (γ u).1 := csInf_le hbdd ⟨u, hsub hu, rfl⟩
        linarith
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rcases le_total u u' with huu' | huu'
    · exact key u hu u' hu' huu'
    · rw [dist_comm]; exact key u' hu' u hu huu'
  obtain ⟨p, hp⟩ := CompleteSpace.complete hcauchy
  exact ⟨p, hp⟩

/-- A short initial piece of a straight causal segment stays in an open set containing its start. -/
theorem exists_seg_mem_start (hP : Adm P) (hPQ : NullCone (Q - P)) {W : Opens E0}
    (hW : unlift P ∈ W) : ∃ s₀ ∈ Ioc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) s₀, unlift (seg P Q s) ∈ W := by
  have hcont := continuousOn_unlift_seg hP hPQ
  have hpre : (fun s => unlift (seg P Q s)) ⁻¹' W ∈ 𝓝[Icc 0 1] 0 :=
    hcont 0 ⟨le_rfl, zero_le_one⟩ (by beta_reduce; rw [seg_zero]; exact W.isOpen.mem_nhds hW)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨min (ε / 2) 1, ⟨lt_min (by linarith) one_pos, min_le_right _ _⟩, fun s hs => ?_⟩
  refine hball ⟨?_, hs.1, hs.2.trans (min_le_right _ _)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
  exact hs.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))

/-- A short final piece of a straight causal segment stays in an open set containing its end. -/
theorem exists_seg_mem_end (hP : Adm P) (hPQ : NullCone (Q - P)) {W : Opens E0}
    (hW : unlift Q ∈ W) : ∃ s₀ ∈ Ico (0 : ℝ) 1, ∀ s ∈ Icc s₀ 1, unlift (seg P Q s) ∈ W := by
  have hcont := continuousOn_unlift_seg hP hPQ
  have hpre : (fun s => unlift (seg P Q s)) ⁻¹' W ∈ 𝓝[Icc 0 1] 1 :=
    hcont 1 ⟨zero_le_one, le_rfl⟩ (by beta_reduce; rw [seg_one]; exact W.isOpen.mem_nhds hW)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨max (1 - ε / 2) 0, ⟨le_max_right _ _, max_lt (by linarith) one_pos⟩, fun s hs => ?_⟩
  refine hball ⟨?_, (le_max_right _ _).trans hs.1, hs.2⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  have := (le_max_left (1 - ε / 2) 0).trans hs.1
  constructor <;> linarith [hs.2]

/-- The piece `[s, s']` of a straight causal segment is a causal curve of every open set holding
it. -/
theorem cle_of_seg_piece (hP : Adm P) (hPQ : NullCone (Q - P)) {W : Opens E0} {s s' : ℝ}
    (hs : 0 ≤ s) (hss' : s ≤ s') (hs' : s' ≤ 1)
    (hW : ∀ σ ∈ Icc s s', unlift (seg P Q σ) ∈ W) :
    CLe W (unlift (seg P Q s)) (unlift (seg P Q s')) :=
  ⟨s, s', hss', _, curveOn_of_continuousOn ((continuousOn_unlift_seg hP hPQ).mono
    (Icc_subset_Icc hs hs')) hW fun _ hσ _ _ h => le_unlift_seg hP hPQ (hs.trans hσ.1) h.le,
    rfl, rfl⟩

theorem Lt.ne (h : Lt x y) : x ≠ y := fun he => by
  have := h.closed.1; rw [he] at this; exact lt_irrefl _ this

variable {p : E0}

/-- **Every point has a causal future point in each open set containing it.** -/
theorem exists_le_ne (W : Opens E0) (hp : p ∈ W) : ∃ q, causality.le W p q ∧ q ≠ p := by
  set P := lift p (arg p.2)
  set Q := P + timelikeT 1
  have hPQ : NullConeLt (Q - P) := by
    rw [show Q - P = timelikeT 1 by simp [Q]]; exact nullConeLt_timelikeT one_pos
  have hP : Adm P := adm_lift p _
  have hPp : unlift P = p := unlift_lift (polar_arg p)
  obtain ⟨s₀, hs₀, hmem⟩ := exists_seg_mem_start hP hPQ.nullCone (W := W) (by rw [hPp]; exact hp)
  refine ⟨unlift (seg P Q s₀), ?_, ?_⟩
  · have := cle_of_seg_piece hP hPQ.nullCone le_rfl hs₀.1.le hs₀.2 (W := W)
      fun σ hσ => hmem σ ⟨hσ.1, hσ.2⟩
    rwa [seg_zero, hPp] at this
  · have := lt_unlift_seg hP hPQ le_rfl hs₀.1
    rw [seg_zero, hPp] at this
    exact this.ne.symm

/-- **Every point has a causal past point in each open set containing it** (off the axis by a
timelike segment, on the axis along the line). -/
theorem exists_ge_ne (W : Opens E0) (hp : p ∈ W) : ∃ q, causality.le W q p ∧ q ≠ p := by
  by_cases hax : p ∈ axis
  · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 W.isOpen p hp
    have hp0 : p.2 = 0 := hax
    have hmem : ∀ t ∈ Icc (-(δ / 2)) 0, axisLine p t ∈ W := fun t ht => hball (by
      rw [Metric.mem_ball, dist_axis hax, max_lt_iff]
      refine ⟨?_, ?_⟩
      · simp only [axisLine]; rw [add_sub_cancel_left, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      · rw [rad_eq_zero.2 (axisLine_mem p t)]; exact hδ)
    rcases curveOn_axisLine p W (-(δ / 2)) 0 with hc | hc
    · refine ⟨axisLine p (-(δ / 2)), ⟨-(δ / 2), 0, by linarith, _, hc, rfl, ?_⟩, ?_⟩
      · exact Prod.ext (add_zero _) (show (0 : ℂ) = p.2 from hp0.symm)
      · intro h
        have := congrArg Prod.fst h
        simp only [axisLine] at this
        linarith
    · exact absurd hmem hc
  · have hr := rad_pos.2 hax
    set Q := lift p (arg p.2)
    set P := Q - timelikeT (rad p / 2)
    have hPQ : NullConeLt (Q - P) := by
      rw [show Q - P = timelikeT (rad p / 2) by simp [P]]
      exact nullConeLt_timelikeT (by linarith)
    have hP : Adm P := by
      left
      have : P.2.1 = rad p - rad p / 2 := rfl
      rw [this]; linarith
    have hQp : unlift Q = p := unlift_lift (polar_arg p)
    obtain ⟨s₀, hs₀, hmem⟩ := exists_seg_mem_end hP hPQ.nullCone (W := W) (by rw [hQp]; exact hp)
    refine ⟨unlift (seg P Q s₀), ?_, ?_⟩
    · have := cle_of_seg_piece hP hPQ.nullCone hs₀.1 hs₀.2.le le_rfl (W := W)
        fun σ hσ => hmem σ hσ
      rwa [seg_one, hQp] at this
    · have := lt_unlift_seg hP hPQ hs₀.1 hs₀.2
      rw [seg_one, hQp] at this
      exact this.ne

theorem Jplus_ne_singleton {W : Opens E0} (hp : p ∈ W) : causality.Jplus W {p} ≠ {p} := by
  obtain ⟨q, hq, hne⟩ := exists_le_ne W hp
  intro h
  have : q ∈ causality.Jplus W {p} := Causal.Precausality.mem_Jplus_singleton.2 hq
  rw [h] at this; exact hne this

theorem Jminus_ne_singleton {W : Opens E0} (hp : p ∈ W) : causality.Jminus W {p} ≠ {p} := by
  obtain ⟨q, hq, hne⟩ := exists_ge_ne W hp
  intro h
  have : q ∈ causality.Jminus W {p} := Causal.Precausality.mem_Jminus_singleton.2 hq
  rw [h] at this; exact hne this

end Limits

/-! ### The cone slice at a BTZ point (`LocalModel.coneSlicePast` on the axis) -/

section AxisSlice

open TopologicalSpace

theorem fcoord_eq_hcoord (z : E0) : fcoord z = hcoord z - 3 / 2 * rad z := by
  simp only [fcoord, hcoord]; ring

theorem isOpen_sliceDom (a b c : ℝ) :
    IsOpen {z : E0 | a < fcoord z ∧ hcoord z < b ∧ rad z < 2 * (c - a) / 3} := by
  simp only [setOf_and]
  exact (isOpen_lt continuous_const continuous_fcoord).inter
    ((isOpen_lt continuous_hcoord continuous_const).inter (isOpen_lt continuous_rad continuous_const))

/-- **The development domain of the level `{h = c}` near a BTZ point**:
`N = {f > a, h < b, r < 2(c − a)/3}`. Its three walls are placed so that no inextensible causal
curve of `N` can leave it without crossing `{h = c}`: below the level the wall `r = 2(c−a)/3` is
out of reach (there `r = 2(h − f)/3 < 2(c − a)/3`), above it the wall `f = a` is (there
`f = h − 3r/2 > c − (c − a)`); the wall `h = b` is above the level. -/
def sliceDom (a b c : ℝ) : Opens E0 :=
  ⟨{z | a < fcoord z ∧ hcoord z < b ∧ rad z < 2 * (c - a) / 3}, isOpen_sliceDom a b c⟩

theorem mem_sliceDom {a b c : ℝ} {z : E0} :
    z ∈ sliceDom a b c ↔ a < fcoord z ∧ hcoord z < b ∧ rad z < 2 * (c - a) / 3 := Iff.rfl

theorem le_of_le_top_curve {W : Opens E0} {J : Set ℝ} {γ : ℝ → E0}
    (hγ : causality.CausalCurveIn W J γ) :
    ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → causality.le ⊤ (γ u) (γ u') :=
  fun _ hu _ hu' huu' => causality.le_mono le_top (hγ.le_of_le hu hu' huu')

/-- **Past end**: a causal curve of `N` above the level `{h = c}`, over a parameter interval
bounded below, is extensible in `N` at its past end (its limit there is in `N`). -/
theorem pastExtensible_sliceDom {a b c : ℝ} {J : Set ℝ} {γ : ℝ → E0}
    (hγ : causality.CausalCurveIn (sliceDom a b c) J γ) (hJ : BddBelow J)
    (hT : ∀ u ∈ J, c < hcoord (γ u)) : causality.PastExtensible (sliceDom a b c) J γ := by
  by_cases hmin : ∃ a', IsLeast J a'
  · obtain ⟨a', ha⟩ := hmin
    exact Causal.Causality.pastExtensible_of_isLeast causallyArcConnected isCausal hγ ha
      (Jminus_ne_singleton (hγ.mem ha.1))
  have hglb : IsGLB J (sInf J) := isGLB_csInf hγ.nonempty hJ
  have hαJ : sInf J ∉ J := fun hα => hmin ⟨_, hα, hglb.1⟩
  have hgt : ∀ u ∈ J, sInf J < u := fun u hu =>
    lt_of_le_of_ne (hglb.1 hu) fun he => hαJ (he ▸ hu)
  have hle := le_of_le_top_curve hγ
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  have hbdd : BddBelow ((fun u => (γ u).1) '' J) := by
    refine ⟨a, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h1 := (hγ.mem hu).1
    have h2 := rad_nonneg (γ u)
    simp only [fcoord] at h1
    linarith
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddBelow (fun u hu u' hu' h => le_top_iff.1 (hle u hu u' hu' h))
    hγ.nonempty hγ.ordConnected hglb hαJ hbdd
  have hsub := Causal.Flat.Ioo_subset_of_isGLB hγ.ordConnected hglb hu₀
  have hev : ∀ᶠ u in 𝓝[>] (sInf J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsGT (hgt u₀ hu₀)) hsub
  have hpz : causality.le ⊤ p (γ u₀) := by
    refine Causal.Precausality.mem_Jminus_singleton.1 ((isClosed_Jminus (γ u₀)).mem_of_tendsto hp ?_)
    filter_upwards [Ioo_mem_nhdsGT (hgt u₀ hu₀)] with u hu
    exact Causal.Precausality.mem_Jminus_singleton.2 (hle u (hsub hu) u₀ hu₀ hu.2.le)
  have hhp : c ≤ hcoord p := (isClosed_le continuous_const continuous_hcoord).mem_of_tendsto hp
    (hev.mono fun u hu => (hT u hu).le)
  have hcal := calculus_le hpz
  obtain ⟨-, hz2, hz3⟩ := hγ.mem hu₀
  have hpN : p ∈ sliceDom a b c := by
    refine ⟨?_, by linarith [hcal.2.2.2.2.2], by linarith [hcal.2.2.2.1]⟩
    rw [fcoord_eq_hcoord]; linarith [hcal.2.2.2.1]
  exact Causal.Causality.pastExtensible_of_tendsto_opens isClosed_Jminus stronglyCausal
    causallyArcConnected isCausal hγ hpN hgt
    (Causal.Flat.ordConnected_insert_of_isGLB hγ.ordConnected hglb) hp (Jminus_ne_singleton hpN)

/-- **Future end**: a causal curve of `N` below the level `{h = c}` (`c < b`), over a parameter
interval bounded above, is extensible in `N` at its future end. -/
theorem futureExtensible_sliceDom {a b c : ℝ} (hcb : c < b) {J : Set ℝ} {γ : ℝ → E0}
    (hγ : causality.CausalCurveIn (sliceDom a b c) J γ) (hJ : BddAbove J)
    (hT : ∀ u ∈ J, hcoord (γ u) < c) : causality.FutureExtensible (sliceDom a b c) J γ := by
  by_cases hmax : ∃ b', IsGreatest J b'
  · obtain ⟨b', hb⟩ := hmax
    exact Causal.Causality.futureExtensible_of_isGreatest causallyArcConnected isCausal hγ hb
      (Jplus_ne_singleton (hγ.mem hb.1))
  have hlub : IsLUB J (sSup J) := isLUB_csSup hγ.nonempty hJ
  have hβJ : sSup J ∉ J := fun hβ => hmax ⟨_, hβ, hlub.1⟩
  have hlt : ∀ u ∈ J, u < sSup J := fun u hu =>
    lt_of_le_of_ne (hlub.1 hu) fun he => hβJ (he ▸ hu)
  have hle := le_of_le_top_curve hγ
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  have hbdd : BddAbove ((fun u => (γ u).1) '' J) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h1 := hT u hu
    have h2 := rad_nonneg (γ u)
    simp only [hcoord] at h1
    simp only
    linarith
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddAbove (fun u hu u' hu' h => le_top_iff.1 (hle u hu u' hu' h))
    hγ.nonempty hγ.ordConnected hlub hβJ hbdd
  have hsub := Causal.Flat.Ioo_subset_of_isLUB hγ.ordConnected hlub hu₀
  have hev : ∀ᶠ u in 𝓝[<] (sSup J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsLT (hlt u₀ hu₀)) hsub
  have hzp : causality.le ⊤ (γ u₀) p := by
    refine Causal.Precausality.mem_Jplus_singleton.1 ((isClosed_Jplus (γ u₀)).mem_of_tendsto hp ?_)
    filter_upwards [Ioo_mem_nhdsLT (hlt u₀ hu₀)] with u hu
    exact Causal.Precausality.mem_Jplus_singleton.2 (hle u₀ hu₀ u (hsub hu) hu.1.le)
  have hhp : hcoord p ≤ c := (isClosed_le continuous_hcoord continuous_const).mem_of_tendsto hp
    (hev.mono fun u hu => (hT u hu).le)
  have hcal := calculus_le hzp
  obtain ⟨hz1, -, -⟩ := hγ.mem hu₀
  have hfp : a < fcoord p := by linarith [hcal.2.2.2.2.1]
  have hpN : p ∈ sliceDom a b c := by
    refine ⟨hfp, by linarith, ?_⟩
    have := fcoord_eq_hcoord p
    linarith
  exact Causal.Causality.futureExtensible_of_tendsto_opens isClosed_Jplus stronglyCausal
    causallyArcConnected isCausal hγ hpN hlt
    (Causal.Flat.ordConnected_insert_of_isLUB hγ.ordConnected hlub) hp (Jplus_ne_singleton hpN)

/-- **The level `{h = c}` is a Cauchy surface of `N = sliceDom a b c`** (`c < b`): every
inextensible causal curve of `N` reaches both sides of the level (`pastExtensible_sliceDom`,
`futureExtensible_sliceDom`, after an `arctan` reparametrisation), hence meets it (intermediate
values of the continuous `h`), and meets it once (`h` strictly increasing along `≤`). -/
theorem isCauchySurfaceOn_sliceDom {a b c : ℝ} (hcb : c < b) :
    causality.IsCauchySurfaceOn (sliceDom a b c) ({z | hcoord z = c} ∩ sliceDom a b c) := by
  intro I γ hγ
  have hle := le_of_le_top_curve hγ.1
  obtain ⟨hpi, hfi⟩ := Causal.Causality.inextensible_iff.1 hγ
  obtain ⟨hd, hsub, htan, hpast, hfut⟩ := hγ.1.arctanReparam
  have hbb : BddBelow (Real.arctan '' I) := ⟨-(π / 2), fun u hu => (hsub hu).1.le⟩
  have hba : BddAbove (Real.arctan '' I) := ⟨π / 2, fun u hu => (hsub hu).2.le⟩
  obtain ⟨s₁, hs₁, h₁⟩ : ∃ s ∈ I, hcoord (γ s) ≤ c := by
    by_contra hcon
    push Not at hcon
    exact hpi.2 (hpast (pastExtensible_sliceDom hd hbb fun u hu => hcon _ (htan u hu)))
  obtain ⟨s₂, hs₂, h₂⟩ : ∃ s ∈ I, c ≤ hcoord (γ s) := by
    by_contra hcon
    push Not at hcon
    exact hfi.2 (hfut (futureExtensible_sliceDom hcb hd hba fun u hu => hcon _ (htan u hu)))
  have hex : ∃ s ∈ I, hcoord (γ s) = c := by
    rcases le_total s₁ s₂ with h12 | h21
    · have hIcc : Icc s₁ s₂ ⊆ I := hγ.1.ordConnected.out hs₁ hs₂
      have hcont : ContinuousOn (fun s => hcoord (γ s)) (Icc s₁ s₂) :=
        continuous_hcoord.comp_continuousOn (hγ.1.continuousOn_Icc hs₁ hs₂)
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc h12 hcont ⟨h₁, h₂⟩
      exact ⟨s, hIcc hs, hs0⟩
    · have := (calculus_le (hle s₂ hs₂ s₁ hs₁ h21)).2.2.2.2.2
      exact ⟨s₂, hs₂, le_antisymm (this.trans h₁) h₂⟩
  obtain ⟨s, hs, hsc⟩ := hex
  refine ⟨γ s, ⟨⟨s, hs, rfl⟩, hsc, hγ.1.mem hs⟩, ?_⟩
  rintro _ ⟨⟨s', hs', rfl⟩, hs'c, -⟩
  have hs'c' : hcoord (γ s') = c := hs'c
  by_contra hne
  rcases le_total s s' with h | h
  · have := hcoord_lt_of_le (hle s hs s' hs' h) (Ne.symm hne)
    rw [hsc, hs'c'] at this; exact lt_irrefl _ this
  · have := hcoord_lt_of_le (hle s' hs' s hs h) hne
    rw [hsc, hs'c'] at this; exact lt_irrefl _ this

/-- Points of `J⁺(w) ∩ ball(w, δ)` at a BTZ point `w` are reached inside the ball. -/
theorem cle_ball_of_le_axis {w z : E0} (hw : w ∈ axis) {δ : ℝ} (hz : z ∈ Metric.ball w δ)
    (h : Le w z) {O : Opens E0} (hO : Metric.ball w δ ⊆ O) : causality.le O w z := by
  obtain ⟨θ₁, θ₂, h₁, h₂, hc⟩ := h
  refine cle_of_seg h₁ h₂ hc fun s hs => hO ?_
  have hends := le_seg_ends (adm_lift w θ₁) hc hs
  rw [unlift_lift h₁, unlift_lift h₂] at hends
  exact mem_ball_of_le_of_le hw hends.1 hends.2 (Metric.mem_ball_self (Metric.pos_of_mem_ball hz)) hz

/-- **`LocalModel.coneSlicePast` at a BTZ point of `𝔼₀`** (the dispatch's
`K = J⁺_O(w) ∩ {τ + r = c}`, `c` slightly above `τ(w)`): `K = {f ≥ τ_w, h = c}` (the part of the
level in `J⁺(w)`, a compact disc of radius `2(c − τ_w)/3`); an open `V ⊇ K` contains the thickened
disc `{f > τ_w − η, h = c}` (compactness), which is the level `{h = c}` of the domain
`N = sliceDom (τ_w − η) b c`, a Cauchy surface of it (`isCauchySurfaceOn_sliceDom`). -/
theorem sliceAt_past_of_mem_axis {w : E0} (hw : w ∈ axis) :
    SliceAt causality w fun O z => causality.le O w z := by
  intro O hwO
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 O.isOpen w hwO
  have hw0 : rad w = 0 := rad_eq_zero.2 hw
  set ε := δ / 4 with hε
  have hε0 : 0 < ε := by positivity
  set c := w.1 + ε with hc
  set K : Set E0 := {z | w.1 ≤ fcoord z ∧ hcoord z = c} with hK
  have hKball : ∀ z ∈ K, z ∈ Metric.ball w δ := by
    rintro z ⟨hf, hh⟩
    have hr := rad_nonneg z
    have h1 := fcoord_eq_hcoord z
    rw [hh] at h1
    have h2 : z.1 = c - rad z := by
      have : hcoord z = z.1 + rad z := rfl
      linarith
    rw [Metric.mem_ball, dist_axis hw, max_lt_iff, abs_lt]
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  refine ⟨K, fun z hz => hδO (hKball z hz), fun z hz => ⟨?_, ?_⟩, fun V hV hKV => ?_⟩
  · rintro rfl
    have h := hz.2
    simp only [hcoord, hw0, add_zero, hc] at h
    linarith
  · exact cle_ball_of_le_axis hw (hKball z hz) ((le_axis_iff hw).2 hz.1) hδO
  · -- compactness: a thickening of `K` in `V`
    have hKc : IsCompact K := by
      refine Metric.isCompact_of_isClosed_isBounded
        ((isClosed_le continuous_const continuous_fcoord).inter
          (isClosed_eq continuous_hcoord continuous_const))
        (Metric.isBounded_ball.subset fun z hz => hKball z hz)
    obtain ⟨η', hη', hthick⟩ := hKc.exists_thickening_subset_open hV hKV
    set η := min ε η' with hη
    have hη0 : 0 < η := lt_min hε0 hη'
    have hηε : η ≤ ε := min_le_left _ _
    have hηη' : η ≤ η' := min_le_right _ _
    set a := w.1 - η with ha
    set b := w.1 + 2 * ε with hb
    have hcb : c < b := by rw [hc, hb]; linarith
    refine ⟨sliceDom a b c, {z | hcoord z = c} ∩ sliceDom a b c, ?_, ?_, inter_subset_right,
      ?_, isCauchySurfaceOn_sliceDom hcb⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [fcoord_of_axis hw, ha]; linarith
      · simp only [hcoord, hw0, add_zero, hb]; linarith
      · rw [hw0, hc, ha]; linarith
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := hz
      have hr := rad_nonneg z
      simp only [fcoord] at h1
      simp only [hcoord] at h2
      refine hδO ?_
      rw [Metric.mem_ball, dist_axis hw, max_lt_iff, abs_lt]
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      have : rad z < 2 * (c - a) / 3 := h3
      rw [hc, ha] at this
      linarith
    · rintro z ⟨hzc, hzN⟩
      have hzc' : hcoord z = c := hzc
      refine hthick (Metric.mem_thickening_iff.2 ?_)
      by_cases hfz : w.1 ≤ fcoord z
      · exact ⟨z, ⟨hfz, hzc'⟩, by rw [dist_self]; exact hη'⟩
      · push Not at hfz
        have hf1 : a < fcoord z := hzN.1
        have hfeq := fcoord_eq_hcoord z
        rw [hzc'] at hfeq
        set r := rad z with hr
        have hrpos : 2 * ε / 3 < r := by linarith
        have hrlt : r < 2 * (ε + η) / 3 := by linarith
        have hr0 : 0 < r := by linarith
        set r' := 2 * ε / 3 with hr'
        set z' : E0 := (c - r', ((r' / r : ℝ) : ℂ) * z.2) with hz'
        have hrz' : rad z' = r' := by
          simp only [rad, hz', norm_mul, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_pos (by positivity), show ‖z.2‖ = r from rfl]
          field_simp
        have hz1 : z.1 = c - r := by
          have : hcoord z = z.1 + rad z := rfl
          rw [hzc'] at this; linarith
        refine ⟨z', ⟨?_, ?_⟩, ?_⟩
        · show w.1 ≤ (c - r') - rad z' / 2
          rw [hrz', hc, hr']; linarith
        · show (c - r') + rad z' = c
          rw [hrz']; ring
        · rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm, max_lt_iff]
          have hnorm : ‖z.2 - ((r' / r : ℝ) : ℂ) * z.2‖ = r - r' := by
            rw [show z.2 - ((r' / r : ℝ) : ℂ) * z.2 = ((1 - r' / r : ℝ) : ℂ) * z.2 by push_cast; ring,
              norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have : r' / r ≤ 1 := (div_le_one hr0).2 (by linarith)
            rw [abs_of_nonneg (by linarith)]
            show (1 - r' / r) * r = r - r'
            field_simp
          refine ⟨?_, ?_⟩
          · simp only [hz']; rw [hz1, abs_lt]; constructor <;> linarith
          · simp only [hz']; rw [hnorm]; linarith

end AxisSlice

/-! ### Diamonds form a basis of the topology -/

section Diamonds

open TopologicalSpace

/-- A full diamond with vertices `δ`-close to `x` lies in the ball of radius `7δ` (`Le.dist_le`). -/
theorem diamond_subset_ball {x p q : E0} {δ : ℝ} (hp : dist p x < δ) (hq : dist q x < δ) :
    causality.diamond ⊤ p q ⊆ Metric.ball x (7 * δ) := by
  rintro w ⟨hwq, hpw⟩
  have h1 := (le_top_iff.1 (Causal.Precausality.mem_Jplus_singleton.1 hpw)).dist_le
  have h2 := (le_top_iff.1 (Causal.Precausality.mem_Jminus_singleton.1 hwq)).closed.1
  have hτp := abs_lt.1 ((abs_fst_sub_le_dist p x).trans_lt hp)
  have hτq := abs_lt.1 ((abs_fst_sub_le_dist q x).trans_lt hq)
  rw [Metric.mem_ball]
  calc dist w x ≤ dist w p + dist p x := dist_triangle _ _ _
    _ = dist p w + dist p x := by rw [dist_comm w p]
    _ < 7 * δ := by linarith [hτp.1, hτp.2, hτq.1, hτq.2]

/-- **Diamonds form a basis** (`rem:sing_tarentin` with the localisation the topology asks): for
every `x` and every neighbourhood `U` of `x` there are `p, q ∈ U` with
`x ∈ Int J(p, q) ⊆ J(p, q) ⊆ U`, BTZ points included (there `I⁻(x) = ∅`, so the basis uses the
interiors of the full diamonds `J⁺(p) ∩ J⁻(q)`, not chronological diamonds). -/
theorem diamonds_basis (x : E0) {U : Set E0} (hU : U ∈ 𝓝 x) :
    ∃ p ∈ U, ∃ q ∈ U, x ∈ causality.openDiamond ⊤ p q ∧ causality.diamond ⊤ p q ⊆ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨p, hp, q, hq, hx⟩ := tarentin x (Metric.ball x (δ / 7)) (Metric.ball_mem_nhds x (by positivity))
  have hsub : causality.diamond ⊤ p q ⊆ U := fun w hw => hball (by
    have := diamond_subset_ball hp hq hw
    rwa [show 7 * (δ / 7) = δ by ring] at this)
  exact ⟨p, hball (Metric.ball_subset_ball (by linarith) hp), q,
    hball (Metric.ball_subset_ball (by linarith) hq), hx, hsub⟩

/-- **The open diamonds form a neighbourhood basis at every point.** -/
theorem nhds_hasBasis_openDiamond (x : E0) :
    (𝓝 x).HasBasis (fun pq : E0 × E0 => x ∈ causality.openDiamond ⊤ pq.1 pq.2)
      fun pq => causality.openDiamond ⊤ pq.1 pq.2 := by
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨pq, hx, hsub⟩ => ?_⟩⟩
  · obtain ⟨p, -, q, -, hx, hsub⟩ := diamonds_basis x hU
    exact ⟨(p, q), hx, interior_subset.trans hsub⟩
  · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hx) hsub

/-- **The Alexandrov topology of `𝔼₀` is its topology** (`def:alexandrov_topology`). -/
theorem alexandrovTopology_eq :
    causality.alexandrovTopology = (inferInstance : TopologicalSpace E0) := by
  refine le_antisymm ?_ (le_generateFrom fun s ⟨p, q, hs⟩ => hs ▸ isOpen_interior)
  refine le_of_nhds_le_nhds fun x U hU => ?_
  obtain ⟨p, -, q, -, hx, hsub⟩ := diamonds_basis x hU
  exact @Filter.mem_of_superset _ _ _ _
    (@IsOpen.mem_nhds _ causality.alexandrovTopology _ _
      (TopologicalSpace.isOpen_generateFrom_of_mem ⟨p, q, rfl⟩) hx) (interior_subset.trans hsub)

end Diamonds

end E0

end Causal
