import GX.BTZ.LiftGH
import GX.BTZ.HeadlineBridge
import GX.BTZ.Spear

/-!
# `GX.BTZ.FutureRay` — the future half of the developed BTZ line (DEC-126)

Package WP-47e. `papers/gx` §4.6: the last step of the proof of
`prop:globally_hyperbolic_cauchy_complete_manifolds` (l.2348–2353, « Lemma 2.4 of
\cite{brunswic2021cauchy} implies that the singular locus contains full future BTZ rays ») and the
half-lines `Δₓ = D(S_x)` of `theo:globally_hyperbolic_cauchy_complete_cauchy_maximal`
(l.2363–2396, « `S_x` is a totally ordered relatively open future half line, so is its image »).
Rulings: DEC-126 (this package), DEC-125 (b) (`IsFullFutureBTZRay`), DEC-118 (a)/(c)
(`BTZTildeData.causality`, the chartwise `M̃`), DEC-119 (the bridge), DEC-106, DEC-33.
**No label is marked**: neither row is closed by this file alone (SCOPE (a)). **0 `sorry`,
standard axioms only.**

* `prop:globally_hyperbolic_cauchy_complete_manifolds` — the one open case of its DEC-118 (a)
  reading, the null part of `J⁺(D x) ⊆ D(J⁺(x))` at a BTZ point `x` of `M̃` ALONG the developed BTZ
  line: `GX.futureRay_null_supset` is the hypothesis `hnull` of `GX.btzTilde_supset_of_null`
  (`GX.BTZ.Uniformization`) verbatim, from full future BTZ rays (`hrays`) and the regular
  case (`hreg`, the first half of `GX.btzTilde_supset_of_reg`); `GX.futureRay_Jplus_supset` is
  the whole causal inclusion at BTZ points. Wired (four lines, checked in
  `campaign/WP-47e/Wiring.lean` against the built `Uniformization`, standard axioms), it closes
  the tagged `sorry` of `GX.btzTilde_null_supset`.
* `theo:globally_hyperbolic_cauchy_complete_cauchy_maximal` — the lifted ray and its image:
  `GX.futureRay_halfLine`: for a BTZ point `x` of the chartwise `M̃` there are a full future BTZ
  ray `γ` of `M` from `p(x)` and a future null `u ≠ 0` such that for every `λ ≥ 0` some
  `z ≥ x` over `γ(λ/2)` has `D z = D x + λ u` — `D` maps the lift of the ray ONTO the whole
  future half-line `D x + ℝ₊ u`; and every `m ≥ D x` off that half-line is reached from a regular
  `y ≥ x` with `D y ≤ m`.

**The proof** (DEC-126's route). (1) For each `T > 0`, ONE descending `𝔼₀`-chart along `γ([0, T])`
(`GX.futureRay_exists_chart`): a box of `𝔼₀` around the axis segment inside the domain of the
ray's morphism `ψ` (tube lemma, `GX.futureRay_exists_box`), `ψ⁻¹` on its image as an
`𝔼₀`-chart of `def:atlas` for the bridge structure (`GX.futureRay_isFlatCompat`,
`GX.futureRay_isAEMorphism`), descending because boxes have maximal lifts. (2) Its lift at `x`
(`GX.BTZTildeData.futureRay_lift`, through `exists_liftedChart_of_isChartwise` and
`LiftGH.exists_chart_of_descent`): `D (z s) = g · s u₀` on the lifted axis, `x ≤ z s` by one link
along the developed axis, the BTZ fibre of the lifted component is one point
(`GX.futureRay_eq_apex_of_orbitMk`: `Γ` fixes the axis), and off the line a chart step lands at a
regular point. (3) The chain: the charts for `T` and for `1` agree on the BTZ fibre of their
common component, so the two isometries agree on the developed axis
(`GX.futureRay_isom_axis`) — the parabolic stabiliser's freedom (a boost of the null direction,
`GX.IsAxisAff`) is pinned by the ray's affine parameter.

## Hypothesis checklist

| paper / dispatch | here |
|---|---|
| `M` an `𝔼₀`-manifold | ✓ `ChartedSpace E0Y M`, `HasGroupoid M e0Groupoid`, Hausdorff, connected, first countable (`maxBranched_basic`), bridge structure (DEC-119) |
| full future BTZ rays (B21 Lemma 2.3/2.4) | ✓ carried, `hrays` (DEC-125 (b)), as in `GX.btzTilde_null_supset` |
| `M̃` (DEC-106/118 (c)) | ✓ any chartwise datum `d.IsChartwise` |
| the regular case | carried as `hreg` (proved upstream, `GX.btzTilde_supset_of_reg`) |
| `M` GH, Cauchy-complete, Cauchy-maximal | not used |

## SCOPE (disclosed)

* (a) Neither label closes here: the prop's assembly (`GX.isBTZFutureComplete_of_regFuture`) and
  the headline's display live in `Uniformization` (outside this write set); this file supplies the
  missing step and the half-line. The headline's `Δᵢ ⊂ ∂Ω`, the image formula and
  `M ≅ ρ\D(M̃)` are not attempted.
* (b) `hreg` is a hypothesis, not a gap: `Uniformization` imports this file, not conversely.
-/

namespace GX

open Set Filter Topology Function
open scoped Real

set_option linter.unusedSectionVars false

/-! ### §1 The model: the fibre of `\widetilde{𝔼₀}` over an axis point is one point -/

/-- **Over an axis point of `𝔼₀` the cylinder has one point**: `Γ` fixes the axis
`{apex} × ℝ` pointwise. -/
theorem futureRay_eq_apex_of_orbitMk {y : DInfty × ℝ} {s : ℝ}
    (h : orbitMk (GammaA (2 * π)) y = orbitMk (GammaA (2 * π)) (DInfty.apex, s)) :
    y = (DInfty.apex, s) := by
  obtain ⟨k, hk⟩ := exists_smul_eq_of_orbitMk_eq h.symm
  rw [← hk, DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_apex]

/-- The axis of the model develops onto the null line `ℝ · u` (`u = nullToMink nullU`). -/
theorem futureRay_btzDevM_apex (s : ℝ) :
    btzDevM 0 btzV0 (DInfty.apex, s) = nullToMink (s • nullU) := by
  rw [btzDevM_apex, zero_add]

/-- The developed axis is affine (here linear) in its parameter. -/
theorem futureRay_nullToMink_affine (a s t : ℝ) :
    nullToMink (a • nullU) + t • (nullToMink (s • nullU) - nullToMink (a • nullU)) =
      nullToMink ((a + t * (s - a)) • nullU) := by
  rw [← map_sub, ← map_smul, ← map_add]
  congr 1
  rw [← sub_smul, smul_smul, ← add_smul]

/-- An isometry is affine along the developed axis. -/
theorem futureRay_isom_axis (g : Causal.Flat.isom 2) (a s : ℝ) :
    g • nullToMink (s • nullU) =
      g • nullToMink (a • nullU) + (s - a) •
        (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear (nullToMink nullU) := by
  have h := Causal.Flat.isom_sub (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2)
    (nullToMink (a • nullU)) (nullToMink (s • nullU))
  rw [Causal.Flat.isom_smul_def, Causal.Flat.isom_smul_def, ← sub_eq_iff_eq_add', h, ← map_sub,
    ← sub_smul, map_smul, map_smul]

/-! ### §2 The lifted ray in `M̃`, through one descending chart -/

section TildeRay

universe v

attribute [local instance] btzE0Structure

variable {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]

namespace BTZTildeData

variable {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
  {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}
  (d : BTZTildeData M y₀ Φ)

/-- **One chart step towards `m`, in a GIVEN chart** (the chart step of
`GX.BTZ.Uniformization`'s `BTZTildeData.exists_chart_step`, for a prescribed chart `κ` of
the developed atlas with `D = g · κ` on its source): for `D x ≤ m` there are `y` in the source of
`κ` and `t > 0` with `κ y = κ x + t (g⁻¹ m − κ x)`, `x ≤ y` in `M̃` and `D y ≤ m`. -/
theorem futureRay_chartStep {κ : OpenPartialHomeomorph d.Space BTZJ0}
    (hκ : κ ∈ btzTildeDevAtlas (N := d.Space) d.D) {g : Causal.Flat.isom 2}
    (hg : ∀ w ∈ κ.source, d.D w = g • (κ w).val) {x : d.Space} (hx : x ∈ κ.source)
    {m : Causal.Minkowski 2} (hm : (Causal.minkowski 2).le ⊤ (d.D x) m) :
    ∃ y : d.Space, ∃ t : ℝ, y ∈ κ.source ∧ 0 < t ∧
      (κ y).val = (κ x).val + t • (g⁻¹ • m - (κ x).val) ∧
      d.causality.le ⊤ x y ∧ (Causal.minkowski 2).le ⊤ (d.D y) m := by
  have hDx : d.D x = g • (κ x).val := hg x hx
  have h1 : (Causal.minkowski 2).le ⊤ (κ x).val (g⁻¹ • m) := by
    have := (Causal.Flat.isom_le_top_iff g⁻¹).2 hm
    rwa [hDx, inv_smul_smul] at this
  have hm' : g⁻¹ • m ∈ btzJplus (0 : ℝ × ℝ × ℝ) := by
    obtain ⟨p, hp, hpq⟩ := (κ x).mem
    exact ⟨p, hp, (Causal.minkowski 2).le_trans hpq h1⟩
  set q₁ : BTZJ0 := BTZJplus.mk (g⁻¹ • m) hm' with hq₁
  have hlink : btzJLe (κ x) q₁ := h1
  set c := btzJSeg hlink with hcdef
  have hcont := btzJ_continuousOn_seg hlink
  have hT : κ.target ∈ 𝓝 (c 0) := by
    rw [hcdef, btzJSeg_zero]; exact κ.open_target.mem_nhds (κ.map_source hx)
  have hev : c ⁻¹' κ.target ∈ 𝓝[Icc (0 : ℝ) 1] 0 := hcont 0 ⟨le_rfl, zero_le_one⟩ hT
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set t : ℝ := min (δ / 2) (1 / 2) with htdef
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsmall : ∀ s ∈ Icc (0 : ℝ) 1, c (s * t) ∈ κ.target := fun s hs => by
    have hst : s * t ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hs.1 ht0.le, by nlinarith [hs.1, hs.2, ht0, ht1]⟩
    refine hball ⟨?_, hst⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hst.1]
    nlinarith [hs.1, hs.2, ht0, htδ]
  set q₂ := c t with hq₂
  have hq₂T : q₂ ∈ κ.target := by simpa using hsmall 1 ⟨zero_le_one, le_rfl⟩
  have hlink2 : btzJLe (κ x) q₂ := by
    show (Causal.minkowski 2).le ⊤ (κ x).val (btzJSegPt (κ x) q₁ t)
    have := btzJ_le_segPt hlink ht0.le
    rwa [btzJSegPt_zero] at this
  have hval2 : q₂.val = (κ x).val + t • ((g⁻¹ • m) - (κ x).val) := by
    show btzJSegPt (κ x) q₁ t = _
    rw [btzJSegPt_eq_of_mem ⟨ht0.le, ht1.le⟩]; rfl
  have hseg2 : ∀ s ∈ Icc (0 : ℝ) 1, btzJSeg hlink2 s = c (s * t) := fun s hs => by
    have hst : s * t ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hs.1 ht0.le, by nlinarith [hs.1, hs.2, ht0, ht1]⟩
    apply BTZJplus.ext
    show btzJSegPt (κ x) q₂ s = btzJSegPt (κ x) q₁ (s * t)
    rw [btzJSegPt_eq_of_mem hs, btzJSegPt_eq_of_mem hst, hval2, add_sub_cancel_left, smul_smul]
    rfl
  have hmem2 : ∀ s ∈ Icc (0 : ℝ) 1,
      btzJSeg hlink2 s ∈ Causal.chartImage κ (⊤ ⊓ Causal.chartSource κ) := fun s hs => by
    rw [hseg2 s hs]
    have hT' := hsmall s hs
    exact ⟨κ.symm (c (s * t)), ⟨κ.map_target hT', trivial, κ.map_target hT'⟩, κ.right_inv hT'⟩
  set y := κ.symm q₂ with hydef
  have hy : y ∈ κ.source := κ.map_target hq₂T
  have hκy : κ y = q₂ := κ.right_inv hq₂T
  have hDy : d.D y = g • q₂.val := by rw [hg y hy, hκy]
  have hle : d.causality.le ⊤ x y := by
    refine btzTildeAtlasCausality_le_of_link (hA := d.isBTZTildeDev) hκ
      (btzTilde_link_le_iff.2 ⟨⟨trivial, hx⟩, ⟨trivial, hy⟩, ?_⟩)
    rw [hκy]
    exact ⟨0, 1, zero_le_one, btzJSeg hlink2, btzJ_curveOn_seg hlink2 hmem2, btzJSeg_zero hlink2,
      btzJSeg_one hlink2⟩
  have hq₂m : (Causal.minkowski 2).le ⊤ q₂.val (g⁻¹ • m) := by
    have := btzJ_le_segPt hlink ht1.le
    rw [btzJSegPt_one] at this
    exact this
  refine ⟨y, t, hy, ht0, by rw [hκy, hval2], hle, ?_⟩
  rw [hDy, ← smul_inv_smul g m]
  exact (Causal.Flat.isom_le_top_iff g).2 hq₂m

set_option maxHeartbeats 1600000 in
/-- **The lifted ray through one descending chart** (the core of DEC-126). Let `c : U ≅ V` be a
descending `𝔼₀`-chart of `M` and `r : [a, b] → U` a path of BTZ points read by `c` as the axis
segment `s ↦ [apex, s]` of `𝔼₀`, starting at the projection of `x ∈ M̃`. Then, for the chartwise
datum, there are an isometry `g` and a lift `z : [a, b] → M̃` of `r` from `x` (continuous for the
natural topology) with `x ≤ z s` and `D (z s) = g · s u` (`u = nullToMink nullU`): `D` maps the
lift onto a segment of the developed BTZ line. Moreover every point of the component `Û ∋ x` of
`p⁻¹(U)` over `r s` develops to `g · s u` (the BTZ fibre of `Û` is one point), and every `m ≥ D x`
off the developed line `g · ℝu` is reached from a REGULAR point `y ≥ x` with `D y ≤ m`. -/
theorem futureRay_lift (hd : d.IsChartwise) {p : M}
    (c : XAChart (Causal.Flat.isom 2) (Causal.Minkowski 2) btzFam btzFamS () p)
    (hc : IsDescendingChartMap (Causal.Flat.isom 2) (Causal.Minkowski 2) c.φ)
    {a b : ℝ} (hab : a ≤ b) (r : ℝ → M)
    (hr : ∀ s ∈ Icc a b, r s ∈ (c.U : Set M) ∧
      chartExt c.φ (r s) = orbitMk (GammaA (2 * π)) (DInfty.apex, s))
    (hra : r a = p) (x : d.Space) (hx : (d.toNat x).base = p) :
    ∃ g : Causal.Flat.isom 2, ∃ z : ℝ → d.Space,
      ContinuousOn (fun s => d.toNat (z s)) (Icc a b) ∧ z a = x ∧
      (∀ s ∈ Icc a b, (d.toNat (z s)).base = r s ∧ d.causality.le ⊤ x (z s) ∧
        d.D (z s) = g • nullToMink (s • nullU)) ∧
      (∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) (d.toNat x),
        ∀ s ∈ Icc a b, w.base = r s → d.D w = g • nullToMink (s • nullU)) ∧
      ∀ m, (Causal.minkowski 2).le ⊤ (d.D x) m →
        (∃ s : ℝ, m = g • nullToMink (s • nullU)) ∨
        ∃ y : d.Space, (d.toNat y).base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M ∧
          d.causality.le ⊤ x y ∧ (Causal.minkowski 2).le ⊤ (d.D y) m := by
  classical
  have hra' : chartExt c.φ p = orbitMk (GammaA (2 * π)) (DInfty.apex, a) := by
    have h := (hr a ⟨le_rfl, hab⟩).2; rwa [hra] at h
  have hxU : (d.toNat x).base ∈ (c.U : Set M) := by
    have h := (hr a ⟨le_rfl, hab⟩).1
    rw [hra] at h
    exact (congrArg (· ∈ (c.U : Set M)) hx).mpr h
  obtain ⟨f, Ψ, hΨ, hΨf, hVo, hVoB, hUo, hbij, hnat, hT'n, g, hg⟩ :=
    d.exists_liftedChart_of_isChartwise hd c hc (d.toNat x) hxU
  set Vh := connectedComponentIn ((SpreadEnd.base : MaxBranchedCover
    (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN → BTZE0) ⁻¹' (c.V : Set BTZE0)) f
    with hVhdef
  set Uh := connectedComponentIn ((SpreadEnd.base : MaxBranchedCover
    (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ → M) ⁻¹' (c.U : Set M)) (d.toNat x)
    with hUhdef
  have hfV : f ∈ Vh := mem_connectedComponentIn hΨ.base_mem
  -- `chartExt c.φ` is injective on `U`
  have hinjU : ∀ m ∈ (c.U : Set M), ∀ m' ∈ (c.U : Set M), chartExt c.φ m = chartExt c.φ m' →
      m = m' := by
    intro m hm m' hm' h
    rw [chartExt_apply c.φ hm, chartExt_apply c.φ hm'] at h
    exact congrArg Subtype.val (c.φ.injective (Subtype.ext h))
  -- the model point of a point of `V̂` over an axis point
  have hΦapex : ∀ w : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN,
      ∀ s, w.base = orbitMk (GammaA (2 * π)) (DInfty.apex, s) → Φ w = (DInfty.apex, s) := by
    intro w s h
    apply futureRay_eq_apex_of_orbitMk
    rw [d.isPresentation]; exact h
  -- the base point
  have hfb : f.base = orbitMk (GammaA (2 * π)) (DInfty.apex, a) := by
    rw [← hΨ.base f hfV, hΨf, hx]; exact hra'
  have hΦf : Φ f = (DInfty.apex, a) := hΦapex f a hfb
  -- the model ray
  set σ : ℝ → MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN :=
    fun s => Φ.symm (DInfty.apex, s) with hσdef
  have hσc : Continuous σ := Φ.symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hσb : ∀ s, (σ s).base = orbitMk (GammaA (2 * π)) (DInfty.apex, s) := fun s => by
    rw [← d.isPresentation, hσdef, Φ.apply_symm_apply]
  have hσa : σ a = f := by
    show Φ.symm (DInfty.apex, a) = f
    rw [← hΦf, Φ.symm_apply_apply]
  have hσV : ∀ s ∈ Icc a b, σ s ∈ Vh := by
    have hsub : σ '' Icc a b ⊆ SpreadEnd.base ⁻¹' (c.V : Set BTZE0) := by
      rintro _ ⟨s, hs, rfl⟩
      rw [mem_preimage, hσb, ← (hr s hs).2]
      exact mapsTo_chartExt c.φ (hr s hs).1
    have h := (isPreconnected_Icc.image σ hσc.continuousOn).subset_connectedComponentIn
      ⟨a, ⟨le_rfl, hab⟩, rfl⟩ hsub
    rw [hσa] at h
    exact fun s hs => h ⟨s, hs, rfl⟩
  have hΦσ : ∀ s, Φ (σ s) = (DInfty.apex, s) := fun s => Φ.apply_symm_apply _
  -- the lift
  set z : ℝ → d.Space := fun s => d.fromNat (Ψ (σ s)) with hzdef
  have hza : z a = x := by
    show d.fromNat (Ψ (σ a)) = x
    rw [hσa, hΨf]; rfl
  have hzb : ∀ s ∈ Icc a b, (d.toNat (z s)).base = r s := fun s hs => by
    have h1 := hΨ.base (σ s) (hσV s hs)
    rw [hσb, ← (hr s hs).2] at h1
    exact hinjU _ (hΨ.mem (σ s) (hσV s hs)) _ (hr s hs).1 h1
  have hzD : ∀ s ∈ Icc a b, d.D (z s) = g • nullToMink (s • nullU) := fun s hs => by
    show d.D (Ψ (σ s)) = _
    rw [hg (σ s) (hσV s hs), hΦσ, futureRay_btzDevM_apex]
  -- the chart of `Û`
  obtain ⟨κ, hκA, hκs, hκΨ, hκt⟩ := LiftGH.exists_chart_of_descent (E := d.Space) (D := d.D)
    Φ.toEquiv hVoB (TopologicalSpace.le_def.1 d.le_natural _ hUo) hbij hT'n hg ⟨f, hfV⟩
  set js : BTZJ0 → DInfty × ℝ := ⇑(btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).symm
    with hjsdef
  have hjsj : ∀ y, js (btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos y) = y := fun y =>
    (btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).symm_apply_apply y
  have hxUh : d.toNat x ∈ Uh := mem_connectedComponentIn hxU
  have hxκ : x ∈ κ.source := by
    rw [hκs]; exact hxUh
  have hκx : κ x = btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos (DInfty.apex, a) := by
    have h := hκΨ f hfV
    simp only [Homeomorph.coe_toEquiv] at h
    rw [hΨf, hΦf] at h; exact h
  have hzκ : ∀ s ∈ Icc a b, z s ∈ κ.source := fun s hs => by
    rw [hκs]; exact hbij.mapsTo (hσV s hs)
  have hκz : ∀ s ∈ Icc a b, κ (z s) = btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos (DInfty.apex, s) :=
    fun s hs => by
      have h := hκΨ (σ s) (hσV s hs)
      simp only [Homeomorph.coe_toEquiv] at h
      rw [hΦσ] at h; exact h
  -- `x ≤ z s`, by one link along the developed axis
  have hle : ∀ s ∈ Icc a b, d.causality.le ⊤ x (z s) := by
    intro s hs
    have hlink : btzJLe (κ x) (κ (z s)) := by
      show (Causal.minkowski 2).le ⊤ (κ x).val (κ (z s)).val
      rw [hκx, hκz s hs, btzJDev_val, btzJDev_val, btzDevM_le_iff]
      simp only [BtzDevLe, DInfty.apex_r, zero_mul, zero_add, sub_self, le_refl, mul_zero,
        true_and]
      simpa using hs.1
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
        btzJSeg hlink t ∈ Causal.chartImage κ (⊤ ⊓ Causal.chartSource κ) := by
      intro t ht
      have heq : btzJSeg hlink t =
          btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos (DInfty.apex, a + t * (s - a)) := by
        apply BTZJplus.ext
        rw [btzJSeg_val, btzJSegPt_eq_of_mem ht, hκx, hκz s hs, btzJDev_val, btzJDev_val,
          btzJDev_val, futureRay_btzDevM_apex, futureRay_btzDevM_apex, futureRay_btzDevM_apex,
          futureRay_nullToMink_affine]
      have hst : a + t * (s - a) ∈ Icc a b :=
        ⟨by nlinarith [ht.1, hs.1], by nlinarith [ht.2, hs.1, hs.2, ht.1]⟩
      have hmem' : btzJSeg hlink t ∈ κ.target := by
        refine hκt _ ?_
        show Φ.symm (js (btzJSeg hlink t)) ∈ Vh
        rw [heq, hjsj]; exact hσV _ hst
      exact ⟨κ.symm (btzJSeg hlink t), ⟨κ.map_target hmem', trivial, κ.map_target hmem'⟩,
        κ.right_inv hmem'⟩
    exact btzTildeAtlasCausality_le_of_link (hA := d.isBTZTildeDev) hκA
      (btzTilde_link_le_iff.2 ⟨⟨trivial, hxκ⟩, ⟨trivial, hzκ s hs⟩,
        0, 1, zero_le_one, btzJSeg hlink, btzJ_curveOn_seg hlink hseg, btzJSeg_zero hlink,
        btzJSeg_one hlink⟩)
  refine ⟨g, z, ?_, hza, fun s hs => ⟨hzb s hs, hle s hs, hzD s hs⟩, ?_, ?_⟩
  · -- continuity of the lift (natural topology)
    exact hΨ.contOn.comp hσc.continuousOn fun s hs => hσV s hs
  · -- the BTZ fibre of `Û` over the ray
    intro w hw s hs hwb
    obtain ⟨w', hw', rfl⟩ := hbij.surjOn hw
    have h1 := hΨ.base w' hw'
    rw [hwb, (hr s hs).2] at h1
    rw [hg w' hw', hΦapex w' s h1.symm, futureRay_btzDevM_apex]
  · -- off the developed line: a regular chart step
    intro m hm
    by_cases hline : ∃ s : ℝ, m = g • nullToMink (s • nullU)
    · exact Or.inl hline
    right
    have hDκ : ∀ w ∈ κ.source, d.D w = g • (κ w).val := by
      intro w hw
      rw [hκs] at hw
      obtain ⟨w', hw', rfl⟩ := hbij.surjOn hw
      rw [hg w' hw', hκΨ w' hw', btzJDev_val]; rfl
    obtain ⟨y, t, hy, ht, hκy, hxy, hym⟩ := d.futureRay_chartStep hκA hDκ hxκ hm
    refine ⟨y, ?_, hxy, hym⟩
    have hyU : d.toNat y ∈ Uh := by rw [← hκs]; exact hy
    obtain ⟨w', hw', hΨw'⟩ := hbij.surjOn hyU
    have hκw : κ y = btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos (Φ w') := by
      have h := hκΨ w' hw'
      simp only [Homeomorph.coe_toEquiv] at h
      rw [hΨw'] at h; exact h
    -- the model point is off the axis
    have hr0 : 0 < (Φ w').1.r := by
      rcases (Φ w').1.pos_or_eq_apex with h | h
      · exact h
      exfalso
      apply hline
      have hval : (κ y).val = nullToMink ((Φ w').2 • nullU) := by
        rw [hκw, btzJDev_val]
        have : Φ w' = (DInfty.apex, (Φ w').2) := Prod.ext h rfl
        rw [this, futureRay_btzDevM_apex]
      have hκxv : (κ x).val = nullToMink (a • nullU) := by
        rw [hκx, btzJDev_val, futureRay_btzDevM_apex]
      refine ⟨a + t⁻¹ * ((Φ w').2 - a), ?_⟩
      have hm' : g⁻¹ • m = nullToMink (a • nullU) +
          t⁻¹ • (nullToMink ((Φ w').2 • nullU) - nullToMink (a • nullU)) := by
        rw [← hval, hκy, hκxv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul,
          add_sub_cancel]
      rw [← futureRay_nullToMink_affine, ← hm', smul_inv_smul]
    -- hence the base point is regular
    have hw'R : w'.base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := by
      have hsing := btz_sing btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0
      by_contra hns
      have hS : w'.base ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := hns
      obtain ⟨y', hy', he⟩ := (Set.ext_iff.1 hsing w'.base).1 hS
      rw [← d.isPresentation w'] at he
      obtain ⟨k, hk⟩ := exists_smul_eq_of_orbitMk_eq he
      have := gammaA_smul_r k y'
      rw [hk, hy', DInfty.apex_r] at this
      exact hr0.ne' this
    have h1 := hΨ.base w' hw'
    rw [hΨw'] at h1
    have h2 := (chartExt_mem_reg_iff c.isAEMorphism (by rw [← hΨw']; exact hΨ.mem w' hw')).1
      (h1 ▸ hw'R)
    exact h2

end BTZTildeData

end TildeRay

/-! ### §3 The `𝔼₀` side: a descending chart along a segment of a full future BTZ ray -/

section E0Charts

attribute [local instance] btzE0Structure

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **An injective `𝔼₀`-morphism, inverted, is flat-compatible** with the bridge structure
(DEC-119): its inverse sees the regular locus, and followed by a regular chart of the model it is a
chart of the maximal a.e. atlas (the change of chart to a flat chart is, near every regular point,
an element of `Isom(𝐌³)`: the morphism is locally an element of `e0Groupoid`). -/
theorem futureRay_isFlatCompat (κ : OpenPartialHomeomorph E0Y M) {W : Set E0Y} (hW : IsOpen W)
    (hψ : E0Spear.IsE0Mor (⇑κ) W) (hsrc : κ.source ⊆ W) : E0Bridge.IsFlatCompat κ.symm := by
  have hloc : ∀ y ∈ κ.source, ∃ e ∈ e0Groupoid, y ∈ e.source ∧
      ∀ z ∈ W ∩ e.source, chartAt E0Y (κ y) (κ z) = e z := by
    intro y hy
    have h := (hψ y (hsrc hy)).2
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      preimage_id_eq] at h
    obtain ⟨e, he, hfe, hye⟩ := h (hsrc hy)
    exact ⟨e, he, hye, fun z hz => hfe hz⟩
  refine ⟨fun m hm => ?_, fun c hc => ?_⟩
  · have hmt : m ∈ κ.target := hm
    have hy : κ.symm m ∈ κ.source := κ.map_target hmt
    have hκy : κ (κ.symm m) = m := κ.right_inv hmt
    obtain ⟨e, he, hye, heq⟩ := hloc _ hy
    have hcm : chartAt E0Y m m = e (κ.symm m) := by
      have := heq (κ.symm m) ⟨hsrc hy, hye⟩
      rwa [hκy] at this
    refine (mem_e0Reg_iff_of_mem he hye).trans ?_
    rw [← hcm]
    exact (E0LM.mem_e0RegM_iff (mem_chart_source E0Y m)).symm
  · letI := E0Bridge.e0SingularGXStructure M
    have hBM := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M
    refine hBM.mem_of_compatible fun a ha m hm => ?_
    obtain ⟨⟨hmt, hmc⟩, hma⟩ := hm
    have hmt' : m ∈ κ.target := hmt
    have hy : κ.symm m ∈ κ.source := κ.map_target hmt'
    have hκy : κ (κ.symm m) = m := κ.right_inv hmt'
    obtain ⟨e, he, hye, heq⟩ := hloc _ hy
    have hyR : κ.symm m ∈ e0Reg := E0LM.source_subset_e0Reg hc hmc
    have heyR : e (κ.symm m) ∈ e0Reg := mapsTo_e0Reg_of_mem he hye hyR
    obtain ⟨c', hc', hc'y⟩ := mem_support.1 heyR
    obtain ⟨-, hch⟩ := ((mem_e0Groupoid_iff.1 he).1 _ hye).2 hyR
    obtain ⟨g₂, hg₂⟩ := hch c hc c' hc' hmc hc'y
    have hcm : chartAt E0Y m m = e (κ.symm m) := by
      have := heq (κ.symm m) ⟨hsrc hy, hye⟩
      rwa [hκy] at this
    have hfl : (chartAt E0Y m).trans c' ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M :=
      E0Bridge.flatCharts_subset_aeAtlas (E0Bridge.trans_mem_flatCharts m hc')
    have hmfl : m ∈ ((chartAt E0Y m).trans c').source :=
      ⟨mem_chart_source E0Y m, by show chartAt E0Y m m ∈ c'.source; rw [hcm]; exact hc'y⟩
    obtain ⟨g₁, hg₁⟩ := hBM.1.1.eventually_smul_eq hfl ha hmfl hma
    refine ⟨g₁ * g₂, ?_⟩
    have hcont : ContinuousAt κ.symm m := κ.continuousAt_symm hmt'
    have hWe : ∀ᶠ q in 𝓝 m, κ.symm q ∈ W ∩ e.source :=
      hcont.eventually ((hW.inter e.open_source).mem_nhds ⟨hsrc hy, hye⟩)
    filter_upwards [hg₁, hcont.eventually hg₂, hWe, κ.open_target.mem_nhds hmt'] with q h1 h2 h3 h4
    have h5 : chartAt E0Y m q = e (κ.symm q) := by
      have := heq (κ.symm q) h3
      rwa [κ.right_inv h4, hκy] at this
    rw [h1, mul_smul]
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply]
    rw [h5, h2]

/-- The domain of the `𝔼₀`-chart of a flat-compatible chart `κ`, over an open `V ⊆ 𝔼₀` whose
image lies in the target of `κ`. -/
def futureRayU (κ : OpenPartialHomeomorph M E0Y) (V : TopologicalSpace.Opens BTZE0) :
    TopologicalSpace.Opens M :=
  ⟨κ.source ∩ κ ⁻¹' (Sum.inr '' (V : Set BTZE0)),
    κ.isOpen_inter_preimage (isOpenMap_inr _ V.isOpen)⟩

theorem futureRay_exists_inr {κ : OpenPartialHomeomorph M E0Y} {V : TopologicalSpace.Opens BTZE0}
    {u : M} (hu : u ∈ futureRayU κ V) : ∃ v ∈ (V : Set BTZE0), κ u = Sum.inr v := by
  obtain ⟨v, hv, he⟩ := hu.2
  exact ⟨v, hv, he.symm⟩

/-- The `𝔼₀`-chart of a flat-compatible `κ` over `V`, as a homeomorphism (`κ` followed by
`inr⁻¹`; `GX.E0Bridge.xaHomeo` for an arbitrary chart). -/
noncomputable def futureRayHomeo (κ : OpenPartialHomeomorph M E0Y) (V : TopologicalSpace.Opens BTZE0)
    (hV : ∀ v ∈ (V : Set BTZE0), (Sum.inr v : E0Y) ∈ κ.target) : futureRayU κ V ≃ₜ V where
  toFun u := ⟨e0Inr.symm (κ u), by
    obtain ⟨v, hv, he⟩ := futureRay_exists_inr u.2
    rw [he, e0Inr_symm_inr]; exact hv⟩
  invFun v := ⟨κ.symm (Sum.inr v), by
    have ht : Sum.inr (v : BTZE0) ∈ κ.target := hV v v.2
    exact ⟨κ.map_target ht, ⟨v, v.2, (κ.right_inv ht).symm⟩⟩⟩
  left_inv u := by
    obtain ⟨v, -, he⟩ := futureRay_exists_inr u.2
    apply Subtype.ext
    show κ.symm (Sum.inr (e0Inr.symm (κ u))) = u
    rw [he, e0Inr_symm_inr, ← he, κ.left_inv u.2.1]
  right_inv v := by
    have ht : Sum.inr (v : BTZE0) ∈ κ.target := hV v v.2
    apply Subtype.ext
    show e0Inr.symm (κ (κ.symm (Sum.inr v))) = v
    rw [κ.right_inv ht, e0Inr_symm_inr]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine e0Inr.continuousOn_symm.comp_continuous
      (κ.continuousOn.comp_continuous continuous_subtype_val fun u => u.2.1) fun u => ?_
    obtain ⟨v, -, he⟩ := futureRay_exists_inr u.2
    rw [e0Inr_target, he]; exact ⟨v, rfl⟩
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact κ.continuousOn_symm.comp_continuous (continuous_inr.comp continuous_subtype_val)
      fun v => hV v v.2

theorem futureRayHomeo_apply (κ : OpenPartialHomeomorph M E0Y) (V : TopologicalSpace.Opens BTZE0)
    (hV : ∀ v ∈ (V : Set BTZE0), (Sum.inr v : E0Y) ∈ κ.target) (u : futureRayU κ V) :
    ((futureRayHomeo κ V hV u : BTZE0)) = e0Inr.symm (κ u) := rfl

/-- **The `𝔼₀`-chart of a flat-compatible chart is an a.e. `(Isom 𝐌³, 𝐌³)`-morphism**
(`GX.E0Bridge.isAEMorphism_xaHomeo` for an arbitrary flat-compatible chart). -/
theorem futureRay_isAEMorphism {κ : OpenPartialHomeomorph M E0Y} (hκ : E0Bridge.IsFlatCompat κ)
    (V : TopologicalSpace.Opens BTZE0) (hV : ∀ v ∈ (V : Set BTZE0), (Sum.inr v : E0Y) ∈ κ.target) :
    letI := E0Bridge.e0SingularGXStructure M
    IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2)
      (futureRayHomeo κ V hV : futureRayU κ V → _) := by
  letI := E0Bridge.e0SingularGXStructure M
  set U := futureRayU κ V
  set f : U → BTZE0 := Subtype.val ∘ (futureRayHomeo κ V hV : U → V)
  refine isAEMorphism_of_val_comp V ?_
  have hBN := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
  have hBU := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) U
  have hBM := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M
  have hfc : Continuous f := continuous_subtype_val.comp (futureRayHomeo κ V hV).continuous
  have hval := isAEMorphism_opensSingular_val (G := Causal.Flat.isom 2)
    (X := Causal.Minkowski 2) U
  have hvaleq := IsAEMorphismOf.regLocusOf_eq hBU.1 hBM.1 hval
  have hvalreg := isRegularOn_regLocusOf (G := Causal.Flat.isom 2)
    (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) U)
    (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) (Subtype.val : U → M)
  have hRU : ∀ u : U, u ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) U →
      (u : M) ∈ (E0LM.e0RegM M : Set M) := fun u hu => by
    rw [reg_opensSingular, mem_preimage, E0Bridge.reg_e0SingularGXStructure] at hu
    exact hu
  have hmaps : ∀ u : U, u ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) U →
      f u ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 := fun u hu => by
    have h1 := (hκ.1 u u.2.1).2 (hRU u hu)
    obtain ⟨v, -, he⟩ := futureRay_exists_inr u.2
    have hfu : f u = v := by
      show e0Inr.symm (κ u) = v
      rw [he, e0Inr_symm_inr]
    rw [hfu]
    rw [he] at h1
    exact inr_mem_e0Reg_iff.1 h1
  refine (isAEMorphismOf_iff hBN.1).2 ⟨hfc, _, isPortly_reg _ _ _, IsRegularOn.of_exists hBU.1.1
    hBN.1.1 (isOpen_reg _ _ _) subset_rfl (fun u hu => hmaps u hu) hfc.continuousOn
    fun u hu => ?_⟩
  obtain ⟨e, he, hue⟩ := mem_support.1 hu
  obtain ⟨c, hc, hfuc⟩ := mem_support.1 (hmaps u hu)
  set a := κ.trans (e0Inr.symm.trans c)
  have ha : a ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M :=
    hκ.2 _ (e0InrChart_mem_e0Atlas hc)
  obtain ⟨v, -, hev⟩ := futureRay_exists_inr u.2
  have hfu : f u = v := by
    show e0Inr.symm (κ u) = v
    rw [hev, e0Inr_symm_inr]
  have hua : (u : M) ∈ a.source := by
    refine ⟨u.2.1, ?_⟩
    show κ u ∈ (e0Inr.symm.trans c).source
    rw [hev]; exact mem_e0InrChart_source.2 ⟨v, hfu ▸ hfuc, rfl⟩
  have huR : u ∈ regLocusOf (Causal.Flat.isom 2)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) U)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) Subtype.val := by
    rw [hvaleq]; exact ⟨hu, mem_support.2 ⟨a, ha, hua⟩⟩
  obtain ⟨g, hg⟩ := hvalreg.exists_smul_eq u huR e he a ha hue hua
  exact ⟨e, he, c, hc, hue, hfuc, g, hg⟩

/-- The axis point `[apex, s]` of `𝔼₀`, in `Y`, is the ray point `yAxis v (s/2 − v)`. -/
theorem futureRay_yAxis_eq (v s : ℝ) :
    E0Spear.yAxis v (s / 2 - v) = Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s)) := by
  show E0.paperInY _ = _
  rw [E0.paperInY_apply]
  congr 1
  rw [E0.toPaper.symm_apply_eq]
  have h := E0.toPaper_apex (s / 2)
  rw [show 2 * (s / 2) = s by ring] at h
  rw [h]
  exact Prod.ext (by ring) rfl

/-- The vertex of a ray is the axis point `[apex, 2v]`. -/
theorem futureRay_yVertex_eq (v : ℝ) :
    E0Spear.yVertex v = Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, 2 * v)) := by
  rw [← E0Spear.yAxis_zero, show (0 : ℝ) = (2 * v) / 2 - v by ring, futureRay_yAxis_eq]

/-- **A box around a segment of the ray inside the domain of its morphism** (tube lemma): for
`T > 0`, a box `π({r < η} × ]2v − η, 2v + 2T + η[)` of `𝔼₀` lies in `W` and contains the axis
segment `[apex, s]`, `s ∈ [2v, 2v + 2T]`. -/
theorem futureRay_exists_box {v T : ℝ} (hT : 0 < T) {W : Set E0Y} (hW : IsOpen W)
    (hray : ∀ t, 0 ≤ t → E0Spear.yAxis v t ∈ W) :
    ∃ η > 0, (∀ b ∈ (btzBox η (2 * v + T) (T + η) : Set BTZE0), (Sum.inr b : E0Y) ∈ W) ∧
      ∀ s ∈ Icc (2 * v) (2 * v + 2 * T),
        orbitMk (GammaA (2 * π)) (DInfty.apex, s) ∈ (btzBox η (2 * v + T) (T + η) : Set BTZE0) := by
  have haxis : ∀ s, 2 * v ≤ s →
      (Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s)) : E0Y) ∈ W := by
    intro s hs
    have h := hray (s / 2 - v) (by linarith)
    rwa [futureRay_yAxis_eq] at h
  set O : Set (DInfty × ℝ) := {y | (Sum.inr (orbitMk (GammaA (2 * π)) y) : E0Y) ∈ W} with hOdef
  have hO : IsOpen O := hW.preimage (continuous_inr.comp continuous_quot_mk)
  have hsub : ({DInfty.apex} : Set DInfty) ×ˢ Icc (2 * v) (2 * v + 2 * T) ⊆ O := by
    rintro ⟨p, s⟩ ⟨hp, hs⟩
    simp only [mem_singleton_iff] at hp
    subst hp
    exact haxis s hs.1
  obtain ⟨u, w, hu, hw, hau, hIw, huw⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hO hsub
  obtain ⟨ε, hε, hεu⟩ := DInfty.hasBasis_nhds_apex.mem_iff.1 (hu.mem_nhds (hau rfl))
  obtain ⟨δ, hδ, hδw⟩ := isCompact_Icc.exists_thickening_subset_open hw hIw
  have hη : 0 < min ε δ := lt_min hε hδ
  refine ⟨min ε δ, hη, fun b hb => ?_, fun s hs => ?_⟩
  · obtain ⟨y, rfl⟩ := Quotient.mk''_surjective
      (s₁ := MulAction.orbitRel (GammaA (2 * π)) (DInfty × ℝ)) b
    have hy0 : y ∈ orbitMk (GammaA (2 * π)) ⁻¹'
        (btzBox (min ε δ) (2 * v + T) (T + min ε δ) : Set BTZE0) := hb
    have hy : y ∈ {p : DInfty | p.r < min ε δ} ×ˢ Metric.ball (2 * v + T) (T + min ε δ) := by
      rw [← cylBasic_preimage btz_two_pi_ne_zero (min ε δ)
        (Metric.ball (2 * v + T) (T + min ε δ))]
      exact hy0
    obtain ⟨hy1, hy2⟩ := hy
    have h1 : y.1 ∈ u := hεu (show y.1.r < ε from lt_of_lt_of_le hy1 (min_le_left _ _))
    have hmδ : min ε δ ≤ δ := min_le_right _ _
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy2
    have h2 : y.2 ∈ w := by
      apply hδw
      rw [Metric.mem_thickening_iff]
      by_cases hlo : y.2 < 2 * v
      · refine ⟨2 * v, ⟨le_rfl, by linarith⟩, ?_⟩
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      by_cases hhi : y.2 ≤ 2 * v + 2 * T
      · exact ⟨y.2, ⟨not_lt.1 hlo, hhi⟩, by simpa using hδ⟩
      · refine ⟨2 * v + 2 * T, ⟨by linarith, le_rfl⟩, ?_⟩
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    exact huw ⟨h1, h2⟩
  · have h : ((DInfty.apex, s) : DInfty × ℝ) ∈
        {p : DInfty | p.r < min ε δ} ×ˢ Metric.ball (2 * v + T) (T + min ε δ) := by
      refine ⟨by simpa using hη, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    rw [← cylBasic_preimage btz_two_pi_ne_zero (min ε δ)
      (Metric.ball (2 * v + T) (T + min ε δ))] at h
    exact h

/-- **A descending `𝔼₀`-chart along a segment of a full future BTZ ray** (the chart of the
chain): for the injective `𝔼₀`-morphism `ψ` of a full future BTZ ray of vertex `(v, 0)` and
`T > 0`, an `𝔼₀`-chart of `def:atlas` (bridge structure) centred at `ψ(v, 0)`, descending from the
maximal covering of its model (its image is a box, `hasMaximalLifts_btzBox`), which reads the ray
points `ψ [apex, s]`, `s ∈ [2v, 2v + 2T]`, as the axis points `[apex, s]`. -/
theorem futureRay_exists_chart [T2Space M] [ConnectedSpace M] [FirstCountableTopology M]
    {v : ℝ} {W : Set E0Y} {ψ : E0Y → M} (hW : IsOpen W)
    (hray : ∀ t, 0 ≤ t → E0Spear.yAxis v t ∈ W) (hψ : E0Spear.IsE0Mor ψ W) (hinj : InjOn ψ W)
    {T : ℝ} (hT : 0 < T) :
    letI := E0Bridge.e0SingularGXStructure M
    haveI := ChartedSpace.locPathConnectedSpace E0Y M
    ∃ c : XAChart (Causal.Flat.isom 2) (Causal.Minkowski 2) btzFam btzFamS ()
        (ψ (E0Spear.yVertex v)),
      IsDescendingChartMap (Causal.Flat.isom 2) (Causal.Minkowski 2) c.φ ∧
      ∀ s ∈ Icc (2 * v) (2 * v + 2 * T),
        ψ (Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s))) ∈ (c.U : Set M) ∧
        chartExt c.φ (ψ (Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s)))) =
          orbitMk (GammaA (2 * π)) (DInfty.apex, s) := by
  letI := E0Bridge.e0SingularGXStructure M
  haveI := ChartedSpace.locPathConnectedSpace E0Y M
  obtain ⟨η, hη, hbox, haxis⟩ := futureRay_exists_box hT hW hray
  set B := btzBox η (2 * v + T) (T + η) with hBdef
  set B' : Set E0Y := Sum.inr '' (B : Set BTZE0) with hB'def
  have hB'o : IsOpen B' := isOpenMap_inr _ B.isOpen
  have hB'W : B' ⊆ W := by rintro _ ⟨b, hb, rfl⟩; exact hbox b hb
  haveI : Nonempty E0Y := ⟨Sum.inl 0⟩
  have hE := E0Spear.isEMorphismOn_of_isE0Mor (W := ⟨W, hW⟩) hψ
  have hψc : ContinuousOn ψ W := fun y hy => (hψ y hy).continuousWithinAt
  set e := (hinj.mono hB'W).toPartialEquiv ψ B' with hedef
  have hopen : IsOpenMap (e.source.restrict e) := by
    intro O hO
    have hO' : IsOpen (Subtype.val '' O : Set E0Y) := hB'o.isOpenMap_subtype_val O hO
    have himg : (e.source.restrict e) '' O = ψ '' (Subtype.val '' O) := by
      rw [Set.image_image]; rfl
    rw [himg]
    exact hE.isOpen_image ⟨_, hO'⟩ (by rintro _ ⟨z, -, rfl⟩; exact hB'W z.2)
  set κ := OpenPartialHomeomorph.ofContinuousOpenRestrict e (hψc.mono hB'W) hopen hB'o
    with hκdef
  have hκs : κ.source = B' := rfl
  have hκf : ∀ y, κ y = ψ y := fun _ => rfl
  have hκmor : E0Spear.IsE0Mor (⇑κ) W := hψ
  have hfc := futureRay_isFlatCompat κ hW hκmor (by rw [hκs]; exact hB'W)
  have hV : ∀ b ∈ (B : Set BTZE0), (Sum.inr b : E0Y) ∈ κ.symm.target := fun b hb => ⟨b, hb, rfl⟩
  have hmem2v : 2 * v ∈ Icc (2 * v) (2 * v + 2 * T) := ⟨le_rfl, by linarith⟩
  have hU : ∀ s ∈ Icc (2 * v) (2 * v + 2 * T),
      ψ (Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s))) ∈ futureRayU κ.symm B ∧
      κ.symm (ψ (Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s)))) =
        Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s)) := by
    intro s hs
    have hsB' : (Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s)) : E0Y) ∈ B' :=
      ⟨_, haxis s hs, rfl⟩
    have hl : κ.symm (ψ (Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s)))) =
        Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s)) := by
      rw [← hκf]; exact κ.left_inv hsB'
    refine ⟨⟨⟨_, hsB', rfl⟩, ?_⟩, hl⟩
    show κ.symm (ψ _) ∈ Sum.inr '' (B : Set BTZE0)
    rw [hl]; exact ⟨_, haxis s hs, rfl⟩
  have hp : ψ (E0Spear.yVertex v) ∈ futureRayU κ.symm B := by
    rw [futureRay_yVertex_eq]; exact (hU _ hmem2v).1
  have hBc : IsConnected (B : Set BTZE0) := isConnected_btzBox hη (by linarith) (2 * v + T)
  have hAE := futureRay_isAEMorphism hfc B hV
  refine ⟨⟨futureRayU κ.symm B, B, futureRayHomeo κ.symm B hV, hp, hBc, hAE, ?_⟩, ?_,
    fun s hs => ⟨(hU s hs).1, ?_⟩⟩
  · show e0Inr.symm (κ.symm (ψ (E0Spear.yVertex v))) ∈
      Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
    rw [futureRay_yVertex_eq, (hU _ hmem2v).2, e0Inr_symm_inr,
      btz_sing btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0]
    exact ⟨_, rfl, rfl⟩
  · haveI : ConnectedSpace B := isConnected_iff_connectedSpace.1 hBc
    haveI : ConnectedSpace (futureRayU κ.symm B) :=
      (futureRayHomeo κ.symm B hV).symm.surjective.connectedSpace
        (futureRayHomeo κ.symm B hV).symm.continuous
    exact isDescendingChartMap_of_homeomorph (isLocallyUnloopable_of_normedSpace _) hAE
      (isConnected_iff_connectedSpace.2 inferInstance) hBc (isLocallyGaloisian_btzE0 B)
      (hasMaximalLifts_btzBox hη (by linarith) _)
  · rw [chartExt_apply _ (hU s hs).1]
    show e0Inr.symm (κ.symm (ψ _)) = _
    rw [(hU s hs).2, e0Inr_symm_inr]

end E0Charts

/-! ### §4 The future half of the developed BTZ line -/

section E0HalfLine

attribute [local instance] btzE0Structure

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [FirstCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **DEC-126: the full future BTZ ray of `M`, lifted to `M̃`, develops onto a whole future
half-line.** Let `M` be an `𝔼₀`-manifold whose BTZ points carry full future BTZ rays (B21
Lemma 2.3, `hrays`; DEC-125 (b)), `M̃` a chartwise datum (DEC-118 (c)) and `x ∈ M̃` a BTZ point.
Then there are a full future BTZ ray `γ` from `p(x)` and a future null vector `u ≠ 0` (the
developed direction of the BTZ line, `g · nullU` for the descending charts' isometry `g`, the same
for every chart of the chain: the parabolic stabiliser of the line acts on it, and its scale is
pinned by the ray's affine parameter) such that

* for every `λ ≥ 0` there is `z ∈ M̃` over `γ(λ/2)`, with `x ≤ z` and `D z = D x + λ u`
  (the lifted ray `z`, and `D` of it is the WHOLE half-line `D x + ℝ₊ u`);
* every `m ≥ D x` is on that half-line, or is reached from a REGULAR `y ≥ x` with `D y ≤ m`.

Proof: a chain of descending charts along `γ` — for each `T`, ONE `𝔼₀`-chart (a box) along
`γ([0, T])` (`futureRay_exists_chart`), lifted at `x` (`futureRay_lift`); two charts of the chain
agree on the BTZ fibre of their common component (it is one point, `futureRay_eq_apex_of_orbitMk`),
which pins `g u` (`futureRay_isom_axis`). -/
theorem futureRay_halfLine
    (hrays : ∀ p ∈ E0CBG.S0 M, ∃ γ : ℝ → M, E0Spear.IsFullFutureBTZRay p γ) :
    letI := E0Bridge.e0SingularGXStructure M
    haveI := ChartedSpace.locPathConnectedSpace E0Y M
    ∀ {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
      {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
      {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
        DInfty × ℝ} (d : BTZTildeData M y₀ Φ), d.IsChartwise →
      ∀ x : d.Space, (d.toNat x).base ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M →
        ∃ γ : ℝ → M, E0Spear.IsFullFutureBTZRay (d.toNat x).base γ ∧
        ∃ u : Causal.Minkowski 2, Causal.Flat.IsFutureCausal u ∧ Causal.Flat.minkQ u = 0 ∧
          u ≠ 0 ∧
          (∀ lam : ℝ, 0 ≤ lam → ∃ z : d.Space, d.causality.le ⊤ x z ∧
            (d.toNat z).base = γ (lam / 2) ∧ d.D z = d.D x + lam • u) ∧
          ∀ m, (Causal.minkowski 2).le ⊤ (d.D x) m →
            (∃ lam : ℝ, 0 ≤ lam ∧ m = d.D x + lam • u) ∨
            ∃ y : d.Space, (d.toNat y).base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M ∧
              d.causality.le ⊤ x y ∧ (Causal.minkowski 2).le ⊤ (d.D y) m := by
  letI := E0Bridge.e0SingularGXStructure M
  haveI := ChartedSpace.locPathConnectedSpace E0Y M
  intro y₀ yN Φ d hd x hx
  have hxS : (d.toNat x).base ∈ E0CBG.S0 M := by
    exact (Set.ext_iff.1 (E0Bridge.sing_e0SingularGXStructure (M := M)) _).1 hx
  obtain ⟨γ, hγ⟩ := hrays _ hxS
  obtain ⟨v, W, ψ, hW, hray, hψ, hinj, hp, hγψ⟩ := id hγ
  set r : ℝ → M := fun s => ψ (Sum.inr (orbitMk (GammaA (2 * π)) (DInfty.apex, s))) with hrdef
  have hra : r (2 * v) = ψ (E0Spear.yVertex v) := by
    rw [hrdef, futureRay_yVertex_eq]
  have hx' : (d.toNat x).base = ψ (E0Spear.yVertex v) := hp.symm
  have hmem : ∀ T : ℝ, 0 ≤ T → 2 * v ∈ Icc (2 * v) (2 * v + 2 * T) := fun T hT =>
    ⟨le_rfl, by linarith⟩
  -- the reference chart (`T = 1`)
  obtain ⟨c₁, hc₁, hr₁⟩ := futureRay_exists_chart hW hray hψ hinj one_pos
  obtain ⟨g₁, z₁, -, hz₁a, hz₁, huniq₁, hoff₁⟩ :=
    d.futureRay_lift hd c₁ hc₁ (a := 2 * v) (b := 2 * v + 2 * 1) (by linarith) r hr₁ hra x hx'
  have hDx : d.D x = g₁ • nullToMink ((2 * v) • nullU) := by
    have h := (hz₁ (2 * v) (hmem 1 zero_le_one)).2.2
    rwa [hz₁a] at h
  set u : Causal.Minkowski 2 :=
    (g₁ : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear (nullToMink nullU) with hudef
  -- every chart of the chain develops the ray onto the same half-line
  have hT : ∀ T : ℝ, 1 ≤ T → ∀ s ∈ Icc (2 * v) (2 * v + 2 * T), ∃ z : d.Space,
      d.causality.le ⊤ x z ∧ (d.toNat z).base = r s ∧ d.D z = g₁ • nullToMink (s • nullU) := by
    intro T hT1 s hs
    obtain ⟨c, hc, hr⟩ := futureRay_exists_chart hW hray hψ hinj (by linarith : 0 < T)
    obtain ⟨gT, zT, hzTc, hzTa, hzT, -, -⟩ :=
      d.futureRay_lift hd c hc (a := 2 * v) (b := 2 * v + 2 * T) (by linarith) r hr hra x hx'
    have hs₁ : 2 * v + 1 ∈ Icc (2 * v) (2 * v + 2 * T) := ⟨by linarith, by linarith⟩
    have hs₁' : 2 * v + 1 ∈ Icc (2 * v) (2 * v + 2 * 1) := ⟨by linarith, by linarith⟩
    -- the lift of chart `T` stays, up to `2v + 1`, in the component of chart `1`
    have hpath : d.toNat (zT (2 * v + 1)) ∈ connectedComponentIn
        (SpreadEnd.base ⁻¹' (c₁.U : Set M)) (d.toNat x) := by
      have hsubI : Icc (2 * v) (2 * v + 1) ⊆ Icc (2 * v) (2 * v + 2 * T) :=
        Icc_subset_Icc le_rfl hs₁.2
      have hpc : IsPreconnected ((fun s => d.toNat (zT s)) '' Icc (2 * v) (2 * v + 1)) :=
        isPreconnected_Icc.image _ (hzTc.mono hsubI)
      have hsub : (fun s => d.toNat (zT s)) '' Icc (2 * v) (2 * v + 1) ⊆
          SpreadEnd.base ⁻¹' (c₁.U : Set M) := by
        rintro _ ⟨s', hs', rfl⟩
        rw [mem_preimage, (hzT s' (hsubI hs')).1]
        exact (hr₁ s' ⟨hs'.1, by linarith [hs'.2]⟩).1
      have h0 : d.toNat (zT (2 * v)) = d.toNat x := by rw [hzTa]
      have h := hpc.subset_connectedComponentIn ⟨2 * v, ⟨le_rfl, by linarith⟩, h0⟩ hsub
      exact h ⟨2 * v + 1, ⟨by linarith, le_rfl⟩, rfl⟩
    have h1 := huniq₁ _ hpath (2 * v + 1) hs₁' (hzT _ hs₁).1
    have h2 : gT • nullToMink ((2 * v + 1) • nullU) = g₁ • nullToMink ((2 * v + 1) • nullU) :=
      (hzT _ hs₁).2.2.symm.trans h1
    have h3 : gT • nullToMink ((2 * v) • nullU) = g₁ • nullToMink ((2 * v) • nullU) := by
      have h := (hzT _ (hmem T (by linarith))).2.2
      rw [hzTa] at h
      rw [← h, hDx]
    have hL : (gT : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear (nullToMink nullU) = u := by
      have e1 := futureRay_isom_axis gT (2 * v) (2 * v + 1)
      have e2 := futureRay_isom_axis g₁ (2 * v) (2 * v + 1)
      rw [h2, h3] at e1
      rw [e1, add_sub_cancel_left, one_smul, one_smul] at e2
      exact add_left_cancel e2
    refine ⟨zT s, (hzT s hs).2.1, (hzT s hs).1, ?_⟩
    rw [(hzT s hs).2.2, futureRay_isom_axis gT (2 * v) s, futureRay_isom_axis g₁ (2 * v) s, h3,
      hL]
  -- the direction `u`
  have hw₀ := linearPart_btzHol_nullU 0 0
  have hfc₀ : Causal.Flat.IsFutureCausal (nullToMink nullU) := by
    have h : (Causal.minkowski 2).le ⊤ (nullToMink 0) (nullToMink nullU) :=
      (btzJ_le_iff _ _).2 (by simp [nullU])
    rw [Causal.Flat.le_top_iff_minkQ, map_zero, sub_zero] at h
    exact h
  have hu₁ : Causal.Flat.IsFutureCausal u := Causal.Flat.lorentz.isFutureCausal_apply g₁.2 hfc₀
  have hu₂ : Causal.Flat.minkQ u = 0 := by
    exact (Causal.Flat.lorentz.minkQ_apply g₁.2 _).trans hw₀.2.1
  have hu₃ : u ≠ 0 := by
    rw [hudef]
    intro h
    apply hw₀.2.2
    exact (g₁ : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear.injective
      (h.trans (map_zero _).symm)
  have hDs : ∀ s : ℝ, g₁ • nullToMink (s • nullU) = d.D x + (s - 2 * v) • u := fun s => by
    rw [futureRay_isom_axis g₁ (2 * v) s, hDx]
  refine ⟨γ, hγ, u, hu₁, hu₂, hu₃, fun lam hlam => ?_, fun m hm => ?_⟩
  · obtain ⟨z, hxz, hzb, hzD⟩ := hT (max 1 (lam / 2)) (le_max_left _ _) (2 * v + lam)
      ⟨by linarith, by linarith [le_max_right 1 (lam / 2)]⟩
    refine ⟨z, hxz, ?_, ?_⟩
    · rw [hzb, hγψ, hrdef]
      show _ = ψ (E0Spear.yAxis v (lam / 2))
      rw [show lam / 2 = (2 * v + lam) / 2 - v by ring, futureRay_yAxis_eq]
    · rw [hzD, hDs, add_sub_cancel_left]
  · rcases hoff₁ m hm with ⟨s, hs⟩ | hy
    · left
      have hle : 2 * v ≤ s := by
        have h := hm
        rw [hDx, hs, Causal.Flat.isom_le_top_iff, btzJ_le_iff] at h
        have h1 := h.1
        simp [nullU] at h1
        linarith
      exact ⟨s - 2 * v, by linarith, by rw [hs, hDs]⟩
    · exact Or.inr hy

/-- **The reverse inclusion `J⁺(D x) ⊆ D(J⁺(x))` at every BTZ point of `M̃`, given it at the
regular points** (DEC-118 (a)'s causal half of `def:manifold_future_complete_all` at the BTZ
points, the last case of `prop:globally_hyperbolic_cauchy_complete_manifolds`, l.2350–2352): on
the developed half-line by the lifted ray (`futureRay_halfLine`), off it by a regular chart
step and the hypothesis `hreg` at that regular point. -/
theorem futureRay_Jplus_supset
    (hrays : ∀ p ∈ E0CBG.S0 M, ∃ γ : ℝ → M, E0Spear.IsFullFutureBTZRay p γ) :
    letI := E0Bridge.e0SingularGXStructure M
    haveI := ChartedSpace.locPathConnectedSpace E0Y M
    ∀ {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
      {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
      {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
        DInfty × ℝ} (d : BTZTildeData M y₀ Φ), d.IsChartwise →
      (∀ y : d.Space, (d.toNat y).base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M →
        (Causal.minkowski 2).Jplus ⊤ {d.D y} ⊆ d.D '' d.causality.Jplus ⊤ {y}) →
      ∀ x : d.Space, (d.toNat x).base ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M →
        (Causal.minkowski 2).Jplus ⊤ {d.D x} ⊆ d.D '' d.causality.Jplus ⊤ {x} := by
  letI := E0Bridge.e0SingularGXStructure M
  haveI := ChartedSpace.locPathConnectedSpace E0Y M
  intro y₀ yN Φ d hd hreg x hx m hm
  have hm' := Causal.Precausality.mem_Jplus_singleton.1 hm
  obtain ⟨γ, -, u, -, -, -, hhalf, hoff⟩ := futureRay_halfLine hrays d hd x hx
  rcases hoff m hm' with ⟨lam, hlam, rfl⟩ | ⟨y, hyR, hxy, hym⟩
  · obtain ⟨z, hxz, -, hzD⟩ := hhalf lam hlam
    have h2 : d.fromNat (d.toNat z) ∈ d.causality.Jplus ⊤ {x} :=
      Causal.Precausality.mem_Jplus_singleton.2 hxz
    exact ⟨d.toNat z, h2, hzD⟩
  · obtain ⟨y', hy', hDy'⟩ := hreg y hyR (Causal.Precausality.mem_Jplus_singleton.2 hym)
    have hy'' : d.causality.le ⊤ y (d.fromNat y') :=
      (Causal.Precausality.mem_Jplus_singleton (M := d.Space)).1 hy'
    have h2 : d.fromNat y' ∈ d.causality.Jplus ⊤ {x} :=
      Causal.Precausality.mem_Jplus_singleton.2 (d.causality.le_trans hxy hy'')
    exact ⟨y', h2, hDy'⟩

/-- **The hypothesis `hnull` of `GX.btzTilde_supset_of_null`** (`GX.BTZ.Uniformization`),
in its exact form: at a BTZ point `x` of the chartwise `M̃`, every `m ∈ J⁺(D x) ∖ I⁺(D x)` is in
`D(J⁺(x))` — from full future BTZ rays in `M` and the regular case. This is the statement whose
proof was the tagged `sorry` of `GX.btzTilde_null_supset`: with `hreg` the first half of
`GX.btzTilde_supset_of_reg`, it closes that `sorry`. -/
theorem futureRay_null_supset
    (hrays : ∀ p ∈ E0CBG.S0 M, ∃ γ : ℝ → M, E0Spear.IsFullFutureBTZRay p γ) :
    letI := E0Bridge.e0SingularGXStructure M
    haveI := ChartedSpace.locPathConnectedSpace E0Y M
    ∀ {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
      {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
      {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
        DInfty × ℝ} (d : BTZTildeData M y₀ Φ), d.IsChartwise →
      (∀ y : d.Space, (d.toNat y).base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M →
        (Causal.minkowski 2).Jplus ⊤ {d.D y} ⊆ d.D '' d.causality.Jplus ⊤ {y}) →
      ∀ x : d.Space, (d.toNat x).base ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M →
        ∀ m ∈ (Causal.minkowski 2).Jplus ⊤ {d.D x}, m ∉ (Causal.minkowski 2).Iplus ⊤ {d.D x} →
          m ∈ d.D '' d.causality.Jplus ⊤ {x} := by
  letI := E0Bridge.e0SingularGXStructure M
  haveI := ChartedSpace.locPathConnectedSpace E0Y M
  intro y₀ yN Φ d hd hreg x hx m hm _
  exact futureRay_Jplus_supset hrays d hd hreg x hx hm

end E0HalfLine

end GX
