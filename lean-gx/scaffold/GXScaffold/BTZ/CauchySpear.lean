import GXScaffold.BTZ.MaxExtension
import GX.BTZ.BluntSpear

/-!
# btz § 5.4, `theo:BTZ_Cauchy-completness`, Step 1 for `𝔼₀`-manifolds: every BTZ line of the maximal BTZ-extension of `M₀` has a spear neighbourhood

Target `T-btz-cauchy-spear` (`roadmap/roadmap.toml`). Paper `btz`
(`papers/btz/legacy/labeled/BTZ_1.tex`), theorem l.1582–1589, proof l.1592–1637; Step 1 is
l.1598–1604. Row (unmarked, partial):

* `btzthm:BTZ_Cauchy-completness` — `BTZ_1.tex:1582` (Step 1 of (i) ⇒ (iii), l.1598–1604) —
  `GX.BTZCauchySpear.cauchy_spear`, with `GX.BTZCauchySpear.exists_cauchyMaximalExt` (`M₂`),
  `GX.BTZCauchySpear.bluntSpear_subset_M0` (the analytic core), `GX.BTZCauchySpear.spearInt_subset_range`
  (BTZ-maximality of `M₁`), `GX.BTZCauchySpear.globallyHyperbolicOn_union` (with
  `GX.BTZCauchySpear.causallyConvexIn_union`, `GX.BTZCauchySpear.exists_axis_eq_of_le`),
  `GX.BTZCauchySpear.exists_spearNbhd_of_subset` and `GX.BTZCauchySpear.causallyConvexIn_range`.
  Step 2 (`M₁ = M₂` Cauchy-complete) is T-btz-cauchy-conservation; nothing of it is here.

> Let $M_0:=\reg_{>0}(M)$ and assume $M_0$ is a globally hyperbolic Cauchy-complete Cauchy-maximal
> $\mass{>0}$-manifold. Consider, $M_1$ the maximal BTZ-extension of $M_0$ and $M_2$ the
> Cauchy-maximal extension of $M_1$. (l.1595–1596)
>
> Step 1 : every BTZ-line of $M_1$ admits a spear neighborhood. (l.1598)
>
> Let $\Delta$ be BTZ-line of $M_2$ and let $p\in \Delta$ in the past of $\Sigma_1$. By Lemma
> \ref{lem:tube} there exists $\S\xrightarrow{\phi} \mass{0}$ a spear neighborhood of vertex $p$
> (l.1600) […] By Cauchy-maximality of $M_0$, we deduce that $N\subset M_0$. In particular, $M_0$
> contains some blunt spear neighborhood $\S_1^*$ the regular part of a spear neighborhood
> $\S_1\subset M_2$ around $\Delta$ of some vertex $p'$. Notice $M_1\cup \mathrm{Int}(\S_1)$ is a
> globally hyperbolic BTZ-extension of $M_1$, by BTZ-maximality of $M_1$, we deduce that
> $\mathrm{Int}(\S_1)\subset M_1$. Therefore, every BTZ-line of $M_1$ admits a spear neighborhood.
> (l.1604)

## The proof, step by step

1. `M₂` (l.1596): `exists_cauchyMaximalExt` — CBG (`GX.E0CBG.e0_cbg_isETTMaximal`) gives an
   ETT-maximal Cauchy development of `M₁`; it is `IsE0CauchyMaximal` (any Cauchy `𝔼₀`-embedding out
   of it makes a development of `M₁`). Closed.
2. `lem:tube` in `M₂` (l.1600): the strict `GX.E0Spear.lem_tube_e0`, at the image of the BTZ point.
3. The blunt spear of `M₀` (l.1601–1604): `bluntSpear_subset_M0`, **one tagged `sorry`** (SCOPE).
4. BTZ-maximality of `M₁` (l.1604): `spearInt_subset_range` — the corestriction of `M₁ → M₂` to
   `M₁ ∪ Int(S₁)` is a BTZ-embedding (the points of `Int(S₁)` outside `M₁` are on the axis), so
   by inextensibility of a maximal extension (`GX.BTZMax.isInextensible_of_isMaximal`) it is onto.
   Closed, with `globallyHyperbolicOn_union` (T-btz-spear-union-gh): `M₁ ∪ Int(S₁)` is causally
   convex in `M₂` (`causallyConvexIn_union`, §2b), hence globally hyperbolic (B21 Remark 1). The
   convexity rests on the matching of a BTZ line with a spear chart's axis
   (`exists_axis_eq_of_le`: a BTZ point above an axis point is on the axis, through
   `IsFullFutureBTZRay.exists_eq_of_line`), and on regular points of the blunt spear (in `M₁`)
   above every axis point and below every regular point above a non-vertex axis point.
5. The spear of `M₁` (l.1604, « Therefore »): `exists_spearNbhd_of_subset` — a spear of vertex
   `(v' + 1, 0)` and radius `R'/2` inside `Int(S₁)`, pulled back to `M₁`; its vertex is on the BTZ
   line of `M₁` through `p` because the axis segment between them lies in `M₁`, the image of a
   Cauchy embedding being causally convex (`causallyConvexIn_range`). Closed.

## Hypothesis checklist (`cauchy_spear`)

| paper hypothesis | here |
|---|---|
| `𝔼_{≥0}`-manifolds | ⚠ `𝔼₀` only (T-btz-scope) |
| `M₀` an `𝔼_{>0}`-manifold | ✓ read as a flat spacetime `N : Causal.Flat.FlatSpacetime 2` (connected, Hausdorff; second countable by DEC-49), seen as an `𝔼₀`-manifold through `GX.FlatE0` (the `𝔼_{A*}`, `A* = ∅`, of l.1088; OQ-142 (f)) |
| `M₀` globally hyperbolic, Cauchy-maximal | ✓ `Causal.Flat.MGH N` (GH, and every flat Cauchy embedding onto), the form `prop_reg_complete` proves for `Reg M` |
| `M₀` Cauchy-complete | ⚠ read `Causal.Flat.IsCauchyComplete 2 N` (DEC-31/35: a spacelike-Lipschitz complete Cauchy surface), the form `prop_reg_complete` proves; not the « smooth » one of l.227 (OQ-142 (e)) |
| `M₁` « the maximal BTZ-extension of `M₀` » | ✓ any `Causal.AbstractDev.IsMaximal` `GX.BTZMax.GHExt` of `M₀` (OQ-150 (a)); no `RichardsInput` (`GX.BTZMax.btz_ext` supplies one under it) |
| `M₂` « the Cauchy-maximal extension of `M₁` » | ✓ constructed (`exists_cauchyMaximalExt`), not assumed |
| conclusion: a spear neighbourhood around every BTZ line of `M₁` | ✓ for every `p ∈ sing₀(M₁)`, an `IsSpearNbhd q R U` in `M₁` with `q` in the connected component of `sing₀(M₁)` through `p` |

## SCOPE (disclosed)

`cauchy_spear` rests on one tagged `sorry` of this file, `bluntSpear_subset_M0`, so the row is
not marked. (`globallyHyperbolicOn_union`, formerly the second, is proved: §2b.)

* `bluntSpear_subset_M0` (l.1601–1604): that the regular part of a sub-spear of the spear of `M₂`
  lies in `M₀`. The paper's route: `lem:add_BTZ_param` on `Σ₁`, `lem:blunt_spear_neighborhood` on
  `Σ₀` (applied before `reg(S) ⊂ M₀` is known, OQ-143 (e)), `lem:surface_complete` (`τ₀ → +∞`),
  the open set `N := (M₀ ∖ J⁺(C′)) ∪ reg(Int(S) ∖ J⁻_S(C″))`, « a simple analysis using Lemma
  lem:intersect_number_complete » that `Σ₀` is a Cauchy surface of `N`, and Cauchy-maximality of
  `M₀` for « `N ⊂ M₀` ». Not formalized: the construction of `N` and the Cauchy property of `Σ₀`
  in it are not printed, and the strict `GX.E0Surgery.lem_surface_complete_two` needs a `C¹`
  graph, which the Lipschitz reading of « Cauchy-complete » does not give.
* `globallyHyperbolicOn_union` (l.1604, « Notice `M₁ ∪ Int(S₁)` is a globally hyperbolic
  BTZ-extension of `M₁` », asserted): **proved** (T-btz-spear-union-gh). An open subset of the
  globally hyperbolic `M₂` need not be globally hyperbolic; the proof supplied here is causal
  convexity of `M₁ ∪ Int(S₁)` in `M₂` (`causallyConvexIn_union`), from that of `M₁`
  (`causallyConvexIn_range`, the Cauchy property of `M₁ → M₂`) and the regular part of `S₁` lying
  in `M₁`; the hypothesis `IsE0Mor j univ` is carried but unused.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open E0 E0CBG E0Spear E0BluntSpear E0AbsMax

namespace BTZCauchySpear

/-! ### §1 The Cauchy-maximal extension `M₂` of an `𝔼₀`-manifold -/

theorem exists_cauchyMaximalExt {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace E0Y X] [HasGroupoid X e0Groupoid]
    (hGH : (CE X).GloballyHyperbolic) :
    ∃ (Y : E0Mfd) (_ : ConnectedSpace Y) (j : X → Y),
      Causal.IsCauchyEmbedding (CE X) (CE Y) j ∧ IsE0Mor j univ ∧ IsE0CauchyMaximal Y := by
  have hLine := E0LM.e0_globalBTZ
  have hSC : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
      [HasGroupoid M e0Groupoid], (Causal.CBG.chartedCausality E0LM.D M).GloballyHyperbolic →
      ∀ S : Set M, (Causal.CBG.chartedCausality E0LM.D M).IsCauchySurface S →
      SecondCountableTopology S → SecondCountableTopology M :=
    fun {_} _ _ _ _ _ => E0LM.e0_secondCountable_of_cauchy
  obtain ⟨S, hS⟩ := exists_isCauchySurface_of_globalBTZ (E0LM.e0_globalBTZ X) hGH
  obtain ⟨Mbar, hmax⟩ := e0_cbg_isETTMaximal hLine hSC hGH hS
  letI : ChartedSpace E0Y Mbar.carrier := Mbar.str.1
  haveI : HasGroupoid Mbar.carrier e0Groupoid := Mbar.str.2
  refine ⟨E0Mfd.of Mbar.carrier, Mbar.conn, Mbar.emb, Mbar.isCauchyEmbedding, Mbar.isMor, ?_⟩
  intro K _ _ _ _ _ _ f hf hfm
  have hc : Causal.IsCauchyEmbedding (CE X) (CE K) (f ∘ Mbar.emb) := by
    have h1 : Causal.IsCauchyEmbedding (CE X) (CE Mbar.carrier) Mbar.emb := Mbar.isCauchyEmbedding
    obtain ⟨T, hT, hT'⟩ := h1.exists_cauchy
    refine ⟨h1.globallyHyperbolic_source, hf.globallyHyperbolic_target,
      Causal.IsEMorphism.comp hf.isEMorphism h1.isEMorphism, hf.injective.comp h1.injective,
      T, hT, ?_⟩
    rw [image_comp]
    exact hf.isCauchySurface_image hT'
  have hm : IsE0Mor (f ∘ Mbar.emb) univ :=
    Causal.CBG.liftPropOn_comp isOpen_univ isOpen_univ hfm Mbar.isMor (mapsTo_univ _ _)
  let Kd : Causal.CBG.Dev (e0Geometry hLine hSC).toPreGeometry (e0Str hLine hSC X) :=
    { carrier := K
      str := e0Str hLine hSC K
      emb := f ∘ Mbar.emb
      isCauchyEmbedding := hc
      isMor := hm }
  exact hmax Kd f ⟨hfm, rfl⟩

/-! ### §2 The setting: `M₀` flat, `M₁` a maximal globally hyperbolic BTZ-extension, `M₂ ⊇ M₁` -/

variable {N : Causal.Flat.FlatSpacetime.{0} 2}

/-- **The image of a Cauchy embedding of `𝔼₀`-manifolds is causally convex** (Design §3 step 3,
`Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn`). -/
theorem causallyConvexIn_range {X Y : Type} [TopologicalSpace X] [ChartedSpace E0Y X]
    [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [SecondCountableTopology Y]
    [ChartedSpace E0Y Y] [HasGroupoid Y e0Groupoid] {j : X → Y}
    (hj : Causal.IsCauchyEmbedding (CE X) (CE Y) j) :
    (CE Y).CausallyConvexIn (range j) ⊤ := by
  have hGY := hj.globallyHyperbolic_target
  obtain ⟨S, hS, hS'⟩ := hj.exists_cauchy
  have h := Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn (C := CE Y)
    (A := hj.rangeOpens) (B := ⊤) (fun x y hxy hyx => hGY.1 hxy hyx)
    (e0_sfa_of_globalBTZ Y).causallyArcConnected (E0LM.e0_curvesExtend hGY) le_top
    (by rw [Causal.IsCauchyEmbedding.coe_rangeOpens]; exact image_subset_range _ _)
    ((hj.isEMorphism.isCauchySurface_iff hj.injective S).1 hS) hS'
  rwa [Causal.IsCauchyEmbedding.coe_rangeOpens] at h

/-- The interior `{f > v, r < R}` of the spear `spearY v R`, in `Y`. -/
noncomputable def spearIntY (v R : ℝ) : Set E0Y := paperInY '' {x : E0 | v < fcoord x ∧ rad x < R}

/-- **Step 1, the analytic core** (`BTZ_1.tex:1601–1604`): for a spear chart `φ` of `M₂` with
vertex `j p`, `p` a BTZ point of `M₁` (the paper's « `Δ` a BTZ-line of `M₂` », l.1600, is a line
of `M₁` read in `M₂`: every BTZ line of `M₂` meets the Cauchy surface `Σ₁ ⊂ M₁`, and `M₁` is causally
convex in `M₂`, so the lines of the two correspond one to one), the regular part of a
sub-spear `φ(bspear v' R')`, `v ≤ v'`, `R' ≤ R`, lies in `M₀` (« `M₀` contains some blunt spear
neighborhood `S₁*` the regular part of a spear neighborhood `S₁ ⊂ M₂` around `Δ` »). -/
theorem bluntSpear_subset_M0 (hmax : Causal.Flat.MGH N) (hcc : Causal.Flat.IsCauchyComplete 2 N)
    (E : BTZMax.GHExt (FlatE0 N)) {Y : E0Mfd} [ConnectedSpace Y] {j : E.N → Y}
    (hj : Causal.IsCauchyEmbedding (CE E.N) (CE Y) j) (hjm : IsE0Mor j univ)
    {p : E.N} (hp : p ∈ S0 E.N) {v R : ℝ} {W : Set E0Y} {φ : E0Y → Y} (hR : 0 < R)
    (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hφ : IsE0Mor φ W) (hinj : InjOn φ W)
    (hv : φ (yVertex v) = j p) :
    ∃ v' R', v ≤ v' ∧ 0 < R' ∧ R' ≤ R ∧ φ '' bspearY v' R' ⊆ range (j ∘ E.ι) := by
  sorry -- SORRY(btzthm:BTZ_Cauchy-completness): l.1601–1604 unprinted: Σ₀ Cauchy in N := (M₀ ∖ J⁺(C′)) ∪ reg(Int S ∖ J⁻(C″)) (intersect_number_complete on Σ₀'s cusp in S, needing Σ₀ ∩ S a graph before reg S ⊂ M₀ is known, OQ-143 (e)), then N ⊂ M₀ by MGH; surface_complete needs a C¹ graph, the Lipschitz completeness gives none

/-! ### §2b `M₁ ∪ Int(S₁)` is causally convex in `M₂` (`BTZ_1.tex:1604`)

The axis of a spear chart is a full future BTZ ray; the BTZ points above an axis point are on the
axis (`IsFullFutureBTZRay.exists_eq_of_line`, the matching of the BTZ line with the chart's axis);
the axis points of the spear lie between regular points of its blunt part, in the causal sense
that each has one in its future (`exists_nhds_diff_sing_subset_Iplus`) and each regular point
above an axis point `ψ(v + t, 0)`, `t > 0`, has one in its past (push-up through the vertex). -/

section UnionGH

variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E0Y Y] [HasGroupoid Y e0Groupoid]

omit [HasGroupoid Y e0Groupoid] in
/-- The axis of a spear chart, started at its point of parameter `t₁ ≥ 0`, is a full future BTZ
ray. -/
theorem isFullFutureBTZRay_axis_shift {v : ℝ} {W : Set E0Y} {φ : E0Y → Y} (hW : IsOpen W)
    (hray : ∀ t, 0 ≤ t → yAxis v t ∈ W) (hφ : IsE0Mor φ W) (hinj : InjOn φ W) {t₁ : ℝ}
    (ht₁ : 0 ≤ t₁) :
    IsFullFutureBTZRay (φ (yAxis v t₁)) (fun t => φ (yAxis v (t₁ + t))) := by
  have e : ∀ t, yAxis (v + t₁) t = yAxis v (t₁ + t) := fun t => by
    simp only [yAxis, add_assoc]
  refine ⟨v + t₁, W, φ, hW, fun t ht => ?_, hφ, hinj, ?_, fun t => by rw [e]⟩
  · rw [e]; exact hray _ (by linarith)
  · rw [← yAxis_zero, e, add_zero]

/-- **The BTZ points above an axis point of a spear chart are on its axis** (the matching of the
BTZ line, `SingularFlatAxioms.line`, with the chart's axis, `IsFullFutureBTZRay.exists_eq_of_line`;
global hyperbolicity is used). -/
theorem exists_axis_eq_of_le [T2Space Y] [ConnectedSpace Y] [SecondCountableTopology Y]
    (hGY : (CE Y).GloballyHyperbolic) {v : ℝ} {W : Set E0Y} {φ : E0Y → Y} (hW : IsOpen W)
    (hray : ∀ t, 0 ≤ t → yAxis v t ∈ W) (hφ : IsE0Mor φ W) (hinj : InjOn φ W) {t₁ : ℝ}
    (ht₁ : 0 ≤ t₁) {y : Y} (hy : y ∈ S0 Y) (hle : (CE Y).le ⊤ (φ (yAxis v t₁)) y) :
    ∃ t, t₁ ≤ t ∧ φ (yAxis v t) = y := by
  have hr := isFullFutureBTZRay_axis_shift hW hray hφ hinj ht₁
  have hq : φ (yAxis v t₁) ∈ S0 Y := by
    have := hr.mem_S0 (le_refl (0 : ℝ))
    simpa only [add_zero] using this
  obtain ⟨γ, hγ0, hγe, hγi, hγr⟩ := (E0LM.e0_globalBTZ Y).line _ hq
  have hγe' := hγe hGY.1
  have hsfa := e0_sfa_of_globalBTZ Y
  have hyc : y ∈ connectedComponentIn (S0 Y) (φ (yAxis v t₁)) := by
    have h1 := hsfa.Jminus_subset_component hy hle
    show y ∈ connectedComponentIn (Causal.CBG.chartedSing e0SingY Y 0) _
    rw [← connectedComponentIn_eq h1]
    exact mem_connectedComponentIn hy
  rw [← hγr] at hyc
  obtain ⟨s, rfl⟩ := hyc
  have hs : 0 ≤ s := by
    by_contra h
    push Not at h
    have h1 : (CE Y).le ⊤ (γ s) (γ 0) := hγi.1.le_of_le trivial trivial h.le
    rw [hγ0] at h1
    have h2 := hγe'.injective ((hGY.1 h1 hle).trans hγ0.symm)
    linarith
  obtain ⟨t, ht, hrt⟩ := hr.exists_eq_of_line hGY hγ0 hγe' hγi.1 hγr hs
  exact ⟨t₁ + t, by linarith, hrt⟩

omit [HasGroupoid Y e0Groupoid] in
/-- A point of a spear chart off the axis is regular. -/
theorem notMem_S0_of_ne_zero {W : Set E0Y} {φ : E0Y → Y} (hW : IsOpen W) (hφ : IsE0Mor φ W)
    {e : E0} (he : paperInY e ∈ W) (h2 : e.2 ≠ 0) : φ (paperInY e) ∉ S0 Y := by
  rw [← Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem hW hφ he le_rfl]
  show ¬ (chartAt E0Y (paperInY e) (paperInY e) ∈ e0SingY 0)
  rw [chartAt_self_eq]
  exact fun h => h2 ((e0Loop_paperInY_mem_sing_iff e).1 h)

omit [HasGroupoid Y e0Groupoid] in
/-- **Every neighbourhood of an axis point of a spear chart meets its blunt part in a regular
point.** -/
theorem exists_bspear_near_axis {v R : ℝ} {W : Set E0Y} {φ : E0Y → Y} (hR : 0 < R)
    (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hφ : IsE0Mor φ W) {t : ℝ} (ht : 0 ≤ t)
    {V : Set Y} (hV : V ∈ 𝓝 (φ (yAxis v t))) :
    ∃ x ∈ φ '' bspearY v R, x ∈ V ∧ x ∉ S0 Y := by
  set c : ℝ → E0Y := fun ε => paperInY ((v + t + ε, (ε : ℂ)) : E0) with hc
  have hcc : Continuous c := continuous_paperInY.comp
    ((continuous_const.add continuous_id).prodMk Complex.continuous_ofReal)
  have hc0 : c 0 = yAxis v t := by simp [hc, yAxis]
  have hW0 : yAxis v t ∈ W := hsub (yAxis_mem_spearY hR.le ht)
  have hφc : ContinuousAt φ (yAxis v t) :=
    (hφ _ hW0).continuousWithinAt.continuousAt (hW.mem_nhds hW0)
  have hlim : Tendsto (φ ∘ c) (𝓝 0) (𝓝 (φ (yAxis v t))) := by
    have := hφc.tendsto.comp (hc0 ▸ hcc.tendsto 0)
    exact this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (φ (c ε) ∈ V ∧ c ε ∈ W) ∧ ε ∈ Ioo 0 R :=
    ((hlim.eventually hV).and ((hc0 ▸ hcc.tendsto 0).eventually (hW.mem_nhds hW0))).filter_mono
      nhdsWithin_le_nhds |>.and (Ioo_mem_nhdsGT hR)
  obtain ⟨ε, ⟨hεV, hεW⟩, hε0, hεR⟩ := hev.exists
  have hrad : rad ((v + t + ε, (ε : ℂ)) : E0) = ε := by
    simp [rad, Complex.norm_real, abs_of_pos hε0]
  refine ⟨φ (c ε), ⟨c ε, ⟨_, ⟨?_, ?_, ?_⟩, rfl⟩, rfl⟩, hεV, ?_⟩
  · simp only [fcoord, hrad]; linarith
  · rw [hrad]; exact hε0
  · rw [hrad]; exact hεR.le
  · exact notMem_S0_of_ne_zero hW hφ hεW (by simpa using hε0.ne')

variable [T2Space Y] [ConnectedSpace Y] [SecondCountableTopology Y]

/-- **Each axis point of a spear chart has a regular point of the blunt spear in its future**
(`exists_nhds_diff_sing_subset_Iplus` at the axis point one parameter higher). -/
theorem exists_bspear_above_axis {v R : ℝ} {W : Set E0Y}
    {φ : E0Y → Y} (hR : 0 < R) (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hφ : IsE0Mor φ W)
    (hinj : InjOn φ W) {t : ℝ} (ht : 0 ≤ t) :
    ∃ w ∈ φ '' bspearY v R, (CE Y).le ⊤ (φ (yAxis v t)) w := by
  have hray : IsFullFutureBTZRay (φ (yVertex v)) (fun t => φ (yAxis v t)) :=
    ⟨v, W, φ, hW, fun t ht => hsub (yAxis_mem_spearY hR.le ht), hφ, hinj, rfl, fun _ => rfl⟩
  have hsfa := e0_sfa_of_globalBTZ Y
  have hne : φ (yAxis v t) ≠ φ (yAxis v (t + 1)) := fun h => by
    have := hray.injOn (mem_Ici.2 ht) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ t + 1)) h
    linarith
  obtain ⟨V, hV, hVI⟩ := exists_nhds_diff_sing_subset_Iplus hsfa (hray.mem_S0 ht)
    (hray.mem_S0 (by linarith)) (hray.le ht (by linarith)) hne
  obtain ⟨x, hx, hxV, hxs⟩ := exists_bspear_near_axis hR hW hsub hφ (by linarith : 0 ≤ t + 1) hV
  have hlt := hVI ⟨hxV, hxs⟩
  exact ⟨x, hx, (CE Y).le_of_lt (Causal.Precausality.mem_Iplus_singleton.1 hlt)⟩

/-- **A regular point above an axis point `ψ(v + t₁, 0)`, `t₁ > 0`, of a spear chart has a regular
point of the blunt spear in its past**: the vertex is in its chronological past
(`lt_of_lt_of_le_of_not_mem`), which is open. -/
theorem exists_bspear_below_of_le {v R : ℝ} {W : Set E0Y}
    {φ : E0Y → Y} (hR : 0 < R) (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hφ : IsE0Mor φ W)
    (hinj : InjOn φ W) {t₁ : ℝ} (ht₁ : 0 < t₁) {y : Y} (hy : y ∉ S0 Y)
    (hle : (CE Y).le ⊤ (φ (yAxis v t₁)) y) :
    ∃ w ∈ φ '' bspearY v R, (CE Y).le ⊤ w y := by
  have hray : IsFullFutureBTZRay (φ (yVertex v)) (fun t => φ (yAxis v t)) :=
    ⟨v, W, φ, hW, fun t ht => hsub (yAxis_mem_spearY hR.le ht), hφ, hinj, rfl, fun _ => rfl⟩
  have hsfa := e0_sfa_of_globalBTZ Y
  have hne : φ (yAxis v 0) ≠ φ (yAxis v t₁) := fun h => by
    have := hray.injOn (mem_Ici.2 le_rfl) (mem_Ici.2 ht₁.le) h
    linarith
  have hlt : (CE Y).lt ⊤ (φ (yAxis v 0)) y :=
    hsfa.lt_of_lt_of_le_of_not_mem (hray.mem_S0 le_rfl) (hray.mem_S0 ht₁.le)
      (hray.le le_rfl ht₁.le) hne hy hle
  have hI : (CE Y).Iminus ⊤ {y} ∈ 𝓝 (φ (yAxis v 0)) :=
    (CE Y).isOpen_Iminus.mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 hlt)
  obtain ⟨x, hx, hxI, -⟩ := exists_bspear_near_axis hR hW hsub hφ le_rfl hI
  exact ⟨x, hx, (CE Y).le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hxI)⟩

/-- **`M₁ ∪ Int(S₁)` is causally convex in `M₂`** (`BTZ_1.tex:1604`; the step the paper leaves
implicit). For `a ≤ y ≤ b` with `a, b ∈ M₁ ∪ Int(S₁)` and `y ∉ M₁`: a point of `Int(S₁)` outside
`M₁` is an axis point `ψ(v + t, 0)`, `t > 0`. If `y` is BTZ, it is on the axis — above `a` when
`a` is an axis point (`exists_axis_eq_of_le`), and otherwise comparable with the vertex on the line
below `b` (`SingularFlatAxioms.Jminus_eq_image`), not below it (the vertex precedes a point of
`M₁`, `exists_bspear_above_axis`, and `M₁` is causally convex) and not equal to it. If `y` is
regular, `b ∈ M₁` (BTZ points precede only BTZ points), so `a` is an axis point and a regular point
of `M₁` precedes `y` (`exists_bspear_below_of_le`): `y ∈ M₁` by causal convexity of `M₁`. -/
theorem causallyConvexIn_union {X : Type} [TopologicalSpace X] [ChartedSpace E0Y X] {j : X → Y}
    (hj : Causal.IsCauchyEmbedding (CE X) (CE Y) j)
    {v R : ℝ} {W : Set E0Y} {φ : E0Y → Y} (hR : 0 < R) (hW : IsOpen W) (hsub : spearY v R ⊆ W)
    (hφ : IsE0Mor φ W) (hinj : InjOn φ W) (hreg : φ '' bspearY v R ⊆ range j) :
    (CE Y).CausallyConvexIn (range j ∪ φ '' spearIntY v R) ⊤ := by
  have hGY := hj.globallyHyperbolic_target
  have hconv := causallyConvexIn_range hj
  have hsfa := e0_sfa_of_globalBTZ Y
  have hray0 : ∀ t, 0 ≤ t → yAxis v t ∈ W := fun t ht => hsub (yAxis_mem_spearY hR.le ht)
  have hray : IsFullFutureBTZRay (φ (yVertex v)) (fun t => φ (yAxis v t)) :=
    ⟨v, W, φ, hW, hray0, hφ, hinj, rfl, fun _ => rfl⟩
  -- the axis points of the interior
  have hAx : ∀ t, 0 < t → φ (yAxis v t) ∈ φ '' spearIntY v R := fun t ht =>
    ⟨_, ⟨((v + t, 0) : E0), ⟨by simp [fcoord, rad, ht], by simp [rad, hR]⟩, rfl⟩, rfl⟩
  -- a point of `M₁ ∪ Int(S₁)` is in `M₁` or an axis point of positive parameter
  have hout : ∀ x ∈ range j ∪ φ '' spearIntY v R, x ∈ range j ∨ ∃ t, 0 < t ∧ φ (yAxis v t) = x := by
    rintro x (hx | ⟨_, ⟨e, he, rfl⟩, rfl⟩)
    · exact Or.inl hx
    by_cases hr : rad e = 0
    · have he2 : e.2 = 0 := rad_eq_zero.1 hr
      refine Or.inr ⟨e.1 - v, ?_, ?_⟩
      · have := he.1
        simp only [fcoord, hr, zero_div, sub_zero] at this
        linarith
      · show φ (paperInY ((v + (e.1 - v), 0) : E0)) = φ (paperInY e)
        congr 2
        exact Prod.ext (by simp) he2.symm
    · exact Or.inl (hreg ⟨paperInY e, ⟨e, ⟨he.1.le,
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr), he.2.le⟩, rfl⟩, rfl⟩)
  refine ⟨subset_univ _, fun a ha b hb y hy => ?_⟩
  obtain ⟨hay, hyb⟩ := Causal.Causality.mem_diamond.1 hy
  by_cases hyj : y ∈ range j
  · exact Or.inl hyj
  have key : ∀ a' ∈ range j, ∀ b' ∈ range j, (CE Y).le ⊤ a' y → (CE Y).le ⊤ y b' → False :=
    fun a' ha' b' hb' h1 h2 => hyj (hconv.2 a' ha' b' hb' (Causal.Causality.mem_diamond.2 ⟨h1, h2⟩))
  -- the vertex precedes a point of `M₁`
  obtain ⟨w₀, hw₀, hvw₀⟩ := exists_bspear_above_axis hR hW hsub hφ hinj (le_refl (0 : ℝ))
  by_cases hys : y ∈ S0 Y
  · rcases hout a ha with ha' | ⟨ta, hta, rfl⟩
    · -- `a ∈ M₁`: `b` is an axis point
      rcases hout b hb with hb' | ⟨tb, htb, rfl⟩
      · exact (key a ha' b hb' hay hyb).elim
      have hb0 : φ (yAxis v tb) ∈ S0 Y := hray.mem_S0 htb.le
      obtain ⟨γ, hγ0, hγe, hγi, hγr⟩ := (E0LM.e0_globalBTZ Y).line _ hb0
      have hγe' := hγe hGY.1
      have hJ := hsfa.Jminus_eq_image hGY.1 hb0 hγ0 hγe' hγi.1 hγr
      have hyJ : y ∈ (CE Y).Jminus ⊤ {φ (yAxis v tb)} :=
        Causal.Precausality.mem_Jminus_singleton.2 hyb
      have hvJ : φ (yAxis v 0) ∈ (CE Y).Jminus ⊤ {φ (yAxis v tb)} :=
        Causal.Precausality.mem_Jminus_singleton.2 (hray.le le_rfl htb.le)
      rw [hJ] at hyJ hvJ
      obtain ⟨s, -, hs⟩ := hyJ
      obtain ⟨s', -, hs'⟩ := hvJ
      rcases le_total s s' with h | h
      · -- `y` below the vertex: in `M₁`
        have h1 : (CE Y).le ⊤ y (φ (yAxis v 0)) := by
          rw [← hs, ← hs']; exact hγi.1.le_of_le trivial trivial h
        exact (key a ha' w₀ (hreg hw₀) hay ((CE Y).le_trans h1 hvw₀)).elim
      · -- `y` above the vertex: on the axis
        have h1 : (CE Y).le ⊤ (φ (yAxis v 0)) y := by
          rw [← hs, ← hs']; exact hγi.1.le_of_le trivial trivial h
        obtain ⟨t, ht, hty⟩ := exists_axis_eq_of_le hGY hW hray0 hφ hinj le_rfl hys h1
        rcases ht.lt_or_eq with ht | ht
        · rw [← hty]; exact Or.inr (hAx t ht)
        · subst ht
          rw [hty] at hvw₀
          exact (key a ha' w₀ (hreg hw₀) hay hvw₀).elim
    · -- `a` an axis point: so is `y`
      obtain ⟨t, ht, hty⟩ := exists_axis_eq_of_le hGY hW hray0 hφ hinj hta.le hys hay
      rw [← hty]; exact Or.inr (hAx t (hta.trans_le ht))
  · -- `y` regular: `b ∈ M₁`, `a` an axis point
    rcases hout b hb with hb' | ⟨tb, htb, rfl⟩
    · rcases hout a ha with ha' | ⟨ta, hta, rfl⟩
      · exact (key a ha' b hb' hay hyb).elim
      obtain ⟨w, hw, hwy⟩ := exists_bspear_below_of_le hR hW hsub hφ hinj hta hys hay
      exact (key w (hreg hw) b hb' hwy hyb).elim
    · exact (hys (hsfa.mem_sing_zero_of_le (hray.mem_S0 htb.le) hyb)).elim

end UnionGH

/-- **`M₁ ∪ Int(S₁)` is globally hyperbolic** (`BTZ_1.tex:1604`, asserted without justification):
B21 Remark 1 (`E0AbsMax.globallyHyperbolicOn_of_causallyConvexIn`) on the causal convexity
`causallyConvexIn_union`. The `𝔼₀`-morphism hypothesis on `j` is not used (the Cauchy embedding
suffices). -/
theorem globallyHyperbolicOn_union {X Y : Type} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace E0Y X] [HasGroupoid X e0Groupoid]
    [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [SecondCountableTopology Y]
    [ChartedSpace E0Y Y] [HasGroupoid Y e0Groupoid] {j : X → Y}
    (hj : Causal.IsCauchyEmbedding (CE X) (CE Y) j) (_hjm : IsE0Mor j univ)
    {v R : ℝ} {W : Set E0Y} {φ : E0Y → Y} (hR : 0 < R) (hW : IsOpen W) (hsub : spearY v R ⊆ W)
    (hφ : IsE0Mor φ W) (hinj : InjOn φ W) (hreg : φ '' bspearY v R ⊆ range j)
    (hU : IsOpen (range j ∪ φ '' spearIntY v R)) :
    (CE Y).GloballyHyperbolicOn ⟨range j ∪ φ '' spearIntY v R, hU⟩ := by
  exact globallyHyperbolicOn_of_causallyConvexIn hj.globallyHyperbolic_target
    E0LM.e0_causallyArcConnected (causallyConvexIn_union hj hR hW hsub hφ hinj hreg)

/-- **BTZ-maximality of `M₁`** (`BTZ_1.tex:1604`): the interior of the spear lies in `M₁`. -/
theorem spearInt_subset_range (E : BTZMax.GHExt (FlatE0 N))
    (hE : Causal.AbstractDev.IsMaximal (carrier := fun X : BTZMax.GHExt (FlatE0 N) => (X.N : Type))
      (BTZMax.extMor (FlatE0 N)) E)
    {Y : E0Mfd} [ConnectedSpace Y] {j : E.N → Y}
    (hj : Causal.IsCauchyEmbedding (CE E.N) (CE Y) j) (hjm : IsE0Mor j univ)
    {v R : ℝ} {W : Set E0Y} {φ : E0Y → Y} (hR : 0 < R)
    (hW : IsOpen W) (hsub : spearY v R ⊆ W) (hφ : IsE0Mor φ W) (hinj : InjOn φ W)
    (hreg : φ '' bspearY v R ⊆ range (j ∘ E.ι)) :
    φ '' spearIntY v R ⊆ range j := by
  classical
  haveI : ConnectedSpace E.N := BTZMax.connectedSpace_N E
  have hjr : IsOpen (range j) := (isOpenMap_of_isE0Mor hjm).isOpen_range
  have hOo : IsOpen {x : E0 | v < fcoord x ∧ rad x < R} :=
    (isOpen_lt continuous_const continuous_fcoord).inter (isOpen_lt continuous_rad continuous_const)
  have hO : IsOpen (spearIntY v R) := isOpen_paperInY_image hOo
  have hOW : spearIntY v R ⊆ W := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    exact hsub ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
  have hA : IsOpen (φ '' spearIntY v R) :=
    (isEMorphismOn_of_isE0Mor (W := ⟨W, hW⟩) hφ).isOpen_image ⟨_, hO⟩ hOW
  have hZo : IsOpen (range j ∪ φ '' spearIntY v R) := hjr.union hA
  set Z : Opens Y := ⟨range j ∪ φ '' spearIntY v R, hZo⟩ with hZdef
  -- the points of `Z` outside `M₁` are BTZ: they are on the axis of the spear
  have hZS0 : ∀ y ∈ (Z : Set Y), y ∉ range j → y ∈ S0 Y := by
    rintro y (hy | ⟨_, ⟨e, he, rfl⟩, rfl⟩) hyj
    · exact absurd hy hyj
    · by_cases hr : rad e = 0
      · refine (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem hW hφ
          (hOW ⟨e, he, rfl⟩) le_rfl).1 ?_
        show chartAt E0Y (paperInY e) (paperInY e) ∈ e0SingY 0
        rw [chartAt_self_eq]
        have he2 : e.2 = 0 := rad_eq_zero.1 hr
        have : paperInY e = yAxis 0 e.1 := by
          simp only [yAxis, zero_add]
          congr 1
          exact Prod.ext rfl he2
        rw [this]
        exact yAxis_mem_e0SingY 0 e.1
      · exact absurd (range_comp_subset_range _ _ (hreg ⟨paperInY e, ⟨e, ⟨he.1.le,
          lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr), he.2.le⟩, rfl⟩, rfl⟩)) hyj
  -- `M₁ ∪ Int(S)` as a globally hyperbolic BTZ-extension of `M₀`
  have hGZ : (CE Z).GloballyHyperbolic := by
    rw [ce_opens_eq]
    exact Causal.Causality.globallyHyperbolic_toSubtype
      (globallyHyperbolicOn_union hj hjm hR hW hsub hφ hinj
        (hreg.trans (range_comp_subset_range _ _)) hZo)
  let ι' : E.N → Z := fun x => ⟨j x, Or.inl ⟨x, rfl⟩⟩
  have hι'm : IsE0Mor ι' univ := (isE0Mor_corestrict_iff (U := Z) ι' univ).1 hjm
  have hι' : IsBTZEmbedding ι' := by
    refine isBTZEmbedding_iff_injective.2 ⟨fun a b h => hj.injective (congrArg Subtype.val h),
      hι'm, fun z hz => ?_⟩
    refine (mem_S0_iff_of_isE0Mor (isE0Mor_val Z) z).1 (hZS0 z z.2 ?_)
    rintro ⟨x, hx⟩
    exact hz ⟨x, Subtype.ext hx⟩
  let X' : BTZMax.GHExt (FlatE0 N) := ⟨E0Mfd.of Z, ι' ∘ E.ι, hι'.comp E.isBTZ, hGZ⟩
  obtain ⟨-, g, -, -, hgι⟩ := BTZMax.isInextensible_of_isMaximal hE X' ι' ⟨hι', rfl⟩
  intro y hy
  have h1 := congrFun hgι (⟨y, Or.inr hy⟩ : Z)
  exact ⟨g ⟨y, Or.inr hy⟩, congrArg Subtype.val h1⟩

/-- **The spear of `M₁`** (`BTZ_1.tex:1604`, « Therefore, every BTZ-line of `M₁` admits a spear
neighborhood »): a spear of `M₂` whose interior lies in `M₁` gives a spear neighbourhood in `M₁`
around the same BTZ line. -/
theorem exists_spearNbhd_of_subset {X Y : Type} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace E0Y X] [HasGroupoid X e0Groupoid]
    [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [SecondCountableTopology Y]
    [ChartedSpace E0Y Y] [HasGroupoid Y e0Groupoid] {j : X → Y}
    (hj : Causal.IsCauchyEmbedding (CE X) (CE Y) j) (hjm : IsE0Mor j univ)
    {p : X} {v R v' R' : ℝ} {W : Set E0Y} {φ : E0Y → Y} (hR : 0 < R) (hW : IsOpen W)
    (hsub : spearY v R ⊆ W) (hφ : IsE0Mor φ W) (hinj : InjOn φ W) (hv : φ (yVertex v) = j p)
    (hvv : v ≤ v') (hR' : 0 < R') (hRR : R' ≤ R) (hint : φ '' spearIntY v' R' ⊆ range j) :
    ∃ q ∈ connectedComponentIn (S0 X) p, ∃ R'' U, IsSpearNbhd q R'' U := by
  classical
  haveI : Nonempty X := ⟨p⟩
  set ji : Y → X := invFunOn j univ with hjidef
  have hjinv : IsE0Mor ji (range j) := by
    have := Causal.CBG.liftPropOn_invFunOn isOpen_univ hjm hj.injective.injOn
    rwa [image_univ] at this
  have hjr : IsOpen (range j) := (isOpenMap_of_isE0Mor hjm).isOpen_range
  have hji : ∀ y ∈ range j, j (ji y) = y := by
    rintro y ⟨x, rfl⟩
    exact invFunOn_eq ⟨x, mem_univ _, rfl⟩
  have hjij : ∀ x, ji (j x) = x := fun x => hj.injective.injOn.leftInvOn_invFunOn (mem_univ x)
  -- the interior of the sub-spear, and a smaller spear inside it
  have hOo : IsOpen {x : E0 | v' < fcoord x ∧ rad x < R'} :=
    (isOpen_lt continuous_const continuous_fcoord).inter (isOpen_lt continuous_rad continuous_const)
  have hO : IsOpen (spearIntY v' R') := isOpen_paperInY_image hOo
  have hOW : spearIntY v' R' ⊆ W := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    exact hsub ⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
  have hsp : spearY (v' + 1) (R' / 2) ⊆ spearIntY v' R' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
  have hψ : IsE0Mor (ji ∘ φ) (spearIntY v' R') :=
    Causal.CBG.liftPropOn_comp hO hjr hjinv (Causal.CBG.liftPropOn_mono_of_le hW hO hφ hOW)
      (fun y hy => hint ⟨y, hy, rfl⟩)
  have hψinj : InjOn (ji ∘ φ) (spearIntY v' R') := by
    intro a ha b hb hab
    have h1 := congrArg j hab
    simp only [comp_apply] at h1
    rw [hji _ (hint ⟨a, ha, rfl⟩), hji _ (hint ⟨b, hb, rfl⟩)] at h1
    exact hinj (hOW ha) (hOW hb) h1
  have hGX : (CE X).GloballyHyperbolic := hj.globallyHyperbolic_source
  refine ⟨ji (φ (yVertex (v' + 1))), ?_, R' / 2, _, IsSpearNbhd.of_chart hGX (by positivity)
    ⟨v' + 1, spearIntY v' R', ji ∘ φ, hO, hsp, hψ, hψinj, rfl, rfl⟩⟩
  -- the axis segment from `p` to the new vertex lies in `range j`, in `sing₀`
  have hray : IsFullFutureBTZRay (j p) (fun t => φ (yAxis v t)) :=
    ⟨v, W, φ, hW, fun t ht => hsub (yAxis_mem_spearY hR.le ht), hφ, hinj, hv, fun _ => rfl⟩
  set T : ℝ := v' + 1 - v with hTdef
  have hT : 0 ≤ T := by rw [hTdef]; linarith
  have hend : φ (yAxis v T) = φ (yVertex (v' + 1)) := by
    congr 1
    simp [yAxis, yVertex, vertex, hTdef]
  have hconv := causallyConvexIn_range hj
  have hmemj : ∀ t ∈ Icc (0 : ℝ) T, φ (yAxis v t) ∈ range j := by
    intro t ht
    have hTj : φ (yAxis v T) ∈ range j := by
      rw [hend]
      refine hint ⟨_, ⟨((v' + 1, 0) : E0), ⟨?_, ?_⟩, rfl⟩, rfl⟩
      · have h0 : rad (((v' + 1, 0) : E0)) = 0 := rad_eq_zero.2 rfl
        simp only [fcoord, h0]; linarith
      · rw [rad_eq_zero.2 rfl]; exact hR'
    refine hconv.2 (j p) ⟨p, rfl⟩ _ hTj
      (Causal.Causality.mem_diamond.2 ⟨?_, hray.le ht.1 ht.2⟩)
    have := hray.le le_rfl ht.1
    simpa [yAxis_zero, hv] using this
  have hS0 : ∀ t ∈ Icc (0 : ℝ) T, ji (φ (yAxis v t)) ∈ S0 X := by
    intro t ht
    rw [← mem_S0_iff_of_isE0Mor hjm, hji _ (hmemj t ht)]
    exact hray.mem_S0 ht.1
  have hcont : ContinuousOn (fun t => ji (φ (yAxis v t))) (Icc 0 T) := by
    have h1 : ContinuousOn ji (range j) := fun y hy => (hjinv y hy).continuousWithinAt
    exact h1.comp (hray.continuousOn.mono Icc_subset_Ici_self) (fun t ht => hmemj t ht)
  have hpc : IsPreconnected ((fun t => ji (φ (yAxis v t))) '' Icc 0 T) :=
    isPreconnected_Icc.image _ hcont
  have hp0 : p ∈ (fun t => ji (φ (yAxis v t))) '' Icc 0 T :=
    ⟨0, ⟨le_rfl, hT⟩, by simp only [yAxis_zero, hv, hjij]⟩
  have hsubc := hpc.subset_connectedComponentIn hp0 (by rintro _ ⟨t, ht, rfl⟩; exact hS0 t ht)
  refine hsubc ⟨T, ⟨hT, le_rfl⟩, ?_⟩
  show ji (φ (yAxis v T)) = ji (φ (yVertex (v' + 1)))
  rw [hend]

/-! ### §3 Step 1 -/

/-- **`theo:BTZ_Cauchy-completness`, Step 1** (`BTZ_1.tex:1595–1604`). -/
theorem cauchy_spear (hmax : Causal.Flat.MGH N) (hcc : Causal.Flat.IsCauchyComplete 2 N)
    (E : BTZMax.GHExt (FlatE0 N))
    (hE : Causal.AbstractDev.IsMaximal (carrier := fun X : BTZMax.GHExt (FlatE0 N) => (X.N : Type))
      (BTZMax.extMor (FlatE0 N)) E)
    {p : E.N} (hp : p ∈ S0 E.N) :
    ∃ q ∈ connectedComponentIn (S0 E.N) p, ∃ R U, IsSpearNbhd q R U := by
  haveI : ConnectedSpace E.N := BTZMax.connectedSpace_N E
  -- `M₂`, the Cauchy-maximal extension of `M₁` (CBG)
  obtain ⟨Y, hYc, j, hj, hjm, hY⟩ := exists_cauchyMaximalExt E.gh
  have hGY := hj.globallyHyperbolic_target
  have hjp : j p ∈ S0 Y := (mem_S0_iff_of_isE0Mor hjm p).2 hp
  -- `lem:tube` in `M₂`
  obtain ⟨R, U, hU⟩ := lem_tube_e0 hGY hY hjp
  obtain ⟨v, W, φ, hW, hsub, hφ, hinj, hv, -⟩ := hU.chart
  -- the blunt sub-spear in `M₀` (Cauchy-maximality and completeness of `M₀`)
  obtain ⟨v', R', hvv, hR', hRR, hreg⟩ :=
    bluntSpear_subset_M0 hmax hcc E hj hjm hp hU.pos hW hsub hφ hinj hv
  have hsub' : spearY v' R' ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsub ⟨x, ⟨hvv.trans hx.1, hx.2.trans hRR⟩, rfl⟩
  -- BTZ-maximality of `M₁`
  have hint := spearInt_subset_range E hE hj hjm hR' hW hsub' hφ hinj hreg
  exact exists_spearNbhd_of_subset hj hjm hU.pos hW hsub hφ hinj hv hvv hR' hRR hint

end BTZCauchySpear

end GX
