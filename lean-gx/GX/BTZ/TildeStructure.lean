import GX.BTZ.Manifolds

/-!
# `GX.BTZ.TildeStructure` — `(\widetilde M, T_BTZ)` is a singular `(G,X)`-manifold, a `\widetilde{𝔼₀}`-manifold

Package WP-48b (DEC-130, 2026-11-08: "Full structure"). `papers/gx`, `RamcovGX.tex:2308–2310`.
**0 `sorry`.** `G = Isom(𝐌³) = Causal.Flat.isom 2`, `X = Causal.Minkowski 2` (DEC-33: qualified,
never opened).

* **`prop:manifold_admits_galoisian_maximal`** — `RamcovGX.tex:2308`, under DEC-130 (the
  `\widetilde{BTZ}`-manifold clause) and DEC-118 (c) (the chartwise construction of
  `\widetilde M`): `GX.btz_manifold_galoisian_maximal_full` (and `GX.btz_xaManifold_galoisian_maximal_full`
  for `IsXAManifold`). The certificate spans `GX.BTZ.VirtTame` — Galoisian and exactly branched
  (`GX.btz_manifold_galoisian_maximal`, `GX.btz_manifold_isGaloisian`,
  `GX.btz_manifold_sing_subset_branchingLocus`), the presentation `GX.btz_exists_presentation` —
  `GX.BTZ.Manifolds` (the chartwise tamifying `T_BTZ`, `GX.btz_manifold_exists_chartwise_tamifying_reg`,
  `GX.isLocallyBTZTilde_of_chartwise`, the datum `GX.BTZTildeData`) and this file: **the full
  singular `(G,X)`-structure on `(\widetilde M, T_BTZ)`** `GX.BTZTildeData.singularGXStructure`
  (DEC-25 maximal a.e. atlas) which is the pulled-back flat structure `p^*B`
  (`GX.BTZTildeData.aeAtlas_space`, `GX.BTZTildeData.isAEMorphism_proj`), whose regular locus is
  `p⁻¹(reg M)` (`GX.BTZTildeData.reg_space`), developed by `D`
  (`GX.BTZTildeData.isAEMorphismOf_dev`), and whose singular points are centres of
  `\widetilde{𝔼₀}`-charts (`def:atlas` over the model family `GX.btzTildeFam`,
  `GX.BTZTildeData.hasXAType_of_mem_sing`, `GX.IsBTZTildeSingModelled`); Hausdorff, locally
  path-connected, first countable, connected (`BTZTildeData.Space`'s instances).

> Let $M$ be a $\mass{0}$-manifold, then $M$ admits a Galoisian maximal covering exactly branched
> above $\sing(M)$ and admits a developing map continuous for the tamifying topology $\T_{BTZ}$.
> Furthermore, $\widetilde M$ is a $\BTZtilde$-manifold. (l.2308–2310)
>
> Consider $M$ a $\mass{0}$-manifold, ie a singular $\mass{}$-manifold whose singular locus is
> locally modelled on $\mass{0}$. (l.2300)

## What is built

* The model: `\widetilde{𝔼₀}` with `T_BTZ = Φ^* hornTop` (`GX.BTZTildeTB Φ`), as the datum
  `GX.btzTildeModel` over `𝔼₀` itself (lifted chart: the identity, `GX.btzTilde_isLocallyBTZTilde`),
  so it receives the same structure; it is an `X_A`-manifold over `{\widetilde{𝔼₀}}` in the full
  DEC-67 (e) sense (`GX.btzTildeModel_isXAManifold`), with non-empty `S = sing` (`GX.btzTildeFamS_nonempty`).
* For every datum `d : BTZTildeData M y₀ Φ` (a topology `T'` finer than the natural one, natural
  over `reg M`, a `T'`-continuous `D`, the lifted charts): `p⁻¹(reg M)` is `T'`-portly
  (`GX.BTZTildeData.isPortly_regSpace`), `p` is a local homeomorphism there
  (`GX.BTZTildeData.isLocalHomeomorphOn_proj`), so `p^*B` exists (`lem:aepullback`) and is the
  structure. **No point over `sing M` becomes regular for `T'`**: a chart there would make `D`, on
  a lifted chart, one translate of the chart (`GX.exists_smul_eq_on_of_isPreconnected`, density and
  `T'`-continuity), so `D(U)` would be open around a point of the BTZ line inside `g · J⁺(Δ)`
  (`GX.btzDevM_range_notMem_nhds`). A lifted chart, inverted, is an `\widetilde{𝔼₀}`-chart: a
  homeomorphism (continuous and open, `T_BTZ` to `T'`), an a.e. morphism because it intertwines two
  chart-developing maps (`GX.isAEMorphism_of_developsCharts`, `GX.DevelopsCharts`).

## Hypothesis checklist

| paper | here |
|---|---|
| `M` an `𝔼₀`-manifold (l.2308, l.2300) | ⚠ weakened: `IsBTZSingModelled` (every singular point centred in an `𝔼₀`-chart); `IsXAManifold` (DEC-67 (e)) implies it, corollary `btz_xaManifold_galoisian_maximal_full` |
| standing: `M` Hausdorff, LPC, first countable, connected (DEC-66) | ✓ carried |
| "a developing map continuous for the tamifying topology `T_BTZ`" (l.2309) | ✓ read (DEC-118 (c), the chartwise construction of `\widetilde M`): `T'` tamifying, its neighbourhoods at every lifted descending `𝔼₀`-chart the images of `T_BTZ`-ones, `D` `T'`-continuous; every base point, every presentation |
| "`\widetilde M` is a `\widetilde{BTZ}`-manifold" (l.2310) | ✓ ruled (DEC-130): a full singular `(G,X)`-structure on `(\widetilde M, T_BTZ)` (pullback `p^*B`, `Reg = p⁻¹(reg M)`), every singular point the centre of a `\widetilde{𝔼₀}`-chart (`IsBTZTildeSingModelled`) |

## SCOPE (disclosed)

* **(a)** "`\widetilde{BTZ}`-manifold" is read as the paper reads "`𝔼₀`-manifold" (l.2300) and as
  the hypothesis is formalized (`IsBTZSingModelled`): every singular point has a
  `\widetilde{𝔼₀}`-chart — the `hasType` clause of DEC-67 (e). Its atlas clause (every point,
  regular ones included, in the domain of a `\widetilde{𝔼₀}`-chart) is neither assumed of `M`
  nor proved of `\widetilde M`; it is proved for the model (`btzTildeModel_isXAManifold`).
* **(b)** The model `\widetilde{𝔼₀}` depends on the presentation `Φ` (base point `yN`); the
  analyticity of the one-member family `{\widetilde{𝔼₀}}` (`def:family_singular_manifolds_endowed`)
  is not used and not proved.
* **(c)** Second countability of `\widetilde M` (README's singular `(G,X)`-manifold) is not proved;
  the DEC-66 standing set (Hausdorff, LPC, first countable, connected) is.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

universe v

attribute [local instance] btzE0Structure

set_option linter.unusedSectionVars false

/-! ### Rigidity of a chart against a developing map -/

section DevChart

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]

/-- `F` *develops the charts* of a singular `(G,X)`-manifold `P`: near every point of the source
of every chart `c` of the maximal a.e. atlas, `F` is a translate `k • c`. -/
def DevelopsCharts (P : Type*) [TopologicalSpace P] [SingularGXStructure G X P] (F : P → X) :
    Prop :=
  ∀ c ∈ aeAtlas G X P, ∀ z ∈ c.source, ∃ k : G, ∀ᶠ y in 𝓝 z, F y = k • c y

/-- A map developing the charts of `P` develops those of an open subset `U ⊆ P` (with its induced
structure, the pullback along the inclusion). -/
theorem DevelopsCharts.opens {P : Type*} [TopologicalSpace P] [SingularGXStructure G X P]
    {F : P → X} (hF : DevelopsCharts (G := G) P F) (U : Opens P) :
    DevelopsCharts (G := G) U (F ∘ Subtype.val) := by
  intro c hc z hz
  have hBU := isMaximalAEAtlas_aeAtlas G X U
  have hBP := isMaximalAEAtlas_aeAtlas G X P
  have hval := isAEMorphism_opensSingular_val (G := G) (X := X) U
  have hzU : z ∈ Reg G X U := mem_support.2 ⟨c, hc, hz⟩
  have hzP : (z : P) ∈ Reg G X P := by
    have := hzU; rw [reg_opensSingular] at this; exact this
  obtain ⟨c₀, hc₀, hzc₀⟩ := mem_support.1 hzP
  have hzR : z ∈ regLocusOf G (aeAtlas G X U) (aeAtlas G X P) (Subtype.val : U → P) := by
    rw [IsAEMorphismOf.regLocusOf_eq hBU.1 hBP.1 hval]; exact ⟨hzU, hzP⟩
  obtain ⟨h, hh⟩ := (isRegularOn_regLocusOf (G := G) (aeAtlas G X U) (aeAtlas G X P)
    (Subtype.val : U → P)).exists_smul_eq z hzR c hc c₀ hc₀ hz hzc₀
  obtain ⟨k, hk⟩ := hF c₀ hc₀ (z : P) hzc₀
  refine ⟨k * h, ?_⟩
  filter_upwards [hh, continuous_subtype_val.continuousAt.eventually hk] with y h1 h2
  simp only [comp_apply] at h2 ⊢
  rw [h2, h1, mul_smul]

/-- A continuous map developing the charts of `P` is an a.e. `(G,X)`-morphism into `X` (a
developing map of `P`). -/
theorem DevelopsCharts.isAEMorphismOf {P : Type*} [TopologicalSpace P] [SingularGXStructure G X P]
    {F : P → X} (hF : DevelopsCharts (G := G) P F) (hc : Continuous F) :
    IsAEMorphismOf G (aeAtlas G X P) (gxModelAtlas G X) F := by
  have hB := isMaximalAEAtlas_aeAtlas G X P
  have hM := isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)
  refine (isAEMorphismOf_iff hM.1).2 ⟨hc, Reg G X P, isPortly_reg G X P,
    IsRegularOn.of_exists hB.1.1 hM.1.1 (isOpen_reg G X P) subset_rfl
      (fun _ _ => by rw [support_gxModelAtlas]; trivial) hc.continuousOn fun x hx => ?_⟩
  obtain ⟨c, hc', hxc⟩ := mem_support.1 hx
  obtain ⟨k, hk⟩ := hF c hc' x hxc
  exact ⟨c, hc', _, refl_mem_gxModelAtlas, hxc, mem_univ _, k, hk⟩

/-- **A map intertwining two chart-developing maps is an a.e. `(G,X)`-morphism**: if `F`, `F'`
develop the charts of `P`, `N`, and `f : P → N` is continuous, maps `Reg P` into `Reg N` and
satisfies `F = g • F' ∘ f`, then `f` read in charts is locally an element of `G`. -/
theorem isAEMorphism_of_developsCharts {P : Type*} [TopologicalSpace P] [SingularGXStructure G X P]
    {N : Type*} [TopologicalSpace N] [SingularGXStructure G X N] {F : P → X} {F' : N → X}
    (hF : DevelopsCharts (G := G) P F) (hF' : DevelopsCharts (G := G) N F') {f : P → N}
    (hf : Continuous f) (hreg : MapsTo f (Reg G X P) (Reg G X N)) (g : G)
    (hfg : ∀ y, F y = g • F' (f y)) : IsAEMorphism G X f := by
  have hBN := isMaximalAEAtlas_aeAtlas G X N
  refine (isAEMorphismOf_iff hBN.1).2 ⟨hf, Reg G X P, isPortly_reg G X P,
    ⟨isOpen_reg G X P, subset_rfl, hreg, hf.continuousOn, fun x _ e he e' he' hxe hfxe' => ?_⟩⟩
  obtain ⟨k, hk⟩ := hF e he x hxe
  obtain ⟨k', hk'⟩ := hF' e' he' (f x) hfxe'
  refine ⟨k'⁻¹ * g⁻¹ * k, ?_⟩
  filter_upwards [hk, hf.continuousAt.eventually hk'] with y h1 h2
  rw [mul_smul, mul_smul, ← h1, hfg y, inv_smul_smul, h2, inv_smul_smul]

end DevChart


/-! ### The model `\widetilde{𝔼₀}` with `T_BTZ` -/

section Model

/-- **`\widetilde{𝔼₀}` with the BTZ topology** `T_BTZ = Φ^* hornTop` (`Φ` a presentation of
`\widetilde{𝔼₀}` on the cylinder `𝔻_∞ × ℝ`), as a type carrying it as its instance. -/
abbrev BTZTildeTB {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
    (Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
      DInfty × ℝ) : Type :=
  WithWrappedTop (⟨TopologicalSpace.induced Φ hornTop⟩ :
    WrappedTop (MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN))

/-- **No neighbourhood of a point of the BTZ line lies in the image `J⁺(Δ)` of `D`**: the points
`t u − ε (0,1,0)` (null coordinates), `ε > 0`, tend to `t u` and are not in `D(\widetilde{𝔼₀})`. -/
theorem btzDevM_range_notMem_nhds (t : ℝ) :
    range (btzDevM 0 btzV0) ∉ 𝓝 (btzDevM 0 btzV0 (DInfty.apex, t)) := by
  intro h
  set γ : ℝ → ℝ × ℝ × ℝ := fun ε => (0 : ℝ × ℝ × ℝ) + t • nullU + ((0 : ℝ), -ε, (0 : ℝ))
  have hγc : Continuous γ := by fun_prop
  have hγ0 : nullToMink (γ 0) = btzDevM 0 btzV0 (DInfty.apex, t) := by
    rw [btzDevM_apex]; simp [γ]
  have hc : Continuous (fun ε => nullToMink (γ ε)) :=
    nullToMinkHomeomorph.continuous.comp hγc
  have h' : (fun ε => nullToMink (γ ε)) ⁻¹' range (btzDevM 0 btzV0) ∈ 𝓝 (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [hγ0]; exact h
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 h'
  have hmem : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]; linarith
  obtain ⟨z, hz⟩ := hball hmem
  have hz' : btzDev 0 btzV0 z = γ (r / 2) := nullToMink.injective hz
  have hrange : γ (r / 2) ∈ range (btzDev 0 btzV0) := ⟨z, hz'⟩
  rw [range_btzDev 0 btzV0_pos] at hrange
  rcases hrange with h1 | ⟨s, hs⟩
  · simp only [mem_setOf_eq, γ, nullU] at h1
    simp at h1
    linarith
  · have := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hs
    simp only [γ, nullU] at this
    simp at this
    linarith

variable {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}

/-- A singular point of `\widetilde{𝔼₀}` sits on the axis of the presentation. -/
theorem btzTilde_apex_of_sing (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base)
    {w : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN}
    (hw : w.base ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) :
    (Φ w).1 = DInfty.apex := by
  have key : ∀ (k : GammaA (2 * π)) (y : DInfty × ℝ), y.1 = DInfty.apex → k • y = y := by
    rintro k ⟨p, t⟩ hp
    simp only at hp
    subst hp
    rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_apex]
  have hs' : orbitMk (GammaA (2 * π)) (Φ w) ∈
      orbitMk (GammaA (2 * π)) '' {x : DInfty × ℝ | x.1 = DInfty.apex} := by
    rw [← btz_sing btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0, hΦ w]; exact hw
  obtain ⟨x, hx, hxe⟩ := hs'
  obtain ⟨k, hk⟩ := exists_smul_eq_of_orbitMk_eq hxe
  rw [← hk, key k x hx]; exact hx

/-- The developing map of a singular point of `\widetilde{𝔼₀}` lies on the BTZ line, and no
neighbourhood of it lies in `D(\widetilde{𝔼₀})`. -/
theorem btzTilde_range_notMem_nhds_of_sing (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base)
    {w : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN}
    (hw : w.base ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) :
    range (btzDevM 0 btzV0) ∉ 𝓝 (btzDevM 0 btzV0 (Φ w)) := by
  have h := btzTilde_apex_of_sing hΦ hw
  have hΦw : Φ w = (DInfty.apex, (Φ w).2) := Prod.ext h rfl
  rw [hΦw]
  exact btzDevM_range_notMem_nhds _

/-- `T_BTZ` is a tamifying topology of `\widetilde{𝔼₀}` (`btz_isTamifyingTopology`), read on
`BTZTildeTB Φ`. -/
theorem btzTildeTB_isTamifying (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    IsTamifyingTopology (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 yN
      (TopologicalSpace.induced Φ hornTop) :=
  btz_isTamifyingTopology btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0 hΦ

end Model


/-! ### The singular `(G,X)`-structure of `(\widetilde M, T')` -/

section TildeStructure

variable {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]

namespace BTZTildeData

variable {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
  {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}
  (d : BTZTildeData M y₀ Φ)

/-- `reg M` is semi-locally simply connected (`𝐌³` is locally unloopable). -/
theorem slsc_compl_sing :
    SemilocallySimplyConnected ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M) :=
  semilocallySimplyConnected_compl_of_sing_subset (G := Causal.Flat.isom 2)
    (isLocallyUnloopable_of_normedSpace (Causal.Minkowski 2))
    (isClosed_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) subset_rfl

/-- The regular part `p⁻¹(reg M)` of `(\widetilde M, T')`. -/
def regSpace : Set d.Space := d.proj ⁻¹' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M

theorem mem_regSpace_iff {x : d.Space} :
    x ∈ d.regSpace ↔ d.proj x ∉ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M := by
  rw [regSpace, mem_preimage, Sing, mem_compl_iff, not_not]

theorem isOpen_regSpace : IsOpen d.regSpace :=
  (isOpen_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M).preimage d.continuous_proj

/-- The identity from the natural topology to `T'` is continuous over `reg M`. -/
theorem continuousOn_fromNat
    {S : Set (MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀)}
    (hSR : ∀ z ∈ S, z.base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M) :
    ContinuousOn d.fromNat S := fun z hz => by
  refine ContinuousAt.continuousWithinAt ?_
  unfold ContinuousAt
  have h := d.nhds_reg z (hSR z hz)
  have h' : (𝓝 (d.fromNat z) : Filter d.Space) =
      @nhds _ (weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀) z := h
  rw [h']
  exact fun s hs => hs

/-- A naturally preconnected set over `reg M` is preconnected in `(\widetilde M, T')` (the two
topologies have the same neighbourhoods there). -/
theorem isPreconnected_of_nat
    {S : Set (MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀)}
    (hS : IsPreconnected S)
    (hSR : ∀ z ∈ S, z.base ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M) :
    IsPreconnected (d.toNat ⁻¹' S) := by
  have hcont : ContinuousOn d.fromNat S := fun z hz => by
    refine ContinuousAt.continuousWithinAt ?_
    unfold ContinuousAt
    have h := d.nhds_reg z (hSR z hz)
    have h' : (𝓝 (d.fromNat z) : Filter d.Space) =
        @nhds _ (weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀) z := h
    rw [h']
    exact fun s hs => hs
  have h := hS.image d.fromNat hcont
  have heq : d.fromNat '' S = d.toNat ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hz; exact ⟨z, hz, rfl⟩
  rwa [heq] at h

/-- **The lifted chart at a singular point**, in the form used below (`GX.IsLocallyBTZTilde`): an
open `V ⊆ \widetilde{𝔼₀}` (`T_BTZ`), an open `U ∋ x` of `(\widetilde M, T')`, a bijection
`Ψ : V → U` with `Ψ v = x` mapping `T_BTZ`-neighbourhoods onto neighbourhoods, preserving the
singular loci, with `D ∘ Ψ = g · D_{𝔼₀}`. -/
theorem exists_lifted (x : d.Space)
    (hx : d.proj x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) :
    ∃ (V : Set (BTZTildeTB Φ)) (U : Set d.Space) (Ψ : BTZTildeTB Φ → d.Space) (v : BTZTildeTB Φ)
      (g : Causal.Flat.isom 2),
      IsOpen V ∧ IsOpen U ∧ v ∈ V ∧ Ψ v = x ∧ BijOn Ψ V U ∧
      (∀ w ∈ V, 𝓝 (Ψ w) = Filter.map Ψ (𝓝 w)) ∧
      (∀ w ∈ V, (d.proj (Ψ w) ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M ↔
        SpreadEnd.base w ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)) ∧
      (∀ w ∈ V, d.D (Ψ w) = g • btzDevM 0 btzV0 (Φ w)) := by
  obtain ⟨c, f, Ψ, -, -, -, hVoB, -, hUoT, hbij, -, hsing, -, hT'n, g, hg⟩ :=
    d.isLocallyBTZTilde (d.toNat x) hx
  obtain ⟨v, hv, hvx⟩ := hbij.surjOn (mem_connectedComponentIn (x := d.toNat x)
    (F := (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
      y₀ → M) ⁻¹' (c.U : Set M)) c.mem)
  exact ⟨_, _, Ψ, v, g, hVoB, hUoT, hv, hvx, hbij, hT'n, hsing, hg⟩

/-- The lifted chart at a singular point, cut down inside a given open `O ∋ x`, with `V`
(`T_BTZ`-)preconnected. -/
theorem exists_lifted_in (x : d.Space)
    (hx : d.proj x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) {O : Set d.Space}
    (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ (V : Set (BTZTildeTB Φ)) (U : Set d.Space) (Ψ : BTZTildeTB Φ → d.Space) (v : BTZTildeTB Φ)
      (g : Causal.Flat.isom 2),
      IsOpen V ∧ IsPreconnected V ∧ IsOpen U ∧ U ⊆ O ∧ v ∈ V ∧ Ψ v = x ∧ BijOn Ψ V U ∧
      (∀ w ∈ V, 𝓝 (Ψ w) = Filter.map Ψ (𝓝 w)) ∧
      (∀ w ∈ V, (d.proj (Ψ w) ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M ↔
        SpreadEnd.base w ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)) ∧
      (∀ w ∈ V, d.D (Ψ w) = g • btzDevM 0 btzV0 (Φ w)) := by
  obtain ⟨V, U, Ψ, v, g, hV, -, hv, hvx, hbij, hn, hs, hD⟩ := d.exists_lifted x hx
  haveI : LocPathConnectedSpace (BTZTildeTB Φ) :=
    (btzTildeTB_isTamifying d.isPresentation).locPathConnected
  set W : Set (BTZTildeTB Φ) := V ∩ Ψ ⁻¹' O with hWdef
  have hW : IsOpen W := isOpen_iff_mem_nhds.2 fun w hw => inter_mem (hV.mem_nhds hw.1) (by
    have h1 : O ∈ 𝓝 (Ψ w) := hO.mem_nhds hw.2
    rw [hn w hw.1] at h1; exact h1)
  have hvW : v ∈ W := ⟨hv, by rw [mem_preimage, hvx]; exact hxO⟩
  set V' := connectedComponentIn W v with hV'def
  have hV'W : V' ⊆ W := connectedComponentIn_subset _ _
  have hV'o : IsOpen V' := hW.connectedComponentIn
  refine ⟨V', Ψ '' V', Ψ, v, g, hV'o, isPreconnected_connectedComponentIn, ?_, ?_,
    mem_connectedComponentIn hvW, hvx,
    (hbij.injOn.mono (hV'W.trans inter_subset_left)).bijOn_image,
    fun w hw => hn w (hV'W hw).1, fun w hw => hs w (hV'W hw).1, fun w hw => hD w (hV'W hw).1⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨w, hw, rfl⟩
    rw [hn w (hV'W hw).1]
    exact mem_map.2 (mem_of_superset (hV'o.mem_nhds hw) (subset_preimage_image _ _))
  · rintro _ ⟨w, hw, rfl⟩; exact (hV'W hw).2

/-- `Ψ` is continuous on `V` (`T_BTZ` to `T'`). -/
theorem continuousOn_of_nhds_eq {V : Set (BTZTildeTB Φ)} {Ψ : BTZTildeTB Φ → d.Space}
    (hn : ∀ w ∈ V, 𝓝 (Ψ w) = Filter.map Ψ (𝓝 w)) : ContinuousOn Ψ V := fun w hw => by
  refine ContinuousAt.continuousWithinAt ?_
  unfold ContinuousAt
  rw [hn w hw]
  exact tendsto_map

/-- The regular part of the image of a preconnected lifted chart is preconnected (the regular
part of `\widetilde{𝔼₀}` is `T_BTZ`-portly). -/
theorem isPreconnected_image_inter_regSpace {V : Set (BTZTildeTB Φ)} {Ψ : BTZTildeTB Φ → d.Space}
    (hV : IsOpen V) (hVc : IsPreconnected V) (hn : ∀ w ∈ V, 𝓝 (Ψ w) = Filter.map Ψ (𝓝 w))
    (hs : ∀ w ∈ V, (d.proj (Ψ w) ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M ↔
        SpreadEnd.base w ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)) :
    IsPreconnected (Ψ '' V ∩ d.regSpace) := by
  have hTN := btzTildeTB_isTamifying d.isPresentation
  set RE : Set (BTZTildeTB Φ) := {w | SpreadEnd.base w ∈
    Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0} with hREdef
  have hP : IsPortly RE := @IsPortly.mk _ (TopologicalSpace.induced Φ hornTop) _
    (@IsPortly.isOpen _ (TopologicalSpace.induced Φ hornTop) _ hTN.isPortly)
    (@IsPortly.dense _ (TopologicalSpace.induced Φ hornTop) _ hTN.isPortly)
    (@IsPortly.locallyConnectedIn _ (TopologicalSpace.induced Φ hornTop) _ hTN.isPortly)
  have hVR : IsPreconnected (V ∩ RE) := hP.locallyConnectedIn V hV hVc
  have heq : Ψ '' V ∩ d.regSpace = Ψ '' (V ∩ RE) := by
    ext y
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hy⟩
      refine ⟨w, ⟨hw, ?_⟩, rfl⟩
      have h1 := (d.mem_regSpace_iff).1 hy
      have h2 : SpreadEnd.base w ∉ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
        fun h => h1 ((hs w hw).2 h)
      show SpreadEnd.base w ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
      simpa [Sing] using h2
    · rintro ⟨w, ⟨hw, hwR⟩, rfl⟩
      refine ⟨⟨w, hw, rfl⟩, (d.mem_regSpace_iff).2 fun h => ?_⟩
      have h2 := (hs w hw).1 h
      exact h2 hwR
  rw [heq]
  exact hVR.image Ψ ((d.continuousOn_of_nhds_eq hn).mono inter_subset_left)

/-- **`p⁻¹(reg M)` is portly in `(\widetilde M, T')`**: open, dense (a lifted chart carries the
`T_BTZ`-dense regular part of `\widetilde{𝔼₀}` onto regular points) and locally connected in
(naturally over `reg M`, through the lifted charts over `sing M`). -/
theorem isPortly_regSpace : IsPortly d.regSpace := by
  have hTN := btzTildeTB_isTamifying d.isPresentation
  have hdense : Dense d.regSpace := by
    intro x
    by_cases hx : d.proj x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M
    · obtain ⟨V, U, Ψ, v, g, hV, -, hv, hvx, -, hn, hs, -⟩ := d.exists_lifted x hx
      rw [mem_closure_iff_nhds]
      intro t ht
      rw [← hvx, hn v hv] at ht
      have h1 : Ψ ⁻¹' t ∩ V ∈ 𝓝 v := inter_mem ht (hV.mem_nhds hv)
      have hd : Dense {w : BTZTildeTB Φ | SpreadEnd.base w ∈
          Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0} :=
        @IsPortly.dense _ (TopologicalSpace.induced Φ hornTop) _ hTN.isPortly
      obtain ⟨w, hwR, hwt, hwV⟩ := hd.inter_nhds_nonempty h1
      refine ⟨Ψ w, hwt, (d.mem_regSpace_iff).2 fun h => ?_⟩
      exact (hs w hwV).1 h hwR
    · exact subset_closure ((d.mem_regSpace_iff).2 hx)
  refine ⟨d.isOpen_regSpace, hdense, fun W hW hWc => ?_⟩
  refine isPreconnected_of_local hWc inter_subset_left (hdense.open_subset_closure_inter hW)
    fun x hx => ?_
  by_cases hxs : d.proj x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M
  · obtain ⟨V, U, Ψ, v, g, hV, hVc, hU, hUW, hv, hvx, hbij, hn, hs, -⟩ :=
      d.exists_lifted_in x hxs hW hx
    refine ⟨U, hU, by rw [← hvx]; exact hbij.mapsTo hv, ?_⟩
    have heq : U ∩ (W ∩ d.regSpace) = U ∩ d.regSpace := by
      ext y; exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hUW h.1, h.2⟩⟩
    rw [heq, ← hbij.image_eq]
    exact d.isPreconnected_image_inter_regSpace hV hVc hn hs
  · have hxR : x ∈ d.regSpace := (d.mem_regSpace_iff).2 hxs
    obtain ⟨-, -, -, -, hβl, -⟩ := maxBranched_basic
      (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) slsc_compl_sing y₀
    haveI := hβl
    have hSo := d.isOpen_inter_regPart hW
    set N := connectedComponentIn (d.fromNat ⁻¹' W ∩ regPart (y₀ := y₀)) (d.toNat x) with hNdef
    have hxN : d.toNat x ∈ N := mem_connectedComponentIn ⟨hx, hxR⟩
    have hNS : N ⊆ d.fromNat ⁻¹' W ∩ regPart (y₀ := y₀) := connectedComponentIn_subset _ _
    have hNo : IsOpen N := hSo.connectedComponentIn
    refine ⟨d.toNat ⁻¹' N, hNo.preimage d.continuous_toNat, hxN, ?_⟩
    have heq : d.toNat ⁻¹' N ∩ (W ∩ d.regSpace) = d.toNat ⁻¹' N := by
      refine inter_eq_left.2 fun y hy => ⟨(hNS hy).1, (hNS hy).2⟩
    rw [heq]
    exact d.isPreconnected_of_nat isPreconnected_connectedComponentIn fun z hz => (hNS hz).2

/-- `p` is a local homeomorphism of `(\widetilde M, T')` over `reg M`. -/
theorem isLocalHomeomorphOn_proj : IsLocalHomeomorphOn d.proj d.regSpace := by
  obtain ⟨-, hbc, hpb, -, hβl, -⟩ := maxBranched_basic
    (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) slsc_compl_sing y₀
  haveI := hβl
  refine IsLocalHomeomorphOn.mk _ _ fun x hx => ?_
  have hord : d.toNat x ∈ ordX (SpreadEnd.base : MaxBranchedCover
      (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ → M) := by
    by_contra h
    exact (d.mem_regSpace_iff).1 hx (hpb h)
  obtain ⟨φ, hxφ, hφ⟩ := hbc.ordX_subset_isLocalHomeomorphOn hord (d.toNat x) rfl
  set φ' := φ.restrOpen _ (isOpen_preimage_base_weakTopMax y₀
    (isOpen_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M))
  let ψ : OpenPartialHomeomorph d.Space M :=
    OpenPartialHomeomorph.retopBTZ d.T' φ' d.le_natural (fun z hz => d.nhds_reg z hz.2)
  refine ⟨ψ, ⟨hxφ, hx⟩, fun z _ => ?_⟩
  show SpreadEnd.base (d.toNat z) = φ z
  rw [hφ]; rfl


/-- `p : (\widetilde M, T') → M` is almost everywhere a local homeomorphism into `reg M`. -/
theorem isAELocalHomeomorph_proj :
    IsAELocalHomeomorph (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) d.proj :=
  ⟨d.regSpace, Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M, d.isPortly_regSpace,
    isPortly_reg _ _ M, subset_rfl, fun _ h => h, d.isLocalHomeomorphOn_proj⟩

/-- The pullback `p^*B` of the structure of `M` to `(\widetilde M, T')` exists (`lem:aepullback`). -/
theorem aePullback_proj_spec :
    IsMaximalAEAtlas (Causal.Flat.isom 2) (aePullback (Causal.Flat.isom 2)
        (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) d.proj) ∧
      IsAEMorphismOf (Causal.Flat.isom 2) (aePullback (Causal.Flat.isom 2)
        (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) d.proj)
        (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) d.proj :=
  aePullback_spec_of_isAELocalHomeomorph
    (isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M).1 d.continuous_proj
    d.isAELocalHomeomorph_proj

/-- **The singular `(Isom(𝐌³), 𝐌³)`-structure of `(\widetilde M, T_BTZ)`** (DEC-130, DEC-25): the
maximal a.e. atlas `p^*B`, the pullback of the structure of `M` along `p` (`lem:aepullback`). -/
instance singularGXStructure :
    SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space :=
  ⟨_, d.aePullback_proj_spec.1⟩

/-- The maximal a.e. atlas of `(\widetilde M, T')` **is** the pulled-back flat structure `p^*B`. -/
theorem aeAtlas_space : aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space =
    aePullback (Causal.Flat.isom 2) (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
      d.proj := rfl

/-- `p : (\widetilde M, T') → M` is an a.e. `(G,X)`-morphism. -/
theorem isAEMorphism_proj : IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) d.proj :=
  d.aePullback_proj_spec.2

theorem regSpace_subset_reg : d.regSpace ⊆ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space :=
  fun _ hx => IsAEMorphismOf.mem_support_of_isLocalHomeomorphOn'
    (isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space)
    (isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M).1 d.isAEMorphism_proj
    hx (d.isLocalHomeomorphOn_proj.mono (singleton_subset_iff.2 hx))

/-- Near a regular point, `D` is a translate of any chart of `M` read through `p`. -/
theorem eventually_dev_eq_smul_chart {z : d.Space} (hz : z ∈ d.regSpace)
    {a : OpenPartialHomeomorph M (Causal.Minkowski 2)}
    (ha : a ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) (hza : d.proj z ∈ a.source) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ y : d.Space in 𝓝 z, d.D y = g • a (d.proj y) := by
  obtain ⟨-, hbc, -, -, hβl, -⟩ := maxBranched_basic
    (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) slsc_compl_sing y₀
  haveI := hβl
  set P := aePullback (Causal.Flat.isom 2) (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
    (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ → M)
  set B := aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M
  have hBm := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M
  have hA := aePullback_spec_of_isAELocalHomeomorph hBm.1 hbc.isSpread.continuous
    (hbc.isAELocalHomeomorph hBm.1)
  have hreg := hA.2.regLocusOf_eq hA.1.1 hBm.1
  have hwR : d.toNat z ∈ (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) M) y₀ → M) ⁻¹' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M := hz
  obtain ⟨e, he, hwe⟩ := mem_support.1 (d.isRegDeveloping.subset_support hwR)
  obtain ⟨g, hg⟩ := d.isRegDeveloping.exists_smul_eq _ hwR e he _ refl_mem_gxModelAtlas hwe
    (mem_univ _)
  have hwL : d.toNat z ∈ regLocusOf (Causal.Flat.isom 2) P B SpreadEnd.base := by
    rw [hreg]; exact ⟨mem_support.2 ⟨e, he, hwe⟩, mem_support.2 ⟨a, ha, hza⟩⟩
  obtain ⟨h, hh⟩ := (isRegularOn_regLocusOf (G := Causal.Flat.isom 2) P B
    SpreadEnd.base).exists_smul_eq _ hwL e he a ha hwe hza
  refine ⟨g * h⁻¹, ?_⟩
  have hn : (𝓝 z : Filter d.Space) =
      @nhds _ (weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀) (d.toNat z) :=
    d.nhds_reg z hz
  rw [hn]
  filter_upwards [hg, hh] with y h1 h2
  rw [OpenPartialHomeomorph.refl_apply, id_eq] at h1
  show d.D y = (g * h⁻¹) • a (SpreadEnd.base y)
  rw [h1, mul_smul, h2, inv_smul_smul]

/-- Near a regular point of the source of a chart `c` of `(\widetilde M, T')`, `D` is a translate
of `c`. -/
theorem eventually_dev_eq_smul_of_regSpace
    {c : OpenPartialHomeomorph d.Space (Causal.Minkowski 2)}
    (hc : c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space) {z : d.Space}
    (hzc : z ∈ c.source) (hz : z ∈ d.regSpace) :
    ∃ k : Causal.Flat.isom 2, ∀ᶠ y : d.Space in 𝓝 z, d.D y = k • c y := by
  have hA : IsMaximalAEAtlas (Causal.Flat.isom 2)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space) ∧
      IsAEMorphismOf (Causal.Flat.isom 2) (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space)
        (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) d.proj := d.aePullback_proj_spec
  have hBm := isMaximalAEAtlas_aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M
  obtain ⟨a, ha, hza⟩ := mem_support.1 (show d.proj z ∈ Reg (Causal.Flat.isom 2)
    (Causal.Minkowski 2) M from hz)
  have hzL : z ∈ regLocusOf (Causal.Flat.isom 2)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) d.proj := by
    rw [hA.2.regLocusOf_eq hA.1.1 hBm.1]; exact ⟨mem_support.2 ⟨c, hc, hzc⟩, hz⟩
  obtain ⟨h, hh⟩ := (isRegularOn_regLocusOf (G := Causal.Flat.isom 2)
    (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space)
    (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M) d.proj).exists_smul_eq z hzL c hc a ha
    hzc hza
  obtain ⟨g, hg⟩ := d.eventually_dev_eq_smul_chart hz ha hza
  refine ⟨g * h, ?_⟩
  filter_upwards [hg, hh] with y h1 h2
  rw [h1, h2, mul_smul]

/-- **`Reg(\widetilde M, T') = p⁻¹(reg M)`**: no point over `sing M` is regular. A chart `c` at
such a point `x` would be, on a lifted chart `U ∋ x` inside its source (whose regular part is
preconnected and dense), one translate `k • c` of `D` (rigidity, then continuity of `D` for `T'`);
so `D(U)` would be an open neighbourhood of `D(x)`, while `g⁻¹ D(U) ⊆ D_{𝔼₀}(\widetilde{𝔼₀}) = J⁺(Δ)`
and `g⁻¹ D(x)` lies on the BTZ line `Δ` (`btzTilde_range_notMem_nhds_of_sing`). -/
theorem reg_space : Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space = d.regSpace := by
  refine Subset.antisymm (fun x hx => ?_) d.regSpace_subset_reg
  by_contra hxR
  have hxs : d.proj x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M := by
    by_contra h; exact hxR ((d.mem_regSpace_iff).2 h)
  obtain ⟨c, hc, hxc⟩ := mem_support.1 hx
  obtain ⟨V, U, Ψ, v, g, hV, hVc, hU, hUc, hv, hvx, hbij, hn, hs, hD⟩ :=
    d.exists_lifted_in x hxs c.open_source hxc
  have hxU : x ∈ U := by rw [← hvx]; exact hbij.mapsTo hv
  have hUR : IsPreconnected (U ∩ d.regSpace) := by
    rw [← hbij.image_eq]; exact d.isPreconnected_image_inter_regSpace hV hVc hn hs
  obtain ⟨k, hk⟩ := exists_smul_eq_on_of_isPreconnected hUR (fun z hz => hUc hz.1)
    fun z hz => d.eventually_dev_eq_smul_of_regSpace hc (hUc hz.1) hz.2
  have hEq : EqOn d.dev (fun y => k • c y) U :=
    EqOn.of_subset_closure hk d.continuous_dev.continuousOn
      ((continuous_const_smul k).comp_continuousOn (c.continuousOn.mono hUc)) inter_subset_left
      (d.isPortly_regSpace.dense.open_subset_closure_inter hU)
  have himg : d.dev '' U = (fun p => k • p) '' (c '' U) := by
    rw [image_image]; exact image_congr hEq
  have hopen : IsOpen (d.dev '' U) := by
    rw [himg]; exact isOpenMap_smul k _ (c.isOpen_image_of_subset_source hU hUc)
  have hvs : SpreadEnd.base v ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
    (hs v hv).1 (by rw [hvx]; exact hxs)
  apply btzTilde_range_notMem_nhds_of_sing d.isPresentation hvs
  have hDx : g • btzDevM 0 btzV0 (Φ v) = d.dev x := by rw [← hD v hv, hvx]; rfl
  have hmem : (fun p => g • p) ⁻¹' (d.dev '' U) ∈ 𝓝 (btzDevM 0 btzV0 (Φ v)) :=
    (continuous_const_smul g).continuousAt.preimage_mem_nhds
      (by rw [hDx]; exact hopen.mem_nhds ⟨x, hxU, rfl⟩)
  refine mem_of_superset hmem fun p hp => ?_
  obtain ⟨y, hyU, hyp⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hbij.surjOn hyU
  refine ⟨Φ w, smul_left_cancel g ?_⟩
  rw [← hD w hw]; exact hyp

/-- `Sing(\widetilde M, T') = p⁻¹(sing M)`. -/
theorem sing_space : Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space =
    d.proj ⁻¹' Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M := by
  rw [Sing, reg_space, regSpace, Sing, preimage_compl]

/-- **`D` develops the charts of `(\widetilde M, T')`**: near every point of the source of a chart
`c` of the maximal a.e. atlas, `D = k • c`. -/
theorem developsCharts : DevelopsCharts (G := Causal.Flat.isom 2) d.Space d.dev :=
  fun _ hc _ hz => d.eventually_dev_eq_smul_of_regSpace hc hz
    (by rw [← d.reg_space]; exact mem_support.2 ⟨_, hc, hz⟩)

/-- **`D` is a developing map of `(\widetilde M, T')`**: an a.e. `(G,X)`-morphism into `𝐌³`. -/
theorem isAEMorphismOf_dev : IsAEMorphismOf (Causal.Flat.isom 2)
    (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space)
    (gxModelAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2)) d.dev :=
  d.developsCharts.isAEMorphismOf d.continuous_dev

end BTZTildeData

end TildeStructure


/-! ### The model datum: `\widetilde{𝔼₀}` with `T_BTZ` over `𝔼₀` -/

section ModelDatum

variable {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}

/-- `\widetilde{𝔼₀}` (natural topology) is connected, so every component of the preimage of all
of `𝔼₀` is the whole space. -/
theorem btzTilde_connectedComponentIn_univ
    (f : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN) :
    connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) BTZE0) yN → BTZE0) ⁻¹' univ) f = univ := by
  obtain ⟨-, hbc, -⟩ := maxBranched_basic
    (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)
    (BTZTildeData.slsc_compl_sing (M := BTZE0)) yN
  haveI := hbc.connectedSpace_source
  rw [preimage_univ, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]

/-- **`\widetilde{𝔼₀}` is `\widetilde{𝔼₀}`-modelled at its singular points**, in the local reading
`IsLocallyBTZTilde` for `M = 𝔼₀`: the lifted chart of the chart `(𝔼₀, 𝔼₀, id)` is the identity. -/
theorem btzTilde_isLocallyBTZTilde :
    IsLocallyBTZTilde BTZE0 yN Φ ⟨TopologicalSpace.induced Φ hornTop⟩ (btzDevM 0 btzV0 ∘ Φ) := by
  intro e he
  let c : XAChart (Causal.Flat.isom 2) (Causal.Minkowski 2) btzFam btzFamS () e.base :=
    modelChartSelf (Causal.Flat.isom 2) (Causal.Minkowski 2) btzFamS () (s := e.base) he
  have hK : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) BTZE0) yN → BTZE0) ⁻¹' (c.V : Set BTZE0)) e = univ :=
    btzTilde_connectedComponentIn_univ e
  have hK' : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) BTZE0) yN → BTZE0) ⁻¹' (c.U : Set BTZE0)) e = univ :=
    btzTilde_connectedComponentIn_univ e
  refine ⟨c, e, id, he, rfl, ?_, ?_, ?_, ?_, ?_, fun v _ => ?_, fun v _ => Iff.rfl,
    fun v _ => map_id.symm, fun v _ => map_id.symm, 1, fun v _ => (one_smul _ _).symm⟩
  · rw [hK]; exact isOpen_univ
  · rw [hK]; exact @isOpen_univ _ (TopologicalSpace.induced Φ hornTop)
  · rw [hK']; exact isOpen_univ
  · rw [hK']; exact @isOpen_univ _ (TopologicalSpace.induced Φ hornTop)
  · rw [hK, hK']; exact bijOn_id univ
  · rw [chartExt_apply _ (show v.base ∈ c.V from trivial)]; rfl

/-- **The model datum**: `\widetilde{𝔼₀}` with `T_BTZ = Φ^* hornTop` and developing map
`D_{𝔼₀} = btzDevM ∘ Φ`, as a `BTZTildeData` over `𝔼₀` itself. Its space is `BTZTildeTB Φ`. -/
noncomputable def btzTildeModel (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    BTZTildeData BTZE0 yN Φ where
  T' := ⟨TopologicalSpace.induced Φ hornTop⟩
  le_natural := (btzTildeTB_isTamifying hΦ).le_natural
  nhds_reg := fun _ he => IsTamifyingTopology.nhds_eq_of_reg
    (BTZTildeData.slsc_compl_sing (M := BTZE0)) (T := ⟨TopologicalSpace.induced Φ hornTop⟩)
    (btzTildeTB_isTamifying hΦ) he
  D := btzDevM 0 btzV0 ∘ Φ
  continuous_D := @Continuous.comp _ _ _ (TopologicalSpace.induced Φ hornTop) hornTop _ _ _
    (continuous_btzDevM_hornTop 0 btzV0_pos) continuous_induced_dom
  isRegDeveloping := btz_isRegDevelopingOnReg btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0 hΦ
  isLocallyBTZTilde := btzTilde_isLocallyBTZTilde
  isPresentation := hΦ

theorem btzTildeModel_dev (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base)
    (w : (btzTildeModel hΦ).Space) : (btzTildeModel hΦ).dev w = btzDevM 0 btzV0 (Φ w) := rfl

theorem btzTildeModel_proj (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base)
    (w : (btzTildeModel hΦ).Space) : (btzTildeModel hΦ).proj w = SpreadEnd.base w := rfl

instance btzTildeModel_locPathConnectedSpace (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    LocPathConnectedSpace (btzTildeModel hΦ).Space :=
  (btzTildeTB_isTamifying hΦ).locPathConnected

instance btzTildeModel_firstCountableTopology
    (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    FirstCountableTopology (btzTildeModel hΦ).Space :=
  (btzTildeTB_isTamifying hΦ).firstCountable

variable (Φ) in
/-- **The model family `{\widetilde{𝔼₀}}`** (one model, `A = Unit`): `\widetilde{𝔼₀}` with `T_BTZ`
and its singular `(G,X)`-structure (`BTZTildeData.singularGXStructure` of the model datum). -/
abbrev btzTildeFam (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) : Unit → Type :=
  fun _ => (btzTildeModel hΦ).Space

variable (Φ) in
/-- The distinguished singular sets of `btzTildeFam`: the whole singular locus (the lifted BTZ
line). -/
def btzTildeFamS (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    ∀ a : Unit, Set (btzTildeFam Φ hΦ a) :=
  fun _ => Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (btzTildeModel hΦ).Space

end ModelDatum


/-! ### `\widetilde M` is a `\widetilde{𝔼₀}`-manifold -/

section XA

variable {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]

namespace BTZTildeData

variable {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
  {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}
  (d : BTZTildeData M y₀ Φ)

/-- **Every singular point of `(\widetilde M, T')` is the centre of a `\widetilde{𝔼₀}`-chart**
(`def:atlas` over the model family `btzTildeFam`): the lifted chart `Ψ : V → U` of
`IsLocallyBTZTilde` (`V` a `T_BTZ`-connected open of `\widetilde{𝔼₀}`), inverted, is a homeomorphism
`U ≅ V` (`Ψ` is continuous and open, `T_BTZ` to `T'`), an a.e. `(G,X)`-morphism (it intertwines the
chart-developing maps `D` and `D_{𝔼₀}`, `D ∘ Ψ = g · D_{𝔼₀}`), and it sends the point to a singular
point of `\widetilde{𝔼₀}`. -/
theorem hasXAType_of_mem_sing {x : d.Space}
    (hx : x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space) :
    HasXAType (G := Causal.Flat.isom 2) (X := Causal.Minkowski 2)
      (Xα := btzTildeFam Φ d.isPresentation) (S := btzTildeFamS Φ d.isPresentation) () x := by
  have hx' : d.proj x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M := by
    rw [sing_space] at hx; exact hx
  obtain ⟨V, U, Ψ, v, g, hV, hVc, hU, -, hv, hvx, hbij, hn, hs, hD⟩ :=
    d.exists_lifted_in x hx' isOpen_univ (mem_univ x)
  set m := btzTildeModel (yN := yN) (Φ := Φ) d.isPresentation with hmdef
  let V' : Opens m.Space := ⟨V, hV⟩
  let U' : Opens d.Space := ⟨U, hU⟩
  let e : V' ≃ U' := hbij.equiv Ψ
  have hcont : Continuous e :=
    ContinuousOn.mapsToRestrict (d.continuousOn_of_nhds_eq hn) hbij.mapsTo
  have hopen : IsOpenMap e := by
    intro O hO
    obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.1 hO
    have hW : IsOpen (Ψ '' (V ∩ O₀)) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨w, ⟨hwV, hwO⟩, rfl⟩
      rw [hn w hwV]
      exact mem_map.2 (mem_of_superset (inter_mem (hV.mem_nhds hwV) (hO₀.mem_nhds hwO))
        (subset_preimage_image _ _))
    have heq : e '' (Subtype.val ⁻¹' O₀) = Subtype.val ⁻¹' (Ψ '' (V ∩ O₀)) := by
      ext u
      constructor
      · rintro ⟨w, hwO, rfl⟩
        exact ⟨w.1, ⟨w.2, hwO⟩, rfl⟩
      · rintro ⟨w, ⟨hwV, hwO⟩, hwu⟩
        exact ⟨⟨w, hwV⟩, hwO, Subtype.ext hwu⟩
    rw [heq]
    exact hW.preimage continuous_subtype_val
  let E : V' ≃ₜ U' := e.toHomeomorphOfContinuousOpen hcont hopen
  have hxU : x ∈ U' := by rw [← hvx]; exact hbij.mapsTo hv
  have hEv : E.symm ⟨x, hxU⟩ = ⟨v, hv⟩ := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hvx.symm
  have hEsymm : ∀ u : U', Ψ ((E.symm u : V') : m.Space) = (u : d.Space) := fun u => by
    have h := E.apply_symm_apply u
    exact congrArg Subtype.val h
  refine ⟨⟨U', V', E.symm, hxU, ⟨⟨v, hv⟩, hVc⟩, ?_, ?_⟩⟩
  · apply isAEMorphism_of_val_comp
    refine isAEMorphism_of_developsCharts (d.developsCharts.opens U') m.developsCharts
      (continuous_subtype_val.comp E.symm.continuous) ?_ g fun u => ?_
    · intro u hu
      have hu' : (u : d.Space) ∈ d.regSpace := by
        rw [reg_opensSingular, mem_preimage, reg_space] at hu; exact hu
      rw [reg_space]
      set w := ((E.symm u : V') : m.Space)
      have hw : w ∈ V := (E.symm u).2
      show m.proj w ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
      rw [btzTildeModel_proj]
      have h1 := (d.mem_regSpace_iff).1 hu'
      rw [← hEsymm u] at h1
      have h2 : SpreadEnd.base w ∉ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
        fun h => h1 ((hs w hw).2 h)
      simpa [Sing] using h2
    · set w := ((E.symm u : V') : m.Space)
      have hw : w ∈ V := (E.symm u).2
      show d.dev (u : d.Space) = g • m.dev w
      rw [btzTildeModel_dev, ← hEsymm u]
      exact hD w hw
  · show ((E.symm ⟨x, hxU⟩ : V') : m.Space) ∈
      Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) m.Space
    rw [hEv, sing_space]
    show SpreadEnd.base v ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
    exact (hs v hv).1 (by rw [hvx]; exact hx')

end BTZTildeData

end XA


/-! ### The standing instances of `(\widetilde M, T')` (DEC-66) -/

section Instances

variable {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]

namespace BTZTildeData

variable {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
  {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}
  (d : BTZTildeData M y₀ Φ)

/-- `(\widetilde M, T')` is locally path-connected: naturally over `reg M`, through the lifted
charts (`T_BTZ` is locally path-connected) over `sing M`. -/
instance locPathConnectedSpace_space : LocPathConnectedSpace d.Space := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  by_cases hx : d.proj x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M
  · obtain ⟨V, U, Ψ, v, -, hV, -, -, hUu, hv, hvx, hbij, hn, -, -⟩ :=
      d.exists_lifted_in x hx hu hxu
    haveI : LocPathConnectedSpace (BTZTildeTB Φ) :=
      (btzTildeTB_isTamifying d.isPresentation).locPathConnected
    have hP : pathComponentIn V v ∈ 𝓝 v := pathComponentIn_mem_nhds (hV.mem_nhds hv)
    have hmem : Ψ '' pathComponentIn V v ∈ 𝓝 x := by
      rw [← hvx, hn v hv]
      exact mem_map.2 (mem_of_superset hP (subset_preimage_image _ _))
    refine mem_of_superset hmem ?_
    rintro _ ⟨w, hw, rfl⟩
    have h1 := (hw : JoinedIn V v w).map_continuousOn (d.continuousOn_of_nhds_eq hn)
    rw [hvx, hbij.image_eq] at h1
    exact h1.mono hUu
  · have hxR : x ∈ d.regSpace := (d.mem_regSpace_iff).2 hx
    obtain ⟨-, -, -, -, hβl, -⟩ := maxBranched_basic
      (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) slsc_compl_sing y₀
    haveI := hβl
    set S := d.fromNat ⁻¹' u ∩ regPart (y₀ := y₀)
    have hSo : IsOpen S := d.isOpen_inter_regPart hu
    have hP : pathComponentIn S (d.toNat x) ∈
        @nhds _ (weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀) (d.toNat x) :=
      pathComponentIn_mem_nhds (hSo.mem_nhds ⟨hxu, hxR⟩)
    have hn : (𝓝 x : Filter d.Space) =
        @nhds _ (weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀) (d.toNat x) :=
      d.nhds_reg x hxR
    rw [hn]
    refine mem_of_superset hP fun y hy => ?_
    have h1 := (hy : JoinedIn S (d.toNat x) y).map_continuousOn
      (d.continuousOn_fromNat fun z hz => hz.2)
    exact h1.mono (by rintro _ ⟨z, hz, rfl⟩; exact hz.1)

/-- `(\widetilde M, T')` is first countable: `T_BTZ` is, and `p` is a local homeomorphism over
`reg M`. -/
instance firstCountableTopology_space : FirstCountableTopology d.Space := by
  refine ⟨fun x => ?_⟩
  by_cases hx : d.proj x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M
  · obtain ⟨V, U, Ψ, v, -, -, -, hv, hvx, -, hn, -, -⟩ := d.exists_lifted x hx
    haveI : FirstCountableTopology (BTZTildeTB Φ) :=
      (btzTildeTB_isTamifying d.isPresentation).firstCountable
    rw [← hvx, hn v hv]
    infer_instance
  · obtain ⟨φ, hxφ, -⟩ := d.isLocalHomeomorphOn_proj x ((d.mem_regSpace_iff).2 hx)
    have h := φ.symm.map_nhds_eq (φ.map_source hxφ)
    rw [φ.left_inv hxφ] at h
    rw [← h]
    infer_instance

/-- `(\widetilde M, T')` is connected: `p⁻¹(reg M)` is (naturally, hence for `T'`) connected and
`T'`-dense. -/
instance connectedSpace_space : ConnectedSpace d.Space := by
  obtain ⟨-, hbc, -, -, -, -⟩ := maxBranched_basic
    (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) slsc_compl_sing y₀
  haveI := hbc.connectedSpace_source
  have hR := hbc.isPortly_preimage (isPortly_reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
  have hRc : IsPreconnected ((SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2)
      (Causal.Minkowski 2) M) y₀ → M) ⁻¹' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M) := by
    have := hR.locallyConnectedIn univ isOpen_univ isPreconnected_univ
    rwa [univ_inter] at this
  have h1 : IsPreconnected d.regSpace := d.isPreconnected_of_nat hRc fun _ hz => hz
  have h2 := h1.closure
  rw [d.isPortly_regSpace.dense.closure_eq] at h2
  haveI : PreconnectedSpace d.Space := ⟨h2⟩
  obtain ⟨z⟩ := (inferInstance : Nonempty (MaxBranchedCover (Sing (Causal.Flat.isom 2)
    (Causal.Minkowski 2) M) y₀))
  exact ⟨⟨d.fromNat z⟩⟩

end BTZTildeData

end Instances

/-! ### `\widetilde{𝔼₀}`-manifolds -/

section TildeManifold

variable {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}

variable (Φ) in
/-- **A `\widetilde{𝔼₀}`-manifold** (a "`\widetilde{BTZ}`-manifold", `RamcovGX.tex:2310`, DEC-130):
a singular `(Isom(𝐌³), 𝐌³)`-manifold whose singular locus is locally modelled on `\widetilde{𝔼₀}`
with `T_BTZ` — every singular point is the centre of a `\widetilde{𝔼₀}`-chart (`def:atlas` over
the model family `btzTildeFam`), the reading of l.2300 for `𝔼₀` (`GX.IsBTZSingModelled`) with
`𝔼₀` replaced by `\widetilde{𝔼₀}`. -/
def IsBTZTildeSingModelled (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) (N : Type*)
    [TopologicalSpace N] [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) N] :
    Prop :=
  ∀ y ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) N,
    ∃ a, HasXAType (G := Causal.Flat.isom 2) (X := Causal.Minkowski 2)
      (Xα := btzTildeFam Φ hΦ) (S := btzTildeFamS Φ hΦ) a y

variable {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]
  {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}

/-- **`(\widetilde M, T_BTZ)` is a `\widetilde{𝔼₀}`-manifold** (DEC-130), for every datum. -/
theorem BTZTildeData.isBTZTildeSingModelled (d : BTZTildeData M y₀ Φ) :
    IsBTZTildeSingModelled Φ d.isPresentation d.Space :=
  fun _ hx => ⟨(), d.hasXAType_of_mem_sing hx⟩

/-- The model has singular points (the lifted BTZ line is non-empty). -/
theorem btzTildeFamS_nonempty (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) (a : Unit) :
    (btzTildeFamS Φ hΦ a).Nonempty := by
  obtain ⟨s, hs⟩ := btzE0_sing_nonempty
  obtain ⟨x, hx, -⟩ := BTZTildeData.exists_not_mem_regPart (y₀ := yN) hs
  refine ⟨(btzTildeModel hΦ).fromNat x, ?_⟩
  show _ ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) (btzTildeModel hΦ).Space
  rw [BTZTildeData.sing_space]
  show SpreadEnd.base x ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0
  rw [hx]; exact hs

/-- **Non-vacuity: the model `\widetilde{𝔼₀}` itself is an `X_A`-manifold over `{\widetilde{𝔼₀}}`**
in the full sense of DEC-67 (e) (atlas clause included: the chart `(\widetilde{𝔼₀}, \widetilde{𝔼₀},
id)`), and a `\widetilde{𝔼₀}`-manifold. -/
theorem btzTildeModel_isXAManifold (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    IsXAManifold (Causal.Flat.isom 2) (Causal.Minkowski 2) (btzTildeFam Φ hΦ) (btzTildeFamS Φ hΦ)
      (btzTildeModel hΦ).Space :=
  isXAManifold_model_of_sing_subset (btzTildeFamS_nonempty hΦ) () subset_rfl

end TildeManifold


/-! ### `prop:manifold_admits_galoisian_maximal`, in full -/

section GalMaxFull

variable {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]

/-- **`prop:manifold_admits_galoisian_maximal`** (`RamcovGX.tex:2308–2310`), every assertion, the
last as ruled by DEC-130: for an `𝔼₀`-manifold `M` (l.2300, `IsBTZSingModelled`),
(1) for every base point the maximal covering `\widetilde M → M` is Galoisian and exactly branched
above `sing M` (`GX.btz_manifold_galoisian_maximal`); (2) `\widetilde{𝔼₀}` has a presentation `Φ`;
(3) for every base point and every presentation, `\widetilde M` carries the tamifying topology
`T_BTZ` — chartwise `T_BTZ` at every lifted descending `𝔼₀`-chart (DEC-118 (c)) — with a
`T_BTZ`-continuous developing map `D`, and **`(\widetilde M, T_BTZ)` is a
`\widetilde{𝔼₀}`-manifold**: it carries a full singular `(Isom(𝐌³), 𝐌³)`-structure
(`BTZTildeData.singularGXStructure`, a maximal a.e. atlas, DEC-25) which is the pulled-back flat
structure `p^*B` (`p` an a.e. morphism), whose regular locus is `p⁻¹(reg M)`, for which `D` is an
a.e. `(G,X)`-morphism into `𝐌³` (a developing map), and whose every singular point is the centre of
a `\widetilde{𝔼₀}`-chart (`IsBTZTildeSingModelled`). The space is moreover Hausdorff, locally
path-connected, first countable and connected (the instances of `BTZTildeData.Space`). -/
theorem btz_manifold_galoisian_maximal_full (hM : IsBTZSingModelled M) :
    (∀ y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M),
      IsGaloisian (SpreadEnd.base :
        MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ → M) ∧
      branchingLocus (SpreadEnd.base :
        MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ → M) =
        Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) ∧
    (∃ (yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0))
      (Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
        DInfty × ℝ), ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) ∧
    ∀ (y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M))
      (yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0))
      (Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
        DInfty × ℝ) (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base),
      ∃ d : BTZTildeData M y₀ Φ,
        IsTamifyingTopology (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀ d.T'.top ∧
        (∀ (y : M) (c : XAChart (Causal.Flat.isom 2) (Causal.Minkowski 2) btzFam btzFamS () y),
          IsDescendingChartMap (Causal.Flat.isom 2) (Causal.Minkowski 2) c.φ →
          ∀ (f : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN)
            (Ψ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN →
              MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀),
            IsChartDescent (c.U : Set M) (c.V : Set BTZE0) (chartExt c.φ) f Ψ →
            ∀ v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f,
              @nhds _ d.T'.top (Ψ v) =
                Filter.map Ψ (@nhds _ (TopologicalSpace.induced Φ hornTop) v)) ∧
        Continuous d.dev ∧
        IsRegDevelopingOnReg (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀ d.D ∧
        aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space =
          aePullback (Causal.Flat.isom 2) (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
            d.proj ∧
        IsAEMorphism (Causal.Flat.isom 2) (Causal.Minkowski 2) d.proj ∧
        Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space =
          d.proj ⁻¹' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M ∧
        IsAEMorphismOf (Causal.Flat.isom 2)
          (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space)
          (gxModelAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2)) d.dev ∧
        IsBTZTildeSingModelled Φ hΦ d.Space := by
  refine ⟨(btz_manifold_galoisian_maximal hM).1, btz_exists_presentation,
    fun y₀ yN Φ hΦ => ?_⟩
  obtain ⟨T, hT, hreg, hch⟩ := btz_manifold_exists_chartwise_tamifying_reg hM y₀ yN Φ hΦ
  obtain ⟨D, hDc, hDr⟩ := hT.exists_extension
  let d : BTZTildeData M y₀ Φ := ⟨⟨T⟩, hT.le_natural, hreg, D, hDc, hDr,
    isLocallyBTZTilde_of_chartwise hM hΦ ⟨T⟩ hT hch hDc hDr, hΦ⟩
  exact ⟨d, hT, hch, d.continuous_dev, hDr, rfl, d.isAEMorphism_proj, d.reg_space,
    d.isAEMorphismOf_dev, d.isBTZTildeSingModelled⟩

/-- `prop:manifold_admits_galoisian_maximal` in full, for `𝔼₀`-manifolds as `X_A`-manifolds over
`{𝔼₀}` (DEC-67 (e)). -/
theorem btz_xaManifold_galoisian_maximal_full
    (hM : IsXAManifold (Causal.Flat.isom 2) (Causal.Minkowski 2) btzFam btzFamS M)
    (y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M))
    (yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0))
    (Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
      DInfty × ℝ) (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    ∃ d : BTZTildeData M y₀ Φ,
      IsTamifyingTopology (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀ d.T'.top ∧
      Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) d.Space =
        d.proj ⁻¹' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M ∧
      IsBTZTildeSingModelled Φ hΦ d.Space := by
  obtain ⟨d, hT, -, -, -, -, -, hR, -, hB⟩ :=
    (btz_manifold_galoisian_maximal_full hM.isBTZSingModelled).2.2 y₀ yN Φ hΦ
  exact ⟨d, hT, hR, hB⟩

end GalMaxFull

end GX
