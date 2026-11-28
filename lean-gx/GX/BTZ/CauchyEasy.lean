import GX.BTZ.MaxExtension
import GX.BTZ.RegComplete
import Causal.Flat.Cla.CoverMax

/-!
# btz § 5.4, `theo:BTZ_Cauchy-completness`, the two implications the paper calls immediate, for `𝔼₀`-manifolds

Target `T-btz-cauchy-easy` (`roadmap/roadmap.toml`). Paper `btz`
(`papers/btz/legacy/labeled/BTZ_1.tex`), theorem l.1582–1589, proof l.1593. Row (unmarked,
partial: `𝔼₀` only, the readings of OQ-142 (e)(f), and (i) ⇒ (iii) is not here):

* `btzthm:BTZ_Cauchy-completness` — `BTZ_1.tex:1582` (the sentence l.1593) —
  `GX.BTZCauchyEasy.iii_imp_ii` ((iii) ⇒ (ii)), `GX.BTZCauchyEasy.ii_imp_i` ((ii) ⇒ (i)),
  `GX.BTZCauchyEasy.iii_imp_i`, with the transfer along the induced isometry
  `GX.BTZCauchyEasy.regM_of_isBTZEmbedding`, the restriction
  `GX.BTZCauchyEasy.regMap` of an `𝔼₀`-morphism to the regular parts
  (`isLocalIsometry_regMap`, `isIsometricEmbedding_regMap`, `surjective_regMap`), and the flat
  transport lemmas `GX.BTZCauchyEasy.isCauchyComplete_of_isIsometricEmbedding_of_surjective`,
  `GX.BTZCauchyEasy.mgh_of_isIsometricEmbedding_of_surjective`,
  `GX.BTZCauchyEasy.isIsometricEmbedding_surjInv`, `GX.BTZCauchyEasy.pathLength_eq_of_local`.

> Let $M$ be a globally hyperbolic $\mass{\geq0}$-manifold. The following a then equivalent:
> (i) $\reg_{>0}(M)$ is Cauchy-complete and Cauchy-maximal;
> (ii) there exists a BTZ-extension of $M$ which is Cauchy-complete and Cauchy-maximal;
> (iii) $\BTZext(M)$ is Cauchy-complete and Cauchy-maximal. (l.1582–1589)
>
> $(iii)\Rightarrow (ii)$ is trivial and $(ii)\Rightarrow (i)$ is a consequence of Proposition
> \ref{prop:reg_complete}. (l.1593)

## Hypothesis checklist

| paper | here |
|---|---|
| `M` an `𝔼_{≥0}`-manifold | ⚠ `𝔼₀` only (T-btz-scope, DEC-116 (b), DEC-125 (a)(e)): `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2; then `Reg_{>0} M = Reg M = E0LM.e0RegM M`. Second countability of `M` (l.261) ⚠ weakened: not used (the extension's carrier, an `E0Mfd`, has it) |
| (none; l.261 does not require it) | ⚠ strengthened: `M` connected (`e0RegMFlat M` is a `Causal.Flat.FlatSpacetime`, connected by definition; as in `prop_reg_complete`) |
| `M` globally hyperbolic | ⚠ weakened: not assumed. GH of `Reg M` comes from that of `Reg N` along the isometry |
| (ii) « a BTZ-extension of `M` which is Cauchy-complete and Cauchy-maximal » | ⚠ added in Lean: a `GX.BTZMax.GHExt M` (a BTZ-embedding into a *globally hyperbolic* `𝔼₀`-manifold, OQ-150 (a), T-btz-maximal-extension), with `E0C1CauchyComplete` (OQ-142 (e)) and `IsE0CauchyMaximal`. At l.222 global hyperbolicity is the existence of a Cauchy surface, so a Cauchy-complete extension is GH by the paper's definitions; ETT's GH (causal with compact diamonds) is not derived from a Cauchy surface in the library, so it is carried — redundant under l.222, but the lemma is not in the library |
| (iii) « `BTZext(M)` is Cauchy-complete and Cauchy-maximal » | ✓ any `Causal.AbstractDev.IsMaximal` `GHExt M` (OQ-150 (a), as in `GXScaffold.BTZ.CauchySpear`), with the readings of (ii) |
| (i) « `Reg_{>0}(M)` Cauchy-complete and Cauchy-maximal » | ⚠ read: `Causal.Flat.GH`, `Causal.Flat.MGH` (OQ-142 (f)) and `Causal.Flat.IsCauchyComplete 2` (spacelike Lipschitz, DEC-31/35; OQ-142 (e)) of `e0RegMFlat M`, as in `prop_reg_complete'` |

## SCOPE (disclosed)

(i) ⇒ (iii) (Steps 1 and 2 of the proof, l.1594–1614) is not here: it is
`GXScaffold.BTZ.CauchySpear` and T-btz-cauchy-conservation. The two implications here are proved
with no `sorry`: (iii) ⇒ (ii) takes the maximal extension itself; (ii) ⇒ (i) applies the strict
`GX.E0RegComplete.prop_reg_complete'` to the extension `N` and carries its three conclusions back
along the flat isometry `Reg M ≅ Reg N` which the BTZ-embedding induces (`regMap`: an
`𝔼₀`-morphism preserves the type of points, and the complement of the image is BTZ, so the
restriction is a bijection of the regular parts, and it is a flat local isometry because an
element of `e0Groupoid` read in two regular charts of `Y` is locally in `Isom(𝐌³)`,
`E0LM.e0_flat_transition_aux`). The paper's « consequence of Proposition prop:reg_complete »
leaves this transfer implicit. The row stays partial: the `𝔼₀` scope, the readings above, and
the third implication.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped ENNReal Pointwise

namespace BTZCauchyEasy

open Causal.Flat

/-! ### §1 Flat transport along a bijective isometric embedding -/

section FlatTransport

variable {d : ℕ}

/-- **Lengths are local, two chart systems**: if near every point the system of `X` is the
system of `Y` read through `q`, up to an isometry of `𝐌ⁿ`, then `q` preserves path lengths. -/
theorem pathLength_eq_of_local {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φX : X → X → Causal.Minkowski d) (φY : Y → Y → Causal.Minkowski d) {q : X → Y}
    (hq : Continuous q)
    (hloc : ∀ x, ∃ g : isom d, ∀ᶠ x' in 𝓝 x, φX x x' = g • φY (q x) (q x')) {a b : X}
    (γ : Path a b) : pathLength φX γ = pathLength φY (γ.map hq) := by
  have hext : ⇑(γ.map hq).extend = q ∘ γ.extend := rfl
  have key : ∀ t, (LocLipAt φX γ.extend t ↔ LocLipAt φY (q ∘ γ.extend) t) ∧
      localDensity φX γ.extend t = localDensity φY (q ∘ γ.extend) t := fun t => by
    obtain ⟨g, hg⟩ := hloc (γ.extend t)
    exact locLipAt_pulled_iff_of_eventually (φX (γ.extend t)) φY q
      γ.continuous_extend.continuousAt hg
  have hiff : IsLocLip φX γ.extend ↔ IsLocLip φY (γ.map hq).extend := by
    rw [hext]; exact forall_congr' fun t => (key t).1
  by_cases hL : IsLocLip φX γ.extend
  · rw [pathLength_of_isLocLip _ hL, pathLength_of_isLocLip _ (hiff.1 hL), hext]
    exact MeasureTheory.lintegral_congr fun t => (key t).2
  · rw [pathLength_of_not_isLocLip _ hL, pathLength_of_not_isLocLip _ (mt hiff.2 hL)]

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace (Causal.Minkowski d) X]
  [TopologicalSpace Y] [ChartedSpace (Causal.Minkowski d) Y]

/-- **A local isometry does not increase the induced length** of a hypersurface carried into
another. -/
theorem edist_inducedLengthSpace_le {φ : X → Y} (hφ : IsLocalIsometry d φ) {S : Set X}
    {T : Set Y} (hST : MapsTo φ S T) (a b : S) :
    edist (InducedLengthSpace.toSubtype.symm (hST.restrict φ S T a) : InducedLengthSpace d T)
        (InducedLengthSpace.toSubtype.symm (hST.restrict φ S T b)) ≤
      edist (InducedLengthSpace.toSubtype.symm a : InducedLengthSpace d S)
        (InducedLengthSpace.toSubtype.symm b) := by
  set q : S → T := hST.restrict φ S T with hqdef
  have hqc : Continuous q := (hφ.continuous.comp continuous_subtype_val).subtype_mk _
  have hloc : ∀ x : S, ∃ g : isom d, ∀ᶠ x' in 𝓝 x,
      chartSys d S x x' = g • chartSys d T (q x) (q x') := by
    intro x
    obtain ⟨g, hg⟩ := (isLocalIsometry_iff_eventually.1 hφ).2 (x : X)
    refine ⟨g⁻¹, ?_⟩
    filter_upwards [(continuous_subtype_val.continuousAt (x := x)).eventually hg] with x' hx'
    change chartAt (Causal.Minkowski d) (x : X) (x' : X) =
      g⁻¹ • chartAt (Causal.Minkowski d) (φ x) (φ x')
    rw [hx', inv_smul_smul]
  change (⨅ γ : Path (q a) (q b), pathLength (chartSys d T) γ) ≤
    ⨅ γ : Path a b, pathLength (chartSys d S) γ
  exact le_iInf fun c => (iInf_le _ (c.map hqc)).trans_eq
    (pathLength_eq_of_local _ _ hqc hloc c).symm

/-- **The inverse of a bijective isometric embedding is an isometric embedding.** -/
theorem isIsometricEmbedding_surjInv {φ : X → Y} (hφ : IsIsometricEmbedding d φ)
    (hs : Surjective φ) : IsIsometricEmbedding d (surjInv hs) := by
  have hr : ∀ y, φ (surjInv hs y) = y := rightInverse_surjInv hs
  have hl : ∀ x, surjInv hs (φ x) = x := leftInverse_surjInv ⟨hφ.injective, hs⟩
  let hhomeo : X ≃ₜ Y := (Equiv.ofBijective φ ⟨hφ.injective, hs⟩).toHomeomorphOfIsInducing
    hφ.isOpenEmbedding.isInducing
  have hc : Continuous (surjInv hs) := by
    have : (surjInv hs) = hhomeo.symm := by
      funext y
      apply hφ.injective
      rw [hr]
      exact (hhomeo.apply_symm_apply y).symm.trans rfl
    rw [this]; exact hhomeo.symm.continuous
  refine ⟨isLocalIsometry_iff_eventually.2 ⟨hc, fun y => ?_⟩, (rightInverse_surjInv hs).injective⟩
  obtain ⟨g, hg⟩ := (isLocalIsometry_iff_eventually.1 hφ.isLocalIsometry).2 (surjInv hs y)
  refine ⟨g⁻¹, ?_⟩
  filter_upwards [hc.continuousAt.eventually hg] with y' hy'
  rw [hr, hr] at hy'
  rw [hy', inv_smul_smul]

variable [HasGroupoid X (Causal.gxGroupoid (isom d) (Causal.Minkowski d))]
  [HasGroupoid Y (Causal.gxGroupoid (isom d) (Causal.Minkowski d))]

/-- **Cauchy-completeness transports along a bijective isometric embedding** (DEC-31/35's
`IsCauchyComplete`, all four fields: the image of the surface is a Cauchy surface, spacelike
Lipschitz in the charts of `Y`, and the induced length spaces are isometric). -/
theorem isCauchyComplete_of_isIsometricEmbedding_of_surjective {φ : X → Y}
    (hφ : IsIsometricEmbedding d φ) (hs : Surjective φ) (h : IsCauchyComplete d X) :
    IsCauchyComplete d Y := by
  obtain ⟨S, hC, hL, hcomp, htop⟩ := h
  have hr : ∀ y, φ (surjInv hs y) = y := rightInverse_surjInv hs
  have hl : ∀ x, surjInv hs (φ x) = x := leftInverse_surjInv ⟨hφ.injective, hs⟩
  have hψ := isIsometricEmbedding_surjInv hφ hs
  set T : Set Y := φ '' S with hT
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · -- the image is a Cauchy surface
    have hU : ((⊤ : Opens Y) : Set Y) = φ '' ((⊤ : Opens X) : Set X) := by
      rw [Opens.coe_top, Opens.coe_top, image_univ, hs.range_eq]
    exact (hφ.isEMorphism.isCauchySurfaceOn_image_iff hφ.2.injOn le_rfl hU (subset_univ S)).1 hC
  · -- spacelike Lipschitz in the charts of `Y`
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨V0, hpV0, -, hL0⟩ := hL p hp
    obtain ⟨g, hg⟩ := (isLocalIsometry_iff_eventually.1 hφ.1).2 p
    set e := chartAt (Causal.Minkowski d) (φ p) with he
    set e0 := chartAt (Causal.Minkowski d) p with he0
    have hsrc : ∀ᶠ y in 𝓝 p, φ y ∈ e.source :=
      hφ.continuous.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds (mem_chart_source _ _))
    have hsrc0 : ∀ᶠ y in 𝓝 p, y ∈ e0.source := e0.open_source.mem_nhds (mem_chart_source _ _)
    obtain ⟨W, hWsub, hWo, hpW⟩ := mem_nhds_iff.1 (hg.and (hsrc.and hsrc0))
    have hW : ∀ y ∈ W, e (φ y) = g • e0 y ∧ φ y ∈ e.source ∧ y ∈ e0.source := fun y hy => hWsub hy
    have hWo' : IsOpen (e0 '' W) := e0.isOpen_image_of_subset_source hWo fun y hy => (hW y hy).2.2
    set U : Opens (Causal.Minkowski d) := ⟨e0 '' W ∩ V0, hWo'.inter V0.isOpen⟩ with hUdef
    set V : Opens (Causal.Minkowski d) := Causal.Flat.isomImage g U with hVdef
    have hVmem : ∀ z, z ∈ V ↔ ∃ y ∈ W, e0 y ∈ V0 ∧ g • e0 y = z := by
      intro z
      rw [← SetLike.mem_coe, hVdef, Causal.Flat.coe_isomImage]
      constructor
      · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hyV⟩, rfl⟩; exact ⟨y, hy, hyV, rfl⟩
      · rintro ⟨y, hy, hyV, rfl⟩; exact ⟨e0 y, ⟨⟨y, hy, rfl⟩, hyV⟩, rfl⟩
    refine ⟨V, (hVmem _).2 ⟨p, hpW, hpV0, (hW p hpW).1.symm⟩, fun z hz => ?_, ?_⟩
    · obtain ⟨y, hy, -, rfl⟩ := (hVmem z).1 hz
      rw [← (hW y hy).1]
      exact e.map_source (hW y hy).2.1
    have hset : e '' (T ∩ e.source) ∩ (V : Set (Causal.Minkowski d)) =
        g • (e0 '' (S ∩ e0.source) ∩ (V0 : Set (Causal.Minkowski d))) ∩
          (V : Set (Causal.Minkowski d)) := by
      ext z
      constructor
      · rintro ⟨⟨m, ⟨hmT, hmsrc⟩, rfl⟩, hzV⟩
        refine ⟨?_, hzV⟩
        obtain ⟨y, hy, hyV0, hyz⟩ := (hVmem _).1 hzV
        have hm : φ y = m := e.injOn (hW y hy).2.1 hmsrc ((hW y hy).1.trans hyz)
        obtain ⟨s', hs', rfl⟩ := hmT
        obtain rfl : y = s' := hφ.2 hm
        exact Set.mem_smul_set.2 ⟨e0 y, ⟨⟨y, ⟨hs', (hW y hy).2.2⟩, rfl⟩, hyV0⟩, hyz⟩
      · rintro ⟨hzA, hzV⟩
        obtain ⟨a, ⟨⟨s', ⟨hsS, hssrc⟩, rfl⟩, -⟩, rfl⟩ := Set.mem_smul_set.1 hzA
        obtain ⟨y, hy, -, hyz⟩ := (hVmem _).1 hzV
        have h1 : e0 y = e0 s' := MulAction.injective g hyz
        obtain rfl : y = s' := e0.injOn (hW y hy).2.2 hssrc h1
        exact ⟨⟨φ y, ⟨⟨y, hsS, rfl⟩, (hW y hy).2.1⟩, (hW y hy).1⟩, hzV⟩
    rw [hset]
    refine (hL0.smul Causal.Flat.isom_strongMorphism g).restrict fun z hz => ?_
    obtain ⟨y, hy, hyV0, rfl⟩ := (hVmem z).1 hz
    rw [← SetLike.mem_coe, Causal.Flat.coe_smulOpens]
    exact Set.smul_mem_smul_set hyV0
  all_goals
    have hST : MapsTo φ S T := mapsTo_image φ S
    have hTS : MapsTo (surjInv hs) T S := by
      rintro _ ⟨x, hx, rfl⟩; rw [hl]; exact hx
    have hrq : ∀ a : S, hTS.restrict _ T S (hST.restrict φ S T a) = a := fun a =>
      Subtype.ext (hl a)
    have hqr : ∀ b : T, hST.restrict φ S T (hTS.restrict _ T S b) = b := fun b =>
      Subtype.ext (hr b)
    let E : InducedLengthSpace d S ≃ InducedLengthSpace d T :=
      { toFun := fun a => InducedLengthSpace.toSubtype.symm
          (hST.restrict φ S T (InducedLengthSpace.toSubtype a))
        invFun := fun b => InducedLengthSpace.toSubtype.symm
          (hTS.restrict _ T S (InducedLengthSpace.toSubtype b))
        left_inv := fun a => hrq a
        right_inv := fun b => hqr b }
    have hE : Isometry E := by
      intro a b
      refine le_antisymm (edist_inducedLengthSpace_le hφ.1 hST a b) ?_
      have h2 := edist_inducedLengthSpace_le hψ.1 hTS (hST.restrict φ S T a)
        (hST.restrict φ S T b)
      rw [hrq, hrq] at h2
      exact h2
    let I : InducedLengthSpace d S ≃ᵢ InducedLengthSpace d T := ⟨E, hE⟩
  · haveI := hcomp
    exact I.symm.completeSpace
  · refine (hφ.continuous.comp (htop.comp I.symm.continuous)).congr fun b => ?_
    exact hr ((InducedLengthSpace.toSubtype b : T) : Y)

end FlatTransport

section FlatSpacetimes

variable {d : ℕ}

/-- **MGH transports along a bijective isometric embedding**: a flat Cauchy embedding of the
target, precomposed, is one of the source. -/
theorem mgh_of_isIsometricEmbedding_of_surjective {A B : FlatSpacetime.{0} d} {φ : A → B}
    (hφ : IsIsometricEmbedding d φ) (hs : Surjective φ) (h : MGH A) : MGH B := by
  refine ⟨Cla.cover_gh_of_isIsometricEmbedding_of_surjective hφ hs h.1, fun N f hf => ?_⟩
  obtain ⟨hfi, -, hN, S, hS, hfS⟩ := isFlatCauchyEmbedding_iff.1 hf
  have hU : ((⊤ : Opens B) : Set B) = φ '' ((⊤ : Opens A) : Set A) := by
    rw [Opens.coe_top, Opens.coe_top, image_univ, hs.range_eq]
  have hS' : (flatCausality d A).IsCauchySurface (φ ⁻¹' S) :=
    (hφ.isEMorphism.isCauchySurfaceOn_image_iff hφ.2.injOn le_rfl hU (subset_univ _)).2
      (by rw [image_preimage_eq S hs]; exact hS)
  have hc : IsFlatCauchyEmbedding d (f ∘ φ) :=
    isFlatCauchyEmbedding_iff.2 ⟨hfi.comp hφ, h.1, hN, φ ⁻¹' S, hS',
      by rw [image_comp, image_preimage_eq S hs]; exact hfS⟩
  exact Surjective.of_comp (h.2 N (f ∘ φ) hc)

/-- **GH, MGH and Cauchy-completeness transport along a bijective isometric embedding.** -/
theorem transfer_of_isIsometricEmbedding_of_surjective {A B : FlatSpacetime.{0} d} {φ : A → B}
    (hφ : IsIsometricEmbedding d φ) (hs : Surjective φ)
    (h : GH A ∧ MGH A ∧ IsCauchyComplete d A) : GH B ∧ MGH B ∧ IsCauchyComplete d B :=
  ⟨Cla.cover_gh_of_isIsometricEmbedding_of_surjective hφ hs h.1,
    mgh_of_isIsometricEmbedding_of_surjective hφ hs h.2.1,
    isCauchyComplete_of_isIsometricEmbedding_of_surjective hφ hs h.2.2⟩

end FlatSpacetimes

/-! ### §2 The restriction of an `𝔼₀`-morphism to the regular parts -/

section RegMap

open E0Spear

variable {M N : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
  [TopologicalSpace N] [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid]

/-- An `𝔼₀`-morphism maps regular points to regular points. -/
theorem mem_e0RegM_of_isE0Mor {f : M → N} (hf : IsE0Mor f univ) {x : M}
    (hx : x ∈ E0LM.e0RegM M) : f x ∈ E0LM.e0RegM N :=
  fun h => hx ((GX.mem_S0_iff_of_isE0Mor hf x).1 h)

/-- **The restriction of an `𝔼₀`-morphism to the regular parts.** -/
def regMap {f : M → N} (hf : IsE0Mor f univ) (x : E0LM.e0RegM M) : E0LM.e0RegM N :=
  ⟨f x, mem_e0RegM_of_isE0Mor hf x.2⟩

/-- **The restriction of an `𝔼₀`-morphism to the regular parts is a flat local isometry**: read
in the flat charts `regChartM` (an `𝔼₀` chart, then a regular chart of `Y`), it is an element of
`e0Groupoid` read in two regular charts of `Y`, locally in `Isom(𝐌³)`
(`E0LM.e0_flat_transition_aux`). -/
theorem isLocalIsometry_regMap {f : M → N} (hf : IsE0Mor f univ) :
    IsLocalIsometry 2 (regMap hf) := by
  have hfc : Continuous f := E0AbsMax.continuous_of_isE0Mor hf
  refine isLocalIsometry_iff_eventually.2
    ⟨(hfc.comp continuous_subtype_val).subtype_mk _, fun x => ?_⟩
  set m : M := (x : M) with hm
  obtain ⟨O, hxO, -, hO⟩ := (Causal.CBG.liftPropOn_iff_repOn isOpen_univ).1 hf m (mem_univ m)
  obtain ⟨hOo, -, -, -, t, ht, hme, heq⟩ := hO
  set em := chartAt E0Y m with hem
  set R := E0LM.regAtlasChart x with hR
  set R' := E0LM.regAtlasChart (regMap hf x) with hR'
  have hmR : em m ∈ R.source := E0LM.mem_regAtlasChart_source x
  have hfmR' : chartAt E0Y (f m) (f m) ∈ R'.source := E0LM.mem_regAtlasChart_source (regMap hf x)
  have hz0 : R (em m) ∈ (R.symm.trans (t.trans R')).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source, R.left_inv hmR]
    exact ⟨R.map_source hmR, hme hxO, by rw [← heq m hxO]; exact hfmR'⟩
  obtain ⟨g, hg⟩ := E0LM.e0_flat_transition_aux ht (E0LM.regAtlasChart_mem x)
    (E0LM.regAtlasChart_mem (regMap hf x)) _ hz0
  refine ⟨g, ?_⟩
  have hemc : ContinuousAt em m := em.continuousAt (mem_chart_source E0Y m)
  have hRc : ContinuousAt (fun z => R (em z)) m := (R.continuousAt hmR).comp hemc
  have E1 : ∀ᶠ z in 𝓝 m, z ∈ O := hOo.mem_nhds hxO
  have E2 : ∀ᶠ z in 𝓝 m, em z ∈ R.source := hemc.preimage_mem_nhds (R.open_source.mem_nhds hmR)
  have E4 := hRc.eventually hg
  have hall : ∀ᶠ z in 𝓝 m,
      R' (chartAt E0Y (f m) (f z)) = g • R (em z) := by
    filter_upwards [E1, E2, E4] with z h1 h2 h4
    simp only [OpenPartialHomeomorph.coe_trans, comp_apply] at h4
    rw [show (E0LM.regAtlasChart x).symm (R (em z)) = em z from R.left_inv h2] at h4
    rw [heq z h1]
    exact h4
  filter_upwards [(continuous_subtype_val.continuousAt (x := x)).eventually hall] with y hy
  have hc1 : chartAt (Causal.Minkowski 2) (regMap hf x) (regMap hf y) =
      R' (chartAt E0Y (f m) (f y)) := by
    show ((E0LM.regChartM (regMap hf x)).subtypeRestr ⟨regMap hf x⟩) (regMap hf y) = _
    rw [E0AbsMax.regChart_subtypeRestr_eq]
    rfl
  have hc2 : chartAt (Causal.Minkowski 2) x y = R (em y) := by
    show ((E0LM.regChartM x).subtypeRestr ⟨x⟩) y = _
    rw [E0AbsMax.regChart_subtypeRestr_eq]
    rfl
  rw [hc1, hc2]
  exact hy

/-- The restriction of a BTZ-embedding to the regular parts is an isometric embedding. -/
theorem isIsometricEmbedding_regMap {ι : M → N} (hι : IsBTZEmbedding ι) :
    IsIsometricEmbedding 2 (regMap hι.isE0Mor) :=
  ⟨isLocalIsometry_regMap hι.isE0Mor, fun _ _ hxy =>
    Subtype.ext (hι.injective (congrArg Subtype.val hxy))⟩

/-- **A BTZ-embedding maps `Reg M` onto `Reg N`**: a regular point of `N` is in the image (the
complement of the image is BTZ), and its preimage is regular (types of points are preserved). -/
theorem surjective_regMap {ι : M → N} (hι : IsBTZEmbedding ι) :
    Surjective (regMap hι.isE0Mor) := by
  intro y
  have hy : (y : N) ∈ range ι := by
    by_contra h
    exact y.2 (hι.compl_range_subset h)
  obtain ⟨x, hx⟩ := hy
  have hxr : x ∈ E0LM.e0RegM M := fun h => by
    have := (hι.mem_S0_iff x).2 h
    rw [hx] at this
    exact y.2 this
  exact ⟨⟨x, hxr⟩, Subtype.ext hx⟩

variable [T2Space M] [ConnectedSpace M] [T2Space N] [ConnectedSpace N]

/-- **GH, MGH and Cauchy-completeness of the regular part pass from a BTZ-extension back to
`M`**, along the isometry `Reg M ≅ Reg N` that the BTZ-embedding induces. -/
theorem regM_of_isBTZEmbedding {ι : M → N} (hι : IsBTZEmbedding ι)
    (h : GH (e0RegMFlat N) ∧ MGH (e0RegMFlat N) ∧ IsCauchyComplete 2 (e0RegMFlat N)) :
    GH (e0RegMFlat M) ∧ MGH (e0RegMFlat M) ∧ IsCauchyComplete 2 (e0RegMFlat M) := by
  have hs : Surjective (regMap hι.isE0Mor) := surjective_regMap hι
  have hψ : IsIsometricEmbedding 2 (surjInv hs) :=
    isIsometricEmbedding_surjInv (isIsometricEmbedding_regMap hι) hs
  exact transfer_of_isIsometricEmbedding_of_surjective (A := e0RegMFlat N) (B := e0RegMFlat M)
    (φ := surjInv hs) hψ
    (leftInverse_surjInv ⟨(isIsometricEmbedding_regMap hι).injective, hs⟩).surjective h

end RegMap

/-! ### §3 The two implications -/

section Implications

open E0CBG E0Spear E0RegComplete BTZMax

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **(ii) and (iii)'s predicate**: the extension is Cauchy-complete (`E0C1CauchyComplete`,
OQ-142 (e)) and Cauchy-maximal (`IsE0CauchyMaximal`). -/
def CauchyCompleteMaximal (X : GHExt M) : Prop :=
  haveI := connectedSpace_N X
  E0C1CauchyComplete X.N ∧ IsE0CauchyMaximal X.N

/-- **(i)**: `Reg M` is globally hyperbolic, Cauchy-maximal and Cauchy-complete
(OQ-142 (e)(f)). -/
def RegCauchyCompleteMaximal (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] : Prop :=
  GH (e0RegMFlat M) ∧ MGH (e0RegMFlat M) ∧ IsCauchyComplete 2 (e0RegMFlat M)

omit [T2Space M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **btz `theo:BTZ_Cauchy-completness`, (iii) ⇒ (ii)** (l.1593, « trivial »): if a maximal
globally hyperbolic BTZ-extension of `M` is Cauchy-complete and Cauchy-maximal, some
BTZ-extension of `M` is. -/
theorem iii_imp_ii (E : GHExt M)
    (_hE : Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E)
    (h : CauchyCompleteMaximal E) : ∃ X : GHExt M, CauchyCompleteMaximal X :=
  ⟨E, h⟩

omit [SecondCountableTopology M] in
/-- **btz `theo:BTZ_Cauchy-completness`, (ii) ⇒ (i)** (l.1593, « a consequence of Proposition
prop:reg_complete »): if a globally hyperbolic BTZ-extension `ι : M → N` is Cauchy-complete and
Cauchy-maximal, then `Reg M` is globally hyperbolic, Cauchy-maximal and Cauchy-complete:
`prop_reg_complete'` for `N`, carried back along `Reg M ≅ Reg N`. The global hyperbolicity of
`M` (the theorem's standing hypothesis) is not used. -/
theorem ii_imp_i (h : ∃ X : GHExt M, CauchyCompleteMaximal X) : RegCauchyCompleteMaximal M := by
  obtain ⟨X, hX⟩ := h
  haveI := connectedSpace_N X
  obtain ⟨hCC, hmax⟩ := hX
  exact regM_of_isBTZEmbedding X.isBTZ (prop_reg_complete' X.gh hCC hmax)

omit [SecondCountableTopology M] in
/-- **(iii) ⇒ (i)**, the composite. -/
theorem iii_imp_i (E : GHExt M)
    (hE : Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E)
    (h : CauchyCompleteMaximal E) : RegCauchyCompleteMaximal M :=
  ii_imp_i (iii_imp_ii E hE h)

end Implications

end BTZCauchyEasy

end GX
