import GX.BTZ.Ppcm
import Causal.AbstractDev

/-!
# btz § 5.3: the maximal BTZ-extension of a globally hyperbolic `𝔼₀`-manifold, as an instance of `Causal.AbstractDev`

Target `T-btz-maximal-extension` (`roadmap/roadmap.toml`, DEC-208). `papers/btz/legacy/labeled/BTZ_1.tex`.
None of the three rows is marked: `𝔼₀`-manifolds only (T-btz-scope), `M` connected is added (as
in `GX.Ppcm.btz_ppcm`, which the uniqueness uses), and the second bullet of the proof is carried
as the named cited input `GX.BTZMax.RichardsInput`, equivalent to « countably many BTZ lines »
(`GX.BTZLine.CountableLinesInput`, Richards' theorem MR143186; each line's second countability is
proved, `GX.BTZLine.secondCountable_line`).

* `btzthm:BTZ_ext` — `BTZ_1.tex:1528` (proof l.1535–1554) — `GX.BTZMax.btz_ext` (existence of a
  globally hyperbolic BTZ-extension maximal among such, inextensible, universal, unique up to
  equivalence; under `RichardsInput`), with `GX.BTZMax.chainsInherit` (the union of a coherent
  chain), `GX.BTZMax.uniqueMorphisms`, `GX.BTZMax.isUniversal_of_isMaximal`,
  `GX.BTZMax.equivalent_of_isMaximal`.
* `btzthm:maximal_btz_extension` — `BTZ_1.tex:1269` — the same `GX.BTZMax.btz_ext`
  (« unique up to isomorphism »: an equivalence is an isomorphism over `M`).
* `btzthm:globally_hyperbolic_manifolds_exists` — `BTZ_1.tex:331` — the same `GX.BTZMax.btz_ext`
  (the introduction's statement, verbatim l.1529–1532).

> Let $M$ be globally hyperbolic $\mass{\geq 0}$-manifolds, there exists a globally hyperbolic
> BTZ-extension $M\xrightarrow{\iota} N$ which is maximal among such extensions. Moreover,
> $M\xrightarrow{\iota}N$ is unique up to equivalence. (l.1529–1530)
>
> Define $\overline M:= \varinjlim N$ as the inductive limit […] where $N$ goes through the
> BTZ-extensions of $M$. This inductive limit is well defined, since the family of BTZ-extensions
> of $M$ is right filtered by Proposition \ref{prop:ppcm} and the BTZ-extensions of $M$ all have
> the same cardinality. (l.1536)
>
> An inductive limit $N$ of BTZ-extensions of $M$ which is second countable is globally
> hyperbolic. Indeed, by Corollary \ref{cor:GH_causal}, $N$ is causal. Furthermore, for any
> $p,q \in N$, there exists a globally hyperbolic BTZ-extension $M_1$ of $M$ which contains $p$
> and $q$. By Lemma \ref{lem:BTZext_caus_conv}, $M_1$ is causally convex in $N$. Finally,
> $J^+_{N}(p)\cap J^-_{N}(q) = J^+_{M_1}(p)\cap J^-_{M_1}(q)$ which is compact. (l.1541)
>
> Let $\Sigma$ be a Cauchy surface of $M$. Each BTZ line of $\overline M\setminus M$ is associated
> to a puncture of $\Sigma$ ie an end which admits a disc neighborhood. By Richards Theorem
> \cite{MR143186}, a surface can only have countably many such ends. Therefore,
> $\sing_0(\overline M)$ has at most countably many connected components. […] Finally, $\Delta$
> admits a Riemannian metric and is thus second countable. (l.1544–1546)

## Hypothesis checklist (`btz_ext`)

| paper hypothesis | here |
|---|---|
| `𝔼_{≥0}`-manifolds | ⚠ `𝔼₀` only (T-btz-scope) |
| `M` globally hyperbolic | ✓ carried |
| `M` Hausdorff, second countable (l.261) | ✓ carried |
| (none) | ⚠ strengthened: `M` connected (`E0AbsMax.e0_sfa_of_globalBTZ` on the union, and `GX.Ppcm.btz_ppcm` for uniqueness) |
| Richards' theorem MR143186 and the line-to-puncture association (l.1544) | ⚠ named cited input `RichardsInput M`: in a Hausdorff connected `𝔼₀`-manifold any two points of which lie in one open, second countable, globally hyperbolic BTZ-extension of `M`, `sing₀` is Lindelöf. It is equivalent (`GX.BTZLine.richardsInput_iff_countableLines`, `GXScaffold.BTZ.LineStructure`) to `GX.BTZLine.CountableLinesInput M`, « countably many BTZ lines », the form of record: the second countability of each line (l.1546) is proved there (`GX.BTZLine.secondCountable_line`), not cited. The theorems restated on `CountableLinesInput` are in `GXScaffold.BTZ.RichardsSplit` (`GX.BTZMax.btz_ext_of_countableLines`) |
| « maximal among such extensions » | ✓ carried as `AbstractDev.IsMaximal`, strengthened: inextensible (`IsInextensible`) and universal (every globally hyperbolic BTZ-extension maps into it) |
| « unique up to equivalence » | ✓ carried: every maximal one is equivalent to it (a bijective BTZ-embedding over `M`) |

## SCOPE (disclosed)

* **The route.** The paper's inductive limit over all BTZ-extensions is replaced by Zorn
  (`Causal.AbstractDev.exists_isMaximal_of_uniqueMorphisms`, Chruściel's route): developments the
  globally hyperbolic BTZ-extensions of `M` (`GHExt`), morphisms the BTZ-embeddings over `M`
  (`extMor`), unique by density of `ι(M)` (`uniqueMorphisms`). Chain inheritance is the paper's
  two bullets for a chain: the union of a coherent chain is built in `Type` as a set of filters on
  `M` (the germ `comap ι (𝓝 x)` of a point; injective since `ι(M)` is dense and the extension
  Hausdorff), with the final topology, the glued atlas (`Causal.CBG.gluedChartedSpace`), Hausdorff
  (two points lie in one member), second countable from `RichardsInput`, globally hyperbolic by
  the paper's first bullet (`globallyHyperbolic_of_iCover`, which needs no directedness). The paper's « right filtered by
  Proposition ppcm » becomes, after Zorn, the universality of the maximal extension
  (`isUniversal_of_isMaximal`, through `GX.Ppcm.btz_ppcm`), whence uniqueness.
* **The cited input** is not Richards' classification itself, which is not in mathlib: it is the
  consequence the proof draws from it, in the form « `sing₀` is Lindelöf ». It is a hypothesis of
  `btz_ext`, never an axiom. The second countability of each line is not part of what is cited:
  it is proved in `GXScaffold.BTZ.LineStructure`, where `RichardsInput` is shown equivalent to
  `GX.BTZLine.CountableLinesInput` (« countably many lines », the form of record); `btz_ext` on that
  input is `GX.BTZMax.btz_ext_of_countableLines` (`GXScaffold.BTZ.RichardsSplit`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open E0CBG E0Spear

namespace BTZMax

/-! ### §1 The developments: globally hyperbolic BTZ-extensions of `M`, and their morphisms -/

section Dev

variable (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M]

/-- **A globally hyperbolic BTZ-extension of `M`** (`BTZ_1.tex:1529`): an `𝔼₀`-manifold `N`,
globally hyperbolic, with a BTZ-embedding `M → N`. -/
structure GHExt where
  /-- The extension. -/
  N : E0Mfd
  /-- The BTZ-embedding. -/
  ι : M → N
  isBTZ : IsBTZEmbedding ι
  gh : (CE N).GloballyHyperbolic

/-- **The morphisms**: BTZ-embeddings over `M`. -/
def extMor (X Y : GHExt M) (f : X.N → Y.N) : Prop := IsBTZEmbedding f ∧ f ∘ X.ι = Y.ι

/-- **Equivalence of extensions** (`BTZ_1.tex:1530`): a bijective morphism. -/
def Equivalent (X Y : GHExt M) : Prop := ∃ f : X.N → Y.N, extMor M X Y f ∧ Bijective f

variable {M}

theorem morphismsCompose :
    Causal.AbstractDev.MorphismsCompose (carrier := fun X : GHExt M => (X.N : Type))
      (extMor M) where
  isMor_id X := ⟨isBTZEmbedding_id, rfl⟩
  isMor_comp _ _ _ _ _ hf hg := ⟨hg.1.comp hf.1, by rw [comp_assoc, hf.2, hg.2]⟩

/-- **Morphisms are unique** (Liouville in its density form: two continuous maps agreeing on the
dense `ι(M)`). -/
theorem uniqueMorphisms :
    Causal.AbstractDev.UniqueMorphisms (carrier := fun X : GHExt M => (X.N : Type))
      (extMor M) := by
  intro X Y f g hf hg
  refine X.isBTZ.ext hf.1.continuous hg.1.continuous ?_
  rw [hf.2, hg.2]

end Dev

/-! ### §2 The union of a chain, in `Type`: germs of points as filters on `M` -/

section Germ

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]

/-- The germ of a point of an extension: the trace on `M` of its neighbourhood filter. -/
def germ (X : GHExt M) (x : X.N) : Filter M := Filter.comap X.ι (𝓝 x)

/-- A morphism preserves germs. -/
theorem germ_map {X Y : GHExt M} {f : X.N → Y.N} (hf : extMor M X Y f) (x : X.N) :
    germ Y (f x) = germ X x := by
  unfold germ
  rw [← hf.2, ← Filter.comap_comap, ← hf.1.isEmbedding.isInducing.nhds_eq_comap]

/-- The germ map is injective (`X.N` Hausdorff, `ι(M)` dense). -/
theorem germ_injective (X : GHExt M) : Injective (germ X) := by
  intro x y hxy
  by_contra hne
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hne
  have h1 : X.ι ⁻¹' u ∈ germ X x := preimage_mem_comap (hu.mem_nhds hxu)
  have h2 : X.ι ⁻¹' v ∈ germ X x := hxy ▸ preimage_mem_comap (hv.mem_nhds hyv)
  have h3 : X.ι ⁻¹' (u ∩ v) ∈ germ X x := by rw [preimage_inter]; exact inter_mem h1 h2
  rw [huv.inter_eq, preimage_empty] at h3
  obtain ⟨t, ht, hts⟩ := mem_comap.1 h3
  obtain ⟨_, hz, m, rfl⟩ := mem_closure_iff_nhds.1 (X.isBTZ.dense_range x) t ht
  exact hts hz

variable {ι : Type*} (X : ι → GHExt M)

/-- **The carrier of the union** of a family of extensions: the germs of their points. -/
def Carrier : Type := {F : Filter M // ∃ i, ∃ x : (X i).N, germ (X i) x = F}

/-- The map of a member into the union. -/
def inj (i : ι) (x : (X i).N) : Carrier X := ⟨germ (X i) x, i, x, rfl⟩

/-- The final topology of the union. -/
instance : TopologicalSpace (Carrier X) :=
  ⨆ i, TopologicalSpace.coinduced (inj X i) inferInstance

theorem inj_injective (i : ι) : Injective (inj X i) := fun _ _ h =>
  germ_injective (X i) (congrArg Subtype.val h)

theorem inj_cover (z : Carrier X) : ∃ i, z ∈ range (inj X i) := by
  obtain ⟨F, i, x, rfl⟩ := z
  exact ⟨i, x, rfl⟩

theorem continuous_inj (i : ι) : Continuous (inj X i) :=
  continuous_iff_coinduced_le.2 (le_iSup (fun i => TopologicalSpace.coinduced (inj X i)
    inferInstance) i)

end Germ

/-! ### §3 The named cited input, and global hyperbolicity of a cover (the first bullet) -/

section Input

/-- **The named cited input** (the second bullet of the proof, `BTZ_1.tex:1544–1546`: Richards'
theorem MR143186, « a surface can only have countably many such ends », whence countably many BTZ
lines, and the second countability of each line through its `(ℝ,ℝ)`-structure): in a Hausdorff,
connected `𝔼₀`-manifold `C` with a BTZ-embedding of `M`, any two points of which lie in an open,
second countable, globally hyperbolic BTZ-extension of `M`, the BTZ locus is Lindelöf. Carried as a
hypothesis, never an axiom; not proved here. -/
def RichardsInput (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] : Prop :=
  ∀ (C : Type) [TopologicalSpace C] [T2Space C] [ConnectedSpace C] [ChartedSpace E0Y C]
    [HasGroupoid C e0Groupoid] (ι : M → C), IsBTZEmbedding ι →
    (∀ p q : C, ∃ U : Opens C, p ∈ U ∧ q ∈ U ∧ range ι ⊆ U ∧
      SecondCountableTopology U ∧ (CE C).GloballyHyperbolicOn U) →
    IsLindelof (S0 C)

/-- **The first bullet of the proof** (`BTZ_1.tex:1541`): an `𝔼₀`-manifold covered by the images of
BTZ-embeddings of globally hyperbolic manifolds is globally hyperbolic. Causal by Cor 2.15, and the
diamond of `p ≤ q` lies in the image containing `p` (a future set, `GX.Ppcm.mem_range_of_le`),
which is causally convex (Lemma 2.13 (b)). -/
theorem globallyHyperbolic_of_iCover {Z : Type} [TopologicalSpace Z] [ChartedSpace E0Y Z]
    [T2Space Z] [ConnectedSpace Z] [SecondCountableTopology Z] [HasGroupoid Z e0Groupoid]
    {κ : Type*} {Y : κ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, ChartedSpace E0Y (Y k)]
    [∀ k, HasGroupoid (Y k) e0Groupoid] {a : ∀ k, Y k → Z} (ha : ∀ k, IsBTZEmbedding (a k))
    (hG : ∀ k, (CE (Y k)).GloballyHyperbolic) (hcov : ∀ z, ∃ k, z ∈ range (a k)) :
    (CE Z).GloballyHyperbolic := by
  have h := E0AbsMax.e0_sfa_of_globalBTZ Z
  obtain ⟨k₀, -⟩ := hcov (Classical.arbitrary Z)
  refine ⟨E0AbsMax.cor_GH_causal_e0 (A := (ha k₀).rangeOpens) (ha k₀).compl_range_subset
    (Ppcm.globallyHyperbolicOn_range (ha k₀) (hG k₀)), fun p q => ?_⟩
  by_cases hpq : (CE Z).le ⊤ p q
  · obtain ⟨k, hp⟩ := hcov p
    have hGA := Ppcm.globallyHyperbolicOn_range (ha k) (hG k)
    have hcA := E0AbsMax.btzExt_causallyConvexIn_of_globallyHyperbolicOn_e0
      (A := (ha k).rangeOpens) (ha k).compl_range_subset hGA
    have hq := Ppcm.mem_range_of_le (ha k) (hG k) hp hpq
    rw [← E0AbsMax.diamond_eq_of_subset h.causallyArcConnected (hcA.2 p hp q hq)]
    exact hGA.2 p q
  · have : (CE Z).diamond ⊤ p q = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun z hz => hpq ?_
      obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hz
      exact (CE Z).le_trans h1 h2
    rw [this]
    exact isCompact_empty

end Input

/-! ### §4 The union of a coherent chain (chain inheritance) -/

section Chain

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]

/-- A non-empty extension class: every extension of a non-empty `M` is non-empty. -/
instance nonempty_N [Nonempty M] (X : GHExt M) : Nonempty X.N := ⟨X.ι (Classical.arbitrary M)⟩

variable {ι : Type*} {r : ι → ι → Prop} {X : ι → GHExt M}
  {φ : ∀ ⦃i j : ι⦄, r i j → (X i).N → (X j).N}

variable (r X φ) in
/-- The coherent chains of the class (`Causal.AbstractDev.IsCoherentChain`). -/
abbrev Chain : Prop :=
  Causal.AbstractDev.IsCoherentChain (carrier := fun Y : GHExt M => (Y.N : Type)) (extMor M) r X φ

theorem inj_map (hc : Chain r X φ) {i j : ι} (h : r i j) (x : (X i).N) :
    inj X j (φ h x) = inj X i x :=
  Subtype.ext (germ_map (hc.isMor h) x)

theorem preimage_image_of_le (hc : Chain r X φ) {i j : ι} (h : r i j) (U : Set (X i).N) :
    inj X j ⁻¹' (inj X i '' U) = φ h '' U := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, inj_injective X j ((inj_map hc h x).trans hxy)⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (inj_map hc h x).symm⟩

theorem preimage_image_of_ge (hc : Chain r X φ) {i j : ι} (h : r j i) (U : Set (X i).N) :
    inj X j ⁻¹' (inj X i '' U) = φ h ⁻¹' U := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have : x = φ h y := inj_injective X i (hxy.trans (inj_map hc h y).symm)
    rw [mem_preimage, ← this]
    exact hx
  · intro hy
    exact ⟨φ h y, hy, inj_map hc h y⟩

theorem isOpenMap_inj (hc : Chain r X φ) (i : ι) : IsOpenMap (inj X i) := by
  intro U hU
  rw [isOpen_iSup_iff]
  intro j
  rw [isOpen_coinduced]
  rcases hc.total i j with h | h
  · rw [preimage_image_of_le hc h]
    exact (hc.isMor h).1.isOpenEmbedding.isOpenMap U hU
  · rw [preimage_image_of_ge hc h]
    exact hU.preimage (hc.isMor h).1.continuous

theorem isOpenEmbedding_inj (hc : Chain r X φ) (i : ι) : IsOpenEmbedding (inj X i) :=
  .of_continuous_injective_isOpenMap (continuous_inj X i) (inj_injective X i)
    (isOpenMap_inj hc i)

/-- **The union of a chain is Hausdorff**: two points lie in one member. -/
theorem t2Space_carrier (hc : Chain r X φ) : T2Space (Carrier X) := by
  have key : ∀ {i j : ι} (h : r i j) (x : (X i).N) (y : (X j).N), inj X i x ≠ inj X j y →
      ∃ u v : Set (Carrier X), IsOpen u ∧ IsOpen v ∧ inj X i x ∈ u ∧ inj X j y ∈ v ∧
        Disjoint u v := by
    intro i j h x y hne
    rw [← inj_map hc h x] at hne ⊢
    have hne' : φ h x ≠ y := fun e => hne (by rw [e])
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hne'
    exact ⟨inj X j '' u, inj X j '' v, isOpenMap_inj hc j u hu, isOpenMap_inj hc j v hv,
      mem_image_of_mem _ hxu, mem_image_of_mem _ hyv,
      (disjoint_image_iff (inj_injective X j)).2 huv⟩
  refine ⟨fun z z' hne => ?_⟩
  obtain ⟨i, x, rfl⟩ := inj_cover X z
  obtain ⟨j, y, rfl⟩ := inj_cover X z'
  rcases hc.total i j with h | h
  · exact key h x y hne
  · obtain ⟨u, v, hu, hv, hyu, hxv, huv⟩ := key h y x (Ne.symm hne)
    exact ⟨v, u, hv, hu, hxv, hyu, huv.symm⟩

variable [Nonempty M]

/-- **The glued atlas of the union** (`BTZ_1.tex:1538`, « the `𝔼≥0`-structure induced by the
(open) topological embeddings `N → M̄` »). -/
@[reducible] noncomputable def unionCS (hc : Chain r X φ) : ChartedSpace E0Y (Carrier X) :=
  Causal.CBG.gluedChartedSpace E0Y (isOpenEmbedding_inj hc) (inj_cover X)

/-- The transitions of the glued atlas: `φ` forwards, `φ⁻¹` on its image backwards. -/
theorem trans_inj (hc : Chain r X φ) (i j : ι) :
    ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt
      (Causal.CBG.glueTransition (isOpenEmbedding_inj hc) i j)
      (inj X i ⁻¹' range (inj X j)) := by
  have he := isOpenEmbedding_inj hc
  have hsymm : ∀ k (x : (X k).N), (Causal.CBG.glueEmb he k).symm (inj X k x) = x :=
    fun k x => Causal.CBG.glueEmb_symm_apply he k x
  have hW : IsOpen (inj X i ⁻¹' range (inj X j)) :=
    (he j).isOpen_range.preimage (he i).continuous
  rcases hc.total i j with h | h
  · refine Causal.CBG.liftPropOn_congr_of_eqOn hW (Causal.CBG.liftPropOn_mono_of_le isOpen_univ hW
      (hc.isMor h).1.isE0Mor (subset_univ _)) fun x _ => ?_
    show φ h x = (Causal.CBG.glueEmb he j).symm (inj X i x)
    rw [← inj_map hc h x, hsymm]
  · have hR : inj X i ⁻¹' range (inj X j) = range (φ h) := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, inj_injective X i ((inj_map hc h y).trans hy)⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, (inj_map hc h y).symm⟩
    show ChartedSpace.LiftPropOn _ _ (inj X i ⁻¹' range (inj X j))
    rw [hR]
    obtain ⟨G, hG, hGφ⟩ := Pgcd.exists_ext (hc.isMor h).1
      (Causal.CBG.liftPropOn_id (G := e0Groupoid) (M := (X j).N) isOpen_univ)
    refine Causal.CBG.liftPropOn_congr_of_eqOn (hc.isMor h).1.isOpen_range hG ?_
    rintro _ ⟨y, rfl⟩
    show G (φ h y) = (Causal.CBG.glueEmb he j).symm (inj X i (φ h y))
    rw [inj_map hc h y, hsymm, hGφ]
    rfl

theorem unionCS_hasGroupoid (hc : Chain r X φ) :
    @HasGroupoid E0Y _ (Carrier X) _ (unionCS hc) e0Groupoid :=
  Causal.CBG.gluedChartedSpace_hasGroupoid _ (inj_cover X) (trans_inj hc)

theorem isE0Mor_inj (hc : Chain r X φ) (i : ι) :
    letI := unionCS hc; IsE0Mor (inj X i) univ :=
  Causal.CBG.liftPropOn_glue (isOpenEmbedding_inj hc) (inj_cover X) (trans_inj hc) i

/-- **Each member is a BTZ-extension of the union** (its complement: the points of later members
outside its image, BTZ). -/
theorem isBTZ_inj (hc : Chain r X φ) (i : ι) :
    letI := unionCS hc; IsBTZEmbedding (inj X i) := by
  letI := unionCS hc
  refine isBTZEmbedding_iff_injective.2 ⟨inj_injective X i, isE0Mor_inj hc i, fun z hz => ?_⟩
  obtain ⟨j, y, rfl⟩ := inj_cover X z
  rcases hc.total i j with h | h
  · have hy : y ∉ range (φ h) := by
      rintro ⟨x, rfl⟩
      exact hz ⟨x, (inj_map hc h x).symm⟩
    exact (mem_S0_iff_of_isE0Mor (isE0Mor_inj hc j) y).2 ((hc.isMor h).1.compl_range_subset hy)
  · exact absurd ⟨φ h y, inj_map hc h y⟩ hz

omit [Nonempty M] in
/-- The embeddings of `M` through the members agree. -/
theorem inj_comp_ι (hc : Chain r X φ) (i j : ι) : inj X i ∘ (X i).ι = inj X j ∘ (X j).ι := by
  have key : ∀ {i j : ι}, r i j → inj X j ∘ (X j).ι = inj X i ∘ (X i).ι := fun {i j} h => by
    rw [← (hc.isMor h).2, ← comp_assoc]
    exact congrArg (· ∘ (X i).ι) (funext (inj_map hc h))
  rcases hc.total i j with h | h
  · exact (key h).symm
  · exact key h

theorem connectedSpace_carrier [ConnectedSpace M] (hc : Chain r X φ) (i₀ : ι) :
    letI := unionCS hc; ConnectedSpace (Carrier X) := by
  letI := unionCS hc
  haveI := unionCS_hasGroupoid hc
  have hb := (isBTZ_inj hc i₀).comp (X i₀).isBTZ
  have h := isPreconnected_range hb.continuous
  refine { isPreconnected_univ := ?_, toNonempty := ⟨inj X i₀ ((X i₀).ι (Classical.arbitrary M))⟩ }
  rw [← hb.dense_range.closure_eq]
  exact h.closure

/-- **The union is second countable** (the second bullet, from the named input): `sing₀` is
covered by countably many members, and the rest lies in one. -/
theorem secondCountable_carrier [ConnectedSpace M] (hc : Chain r X φ) (i₀ : ι)
    (hR : RichardsInput M) : letI := unionCS hc; SecondCountableTopology (Carrier X) := by
  letI := unionCS hc
  haveI := unionCS_hasGroupoid hc
  haveI := t2Space_carrier hc
  haveI := connectedSpace_carrier hc i₀
  have hbtz : ∀ k, IsBTZEmbedding (inj X k) := fun k => isBTZ_inj hc k
  have hsc : ∀ k, SecondCountableTopology (range (inj X k)) := fun k =>
    ((isOpenEmbedding_inj hc k).isEmbedding.toHomeomorph).symm.secondCountableTopology
  have hb : IsBTZEmbedding (inj X i₀ ∘ (X i₀).ι) := (hbtz i₀).comp (X i₀).isBTZ
  have hk : ∀ k, ∀ p q : Carrier X, p ∈ range (inj X k) → q ∈ range (inj X k) →
      ∃ U : Opens (Carrier X), p ∈ U ∧ q ∈ U ∧ range (inj X i₀ ∘ (X i₀).ι) ⊆ U ∧
        SecondCountableTopology U ∧ (CE (Carrier X)).GloballyHyperbolicOn U := by
    intro k p q hp hq
    refine ⟨(hbtz k).rangeOpens, hp, hq, ?_, hsc k,
      Ppcm.globallyHyperbolicOn_range (hbtz k) (X k).gh⟩
    rw [inj_comp_ι hc i₀ k]
    exact range_comp_subset_range _ _
  have hdir : ∀ p q : Carrier X, ∃ U : Opens (Carrier X), p ∈ U ∧ q ∈ U ∧
      range (inj X i₀ ∘ (X i₀).ι) ⊆ U ∧ SecondCountableTopology U ∧
        (CE (Carrier X)).GloballyHyperbolicOn U := by
    intro p q
    obtain ⟨i, x, rfl⟩ := inj_cover X p
    obtain ⟨j, y, rfl⟩ := inj_cover X q
    rcases hc.total i j with h | h
    · exact hk j _ _ ⟨φ h x, inj_map hc h x⟩ ⟨y, rfl⟩
    · exact hk i _ _ ⟨x, rfl⟩ ⟨φ h y, inj_map hc h y⟩
  have hL := hR (Carrier X) (inj X i₀ ∘ (X i₀).ι) hb hdir
  obtain ⟨T, hT, hcovT⟩ := hL.elim_countable_subcover (fun i => range (inj X i))
    (fun i => (isOpenEmbedding_inj hc i).isOpen_range) (fun z _ => mem_iUnion.2 (inj_cover X z))
  haveI : Countable (insert i₀ T : Set ι) := (hT.insert i₀).to_subtype
  haveI : ∀ t : (insert i₀ T : Set ι), SecondCountableTopology (range (inj X t)) :=
    fun t => hsc t
  refine secondCountableTopology_of_countable_cover
    (U := fun t : (insert i₀ T : Set ι) => range (inj X t))
    (fun t => (isOpenEmbedding_inj hc t).isOpen_range) ?_
  refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
  by_cases hz : z ∈ S0 (Carrier X)
  · obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.1 (hcovT hz)
    exact ⟨⟨t, mem_insert_of_mem _ ht⟩, hzt⟩
  · have : z ∈ range (inj X i₀ ∘ (X i₀).ι) := by_contra fun h => hz (hb.compl_range_subset h)
    obtain ⟨m, rfl⟩ := this
    exact ⟨⟨i₀, mem_insert _ _⟩, _, rfl⟩

/-- **The union of a coherent chain, as an `𝔼₀`-manifold.** -/
noncomputable def unionMfd [ConnectedSpace M] (hc : Chain r X φ) (i₀ : ι)
    (hR : RichardsInput M) : E0Mfd :=
  letI := unionCS hc
  haveI := unionCS_hasGroupoid hc
  haveI := t2Space_carrier hc
  haveI := secondCountable_carrier hc i₀ hR
  E0Mfd.of (Carrier X)

/-- **The union of a coherent chain, as a globally hyperbolic BTZ-extension of `M`** (the first
bullet, `BTZ_1.tex:1541`). -/
noncomputable def unionExt [ConnectedSpace M] (hc : Chain r X φ) (i₀ : ι)
    (hR : RichardsInput M) : GHExt M where
  N := unionMfd hc i₀ hR
  ι := inj X i₀ ∘ (X i₀).ι
  isBTZ := by
    letI := unionCS hc
    exact (isBTZ_inj hc i₀).comp (X i₀).isBTZ
  gh := by
    haveI : ConnectedSpace (unionMfd hc i₀ hR) := connectedSpace_carrier hc i₀
    exact globallyHyperbolic_of_iCover (Z := unionMfd hc i₀ hR) (Y := fun i => ((X i).N : Type))
      (a := inj X) (isBTZ_inj hc) (fun i => (X i).gh) (inj_cover X)

end Chain

/-! ### §5 Zorn, universality, uniqueness: `btzthm:BTZ_ext` -/

section Main

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]

/-- **Chain inheritance** (`BTZ_1.tex:1535–1550`, for a chain): the union of a non-empty coherent
chain of globally hyperbolic BTZ-extensions is one, and an upper bound. -/
theorem chainsInherit [ConnectedSpace M] (hR : RichardsInput M) :
    Causal.AbstractDev.ChainsInherit.{1} (carrier := fun X : GHExt M => (X.N : Type))
      (extMor M) := by
  intro ι _ hne r X φ hc
  obtain ⟨i₀⟩ := hne
  refine ⟨unionExt hc i₀ hR, fun i => inj X i, ⟨fun i => ⟨isBTZ_inj hc i, inj_comp_ι hc i i₀⟩,
    fun i j h => funext (inj_map hc h)⟩⟩

/-- `M` itself, the trivial extension. -/
def base [T2Space M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] (hG : (CE M).GloballyHyperbolic) : GHExt M := ⟨E0Mfd.of M, id, isBTZEmbedding_id, hG⟩

/-- An extension of a connected `M` is connected (`ι(M)` is dense). -/
theorem connectedSpace_N [ConnectedSpace M] (X : GHExt M) : ConnectedSpace X.N := by
  have h := isPreconnected_range X.isBTZ.continuous
  refine { isPreconnected_univ := ?_, toNonempty := ⟨X.ι (Classical.arbitrary M)⟩ }
  rw [← X.isBTZ.dense_range.closure_eq]
  exact h.closure

/-- **A maximal extension is inextensible** (rigidity from unique morphisms). -/
theorem isInextensible_of_isMaximal {E : GHExt M}
    (hE : Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E) :
    Causal.AbstractDev.IsInextensible (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E :=
  hE.isInextensible morphismsCompose (uniqueMorphisms.rigidEndomorphisms morphismsCompose)

/-- **A maximal extension is universal** (the paper's « right filtered by Proposition ppcm »,
`BTZ_1.tex:1536`): every globally hyperbolic BTZ-extension maps into it, through `M₁ ∨ M₂`. -/
theorem isUniversal_of_isMaximal [ConnectedSpace M] {E : GHExt M}
    (hE : Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E)
    (Y : GHExt M) : ∃ f : Y.N → E.N, extMor M Y E f := by
  haveI := connectedSpace_N E
  obtain ⟨P, hGP, -, -⟩ := Ppcm.btz_ppcm E.isBTZ Y.isBTZ E.gh Y.gh
  let W : GHExt M := ⟨P.X, P.a ∘ E.ι, P.ha.comp E.isBTZ, hGP⟩
  have hEW : extMor M E W P.a := ⟨P.ha, rfl⟩
  obtain ⟨-, g, hg, hga, -⟩ := isInextensible_of_isMaximal hE W P.a hEW
  refine ⟨g ∘ P.b, hg.1.comp P.hb, ?_⟩
  show g ∘ P.b ∘ Y.ι = E.ι
  rw [← P.comm, ← comp_assoc, hga, id_comp]

/-- **Uniqueness up to equivalence** (`BTZ_1.tex:1530`): two maximal globally hyperbolic
BTZ-extensions of `M` are equivalent. -/
theorem equivalent_of_isMaximal [ConnectedSpace M] {E E' : GHExt M}
    (hE : Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E)
    (hE' : Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M)
      E') : Equivalent M E E' := by
  obtain ⟨f, hf⟩ := isUniversal_of_isMaximal hE E'
  obtain ⟨g, hg⟩ := hE' E f hf
  have h1 : g ∘ f = id := uniqueMorphisms E' E' _ _ (morphismsCompose.isMor_comp hf hg)
    (morphismsCompose.isMor_id E')
  have h2 : f ∘ g = id := uniqueMorphisms E E _ _ (morphismsCompose.isMor_comp hg hf)
    (morphismsCompose.isMor_id E)
  exact ⟨g, hg, (LeftInverse.injective (congrFun h2)), (RightInverse.surjective (congrFun h1))⟩

/-- **`btzthm:BTZ_ext`** (unmarked: `𝔼₀` only, `M` connected added, `RichardsInput` named)
(`BTZ_1.tex:1528–1532`; also `btzthm:maximal_btz_extension`, l.1269, and
`btzthm:globally_hyperbolic_manifolds_exists`, l.331): a globally hyperbolic `𝔼₀`-manifold `M` has
a globally hyperbolic BTZ-extension `E` maximal among such extensions — inextensible, and every
globally hyperbolic BTZ-extension of `M` maps into it — unique up to equivalence. -/
theorem btz_ext [T2Space M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid]
    [ConnectedSpace M] (hG : (CE M).GloballyHyperbolic) (hR : RichardsInput M) :
    ∃ E : GHExt M,
      Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E ∧
      Causal.AbstractDev.IsInextensible (carrier := fun X : GHExt M => (X.N : Type)) (extMor M)
        E ∧
      (∀ Y : GHExt M, ∃ f : Y.N → E.N, extMor M Y E f) ∧
      ∀ E' : GHExt M,
        Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E' →
          Equivalent M E E' := by
  obtain ⟨E, -, -, hE⟩ := Causal.AbstractDev.exists_isMaximal_of_uniqueMorphisms morphismsCompose
    uniqueMorphisms (chainsInherit hR) (base hG)
  exact ⟨E, hE, isInextensible_of_isMaximal hE, isUniversal_of_isMaximal hE,
    fun E' hE' => equivalent_of_isMaximal hE hE'⟩

end Main

end BTZMax

end GX
