import GX.BTZ.PpcmHausdorff

/-!
# btz § 5.2: the minimal common over-BTZ-extension `M₁ ∨ M₂`, assembled, for `𝔼₀`-manifolds

Target `T-btz-ppcm` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`.
The row is not marked: `𝔼₀`-manifolds only (T-btz-scope), and `M₁` connected is added (as in
`GX.PpcmHausdorff`, whose Hausdorff theorem this file assembles).

* `btzprop:ppcm` — `BTZ_1.tex:1415` (proof l.1422–1520) — `GX.Ppcm.btz_ppcm` (the assembly:
  a globally hyperbolic common over-BTZ-extension, minimal, unique up to equivalence),
  `GX.Ppcm.ppcm` (the paper's `M₁ ∨ M₂ = (M₁ ⊔ M₂)/∼` along `M₁ ∧ M₂` with its `𝔼₀`-structure and
  `π₁`, `π₂`), `GX.Ppcm.globallyHyperbolic_ppcm`, `GX.Ppcm.ppcm_isMinimal`,
  `GX.Ppcm.equivalent_ppcm`; the gluing of `𝔼₀`-atlases `GX.Ppcm.glueMfd`,
  `GX.Ppcm.isBTZEmbedding_π₁`, `GX.Ppcm.isBTZEmbedding_π₂`; the last bullet
  `GX.Ppcm.globallyHyperbolic_of_cover`.

> There exits a globally hyperbolic over-BTZ-extension $\ppcm$ common to $M_1$ et $M_2$ which is
> minimal among such extensions. Furthermore, $\ppcm$ is unique up to equivalence. (l.1417–1419)
>
> If one shows that the quotient is Hausdorff, the maps $\pi_1,\pi_2$ are then homeomorphism on
> their image and the $\mass{\geq0}$-structure of $M_1$ and $M_2$ induces two
> $\mass{\geq0}$-structure on the image of $\pi_1$ and $\pi_2$. Since
> $\pi_{1|\pgcd} = \pi_2\circ\phi$, the $\mass{\geq0}$-structures agree on the intersection of the
> image, namely $\pi_1(\pgcd)$, and define a $\mass{\geq0}$-structure on $\ppcm$. (l.1424–1426)
>
> The maps $M_1,M_2\xrightarrow{\pi_1,\pi_2} \ppcm$ are BTZ-embeddings and $M_1,M_2$, are globally
> hyperbolic; then, by Lemma \ref{lem:BTZext_caus_conv}, $\pi_i(M_i)$ is causally convex in
> $\ppcm$ for $i\in\{1,2\}$ and, by Corollary \ref{cor:GH_causal}, $\ppcm$ is causal. (l.1512)
>
> Consider $q'\in I^+(q)\subset \reg_{>0}(\ppcm)\subset \pi_1(M_1)$, we notice that
> $q\in J^-_{\ppcm}(q')$ thus, by causal convexity of $\pi_1(M_1)$ […] In particular,
> $q\in \pi_1(M_1)$ and the previous observation applies again. (l.1516–1518)

## Hypothesis checklist (`btz_ppcm`)

| paper hypothesis | here |
|---|---|
| `𝔼_{≥0}`-manifolds | ⚠ `𝔼₀` only (T-btz-scope) |
| `i`, `j` BTZ-extensions | ✓ carried: `IsBTZEmbedding i`, `IsBTZEmbedding j` |
| `M₀` globally hyperbolic | ⚠ weakened: not used |
| `M₁`, `M₂` globally hyperbolic | ✓ carried |
| `M₁`, `M₂` Hausdorff, second countable (l.261) | ✓ carried |
| (none) | ⚠ strengthened: `M₁` connected (`E0AbsMax.e0_sfa_of_globalBTZ`, as in `GX.PpcmHausdorff`) |
| « minimal among such extensions » | ✓ carried, conclusion strengthened: minimal among **all** common over-BTZ-extensions (`IsMinimal`), globally hyperbolic or not |
| « unique up to equivalence » | ✓ carried under both readings of « minimal »: `equivalent_ppcm` (universal, `IsMinimalGH`) and `equivalent_ppcm_of_isOrderMinimalGH` (no proper sub-object, `IsOrderMinimalGH`) |

## SCOPE (disclosed)

* **Readings.** « minimal » is not defined in the paper: read, dually to
  `btzdef:maximal_common_sub_btz_extension` (l.1336), as « for every common over-BTZ-extension
  `M'` there is an injective morphism of common over-BTZ-extensions `M₁ ∨ M₂ → M'` »
  (`GX.Ppcm.IsMinimal`); « minimal among such extensions » restricts `M'` to the globally
  hyperbolic ones (`IsMinimalGH`). Proved here in the stronger, unrestricted form. « unique up to
  equivalence » is proved under both readings of « minimal »: every globally hyperbolic common
  over-BTZ-extension minimal among the globally hyperbolic ones (`equivalent_ppcm`), or with no
  proper globally hyperbolic sub-object (`equivalent_ppcm_of_isOrderMinimalGH`), is equivalent to
  `M₁ ∨ M₂`. The gluing is
  `Causal.Gluing` along the paper's `M₁ ∧ M₂` (`Pgcd.ghDom`), as in `GX.PpcmHausdorff` (OQ-148).
* **The `𝔼₀`-structure** (l.1424–1426) is `Causal.CBG.gluedChartedSpace` over the two pieces, its
  transitions `φ` and `φ⁻¹` (`glueMfd`): the paper's argument, in lean-causal's gluing of atlases.
  `E0AbsMax.E0Pushout` is not reused: its second piece is a flat spacetime read through `FlatE0`,
  not an `𝔼₀`-manifold, and its gluing is along `Reg M`; the construction it rests on
  (`gluedChartedSpace`, `gluedChartedSpace_hasGroupoid`, `liftPropOn_glue`) is the one used here.
* **Global hyperbolicity** (l.1512–1518) is proved for any `𝔼₀`-manifold covered by the images of
  two BTZ-embeddings of globally hyperbolic manifolds (`globallyHyperbolic_of_cover`): the image of
  each is globally hyperbolic and causally convex (B21 Lemma 2.13 (b)), the manifold is causal by
  Cor 2.15 (`cor_GH_causal_e0`), and each image is a future set (the paper's `q' ∈ I⁺(q)`), so
  every non-empty diamond lies in one image. The paper's case split on regular points is not
  needed.
* **Minimality and uniqueness** are not proved in the paper (« minimal » appears only in the
  statement); here they come from the universal property of the gluing (`Causal.Gluing.desc`):
  `a ∘ π₁⁻¹` and `b ∘ π₂⁻¹` agree on `π₁(M₁ ∧ M₂)` by density of `i(M₀)`, the descended map is an
  `𝔼₀`-morphism, and it is injective because `a⁻¹(b(M₂))` is an extension domain of `j ∘ i⁻¹`,
  hence inside `M₁ ∧ M₂` (its maximality, `Pgcd.le_dom`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open E0CBG E0Spear

namespace Ppcm

/-! ### §1 Global hyperbolicity of a manifold covered by two BTZ-images (l.1512–1518) -/

section Cover

/-- **The image of a BTZ-embedding of a globally hyperbolic manifold is globally hyperbolic**
(as an open set, kb/0001): an injective `𝔼₀`-morphism is an isomorphism of the charted
causalities onto its image (`E0AbsMax.le_iff_of_isE0Mor`). -/
theorem globallyHyperbolicOn_range {M Z : Type} [TopologicalSpace M] [TopologicalSpace Z]
    [ChartedSpace E0Y M] [ChartedSpace E0Y Z] [HasGroupoid M e0Groupoid]
    [HasGroupoid Z e0Groupoid] {a : M → Z} (ha : IsBTZEmbedding a)
    (hG : (CE M).GloballyHyperbolic) : (CE Z).GloballyHyperbolicOn ha.rangeOpens := by
  have hle : ∀ x y : M, (CE Z).le ha.rangeOpens (a x) (a y) ↔ (CE M).le ⊤ x y :=
    E0AbsMax.le_iff_of_isE0Mor ha.isE0Mor ha.injective rfl
  refine ⟨fun x y hxy hyx => ?_, fun p q => ?_⟩
  · obtain ⟨x', rfl⟩ : x ∈ range a := (CE Z).le_mem_left hxy
    obtain ⟨y', rfl⟩ : y ∈ range a := (CE Z).le_mem_right hxy
    rw [hle] at hxy hyx
    exact congrArg a (hG.1 hxy hyx)
  · by_cases hpq : p ∈ range a ∧ q ∈ range a
    · obtain ⟨⟨p', rfl⟩, ⟨q', rfl⟩⟩ := hpq
      have hD : (CE Z).diamond ha.rangeOpens (a p') (a q') = a '' (CE M).diamond ⊤ p' q' := by
        ext z
        constructor
        · intro hz
          obtain ⟨z', rfl⟩ : z ∈ range a :=
            (CE Z).le_mem_right (Causal.Causality.mem_diamond.1 hz).1
          rw [Causal.Causality.mem_diamond, hle, hle] at hz
          exact ⟨z', Causal.Causality.mem_diamond.2 hz, rfl⟩
        · rintro ⟨z', hz', rfl⟩
          rw [Causal.Causality.mem_diamond, hle, hle]
          exact Causal.Causality.mem_diamond.1 hz'
      rw [hD]
      exact (hG.2 p' q').image ha.continuous
    · rw [not_and_or] at hpq
      rw [E0AbsMax.diamond_eq_empty_of_notMem hpq]
      exact isCompact_empty

variable {M₁ M₂ Z : Type} [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace Z]
  [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂] [ChartedSpace E0Y Z]
  [HasGroupoid M₁ e0Groupoid] [HasGroupoid M₂ e0Groupoid]
  [T2Space Z] [ConnectedSpace Z] [SecondCountableTopology Z] [HasGroupoid Z e0Groupoid]

/-- **The image of a BTZ-embedding of a globally hyperbolic manifold is a future set** (the
paper's « $q'\in I^+(q)\subset \pi_1(M_1)$ … $q\in \pi_1(M_1)$ », l.1516–1518). -/
theorem mem_range_of_le {a : M₁ → Z} (ha : IsBTZEmbedding a) (hG : (CE M₁).GloballyHyperbolic)
    {p q : Z} (hp : p ∈ range a) (hpq : (CE Z).le ⊤ p q) : q ∈ range a := by
  have h := E0AbsMax.e0_sfa_of_globalBTZ Z
  have hconv := E0AbsMax.btzExt_causallyConvexIn_of_globallyHyperbolicOn_e0
    (A := ha.rangeOpens) ha.compl_range_subset (globallyHyperbolicOn_range ha hG)
  obtain ⟨q', hqq', hq'reg⟩ := E0AbsMax.exists_lt_notMem_sing h q
  have hq' : q' ∈ range a := by_contra fun hn => hq'reg (ha.compl_range_subset hn)
  exact hconv.2 p hp q' hq' (Causal.Causality.mem_diamond.2 ⟨hpq, (CE Z).le_of_lt hqq'⟩)

/-- **The last bullet of `btzprop:ppcm`** (`BTZ_1.tex:1512–1518`): an `𝔼₀`-manifold covered by the
images of two BTZ-embeddings of globally hyperbolic manifolds is globally hyperbolic. -/
theorem globallyHyperbolic_of_cover {a : M₁ → Z} {b : M₂ → Z} (ha : IsBTZEmbedding a)
    (hb : IsBTZEmbedding b) (hcov : ∀ z, z ∈ range a ∨ z ∈ range b)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    (CE Z).GloballyHyperbolic := by
  have h := E0AbsMax.e0_sfa_of_globalBTZ Z
  have hGA := globallyHyperbolicOn_range ha hG₁
  have hGB := globallyHyperbolicOn_range hb hG₂
  have hcA := E0AbsMax.btzExt_causallyConvexIn_of_globallyHyperbolicOn_e0
    (A := ha.rangeOpens) ha.compl_range_subset hGA
  have hcB := E0AbsMax.btzExt_causallyConvexIn_of_globallyHyperbolicOn_e0
    (A := hb.rangeOpens) hb.compl_range_subset hGB
  refine ⟨E0AbsMax.cor_GH_causal_e0 (A := ha.rangeOpens) ha.compl_range_subset hGA,
    fun p q => ?_⟩
  by_cases hpq : (CE Z).le ⊤ p q
  · rcases hcov p with hp | hp
    · have hq := mem_range_of_le ha hG₁ hp hpq
      rw [← E0AbsMax.diamond_eq_of_subset h.causallyArcConnected (hcA.2 p hp q hq)]
      exact hGA.2 p q
    · have hq := mem_range_of_le hb hG₂ hp hpq
      rw [← E0AbsMax.diamond_eq_of_subset h.causallyArcConnected (hcB.2 p hp q hq)]
      exact hGB.2 p q
  · have : (CE Z).diamond ⊤ p q = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun z hz => hpq ?_
      obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hz
      exact (CE Z).le_trans h1 h2
    rw [this]
    exact isCompact_empty

end Cover

/-! ### §2 The `𝔼₀`-atlas of a gluing along a BTZ-embedding (l.1424–1426) -/

section Atlas

/-- The two pieces of the gluing: `true ↦ M₁`, `false ↦ M₂`. -/
def piece (M₁ M₂ : Type) : Bool → Type
  | true => M₁
  | false => M₂

instance piece.instTop (M₁ M₂ : Type) [TopologicalSpace M₁] [TopologicalSpace M₂] :
    ∀ b, TopologicalSpace (piece M₁ M₂ b)
  | true => inferInstanceAs (TopologicalSpace M₁)
  | false => inferInstanceAs (TopologicalSpace M₂)

instance piece.instNonempty (M₁ M₂ : Type) [Nonempty M₁] [Nonempty M₂] :
    ∀ b, Nonempty (piece M₁ M₂ b)
  | true => inferInstanceAs (Nonempty M₁)
  | false => inferInstanceAs (Nonempty M₂)

noncomputable instance piece.instCharted (M₁ M₂ : Type) [TopologicalSpace M₁]
    [TopologicalSpace M₂] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂] :
    ∀ b, ChartedSpace E0Y (piece M₁ M₂ b)
  | true => inferInstanceAs (ChartedSpace E0Y M₁)
  | false => inferInstanceAs (ChartedSpace E0Y M₂)

instance piece.instHasGroupoid (M₁ M₂ : Type) [TopologicalSpace M₁] [TopologicalSpace M₂]
    [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂] [HasGroupoid M₁ e0Groupoid]
    [HasGroupoid M₂ e0Groupoid] : ∀ b, HasGroupoid (piece M₁ M₂ b) e0Groupoid
  | true => inferInstanceAs (HasGroupoid M₁ e0Groupoid)
  | false => inferInstanceAs (HasGroupoid M₂ e0Groupoid)

variable {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂] {D : Opens M₁} {φ : D → M₂}

variable (D φ) in
/-- The two embeddings of the pieces into the gluing `(M₁ ⊔ M₂)/(x ∼ φ x)`. -/
def emb : ∀ b, piece M₁ M₂ b → Causal.Gluing (Subtype.val : D → M₁) φ
  | true => Causal.Gluing.ι₁ _ φ
  | false => Causal.Gluing.ι₂ (Subtype.val : D → M₁) φ

omit [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂] in
theorem isOpenEmbedding_emb (hφ : IsOpenEmbedding φ) : ∀ b, IsOpenEmbedding (emb D φ b)
  | true => Causal.Gluing.isOpenEmbedding_ι₁ D.isOpen.isOpenEmbedding_subtypeVal hφ
  | false => Causal.Gluing.isOpenEmbedding_ι₂ D.isOpen.isOpenEmbedding_subtypeVal hφ

omit [TopologicalSpace M₂] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂] in
theorem emb_cover (z : Causal.Gluing (Subtype.val : D → M₁) φ) : ∃ b, z ∈ range (emb D φ b) := by
  rcases Causal.Gluing.exists_ι z with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨true, x, hx⟩
  · exact ⟨false, y, hy⟩

variable [Nonempty M₁] [Nonempty M₂]

/-- **The glued atlas** of `(M₁ ⊔ M₂)/∼` (`BTZ_1.tex:1424–1426`). -/
@[reducible] noncomputable def glueCS (hφ : IsOpenEmbedding φ) :
    ChartedSpace E0Y (Causal.Gluing (Subtype.val : D → M₁) φ) :=
  Causal.CBG.gluedChartedSpace E0Y (isOpenEmbedding_emb hφ) emb_cover

variable [HasGroupoid M₁ e0Groupoid] [HasGroupoid M₂ e0Groupoid]

/-- **The transitions of the glued atlas are `𝔼₀`-morphisms**: the identities, `φ` on `D` and
`φ⁻¹` on `φ(D)` (« the `𝔼≥0`-structures agree on the intersection of the image », l.1426). -/
theorem trans_emb (hD : (D : Set M₁)ᶜ ⊆ S0 M₁) (hφ : IsBTZEmbedding φ) (b c : Bool) :
    ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt
      (Causal.CBG.glueTransition (isOpenEmbedding_emb hφ.isOpenEmbedding) b c)
      (emb D φ b ⁻¹' range (emb D φ c)) := by
  obtain ⟨F', hF', hF'φ⟩ := Pgcd.exists_ext hφ (isE0Mor_val D)
  obtain ⟨F, hF, hFφ⟩ := Pgcd.exists_ext ((isBTZEmbedding_subtypeVal_iff D).2 hD) hφ.isE0Mor
  exact GluingTrans.liftPropOn_glueTransition_pair (X := piece M₁ M₂) (e := emb D φ)
    (j₁ := (Subtype.val : D → M₁)) (j₂ := φ) _ Causal.Gluing.ι₁_j₁
    (fun _ _ h => (Causal.Gluing.ι₁_eq_ι₂_iff Subtype.val_injective hφ.injective).1 h)
    hF hFφ hF' hF'φ b c

/-- The glued atlas has its transitions in `e0Groupoid`. -/
theorem glueCS_hasGroupoid (hD : (D : Set M₁)ᶜ ⊆ S0 M₁) (hφ : IsBTZEmbedding φ) :
    @HasGroupoid E0Y _ _ _ (glueCS hφ.isOpenEmbedding) e0Groupoid :=
  Causal.CBG.gluedChartedSpace_hasGroupoid _ emb_cover (trans_emb hD hφ)

variable [T2Space M₁] [SecondCountableTopology M₁] [T2Space M₂] [SecondCountableTopology M₂]

/-- **The bundled `𝔼₀`-manifold `(M₁ ⊔ M₂)/∼`**, once the gluing is Hausdorff. -/
noncomputable def glueMfd (hD : (D : Set M₁)ᶜ ⊆ S0 M₁) (hφ : IsBTZEmbedding φ)
    (hT2 : T2Space (Causal.Gluing (Subtype.val : D → M₁) φ)) : E0Mfd :=
  letI := glueCS hφ.isOpenEmbedding
  haveI := glueCS_hasGroupoid hD hφ
  haveI : SecondCountableTopology (Causal.Gluing (Subtype.val : D → M₁) φ) :=
    isQuotientMap_quot_mk.secondCountableTopology
      (Causal.Gluing.isOpenMap_mk D.isOpen.isOpenEmbedding_subtypeVal hφ.isOpenEmbedding)
  E0Mfd.of (Causal.Gluing (Subtype.val : D → M₁) φ)

variable (hD : (D : Set M₁)ᶜ ⊆ S0 M₁) (hφ : IsBTZEmbedding φ)
  (hT2 : T2Space (Causal.Gluing (Subtype.val : D → M₁) φ))

/-- `π₁ : M₁ → M₁ ∨ M₂`. -/
noncomputable def π₁ : M₁ → glueMfd hD hφ hT2 := Causal.Gluing.ι₁ _ φ

/-- `π₂ : M₂ → M₁ ∨ M₂`. -/
noncomputable def π₂ : M₂ → glueMfd hD hφ hT2 := Causal.Gluing.ι₂ (Subtype.val : D → M₁) φ

omit [T2Space M₁] [T2Space M₂] in
theorem π₁_val (w : D) : π₁ hD hφ hT2 w = π₂ hD hφ hT2 (φ w) :=
  Causal.Gluing.ι₁_j₁ w

omit [T2Space M₁] [T2Space M₂] in
theorem isE0Mor_π₁ : IsE0Mor (π₁ hD hφ hT2) univ :=
  Causal.CBG.liftPropOn_glue (isOpenEmbedding_emb hφ.isOpenEmbedding) emb_cover
    (trans_emb hD hφ) true

omit [T2Space M₁] [T2Space M₂] in
theorem isE0Mor_π₂ : IsE0Mor (π₂ hD hφ hT2) univ :=
  Causal.CBG.liftPropOn_glue (isOpenEmbedding_emb hφ.isOpenEmbedding) emb_cover
    (trans_emb hD hφ) false

omit [T2Space M₁] [T2Space M₂] in
/-- **`π₁` is a BTZ-embedding** (l.1512): its image misses only `π₂(M₂ ∖ φ(D))`, BTZ points. -/
theorem isBTZEmbedding_π₁ : IsBTZEmbedding (π₁ hD hφ hT2) := by
  refine isBTZEmbedding_iff_injective.2 ⟨Causal.Gluing.injective_ι₁ Subtype.val_injective
    hφ.injective, isE0Mor_π₁ hD hφ hT2, fun z hz => ?_⟩
  rcases Causal.Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact absurd ⟨x, rfl⟩ hz
  · have hy : y ∉ range φ := by
      rintro ⟨w, rfl⟩
      exact hz ⟨w, π₁_val hD hφ hT2 w⟩
    exact (mem_S0_iff_of_isE0Mor (isE0Mor_π₂ hD hφ hT2) y).2 (hφ.compl_range_subset hy)

omit [T2Space M₁] [T2Space M₂] in
/-- **`π₂` is a BTZ-embedding** (l.1512): its image misses only `π₁(M₁ ∖ D)`, BTZ points. -/
theorem isBTZEmbedding_π₂ : IsBTZEmbedding (π₂ hD hφ hT2) := by
  refine isBTZEmbedding_iff_injective.2 ⟨Causal.Gluing.injective_ι₂ Subtype.val_injective
    hφ.injective, isE0Mor_π₂ hD hφ hT2, fun z hz => ?_⟩
  rcases Causal.Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · have hx : x ∉ D := fun hx => hz ⟨φ ⟨x, hx⟩, (π₁_val hD hφ hT2 ⟨x, hx⟩).symm⟩
    exact (mem_S0_iff_of_isE0Mor (isE0Mor_π₁ hD hφ hT2) x).2 (hD hx)
  · exact absurd ⟨y, rfl⟩ hz

omit [T2Space M₁] [T2Space M₂] in
theorem cover_π (z : glueMfd hD hφ hT2) : z ∈ range (π₁ hD hφ hT2) ∨ z ∈ range (π₂ hD hφ hT2) :=
  Causal.Gluing.exists_ι z

omit [T2Space M₁] [T2Space M₂] in
/-- The gluing is connected when `M₁` is: `π₁(M₁)` is dense. -/
theorem connectedSpace_glueMfd [ConnectedSpace M₁] : ConnectedSpace (glueMfd hD hφ hT2) := by
  have h := isPreconnected_range (isBTZEmbedding_π₁ hD hφ hT2).continuous
  have hd := (isBTZEmbedding_π₁ hD hφ hT2).dense_range
  obtain ⟨x₀⟩ := ‹Nonempty M₁›
  refine { isPreconnected_univ := ?_, toNonempty := ⟨π₁ hD hφ hT2 x₀⟩ }
  rw [← hd.closure_eq]
  exact h.closure

end Atlas

/-! ### §3 Minimality: the universal property of the gluing -/

section Minimal

variable {M₀ M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂] {i : M₀ → M₁} {j : M₀ → M₂}

/-- **Minimal common over-BTZ-extension** (the paper's « minimal », l.1417, read dually to
`btzdef:maximal_common_sub_btz_extension`, l.1336): an injective morphism of common
over-BTZ-extensions into every common over-BTZ-extension. -/
def IsMinimal (X : CommonOverBTZ i j) : Prop :=
  ∀ Y : CommonOverBTZ i j, ∃ φ : X.X → Y.X, X.IsMorphism Y φ ∧ Injective φ

/-- **« minimal among such extensions »** (l.1417–1418): into every *globally hyperbolic* common
over-BTZ-extension. -/
def IsMinimalGH (X : CommonOverBTZ i j) : Prop :=
  ∀ Y : CommonOverBTZ i j, (CE Y.X).GloballyHyperbolic →
    ∃ φ : X.X → Y.X, X.IsMorphism Y φ ∧ Injective φ

/-- **« minimal », order reading** (« no proper sub-object »): every injective morphism into `X`
from a globally hyperbolic common over-BTZ-extension is bijective. -/
def IsOrderMinimalGH (X : CommonOverBTZ i j) : Prop :=
  ∀ Z : CommonOverBTZ i j, (CE Z.X).GloballyHyperbolic →
    ∀ φ : Z.X → X.X, Z.IsMorphism X φ → Injective φ → Bijective φ

theorem IsMinimal.isMinimalGH {X : CommonOverBTZ i j} (h : IsMinimal X) : IsMinimalGH X :=
  fun Y _ => h Y

/-- **Two minimal common over-BTZ-extensions are equivalent** (« unique up to equivalence »,
l.1419): the morphisms both ways compose to identities (`CommonOverBTZ.IsMorphism.unique`). -/
theorem equivalent_of_isMinimalGH {X Y : CommonOverBTZ i j} (hX : IsMinimalGH X)
    (hY : IsMinimalGH Y) (hGX : (CE X.X).GloballyHyperbolic) (hGY : (CE Y.X).GloballyHyperbolic) :
    X.Equivalent Y := by
  obtain ⟨φ, hφ, -⟩ := hX Y hGY
  obtain ⟨ψ, hψ, -⟩ := hY X hGX
  have h1 : ψ ∘ φ = id := (hψ.comp hφ).unique X.isMorphism_id
  have h2 : φ ∘ ψ = id := (hφ.comp hψ).unique Y.isMorphism_id
  refine ⟨φ, hφ, fun a b hab => ?_, fun y => ⟨ψ y, congrFun h2 y⟩⟩
  have ha : ψ (φ a) = a := congrFun h1 a
  have hb : ψ (φ b) = b := congrFun h1 b
  rw [← ha, ← hb, hab]

end Minimal

/-! ### §4 `btzprop:ppcm`: the paper's `M₁ ∨ M₂` along `M₁ ∧ M₂ = Pgcd.ghDom` -/

section Ppcm

variable {M₀ M₁ M₂ : Type} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₀] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]
  [T2Space M₁] [ConnectedSpace M₁] [SecondCountableTopology M₁] [HasGroupoid M₁ e0Groupoid]
  [T2Space M₂] [SecondCountableTopology M₂] [HasGroupoid M₂ e0Groupoid]
  {i : M₀ → M₁} {j : M₀ → M₂}

omit [SecondCountableTopology M₂] in
/-- Under the proposition's hypotheses, the paper's `M₁ ∧ M₂` is the maximal domain
(`PpcmHausdorff.globallyHyperbolicOn_maxDom`, `Pgcd.ghDom_eq_dom_of_globallyHyperbolicOn`). -/
theorem ghDom_eq_dom (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    Pgcd.ghDom i j = Pgcd.dom i j :=
  Pgcd.ghDom_eq_dom_of_globallyHyperbolicOn hi hj
    (PpcmHausdorff.globallyHyperbolicOn_maxDom hi hj hG₁ hG₂)

omit [TopologicalSpace M₂] [ChartedSpace E0Y M₂] [T2Space M₁] [SecondCountableTopology M₁]
  [T2Space M₂] [SecondCountableTopology M₂] [HasGroupoid M₂ e0Groupoid] in
theorem nonempty_M₂ (hi : IsBTZEmbedding i) (j : M₀ → M₂) : Nonempty M₂ := by
  obtain ⟨z, hz⟩ := (E0LM.dense_e0RegM (M := M₁)).nonempty
  obtain ⟨m, -⟩ : z ∈ range i := by_contra fun h => hz (hi.compl_range_subset h)
  exact ⟨j m⟩

omit [SecondCountableTopology M₂] in
/-- `(M₁ ∧ M₂)ᶜ` is BTZ. -/
theorem compl_ghDom_subset (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    ((Pgcd.ghDom i j : Set M₁))ᶜ ⊆ S0 M₁ := by
  rw [ghDom_eq_dom hi hj hG₁ hG₂]
  exact Pgcd.compl_dom_subset hi hj

omit [SecondCountableTopology M₂] in
/-- **`φ : M₁ ∧ M₂ → M₂` is a BTZ-embedding** (`BTZ_1.tex:1366`, on the paper's `M₁ ∧ M₂`). -/
theorem isBTZEmbedding_ghMap (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    IsBTZEmbedding (PpcmHausdorff.ghMap i j) := by
  let incl : Pgcd.ghDom i j → Pgcd.dom i j := fun x => ⟨x.1, Pgcd.ghDom_le_dom x.2⟩
  have hincl : IsE0Mor incl univ :=
    (isE0Mor_corestrict_iff (U := Pgcd.dom i j) incl univ).1 (isE0Mor_val (Pgcd.ghDom i j))
  have hmor : IsE0Mor (Pgcd.pgcdMap i j ∘ incl) univ :=
    Causal.CBG.liftPropOn_comp isOpen_univ isOpen_univ (Pgcd.isE0Mor_pgcdMap hi) hincl
      (mapsTo_univ _ _)
  refine isBTZEmbedding_iff_injective.2 ⟨(Pgcd.pgcdMap_injective hi hj).comp
    (fun x y h => Subtype.ext (congrArg Subtype.val h : _)), hmor, fun q hq => ?_⟩
  refine hj.compl_range_subset fun ⟨m, hm⟩ => hq ?_
  have hm' : i m ∈ Pgcd.ghDom i j := by
    rw [ghDom_eq_dom hi hj hG₁ hG₂]; exact Pgcd.range_subset_dom hi hj ⟨m, rfl⟩
  exact ⟨⟨i m, hm'⟩, (Pgcd.pgcdMap_of_eq _ m rfl).trans hm⟩

omit [SecondCountableTopology M₂] in
theorem range_subset_ghDom (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    range i ⊆ Pgcd.ghDom i j := by
  rw [ghDom_eq_dom hi hj hG₁ hG₂]
  exact Pgcd.range_subset_dom hi hj

/-- **The paper's `M₁ ∨ M₂`** (`BTZ_1.tex:1424`) as a common over-BTZ-extension: the gluing
`PpcmHausdorff.GhGlue i j` along `M₁ ∧ M₂`, Hausdorff (`PpcmHausdorff.t2Space_ghGlue`), with the
glued `𝔼₀`-atlas and the BTZ-embeddings `π₁`, `π₂`. -/
noncomputable def ppcm (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    CommonOverBTZ i j :=
  haveI := nonempty_M₂ hi j
  { X := glueMfd (compl_ghDom_subset hi hj hG₁ hG₂) (isBTZEmbedding_ghMap hi hj hG₁ hG₂)
      (PpcmHausdorff.t2Space_ghGlue hi hj hG₁ hG₂)
    a := π₁ _ _ _
    b := π₂ _ _ _
    ha := isBTZEmbedding_π₁ _ _ _
    hb := isBTZEmbedding_π₂ _ _ _
    comm := funext fun m => (π₁_val (compl_ghDom_subset hi hj hG₁ hG₂) (isBTZEmbedding_ghMap hi hj hG₁ hG₂)
      (PpcmHausdorff.t2Space_ghGlue hi hj hG₁ hG₂) ⟨i m, range_subset_ghDom hi hj hG₁ hG₂ ⟨m, rfl⟩⟩).trans
      (congrArg _ (Pgcd.pgcdMap_of_eq _ m rfl)) }

/-- The carrier of `ppcm` is the paper's gluing. -/
theorem ppcm_carrier (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    ((ppcm hi hj hG₁ hG₂).X : Type) = PpcmHausdorff.GhGlue i j := rfl

/-- `π₁` and `π₂` of `ppcm` are the maps of the gluing. -/
theorem ppcm_a_b (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    (∀ x, (ppcm hi hj hG₁ hG₂).a x = Causal.Gluing.ι₁ _ (PpcmHausdorff.ghMap i j) x) ∧
      ∀ y, (ppcm hi hj hG₁ hG₂).b y =
        Causal.Gluing.ι₂ (Subtype.val : Pgcd.ghDom i j → M₁) (PpcmHausdorff.ghMap i j) y :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **`M₁ ∨ M₂` is globally hyperbolic** (`BTZ_1.tex:1512–1518`). -/
theorem globallyHyperbolic_ppcm (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    (CE (ppcm hi hj hG₁ hG₂).X).GloballyHyperbolic := by
  haveI := nonempty_M₂ hi j
  haveI : ConnectedSpace (ppcm hi hj hG₁ hG₂).X := connectedSpace_glueMfd (compl_ghDom_subset hi hj hG₁ hG₂) (isBTZEmbedding_ghMap hi hj hG₁ hG₂)
      (PpcmHausdorff.t2Space_ghGlue hi hj hG₁ hG₂)
  exact globallyHyperbolic_of_cover (ppcm hi hj hG₁ hG₂).ha (ppcm hi hj hG₁ hG₂).hb
    (cover_π (compl_ghDom_subset hi hj hG₁ hG₂) (isBTZEmbedding_ghMap hi hj hG₁ hG₂)
      (PpcmHausdorff.t2Space_ghGlue hi hj hG₁ hG₂)) hG₁ hG₂

/-- **`M₁ ∨ M₂` is minimal among all common over-BTZ-extensions** (`BTZ_1.tex:1417–1418`). -/
theorem ppcm_isMinimal (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    IsMinimal (ppcm hi hj hG₁ hG₂) := by
  haveI := nonempty_M₂ hi j
  intro Y
  set X := ppcm hi hj hG₁ hG₂ with hXdef
  -- `a` and `b ∘ φ` agree on `M₁ ∧ M₂`, by density of `i(M₀)`
  have hagree : ∀ w : Pgcd.ghDom i j, Y.a w = Y.b (PpcmHausdorff.ghMap i j w) := by
    have hd : Dense ((Subtype.val : Pgcd.ghDom i j → M₁) ⁻¹' range i) :=
      hi.dense_range.preimage (Pgcd.ghDom i j).isOpen.isOpenMap_subtype_val
    have hφc : Continuous (PpcmHausdorff.ghMap i j) :=
      (isBTZEmbedding_ghMap hi hj hG₁ hG₂).continuous
    refine congrFun (Continuous.ext_on hd (Y.ha.continuous.comp continuous_subtype_val)
      (Y.hb.continuous.comp hφc) ?_)
    rintro w ⟨m, hm⟩
    have h1 : PpcmHausdorff.ghMap i j w = j m := Pgcd.pgcdMap_of_eq _ m hm.symm
    simp only [h1, ← hm]
    exact congrFun Y.comm m
  -- the injectivity step: `a x = b y` forces `x ∈ M₁ ∧ M₂` and `φ x = y`
  have hkey : ∀ x y, Y.a x = Y.b y →
      ∃ hx : x ∈ Pgcd.ghDom i j, PpcmHausdorff.ghMap i j ⟨x, hx⟩ = y := by
    intro x y hxy
    let A : Opens M₁ := ⟨Y.a ⁻¹' range Y.b, Y.hb.isOpen_range.preimage Y.ha.continuous⟩
    have hgb : ∀ y, invFunOn Y.b univ (Y.b y) = y := fun y =>
      Y.hb.injective.injOn.leftInvOn_invFunOn (mem_univ y)
    have hg : IsE0Mor (invFunOn Y.b univ ∘ Y.a) A :=
      Causal.CBG.liftPropOn_comp A.isOpen Y.hb.isOpen_range Y.hb.isE0Mor_invFunOn
        (Causal.CBG.liftPropOn_mono_of_le isOpen_univ A.isOpen Y.ha.isE0Mor (subset_univ _))
        fun x hx => hx
    have hgi : ∀ m, (invFunOn Y.b univ ∘ Y.a) (i m) = j m := fun m => by
      rw [comp_apply, show Y.a (i m) = Y.b (j m) from congrFun Y.comm m, hgb]
    have hext : Pgcd.IsExtDomain i j A :=
      ⟨fun _ ⟨m, hm⟩ => ⟨j m, by rw [← hm]; exact (congrFun Y.comm m).symm⟩, _, hg, hgi⟩
    have hxA : x ∈ A := ⟨y, hxy.symm⟩
    have hxd : x ∈ Pgcd.dom i j := Pgcd.le_dom hext hxA
    have hxg : x ∈ Pgcd.ghDom i j := by rw [ghDom_eq_dom hi hj hG₁ hG₂]; exact hxd
    refine ⟨hxg, ?_⟩
    have := Pgcd.pgcdMap_eq hi hg hgi ⟨x, hxd⟩ hxA
    refine this.trans ?_
    rw [comp_apply, hxy, hgb]
  let Φ : X.X → Y.X := Causal.Gluing.desc Y.a Y.b hagree
  have hΦ₁ : Φ ∘ X.a = Y.a := rfl
  have hΦ₂ : Φ ∘ X.b = Y.b := rfl
  have hmor : IsE0Mor Φ univ := by
    refine Causal.CBG.liftPropOn_of_locally isOpen_univ fun z _ => ?_
    rcases cover_π (compl_ghDom_subset hi hj hG₁ hG₂) (isBTZEmbedding_ghMap hi hj hG₁ hG₂)
      (PpcmHausdorff.t2Space_ghGlue hi hj hG₁ hG₂) z with hz | hz
    · obtain ⟨f, hf, hfa⟩ := Pgcd.exists_ext X.ha Y.ha.isE0Mor
      refine ⟨range X.a, X.ha.isOpen_range, subset_univ _, hz, ?_⟩
      refine Causal.CBG.liftPropOn_congr_of_eqOn X.ha.isOpen_range hf ?_
      rintro _ ⟨x, rfl⟩
      exact (hfa x).trans (congrFun hΦ₁ x).symm
    · obtain ⟨f, hf, hfb⟩ := Pgcd.exists_ext X.hb Y.hb.isE0Mor
      refine ⟨range X.b, X.hb.isOpen_range, subset_univ _, hz, ?_⟩
      refine Causal.CBG.liftPropOn_congr_of_eqOn X.hb.isOpen_range hf ?_
      rintro _ ⟨y, rfl⟩
      exact (hfb y).trans (congrFun hΦ₂ y).symm
  refine ⟨Φ, ⟨hmor, hΦ₁, hΦ₂⟩, fun z z' hzz => ?_⟩
  have hX12 : ∀ x y, Y.a x = Y.b y → X.a x = X.b y := fun x y h => by
    obtain ⟨hx, hφ⟩ := hkey x y h
    rw [← hφ]
    exact π₁_val (compl_ghDom_subset hi hj hG₁ hG₂) (isBTZEmbedding_ghMap hi hj hG₁ hG₂)
      (PpcmHausdorff.t2Space_ghGlue hi hj hG₁ hG₂) ⟨x, hx⟩
  rcases cover_π (compl_ghDom_subset hi hj hG₁ hG₂) (isBTZEmbedding_ghMap hi hj hG₁ hG₂)
      (PpcmHausdorff.t2Space_ghGlue hi hj hG₁ hG₂) z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;>
    rcases cover_π (compl_ghDom_subset hi hj hG₁ hG₂) (isBTZEmbedding_ghMap hi hj hG₁ hG₂)
      (PpcmHausdorff.t2Space_ghGlue hi hj hG₁ hG₂) z' with ⟨x', rfl⟩ | ⟨y', rfl⟩
  · exact congrArg X.a (Y.ha.injective hzz)
  · exact hX12 x y' hzz
  · exact (hX12 x' y hzz.symm).symm
  · exact congrArg X.b (Y.hb.injective hzz)

/-- **Uniqueness up to equivalence** (`BTZ_1.tex:1419`): a globally hyperbolic common
over-BTZ-extension minimal among the globally hyperbolic ones is equivalent to `M₁ ∨ M₂`. -/
theorem equivalent_ppcm (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic)
    (Y : CommonOverBTZ i j) (hGY : (CE Y.X).GloballyHyperbolic) (hY : IsMinimalGH Y) :
    (ppcm hi hj hG₁ hG₂).Equivalent Y :=
  equivalent_of_isMinimalGH (ppcm_isMinimal hi hj hG₁ hG₂).isMinimalGH hY
    (globallyHyperbolic_ppcm hi hj hG₁ hG₂) hGY

/-- **Uniqueness up to equivalence, order reading of « minimal »** (`BTZ_1.tex:1419`): a globally
hyperbolic common over-BTZ-extension with no proper globally hyperbolic sub-object is equivalent
to `M₁ ∨ M₂` (the injective morphism `M₁ ∨ M₂ → Y` of `ppcm_isMinimal` is then bijective). -/
theorem equivalent_ppcm_of_isOrderMinimalGH (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic)
    (Y : CommonOverBTZ i j) (hY : IsOrderMinimalGH Y) :
    (ppcm hi hj hG₁ hG₂).Equivalent Y := by
  obtain ⟨φ, hφ, hinj⟩ := ppcm_isMinimal hi hj hG₁ hG₂ Y
  exact ⟨φ, hφ, hY _ (globallyHyperbolic_ppcm hi hj hG₁ hG₂) φ hφ hinj⟩

/-- **`btzprop:ppcm`** (unmarked: `𝔼₀` only, `M₁` connected added) (`BTZ_1.tex:1415–1420`): two
globally hyperbolic BTZ-extensions `M₀ → M₁`, `M₀ → M₂` have a globally hyperbolic common
over-BTZ-extension, minimal among all common over-BTZ-extensions, and unique up to equivalence
among the globally hyperbolic minimal ones. `M₀` need not be globally hyperbolic. -/
theorem btz_ppcm (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j)
    (hG₁ : (CE M₁).GloballyHyperbolic) (hG₂ : (CE M₂).GloballyHyperbolic) :
    ∃ X : CommonOverBTZ i j, (CE X.X).GloballyHyperbolic ∧ IsMinimal X ∧
      ∀ Y : CommonOverBTZ i j, (CE Y.X).GloballyHyperbolic → IsMinimalGH Y → X.Equivalent Y :=
  ⟨ppcm hi hj hG₁ hG₂, globallyHyperbolic_ppcm hi hj hG₁ hG₂, ppcm_isMinimal hi hj hG₁ hG₂,
    fun Y hGY hY => equivalent_ppcm hi hj hG₁ hG₂ Y hGY hY⟩

end Ppcm

end Ppcm

end GX
