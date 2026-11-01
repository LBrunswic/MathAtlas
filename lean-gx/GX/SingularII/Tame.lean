import GX.SingularII.Developing

/-!
# Singular `(G,X)`-manifolds (II): tame singularities

Package WP-27i. `papers/gx`, `RamcovGX.tex:1826–1888`, §2.5.2 "Tame singularities" (`M`, `N`
connected singular `(G,X)`-manifolds, l.1712; `(G,X)` analytical with `X` locally unloopable,
l.1660), on WP-27h's `GX.SingularII.Developing`.

* **`def:singular_manifold_tame_admits`** — `RamcovGX.tex:1826`: `GX.IsTame` (=
  `GX.AdmitsDevelopingMap`); `GX.isTame_iff` (a developing map of `\widetilde M`),
  `GX.isTame_of_isDevelopingMapOf` (of any branched covering).
* **`lem:embedding_tame`** — `RamcovGX.tex:1831` — closed under DEC-66 (`M`, `N` Hausdorff,
  locally path-connected, first countable: §3's standing setting, l.810, covers §2.5):
  `GX.isTame_of_isAEMorphism`, by another route than the paper's (SCOPE (a)).
* **`cor:branched_covering_tame_singular`** — `RamcovGX.tex:1837` — closed under DEC-66 (the
  same): `GX.isTame_of_isBranchedCovering`, `GX.isTame_of_isBranchedCovering'`.
* **`cor:open_subsets_tame_singular`** — `RamcovGX.tex:1839` — closed under DEC-66 (the same;
  the open subset connected by the section's standing convention l.1712 — "`M`, `N` will denote
  connected singular `(G,X)`-manifolds" — with DEC-66(b), `\widetilde M` presupposing `M`
  connected; a disconnected open set is never tame, `GX.IsTame.connectedSpace`): `GX.isTame_opens`,
  on `GX.opensSingularGXStructure`; `GX.IsTame.exists_opens_subset`.
* **`theo:local_tame`** — `RamcovGX.tex:1844` — closed under DEC-66 and DEC-67(d) ("locally
  tamely singular" = every point has a tame open neighbourhood, SCOPE (b)):
  `GX.isTame_iff_isLocallyTame`, `GX.IsLocallyTame`, `GX.isTame_of_isLocallyTame`,
  `GX.exists_local_tame_extension`.
* `rem:tamely_singular_manifold_admits` — `RamcovGX.tex:1869` — partial (Galoisian `N`; both
  readings of "isomorphic", SCOPE (c)): as spaces `GX.tamely_singular_manifold_admits`,
  `GX.homeomorph_rangeTameTopology`; as singular `(G,X)`-manifolds (the quotient structure)
  `GX.tamely_singular_manifold_admits_aeIso`.
* `ex:take_closed_unit_disc` — `RamcovGX.tex:1877` — partial (its last sentence only, SCOPE (d)):
  `GX.not_isOpen_horodisc_insert`, `GX.not_mem_interior_of_subset_ball_insert`.

> A singular $(G,X)$-manifold $M$ is tame if it admits a developing map. (l.1826)
>
> Let $M,N$ be singular $(G,X)$-manifolds and let $M\rightarrow N$ be an a.e.
> $(G,X)$-morphism. If $N$ is tame then $M$ is tame. (l.1831)
>
> A branched covering of a tame singular $(G,X)$-manifold is tame. (l.1837)
>
> Open subsets of tame singular $(G,X)$-manifolds are tame. (l.1839)
>
> Let $M$ be a singular $(G,X)$-manifold the following are equivalent: $M$ is tamely singular;
> $M$ locally tamely singular. (l.1844)
>
> Let $M$ be a tamely singular $(G,X)$-manifold. If $M$ admits an injective developing map
> $N\xrightarrow{\D}X$ for some branched covering $N$ of $M$ then $M$ is isomorphic to
> $\Gamma(N/M)\backslash\D(N)$ where $\Gamma(N/M)$ acts on $X$ via the holonomy of $\D$; $\D(N)$
> is endowed with the topology making $\D$ an homeomorphism. (l.1869)
>
> […] We may choose $\U$ so that $\D(U)$ is a horodisc centered at $\D(x)$. Such a domain is not
> open for the topology of $X$. (l.1880)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(G,X)` analytical (l.341, DEC-39) | ✓ carried: `IsRigidAction`, `FaithfulSMul`, `ContinuousConstSMul`, `X` T2 and locally connected; `X` connected never used |
| `X` locally unloopable (standing, l.1660) | ✓ carried (`hX`) wherever `\widetilde M` is used |
| `M`, `N` connected (standing, l.1712) | ✓ carried; open subsets connected (`[ConnectedSpace U]`); tame spaces are connected (`IsTame.connectedSpace`) |
| singular manifolds Hausdorff, second countable, locally connected | ✓ carried (DEC-66(a)(c)): T2, locally path-connected, first countable — §3's standing setting (l.810) covers §2.5, `M` locally path-connected wherever `\widetilde M` is used; ⚠ weakened: second countable not used |
| `cor:branched_covering_tame_singular`: `N` with the structure of `prop:singular_manifold_branched_covering` | ✓ carried: `p` an a.e. morphism (equivalently `aeAtlas N = p^*B`) |
| `rem:tamely_singular_manifold_admits`: `N` any branched covering, `M` tame | ⚠ strengthened: `N → M` Galoisian (SCOPE (c), finding); ✓ carried (DEC-66): `M` locally path-connected (through `spread_connected_image`, `p` open), first countable; ⚠ weakened: `M` T1 (not T2); ⚠ weakened: `M` tame, `D` an a.e. morphism, not used; `N` locally connected and `p` an a.e. morphism for the `(G,X)` half |

## SCOPE (disclosed)

* **(a)** `lem:embedding_tame`: the paper's first step, "the morphism `M → N` lifts to
  `\widetilde M → \widetilde N`", fails when `f` sends regular points to singular ones (finding).
  The proof lifts from `\widehat M = \widetilde M^{M ∖ U}`, `U` portly on which `f` is regular:
  `\widetilde U → reg N` lifts to `\widetilde{reg N}`, extends to the Fox completions, and its
  composite with the developing map of `\widetilde N` is a developing map of `\widehat M → M`
  (`lem:morphism_singular_manifolds_branched`); `prop:branched_devmap` concludes.
* **(b)** "Locally tamely singular" is not defined in the paper; it is read, as DEC-67(d) rules,
  as: every point has an open neighbourhood which, with the induced structure (`GX.opensSingularGXStructure`, the
  pullback along the inclusion), is tame. The forward direction gives the stronger form (a basis
  of connected tame open neighbourhoods, `GX.IsTame.exists_opens_subset`). The converse follows
  the paper: local extensions of the developing map of `\widetilde{reg M}` to the components of
  `p⁻¹(V)` (`GX.exists_local_tame_extension`), glued by density.
* **(c)** `rem:tamely_singular_manifold_admits` is proved for a Galoisian `N → M` (`Γ(N/M)`
  transitive on the fibres, `GX.IsGaloisian`), under both readings of "isomorphic" (question):
  as spaces, a homeomorphism `Γ(N/M)\D(N) ≃ₜ M`, `[D x] ↦ p x`, `D(N)` with the coinduced
  topology; as singular `(G,X)`-manifolds, `D(N)` with the structure transported from `N` along
  `D` (for which, `D` being a developing map, the inclusion `D(N) ⊆ X` is an a.e. morphism) and
  `Γ(N/M)\D(N)` with the quotient structure — proved to exist and to be unique among maximal
  a.e. atlases making the projection an a.e. morphism — the homeomorphism being an a.e.
  `(G,X)`-isomorphism (`GX.tamely_singular_manifold_admits_aeIso`). `prop:aeGXquotient`
  (`GX.existsUnique_aeGXQuotient`) is not invoked: its freeness and proper-discontinuity
  hypotheses are not available for `Γ(N/M)` on `D(N)`, and the quotient structure is obtained
  through `M` instead. Without transitivity on the fibres `Γ(N/M)\D(N) → M` is not injective.
  Over the ordinary regular locus transitivity should follow from `D` injective and equivariant
  (normality of the holonomy subgroup, then Fox extension of the decks; sketch, not formalized);
  whether an injective developing map forces it over the branch fibres is left open (question).
* **(d)** `ex:take_closed_unit_disc`: only the last sentence is certified — a horodisc together
  with its point at infinity is not open in the closed disc, in the stronger form that no subset
  of the open disc `∪ {ξ}` is a neighbourhood of `ξ`. The example's other assertions — `M` tamely
  singular with an injective developing map `\widetilde M → X`, neighbourhoods of a singular
  point of `\widetilde M` homeomorphic to `{r < r₀} ⊆ D_∞`, `D(U)` a horodisc — are not stated:
  the example GIVES the complete finite-volume metric on `M ∖ S`, and what is missing is the
  infrastructure of hyperbolic surfaces, none of it at this mathlib pin: `Isom(ℍ²)` and its
  action on the closed disc by homeomorphisms; completeness making the developing map of the
  universal cover of `M ∖ S` a homeomorphism onto `ℍ²` (the Hopf–Rinow / Cartan–Hadamard step for
  `(G,X)`-structures); the thick–thin decomposition giving each end of finite volume a cusp
  neighbourhood with parabolic holonomy; and the extension of `D` to the parabolic fixed points of
  `∂ℍ²` (question).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.SingularII.Developing`, `GX.Branched.Universality`, `GX.Singular.Atlas`,
`GX.Spread.Completion`, `GX.Singular.Quotient` (`IsAEMorphismOf.eq_of_isMaximalAEAtlas_right`).
-/
noncomputable section
open Set Filter Topology Function TopologicalSpace
open scoped GX
namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

universe u v

/-! ### `def:singular_manifold_tame_admits` -/

section Def

variable (G : Type*) (X : Type*) [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] (M : Type*) [TopologicalSpace M] [SingularGXStructure G X M]

/-- **`def:singular_manifold_tame_admits`** (`RamcovGX.tex:1826`): a singular `(G,X)`-manifold
is *tame* (*tamely singular*) if it admits a developing map (`def:developing_map`, second
sentence: some branched covering possibly branched above `sing(M)` has an a.e.
`(G,X)`-morphism into `X`). -/
def IsTame : Prop := AdmitsDevelopingMap G X M

end Def

/-! ### Open subsets as singular `(G,X)`-manifolds -/

section Opens

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type*} [TopologicalSpace M] [SingularGXStructure G X M]

/-- The inclusion of an open subset is almost everywhere a local homeomorphism into the regular
locus. -/
theorem isAELocalHomeomorph_opensSingular_val (U : Opens M) :
    IsAELocalHomeomorph (aeAtlas G X M) (Subtype.val : U → M) :=
  ⟨Subtype.val ⁻¹' Reg G X M, Reg G X M, (isPortly_reg G X M).preimage_val_of_isOpen U.isOpen,
    isPortly_reg G X M, subset_rfl, fun _ h => h,
    U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn⟩

theorem aePullback_opensSingular_val_spec (U : Opens M) :
    IsMaximalAEAtlas G (aePullback G (aeAtlas G X M) (Subtype.val : U → M)) ∧
      IsAEMorphismOf G (aePullback G (aeAtlas G X M) (Subtype.val : U → M)) (aeAtlas G X M)
        Subtype.val :=
  aePullback_spec_of_isAELocalHomeomorph (isMaximalAEAtlas_aeAtlas G X M).1
    continuous_subtype_val (isAELocalHomeomorph_opensSingular_val U)

/-- An open subset `U` of a singular `(G,X)`-manifold is a singular `(G,X)`-manifold: its
structure is the pullback `ι^* B` along the inclusion (`lem:aepullback`), the unique maximal one
making the inclusion an a.e. morphism. -/
instance opensSingularGXStructure (U : Opens M) : SingularGXStructure G X U :=
  ⟨_, (aePullback_opensSingular_val_spec U).1⟩

theorem aeAtlas_opensSingular (U : Opens M) :
    aeAtlas G X U = aePullback G (aeAtlas G X M) (Subtype.val : U → M) := rfl

/-- The inclusion of an open subset is an a.e. `(G,X)`-morphism. -/
theorem isAEMorphism_opensSingular_val (U : Opens M) : IsAEMorphism G X (Subtype.val : U → M) :=
  (aePullback_opensSingular_val_spec U).2

theorem reg_opensSingular (U : Opens M) : Reg G X U = Subtype.val ⁻¹' Reg G X M :=
  ((isAEMorphism_opensSingular_val U).preimage_support_eq (isMaximalAEAtlas_aeAtlas G X U)
    (isMaximalAEAtlas_aeAtlas G X M) U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph).1.symm

theorem sing_opensSingular (U : Opens M) : Sing G X U = Subtype.val ⁻¹' Sing G X M := by
  rw [Sing, Sing, reg_opensSingular, preimage_compl]

variable (G X M) in
/-- *Locally tamely singular* (`theo:local_tame`, item 2; the paper does not define the term,
SCOPE (b); the reading accepted by DEC-67(d)): every point has an open neighbourhood which, with
the induced structure, is tame (tame neighbourhoods are connected, `IsTame.connectedSpace`). -/
def IsLocallyTame : Prop := ∀ x : M, ∃ U : Opens M, x ∈ U ∧ IsTame G X U

end Opens

/-- A tame singular `(G,X)`-manifold is connected (the target of a branched covering). -/
theorem IsTame.connectedSpace {G : Type*} {X : Type*} [TopologicalSpace X] [Group G]
    [MulAction G X] [ContinuousConstSMul G X] {M : Type*} [TopologicalSpace M]
    [SingularGXStructure G X M] (h : IsTame G X M) : ConnectedSpace M := by
  obtain ⟨N, _, _, _, _, p, hp, -⟩ := h
  exact hp.connectedSpace_target

/-- An open subset of a locally path-connected space is locally path-connected. -/
instance opensTame_locPathConnectedSpace {M : Type*} [TopologicalSpace M] [LocPathConnectedSpace M]
    (U : Opens M) : LocPathConnectedSpace U :=
  U.isOpen.locPathConnectedSpace

/-- An open subset of a first countable space is first countable. -/
instance opensTame_firstCountableTopology {M : Type*} [TopologicalSpace M]
    [FirstCountableTopology M] (U : Opens M) : FirstCountableTopology U :=
  Subtype.firstCountableTopology (U : Set M)

/-! ### Tameness through `\widetilde M` -/

section Main

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X] {M : Type u} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]

/-- Under the section's standing hypothesis (`X` locally unloopable, l.1660), `M` is tame iff
`\widetilde M = \widetilde M^{sing M}` has a developing map. -/
theorem isTame_iff (hX : IsLocallyUnloopable X) (y₀ : ((Sing G X M)ᶜ : Set M)) :
    IsTame G X M ↔ ∃ D : MaxBranchedCover (Sing G X M) y₀ → X,
      IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base D :=
  admitsDevelopingMap_iff G X (semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X M) subset_rfl) y₀

/-- `M` is tame as soon as **some** branched covering of `M` (branched anywhere) has a developing
map (`prop:branched_devmap`). -/
theorem isTame_of_isDevelopingMapOf (hX : IsLocallyUnloopable X) {N : Type*} [TopologicalSpace N]
    [T2Space N] [LocPathConnectedSpace N] [FirstCountableTopology N] {p : N → M}
    (hp : IsBranchedCovering p) {D : N → X} (hD : IsDevelopingMapOf G (aeAtlas G X M) p D) :
    IsTame G X M := by
  obtain ⟨y₀⟩ := (nonempty_compl_of_isSkeletal (isSkeletal_sing G X M)).to_subtype
  have hreg := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    (isClosed_sing G X M) subset_rfl
  have hT := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX
    ((hp.branching_locii.1.union (isSkeletal_sing G X M)).isClosed) subset_union_right
  exact (isTame_iff hX y₀).2 (exists_developing_maxBranched_of_branchedCovering hreg y₀ hp hT hD)

/-- **`lem:embedding_tame`** (`RamcovGX.tex:1831`; closed under DEC-66: `M`, `N` Hausdorff,
locally path-connected, first countable, the §2.5 standing setting): if
`f : M → N` is an a.e. `(G,X)`-morphism of connected singular `(G,X)`-manifolds and `N` is
tame, then `M` is tame. The paper's lift
`\widetilde M → \widetilde N` need not exist (`f` may send regular points to singular ones); the
proof lifts `f` instead from `\widehat M = \widetilde M^{T}`, `T = M ∖ U` for a portly `U` on which
`f` is regular: `\widetilde{M∖T} → M∖T → reg N` lifts to `\widetilde{reg N}` (simply connected
source), the lift extends to the Fox completions (`IsFoxCompletion.existsUnique_extend`), and
composed with the developing map of `\widetilde N` it is a developing map of `\widehat M → M`
(`lem:morphism_singular_manifolds_branched`); `prop:branched_devmap` concludes. -/
theorem isTame_of_isAEMorphism (hX : IsLocallyUnloopable X) {N : Type v} [TopologicalSpace N]
    [T2Space N] [LocPathConnectedSpace N] [FirstCountableTopology N] [ConnectedSpace N]
    [SingularGXStructure G X N] {f : M → N} (hf : IsAEMorphism G X f) (hN : IsTame G X N) :
    IsTame G X M := by
  have hBM := isMaximalAEAtlas_aeAtlas G X M
  have hBN := isMaximalAEAtlas_aeAtlas G X N
  -- the developing map of `\widetilde N`
  have hSN := isSkeletal_sing G X N
  obtain ⟨z₀⟩ := (nonempty_compl_of_isSkeletal hSN).to_subtype
  have hregN := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX hSN.isClosed
    subset_rfl
  obtain ⟨DN, hDN⟩ := (isTame_iff hX z₀).1 hN
  -- the portly set on which `f` is regular
  obtain ⟨U, hU, hfU⟩ := ((isAEMorphismOf_iff hBN.1).1 hf).2
  set T : Set M := Uᶜ with hTdef
  have hT : IsSkeletal T := isSkeletal_compl_iff.2 hU
  have hSingT : Sing G X M ⊆ T := fun x hx hxU => hx (hfU.subset_support hxU)
  have hslT := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX hT.isClosed hSingT
  obtain ⟨y₁⟩ := (nonempty_compl_of_isSkeletal hT).to_subtype
  obtain ⟨h₁, hbc₁, -, -, hl₁, -⟩ := maxBranched_basic hT hslT y₁
  obtain ⟨h₂, hbc₂, -, -, hl₂, -⟩ := maxBranched_basic hSN hregN z₀
  haveI := hl₁
  haveI := hl₂
  -- lift `f` on `\widetilde{M ∖ T}` to `\widetilde{reg N}`
  haveI : LocPathConnectedSpace (Tᶜ : Set M) := (isSkeletal_iff.1 hT).isOpen.locPathConnectedSpace
  haveI : LocPathConnectedSpace ((Sing G X N)ᶜ : Set N) :=
    (isSkeletal_iff.1 hSN).isOpen.locPathConnectedSpace
  haveI : PathConnectedSpace ((Sing G X N)ᶜ : Set N) :=
    pathConnectedSpace_iff_connectedSpace.2
      (isConnected_iff_connectedSpace.1 (isSkeletal_iff.1 hSN).isConnected)
  haveI := UniversalCover.simplyConnectedSpace (y₀ := y₁) hslT
  have hπN := UniversalCover.isCoveringMap_proj (y₀ := z₀) hregN
  have hmem : ∀ c : UniversalCover (Tᶜ : Set M) y₁,
      f (univCoverProj T y₁ c) ∈ ((Sing G X N)ᶜ : Set N) := fun c => by
    have hc : univCoverProj T y₁ c ∈ U := not_not.1 (UniversalCover.proj (Tᶜ : Set M) y₁ c).2
    show f _ ∈ (Reg G X N)ᶜᶜ
    rw [compl_compl]
    exact hfU.mapsTo hc
  set φ : C(UniversalCover (Tᶜ : Set M) y₁, ((Sing G X N)ᶜ : Set N)) :=
    ⟨fun c => ⟨f (univCoverProj T y₁ c), hmem c⟩,
      (hf.continuous.comp (continuous_subtype_val.comp UniversalCover.continuous_proj)).subtype_mk
        _⟩
  obtain ⟨e₀, he₀⟩ := UniversalCover.proj_surjective (y₀ := z₀) (φ (UniversalCover.base y₁))
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hπN.existsUnique_continuousMap_lifts φ (UniversalCover.base y₁) e₀ he₀
  have hcomm : ∀ c, univCoverProj (Sing G X N) z₀ (F c) = f (univCoverProj T y₁ c) := fun c =>
    congrArg Subtype.val (congrFun hF c)
  -- extend to the completions
  obtain ⟨Ĝ, ⟨hĜc, hĜp, -⟩, -⟩ :=
    h₁.toIsFoxCompletion.existsUnique_extend h₂.toIsFoxCompletion hf.continuous F.continuous hcomm
  have hĜ := morphism_singular_manifolds_branched hBM.1 hBN.1 hf hbc₁ hbc₂ hĜc hĜp
  have hD : IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base (DN ∘ Ĝ) := hDN.comp hĜ
  exact isTame_of_isDevelopingMapOf hX hbc₁ hD

/-- **`cor:branched_covering_tame_singular`** (`RamcovGX.tex:1837`; closed under DEC-66, as
`lem:embedding_tame`): a branched covering `p : N → M` of a tame singular `(G,X)`-manifold,
`N` with the structure making `p` an a.e.
`(G,X)`-morphism (`prop:singular_manifold_branched_covering`), is tame. -/
theorem isTame_of_isBranchedCovering (hX : IsLocallyUnloopable X) {N : Type v} [TopologicalSpace N]
    [T2Space N] [LocPathConnectedSpace N] [FirstCountableTopology N] [SingularGXStructure G X N]
    {p : N → M} (hp : IsBranchedCovering p) (hpm : IsAEMorphism G X p) (hM : IsTame G X M) :
    IsTame G X N := by
  haveI := hp.connectedSpace_source
  exact isTame_of_isAEMorphism hX hpm hM

/-- **`cor:branched_covering_tame_singular`** (closed under DEC-66), with `N`'s structure given
as the pullback `p^*B`. -/
theorem isTame_of_isBranchedCovering' (hX : IsLocallyUnloopable X) {N : Type v}
    [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N] [FirstCountableTopology N]
    [SingularGXStructure G X N] {p : N → M} (hp : IsBranchedCovering p)
    (hN : aeAtlas G X N = aePullback G (aeAtlas G X M) p) (hM : IsTame G X M) : IsTame G X N := by
  refine isTame_of_isBranchedCovering hX hp ?_ hM
  have hB := isMaximalAEAtlas_aeAtlas G X M
  have := (aePullback_spec_of_isAELocalHomeomorph hB.1 hp.isSpread.continuous
    (hp.isAELocalHomeomorph hB.1)).2
  unfold IsAEMorphism
  rw [hN]
  exact this

/-- **`cor:open_subsets_tame_singular`** (`RamcovGX.tex:1839`; closed under DEC-66, as
`lem:embedding_tame`): a (connected — the section's standing convention, l.1712, with DEC-66(b))
open subset of a tame singular
`(G,X)`-manifold, with the induced
structure, is tame. -/
theorem isTame_opens (hX : IsLocallyUnloopable X) (hM : IsTame G X M) (U : Opens M)
    [ConnectedSpace U] : IsTame G X U :=
  isTame_of_isAEMorphism hX (isAEMorphism_opensSingular_val U) hM

/-- The forward half of `theo:local_tame` in its strong form: a tame `M` has, at every point, a
basis of connected open tame neighbourhoods. -/
theorem IsTame.exists_opens_subset (hX : IsLocallyUnloopable X) (hM : IsTame G X M) (x : M)
    {W : Set M} (hW : W ∈ 𝓝 x) :
    ∃ U : Opens M, x ∈ U ∧ (U : Set M) ⊆ W ∧ IsConnected (U : Set M) ∧ IsTame G X U := by
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVW⟩ := (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 hW
  haveI : ConnectedSpace (⟨V, hVo⟩ : Opens M) := isConnected_iff_connectedSpace.1 hVc
  exact ⟨⟨V, hVo⟩, hxV, hVW, hVc, isTame_opens hX hM _⟩

/-! ### `theo:local_tame` -/

/-- The classical developing map of `\widetilde{reg M}` (`GX.exists_developing_of_simplyConnected`),
read on `\widetilde M`: near every regular point it is a translate of a chart of `M` read through
the projection. -/
theorem exists_regDeveloping_maxBranched
    (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M)) (y₀ : ((Sing G X M)ᶜ : Set M)) :
    ∃ F₀ : MaxBranchedCover (Sing G X M) y₀ → X, ∀ c : MaxBranchedCover (Sing G X M) y₀,
      c.base ∈ (Sing G X M)ᶜ → ∃ c' ∈ aeAtlas G X M, c.base ∈ c'.source ∧
        ∃ h : G, ∀ᶠ c'' in 𝓝 c, F₀ c'' = h • c' c''.base := by
  set B := aeAtlas G X M
  have hBm : IsMaximalAEAtlas G B := isMaximalAEAtlas_aeAtlas G X M
  have hS₀ : IsSkeletal (Sing G X M) := isSkeletal_sing G X M
  have hRegB : (Sing G X M)ᶜ = support B := compl_compl _
  obtain ⟨-, hβbc, -, hβpre, hβl, hβsp⟩ := maxBranched_basic hS₀ hreg y₀
  haveI := hβl
  haveI : LocPathConnectedSpace ((Sing G X M)ᶜ : Set M) :=
    (isSkeletal_iff.1 hS₀).isOpen.locPathConnectedSpace
  have hπcov := UniversalCover.isCoveringMap_proj (y₀ := y₀) hreg
  haveI := UniversalCover.simplyConnectedSpace (y₀ := y₀) hreg
  haveI : T2Space (UniversalCover ((Sing G X M)ᶜ : Set M) y₀) := t2Space_of_isCoveringMap hπcov
  have hπ : IsLocalHomeomorph (Subtype.val ∘ UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀) :=
    (isSkeletal_iff.1 hS₀).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
      hπcov.isLocalHomeomorph
  obtain ⟨F, -, hF⟩ := exists_developing_of_simplyConnected (G := G) hBm.1 hπ
    (fun z => by rw [← hRegB]; exact (UniversalCover.proj _ y₀ z).2)
  have hemb := SpreadEnd.isEmbedding_ofPoint hβsp
  have hoe : IsOpenEmbedding (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) :=
    ⟨hemb, by rw [← hβpre]; exact hS₀.isClosed.isOpen_compl.preimage hβbc.isSpread.continuous⟩
  refine ⟨Function.extend (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) F
      (fun _ => F (UniversalCover.base y₀)), fun c hc => ?_⟩
  have hc' : c ∈ range (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) := by
    rw [← hβpre]; exact hc
  obtain ⟨z, rfl⟩ := hc'
  obtain ⟨c', hc', hzc', h, hh⟩ := hF z
  refine ⟨c', hc', hzc', h, ?_⟩
  rw [← hoe.map_nhds_eq z, eventually_map]
  filter_upwards [hh] with z' hz'
  rw [hemb.injective.extend_apply]
  exact hz'

/-- The local step of `theo:local_tame`, (2) ⇒ (1): over a tame open `V ∋ x`, the developing map
`F₀` of `\widetilde{reg M}` extends continuously to the component `\widehat V` of `p⁻¹(V)`
through `xt`. Route of the paper's proof: `\widehat V → V` is a branched covering
(`lem:branched_covering_restriction`) possibly branched over `sing V`, `\widetilde V → \widehat V`
by universality; the developing map `D_V` of `\widetilde V` and `F₀` read on `\widetilde V` differ
by one `g` on the connected `\widetilde{reg V}`, so `D_V` is constant on the fibres of the open map
`\widetilde V → \widehat V` and descends. -/
theorem exists_local_tame_extension (hX : IsLocallyUnloopable X)
    (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M)) (y₀ : ((Sing G X M)ᶜ : Set M))
    {F₀ : MaxBranchedCover (Sing G X M) y₀ → X}
    (hF₀ : ∀ c : MaxBranchedCover (Sing G X M) y₀, c.base ∈ (Sing G X M)ᶜ →
      ∃ c' ∈ aeAtlas G X M, c.base ∈ c'.source ∧ ∃ h : G, ∀ᶠ c'' in 𝓝 c, F₀ c'' = h • c' c''.base)
    {V : Opens M} (hV : IsTame G X V) (xt : MaxBranchedCover (Sing G X M) y₀)
    (hx : xt.base ∈ V) :
    ∃ W : Set (MaxBranchedCover (Sing G X M) y₀), IsOpen W ∧ xt ∈ W ∧
      ∃ h : MaxBranchedCover (Sing G X M) y₀ → X, ContinuousOn h W ∧
        ∀ w ∈ W, w.base ∈ (Sing G X M)ᶜ → h w = F₀ w := by
  have hS₀ := isSkeletal_sing G X M
  obtain ⟨-, hβbc, hβS, -, hβl, -⟩ := maxBranched_basic hS₀ hreg y₀
  haveI := hβl
  haveI : ConnectedSpace V := hV.connectedSpace
  have hβc : Continuous (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) := hβbc.isSpread.continuous
  -- the component `\widehat V` of `p⁻¹(V)` through `xt`
  set Wh : Set (MaxBranchedCover (Sing G X M) y₀) := connectedComponentIn ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' (V : Set M)) xt
  have hWho : IsOpen Wh := (V.isOpen.preimage hβc).connectedComponentIn
  have hxWh : xt ∈ Wh := mem_connectedComponentIn hx
  have hcomp : IsCompOf (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) (V : Set M) Wh := isCompOf_connectedComponentIn hx
  have hmaps : MapsTo (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) Wh (V : Set M) :=
    fun w hw => connectedComponentIn_subset ((SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) ⁻¹' (V : Set M)) xt hw
  have hVconn : IsPreconnected (V : Set M) :=
    isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace V)
  haveI : LocPathConnectedSpace Wh := hWho.locPathConnectedSpace
  set q : Wh → V := fun w => ⟨(w : MaxBranchedCover (Sing G X M) y₀).base, hmaps w.2⟩ with hqdef
  have hq : IsBranchedCovering q :=
    branched_covering_restriction hβbc V.isOpen hVconn hcomp hmaps
  -- `q` is possibly branched over `sing V`
  have hqS : IsPossiblyBranchedOver q (Sing G X V) := by
    intro v hv
    rw [sing_opensSingular]
    by_contra hvS
    apply hv
    have hvo : (v : M) ∈ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) := by
      by_contra hn; exact hvS (hβS hn)
    have := subset_ordY_restrict hβc hmaps V.isOpen
      (fun W' hW'V a ha => hcomp.subset_of_meets isPreconnected_connectedComponentIn
        ((connectedComponentIn_subset _ _).trans (preimage_mono hW'V))
        ⟨a, mem_connectedComponentIn ha, a.2⟩) (fun b _ => hq.surjective b)
    exact this ⟨v.2, hvo⟩
  -- the developing map of `\widetilde V`
  have hSV := isSkeletal_sing G X V
  have hregV := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX hSV.isClosed subset_rfl
  obtain ⟨v₀⟩ := (nonempty_compl_of_isSkeletal hSV).to_subtype
  obtain ⟨DV, hDV⟩ := (isTame_iff hX v₀).1 hV
  obtain ⟨-, hγbc, hγS, -, hγl, -⟩ := maxBranched_basic hSV hregV v₀
  haveI := hγl
  haveI := hγbc.connectedSpace_source
  -- `Ψ : \widetilde V → \widehat V`
  obtain ⟨Ψ, hΨc, hΨp, hΨbc, -⟩ := maxBranched_universal hSV hregV v₀ hq hqS
  have hΨb : ∀ e, ((Ψ e : MaxBranchedCover (Sing G X M) y₀)).base = ((e.base : V) : M) := fun e =>
    congrArg Subtype.val (hΨp e)
  -- the structures
  have hBVm := isMaximalAEAtlas_aeAtlas G X V
  have hBm := isMaximalAEAtlas_aeAtlas G X M
  have hAγ := aePullback_spec_of_isAELocalHomeomorph hBVm.1 hγbc.isSpread.continuous
    (hγbc.isAELocalHomeomorph hBVm.1)
  set Rv : Set (MaxBranchedCover (Sing G X V) v₀) := SpreadEnd.base ⁻¹' (Sing G X V)ᶜ
  have hRvp : IsPortly Rv := hγbc.isPortly_preimage hSV
  have hordγ : (Sing G X V)ᶜ ⊆
      ordY (SpreadEnd.base : MaxBranchedCover (Sing G X V) v₀ → V) := fun y hy => by
    by_contra hn; exact hy (hγS hn)
  have hRegBV : (Sing G X V)ᶜ = support (aeAtlas G X V) := compl_compl _
  have hRvsupp : Rv ⊆ support (aePullback G (aeAtlas G X V)
      (SpreadEnd.base : MaxBranchedCover (Sing G X V) v₀ → V)) := fun w hw =>
    hAγ.2.mem_support_of_isLocalHomeomorphOn' hAγ.1 hBVm.1 (by rw [← hRegBV]; exact hw)
      (hγbc.ordX_subset_isLocalHomeomorphOn (hordγ hw))
  have hmemReg : ∀ v : V, v ∈ (Sing G X V)ᶜ → (v : M) ∈ (Sing G X M)ᶜ := fun v hv => by
    have h' : v ∉ Sing G X V := hv
    rw [sing_opensSingular] at h'
    exact h'
  -- `D_V` is regular on `\widetilde{reg V}`
  have hDVreg := IsAEMorphismOf.regLocusOf_eq hAγ.1.1
    (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1 hDV
  rw [support_gxModelAtlas, preimage_univ, inter_univ] at hDVreg
  have hDVR := (isRegularOn_regLocusOf (G := G) _ (gxModelAtlas G X) DV).mono
    (by rw [hDVreg]; exact hRvsupp) hRvp.isOpen
  -- `ι ∘ p_V` is regular on `\widetilde{reg V}`
  have hcompV : IsAEMorphismOf G (aePullback G (aeAtlas G X V)
      (SpreadEnd.base : MaxBranchedCover (Sing G X V) v₀ → V)) (aeAtlas G X M)
      (Subtype.val ∘ (SpreadEnd.base : MaxBranchedCover (Sing G X V) v₀ → V)) :=
    IsAEMorphismOf.comp (isAEMorphism_opensSingular_val V) hAγ.2
  have hregc := hcompV.regLocusOf_eq hAγ.1.1 hBm.1
  have hfR : IsRegularOn G (aePullback G (aeAtlas G X V)
      (SpreadEnd.base : MaxBranchedCover (Sing G X V) v₀ → V)) (aeAtlas G X M)
      (Subtype.val ∘ (SpreadEnd.base : MaxBranchedCover (Sing G X V) v₀ → V)) Rv :=
    (isRegularOn_regLocusOf (G := G) _ _ _).mono (fun w hw => by
      rw [hregc]
      refine ⟨hRvsupp hw, ?_⟩
      have := hmemReg _ hw
      exact not_not.1 this) hRvp.isOpen
  -- `F₀` read on `\widetilde V` is regular there
  set F₁ : MaxBranchedCover (Sing G X V) v₀ → X := fun e => F₀ (Ψ e : MaxBranchedCover (Sing G X M) y₀) with hF₁def
  have hF₁R : IsRegularOn G (aePullback G (aeAtlas G X V)
      (SpreadEnd.base : MaxBranchedCover (Sing G X V) v₀ → V)) (gxModelAtlas G X) F₁ Rv := by
    refine isRegularOn_model_of_eventually_comp hAγ.1.1.1 hfR fun e he => ?_
    have hbe : ((Ψ e : MaxBranchedCover (Sing G X M) y₀)).base ∈ (Sing G X M)ᶜ := by rw [hΨb]; exact hmemReg _ he
    obtain ⟨c', hc', hec', g, hg⟩ := hF₀ (Ψ e) hbe
    refine ⟨c', hc', ?_, g, ?_⟩
    · show ((e.base : V) : M) ∈ c'.source
      rw [← hΨb]; exact hec'
    · filter_upwards [(continuous_subtype_val.comp hΨc).continuousAt.eventually hg] with e' he'
      show F₀ (Ψ e' : MaxBranchedCover (Sing G X M) y₀) = g • c' ((e'.base : V) : M)
      rw [← hΨb]
      exact he'
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isRegularOn hRvp.isConnected.isPreconnected hF₁R hDVR
  -- the fibres of `Ψ`
  set Wr : Set Wh := q ⁻¹' (Sing G X V)ᶜ
  have hWrp : IsPortly Wr := hq.isPortly_preimage hSV
  have hWrmem : ∀ w : Wh, w ∈ Wr ↔ (w : MaxBranchedCover (Sing G X M) y₀).base ∈ (Sing G X M)ᶜ := fun w => by
    show q w ∉ Sing G X V ↔ _
    rw [sing_opensSingular]
    rfl
  have hΨW : ∀ y, Ψ y ∈ Wr ↔ y ∈ Rv := fun y => by
    show q (Ψ y) ∈ (Sing G X V)ᶜ ↔ y.base ∈ (Sing G X V)ᶜ
    rw [hΨp]
  have hΨo : IsOpenMap Ψ := (spread_connected_image hΨbc).1
  have hDVc : Continuous DV := hDV.continuous
  have hfib : ∀ x x', Ψ x = Ψ x' → DV x = DV x' := by
    intro x x' hxx'
    by_contra hne
    obtain ⟨O, O', hO, hO', hxO, hxO', hOO'⟩ := t2_separation hne
    have hU : IsOpen (Ψ '' (DV ⁻¹' O) ∩ Ψ '' (DV ⁻¹' O')) :=
      (hΨo _ (hO.preimage hDVc)).inter (hΨo _ (hO'.preimage hDVc))
    obtain ⟨w, ⟨⟨u, hu, rfl⟩, ⟨u', hu', huu'⟩⟩, hwW⟩ :=
      hWrp.dense.inter_open_nonempty _ hU ⟨Ψ x, ⟨x, hxO, rfl⟩, ⟨x', hxO', hxx'.symm⟩⟩
    have huV : u ∈ Rv := (hΨW u).1 hwW
    have hu'V : u' ∈ Rv := (hΨW u').1 (by rw [huu']; exact hwW)
    have heq : DV u = DV u' := by
      rw [hg u huV, hg u' hu'V]
      show g • F₀ (Ψ u : MaxBranchedCover (Sing G X M) y₀) = g • F₀ (Ψ u' : MaxBranchedCover (Sing G X M) y₀)
      rw [huu']
    exact Set.disjoint_left.1 hOO' hu (by rw [heq]; exact hu')
  -- descent along `Ψ`
  have hΨs := hΨbc.surjective
  set D'' : Wh → X := fun w => DV (hΨs w).choose
  have hD''Ψ : ∀ y, D'' (Ψ y) = DV y := fun y => hfib _ _ (hΨs (Ψ y)).choose_spec
  have hD''c : Continuous D'' := (hΨo.isQuotientMap hΨc hΨs).continuous_iff.2 (by
    have : D'' ∘ Ψ = DV := funext hD''Ψ
    rw [this]; exact hDVc)
  refine ⟨Wh, hWho, hxWh, fun z => if hz : z ∈ Wh then g⁻¹ • D'' ⟨z, hz⟩ else F₀ z, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : Wh.restrict (fun z => if hz : z ∈ Wh then g⁻¹ • D'' ⟨z, hz⟩ else F₀ z) =
        fun w => g⁻¹ • D'' w := funext fun w => dif_pos w.2
    rw [this]
    exact hD''c.const_smul _
  · intro w hw hwR
    simp only [dif_pos hw]
    obtain ⟨y, hy⟩ := hΨs ⟨w, hw⟩
    have hyR : y ∈ Rv := (hΨW y).1 (by rw [hy]; exact (hWrmem _).2 hwR)
    have : D'' ⟨w, hw⟩ = g • F₀ w := by
      rw [← hy, hD''Ψ, hg y hyR]
      show g • F₀ (Ψ y : MaxBranchedCover (Sing G X M) y₀) = g • F₀ w
      rw [hy]
    rw [this, inv_smul_smul]

/-- `theo:local_tame`, (2) ⇒ (1) (`RamcovGX.tex:1844`; under DEC-66 and DEC-67(d), SCOPE (b)):
a locally tame singular
`(G,X)`-manifold is tame. The local extensions of `exists_local_tame_extension` agree on overlaps
(they agree with `F₀` on the dense regular part, `X` Hausdorff) and glue to a continuous map
`\widetilde M → X` regular on `\widetilde{reg M}`. -/
theorem isTame_of_isLocallyTame (hX : IsLocallyUnloopable X) (hloc : IsLocallyTame G X M) :
    IsTame G X M := by
  set B := aeAtlas G X M
  have hBm : IsMaximalAEAtlas G B := isMaximalAEAtlas_aeAtlas G X M
  have hS₀ : IsSkeletal (Sing G X M) := isSkeletal_sing G X M
  have hreg := semilocallySimplyConnected_compl_of_sing_subset (G := G) hX hS₀.isClosed subset_rfl
  obtain ⟨y₀⟩ := (nonempty_compl_of_isSkeletal hS₀).to_subtype
  obtain ⟨-, hβbc, hβS, -, hβl, -⟩ := maxBranched_basic hS₀ hreg y₀
  haveI := hβl
  obtain ⟨F₀, hF₀⟩ := exists_regDeveloping_maxBranched hreg y₀
  set R : Set (MaxBranchedCover (Sing G X M) y₀) := SpreadEnd.base ⁻¹' (Sing G X M)ᶜ with hRdef
  have hRp : IsPortly R := hβbc.isPortly_preimage hS₀
  have hLC : ∀ xt : MaxBranchedCover (Sing G X M) y₀,
      ∃ W : Set (MaxBranchedCover (Sing G X M) y₀), IsOpen W ∧ xt ∈ W ∧
        ∃ h : MaxBranchedCover (Sing G X M) y₀ → X, ContinuousOn h W ∧
          ∀ w ∈ W, w.base ∈ (Sing G X M)ᶜ → h w = F₀ w := fun xt => by
    obtain ⟨V, hxV, hV⟩ := hloc xt.base
    exact exists_local_tame_extension hX hreg y₀ hF₀ hV xt hxV
  choose W hWo hxW h hhc hhF using hLC
  have hagree : ∀ a b, EqOn (h a) (h b) (W a ∩ W b) := fun a b =>
    EqOn.of_subset_closure (s := W a ∩ W b ∩ R)
      (fun w hw => by rw [hhF a w hw.1.1 hw.2, hhF b w hw.1.2 hw.2])
      ((hhc a).mono inter_subset_left) ((hhc b).mono inter_subset_right) inter_subset_left
      (hRp.dense.open_subset_closure_inter ((hWo a).inter (hWo b)))
  set D : MaxBranchedCover (Sing G X M) y₀ → X := fun z => h z z
  have hDev : ∀ a, ∀ w ∈ W a, D w = h a w := fun a w hw => hagree w a ⟨hxW w, hw⟩
  have hDc : Continuous D := continuous_iff_continuousAt.2 fun a =>
    ((hhc a).continuousAt ((hWo a).mem_nhds (hxW a))).congr
      (eventuallyEq_of_mem ((hWo a).mem_nhds (hxW a)) fun w hw => (hDev a w hw).symm)
  have hDR : ∀ w ∈ R, D w = F₀ w := fun w hw => hhF w w (hxW w) hw
  -- `D` is regular on `R`
  have hAt := aePullback_spec_of_isAELocalHomeomorph hBm.1 hβbc.isSpread.continuous
    (hβbc.isAELocalHomeomorph hBm.1)
  have hRegB : (Sing G X M)ᶜ = support B := compl_compl _
  have hordβ : (Sing G X M)ᶜ ⊆
      ordY (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) := fun y hy => by
    by_contra hn; exact hy (hβS hn)
  have hRsupp : R ⊆ support (aePullback G B
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) := fun w hw =>
    hAt.2.mem_support_of_isLocalHomeomorphOn' hAt.1 hBm.1 (by rw [← hRegB]; exact hw)
      (hβbc.ordX_subset_isLocalHomeomorphOn (hordβ hw))
  have hregβ := hAt.2.regLocusOf_eq hAt.1.1 hBm.1
  have hβR := (isRegularOn_regLocusOf (G := G) _ B
    (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)).mono
    (fun w hw => by rw [hregβ]; exact ⟨hRsupp hw, by rw [← hRegB]; exact hw⟩) hRp.isOpen
  have hDR' : IsRegularOn G (aePullback G B
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) (gxModelAtlas G X) D R := by
    refine isRegularOn_model_of_eventually_comp hAt.1.1.1 hβR fun w hw => ?_
    obtain ⟨c', hc', hwc', g, hg⟩ := hF₀ w hw
    refine ⟨c', hc', hwc', g, ?_⟩
    filter_upwards [hg, hRp.isOpen.mem_nhds hw] with w' h1 h2
    rw [hDR w' h2, h1]
  exact (isTame_iff hX y₀).2 ⟨D, (isAEMorphismOf_iff
    (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1).2 ⟨hDc, R, hRp, hDR'⟩⟩

/-- **`theo:local_tame`** (`RamcovGX.tex:1844`; closed under DEC-66 and DEC-67(d): "locally
tamely singular" is `GX.IsLocallyTame`, SCOPE (b); `M` locally path-connected, DEC-66(c)):
a singular `(G,X)`-manifold is tamely singular iff it is locally tamely singular. -/
theorem isTame_iff_isLocallyTame (hX : IsLocallyUnloopable X) :
    IsTame G X M ↔ IsLocallyTame G X M := by
  refine ⟨fun h x => ?_, isTame_of_isLocallyTame hX⟩
  obtain ⟨U, hxU, -, -, hU⟩ := h.exists_opens_subset hX x univ_mem
  exact ⟨U, hxU, hU⟩

end Main

/-! ### `rem:tamely_singular_manifold_admits` -/

section Remark

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- The topology on `D(N)` "making `D` a homeomorphism" (`rem:tamely_singular_manifold_admits`):
the topology coinduced by `D : N → D(N)` (`GX.homeomorph_rangeTameTopology`). -/
@[reducible] def rangeTameTopology (D : N → X) : TopologicalSpace (range D) :=
  TopologicalSpace.coinduced (rangeFactorization D) inferInstance

/-- For an injective `D`, the coinduced topology makes `D : N → D(N)` a homeomorphism. -/
theorem homeomorph_rangeTameTopology {D : N → X} (hD : Injective D) :
    letI := rangeTameTopology D
    ∃ e : N ≃ₜ range D, ∀ x, (e x : X) = D x := by
  letI := rangeTameTopology D
  have hbij : Bijective (rangeFactorization D) :=
    ⟨fun a b h => hD (congrArg Subtype.val h), rangeFactorization_surjective⟩
  refine ⟨(Equiv.ofBijective _ hbij).toHomeomorphOfContinuousOpen continuous_coinduced_rng
    fun U hU => ?_, fun _ => rfl⟩
  show IsOpen (rangeFactorization D ⁻¹' (rangeFactorization D '' U))
  rwa [hbij.1.preimage_image]

/-- The orbit relation on `D(N)` of `Γ(N/M)` acting on `X` through the holonomy `ρ`. -/
def tameHolonomyOrbitSetoid (p : N → M) (D : N → X) (ρ : Deck p →* G) : Setoid (range D) where
  r a b := ∃ γ : Deck p, (b : X) = ρ γ • (a : X)
  iseqv := ⟨fun a => ⟨1, by rw [map_one, one_smul]⟩,
    fun ⟨γ, h⟩ => ⟨γ⁻¹, by rw [h, map_inv, inv_smul_smul]⟩,
    fun ⟨γ, h⟩ ⟨δ, h'⟩ => ⟨δ * γ, by rw [h', h, map_mul, mul_smul]⟩⟩

/-- `rem:tamely_singular_manifold_admits` (`RamcovGX.tex:1869`), for a **Galoisian** branched
covering `p : N → M` (SCOPE (c)): if `D : N → X` is injective with holonomy `ρ`
(`D ∘ γ = ρ(γ) D`), then `M` is homeomorphic to `Γ(N/M)\D(N)`, `Γ(N/M)` acting on `X` through
`ρ` and `D(N)` carrying the topology making `D` a homeomorphism, by `[D x] ↦ p x`. Neither
tameness of `M` nor that `D` be an a.e. morphism is used. -/
theorem tamely_singular_manifold_admits [T1Space M] [LocPathConnectedSpace M]
    [FirstCountableTopology M] {p : N → M} (hp : IsGaloisian p) {D : N → X} (hD : Injective D)
    {ρ : Deck p →* G} (hρ : IsHolonomyOf p D ρ) :
    letI := rangeTameTopology D
    ∃ h : Quotient (tameHolonomyOrbitSetoid p D ρ) ≃ₜ M,
      ∀ x, h (Quotient.mk _ ⟨D x, x, rfl⟩) = p x := by
  letI := rangeTameTopology D
  set S := tameHolonomyOrbitSetoid p D ρ
  -- the inverse of `D` on its range
  set g : range D → N := fun a => a.2.choose
  have hg : ∀ a, D (g a) = a := fun a => a.2.choose_spec
  have hgD : ∀ x, g ⟨D x, x, rfl⟩ = x := fun x => hD (hg _)
  have hgc : Continuous (p ∘ g) := by
    refine (continuous_coinduced_dom (f := rangeFactorization D)).2 ?_
    have : (p ∘ g) ∘ rangeFactorization D = p := funext fun x => by
      show p (g ⟨D x, x, rfl⟩) = p x
      rw [hgD]
    rw [this]; exact hp.1.isSpread.continuous
  have hresp : ∀ a b, a ≈ b → (p ∘ g) a = (p ∘ g) b := by
    rintro a b ⟨γ, hγ⟩
    have hb : g b = (γ : N ≃ₜ N) (g a) := hD (by rw [hg, hρ, hg]; exact hγ)
    show p (g a) = p (g b)
    rw [hb, deck_apply p γ.2]
  set f : Quotient S → M := Quotient.lift (p ∘ g) hresp
  have hfc : Continuous f := hgc.quotient_lift hresp
  have hfmk : ∀ x, f (Quotient.mk _ ⟨D x, x, rfl⟩) = p x := fun x => by
    show p (g ⟨D x, x, rfl⟩) = p x
    rw [hgD]
  have hinj : Injective f := by
    rintro ⟨a⟩ ⟨b⟩ hab
    change p (g a) = p (g b) at hab
    obtain ⟨φ, hφ, hφa⟩ := hp.2 _ _ hab
    refine Quotient.sound ⟨⟨φ, hφ⟩, ?_⟩
    rw [← hg b, ← hφa, ← hg a]
    exact hρ ⟨φ, hφ⟩ (g a)
  have hsurj : Surjective f := fun y => by
    obtain ⟨x, rfl⟩ := hp.1.surjective y
    exact ⟨_, hfmk x⟩
  have hπc : Continuous (fun x : N => (Quotient.mk S ⟨D x, x, rfl⟩ : Quotient S)) :=
    continuous_quotient_mk'.comp continuous_coinduced_rng
  have hpo : IsOpenMap p := (spread_connected_image hp.1).1
  have hfo : IsOpenMap f := fun O hO => by
    have : f '' O = p '' ((fun x : N => (Quotient.mk S ⟨D x, x, rfl⟩ : Quotient S)) ⁻¹' O) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with
        | h a =>
          obtain ⟨x, hx⟩ := a.2
          have ha : a = ⟨D x, x, rfl⟩ := Subtype.ext hx.symm
          subst ha
          exact ⟨x, hq, (hfmk x).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, hx, hfmk x⟩
    rw [this]
    exact hpo _ (hO.preimage hπc)
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hfc hfo, hfmk⟩

/-- `rem:tamely_singular_manifold_admits` (`RamcovGX.tex:1869`), **as singular
`(G,X)`-manifolds** (SCOPE (c), the second reading of "isomorphic"), for a Galoisian `p : N → M`
which is an a.e. `(G,X)`-morphism (`N` with the structure of
`prop:singular_manifold_branched_covering`). `D(N)` carries the structure transported from `N`
along the homeomorphism `D` (for a developing map `D`, the one for which the inclusion
`D(N) ⊆ X` is an a.e. morphism), and `Γ(N/M)\D(N)` the **quotient structure**: the unique
maximal a.e. atlas for which the projection `N ≅ D(N) → Γ(N/M)\D(N)` is an a.e. morphism.
The homeomorphism `h : Γ(N/M)\D(N) ≃ₜ M`, `[D x] ↦ p x`, is then an isomorphism: the quotient
structure exists and is unique, and it is `h^* B_M` (`lem:aepullback`), for which `h` is an a.e.
`(G,X)`-morphism (whose inverse is one, `IsAEMorphismOf.symm_of_homeomorph`). -/
theorem tamely_singular_manifold_admits_aeIso [ContinuousConstSMul G X] [LocallyConnectedSpace X]
    [T2Space X] [IsRigidAction G X] [T1Space M] [LocPathConnectedSpace M]
    [FirstCountableTopology M] [LocallyConnectedSpace N] [SingularGXStructure G X M]
    [SingularGXStructure G X N] {p : N → M} (hp : IsGaloisian p) (hpm : IsAEMorphism G X p)
    {D : N → X} (hD : Injective D) {ρ : Deck p →* G} (hρ : IsHolonomyOf p D ρ) :
    letI := rangeTameTopology D
    ∃ h : Quotient (tameHolonomyOrbitSetoid p D ρ) ≃ₜ M,
      (∀ x, h (Quotient.mk _ ⟨D x, x, rfl⟩) = p x) ∧
      IsMaximalAEAtlas G (aePullback G (aeAtlas G X M) h) ∧
      IsAEMorphismOf G (aePullback G (aeAtlas G X M) h) (aeAtlas G X M) h ∧
      IsAEMorphismOf G (aeAtlas G X M) (aePullback G (aeAtlas G X M) h) h.symm ∧
      IsAEMorphismOf G (aeAtlas G X N) (aePullback G (aeAtlas G X M) h)
        (fun x => (Quotient.mk _ ⟨D x, x, rfl⟩ : Quotient (tameHolonomyOrbitSetoid p D ρ))) ∧
      ∀ B : Set (OpenPartialHomeomorph (Quotient (tameHolonomyOrbitSetoid p D ρ)) X),
        IsMaximalAEAtlas G B →
        IsAEMorphismOf G (aeAtlas G X N) B
          (fun x => (Quotient.mk _ ⟨D x, x, rfl⟩ : Quotient (tameHolonomyOrbitSetoid p D ρ))) →
        B = aePullback G (aeAtlas G X M) h := by
  letI := rangeTameTopology D
  obtain ⟨h, hh⟩ := tamely_singular_manifold_admits hp hD hρ
  set π : N → Quotient (tameHolonomyOrbitSetoid p D ρ) := fun x => Quotient.mk _ ⟨D x, x, rfl⟩
  have hπ : π = h.symm ∘ p := funext fun x => by
    show π x = h.symm (p x)
    rw [← hh x, h.symm_apply_apply]
  have hBM := isMaximalAEAtlas_aeAtlas G X M
  have hloc : IsAELocalHomeomorph (aeAtlas G X M) h := by
    refine ⟨h ⁻¹' Reg G X M, Reg G X M, ?_, isPortly_reg G X M, subset_rfl, fun _ hx => hx,
      h.isLocalHomeomorph.isLocalHomeomorphOn⟩
    rw [← h.image_symm]
    exact (isPortly_reg G X M).image_of_isOpenMap h.symm.continuous h.symm.isOpenMap
      h.symm.surjective
  have hspec := aePullback_spec_of_isAELocalHomeomorph hBM.1 h.continuous hloc
  have hsymm : IsAEMorphismOf G (aeAtlas G X M) (aePullback G (aeAtlas G X M) h) h.symm :=
    IsAEMorphismOf.symm_of_homeomorph hspec.1 hBM hspec.2
  have hπm : IsAEMorphismOf G (aeAtlas G X N) (aePullback G (aeAtlas G X M) h) π := by
    rw [hπ]; exact hsymm.comp hpm
  have hπo : IsOpenMap π := by
    rw [hπ]; exact h.symm.isOpenMap.comp (spread_connected_image hp.1).1
  have hπs : Surjective π := by
    rw [hπ]; exact h.symm.surjective.comp hp.1.surjective
  exact ⟨h, hh, hspec.1, hspec.2, hsymm, hπm, fun B hB hBπ =>
    IsAEMorphismOf.eq_of_isMaximalAEAtlas_right hB hspec.1 hπo hπs hBπ hπm⟩

end Remark

/-! ### `ex:take_closed_unit_disc`: the last sentence -/

/-- `ex:take_closed_unit_disc` (`RamcovGX.tex:1877`), its last sentence, in the closed unit disc
`X ⊆ ℂ`: a boundary point `ξ` is interior to no subset `A` of `X` contained in the open disc
`∪ {ξ}` — every neighbourhood of `ξ` in `X` meets the circle elsewhere. -/
theorem not_mem_interior_of_subset_ball_insert {ξ : ℂ} (hξ : ‖ξ‖ = 1)
    {A : Set (Metric.closedBall (0 : ℂ) 1)}
    (hA : ∀ z ∈ A, (z : ℂ) = ξ ∨ ‖(z : ℂ)‖ < 1) :
    (⟨ξ, by rw [Metric.mem_closedBall, dist_zero_right, hξ]⟩ : Metric.closedBall (0 : ℂ) 1) ∉
      interior A := by
  intro hint
  have hnhds : A ∈ 𝓝 (⟨ξ, by rw [Metric.mem_closedBall, dist_zero_right, hξ]⟩ :
      Metric.closedBall (0 : ℂ) 1) := mem_interior_iff_mem_nhds.1 hint
  -- the points `ξ e^{i/(n+1)}` of the circle tend to `ξ`
  set w : ℕ → ℂ := fun n => ξ * Complex.exp (Complex.ofReal (1 / ((n : ℝ) + 1)) * Complex.I)
  have hw1 : ∀ n, ‖w n‖ = 1 := fun n => by
    rw [norm_mul, hξ, one_mul, Complex.norm_exp_ofReal_mul_I]
  have hwmem : ∀ n, w n ∈ Metric.closedBall (0 : ℂ) 1 := fun n => by
    rw [Metric.mem_closedBall, dist_zero_right, hw1]
  have hlim : Tendsto w atTop (𝓝 ξ) := by
    have h0 : Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => ξ * Complex.exp (Complex.ofReal (1 / ((n : ℝ) + 1)) * Complex.I))
        atTop (𝓝 (ξ * Complex.exp (Complex.ofReal 0 * Complex.I))) := by
      refine tendsto_const_nhds.mul ((Complex.continuous_exp.tendsto _).comp ?_)
      exact ((Complex.continuous_ofReal.tendsto 0).comp h0).mul_const _
    have h2 : ξ * Complex.exp (Complex.ofReal 0 * Complex.I) = ξ := by simp
    rw [h2] at h1
    exact h1
  have hlim' : Tendsto (fun n => (⟨w n, hwmem n⟩ : Metric.closedBall (0 : ℂ) 1)) atTop
      (𝓝 ⟨ξ, by rw [Metric.mem_closedBall, dist_zero_right, hξ]⟩) := by
    rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    exact hlim
  obtain ⟨n, hn⟩ := (hlim'.eventually hnhds).exists
  rcases hA _ hn with h | h
  · -- `e^{i/(n+1)} ≠ 1`
    have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ
    have hexp : Complex.exp (Complex.ofReal (1 / ((n : ℝ) + 1)) * Complex.I) = 1 := by
      have h' : ξ * Complex.exp (Complex.ofReal (1 / ((n : ℝ) + 1)) * Complex.I) = ξ * 1 := by
        rw [mul_one]; exact h
      exact mul_left_cancel₀ hξ0 h'
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hexp
    have hk' : (1 : ℝ) / ((n : ℝ) + 1) = k * (2 * Real.pi) := by
      have := congrArg Complex.im hk
      simp only [Complex.mul_I_im, Complex.ofReal_re] at this
      rw [this]
      simp
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hk0 : (0 : ℝ) < k := by
      by_contra hk0
      push Not at hk0
      nlinarith [Real.pi_pos]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by exact_mod_cast hk0)
    nlinarith [Real.pi_gt_three]
  · exact absurd (hw1 n) (ne_of_lt h)

/-- `ex:take_closed_unit_disc`, the horodisc: for a Euclidean disc `H` of radius `r < 1` internally
tangent to the unit circle at `ξ` (a horodisc of the Poincaré disc centred at `ξ`), `H ∪ {ξ}` is
not open in the closed unit disc `X`. -/
theorem not_isOpen_horodisc_insert {ξ : ℂ} (hξ : ‖ξ‖ = 1) {r : ℝ} (hr : r < 1) :
    ¬ IsOpen {z : Metric.closedBall (0 : ℂ) 1 |
      (z : ℂ) = ξ ∨ (z : ℂ) ∈ Metric.ball (((1 - r : ℝ) : ℂ) * ξ) r} := by
  intro hO
  refine not_mem_interior_of_subset_ball_insert hξ (A := {z : Metric.closedBall (0 : ℂ) 1 |
      (z : ℂ) = ξ ∨ (z : ℂ) ∈ Metric.ball (((1 - r : ℝ) : ℂ) * ξ) r}) ?_ ?_
  · rintro z (h | h)
    · exact Or.inl h
    · right
      rw [Metric.mem_ball, dist_eq_norm] at h
      have hc : ‖((1 - r : ℝ) : ℂ) * ξ‖ = 1 - r := by
        rw [norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      calc ‖(z : ℂ)‖ = ‖((z : ℂ) - ((1 - r : ℝ) : ℂ) * ξ) + ((1 - r : ℝ) : ℂ) * ξ‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖(z : ℂ) - ((1 - r : ℝ) : ℂ) * ξ‖ + ‖((1 - r : ℝ) : ℂ) * ξ‖ := norm_add_le _ _
        _ < r + (1 - r) := by rw [hc]; linarith
        _ = 1 := by ring
  · rw [hO.interior_eq]
    exact Or.inl rfl

end GX
