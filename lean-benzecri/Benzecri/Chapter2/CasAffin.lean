import Benzecri.Chapter2.Compact
import Benzecri.Chapter2.Projection

/-!
# Chapter 2 § 2, the affine case — the Remark before Prop. 7′ (affine automorphisms are projective automorphisms, an affine pocket is a projective one) and Prop. 7′

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal p. 253; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-cas-affin.

* **`bzrem:c2s2r1_cas_affin`** — `benzecri1960_ch2.tex:493` (Remarque, l.493–505).
  `Benzecri.cas_affin`, every dimension, sorry-free. Its parts: `GXAut.affToProj` (the affine
  automorphisms embed in the projective automorphisms of the canonical projective structure
  `projOfAff`, each acting as itself: `GXAut.affToProj_smul`, `GXAut.affToProj_injective`), from
  `IsGXMorphism.affToProj` and its general form `IsGXMorphism.transport` / `GXAut.transport`;
  sweepability carried over with the same compact (`IsBalayableFor.affToProj`); the pocket
  (`IsPocheAff.toPocheProj`, strict).
* **`bzprop:c2s2p7prime_compact_dans_poche_affine`** — `benzecri1960_ch2.tex:507` (Prop. 7′,
  l.507–512; no proof printed, l.513). `Benzecri.compact_dans_poche_affine` and
  `Benzecri.deux_points_dans_poche_affine`, every dimension, sorry-free; both assertions together,
  over the paper's manifolds: `compactDansPocheAffinePrinted n` for every `n`.

Non-vacuity. Every dimension: `ℝⁿ` swept by its translations, with the pocket `(ℝⁿ, id, 0)`
(`compactDansPocheAffine_hypotheses_model`). Every dimension `n + 1 ≥ 1`, with a NON-CONSTANT cote:
the open half-space `{x₀ > 0}` of `ℝⁿ⁺¹`, swept by its affine automorphisms from one point, with
the pocket `({0 < x₀ < 1}, id, x₀)` (`compactDansPocheAffine_hypotheses_demiEspace`, and Prop. 7′
applied to it, `exists_smul_subset_slab_demiEspace`). « connexe » is needed in the Remark's last
sentence: `not_deuxPointsDansPocheAffineSansConnexe` (SCOPE).

> **Remarque.** Soit $V$ une variété localement affine balayable pour un groupe $G$
> d'automorphismes affins. Supposons que $V$ possède une poche $(P, \varphi, z)$. Pour la structure
> localement projective de $V$ (cf. chap. 1, § 1, déf. 12, remarque), $G$ est un groupe
> d'automorphismes projectifs; de plus (cf. chap. 2, § 1, déf. 1′, remarque), si $j$ désigne un
> homéomorphisme de $\R^n$ sur un hémisphère $\mathring{H}$ de $S(n)$ ($j$ compatible avec les
> structures affines), $(P, \mathring{H}, j\circ\varphi, z\circ j^{-1})$ est une poche de la
> variété localement projective de $V$. La proposition 7 et son corollaire sont donc vrais aussi
> dans le cas affin : on a l'énoncé :
>
> **Proposition 7′.** Soit $V$ une variété localement affine, connexe et balayable pour un groupe
> $G$ d'automorphismes affins; soit $(P, \varphi, z)$ une poche de $V$. Soit $E$ un compact de
> $V$. Il existe $g\in G$ tel que $gE\subset P$. Si $M$ et $N$ sont deux points de $V$, il existe
> $g\in G$ tel que : $gM\in P$; $gN\in P$.

## The proof formalized

The Remark's argument. An affine morphism, read in the charts `j₀ ∘ φ` of `projOfAff`
(`j₀ = hemiChart`, `y ↦ s(y, 1)`), is `j₀ ∘ a ∘ φ = affToGS a • (j₀ ∘ φ)` near every point
(`Sphere.hemiChart_apply_eq_smul`), so it is a projective morphism; an affine automorphism (a
homeomorphism which is a morphism both ways) is then a projective one, and `f ↦ f` is an injective
group morphism `GXAut.affToProj`. A compact `K` with `⋃_{g ∈ G} gK = V` serves for the image of `G`
(the action is unchanged). With any `j : ℝⁿ ≃ H̊`, the strict `IsPocheAff.toPocheProj` gives the
projective pocket. **Prop. 7′**: Prop. 7 (`compact_dans_poche`) and its corollary
(`deux_points_dans_poche`) applied to `projOfAff`, the image of `G`, and the pocket transported by
some `j` (`Sphere.nonempty_hemi_affineEquiv`); the `g` they give is the image of some `g ∈ G`,
acting the same way.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « une variété localement affine » (connected by definition: Ch. 1 Déf. 12, « Sur une variété $V$, convexe [lire « connexe »] ») | ⚠ weakened: `[ChartedSpace (Fin n → ℝ) V]`, `[HasGroupoid V (affGroupoid n)]`; Hausdorff and second countable never used (the printed form `CompactDansPocheAffinePrinted` carries them); connectedness unused in the Remark's first four assertions, `[PreconnectedSpace V]` for the fifth (Prop. 7 and its corollary) |
| Prop. 7′: `V` connexe | ⚠ weakened: `[PreconnectedSpace V]` (the empty `V` allowed) |
| « balayable pour un groupe $G$ d'automorphismes affins » (Ch. 1 Déf. 15, affine case) | ✓ carried: `G : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)`, `IsBalayableFor (GAR n) (Fin n → ℝ) V G` (strict) |
| « une poche $(P, \varphi, z)$ » (Déf. 1) | ✓ carried: `IsPocheAff P φ z` (strict) |
| Remark: « la structure localement projective de $V$ » (Ch. 1, Déf. 12, Remarque) | ✓ carried: `projOfAff` (strict; independent of the chart, `remarque_affine_vers_projective`), a locally projective structure (`HasGroupoid V (projGroupoid n)`, first conjunct) |
| Remark: « $G$ est un groupe d'automorphismes projectifs » | ✓ carried, and more: an injective group morphism `GXAut.affToProj`, each automorphism acting as itself on `V`; `V` sweepable for the image `G.map GXAut.affToProj` |
| Remark: « $j$ un homéomorphisme de $\R^n$ sur un hémisphère $\mathring{H}$ … compatible avec les structures affines » | ✓ carried: every `j : ℝⁿ ≃ᵃ[ℝ] H̊`, any open hemisphere `l ≠ 0` (an affine bijection is a homeomorphism, `isOpenEmbedding_coe_affineEquiv`), the reading of the strict Remark after Déf. 1′ |
| Remark: « La proposition 7 et son corollaire sont donc vrais aussi dans le cas affin » | ✓ carried with Prop. 7's « connexe », as Prop. 7′ prints it (`PreconnectedSpace V →`); see SCOPE |
| « $E$ un compact » | ⚠ weakened: `IsCompact E` |
| « $gE\subset P$ » | ✓ carried as `g • E ⊆ P` (Bourbaki's inclusion, as for Prop. 7) |
| « $gM\in P$; $gN\in P$ » | ✓ carried |
| the dimension | ✓ every `n`, `n = 0` included |

## SCOPE (disclosed)

* Nothing is left unproved: no `sorry`, no added hypothesis; both labels are marked.
* **« connexe » in the Remark's last sentence** (« La proposition 7 et son corollaire sont donc
  vrais aussi dans le cas affin », l.503–504). The Remark's hypotheses do not print « connexe », but
  its « variété localement affine » is connected by definition: Ch. 1 Déf. 12 (ch1 l.304–309)
  defines the structure « sur une variété $V$, convexe [lire « connexe »] ». Prop. 7 prints
  « connexe », and so does the statement the Remark announces (« on a l'énoncé : », Prop. 7′); the
  standing convention that a « variété » is connected (docs/CAMPAIGN.md) agrees, so the reading is
  settled by the text, not open. `cas_affin`
  proves the first two assertions with no connectedness and the third under `PreconnectedSpace V`.
  Without it the third fails, in every dimension `≥ 1`: the complement of a hyperplane is sweepable
  and has a pocket, and no automorphism moves a point of each side into it
  (`not_deuxPointsDansPocheAffineSansConnexe`). Not a finding: the paper prints the connected form.
* **Independent of OQ-45 and OQ-61.** Prop. 7 and its corollary, used here, hold in every dimension
  and use only « B ∈ P » of Prop. 6 (T-bz-c2-compact). Should OQ-61 (a) add a non-constant cote to
  Déf. 1, the hypothesis only strengthens, the theorems stand, and the half-space and
  hyperplane-complement witnesses still apply (`n ≥ 1`); the `ℝⁿ` witness with `z ≡ 0` would no
  longer qualify. OQ-61 (a) would change Déf. 1′ too, so `cas_affin`'s pocket conclusion would
  strengthen; it would still hold once `IsPocheAff.toPocheProj` is re-proved with the new field,
  which is immediate. In dimension `0` every affine function is constant, so Prop. 7′ would then
  be vacuous there.
* The projective structure is `projOfAff` (the charts `j₀ ∘ φ`); `GXAut.transport` gives the same
  embedding for the structure transported along any equivariant open embedding of models.
* Lemmas of general use proved here: `IsGXMorphism.transport`, `GXAut.transport`,
  `GXAut.ofOpens` (an element of the model's group preserving an open set `U` is an automorphism of
  `U`).
* The scan (p. 253, PDF p. 26) agrees with the transcription of l.493–512.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Pointwise

namespace Benzecri

universe u v w

/-! ### Morphisms and automorphisms along an equivariant open embedding of models -/

section Transport

variable {X : Type v} [TopologicalSpace X] {G : Type w} [Group G] [MulAction G X]
  {X' : Type*} [TopologicalSpace X'] [Nonempty X'] {G' : Type*} [Group G'] [MulAction G' X']
  {ι : X' → X} {M : Type u} [TopologicalSpace M] [ChartedSpace X' M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace X' N]

/-- **A `(G', X')`-morphism is a `(G, X)`-morphism of the transported structures**
(`transportChartedSpace`, charts `ι ∘ e`), for an open embedding `ι : X' → X` equivariant through
`φ : G' →* G`: read in the charts, `ι ∘ (g' • ·) = φ g' • ι`. -/
theorem IsGXMorphism.transport (hι : IsOpenEmbedding ι) (φ : G' →* G)
    (hφ : ∀ (g : G') (p : X'), ι (g • p) = φ g • ι p) {f : M → N}
    (hf : IsGXMorphism G' X' f) :
    @IsGXMorphism G X _ _ _ M _ N _ (transportChartedSpace hι M) (transportChartedSpace hι N)
      f := by
  letI := transportChartedSpace hι M
  letI := transportChartedSpace hι N
  refine ⟨hf.continuous, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hf.exists_smul_eq x
  refine ⟨φ g, ?_⟩
  filter_upwards [hg] with y hy
  rw [transport_chartAt, transport_chartAt]
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, hy, hφ]

/-- **The automorphisms of a `(G', X')`-manifold are automorphisms of the transported
`(G, X)`-structure**: the same homeomorphism, as a group morphism. -/
def GXAut.transport (hι : IsOpenEmbedding ι) (φ : G' →* G)
    (hφ : ∀ (g : G') (p : X'), ι (g • p) = φ g • ι p) :
    GXAut G' X' M →* @GXAut G X _ _ _ M _ (transportChartedSpace hι M) where
  toFun f := show @gxAutSubgroup G X _ _ _ M _ (transportChartedSpace hι M) from
    ⟨f.toHomeomorph, f.isGXMorphism.transport hι φ hφ, f.isGXMorphism_symm.transport hι φ hφ⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The transported automorphism is the same homeomorphism. -/
theorem GXAut.transport_toHomeomorph (hι : IsOpenEmbedding ι) (φ : G' →* G)
    (hφ : ∀ (g : G') (p : X'), ι (g • p) = φ g • ι p) (f : GXAut G' X' M) :
    @GXAut.toHomeomorph G X _ _ _ M _ (transportChartedSpace hι M) (GXAut.transport hι φ hφ f) =
      f.toHomeomorph :=
  rfl

end Transport

/-! ### Affine automorphisms are projective automorphisms of the canonical projective structure -/

section AffToProj

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  {W : Type*} [TopologicalSpace W] [ChartedSpace (Fin n → ℝ) W]

/-- **An affine morphism is a projective morphism** of the canonical projective structures
(`projOfAff`, Ch. 1, Déf. 12, Remarque): `j₀ ∘ a = affToGS a • j₀` (`hemiChart_apply_eq_smul`). -/
theorem IsGXMorphism.affToProj {f : V → W} (hf : IsGXMorphism (GAR n) (Fin n → ℝ) f) :
    @IsGXMorphism (GSR n) (S n) _ _ _ V _ W _ (projOfAff n V) (projOfAff n W) f :=
  hf.transport Sphere.isOpenEmbedding_hemiChart Sphere.affToGS
    fun g y => Sphere.hemiChart_apply_eq_smul g y

/-- **« Pour la structure localement projective de $V$, $G$ est un groupe d'automorphismes
projectifs »**: the group of affine automorphisms of `V` embeds in the group of projective
automorphisms of the canonical projective structure, each automorphism going to itself
(`GXAut.affToProj_smul`, `GXAut.affToProj_injective`). -/
def GXAut.affToProj :
    GXAut (GAR n) (Fin n → ℝ) V →* @GXAut (GSR n) (S n) _ _ _ V _ (projOfAff n V) :=
  GXAut.transport Sphere.isOpenEmbedding_hemiChart Sphere.affToGS
    fun g y => Sphere.hemiChart_apply_eq_smul g y

section Local

attribute [local instance] projOfAff

/-- An affine automorphism acts on `V` as its image, the projective automorphism. -/
theorem GXAut.affToProj_smul (g : GXAut (GAR n) (Fin n → ℝ) V) (x : V) :
    GXAut.affToProj g • x = g • x :=
  rfl

/-- The embedding of the affine automorphisms into the projective ones is injective. -/
theorem GXAut.affToProj_injective :
    Function.Injective (GXAut.affToProj (n := n) (V := V)) := fun f g h =>
  FaithfulSMul.eq_of_smul_eq_smul fun x : V => by
    have := congrArg (fun k : GXAut (GSR n) (S n) V => k • x) h
    simpa only [GXAut.affToProj_smul] using this

/-- **Sweepability carries over**: if `V` is sweepable for a group `G` of affine automorphisms, it
is sweepable for `G` seen as a group of projective automorphisms, with the same compact generating
domain. -/
theorem IsBalayableFor.affToProj {G : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)}
    (hG : IsBalayableFor (GAR n) (Fin n → ℝ) V G) :
    IsBalayableFor (GSR n) (S n) V (G.map GXAut.affToProj) := by
  obtain ⟨K, hK, hU⟩ := hG
  refine ⟨K, hK, eq_univ_of_forall fun x => ?_⟩
  obtain ⟨g, hg, hx⟩ := mem_iUnion₂.1 (hU ▸ mem_univ x)
  exact mem_iUnion₂.2 ⟨GXAut.affToProj g, Subgroup.mem_map_of_mem _ hg, hx⟩

end Local

end AffToProj

/-! ### Prop. 7′ -/

section Prop7Prime

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  [HasGroupoid V (affGroupoid n)]

/-- **Prop. 7′, first assertion** (`bzprop:c2s2p7prime_compact_dans_poche_affine`), every
dimension: in a connected locally affine `V`, sweepable for a group `G` of affine automorphisms,
with a pocket `(P, φ, z)`, some `g ∈ G` maps a given compact set `E` into `P`. -/
theorem compact_dans_poche_affine [PreconnectedSpace V]
    {G : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)} (hG : IsBalayableFor (GAR n) (Fin n → ℝ) V G)
    {P : Set V} {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}
    (hP : IsPocheAff P φ z) {E : Set V} (hE : IsCompact E) : ∃ g ∈ G, g • E ⊆ P := by
  letI := projOfAff n V
  haveI := hasGroupoid_projOfAff (n := n) (V := V)
  obtain ⟨j⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm n)
    (Module.finrank_fin_fun ℝ)
  obtain ⟨_, hg', hgE⟩ := compact_dans_poche hG.affToProj (hP.toPocheProj j.symm) hE
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hg'
  exact ⟨g, hg, hgE⟩

/-- **Prop. 7′, second assertion** (`bzprop:c2s2p7prime_compact_dans_poche_affine`), every
dimension: some `g ∈ G` maps two given points into `P`. -/
theorem deux_points_dans_poche_affine [PreconnectedSpace V]
    {G : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)} (hG : IsBalayableFor (GAR n) (Fin n → ℝ) V G)
    {P : Set V} {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}
    (hP : IsPocheAff P φ z) (M N : V) : ∃ g ∈ G, g • M ∈ P ∧ g • N ∈ P := by
  obtain ⟨g, hg, hgP⟩ := compact_dans_poche_affine hG hP
    (isCompact_singleton.insert M : IsCompact {M, N})
  exact ⟨g, hg, hgP (smul_mem_smul_set (mem_insert M {N})),
    hgP (smul_mem_smul_set (mem_insert_of_mem M rfl))⟩

end Prop7Prime

/-! ### The Remark -/

section Remarque

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  [HasGroupoid V (affGroupoid n)]

attribute [local instance] projOfAff

/-- **The Remark before Prop. 7′** (`bzrem:c2s2r1_cas_affin`), every dimension. Let `V` be a
locally affine manifold, sweepable for a group `G` of affine automorphisms, with a pocket
`(P, φ, z)`, and `j : ℝⁿ ≃ H̊` an affine isomorphism onto any open hemisphere. For the canonical
locally projective structure of `V` (`projOfAff`, a locally projective structure):
(1) `G` is a group of projective automorphisms — the affine automorphisms embed injectively in the
projective ones, acting the same way — and `V` is sweepable for it; (2) `(P, H̊, j ∘ φ, z ∘ j⁻¹)`
is a pocket; (3) hence, `V` connected, Prop. 7 and its corollary hold for `G` and `(P, φ, z)`. -/
theorem cas_affin {G : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)}
    (hG : IsBalayableFor (GAR n) (Fin n → ℝ) V G) {P : Set V}
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ} (hP : IsPocheAff P φ z)
    {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    (j : (Fin n → ℝ) ≃ᵃ[ℝ] Sphere.openHemisphere l) :
    HasGroupoid V (projGroupoid n) ∧
    (Function.Injective (GXAut.affToProj (n := n) (V := V)) ∧
      ∀ (g : GXAut (GAR n) (Fin n → ℝ) V) (x : V), GXAut.affToProj g • x = g • x) ∧
    IsBalayableFor (GSR n) (S n) V (G.map GXAut.affToProj) ∧
    IsPocheProj P l
      (φ.trans ((isOpenEmbedding_coe_affineEquiv j).toOpenPartialHomeomorph _))
      (z.comp j.symm.toAffineMap) ∧
    (PreconnectedSpace V →
      (∀ E : Set V, IsCompact E → ∃ g ∈ G, g • E ⊆ P) ∧
        ∀ M N : V, ∃ g ∈ G, g • M ∈ P ∧ g • N ∈ P) :=
  ⟨hasGroupoid_projOfAff, ⟨GXAut.affToProj_injective, GXAut.affToProj_smul⟩, hG.affToProj,
    hP.toPocheProj j,
    fun _ => ⟨fun _ hE => compact_dans_poche_affine hG hP hE,
      deux_points_dans_poche_affine hG hP⟩⟩

end Remarque

/-! ### The printed statement of Prop. 7′ -/

/-- **Prop. 7′ as printed**, both assertions, over the locally affine `n`-manifolds of the paper
(Hausdorff, connected, second countable; `V : Type`): for every group `G` of affine automorphisms
for which `V` is sweepable and every pocket `(P, φ, z)`, every compact `E` is mapped into `P` by
some `g ∈ G`, and so is every pair of points. -/
def CompactDansPocheAffinePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V]
    (G : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)), IsBalayableFor (GAR n) (Fin n → ℝ) V G →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z →
        (∀ E : Set V, IsCompact E → ∃ g ∈ G, g • E ⊆ P) ∧
          ∀ M N : V, ∃ g ∈ G, g • M ∈ P ∧ g • N ∈ P

/-- **Prop. 7′ holds as printed in every dimension**, `n = 0` included. -/
theorem compactDansPocheAffinePrinted (n : ℕ) : CompactDansPocheAffinePrinted n :=
  fun _ _ _ _ _ _ _ _ hG _ _ _ hP =>
    ⟨fun _ hE => compact_dans_poche_affine hG hP hE, deux_points_dans_poche_affine hG hP⟩

/-! ### Non-vacuity -/

section OpensAut

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X]

/-- **An element of the model's group preserving an open set `U` of the model is an automorphism
of `U`** (`U` with Mathlib's charted space on an open subset): its restriction. -/
def GXAut.ofOpens (U : TopologicalSpace.Opens X) (g : G) (hg : ∀ x, g • x ∈ U ↔ x ∈ U) :
    GXAut G X U :=
  GXAut.ofBijective (f := fun x : U => (⟨g • (x : X), (hg x).2 x.2⟩ : U))
    ⟨((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _,
      fun _ => ⟨g, Eventually.of_forall fun _ => rfl⟩⟩
    ⟨fun _ _ h => Subtype.ext (MulAction.injective g (congrArg Subtype.val h)), fun y =>
      ⟨⟨g⁻¹ • (y : X), (hg _).1 (by rw [smul_inv_smul]; exact y.2)⟩,
        Subtype.ext (smul_inv_smul g _)⟩⟩

theorem GXAut.ofOpens_smul (U : TopologicalSpace.Opens X) (g : G) (hg : ∀ x, g • x ∈ U ↔ x ∈ U)
    (x : U) : ((GXAut.ofOpens U g hg • x : U) : X) = g • (x : X) :=
  rfl

end OpensAut

section Model

variable (n : ℕ)

/-- The translations of `ℝⁿ`, a subgroup of its affine automorphisms. -/
def translationSubgroup : Subgroup (GXAut (GAR n) (Fin n → ℝ) (Fin n → ℝ)) :=
  Subgroup.closure (range translationAut)

/-- `ℝⁿ` is sweepable for its translations, from the compact `{0}`. -/
theorem isBalayableFor_translationSubgroup :
    IsBalayableFor (GAR n) (Fin n → ℝ) (Fin n → ℝ) (translationSubgroup n) :=
  ⟨{0}, isCompact_singleton, eq_univ_of_forall fun y => mem_iUnion₂.2
    ⟨translationAut y, Subgroup.subset_closure (mem_range_self y),
      by rw [smul_set_singleton, translationAut_smul, add_zero]; rfl⟩⟩

/-- **Non-vacuity of the Remark and of Prop. 7′ in every dimension** (`n = 0` included): `ℝⁿ`
(Hausdorff, connected, second countable, locally affine), sweepable for its translations, with the
pocket `(ℝⁿ, id, 0)` (`isPocheAff_model`). -/
theorem compactDansPocheAffine_hypotheses_model :
    ConnectedSpace (Fin n → ℝ) ∧ T2Space (Fin n → ℝ) ∧ SecondCountableTopology (Fin n → ℝ) ∧
      IsBalayableFor (GAR n) (Fin n → ℝ) (Fin n → ℝ) (translationSubgroup n) ∧
      IsPocheAff (univ : Set (Fin n → ℝ)) (OpenPartialHomeomorph.refl _) 0 :=
  ⟨inferInstance, inferInstance, inferInstance, isBalayableFor_translationSubgroup n,
    isPocheAff_model n⟩

end Model

section DemiEspace

variable (n : ℕ)

/-- The open half-space `{x | x₀ > 0}` of `ℝⁿ⁺¹`, an open set of the model, hence a locally affine
`(n + 1)`-manifold (Mathlib's `TopologicalSpace.Opens.instChartedSpace` and `instHasGroupoid`). -/
def demiEspaceOuvert : TopologicalSpace.Opens (Fin (n + 1) → ℝ) :=
  ⟨{x | 0 < x 0}, isOpen_lt continuous_const (continuous_apply 0)⟩

theorem mem_demiEspaceOuvert {x : Fin (n + 1) → ℝ} : x ∈ demiEspaceOuvert n ↔ 0 < x 0 :=
  Iff.rfl

/-- The half-space is connected (convex and nonempty). -/
instance connectedSpace_demiEspaceOuvert : ConnectedSpace (demiEspaceOuvert n) :=
  isConnected_iff_connectedSpace.1
    ⟨⟨fun _ => 1, show (0 : ℝ) < 1 from one_pos⟩,
      ((convex_Ioi (0 : ℝ)).linear_preimage
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0)).isPreconnected⟩

/-- The inclusion of the half-space in `ℝⁿ⁺¹` is a developing map. -/
theorem isDeveloping_val_demiEspaceOuvert :
    IsDeveloping (GAR (n + 1)) (Subtype.val : demiEspaceOuvert n → Fin (n + 1) → ℝ) := fun x =>
  ⟨chartAt (Fin (n + 1) → ℝ) x, (gxGroupoid _ _).chart_mem_maximalAtlas x, mem_chart_source _ x,
    rfl⟩

/-- The affine map `x ↦ (y - y₀ 𝟙) + y₀ x`, `y₀ ≠ 0`: it maps `𝟙` to `y`; for `y₀ > 0` it
preserves the half-space. -/
def demiEspaceAff (y : Fin (n + 1) → ℝ) (hy : y 0 ≠ 0) : GAR (n + 1) :=
  (LinearEquiv.smulOfNeZero ℝ (Fin (n + 1) → ℝ) (y 0) hy).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (Fin (n + 1) → ℝ) (y - y 0 • fun _ => 1))

theorem demiEspaceAff_apply (y : Fin (n + 1) → ℝ) (hy : y 0 ≠ 0) (x : Fin (n + 1) → ℝ) :
    demiEspaceAff n y hy • x = (y - y 0 • fun _ => 1) + y 0 • x :=
  rfl

theorem demiEspaceAff_apply_one (y : Fin (n + 1) → ℝ) (hy : y 0 ≠ 0) :
    demiEspaceAff n y hy • (fun _ => 1 : Fin (n + 1) → ℝ) = y := by
  rw [demiEspaceAff_apply, sub_add_cancel]

theorem demiEspaceAff_mem_iff (y : Fin (n + 1) → ℝ) (hy : 0 < y 0) (x : Fin (n + 1) → ℝ) :
    demiEspaceAff n y hy.ne' • x ∈ demiEspaceOuvert n ↔ x ∈ demiEspaceOuvert n := by
  rw [mem_demiEspaceOuvert, mem_demiEspaceOuvert, demiEspaceAff_apply]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, sub_self, zero_add]
  exact mul_pos_iff_of_pos_left hy

/-- **The half-space is homogeneous, hence sweepable** (from the compact `{𝟙}`), for its affine
automorphisms. -/
theorem isBalayable_demiEspaceOuvert :
    IsBalayable (GAR (n + 1)) (Fin (n + 1) → ℝ) (demiEspaceOuvert n) := by
  refine ⟨{⟨fun _ => 1, show (0 : ℝ) < 1 from one_pos⟩}, isCompact_singleton,
    eq_univ_of_forall fun y => mem_iUnion₂.2 ⟨GXAut.ofOpens _ (demiEspaceAff n y y.2.ne')
      (demiEspaceAff_mem_iff n y y.2), Subgroup.mem_top _, ?_⟩⟩
  rw [smul_set_singleton]
  exact Subtype.ext (demiEspaceAff_apply_one n y _).symm

/-- **A pocket with a non-constant cote in the half-space**: `P = {0 < x₀ < 1}`, `φ` the
inclusion, `z = x₀` (through the affine example, `exemple_poche_affine`). -/
theorem exists_isPocheAff_demiEspace :
    ∃ φ : OpenPartialHomeomorph (demiEspaceOuvert n) (Fin (n + 1) → ℝ),
      IsPocheAff {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} φ
        (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧
      EqOn φ Subtype.val {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ∧
      φ '' {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} =
        {x | 0 < x 0 ∧ x 0 < 1} := by
  set z : (Fin (n + 1) → ℝ) →ᵃ[ℝ] ℝ :=
    (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap with hz
  let x₀ : demiEspaceOuvert n := ⟨fun _ => 1 / 2, show (0 : ℝ) < 1 / 2 by norm_num⟩
  set U := (Subtype.val : demiEspaceOuvert n → Fin (n + 1) → ℝ) ⁻¹' {y | z y < 1} with hU
  have himgU : (Subtype.val '' U : Set (Fin (n + 1) → ℝ)) = {x | 0 < x 0 ∧ x 0 < 1} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1⟩, h2, rfl⟩
  have hC : Convex ℝ {x : Fin (n + 1) → ℝ | 0 < x 0 ∧ x 0 < 1} :=
    (convex_Ioo (0 : ℝ) 1).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0)
  have hUconn : IsPreconnected U := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    convert hC.isPreconnected using 1
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1⟩, h2, rfl⟩
  have hx₀ : z (x₀ : Fin (n + 1) → ℝ) < 1 := show (1 / 2 : ℝ) < 1 by norm_num
  have hP : connectedComponentIn U x₀ = U := hUconn.connectedComponentIn hx₀
  have hinf : IsGLB (z '' (Subtype.val '' connectedComponentIn U x₀)) 0 := by
    rw [hP, himgU]
    have : z '' {x : Fin (n + 1) → ℝ | 0 < x 0 ∧ x 0 < 1} = Ioo 0 1 := by
      ext t
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro ht
        exact ⟨fun _ => t, ht, rfl⟩
    rw [this]
    exact isGLB_Ioo zero_lt_one
  obtain ⟨φ, hφeq, hφ⟩ := exemple_poche_affine (isDeveloping_val_demiEspaceOuvert n) z hx₀ hinf
    Subtype.val_injective.injOn
  have hφimg : φ '' connectedComponentIn U x₀ = {x | 0 < x 0 ∧ x 0 < 1} := by
    rw [image_congr hφeq, hP, himgU]
  rw [hP] at hφ hφeq hφimg
  exact ⟨φ, hφ, hφeq, hφimg⟩

/-- **Non-vacuity of the Remark and of Prop. 7′ with a non-constant cote, in every dimension
`n + 1 ≥ 1`**: the open half-space `{x₀ > 0}` of `ℝⁿ⁺¹` (Hausdorff, connected, second countable,
locally affine) is sweepable for its affine automorphisms and has the pocket `({0 < x₀ < 1}, id,
x₀)`, whose cote is not constant. -/
theorem compactDansPocheAffine_hypotheses_demiEspace :
    ConnectedSpace (demiEspaceOuvert n) ∧ T2Space (demiEspaceOuvert n) ∧
      SecondCountableTopology (demiEspaceOuvert n) ∧
      IsBalayable (GAR (n + 1)) (Fin (n + 1) → ℝ) (demiEspaceOuvert n) ∧
      ∃ φ : OpenPartialHomeomorph (demiEspaceOuvert n) (Fin (n + 1) → ℝ),
        IsPocheAff {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} φ
          (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧
        EqOn φ Subtype.val {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} ∧
        φ '' {x : demiEspaceOuvert n | (x : Fin (n + 1) → ℝ) 0 < 1} =
          {x | 0 < x 0 ∧ x 0 < 1} :=
  ⟨inferInstance, inferInstance, inferInstance, isBalayable_demiEspaceOuvert n,
    exists_isPocheAff_demiEspace n⟩

/-- Prop. 7′ applied to the half-space: every compact set of the half-space is moved into the
slab `{0 < x₀ < 1}` by an affine automorphism. -/
theorem exists_smul_subset_slab_demiEspace {E : Set (demiEspaceOuvert n)} (hE : IsCompact E) :
    ∃ g : GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (demiEspaceOuvert n),
      ∀ x ∈ E, ((g • x : demiEspaceOuvert n) : Fin (n + 1) → ℝ) 0 < 1 := by
  obtain ⟨φ, hP, -, -⟩ := exists_isPocheAff_demiEspace n
  obtain ⟨g, -, hg⟩ := (compactDansPocheAffinePrinted (n + 1) (demiEspaceOuvert n) ⊤
    (isBalayable_demiEspaceOuvert n) _ φ _ hP).1 E hE
  exact ⟨g, fun x hx => hg (smul_mem_smul_set hx)⟩

end DemiEspace

/-! ### « connexe » cannot be dropped from the Remark's last sentence -/

section Disconnected

variable (n : ℕ)

/-- The complement of the hyperplane `{x₀ = 0}` in `ℝⁿ⁺¹` (two open half-spaces): a locally affine
`(n + 1)`-manifold, Hausdorff and second countable, not connected. -/
def complHyperplan : TopologicalSpace.Opens (Fin (n + 1) → ℝ) :=
  ⟨{x | x 0 ≠ 0}, isOpen_ne_fun (continuous_apply 0) continuous_const⟩

theorem mem_complHyperplan {x : Fin (n + 1) → ℝ} : x ∈ complHyperplan n ↔ x 0 ≠ 0 :=
  Iff.rfl

theorem demiEspaceAff_mem_complHyperplan_iff (y : Fin (n + 1) → ℝ) (hy : y 0 ≠ 0)
    (x : Fin (n + 1) → ℝ) :
    demiEspaceAff n y hy • x ∈ complHyperplan n ↔ x ∈ complHyperplan n := by
  rw [mem_complHyperplan, mem_complHyperplan, demiEspaceAff_apply]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, sub_self, zero_add]
  exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero hy h⟩

/-- The complement of the hyperplane is homogeneous, hence sweepable from `{𝟙}`. -/
theorem isBalayable_complHyperplan :
    IsBalayable (GAR (n + 1)) (Fin (n + 1) → ℝ) (complHyperplan n) := by
  refine ⟨{⟨fun _ => 1, show (1 : ℝ) ≠ 0 from one_ne_zero⟩}, isCompact_singleton,
    eq_univ_of_forall fun y => mem_iUnion₂.2 ⟨GXAut.ofOpens _ (demiEspaceAff n y y.2)
      (demiEspaceAff_mem_complHyperplan_iff n y y.2), Subgroup.mem_top _, ?_⟩⟩
  rw [smul_set_singleton]
  exact Subtype.ext (demiEspaceAff_apply_one n y _).symm

/-- The inclusion is a developing map. -/
theorem isDeveloping_val_complHyperplan :
    IsDeveloping (GAR (n + 1)) (Subtype.val : complHyperplan n → Fin (n + 1) → ℝ) := fun x =>
  ⟨chartAt (Fin (n + 1) → ℝ) x, (gxGroupoid _ _).chart_mem_maximalAtlas x, mem_chart_source _ x,
    rfl⟩

/-- The positive side `{x₀ > 0}` is clopen in the complement of the hyperplane. -/
theorem isClopen_pos_complHyperplan :
    IsClopen {x : complHyperplan n | 0 < (x : Fin (n + 1) → ℝ) 0} := by
  constructor
  · rw [← isOpen_compl_iff]
    have : {x : complHyperplan n | 0 < (x : Fin (n + 1) → ℝ) 0}ᶜ =
        {x : complHyperplan n | (x : Fin (n + 1) → ℝ) 0 < 0} := by
      ext x
      simp only [mem_compl_iff, mem_setOf_eq, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h x.2, fun h => h.le⟩
    rw [this]
    exact isOpen_lt ((continuous_apply 0).comp continuous_subtype_val) continuous_const
  · exact isOpen_lt continuous_const ((continuous_apply 0).comp continuous_subtype_val)

/-- A convex set of `ℝⁿ⁺¹` off the hyperplane is preconnected in its complement. -/
theorem isPreconnected_preimage_val_complHyperplan {C : Set (Fin (n + 1) → ℝ)}
    (hC : Convex ℝ C) (hCU : C ⊆ complHyperplan n) :
    IsPreconnected ((Subtype.val : complHyperplan n → Fin (n + 1) → ℝ) ⁻¹' C) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
  convert hC.isPreconnected using 1
  ext y
  exact ⟨fun ⟨_, hx, hxy⟩ => hxy ▸ hx, fun hy => ⟨⟨y, hCU hy⟩, hy, rfl⟩⟩

/-- **A pocket with a non-constant cote in the complement of the hyperplane**: `{0 < x₀ < 1}`, the
inclusion, `z = x₀` (`exemple_poche_affine`). -/
theorem exists_isPocheAff_complHyperplan :
    ∃ φ : OpenPartialHomeomorph (complHyperplan n) (Fin (n + 1) → ℝ),
      IsPocheAff {x : complHyperplan n | 0 < (x : Fin (n + 1) → ℝ) 0 ∧
        (x : Fin (n + 1) → ℝ) 0 < 1} φ
        (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap := by
  set z : (Fin (n + 1) → ℝ) →ᵃ[ℝ] ℝ :=
    (LinearMap.proj 0 : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ).toAffineMap with hz
  let x₀ : complHyperplan n := ⟨fun _ => 1 / 2, show (1 / 2 : ℝ) ≠ 0 by norm_num⟩
  set A := (Subtype.val : complHyperplan n → Fin (n + 1) → ℝ) ⁻¹' {y | z y < 1} with hA
  set B := {x : complHyperplan n | 0 < (x : Fin (n + 1) → ℝ) 0 ∧ (x : Fin (n + 1) → ℝ) 0 < 1}
    with hB
  have hC : Convex ℝ {x : Fin (n + 1) → ℝ | 0 < x 0 ∧ x 0 < 1} :=
    (convex_Ioo (0 : ℝ) 1).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0)
  have hBpre : IsPreconnected B :=
    isPreconnected_preimage_val_complHyperplan n hC fun x hx => hx.1.ne'
  have hx₀A : x₀ ∈ A := show (1 / 2 : ℝ) < 1 by norm_num
  have hx₀B : x₀ ∈ B := ⟨show (0 : ℝ) < 1 / 2 by norm_num, show (1 / 2 : ℝ) < 1 by norm_num⟩
  have hcomp : connectedComponentIn A x₀ = B := by
    refine Subset.antisymm (fun x hx => ⟨?_, connectedComponentIn_subset A x₀ hx⟩)
      (hBpre.subset_connectedComponentIn hx₀B fun x hx => hx.2)
    exact isPreconnected_connectedComponentIn.subset_isClopen (isClopen_pos_complHyperplan n)
      ⟨x₀, mem_connectedComponentIn hx₀A, hx₀B.1⟩ hx
  have hinf : IsGLB (z '' (Subtype.val '' connectedComponentIn A x₀)) 0 := by
    rw [hcomp]
    have : z '' (Subtype.val '' B) = Ioo 0 1 := by
      ext t
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact hy
      · intro ht
        exact ⟨fun _ => t, ⟨⟨fun _ => t, ht.1.ne'⟩, ht, rfl⟩, rfl⟩
    rw [this]
    exact isGLB_Ioo zero_lt_one
  obtain ⟨φ, -, hφ⟩ := exemple_poche_affine (isDeveloping_val_complHyperplan n) z hx₀A hinf
    Subtype.val_injective.injOn
  rw [hcomp] at hφ
  exact ⟨φ, hφ⟩

/-- **The Remark's last sentence read without « connexe »** (its own hypotheses: a locally affine
`V`, sweepable for a group `G` of affine automorphisms, with a pocket): every two points are moved
into the pocket by one `g ∈ G`. -/
def DeuxPointsDansPocheAffineSansConnexe (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [SecondCountableTopology V]
    (G : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)), IsBalayableFor (GAR n) (Fin n → ℝ) V G →
    ∀ (P : Set V) (φ : OpenPartialHomeomorph V (Fin n → ℝ)) (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      IsPocheAff P φ z → ∀ M N : V, ∃ g ∈ G, g • M ∈ P ∧ g • N ∈ P

/-- **Without « connexe » the last sentence of the Remark fails, in every dimension `n + 1 ≥ 1`**:
the complement of the hyperplane `{x₀ = 0}`, sweepable for its affine automorphisms, with the pocket
`{0 < x₀ < 1}` (non-constant cote); `M = ½𝟙`, `N = −½𝟙` lie on the two sides, and an automorphism,
a homeomorphism, maps the side of `N` (connected) into one side only. So the reading of `cas_affin`
(Prop. 7's « connexe » kept, as Prop. 7′ prints it) is needed. -/
theorem not_deuxPointsDansPocheAffineSansConnexe :
    ¬ DeuxPointsDansPocheAffineSansConnexe (n + 1) := by
  intro h
  obtain ⟨φ, hP⟩ := exists_isPocheAff_complHyperplan n
  let M : complHyperplan n := ⟨fun _ => 1 / 2, show (1 / 2 : ℝ) ≠ 0 by norm_num⟩
  let N : complHyperplan n := ⟨fun _ => -1 / 2, show (-1 / 2 : ℝ) ≠ 0 by norm_num⟩
  obtain ⟨g, -, hgM, hgN⟩ := h (complHyperplan n) ⊤ (isBalayable_complHyperplan n) _ φ _ hP M N
  set S := {x : complHyperplan n | 0 < (x : Fin (n + 1) → ℝ) 0} with hS
  set S' := {x : complHyperplan n | (x : Fin (n + 1) → ℝ) 0 < 0} with hS'
  have hT : IsClopen ((fun x => g • x) ⁻¹' S) :=
    (isClopen_pos_complHyperplan n).preimage (continuous_const_smul g)
  have hSpre : IsPreconnected S :=
    isPreconnected_preimage_val_complHyperplan n
      ((convex_Ioi (0 : ℝ)).linear_preimage
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0))
      fun x hx => ne_of_gt hx
  have hS'pre : IsPreconnected S' :=
    isPreconnected_preimage_val_complHyperplan n
      ((convex_Iio (0 : ℝ)).linear_preimage
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0))
      fun x hx => ne_of_lt hx
  have hST : S ⊆ (fun x => g • x) ⁻¹' S :=
    hSpre.subset_isClopen hT ⟨M, show (0 : ℝ) < 1 / 2 by norm_num, hgM.1⟩
  have hS'T : S' ⊆ (fun x => g • x) ⁻¹' S :=
    hS'pre.subset_isClopen hT ⟨N, show (-1 / 2 : ℝ) < 0 by norm_num, hgN.1⟩
  have hall : ∀ x : complHyperplan n, g • x ∈ S := fun x => by
    rcases lt_or_gt_of_ne x.2 with hx | hx
    · exact hS'T hx
    · exact hST hx
  have hN := hall (g⁻¹ • N)
  rw [smul_inv_smul] at hN
  exact absurd hN (show ¬ (0 : ℝ) < -1 / 2 by norm_num)

end Disconnected

end Benzecri
