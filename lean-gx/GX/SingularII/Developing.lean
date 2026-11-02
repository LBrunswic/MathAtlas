import GX.SingularII.Unloopable
import GX.Branched.Galois
import GX.Structure.Developing

/-!
# Singular `(G,X)`-manifolds (II): developing maps, holonomy, the singular developing theorem

Package WP-27h; the author's rulings DEC-66 (c) and DEC-67 (b)(c) applied by WP-35d. `papers/gx`,
`RamcovGX.tex:1706–1825`, §2.5.1 "Developing maps" (`M`, `N` connected singular
`(G,X)`-manifolds, l.1712; `(G,X)` analytical with `X` locally unloopable, l.1660; Hausdorff,
locally path-connected, first countable, §3's standing assumption l.810, which covers §2.5 by
DEC-66 (a)), on the classical developing theorem `GX.Structure.Developing` (DEC-23).

* **`def:developing_map`** — `RamcovGX.tex:1726`: `GX.IsDevelopingMapOf` (an a.e. morphism
  `N → X`, `N` with `p^*B`; `GX.isDevelopingMapOf_iff` for any maximal atlas making `p` a
  morphism), `GX.AdmitsDevelopingMap`; the third sentence justified by `GX.admitsDevelopingMap_iff`.
* **`lem:MtoXG`** — `RamcovGX.tex:1748`: `GX.aeMorphism_model_unique`.
* **`lem:holonomy`** — `RamcovGX.tex:1753` — under DEC-67 (b) (`Γ` acts on `M`, the domain of
  `f`, for the printed "acting on `N`"): `GX.existsUnique_holonomy`; also
  `GX.existsUnique_holonomy_hom` (an action through `Γ →* Homeo(M)`) and
  `GX.existsUnique_holonomyOf` (for `Γ(N/M)`).
* **`def:quasi_galoisian_branched_covering_singular`** — `RamcovGX.tex:1761`: `GX.holonomyOf`,
  `GX.IsHolonomyOf`, `GX.holonomyOf_spec`, `GX.isHolonomyOf_iff`, `GX.isHolonomyOf_one_iff`.
* **`rem:developing_map_quasi_galoisian_covering`** — `RamcovGX.tex:1764`:
  `GX.IsHolonomyOf.mem_fixedPoints`, `GX.IsHolonomyOf.smul_eq_of_mem_deckStab`.
* **`rem:singular_manifold_holonomy_indeed`** — `RamcovGX.tex:1768` — under DEC-67 (c) (the
  restriction of `D` to the universal cover of `reg(M)` is a classical developing map of `reg(M)`,
  its holonomy the restriction of `ρ`) and DEC-66 (c) (`M` locally path-connected):
  `GX.singular_manifold_holonomy_indeed_of_isLocallyUnloopable` (the section's standing `X` locally
  unloopable), `GX.singular_manifold_holonomy_indeed` (only `reg(M)` semilocally simply
  connected), on `GX.regChartedSpace` (`reg(M)` as a `(G,X)`-manifold,
  `GX.hasGroupoid_regChartedSpace`).
* **`lem:quasi_galoisian_branched_covering_singular`** — `RamcovGX.tex:1771`:
  `GX.developing_pair_unique`.
* **`lem:descend_developing_map`** — `RamcovGX.tex:1780` — under DEC-66 (a)(c) (the base `N`
  locally path-connected, a base of a branched covering in §3's class): `GX.descend_developing_map`,
  `GX.eq_of_isHolonomyOf_one`.
* **`lem:morphism_singular_manifolds_branched`** — `RamcovGX.tex:1799`:
  `GX.morphism_singular_manifolds_branched`.
* **`prop:branched_devmap`** — `RamcovGX.tex:1807` — under DEC-66 (c) (`M` locally
  path-connected): **`GX.singular_developing_theorem`** (the section's standing hypothesis, `X`
  locally unloopable), `GX.singular_developing_theorem_of_slsc` (only the semilocal simple
  connectedness the proof uses), `GX.exists_developing_maxBranched_of_branchedCovering`
  ((ii) ⇒ (i)), on `GX.exists_developing_of_simplyConnected` (the classical developing theorem read
  in a singular manifold).

> A developing map $\D$ of $N\rightarrow M$ is any a.e. $(G,X)$-morphism $N \rightarrow X$.
> We say that $M$ admits a developing map if there exists a branched covering
> $\widehat M \rightarrow M$ possibly branched above $\sing(M)$ and a developing map of
> $\widehat M \rightarrow M$. (l.1726)
>
> Let $N\xrightarrow{f_1,f_2} X$ be a.e. $(G,X)$-morphisms, then there exists a unique
> $g\in G$ such that $f_1=gf_2$. (l.1748)
>
> Let $M$ be a singular $(G,X)$-manifold and $\Gamma$ be a group acting on $N$ by a.e.
> $(G,X)$-morphisms. For any a.e. $(G,X)$-morphism $M\xrightarrow{f} X$ there exists a unique
> morphism $\rho:\Gamma\rightarrow G$ such that $f$ is $\rho$-equivariant. (l.1753; read with
> $\Gamma$ acting on $M$, DEC-67 (b))
>
> A developing map $\D$ of a quasi-Galoisian covering $M\rightarrow N$ sends points to some fix
> point of their stabilizer : $\D(x) \in \fix(\rho(\Gamma_x))$. (l.1764)
>
> Let $M\xrightarrow{p} N$ be a quasi-Galoisian branched covering of singular
> $(G,X)$-manifolds. Then, the following are equivalent: (i) there exists an a.e.
> $(G,X)$-morphism $M\rightarrow X$ and the holonomy of $M\rightarrow N$ is trivial, (ii) there
> exists an a.e. $(G,X)$-morphism $N\rightarrow X$. (l.1780)
>
> Let $M$ be a singular $(G,X)$-manifold. The following are then equivalent: (i) there exists an
> a.e. $(G,X)$-morphism $\widetilde M\rightarrow X$, (ii) there exists a branched covering of
> $N\xrightarrow{p} M$ which admits a developing map. (l.1807)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(G,X)` analytical (l.341, DEC-39) | ✓ carried: `IsRigidAction`, `FaithfulSMul` (faithful only where uniqueness in `G` is asserted), `ContinuousConstSMul`, `X` T2 and locally connected; `X` connected never used |
| `X` locally unloopable (standing, l.1660) | ✓ carried in `singular_developing_theorem`, `singular_manifold_holonomy_indeed_of_isLocallyUnloopable`; ⚠ weakened elsewhere: not used (`…_of_slsc`, `singular_manifold_holonomy_indeed` ask only for the semilocal simple connectedness they use) |
| `M`, `N` connected (standing, l.1712) | ✓ carried where used (`lem:MtoXG`, `lem:holonomy`; the source of a branched covering is connected) |
| singular manifolds Hausdorff, second countable, locally connected | ⚠ weakened: T2, first countable, locally connected where used |
| §3's standing assumption (l.810: T2, locally path-connected, first countable) covers §2.5 and the bases of branched coverings (DEC-66 (a)) | ✓ carried where used |
| `prop:branched_devmap`, `rem:…holonomy_indeed`: `M` locally path-connected wherever `\widetilde M` is used (DEC-66 (c)) | ✓ carried (`prop:universality`) |
| `lem:descend_developing_map`: the base `N` locally path-connected (DEC-66 (a)(c), for `lem:dense_orbits`) | ✓ carried |
| "quasi-Galoisian" (l.1761, 1764, 1771) | ⚠ weakened: not used — every branched covering |
| `lem:holonomy`: `Γ` acting on `N` | ✓ read as acting on `M`, the domain of `f` (DEC-67 (b)) |
| `lem:morphism_singular_manifolds_branched`: singular manifolds | ⚠ weakened: a.e. atlases `B_M`, `B_N`, `M` locally connected |

## SCOPE (disclosed)

* **(a)** "A branched covering `N → M` of singular `(G,X)`-manifolds" gives `N` the structure of
  `prop:singular_manifold_branched_covering`, `p^*B = aePullback B p` (DEC-42: any maximal a.e.
  atlas making `p` a morphism is it, `isDevelopingMapOf_iff`). The model `X` carries its maximal
  atlas (`gxModelAtlas`). `\widetilde M` is `MaxBranchedCover (Sing M) y₀` with the corollary's
  structure (`cor:singular_manifold_skeletal_subset`); "`M` admits a developing map" quantifies over
  branched coverings in the class of `prop:universality` (Hausdorff, locally path-connected, first
  countable), in the universe of `M`; (ii) of `prop:branched_devmap` likewise, but
  `exists_developing_maxBranched_of_branchedCovering` holds in every universe.
* **(b)** The holonomy (`def:quasi_galoisian_branched_covering_singular`) is a homomorphism on
  `Deck p = Γ(N/M)`; `lem:holonomy` is proved for `[MulAction Γ M]` and for a homomorphism into
  the homeomorphisms; "the holonomy is trivial" (`lem:descend_developing_map`) is `ρ = 1`, which
  does not depend on the developing map (`developing_pair_unique`).
* **(c)** `prop:branched_devmap`, (ii) ⇒ (i), is not proved by the paper's route through
  `\widehat M'` and `lem:descend_developing_map`, but with the same objects: `D ∘ Φ` on
  `\widehat M = \widetilde M^{S ∪ sing M}` and `F ∘ Ψ` (`F` the classical developing map of the
  simply connected `\widetilde{reg M} ⊆ \widetilde M`, `Ψ : \widehat M → \widetilde M` by
  universality) agree up to `g` on the connected `\widehat M ∖ \widehat S`; `Ψ` being open, `D ∘ Φ`
  is constant on its fibres and descends along it.
* **(d)** `rem:singular_manifold_holonomy_indeed` is read (DEC-67 (c)) as: for a developing map `D` of
  `\widetilde M` with holonomy `ρ`, `D ∘ ι` (`ι : \widetilde{reg M} → \widetilde M`) is a
  developing map of the `(G,X)`-manifold `reg(M)` in the sense of `GX.developing_theorem`, and its
  classical holonomy is `γ ↦ ρ(γ̃)`, `γ̃` the extension of `γ` to `\widetilde M`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Structure.Developing`, `GX.Branched.Universality`, `GX.Singular.Atlas` and the scaffold's
`GX.SingularII.Unloopable`, `GX.Branched.Galois`.
-/
noncomputable section
open Set Filter Topology Function
open scoped GX
namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

universe u v w

section Defs

variable (G : Type*) (X : Type*) [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X]

/-- The model `X` as a `(G,X)`-manifold: its maximal atlas (chart the identity). -/
abbrev gxModelAtlas : Set (OpenPartialHomeomorph X X) := (gxGroupoid G X).maximalAtlas X

variable {X}
variable {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- **`def:developing_map`** (`RamcovGX.tex:1726`): a *developing map* of a branched covering
`p : N → M` of a space with an a.e. atlas `B` is an a.e. `(G,X)`-morphism `N → X`, `N` carrying
the structure `p^* B` making `p` an a.e. morphism (`prop:singular_manifold_branched_covering`). -/
def IsDevelopingMapOf (B : Set (OpenPartialHomeomorph M X)) (p : N → M) (D : N → X) : Prop :=
  IsAEMorphismOf G (aePullback G B p) (gxModelAtlas G X) D

variable {G} in
/-- The holonomy relation (`lem:holonomy`, `def:quasi_galoisian_branched_covering_singular`):
`D ∘ γ = ρ(γ) • D` for every automorphism `γ ∈ Γ(N/M)`. -/
def IsHolonomyOf (p : N → M) (D : N → X) (ρ : Deck p →* G) : Prop :=
  ∀ (γ : Deck p) (x : N), D ((γ : N ≃ₜ N) x) = ρ γ • D x

end Defs

/-! ### The model, and maps into it -/

section Model

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- The model is a singular `(G,X)`-manifold with empty singular locus. -/
theorem isMaximalAEAtlas_gxModelAtlas : IsMaximalAEAtlas G (gxModelAtlas G X) :=
  isMaximalAEAtlas_maximalAtlas (M := X)

omit [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] in
theorem support_gxModelAtlas : support (gxModelAtlas G X) = univ :=
  support_maximalAtlas (M := X)

omit [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] in
theorem refl_mem_gxModelAtlas : OpenPartialHomeomorph.refl X ∈ gxModelAtlas G X :=
  (gxGroupoid G X).id_mem_maximalAtlas

/-- A developing map is an a.e. morphism for **any** maximal a.e. atlas making `p` an a.e.
morphism (all equal `p^* B`, `lem:aepullback`, DEC-42). -/
theorem isDevelopingMapOf_iff {B : Set (OpenPartialHomeomorph M X)} {p : N → M}
    {A : Set (OpenPartialHomeomorph N X)} (hA : IsMaximalAEAtlas G A) (hp : IsAEMorphismOf G A B p)
    {D : N → X} : IsDevelopingMapOf G B p D ↔ IsAEMorphismOf G A (gxModelAtlas G X) D := by
  rw [IsDevelopingMapOf, ← eq_aePullback hA hp]

omit [T2Space X] in
/-- A map into the model which is, near every point of an open `U`, a translate of a chart of a
`(G,X)`-atlas `A`, induces a `(G,X)`-morphism on `U`. -/
theorem isRegularOn_model_of_eventually {A : Set (OpenPartialHomeomorph M X)} (hA : IsGXAtlas G A)
    {U : Set M} (hU : IsOpen U) (hUA : U ⊆ support A) {H : M → X}
    (h : ∀ x ∈ U, ∃ e ∈ A, x ∈ e.source ∧ ∃ g : G, ∀ᶠ y in 𝓝 x, H y = g • e y) :
    IsRegularOn G A (gxModelAtlas G X) H U := by
  refine IsRegularOn.of_exists hA (isGXAtlas_maximalAtlas (G := G) (M := X)) hU hUA
    (fun x _ => by rw [support_gxModelAtlas]; exact mem_univ _) ?_ fun x hx => ?_
  · intro x hx
    obtain ⟨e, -, hxe, g, hg⟩ := h x hx
    have hg' : (fun y => g • e y) =ᶠ[𝓝 x] H := hg.mono fun y hy => hy.symm
    exact (((e.continuousAt hxe).const_smul g).congr hg').continuousWithinAt
  · obtain ⟨e, he, hxe, g, hg⟩ := h x hx
    exact ⟨e, he, _, refl_mem_gxModelAtlas, hxe, mem_univ _, g,
      hg.mono fun y hy => by simpa using hy⟩

omit [T2Space X] in
/-- The same, the translates read through a map `f` inducing a `(G,X)`-morphism on `U`. -/
theorem isRegularOn_model_of_eventually_comp {A : Set (OpenPartialHomeomorph M X)}
    (hA : IsGXAtlas G A) {B : Set (OpenPartialHomeomorph N X)} {f : M → N} {U : Set M}
    (hf : IsRegularOn G A B f U) {H : M → X}
    (h : ∀ x ∈ U, ∃ c ∈ B, f x ∈ c.source ∧ ∃ g : G, ∀ᶠ y in 𝓝 x, H y = g • c (f y)) :
    IsRegularOn G A (gxModelAtlas G X) H U := by
  refine isRegularOn_model_of_eventually hA hf.isOpen hf.subset_support fun x hx => ?_
  obtain ⟨c, hc, hfxc, g, hg⟩ := h x hx
  obtain ⟨e, he, hxe⟩ := mem_support.1 (hf.subset_support hx)
  obtain ⟨a, ha⟩ := hf.exists_smul_eq x hx e he c hc hxe hfxc
  exact ⟨e, he, hxe, g * a, by filter_upwards [hg, ha] with y h1 h2; rw [h1, h2, mul_smul]⟩

omit [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] in
/-- A map inducing a `(G,X)`-morphism into the model is, near every point, a translate of any
chart at that point. -/
theorem IsRegularOn.eventually_eq_smul_model {A : Set (OpenPartialHomeomorph M X)} {H : M → X}
    {U : Set M} (hH : IsRegularOn G A (gxModelAtlas G X) H U) {x : M} (hx : x ∈ U)
    {e : OpenPartialHomeomorph M X} (he : e ∈ A) (hxe : x ∈ e.source) :
    ∃ g : G, ∀ᶠ y in 𝓝 x, H y = g • e y := by
  obtain ⟨g, hg⟩ := hH.exists_smul_eq x hx e he _ refl_mem_gxModelAtlas hxe (mem_univ _)
  exact ⟨g, hg.mono fun y hy => by simpa using hy⟩

omit [LocallyConnectedSpace X] [T2Space X] in
/-- An a.e. `(G,X)`-morphism into the model determines the translating element:
`g • D = h • D` forces `g = h` (the action analytical). -/
theorem IsAEMorphismOf.smul_injective_model [FaithfulSMul G X] [Nonempty M]
    {A : Set (OpenPartialHomeomorph M X)} {D : M → X}
    (hD : IsAEMorphismOf G A (gxModelAtlas G X) D) {g h : G} (heq : ∀ x, g • D x = h • D x) :
    g = h := by
  obtain ⟨U, -, hU, -, -, -, hr⟩ := hD.exists_isRegularOn
  obtain ⟨x, hx⟩ := hU.dense.nonempty
  obtain ⟨e, hxe, hDe⟩ := hr.isLocalHomeomorphOn x hx
  refine FaithfulSMul.eq_of_smul_eq_smul (IsRigidAction.smul_eq_of_eqOn
    (e.isOpen_image_of_subset_source (hU.isOpen.inter e.open_source) inter_subset_right)
    ⟨e x, x, ⟨hx, hxe⟩, rfl⟩ ?_)
  rintro _ ⟨y, -, rfl⟩
  have := heq y
  rw [hDe] at this
  exact this

/-- **`lem:MtoXG`** (`RamcovGX.tex:1748`; `N` connected, the section's standing hypothesis
l.1712): two a.e. `(G,X)`-morphisms `f₁ f₂ : N → X` differ by a unique `g ∈ G`, `f₁ = g f₂`.
The proof: on the portly, hence connected, intersection of their regular loci both are
developing maps, hence differ by one `g` there; `{f₁ = g f₂}` is closed and dense. -/
theorem aeMorphism_model_unique [FaithfulSMul G X] [ConnectedSpace M]
    {A : Set (OpenPartialHomeomorph M X)} {f₁ f₂ : M → X}
    (h₁ : IsAEMorphismOf G A (gxModelAtlas G X) f₁)
    (h₂ : IsAEMorphismOf G A (gxModelAtlas G X) f₂) :
    ∃! g : G, ∀ x, f₁ x = g • f₂ x := by
  obtain ⟨U₁, -, hU₁, -, -, -, r₁⟩ := h₁.exists_isRegularOn
  obtain ⟨U₂, -, hU₂, -, -, -, r₂⟩ := h₂.exists_isRegularOn
  have hR : IsPortly (U₁ ∩ U₂) := hU₁.inter hU₂
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isRegularOn hR.isConnected.isPreconnected
    (r₂.mono inter_subset_right hR.isOpen) (r₁.mono inter_subset_left hR.isOpen)
  have hcl : IsClosed {x | f₁ x = g • f₂ x} :=
    isClosed_eq h₁.continuous (h₂.continuous.const_smul g)
  have hall : ∀ x, f₁ x = g • f₂ x := fun x =>
    (hcl.closure_subset_iff.2 fun y hy => hg y hy) (hR.dense x)
  exact ⟨g, hall, fun g' hg' => h₂.smul_injective_model fun x => by rw [← hg' x, ← hall x]⟩

end Model

/-! ### Holonomy -/

section Holonomy

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X] {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- `lem:holonomy` for a group acting through a homomorphism into the homeomorphisms of `M`:
`f` is `ρ`-equivariant for a unique `ρ : Γ →* G`. -/
theorem existsUnique_holonomy_hom [ConnectedSpace M] [LocallyConnectedSpace M] {Γ : Type*}
    [Group Γ] (act : Γ →* (M ≃ₜ M)) {A : Set (OpenPartialHomeomorph M X)}
    (hΓ : ∀ γ, IsAEMorphismOf G A A (act γ)) {f : M → X}
    (hf : IsAEMorphismOf G A (gxModelAtlas G X) f) :
    ∃! ρ : Γ →* G, ∀ γ x, f (act γ x) = ρ γ • f x := by
  have hex : ∀ γ, ∃ g : G, ∀ x, f (act γ x) = g • f x := fun γ =>
    (aeMorphism_model_unique (hf.comp (hΓ γ)) hf).exists
  choose ρ hρ using hex
  refine ⟨{ toFun := ρ, map_one' := ?_, map_mul' := ?_ }, hρ, fun ρ' hρ' => ?_⟩
  · exact hf.smul_injective_model fun x => by rw [← hρ 1 x, map_one, one_smul]; rfl
  · intro γ δ
    exact hf.smul_injective_model fun x => by
      rw [← hρ (γ * δ) x, mul_smul, ← hρ δ x, ← hρ γ (act δ x), map_mul]; rfl
  · exact MonoidHom.ext fun γ => hf.smul_injective_model fun x => by
      rw [← hρ' γ x]; exact hρ γ x

/-- **`lem:holonomy`** (`RamcovGX.tex:1753`, with the printed "acting on `N`" read as acting on
`M`, the domain of `f`, DEC-67 (b); `M` connected, the section's standing hypothesis): if a group `Γ` acts on
a singular `(G,X)`-manifold by a.e. `(G,X)`-morphisms, every a.e. `(G,X)`-morphism `f : M → X` is
`ρ`-equivariant for a unique homomorphism `ρ : Γ → G`. The proof is the regular one
(`GX.developing_theorem`): `f ∘ γ` is another developing map, so `f ∘ γ = ρ(γ) f` for a unique
`ρ(γ)` (`lem:MtoXG`), and uniqueness makes `ρ` a homomorphism. -/
theorem existsUnique_holonomy [ConnectedSpace M] [LocallyConnectedSpace M] {Γ : Type*} [Group Γ]
    [MulAction Γ M] {A : Set (OpenPartialHomeomorph M X)}
    (hΓ : ∀ γ : Γ, IsAEMorphismOf G A A fun x => γ • x) {f : M → X}
    (hf : IsAEMorphismOf G A (gxModelAtlas G X) f) :
    ∃! ρ : Γ →* G, ∀ γ x, f (γ • x) = ρ γ • f x := by
  let act : Γ →* (M ≃ₜ M) :=
    { toFun := fun γ =>
        { toEquiv := MulAction.toPerm γ
          continuous_toFun := (hΓ γ).continuous
          continuous_invFun := (hΓ γ⁻¹).continuous }
      map_one' := by ext x; simp
      map_mul' := fun γ δ => by ext x; simp [mul_smul] }
  exact existsUnique_holonomy_hom act (fun γ => hΓ γ) hf

variable (G) in
/-- `lem:holonomy` for `Γ(N/M)`: a developing map of a branched covering is equivariant for a
unique homomorphism `Γ(N/M) → G` (the deck transformations are a.e. `(G,X)`-morphisms of `p^*B`,
`prop:singular_manifold_branched_covering`). -/
theorem existsUnique_holonomyOf {p : N → M} (hp : IsBranchedCovering p)
    {B : Set (OpenPartialHomeomorph M X)} (hB : IsAEAtlas G B) {D : N → X}
    (hD : IsDevelopingMapOf G B p D) : ∃! ρ : Deck p →* G, IsHolonomyOf p D ρ := by
  haveI := hp.connectedSpace_source
  haveI := hp.isSpread.locallyConnectedSpace
  exact existsUnique_holonomy_hom (deckGroup p).subtype (fun γ => hp.isAEMorphismOf_deck hB γ.2) hD

/-- **`def:quasi_galoisian_branched_covering_singular`** (`RamcovGX.tex:1761`): the *holonomy*
of a branched covering `p : N → M` (quasi-Galoisian in the paper; not used) associated to a
developing map `D`: the morphism `ρ : Γ(N/M) → G` of `lem:holonomy`. -/
def holonomyOf {p : N → M} (hp : IsBranchedCovering p) {B : Set (OpenPartialHomeomorph M X)}
    (hB : IsAEAtlas G B) {D : N → X} (hD : IsDevelopingMapOf G B p D) : Deck p →* G :=
  (existsUnique_holonomyOf G hp hB hD).exists.choose

theorem holonomyOf_spec {p : N → M} (hp : IsBranchedCovering p)
    {B : Set (OpenPartialHomeomorph M X)} (hB : IsAEAtlas G B) {D : N → X}
    (hD : IsDevelopingMapOf G B p D) : IsHolonomyOf p D (holonomyOf hp hB hD) :=
  (existsUnique_holonomyOf G hp hB hD).exists.choose_spec

/-- The holonomy is the unique homomorphism satisfying the holonomy relation. -/
theorem isHolonomyOf_iff {p : N → M} (hp : IsBranchedCovering p)
    {B : Set (OpenPartialHomeomorph M X)} (hB : IsAEAtlas G B) {D : N → X}
    (hD : IsDevelopingMapOf G B p D) {ρ : Deck p →* G} :
    IsHolonomyOf p D ρ ↔ ρ = holonomyOf hp hB hD :=
  ⟨fun h => (existsUnique_holonomyOf G hp hB hD).unique h (holonomyOf_spec hp hB hD),
    fun h => h ▸ holonomyOf_spec hp hB hD⟩

omit [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] [FaithfulSMul G X]
  [ContinuousConstSMul G X] in
/-- The holonomy is trivial iff the developing map is invariant under `Γ(N/M)`. -/
theorem isHolonomyOf_one_iff {p : N → M} {D : N → X} :
    IsHolonomyOf p D (1 : Deck p →* G) ↔ ∀ γ ∈ deckGroup p, ∀ x, D (γ x) = D x :=
  ⟨fun h γ hγ x => by have := h ⟨γ, hγ⟩ x; rwa [MonoidHom.one_apply, one_smul] at this,
    fun h γ x => by rw [MonoidHom.one_apply, one_smul]; exact h γ.1 γ.2 x⟩

omit [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] [FaithfulSMul G X]
  [ContinuousConstSMul G X] in
/-- **`rem:developing_map_quasi_galoisian_covering`** (`RamcovGX.tex:1764`): a developing map
sends a point to a fixed point of the holonomy of its stabilizer, `D(x) ∈ Fix(ρ(Γ_x))`. -/
theorem IsHolonomyOf.smul_eq_of_mem_deckStab {p : N → M} {D : N → X} {ρ : Deck p →* G}
    (h : IsHolonomyOf p D ρ) (x : N) {γ : Deck p} (hγ : γ ∈ deckStab p x) : ρ γ • D x = D x := by
  rw [← h γ x]
  exact congrArg D hγ

omit [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] [FaithfulSMul G X]
  [ContinuousConstSMul G X] in
/-- `rem:developing_map_quasi_galoisian_covering`, as printed: `D(x)` is fixed by every element of
`ρ(Γ_x)`. -/
theorem IsHolonomyOf.mem_fixedPoints {p : N → M} {D : N → X} {ρ : Deck p →* G}
    (h : IsHolonomyOf p D ρ) (x : N) : ∀ g ∈ (deckStab p x).map ρ, g • D x = D x := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact h.smul_eq_of_mem_deckStab x hγ

/-- **`lem:quasi_galoisian_branched_covering_singular`** (`RamcovGX.tex:1771`): two couples
`(D, ρ)`, `(D', ρ')` of developing map and holonomy of a branched covering are conjugate by a
unique `g ∈ G`: `D' = g D` and `ρ' = g ρ g⁻¹`. (Quasi-Galoisian is not used.) -/
theorem developing_pair_unique {p : N → M} (hp : IsBranchedCovering p)
    {B : Set (OpenPartialHomeomorph M X)} {D D' : N → X} {ρ ρ' : Deck p →* G}
    (hD : IsDevelopingMapOf G B p D) (hρ : IsHolonomyOf p D ρ)
    (hD' : IsDevelopingMapOf G B p D') (hρ' : IsHolonomyOf p D' ρ') :
    ∃! g : G, (∀ x, D' x = g • D x) ∧ ∀ γ, ρ' γ = g * ρ γ * g⁻¹ := by
  haveI := hp.connectedSpace_source
  obtain ⟨g, hg, hu⟩ := aeMorphism_model_unique hD' hD
  refine ⟨g, ⟨hg, fun γ => hD'.smul_injective_model fun x => ?_⟩, fun g' hg' => hu g' hg'.1⟩
  rw [← hρ' γ x, hg, hρ, hg x, mul_smul, mul_smul, inv_smul_smul]

end Holonomy

/-! ### Descent along a quasi-Galoisian covering; lifts of morphisms -/

section Descend

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- A developing map invariant under `Γ(M/N)` of a quasi-Galoisian covering is constant on the
fibres (the orbits are dense in them, `lem:dense_orbits`). -/
theorem eq_of_isHolonomyOf_one [T2Space M] [T2Space N] [LocPathConnectedSpace N]
    [FirstCountableTopology N] {p : M → N} (hp : IsQuasiGaloisian p) {D : M → X}
    (hDc : Continuous D) (hhol : IsHolonomyOf p D (1 : Deck p →* G)) {x x' : M}
    (h : p x = p x') : D x = D x' := by
  rw [isHolonomyOf_one_iff] at hhol
  have hmem : D x' ∈ closure ({D x} : Set X) := by
    rw [mem_closure_iff_nhds]
    intro O hO
    obtain ⟨φ, hφ, hφO⟩ := hp.exists_mem_nhds h (hDc.continuousAt.preimage_mem_nhds hO)
    exact ⟨D x, (hhol φ hφ x) ▸ hφO, mem_singleton _⟩
  rw [closure_singleton] at hmem
  exact hmem.symm

/-- **`lem:descend_developing_map`** (`RamcovGX.tex:1780`): for a quasi-Galoisian branched
covering `p : M → N` of a singular `(G,X)`-manifold `N` (locally path-connected, a base of a
branched covering, DEC-66 (a)(c)) (`M` with the structure `p^*B`), there is a
developing map of `p` with trivial holonomy iff there is an a.e. `(G,X)`-morphism `N → X`; then the
first factors through the second, `D = D̄ ∘ p`. -/
theorem descend_developing_map [T2Space M] [T2Space N] [LocPathConnectedSpace N]
    [FirstCountableTopology N] {p : M → N} (hp : IsQuasiGaloisian p)
    {B : Set (OpenPartialHomeomorph N X)} (hB : IsMaximalAEAtlas G B) :
    ((∃ D : M → X, IsDevelopingMapOf G B p D ∧ IsHolonomyOf p D (1 : Deck p →* G)) ↔
      ∃ D : N → X, IsAEMorphismOf G B (gxModelAtlas G X) D) ∧
    ∀ D : M → X, IsDevelopingMapOf G B p D → IsHolonomyOf p D (1 : Deck p →* G) →
      ∃ D' : N → X, IsAEMorphismOf G B (gxModelAtlas G X) D' ∧ D = D' ∘ p := by
  have hbc := hp.1
  haveI := hbc.isSpread.locallyConnectedSpace
  have hA := aePullback_spec_of_isAELocalHomeomorph hB.1 hbc.isSpread.continuous
    (hbc.isAELocalHomeomorph hB.1)
  have hdesc : ∀ D : M → X, IsDevelopingMapOf G B p D → IsHolonomyOf p D (1 : Deck p →* G) →
      ∃ D' : N → X, IsAEMorphismOf G B (gxModelAtlas G X) D' ∧ D = D' ∘ p := by
    intro D hD hhol
    have hfib : ∀ x x', p x = p x' → D x = D x' := fun x x' h =>
      eq_of_isHolonomyOf_one hp hD.continuous hhol h
    set D' : N → X := fun y => D (hbc.surjective y).choose
    have hD'p : ∀ x, D' (p x) = D x := fun x => hfib _ _ (hbc.surjective (p x)).choose_spec
    have hD'eq : D' ∘ p = D := funext hD'p
    have hq : IsQuotientMap p :=
      (spread_connected_image hbc).1.isQuotientMap hbc.isSpread.continuous hbc.surjective
    have hD'c : Continuous D' := hq.continuous_iff.2 (by rw [hD'eq]; exact hD.continuous)
    have hreg := hA.2.regLocusOf_eq hA.1.1 hB.1
    have hDreg := hD.regLocusOf_eq hA.1.1 (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1
    rw [support_gxModelAtlas, preimage_univ, inter_univ] at hDreg
    refine ⟨D', (isAEMorphismOf_iff (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1).2
      ⟨hD'c, ordY p ∩ support B, hbc.isPortly_ordY.inter hB.1.2, ?_⟩, hD'eq.symm⟩
    refine isRegularOn_model_of_eventually hB.1.1 (isOpen_ordY.inter (isOpen_support B))
      inter_subset_right fun y hy => ?_
    obtain ⟨x, rfl⟩ := hbc.surjective y
    have hloc : IsLocalHomeomorphOn p {x} := hbc.ordX_subset_isLocalHomeomorphOn hy.1
    obtain ⟨φ, hxφ, hpφ⟩ := hloc x rfl
    have hxA : x ∈ support (aePullback G B p) :=
      hA.2.mem_support_of_isLocalHomeomorphOn' hA.1 hB.1 hy.2 hloc
    have hxR : x ∈ regLocusOf G (aePullback G B p) B p := by rw [hreg]; exact ⟨hxA, hy.2⟩
    have hxD : x ∈ regLocusOf G (aePullback G B p) (gxModelAtlas G X) D := by
      rw [hDreg]; exact hxA
    obtain ⟨e, he, hxe⟩ := mem_support.1 hxA
    obtain ⟨c, hc, hyc⟩ := mem_support.1 hy.2
    obtain ⟨b, hb⟩ := (isRegularOn_regLocusOf (G := G) _ _ p).exists_smul_eq x hxR e he c hc hxe hyc
    obtain ⟨a, ha⟩ :=
      (isRegularOn_regLocusOf (G := G) _ _ D).eventually_eq_smul_model hxD he hxe
    have hev : ∀ᶠ y' in 𝓝 x, D y' = (a * b⁻¹) • c (p y') := by
      filter_upwards [ha, hb] with y' h1 h2
      rw [h2, h1, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
    have hφx : φ x = p x := by rw [hpφ]
    have ht : Tendsto φ.symm (𝓝 (p x)) (𝓝 x) := by
      have := (φ.continuousAt_symm (φ.map_source hxφ)).tendsto
      rwa [φ.left_inv hxφ, hφx] at this
    have htgt : φ.target ∈ 𝓝 (p x) := by rw [← hφx]; exact φ.open_target.mem_nhds (φ.map_source hxφ)
    refine ⟨c, hc, hyc, a * b⁻¹, ?_⟩
    filter_upwards [ht.eventually hev, htgt] with y' h1 h2
    have hpy : p (φ.symm y') = y' := by rw [hpφ]; exact φ.right_inv h2
    rw [← hpy, hD'p, h1]
  refine ⟨⟨fun ⟨D, hD, hhol⟩ => (hdesc D hD hhol).imp fun _ h => h.1, ?_⟩, hdesc⟩
  rintro ⟨D', hD'⟩
  refine ⟨D' ∘ p, hD'.comp hA.2, (isHolonomyOf_one_iff).2 fun γ hγ x => ?_⟩
  show D' (p (γ x)) = D' (p x)
  rw [deck_apply p hγ]

/-- **`lem:morphism_singular_manifolds_branched`** (`RamcovGX.tex:1799`): a lift
`f̂ : M̂ → N̂` (`q ∘ f̂ = f ∘ p`, continuous) of an a.e. `(G,X)`-morphism `f : M → N` to branched
coverings `p : M̂ → M`, `q : N̂ → N`, with their structures `p^*B_M`, `q^*B_N`, is an a.e.
`(G,X)`-morphism. The paper's reduction to the regular unbranched case is the portly set
`p⁻¹(Reg f ∩ f⁻¹(ord(q) ∩ Reg N)) ∩ Reg p`, on which the three charts compose. -/
theorem morphism_singular_manifolds_branched [LocallyConnectedSpace M]
    {B_M : Set (OpenPartialHomeomorph M X)} {B_N : Set (OpenPartialHomeomorph N X)}
    (hBM : IsAEAtlas G B_M) (hBN : IsAEAtlas G B_N) {f : M → N} (hf : IsAEMorphismOf G B_M B_N f)
    {M' : Type*} [TopologicalSpace M'] {N' : Type*} [TopologicalSpace N'] {p : M' → M}
    (hp : IsBranchedCovering p) {q : N' → N} (hq : IsBranchedCovering q) {f' : M' → N'}
    (hf' : Continuous f') (hcomm : ∀ x, q (f' x) = f (p x)) :
    IsAEMorphismOf G (aePullback G B_M p) (aePullback G B_N q) f' := by
  haveI := hp.isSpread.locallyConnectedSpace
  have hA₁ := aePullback_spec_of_isAELocalHomeomorph hBM hp.isSpread.continuous
    (hp.isAELocalHomeomorph hBM)
  have hA₂ := aePullback_spec_of_isAELocalHomeomorph hBN hq.isSpread.continuous
    (hq.isAELocalHomeomorph hBN)
  have hRfr := isRegularOn_regLocusOf (G := G) B_M B_N f
  have hO : IsPortly (ordY q ∩ support B_N) := hq.isPortly_ordY.inter hBN.2
  have hP : IsPortly (regLocusOf G B_M B_N f ∩ f ⁻¹' (ordY q ∩ support B_N)) :=
    hf.isPortly_regLocusOf.inter_preimage_of_isLocalHomeomorphOn hRfr.isLocalHomeomorphOn hO
  have hRpr := isRegularOn_regLocusOf (G := G) (aePullback G B_M p) B_M p
  have hRqr := isRegularOn_regLocusOf (G := G) (aePullback G B_N q) B_N q
  have hRq := hA₂.2.regLocusOf_eq hA₂.1.1 hBN
  set U := p ⁻¹' (regLocusOf G B_M B_N f ∩ f ⁻¹' (ordY q ∩ support B_N)) ∩
    regLocusOf G (aePullback G B_M p) B_M p
  have hU : IsPortly U := (hp.isPortly_preimage hP).inter hA₁.2.isPortly_regLocusOf
  have hUq : ∀ x ∈ U, f' x ∈ regLocusOf G (aePullback G B_N q) B_N q := by
    intro x hx
    have h1 : q (f' x) ∈ ordY q ∩ support B_N := by rw [hcomm]; exact hx.1.2
    rw [hRq]
    exact ⟨hA₂.2.mem_support_of_isLocalHomeomorphOn' hA₂.1 hBN h1.2
      (hq.ordX_subset_isLocalHomeomorphOn h1.1), h1.2⟩
  refine (isAEMorphismOf_iff hA₂.1.1).2 ⟨hf', U, hU, ?_⟩
  refine IsRegularOn.of_exists hA₁.1.1.1 hA₂.1.1.1 hU.isOpen
    (fun x hx => hRpr.subset_support hx.2) (fun x hx => hRqr.subset_support (hUq x hx))
    hf'.continuousOn fun x hx => ?_
  obtain ⟨e, he, hxe⟩ := mem_support.1 (hRpr.subset_support hx.2)
  obtain ⟨c, hc, hpxc⟩ := mem_support.1 (hRpr.mapsTo hx.2)
  obtain ⟨d, hd, hfpxd⟩ := mem_support.1 (hRfr.mapsTo hx.1.1)
  obtain ⟨e₂, he₂, hfxe₂⟩ := mem_support.1 (hRqr.subset_support (hUq x hx))
  obtain ⟨a, ha⟩ := hRpr.exists_smul_eq x hx.2 e he c hc hxe hpxc
  obtain ⟨b, hb⟩ := hRfr.exists_smul_eq (p x) hx.1.1 c hc d hd hpxc hfpxd
  obtain ⟨k, hk⟩ := hRqr.exists_smul_eq (f' x) (hUq x hx) e₂ he₂ d hd hfxe₂
    (by rw [hcomm]; exact hfpxd)
  refine ⟨e, he, e₂, he₂, hxe, hfxe₂, k⁻¹ * b * a, ?_⟩
  filter_upwards [ha, hp.isSpread.continuous.continuousAt.eventually hb,
    hf'.continuousAt.eventually hk] with y h1 h2 h3
  rw [hcomm] at h3
  rw [mul_smul, mul_smul, ← h1, ← h2, h3, inv_smul_smul]

end Descend

/-! ### Developing maps from simply connected covers -/

section SimplyConnected

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X] {M : Type*} [TopologicalSpace M]

/-- **The classical developing theorem, read in a singular manifold**: a simply connected, locally
path-connected space `Z` with a local homeomorphism `π : Z → M` into the regular locus of an a.e.
atlas `B` has a developing map — a continuous `F : Z → X` which near every point is a translate of
a chart of `B` read through `π`. Built on `GX.exists_developingMap`, for the structure `π^*B`
(`lem:aepullback`), whose support is all of `Z`. -/
theorem exists_developing_of_simplyConnected {Z : Type*} [TopologicalSpace Z]
    [SimplyConnectedSpace Z] [LocPathConnectedSpace Z] {B : Set (OpenPartialHomeomorph M X)}
    (hB : IsAEAtlas G B) {π : Z → M} (hπ : IsLocalHomeomorph π) (hrange : ∀ z, π z ∈ support B) :
    ∃ F : Z → X, Continuous F ∧
      ∀ z, ∃ c ∈ B, π z ∈ c.source ∧ ∃ h : G, ∀ᶠ z' in 𝓝 z, F z' = h • c (π z') := by
  have hloc : IsAELocalHomeomorph B π :=
    ⟨univ, support B, isPortly_univ, hB.2, subset_rfl, fun z _ => hrange z, hπ.isLocalHomeomorphOn⟩
  have hA := aePullback_spec_of_isAELocalHomeomorph hB hπ.continuous hloc
  have hsupp : ∀ z, ∃ e ∈ aePullback G B π, z ∈ e.source := fun z =>
    mem_support.1 (hA.2.mem_support_of_isLocalHomeomorphOn' hA.1 hB (hrange z)
      (hπ.isLocalHomeomorphOn.mono (subset_univ _)))
  letI cs : ChartedSpace X Z := chartedSpaceOfAtlas (aePullback G B π) hsupp
  haveI : HasGroupoid Z (gxGroupoid G X) := hasGroupoid_chartedSpaceOfAtlas hA.1.1.1 hsupp
  haveI : IsAnalyticAction G X :=
    { toFaithfulSMul := inferInstance, toIsRigidAction := inferInstance }
  obtain ⟨F, hF⟩ := exists_developingMap (G := G) (X := X) (N := Z)
  have hreg := hA.2.regLocusOf_eq hA.1.1 hB
  refine ⟨F, hF.continuous, fun z => ?_⟩
  obtain ⟨g, hg⟩ := (isGXMorphism_iff_model.1 hF).2 z
  obtain ⟨c, hc, hzc⟩ := mem_support.1 (hrange z)
  have hmem : chartAt X z ∈ aePullback G B π := chart_mem_atlas X z
  have hzR : z ∈ regLocusOf G (aePullback G B π) B π := by
    rw [hreg]; exact ⟨mem_support.2 ⟨chartAt X z, hmem, mem_chart_source X z⟩, hrange z⟩
  obtain ⟨a, ha⟩ := (isRegularOn_regLocusOf (G := G) _ B π).exists_smul_eq z hzR (chartAt X z)
    hmem c hc (mem_chart_source X z) hzc
  refine ⟨c, hc, hzc, g * a⁻¹, ?_⟩
  filter_upwards [hg, ha] with y h1 h2
  rw [h1, h2, mul_smul, inv_smul_smul]

end SimplyConnected

/-! ### `prop:branched_devmap`: the singular developing theorem -/

section Main

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [FaithfulSMul G X] {M : Type u} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M] [SingularGXStructure G X M]

/-- **`prop:branched_devmap`, (ii) ⇒ (i)** (`RamcovGX.tex:1807`): if some branched covering
`p : N → M` admits a developing map, so does `\widetilde M = \widetilde M^{sing M}`. The
semilocal simple connectedness of `M ∖ (S ∪ sing M)`, `S` the branching locus of `p`, is the
hypothesis under which the proof's `\widehat M = \widetilde M^{S ∪ sing M}` exists
(`prop:universality`). Route: `D ∘ Φ` on `\widehat M` (`Φ : \widehat M → N` by universality) and
`F ∘ Ψ` (`Ψ : \widehat M → \widetilde M`, `F` the developing map of the simply connected
`\widetilde{reg M} ⊆ \widetilde M`, `GX.exists_developing_of_simplyConnected`) are developing
maps of the connected `\widehat M ∖ \widehat S`, hence differ by one `g`; so `D ∘ Φ` is
constant on the fibres of `Ψ` over the dense `\widetilde M ∖ \widetilde S`, hence (`Ψ` open) on
all fibres, and it descends along the quotient map `Ψ`. -/
theorem exists_developing_maxBranched_of_branchedCovering
    (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M)) (y₀ : ((Sing G X M)ᶜ : Set M))
    {N : Type*} [TopologicalSpace N] [T2Space N] [LocPathConnectedSpace N]
    [FirstCountableTopology N] {p : N → M} (hp : IsBranchedCovering p)
    (hT : SemilocallySimplyConnected ((branchingLocus p ∪ Sing G X M)ᶜ : Set M))
    {D : N → X} (hD : IsDevelopingMapOf G (aeAtlas G X M) p D) :
    ∃ D' : MaxBranchedCover (Sing G X M) y₀ → X,
      IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base D' := by
  set B := aeAtlas G X M
  have hBm : IsMaximalAEAtlas G B := isMaximalAEAtlas_aeAtlas G X M
  have hS₀ : IsSkeletal (Sing G X M) := isSkeletal_sing G X M
  set T := branchingLocus p ∪ (Sing G X M)
  have hTsk : IsSkeletal T := hp.branching_locii.1.union hS₀
  have hS₀T : (Sing G X M) ⊆ T := subset_union_right
  have hRegB : (Sing G X M)ᶜ = support B := compl_compl _
  have hTB : Tᶜ ⊆ support B := fun y hy => by rw [← hRegB]; exact fun h => hy (hS₀T h)
  obtain ⟨y₁, hy₁⟩ := nonempty_compl_of_isSkeletal hTsk
  -- `\widetilde M` and `\widehat M`
  obtain ⟨-, hβbc, hβS, hβpre, hβl, hβsp⟩ := maxBranched_basic hS₀ hreg y₀
  haveI := hβl
  obtain ⟨-, hγbc, hγS, -, hγl, -⟩ := maxBranched_basic hTsk hT ⟨y₁, hy₁⟩
  haveI := hγl
  haveI := hγbc.connectedSpace_source
  obtain ⟨Φ, hΦc, hΦp, hΦbc, -⟩ :=
    maxBranched_universal hTsk hT ⟨y₁, hy₁⟩ hp (subset_union_left : branchingLocus p ⊆ T)
  obtain ⟨Ψ, hΨc, hΨp, hΨbc, -⟩ :=
    maxBranched_universal hTsk hT ⟨y₁, hy₁⟩ hβbc (hβS.trans hS₀T)
  -- the structures
  have hAN := aePullback_spec_of_isAELocalHomeomorph hBm.1 hp.isSpread.continuous
    (hp.isAELocalHomeomorph hBm.1)
  have hAh := aePullback_spec_of_isAELocalHomeomorph hBm.1 hγbc.isSpread.continuous
    (hγbc.isAELocalHomeomorph hBm.1)
  have hAt := aePullback_spec_of_isAELocalHomeomorph hBm.1 hβbc.isSpread.continuous
    (hβbc.isAELocalHomeomorph hBm.1)
  have hΦA := aePullback_spec_of_isAELocalHomeomorph hAN.1.1 hΦc (hΦbc.isAELocalHomeomorph hAN.1.1)
  have hcomp := hAN.2.comp hΦA.2
  have hpΦ : p ∘ Φ = SpreadEnd.base := funext hΦp
  rw [hpΦ] at hcomp
  have heqA := eq_aePullback hΦA.1 hcomp
  have hDh : IsAEMorphismOf G (aePullback G B (SpreadEnd.base : MaxBranchedCover T ⟨y₁, hy₁⟩ → M))
      (gxModelAtlas G X) (D ∘ Φ) := by
    have := IsAEMorphismOf.comp hD hΦA.2
    rwa [heqA] at this
  -- `V = \widehat M ∖ \widehat S`
  set V : Set (MaxBranchedCover T ⟨y₁, hy₁⟩) := SpreadEnd.base ⁻¹' Tᶜ
  have hTordγ : Tᶜ ⊆ ordY (SpreadEnd.base : MaxBranchedCover T ⟨y₁, hy₁⟩ → M) :=
    fun y hy => by by_contra h; exact hy (hγS h)
  have hVsupp : V ⊆ support (aePullback G B (SpreadEnd.base : MaxBranchedCover T ⟨y₁, hy₁⟩ → M)) :=
    fun v hv => hAh.2.mem_support_of_isLocalHomeomorphOn' hAh.1 hBm.1 (hTB hv)
      (hγbc.ordX_subset_isLocalHomeomorphOn (hTordγ hv))
  have hVp : IsPortly V := hγbc.isPortly_preimage hTsk
  have hregγ := hAh.2.regLocusOf_eq hAh.1.1 hBm.1
  have hβhV := (isRegularOn_regLocusOf (G := G) _ B
    (SpreadEnd.base : MaxBranchedCover T ⟨y₁, hy₁⟩ → M)).mono
    (fun v hv => by rw [hregγ]; exact ⟨hVsupp hv, hTB hv⟩) hVp.isOpen
  have hDreg := hDh.regLocusOf_eq hAh.1.1 (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1
  rw [support_gxModelAtlas, preimage_univ, inter_univ] at hDreg
  have hDhatV := (isRegularOn_regLocusOf (G := G) _ (gxModelAtlas G X) (D ∘ Φ)).mono
    (by rw [hDreg]; exact hVsupp) hVp.isOpen
  -- the developing map `F₀` of `\widetilde{reg M}`, read on `\widetilde M`
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
  set F₀ : MaxBranchedCover (Sing G X M) y₀ → X :=
    Function.extend (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) F
      (fun _ => F (UniversalCover.base y₀))
  have hF₀ : ∀ c : MaxBranchedCover (Sing G X M) y₀, c.base ∈ (Sing G X M)ᶜ →
      ∃ c' ∈ B, c.base ∈ c'.source ∧
      ∃ h : G, ∀ᶠ c'' in 𝓝 c, F₀ c'' = h • c' c''.base := by
    intro c hc
    have hc' : c ∈ range (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) := by
      rw [← hβpre]; exact hc
    obtain ⟨z, rfl⟩ := hc'
    obtain ⟨c', hc', hzc', h, hh⟩ := hF z
    refine ⟨c', hc', hzc', h, ?_⟩
    rw [← hoe.map_nhds_eq z, eventually_map]
    filter_upwards [hh] with z' hz'
    rw [show F₀ (SpreadEnd.ofPoint _ z') = F z' from hemb.injective.extend_apply _ _ _]
    exact hz'
  -- `F₀ ∘ Ψ` is a developing map on `V`
  have hHV : IsRegularOn G (aePullback G B (SpreadEnd.base : MaxBranchedCover T ⟨y₁, hy₁⟩ → M))
      (gxModelAtlas G X) (F₀ ∘ Ψ) V := by
    refine isRegularOn_model_of_eventually_comp hAh.1.1.1 hβhV fun v hv => ?_
    have hΨv : (Ψ v).base ∈ (Sing G X M)ᶜ := by rw [hΨp]; exact fun h => hv (hS₀T h)
    obtain ⟨c', hc', hvc', h, hh⟩ := hF₀ (Ψ v) hΨv
    refine ⟨c', hc', by rw [← hΨp v]; exact hvc', h, ?_⟩
    filter_upwards [hΨc.continuousAt.eventually hh] with y hy
    rw [Function.comp_apply, hy, hΨp]
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isRegularOn hVp.isConnected.isPreconnected hDhatV hHV
  have hDhV : ∀ y ∈ V, (D ∘ Φ) y = g⁻¹ • F₀ (Ψ y) := fun y hy => by
    have := hg y hy
    simp only [Function.comp_apply] at this ⊢
    rw [this, inv_smul_smul]
  -- constancy on the fibres of `Ψ`
  set W : Set (MaxBranchedCover (Sing G X M) y₀) := SpreadEnd.base ⁻¹' Tᶜ
  have hWp : IsPortly W := hβbc.isPortly_preimage hTsk
  have hΨW : ∀ y, Ψ y ∈ W ↔ y ∈ V := fun y => by
    show (Ψ y).base ∈ Tᶜ ↔ y.base ∈ Tᶜ
    rw [hΨp]
  have hΨo : IsOpenMap Ψ := (spread_connected_image hΨbc).1
  have hDhc : Continuous (D ∘ Φ) := hDh.continuous
  have hfib : ∀ x x', Ψ x = Ψ x' → (D ∘ Φ) x = (D ∘ Φ) x' := by
    intro x x' hxx'
    by_contra hne
    obtain ⟨O, O', hO, hO', hxO, hxO', hOO'⟩ := t2_separation hne
    have hU : IsOpen (Ψ '' ((D ∘ Φ) ⁻¹' O) ∩ Ψ '' ((D ∘ Φ) ⁻¹' O')) :=
      (hΨo _ (hO.preimage hDhc)).inter (hΨo _ (hO'.preimage hDhc))
    obtain ⟨w, ⟨⟨u, hu, rfl⟩, ⟨u', hu', huu'⟩⟩, hwW⟩ :=
      hWp.dense.inter_open_nonempty _ hU ⟨Ψ x, ⟨x, hxO, rfl⟩, ⟨x', hxO', hxx'.symm⟩⟩
    have huV : u ∈ V := (hΨW u).1 hwW
    have hu'V : u' ∈ V := (hΨW u').1 (by rw [huu']; exact hwW)
    have heq : (D ∘ Φ) u = (D ∘ Φ) u' := by rw [hDhV u huV, hDhV u' hu'V, huu']
    exact Set.disjoint_left.1 hOO' hu (by rw [heq]; exact hu')
  -- descent along `Ψ`
  have hΨs := hΨbc.surjective
  set D' : MaxBranchedCover (Sing G X M) y₀ → X := fun e => (D ∘ Φ) (hΨs e).choose
  have hD'Ψ : ∀ y, D' (Ψ y) = (D ∘ Φ) y := fun y => hfib _ _ (hΨs (Ψ y)).choose_spec
  have hD'c : Continuous D' := (hΨo.isQuotientMap hΨc hΨs).continuous_iff.2 (by
    have : D' ∘ Ψ = D ∘ Φ := funext hD'Ψ
    rw [this]; exact hDhc)
  have hTordβ : Tᶜ ⊆ ordY (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) :=
    fun y hy => by by_contra h; exact hy (hS₀T (hβS h))
  have hWsupp :
      W ⊆ support (aePullback G B (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) :=
    fun w hw => hAt.2.mem_support_of_isLocalHomeomorphOn' hAt.1 hBm.1 (hTB hw)
      (hβbc.ordX_subset_isLocalHomeomorphOn (hTordβ hw))
  have hregβ := hAt.2.regLocusOf_eq hAt.1.1 hBm.1
  have hβW := (isRegularOn_regLocusOf (G := G) _ B
    (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)).mono
    (fun w hw => by rw [hregβ]; exact ⟨hWsupp hw, hTB hw⟩) hWp.isOpen
  have hD'W : IsRegularOn G (aePullback G B (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M))
      (gxModelAtlas G X) D' W := by
    refine isRegularOn_model_of_eventually_comp hAt.1.1.1 hβW fun w hw => ?_
    obtain ⟨c', hc', hwc', h, hh⟩ := hF₀ w (fun h => hw (hS₀T h))
    refine ⟨c', hc', hwc', g⁻¹ * h, ?_⟩
    filter_upwards [hh, hWp.isOpen.mem_nhds hw] with w' h1 h2
    obtain ⟨y, rfl⟩ := hΨs w'
    rw [hD'Ψ, hDhV y ((hΨW y).1 h2), h1, mul_smul]
  exact ⟨D', (isAEMorphismOf_iff (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1).2
    ⟨hD'c, W, hWp, hD'W⟩⟩

variable (G X) in
/-- `prop:branched_devmap` (`RamcovGX.tex:1807`), the general form: for a connected singular
`(G,X)`-manifold `M` (Hausdorff, locally path-connected, first countable — the hypotheses of
`prop:universality`, under which `\widetilde M` is defined), (i) there is an a.e.
`(G,X)`-morphism `\widetilde M → X` iff (ii) some branched covering `N → M` admits a developing
map, as soon as `M ∖ S` is semilocally simply connected for every skeletal `S ⊇ sing(M)` — the
condition of `prop:universality` for `\widetilde M = \widetilde M^{sing M}` and for the proof's
`\widetilde M^{S ∪ sing M}`. -/
theorem singular_developing_theorem_of_slsc
    (hslsc : ∀ S : Set M, IsSkeletal S → Sing G X M ⊆ S → SemilocallySimplyConnected (Sᶜ : Set M))
    (y₀ : ((Sing G X M)ᶜ : Set M)) :
    (∃ D : MaxBranchedCover (Sing G X M) y₀ → X,
        IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base D) ↔
      ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T2Space N) (_ : LocPathConnectedSpace N)
        (_ : FirstCountableTopology N) (p : N → M), IsBranchedCovering p ∧
          ∃ D : N → X, IsDevelopingMapOf G (aeAtlas G X M) p D := by
  have hS₀ := isSkeletal_sing G X M
  have hreg := hslsc _ hS₀ subset_rfl
  constructor
  · rintro ⟨D, hD⟩
    obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS₀ hreg y₀
    exact ⟨MaxBranchedCover (Sing G X M) y₀, inferInstance, inferInstance, hl, inferInstance,
      SpreadEnd.base, hbc, D, hD⟩
  · rintro ⟨N, _, _, _, _, p, hp, D, hD⟩
    exact exists_developing_maxBranched_of_branchedCovering hreg y₀ hp
      (hslsc _ (hp.branching_locii.1.union hS₀) subset_union_right) hD

variable (G X) in
/-- **`prop:branched_devmap`** (`RamcovGX.tex:1807`), **the singular developing theorem**, under
the standing assumption of the section (l.1660: `(G,X)` analytical, `X` locally unloopable): for
a connected singular `(G,X)`-manifold `M` (Hausdorff, first countable; locally path-connected
carried, as `prop:universality` needs to define `\widetilde M`, DEC-66 (c)), the following are equivalent:
(i) there exists an a.e. `(G,X)`-morphism `\widetilde M → X`; (ii) there exists a branched
covering `N → M` which admits a developing map. Local unloopability gives the semilocal simple
connectedness of every `M ∖ S`, `S ⊇ sing(M)` skeletal
(`lem:analytical_structure_locally_unloopable`), which is how the proof's
`\widetilde M^{S ∪ sing M}` exists. -/
theorem singular_developing_theorem (hX : IsLocallyUnloopable X)
    (y₀ : ((Sing G X M)ᶜ : Set M)) :
    (∃ D : MaxBranchedCover (Sing G X M) y₀ → X,
        IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base D) ↔
      ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T2Space N) (_ : LocPathConnectedSpace N)
        (_ : FirstCountableTopology N) (p : N → M), IsBranchedCovering p ∧
          ∃ D : N → X, IsDevelopingMapOf G (aeAtlas G X M) p D :=
  singular_developing_theorem_of_slsc G X
    (fun _ hS hSing => semilocallySimplyConnected_compl_of_sing_subset hX hS.isClosed hSing) y₀

variable (G X M) in
/-- **`def:developing_map`**, second sentence (`RamcovGX.tex:1729`): `M` *admits a developing map*
if some branched covering `\widehat M → M` possibly branched above `sing(M)` (Hausdorff, locally
path-connected, first countable — the class of `prop:universality`, in the universe of `M`) has a
developing map. -/
def AdmitsDevelopingMap : Prop :=
  ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T2Space N) (_ : LocPathConnectedSpace N)
    (_ : FirstCountableTopology N) (p : N → M), IsBranchedCovering p ∧
      IsPossiblyBranchedOver p (Sing G X M) ∧ ∃ D : N → X, IsDevelopingMapOf G (aeAtlas G X M) p D

variable (G X) in
/-- `def:developing_map`, third sentence (`RamcovGX.tex:1731`), justified: `M` admits a developing
map iff `\widetilde M → M` has one — "a developing map of `\widetilde M → M` is
simply called a developing map of `M`". Only the hypothesis under which `\widetilde M` is defined
is used: a covering possibly branched over `sing(M)` has branching locus inside `sing(M)`, so the
proof's `\widetilde M^{S ∪ sing M}` is `\widetilde M` itself. -/
theorem admitsDevelopingMap_iff (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (y₀ : ((Sing G X M)ᶜ : Set M)) :
    AdmitsDevelopingMap G X M ↔ ∃ D : MaxBranchedCover (Sing G X M) y₀ → X,
      IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base D := by
  constructor
  · rintro ⟨N, _, _, _, _, p, hp, hpS, D, hD⟩
    have hT : SemilocallySimplyConnected ((branchingLocus p ∪ Sing G X M)ᶜ : Set M) := by
      rw [union_eq_right.2 hpS]; exact hreg
    exact exists_developing_maxBranched_of_branchedCovering hreg y₀ hp hT hD
  · rintro ⟨D, hD⟩
    obtain ⟨-, hbc, hpb, -, hl, -⟩ := maxBranched_basic (isSkeletal_sing G X M) hreg y₀
    exact ⟨MaxBranchedCover (Sing G X M) y₀, inferInstance, inferInstance, hl, inferInstance,
      SpreadEnd.base, hbc, hpb, D, hD⟩

end Main

/-! ### `rem:singular_manifold_holonomy_indeed`: the regular locus -/

section RegHolonomy

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type u} [TopologicalSpace M] [SingularGXStructure G X M]

omit [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] in
theorem val_mem_support_aeAtlas (z : ((Sing G X M)ᶜ : Set M)) :
    (z : M) ∈ support (aeAtlas G X M) := by
  by_contra h
  exact z.2 h

theorem isAELocalHomeomorph_val_reg :
    IsAELocalHomeomorph (aeAtlas G X M) (Subtype.val : ((Sing G X M)ᶜ : Set M) → M) :=
  ⟨univ, support (aeAtlas G X M), isPortly_univ, (isMaximalAEAtlas_aeAtlas G X M).1.2, subset_rfl,
    fun z _ => val_mem_support_aeAtlas z,
    (isClosed_sing G X M).isOpen_compl.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      |>.isLocalHomeomorphOn⟩

theorem aePullback_val_reg_spec :
    IsMaximalAEAtlas G (aePullback G (aeAtlas G X M) (Subtype.val : ((Sing G X M)ᶜ : Set M) → M)) ∧
      IsAEMorphismOf G (aePullback G (aeAtlas G X M) Subtype.val) (aeAtlas G X M)
        (Subtype.val : ((Sing G X M)ᶜ : Set M) → M) :=
  aePullback_spec_of_isAELocalHomeomorph (isMaximalAEAtlas_aeAtlas G X M).1 continuous_subtype_val
    isAELocalHomeomorph_val_reg

variable (G X M) in
/-- The regular locus is covered by the charts of `val^* B`. -/
theorem exists_mem_aePullback_val_reg (z : ((Sing G X M)ᶜ : Set M)) :
    ∃ e ∈ aePullback G (aeAtlas G X M) (Subtype.val : ((Sing G X M)ᶜ : Set M) → M),
      z ∈ e.source :=
  mem_support.1 (aePullback_val_reg_spec.2.mem_support_of_isLocalHomeomorphOn'
    aePullback_val_reg_spec.1 (isMaximalAEAtlas_aeAtlas G X M).1 (val_mem_support_aeAtlas z)
    ((isClosed_sing G X M).isOpen_compl.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      |>.isLocalHomeomorphOn.mono (subset_univ _)))

variable (G X M) in
/-- `reg(M)` as a `(G,X)`-manifold in the usual sense (DEC-16): the charts of the maximal a.e.
atlas, restricted to the regular locus. -/
@[reducible] def regChartedSpace : ChartedSpace X ((Sing G X M)ᶜ : Set M) :=
  chartedSpaceOfAtlas _ (exists_mem_aePullback_val_reg G X M)

theorem hasGroupoid_regChartedSpace :
    @HasGroupoid X _ _ _ (regChartedSpace G X M) (gxGroupoid G X) :=
  hasGroupoid_chartedSpaceOfAtlas aePullback_val_reg_spec.1.1.1 _

variable [T2Space M] [LocPathConnectedSpace M] [FirstCountableTopology M] [ConnectedSpace M]
  [FaithfulSMul G X]

/-- **`rem:singular_manifold_holonomy_indeed`** (`RamcovGX.tex:1768`): the holonomy of
`\widetilde M → M` is the holonomy of `reg(M)` in the usual sense. Precisely: for a developing
map `D` of `\widetilde M` with holonomy `ρ`, its restriction `D ∘ ι` to the universal cover
`\widetilde{reg M} ⊆ \widetilde M` is a developing map of the `(G,X)`-manifold `reg(M)` in the
classical sense (`GX.developing_theorem`), and it has a classical holonomy `hol` with
`hol(γ) = ρ(γ̃)`, `γ̃ ∈ Γ(\widetilde M/M)` the extension of the deck transformation `γ`. -/
theorem singular_manifold_holonomy_indeed
    (hreg : SemilocallySimplyConnected ((Sing G X M)ᶜ : Set M))
    (y₀ : ((Sing G X M)ᶜ : Set M)) {D : MaxBranchedCover (Sing G X M) y₀ → X}
    (hD : IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base D)
    {ρ : Deck (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) →* G}
    (hρ : IsHolonomyOf SpreadEnd.base D ρ) :
    letI := regChartedSpace G X M
    letI : LocPathConnectedSpace ((Sing G X M)ᶜ : Set M) :=
      (isClosed_sing G X M).isOpen_compl.locPathConnectedSpace
    letI := coverChartedSpace X hreg y₀
    IsGXMorphism G X (D ∘ SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) ∧
      ∃ hol : Deck (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀) →* G,
        (∀ (γ : Deck (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀)) z,
          (D ∘ SpreadEnd.ofPoint _) ((γ : UniversalCover _ y₀ ≃ₜ UniversalCover _ y₀) z) =
            hol γ • (D ∘ SpreadEnd.ofPoint _) z) ∧
        ∀ γ : Deck (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀),
          ∃ γ' : Deck (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M),
          (∀ z, (γ' : MaxBranchedCover _ y₀ ≃ₜ MaxBranchedCover _ y₀) (SpreadEnd.ofPoint _ z) =
            SpreadEnd.ofPoint _ ((γ : UniversalCover _ y₀ ≃ₜ UniversalCover _ y₀) z)) ∧
          hol γ = ρ γ' := by
  letI := regChartedSpace G X M
  haveI := hasGroupoid_regChartedSpace (G := G) (X := X) (M := M)
  letI : LocPathConnectedSpace ((Sing G X M)ᶜ : Set M) :=
    (isClosed_sing G X M).isOpen_compl.locPathConnectedSpace
  letI := coverChartedSpace X hreg y₀
  haveI := hasGroupoid_cover (G := G) (X := X) hreg y₀
  haveI : IsAnalyticAction G X :=
    { toFaithfulSMul := inferInstance, toIsRigidAction := inferInstance }
  have hS₀ := isSkeletal_sing G X M
  have hBm := isMaximalAEAtlas_aeAtlas G X M
  obtain ⟨-, hβbc, hβS, -, hβl, hβsp⟩ := maxBranched_basic hS₀ hreg y₀
  haveI := hβl
  have hAt := aePullback_spec_of_isAELocalHomeomorph hBm.1 hβbc.isSpread.continuous
    (hβbc.isAELocalHomeomorph hBm.1)
  have hιc := SpreadEnd.continuous_ofPoint hβsp
  have hDreg := IsAEMorphismOf.regLocusOf_eq hAt.1.1
    (isMaximalAEAtlas_gxModelAtlas (G := G) (X := X)).1 hD
  rw [support_gxModelAtlas, preimage_univ, inter_univ] at hDreg
  have hregβ := hAt.2.regLocusOf_eq hAt.1.1 hBm.1
  have hrange : ∀ z : UniversalCover ((Sing G X M)ᶜ : Set M) y₀,
      (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀) z).base ∈ support (aeAtlas G X M) :=
    fun z => val_mem_support_aeAtlas (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀ z)
  have hord : ∀ z : UniversalCover ((Sing G X M)ᶜ : Set M) y₀,
      (SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀) z).base ∈
        ordY (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) := fun z => by
    by_contra h; exact (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀ z).2 (hβS h)
  have hιsupp : ∀ z, SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀) z ∈
      support (aePullback G (aeAtlas G X M)
        (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)) := fun z =>
    hAt.2.mem_support_of_isLocalHomeomorphOn' hAt.1 hBm.1 (hrange z)
      (hβbc.ordX_subset_isLocalHomeomorphOn (hord z))
  have hloc : ∀ z : UniversalCover ((Sing G X M)ᶜ : Set M) y₀, ∃ c ∈ aeAtlas G X M,
      ((UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀ z : M)) ∈ c.source ∧ ∃ h : G, ∀ᶠ z' in 𝓝 z,
        D (SpreadEnd.ofPoint _ z') =
          h • c (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀ z' : M) := by
    intro z
    obtain ⟨e, he, hze⟩ := mem_support.1 (hιsupp z)
    obtain ⟨c, hc, hzc⟩ := mem_support.1 (hrange z)
    obtain ⟨a, ha⟩ := (isRegularOn_regLocusOf (G := G) _ _ D).eventually_eq_smul_model
      (by rw [hDreg]; exact hιsupp z) he hze
    obtain ⟨b, hb⟩ := (isRegularOn_regLocusOf (G := G) _ (aeAtlas G X M)
      (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M)).exists_smul_eq _
      (by rw [hregβ]; exact ⟨hιsupp z, hrange z⟩) e he c hc hze hzc
    refine ⟨c, hc, hzc, a * b⁻¹, ?_⟩
    filter_upwards [hιc.continuousAt.eventually ha, hιc.continuousAt.eventually hb] with z' h1 h2
    have h2' : c (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀ z' : M) =
        b • e (SpreadEnd.ofPoint _ z') := h2
    rw [h1, h2', ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have hvreg := aePullback_val_reg_spec.2.regLocusOf_eq (G := G) aePullback_val_reg_spec.1.1 hBm.1
  have hdev : IsGXMorphism G X (D ∘ SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) := by
    refine isGXMorphism_iff_model.2 ⟨hD.continuous.comp hιc, fun z => ?_⟩
    obtain ⟨c, hc, hzc, h, hh⟩ := hloc z
    set w := UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀ z
    have hmem : chartAt X w ∈ aePullback G (aeAtlas G X M)
        (Subtype.val : ((Sing G X M)ᶜ : Set M) → M) := chart_mem_atlas X w
    have hwR : w ∈ regLocusOf G (aePullback G (aeAtlas G X M) Subtype.val) (aeAtlas G X M)
        (Subtype.val : ((Sing G X M)ᶜ : Set M) → M) := by
      rw [hvreg]
      exact ⟨mem_support.2 ⟨chartAt X w, hmem, mem_chart_source X w⟩, val_mem_support_aeAtlas w⟩
    obtain ⟨k, hk⟩ := (isRegularOn_regLocusOf (G := G) _ (aeAtlas G X M) _).exists_smul_eq w hwR
      (chartAt X w) hmem c hc (mem_chart_source X w) hzc
    refine ⟨h * k, ?_⟩
    filter_upwards [hh, (UniversalCover.continuous_proj (Y := ((Sing G X M)ᶜ : Set M))
      (y₀ := y₀)).continuousAt.eventually hk] with y h1 h2
    rw [Function.comp_apply, h1, h2, mul_smul, pullback_chartAt_apply]
  obtain ⟨dev₀, hol₀, hdev₀, -, hhol₀⟩ := developing_theorem (G := G) (X := X) hreg y₀
  obtain ⟨g, hg, -⟩ := developing_unique_of_preconnected hdev₀ hdev
  refine ⟨hdev, (MulAut.conj g).toMonoidHom.comp hol₀, fun γ z => ?_, fun γ => ?_⟩
  · rw [hg, hg z, hhol₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_smul, mul_smul, inv_smul_smul]
  · obtain ⟨Φ, hΦ, hΦc⟩ := maxBranched_deck_of_universalCover y₀ γ.1
      (fun c => congrArg Subtype.val (congrFun γ.2 c))
    refine ⟨⟨Φ, hΦ⟩, hΦc, hdev.smul_injective fun z => ?_⟩
    have h1 : (D ∘ SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) (γ.1 z) =
        ((MulAut.conj g).toMonoidHom.comp hol₀) γ • (D ∘ SpreadEnd.ofPoint _) z := by
      rw [hg, hg z, hhol₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        mul_smul, mul_smul, inv_smul_smul]
    rw [← h1]
    show D (SpreadEnd.ofPoint _ (γ.1 z)) = ρ ⟨Φ, hΦ⟩ • D (SpreadEnd.ofPoint _ z)
    rw [← hΦc z]
    exact hρ ⟨Φ, hΦ⟩ _

/-- **`rem:singular_manifold_holonomy_indeed`** (`RamcovGX.tex:1768`) under the section's standing
assumption (l.1660, `X` locally unloopable) instead of the semilocal simple connectedness of
`reg(M)`: that assumption makes `\widetilde M` (and `\widetilde{reg M}`) always defined
(`lem:analytical_structure_locally_unloopable`), and the remark holds as in
`GX.singular_manifold_holonomy_indeed` (DEC-66 (c), DEC-67 (c)). -/
theorem singular_manifold_holonomy_indeed_of_isLocallyUnloopable (hX : IsLocallyUnloopable X)
    (y₀ : ((Sing G X M)ᶜ : Set M)) {D : MaxBranchedCover (Sing G X M) y₀ → X}
    (hD : IsDevelopingMapOf G (aeAtlas G X M) SpreadEnd.base D)
    {ρ : Deck (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M) →* G}
    (hρ : IsHolonomyOf SpreadEnd.base D ρ) :
    letI := regChartedSpace G X M
    letI : LocPathConnectedSpace ((Sing G X M)ᶜ : Set M) :=
      (isClosed_sing G X M).isOpen_compl.locPathConnectedSpace
    letI := coverChartedSpace X
      (semilocallySimplyConnected_compl_of_sing_subset hX (isClosed_sing G X M) subset_rfl) y₀
    IsGXMorphism G X (D ∘ SpreadEnd.ofPoint (univCoverProj (Sing G X M) y₀)) ∧
      ∃ hol : Deck (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀) →* G,
        (∀ (γ : Deck (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀)) z,
          (D ∘ SpreadEnd.ofPoint _) ((γ : UniversalCover _ y₀ ≃ₜ UniversalCover _ y₀) z) =
            hol γ • (D ∘ SpreadEnd.ofPoint _) z) ∧
        ∀ γ : Deck (UniversalCover.proj ((Sing G X M)ᶜ : Set M) y₀),
          ∃ γ' : Deck (SpreadEnd.base : MaxBranchedCover (Sing G X M) y₀ → M),
          (∀ z, (γ' : MaxBranchedCover _ y₀ ≃ₜ MaxBranchedCover _ y₀) (SpreadEnd.ofPoint _ z) =
            SpreadEnd.ofPoint _ ((γ : UniversalCover _ y₀ ≃ₜ UniversalCover _ y₀) z)) ∧
          hol γ = ρ γ' :=
  singular_manifold_holonomy_indeed
    (semilocallySimplyConnected_compl_of_sing_subset hX (isClosed_sing G X M) subset_rfl) y₀ hD hρ

end RegHolonomy

end GX
