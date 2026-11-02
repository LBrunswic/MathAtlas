import Causal.CBG.Geometry

/-!
# The size bound of the CBG construction: small developments

No paper label is certified by this file (package 9, design `docs/CBG-DESIGN.md` §3 step 6). It
is the « small skeleton » the inductive limit of ETT `theo:CBG` (`ETT.tex:1884`, proof
`ETT.tex:2335–2341`) and of Brunswic's thesis (`these.tex:6313–6318`) needs, and Sbierski's
restriction to developments whose manifold is a subset of a fixed set (1309.7591, §3.3, p. 21).
Cited, unmarked: `rem:CBG_manquant` (ii) — `ETT.tex:2343`, `theo:CBG` — `ETT.tex:1884`.

> The existence of the inductive limit also requires a small skeleton of the category of
> globally hyperbolic $\mass{\geq0}$-manifolds, i.e. a full subcategory containing one
> representative of each isomorphism class and whose morphisms form a set. Since all such
> manifolds have the cardinality of the continuum, this is routine, and we do not detail it.
> (`rem:CBG_manquant` (ii), `ETT.tex:2351–2354`)

> En fait, l'existence d'une limite inductive nécessite également de montrer que l'on peut trouver
> un petit squelette de la catégorie des $\mass{\geq0}$-variétés globalement hyperboliques
> c'est-à-dire une sous-catégorie pleine contenant un représentant de chaque classe d'isomorphisme
> et dont les morphismes forment un ensemble. Comme toutes les $\mass{\geq0}$-variétés globalement
> hyperboliques ont la puissance du continu c'est un fait aisé à vérifier. (`these.tex:6315–6318`)

> However, the following subtlety arises: the collection of all GHDs of given initial data is not
> a set, but a proper class - and thus we cannot use the axioms of the Zermelo-Fraenkel set theory
> for justifying the glueing construction we have in mind. Fortunately, there is an easy way to
> circumvent this obstacle: Instead of considering all GHDs of given initial data, we only consider
> those whose underlying manifold is a subset of M × R. This collection X of GHDs is indeed a set
> (as we will show below), and thus we can glue all such GHDs together along their MCGHDs. In order
> to justify that the so obtained GHD M̃ is indeed the MGHD, we just note that any GHD of the same
> initial data is isometric to one in X, and hence isometrically embeds into M̃.
> (Sbierski 1309.7591, p. 21, `pdftotext` lines 1137–1144)

Contents.
* **Second countable T0 spaces inject into `Set ℕ`**: `basisCode X x`, the indices (by the
  `Encodable` instance of `countableBasis X`) of the basic open sets containing `x`;
  `basisCode_injective` (T0), `exists_injective_setNat`.
* **The copy in `Set ℕ`**: `SmallCarrier A := ULift.{u} A` for `A : Set (Set ℕ)` (a `def`, so no
  `ULift` instance interferes), `setNatEquiv X : X ≃ SmallCarrier (range (basisCode X))`, the
  transported topology `setNatTop X`, and the homeomorphism `setNatHomeomorph X`.
* **Transport of structures along homeomorphisms** (`Geometry.transport`): the inverse
  `Geometry.isMor_transport_symm` (from `isMor_inv`), the causality of the transported structure
  read through `e` (`Geometry.le_transport_iff`, `lt_transport_iff` — the « planned lemma » of
  Geometry's SCOPE for `transport`), and model-free: `globallyHyperbolic_of_inverse`,
  `isCauchySurface_image_of_bijective`, `isCauchyEmbedding_comp_of_inverse`.
* **Developments**: `Dev.transport N e` (the development carried to a homeomorphic carrier),
  `Dev.isMorphism_transport`, `Dev.isMorphism_transport_symm`.
* **`SmallDev 𝔊 s₀ : Type u`**: developments whose carrier is `SmallCarrier A`, `A ⊆ Set ℕ`;
  `SmallDev.toDev`, `SmallDev.ofDev`; **`SmallDev.exists_iso`: every `Dev` is isomorphic, by
  mutually inverse `Dev.IsMorphism`s, to a small one**; `Dev.isUniversal_of_small` (universality
  against small developments suffices: Sbierski's « hence isometrically embeds into M̃ »), and
  `Dev.IsUniversal.small`.
* **Universes** (design step 7): `Dev 𝔊 s₀ : Type (u+1)`, so it cannot index `Geometry.glue`
  (`ι : Type u`); `SmallDev 𝔊 s₀ : Type u` can (checked by an `example` after
  `SmallDev.Carrier`), with the family of carriers
  `SmallDev.Carrier : SmallDev 𝔊 s₀ → Type u` that `glue` and `FamilyGlueData` take. The data
  `A : Set (Set ℕ)` lives in `Type`; the structure `𝔊.Str` lives in `Type u`, so `SmallDev` is in
  `Type` exactly when `u = 0`. The lift to `Type u` is `SmallCarrier A = ULift.{u} A`.

## Hypothesis checklist

| paper / thesis / Sbierski | here |
|---|---|
| « all such manifolds have the cardinality of the continuum » (`ETT.tex:2353–2354`, `these.tex:6318`) | ⚠ weakened: only `≤ 𝔠` is used (T0 + second countability, `basisCode_injective`); `=` holds for the paper's non-empty 3-manifolds and is not needed (an abstract `Geometry` may admit a one-point carrier) |
| carriers subsets of a fixed set (Sbierski: `M × ℝ`; ETT: a set of size `𝔠`) | ✓ `Set ℕ` (`SmallCarrier A`, `A : Set (Set ℕ)`), lifted to `Type u` by `ULift` |
| Sbierski normalises the embedding (`ι(x) = (x, 0)`) | ⚠ weakened: not normalised; `emb` is any Cauchy embedding (universality is unaffected, `Dev.isUniversal_of_small`) |
| « any GHD … is isometric to one in X » | ✓ `SmallDev.exists_iso` (mutually inverse `Dev.IsMorphism`s) |
| « whose morphisms form a set » | ✓ in type theory: `SmallDev 𝔊 s₀ : Type u`, and morphisms between two small developments are a `Type u`-valued function type |
| T0 / second countability of the carriers | ✓ carried by `Dev` (`Dev.t2`, `Dev.sc`, gx review C2) |

## SCOPE (disclosed)

* The isomorphism of `SmallDev.exists_iso` uses only the fields `transport`, `isMor_transport`,
  `isMor_inv`, `isMor_comp`, `isMor_congr`, `isEMorphismOn_of_isMor` of `Geometry`; no field is
  missing for this package. In particular no field relating `causality (transport e s)` to
  `causality s` is needed: it is derived (`le_transport_iff`, `lt_transport_iff`).
* The set-theoretic content of Sbierski's argument (power set, specification) has no counterpart:
  in Lean the issue is the universe level, `Dev : Type (u+1)` against `glue`'s `ι : Type u`.
* **Deviation from design step 6**: `SmallDev 𝔊 s₀ : Type u`, not `Type` — forced, since the
  field `str : 𝔊.Str _` lives in `Type u` (`SmallDev` is in `Type` exactly when `u = 0`). The
  step-7 `ULift` lives in the carrier (`SmallCarrier A := ULift.{u} A`), so package 10 needs no
  further lift: `Geometry.glue` takes `ι : Type u`, `M : ι → Type u`, and
  `SmallDev.Carrier : SmallDev 𝔊 s₀ → Type u`. The design's §3.6–3.7 wording is the master's to
  amend.
* The full subcategory is not shown to be a *skeleton* (one representative per isomorphism
  class): `SmallDev` contains many representatives of each class, which is harmless for
  Sbierski's gluing (he does the same, `X` contains every GHD on a subset of `M × ℝ`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace CBG

open Set Topology Function TopologicalSpace

universe u v

/-! ### Second countable T0 spaces inject into `Set ℕ` -/

section Code

variable (X : Type v) [TopologicalSpace X] [SecondCountableTopology X]

/-- **The code of a point** in `Set ℕ`: the indices (by the `Encodable` instance of the countable
basis `countableBasis X`) of the basic open sets containing it. -/
def basisCode (x : X) : Set ℕ :=
  {n | ∃ b : countableBasis X, Encodable.encode b = n ∧ x ∈ (b : Set X)}

/-- **Second countable T0 spaces inject into `Set ℕ`** (design §3.6): two points with the same
code lie in the same basic open sets, hence in the same open sets, hence are equal (T0). -/
theorem basisCode_injective [T0Space X] : Injective (basisCode X) := by
  intro x y hxy
  have key : ∀ b ∈ countableBasis X, x ∈ b → y ∈ b := by
    intro b hb hx
    have hmem : Encodable.encode (⟨b, hb⟩ : countableBasis X) ∈ basisCode X y := by
      rw [← hxy]; exact ⟨⟨b, hb⟩, rfl, hx⟩
    obtain ⟨b', he, hy⟩ := hmem
    rw [Encodable.encode_injective he] at hy
    exact hy
  have key' : ∀ b ∈ countableBasis X, y ∈ b → x ∈ b := by
    intro b hb hy
    have hmem : Encodable.encode (⟨b, hb⟩ : countableBasis X) ∈ basisCode X x := by
      rw [hxy]; exact ⟨⟨b, hb⟩, rfl, hy⟩
    obtain ⟨b', he, hx⟩ := hmem
    rw [Encodable.encode_injective he] at hx
    exact hx
  refine Inseparable.eq (inseparable_iff_forall_isOpen.2 fun s hs => ⟨fun hx => ?_, fun hy => ?_⟩)
  · obtain ⟨b, hb, hxb, hbs⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hx hs
    exact hbs (key b hb hxb)
  · obtain ⟨b, hb, hyb, hbs⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hy hs
    exact hbs (key' b hb hyb)

/-- **A second countable T0 space injects into `Set ℕ`.** -/
theorem exists_injective_setNat [T0Space X] : ∃ f : X → Set ℕ, Injective f :=
  ⟨basisCode X, basisCode_injective X⟩

end Code

/-! ### The copy of a space inside `Set ℕ`, lifted to `Type u` -/

/-- **The carrier of a small development**: a subset `A` of `Set ℕ`, lifted to `Type u`. A `def`
(not an `abbrev`), so that mathlib's `ULift` topology does not compete with the topology a small
development carries. -/
def SmallCarrier (A : Set (Set ℕ)) : Type u := ULift.{u} A

section Copy

variable (X : Type u) [TopologicalSpace X] [SecondCountableTopology X] [T0Space X]

/-- The bijection of `X` onto its code set, lifted to `Type u`. -/
noncomputable def setNatEquiv : X ≃ SmallCarrier.{u} (range (basisCode X)) :=
  (Equiv.ofInjective _ (basisCode_injective X)).trans Equiv.ulift.symm

/-- The topology of `X` carried to its copy. -/
@[reducible] noncomputable def setNatTop : TopologicalSpace (SmallCarrier.{u} (range (basisCode X))) :=
  TopologicalSpace.induced (setNatEquiv X).symm inferInstance

/-- **The homeomorphism of `X` onto its copy in `Set ℕ`.** -/
noncomputable def setNatHomeomorph :
    @Homeomorph X (SmallCarrier.{u} (range (basisCode X))) _ (setNatTop X) :=
  letI := setNatTop X
  { toEquiv := setNatEquiv X
    continuous_toFun := continuous_induced_rng.2 (by
      convert (continuous_id : Continuous (id : X → X)) using 1
      exact funext (setNatEquiv X).symm_apply_apply)
    continuous_invFun := continuous_induced_dom }

end Copy

/-! ### Model-free: transport of global hyperbolicity and Cauchy surfaces along an isomorphism -/

section ModelFree

variable {M₀ : Type*} {M : Type*} {N : Type*} [TopologicalSpace M₀] [TopologicalSpace M]
  [TopologicalSpace N] {C₀ : Causality M₀} {C : Causality M} {D : Causality N}

/-- **Global hyperbolicity is carried by an isomorphism**: abstract morphisms `f`, `g` with
`f ∘ g = id`. -/
theorem globallyHyperbolic_of_inverse {f : M → N} {g : N → M} (hf : IsEMorphism C D f)
    (hg : IsEMorphism D C g) (hfg : ∀ y, f (g y) = y) (hC : C.GloballyHyperbolic) :
    D.GloballyHyperbolic := by
  have hfc : Continuous f := by
    have := hf.continuousOn; rwa [Opens.coe_top, continuousOn_univ] at this
  have hgle : ∀ {a b : N}, D.le ⊤ a b → C.le ⊤ (g a) (g b) := fun h =>
    hg.map_le ⊤ ⊤ le_rfl (fun _ _ => trivial) h
  have hfle : ∀ {a b : M}, C.le ⊤ a b → D.le ⊤ (f a) (f b) := fun h =>
    hf.map_le ⊤ ⊤ le_rfl (fun _ _ => trivial) h
  refine ⟨fun a b hab hba => ?_, fun p q => ?_⟩
  · rw [← hfg a, ← hfg b, hC.1 (hgle hab) (hgle hba)]
  · have hdia : D.diamond ⊤ p q = f '' C.diamond ⊤ (g p) (g q) := by
      ext z
      constructor
      · intro hz
        rw [Causality.mem_diamond] at hz
        exact ⟨g z, Causality.mem_diamond.2 ⟨hgle hz.1, hgle hz.2⟩, hfg z⟩
      · rintro ⟨x, hx, rfl⟩
        rw [Causality.mem_diamond] at hx ⊢
        have h1 := hfle hx.1
        have h2 := hfle hx.2
        rw [hfg] at h1 h2
        exact ⟨h1, h2⟩
    rw [hdia]
    exact (hC.2 _ _).image hfc

/-- **Cauchy surfaces are carried by a bijective abstract morphism.** -/
theorem isCauchySurface_image_of_bijective {f : M → N} (hf : IsEMorphism C D f)
    (hbij : Bijective f) {S : Set M} (hS : C.IsCauchySurface S) : D.IsCauchySurface (f '' S) := by
  have htop : hf.imageOpens ⊤ le_rfl = ⊤ := by
    apply SetLike.coe_injective
    rw [IsEMorphismOn.coe_imageOpens, Opens.coe_top, image_univ_of_surjective hbij.2,
      Opens.coe_top]
  have := (hf.isCauchySurface_iff hbij.1 S).1 hS
  rw [htop] at this
  exact Causality.isCauchySurfaceOn_top.1 this

/-- **A Cauchy embedding followed by an isomorphism is a Cauchy embedding.** -/
theorem isCauchyEmbedding_comp_of_inverse {φ : M₀ → M} {f : M → N} {g : N → M}
    (hφ : IsCauchyEmbedding C₀ C φ) (hf : IsEMorphism C D f) (hg : IsEMorphism D C g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : IsCauchyEmbedding C₀ D (f ∘ φ) := by
  have hbij : Bijective f :=
    ⟨LeftInverse.injective hgf, RightInverse.surjective hfg⟩
  obtain ⟨S, hS, hS'⟩ := hφ.exists_cauchy
  exact ⟨hφ.globallyHyperbolic_source,
    globallyHyperbolic_of_inverse hf hg hfg hφ.globallyHyperbolic_target,
    IsEMorphism.comp hf hφ.isEMorphism, hbij.1.comp hφ.injective,
    ⟨S, hS, by rw [image_comp]; exact isCauchySurface_image_of_bijective hf hbij hS'⟩⟩

end ModelFree

/-! ### Transport of structures along homeomorphisms -/

namespace Geometry

variable (𝔊 : Geometry.{u}) {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M']

/-- The image of `⊤` by a homeomorphism, read through `isEMorphismOn_of_isMor`, is `⊤`. -/
theorem imageOpens_transport_top (e : M ≃ₜ M') (s : 𝔊.Str M) :
    (𝔊.isEMorphismOn_of_isMor (𝔊.isMor_transport e s)).imageOpens ⊤ le_rfl = ⊤ := by
  apply SetLike.coe_injective
  rw [IsEMorphismOn.coe_imageOpens, Opens.coe_top, image_univ_of_surjective e.surjective,
    Opens.coe_top]

/-- **The inverse of a transport is a morphism** (from `isMor_inv`). -/
theorem isMor_transport_symm [Nonempty M] (e : M ≃ₜ M') (s : 𝔊.Str M) :
    𝔊.IsMor (𝔊.transport e s) s ⊤ e.symm := by
  have h := 𝔊.isMor_inv (𝔊.isMor_transport e s) e.injective.injOn
  rw [imageOpens_transport_top] at h
  refine 𝔊.isMor_congr h fun y _ => ?_
  apply e.injective
  rw [e.apply_symm_apply]
  exact invFunOn_eq ⟨e.symm y, trivial, e.apply_symm_apply y⟩

/-- `e` is an abstract morphism into the transported structure. -/
theorem isEMorphism_transport (e : M ≃ₜ M') (s : 𝔊.Str M) :
    IsEMorphism (𝔊.causality s) (𝔊.causality (𝔊.transport e s)) e :=
  𝔊.isEMorphismOn_of_isMor (𝔊.isMor_transport e s)

/-- `e⁻¹` is an abstract morphism out of the transported structure. -/
theorem isEMorphism_transport_symm [Nonempty M] (e : M ≃ₜ M') (s : 𝔊.Str M) :
    IsEMorphism (𝔊.causality (𝔊.transport e s)) (𝔊.causality s) e.symm :=
  𝔊.isEMorphismOn_of_isMor (𝔊.isMor_transport_symm e s)

/-- The preimage of an open set by a homeomorphism. -/
def preimageOpensHomeo (e : M ≃ₜ M') (U : Opens M') : Opens M :=
  ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩

/-- **The causality of a transported structure is the transported causality** (`≤`): the
« planned lemma » of `Geometry`'s SCOPE for `transport`, derived from `isMor_transport`,
`isMor_inv` and `isEMorphismOn_of_isMor`. -/
theorem le_transport_iff [Nonempty M] (e : M ≃ₜ M') (s : 𝔊.Str M) (U : Opens M') (x y : M) :
    (𝔊.causality (𝔊.transport e s)).le U (e x) (e y) ↔
      (𝔊.causality s).le (preimageOpensHomeo e U) x y := by
  constructor
  · intro h
    have := (𝔊.isEMorphism_transport_symm e s).map_le U (preimageOpensHomeo e U) le_top
      (fun z hz => by
        show e (e.symm z) ∈ (U : Set M')
        rw [e.apply_symm_apply]; exact hz) h
    simpa using this
  · intro h
    exact (𝔊.isEMorphism_transport e s).map_le (preimageOpensHomeo e U) U le_top
      (fun z hz => hz) h

/-- **The causality of a transported structure is the transported causality** (`≪`). -/
theorem lt_transport_iff [Nonempty M] (e : M ≃ₜ M') (s : 𝔊.Str M) (U : Opens M') (x y : M) :
    (𝔊.causality (𝔊.transport e s)).lt U (e x) (e y) ↔
      (𝔊.causality s).lt (preimageOpensHomeo e U) x y := by
  constructor
  · intro h
    have := (𝔊.isEMorphism_transport_symm e s).map_lt U (preimageOpensHomeo e U) le_top
      (fun z hz => by
        show e (e.symm z) ∈ (U : Set M')
        rw [e.apply_symm_apply]; exact hz) h
    simpa using this
  · intro h
    exact (𝔊.isEMorphism_transport e s).map_lt (preimageOpensHomeo e U) U le_top
      (fun z hz => hz) h

end Geometry

/-! ### Developments carried along homeomorphisms -/

section DevTransport

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- **A development carried to a homeomorphic carrier** by `Geometry.transport`. -/
noncomputable def Dev.transport (N : Dev 𝔊.toPreGeometry s₀) {X : Type u} [TopologicalSpace X]
    (e : N.carrier ≃ₜ X) : Dev 𝔊.toPreGeometry s₀ where
  carrier := X
  t2 := e.symm.isEmbedding.t2Space
  conn := e.surjective.connectedSpace e.continuous
  sc := e.symm.isEmbedding.secondCountableTopology
  str := 𝔊.transport e N.str
  emb := e ∘ N.emb
  isCauchyEmbedding :=
    isCauchyEmbedding_comp_of_inverse N.isCauchyEmbedding (𝔊.isEMorphism_transport e N.str)
      (𝔊.isEMorphism_transport_symm e N.str) e.symm_apply_apply e.apply_symm_apply
  isMor := 𝔊.isMor_comp (𝔊.isMor_transport e N.str) N.isMor (fun _ _ => trivial)

/-- `e` is a morphism of developments `N → N.transport e`. -/
theorem Dev.isMorphism_transport (N : Dev 𝔊.toPreGeometry s₀) {X : Type u} [TopologicalSpace X]
    (e : N.carrier ≃ₜ X) : N.IsMorphism (N.transport e) e :=
  ⟨𝔊.isMor_transport e N.str, rfl⟩

/-- `e⁻¹` is a morphism of developments `N.transport e → N`. -/
theorem Dev.isMorphism_transport_symm (N : Dev 𝔊.toPreGeometry s₀) {X : Type u}
    [TopologicalSpace X] (e : N.carrier ≃ₜ X) : (N.transport e).IsMorphism N e.symm :=
  ⟨𝔊.isMor_transport_symm e N.str, funext fun x => e.symm_apply_apply (N.emb x)⟩

end DevTransport

/-! ### Small developments -/

section Small

/-- **A small development** (design §3.6): a development whose carrier is `SmallCarrier A`, the
lift to `Type u` of a subset `A` of `Set ℕ`. `SmallDev 𝔊 s₀ : Type u` (checked by the `example` after
`SmallDev.Carrier`), where `Dev 𝔊 s₀ : Type (u+1)`. -/
structure SmallDev (𝔊 : PreGeometry.{u}) {M₀ : Type u} [TopologicalSpace M₀] (s₀ : 𝔊.Str M₀) where
  /-- The subset of `Set ℕ` underlying the carrier. -/
  carrierSet : Set (Set ℕ)
  [top : TopologicalSpace (SmallCarrier.{u} carrierSet)]
  [t2 : T2Space (SmallCarrier.{u} carrierSet)]
  [conn : ConnectedSpace (SmallCarrier.{u} carrierSet)]
  [sc : SecondCountableTopology (SmallCarrier.{u} carrierSet)]
  /-- The structure. -/
  str : 𝔊.Str (SmallCarrier.{u} carrierSet)
  /-- The embedding of `M₀`. -/
  emb : M₀ → SmallCarrier.{u} carrierSet
  isCauchyEmbedding : IsCauchyEmbedding (𝔊.causality s₀) (𝔊.causality str) emb
  isMor : 𝔊.IsMor s₀ str ⊤ emb

attribute [instance] SmallDev.top SmallDev.t2 SmallDev.conn SmallDev.sc

variable {𝔊 : PreGeometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- A small development as a development. -/
def SmallDev.toDev (N : SmallDev 𝔊 s₀) : Dev 𝔊 s₀ where
  carrier := SmallCarrier.{u} N.carrierSet
  str := N.str
  emb := N.emb
  isCauchyEmbedding := N.isCauchyEmbedding
  isMor := N.isMor

/-- **The family of carriers** of the small developments, the `M : ι → Type u` that
`Geometry.glue` and `FamilyGlueData` take (design step 7). -/
abbrev SmallDev.Carrier (N : SmallDev 𝔊 s₀) : Type u := N.toDev.carrier

/- **Universes** (design step 7), a check rather than a theorem: small developments and their
carriers have exactly the shape `Geometry.glue` asks (`ι : Type u`, `M : ι → Type u`), and so
does the type of the developments themselves only one level up (`Dev 𝔊 s₀ : Type (u+1)`). -/
example : Type u := SmallDev 𝔊 s₀
example : SmallDev 𝔊 s₀ → Type u := SmallDev.Carrier
example : Type (u+1) := Dev 𝔊 s₀

end Small

section SmallGeometry

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- **The small copy of a development**: its carrier transported onto its code set in `Set ℕ`
(`setNatHomeomorph`; the carrier is T0, being T2, and second countable, `Dev.sc`). -/
noncomputable def SmallDev.ofDev (N : Dev 𝔊.toPreGeometry s₀) : SmallDev 𝔊.toPreGeometry s₀ :=
  letI := setNatTop N.carrier
  let N' := N.transport (setNatHomeomorph N.carrier)
  { carrierSet := range (basisCode N.carrier)
    top := setNatTop N.carrier
    t2 := N'.t2
    conn := N'.conn
    sc := N'.sc
    str := N'.str
    emb := N'.emb
    isCauchyEmbedding := N'.isCauchyEmbedding
    isMor := N'.isMor }

/-- The development underlying the small copy is the transported development. -/
theorem SmallDev.toDev_ofDev (N : Dev 𝔊.toPreGeometry s₀) :
    (SmallDev.ofDev N).toDev =
      @Dev.transport _ _ _ _ N _ (setNatTop N.carrier) (setNatHomeomorph N.carrier) :=
  rfl

/-- **Every development is isomorphic to a small one** (design §3.6; Sbierski p. 21, « any GHD of
the same initial data is isometric to one in X »): mutually inverse morphisms of developments. -/
theorem SmallDev.exists_iso (N : Dev 𝔊.toPreGeometry s₀) :
    ∃ (N' : SmallDev 𝔊.toPreGeometry s₀) (f : N.carrier → N'.toDev.carrier)
      (g : N'.toDev.carrier → N.carrier),
      N.IsMorphism N'.toDev f ∧ N'.toDev.IsMorphism N g ∧ g ∘ f = id ∧ f ∘ g = id := by
  letI := setNatTop N.carrier
  refine ⟨SmallDev.ofDev N, setNatHomeomorph N.carrier, (setNatHomeomorph N.carrier).symm,
    ?_, ?_, ?_, ?_⟩
  · exact N.isMorphism_transport _
  · exact N.isMorphism_transport_symm _
  · exact funext (setNatHomeomorph N.carrier).symm_apply_apply
  · exact funext (setNatHomeomorph N.carrier).apply_symm_apply

/-- **Universality against small developments suffices** (Sbierski p. 21, « hence isometrically
embeds into M̃ »; the reduction package 10 needs): if every small development maps uniquely into
`Mbar`, every development does. -/
theorem Dev.isUniversal_of_small {Mbar : Dev 𝔊.toPreGeometry s₀}
    (h : ∀ N : SmallDev 𝔊.toPreGeometry s₀,
      ∃! f : N.toDev.carrier → Mbar.carrier, N.toDev.IsMorphism Mbar f) :
    Mbar.IsUniversal := by
  intro N
  obtain ⟨N', f, g, hf, hg, hgf, hfg⟩ := SmallDev.exists_iso N
  obtain ⟨k, hk, hkuniq⟩ := h N'
  refine ⟨k ∘ f, hk.comp hf, fun k' hk' => ?_⟩
  have : k' ∘ g = k := hkuniq _ (hk'.comp hg)
  rw [← this, comp_assoc, hgf, comp_id]

/-- Conversely, a universal development is universal against small ones. -/
theorem Dev.IsUniversal.small {Mbar : Dev 𝔊.toPreGeometry s₀} (h : Mbar.IsUniversal)
    (N : SmallDev 𝔊.toPreGeometry s₀) :
    ∃! f : N.toDev.carrier → Mbar.carrier, N.toDev.IsMorphism Mbar f :=
  h N.toDev

/-- **Universality is equivalent to universality against small developments.** -/
theorem Dev.isUniversal_iff_small {Mbar : Dev 𝔊.toPreGeometry s₀} :
    Mbar.IsUniversal ↔ ∀ N : SmallDev 𝔊.toPreGeometry s₀,
      ∃! f : N.toDev.carrier → Mbar.carrier, N.toDev.IsMorphism Mbar f :=
  ⟨fun h => h.small, Dev.isUniversal_of_small⟩

end SmallGeometry

end CBG

end Causal
