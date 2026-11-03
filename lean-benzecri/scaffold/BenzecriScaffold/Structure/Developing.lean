import Benzecri.Structure.Jets
import Benzecri.Structure.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Germ

/-!
# `BenzecriScaffold.Structure.Developing` — the developing map of a simply connected manifold (Prop. 2)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal p. 237; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45k (wave 3, layer L4; fix round
after AUDIT-1).

* **`bzprop:c1s1p2_developpement`** — `benzecri1960_ch1.tex:357` (Prop. 2, l.357–369, p. 237).
  For a `(G,X)`-structure with `G` acting analytically (`IsAnalyticAction`) on a simply connected,
  locally path-connected `M`: **a map `p : M → X` all of whose jets lie in `J(V)` exists**
  (`exists_isDeveloping`); **it is unique up to left multiplication by an element of `G`**
  (`IsDeveloping.smul`, `IsDeveloping.existsUnique_smul_eq`); **`M` with `p` is an « ouvert
  étalé » over `X`**: `p` is a local homeomorphism, indeed a `(G,X)`-morphism into the model
  (`IsDeveloping.isLocalHomeomorph`, `isDeveloping_iff_isGXMorphism`). The paper's statement in one
  piece: `prop2_developpement`; for the paper's two cases, with « locally path connected » DERIVED
  from the charts (`locPathConnectedSpace_of_proj`, `locPathConnectedSpace_of_aff`), not assumed:
  `prop2_developpement_proj`, `prop2_developpement_aff`. The pointed form (one developing map
  through each jet of `J(V)`): `existsUnique_isDeveloping_jet`.
  Benzécri's proof is followed: `J(V) → V` is a covering (`isCoveringMap_jets`, Déf. 12, strict
  library); over the simply connected `V` the identity lifts to a continuous section through any jet
  (Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts`; « une composante connexe de $J(V)$
  est isomorphe à $V$ »), and the developing map is the value of the section's germ at its source
  (`developingOfSection`). Conversely every developing map is such a section
  (`IsDeveloping.jetSection`), so developing maps ↔ continuous sections of `J(V) → V`
  (`isDeveloping_iff_continuous_section`). The proof's « $J(V)$ … est topologiquement isomorphe au
  produit de la base $V$ par la fibre » is given set-theoretically: every jet of `J(V)` at `x` is
  `g • jet x p` for a unique `g` (`IsDeveloping.existsUnique_jetSMul_eq`).

Also, for the prose of p. 238 (no label): « Au revêtement universel de $V$, s'applique la
proposition 2 : il peut être muni d'une projection sur $S(n)$ qui est isomorphisme local des
structures projectives » — `exists_isGXMorphism_of_isCoveringMap`: on every simply connected,
locally path-connected covering of a `(G,X)`-manifold, with the pulled-back structure
(`Benzecri.pullbackChartedSpace`), there is a `(G,X)`-morphism to the model; for the paper's two
cases with local path-connectedness derived from the pulled-back charts:
`exists_isGXMorphism_of_isCoveringMap_proj`, `exists_isGXMorphism_of_isCoveringMap_aff`. The value
of a jet at its source is `Benzecri.Jet.value` (Mathlib's `Filter.Germ.value` of `Sigma.snd`).

> **Prop. 2.** Soit $V$ une variété localement projective (resp. affine) simplement connexe : il
> existe une application $p$ de $V$ dans $S(n)$ (resp. $\R^n$) dont tous les jets appartiennent à
> $J(V)$; $p$ est défini à une multiplication à gauche près par un élément de $GS(n, \R)$ [resp.
> $GA(n, \R)$]; $V$, muni de la projection $p$, est un ouvert étalé au-dessus de $S(n)$ (resp.
> $\R^n$).
>
> *Démonstration.* En effet, $J(V)$, revêtement d'une variété simplement connexe, est
> topologiquement isomorphe au produit de la base $V$ par la fibre $GS(n, \R)$ [resp.
> $GA(n, \R)$], munie de la topologie discrète. Une composante connexe, de $J(V)$ est isomorphe à
> $V$, et définit l'application $p$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` a « variété » (connected, Hausdorff, second countable; plan F6) | generalised: Hausdorff and second countable are not used; connectedness is implied by « simplement connexe » (Mathlib's `SimplyConnectedSpace` is path connected, hence nonempty) |
| `V` « simplement connexe » | ✓ carried: `[SimplyConnectedSpace M]` |
| `V` locally path connected (needed by the lifting theorem) | general `(G, X)`: an explicit hypothesis `[LocPathConnectedSpace M]`; the paper's two cases: DERIVED from the charted space over `S(n)` / `ℝⁿ` (`locPathConnectedSpace_of_proj`, `locPathConnectedSpace_of_aff`), so the instantiated statements carry no such hypothesis |
| `J(V)` the jets of the structure, a covering (Déf. 12) | ✓ carried: `jets G X M`, `isCoveringMap_jets` (strict library) |
| « dont tous les jets appartiennent à $J(V)$ » | ✓ carried: `IsDeveloping G p := ∀ x, jet x p ∈ jets G X M` |
| « défini à une multiplication à gauche près par un élément de $GS(n,\R)$ » | ✓ carried, both directions: `g • p` is developing, and any two developing maps differ by a UNIQUE `g` |
| « ouvert étalé au-dessus de $S(n)$ » (kb/0001: a local homeomorphism to the model) | ✓ carried: `IsLocalHomeomorph p`; also `IsGXMorphism G X p` |
| rigidity of `GS(n, ℝ)` / `GA(n, ℝ)` | ✓ carried: `[IsAnalyticAction G X]` (instances for `GSR n` and `GAR n` in the strict library) |

## SCOPE (disclosed)

* Everything is proved for an arbitrary `(G, X)` with an analytic action; the paper's two cases are
  the instances `prop2_developpement_proj` / `prop2_developpement_aff`.
* « $J(V)$ … est topologiquement isomorphe au produit $V \times G$ » (the proof, not the statement) is
  formalized as the bijection `(x, g) ↦ g • jet x p` (`IsDeveloping.existsUnique_jetSMul_eq`); the
  homeomorphism with `M × G` (`G` discrete) is not built — the statement does not need it.
* The universal covering itself is not constructed (Mathlib has none at this pin): the p. 238
  sentence is proved for any simply connected, locally path-connected covering.
* The étalé topology on jets is the strict library's SCOPED instance `Benzecri.etaleTopology`,
  active in `namespace Benzecri`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u v w

section General

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X]

/-- The value of a jet at its source (Mathlib's `Filter.Germ.value` of the germ, `Sigma.snd`). -/
def Jet.value (j : Jet M X) : X := j.2.value

omit [TopologicalSpace X] in
@[simp] theorem Jet.value_jet (x : M) (f : M → X) : Jet.value (jet x f) = f x := rfl

/-- A jet of `J(V)` is the jet of a maximal-atlas chart at its source. -/
theorem eq_jet_of_mem_jets [ChartedSpace X M] {j : Jet M X} (hj : j ∈ jets G X M) :
    ∃ e ∈ (gxGroupoid G X).maximalAtlas M, j.1 ∈ e.source ∧ j = jet j.1 e := by
  obtain ⟨x, γ⟩ := j
  obtain ⟨e, he, hx, hγ⟩ := hj
  simp only at hx hγ
  subst hγ
  exact ⟨e, he, hx, rfl⟩

variable (G) in
/-- **A developing map** (Prop. 2, « une application $p$ de $V$ dans $S(n)$ dont tous les jets
appartiennent à $J(V)$ »): every jet of `p` is a jet of the structure. -/
def IsDeveloping [ChartedSpace X M] (p : M → X) : Prop := ∀ x : M, jet x p ∈ jets G X M

variable [ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)]

/-- **A developing map is a `(G,X)`-morphism into the model**, and conversely: near every point it
is a translate of the chart there. -/
theorem isDeveloping_iff_isGXMorphism {p : M → X} : IsDeveloping G p ↔ IsGXMorphism G X p := by
  rw [isGXMorphism_iff_model]
  constructor
  · intro h
    have hev : ∀ x, ∃ g : G, ∀ᶠ y in 𝓝 x, p y = g • chartAt X x y := by
      intro x
      obtain ⟨e, he, hx, hγ⟩ := h x
      obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
        ((gxGroupoid G X).chart_mem_maximalAtlas x) he (mem_chart_source X x) hx
      have hpe : (e : M → X) =ᶠ[𝓝 x] p := Germ.coe_eq.1 hγ.symm
      exact ⟨g, by filter_upwards [hpe, hg] with y h1 h2; rw [← h1, h2]⟩
    refine ⟨continuous_iff_continuousAt.2 fun x => ?_, hev⟩
    obtain ⟨g, hg⟩ := hev x
    have hc : ContinuousAt (fun y => g • chartAt X x y) x :=
      (continuous_const_smul g).continuousAt.comp
        ((chartAt X x).continuousAt (mem_chart_source X x))
    exact hc.congr (hg.mono fun y hy => hy.symm)
  · rintro ⟨-, h⟩ x
    obtain ⟨g, hg⟩ := h x
    have hmem := jetSMul_jet_mem_jets (G := G) ((gxGroupoid G X).chart_mem_maximalAtlas x)
      (mem_chart_source X x) g
    rw [jetSMul_jet] at hmem
    convert hmem using 1
    exact jet_eq_jet_iff.2 hg

/-- A developing map is continuous. -/
theorem IsDeveloping.continuous {p : M → X} (hp : IsDeveloping G p) : Continuous p :=
  (isDeveloping_iff_isGXMorphism.1 hp).continuous

/-- **« $V$, muni de la projection $p$, est un ouvert étalé »**: a developing map is a local
homeomorphism. -/
theorem IsDeveloping.isLocalHomeomorph {p : M → X} (hp : IsDeveloping G p) :
    IsLocalHomeomorph p :=
  (isDeveloping_iff_isGXMorphism.1 hp).isLocalHomeomorph

/-- **Left multiplication**: `g ∘ p` is developing with `p`. -/
theorem IsDeveloping.smul {p : M → X} (hp : IsDeveloping G p) (g : G) :
    IsDeveloping G fun y => g • p y := fun x => by
  rw [← jetSMul_jet]
  exact (isJetStructure_jets (G := G) (X := X) (M := M)).smul_mem g _ (hp x)

section Rigid

variable [IsAnalyticAction G X]

/-- **Rigidity along a developing map**: if `g • p` and `h • p` agree near one point, `g = h`. -/
theorem IsDeveloping.eq_of_eventuallyEq {p : M → X} (hp : IsDeveloping G p) {g h : G} {x : M}
    (hgh : ∀ᶠ y in 𝓝 x, g • p y = h • p y) : g = h := by
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 hgh
  refine eq_of_eqOn (hp.isLocalHomeomorph.isOpenMap t hto) ⟨p x, mem_image_of_mem p hxt⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ht hy

omit [IsAnalyticAction G X] in
/-- Two developing maps agree near every point up to an element of `G`. -/
theorem IsDeveloping.exists_eventually_smul_eq {p p' : M → X} (hp : IsDeveloping G p)
    (hp' : IsDeveloping G p') (x : M) : ∃ g : G, ∀ᶠ y in 𝓝 x, p' y = g • p y := by
  obtain ⟨g, hg⟩ := (isJetStructure_jets (G := G) (X := X) (M := M)).transitive x _ _ (hp x)
    (hp' x)
  refine ⟨g, ?_⟩
  rw [Germ.map_coe] at hg
  exact Germ.coe_eq.1 hg

/-- **« $p$ est défini à une multiplication à gauche près par un élément de $G$ »**: on a
preconnected nonempty `M`, two developing maps differ by a unique `g ∈ G`. -/
theorem IsDeveloping.existsUnique_smul_eq [PreconnectedSpace M] [Nonempty M] {p p' : M → X}
    (hp : IsDeveloping G p) (hp' : IsDeveloping G p') : ∃! g : G, ∀ y, p' y = g • p y := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨g₀, hg₀⟩ := hp.exists_eventually_smul_eq hp' x₀
  let u : Set M := {y | ∀ᶠ z in 𝓝 y, p' z = g₀ • p z}
  let w : Set M := {y | ∃ g : G, g ≠ g₀ ∧ ∀ᶠ z in 𝓝 y, p' z = g • p z}
  have hu : IsOpen u := isOpen_setOf_eventually_nhds
  have hw : IsOpen w := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨g, hne, hg⟩
    filter_upwards [hg.eventually_nhds] with y' hy' using ⟨g, hne, hy'⟩
  have hcov : (univ : Set M) ⊆ u ∪ w := by
    intro y _
    obtain ⟨g, hg⟩ := hp.exists_eventually_smul_eq hp' y
    by_cases hgg : g = g₀
    · subst hgg; exact Or.inl hg
    · exact Or.inr ⟨g, hgg, hg⟩
  have hdisj : univ ∩ (u ∩ w) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨_, hyu, g, hne, hg⟩ => hne ?_
    exact hp.eq_of_eventuallyEq (x := y) (by
      filter_upwards [hyu, hg] with z h1 h2
      rw [← h1, ← h2])
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_univ u w hu hw hcov hdisj with
    hU | hW
  · refine ⟨g₀, fun y => (hU (mem_univ y)).self_of_nhds, fun g hg => ?_⟩
    refine (hp.eq_of_eventuallyEq (x := x₀) (Eventually.of_forall fun z => ?_))
    rw [← hg z, (hU (mem_univ z)).self_of_nhds]
  · have : x₀ ∈ univ ∩ (u ∩ w) := ⟨mem_univ _, hg₀, hW (mem_univ x₀)⟩
    rw [hdisj] at this
    exact this.elim

/-- **The proof's « $J(V)$ est isomorphe au produit $V \times G$ », set-theoretically**: given a
developing map `p`, every jet of `J(V)` at `x` is `g • jet x p` for a unique `g`. -/
theorem IsDeveloping.existsUnique_jetSMul_eq {p : M → X} (hp : IsDeveloping G p) (x : M)
    (γ : Germ (𝓝 x) X) :
    (⟨x, γ⟩ : Jet M X) ∈ jets G X M ↔ ∃! g : G, (⟨x, γ⟩ : Jet M X) = jetSMul g (jet x p) := by
  constructor
  · intro hj
    obtain ⟨g, hg⟩ := (isJetStructure_jets (G := G) (X := X) (M := M)).transitive x _ γ (hp x) hj
    refine ⟨g, ?_, fun g' hg' => ?_⟩
    · rw [hg]; rfl
    · have h1 : jetSMul g (jet x p) = jetSMul g' (jet x p) := by
        rw [← hg', hg]; rfl
      rw [jetSMul_jet, jetSMul_jet, jet_eq_jet_iff] at h1
      exact (hp.eq_of_eventuallyEq h1).symm
  · rintro ⟨g, hg, -⟩
    rw [hg]
    exact (isJetStructure_jets (G := G) (X := X) (M := M)).smul_mem g _ (hp x)

end Rigid

/-! ### Developing maps and sections of `J(V) → V` -/

section Sections

/-- **The developing map of a section** `σ` of `J(V) → V`: the value of the germ `σ(x)` at its
source (« une composante connexe de $J(V)$ … définit l'application $p$ »). -/
def developingOfSection (σ : M → jets G X M) (x : M) : X := Jet.value (σ x).1

omit [HasGroupoid M (gxGroupoid G X)] in
/-- **A continuous section of `J(V) → V` defines a developing map, whose jets are the section.** -/
theorem jet_developingOfSection {σ : M → jets G X M} (hσ : Continuous σ)
    (hsec : ∀ x, (σ x).1.1 = x) (x : M) : jet x (developingOfSection σ) = (σ x).1 := by
  obtain ⟨e, he, hx, hje⟩ := eq_jet_of_mem_jets (σ x).2
  rw [hsec] at hx hje
  have hB : IsOpen (Subtype.val ⁻¹' ((fun y => jet y e) '' e.source) : Set (jets G X M)) :=
    (isOpen_etaleBasic _ e.open_source).preimage continuous_subtype_val
  have hxB : σ x ∈ Subtype.val ⁻¹' ((fun y => jet y e) '' e.source) := ⟨x, hx, hje.symm⟩
  have hev : ∀ᶠ y in 𝓝 x, developingOfSection σ y = e y := by
    filter_upwards [hσ.continuousAt.preimage_mem_nhds (hB.mem_nhds hxB)] with y hy
    obtain ⟨z, -, hz⟩ := hy
    have hzy : z = y := by
      have := congrArg Sigma.fst hz
      rw [hsec] at this
      exact this
    subst hzy
    rw [developingOfSection, ← hz, Jet.value_jet]
  rw [hje]
  exact jet_eq_jet_iff.2 hev

omit [HasGroupoid M (gxGroupoid G X)] in
theorem isDeveloping_developingOfSection {σ : M → jets G X M} (hσ : Continuous σ)
    (hsec : ∀ x, (σ x).1.1 = x) : IsDeveloping G (developingOfSection σ) := fun x => by
  rw [jet_developingOfSection hσ hsec x]
  exact (σ x).2

/-- **The section of a developing map**: `x ↦ jet x p`. -/
def IsDeveloping.jetSection {p : M → X} (hp : IsDeveloping G p) (x : M) : jets G X M :=
  ⟨jet x p, hp x⟩

omit [HasGroupoid M (gxGroupoid G X)] in
theorem IsDeveloping.continuous_jetSection {p : M → X} (hp : IsDeveloping G p) :
    Continuous hp.jetSection :=
  (continuous_jet p).subtype_mk _

omit [HasGroupoid M (gxGroupoid G X)] in
/-- **Developing maps are exactly the continuous sections of `J(V) → V`**: `p` is developing iff
`x ↦ jet x p` is a continuous section with values in `J(V)`. -/
theorem isDeveloping_iff_continuous_section {p : M → X} :
    IsDeveloping G p ↔ ∃ σ : M → jets G X M, Continuous σ ∧ (∀ x, (σ x).1.1 = x) ∧
      ∀ x, (σ x).1 = jet x p := by
  refine ⟨fun hp => ⟨hp.jetSection, hp.continuous_jetSection, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  rintro ⟨σ, -, -, h⟩ x
  rw [← h]
  exact (σ x).2

end Sections

/-! ### Prop. 2 -/

section Prop2

variable [IsAnalyticAction G X] [SimplyConnectedSpace M] [LocPathConnectedSpace M]

/-- **Prop. 2, existence, through any given jet**: on a simply connected, locally path-connected
`(G,X)`-manifold, for every jet `j₀ ∈ J(V)` at `x₀` there is a developing map whose jet at `x₀` is
`j₀` (Benzécri's proof: lift the identity of `V` through the covering `J(V) → V`). -/
theorem exists_isDeveloping_jet {x₀ : M} {γ₀ : Germ (𝓝 x₀) X}
    (h₀ : (⟨x₀, γ₀⟩ : Jet M X) ∈ jets G X M) :
    ∃ p : M → X, IsDeveloping G p ∧ jet x₀ p = ⟨x₀, γ₀⟩ := by
  obtain ⟨σ, ⟨hσ₀, hσ⟩, -⟩ := (isCoveringMap_jets M X G).existsUnique_continuousMap_lifts
    (ContinuousMap.id M) x₀ ⟨⟨x₀, γ₀⟩, h₀⟩ rfl
  have hsec : ∀ x, (σ x).1.1 = x := fun x => congrFun hσ x
  refine ⟨developingOfSection σ, isDeveloping_developingOfSection σ.continuous hsec, ?_⟩
  rw [jet_developingOfSection σ.continuous hsec, hσ₀]

/-- **Prop. 2, existence**: a simply connected, locally path-connected `(G,X)`-manifold has a
developing map. -/
theorem exists_isDeveloping : ∃ p : M → X, IsDeveloping G p := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨p, hp, -⟩ := exists_isDeveloping_jet (G := G)
    (jet_mem_jets ((gxGroupoid G X).chart_mem_maximalAtlas x₀) (mem_chart_source X x₀))
  exact ⟨p, hp⟩

/-- **Prop. 2, pointed form**: the developing map with a given jet `j₀ ∈ J(V)` at `x₀` is unique. -/
theorem existsUnique_isDeveloping_jet {x₀ : M} {γ₀ : Germ (𝓝 x₀) X}
    (h₀ : (⟨x₀, γ₀⟩ : Jet M X) ∈ jets G X M) :
    ∃! p : M → X, IsDeveloping G p ∧ jet x₀ p = ⟨x₀, γ₀⟩ := by
  obtain ⟨p, hp, hp₀⟩ := exists_isDeveloping_jet h₀
  refine ⟨p, ⟨hp, hp₀⟩, fun p' ⟨hp', hp'₀⟩ => ?_⟩
  obtain ⟨g, hg, -⟩ := hp.existsUnique_smul_eq hp'
  have hev : ∀ᶠ y in 𝓝 x₀, p' y = p y := jet_eq_jet_iff.1 (hp'₀.trans hp₀.symm)
  have hg1 : g = 1 := hp.eq_of_eventuallyEq (x := x₀) (by
    filter_upwards [hev] with y hy
    rw [← hg y, hy, one_smul])
  funext y
  rw [hg y, hg1, one_smul]

/-- **Prop. 2** (`bzprop:c1s1p2_developpement`), for an arbitrary analytic `(G,X)`: on a simply
connected, locally path-connected `(G,X)`-manifold `M`
1. there is a map `p : M → X` all of whose jets belong to `J(V)`;
2. `p` is determined up to left multiplication by an element of `G`: every `g • p` is again such a
   map, and any two such maps differ by a unique `g`;
3. `M` with `p` is an « ouvert étalé » over `X`: `p` is a local homeomorphism (indeed a
   `(G,X)`-morphism into the model). -/
theorem prop2_developpement :
    (∃ p : M → X, IsDeveloping G p) ∧
    (∀ p : M → X, IsDeveloping G p → ∀ g : G, IsDeveloping G fun y => g • p y) ∧
    (∀ p p' : M → X, IsDeveloping G p → IsDeveloping G p' → ∃! g : G, ∀ y, p' y = g • p y) ∧
    (∀ p : M → X, IsDeveloping G p → IsLocalHomeomorph p ∧ IsGXMorphism G X p) :=
  ⟨exists_isDeveloping, fun _ hp g => hp.smul g, fun _ _ hp hp' => hp.existsUnique_smul_eq hp',
    fun _ hp => ⟨hp.isLocalHomeomorph, isDeveloping_iff_isGXMorphism.1 hp⟩⟩

end Prop2

/-! ### p. 238: the developing map of a simply connected covering -/

/-- **p. 238, « Au revêtement universel de $V$, s'applique la proposition 2 »**: every simply
connected, locally path-connected covering `M̃ → M` of a `(G,X)`-manifold, with its pulled-back
structure, has a `(G,X)`-morphism to the model, unique up to `G`. -/
theorem exists_isGXMorphism_of_isCoveringMap [IsAnalyticAction G X] {N : Type*}
    [TopologicalSpace N] [SimplyConnectedSpace N] [LocPathConnectedSpace N] {π : N → M}
    (hπ : IsCoveringMap π) :
    letI := pullbackChartedSpace (X := X) hπ.isLocalHomeomorph
    ∃ p : N → X, IsGXMorphism G X p ∧ IsLocalHomeomorph p ∧
      ∀ p' : N → X, IsGXMorphism G X p' → ∃! g : G, ∀ y, p' y = g • p y := by
  letI := pullbackChartedSpace (X := X) hπ.isLocalHomeomorph
  haveI := hasGroupoid_pullback (G := G) (X := X) hπ.isLocalHomeomorph
  obtain ⟨p, hp⟩ := exists_isDeveloping (G := G) (X := X) (M := N)
  exact ⟨p, isDeveloping_iff_isGXMorphism.1 hp, hp.isLocalHomeomorph, fun p' hp' =>
    hp.existsUnique_smul_eq (isDeveloping_iff_isGXMorphism.2 hp')⟩

end General

/-! ### The paper's two cases -/

section Instances

variable {n : ℕ} {V : Type u} [TopologicalSpace V]

/-- `ℝⁿ⁺¹ ∖ 0` is locally path connected. -/
theorem locPathConnectedSpace_nonzero (n : ℕ) :
    LocPathConnectedSpace {v : Fin n → ℝ // v ≠ 0} :=
  (isOpen_compl_singleton (x := (0 : Fin n → ℝ))).locPathConnectedSpace

/-- **`S(n)` is locally path connected** (a quotient of `ℝⁿ⁺¹ ∖ 0`). -/
theorem locPathConnectedSpace_S (n : ℕ) : LocPathConnectedSpace (S n) :=
  haveI := locPathConnectedSpace_nonzero (n + 1)
  Sphere.isQuotientMap_s.locPathConnectedSpace

/-- A locally projective manifold is locally path connected. -/
theorem locPathConnectedSpace_of_proj [ChartedSpace (S n) V] : LocPathConnectedSpace V :=
  haveI := locPathConnectedSpace_S n
  ChartedSpace.locPathConnectedSpace (S n) V

/-- A locally affine manifold is locally path connected. -/
theorem locPathConnectedSpace_of_aff [ChartedSpace (Fin n → ℝ) V] : LocPathConnectedSpace V :=
  ChartedSpace.locPathConnectedSpace (Fin n → ℝ) V

/-- **Prop. 2, projective case** (`bzprop:c1s1p2_developpement`): a simply connected locally
projective `n`-manifold `V` has a map `p : V → S(n)` all of whose jets are projective jets, unique
up to left multiplication by an element of `GS(n, ℝ)`, and `V` with `p` is an ouvert étalé over
`S(n)`. -/
theorem prop2_developpement_proj [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [SimplyConnectedSpace V] :
    (∃ p : V → S n, IsDeveloping (GSR n) p) ∧
    (∀ p : V → S n, IsDeveloping (GSR n) p → ∀ g : GSR n, IsDeveloping (GSR n) fun y => g • p y) ∧
    (∀ p p' : V → S n, IsDeveloping (GSR n) p → IsDeveloping (GSR n) p' →
      ∃! g : GSR n, ∀ y, p' y = g • p y) ∧
    (∀ p : V → S n, IsDeveloping (GSR n) p → IsLocalHomeomorph p ∧ IsGXMorphism (GSR n) (S n) p) :=
  haveI := locPathConnectedSpace_of_proj (n := n) (V := V)
  prop2_developpement

/-- **Prop. 2, affine case** (`bzprop:c1s1p2_developpement`): a simply connected locally affine
`n`-manifold `V` has a map `p : V → ℝⁿ` all of whose jets are affine jets, unique up to left
multiplication by an element of `GA(n, ℝ)`, and `V` with `p` is an ouvert étalé over `ℝⁿ`. -/
theorem prop2_developpement_aff [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [SimplyConnectedSpace V] :
    (∃ p : V → (Fin n → ℝ), IsDeveloping (GAR n) p) ∧
    (∀ p : V → (Fin n → ℝ), IsDeveloping (GAR n) p → ∀ g : GAR n,
      IsDeveloping (GAR n) fun y => g • p y) ∧
    (∀ p p' : V → (Fin n → ℝ), IsDeveloping (GAR n) p → IsDeveloping (GAR n) p' →
      ∃! g : GAR n, ∀ y, p' y = g • p y) ∧
    (∀ p : V → (Fin n → ℝ), IsDeveloping (GAR n) p →
      IsLocalHomeomorph p ∧ IsGXMorphism (GAR n) (Fin n → ℝ) p) :=
  haveI := locPathConnectedSpace_of_aff (n := n) (V := V)
  prop2_developpement

/-- **p. 238, projective case**: every simply connected covering `N → V` of a locally projective
manifold, with the pulled-back structure, has a projective morphism `N → S(n)`, unique up to
`GS(n, ℝ)`. Local path-connectedness of `N` is derived from the pulled-back charts. -/
theorem exists_isGXMorphism_of_isCoveringMap_proj [ChartedSpace (S n) V]
    [HasGroupoid V (projGroupoid n)] {N : Type*} [TopologicalSpace N] [SimplyConnectedSpace N]
    {π : N → V} (hπ : IsCoveringMap π) :
    letI := pullbackChartedSpace (X := S n) hπ.isLocalHomeomorph
    ∃ p : N → S n, IsGXMorphism (GSR n) (S n) p ∧ IsLocalHomeomorph p ∧
      ∀ p' : N → S n, IsGXMorphism (GSR n) (S n) p' → ∃! g : GSR n, ∀ y, p' y = g • p y := by
  letI := pullbackChartedSpace (X := S n) hπ.isLocalHomeomorph
  haveI := locPathConnectedSpace_of_proj (n := n) (V := N)
  exact exists_isGXMorphism_of_isCoveringMap hπ

/-- **p. 238, affine case**: every simply connected covering `N → V` of a locally affine manifold,
with the pulled-back structure, has an affine morphism `N → ℝⁿ`, unique up to `GA(n, ℝ)`. -/
theorem exists_isGXMorphism_of_isCoveringMap_aff [ChartedSpace (Fin n → ℝ) V]
    [HasGroupoid V (affGroupoid n)] {N : Type*} [TopologicalSpace N] [SimplyConnectedSpace N]
    {π : N → V} (hπ : IsCoveringMap π) :
    letI := pullbackChartedSpace (X := Fin n → ℝ) hπ.isLocalHomeomorph
    ∃ p : N → (Fin n → ℝ), IsGXMorphism (GAR n) (Fin n → ℝ) p ∧ IsLocalHomeomorph p ∧
      ∀ p' : N → (Fin n → ℝ), IsGXMorphism (GAR n) (Fin n → ℝ) p' →
        ∃! g : GAR n, ∀ y, p' y = g • p y := by
  letI := pullbackChartedSpace (X := Fin n → ℝ) hπ.isLocalHomeomorph
  haveI := locPathConnectedSpace_of_aff (n := n) (V := N)
  exact exists_isGXMorphism_of_isCoveringMap hπ

end Instances


end Benzecri
