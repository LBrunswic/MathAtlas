import Benzecri.Structure.Quotient
import Benzecri.Projective.Convex

/-!
# `Benzecri.Structure.Classes` — segments, homogeneous, sweepable, divisible and maximal manifolds (Déf. 14, 15, 16)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal pp. 238–239; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45l (wave 3, layer L4; fix round after AUDIT-1 and DEC-122).

* **`bzdef:c1s1d14_segment_variete`** — `benzecri1960_ch1.tex:410` (Déf. 14, l.410–417, p. 238):
  `Benzecri.IsGXSegment` (any `(G, X)`, with the model's segments as a parameter), and the paper's
  two cases `Benzecri.IsProjSegment` (Déf. 7's CLOSED segment `(m, m')` of `S(n)`, endpoints not
  diametrically opposite) and `Benzecri.IsAffSegment` (Mathlib's `segment` of `ℝⁿ`). The endpoints
  lie in the segment (`IsGXSegment.left_mem`, `right_mem`), and the segments of the model are
  segments of the model manifold (`isProjSegment_closedSeg`, `isAffSegment_segment`).
* **`bzdef:c1s1d15_homogene_balayable_divisible`** — `benzecri1960_ch1.tex:419` (Déf. 15,
  l.419–427, p. 238): the group of automorphisms `Benzecri.GXAut G X V` (homeomorphisms which are
  morphisms both ways; every bijective morphism is one, `GXAut.ofBijective`), acting on `V`;
  `Benzecri.IsHomogeneous` (transitive), `Benzecri.IsBalayableFor` / `Benzecri.IsBalayable`
  (a compact « domaine générateur » `K` with `V = ⋃_{g ∈ G₁} gK`), `Benzecri.IsDivisible` (a
  subgroup, properly discontinuous, without fixed point, with compact quotient). The prose « Il est
  clair que toute variété divisible (ou homogène) est balayable » (l.436, p. 238):
  `IsHomogeneous.isBalayable`, `IsDivisible.isBalayable` (the latter for a locally compact `V`, true
  of every locally projective or affine manifold: `IsDivisible.isBalayable_proj`, `_aff`).
* **`bzdef:c1s1d16_maximale`** — `benzecri1960_ch1.tex:472` (Déf. 16, l.472–476, p. 239):
  `Benzecri.IsMaximal` (`V` connected; every morphism `V → U` into a connected Hausdorff
  `(G, X)`-manifold which is injective is onto); **the printed form** — `V` isomorphic to no open
  subset `W ≠ U`, `W` with its open-subset structure — is equivalent (`isMaximal_iff`, through
  `exists_opens_iso_iff`). The prose « Une variété compacte est évidemment maximale » (l.478):
  `isMaximal_of_compactSpace`.

> **Déf. 14.** Soit $V$ une variété localement projective (resp. affine). Une partie $S$ de $V$ est
> appelée *segments d'extrémités* les deux points $M$ et $N$ de $V$, s'il existe un voisinage
> ouvert $O$ de $S$, et une carte compatible $\varphi$ de $O$, telle que
> $\varphi(S)=(\varphi(M), \varphi(N))$ (sur la notion de segment, *cf.* déf. 7).
>
> **Déf. 15.** Une variété projective $V$ est dite *homogène*, si le groupe $G$ des automorphismes
> projectifs de $V$ opère transitivement dans $V$; elle est dite *balayable* (resp. balayable pour
> un sous-groupe $G_1\subset G$) s'il existe un compact $K\subset V$, appelé *domaine générateur*
> pour $G$ (resp. $G_1$), tel que $V=\bigcup_{g\in G} gK$ (resp. $V=\bigcup_{g\in G_1} gK$),
> $V$ est dit *divisible* s'il existe un sous-groupe $G_1$ de $G$, proprement discontinu, sans
> point fixe, et tel que $V/G_1$ soit compact.
>
> Dans la suite, nous étudierons les ouverts étalés $W$ au-dessus de $S(n)$, qui sont homogènes,
> divisibles ou balayables. Si $V$ est une variété localement projective et compacte, son
> revêtement universel est divisible.
>
> Il est clair que toute variété divisible (ou homogène) est balayable. […]
>
> **Déf. 16.** Une variété $V$ localement projective et connexe est dite *maximale* s'il n'existe
> pas de variété $U$ connexe localement projective, de même dimension que $V$, et telle que $V$
> soit isomorphe à un ouvert de $U$, distinct de $U$.
>
> Une variété compacte est évidemment maximale.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 14: `O` an open neighbourhood of `S`, `φ` a compatible chart of `O` | ✓ carried: `O = φ.source` (open), `S ⊆ φ.source`, `IsCompatibleChart G φ` (Déf. 13) |
| Déf. 14: `φ(M)`, `φ(N)` defined | ✓ carried: `M, N ∈ φ.source`; then `M, N ∈ S` follows (`left_mem`, `right_mem`) |
| Déf. 14: `(φ(M), φ(N))` the segment of Déf. 7 | ✓ carried: Déf. 7's notation `(m, m')` is the CLOSED segment (`)m, m'(` the open one), so `Sphere.closedSeg`, for `φ(M)`, `φ(N)` not diametrically opposite (Déf. 7's standing hypothesis); affine case: `segment ℝ` |
| Déf. 15: « le groupe $G$ des automorphismes projectifs » | ✓ carried: `GXAut G X V`, the invertible morphisms of the category of p. 238 (homeomorphisms that are morphisms both ways; any bijective morphism qualifies, `GXAut.ofBijective`) |
| Déf. 15: « opère transitivement » | ✓ carried: `MulAction.IsPretransitive` |
| Déf. 15: `K` compact, `V = ⋃ gK` | ✓ carried |
| Déf. 15: « proprement discontinu » | ✓ carried as Mathlib's `ProperlyDiscontinuousSMul` (DEC-120) |
| Déf. 15: « sans point fixe » | ✓ carried as `IsCancelSMul` (free action), as in `Structure/Quotient` |
| Déf. 15: « $V/G_1$ compact » | ✓ carried: `CompactSpace (MulAction.orbitRel.Quotient G₁ V)` with the quotient topology |
| prose: divisible ⇒ balayable | ✓ for `V` locally compact (`[LocallyCompactSpace V]`), automatic for every manifold modelled on `S(n)` or `ℝⁿ`; neither proper discontinuity nor freeness is used |
| Déf. 16: `V` connected | ✓ carried: `ConnectedSpace V` is part of `IsMaximal` |
| Déf. 16: `U` a « variété » connexe, localement projective, de même dimension | ✓ carried: `U` charted on the same model `X` (same dimension), `ConnectedSpace U`; « variété » read Hausdorff (`T2Space U`, ruled DEC-122); second countability of `U` not imposed and `U` ranging over the universe of `V` — the two definitions agree for second countable `V` (SCOPE) |
| Déf. 16: « isomorphe à un ouvert de $U$, distinct de $U$ » | ✓ carried as an injective morphism `f : V → U` with `range f ≠ univ`: an injective morphism is an open embedding (`IsGXMorphism.isOpenEmbedding_of_injective`), i.e. an isomorphism onto the open set `f(V)` |
| prose: compact ⇒ maximal | ✓ for `V` compact connected (`U` Hausdorff, as in the definition) |

## SCOPE (disclosed)

* **Readings, not findings**: « segments » (plural, l.411) is read « segment »; Déf. 7's closed
  segment is meant by `(φ(M), φ(N))` (checked on the scan, p. 238: round brackets, Déf. 7's notation
  for the closed segment); the chart is required to be defined at `M` and `N`.
* **Déf. 16, `U` Hausdorff (ruled, DEC-122: « Déf. 16's "compact ⇒ maximal" is read with U
  Hausdorff »)**: without it « une variété compacte est évidemment maximale » fails (the circle
  `S(1)` embeds as a proper open subset of the circle with one point doubled, a connected
  non-Hausdorff locally projective 1-manifold); the counterexample is described here and in
  REPORT, not formalized.
* **Déf. 16, second countability and universe of `U`** (audit AUDIT-1 minor, corrected).
  `IsMaximal` quantifies over connected Hausdorff `(G, X)`-manifolds `U` in the universe of `V`,
  with no countability. Dropping second countability ENLARGES the class of `U`, so `IsMaximal` is a
  priori STRONGER than the plan-F6 reading (`U` second countable); restricting `U` to `V`'s
  universe makes it a priori WEAKER. **For `V` second countable the definitions agree** (argument,
  not formalized): if `f : V → U` is an injective morphism with `f(V) ≠ U`, then `f(V)` is open
  and, `U` being connected, not closed; pick `u ∈ closure f(V) ∖ f(V)` and a connected chart ball
  `B'` at `u` (it meets `f(V)`); then `U' := f(V) ∪ B'` is an open, connected, Hausdorff, second
  countable sub-manifold of `U`, and `f : V → U'` is still injective and not onto (`u ∈ U'`).
  Moreover `|U'| ≤ |V| + 𝔠`, so `U'` is small in `V`'s universe and transports there. So a witness
  of non-maximality in either sense gives one in the other.
* **Not formalized** (prose): « Si $V$ est une variété localement projective et compacte, son
  revêtement universel est divisible » (l.432–433) — now its own ledger row
  `bzthm:c1s1_revetement_universel_divisible` (DEC-122), certified in `Benzecri.UniversalCoverRow`
  over the universal cover of `Benzecri.Port.UniversalCover` (T-bz-universal-cover); the conditions necessary
  for sweepability announced for later; the examples of p. 239 (the parabola, homogeneous not
  divisible; the plane minus the integer lattice; the classification in dimension 2).
* The identification of `GXAut G X V` with `CategoryTheory.Aut` of the bundled object of `GXCat`
  is not stated; `GXAut` is the group of invertible morphisms by construction (a homeomorphism is
  invertible in `GXCat` iff it and its inverse are morphisms; `IsGXMorphism.homeomorph_symm` shows
  the second condition is automatic).
* `GXAut G X V` is a type of this file (a `def` over a `Subgroup (V ≃ₜ V)`), so its `Group`,
  `MulAction`, `ContinuousConstSMul` and `FaithfulSMul` instances are global without being orphans.
* All definitions are stated for an arbitrary `(G, X)`; the paper's « variété projective » is
  `(GSR n, S n)`, its affine analogue `(GAR n, Fin n → ℝ)` (p. 238: « les énoncés équivalents du
  cas affin s'obtiennent en remplaçant $S(n)$ par $\R^n$ »).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Pointwise

namespace Benzecri

universe u v w y

/-! ### Déf. 14 — segments of a manifold -/

section Segment

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] [ChartedSpace X M]

variable (G) in
/-- **Déf. 14, for any `(G, X)`**: `S` is a segment of `M` with endpoints `P`, `Q` if some
compatible chart `φ` (Déf. 13), defined on an open neighbourhood `O = φ.source` of `S` and at
`P`, `Q`, maps `S` onto the segment `seg (φ P) (φ Q)` of the model, the endpoints being admissible
(`adm`; for `S(n)`, not diametrically opposite, as Déf. 7 requires). -/
def IsGXSegment (adm : X → X → Prop) (seg : X → X → Set X) (S : Set M) (P Q : M) : Prop :=
  ∃ φ : OpenPartialHomeomorph M X, IsCompatibleChart G φ ∧ S ⊆ φ.source ∧ P ∈ φ.source ∧
    Q ∈ φ.source ∧ adm (φ P) (φ Q) ∧ φ '' S = seg (φ P) (φ Q)

/-- The first endpoint lies in the segment (when the model's segments contain their endpoints). -/
theorem IsGXSegment.left_mem {adm : X → X → Prop} {seg : X → X → Set X}
    (hseg : ∀ a b, adm a b → a ∈ seg a b) {S : Set M} {P Q : M}
    (h : IsGXSegment G adm seg S P Q) : P ∈ S := by
  obtain ⟨φ, -, hS, hP, -, hadm, himg⟩ := h
  have : φ P ∈ φ '' S := himg ▸ hseg _ _ hadm
  obtain ⟨z, hz, hzP⟩ := this
  rwa [← φ.injOn (hS hz) hP hzP]

/-- The second endpoint lies in the segment. -/
theorem IsGXSegment.right_mem {adm : X → X → Prop} {seg : X → X → Set X}
    (hseg : ∀ a b, adm a b → b ∈ seg a b) {S : Set M} {P Q : M}
    (h : IsGXSegment G adm seg S P Q) : Q ∈ S := by
  obtain ⟨φ, -, hS, -, hQ, hadm, himg⟩ := h
  have : φ Q ∈ φ '' S := himg ▸ hseg _ _ hadm
  obtain ⟨z, hz, hzQ⟩ := this
  rwa [← φ.injOn (hS hz) hQ hzQ]

end Segment

section SegmentCases

variable {n : ℕ} {V : Type u} [TopologicalSpace V]

/-- **Déf. 14, projective case** (`bzdef:c1s1d14_segment_variete`): `S` is a segment of the locally
projective `V` with endpoints `P`, `Q` if a compatible chart `φ` of an open neighbourhood of `S`
maps `S` onto Déf. 7's closed segment `(φ(P), φ(Q))` of `S(n)`, `φ(P)`, `φ(Q)` not diametrically
opposite. -/
abbrev IsProjSegment (n : ℕ) [ChartedSpace (S n) V] (Sg : Set V) (P Q : V) : Prop :=
  IsGXSegment (GSR n) (fun a b : S n => b ≠ -a) Sphere.closedSeg Sg P Q

/-- **Déf. 14, affine case**: `φ(S)` is the closed segment `[φ(P), φ(Q)]` of `ℝⁿ`. -/
abbrev IsAffSegment (n : ℕ) [ChartedSpace (Fin n → ℝ) V] (Sg : Set V) (P Q : V) : Prop :=
  IsGXSegment (GAR n) (fun _ _ : Fin n → ℝ => True) (segment ℝ) Sg P Q

theorem IsProjSegment.left_mem [ChartedSpace (S n) V] {Sg : Set V} {P Q : V}
    (h : IsProjSegment n Sg P Q) : P ∈ Sg :=
  IsGXSegment.left_mem (fun a b _ => Sphere.left_mem_closedSeg a b) h

theorem IsProjSegment.right_mem [ChartedSpace (S n) V] {Sg : Set V} {P Q : V}
    (h : IsProjSegment n Sg P Q) : Q ∈ Sg :=
  IsGXSegment.right_mem (fun a b _ => Sphere.right_mem_closedSeg a b) h

theorem IsAffSegment.left_mem [ChartedSpace (Fin n → ℝ) V] {Sg : Set V} {P Q : V}
    (h : IsAffSegment n Sg P Q) : P ∈ Sg :=
  IsGXSegment.left_mem (fun a b _ => left_mem_segment ℝ a b) h

theorem IsAffSegment.right_mem [ChartedSpace (Fin n → ℝ) V] {Sg : Set V} {P Q : V}
    (h : IsAffSegment n Sg P Q) : Q ∈ Sg :=
  IsGXSegment.right_mem (fun a b _ => right_mem_segment ℝ a b) h

/-- The closed segments of `S(n)` (Déf. 7) are segments of the model manifold `S(n)` (Déf. 14). -/
theorem isProjSegment_closedSeg {a b : S n} (hab : b ≠ -a) :
    IsProjSegment n (Sphere.closedSeg a b) a b :=
  ⟨OpenPartialHomeomorph.refl _, isCompatibleChart_iff.2 (gxGroupoid _ _).id_mem_maximalAtlas,
    subset_univ _, mem_univ _, mem_univ _, hab, image_id _⟩

/-- The closed segments of `ℝⁿ` are segments of the model manifold `ℝⁿ` (Déf. 14). -/
theorem isAffSegment_segment (a b : Fin n → ℝ) : IsAffSegment n (segment ℝ a b) a b :=
  ⟨OpenPartialHomeomorph.refl _, isCompatibleChart_iff.2 (gxGroupoid _ _).id_mem_maximalAtlas,
    subset_univ _, mem_univ _, mem_univ _, trivial, image_id _⟩

end SegmentCases

/-! ### Two facts about morphisms: inverses of homeomorphisms, inclusions of open sets -/

section MorphismFacts

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type u} [TopologicalSpace M] [ChartedSpace X M] {N : Type y} [TopologicalSpace N]
  [ChartedSpace X N]

/-- **The inverse of a homeomorphism which is a morphism is a morphism.** -/
theorem IsGXMorphism.homeomorph_symm {e : M ≃ₜ N} (he : IsGXMorphism G X e) :
    IsGXMorphism G X e.symm := by
  refine ⟨e.symm.continuous, fun y => ?_⟩
  obtain ⟨g, hg⟩ := he.exists_smul_eq (e.symm y)
  refine ⟨g⁻¹, ?_⟩
  filter_upwards [(e.symm.continuous.tendsto y).eventually hg] with z hz
  rw [e.apply_symm_apply, e.apply_symm_apply] at hz
  rw [eq_inv_smul_iff, ← hz]

/-- **The inclusion of an open subset** (with Mathlib's charted space on `TopologicalSpace.Opens`)
is a morphism. -/
theorem isGXMorphism_opens_val (W : TopologicalSpace.Opens N) :
    IsGXMorphism G X (Subtype.val : W → N) :=
  ⟨continuous_subtype_val, fun _ => ⟨1, Eventually.of_forall fun _ => (one_smul G _).symm⟩⟩

end MorphismFacts

/-! ### Déf. 15 — the automorphism group; homogeneous, sweepable, divisible manifolds -/

section Aut

variable (G : Type w) (X : Type v) [TopologicalSpace X] [Group G] [MulAction G X]
  (M : Type u) [TopologicalSpace M] [ChartedSpace X M]

/-- The homeomorphisms of `M` which are morphisms (p. 238) together with their inverse. -/
def gxAutSubgroup : Subgroup (M ≃ₜ M) where
  carrier := {h | IsGXMorphism G X h ∧ IsGXMorphism G X h.symm}
  mul_mem' {_ _} hf hg := ⟨hf.1.comp hg.1, hg.2.comp hf.2⟩
  one_mem' := ⟨isGXMorphism_id, isGXMorphism_id⟩
  inv_mem' {_} hf := ⟨hf.2, hf.1⟩

/-- **The group of automorphisms of a `(G, X)`-manifold** (Déf. 15, « le groupe $G$ des
automorphismes projectifs de $V$ »; p. 238, « on définit les automorphismes »): the invertible
morphisms, i.e. the homeomorphisms `h` with `h` and `h⁻¹` morphisms. -/
def GXAut : Type u := gxAutSubgroup G X M

instance : Group (GXAut G X M) := inferInstanceAs (Group (gxAutSubgroup G X M))

variable {G X M}

namespace GXAut

/-- The underlying homeomorphism. -/
def toHomeomorph (f : GXAut G X M) : M ≃ₜ M := (show gxAutSubgroup G X M from f).1

instance : MulAction (GXAut G X M) M where
  smul f x := f.toHomeomorph x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_def (f : GXAut G X M) (x : M) : f • x = f.toHomeomorph x := rfl

@[simp] theorem toHomeomorph_mul (f g : GXAut G X M) :
    (f * g).toHomeomorph = g.toHomeomorph.trans f.toHomeomorph := rfl

@[simp] theorem toHomeomorph_inv (f : GXAut G X M) : f⁻¹.toHomeomorph = f.toHomeomorph.symm := rfl

/-- An automorphism is a morphism. -/
theorem isGXMorphism (f : GXAut G X M) : IsGXMorphism G X fun x : M => f • x :=
  (show gxAutSubgroup G X M from f).2.1

/-- Its inverse is a morphism. -/
theorem isGXMorphism_symm (f : GXAut G X M) : IsGXMorphism G X f.toHomeomorph.symm :=
  (show gxAutSubgroup G X M from f).2.2

instance : ContinuousConstSMul (GXAut G X M) M := ⟨fun f => f.toHomeomorph.continuous⟩

instance : FaithfulSMul (GXAut G X M) M :=
  ⟨fun h => Subtype.ext (Homeomorph.ext h)⟩

/-- **A bijective morphism is an automorphism** (an isomorphism of the category of p. 238): it is
a homeomorphism (a bijective local homeomorphism) and its inverse is a morphism. -/
def ofBijective [ContinuousConstSMul G X] {f : M → M} (hf : IsGXMorphism G X f)
    (hb : Function.Bijective f) : GXAut G X M :=
  let e : M ≃ₜ M := (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous
    hf.isLocalHomeomorph.isOpenMap
  show gxAutSubgroup G X M from ⟨e, hf, IsGXMorphism.homeomorph_symm (e := e) hf⟩

@[simp] theorem ofBijective_smul [ContinuousConstSMul G X] {f : M → M} (hf : IsGXMorphism G X f)
    (hb : Function.Bijective f) (x : M) : ofBijective hf hb • x = f x := rfl

end GXAut

variable (G X M)

/-- **Déf. 15, homogeneous**: the automorphism group operates transitively on `M`. -/
def IsHomogeneous : Prop := MulAction.IsPretransitive (GXAut G X M) M

/-- **Déf. 15, sweepable for a subgroup `G₁`** (« balayable pour un sous-groupe $G_1$ »): there is
a compact `K` (a « domaine générateur ») with `M = ⋃_{g ∈ G₁} gK`. -/
def IsBalayableFor (G₁ : Subgroup (GXAut G X M)) : Prop :=
  ∃ K : Set M, IsCompact K ∧ ⋃ g ∈ G₁, g • K = univ

/-- **Déf. 15, sweepable** (« balayable »): for the whole automorphism group. -/
def IsBalayable : Prop := IsBalayableFor G X M ⊤

/-- **Déf. 15, divisible**: some subgroup `G₁` of the automorphism group is properly
discontinuous (Mathlib's sense, DEC-120), without fixed point (a free action), and `M/G₁` is
compact. -/
def IsDivisible : Prop :=
  ∃ G₁ : Subgroup (GXAut G X M), ProperlyDiscontinuousSMul G₁ M ∧ IsCancelSMul G₁ M ∧
    CompactSpace (MulAction.orbitRel.Quotient G₁ M)

variable {G X M}

/-- Sweepable for a subgroup implies sweepable for any larger one. -/
theorem IsBalayableFor.mono {G₁ G₂ : Subgroup (GXAut G X M)} (h : IsBalayableFor G X M G₁)
    (h12 : G₁ ≤ G₂) : IsBalayableFor G X M G₂ := by
  obtain ⟨K, hK, hU⟩ := h
  refine ⟨K, hK, eq_univ_of_univ_subset (hU ▸ ?_)⟩
  exact iUnion₂_subset fun g hg => subset_biUnion_of_mem (u := fun g => g • K) (h12 hg)

theorem IsBalayableFor.isBalayable {G₁ : Subgroup (GXAut G X M)} (h : IsBalayableFor G X M G₁) :
    IsBalayable G X M :=
  h.mono le_top

/-- **« toute variété … homogène est balayable »** (p. 238): a single point is a generating
domain. -/
theorem IsHomogeneous.isBalayable (h : IsHomogeneous G X M) : IsBalayable G X M := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨∅, isCompact_empty, eq_univ_of_forall fun x => isEmptyElim x⟩
  refine ⟨{x₀}, isCompact_singleton, eq_univ_of_forall fun y => ?_⟩
  obtain ⟨g, hg⟩ := h.exists_smul_eq x₀ y
  exact mem_iUnion₂.2 ⟨g, Subgroup.mem_top g, by rw [smul_set_singleton, hg]; rfl⟩

/-- **« toute variété divisible … est balayable »** (p. 238), for a locally compact `M`: the
quotient by `G₁` is compact and the projection is open, so finitely many compact neighbourhoods
map onto it. -/
theorem IsDivisible.isBalayable [LocallyCompactSpace M] (h : IsDivisible G X M) :
    IsBalayable G X M := by
  obtain ⟨G₁, -, -, hQ⟩ := h
  haveI : ContinuousConstSMul G₁ M := ⟨fun g => continuous_const_smul (g : GXAut G X M)⟩
  set π : M → MulAction.orbitRel.Quotient G₁ M := Quotient.mk _ with hπ
  have hπo : IsOpenMap π := isOpenMap_quotient_mk'_mul
  choose K hK hKx using fun x : M => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => π '' interior (K x))
    (fun x => hπo _ isOpen_interior)
    (fun q _ => by
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
      exact mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hKx x), rfl⟩)
  refine IsBalayableFor.isBalayable (G₁ := G₁) ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hK x,
    eq_univ_of_forall fun y => ?_⟩
  obtain ⟨x, hxt, k, hk, hky⟩ := mem_iUnion₂.1 (ht (mem_univ (π y)))
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hky.symm)
  refine mem_iUnion₂.2 ⟨(γ : GXAut G X M), γ.2, ⟨k, mem_iUnion₂.2 ⟨x, hxt, interior_subset hk⟩, ?_⟩⟩
  exact hγ

/-- Divisible ⇒ sweepable, **for locally projective manifolds** (always locally compact). -/
theorem IsDivisible.isBalayable_proj {n : ℕ} {V : Type u} [TopologicalSpace V]
    [ChartedSpace (S n) V] (h : IsDivisible (GSR n) (S n) V) : IsBalayable (GSR n) (S n) V :=
  haveI := ChartedSpace.locallyCompactSpace (S n) V
  h.isBalayable

/-- Divisible ⇒ sweepable, **for locally affine manifolds** (always locally compact). -/
theorem IsDivisible.isBalayable_aff {n : ℕ} {V : Type u} [TopologicalSpace V]
    [ChartedSpace (Fin n → ℝ) V] (h : IsDivisible (GAR n) (Fin n → ℝ) V) :
    IsBalayable (GAR n) (Fin n → ℝ) V :=
  haveI := ChartedSpace.locallyCompactSpace (Fin n → ℝ) V
  h.isBalayable

end Aut

/-! ### Déf. 16 — maximal manifolds -/

section Maximal

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X]

/-- An injective morphism is an open embedding. -/
theorem IsGXMorphism.isOpenEmbedding_of_injective {M : Type u} [TopologicalSpace M]
    [ChartedSpace X M] {N : Type y} [TopologicalSpace N] [ChartedSpace X N] {f : M → N}
    (hf : IsGXMorphism G X f) (hi : Function.Injective f) : Topology.IsOpenEmbedding f :=
  hf.isLocalHomeomorph.isOpenEmbedding_of_injective hi

/-- **« $V$ isomorphe à un ouvert de $U$, distinct de $U$ »**, literally — an open set `W ≠ U` and
an isomorphism `M ≃ W` of `(G, X)`-manifolds (`W` with Mathlib's charted space on an open subset,
a homeomorphism which is a morphism both ways) — **is the same as an injective morphism `M → U`
which is not onto.** -/
theorem exists_opens_iso_iff {M : Type u} [TopologicalSpace M] [ChartedSpace X M] {N : Type y}
    [TopologicalSpace N] [ChartedSpace X N] :
    (∃ W : TopologicalSpace.Opens N, (W : Set N) ≠ univ ∧ ∃ h : M ≃ₜ W,
        IsGXMorphism G X h ∧ IsGXMorphism G X h.symm) ↔
      ∃ f : M → N, IsGXMorphism G X f ∧ Function.Injective f ∧ range f ≠ univ := by
  constructor
  · rintro ⟨W, hW, h, hh, -⟩
    refine ⟨Subtype.val ∘ h, (isGXMorphism_opens_val W).comp hh,
      Subtype.val_injective.comp h.injective, ?_⟩
    rwa [range_comp, h.surjective.range_eq, image_univ, Subtype.range_coe]
  · rintro ⟨f, hf, hi, hr⟩
    have he := hf.isOpenEmbedding_of_injective hi
    let W : TopologicalSpace.Opens N := ⟨range f, he.isOpen_range⟩
    let h : M ≃ₜ W := he.isEmbedding.toHomeomorph
    have hh : IsGXMorphism G X h := ⟨h.continuous, fun x => hf.exists_smul_eq x⟩
    exact ⟨W, hr, h, hh, hh.homeomorph_symm⟩

variable (G X) in
/-- **Déf. 16, maximal**: `M` is connected, and there is no connected (Hausdorff) `(G, X)`-manifold
`U` — same model, hence same dimension — with `M` isomorphic to an open subset of `U` distinct
from `U`: every injective morphism `M → U` is onto. -/
def IsMaximal (M : Type u) [TopologicalSpace M] [ChartedSpace X M] : Prop :=
  ConnectedSpace M ∧ ∀ (U : Type u) [TopologicalSpace U] [ChartedSpace X U]
    [HasGroupoid U (gxGroupoid G X)] [ConnectedSpace U] [T2Space U] (f : M → U),
    IsGXMorphism G X f → Function.Injective f → Function.Surjective f

/-- **Déf. 16, literally**: `M` is maximal iff it is connected and isomorphic to no open subset
`W ≠ U` of a connected Hausdorff `(G, X)`-manifold `U`. -/
theorem isMaximal_iff {M : Type u} [TopologicalSpace M] [ChartedSpace X M] :
    IsMaximal G X M ↔ ConnectedSpace M ∧ ∀ (U : Type u) [TopologicalSpace U] [ChartedSpace X U]
      [HasGroupoid U (gxGroupoid G X)] [ConnectedSpace U] [T2Space U],
      ¬ ∃ W : TopologicalSpace.Opens U, (W : Set U) ≠ univ ∧ ∃ h : M ≃ₜ W,
        IsGXMorphism G X h ∧ IsGXMorphism G X h.symm := by
  constructor
  · rintro ⟨hc, H⟩
    refine ⟨hc, fun U _ _ _ _ _ hex => ?_⟩
    obtain ⟨f, hf, hi, hr⟩ := exists_opens_iso_iff.1 hex
    exact hr (range_eq_univ.2 (H U f hf hi))
  · rintro ⟨hc, H⟩
    refine ⟨hc, fun U _ _ _ _ _ f hf hi => ?_⟩
    by_contra hs
    exact H U (exists_opens_iso_iff.2 ⟨f, hf, hi, fun h => hs (range_eq_univ.1 h)⟩)

/-- **« Une variété compacte est évidemment maximale »** (p. 239): a compact connected
`(G, X)`-manifold is maximal — the image of a morphism into a connected Hausdorff `U` is open
(local homeomorphism) and compact, hence closed, nonempty, hence all of `U`. -/
theorem isMaximal_of_compactSpace {M : Type u} [TopologicalSpace M] [ChartedSpace X M]
    [CompactSpace M] [ConnectedSpace M] : IsMaximal G X M := by
  refine ⟨inferInstance, fun U _ _ _ _ _ f hf _ => ?_⟩
  have hcl : IsClopen (range f) :=
    ⟨(isCompact_range hf.continuous).isClosed, hf.isLocalHomeomorph.isOpenMap.isOpen_range⟩
  exact range_eq_univ.1 (hcl.eq_univ (range_nonempty f))

end Maximal

end Benzecri
