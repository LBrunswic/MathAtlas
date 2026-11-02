import Causal.PushoutCausal
import Mathlib.Topology.Gluing

/-!
# Gluing a family of spaces along open embeddings with the cocycle condition

No paper label is certified by this file (package WP-36d-CBGFamilyGluing, design
`docs/CBG-DESIGN.md` §3 step 7 / package 8). It is the model-free topological and causal
infrastructure of Sbierski's proof of Theorem 2.8 (`papers/gx/sources/1309.7591`, §3.3) and of
the "inductive limit" of ETT `theo:CBG` (`ETT.tex:2335`) and of Brunswic's thesis
(`papers/gx/sources/thesis/these.tex:6313`, "la famille des extensions de Cauchy de `M_0` est
filtrante à droite et donc admet une limite inductive").

> We denote the MCGHD of `M_{α_i}` and `M_{α_k}` with `U_{α_i α_k} ⊆ M_{α_i}` and the corresponding
> isometric embedding with `ψ_{α_i α_k} : U_{α_i α_k} → M_{α_k}`. We define an equivalence relation
> `∼` on `⊔_{α∈A} M_α` by `M_{α_i} ∋ p_{α_i} ∼ q_{α_k} ∈ M_{α_k}` iff `p_{α_i} ∈ U_{α_i α_k}` and
> `ψ_{α_i α_k}(p_{α_i}) = q_{α_k}` (3.15) and take the quotient `(⊔ M_α)/∼ =: M̃` with the quotient
> topology. […] For the transitivity observe that if `p_{α_i} ∼ p_{α_k}` and `p_{α_k} ∼ p_{α_l}`,
> then `U_{α_i α_k} ∩ ψ⁻¹_{α_i α_k}(U_{α_k α_l})` together with the composition
> `ψ_{α_k α_l} ∘ ψ_{α_i α_k}` is a CGHD of `M_{α_i}` and `M_{α_l}` […] so certainly the MCGHD of
> `M_{α_i}` and `M_{α_l}` leads to the same identification.
> 1. `M̃` is Hausdorff: […] it is easy to check that the map `π ∘ j_{ik}` descends to the quotient,
> i.e. to `j̃_{ik}`. […] `j̃_{ik}` is open as well. Since `j̃_{ik}` is also continuous and injective,
> it is a homeomorphism onto its image. In Theorem 2.7 we proved that the quotient topology on
> `(M_{α_i} ⊔ M_{α_k})/∼` is Hausdorff - thus we can find open neighbourhoods that separate
> `[p_{α_i}]` and `[q_{α_k}]` […]. Pushing forward these neighbourhoods to `(⊔ M_α)/∼` via
> `j̃_{ik}` we obtain separating open neighbourhoods. (Sbierski, proof of Thm 2.8, p. 22)

* `FamilyGlueData I M`: spaces `M i`, open sets `U i j ⊆ M i`, continuous transitions
  `φ i j : U i j → M j` landing in `U j i`, `U i i = ⊤`, `φ i i = id`, and the cocycle condition
  in Sbierski's form (`cocycle`: `x ∈ U i j`, `φ i j x ∈ U j k` ⟹ `x ∈ U i k` and
  `φ j k (φ i j x) = φ i k x`). The inverse law `φ_φ` and mathlib's `t_inter` form `mem_U_of_mem`
  are derived.
* `Glued D = (Σ i, M i)/∼` (`Rel`, an equivalence relation: `equivalence_rel`), the maps
  `ι i : M i → Glued D`; `ι_eq_ι_iff` (the relation is (3.15) exactly), `injective_ι`,
  `isOpenEmbedding_ι`, `isOpenMap_proj`, `isOpen_iff`, `iUnion_range_ι`;
  the universal property `desc`, `desc_ι`, `eq_desc`, `continuous_desc`.
* The pair gluings: `PairGluing D i j = Gluing (↑) (φ i j)` (the two-space `Causal.Gluing` of
  `M i` and `M j` along `U i j`), `pair i j : PairGluing D i j → Glued D` (Sbierski's `j̃_{ik}`),
  an open embedding (`isOpenEmbedding_pair`).
* **The Hausdorff criterion** `t2Space_iff`: `Glued D` is T2 iff every pair gluing is; with T2
  pieces, iff every `Cdist` is empty (`t2Space_iff_Cdist_eq_empty`, from
  `Gluing.t2Space_iff_Cdist_eq_empty`) iff every graph is closed (`t2Space_iff_isClosed_graph`).
* Second countability: `secondCountableTopology` for `I` countable and every `M i` second
  countable.
* The glued causality: `CompatibleAlong D C` (each transition is an isomorphism of causalities,
  `Gluing.CompatibleAlong` of `Causal.PushoutCausal` for every pair), `causality D C` (generated
  by the transported pieces), `isGluedCausality_causality` (it restricts to every `C i`),
  `exists_isGluedCausality_iff` (a causality restricting to every `C i` exists iff
  `CompatibleAlong`), `causality_absolutelyMinimal` (absolutely minimal when every `C i` is),
  uniqueness among absolutely minimal ones (`IsGluedCausality.unique`,
  `eq_causality_of_isGluedCausality`), `strongMorphism_ι`, `localIsomorphism_ι`; model-free:
  `Causality.absolutelyMinimalOn_pushLocal_extend` (a causality transported along an open embedding
  is absolutely minimal on the image when it is), `Causality.pullback_le_lt_iff_of_injective`
  (along an injective continuous map the pullback reads the relations on the image).
* Witnesses that the hypotheses are inhabited (kb/0011): `ofOpens V` (open subsets of one space
  glued along their intersections), Hausdorff when the space is (`t2Space_ofOpens`), with
  `CompatibleAlong` for the causalities pulled back from one causality on the space
  (`compatibleAlong_ofOpens`, `isGluedCausality_ofOpens`); `const I X` (copies of `X` glued
  identically), `compatibleAlong_const`, and `const_timelikeLine` (absolutely minimal pieces: the
  glued causality of copies of the timelike line is absolutely minimal and every `ι i` is a local
  isomorphism).
* `ofMkCore`: mathlib's `TopCat.GlueData.MkCore` yields a `FamilyGlueData` with the same data.

## Hypothesis checklist

| Sbierski Thm 2.8 / ETT `theo:CBG` gluing | here |
|---|---|
| a set-indexed family of GHDs, `U_{ik}` the MCGHDs, `ψ_{ik}` isometric embeddings | ⚠ weakened: any index type `I`, any topological spaces, `U i j` open, `φ i j` continuous with continuous inverse `φ j i` (the topological content of an injective structure morphism) |
| (3.15) is an equivalence relation (transitivity from maximality of the MCGHD) | ✓ carried: transitivity is the field `cocycle`; reflexivity is `U_self`, `φ_self`; symmetry is `φ_mem` with the derived inverse law `φ_φ` (`cocycle` at `k = i` plus `φ_self`). `φ_mem` (`φ i j` lands in `U j i`, hence with `φ_φ` `U j i = φ i j (U i j)`) is the symmetry of the MCGHD (`U_{ki} = ψ_{ik}(U_{ik})`), which Sbierski uses without stating it; package 10 must supply it |
| Hausdorffness of `M̃` from Theorem 2.7 (pairs) | ✓ proved as an equivalence (`t2Space_iff`); no separation axiom on the pieces |
| second countability of `M̃` (Geroch) | ⚠ strengthened (added hypotheses `[Countable I]` and second-countable pieces; this is not Sbierski's point 5): Sbierski's `A` is uncountable and he uses Geroch's theorem, which is a geometry fact (design §1, `rem:CBG_manquant` (i)) |
| the structure (metric, `𝕄≥0`-charts) of `M̃` | not here: the design's `Geometry.glue` (package 1) |
| causalities of the pieces compatible along the `U i j` | ✓ carried: `CompatibleAlong` (necessary and sufficient, `exists_isGluedCausality_iff`) |

## SCOPE (disclosed)

* **Why not mathlib's `TopCat.GlueData`.** It is stated in `TopCat.{u}` (index type and all pieces
  in one universe, morphisms as bundled continuous maps, the overlaps as pullbacks), and its
  conclusions are categorical (`ι` as a colimit cocone). The CBG proof glues developments
  `M i : Type u` indexed by a set of a possibly different universe, wants the gluing as an
  ordinary quotient whose relation is literally Sbierski's (3.15), and compares it with the
  two-space `Causal.Gluing` already carrying the Hausdorff analysis (`Causal.Pushout`). So the
  structure here is `TopCat.GlueData.MkCore`'s data, unbundled, over `Σ i, M i`, with
  `Quot` as in `Causal.Pushout`. The cocycle field is Sbierski's form; it is equivalent to
  `MkCore`'s pair `t_inter` + `cocycle` (`mem_U_of_mem` gives `t_inter`; `MkCore.cocycle` is
  `cocycle` read at `j, i, k`), so an `MkCore` with the same data yields a `FamilyGlueData`
  (`ofMkCore`, formalized). The converse (a `FamilyGlueData` in one universe as an `MkCore`) is
  not formalized.
* `secondCountableTopology` needs `I` countable. The index of the CBG construction (design step 7,
  package 10: the small developments `SmallDev M₀`) is not countable in general, so this theorem does not give
  the second countability of the maximal extension; that stays a geometry fact (Geroch,
  `rem:CBG_manquant` (i), DEC-49).
* The glued causality is the generated one (`theo:causalite_engendre`), minimal among those
  restricting to the `C i` (`lem:union_causalite`). Uniqueness is proved only among absolutely
  minimal causalities (`IsGluedCausality.unique`, `eq_causality_of_isGluedCausality`; kb/0014);
  nothing is stated without absolute minimality.
* "Strong morphism" and "local isomorphism" are those of `Causal.Morphism`, under its readings.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v w

/-! ### A model-free lemma: transport preserves absolute minimality -/

/-- A causality transported along an open embedding `e` (`Causality.pushLocal`, extended to `Z`)
is absolutely minimal on `e(X)` when the causality is absolutely minimal. -/
theorem Causality.absolutelyMinimalOn_pushLocal_extend {X : Type u} [TopologicalSpace X]
    {Z : Type w} [TopologicalSpace Z] (C : Causality X) {e : X → Z} (he : IsOpenEmbedding e)
    (h : C.AbsolutelyMinimal) :
    (C.pushLocal he).extend.AbsolutelyMinimalOn ⟨range e, he.isOpen_range⟩ := by
  rw [Precausality.absolutelyMinimal_iff] at h
  intro S hS V hV a b
  let S' : Set (Opens X) := (fun O => preimageOpens he.continuous O) '' S
  have hS' : ∀ x ∈ (⊤ : Opens X), ∃ O ∈ S', x ∈ O := by
    intro x _
    obtain ⟨O, hO, hx⟩ := hS (e x) ⟨x, rfl⟩
    exact ⟨_, ⟨O, hO, rfl⟩, hx⟩
  have hinf : ∀ O : Opens Z, preimageOpens he.continuous (V ⊓ O) =
      preimageOpens he.continuous V ⊓ preimageOpens he.continuous O := fun _ => rfl
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [LocalCausality.extend_le_iff hV] at hab
    obtain ⟨x, y, rfl, rfl, hxy⟩ := hab
    refine Relation.TransGen.lift e ?_ ((h S' hS' _ le_top x y).1 hxy)
    rintro c d ⟨_, ⟨O, hO, rfl⟩, hcd⟩
    refine ⟨O, hO, ?_⟩
    rw [LocalCausality.extend_le_iff (inf_le_left.trans hV), C.pushLocal_le_iff he, hinf]
    exact hcd
  · rw [LocalCausality.extend_lt_iff hV] at hab
    obtain ⟨x, y, rfl, rfl, hxy⟩ := hab
    refine Relation.TransGen.lift e ?_ ((h S' hS' _ le_top x y).2 hxy)
    rintro c d ⟨_, ⟨O, hO, rfl⟩, hcd⟩
    refine ⟨O, hO, ?_⟩
    rw [LocalCausality.extend_lt_iff (inf_le_left.trans hV), C.pushLocal_lt_iff he, hinf]
    exact hcd

/-- Along an injective continuous map `e`, the pulled-back causality (`Causality.pullback`) reads
the relations of `C` on the image: for `U = e(V)`, `x ≤_V y` iff `e x ≤_U e y`, and likewise for
`≪`. -/
theorem Causality.pullback_le_lt_iff_of_injective {X : Type u} [TopologicalSpace X]
    {Z : Type w} [TopologicalSpace Z] (C : Causality Z) {e : X → Z} (hc : Continuous e)
    (hi : Injective e) {V : Opens X} {U : Opens Z} (hU : (U : Set Z) = e '' V) (x y : X) :
    ((C.pullback hc).le V x y ↔ C.le U (e x) (e y)) ∧
      ((C.pullback hc).lt V x y ↔ C.lt U (e x) (e y)) := by
  have hmem : ∀ {a : X}, e a ∈ U → a ∈ V := fun {a} ha => by
    rw [← SetLike.mem_coe, hU] at ha
    obtain ⟨b, hb, e'⟩ := ha
    exact hi e' ▸ hb
  refine ⟨⟨?_, fun h => ?_⟩, ⟨PullLink.transGen_imp C.isRelFamily_lt hU, fun h => ?_⟩⟩
  · rintro (⟨rfl, hx⟩ | h)
    · exact C.le_refl (by rw [← SetLike.mem_coe, hU]; exact mem_image_of_mem _ hx)
    · exact PullLink.transGen_imp C.isRelFamily_le hU h
  · exact Or.inr (Relation.TransGen.single ⟨V, le_rfl, hi.injOn, hmem (C.le_mem_left h),
      hmem (C.le_mem_right h), U, hU, h⟩)
  · exact Relation.TransGen.single ⟨V, le_rfl, hi.injOn, hmem (C.lt_mem_left h),
      hmem (C.lt_mem_right h), U, hU, h⟩

namespace CBG

/-- **Glue data for a family**: spaces `M i`, open sets `U i j ⊆ M i` (the part of `M i` glued
to `M j`), continuous transitions `φ i j : U i j → M j` with values in `U j i`, `U i i = ⊤`,
`φ i i = id`, and the cocycle condition in Sbierski's form (the transitivity of (3.15)). -/
structure FamilyGlueData (I : Type v) (M : I → Type u) [∀ i, TopologicalSpace (M i)] where
  /-- The open subset of `M i` glued to `M j`. -/
  U : ∀ i : I, I → Opens (M i)
  /-- The transition from `U i j` to `M j`. -/
  φ : ∀ i j : I, U i j → M j
  continuous_φ : ∀ i j, Continuous (φ i j)
  /-- `φ i j` lands in `U j i` (with `φ_φ`, `U j i = φ i j (U i j)`): the symmetry of the MCGHD,
  implicit in Sbierski; it gives the symmetry of (3.15). -/
  φ_mem : ∀ i j (x : U i j), φ i j x ∈ U j i
  U_self : ∀ i, U i i = ⊤
  φ_self : ∀ i (x : U i i), φ i i x = x
  cocycle : ∀ i j k (x : U i j) (h : φ i j x ∈ U j k),
    ∃ hx : (x : M i) ∈ U i k, φ j k ⟨φ i j x, h⟩ = φ i k ⟨x, hx⟩

namespace FamilyGlueData

variable {I : Type v} {M : I → Type u} [∀ i, TopologicalSpace (M i)] (D : FamilyGlueData I M)

theorem mem_U_self (i : I) (x : M i) : x ∈ D.U i i := by
  rw [D.U_self]; trivial

/-- The transition `U i j → U j i`. -/
def t (i j : I) (x : D.U i j) : D.U j i := ⟨D.φ i j x, D.φ_mem i j x⟩

@[simp] theorem coe_t (i j : I) (x : D.U i j) : (D.t i j x : M j) = D.φ i j x := rfl

/-- The inverse law, from the cocycle condition at `k = i`. -/
theorem φ_φ (i j : I) (x : D.U i j) : D.φ j i ⟨D.φ i j x, D.φ_mem i j x⟩ = x := by
  obtain ⟨hx, e⟩ := D.cocycle i j i x (D.φ_mem i j x)
  rw [e, D.φ_self]

theorem t_t (i j : I) (x : D.U i j) : D.t j i (D.t i j x) = x :=
  Subtype.ext (D.φ_φ i j x)

theorem continuous_t (i j : I) : Continuous (D.t i j) :=
  (D.continuous_φ i j).subtype_mk _

/-- The transition `U i j ≃ₜ U j i`. -/
def tHomeo (i j : I) : D.U i j ≃ₜ D.U j i where
  toFun := D.t i j
  invFun := D.t j i
  left_inv := D.t_t i j
  right_inv := D.t_t j i
  continuous_toFun := D.continuous_t i j
  continuous_invFun := D.continuous_t j i

/-- Mathlib's `t_inter` form of the cocycle condition. -/
theorem mem_U_of_mem (i j k : I) (x : D.U i j) (hx : (x : M i) ∈ D.U i k) :
    D.φ i j x ∈ D.U j k := by
  have h : D.φ j i ⟨D.φ i j x, D.φ_mem i j x⟩ ∈ D.U i k := by rw [D.φ_φ]; exact hx
  exact (D.cocycle j i k ⟨D.φ i j x, D.φ_mem i j x⟩ h).1

theorem φ_eq_comp (i j : I) : (D.φ i j : D.U i j → M j) = Subtype.val ∘ D.t i j := rfl

theorem isOpenEmbedding_φ (i j : I) : IsOpenEmbedding (D.φ i j) :=
  (D.U j i).isOpen.isOpenEmbedding_subtypeVal.comp (D.tHomeo i j).isOpenEmbedding

theorem injective_φ (i j : I) : Injective (D.φ i j) := (D.isOpenEmbedding_φ i j).injective

/-! ### The glued space -/

/-- Sbierski's relation (3.15) on `Σ i, M i`. -/
def Rel (a b : Σ i, M i) : Prop :=
  ∃ h : a.2 ∈ D.U a.1 b.1, D.φ a.1 b.1 ⟨a.2, h⟩ = b.2

theorem equivalence_rel : Equivalence D.Rel where
  refl a := ⟨D.mem_U_self a.1 a.2, D.φ_self _ _⟩
  symm := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨h, e⟩
    dsimp only at h e
    subst e
    exact ⟨D.φ_mem i j ⟨x, h⟩, D.φ_φ i j ⟨x, h⟩⟩
  trans := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨h, e⟩ ⟨h', e'⟩
    dsimp only at h e h' e'
    subst e e'
    obtain ⟨hx, e⟩ := D.cocycle i j k ⟨x, h⟩ h'
    exact ⟨hx, e.symm⟩

/-- The glued space `(Σ i, M i)/∼`, with the quotient topology. -/
def Glued : Type (max u v) := Quot D.Rel

instance : TopologicalSpace D.Glued := inferInstanceAs (TopologicalSpace (Quot _))

/-- The projection `π : Σ i, M i → Glued D`. -/
def proj (a : Σ i, M i) : D.Glued := Quot.mk _ a

/-- The map `M i → Glued D`. -/
def ι (i : I) (x : M i) : D.Glued := D.proj ⟨i, x⟩

theorem proj_eq_proj_iff {a b : Σ i, M i} : D.proj a = D.proj b ↔ D.Rel a b :=
  ⟨fun h => D.equivalence_rel.eqvGen_iff.1 (Quot.eqvGen_exact h), Quot.sound⟩

/-- Two points are identified iff the relation (3.15) holds. -/
theorem ι_eq_ι_iff {i j : I} {x : M i} {y : M j} :
    D.ι i x = D.ι j y ↔ ∃ h : x ∈ D.U i j, D.φ i j ⟨x, h⟩ = y :=
  D.proj_eq_proj_iff

theorem ι_φ (i j : I) (x : D.U i j) : D.ι j (D.φ i j x) = D.ι i x :=
  (D.ι_eq_ι_iff.2 ⟨x.2, rfl⟩).symm

theorem injective_ι (i : I) : Injective (D.ι i) := by
  intro x x' h
  obtain ⟨hx, e⟩ := D.ι_eq_ι_iff.1 h
  rw [← e, D.φ_self]

theorem exists_ι (z : D.Glued) : ∃ i x, D.ι i x = z := by
  induction z using Quot.ind with
  | mk a =>
    obtain ⟨i, x⟩ := a
    exact ⟨i, x, rfl⟩

theorem iUnion_range_ι : ⋃ i, range (D.ι i) = univ :=
  eq_univ_of_forall fun z => by
    obtain ⟨i, x, rfl⟩ := D.exists_ι z
    exact mem_iUnion.2 ⟨i, x, rfl⟩

theorem preimage_ι_image_ι (i j : I) (A : Set (M i)) :
    D.ι j ⁻¹' (D.ι i '' A) = D.φ i j '' (Subtype.val ⁻¹' A) := by
  ext y
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨hU, rfl⟩ := D.ι_eq_ι_iff.1 h
    exact ⟨⟨x, hU⟩, hx, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (D.ι_φ i j w).symm⟩

/-! ### The universal property -/

section desc

variable {Z : Type w}

/-- A family of maps agreeing along the transitions descends to the gluing. -/
def desc (g : ∀ i, M i → Z) (hg : ∀ i j (x : D.U i j), g j (D.φ i j x) = g i x) :
    D.Glued → Z :=
  Quot.lift (fun a => g a.1 a.2) (by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨h, e⟩
    dsimp only at h e
    subst e
    exact (hg i j ⟨x, h⟩).symm)

variable {D} {g : ∀ i, M i → Z} {hg : ∀ i j (x : D.U i j), g j (D.φ i j x) = g i x}

@[simp] theorem desc_ι (i : I) (x : M i) : D.desc g hg (D.ι i x) = g i x := rfl

/-- Uniqueness in the universal property. -/
theorem eq_desc {f : D.Glued → Z} (hf : ∀ i x, f (D.ι i x) = g i x) : f = D.desc g hg := by
  funext z
  obtain ⟨i, x, rfl⟩ := D.exists_ι z
  exact hf i x

/-- The universal property: maps agreeing along the transitions factor uniquely. -/
theorem existsUnique_desc (g : ∀ i, M i → Z) (hg : ∀ i j (x : D.U i j), g j (D.φ i j x) = g i x) :
    ∃! f : D.Glued → Z, ∀ i x, f (D.ι i x) = g i x :=
  ⟨D.desc g hg, fun _ _ => rfl, fun _ hf => eq_desc hf⟩

end desc

/-! ### The quotient topology -/

variable {D} in
theorem continuous_proj : Continuous D.proj := continuous_quot_mk

theorem continuous_ι (i : I) : Continuous (D.ι i) := continuous_proj.comp continuous_sigmaMk

theorem isOpen_iff {s : Set D.Glued} : IsOpen s ↔ ∀ i, IsOpen (D.ι i ⁻¹' s) :=
  (isQuotientMap_quot_mk.isOpen_preimage (s := s)).symm.trans isOpen_sigma_iff

theorem continuous_desc {Z : Type w} [TopologicalSpace Z] {g : ∀ i, M i → Z}
    {hg : ∀ i j (x : D.U i j), g j (D.φ i j x) = g i x} (hc : ∀ i, Continuous (g i)) :
    Continuous (D.desc g hg) :=
  continuous_quot_lift _ (continuous_sigma hc)

theorem isOpenMap_ι (i : I) : IsOpenMap (D.ι i) := fun A hA => by
  rw [isOpen_iff]
  intro j
  rw [preimage_ι_image_ι]
  exact (D.isOpenEmbedding_φ i j).isOpenMap _ (hA.preimage continuous_subtype_val)

/-- Each `M i` is an open subspace of the gluing. -/
theorem isOpenEmbedding_ι (i : I) : IsOpenEmbedding (D.ι i) :=
  .of_continuous_injective_isOpenMap (D.continuous_ι i) (D.injective_ι i) (D.isOpenMap_ι i)

theorem isOpenMap_proj : IsOpenMap D.proj := fun S hS => by
  have : D.proj '' S = ⋃ i, D.ι i '' (Sigma.mk i ⁻¹' S) := by
    ext z
    simp only [mem_image, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨⟨i, x⟩, hx, rfl⟩
      exact ⟨i, x, hx, rfl⟩
    · rintro ⟨i, x, hx, rfl⟩
      exact ⟨⟨i, x⟩, hx, rfl⟩
  rw [this]
  exact isOpen_iUnion fun i => D.isOpenMap_ι i _ (isOpen_sigma_iff.1 hS i)

/-- **Second countability**: a countable gluing of second-countable spaces is second
countable. -/
theorem secondCountableTopology [Countable I] [∀ i, SecondCountableTopology (M i)] :
    SecondCountableTopology D.Glued :=
  isQuotientMap_quot_mk.secondCountableTopology D.isOpenMap_proj

/-! ### The pair gluings and the Hausdorff criterion -/

/-- The two-space gluing (`Causal.Gluing`) of `M i` and `M j` along `U i j`. -/
abbrev PairGluing (i j : I) : Type u := Gluing (Subtype.val : D.U i j → M i) (D.φ i j)

theorem isOpenEmbedding_val (i j : I) : IsOpenEmbedding (Subtype.val : D.U i j → M i) :=
  (D.U i j).isOpen.isOpenEmbedding_subtypeVal

/-- Sbierski's `j̃_{ik}`: the pair gluing maps into the gluing of the family. -/
def pair (i j : I) : D.PairGluing i j → D.Glued :=
  Gluing.desc (D.ι i) (D.ι j) fun w => (D.ι_φ i j w).symm

@[simp] theorem pair_ι₁ (i j : I) (x : M i) :
    D.pair i j (Gluing.ι₁ _ _ x) = D.ι i x := rfl

@[simp] theorem pair_ι₂ (i j : I) (y : M j) :
    D.pair i j (Gluing.ι₂ _ _ y) = D.ι j y := rfl

theorem continuous_pair (i j : I) : Continuous (D.pair i j) :=
  Gluing.continuous_desc (D.continuous_ι i) (D.continuous_ι j)

theorem injective_pair (i j : I) : Injective (D.pair i j) := by
  have h₁ : Injective (Subtype.val : D.U i j → M i) := Subtype.val_injective
  have h₂ := D.injective_φ i j
  intro z z' h
  rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;>
    rcases Gluing.exists_ι z' with ⟨x', rfl⟩ | ⟨y', rfl⟩
  · rw [pair_ι₁, pair_ι₁] at h
    rw [D.injective_ι i h]
  · rw [pair_ι₁, pair_ι₂] at h
    obtain ⟨hx, rfl⟩ := D.ι_eq_ι_iff.1 h
    exact (Gluing.ι₁_eq_ι₂_iff h₁ h₂).2 ⟨⟨x, hx⟩, rfl, rfl⟩
  · rw [pair_ι₂, pair_ι₁] at h
    obtain ⟨hx, rfl⟩ := D.ι_eq_ι_iff.1 h.symm
    exact ((Gluing.ι₁_eq_ι₂_iff h₁ h₂).2 ⟨⟨x', hx⟩, rfl, rfl⟩).symm
  · rw [pair_ι₂, pair_ι₂] at h
    rw [D.injective_ι j h]

theorem isOpenMap_pair (i j : I) : IsOpenMap (D.pair i j) := fun S hS => by
  have hS' := Gluing.isOpen_iff.1 hS
  have : D.pair i j '' S = D.ι i '' (Gluing.ι₁ _ _ ⁻¹' S) ∪ D.ι j '' (Gluing.ι₂ _ _ ⁻¹' S) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases Gluing.exists_ι w with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · exact Or.inl ⟨x, hw, rfl⟩
      · exact Or.inr ⟨y, hw, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact ⟨_, hx, rfl⟩
      · exact ⟨_, hy, rfl⟩
  rw [this]
  exact (D.isOpenMap_ι i _ hS'.1).union (D.isOpenMap_ι j _ hS'.2)

/-- The pair gluing is an open subspace of the gluing of the family. -/
theorem isOpenEmbedding_pair (i j : I) : IsOpenEmbedding (D.pair i j) :=
  .of_continuous_injective_isOpenMap (D.continuous_pair i j) (D.injective_pair i j)
    (D.isOpenMap_pair i j)

/-- **The Hausdorff criterion**: the gluing of the family is Hausdorff iff every pair gluing is.
No separation axiom on the pieces. -/
theorem t2Space_iff : T2Space D.Glued ↔ ∀ i j, T2Space (D.PairGluing i j) := by
  constructor
  · intro _ i j
    exact (D.isOpenEmbedding_pair i j).isEmbedding.t2Space
  · intro h
    rw [t2Space_iff_disjoint_nhds]
    intro z z' hzz'
    obtain ⟨i, x, rfl⟩ := D.exists_ι z
    obtain ⟨j, y, rfl⟩ := D.exists_ι z'
    have he := D.isOpenEmbedding_pair i j
    rw [← D.pair_ι₁ i j x, ← D.pair_ι₂ i j y] at hzz' ⊢
    rw [← he.map_nhds_eq, ← he.map_nhds_eq, disjoint_map he.injective]
    exact disjoint_nhds_nhds.2 fun h' => hzz' (congrArg _ h')

/-- With Hausdorff pieces: the gluing is Hausdorff iff no pair `(p, q) ∈ M i × M j` of distinct
non-separated points exists, for every `i, j` (`rem:non_separe_cas`, read as `Cdist`). -/
theorem t2Space_iff_Cdist_eq_empty [∀ i, T2Space (M i)] :
    T2Space D.Glued ↔ ∀ i j, Gluing.Cdist (Subtype.val : D.U i j → M i) (D.φ i j) = ∅ := by
  rw [t2Space_iff]
  exact forall_congr' fun i => forall_congr' fun j =>
    Gluing.t2Space_iff_Cdist_eq_empty (D.isOpenEmbedding_val i j) (D.isOpenEmbedding_φ i j)

/-- With Hausdorff pieces: the gluing is Hausdorff iff the graph of every transition is closed in
`M i × M j`. -/
theorem t2Space_iff_isClosed_graph [∀ i, T2Space (M i)] :
    T2Space D.Glued ↔ ∀ i j, IsClosed (Gluing.graph (Subtype.val : D.U i j → M i) (D.φ i j)) := by
  rw [t2Space_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Gluing.t2Space_iff (D.isOpenEmbedding_val i j) (D.isOpenEmbedding_φ i j)]
  exact ⟨fun h => h.2.2, fun h => ⟨inferInstance, inferInstance, h⟩⟩

/-! ### The glued causality -/

section CausalityGluing

variable {D}

/-- The causalities `C i` agree along the transitions: for every `i, j`, `φ i j` is an isomorphism
of causalities from `U i j` onto `U j i` (`Gluing.CompatibleAlong` of `Causal.PushoutCausal`). -/
def CompatibleAlong (D : FamilyGlueData I M) (C : ∀ i, Causality (M i)) : Prop :=
  ∀ i j, Gluing.CompatibleAlong (Subtype.val : D.U i j → M i) (D.φ i j) (C i) (C j)

variable (D) in
/-- The open set `ι i (M i)` of the gluing. -/
def O (i : I) : Opens D.Glued := ⟨range (D.ι i), (D.isOpenEmbedding_ι i).isOpen_range⟩

theorem mem_O (z : D.Glued) : ∃ i, z ∈ D.O i := by
  obtain ⟨i, x, rfl⟩ := D.exists_ι z
  exact ⟨i, x, rfl⟩

variable (D) in
/-- The transported causalities, as causalities on the gluing. -/
def pieces (C : ∀ i, Causality (M i)) (i : I) : Causality D.Glued :=
  ((C i).pushLocal (D.isOpenEmbedding_ι i)).extend

variable (D) in
/-- **The causality of the gluing**: the one generated (`theo:causalite_engendre`) by `C i` on
`ι i (M i)`. -/
def causality (C : ∀ i, Causality (M i)) : Causality D.Glued :=
  Causality.generated D.O mem_O (D.pieces C)

/-- The trace on `M i` of an open subset of `ι i (M i) ∩ ι j (M j)` lies in `U i j`. -/
theorem preimage_ι_subset {i j : I} {V : Opens D.Glued} (hV : V ≤ D.O j) :
    (preimageOpens (D.continuous_ι i) V : Set (M i)) ⊆ range (Subtype.val : D.U i j → M i) := by
  intro x hx
  obtain ⟨y, hy⟩ : D.ι i x ∈ range (D.ι j) := hV hx
  obtain ⟨h, -⟩ := D.ι_eq_ι_iff.1 hy.symm
  exact ⟨⟨x, h⟩, rfl⟩

theorem preimage_ι_subset_range_φ {i j : I} {V : Opens D.Glued} (hV : V ≤ D.O i) :
    (preimageOpens (D.continuous_ι j) V : Set (M j)) ⊆ range (D.φ i j) := by
  intro y hy
  obtain ⟨x, hx⟩ : D.ι j y ∈ range (D.ι i) := hV hy
  obtain ⟨h, e⟩ := D.ι_eq_ι_iff.1 hx
  exact ⟨⟨x, h⟩, e⟩

theorem preimage_val_eq (i j : I) (V : Opens D.Glued) :
    (Subtype.val : D.U i j → M i) ⁻¹' (preimageOpens (D.continuous_ι i) V : Set (M i)) =
      D.φ i j ⁻¹' (preimageOpens (D.continuous_ι j) V : Set (M j)) := by
  ext w
  simp only [coe_preimageOpens, mem_preimage, D.ι_φ]

/-- The overlap, one direction: a relation transported from `M i` on an open subset of
`ι i (M i) ∩ ι j (M j)` is the one transported from `M j`. -/
theorem overlap_imp {r : ∀ i, Opens (M i) → M i → M i → Prop}
    (hr : ∀ {i V x y}, r i V x y → x ∈ V ∧ y ∈ V)
    (hc : ∀ i j (V₁ : Opens (M i)) (V₂ : Opens (M j)),
      (V₁ : Set (M i)) ⊆ range (Subtype.val : D.U i j → M i) → (V₂ : Set (M j)) ⊆ range (D.φ i j) →
      (Subtype.val : D.U i j → M i) ⁻¹' V₁ = D.φ i j ⁻¹' V₂ → ∀ u u' : D.U i j,
        (r i V₁ u u' ↔ r j V₂ (D.φ i j u) (D.φ i j u')))
    {i j : I} {V : Opens D.Glued} (hi : V ≤ D.O i) (hj : V ≤ D.O j) {a b : D.Glued}
    (h : ∃ x y, D.ι i x = a ∧ D.ι i y = b ∧ r i (preimageOpens (D.continuous_ι i) V) x y) :
    ∃ x y, D.ι j x = a ∧ D.ι j y = b ∧ r j (preimageOpens (D.continuous_ι j) V) x y := by
  obtain ⟨x, y, rfl, rfl, hxy⟩ := h
  have hc' := hc i j _ _ (preimage_ι_subset hj) (preimage_ι_subset_range_φ hi)
    (D.preimage_val_eq i j V)
  obtain ⟨u, rfl⟩ := preimage_ι_subset hj (hr hxy).1
  obtain ⟨u', rfl⟩ := preimage_ι_subset hj (hr hxy).2
  exact ⟨D.φ i j u, D.φ i j u', D.ι_φ i j u, D.ι_φ i j u', (hc' u u').1 hxy⟩

theorem compatible_pieces {C : ∀ i, Causality (M i)} (hC : CompatibleAlong D C) :
    Precausality.Compatible D.O fun i => (D.pieces C i).toPrecausality := by
  have hle : ∀ i j (V₁ : Opens (M i)) (V₂ : Opens (M j)),
      (V₁ : Set (M i)) ⊆ range (Subtype.val : D.U i j → M i) → (V₂ : Set (M j)) ⊆ range (D.φ i j) →
      (Subtype.val : D.U i j → M i) ⁻¹' V₁ = D.φ i j ⁻¹' V₂ → ∀ u u' : D.U i j,
        ((C i).le V₁ u u' ↔ (C j).le V₂ (D.φ i j u) (D.φ i j u')) :=
    fun i j V₁ V₂ h₁ h₂ h u u' => (hC i j V₁ V₂ h₁ h₂ h u u').1
  have hlt : ∀ i j (V₁ : Opens (M i)) (V₂ : Opens (M j)),
      (V₁ : Set (M i)) ⊆ range (Subtype.val : D.U i j → M i) → (V₂ : Set (M j)) ⊆ range (D.φ i j) →
      (Subtype.val : D.U i j → M i) ⁻¹' V₁ = D.φ i j ⁻¹' V₂ → ∀ u u' : D.U i j,
        ((C i).lt V₁ u u' ↔ (C j).lt V₂ (D.φ i j u) (D.φ i j u')) :=
    fun i j V₁ V₂ h₁ h₂ h u u' => (hC i j V₁ V₂ h₁ h₂ h u u').2
  have mle : ∀ {i V x y}, (C i).le V x y → x ∈ V ∧ y ∈ V :=
    fun h => ⟨(C _).le_mem_left h, (C _).le_mem_right h⟩
  have mlt : ∀ {i V x y}, (C i).lt V x y → x ∈ V ∧ y ∈ V :=
    fun h => ⟨(C _).lt_mem_left h, (C _).lt_mem_right h⟩
  intro i j V hV a b
  have hi : V ≤ D.O i := hV.trans inf_le_left
  have hj : V ≤ D.O j := hV.trans inf_le_right
  refine ⟨(LocalCausality.extend_le_iff (L := (C i).pushLocal (D.isOpenEmbedding_ι i)) hi).trans
    (Iff.trans ?_
      (LocalCausality.extend_le_iff (L := (C j).pushLocal (D.isOpenEmbedding_ι j)) hj).symm),
    (LocalCausality.extend_lt_iff (L := (C i).pushLocal (D.isOpenEmbedding_ι i)) hi).trans
    (Iff.trans ?_
      (LocalCausality.extend_lt_iff (L := (C j).pushLocal (D.isOpenEmbedding_ι j)) hj).symm)⟩
  · exact ⟨overlap_imp (r := fun i => (C i).le) mle hle hi hj,
      overlap_imp (r := fun i => (C i).le) mle hle hj hi⟩
  · exact ⟨overlap_imp (r := fun i => (C i).lt) mlt hlt hi hj,
      overlap_imp (r := fun i => (C i).lt) mlt hlt hj hi⟩

variable {C : ∀ i, Causality (M i)}

theorem causality_le_ι (hC : CompatibleAlong D C) {i : I} {V : Opens D.Glued} (hV : V ≤ D.O i)
    {x y : M i} :
    (D.causality C).le V (D.ι i x) (D.ι i y) ↔
      (C i).le (preimageOpens (D.continuous_ι i) V) x y :=
  (Precausality.generated_le_iff (hU := mem_O) (compatible_pieces hC) (i := i) hV).trans
    ((LocalCausality.extend_le_iff (L := (C i).pushLocal (D.isOpenEmbedding_ι i)) hV).trans
      ((C i).pushLocal_le_iff (D.isOpenEmbedding_ι i)))

theorem causality_lt_ι (hC : CompatibleAlong D C) {i : I} {V : Opens D.Glued} (hV : V ≤ D.O i)
    {x y : M i} :
    (D.causality C).lt V (D.ι i x) (D.ι i y) ↔
      (C i).lt (preimageOpens (D.continuous_ι i) V) x y :=
  (Precausality.generated_lt_iff (hU := mem_O) (compatible_pieces hC) (i := i) hV).trans
    ((LocalCausality.extend_lt_iff (L := (C i).pushLocal (D.isOpenEmbedding_ι i)) hV).trans
      ((C i).pushLocal_lt_iff (D.isOpenEmbedding_ι i)))

variable (D) in
/-- `G` restricts to `C i` on the open subsets of `ι i (M i)`, for every `i`. -/
def IsGluedCausality (G : Causality D.Glued) (C : ∀ i, Causality (M i)) : Prop :=
  ∀ i (V : Opens D.Glued), V ≤ D.O i → ∀ x y : M i,
    (G.le V (D.ι i x) (D.ι i y) ↔ (C i).le (preimageOpens (D.continuous_ι i) V) x y) ∧
      (G.lt V (D.ι i x) (D.ι i y) ↔ (C i).lt (preimageOpens (D.continuous_ι i) V) x y)

theorem isGluedCausality_causality (hC : CompatibleAlong D C) :
    D.IsGluedCausality (D.causality C) C :=
  fun _ _ hV _ _ => ⟨causality_le_ι hC hV, causality_lt_ι hC hV⟩

/-- **A causality on the gluing restricting to every `C i` exists iff the `C i` agree along the
transitions.** The compatibility is the weakest hypothesis. -/
theorem exists_isGluedCausality_iff :
    (∃ G, D.IsGluedCausality G C) ↔ CompatibleAlong D C := by
  constructor
  · rintro ⟨G, hG⟩ i j V₁ V₂ hV₁ hV₂ hpre u u'
    let W : Opens D.Glued := ⟨D.ι i '' V₁, D.isOpenMap_ι i _ V₁.isOpen⟩
    have hW₂ : (W : Set D.Glued) = D.ι j '' V₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨w, rfl⟩ := hV₁ hx
        have hw : w ∈ D.φ i j ⁻¹' V₂ := hpre ▸ hx
        exact ⟨D.φ i j w, hw, D.ι_φ i j w⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨w, rfl⟩ := hV₂ hy
        have hw : w ∈ (Subtype.val : D.U i j → M i) ⁻¹' V₁ := hpre ▸ hy
        exact ⟨w, hw, (D.ι_φ i j w).symm⟩
    have hle₁ : W ≤ D.O i := by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
    have hle₂ : W ≤ D.O j := by
      intro z hz
      rw [← SetLike.mem_coe, hW₂] at hz
      obtain ⟨y, -, rfl⟩ := hz
      exact ⟨y, rfl⟩
    have hp₁ : preimageOpens (D.continuous_ι i) W = V₁ := SetLike.coe_injective
      ((D.injective_ι i).preimage_image _)
    have hp₂ : preimageOpens (D.continuous_ι j) W = V₂ := SetLike.coe_injective (by
      rw [coe_preimageOpens, hW₂]; exact (D.injective_ι j).preimage_image _)
    have e₁ := hG i W hle₁ u u'
    have e₂ := hG j W hle₂ (D.φ i j u) (D.φ i j u')
    rw [hp₁] at e₁
    rw [hp₂, D.ι_φ, D.ι_φ] at e₂
    exact ⟨e₁.1.symm.trans e₂.1, e₁.2.symm.trans e₂.2⟩
  · exact fun hC => ⟨_, isGluedCausality_causality hC⟩

/-- **The glued causality is absolutely minimal when every `C i` is.** No compatibility is
used (`theo:causalite_engendre`, first assertion). -/
theorem causality_absolutelyMinimal (hA : ∀ i, (C i).AbsolutelyMinimal) :
    (D.causality C).AbsolutelyMinimal :=
  Causality.generated_absolutelyMinimal mem_O fun i =>
    (C i).absolutelyMinimalOn_pushLocal_extend (D.isOpenEmbedding_ι i) (hA i)

/-- If `G₁` is absolutely minimal and both `G₁`, `G₂` restrict to every `C i`, the relations of
`G₁` are relations of `G₂` (the family analogue of `LocalIsomorphism.le_of_absolutelyMinimal`). -/
theorem IsGluedCausality.le_lt_of_absolutelyMinimal {G₁ G₂ : Causality D.Glued}
    (h₁ : D.IsGluedCausality G₁ C) (h₂ : D.IsGluedCausality G₂ C) (hmin : G₁.AbsolutelyMinimal)
    (V : Opens D.Glued) (a b : D.Glued) :
    (G₁.le V a b → G₂.le V a b) ∧ (G₁.lt V a b → G₂.lt V a b) := by
  let S : Set (Opens D.Glued) := range D.O
  have hS : ∀ z ∈ (⊤ : Opens D.Glued), ∃ O ∈ S, z ∈ O := fun z _ => by
    obtain ⟨i, hi⟩ := mem_O z
    exact ⟨_, ⟨i, rfl⟩, hi⟩
  have hmin' := (Precausality.absolutelyMinimal_iff.1 hmin) S hS V le_top a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · refine Precausality.le_of_transGen (S := S) (Relation.TransGen.mono ?_ (hmin'.1 hab))
    rintro c d ⟨_, ⟨i, rfl⟩, hcd⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    obtain ⟨x, rfl⟩ := (inf_le_right : V ⊓ D.O i ≤ D.O i) (G₁.le_mem_left hcd)
    obtain ⟨y, rfl⟩ := (inf_le_right : V ⊓ D.O i ≤ D.O i) (G₁.le_mem_right hcd)
    exact ((h₂ i _ inf_le_right x y).1).2 (((h₁ i _ inf_le_right x y).1).1 hcd)
  · refine Precausality.lt_of_transGen (S := S) (Relation.TransGen.mono ?_ (hmin'.2 hab))
    rintro c d ⟨_, ⟨i, rfl⟩, hcd⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    obtain ⟨x, rfl⟩ := (inf_le_right : V ⊓ D.O i ≤ D.O i) (G₁.lt_mem_left hcd)
    obtain ⟨y, rfl⟩ := (inf_le_right : V ⊓ D.O i ≤ D.O i) (G₁.lt_mem_right hcd)
    exact ((h₂ i _ inf_le_right x y).2).2 (((h₁ i _ inf_le_right x y).2).1 hcd)

/-- **Uniqueness**: among absolutely minimal causalities, at most one restricts to every `C i`. -/
theorem IsGluedCausality.unique {G₁ G₂ : Causality D.Glued} (h₁ : D.IsGluedCausality G₁ C)
    (h₂ : D.IsGluedCausality G₂ C) (m₁ : G₁.AbsolutelyMinimal) (m₂ : G₂.AbsolutelyMinimal) :
    G₁ = G₂ := by
  have key : G₁.toPrecausality = G₂.toPrecausality := by
    ext V x y
    · exact ⟨(h₁.le_lt_of_absolutelyMinimal h₂ m₁ V x y).1,
        (h₂.le_lt_of_absolutelyMinimal h₁ m₂ V x y).1⟩
    · exact ⟨(h₁.le_lt_of_absolutelyMinimal h₂ m₁ V x y).2,
        (h₂.le_lt_of_absolutelyMinimal h₁ m₂ V x y).2⟩
  cases G₁; cases G₂; cases key; rfl

/-- When every `C i` is absolutely minimal, `causality D C` is the only absolutely minimal
causality restricting to every `C i` (the compatibility is forced, `exists_isGluedCausality_iff`). -/
theorem eq_causality_of_isGluedCausality (hA : ∀ i, (C i).AbsolutelyMinimal)
    {G : Causality D.Glued} (hG : D.IsGluedCausality G C) (hm : G.AbsolutelyMinimal) :
    G = D.causality C :=
  hG.unique (isGluedCausality_causality (exists_isGluedCausality_iff.1 ⟨G, hG⟩)) hm
    (causality_absolutelyMinimal hA)

/-- `ι i` is a strong morphism into the gluing. -/
theorem strongMorphism_ι (hC : CompatibleAlong D C) (i : I) :
    StrongMorphism (C i) (D.causality C) (D.ι i) where
  continuous := D.continuous_ι i
  isOpenMap := D.isOpenMap_ι i
  map_le U V hV x y hxy := by
    have hpre : preimageOpens (D.continuous_ι i) (U ⊓ D.O i) = V := by
      apply SetLike.coe_injective
      rw [hV]
      ext z
      simp [O]
    refine (D.causality C).le_mono (inf_le_left : U ⊓ D.O i ≤ U) ?_
    rw [causality_le_ι hC inf_le_right, hpre]
    exact hxy
  map_lt U V hV x y hxy := by
    have hpre : preimageOpens (D.continuous_ι i) (U ⊓ D.O i) = V := by
      apply SetLike.coe_injective
      rw [hV]
      ext z
      simp [O]
    refine (D.causality C).lt_mono (inf_le_left : U ⊓ D.O i ≤ U) ?_
    rw [causality_lt_ι hC inf_le_right, hpre]
    exact hxy

/-- `ι i` is a local isomorphism (in the reading of `Causal.Morphism`) onto its image. -/
theorem localIsomorphism_ι (hC : CompatibleAlong D C) (i : I) :
    LocalIsomorphism (C i) (D.causality C) (D.ι i) := by
  refine ⟨(D.isOpenEmbedding_ι i).isLocalHomeomorph, fun _ => ⟨⊤, trivial,
    (D.injective_ι i).injOn, fun V' _ U hU y _ z _ => ?_⟩⟩
  have hUle : U ≤ D.O i := by
    intro a ha
    rw [← SetLike.mem_coe, hU] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact ⟨b, rfl⟩
  have hpre : preimageOpens (D.continuous_ι i) U = V' := SetLike.coe_injective (by
    rw [coe_preimageOpens, hU]; exact (D.injective_ι i).preimage_image _)
  rw [causality_le_ι hC hUle, causality_lt_ι hC hUle, hpre]
  exact ⟨Iff.rfl, Iff.rfl⟩

end CausalityGluing

/-! ### A witness: a family of open subsets of one space -/

section OfOpens

variable {X : Type u} [TopologicalSpace X]

/-- The glue data of a family of open subsets `V i` of one space `X`: `U i j = V i ∩ V j`, the
transitions are the identity of `X`. It shows the hypotheses are inhabited (kb/0011). -/
def ofOpens (V : I → Opens X) : FamilyGlueData I (fun i => V i) where
  U i j := ⟨{x : V i | (x : X) ∈ V j}, (V j).isOpen.preimage continuous_subtype_val⟩
  φ _ _ x := ⟨x.1.1, x.2⟩
  continuous_φ _ _ := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  φ_mem _ _ x := x.1.2
  U_self _ := SetLike.coe_injective (eq_univ_of_forall fun x => x.2)
  φ_self _ _ := rfl
  cocycle _ _ _ _ h := ⟨h, rfl⟩

/-- The gluing of open subsets maps to `X`, by the identity on each piece. -/
def ofOpensMap (V : I → Opens X) : (ofOpens V).Glued → X :=
  (ofOpens V).desc (fun _ x => (x : X)) fun _ _ _ => rfl

theorem injective_ofOpensMap (V : I → Opens X) : Injective (ofOpensMap V) := by
  intro z z' h
  obtain ⟨i, x, rfl⟩ := (ofOpens V).exists_ι z
  obtain ⟨j, y, rfl⟩ := (ofOpens V).exists_ι z'
  have h' : (x : X) = y := h
  refine (ofOpens V).ι_eq_ι_iff.2 ⟨(h' ▸ y.2 : (x : X) ∈ V j), Subtype.ext h'⟩

theorem continuous_ofOpensMap (V : I → Opens X) : Continuous (ofOpensMap V) :=
  (ofOpens V).continuous_desc fun _ => continuous_subtype_val

/-- The gluing of open subsets of a Hausdorff space is Hausdorff; so, by `t2Space_iff`, all its
pair gluings are. -/
theorem t2Space_ofOpens [T2Space X] (V : I → Opens X) : T2Space (ofOpens V).Glued :=
  .of_injective_continuous (injective_ofOpensMap V) (continuous_ofOpensMap V)

/-- The pieces of `ofOpens V` with the causalities pulled back (`Causality.pullback`) from one
causality `Y` on `X` along the inclusions `V i → X`. -/
def ofOpensCausality (Y : Causality X) (V : I → Opens X) (i : I) : Causality (V i) :=
  Y.pullback continuous_subtype_val

/-- **A witness that `CompatibleAlong` is inhabited** (kb/0011): the pulled-back causalities of
open subsets of one space agree along their intersections. -/
theorem compatibleAlong_ofOpens (Y : Causality X) (V : I → Opens X) :
    CompatibleAlong (ofOpens V) (ofOpensCausality Y V) := by
  intro i j V₁ V₂ hV₁ hV₂ hpre u u'
  have himg : ((↑) : V i → X) '' V₁ = ((↑) : V j → X) '' V₂ := by
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨w, rfl⟩ := hV₁ ha
      have hw : w ∈ (ofOpens V).φ i j ⁻¹' V₂ := hpre ▸ ha
      exact ⟨(ofOpens V).φ i j w, hw, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨w, rfl⟩ := hV₂ hb
      have hw : w ∈ (Subtype.val : (ofOpens V).U i j → V i) ⁻¹' V₁ := hpre ▸ hb
      exact ⟨w, hw, rfl⟩
  let U : Opens X := ⟨((↑) : V i → X) '' V₁,
    (V i).isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ V₁.isOpen⟩
  have h₁ := Y.pullback_le_lt_iff_of_injective continuous_subtype_val Subtype.val_injective
    (V := V₁) (U := U) rfl (u : V i) (u' : V i)
  have h₂ := Y.pullback_le_lt_iff_of_injective continuous_subtype_val Subtype.val_injective
    (V := V₂) (U := U) himg ((ofOpens V).φ i j u) ((ofOpens V).φ i j u')
  exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩

/-- So `ofOpens V` carries a glued causality restricting to every pulled-back piece. -/
theorem isGluedCausality_ofOpens (Y : Causality X) (V : I → Opens X) :
    (ofOpens V).IsGluedCausality ((ofOpens V).causality (ofOpensCausality Y V))
      (ofOpensCausality Y V) :=
  isGluedCausality_causality (compatibleAlong_ofOpens Y V)

end OfOpens

/-! ### A witness with absolutely minimal pieces: copies of one space glued identically -/

section Const

variable (I) (X : Type u) [TopologicalSpace X]

/-- The family of copies of `X` indexed by `I`, each glued to each along the whole space by the
identity. -/
def const : FamilyGlueData I (fun _ : I => X) where
  U _ _ := ⊤
  φ _ _ x := x
  continuous_φ _ _ := continuous_subtype_val
  φ_mem _ _ _ := trivial
  U_self _ := rfl
  φ_self _ _ := rfl
  cocycle _ _ _ _ _ := ⟨trivial, rfl⟩

variable {I X}

/-- Any causality on `X`, put on every copy, is compatible along the identity gluings. -/
theorem compatibleAlong_const (Y : Causality X) : CompatibleAlong (const I X) fun _ => Y := by
  intro i j V₁ V₂ _ _ hpre u u'
  have h : V₁ = V₂ := SetLike.coe_injective (by
    ext p
    have := congrArg (fun s => (⟨p, trivial⟩ : (⊤ : Opens X)) ∈ s) hpre
    exact iff_of_eq this)
  subst h
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **A witness for the hypotheses of `causality_absolutelyMinimal`, `strongMorphism_ι` and
`localIsomorphism_ι` together**: copies of the timelike line glued identically carry an absolutely
minimal glued causality, for which every `ι i` is a local isomorphism. -/
theorem const_timelikeLine (I : Type v) :
    ((const I ℝ).causality fun _ => timelikeLine).AbsolutelyMinimal ∧
      ∀ i, LocalIsomorphism timelikeLine ((const I ℝ).causality fun _ => timelikeLine)
        ((const I ℝ).ι i) :=
  ⟨causality_absolutelyMinimal fun _ => timelikeLine_absolutelyMinimal,
    localIsomorphism_ι (compatibleAlong_const timelikeLine)⟩

end Const

/-! ### From mathlib's `TopCat.GlueData.MkCore` -/

/-- Mathlib's glue data `TopCat.GlueData.MkCore` yields a `FamilyGlueData` with the same spaces,
open sets and transitions: Sbierski's cocycle form is `t_inter` read at `(j, i, k)` on `t i j x`
together with the inverse law `MkCore.t_inv`, then `MkCore.cocycle`. -/
def ofMkCore (h : TopCat.GlueData.MkCore.{u}) : FamilyGlueData h.J fun i => (h.U i : Type u) where
  U := h.V
  φ i j x := (h.t i j x).1
  continuous_φ i j := continuous_subtype_val.comp (h.t i j).hom.continuous
  φ_mem i j x := (h.t i j x).2
  U_self := h.V_id
  φ_self i x := congrArg Subtype.val (congrFun (h.t_id i) x)
  cocycle i j k x hk := by
    have hx : (x : h.U i) ∈ h.V i k := by
      have := h.t_inter (i := j) (j := i) k (h.t i j x) hk
      rwa [h.t_inv j i x] at this
    exact ⟨hx, h.cocycle i j k x hx⟩

end FamilyGlueData

end CBG

end Causal
