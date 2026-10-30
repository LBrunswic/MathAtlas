import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The gluing of two spaces along a common open subspace, and when it is Hausdorff

**`defi:ppcm`** — `ETT.tex:1987`. `rem:non_separe_cas` — `ETT.tex:2016` (not marked: its last
sentence is false for the paper's `C` as defined, `ETT.tex:2011`; proved for the corrected `C`).

> With the notation above, let $\ppcm := \left(M_1\coprod M_2\right)/\!\sim,$ where $p\sim q$ if
> there is $x\in \pgcd$ whose images in $M_1$ and $M_2$ are $p$ and $q$, in either order.

> Let $\pi:M_1\coprod M_2\longrightarrow \left(M_1\coprod M_2\right)/N$ be the natural projection
> and set $C:=\left\{(p,q)\in M_1\times M_2 ~\middle|~ \pi(p)\text{ and }\pi(q)\text{ are not
> separated}\right\};$ we then say that $p$ and $q$ \emph{correspond}.

> If $p,q\in M_1\coprod M_2$ have non-separated images, then exactly one of the following holds:
> $p=q$; or $p=j_1(x)$ and $q=j_2(x)$ for some $x\in N$, or the same with the roles of $j_1$ and
> $j_2$ exchanged; or $p\in \partial_{M_1}j_1(N)$ and $q\in \partial_{M_2}j_2(N)$, or the same with
> the roles of $M_1$ and $M_2$ exchanged. Only the last case obstructs the Hausdorff property, and
> it is the case $C\neq \emptyset$.

Both are stated for any spaces `X`, `Y`, `W` and maps `j₁ : W → X`, `j₂ : W → Y` (`N` or
`M₁ ∧ M₂` is `W`; for `defi:ppcm`, `j₁` is the inclusion of `M₁ ∧ M₂` in `M₁` and `j₂` is `φ`).
`Gluing j₁ j₂` is `Quot (GlueRel j₁ j₂)`; `mk` is `π`; `ι₁`, `ι₂` are the two maps into it;
"separated" is `Disjoint (𝓝 a) (𝓝 b)`; `graph j₁ j₂ = {(j₁ w, j₂ w)} ⊆ X × Y`.

* `defi:ppcm`: `GlueRel`, `Gluing`; the generated equivalence is "equal or `∼`"
  (`mk_eq_mk_iff`); `ι₁`, `ι₂` are open embeddings (`isOpenEmbedding_ι₁/₂`), `π` is open
  (`isOpenMap_mk`), the square commutes (`ι₁_j₁`), the universal property (`desc`, `eq_desc`).
* `rem:non_separe_cas`, first sentence: `nonSeparated_cases` (the trichotomy and its
  exclusivity). Second sentence: `t2Space_iff_frontier` ("only the last case obstructs") and
  `t2Space_iff_Cdist_eq_empty` ("it is the case `C ≠ ∅`", with `C` read as `Cdist`).
* The general criterion: `t2Space_iff` — the gluing is Hausdorff iff `X` and `Y` are and the graph
  is closed in `X × Y`; and `disjoint_nhds_ι₁_ι₂_iff`, `C_eq_closure` — the paper's `C` is the
  closure of the graph, with no separation axiom.
* The line with two origins: `lineTwoOrigins_not_t2Space`, `lineTwoOrigins_mem_Cdist`.
* The causal structure of the gluing is in `Causal.PushoutCausal`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M₁`, `M₂` singular flat spacetimes, `M₁ ∧ M₂` / `N` a common sub-extension | ⚠ weakened: any topological spaces `X`, `Y`, `W` |
| `j₁`, `j₂` Cauchy embeddings (`φ` for `defi:ppcm`) | ⚠ weakened: open embeddings (the topological content of an injective `𝕄≥0`-morphism); no hypothesis at all for the definition |
| `M₁`, `M₂` Hausdorff (spacetimes), `rem:non_separe_cas` | ✓ carried: `[T2Space X] [T2Space Y]`; unused by `t2Space_iff`, `C_eq_closure` |
| `M₀` globally hyperbolic, Cauchy surfaces, second countability | ⚠ weakened: not used |

## SCOPE (disclosed)

* **The relation `∼` of `defi:ppcm` is not reflexive** (`p ∼ p` needs `p` in the image of the
  common sub-extension). The quotient is taken by the equivalence relation it generates, which is
  "`p = q` or `p ∼ q`" when `j₁`, `j₂` are injective (`mk_eq_mk_iff`). Injectivity of `φ` is
  necessary for `M₁ → ppcm` to be injective (`injective_j₂_of_injective_ι₁`).
* **`C` as defined (`ETT.tex:2011`) contains every pair `(j₁(x), j₂(x))`**: equal images are not
  separated (`graph_subset_C`, `C_nonempty`). So `C ≠ ∅` as soon as `N ≠ ∅`, even when the gluing
  is Hausdorff (`t2Space_and_C_nonempty`), and the last sentence of `rem:non_separe_cas` is false as
  written. Every later use of `C` (`lem:corresponding_K`, `cor:model_corresponding`,
  `prop:Cauchy_point_min`, the proof of `prop:ppcm_Cauchy`) needs the pairs with **distinct**
  non-separated images: `Cdist`. For Hausdorff `M₁`, `M₂`, `Cdist = closure(graph) ∖ graph ⊆
  ∂j₁(N) × ∂j₂(N)` (`Cdist_eq`, `Cdist_subset_frontier`), and the remark holds for it.
* The remark gives a necessary condition only: a pair of `∂j₁(N) × ∂j₂(N)` need not be
  non-separated. Nothing beyond the paper is claimed there.
* The `𝕄≥0`-manifold structure of `ppcm` (charts descend) is not formalized: the library has no
  `𝕄≥0`-manifolds. A causality on the gluing is built in `Causal.PushoutCausal`, which is
  an addition, not a paper label.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v w

variable {X : Type u} {Y : Type v} {W : Type w}

/-- The relation of `defi:ppcm`: `p ∼ q` when there is `w` whose images in `X` and `Y` are `p`
and `q`, in either order. It is not reflexive; the quotient is by the equivalence relation it
generates (`Quot`), described by `Gluing.mk_eq_mk_iff`. -/
def GlueRel (j₁ : W → X) (j₂ : W → Y) (a b : X ⊕ Y) : Prop :=
  ∃ w, (a = Sum.inl (j₁ w) ∧ b = Sum.inr (j₂ w)) ∨ (a = Sum.inr (j₂ w) ∧ b = Sum.inl (j₁ w))

/-- The gluing `(X ⊔ Y)/∼` of `X` and `Y` along `W` (`defi:ppcm`), with the quotient topology. -/
def Gluing (j₁ : W → X) (j₂ : W → Y) : Type (max u v) := Quot (GlueRel j₁ j₂)

namespace Gluing

variable (j₁ : W → X) (j₂ : W → Y)

instance [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace (Gluing j₁ j₂) :=
  inferInstanceAs (TopologicalSpace (Quot _))

/-- The projection `π : X ⊔ Y → (X ⊔ Y)/∼`. -/
def mk (a : X ⊕ Y) : Gluing j₁ j₂ := Quot.mk _ a

/-- The map `X → (X ⊔ Y)/∼`. -/
def ι₁ (x : X) : Gluing j₁ j₂ := mk j₁ j₂ (Sum.inl x)

/-- The map `Y → (X ⊔ Y)/∼`. -/
def ι₂ (y : Y) : Gluing j₁ j₂ := mk j₁ j₂ (Sum.inr y)

variable {j₁ j₂}

/-- The equivalence relation generated by `∼` is "equal, or `∼`". -/
theorem mk_eq_mk_iff (h₁ : Injective j₁) (h₂ : Injective j₂) {a b : X ⊕ Y} :
    mk j₁ j₂ a = mk j₁ j₂ b ↔ a = b ∨ GlueRel j₁ j₂ a b := by
  constructor
  · intro h
    have := Quot.eqvGen_exact h
    clear h
    induction this with
    | rel a b r => exact Or.inr r
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      rcases ih with rfl | ⟨w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨w, Or.inr ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨w, Or.inl ⟨rfl, rfl⟩⟩
    | trans a b c _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ih₂
      · rcases ih₂ with rfl | ⟨w', ⟨h, rfl⟩ | ⟨h, rfl⟩⟩
        · exact Or.inr ⟨w, Or.inl ⟨rfl, rfl⟩⟩
        · exact absurd h (by simp)
        · obtain rfl := h₂ (Sum.inr.inj h)
          exact Or.inl rfl
      · rcases ih₂ with rfl | ⟨w', ⟨h, rfl⟩ | ⟨h, rfl⟩⟩
        · exact Or.inr ⟨w, Or.inr ⟨rfl, rfl⟩⟩
        · obtain rfl := h₁ (Sum.inl.inj h)
          exact Or.inl rfl
        · exact absurd h (by simp)
  · rintro (rfl | r)
    · rfl
    · exact Quot.sound r

theorem ι₁_eq_ι₁_iff (h₁ : Injective j₁) (h₂ : Injective j₂) {x x' : X} :
    ι₁ j₁ j₂ x = ι₁ j₁ j₂ x' ↔ x = x' := by
  unfold ι₁
  rw [mk_eq_mk_iff h₁ h₂]
  simp [GlueRel]

theorem ι₂_eq_ι₂_iff (h₁ : Injective j₁) (h₂ : Injective j₂) {y y' : Y} :
    ι₂ j₁ j₂ y = ι₂ j₁ j₂ y' ↔ y = y' := by
  unfold ι₂
  rw [mk_eq_mk_iff h₁ h₂]
  simp [GlueRel]

theorem ι₁_eq_ι₂_iff (h₁ : Injective j₁) (h₂ : Injective j₂) {x : X} {y : Y} :
    ι₁ j₁ j₂ x = ι₂ j₁ j₂ y ↔ ∃ w, j₁ w = x ∧ j₂ w = y := by
  unfold ι₁ ι₂
  rw [mk_eq_mk_iff h₁ h₂]
  simp [GlueRel, eq_comm]

theorem injective_ι₁ (h₁ : Injective j₁) (h₂ : Injective j₂) : Injective (ι₁ j₁ j₂) :=
  fun _ _ h => (ι₁_eq_ι₁_iff h₁ h₂).1 h

theorem injective_ι₂ (h₁ : Injective j₁) (h₂ : Injective j₂) : Injective (ι₂ j₁ j₂) :=
  fun _ _ h => (ι₂_eq_ι₂_iff h₁ h₂).1 h

/-- The square commutes: `ι₁ ∘ j₁ = ι₂ ∘ j₂`. -/
theorem ι₁_j₁ (w : W) : ι₁ j₁ j₂ (j₁ w) = ι₂ j₁ j₂ (j₂ w) :=
  Quot.sound ⟨w, Or.inl ⟨rfl, rfl⟩⟩

/-- If `X` embeds in the gluing and `j₁` is injective, `j₂` is injective: for `defi:ppcm`
(`j₁` the inclusion of `M₁ ∧ M₂`), `M₁ → ppcm` is injective only if `φ` is. -/
theorem injective_j₂_of_injective_ι₁ (h : Injective (ι₁ j₁ j₂)) (h₁ : Injective j₁) :
    Injective j₂ := fun w w' hw => h₁ (h (by rw [ι₁_j₁, ι₁_j₁, hw]))

/-- Every point of the gluing comes from `X` or from `Y`. -/
theorem exists_ι (z : Gluing j₁ j₂) : (∃ x, ι₁ j₁ j₂ x = z) ∨ ∃ y, ι₂ j₁ j₂ y = z := by
  induction z using Quot.ind with
  | mk a =>
    rcases a with x | y
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨y, rfl⟩

theorem range_ι₁_union_range_ι₂ : range (ι₁ j₁ j₂) ∪ range (ι₂ j₁ j₂) = univ :=
  eq_univ_of_forall fun z => (exists_ι z).imp id id

/-! ### The universal property -/

/-- Two maps agreeing on `W` descend to the gluing. -/
def desc {Z : Type*} (g₁ : X → Z) (g₂ : Y → Z) (h : ∀ w, g₁ (j₁ w) = g₂ (j₂ w)) :
    Gluing j₁ j₂ → Z :=
  Quot.lift (Sum.elim g₁ g₂) (by
    rintro a b ⟨w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact h w
    · exact (h w).symm)

section desc

variable {Z : Type*} {g₁ : X → Z} {g₂ : Y → Z} {h : ∀ w, g₁ (j₁ w) = g₂ (j₂ w)}

@[simp] theorem desc_ι₁ (x : X) : desc g₁ g₂ h (ι₁ j₁ j₂ x) = g₁ x := rfl

@[simp] theorem desc_ι₂ (y : Y) : desc g₁ g₂ h (ι₂ j₁ j₂ y) = g₂ y := rfl

theorem eq_desc {f : Gluing j₁ j₂ → Z} (hf₁ : ∀ x, f (ι₁ j₁ j₂ x) = g₁ x)
    (hf₂ : ∀ y, f (ι₂ j₁ j₂ y) = g₂ y) : f = desc g₁ g₂ h := by
  funext z
  rcases exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact hf₁ x
  · exact hf₂ y

end desc

theorem preimage_ι₁_image_ι₁ (h₁ : Injective j₁) (h₂ : Injective j₂) (A : Set X) :
    ι₁ j₁ j₂ ⁻¹' (ι₁ j₁ j₂ '' A) = A :=
  (injective_ι₁ h₁ h₂).preimage_image A

theorem preimage_ι₂_image_ι₂ (h₁ : Injective j₁) (h₂ : Injective j₂) (B : Set Y) :
    ι₂ j₁ j₂ ⁻¹' (ι₂ j₁ j₂ '' B) = B :=
  (injective_ι₂ h₁ h₂).preimage_image B

theorem preimage_ι₂_image_ι₁ (h₁ : Injective j₁) (h₂ : Injective j₂) (A : Set X) :
    ι₂ j₁ j₂ ⁻¹' (ι₁ j₁ j₂ '' A) = j₂ '' (j₁ ⁻¹' A) := by
  ext y
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨w, rfl, rfl⟩ := (ι₁_eq_ι₂_iff h₁ h₂).1 h
    exact ⟨w, hx, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨j₁ w, hw, ι₁_j₁ w⟩

theorem preimage_ι₁_image_ι₂ (h₁ : Injective j₁) (h₂ : Injective j₂) (B : Set Y) :
    ι₁ j₁ j₂ ⁻¹' (ι₂ j₁ j₂ '' B) = j₁ '' (j₂ ⁻¹' B) := by
  ext x
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨w, rfl, rfl⟩ := (ι₁_eq_ι₂_iff h₁ h₂).1 h.symm
    exact ⟨w, hy, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨j₂ w, hw, (ι₁_j₁ w).symm⟩

/-! ### The quotient topology -/

section Topology

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem continuous_mk : Continuous (mk j₁ j₂) := continuous_quot_mk

theorem continuous_ι₁ : Continuous (ι₁ j₁ j₂) := continuous_mk.comp continuous_inl

theorem continuous_ι₂ : Continuous (ι₂ j₁ j₂) := continuous_mk.comp continuous_inr

/-- A set of the gluing is open iff its traces on `X` and on `Y` are. -/
theorem isOpen_iff {s : Set (Gluing j₁ j₂)} :
    IsOpen s ↔ IsOpen (ι₁ j₁ j₂ ⁻¹' s) ∧ IsOpen (ι₂ j₁ j₂ ⁻¹' s) :=
  (isQuotientMap_quot_mk.isOpen_preimage (s := s)).symm.trans isOpen_sum_iff

theorem continuous_desc {Z : Type*} [TopologicalSpace Z] {g₁ : X → Z} {g₂ : Y → Z}
    {h : ∀ w, g₁ (j₁ w) = g₂ (j₂ w)} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) :
    Continuous (desc g₁ g₂ h) :=
  continuous_quot_lift _ (hg₁.sumElim hg₂)

variable [TopologicalSpace W]

theorem isOpenMap_ι₁ (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    IsOpenMap (ι₁ j₁ j₂) := fun A hA => by
  rw [isOpen_iff, preimage_ι₁_image_ι₁ hj₁.injective hj₂.injective,
    preimage_ι₂_image_ι₁ hj₁.injective hj₂.injective]
  exact ⟨hA, hj₂.isOpenMap _ (hA.preimage hj₁.continuous)⟩

theorem isOpenMap_ι₂ (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    IsOpenMap (ι₂ j₁ j₂) := fun B hB => by
  rw [isOpen_iff, preimage_ι₂_image_ι₂ hj₁.injective hj₂.injective,
    preimage_ι₁_image_ι₂ hj₁.injective hj₂.injective]
  exact ⟨hj₁.isOpenMap _ (hB.preimage hj₂.continuous), hB⟩

/-- `X` is an open subspace of the gluing. -/
theorem isOpenEmbedding_ι₁ (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    IsOpenEmbedding (ι₁ j₁ j₂) :=
  .of_continuous_injective_isOpenMap continuous_ι₁ (injective_ι₁ hj₁.injective hj₂.injective)
    (isOpenMap_ι₁ hj₁ hj₂)

/-- `Y` is an open subspace of the gluing. -/
theorem isOpenEmbedding_ι₂ (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    IsOpenEmbedding (ι₂ j₁ j₂) :=
  .of_continuous_injective_isOpenMap continuous_ι₂ (injective_ι₂ hj₁.injective hj₂.injective)
    (isOpenMap_ι₂ hj₁ hj₂)

/-- The projection `π` is open. -/
theorem isOpenMap_mk (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    IsOpenMap (mk j₁ j₂) := fun S hS => by
  have hS' := isOpen_sum_iff.1 hS
  have : mk j₁ j₂ '' S = ι₁ j₁ j₂ '' (Sum.inl ⁻¹' S) ∪ ι₂ j₁ j₂ '' (Sum.inr ⁻¹' S) := by
    ext z
    constructor
    · rintro ⟨a | b, ha, rfl⟩
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr ⟨b, ha, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact ⟨_, ha, rfl⟩
      · exact ⟨_, hb, rfl⟩
  rw [this]
  exact (isOpenMap_ι₁ hj₁ hj₂ _ hS'.1).union (isOpenMap_ι₂ hj₁ hj₂ _ hS'.2)

end Topology


/-! ### Separation: the set `C` of non-separated pairs (`rem:non_separe_cas`) -/

section Separation

variable [TopologicalSpace X] [TopologicalSpace Y]

variable (j₁ j₂) in
/-- The graph `{(j₁ w, j₂ w)}` of the identification, a subset of `X × Y`. -/
def graph : Set (X × Y) := range fun w => (j₁ w, j₂ w)

variable (j₁ j₂) in
/-- The paper's `C`, **literally**: the pairs `(p, q) ∈ X × Y` whose images in the gluing are not
separated (have no disjoint neighbourhoods). It contains the graph (`graph_subset_C`). -/
def C : Set (X × Y) := {pq | ¬ Disjoint (𝓝 (ι₁ j₁ j₂ pq.1)) (𝓝 (ι₂ j₁ j₂ pq.2))}

variable (j₁ j₂) in
/-- The reading of `C` under which `rem:non_separe_cas` holds: the pairs whose images are
**distinct** and not separated. -/
def Cdist : Set (X × Y) := {pq | pq ∈ C j₁ j₂ ∧ ι₁ j₁ j₂ pq.1 ≠ ι₂ j₁ j₂ pq.2}

theorem graph_subset_C : graph j₁ j₂ ⊆ C j₁ j₂ := by
  rintro _ ⟨w, rfl⟩
  simp only [C, mem_setOf_eq, ι₁_j₁, disjoint_self]
  exact (nhds_neBot).ne

/-- The literal `C` is non-empty as soon as `W` is: so "`C ≠ ∅`" cannot be the obstruction to
the Hausdorff property (see `t2Space_and_C_nonempty`). -/
theorem C_nonempty [Nonempty W] : (C j₁ j₂).Nonempty :=
  ⟨_, graph_subset_C ⟨Classical.arbitrary W, rfl⟩⟩

variable [TopologicalSpace W]

theorem disjoint_nhds_ι₁_ι₁ (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) {x x' : X} :
    Disjoint (𝓝 (ι₁ j₁ j₂ x)) (𝓝 (ι₁ j₁ j₂ x')) ↔ Disjoint (𝓝 x) (𝓝 x') := by
  rw [← (isOpenEmbedding_ι₁ hj₁ hj₂).map_nhds_eq, ← (isOpenEmbedding_ι₁ hj₁ hj₂).map_nhds_eq,
    disjoint_map (injective_ι₁ hj₁.injective hj₂.injective)]

theorem disjoint_nhds_ι₂_ι₂ (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) {y y' : Y} :
    Disjoint (𝓝 (ι₂ j₁ j₂ y)) (𝓝 (ι₂ j₁ j₂ y')) ↔ Disjoint (𝓝 y) (𝓝 y') := by
  rw [← (isOpenEmbedding_ι₂ hj₁ hj₂).map_nhds_eq, ← (isOpenEmbedding_ι₂ hj₁ hj₂).map_nhds_eq,
    disjoint_map (injective_ι₂ hj₁.injective hj₂.injective)]

/-- **The images of `x ∈ X` and `y ∈ Y` are separated iff `(x, y)` is not in the closure of the
graph.** No separation axiom is used. -/
theorem disjoint_nhds_ι₁_ι₂_iff (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂)
    {x : X} {y : Y} :
    Disjoint (𝓝 (ι₁ j₁ j₂ x)) (𝓝 (ι₂ j₁ j₂ y)) ↔ (x, y) ∉ closure (graph j₁ j₂) := by
  rw [(nhds_basis_opens _).disjoint_iff (nhds_basis_opens _), mem_closure_iff]
  constructor
  · rintro ⟨O, ⟨hxO, hO⟩, O', ⟨hyO', hO'⟩, hOO'⟩ h
    obtain ⟨_, ⟨hw₁, hw₂⟩, w, rfl⟩ :=
      h _ ((hO.preimage continuous_ι₁).prod (hO'.preimage continuous_ι₂)) ⟨hxO, hyO'⟩
    have h₁ : ι₁ j₁ j₂ (j₁ w) ∈ O := hw₁
    have h₂ : ι₁ j₁ j₂ (j₁ w) ∈ O' := by rw [ι₁_j₁]; exact hw₂
    exact hOO'.ne_of_mem h₁ h₂ rfl
  · intro h
    push Not at h
    obtain ⟨o, ho, hxyo, hempty⟩ := h
    obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := isOpen_prod_iff.1 ho x y hxyo
    refine ⟨ι₁ j₁ j₂ '' A, ⟨mem_image_of_mem _ hxA, isOpenMap_ι₁ hj₁ hj₂ _ hA⟩,
      ι₂ j₁ j₂ '' B, ⟨mem_image_of_mem _ hyB, isOpenMap_ι₂ hj₁ hj₂ _ hB⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    obtain ⟨w, rfl, rfl⟩ := (ι₁_eq_ι₂_iff hj₁.injective hj₂.injective).1 hba.symm
    exact (Set.eq_empty_iff_forall_notMem.1 hempty) (j₁ w, j₂ w) ⟨hAB ⟨ha, hb⟩, w, rfl⟩

/-- The literal `C` is the closure of the graph. In the paper this is the sentence "a sequence
`(a_n)` of `N` with `j₁(a_n) → p` and `j₂(a_n) → q` exists because `π(p)` and `π(q)` are not
separated" (proof of `lem:corresponding_K`), in neighbourhood form. -/
theorem C_eq_closure (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    C j₁ j₂ = closure (graph j₁ j₂) := by
  ext ⟨x, y⟩
  simp only [C, mem_setOf_eq, disjoint_nhds_ι₁_ι₂_iff hj₁ hj₂, not_not]

theorem mem_graph_iff (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) {x : X} {y : Y} :
    (x, y) ∈ graph j₁ j₂ ↔ ι₁ j₁ j₂ x = ι₂ j₁ j₂ y := by
  rw [ι₁_eq_ι₂_iff hj₁.injective hj₂.injective]
  simp [graph]

/-- `Cdist` is the closure of the graph minus the graph. -/
theorem Cdist_eq (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    Cdist j₁ j₂ = closure (graph j₁ j₂) \ graph j₁ j₂ := by
  ext ⟨x, y⟩
  simp only [Cdist, mem_setOf_eq, C_eq_closure hj₁ hj₂, Set.mem_sdiff, mem_graph_iff hj₁ hj₂]

/-- Under the Hausdorff property of `X` and `Y`, a pair of `Cdist` lies in
`∂ j₁(W) × ∂ j₂(W)`. -/
theorem Cdist_subset_frontier [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) :
    Cdist j₁ j₂ ⊆ frontier (range j₁) ×ˢ frontier (range j₂) := by
  rintro ⟨x, y⟩ ⟨hC, hne⟩
  have hcl : (x, y) ∈ closure (graph j₁ j₂) := C_eq_closure hj₁ hj₂ ▸ hC
  have hsub : graph j₁ j₂ ⊆ range j₁ ×ˢ range j₂ := by
    rintro _ ⟨w, rfl⟩; exact ⟨⟨w, rfl⟩, ⟨w, rfl⟩⟩
  have hcl' := closure_mono hsub hcl
  rw [closure_prod_eq] at hcl'
  rw [hj₁.isOpen_range.frontier_eq, hj₂.isOpen_range.frontier_eq]
  refine ⟨⟨hcl'.1, ?_⟩, ⟨hcl'.2, ?_⟩⟩
  · rintro ⟨w, rfl⟩
    apply hne
    have h : ¬ Disjoint (𝓝 (ι₂ j₁ j₂ (j₂ w))) (𝓝 (ι₂ j₁ j₂ y)) := by
      rw [← ι₁_j₁]; exact hC
    rw [disjoint_nhds_ι₂_ι₂ hj₁ hj₂, disjoint_nhds_nhds, not_not] at h
    rw [ι₁_j₁, h]
  · rintro ⟨w, rfl⟩
    apply hne
    have h : ¬ Disjoint (𝓝 (ι₁ j₁ j₂ x)) (𝓝 (ι₁ j₁ j₂ (j₁ w))) := by
      rw [ι₁_j₁]; exact hC
    rw [disjoint_nhds_ι₁_ι₁ hj₁ hj₂, disjoint_nhds_nhds, not_not] at h
    rw [h, ι₁_j₁]

/-! ### The Hausdorff criterion -/

/-- **The gluing is Hausdorff iff `X` and `Y` are and the graph of the identification is closed
in `X × Y`.** -/
theorem t2Space_iff (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    T2Space (Gluing j₁ j₂) ↔ T2Space X ∧ T2Space Y ∧ IsClosed (graph j₁ j₂) := by
  constructor
  · intro h
    refine ⟨(isOpenEmbedding_ι₁ hj₁ hj₂).isEmbedding.t2Space,
      (isOpenEmbedding_ι₂ hj₁ hj₂).isEmbedding.t2Space, ?_⟩
    have : graph j₁ j₂ = {p : X × Y | ι₁ j₁ j₂ p.1 = ι₂ j₁ j₂ p.2} := by
      ext ⟨x, y⟩; exact mem_graph_iff hj₁ hj₂
    rw [this]
    exact isClosed_eq (continuous_ι₁.comp continuous_fst) (continuous_ι₂.comp continuous_snd)
  · rintro ⟨hX, hY, hG⟩
    rw [t2Space_iff_disjoint_nhds]
    intro z z' hzz'
    rcases exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;> rcases exists_ι z' with ⟨x', rfl⟩ | ⟨y', rfl⟩
    · rw [disjoint_nhds_ι₁_ι₁ hj₁ hj₂, disjoint_nhds_nhds]
      exact fun h => hzz' (h ▸ rfl)
    · rw [disjoint_nhds_ι₁_ι₂_iff hj₁ hj₂, hG.closure_eq, mem_graph_iff hj₁ hj₂]
      exact hzz'
    · rw [disjoint_comm, disjoint_nhds_ι₁_ι₂_iff hj₁ hj₂, hG.closure_eq, mem_graph_iff hj₁ hj₂]
      exact fun h => hzz' h.symm
    · rw [disjoint_nhds_ι₂_ι₂ hj₁ hj₂, disjoint_nhds_nhds]
      exact fun h => hzz' (h ▸ rfl)

/-- `rem:non_separe_cas`, last sentence, in the reading `Cdist`: for Hausdorff `X` and `Y` the
gluing is Hausdorff iff `Cdist = ∅`. -/
theorem t2Space_iff_Cdist_eq_empty [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) : T2Space (Gluing j₁ j₂) ↔ Cdist j₁ j₂ = ∅ := by
  rw [t2Space_iff hj₁ hj₂, Cdist_eq hj₁ hj₂, Set.sdiff_eq_empty, closure_subset_iff_isClosed]
  exact ⟨fun h => h.2.2, fun h => ⟨inferInstance, inferInstance, h⟩⟩

/-- `rem:non_separe_cas`, "only the last case obstructs the Hausdorff property": for Hausdorff
`X` and `Y` the gluing is Hausdorff iff every point of `∂ j₁(W)` and every point of `∂ j₂(W)` have
separated images. -/
theorem t2Space_iff_frontier [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) :
    T2Space (Gluing j₁ j₂) ↔ ∀ x ∈ frontier (range j₁), ∀ y ∈ frontier (range j₂),
      Disjoint (𝓝 (ι₁ j₁ j₂ x)) (𝓝 (ι₂ j₁ j₂ y)) := by
  constructor
  · intro _ x hx y _
    rw [disjoint_nhds_nhds]
    intro h
    obtain ⟨w, rfl, -⟩ := (ι₁_eq_ι₂_iff hj₁.injective hj₂.injective).1 h
    rw [hj₁.isOpen_range.frontier_eq] at hx
    exact hx.2 ⟨w, rfl⟩
  · intro h
    rw [t2Space_iff_Cdist_eq_empty hj₁ hj₂, Set.eq_empty_iff_forall_notMem]
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := Cdist_subset_frontier hj₁ hj₂ hxy
    exact hxy.1 (h x hx y hy)

/-! ### The case analysis of `rem:non_separe_cas` -/

variable (j₁ j₂) in
/-- The third case of `rem:non_separe_cas`: `p ∈ ∂ j₁(W)` and `q ∈ ∂ j₂(W)`, in either order. -/
def BoundaryPair (a b : X ⊕ Y) : Prop :=
  ∃ x y, x ∈ frontier (range j₁) ∧ y ∈ frontier (range j₂) ∧
    ((a = Sum.inl x ∧ b = Sum.inr y) ∨ (a = Sum.inr y ∧ b = Sum.inl x))

/-- **`rem:non_separe_cas`**: if `p, q ∈ X ⊔ Y` have non-separated images, then exactly one of
`p = q`, `p ∼ q` (`p = j₁(w)` and `q = j₂(w)`, or the reverse), and `p ∈ ∂ j₁(W)`, `q ∈ ∂ j₂(W)`
(or the reverse) holds. -/
theorem nonSeparated_cases [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) {a b : X ⊕ Y}
    (h : ¬ Disjoint (𝓝 (mk j₁ j₂ a)) (𝓝 (mk j₁ j₂ b))) :
    (a = b ∨ GlueRel j₁ j₂ a b ∨ BoundaryPair j₁ j₂ a b) ∧
      ¬ (a = b ∧ GlueRel j₁ j₂ a b) ∧ ¬ (a = b ∧ BoundaryPair j₁ j₂ a b) ∧
      ¬ (GlueRel j₁ j₂ a b ∧ BoundaryPair j₁ j₂ a b) := by
  have hf₁ : ∀ {x}, x ∈ frontier (range j₁) → x ∉ range j₁ := fun hx => by
    rw [hj₁.isOpen_range.frontier_eq] at hx; exact hx.2
  have hf₂ : ∀ {y}, y ∈ frontier (range j₂) → y ∉ range j₂ := fun hy => by
    rw [hj₂.isOpen_range.frontier_eq] at hy; exact hy.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases a with x | y <;> rcases b with x' | y'
    · change ¬ Disjoint (𝓝 (ι₁ j₁ j₂ x)) (𝓝 (ι₁ j₁ j₂ x')) at h
      rw [disjoint_nhds_ι₁_ι₁ hj₁ hj₂, disjoint_nhds_nhds, not_not] at h
      exact Or.inl (h ▸ rfl)
    · change ¬ Disjoint (𝓝 (ι₁ j₁ j₂ x)) (𝓝 (ι₂ j₁ j₂ y')) at h
      by_cases he : ι₁ j₁ j₂ x = ι₂ j₁ j₂ y'
      · obtain ⟨w, rfl, rfl⟩ := (ι₁_eq_ι₂_iff hj₁.injective hj₂.injective).1 he
        exact Or.inr (Or.inl ⟨w, Or.inl ⟨rfl, rfl⟩⟩)
      · obtain ⟨hx, hy⟩ := Cdist_subset_frontier hj₁ hj₂ (⟨h, he⟩ : (x, y') ∈ Cdist j₁ j₂)
        exact Or.inr (Or.inr ⟨x, y', hx, hy, Or.inl ⟨rfl, rfl⟩⟩)
    · change ¬ Disjoint (𝓝 (ι₂ j₁ j₂ y)) (𝓝 (ι₁ j₁ j₂ x')) at h
      rw [disjoint_comm] at h
      by_cases he : ι₁ j₁ j₂ x' = ι₂ j₁ j₂ y
      · obtain ⟨w, rfl, rfl⟩ := (ι₁_eq_ι₂_iff hj₁.injective hj₂.injective).1 he
        exact Or.inr (Or.inl ⟨w, Or.inr ⟨rfl, rfl⟩⟩)
      · obtain ⟨hx, hy⟩ := Cdist_subset_frontier hj₁ hj₂ (⟨h, he⟩ : (x', y) ∈ Cdist j₁ j₂)
        exact Or.inr (Or.inr ⟨x', y, hx, hy, Or.inr ⟨rfl, rfl⟩⟩)
    · change ¬ Disjoint (𝓝 (ι₂ j₁ j₂ y)) (𝓝 (ι₂ j₁ j₂ y')) at h
      rw [disjoint_nhds_ι₂_ι₂ hj₁ hj₂, disjoint_nhds_nhds, not_not] at h
      exact Or.inl (h ▸ rfl)
  · rintro ⟨rfl, w, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Sum.inl_ne_inr (h1.symm.trans h2)
    · exact Sum.inr_ne_inl (h1.symm.trans h2)
  · rintro ⟨rfl, x, y, -, -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Sum.inl_ne_inr (h1.symm.trans h2)
    · exact Sum.inr_ne_inl (h1.symm.trans h2)
  · rintro ⟨⟨w, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩, x, y, hx, hy, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
    · exact hf₁ hx ⟨w, Sum.inl.inj (h1.symm.trans h3)⟩
    · exact Sum.inl_ne_inr (h1.symm.trans h3)
    · exact Sum.inr_ne_inl (h1.symm.trans h3)
    · exact hf₂ hy ⟨w, Sum.inr.inj (h1.symm.trans h3)⟩

end Separation

/-! ### The literal `C` is not the obstruction -/

/-- Gluing a point to a point along a point gives a Hausdorff space whose literal `C` is
non-empty: "`C ≠ ∅`" in the paper's literal sense does not obstruct the Hausdorff property. -/
theorem t2Space_and_C_nonempty :
    T2Space (Gluing (id : Unit → Unit) id) ∧ (C (id : Unit → Unit) id).Nonempty := by
  refine ⟨(t2Space_iff .id .id).2 ⟨inferInstance, inferInstance, ?_⟩, C_nonempty⟩
  exact Set.subsingleton_of_subsingleton.isClosed

/-! ### The line with two origins -/

/-- The inclusion of `ℝ ∖ {0}` in `ℝ`. -/
abbrev lineTwoOriginsInc : ↥({0}ᶜ : Set ℝ) → ℝ := Subtype.val

/-- The line with two origins: two copies of `ℝ` glued along `ℝ ∖ {0}`. -/
abbrev LineTwoOrigins : Type := Gluing lineTwoOriginsInc lineTwoOriginsInc

theorem isOpenEmbedding_lineTwoOriginsInc : IsOpenEmbedding lineTwoOriginsInc :=
  isOpen_compl_singleton.isOpenEmbedding_subtypeVal

/-- The two origins form a pair of `Cdist`: distinct, not separated. -/
theorem lineTwoOrigins_mem_Cdist :
    ((0 : ℝ), (0 : ℝ)) ∈ Cdist lineTwoOriginsInc lineTwoOriginsInc := by
  rw [Cdist_eq isOpenEmbedding_lineTwoOriginsInc isOpenEmbedding_lineTwoOriginsInc]
  refine ⟨?_, ?_⟩
  · have h0 : (0 : ℝ) ∈ closure ({0}ᶜ : Set ℝ) := by
      rw [closure_compl_singleton]; trivial
    refine map_mem_closure (f := fun t : ℝ => (t, t)) (by fun_prop) h0 ?_
    intro t ht
    exact ⟨⟨t, ht⟩, rfl⟩
  · rintro ⟨⟨t, ht⟩, h⟩
    exact ht (Prod.mk.inj h).1

theorem lineTwoOrigins_ι₁_ne_ι₂ :
    ι₁ lineTwoOriginsInc lineTwoOriginsInc (0 : ℝ) ≠ ι₂ lineTwoOriginsInc lineTwoOriginsInc 0 :=
  lineTwoOrigins_mem_Cdist.2

theorem lineTwoOrigins_not_separated :
    ¬ Disjoint (𝓝 (ι₁ lineTwoOriginsInc lineTwoOriginsInc (0 : ℝ)))
      (𝓝 (ι₂ lineTwoOriginsInc lineTwoOriginsInc 0)) :=
  lineTwoOrigins_mem_Cdist.1

/-- The line with two origins is not Hausdorff. -/
theorem lineTwoOrigins_not_t2Space : ¬ T2Space LineTwoOrigins := by
  rw [t2Space_iff_Cdist_eq_empty isOpenEmbedding_lineTwoOriginsInc
    isOpenEmbedding_lineTwoOriginsInc]
  exact (Set.nonempty_of_mem lineTwoOrigins_mem_Cdist).ne_empty

end Gluing

end Causal
