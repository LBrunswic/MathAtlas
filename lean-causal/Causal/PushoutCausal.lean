import Causal.Pushout
import Causal.Morphism

/-!
# A causality on the gluing of two topological spacetimes

No paper label is certified by this file.

`Causal.Pushout` builds the gluing `Gluing j₁ j₂ = (X ⊔ Y)/∼` of `defi:ppcm`
(`ETT.tex:1987`) as a topological space. The paper's `ppcm` is meant to be a spacetime again; its
`𝕄≥0`-structure ("the charts of `M₁` and `M₂` descend", `ETT.tex:2000`) is not modelled by the
library. This file gives the topological-spacetime counterpart:

* a causality on `X` transports along an open embedding `e : X → Z` to a causality on the open set
  `e(X)` (`Causality.pushLocal`, `pushLocal_le_iff`, `pushLocal_lt_iff`);
* `Gluing.causality` is the causality generated (`theo:causalite_engendre`, `Causal.Generated`) by
  `C₁` on `ι₁(X)` and `C₂` on `ι₂(Y)`; when `C₁`, `C₂` agree along `W`
  (`Gluing.CompatibleAlong`: `f = j₂ ∘ j₁⁻¹` matches the relations of `j₁(W)` and `j₂(W)`), it
  restricts to `C₁` and `C₂` (`isGluingCausality_causality`), and `ι₁`, `ι₂` are strong morphisms
  (`strongMorphism_ι₁/₂`) and local isomorphisms (`localIsomorphism_ι₁/₂`);
* a causality on the gluing restricting to `C₁` and `C₂` exists **iff** they agree along `W`
  (`exists_isGluingCausality_iff`): the compatibility is the weakest hypothesis.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M₁`, `M₂` singular flat spacetimes, `j₁`, `j₂` Cauchy embeddings | ⚠ weakened: topological spaces with causalities, `j₁`, `j₂` open embeddings |
| the embeddings are `𝕄≥0`-morphisms, compatible with the structures | ✓ carried as `CompatibleAlong` (necessary and sufficient) |
| Hausdorff, second countability, global hyperbolicity | ⚠ weakened: not used |

## SCOPE (disclosed)

* "Strong morphism" and "local isomorphism" are those of `Causal.Morphism`, under its
  readings (SCOPE (a), (c) there) awaiting the author. This is why the file stays in the scaffold.
* The generated causality is one choice among the causalities restricting to `C₁` and `C₂`; it is
  the minimal one (`lem:union_causalite`). Uniqueness is not stated here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v w

variable {X : Type u} {Y : Type v} {W : Type w}

/-! ### A causality on the gluing -/

section Transport

variable [TopologicalSpace X] {Z : Type*} [TopologicalSpace Z] {e : X → Z}

/-- A causality on `X`, transported along the open embedding `e` to a causality on the open
subset `e(X)` of `Z`. -/
def Causality.pushLocal (C : Causality X) (he : IsOpenEmbedding e) :
    LocalCausality (⟨range e, he.isOpen_range⟩ : Opens Z) where
  le U a b := ∃ x y, e x = a ∧ e y = b ∧ C.le (preimageOpens he.continuous U) x y
  lt U a b := ∃ x y, e x = a ∧ e y = b ∧ C.lt (preimageOpens he.continuous U) x y
  le_mem_left := by rintro U a b - ⟨x, y, rfl, rfl, h⟩; exact C.le_mem_left h
  le_mem_right := by rintro U a b - ⟨x, y, rfl, rfl, h⟩; exact C.le_mem_right h
  lt_mem_left := by rintro U a b - ⟨x, y, rfl, rfl, h⟩; exact C.lt_mem_left h
  lt_mem_right := by rintro U a b - ⟨x, y, rfl, rfl, h⟩; exact C.lt_mem_right h
  le_refl := by
    intro U a hU ha
    obtain ⟨x, rfl⟩ : a ∈ range e := hU ha
    exact ⟨x, x, rfl, rfl, C.le_refl ha⟩
  le_trans := by
    rintro U a b c - ⟨x, y, rfl, rfl, h₁⟩ ⟨y', z, hy, rfl, h₂⟩
    obtain rfl := he.injective hy
    exact ⟨x, z, rfl, rfl, C.le_trans h₁ h₂⟩
  lt_trans := by
    rintro U a b c - ⟨x, y, rfl, rfl, h₁⟩ ⟨y', z, hy, rfl, h₂⟩
    obtain rfl := he.injective hy
    exact ⟨x, z, rfl, rfl, C.lt_trans h₁ h₂⟩
  le_mono := by
    rintro U V - hVU a b ⟨x, y, rfl, rfl, h⟩
    exact ⟨x, y, rfl, rfl, C.le_mono (fun z hz => hVU hz) h⟩
  lt_mono := by
    rintro U V - hVU a b ⟨x, y, rfl, rfl, h⟩
    exact ⟨x, y, rfl, rfl, C.lt_mono (fun z hz => hVU hz) h⟩
  le_of_lt := by
    rintro U a b - ⟨x, y, rfl, rfl, h⟩
    exact ⟨x, y, rfl, rfl, C.le_of_lt h⟩
  isOpen_lt_right U a _ := by
    by_cases ha : a ∈ range e
    · obtain ⟨x, rfl⟩ := ha
      have : {b | ∃ x' y, e x' = e x ∧ e y = b ∧ C.lt (preimageOpens he.continuous U) x' y} =
          e '' {y | C.lt (preimageOpens he.continuous U) x y} := by
        ext b
        constructor
        · rintro ⟨x', y, hx', rfl, h⟩
          obtain rfl := he.injective hx'
          exact ⟨y, h, rfl⟩
        · rintro ⟨y, h, rfl⟩
          exact ⟨x, y, rfl, rfl, h⟩
      rw [this]
      exact he.isOpenMap _ (C.isOpen_lt_right _ x)
    · convert isOpen_empty
      ext b
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨x, y, rfl, -, -⟩
      exact ha ⟨x, rfl⟩
  isOpen_lt_left U a _ := by
    by_cases ha : a ∈ range e
    · obtain ⟨x, rfl⟩ := ha
      have : {b | ∃ y x', e y = b ∧ e x' = e x ∧ C.lt (preimageOpens he.continuous U) y x'} =
          e '' {y | C.lt (preimageOpens he.continuous U) y x} := by
        ext b
        constructor
        · rintro ⟨y, x', rfl, hx', h⟩
          obtain rfl := he.injective hx'
          exact ⟨y, h, rfl⟩
        · rintro ⟨y, h, rfl⟩
          exact ⟨y, x, rfl, rfl, h⟩
      rw [this]
      exact he.isOpenMap _ (C.isOpen_lt_left _ x)
    · convert isOpen_empty
      ext b
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨y, x, -, rfl, -⟩
      exact ha ⟨x, rfl⟩

theorem Causality.pushLocal_le_iff (C : Causality X) (he : IsOpenEmbedding e) {U : Opens Z}
    {x y : X} :
    (C.pushLocal he).le U (e x) (e y) ↔ C.le (preimageOpens he.continuous U) x y := by
  constructor
  · rintro ⟨x', y', hx, hy, h⟩
    rwa [← he.injective hx, ← he.injective hy]
  · exact fun h => ⟨x, y, rfl, rfl, h⟩

theorem Causality.pushLocal_lt_iff (C : Causality X) (he : IsOpenEmbedding e) {U : Opens Z}
    {x y : X} :
    (C.pushLocal he).lt U (e x) (e y) ↔ C.lt (preimageOpens he.continuous U) x y := by
  constructor
  · rintro ⟨x', y', hx, hy, h⟩
    rwa [← he.injective hx, ← he.injective hy]
  · exact fun h => ⟨x, y, rfl, rfl, h⟩

end Transport

namespace Gluing

section CausalityGluing

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
  {j₁ : W → X} {j₂ : W → Y}

variable (j₁ j₂) in
/-- The causalities `C₁` on `X` and `C₂` on `Y` agree along `W`: `f = j₂ ∘ j₁⁻¹` is an
isomorphism of causalities from `j₁(W)` onto `j₂(W)`. -/
def CompatibleAlong (C₁ : Causality X) (C₂ : Causality Y) : Prop :=
  ∀ (V₁ : Opens X) (V₂ : Opens Y), (V₁ : Set X) ⊆ range j₁ → (V₂ : Set Y) ⊆ range j₂ →
    j₁ ⁻¹' V₁ = j₂ ⁻¹' V₂ → ∀ u u' : W,
      (C₁.le V₁ (j₁ u) (j₁ u') ↔ C₂.le V₂ (j₂ u) (j₂ u')) ∧
        (C₁.lt V₁ (j₁ u) (j₁ u') ↔ C₂.lt V₂ (j₂ u) (j₂ u'))

/-- The open set `ι₁(X)` of the gluing. -/
def O₁ (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) : Opens (Gluing j₁ j₂) :=
  ⟨range (ι₁ j₁ j₂), (isOpenEmbedding_ι₁ hj₁ hj₂).isOpen_range⟩

/-- The open set `ι₂(Y)` of the gluing. -/
def O₂ (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) : Opens (Gluing j₁ j₂) :=
  ⟨range (ι₂ j₁ j₂), (isOpenEmbedding_ι₂ hj₁ hj₂).isOpen_range⟩

variable (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂)

/-- The cover `{ι₁(X), ι₂(Y)}`, indexed by `Bool`. -/
def cover : Bool → Opens (Gluing j₁ j₂) := fun b => cond b (O₁ hj₁ hj₂) (O₂ hj₁ hj₂)

theorem mem_cover (z : Gluing j₁ j₂) : ∃ b, z ∈ cover hj₁ hj₂ b :=
  (exists_ι z).elim (fun ⟨x, hx⟩ => ⟨true, x, hx⟩) (fun ⟨y, hy⟩ => ⟨false, y, hy⟩)

/-- The two transported causalities, as causalities on the gluing. -/
def pieces (C₁ : Causality X) (C₂ : Causality Y) : Bool → Causality (Gluing j₁ j₂) :=
  fun b => cond b (C₁.pushLocal (isOpenEmbedding_ι₁ hj₁ hj₂)).extend
    (C₂.pushLocal (isOpenEmbedding_ι₂ hj₁ hj₂)).extend

/-- The causality of the gluing: the one generated (`theo:causalite_engendre`) by `C₁` on
`ι₁(X)` and `C₂` on `ι₂(Y)`. -/
def causality (C₁ : Causality X) (C₂ : Causality Y) : Causality (Gluing j₁ j₂) :=
  Causality.generated (cover hj₁ hj₂) (mem_cover hj₁ hj₂) (pieces hj₁ hj₂ C₁ C₂)

variable {hj₁ hj₂}

theorem subset_range_j₁ {V : Opens (Gluing j₁ j₂)} (hV : V ≤ O₁ hj₁ hj₂ ⊓ O₂ hj₁ hj₂) :
    (preimageOpens (continuous_ι₁ (j₁ := j₁) (j₂ := j₂)) V : Set X) ⊆ range j₁ := by
  intro x hx
  obtain ⟨y, hy⟩ : ι₁ j₁ j₂ x ∈ range (ι₂ j₁ j₂) := (hV hx).2
  obtain ⟨w, hw, -⟩ := (ι₁_eq_ι₂_iff hj₁.injective hj₂.injective).1 hy.symm
  exact ⟨w, hw⟩

theorem subset_range_j₂ {V : Opens (Gluing j₁ j₂)} (hV : V ≤ O₁ hj₁ hj₂ ⊓ O₂ hj₁ hj₂) :
    (preimageOpens (continuous_ι₂ (j₁ := j₁) (j₂ := j₂)) V : Set Y) ⊆ range j₂ := by
  intro y hy
  obtain ⟨x, hx⟩ : ι₂ j₁ j₂ y ∈ range (ι₁ j₁ j₂) := (hV hy).1
  obtain ⟨w, -, hw⟩ := (ι₁_eq_ι₂_iff hj₁.injective hj₂.injective).1 hx
  exact ⟨w, hw⟩

omit [TopologicalSpace W] in
theorem preimage_j_eq (V : Opens (Gluing j₁ j₂)) :
    j₁ ⁻¹' (preimageOpens (continuous_ι₁ (j₁ := j₁) (j₂ := j₂)) V : Set X) =
      j₂ ⁻¹' (preimageOpens (continuous_ι₂ (j₁ := j₁) (j₂ := j₂)) V : Set Y) := by
  ext w
  simp only [coe_preimageOpens, mem_preimage, ι₁_j₁]

/-- The overlap: on an open subset of `ι₁(X) ∩ ι₂(Y)` the two transported relations agree. -/
theorem overlap_iff {r₁ : Opens X → X → X → Prop} {r₂ : Opens Y → Y → Y → Prop}
    (hr₁ : ∀ {V x y}, r₁ V x y → x ∈ V ∧ y ∈ V) (hr₂ : ∀ {V x y}, r₂ V x y → x ∈ V ∧ y ∈ V)
    (hc : ∀ (V₁ : Opens X) (V₂ : Opens Y), (V₁ : Set X) ⊆ range j₁ → (V₂ : Set Y) ⊆ range j₂ →
      j₁ ⁻¹' V₁ = j₂ ⁻¹' V₂ → ∀ u u' : W, r₁ V₁ (j₁ u) (j₁ u') ↔ r₂ V₂ (j₂ u) (j₂ u'))
    {V : Opens (Gluing j₁ j₂)} (hV : V ≤ O₁ hj₁ hj₂ ⊓ O₂ hj₁ hj₂) {a b : Gluing j₁ j₂} :
    (∃ x y, ι₁ j₁ j₂ x = a ∧ ι₁ j₁ j₂ y = b ∧ r₁ (preimageOpens continuous_ι₁ V) x y) ↔
      (∃ x y, ι₂ j₁ j₂ x = a ∧ ι₂ j₁ j₂ y = b ∧ r₂ (preimageOpens continuous_ι₂ V) x y) := by
  have hc' := hc _ _ (subset_range_j₁ hV) (subset_range_j₂ hV) (preimage_j_eq V)
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain ⟨u, rfl⟩ := subset_range_j₁ hV (hr₁ h).1
    obtain ⟨u', rfl⟩ := subset_range_j₁ hV (hr₁ h).2
    exact ⟨j₂ u, j₂ u', (ι₁_j₁ u).symm, (ι₁_j₁ u').symm, (hc' u u').1 h⟩
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain ⟨u, rfl⟩ := subset_range_j₂ hV (hr₂ h).1
    obtain ⟨u', rfl⟩ := subset_range_j₂ hV (hr₂ h).2
    exact ⟨j₁ u, j₁ u', ι₁_j₁ u, ι₁_j₁ u', (hc' u u').2 h⟩

theorem compatible_pieces {C₁ : Causality X} {C₂ : Causality Y}
    (hC : CompatibleAlong j₁ j₂ C₁ C₂) :
    Precausality.Compatible (cover hj₁ hj₂) fun b => (pieces hj₁ hj₂ C₁ C₂ b).toPrecausality := by
  have key : ∀ (V : Opens (Gluing j₁ j₂)), V ≤ O₁ hj₁ hj₂ ⊓ O₂ hj₁ hj₂ → ∀ a b,
      ((pieces hj₁ hj₂ C₁ C₂ true).le V a b ↔ (pieces hj₁ hj₂ C₁ C₂ false).le V a b) ∧
      ((pieces hj₁ hj₂ C₁ C₂ true).lt V a b ↔ (pieces hj₁ hj₂ C₁ C₂ false).lt V a b) := by
    intro V hV a b
    have h₁ : V ≤ O₁ hj₁ hj₂ := hV.trans inf_le_left
    have h₂ : V ≤ O₂ hj₁ hj₂ := hV.trans inf_le_right
    refine ⟨(LocalCausality.extend_le_iff (L := C₁.pushLocal (isOpenEmbedding_ι₁ hj₁ hj₂)) h₁).trans
      ((overlap_iff (fun h => ⟨C₁.le_mem_left h, C₁.le_mem_right h⟩)
        (fun h => ⟨C₂.le_mem_left h, C₂.le_mem_right h⟩)
        (fun V₁ V₂ h₁ h₂ h u u' => (hC V₁ V₂ h₁ h₂ h u u').1) hV).trans
        (LocalCausality.extend_le_iff (L := C₂.pushLocal (isOpenEmbedding_ι₂ hj₁ hj₂)) h₂).symm),
      (LocalCausality.extend_lt_iff (L := C₁.pushLocal (isOpenEmbedding_ι₁ hj₁ hj₂)) h₁).trans
      ((overlap_iff (fun h => ⟨C₁.lt_mem_left h, C₁.lt_mem_right h⟩)
        (fun h => ⟨C₂.lt_mem_left h, C₂.lt_mem_right h⟩)
        (fun V₁ V₂ h₁ h₂ h u u' => (hC V₁ V₂ h₁ h₂ h u u').2) hV).trans
        (LocalCausality.extend_lt_iff (L := C₂.pushLocal (isOpenEmbedding_ι₂ hj₁ hj₂)) h₂).symm)⟩
  rintro (_ | _) (_ | _) V hV a b
  · exact ⟨Iff.rfl, Iff.rfl⟩
  · exact ⟨(key V (by rwa [inf_comm]) a b).1.symm, (key V (by rwa [inf_comm]) a b).2.symm⟩
  · exact key V hV a b
  · exact ⟨Iff.rfl, Iff.rfl⟩

variable {C₁ : Causality X} {C₂ : Causality Y}

theorem causality_le_ι₁ (hC : CompatibleAlong j₁ j₂ C₁ C₂) {V : Opens (Gluing j₁ j₂)}
    (hV : V ≤ O₁ hj₁ hj₂) {x y : X} :
    (causality hj₁ hj₂ C₁ C₂).le V (ι₁ j₁ j₂ x) (ι₁ j₁ j₂ y) ↔
      C₁.le (preimageOpens continuous_ι₁ V) x y :=
  (Precausality.generated_le_iff (hU := mem_cover hj₁ hj₂) (compatible_pieces hC) (i := true) hV).trans
    ((LocalCausality.extend_le_iff (L := C₁.pushLocal (isOpenEmbedding_ι₁ hj₁ hj₂)) hV).trans
      (C₁.pushLocal_le_iff (isOpenEmbedding_ι₁ hj₁ hj₂)))

theorem causality_lt_ι₁ (hC : CompatibleAlong j₁ j₂ C₁ C₂) {V : Opens (Gluing j₁ j₂)}
    (hV : V ≤ O₁ hj₁ hj₂) {x y : X} :
    (causality hj₁ hj₂ C₁ C₂).lt V (ι₁ j₁ j₂ x) (ι₁ j₁ j₂ y) ↔
      C₁.lt (preimageOpens continuous_ι₁ V) x y :=
  (Precausality.generated_lt_iff (hU := mem_cover hj₁ hj₂) (compatible_pieces hC) (i := true) hV).trans
    ((LocalCausality.extend_lt_iff (L := C₁.pushLocal (isOpenEmbedding_ι₁ hj₁ hj₂)) hV).trans
      (C₁.pushLocal_lt_iff (isOpenEmbedding_ι₁ hj₁ hj₂)))

theorem causality_le_ι₂ (hC : CompatibleAlong j₁ j₂ C₁ C₂) {V : Opens (Gluing j₁ j₂)}
    (hV : V ≤ O₂ hj₁ hj₂) {x y : Y} :
    (causality hj₁ hj₂ C₁ C₂).le V (ι₂ j₁ j₂ x) (ι₂ j₁ j₂ y) ↔
      C₂.le (preimageOpens continuous_ι₂ V) x y :=
  (Precausality.generated_le_iff (hU := mem_cover hj₁ hj₂) (compatible_pieces hC) (i := false) hV).trans
    ((LocalCausality.extend_le_iff (L := C₂.pushLocal (isOpenEmbedding_ι₂ hj₁ hj₂)) hV).trans
      (C₂.pushLocal_le_iff (isOpenEmbedding_ι₂ hj₁ hj₂)))

theorem causality_lt_ι₂ (hC : CompatibleAlong j₁ j₂ C₁ C₂) {V : Opens (Gluing j₁ j₂)}
    (hV : V ≤ O₂ hj₁ hj₂) {x y : Y} :
    (causality hj₁ hj₂ C₁ C₂).lt V (ι₂ j₁ j₂ x) (ι₂ j₁ j₂ y) ↔
      C₂.lt (preimageOpens continuous_ι₂ V) x y :=
  (Precausality.generated_lt_iff (hU := mem_cover hj₁ hj₂) (compatible_pieces hC) (i := false) hV).trans
    ((LocalCausality.extend_lt_iff (L := C₂.pushLocal (isOpenEmbedding_ι₂ hj₁ hj₂)) hV).trans
      (C₂.pushLocal_lt_iff (isOpenEmbedding_ι₂ hj₁ hj₂)))

variable (hj₁ hj₂) in
/-- `C` restricts to `C₁` on the open subsets of `ι₁(X)` and to `C₂` on those of `ι₂(Y)`. -/
def IsGluingCausality (C : Causality (Gluing j₁ j₂)) (C₁ : Causality X) (C₂ : Causality Y) :
    Prop :=
  (∀ V : Opens (Gluing j₁ j₂), V ≤ O₁ hj₁ hj₂ → ∀ x y : X,
    (C.le V (ι₁ j₁ j₂ x) (ι₁ j₁ j₂ y) ↔ C₁.le (preimageOpens continuous_ι₁ V) x y) ∧
      (C.lt V (ι₁ j₁ j₂ x) (ι₁ j₁ j₂ y) ↔ C₁.lt (preimageOpens continuous_ι₁ V) x y)) ∧
  (∀ V : Opens (Gluing j₁ j₂), V ≤ O₂ hj₁ hj₂ → ∀ x y : Y,
    (C.le V (ι₂ j₁ j₂ x) (ι₂ j₁ j₂ y) ↔ C₂.le (preimageOpens continuous_ι₂ V) x y) ∧
      (C.lt V (ι₂ j₁ j₂ x) (ι₂ j₁ j₂ y) ↔ C₂.lt (preimageOpens continuous_ι₂ V) x y))

theorem isGluingCausality_causality (hC : CompatibleAlong j₁ j₂ C₁ C₂) :
    IsGluingCausality hj₁ hj₂ (causality hj₁ hj₂ C₁ C₂) C₁ C₂ :=
  ⟨fun _ hV _ _ => ⟨causality_le_ι₁ hC hV, causality_lt_ι₁ hC hV⟩,
    fun _ hV _ _ => ⟨causality_le_ι₂ hC hV, causality_lt_ι₂ hC hV⟩⟩

/-- **A causality on the gluing restricting to `C₁` and `C₂` exists iff `C₁` and `C₂` agree
along `W`.** The compatibility is therefore the weakest hypothesis. -/
theorem exists_isGluingCausality_iff :
    (∃ C, IsGluingCausality hj₁ hj₂ C C₁ C₂) ↔ CompatibleAlong j₁ j₂ C₁ C₂ := by
  constructor
  · rintro ⟨C, h₁, h₂⟩ V₁ V₂ hV₁ hV₂ hpre u u'
    let U : Opens (Gluing j₁ j₂) := ⟨ι₁ j₁ j₂ '' V₁, isOpenMap_ι₁ hj₁ hj₂ _ V₁.isOpen⟩
    have hU₂ : (U : Set (Gluing j₁ j₂)) = ι₂ j₁ j₂ '' V₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨w, rfl⟩ := hV₁ hx
        have hw : w ∈ j₂ ⁻¹' V₂ := hpre ▸ hx
        exact ⟨j₂ w, hw, (ι₁_j₁ w).symm⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨w, rfl⟩ := hV₂ hy
        have hw : w ∈ j₁ ⁻¹' V₁ := hpre ▸ hy
        exact ⟨j₁ w, hw, ι₁_j₁ w⟩
    have hle₁ : U ≤ O₁ hj₁ hj₂ := by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
    have hle₂ : U ≤ O₂ hj₁ hj₂ := by
      intro z hz
      rw [← SetLike.mem_coe, hU₂] at hz
      obtain ⟨y, -, rfl⟩ := hz
      exact ⟨y, rfl⟩
    have hp₁ : preimageOpens continuous_ι₁ U = V₁ := SetLike.coe_injective
      (preimage_ι₁_image_ι₁ hj₁.injective hj₂.injective _)
    have hp₂ : preimageOpens continuous_ι₂ U = V₂ := SetLike.coe_injective (by
      rw [coe_preimageOpens, hU₂]; exact preimage_ι₂_image_ι₂ hj₁.injective hj₂.injective _)
    have e₁ := h₁ U hle₁ (j₁ u) (j₁ u')
    have e₂ := h₂ U hle₂ (j₂ u) (j₂ u')
    rw [hp₁, ι₁_j₁, ι₁_j₁] at e₁
    rw [hp₂] at e₂
    exact ⟨e₁.1.symm.trans e₂.1, e₁.2.symm.trans e₂.2⟩
  · exact fun hC => ⟨_, isGluingCausality_causality hC⟩

/-- `ι₁` is a strong morphism into the gluing. -/
theorem strongMorphism_ι₁ (hC : CompatibleAlong j₁ j₂ C₁ C₂) :
    StrongMorphism C₁ (causality hj₁ hj₂ C₁ C₂) (ι₁ j₁ j₂) where
  continuous := continuous_ι₁
  isOpenMap := isOpenMap_ι₁ hj₁ hj₂
  map_le U V hV x y hxy := by
    have hpre : preimageOpens continuous_ι₁ (U ⊓ O₁ hj₁ hj₂) = V := by
      apply SetLike.coe_injective
      rw [hV]
      ext z
      simp [O₁]
    refine (causality hj₁ hj₂ C₁ C₂).le_mono (inf_le_left : U ⊓ O₁ hj₁ hj₂ ≤ U) ?_
    rw [causality_le_ι₁ hC inf_le_right, hpre]
    exact hxy
  map_lt U V hV x y hxy := by
    have hpre : preimageOpens continuous_ι₁ (U ⊓ O₁ hj₁ hj₂) = V := by
      apply SetLike.coe_injective
      rw [hV]
      ext z
      simp [O₁]
    refine (causality hj₁ hj₂ C₁ C₂).lt_mono (inf_le_left : U ⊓ O₁ hj₁ hj₂ ≤ U) ?_
    rw [causality_lt_ι₁ hC inf_le_right, hpre]
    exact hxy

/-- `ι₂` is a strong morphism into the gluing. -/
theorem strongMorphism_ι₂ (hC : CompatibleAlong j₁ j₂ C₁ C₂) :
    StrongMorphism C₂ (causality hj₁ hj₂ C₁ C₂) (ι₂ j₁ j₂) where
  continuous := continuous_ι₂
  isOpenMap := isOpenMap_ι₂ hj₁ hj₂
  map_le U V hV x y hxy := by
    have hpre : preimageOpens continuous_ι₂ (U ⊓ O₂ hj₁ hj₂) = V := by
      apply SetLike.coe_injective
      rw [hV]
      ext z
      simp [O₂]
    refine (causality hj₁ hj₂ C₁ C₂).le_mono (inf_le_left : U ⊓ O₂ hj₁ hj₂ ≤ U) ?_
    rw [causality_le_ι₂ hC inf_le_right, hpre]
    exact hxy
  map_lt U V hV x y hxy := by
    have hpre : preimageOpens continuous_ι₂ (U ⊓ O₂ hj₁ hj₂) = V := by
      apply SetLike.coe_injective
      rw [hV]
      ext z
      simp [O₂]
    refine (causality hj₁ hj₂ C₁ C₂).lt_mono (inf_le_left : U ⊓ O₂ hj₁ hj₂ ≤ U) ?_
    rw [causality_lt_ι₂ hC inf_le_right, hpre]
    exact hxy

/-- `ι₁` is a local isomorphism (in the reading of `Causal.Morphism`) onto its image. -/
theorem localIsomorphism_ι₁ (hC : CompatibleAlong j₁ j₂ C₁ C₂) :
    LocalIsomorphism C₁ (causality hj₁ hj₂ C₁ C₂) (ι₁ j₁ j₂) := by
  refine ⟨(isOpenEmbedding_ι₁ hj₁ hj₂).isLocalHomeomorph, fun _ => ⟨⊤, trivial,
    (injective_ι₁ hj₁.injective hj₂.injective).injOn, fun V' _ U hU y _ z _ => ?_⟩⟩
  have hUle : U ≤ O₁ hj₁ hj₂ := by
    intro a ha
    rw [← SetLike.mem_coe, hU] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact ⟨b, rfl⟩
  have hpre : preimageOpens continuous_ι₁ U = V' := SetLike.coe_injective (by
    rw [coe_preimageOpens, hU]; exact preimage_ι₁_image_ι₁ hj₁.injective hj₂.injective _)
  rw [causality_le_ι₁ hC hUle, causality_lt_ι₁ hC hUle, hpre]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- `ι₂` is a local isomorphism onto its image. -/
theorem localIsomorphism_ι₂ (hC : CompatibleAlong j₁ j₂ C₁ C₂) :
    LocalIsomorphism C₂ (causality hj₁ hj₂ C₁ C₂) (ι₂ j₁ j₂) := by
  refine ⟨(isOpenEmbedding_ι₂ hj₁ hj₂).isLocalHomeomorph, fun _ => ⟨⊤, trivial,
    (injective_ι₂ hj₁.injective hj₂.injective).injOn, fun V' _ U hU y _ z _ => ?_⟩⟩
  have hUle : U ≤ O₂ hj₁ hj₂ := by
    intro a ha
    rw [← SetLike.mem_coe, hU] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact ⟨b, rfl⟩
  have hpre : preimageOpens continuous_ι₂ U = V' := SetLike.coe_injective (by
    rw [coe_preimageOpens, hU]; exact preimage_ι₂_image_ι₂ hj₁.injective hj₂.injective _)
  rw [causality_le_ι₂ hC hUle, causality_lt_ι₂ hC hUle, hpre]
  exact ⟨Iff.rfl, Iff.rfl⟩

end CausalityGluing

end Gluing

end Causal
