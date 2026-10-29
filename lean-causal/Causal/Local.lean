import Causal.Generated

/-!
# A causality given on an open subset extends to the whole space

`Causal.Generated` carries "each `U_i` is endowed with a causality" by a causality on `M` of which
only the restriction to `U_i` is read. This file is the justification: a precausality, or a
causality, given on the open subsets of `W` alone (`LocalPrecausality W`, `LocalCausality W`) is
the restriction of one given on `M` (`extend`, `extend_le_iff`, `extend_lt_iff`), and absolute
minimality and causal plainness of `W` are read on the restriction. So nothing is lost by
quantifying over causalities on `M`.

No paper label is certified by this file.

## SCOPE (disclosed)

* The extension adds the diagonal to the causal relation and nothing to the chronological one. It
  is one extension among others; no statement of the library depends on which.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

universe u

variable {M : Type u} [TopologicalSpace M]

/-- A precausality on the open subset `W`: the axioms of `Precausality`, asked of the open
subsets of `W` only. -/
structure LocalPrecausality (W : Opens M) where
  le : Opens M → M → M → Prop
  lt : Opens M → M → M → Prop
  le_mem_left : ∀ {U : Opens M} {x y : M}, U ≤ W → le U x y → x ∈ U
  le_mem_right : ∀ {U : Opens M} {x y : M}, U ≤ W → le U x y → y ∈ U
  lt_mem_left : ∀ {U : Opens M} {x y : M}, U ≤ W → lt U x y → x ∈ U
  lt_mem_right : ∀ {U : Opens M} {x y : M}, U ≤ W → lt U x y → y ∈ U
  le_refl : ∀ {U : Opens M} {x : M}, U ≤ W → x ∈ U → le U x x
  le_trans : ∀ {U : Opens M} {x y z : M}, U ≤ W → le U x y → le U y z → le U x z
  lt_trans : ∀ {U : Opens M} {x y z : M}, U ≤ W → lt U x y → lt U y z → lt U x z
  le_mono : ∀ {U V : Opens M}, U ≤ W → V ≤ U → ∀ {x y : M}, le V x y → le U x y
  lt_mono : ∀ {U V : Opens M}, U ≤ W → V ≤ U → ∀ {x y : M}, lt V x y → lt U x y

/-- A causality on the open subset `W`. -/
structure LocalCausality (W : Opens M) extends LocalPrecausality W where
  le_of_lt : ∀ {U : Opens M} {x y : M}, U ≤ W → lt U x y → le U x y
  isOpen_lt_right : ∀ (U : Opens M) (x : M), U ≤ W → IsOpen {y | lt U x y}
  isOpen_lt_left : ∀ (U : Opens M) (x : M), U ≤ W → IsOpen {y | lt U y x}

variable {W : Opens M}

namespace LocalPrecausality

variable (L : LocalPrecausality W)

/-- The extension of a precausality on `W` to `M`: the diagonal is added to the causal
relation. -/
def extend : Precausality M where
  le U x y := (x = y ∧ x ∈ U) ∨ L.le (U ⊓ W) x y
  lt U x y := L.lt (U ⊓ W) x y
  le_mem_left := by
    rintro U x y (⟨-, hx⟩ | h)
    · exact hx
    · exact (inf_le_left : U ⊓ W ≤ U) (L.le_mem_left inf_le_right h)
  le_mem_right := by
    rintro U x y (⟨rfl, hx⟩ | h)
    · exact hx
    · exact (inf_le_left : U ⊓ W ≤ U) (L.le_mem_right inf_le_right h)
  lt_mem_left h := (inf_le_left : _ ⊓ W ≤ _) (L.lt_mem_left inf_le_right h)
  lt_mem_right h := (inf_le_left : _ ⊓ W ≤ _) (L.lt_mem_right inf_le_right h)
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans := by
    rintro U x y z (⟨rfl, -⟩ | h₁) h₂
    · exact h₂
    · rcases h₂ with ⟨rfl, -⟩ | h₂
      · exact Or.inr h₁
      · exact Or.inr (L.le_trans inf_le_right h₁ h₂)
  lt_trans h₁ h₂ := L.lt_trans inf_le_right h₁ h₂
  le_mono := by
    rintro U V hVU x y (⟨rfl, hx⟩ | h)
    · exact Or.inl ⟨rfl, hVU hx⟩
    · exact Or.inr (L.le_mono inf_le_right (inf_le_inf_right _ hVU) h)
  lt_mono hVU _ _ h := L.lt_mono inf_le_right (inf_le_inf_right _ hVU) h

variable {L} {U : Opens M} {x y : M}

/-- The extension restricts to the given precausality on the open subsets of `W`. -/
theorem extend_le_iff (hU : U ≤ W) : L.extend.le U x y ↔ L.le U x y := by
  have hUW : U ⊓ W = U := inf_eq_left.2 hU
  constructor
  · rintro (⟨rfl, hx⟩ | h)
    · exact L.le_refl hU hx
    · rwa [hUW] at h
  · intro h
    refine Or.inr ?_
    rwa [hUW]

theorem extend_lt_iff (hU : U ≤ W) : L.extend.lt U x y ↔ L.lt U x y := by
  have hUW : U ⊓ W = U := inf_eq_left.2 hU
  constructor
  · intro h
    have h' : L.lt (U ⊓ W) x y := h
    rwa [hUW] at h'
  · intro h
    show L.lt (U ⊓ W) x y
    rwa [hUW]

end LocalPrecausality

namespace LocalCausality

variable (L : LocalCausality W)

/-- The extension of a causality on `W` to `M`. -/
def extend : Causality M where
  toPrecausality := L.toLocalPrecausality.extend
  le_of_lt h := Or.inr (L.le_of_lt inf_le_right h)
  isOpen_lt_right U x := L.isOpen_lt_right (U ⊓ W) x inf_le_right
  isOpen_lt_left U x := L.isOpen_lt_left (U ⊓ W) x inf_le_right

variable {L} {U : Opens M} {x y : M}

theorem extend_le_iff (hU : U ≤ W) : L.extend.le U x y ↔ L.le U x y :=
  LocalPrecausality.extend_le_iff hU

theorem extend_lt_iff (hU : U ≤ W) : L.extend.lt U x y ↔ L.lt U x y :=
  LocalPrecausality.extend_lt_iff hU

end LocalCausality

/-- The restriction of a causality on `M` to an open subset. -/
def Causality.restrict (C : Causality M) (W : Opens M) : LocalCausality W where
  le := C.le
  lt := C.lt
  le_mem_left _ h := C.le_mem_left h
  le_mem_right _ h := C.le_mem_right h
  lt_mem_left _ h := C.lt_mem_left h
  lt_mem_right _ h := C.lt_mem_right h
  le_refl _ hx := C.le_refl hx
  le_trans _ h₁ h₂ := C.le_trans h₁ h₂
  lt_trans _ h₁ h₂ := C.lt_trans h₁ h₂
  le_mono _ hVU _ _ h := C.le_mono hVU h
  lt_mono _ hVU _ _ h := C.lt_mono hVU h
  le_of_lt _ h := C.le_of_lt h
  isOpen_lt_right U x _ := C.isOpen_lt_right U x
  isOpen_lt_left U x _ := C.isOpen_lt_left U x

/-- Every causality on the open subset `W` is the restriction of a causality on `M`: the
relations of the extension and the given ones agree on every open subset of `W`. -/
theorem LocalCausality.exists_extension (L : LocalCausality W) :
    ∃ C : Causality M, ∀ U : Opens M, U ≤ W → ∀ x y : M,
      (C.le U x y ↔ L.le U x y) ∧ (C.lt U x y ↔ L.lt U x y) :=
  ⟨L.extend, fun _ hU _ _ => ⟨extend_le_iff hU, extend_lt_iff hU⟩⟩

end Causal
