import Causal.Generated
import Causal.ArcConnected
import Causal.GXStructure
import Causal.SFATransfer
import Mathlib.Topology.Separation.Regular

/-!
# Gluing inventory (DEC-167), the tools: the two forms of gluing, and three ways to refute it

No paper label is certified by this file. It serves the inventory of the target
`T-abs-gluing-models` (programme roadmap): under DEC-167 the sheaf clause of `defi:causalite`
(`ETT.tex:237`) is read *with gluing*, every ETT causality is absolutely minimal
(`def:topological_space_causality_absolutely`, `ETT.tex:397`), and the library's `Causality` will
gain a gluing field whose form is open (OQ-95):

* **hereditary**: `∀ W : Opens M, C.AbsolutelyMinimalOn W` (the sheaf condition on every open);
* **on `M`**: `C.AbsolutelyMinimal`, `def:topological_space_causality_absolutely` as printed.

The hereditary form implies the other (`absolutelyMinimal_of_forall`), and a refutation of the
form on `M` refutes both (`not_forall_of_not_absolutelyMinimal`). The transparent-point line
(`cexemple:point_transparent`, `ETT.tex:472`) separates them.

Three refutation tools, used by the inventory's `NonMinimal` module:

* `le_mem_of_split` / `lt_mem_of_split`: absolute minimality on `W` keeps a
  relation of an open `A ⊔ B ≤ W`, whose parts have disjoint closures, inside the part it starts
  from (the cover `{M ∖ cl B, M ∖ cl A}`). Hence `not_absolutelyMinimal_of_le_of_ne`: on a `T2.5`
  space, a precausality relating two distinct points in *every* open set containing both (the
  shape of `Causality.ofRelation`, kb/0014) is not absolutely minimal.
* `topEnlarge_not_absolutelyMinimal`, `topTotal_not_absolutelyMinimal`: enlarging the relation of
  `M` alone (kb/0014) destroys absolute minimality on a `T1` space as soon as the enlarged
  relation is new; the cover `{M ∖ {x}, M ∖ {y}}` never sees `M`.
* `forall_of_causallyArcConnected`: the positive side, a re-export of
  `Causality.CausallyArcConnected.absolutelyMinimalOn_all` under the inventory's name.

Possibly duplicated by the sibling target `T-abs-gluing-generic` (generic constructions): the two
form lemmas and `forall_of_causallyArcConnected`. They are proved here, in the namespace
`Causal.GluingModels`, so the master merges at graduation.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff | ⚠ weakened: not used; `T2.5` (resp. `T1`) where a refutation separates two points |

## SCOPE (disclosed)

* Nothing here changes a definition. The field's form is the master's (OQ-95).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace GluingModels

open Set TopologicalSpace Topology Relation

universe u

variable {M : Type u} [TopologicalSpace M]

/-! ### The two forms -/

/-- The hereditary form of gluing gives the form on `M`. -/
theorem absolutelyMinimal_of_forall {Q : Precausality M} (h : ∀ W : Opens M, Q.AbsolutelyMinimalOn W) :
    Q.AbsolutelyMinimal :=
  Precausality.absolutelyMinimal_iff.2 (h ⊤)

/-- A refutation of gluing on `M` refutes the hereditary form. -/
theorem not_forall_of_not_absolutelyMinimal {Q : Precausality M} (h : ¬ Q.AbsolutelyMinimal) :
    ¬ ∀ W : Opens M, Q.AbsolutelyMinimalOn W :=
  fun h' => h (absolutelyMinimal_of_forall h')

/-- A refutation on `⊤` is a refutation on `M`. -/
theorem not_absolutelyMinimal_of_not_top {Q : Precausality M} (h : ¬ Q.AbsolutelyMinimalOn ⊤) :
    ¬ Q.AbsolutelyMinimal :=
  fun h' => h (Precausality.absolutelyMinimal_iff.1 h')

/-- Causal arc-connectedness gives the hereditary form. -/
theorem forall_of_causallyArcConnected {C : Causality M} (h : C.CausallyArcConnected) :
    ∀ W : Opens M, C.AbsolutelyMinimalOn W :=
  h.absolutelyMinimalOn_all

/-- The hereditary form passes to the time reversal. -/
theorem forall_dual {C : Causality M} (h : ∀ W : Opens M, C.AbsolutelyMinimalOn W) :
    ∀ W : Opens M, C.dual.AbsolutelyMinimalOn W := fun W =>
  Precausality.dual_absolutelyMinimalOn.2 (h W)

/-! ### Relations of a split open set do not cross -/

section Split

variable {r : Opens M → M → M → Prop}

/-- The two-member cover `{M ∖ cl B, M ∖ cl A}` of `M`, when `cl A` and `cl B` are disjoint. -/
theorem splitCover_covers {A B : Opens M} (hAB : Disjoint (closure (A : Set M)) (closure (B : Set M)))
    (W : Opens M) : ∀ z ∈ W, ∃ O ∈ ({⟨(closure (B : Set M))ᶜ, isClosed_closure.isOpen_compl⟩,
      ⟨(closure (A : Set M))ᶜ, isClosed_closure.isOpen_compl⟩} : Set (Opens M)), z ∈ O := by
  intro z _
  by_cases hz : z ∈ closure (A : Set M)
  · exact ⟨_, Or.inl rfl, fun hzB => hAB.ne_of_mem hz hzB rfl⟩
  · exact ⟨_, Or.inr rfl, hz⟩

/-- One link of a chain over the split cover, starting in `A`, ends in `A`. -/
theorem split_link {A B : Opens M} (hl : ∀ {N : Opens M} {a b : M}, r N a b → a ∈ N)
    (hr : ∀ {N : Opens M} {a b : M}, r N a b → b ∈ N) {a b : M} (ha : a ∈ A)
    (h : ∃ O ∈ ({⟨(closure (B : Set M))ᶜ, isClosed_closure.isOpen_compl⟩,
      ⟨(closure (A : Set M))ᶜ, isClosed_closure.isOpen_compl⟩} : Set (Opens M)),
      r ((A ⊔ B) ⊓ O) a b) : b ∈ A := by
  obtain ⟨O, hO, hab⟩ := h
  rcases hO with rfl | hO
  · obtain ⟨hbAB, hbO⟩ := hr hab
    rcases hbAB with hbA | hbB
    · exact hbA
    · exact absurd (subset_closure hbB) hbO
  · rw [mem_singleton_iff] at hO
    subst hO
    obtain ⟨-, haO⟩ := hl hab
    exact absurd (subset_closure ha) haO

/-- A chain over the split cover, starting in `A`, stays in `A`. -/
theorem split_chain {A B : Opens M} (hl : ∀ {N : Opens M} {a b : M}, r N a b → a ∈ N)
    (hr : ∀ {N : Opens M} {a b : M}, r N a b → b ∈ N) {x y : M} (hx : x ∈ A)
    (h : TransGen (fun a b => ∃ O ∈ ({⟨(closure (B : Set M))ᶜ, isClosed_closure.isOpen_compl⟩,
      ⟨(closure (A : Set M))ᶜ, isClosed_closure.isOpen_compl⟩} : Set (Opens M)),
      r ((A ⊔ B) ⊓ O) a b) x y) : y ∈ A := by
  induction h with
  | single hab => exact split_link hl hr hx hab
  | tail _ hbc ih => exact split_link hl hr ih hbc

/-- **Absolute minimality on `W` keeps the causal relations of a split open set on one side**:
for opens `A`, `B` with disjoint closures and `A ⊔ B ≤ W`, `x ≤_{A ⊔ B} y` with `x ∈ A` forces
`y ∈ A`. -/
theorem le_mem_of_split {Q : Precausality M} {W A B : Opens M}
    (h : Q.AbsolutelyMinimalOn W) (hAB : Disjoint (closure (A : Set M)) (closure (B : Set M)))
    (hW : A ⊔ B ≤ W) {x y : M} (hx : x ∈ A) (hxy : Q.le (A ⊔ B) x y) : y ∈ A :=
  split_chain (r := Q.le) Q.le_mem_left Q.le_mem_right hx
    ((h _ (splitCover_covers hAB W) (A ⊔ B) hW x y).1 hxy)

/-- The chronological half of `le_mem_of_split`. -/
theorem lt_mem_of_split {Q : Precausality M} {W A B : Opens M}
    (h : Q.AbsolutelyMinimalOn W) (hAB : Disjoint (closure (A : Set M)) (closure (B : Set M)))
    (hW : A ⊔ B ≤ W) {x y : M} (hx : x ∈ A) (hxy : Q.lt (A ⊔ B) x y) : y ∈ A :=
  split_chain (r := Q.lt) Q.lt_mem_left Q.lt_mem_right hx
    ((h _ (splitCover_covers hAB W) (A ⊔ B) hW x y).2 hxy)

/-- **A causal relation across a split open set refutes absolute minimality.** -/
theorem not_absolutelyMinimalOn_of_le_split {Q : Precausality M} {W A B : Opens M}
    (hAB : Disjoint (closure (A : Set M)) (closure (B : Set M))) (hW : A ⊔ B ≤ W) {x y : M}
    (hx : x ∈ A) (hy : y ∈ B) (hxy : Q.le (A ⊔ B) x y) : ¬ Q.AbsolutelyMinimalOn W := fun h =>
  hAB.ne_of_mem (subset_closure (le_mem_of_split h hAB hW hx hxy)) (subset_closure hy) rfl

/-- **A chronological relation across a split open set refutes absolute minimality.** -/
theorem not_absolutelyMinimalOn_of_lt_split {Q : Precausality M} {W A B : Opens M}
    (hAB : Disjoint (closure (A : Set M)) (closure (B : Set M))) (hW : A ⊔ B ≤ W) {x y : M}
    (hx : x ∈ A) (hy : y ∈ B) (hxy : Q.lt (A ⊔ B) x y) : ¬ Q.AbsolutelyMinimalOn W := fun h =>
  hAB.ne_of_mem (subset_closure (lt_mem_of_split h hAB hW hx hxy)) (subset_closure hy) rfl

/-- **Non-local relations are not glued** (kb/0014): on a `T2.5` space, a precausality in which
`x ≤_V y` for every open `V` containing two distinct points `x`, `y` is not absolutely minimal.
Every `Causality.ofRelation` whose relation `R` relates two distinct points is of this shape. -/
theorem not_absolutelyMinimal_of_le_of_ne [T25Space M] {Q : Precausality M} {x y : M} (hne : x ≠ y)
    (h : ∀ V : Opens M, x ∈ V → y ∈ V → Q.le V x y) : ¬ Q.AbsolutelyMinimal := by
  obtain ⟨u, hxu, hu, v, hyv, hv, huv⟩ := exists_open_nhds_disjoint_closure hne
  refine not_absolutelyMinimal_of_not_top
    (not_absolutelyMinimalOn_of_le_split (A := ⟨u, hu⟩) (B := ⟨v, hv⟩) huv le_top hxu hyv ?_)
  exact h _ (Or.inl hxu) (Or.inr hyv)

/-- The chronological form of `not_absolutelyMinimal_of_le_of_ne`. -/
theorem not_absolutelyMinimal_of_lt_of_ne [T25Space M] {Q : Precausality M} {x y : M} (hne : x ≠ y)
    (h : ∀ V : Opens M, x ∈ V → y ∈ V → Q.lt V x y) : ¬ Q.AbsolutelyMinimal := by
  obtain ⟨u, hxu, hu, v, hyv, hv, huv⟩ := exists_open_nhds_disjoint_closure hne
  refine not_absolutelyMinimal_of_not_top
    (not_absolutelyMinimalOn_of_lt_split (A := ⟨u, hu⟩) (B := ⟨v, hv⟩) huv le_top hxu hyv ?_)
  exact h _ (Or.inl hxu) (Or.inr hyv)

/-- `Causality.ofRelation` (`Causal.LinesReachable`) relating two distinct points of a `T2.5`
space is not absolutely minimal. -/
theorem ofRelation_not_absolutelyMinimal [T25Space M] {R S : M → M → Prop} {hrefl htrans hStrans hSR
    hright hleft} {x y : M} (hne : x ≠ y) (hR : R x y) :
    ¬ (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).AbsolutelyMinimal :=
  not_absolutelyMinimal_of_le_of_ne hne fun _ hx hy => ⟨hx, hy, hR⟩

end Split

/-! ### Enlarging the relation of `M` alone -/

section TopEnlarge

/-- Over a cover by open sets different from `⊤`, a chain of `topEnlarge`-links is a chain of
`C`-links, hence a relation of `C` on `M`. -/
theorem le_top_of_chain_ne_top {C : Causality M} {S : Set (Opens M)} (hS : ∀ O ∈ S, O ≠ ⊤)
    (r : Opens M → M → M → Prop) (hr : ∀ {N : Opens M} {a b : M}, N ≠ ⊤ → r N a b → C.le N a b)
    {x y : M} (h : TransGen (fun a b => ∃ O ∈ S, r (⊤ ⊓ O) a b) x y) : C.le ⊤ x y := by
  have link : ∀ a b, (∃ O ∈ S, r (⊤ ⊓ O) a b) → C.le ⊤ a b := by
    rintro a b ⟨O, hO, hab⟩
    rw [top_inf_eq] at hab
    exact C.le_mono le_top (hr (hS O hO) hab)
  induction h with
  | single hab => exact link _ _ hab
  | tail _ hbc ih => exact C.le_trans ih (link _ _ hbc)

/-- The cover `{M ∖ {x}, M ∖ {y}}` of a `T1` space, `x ≠ y`: no member is `⊤`. -/
theorem pairCover {x y : M} [T1Space M] (hne : x ≠ y) :
    (∀ z ∈ (⊤ : Opens M), ∃ O ∈ ({⟨{x}ᶜ, isOpen_compl_singleton⟩, ⟨{y}ᶜ, isOpen_compl_singleton⟩} :
      Set (Opens M)), z ∈ O) ∧
    ∀ O ∈ ({⟨{x}ᶜ, isOpen_compl_singleton⟩, ⟨{y}ᶜ, isOpen_compl_singleton⟩} : Set (Opens M)),
      O ≠ ⊤ := by
  refine ⟨fun z _ => ?_, fun O hO hOtop => ?_⟩
  · by_cases hz : z = x
    · subst hz; exact ⟨_, Or.inr rfl, hne⟩
    · exact ⟨_, Or.inl rfl, hz⟩
  · rcases hO with rfl | hO
    · have : x ∈ ((⊤ : Opens M) : Set M) := trivial
      rw [← hOtop] at this
      exact this rfl
    · rw [mem_singleton_iff] at hO
      subst hO
      have : y ∈ ((⊤ : Opens M) : Set M) := trivial
      rw [← hOtop] at this
      exact this rfl

/-- **`Causality.topEnlarge` is not glued** (`Causal.GXStructure`, kb/0014): on a `T1` space,
if `C` does not relate two distinct points `x`, `y` on `M`, the causality relating every pair at
`M` alone is not absolutely minimal. `timelikeLineTop` is the case of the timelike line. -/
theorem topEnlarge_not_absolutelyMinimal [T1Space M] {C : Causality M} {x y : M} (hne : x ≠ y)
    (hxy : ¬ C.le ⊤ x y) : ¬ C.topEnlarge.AbsolutelyMinimal := by
  intro h
  obtain ⟨hS, hS'⟩ := pairCover (M := M) hne
  have hc := ((Precausality.absolutelyMinimal_iff.1 h) _ hS ⊤ le_rfl x y).1 (Or.inl rfl)
  exact hxy (le_top_of_chain_ne_top hS' _ (fun hN hab => hab.resolve_left hN) hc)

/-- **`SFATransfer.topTotal` is not glued** (`Causal.SFATransfer`, kb/0014): the same, for the
causality relating every pair causally and chronologically at `M` alone. -/
theorem topTotal_not_absolutelyMinimal [T1Space M] {D : Causality M} {x y : M} (hne : x ≠ y)
    (hxy : ¬ D.le ⊤ x y) : ¬ (SFATransfer.topTotal D).AbsolutelyMinimal := by
  intro h
  obtain ⟨hS, hS'⟩ := pairCover (M := M) hne
  have hc := ((Precausality.absolutelyMinimal_iff.1 h) _ hS ⊤ le_rfl x y).1 (Or.inl rfl)
  exact hxy (le_top_of_chain_ne_top hS' _ (fun hN hab => hab.resolve_left hN) hc)

end TopEnlarge

end GluingModels

end Causal
