import Causal.LinesReachable
import Causal.ArcConnected
import Causal.PushUp
import Mathlib.Topology.Semicontinuity.Basic

/-!
# The two forms of push-up: plainness without push-up, and why the witness cannot be local

Target `T-ett-deux-pushup` (2026-11-20). Cited, **unmarked** (SCOPE: the witness of the converse
is not absolutely minimal, and cannot be): `rem:deux_pushup` — `ETT.tex:314`. It opposes
`defi:causalement_plat` — `ETT.tex:283` (`Causality.CausallyPlain`) to `defi:pushup` —
`ETT.tex:307` (`Causality.PushUp`). "Push-up" in this file is always the relational property of
`defi:pushup`, which is the one the remark names; the paper also calls plainness "the push-up
property" (`ETT.tex:209–210`, `290`), and in that sense the converse would say nothing.

> Definitions \ref{defi:causalement_plat} and \ref{defi:pushup} are the topological and the
> relational form of one classical phenomenon, and neither implies the other. The lightlike line
> has $I^\pm=\emptyset$, so it has the push-up property vacuously while failing to be causally
> plain (Remark \ref{rem:droites_pas_plates}). Conversely, causal plainness is a statement about
> $\mathrm{Int}\left(J^\pm\right)$ and is silent at a point whose causal future or past has empty
> interior. (`ETT.tex:315–320`)

## What is proved (no `sorry` in this file)

* **Both halves, in the library's reading of `defi:causalite`** (the "equivalently" form, no
  gluing, kb/0014): `deux_pushup`, `deux_pushup_neither`. Push-up without plainness: the
  lightlike line (`lightlikeLine_pushUp`, `lightlikeLine_not_causallyPlain`, reused), which is
  moreover causal and absolutely minimal (`lightlikeLine_absolutelyMinimal`). Plainness without
  push-up: `deuxPushup`, a causal causality on `ℝ` (second countable, Hausdorff):
  `deuxPushup_causallyPlain`, `deuxPushup_not_pushUp` (`-2 ≤ -1 ≪ 1`, not `-2 ≪ 1`),
  `deuxPushup_isCausal`. Its chronological relation is `a ≪ b ⇔ φ(a) < ψ(b)` with `ψ ≤ φ`,
  `φ` upper and `ψ` lower semicontinuous (`DeuxPushup.phi`, `DeuxPushup.psi`): the order of `ℝ`
  away from `-2, -1, 0, 1`, with the times `]0, 3]` skipped at `0`; its causal relation adds the one
  pair `-2 ≤ -1` to the reflexive closure (`DeuxPushup.extLe`). Plainness holds because
  `I^+(-1) = ]0, +∞[` lies in the closure of `I^+(-2) = ]0, +∞[ ∖ {1}`
  (`DeuxPushup.interior_extLe_subset_closure`, `Causality.ofRelation_causallyPlain`).
* **Finding: the converse independence is false for absolutely minimal causalities.** On a `T1`
  space, causal plainness and absolute minimality give push-up
  (`Causality.pushUp_of_causallyPlain_of_absolutelyMinimal`; on an open subset,
  `Causality.pushUpOn_of_causallyPlainOn_of_absolutelyMinimalOn`; the asymmetry,
  `deux_pushup_absolutelyMinimal`). The mechanism: absolute minimality makes every `≪_U`
  interpolate (`Causality.interpolatesOn_of_absolutelyMinimalOn`: cover by the complements of the
  two end points), and plainness plus interpolation is push-up
  (`Causality.pushUpOn_of_causallyPlainOn_of_interpolatesOn`). So `deuxPushup` is neither
  absolutely minimal nor interpolating (`deuxPushup_not_absolutelyMinimal`,
  `deuxPushup_not_interpolates`), and no witness of the converse can be.
* **Finding: the remark's reason is not the mechanism.** A failure `x ≤_U y ≪_U z`, not
  `x ≪_U z`, puts `z` in `Int J^+_U(x)` and `y` in `Int J^-_U(z)`
  (`Causality.mem_interior_Jplus_of_le_of_lt`, `Causality.mem_interior_Jminus_of_lt_of_le`); at a
  point whose causal future (past) has empty interior the future (past) clauses of `defi:pushup`
  hold vacuously (`Causality.pushUp_future_of_interior_Jplus_eq_empty`,
  `Causality.pushUp_past_of_interior_Jminus_eq_empty`). What plainness leaves open is the gap
  between `I^+_U(x)` and its closure (`Causality.mem_closure_Iplus_of_le_of_lt_of_causallyPlain`),
  and only a chronological relation without interpolation reaches into it.

## Hypothesis checklist

| paper | here |
|---|---|
| topological spacetime: second countable Hausdorff (`def:category_topological_spacetimes`) | ✓ the witnesses live on `ℝ`; the finding asks `T1Space` only (⚠ weakened) |
| a causality (`defi:causalite`) | ✓ the "equivalently" form (`Causality`, kb/0014) for the witnesses; the finding adds absolute minimality of `M`, which a gluing reading of "sheaf" implies (SCOPE) |
| the lightlike line (`ex:causalities_lines`, item 2) | ✓ `lightlikeLine` |

## SCOPE (disclosed)

* **The plain witness is non-local, and has to be.** `deuxPushup` has `-1 ≪ 1` with nothing
  chronologically between them; its relations on `U` are the restrictions of global relations
  (`Causality.ofRelation`, kb/0014, kb/0019). By the finding, any causality on a `T1` space which
  is causally plain and fails push-up is not absolutely minimal, so neither the "spokes" device
  (kb/0037) nor any generated causality can serve. `defi:causalite` (`ETT.tex:238`) calls a
  causality "a sheaf on `M` with values in `𝐂`". The extension maps `(V, ≤_V) → (U, ≤_U)` make it a
  precosheaf; read with gluing, the relations of `U` are the colimit — the relations generated by
  those of the members of any open cover of `U` — which is absolute minimality of every open subset.
  In that reading causal plainness implies push-up for every topological spacetime, and the second
  half of "neither implies the other" (`ETT.tex:316`, also `ETT.tex:303`) is false. In the
  "equivalently" form (`ETT.tex:245–251`), which the library carries, the remark holds. Which
  reading is the paper's is a question for the author; the label is not marked meanwhile.
* The remark's second paragraph (`ETT.tex:322–327`) cites other results and is not restated
  here. Its density sentence is the one already recorded under `prop:K_plongement_ordre`: push-up
  gives density of `I^-(x)` in `J^-(x)` only together with `J^-(x) ⊂ Z^-`
  (`Jminus_subset_closure_Iminus_of_pushUp`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation

universe u

variable {M : Type u}

section Topological

variable [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-- The chronological relation **interpolates** in every open subset of `W`: `x ≪_U z` gives
`x ≪_U w ≪_U z` for some `w`. Not a notion of the paper. -/
def InterpolatesOn (W : Opens M) : Prop :=
  ∀ U : Opens M, U ≤ W → ∀ ⦃x z : M⦄, C.lt U x z → ∃ w, C.lt U x w ∧ C.lt U w z

/-- Interpolation in every open set. -/
def Interpolates : Prop := C.InterpolatesOn ⊤

variable {C} {W U : Opens M} {x y z : M}

/-! ### Where a failure of push-up sits -/

/-- A causal relation followed by a chronological one ends in the interior of the causal
future: `z ∈ Int J^+_U(x)` whenever `x ≤_U y ≪_U z`. -/
theorem mem_interior_Jplus_of_le_of_lt (hxy : C.le U x y) (hyz : C.lt U y z) :
    z ∈ interior (C.Jplus U {x}) := by
  refine interior_maximal (fun v hv => ?_) (C.isOpen_lt_right U y) hyz
  rw [Precausality.mem_Jplus_singleton]
  exact C.le_trans hxy (C.le_of_lt hv)

/-- `x ∈ Int J^-_U(z)` whenever `x ≪_U y ≤_U z`. -/
theorem mem_interior_Jminus_of_lt_of_le (hxy : C.lt U x y) (hyz : C.le U y z) :
    x ∈ interior (C.Jminus U {z}) := by
  refine interior_maximal (fun v hv => ?_) (C.isOpen_lt_left U y) hxy
  rw [Precausality.mem_Jminus_singleton]
  exact C.le_trans (C.le_of_lt hv) hyz

/-- At a point whose causal future in `U` has empty interior, the two future clauses of
`defi:pushup` hold, vacuously: `I^+_U(x) = ∅` and `I^+_U(J^+_U(x)) = ∅`. -/
theorem pushUp_future_of_interior_Jplus_eq_empty (h : interior (C.Jplus U {x}) = ∅) :
    C.Jplus U (C.Iplus U {x}) ⊆ C.Iplus U {x} ∧ C.Iplus U (C.Jplus U {x}) ⊆ C.Iplus U {x} := by
  have h1 : C.Iplus U {x} = ∅ := by
    rw [← subset_empty_iff, ← h]
    exact Iplus_subset_interior_Jplus
  have h2 : C.Iplus U (C.Jplus U {x}) = ∅ := by
    rw [← subset_empty_iff, ← h]
    refine interior_maximal (fun v hv => ?_) isOpen_Iplus
    rw [← Precausality.Jplus_Jplus (P := C.toPrecausality)]
    exact Iplus_subset_Jplus hv
  refine ⟨?_, by rw [h2]; exact empty_subset _⟩
  rw [h1]
  rintro v ⟨w, hw, -⟩
  exact hw

/-- The past form of `pushUp_future_of_interior_Jplus_eq_empty`. -/
theorem pushUp_past_of_interior_Jminus_eq_empty (h : interior (C.Jminus U {x}) = ∅) :
    C.Jminus U (C.Iminus U {x}) ⊆ C.Iminus U {x} ∧
      C.Iminus U (C.Jminus U {x}) ⊆ C.Iminus U {x} :=
  pushUp_future_of_interior_Jplus_eq_empty (C := C.dual) h

/-- What causal plainness does say about a failure `x ≤_U y ≪_U z`: `z` lies in the closure of
`I^+_U(x)`. -/
theorem mem_closure_Iplus_of_le_of_lt_of_causallyPlain (hp : C.CausallyPlain) (hxy : C.le U x y)
    (hyz : C.lt U y z) : z ∈ closure (C.Iplus U {x}) :=
  (hp U {x}).1 (mem_interior_Jplus_of_le_of_lt hxy hyz)

/-! ### Plainness and interpolation give push-up -/

/-- **Causal plainness and interpolation give push-up**, on an open subset `W`. -/
theorem pushUpOn_of_causallyPlainOn_of_interpolatesOn (hp : C.CausallyPlainOn W)
    (hi : C.InterpolatesOn W) : C.PushUpOn W := by
  intro U hU x y z
  refine ⟨fun hxy hyz => ?_, fun hxy hyz => ?_⟩
  · -- `x ≪ y ≤ z`: interpolate `x ≪ w ≪ y`; `I^+(x) ∩ I^-(y)` is open in `J^-(z)`
    obtain ⟨w, hxw, hwy⟩ := hi U hU hxy
    have hO : IsOpen ({v | C.lt U x v} ∩ {v | C.lt U v y}) :=
      (C.isOpen_lt_right U x).inter (C.isOpen_lt_left U y)
    have hOJ : {v | C.lt U x v} ∩ {v | C.lt U v y} ⊆ C.Jminus U {z} := fun v hv => by
      rw [Precausality.mem_Jminus_singleton]
      exact C.le_trans (C.le_of_lt hv.2) hyz
    have hw : w ∈ closure (C.Iminus U {z}) :=
      (hp U hU {z}).2 (interior_maximal hOJ hO ⟨hxw, hwy⟩)
    obtain ⟨v, hvO, hvI⟩ := mem_closure_iff.1 hw _ hO ⟨hxw, hwy⟩
    rw [Precausality.mem_Iminus_singleton] at hvI
    exact C.lt_trans hvO.1 hvI
  · -- `x ≤ y ≪ z`: interpolate `y ≪ w ≪ z`; `I^+(y) ∩ I^-(z)` is open in `J^+(x)`
    obtain ⟨w, hyw, hwz⟩ := hi U hU hyz
    have hO : IsOpen ({v | C.lt U y v} ∩ {v | C.lt U v z}) :=
      (C.isOpen_lt_right U y).inter (C.isOpen_lt_left U z)
    have hOJ : {v | C.lt U y v} ∩ {v | C.lt U v z} ⊆ C.Jplus U {x} := fun v hv => by
      rw [Precausality.mem_Jplus_singleton]
      exact C.le_trans hxy (C.le_of_lt hv.1)
    have hw : w ∈ closure (C.Iplus U {x}) :=
      (hp U hU {x}).1 (interior_maximal hOJ hO ⟨hyw, hwz⟩)
    obtain ⟨v, hvO, hvI⟩ := mem_closure_iff.1 hw _ hO ⟨hyw, hwz⟩
    rw [Precausality.mem_Iplus_singleton] at hvI
    exact C.lt_trans hvI hvO.2

/-- Absolute minimality makes the chronological relation interpolate, on a `T1` space: cover
by the complements of the two end points. -/
theorem interpolatesOn_of_absolutelyMinimalOn [T1Space M] (h : C.AbsolutelyMinimalOn W) :
    C.InterpolatesOn W := by
  intro U hU x z hxz
  by_cases hx : x = z
  · subst hx
    exact ⟨x, hxz, hxz⟩
  · let O : Opens M := ⟨{z}ᶜ, isOpen_compl_singleton⟩
    obtain ⟨r, hxr, hrz⟩ := Precausality.AbsolutelyMinimalOn.exists_lt_inf h hU O
      (show x ∈ O from hx) hxz
    have hrO : r ∈ O := (inf_le_right : U ⊓ O ≤ O) (C.lt_mem_right hxr)
    refine ⟨r, C.lt_mono inf_le_left hxr, ?_⟩
    rcases hrz with hrz | hrz
    · exact absurd hrz hrO
    · exact hrz

/-- **Finding.** On a `T1` space, an absolutely minimal, causally plain open subset has the
push-up property. -/
theorem pushUpOn_of_causallyPlainOn_of_absolutelyMinimalOn [T1Space M]
    (hmin : C.AbsolutelyMinimalOn W) (hp : C.CausallyPlainOn W) : C.PushUpOn W :=
  pushUpOn_of_causallyPlainOn_of_interpolatesOn hp (interpolatesOn_of_absolutelyMinimalOn hmin)

/-- **Finding.** On a `T1` space, an absolutely minimal, causally plain causality has the
push-up property (`defi:pushup`): the converse half of `rem:deux_pushup` has no absolutely
minimal witness. -/
theorem pushUp_of_causallyPlain_of_absolutelyMinimal [T1Space M] (hmin : C.AbsolutelyMinimal)
    (hp : C.CausallyPlain) : C.PushUp :=
  pushUpOn_top.1 (pushUpOn_of_causallyPlainOn_of_absolutelyMinimalOn
    (Precausality.absolutelyMinimal_iff.1 hmin) (causallyPlainOn_top.2 hp))

end Causality

end Topological

/-! ### The lightlike line is absolutely minimal -/

/-- The lightlike line is absolutely minimal in every open subset: its causal relation is the
timelike line's, and it has no chronological relation. -/
theorem lightlikeLine_absolutelyMinimalOn (W : Opens ℝ) : lightlikeLine.AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  exact ⟨fun hxy => ((timelikeLine_absolutelyMinimalOn W) S hS V hV x y).1 hxy,
    fun hxy => hxy.elim⟩

theorem lightlikeLine_absolutelyMinimal : lightlikeLine.AbsolutelyMinimal :=
  Precausality.absolutelyMinimal_iff.2 (lightlikeLine_absolutelyMinimalOn ⊤)

/-! ### A relation with one extra causal pair -/

namespace DeuxPushup

/-- The reflexive closure of `S`, with one extra causal pair `x ≤ y` and its consequences:
`a ≤ b` iff `a = b`, or `a ≪ b`, or `a ≤ x` and `y ≤ b` in the reflexive closure of `S`. -/
def extLe (S : M → M → Prop) (x y a b : M) : Prop :=
  a = b ∨ S a b ∨ ((a = x ∨ S a x) ∧ (y = b ∨ S y b))

variable {S : M → M → Prop} {x y : M}

theorem extLe_refl (a : M) : extLe S x y a a := Or.inl rfl

theorem extLe_of_rel {a b : M} (h : S a b) : extLe S x y a b := Or.inr (Or.inl h)

theorem extLe_trans (hS : ∀ a b c, S a b → S b c → S a c) (a b c : M) :
    extLe S x y a b → extLe S x y b c → extLe S x y a c := by
  have r0 : ∀ {a b c : M}, (a = b ∨ S a b) → (b = c ∨ S b c) → (a = c ∨ S a c) := by
    rintro a b c (rfl | hab) (rfl | hbc)
    · exact Or.inl rfl
    · exact Or.inr hbc
    · exact Or.inr hab
    · exact Or.inr (hS _ _ _ hab hbc)
  rintro (rfl | hab | ⟨hax, hyb⟩) (rfl | hbc | ⟨hbx, hyc⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hbc)
  · exact Or.inr (Or.inr ⟨hbx, hyc⟩)
  · exact Or.inr (Or.inl hab)
  · exact Or.inr (Or.inl (hS _ _ _ hab hbc))
  · exact Or.inr (Or.inr ⟨r0 (Or.inr hab) hbx, hyc⟩)
  · exact Or.inr (Or.inr ⟨hax, hyb⟩)
  · exact Or.inr (Or.inr ⟨hax, r0 hyb (Or.inr hbc)⟩)
  · exact Or.inr (Or.inr ⟨hax, hyc⟩)

/-- Time reversal of `extLe`: reversing `S` swaps the two ends of the extra pair. -/
theorem extLe_flip {a b : M} : extLe (flip S) y x a b ↔ extLe S x y b a := by
  unfold extLe flip
  constructor
  · rintro (h | h | ⟨h₁, h₂⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h₂.imp Eq.symm id, h₁.imp Eq.symm id⟩)
  · rintro (h | h | ⟨h₁, h₂⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h₂.imp Eq.symm id, h₁.imp Eq.symm id⟩)

variable [TopologicalSpace M]

/-- **Plainness of the future, for one global relation.** If every non-empty open set holds a
pair `a ≪ b` with `a ≠ y`, and `I^+(y) ⊂ closure I^+(x)`, then the extra pair `x ≤ y` keeps the
interior of every causal future in the closure of the chronological one. -/
theorem interior_extLe_subset_closure (hS : ∀ a b c, S a b → S b c → S a c)
    (hrich : ∀ O : Set M, IsOpen O → O.Nonempty → ∃ a ∈ O, ∃ b ∈ O, a ≠ y ∧ S a b)
    (hyx : {b | S y b} ⊆ closure {b | S x b}) (A : Set M) :
    interior {b | ∃ a ∈ A, extLe S x y a b} ⊆ closure {b | ∃ a ∈ A, S a b} := by
  intro w hw
  rw [mem_closure_iff]
  intro N hN hwN
  have hO : IsOpen (N ∩ interior {b | ∃ a ∈ A, extLe S x y a b}) := hN.inter isOpen_interior
  -- a chronological pair `a ≪ b` near `w`, with `a ≠ y`
  obtain ⟨a, haO, b, hbO, hay, hab⟩ := hrich _ hO ⟨w, hwN, hw⟩
  obtain ⟨a', ha'A, ha'a⟩ := interior_subset haO.2
  rcases ha'a with rfl | ha'a | ⟨ha'x, hya⟩
  · exact ⟨b, hbO.1, a', ha'A, hab⟩
  · exact ⟨b, hbO.1, a', ha'A, hS _ _ _ ha'a hab⟩
  · -- `a' ≤ x`, `y ≪ a`: `a ∈ I^+(y) ⊂ closure I^+(x) ⊂ closure I^+(a')`
    have hya' : S y a := hya.resolve_left fun h => hay h.symm
    obtain ⟨v, hvO, hxv⟩ := mem_closure_iff.1 (hyx hya') _ hO haO
    refine ⟨v, hvO.1, a', ha'A, ?_⟩
    rcases ha'x with rfl | ha'x
    · exact hxv
    · exact hS _ _ _ ha'x hxv

end DeuxPushup

/-- A causality built from one global relation (`Causality.ofRelation`) is causally plain as
soon as the global relations are. -/
theorem Causality.ofRelation_causallyPlain [TopologicalSpace M] {R S : M → M → Prop} (hrefl : ∀ x, R x x)
    (htrans : ∀ x y z, R x y → R y z → R x z) (hStrans : ∀ x y z, S x y → S y z → S x z)
    (hSR : ∀ x y, S x y → R x y) (hright : ∀ x, IsOpen {y | S x y})
    (hleft : ∀ y, IsOpen {x | S x y})
    (hfut : ∀ A : Set M, interior {b | ∃ a ∈ A, R a b} ⊆ closure {b | ∃ a ∈ A, S a b})
    (hpast : ∀ A : Set M, interior {b | ∃ a ∈ A, R b a} ⊆ closure {b | ∃ a ∈ A, S b a}) :
    (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).CausallyPlain := by
  intro U A
  set C := Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft
  have hJp : C.Jplus U A = (U : Set M) ∩ {b | ∃ a ∈ A ∩ U, R a b} := by
    ext b
    simp only [C, Precausality.Jplus, Causality.ofRelation, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨a, ha, haU, hbU, hab⟩
      exact ⟨hbU, a, ⟨ha, haU⟩, hab⟩
    · rintro ⟨hbU, a, ⟨ha, haU⟩, hab⟩
      exact ⟨a, ha, haU, hbU, hab⟩
  have hIp : C.Iplus U A = (U : Set M) ∩ {b | ∃ a ∈ A ∩ U, S a b} := by
    ext b
    simp only [C, Precausality.Iplus, Causality.ofRelation, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨a, ha, haU, hbU, hab⟩
      exact ⟨hbU, a, ⟨ha, haU⟩, hab⟩
    · rintro ⟨hbU, a, ⟨ha, haU⟩, hab⟩
      exact ⟨a, ha, haU, hbU, hab⟩
  have hJm : C.Jminus U A = (U : Set M) ∩ {b | ∃ a ∈ A ∩ U, R b a} := by
    ext b
    simp only [C, Precausality.Jminus, Causality.ofRelation, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨a, ha, hbU, haU, hab⟩
      exact ⟨hbU, a, ⟨ha, haU⟩, hab⟩
    · rintro ⟨hbU, a, ⟨ha, haU⟩, hab⟩
      exact ⟨a, ha, hbU, haU, hab⟩
  have hIm : C.Iminus U A = (U : Set M) ∩ {b | ∃ a ∈ A ∩ U, S b a} := by
    ext b
    simp only [C, Precausality.Iminus, Causality.ofRelation, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨a, ha, hbU, haU, hab⟩
      exact ⟨hbU, a, ⟨ha, haU⟩, hab⟩
    · rintro ⟨hbU, a, ⟨ha, haU⟩, hab⟩
      exact ⟨a, ha, hbU, haU, hab⟩
  refine ⟨?_, ?_⟩
  · rw [hJp, hIp, interior_inter, U.isOpen.interior_eq]
    exact (inter_subset_inter_right _ (hfut _)).trans U.isOpen.inter_closure
  · rw [hJm, hIm, interior_inter, U.isOpen.interior_eq]
    exact (inter_subset_inter_right _ (hpast _)).trans U.isOpen.inter_closure

/-! ### The witness on `ℝ` -/

namespace DeuxPushup

/-- The time at which a point stops being a chronological past: `t`, raised by `3` on
`[0, +∞[` (the jump at `0`), and raised at `-2` and `-1`. -/
noncomputable def phi (t : ℝ) : ℝ :=
  t + indicator (Ici 0) (fun _ => (3 : ℝ)) t + indicator {(-2 : ℝ)} (fun _ => (4 : ℝ)) t +
    indicator {(-1 : ℝ)} (fun _ => (2 : ℝ)) t

/-- The time at which a point starts being a chronological future: `t`, raised by `3` on
`]0, +∞[`, and lowered at `1`. -/
noncomputable def psi (t : ℝ) : ℝ :=
  t + indicator (Ioi 0) (fun _ => (3 : ℝ)) t + indicator {(1 : ℝ)} (fun _ => (-2 : ℝ)) t

/-- The chronological relation of the witness: `a ≪ b` iff `φ(a) < ψ(b)`. -/
def lt (a b : ℝ) : Prop := phi a < psi b

/-- The causal relation of the witness: `≪`, the diagonal, and the extra pair `-2 ≤ -1`. -/
def le (a b : ℝ) : Prop := extLe lt (-2) (-1) a b

theorem psi_le_phi (t : ℝ) : psi t ≤ phi t := by
  unfold psi phi
  simp only [indicator_apply, mem_Ici, mem_Ioi, mem_singleton_iff]
  split_ifs <;> linarith

theorem lt_trans' (a b c : ℝ) : lt a b → lt b c → lt a c :=
  fun hab hbc => hab.trans (lt_of_le_of_lt (psi_le_phi b) hbc)

theorem psi_lowerSemicontinuous : LowerSemicontinuous psi := by
  have h1 : LowerSemicontinuous (fun t : ℝ => t) := continuous_id.lowerSemicontinuous
  have h2 : LowerSemicontinuous (indicator (Ioi (0 : ℝ)) (fun _ => (3 : ℝ))) :=
    isOpen_Ioi.lowerSemicontinuous_indicator (by norm_num)
  have h3 : LowerSemicontinuous (indicator {(1 : ℝ)} (fun _ => (-2 : ℝ))) :=
    isClosed_singleton.lowerSemicontinuous_indicator (by norm_num)
  exact (h1.add h2).add h3

theorem phi_upperSemicontinuous : UpperSemicontinuous phi := by
  have h1 : UpperSemicontinuous (fun t : ℝ => t) := continuous_id.upperSemicontinuous
  have h2 : UpperSemicontinuous (indicator (Ici (0 : ℝ)) (fun _ => (3 : ℝ))) :=
    isClosed_Ici.upperSemicontinuous_indicator (by norm_num)
  have h3 : UpperSemicontinuous (indicator {(-2 : ℝ)} (fun _ => (4 : ℝ))) :=
    isClosed_singleton.upperSemicontinuous_indicator (by norm_num)
  have h4 : UpperSemicontinuous (indicator {(-1 : ℝ)} (fun _ => (2 : ℝ))) :=
    isClosed_singleton.upperSemicontinuous_indicator (by norm_num)
  exact ((h1.add h2).add h3).add h4

theorem isOpen_lt_right (a : ℝ) : IsOpen {b | lt a b} :=
  psi_lowerSemicontinuous.isOpen_preimage (phi a)

theorem isOpen_lt_left (b : ℝ) : IsOpen {a | lt a b} :=
  phi_upperSemicontinuous.isOpen_preimage (psi b)

theorem phi_neg_two : phi (-2) = 2 := by
  simp only [phi, indicator_apply, mem_Ici, mem_singleton_iff]; norm_num

theorem phi_neg_one : phi (-1) = 1 := by
  simp only [phi, indicator_apply, mem_Ici, mem_singleton_iff]; norm_num

theorem psi_one : psi 1 = 2 := by
  simp only [psi, indicator_apply, mem_Ioi, mem_singleton_iff]; norm_num

theorem psi_neg_two : psi (-2) = -2 := by
  simp only [psi, indicator_apply, mem_Ioi, mem_singleton_iff]; norm_num

theorem psi_neg_one : psi (-1) = -1 := by
  simp only [psi, indicator_apply, mem_Ioi, mem_singleton_iff]; norm_num

/-- Away from the three marked points, `≪` is the order of `ℝ`. -/
theorem lt_of_lt {a b : ℝ} (hab : a < b) (ha2 : a ≠ -2) (ha1 : a ≠ -1) (hb : b ≠ 1) :
    lt a b := by
  unfold lt phi psi
  simp only [indicator_apply, mem_Ici, mem_Ioi, mem_singleton_iff, ha2, ha1, hb, if_false]
  split_ifs <;> linarith

/-- `≪` goes up in `ℝ`. -/
theorem lt_imp_lt {a b : ℝ} (h : lt a b) : a < b := by
  by_contra hba
  have hba' : b ≤ a := not_lt.1 hba
  have : psi b ≤ phi a := by
    unfold psi phi
    simp only [indicator_apply, mem_Ici, mem_Ioi, mem_singleton_iff]
    split_ifs <;> linarith
  exact absurd h (not_lt.2 this)

/-- `≤` goes up in `ℝ`. -/
theorem le_imp_le {a b : ℝ} (h : le a b) : a ≤ b := by
  rcases h with rfl | h | ⟨ha, hb⟩
  · exact le_rfl
  · exact (lt_imp_lt h).le
  · have ha' : a ≤ -2 := by
      rcases ha with rfl | ha
      · exact le_rfl
      · exact (lt_imp_lt ha).le
    have hb' : -1 ≤ b := by
      rcases hb with rfl | hb
      · exact le_rfl
      · exact (lt_imp_lt hb).le
    linarith

/-- `-1 ≪ 1`. -/
theorem lt_neg_one_one : lt (-1) 1 := by
  show phi (-1) < psi 1
  rw [phi_neg_one, psi_one]; norm_num

/-- Not `-2 ≪ 1`. -/
theorem not_lt_neg_two_one : ¬ lt (-2) 1 := by
  show ¬ phi (-2) < psi 1
  rw [phi_neg_two, psi_one]; norm_num

/-- The chronological future of `-1` lies in `]0, +∞[`. -/
theorem pos_of_lt_neg_one {b : ℝ} (h : lt (-1) b) : 0 < b := by
  have h' : 1 < psi b := by
    have := h
    unfold lt at this
    rwa [phi_neg_one] at this
  by_contra hb
  have hb' : b ≤ 0 := not_lt.1 hb
  unfold psi at h'
  simp only [indicator_apply, mem_Ioi, mem_singleton_iff] at h'
  split_ifs at h' <;> linarith

/-- The chronological future of `-2` contains `]0, +∞[ ∖ {1}`. -/
theorem lt_neg_two_of_pos {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) : lt (-2) b := by
  show phi (-2) < psi b
  rw [phi_neg_two]
  unfold psi
  simp only [indicator_apply, mem_Ioi, mem_singleton_iff, hb1, if_false, hb, if_true]
  linarith

/-- `I^+(-1) ⊂ closure I^+(-2)`. -/
theorem Iplus_neg_one_subset : {b | lt (-1) b} ⊆ closure {b | lt (-2) b} := by
  intro b hb
  have hsub : Ioi (0 : ℝ) ∩ {1}ᶜ ⊆ {b | lt (-2) b} := fun t ht => lt_neg_two_of_pos ht.1 ht.2
  refine closure_mono hsub (isOpen_Ioi.inter_closure ⟨pos_of_lt_neg_one hb, ?_⟩)
  rw [closure_compl_singleton]
  trivial

/-- `I^-(-2) ⊂ I^-(-1)`. -/
theorem Iminus_neg_two_subset : {a | lt a (-2)} ⊆ closure {a | lt a (-1)} := by
  intro a ha
  apply subset_closure
  show phi a < psi (-1)
  have : phi a < psi (-2) := ha
  rw [psi_neg_two] at this
  rw [psi_neg_one]
  linarith

/-- Every non-empty open subset of `ℝ` holds a pair `a ≪ b` with `a ≠ -1` and `b ≠ -2`. -/
theorem rich (O : Set ℝ) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ a ∈ O, ∃ b ∈ O, a ≠ -1 ∧ b ≠ -2 ∧ lt a b := by
  have hD : Dense ((({(-2 : ℝ)}ᶜ \ {(-1 : ℝ)}) \ {(1 : ℝ)}) : Set ℝ) :=
    ((dense_compl_singleton (-2 : ℝ)).sdiff_singleton (-1)).sdiff_singleton 1
  obtain ⟨c, hcD, hcO⟩ := hD.exists_mem_open hO hne
  set V : Set ℝ := O ∩ ({(-2 : ℝ)}ᶜ ∩ ({(-1 : ℝ)}ᶜ ∩ {(1 : ℝ)}ᶜ)) with hVdef
  have hV : IsOpen V :=
    hO.inter (isOpen_compl_singleton.inter (isOpen_compl_singleton.inter isOpen_compl_singleton))
  have hcV : c ∈ V := by
    simp only [mem_sdiff, mem_compl_iff, mem_singleton_iff] at hcD
    exact ⟨hcO, hcD.1.1, hcD.1.2, hcD.2⟩
  obtain ⟨d, hdc, hdV⟩ := (dense_compl_singleton c).exists_mem_open hV ⟨c, hcV⟩
  have key : ∀ {a b : ℝ}, a ∈ V → b ∈ V → a < b →
      ∃ a ∈ O, ∃ b ∈ O, a ≠ -1 ∧ b ≠ -2 ∧ lt a b := by
    intro a b ha hb hab
    exact ⟨a, ha.1, b, hb.1, ha.2.2.1, hb.2.1, lt_of_lt hab ha.2.1 ha.2.2.1 hb.2.2.2⟩
  rcases lt_or_gt_of_ne (show d ≠ c from hdc) with h | h
  · exact key hdV hcV h
  · exact key hcV hdV h

theorem le_trans' (a b c : ℝ) : le a b → le b c → le a c :=
  extLe_trans lt_trans' a b c

end DeuxPushup

open DeuxPushup in
/-- **The witness of the converse half of `rem:deux_pushup`**: a causality on `ℝ` which is
causally plain and fails push-up. Its relations on `U` are the restrictions of global ones
(`Causality.ofRelation`): it is not absolutely minimal (`deuxPushup_not_absolutelyMinimal`). -/
noncomputable def deuxPushup : Causality ℝ :=
  Causality.ofRelation DeuxPushup.le DeuxPushup.lt extLe_refl le_trans' lt_trans'
    (fun _ _ h => extLe_of_rel h) isOpen_lt_right isOpen_lt_left

@[simp] theorem deuxPushup_le {U : Opens ℝ} {a b : ℝ} :
    deuxPushup.le U a b ↔ a ∈ U ∧ b ∈ U ∧ DeuxPushup.le a b := Iff.rfl

@[simp] theorem deuxPushup_lt {U : Opens ℝ} {a b : ℝ} :
    deuxPushup.lt U a b ↔ a ∈ U ∧ b ∈ U ∧ DeuxPushup.lt a b := Iff.rfl

/-- The witness is causal: `≤_ℝ` is an order, contained in that of `ℝ`. -/
theorem deuxPushup_isCausal : deuxPushup.IsCausal := by
  intro a b hab hba
  rw [deuxPushup_le] at hab hba
  exact le_antisymm (DeuxPushup.le_imp_le hab.2.2) (DeuxPushup.le_imp_le hba.2.2)

/-- **The witness is causally plain.** -/
theorem deuxPushup_causallyPlain : deuxPushup.CausallyPlain := by
  apply Causality.ofRelation_causallyPlain
  · intro A
    exact DeuxPushup.interior_extLe_subset_closure DeuxPushup.lt_trans'
      (fun O hO hne => by
        obtain ⟨a, ha, b, hb, ha1, -, hab⟩ := DeuxPushup.rich O hO hne
        exact ⟨a, ha, b, hb, ha1, hab⟩)
      DeuxPushup.Iplus_neg_one_subset A
  · intro A
    have h := DeuxPushup.interior_extLe_subset_closure (S := flip DeuxPushup.lt)
      (x := (-1 : ℝ)) (y := (-2 : ℝ)) (fun a b c hab hbc => DeuxPushup.lt_trans' c b a hbc hab)
      (fun O hO hne => by
        obtain ⟨a, ha, b, hb, -, hb2, hab⟩ := DeuxPushup.rich O hO hne
        exact ⟨b, hb, a, ha, hb2, hab⟩)
      DeuxPushup.Iminus_neg_two_subset A
    have e : {b | ∃ a ∈ A, DeuxPushup.le b a} =
        {b | ∃ a ∈ A, DeuxPushup.extLe (flip DeuxPushup.lt) (-1) (-2) a b} := by
      ext b
      simp only [mem_setOf_eq, DeuxPushup.le, DeuxPushup.extLe_flip]
    rw [e]
    exact h

/-- **The witness fails push-up**: `-2 ≤ -1 ≪ 1` and not `-2 ≪ 1`. -/
theorem deuxPushup_not_pushUp : ¬ deuxPushup.PushUp := by
  intro h
  have h1 : deuxPushup.le ⊤ (-2) (-1) := by
    rw [deuxPushup_le]
    exact ⟨trivial, trivial, Or.inr (Or.inr ⟨Or.inl rfl, Or.inl rfl⟩)⟩
  have h2 : deuxPushup.lt ⊤ (-1) 1 := by
    rw [deuxPushup_lt]
    exact ⟨trivial, trivial, DeuxPushup.lt_neg_one_one⟩
  have h3 := ((Causality.pushUp_iff.1 h) ⊤).2 h1 h2
  rw [deuxPushup_lt] at h3
  exact DeuxPushup.not_lt_neg_two_one h3.2.2

/-- The witness's chronological relation does not interpolate (`-1 ≪ 1` with nothing between). -/
theorem deuxPushup_not_interpolates : ¬ deuxPushup.Interpolates := fun hi =>
  deuxPushup_not_pushUp (Causality.pushUpOn_top.1
    (Causality.pushUpOn_of_causallyPlainOn_of_interpolatesOn
      (Causality.causallyPlainOn_top.2 deuxPushup_causallyPlain) hi))

/-- The witness is not absolutely minimal, as the finding forces. -/
theorem deuxPushup_not_absolutelyMinimal : ¬ deuxPushup.AbsolutelyMinimal := fun hmin =>
  deuxPushup_not_pushUp
    (Causality.pushUp_of_causallyPlain_of_absolutelyMinimal hmin deuxPushup_causallyPlain)

/-! ### The remark -/

/-- `rem:deux_pushup`, the independence, in the library's reading of `defi:causalite`:
push-up does not imply causal plainness (the lightlike line, which is absolutely minimal), and
causal plainness does not imply push-up (`deuxPushup`, causal, not absolutely minimal). Both
live on `ℝ`, second countable and Hausdorff. -/
theorem deux_pushup :
    (lightlikeLine.AbsolutelyMinimal ∧ lightlikeLine.IsCausal ∧ lightlikeLine.PushUp ∧
        ¬ lightlikeLine.CausallyPlain) ∧
      (deuxPushup.IsCausal ∧ deuxPushup.CausallyPlain ∧ ¬ deuxPushup.PushUp) :=
  ⟨⟨lightlikeLine_absolutelyMinimal, lightlikeLine_isCausal, lightlikeLine_pushUp,
      lightlikeLine_not_causallyPlain⟩,
    deuxPushup_isCausal, deuxPushup_causallyPlain, deuxPushup_not_pushUp⟩

/-- `rem:deux_pushup`, "neither implies the other", over the topological spacetimes on `ℝ`. -/
theorem deux_pushup_neither :
    ¬ (∀ C : Causality ℝ, C.PushUp → C.CausallyPlain) ∧
      ¬ (∀ C : Causality ℝ, C.CausallyPlain → C.PushUp) :=
  ⟨fun h => lightlikeLine_not_causallyPlain (h _ lightlikeLine_pushUp),
    fun h => deuxPushup_not_pushUp (h _ deuxPushup_causallyPlain)⟩

/-- **Finding**, the asymmetry: among absolutely minimal causalities, push-up still does not
imply plainness (the lightlike line), but plainness implies push-up on every `T1` space. -/
theorem deux_pushup_absolutelyMinimal :
    (lightlikeLine.AbsolutelyMinimal ∧ lightlikeLine.PushUp ∧ ¬ lightlikeLine.CausallyPlain) ∧
      ∀ (N : Type u) [TopologicalSpace N] [T1Space N] (C : Causality N),
        C.AbsolutelyMinimal → C.CausallyPlain → C.PushUp :=
  ⟨⟨lightlikeLine_absolutelyMinimal, lightlikeLine_pushUp, lightlikeLine_not_causallyPlain⟩,
    fun _ _ _ _ hmin hp => Causality.pushUp_of_causallyPlain_of_absolutelyMinimal hmin hp⟩

end Causal
