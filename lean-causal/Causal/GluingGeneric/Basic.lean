import Causal.Morphism
import Causal.CurveComponents
import Causal.TransparentLine

/-!
# Gluing in its hereditary form, generic constructions (1): restriction, extension, dual

No label of `ETT.tex` is marked by this file. It is the first module of the programme target
`T-abs-gluing-generic` (DEC-167, step 1a): for each generic construction of a causality in the
ETT layer, which form of the gluing clause it preserves. Cited, unmarked:
`defi:causalite` — `ETT.tex:237`, `def:topological_space_causality_absolutely` — `ETT.tex:397`,
`ex:open_subset` — `ETT.tex:259`, `cexemple:point_transparent` — `ETT.tex:472`,
`lem:precausalite_restriction_minimale` — `ETT.tex:491`.

> A causality $\mathscr{C}$ on $M$ is a sheaf on $M$ with values in the category $\mathbf{C}$.
> (`ETT.tex:238`)

> An open subset of a topological spacetime carries a unique topological spacetime structure for
> which the inclusion is a strong morphism. (`ETT.tex:260`)

DEC-167 reads the sheaf clause with gluing. The form of the clause is open (OQ-95): the
**hereditary form** `∀ W : Opens M, P.AbsolutelyMinimalOn W` (the sheaf condition on every open
set), or the **M-only form** `P.AbsolutelyMinimal` (`def:topological_space_causality_absolutely`
as printed). Every statement below is written with one of these two expressions, unabbreviated,
so that it serves whatever name the design gives the field.

## What is proved (no `sorry` in this file)

* Tools: `GluingGeneric.transGen_of_image` (a chain whose steps live in `f '' s` comes from a
  chain upstairs), `GluingGeneric.transGen_flatten`; `Precausality.absolutelyMinimalOn_congr`
  (absolute minimality of `W` reads only the relations of the opens of `W`);
  `Precausality.absolutelyMinimalOn_of_supported` (**locality of the hereditary form**: relations
  carried by one open `W`, plus the diagonal, and hereditarily minimal inside `W`, are
  hereditarily minimal), `absolutelyMinimalOn_of_supported_of_le` (its M-only counterpart);
  `Precausality.absolutelyMinimalOn_of_subsingleton`.
* **The jump lemma** `Precausality.AbsolutelyMinimalOn.mem_of_le_sup`: an absolutely minimal
  relation in `A ⊔ B` never leaves `A` when `A`, `B` are disjoint opens whose closures do not meet
  in `W`; `mem_of_le_sup_of_disjoint`, the hereditary instance `W = A ⊔ B`.
* **Dual**: both forms, both directions (`dual_absolutelyMinimalOn_all`; the M-only one is the
  library's `Causality.dual_absolutelyMinimal`).
* **Extension of a causality given on `W`** (`LocalPrecausality.extend`, `LocalCausality.extend`):
  hereditary on the opens of `W` ⇒ hereditary (`extend_absolutelyMinimalOn_all`); minimal on `W`
  ⇒ minimal on every `W' ⊇ W`, in particular on `M` (`extend_absolutelyMinimal`). The diagonal
  causality of `W` extends to a hereditarily minimal one (`diagonal_extend_absolutelyMinimalOn`).
* **Restriction carried by `M`** (`Causality.relativeTo U`): hereditary ⇒ hereditary
  (`relativeTo_absolutelyMinimalOn_all`), **and M-only ⇒ M-only** (`relativeTo_absolutelyMinimal`).
* **Restriction as a spacetime of its own** (`(C.restrict W).toSubtype`, the bridge of
  `ex:open_subset`): its absolute minimality on `V'` is `C`'s on the image of `V'`
  (`LocalCausality.toSubtype_absolutelyMinimalOn_iff`,
  `Causality.restrict_toSubtype_absolutelyMinimalOn_iff`); so hereditary ⇒ hereditary
  (`restrict_toSubtype_absolutelyMinimalOn_all`), and the M-only form is `C.AbsolutelyMinimalOn W`
  (`restrict_toSubtype_absolutelyMinimal_iff`), **which the M-only form of `C` does not give**:
  `transparentLine_restrict_toSubtype_not_absolutelyMinimal` (the transparent-point line).
  The same line separates the two forms for the extension:
  `transparentLine_relativeTo_separates` (`relativeTo` absolutely minimal on `M`, not on `ℝ ∖ {0}`).
* **`ex:open_subset`, first sentence, uniqueness fails under gluing in either form**:
  `openSubset_not_unique_of_absolutelyMinimal` (the timelike line on `ℝ` and the diagonal
  causality are both hereditarily minimal and both make the inclusion a strong morphism).
* **Locally causally arc-connected causalities**: the two forms agree
  (`LocallyCausallyArcConnected.absolutelyMinimal_iff_all`, from the library's
  `lem:precausalite_restriction_minimale`).

## Hypothesis checklist

| DEC-167 / the target | here |
|---|---|
| the gluing clause, hereditary form | ✓ `∀ W : Opens M, P.AbsolutelyMinimalOn W`, written out |
| the gluing clause, M-only form | ✓ `P.AbsolutelyMinimal` (`= AbsolutelyMinimalOn ⊤`, `absolutelyMinimal_iff`) |
| `M` second countable, Hausdorff | ⚠ weakened: not used |

## SCOPE (disclosed)

* No definition of the library changes and no new notion is defined (the field is
  `T-abs-gluing-field`'s). `traceOpens` is a helper (the trace of an open set on `↥W`).
* The restriction to an open subset has two Lean forms: `relativeTo U` (a causality on `M`, the
  diagonal outside `U`) and `(C.restrict U).toSubtype` (a causality on `↥U`). They agree on the
  opens of `U` but not on the M-only form of gluing; the second is the paper's "the open subset
  carries a topological spacetime structure". The subtype appears only through the bridge
  `toSubtype` of `Causal.Morphism` (kb/0001).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation

universe u v

variable {M : Type u} [TopologicalSpace M]

/-! ### Tools on chains -/

namespace GluingGeneric

/-- A chain downstairs whose steps start in `f '' s` and which joins two points of `f '' s` comes
from a chain upstairs, when every step between images of points of `s` lifts. -/
theorem transGen_of_image {α : Type*} {β : Type*} {f : α → β} {s : Set α} {r : β → β → Prop}
    {r' : α → α → Prop} (hr : ∀ c d, r c d → c ∈ f '' s)
    (hstep : ∀ x ∈ s, ∀ y ∈ s, r (f x) (f y) → r' x y) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (h : TransGen r (f a) (f b)) : TransGen r' a b := by
  suffices key : ∀ q, TransGen r (f a) q → ∀ b ∈ s, f b = q → TransGen r' a b from
    key _ h b hb rfl
  intro q hq
  induction hq with
  | single hl =>
    intro b hb e
    subst e
    exact TransGen.single (hstep a ha b hb hl)
  | tail _ hl ih =>
    intro b hb e
    subst e
    obtain ⟨c₀, hc₀, rfl⟩ := hr _ _ hl
    exact (ih c₀ hc₀ rfl).tail (hstep c₀ hc₀ b hb hl)

/-- A chain of chains is a chain. -/
theorem transGen_flatten {α : Type*} {r p : α → α → Prop} (h : ∀ a b, r a b → TransGen p a b)
    {a b : α} (hab : TransGen r a b) : TransGen p a b := by
  induction hab with
  | single hl => exact h _ _ hl
  | tail _ hl ih => exact ih.trans (h _ _ hl)

/-- The trace on `↥W` of an open set of `M`. -/
def traceOpens (W : Opens M) (O : Opens M) : Opens W :=
  ⟨Subtype.val ⁻¹' (O : Set M), O.isOpen.preimage continuous_subtype_val⟩

theorem mem_traceOpens {W O : Opens M} {z : W} : z ∈ traceOpens W O ↔ (z : M) ∈ O := Iff.rfl

theorem imageOpens_traceOpens {W O : Opens M} (hO : O ≤ W) : imageOpens (traceOpens W O) = O := by
  apply SetLike.coe_injective
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hp
    exact ⟨⟨p, hO hp⟩, hp, rfl⟩

theorem imageOpens_inf {W : Opens M} (V V' : Opens W) :
    imageOpens (V ⊓ V') = imageOpens V ⊓ imageOpens V' := by
  apply SetLike.coe_injective
  exact Set.image_inter Subtype.val_injective

theorem imageOpens_top (W : Opens M) : imageOpens (⊤ : Opens W) = W := by
  apply SetLike.coe_injective
  ext p
  constructor
  · rintro ⟨z, -, rfl⟩
    exact z.2
  · intro hp
    exact ⟨⟨p, hp⟩, trivial, rfl⟩

end GluingGeneric

open GluingGeneric

/-! ### Precausalities: congruence, locality, the jump lemma -/

namespace Precausality

variable {P Q : Precausality M} {W : Opens M}

/-- Absolute minimality of `W` reads only the relations of the open subsets of `W`. -/
theorem absolutelyMinimalOn_congr
    (h : ∀ V : Opens M, V ≤ W → ∀ x y, (P.le V x y ↔ Q.le V x y) ∧ (P.lt V x y ↔ Q.lt V x y)) :
    P.AbsolutelyMinimalOn W ↔ Q.AbsolutelyMinimalOn W := by
  have key : ∀ P Q : Precausality M, (∀ V : Opens M, V ≤ W → ∀ x y,
      (P.le V x y ↔ Q.le V x y) ∧ (P.lt V x y ↔ Q.lt V x y)) →
      P.AbsolutelyMinimalOn W → Q.AbsolutelyMinimalOn W := by
    intro P Q h hP S hS V hV x y
    refine ⟨fun hxy => ?_, fun hxy => ?_⟩
    · refine TransGen.mono ?_ ((hP S hS V hV x y).1 ((h V hV x y).1.2 hxy))
      rintro a b ⟨O, hO, hab⟩
      exact ⟨O, hO, (h _ (inf_le_left.trans hV) a b).1.1 hab⟩
    · refine TransGen.mono ?_ ((hP S hS V hV x y).2 ((h V hV x y).2.2 hxy))
      rintro a b ⟨O, hO, hab⟩
      exact ⟨O, hO, (h _ (inf_le_left.trans hV) a b).2.1 hab⟩
  exact ⟨key P Q h, key Q P fun V hV x y => ⟨(h V hV x y).1.symm, (h V hV x y).2.symm⟩⟩

/-- Time reversal preserves the hereditary form, both ways. -/
theorem dual_absolutelyMinimalOn_all :
    (∀ W : Opens M, P.dual.AbsolutelyMinimalOn W) ↔ ∀ W : Opens M, P.AbsolutelyMinimalOn W :=
  forall_congr' fun _ => dual_absolutelyMinimalOn

/-- **Locality of the hereditary form, one open set.** If every relation of `P` in an open `V` is
a relation in `V ⊓ W`, or (causal) the diagonal of `V`, and `P` is absolutely minimal on every
open subset of `W`, then `P` is absolutely minimal on every open set. -/
theorem absolutelyMinimalOn_of_supported
    (hle : ∀ (V : Opens M) (x y : M), P.le V x y → x = y ∨ P.le (V ⊓ W) x y)
    (hlt : ∀ (V : Opens M) (x y : M), P.lt V x y → P.lt (V ⊓ W) x y)
    (hW : ∀ W' : Opens M, W' ≤ W → P.AbsolutelyMinimalOn W') (W' : Opens M) :
    P.AbsolutelyMinimalOn W' := by
  intro S hS V hV x y
  have hS' : ∀ z ∈ W' ⊓ W, ∃ O ∈ S, z ∈ O := fun z hz => hS z hz.1
  have hVW : V ⊓ W ≤ W' ⊓ W := inf_le_inf_right _ hV
  have hmono : ∀ O : Opens M, V ⊓ W ⊓ O ≤ V ⊓ O := fun O => inf_le_inf_right O inf_le_left
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rcases hle V x y hxy with rfl | h
    · have hx := P.le_mem_left hxy
      obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
      exact TransGen.single ⟨O, hO, P.le_refl ⟨hx, hxO⟩⟩
    · refine TransGen.mono ?_ ((hW _ inf_le_right S hS' _ hVW x y).1 h)
      rintro a b ⟨O, hO, hab⟩
      exact ⟨O, hO, P.le_mono (hmono O) hab⟩
  · refine TransGen.mono ?_ ((hW _ inf_le_right S hS' _ hVW x y).2 (hlt V x y hxy))
    rintro a b ⟨O, hO, hab⟩
    exact ⟨O, hO, P.lt_mono (hmono O) hab⟩

/-- The M-only counterpart: under the same support condition, absolute minimality of `W` passes
to every open `W' ⊇ W` (and so to `M`). -/
theorem absolutelyMinimalOn_of_supported_of_le
    (hle : ∀ (V : Opens M) (x y : M), P.le V x y → x = y ∨ P.le (V ⊓ W) x y)
    (hlt : ∀ (V : Opens M) (x y : M), P.lt V x y → P.lt (V ⊓ W) x y)
    (hW : P.AbsolutelyMinimalOn W) {W' : Opens M} (hWW' : W ≤ W') : P.AbsolutelyMinimalOn W' := by
  intro S hS V hV x y
  have hS' : ∀ z ∈ W, ∃ O ∈ S, z ∈ O := fun z hz => hS z (hWW' hz)
  have hmono : ∀ O : Opens M, V ⊓ W ⊓ O ≤ V ⊓ O := fun O => inf_le_inf_right O inf_le_left
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rcases hle V x y hxy with rfl | h
    · have hx := P.le_mem_left hxy
      obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
      exact TransGen.single ⟨O, hO, P.le_refl ⟨hx, hxO⟩⟩
    · refine TransGen.mono ?_ ((hW S hS' _ inf_le_right x y).1 h)
      rintro a b ⟨O, hO, hab⟩
      exact ⟨O, hO, P.le_mono (hmono O) hab⟩
  · refine TransGen.mono ?_ ((hW S hS' _ inf_le_right x y).2 (hlt V x y hxy))
    rintro a b ⟨O, hO, hab⟩
    exact ⟨O, hO, P.lt_mono (hmono O) hab⟩

/-- On a subsingleton space every precausality is absolutely minimal on every open set. -/
theorem absolutelyMinimalOn_of_subsingleton [Subsingleton M] (P : Precausality M)
    (W : Opens M) : P.AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  have key : x ∈ V → ∃ O ∈ S, V ⊓ O = V := by
    intro hx
    obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
    refine ⟨O, hO, inf_eq_left.2 fun z _ => ?_⟩
    rwa [Subsingleton.elim z x]
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · obtain ⟨O, hO, hVO⟩ := key (P.le_mem_left hxy)
    exact TransGen.single ⟨O, hO, by rwa [hVO]⟩
  · obtain ⟨O, hO, hVO⟩ := key (P.lt_mem_left hxy)
    exact TransGen.single ⟨O, hO, by rwa [hVO]⟩

/-- **The jump lemma.** Let `P` be absolutely minimal on `W` and `A`, `B` open subsets of `W` whose
closures do not meet in `W` (so `A`, `B` are disjoint). A relation in `A ⊔ B` starting in `A`
ends in `A`. -/
theorem AbsolutelyMinimalOn.mem_of_le_sup (h : P.AbsolutelyMinimalOn W) {A B : Opens M}
    (hA : A ≤ W) (hB : B ≤ W)
    (hcl : ∀ z ∈ W, z ∉ closure (A : Set M) ∨ z ∉ closure (B : Set M)) {x y : M} (hx : x ∈ A) :
    (P.le (A ⊔ B) x y → y ∈ A) ∧ (P.lt (A ⊔ B) x y → y ∈ A) := by
  let O₁ : Opens M := ⟨(closure (B : Set M))ᶜ, isClosed_closure.isOpen_compl⟩
  let O₂ : Opens M := ⟨(closure (A : Set M))ᶜ, isClosed_closure.isOpen_compl⟩
  have hS : ∀ z ∈ W, ∃ O ∈ ({O₁, O₂} : Set (Opens M)), z ∈ O := by
    intro z hz
    rcases hcl z hz with h' | h'
    · exact ⟨O₂, by simp, h'⟩
    · exact ⟨O₁, by simp, h'⟩
  have hsup : A ⊔ B ≤ W := sup_le hA hB
  -- one step from a point of `A` ends in `A`
  have step : ∀ a b, a ∈ A → (∃ O ∈ ({O₁, O₂} : Set (Opens M)),
      b ∈ (A ⊔ B) ⊓ O ∧ a ∈ (A ⊔ B) ⊓ O) → b ∈ A := by
    rintro a b ha ⟨O, hO, hb, ha'⟩
    rcases hO with rfl | hO
    · rcases Opens.mem_sup.1 hb.1 with hbA | hbB
      · exact hbA
      · exact absurd (subset_closure hbB) (hb.2 : b ∉ closure (B : Set M))
    · rw [mem_singleton_iff] at hO
      subst hO
      exact absurd (subset_closure ha) (ha'.2 : a ∉ closure (A : Set M))
  have chain : ∀ r : Opens M → M → M → Prop, (∀ {V a b}, r V a b → a ∈ V ∧ b ∈ V) → ∀ b,
      TransGen (fun a b => ∃ O ∈ ({O₁, O₂} : Set (Opens M)), r ((A ⊔ B) ⊓ O) a b) x b →
        b ∈ A := by
    intro r hr b hb
    induction hb with
    | single hl =>
      obtain ⟨O, hO, hl⟩ := hl
      exact step _ _ hx ⟨O, hO, (hr hl).2, (hr hl).1⟩
    | tail _ hl ih =>
      obtain ⟨O, hO, hl⟩ := hl
      exact step _ _ ih ⟨O, hO, (hr hl).2, (hr hl).1⟩
  exact ⟨fun hxy => chain P.le (fun h => ⟨P.le_mem_left h, P.le_mem_right h⟩) y
      ((h _ hS _ hsup x y).1 hxy),
    fun hxy => chain P.lt (fun h => ⟨P.lt_mem_left h, P.lt_mem_right h⟩) y
      ((h _ hS _ hsup x y).2 hxy)⟩

/-- The jump lemma in the hereditary form: `W = A ⊔ B`. -/
theorem AbsolutelyMinimalOn.mem_of_le_sup_of_disjoint {A B : Opens M}
    (h : P.AbsolutelyMinimalOn (A ⊔ B)) (hAB : Disjoint (A : Set M) B) {x y : M} (hx : x ∈ A) :
    (P.le (A ⊔ B) x y → y ∈ A) ∧ (P.lt (A ⊔ B) x y → y ∈ A) := by
  refine h.mem_of_le_sup le_sup_left le_sup_right (fun z hz => ?_) hx
  rcases Opens.mem_sup.1 hz with hzA | hzB
  · exact Or.inr fun hzB => Set.disjoint_left.1 (hAB.closure_right A.isOpen) hzA hzB
  · exact Or.inl fun hzA => Set.disjoint_left.1 (hAB.closure_left B.isOpen) hzA hzB

end Precausality

/-! ### Extension of a causality given on an open set -/

namespace LocalPrecausality

variable {W : Opens M} (L : LocalPrecausality W)

/-- The extension of a precausality on `W` is hereditarily minimal as soon as it is absolutely
minimal on every open subset of `W`. -/
theorem extend_absolutelyMinimalOn_all
    (hL : ∀ W' : Opens M, W' ≤ W → L.extend.AbsolutelyMinimalOn W') (W' : Opens M) :
    L.extend.AbsolutelyMinimalOn W' := by
  refine Precausality.absolutelyMinimalOn_of_supported (W := W) (fun V x y h => ?_)
    (fun V x y h => (extend_lt_iff (L := L) inf_le_right).2 h) hL W'
  rcases h with ⟨rfl, -⟩ | h
  · exact Or.inl rfl
  · exact Or.inr ((extend_le_iff (L := L) inf_le_right).2 h)

/-- The extension of a precausality absolutely minimal on `W` is absolutely minimal on every open
`W' ⊇ W`. -/
theorem extend_absolutelyMinimalOn_of_le (hL : L.extend.AbsolutelyMinimalOn W) {W' : Opens M}
    (hWW' : W ≤ W') : L.extend.AbsolutelyMinimalOn W' := by
  refine Precausality.absolutelyMinimalOn_of_supported_of_le (W := W) (fun V x y h => ?_)
    (fun V x y h => (extend_lt_iff (L := L) inf_le_right).2 h) hL hWW'
  rcases h with ⟨rfl, -⟩ | h
  · exact Or.inl rfl
  · exact Or.inr ((extend_le_iff (L := L) inf_le_right).2 h)

/-- The extension of a precausality absolutely minimal on `W` is absolutely minimal. -/
theorem extend_absolutelyMinimal (hL : L.extend.AbsolutelyMinimalOn W) :
    L.extend.AbsolutelyMinimal := by
  rw [Precausality.absolutelyMinimal_iff]
  exact L.extend_absolutelyMinimalOn_of_le hL le_top

end LocalPrecausality

namespace LocalCausality

variable {W : Opens M} (L : LocalCausality W)

theorem extend_absolutelyMinimalOn_all
    (hL : ∀ W' : Opens M, W' ≤ W → L.extend.AbsolutelyMinimalOn W') (W' : Opens M) :
    L.extend.AbsolutelyMinimalOn W' :=
  LocalPrecausality.extend_absolutelyMinimalOn_all L.toLocalPrecausality hL W'

theorem extend_absolutelyMinimal (hL : L.extend.AbsolutelyMinimalOn W) :
    L.extend.AbsolutelyMinimal :=
  LocalPrecausality.extend_absolutelyMinimal L.toLocalPrecausality hL

/-- The diagonal causality of `W` (`LocalCausality.diagonal`) extends to a causality absolutely
minimal on every open set. -/
theorem diagonal_extend_absolutelyMinimalOn (W W' : Opens M) :
    (LocalCausality.diagonal W).extend.AbsolutelyMinimalOn W' := by
  intro S hS V hV x y
  refine ⟨fun hxy => ?_, fun hxy => False.elim hxy⟩
  have h' : x = y ∧ x ∈ V := by
    rcases hxy with h | ⟨h, hx⟩
    · exact h
    · exact ⟨h, (inf_le_left : V ⊓ W ≤ V) hx⟩
  obtain ⟨rfl, hx⟩ := h'
  obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
  exact TransGen.single ⟨O, hO, Or.inl ⟨rfl, hx, hxO⟩⟩

/-! ### The open subset as a spacetime of its own: the bridge `toSubtype` -/

/-- **Absolute minimality of the subspace is absolute minimality of the image**: the causality `L`
of `W`, read on `↥W`, is absolutely minimal on `V'` iff its extension is absolutely minimal on the
image of `V'` in `M`. -/
theorem toSubtype_absolutelyMinimalOn_iff (V' : Opens W) :
    L.toSubtype.AbsolutelyMinimalOn V' ↔ L.extend.AbsolutelyMinimalOn (imageOpens V') := by
  constructor
  · intro h S hS V hV x y
    have hVW : V ≤ W := hV.trans (imageOpens_le V')
    have hVs : imageOpens (traceOpens W V) = V := imageOpens_traceOpens hVW
    have hVsV' : traceOpens W V ≤ V' := fun z hz => val_mem_imageOpens.1 (hV hz)
    have hS' : ∀ z ∈ V', ∃ O' ∈ traceOpens W '' S, z ∈ O' := fun z hz => by
      obtain ⟨O, hO, hzO⟩ := hS z.1 (val_mem_imageOpens.2 hz)
      exact ⟨traceOpens W O, mem_image_of_mem _ hO, hzO⟩
    have hstep : ∀ O : Opens M, imageOpens (traceOpens W V ⊓ traceOpens W O) = V ⊓ O := by
      intro O
      apply SetLike.coe_injective
      ext p
      constructor
      · rintro ⟨z, ⟨hzV, hzO⟩, rfl⟩
        exact ⟨hzV, hzO⟩
      · rintro ⟨hpV, hpO⟩
        exact ⟨⟨p, hVW hpV⟩, ⟨hpV, hpO⟩, rfl⟩
    refine ⟨fun hxy => ?_, fun hxy => ?_⟩
    · rw [LocalCausality.extend_le_iff hVW] at hxy
      have hx : x ∈ W := hVW (L.le_mem_left hVW hxy)
      have hy : y ∈ W := hVW (L.le_mem_right hVW hxy)
      have hxy' : L.toSubtype.le (traceOpens W V) ⟨x, hx⟩ ⟨y, hy⟩ := by
        show L.le (imageOpens (traceOpens W V)) x y
        rw [hVs]; exact hxy
      refine TransGen.lift Subtype.val (fun a b hab => ?_) ((h _ hS' _ hVsV' _ _).1 hxy')
      obtain ⟨_, ⟨O, hO, rfl⟩, hab⟩ := hab
      refine ⟨O, hO, (LocalCausality.extend_le_iff (inf_le_left.trans hVW)).2 ?_⟩
      have hab' : L.le (imageOpens (traceOpens W V ⊓ traceOpens W O)) a b := hab
      rwa [hstep] at hab'
    · rw [LocalCausality.extend_lt_iff hVW] at hxy
      have hx : x ∈ W := hVW (L.lt_mem_left hVW hxy)
      have hy : y ∈ W := hVW (L.lt_mem_right hVW hxy)
      have hxy' : L.toSubtype.lt (traceOpens W V) ⟨x, hx⟩ ⟨y, hy⟩ := by
        show L.lt (imageOpens (traceOpens W V)) x y
        rw [hVs]; exact hxy
      refine TransGen.lift Subtype.val (fun a b hab => ?_) ((h _ hS' _ hVsV' _ _).2 hxy')
      obtain ⟨_, ⟨O, hO, rfl⟩, hab⟩ := hab
      refine ⟨O, hO, (LocalCausality.extend_lt_iff (inf_le_left.trans hVW)).2 ?_⟩
      have hab' : L.lt (imageOpens (traceOpens W V ⊓ traceOpens W O)) a b := hab
      rwa [hstep] at hab'
  · intro h S' hS' Vs hVs a b
    have hVV' : imageOpens Vs ≤ imageOpens V' := imageOpens_mono hVs
    have hS : ∀ z ∈ imageOpens V', ∃ O ∈ imageOpens '' S', z ∈ O := by
      intro z hz
      obtain ⟨z, hz, rfl⟩ := hz
      obtain ⟨O', hO', hzO'⟩ := hS' z hz
      exact ⟨imageOpens O', mem_image_of_mem _ hO', val_mem_imageOpens.2 hzO'⟩
    have hmem : ∀ {c : M} {O : Opens M}, c ∈ imageOpens Vs ⊓ O →
        c ∈ Subtype.val '' (univ : Set W) :=
      fun {c} {O} hc => ⟨⟨c, imageOpens_le Vs hc.1⟩, trivial, rfl⟩
    refine ⟨fun hab => ?_, fun hab => ?_⟩
    · have hab' : L.extend.le (imageOpens Vs) a b :=
        (LocalCausality.extend_le_iff (imageOpens_le Vs)).2 hab
      refine transGen_of_image (f := Subtype.val) (s := univ) ?_ ?_ trivial trivial
        ((h _ hS _ hVV' a b).1 hab')
      · rintro c d ⟨O, -, hcd⟩
        exact hmem (L.extend.le_mem_left hcd)
      · rintro p - q - ⟨_, ⟨O', hO', rfl⟩, hpq⟩
        refine ⟨O', hO', ?_⟩
        rw [← imageOpens_inf] at hpq
        exact (LocalCausality.extend_le_iff (imageOpens_le _)).1 hpq
    · have hab' : L.extend.lt (imageOpens Vs) a b :=
        (LocalCausality.extend_lt_iff (imageOpens_le Vs)).2 hab
      refine transGen_of_image (f := Subtype.val) (s := univ) ?_ ?_ trivial trivial
        ((h _ hS _ hVV' a b).2 hab')
      · rintro c d ⟨O, -, hcd⟩
        exact hmem (L.extend.lt_mem_left hcd)
      · rintro p - q - ⟨_, ⟨O', hO', rfl⟩, hpq⟩
        refine ⟨O', hO', ?_⟩
        rw [← imageOpens_inf] at hpq
        exact (LocalCausality.extend_lt_iff (imageOpens_le _)).1 hpq

theorem toSubtype_absolutelyMinimal_iff :
    L.toSubtype.AbsolutelyMinimal ↔ L.extend.AbsolutelyMinimalOn W := by
  rw [Precausality.absolutelyMinimal_iff, toSubtype_absolutelyMinimalOn_iff, imageOpens_top]

theorem toSubtype_absolutelyMinimalOn_all_iff :
    (∀ V' : Opens W, L.toSubtype.AbsolutelyMinimalOn V') ↔
      ∀ W' : Opens M, W' ≤ W → L.extend.AbsolutelyMinimalOn W' := by
  constructor
  · intro h W' hW'
    have := (L.toSubtype_absolutelyMinimalOn_iff (traceOpens W W')).1 (h _)
    rwa [imageOpens_traceOpens hW'] at this
  · intro h V'
    exact (L.toSubtype_absolutelyMinimalOn_iff V').2 (h _ (imageOpens_le V'))

end LocalCausality

/-! ### Restriction -/

namespace Causality

variable {C : Causality M} {U W : Opens M}

/-- `relativeTo U` has the relations of `C` on the open subsets of `U`. -/
theorem relativeTo_agree (hV : W ≤ U) (x y : M) :
    ((C.relativeTo U).le W x y ↔ C.le W x y) ∧ ((C.relativeTo U).lt W x y ↔ C.lt W x y) :=
  ⟨relativeTo_le_iff hV, LocalCausality.extend_lt_iff hV⟩

theorem relativeTo_absolutelyMinimalOn_iff (hW : W ≤ U) :
    (C.relativeTo U).AbsolutelyMinimalOn W ↔ C.AbsolutelyMinimalOn W :=
  Precausality.absolutelyMinimalOn_congr fun _ hV x y => relativeTo_agree (hV.trans hW) x y

/-- **Restriction carried by `M`, hereditary form**: `C` hereditarily minimal ⇒ `C.relativeTo U`
hereditarily minimal. -/
theorem relativeTo_absolutelyMinimalOn_all (h : ∀ W : Opens M, C.AbsolutelyMinimalOn W)
    (U W : Opens M) : (C.relativeTo U).AbsolutelyMinimalOn W := by
  exact LocalCausality.extend_absolutelyMinimalOn_all (C.restrict U)
    (fun W' hW' => (relativeTo_absolutelyMinimalOn_iff hW').2 (h W')) W

/-- **Restriction carried by `M`, M-only form**: `C` absolutely minimal ⇒ `C.relativeTo U`
absolutely minimal, for every open `U`. -/
theorem relativeTo_absolutelyMinimal (h : C.AbsolutelyMinimal) (U : Opens M) :
    (C.relativeTo U).AbsolutelyMinimal := by
  rw [Precausality.absolutelyMinimal_iff] at h ⊢
  intro S hS V _ x y
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · have hxy' : (x = y ∧ x ∈ V) ∨ C.le (V ⊓ U) x y := hxy
    rcases hxy' with ⟨rfl, hx⟩ | hxy'
    · obtain ⟨O, hO, hxO⟩ := hS x trivial
      exact TransGen.single ⟨O, hO, Or.inl ⟨rfl, hx, hxO⟩⟩
    · refine TransGen.mono ?_ ((h S hS (V ⊓ U) le_top x y).1 hxy')
      rintro a b ⟨O, hO, hab⟩
      refine ⟨O, hO, Or.inr ?_⟩
      show C.le (V ⊓ O ⊓ U) a b
      rwa [inf_right_comm]
  · have hxy' : C.lt (V ⊓ U) x y := hxy
    refine TransGen.mono ?_ ((h S hS (V ⊓ U) le_top x y).2 hxy')
    rintro a b ⟨O, hO, hab⟩
    refine ⟨O, hO, ?_⟩
    show C.lt (V ⊓ O ⊓ U) a b
    rwa [inf_right_comm]

/-- The restriction of `C` to `W`, as a spacetime of its own, is absolutely minimal on `V'` iff `C`
is absolutely minimal on the image of `V'`. -/
theorem restrict_toSubtype_absolutelyMinimalOn_iff (C : Causality M) (W : Opens M)
    (V' : Opens W) :
    ((C.restrict W).toSubtype).AbsolutelyMinimalOn V' ↔ C.AbsolutelyMinimalOn (imageOpens V') := by
  exact ((C.restrict W).toSubtype_absolutelyMinimalOn_iff V').trans
    (relativeTo_absolutelyMinimalOn_iff (C := C) (imageOpens_le V'))

/-- **Restriction as a spacetime, hereditary form**: every open subset of a hereditarily minimal
causality is, with the restricted causality, a hereditarily minimal spacetime. -/
theorem restrict_toSubtype_absolutelyMinimalOn_all (h : ∀ W : Opens M, C.AbsolutelyMinimalOn W)
    (W : Opens M) (V' : Opens W) : ((C.restrict W).toSubtype).AbsolutelyMinimalOn V' := by
  exact (restrict_toSubtype_absolutelyMinimalOn_iff C W V').2 (h _)

/-- **Restriction as a spacetime, M-only form**: it is absolute minimality of `C` on `W`. -/
theorem restrict_toSubtype_absolutelyMinimal_iff (C : Causality M) (W : Opens M) :
    ((C.restrict W).toSubtype).AbsolutelyMinimal ↔ C.AbsolutelyMinimalOn W := by
  rw [Precausality.absolutelyMinimal_iff, restrict_toSubtype_absolutelyMinimalOn_iff,
    imageOpens_top]

/-- For a locally causally arc-connected causality the two forms of gluing agree. -/
theorem LocallyCausallyArcConnected.absolutelyMinimal_iff_all
    (hloc : C.LocallyCausallyArcConnected) :
    C.AbsolutelyMinimal ↔ ∀ W : Opens M, C.AbsolutelyMinimalOn W :=
  ⟨fun h => hloc.absolutelyMinimalOn h, fun h => Precausality.absolutelyMinimal_iff.2 (h ⊤)⟩

end Causality

/-! ### The transparent-point line separates the two forms on restrictions -/

/-- **The M-only form is not preserved by restriction to an open subset, as a spacetime**: the
transparent-point line is absolutely minimal, its restriction to `ℝ ∖ {0}` is not. -/
theorem transparentLine_restrict_toSubtype_not_absolutelyMinimal :
    transparentLine.AbsolutelyMinimal ∧
      ¬ ((transparentLine.restrict realMinusZero).toSubtype).AbsolutelyMinimal := by
  refine ⟨transparentLine_absolutelyMinimal, fun h => ?_⟩
  exact transparentLine_not_absolutelyMinimalOn
    ((Causality.restrict_toSubtype_absolutelyMinimal_iff _ _).1 h)

/-- The extension of a causality given on `W` may be absolutely minimal on `M` without being so
on `W`: `relativeTo (ℝ ∖ {0})` of the transparent-point line. -/
theorem transparentLine_relativeTo_separates :
    (transparentLine.relativeTo realMinusZero).AbsolutelyMinimal ∧
      ¬ (transparentLine.relativeTo realMinusZero).AbsolutelyMinimalOn realMinusZero := by
  exact ⟨Causality.relativeTo_absolutelyMinimal transparentLine_absolutelyMinimal _,
    fun h => transparentLine_not_absolutelyMinimalOn
      ((Causality.relativeTo_absolutelyMinimalOn_iff le_rfl).1 h)⟩

/-! ### `ex:open_subset`, first sentence: uniqueness fails under gluing -/

/-- **`ex:open_subset`, first sentence, uniqueness is false under gluing, in either form**: the
open set `ℝ` of the timelike line carries two distinct causalities, both hereditarily minimal (so
absolutely minimal), for which the inclusion is a strong morphism: the restriction and the
diagonal one. -/
theorem openSubset_not_unique_of_absolutelyMinimal :
    ∃ L₁ L₂ : LocalCausality (⊤ : Opens ℝ), L₁.InclusionStrong timelikeLine ∧
      L₂.InclusionStrong timelikeLine ∧
      (∀ V' : Opens (⊤ : Opens ℝ), L₁.toSubtype.AbsolutelyMinimalOn V') ∧
      (∀ V' : Opens (⊤ : Opens ℝ), L₂.toSubtype.AbsolutelyMinimalOn V') ∧
      L₁.le ⊤ 0 1 ∧ ¬ L₂.le ⊤ 0 1 := by
  refine ⟨timelikeLine.restrict ⊤, LocalCausality.diagonal ⊤,
    timelikeLine.restrict_inclusionStrong ⊤, LocalCausality.diagonal_inclusionStrong _,
    Causality.restrict_toSubtype_absolutelyMinimalOn_all timelikeLine_absolutelyMinimalOn ⊤,
    fun V' => ((LocalCausality.diagonal ⊤).toSubtype_absolutelyMinimalOn_iff V').2
      (LocalCausality.diagonal_extend_absolutelyMinimalOn _ _), ?_, ?_⟩
  · exact ⟨zero_le_one, fun _ _ => trivial⟩
  · rintro ⟨h, -⟩
    exact zero_ne_one h

end Causal
