import Causal.GluingGeneric.Basic
import Causal.Chains
import Causal.SubExtension

/-!
# Gluing in its hereditary form, generic constructions (4): causalities from one global relation

No label of `ETT.tex` is marked by this file (target `T-abs-gluing-generic`, DEC-167 step 1a).
Cited, unmarked: `defi:causalite` — `ETT.tex:237`.

> Equivalently, a causality is a pair $(\leq,\tll )=(\leq_{\U},\ll_\U)_{\U\subset M}$ of families
> of preorder relations on $M$ […] (`ETT.tex:245`)

`Causality.ofRelation R S` (`Causal.LinesReachable`) restricts one global preorder `R` and one
global transitive relation `S` to every open set. It is a causality of the "equivalently" form, with
no gluing (kb/0014). This file says exactly when it glues.

## What is proved (no `sorry` in this file)

* `Causality.ofRelation_absolutelyMinimalOn_of_eq`: if `R` and `S` are contained in the diagonal,
  `ofRelation R S` is hereditarily minimal (no hypothesis on `M`).
* **Hereditary form** (`ofRelation_absolutelyMinimalOn_all_iff`, `M` Hausdorff): `ofRelation R S`
  is hereditarily minimal **iff** `R` and `S` are contained in the diagonal.
* **M-only form** (`ofRelation_absolutelyMinimal_iff`, `M` a `T₂.₅` space, e.g. metrizable): the
  same characterization. Both come from the jump lemma of `Causal.GluingGeneric.Basic`
  (`Precausality.AbsolutelyMinimalOn.mem_of_le_sup`).
* The library's `ofRelation` sites, as corollaries (they may duplicate the concrete inventory of
  `T-abs-gluing-models`): **not** absolutely minimal: `totalLine`
  (`totalLine_not_absolutelyMinimal`), `fan`, `bowtie`, `puncturedPlane`
  (`puncturedPlane_not_absolutelyMinimal`, the punctured null plane of `Causal.LinesReachable`);
  hereditarily minimal: `diagonalCausality` (`diagonalCausality_absolutelyMinimalOn_all`) and
  `pointSpace` (`pointSpace_absolutelyMinimalOn_all`, a subsingleton).

## Hypothesis checklist

| the construction | here |
|---|---|
| `ofRelation`: a global preorder `R`, a global transitive `S ⊆ R` with open sections | ✓ carried |
| separation | `T2Space M` for the hereditary characterization, `T25Space M` for the M-only one; neither for the sufficient condition |

## SCOPE (disclosed)

* On a non-Hausdorff space `ofRelation` may glue with a non-diagonal `R` (e.g. any precausality
  on Sierpiński space is hereditarily minimal, `Precausality.absolutelyMinimalOn_prop` of
  `Causal.GluingGeneric.Pullback`); the characterization is stated where the separation it
  uses holds.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {R S : M → M → Prop} (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
  (hStrans : ∀ x y z, S x y → S y z → S x z) (hSR : ∀ x y, S x y → R x y)
  (hright : ∀ x, IsOpen {y | S x y}) (hleft : ∀ y, IsOpen {x | S x y})

/-- `ofRelation R S` with `R` and `S` inside the diagonal is absolutely minimal on every open
set. -/
theorem ofRelation_absolutelyMinimalOn_of_eq (hR : ∀ x y, R x y → x = y)
    (hS : ∀ x y, S x y → x = y) (W : Opens M) :
    (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).AbsolutelyMinimalOn W := by
  intro S' hS' V hV x y
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · obtain ⟨hx, hy, hxy'⟩ := hxy
    obtain rfl := hR x y hxy'
    obtain ⟨O, hO, hxO⟩ := hS' x (hV hx)
    exact TransGen.single ⟨O, hO, ⟨hx, hxO⟩, ⟨hx, hxO⟩, hxy'⟩
  · obtain ⟨hx, hy, hxy'⟩ := hxy
    obtain rfl := hS x y hxy'
    obtain ⟨O, hO, hxO⟩ := hS' x (hV hx)
    exact TransGen.single ⟨O, hO, ⟨hx, hxO⟩, ⟨hx, hxO⟩, hxy'⟩

/-- **`ofRelation`, hereditary form**: on a Hausdorff space, `ofRelation R S` is absolutely minimal
on every open set iff `R` and `S` are contained in the diagonal. -/
theorem ofRelation_absolutelyMinimalOn_all_iff [T2Space M] :
    (∀ W : Opens M,
        (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).AbsolutelyMinimalOn W) ↔
      (∀ x y, R x y → x = y) ∧ (∀ x y, S x y → x = y) := by
  constructor
  · intro h
    have key : ∀ (r : Opens M → M → M → Prop) (T : M → M → Prop),
        (∀ (U : Opens M) x y, x ∈ U → y ∈ U → T x y → r U x y) →
        (∀ (A B : Opens M) x y, Disjoint (A : Set M) B → x ∈ A → r (A ⊔ B) x y → y ∈ A) →
        ∀ x y, T x y → x = y := by
      intro r T hr hjump x y hxy
      by_contra hne
      obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := t2_separation hne
      have hyA := hjump ⟨A, hA⟩ ⟨B, hB⟩ x y hAB hxA
        (hr _ x y (Opens.mem_sup.2 (Or.inl hxA)) (Opens.mem_sup.2 (Or.inr hyB)) hxy)
      exact Set.disjoint_left.1 hAB hyA hyB
    exact ⟨key (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).le R
        (fun U x y hx hy h => ⟨hx, hy, h⟩)
        (fun A B x y hAB hx h' => ((h (A ⊔ B)).mem_of_le_sup_of_disjoint hAB hx).1 h'),
      key (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).lt S
        (fun U x y hx hy h => ⟨hx, hy, h⟩)
        (fun A B x y hAB hx h' => ((h (A ⊔ B)).mem_of_le_sup_of_disjoint hAB hx).2 h')⟩
  · rintro ⟨hR, hS⟩ W
    exact ofRelation_absolutelyMinimalOn_of_eq hrefl htrans hStrans hSR hright hleft hR hS W

/-- **`ofRelation`, M-only form**: on a `T₂.₅` space, `ofRelation R S` is absolutely minimal iff
`R` and `S` are contained in the diagonal. -/
theorem ofRelation_absolutelyMinimal_iff [T25Space M] :
    (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).AbsolutelyMinimal ↔
      (∀ x y, R x y → x = y) ∧ (∀ x y, S x y → x = y) := by
  constructor
  · intro h
    rw [Precausality.absolutelyMinimal_iff] at h
    have key : ∀ (r : Opens M → M → M → Prop) (T : M → M → Prop),
        (∀ (U : Opens M) x y, x ∈ U → y ∈ U → T x y → r U x y) →
        (∀ (A B : Opens M) x y,
          (∀ z ∈ (⊤ : Opens M), z ∉ closure (A : Set M) ∨ z ∉ closure (B : Set M)) →
            x ∈ A → r (A ⊔ B) x y → y ∈ A) →
        ∀ x y, T x y → x = y := by
      intro r T hr hjump x y hxy
      by_contra hne
      obtain ⟨u, hxu, hu, v, hyv, hv, huv⟩ := exists_open_nhds_disjoint_closure hne
      have hcl : ∀ z ∈ (⊤ : Opens M), z ∉ closure u ∨ z ∉ closure v := by
        intro z _
        by_cases hz : z ∈ closure u
        · exact Or.inr fun hz' => Set.disjoint_left.1 huv hz hz'
        · exact Or.inl hz
      have hyA := hjump ⟨u, hu⟩ ⟨v, hv⟩ x y hcl hxu
        (hr _ x y (Opens.mem_sup.2 (Or.inl hxu)) (Opens.mem_sup.2 (Or.inr hyv)) hxy)
      exact Set.disjoint_left.1 huv (subset_closure hyA) (subset_closure hyv)
    exact ⟨key (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).le R
        (fun U x y hx hy h => ⟨hx, hy, h⟩)
        (fun A B x y hcl hx h' => (h.mem_of_le_sup le_top le_top hcl hx).1 h'),
      key (Causality.ofRelation R S hrefl htrans hStrans hSR hright hleft).lt S
        (fun U x y hx hy h => ⟨hx, hy, h⟩)
        (fun A B x y hcl hx h' => (h.mem_of_le_sup le_top le_top hcl hx).2 h')⟩
  · rintro ⟨hR, hS⟩
    exact Precausality.absolutelyMinimal_iff.2
      (ofRelation_absolutelyMinimalOn_of_eq hrefl htrans hStrans hSR hright hleft hR hS ⊤)

end Causality

/-! ### The library's `ofRelation` sites -/

theorem totalLine_not_absolutelyMinimal : ¬ totalLine.AbsolutelyMinimal := by
  intro h
  exact zero_ne_one (((Causality.ofRelation_absolutelyMinimal_iff _ _ _ _ _ _).1 h).1 0 1 trivial)

theorem fan_not_absolutelyMinimal : ¬ fan.AbsolutelyMinimal := by
  intro h
  have := ((Causality.ofRelation_absolutelyMinimal_iff _ _ _ _ _ _).1 h).1 0 2
    (Or.inr (Or.inl rfl))
  omega

theorem bowtie_not_absolutelyMinimal : ¬ bowtie.AbsolutelyMinimal := by
  intro h
  have := ((Causality.ofRelation_absolutelyMinimal_iff _ _ _ _ _ _).1 h).1 Bowtie.a₁ Bowtie.b₁
    (Or.inr ⟨trivial, fun h => h⟩)
  cases this

theorem puncturedPlane_not_absolutelyMinimal : ¬ puncturedPlane.AbsolutelyMinimal := by
  intro h
  let p : PuncturedPlane := ⟨(1, 1), fun h => by simp [Prod.ext_iff] at h⟩
  let q : PuncturedPlane := ⟨(2, 2), fun h => by simp [Prod.ext_iff] at h⟩
  have hpq := ((Causality.ofRelation_absolutelyMinimal_iff _ _ _ _ _ _).1 h).2 p q
    (show (1 : ℝ) < 2 ∧ (1 : ℝ) < 2 by norm_num)
  have := congrArg (fun z : PuncturedPlane => z.1.1) hpq
  norm_num [p, q] at this

theorem diagonalCausality_absolutelyMinimalOn_all (M : Type u) [TopologicalSpace M]
    [DiscreteTopology M] (W : Opens M) : (diagonalCausality M).AbsolutelyMinimalOn W := by
  exact Causality.ofRelation_absolutelyMinimalOn_of_eq _ _ _ _ _ _ (fun _ _ h => h)
    (fun _ _ h => h) W

theorem pointSpace_absolutelyMinimalOn_all (W : Opens Unit) :
    pointSpace.AbsolutelyMinimalOn W :=
  Precausality.absolutelyMinimalOn_of_subsingleton _ W

end Causal
