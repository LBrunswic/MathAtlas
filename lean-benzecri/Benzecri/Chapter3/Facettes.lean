import Mathlib

/-!
# Chapter 3 § 1 — the preorder α(W) on a convex set, W-facettes and their order, supports, filtering

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 1, journal pp. 259–260; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (checked against the scan, PDF pp. 32–33).
Target T-bz-c3-facettes. Over an arbitrary real vector space `E`, no topology on `E`.

* **`bzdef:c3s1d1_preordre_alpha`** — `benzecri1960_ch3.tex:91` (Déf. 1, l.91–95; the
  simplified form l.97–106; the preorder check l.114–123) — `Benzecri.AlphaW`, the printed
  simplification `alphaW_iff_openSegment`, reflexivity `alphaW_refl`, transitivity
  `alphaW_trans` (W convex), the preorder `alphaPreorder` on the points of `W`.
* **`bzdef:c3s1d2_facette`** — `benzecri1960_ch3.tex:125` (Déf. 2, l.125–132) — `Benzecri.FW`
  (an equivalence, `fwSetoid`), the facettes `IsFacette` (the classes: `isFacette_iff_quotient`),
  `FacetteLE`, well defined (`facetteLE_iff_forall`), the order `facettePartialOrder` on
  `Facette W`, induced by α (`facetteLE_facetteOf_iff`). Instance: `isFacette_Icc_iff`,
  `segment01_order`.
* **`bzrem:c3s1r1_facette_points_interieurs`** — `benzecri1960_ch3.tex:134` (Remarque,
  l.134–138) — the printed « si » and its converse: `fw_iff_interieur_moduleTopology` (bare `E`,
  the canonical topology of `L`), `fw_iff_interieur` (any Hausdorff topological vector space
  structure on `E`; the « si » `fw_of_interieur` needs no Hausdorff hypothesis);
  « une même facette » `pairwise_fw_iff_exists_facette`.
* **`bzprop:c3s1p2_alpha_support`** — `benzecri1960_ch3.tex:152` (Prop. 2, l.152–155, proof
  l.157–162) — `Benzecri.alphaW_iff_mem_support`.
* **`bzprop:c3s1p3_ordre_supports`** — `benzecri1960_ch3.tex:164` (Prop. 3, l.164–167, no proof
  printed) — `facetteLE_iff_support_le`, `support_eq_iff`.
* **`bzprop:c3s1p4_facettes_filtrant`** — `benzecri1960_ch3.tex:170` (Prop. 4, l.170–172, proof
  l.174–178) — `facettes_filtrant`, `facettes_isDirected`.
* **`bzcor:c3s1p4c_supports_filtrant`** — `benzecri1960_ch3.tex:180` (Corollaire, l.180–183, no
  proof printed) — `supports_filtrant`.

> **Définition 1.** Sur un ensemble convexe $W$, dans un espace vectoriel, on définit la relation
> de préordre $\alpha(W)$ : $A\,\alpha(W)\,B$ s'il existe un segment $(A', B)\subset W$ tel que
> $A\in)A', B($, ou si $A=B$.
>
> **Définition 2.** La relation d'équivalence associée à la relation de préordre $\alpha(W)$ se
> note $F_W(A, B)$ : les classes d'équivalence correspondantes sont appelées *$W$-facettes*. La
> relation de préordre $\alpha$ définit canoniquement sur l'ensemble des facettes une relation
> d'ordre que nous noterons aussi $\alpha$.
>
> **Remarque.** On peut donner de la définition de $F_W(A, B)$ l'énoncé suivant : $n$ points
> $A_1$, …, $A_n$ de $W$ appartiennent à une même facette si, pour la topologie de la variété
> linéaire $L$ support de $\{A_1, …, A_n\}$, $A_1$, …, $A_n$ sont intérieurs à $L\cap W$.
>
> **Proposition 2.** Soient $F$ une facette de $W$, $L$ son support, et soient $A\in F$,
> $B\in W$; alors $A\,\alpha\,B$ si et seulement si $B\in L$.
>
> **Proposition 3.** Soit $F$, $F'$ deux facettes de $W$ de supports $L$ et $L'$; on a
> $F\,\alpha\,F'$ si et seulement si $L'\subset L$; on a $L=L'$ si et seulement si $F=F'$.
>
> **Proposition 4.** L'ensemble des facettes muni de la relation d'ordre $\alpha$ est filtrant à
> gauche.
>
> **Corollaire.** L'ensemble des variétés linéaires supports de facettes du convexe $W$ est
> filtrant à droite pour la relation d'inclusion.

## The proofs formalized

Everything runs through `alphaW_iff_extend`: for `W` convex, `A α B` iff `A, B ∈ W` and
`A + ε (A − B) ∈ W` for some `ε > 0` (the segment from `B` through `A` extends beyond `A`).
Transitivity is an explicit convex combination of the two extension points (the printed proof
goes through the convex hull of `A′, B′, C`, the same computation). The two-sided directions
of `W` at `A ∈ W` form a vector subspace `dirW`; every `B − A`, `B ∈ F`, lies in it, hence the
whole direction of the support `L`: that is Prop. 2's « si », and finitely many directions have a
common bound (`exists_uniform_isDirW`), which with the open mapping theorem for a surjection onto
a finite-dimensional space is the Remark's converse. Prop. 2's « seulement si » takes the point
`C = A + (ε/2)(A − B)` of `F`, and `B` on the line `AC`. Prop. 3 is Prop. 2 applied twice, then
antisymmetry; Prop. 4 is the printed midpoint; the corollary is Prop. 4 through Prop. 3.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « dans un espace vectoriel » (real) | ✓ carried: `[AddCommGroup E] [Module ℝ E]`, any dimension, no topology |
| « un ensemble convexe $W$ » | ✓ carried: `Convex ℝ W` where used; `AlphaW`, `FW`, `IsFacette`, `FacetteLE` are defined for every `W` |
| Déf. 1: « un segment $(A', B)\subset W$ » | ✓ carried: `segment ℝ A' B ⊆ W` (closed segment, Chapter 1's $(A, B)$) |
| Déf. 1: « ou si $A=B$ » | ✓ carried: `A = B ∧ A ∈ W` (a relation on the points of `W`) |
| Remark: « la topologie de la variété linéaire $L$ » | ✓ carried: the canonical topology (`moduleTopology`) of the finite-dimensional direction of `L`; also, as a cross-check, the topology induced by any Hausdorff vector topology on `E` |
| Props. 2–4: « $F$ une facette de $W$ », « $L$ son support » | ✓ carried: `IsFacette W F`, `affineSpan ℝ F` |
| Prop. 4: « filtrant à gauche » | ✓ carried: `DirectedOn` for the reversed order, and `IsDirected (Facette W) (· ≥ ·)` |
| Corollaire: « filtrant à droite pour l'inclusion » | ✓ carried: `DirectedOn (· ≤ ·)` on `AffineSubspace ℝ E` |

## SCOPE (disclosed)

* Nothing is omitted; no `sorry`. The Remark is proved as an equivalence (the printed « si » is
  `fw_of_interieur` / the `←` of `fw_iff_interieur_moduleTopology`); « $n$ points appartiennent à
  une même facette » is read as `F_W` pairwise, equivalent to membership in one facette for
  `n ≥ 1` (`pairwise_fw_iff_exists_facette`).
* Déf. 2's « canoniquement »: the order on `Facette W` is `F α F′ ⟺ ∃ A ∈ F, A′ ∈ F′, A α A′`,
  equivalently for all representatives (`facetteLE_iff_forall`).
* The instance (non-vacuity): the segment `[0, 1] ⊂ ℝ` has exactly the facettes `{0}`, `{1}`,
  `]0, 1[` (`isFacette_Icc_iff`), with `]0, 1[ α {0}` and not conversely (`segment01_order`);
  the support of `]0, 1[` is the whole line (`affineSpan_Ioo01`).
* Prop. 1 (`bzprop:c3s1p1_facette_ouverte`, the finest locally convex topology) is not in this
  target.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology

namespace Benzecri

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Déf. 1 -/

/-- **Déf. 1.** `A α(W) B`: there is a closed segment `(A′, B) ⊆ W` with `A` in the open
segment `)A′, B(`, or `A = B` (a point of `W`). -/
def AlphaW (W : Set E) (A B : E) : Prop :=
  (∃ A' : E, segment ℝ A' B ⊆ W ∧ A ∈ openSegment ℝ A' B) ∨ (A = B ∧ A ∈ W)

/-- **Déf. 1, simplified** (l.97–106): with the convention `)A, A( = {A}` (Mathlib's
`openSegment_same`) the clause « ou si A = B » is absorbed. -/
theorem alphaW_iff_openSegment {W : Set E} {A B : E} :
    AlphaW W A B ↔ ∃ A' : E, segment ℝ A' B ⊆ W ∧ A ∈ openSegment ℝ A' B := by
  constructor
  · rintro (h | ⟨rfl, hA⟩)
    · exact h
    · exact ⟨A, by simpa [segment_same] using hA, by simp [openSegment_same]⟩
  · exact Or.inl

theorem AlphaW.mem_left {W : Set E} {A B : E} (h : AlphaW W A B) : A ∈ W := by
  obtain ⟨A', hs, hA⟩ := alphaW_iff_openSegment.1 h
  exact hs (openSegment_subset_segment _ _ _ hA)

theorem AlphaW.mem_right {W : Set E} {A B : E} (h : AlphaW W A B) : B ∈ W := by
  obtain ⟨A', hs, -⟩ := alphaW_iff_openSegment.1 h
  exact hs (right_mem_segment _ _ _)

/-- α(W) for convex `W`: the segment from `B` through `A` extends beyond `A` in `W`. -/
theorem alphaW_iff_extend {W : Set E} (hW : Convex ℝ W) {A B : E} :
    AlphaW W A B ↔ A ∈ W ∧ B ∈ W ∧ ∃ ε : ℝ, 0 < ε ∧ A + ε • (A - B) ∈ W := by
  constructor
  · intro h
    refine ⟨h.mem_left, h.mem_right, ?_⟩
    obtain ⟨A', hs, a, b, ha, hb, hab, hAeq⟩ := alphaW_iff_openSegment.1 h
    refine ⟨b / a, div_pos hb ha, ?_⟩
    have key : a • (A + (b / a) • (A - B)) = a • A' := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ ha.ne']
      subst hAeq
      obtain rfl : a = 1 - b := by linarith
      module
    rw [smul_right_injective E ha.ne' key]
    exact hs (left_mem_segment _ _ _)
  · rintro ⟨hA, hB, ε, hε, hP⟩
    refine alphaW_iff_openSegment.2 ⟨A + ε • (A - B), hW.segment_subset hP hB, ?_⟩
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, by field_simp, ?_⟩
    have h1 : (A + ε • (A - B)) + ε • B = (1 + ε) • A := by module
    rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, one_smul, ← smul_add, h1,
      inv_smul_smul₀ (by positivity)]

theorem alphaW_refl {W : Set E} {A : E} (hA : A ∈ W) : AlphaW W A A := Or.inr ⟨rfl, hA⟩

/-- **Déf. 1**: α(W) is transitive (the printed check, l.114–123). -/
theorem alphaW_trans {W : Set E} (hW : Convex ℝ W) {A B C : E}
    (hAB : AlphaW W A B) (hBC : AlphaW W B C) : AlphaW W A C := by
  obtain ⟨hA, -, ε, hε, hP⟩ := (alphaW_iff_extend hW).1 hAB
  obtain ⟨-, hC, δ, hδ, hQ⟩ := (alphaW_iff_extend hW).1 hBC
  set D : ℝ := 1 + δ + ε with hD
  have hDpos : 0 < D := by positivity
  refine (alphaW_iff_extend hW).2 ⟨hA, hC, ε * δ / D, by positivity, ?_⟩
  have hmem := hW hP hQ (a := (1 + δ) / D) (b := ε / D) (by positivity) (by positivity)
    (by field_simp; ring)
  convert hmem using 1
  apply smul_right_injective E hDpos.ne'
  have e1 : D * (ε * δ / D) = ε * δ := mul_div_cancel₀ _ hDpos.ne'
  have e2 : D * ((1 + δ) / D) = 1 + δ := mul_div_cancel₀ _ hDpos.ne'
  have e3 : D * (ε / D) = ε := mul_div_cancel₀ _ hDpos.ne'
  simp only [smul_add, smul_smul, ← mul_assoc, e1, e2, e3]
  rw [hD]
  module

/-- The preorder α(W) on the points of `W`. -/
@[reducible] def alphaPreorder {W : Set E} (hW : Convex ℝ W) : Preorder W where
  le A B := AlphaW W A B
  le_refl A := alphaW_refl A.2
  le_trans _ _ _ h₁ h₂ := alphaW_trans hW h₁ h₂

/-! ### Déf. 2 -/

/-- **Déf. 2.** `F_W(A, B)`: the equivalence relation associated with the preorder α(W). -/
def FW (W : Set E) (A B : E) : Prop := AlphaW W A B ∧ AlphaW W B A

/-- The `W`-facette of `A`: the class of `A` for `F_W`. -/
def facetteOf (W : Set E) (A : E) : Set E := {B | FW W A B}

/-- **Déf. 2.** `F` is a `W`-facette: an equivalence class of `F_W` (of a point of `W`). -/
def IsFacette (W F : Set E) : Prop := ∃ A ∈ W, F = facetteOf W A

/-- **Déf. 2.** The order α on facettes, induced by the preorder α(W). -/
def FacetteLE (W F F' : Set E) : Prop := ∃ A ∈ F, ∃ A' ∈ F', AlphaW W A A'

/-- The set of `W`-facettes, as a type. -/
def Facette (W : Set E) : Type _ := {F : Set E // IsFacette W F}

theorem fw_refl {W : Set E} {A : E} (hA : A ∈ W) : FW W A A := ⟨alphaW_refl hA, alphaW_refl hA⟩

theorem FW.symm {W : Set E} {A B : E} (h : FW W A B) : FW W B A := ⟨h.2, h.1⟩

theorem FW.trans {W : Set E} (hW : Convex ℝ W) {A B C : E} (h₁ : FW W A B) (h₂ : FW W B C) :
    FW W A C := ⟨alphaW_trans hW h₁.1 h₂.1, alphaW_trans hW h₂.2 h₁.2⟩

/-- `F_W` is an equivalence relation on the points of `W`. -/
def fwSetoid {W : Set E} (hW : Convex ℝ W) : Setoid W where
  r A B := FW W A B
  iseqv := ⟨fun A => fw_refl A.2, FW.symm, FW.trans hW⟩

theorem mem_facetteOf_self {W : Set E} {A : E} (hA : A ∈ W) : A ∈ facetteOf W A := fw_refl hA

theorem isFacette_facetteOf {W : Set E} {A : E} (hA : A ∈ W) : IsFacette W (facetteOf W A) :=
  ⟨A, hA, rfl⟩

theorem facetteOf_eq_of_fw {W : Set E} (hW : Convex ℝ W) {A B : E} (h : FW W A B) :
    facetteOf W A = facetteOf W B := by
  ext C
  exact ⟨fun hC => h.symm.trans hW hC, fun hC => h.trans hW hC⟩

theorem IsFacette.eq_facetteOf {W : Set E} (hW : Convex ℝ W) {F : Set E} (hF : IsFacette W F)
    {A : E} (hA : A ∈ F) : F = facetteOf W A := by
  obtain ⟨A₀, -, rfl⟩ := hF
  exact facetteOf_eq_of_fw hW hA

theorem IsFacette.subset {W F : Set E} (hF : IsFacette W F) : F ⊆ W := by
  obtain ⟨A₀, -, rfl⟩ := hF
  exact fun B hB => hB.1.mem_right

theorem IsFacette.nonempty {W F : Set E} (hF : IsFacette W F) : F.Nonempty := by
  obtain ⟨A₀, hA₀, rfl⟩ := hF
  exact ⟨A₀, mem_facetteOf_self hA₀⟩

/-- The facettes are exactly the classes of `F_W`. -/
theorem isFacette_iff_quotient {W : Set E} (hW : Convex ℝ W) {F : Set E} :
    IsFacette W F ↔ ∃ q : Quotient (fwSetoid hW),
      F = Subtype.val '' {A : W | Quotient.mk (fwSetoid hW) A = q} := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Quotient.mk _ ⟨A, hA⟩, ?_⟩
    ext B
    constructor
    · intro hB
      exact ⟨⟨B, hB.1.mem_right⟩, Quotient.sound hB.symm, rfl⟩
    · rintro ⟨B', hB', rfl⟩
      exact (Quotient.exact hB').symm
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h A =>
      refine ⟨A, A.2, ?_⟩
      ext B
      constructor
      · rintro ⟨B', hB', rfl⟩
        exact (Quotient.exact hB').symm
      · intro hB
        exact ⟨⟨B, hB.1.mem_right⟩, Quotient.sound hB.symm, rfl⟩

theorem facetteLE_iff_forall {W : Set E} (hW : Convex ℝ W) {F F' : Set E}
    (hF : IsFacette W F) (hF' : IsFacette W F') :
    FacetteLE W F F' ↔ ∀ A ∈ F, ∀ A' ∈ F', AlphaW W A A' := by
  constructor
  · rintro ⟨A₀, hA₀, A₀', hA₀', h⟩ A hA A' hA'
    have h1 : FW W A A₀ := by
      rw [hF.eq_facetteOf hW hA] at hA₀; exact hA₀
    have h2 : FW W A₀' A' := by
      rw [hF'.eq_facetteOf hW hA₀'] at hA'; exact hA'
    exact alphaW_trans hW (alphaW_trans hW h1.1 h) h2.1
  · intro h
    obtain ⟨A, hA⟩ := hF.nonempty
    obtain ⟨A', hA'⟩ := hF'.nonempty
    exact ⟨A, hA, A', hA', h A hA A' hA'⟩

theorem facetteLE_facetteOf_iff {W : Set E} (hW : Convex ℝ W) {A B : E} (hA : A ∈ W)
    (hB : B ∈ W) : FacetteLE W (facetteOf W A) (facetteOf W B) ↔ AlphaW W A B :=
  ⟨fun h => (facetteLE_iff_forall hW (isFacette_facetteOf hA) (isFacette_facetteOf hB)).1 h A
      (mem_facetteOf_self hA) B (mem_facetteOf_self hB),
    fun h => ⟨A, mem_facetteOf_self hA, B, mem_facetteOf_self hB, h⟩⟩

theorem FacetteLE.antisymm {W : Set E} (hW : Convex ℝ W) {F F' : Set E}
    (hF : IsFacette W F) (hF' : IsFacette W F') (h : FacetteLE W F F') (h' : FacetteLE W F' F) :
    F = F' := by
  obtain ⟨A, hA⟩ := hF.nonempty
  obtain ⟨A', hA'⟩ := hF'.nonempty
  have e : FW W A A' := ⟨(facetteLE_iff_forall hW hF hF').1 h A hA A' hA',
    (facetteLE_iff_forall hW hF' hF).1 h' A' hA' A hA⟩
  rw [hF.eq_facetteOf hW hA, hF'.eq_facetteOf hW hA']
  exact facetteOf_eq_of_fw hW e

/-- **Déf. 2.** α is a partial order on the set of facettes. -/
@[reducible] def facettePartialOrder {W : Set E} (hW : Convex ℝ W) : PartialOrder (Facette W) where
  le F G := FacetteLE W F.1 G.1
  le_refl F := by
    obtain ⟨A, hA⟩ := F.2.nonempty
    exact ⟨A, hA, A, hA, alphaW_refl (F.2.subset hA)⟩
  le_trans F G H hFG hGH := by
    obtain ⟨B, hB⟩ := G.2.nonempty
    obtain ⟨A, hA⟩ := F.2.nonempty
    obtain ⟨C', hC'⟩ := H.2.nonempty
    exact ⟨A, hA, C', hC', alphaW_trans hW
      ((facetteLE_iff_forall hW F.2 G.2).1 hFG A hA B hB)
      ((facetteLE_iff_forall hW G.2 H.2).1 hGH B hB C' hC')⟩
  le_antisymm F G h h' := Subtype.ext (FacetteLE.antisymm hW F.2 G.2 h h')

/-! ### Two-sided directions of `W` at a point -/

/-- `v` is a two-sided direction of `W` at `A`: `A + δ • v ∈ W` for all small `|δ|`. -/
def IsDirW (W : Set E) (A v : E) : Prop := ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| ≤ ε → A + δ • v ∈ W

theorem isDirW_of {W : Set E} (hW : Convex ℝ W) {A v : E} (hA : A ∈ W) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (h1 : A + a • v ∈ W) (h2 : A + b • (-v) ∈ W) : IsDirW W A v := by
  refine ⟨min a b, lt_min ha hb, fun δ hδ => ?_⟩
  rcases le_or_gt 0 δ with h0 | h0
  · have hδa : δ ≤ a := le_trans (le_abs_self δ) (hδ.trans (min_le_left _ _))
    have := hW.add_smul_mem hA h1 (t := δ / a) ⟨div_nonneg h0 ha.le, (div_le_one ha).2 hδa⟩
    convert this using 2
    rw [smul_smul, div_mul_cancel₀ _ ha.ne']
  · have hδb : -δ ≤ b := le_trans (neg_le_abs δ) (hδ.trans (min_le_right _ _))
    have := hW.add_smul_mem hA h2 (t := -δ / b)
      ⟨div_nonneg (by linarith) hb.le, (div_le_one hb).2 hδb⟩
    convert this using 2
    rw [smul_smul, div_mul_cancel₀ _ hb.ne', neg_smul_neg]

/-- The two-sided directions of a convex `W` at `A ∈ W` form a vector subspace. -/
def dirW {W : Set E} (hW : Convex ℝ W) {A : E} (hA : A ∈ W) : Submodule ℝ E where
  carrier := {v | IsDirW W A v}
  zero_mem' := ⟨1, one_pos, fun δ _ => by simpa using hA⟩
  add_mem' := by
    rintro v w ⟨ε, hε, hv⟩ ⟨η, hη, hw⟩
    refine ⟨min ε η / 2, by positivity, fun δ hδ => ?_⟩
    have h2 : |2 * δ| ≤ min ε η := by rw [abs_mul, abs_two]; linarith
    have := hW (hv (2 * δ) (h2.trans (min_le_left _ _))) (hw (2 * δ) (h2.trans (min_le_right _ _)))
      (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    convert this using 1
    module
  smul_mem' := by
    rintro c v ⟨ε, hε, hv⟩
    refine ⟨ε / (|c| + 1), by positivity, fun δ hδ => ?_⟩
    have hc : 0 ≤ |c| := abs_nonneg c
    have h1 : |δ| * |c| ≤ ε / (|c| + 1) * |c| := mul_le_mul_of_nonneg_right hδ hc
    have h3 : ε / (|c| + 1) * |c| ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    have : |δ * c| ≤ ε := by rw [abs_mul]; linarith
    show A + δ • (c • v) ∈ W
    rw [smul_smul]; exact hv _ this

theorem mem_dirW {W : Set E} (hW : Convex ℝ W) {A : E} (hA : A ∈ W) {v : E} :
    v ∈ dirW hW hA ↔ IsDirW W A v := Iff.rfl

theorem isDirW_sub_of_alphaW {W : Set E} (hW : Convex ℝ W) {A B : E} (h : AlphaW W A B) :
    IsDirW W A (B - A) := by
  obtain ⟨hA, hB, ε, hε, hP⟩ := (alphaW_iff_extend hW).1 h
  refine isDirW_of hW hA one_pos hε (by simpa using hB) ?_
  rwa [neg_sub]

theorem alphaW_of_isDirW {W : Set E} (hW : Convex ℝ W) {A B : E} (hB : B ∈ W)
    (h : IsDirW W A (B - A)) : AlphaW W A B := by
  obtain ⟨ε, hε, h⟩ := h
  have hA : A ∈ W := by simpa using h 0 (by simp; exact hε.le)
  refine (alphaW_iff_extend hW).2 ⟨hA, hB, ε, hε, ?_⟩
  have := h (-ε) (by rw [abs_neg, abs_of_pos hε])
  rwa [neg_smul, ← smul_neg, neg_sub] at this

/-- Finitely many two-sided directions admit a common bound. -/
theorem exists_uniform_isDirW {W : Set E} (hW : Convex ℝ W) {A : E} (hA : A ∈ W) {ι : Type*}
    (S : Finset ι) (v : ι → E) (hv : ∀ j ∈ S, IsDirW W A (v j)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ι → ℝ, (∀ j ∈ S, |t j| ≤ ε) → A + ∑ j ∈ S, t j • v j ∈ W := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun t _ => by simpa using hA⟩
  | insert k S hk ih =>
    obtain ⟨ε, hε, h⟩ := ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))
    obtain ⟨η, hη, hk'⟩ := hv k (Finset.mem_insert_self _ _)
    refine ⟨min ε η / 2, by positivity, fun t ht => ?_⟩
    have h1 : A + (2 * t k) • v k ∈ W := hk' _ (by
      have := ht k (Finset.mem_insert_self _ _)
      rw [abs_mul, abs_two]; linarith [min_le_right ε η])
    have h2 : A + ∑ j ∈ S, (2 * t j) • v j ∈ W := h (fun j => 2 * t j) (fun j hj => by
      have := ht j (Finset.mem_insert_of_mem hj)
      rw [abs_mul, abs_two]; linarith [min_le_left ε η])
    have := hW h1 h2 (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    convert this using 1
    rw [Finset.sum_insert hk]
    simp only [mul_smul, ← Finset.smul_sum]
    module

/-! ### Remark -/

/-- **Remark**, the printed « si », for any vector topology on `E`. -/
theorem fw_of_interieur [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {W : Set E} (hW : Convex ℝ W) {n : ℕ} (A : Fin n → E)
    (h : ∀ i, W ∈ 𝓝[(affineSpan ℝ (range A) : Set E)] (A i)) :
    ∀ i j, FW W (A i) (A j) := by
  have key : ∀ i j, AlphaW W (A i) (A j) := by
    intro i j
    set L := affineSpan ℝ (range A)
    have hLi : A i ∈ L := subset_affineSpan ℝ _ (mem_range_self i)
    have hLj : A j ∈ L := subset_affineSpan ℝ _ (mem_range_self j)
    have hAiW : A i ∈ W := mem_of_mem_nhdsWithin hLi (h i)
    have hAjW : A j ∈ W := mem_of_mem_nhdsWithin hLj (h j)
    let f : ℝ → E := fun t => A i + t • (A i - A j)
    have hf : Tendsto f (𝓝 0) (𝓝[(L : Set E)] (A i)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun t => ?_⟩
      · have hc : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
        simpa [f] using hc.tendsto 0
      · have := AffineSubspace.smul_vsub_vadd_mem L t hLi hLj hLi
        simpa [f, vsub_eq_sub, vadd_eq_add, add_comm] using this
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ W ∧ t ∈ Ioi 0 :=
      ((hf.eventually (h i)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨t, ht, htpos⟩ := hev.exists
    exact (alphaW_iff_extend hW).2 ⟨hAiW, hAjW, t, htpos, ht⟩
  exact fun i j => ⟨key i j, key j i⟩

/-- **Remark**, the converse, for any Hausdorff vector topology on `E`. -/
theorem interieur_of_fw [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] {W : Set E} (hW : Convex ℝ W) {n : ℕ} (A : Fin n → E)
    (h : ∀ i j, FW W (A i) (A j)) :
    ∀ i, W ∈ 𝓝[(affineSpan ℝ (range A) : Set E)] (A i) := by
  intro i
  classical
  have hAi : A i ∈ W := (h i i).1.mem_left
  set L := affineSpan ℝ (range A) with hL
  set V := vectorSpan ℝ (range A) with hVdef
  set w : Fin n → E := fun j => A j - A i with hw
  obtain ⟨ε, hε, hU⟩ := exists_uniform_isDirW hW hAi Finset.univ w
    (fun j _ => isDirW_sub_of_alphaW hW (h i j).1)
  have hV : V = Submodule.span ℝ (range w) := by
    rw [hVdef, vectorSpan_eq_span_vsub_set_right ℝ (mem_range_self i), ← Set.range_comp]
    rfl
  let ψ : (Fin n → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ w
  have hψV : ∀ t, ψ t ∈ V := by
    intro t
    rw [hV, ← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ t
  let ψV : (Fin n → ℝ) →ₗ[ℝ] V := ψ.codRestrict V hψV
  have hsurj : Function.Surjective ψV := by
    rintro ⟨v, hv⟩
    rw [hV, ← Fintype.range_linearCombination] at hv
    obtain ⟨t, rfl⟩ := hv
    exact ⟨t, rfl⟩
  have hopen : IsOpen (ψV '' Metric.ball 0 ε) :=
    LinearMap.isOpenMap_of_finiteDimensional ψV hsurj _ Metric.isOpen_ball
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.1 hopen
  refine mem_nhdsWithin.2 ⟨(fun x => x - A i) ⁻¹' O,
    hO.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · have h0 : (0 : V) ∈ ψV '' Metric.ball 0 ε := ⟨0, Metric.mem_ball_self hε, map_zero _⟩
    rw [← hpre] at h0
    simpa using h0
  · rintro x ⟨hxO, hxL⟩
    have hxV : x - A i ∈ V := by
      have := AffineSubspace.vsub_mem_direction hxL
        (subset_affineSpan ℝ _ (mem_range_self i) : A i ∈ L)
      rwa [direction_affineSpan] at this
    have hmem : (⟨x - A i, hxV⟩ : V) ∈ ψV '' Metric.ball 0 ε := by
      rw [← hpre]; exact hxO
    obtain ⟨t, ht, hte⟩ := hmem
    have hte' : ψ t = x - A i := congrArg Subtype.val hte
    have hx : x = A i + ∑ j, t j • w j := by
      rw [← Fintype.linearCombination_apply]
      change x = A i + ψ t
      rw [hte']; abel
    rw [hx]
    refine hU t (fun j _ => ?_)
    have := norm_le_pi_norm t j
    rw [mem_ball_zero_iff] at ht
    rw [← Real.norm_eq_abs]; linarith

/-- The Remark as an equivalence (its « si » and the converse), for every Hausdorff topological
vector space structure on `E`. -/
theorem fw_iff_interieur [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] {W : Set E} (hW : Convex ℝ W) {n : ℕ} (A : Fin n → E) :
    (∀ i j, FW W (A i) (A j)) ↔ ∀ i, W ∈ 𝓝[(affineSpan ℝ (range A) : Set E)] (A i) :=
  ⟨interieur_of_fw hW A, fw_of_interieur hW A⟩

/-- **The Remark, topology-free** (`E` a bare real vector space): `n` points of `W` lie in one
facette iff each `A i` is interior to `L ∩ W` for the topology of `L = affineSpan (range A)`,
that is, iff `{v ∈ direction L | A i + v ∈ W}` is a neighbourhood of `0` for the canonical
topology (`moduleTopology`) of the finite-dimensional direction of `L`. -/
theorem fw_iff_interieur_moduleTopology {W : Set E} (hW : Convex ℝ W) {n : ℕ}
    (A : Fin n → E) :
    (∀ i j, FW W (A i) (A j)) ↔ ∀ i,
      {v : vectorSpan ℝ (range A) | A i + (v : E) ∈ W} ∈
        @nhds (vectorSpan ℝ (range A)) (moduleTopology ℝ _) 0 := by
  set V := vectorSpan ℝ (range A) with hVdef
  letI : TopologicalSpace V := moduleTopology ℝ V
  haveI : IsModuleTopology ℝ V := ⟨rfl⟩
  constructor
  · intro h i
    classical
    have hAi : A i ∈ W := (h i i).1.mem_left
    set w : Fin n → E := fun j => A j - A i with hw
    obtain ⟨ε, hε, hU⟩ := exists_uniform_isDirW hW hAi Finset.univ w
      (fun j _ => isDirW_sub_of_alphaW hW (h i j).1)
    have hV : V = Submodule.span ℝ (range w) := by
      rw [hVdef, vectorSpan_eq_span_vsub_set_right ℝ (mem_range_self i), ← Set.range_comp]
      rfl
    let ψ : (Fin n → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ w
    have hψV : ∀ t, ψ t ∈ V := by
      intro t
      rw [hV, ← Fintype.range_linearCombination]
      exact LinearMap.mem_range_self _ t
    let ψV : (Fin n → ℝ) →ₗ[ℝ] V := ψ.codRestrict V hψV
    have hsurj : Function.Surjective ψV := by
      rintro ⟨v, hv⟩
      rw [hV, ← Fintype.range_linearCombination] at hv
      obtain ⟨t, rfl⟩ := hv
      exact ⟨t, rfl⟩
    have hopen : IsOpen (ψV '' Metric.ball 0 ε) :=
      IsModuleTopology.isOpenMap_of_surjective hsurj _ Metric.isOpen_ball
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨0, Metric.mem_ball_self hε, map_zero _⟩) ?_
    rintro _ ⟨t, ht, rfl⟩
    show A i + ψ t ∈ W
    refine hU t (fun j _ => ?_)
    have := norm_le_pi_norm t j
    rw [mem_ball_zero_iff] at ht
    rw [← Real.norm_eq_abs]; linarith
  · intro h
    have key : ∀ i j, AlphaW W (A i) (A j) := by
      intro i j
      have hv : A i - A j ∈ V := by
        have := vsub_mem_vectorSpan ℝ (mem_range_self (f := A) i) (mem_range_self (f := A) j)
        simpa [vsub_eq_sub] using this
      have hAiW : A i ∈ W := by simpa using mem_of_mem_nhds (h i)
      have hAjW : A j ∈ W := by simpa using mem_of_mem_nhds (h j)
      let f : ℝ → V := fun t => t • ⟨A i - A j, hv⟩
      have hf : Tendsto f (𝓝 0) (𝓝 0) := by
        have hc : Continuous f := continuous_id.smul continuous_const
        have := hc.tendsto 0
        rwa [show f 0 = 0 from zero_smul ℝ _] at this
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ {v : V | A i + (v : E) ∈ W} ∧ t ∈ Ioi 0 :=
        ((hf.eventually (h i)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
      obtain ⟨t, ht, htpos⟩ := hev.exists
      exact (alphaW_iff_extend hW).2 ⟨hAiW, hAjW, t, htpos, ht⟩
    exact fun i j => ⟨key i j, key j i⟩

/-- « appartiennent à une même facette » is the pairwise relation `F_W`, for `n ≥ 1` points. -/
theorem pairwise_fw_iff_exists_facette {W : Set E} (hW : Convex ℝ W) {n : ℕ} [NeZero n]
    (A : Fin n → E) : (∀ i j, FW W (A i) (A j)) ↔ ∃ F, IsFacette W F ∧ ∀ i, A i ∈ F := by
  constructor
  · intro h
    exact ⟨facetteOf W (A 0), isFacette_facetteOf (h 0 0).1.mem_left, fun i => h 0 i⟩
  · rintro ⟨F, hF, hA⟩ i j
    have := hA j
    rw [hF.eq_facetteOf hW (hA i)] at this
    exact this

/-! ### Props. 2, 3, 4 and the corollary -/

/-- **Prop. 2.** For `A` in a facette `F` of support `L` and `B ∈ W`: `A α B ↔ B ∈ L`. -/
theorem alphaW_iff_mem_support {W : Set E} (hW : Convex ℝ W) {F : Set E} (hF : IsFacette W F)
    {A B : E} (hA : A ∈ F) (hB : B ∈ W) :
    AlphaW W A B ↔ B ∈ affineSpan ℝ F := by
  have hAW : A ∈ W := hF.subset hA
  constructor
  · intro h
    obtain ⟨-, -, ε, hε, hP⟩ := (alphaW_iff_extend hW).1 h
    set C : E := A + (1 / 2 : ℝ) • (ε • (A - B)) with hCdef
    have hCW : C ∈ W := hW.add_smul_mem hAW (by simpa using hP) ⟨by norm_num, by norm_num⟩
    have hCA : AlphaW W C A := by
      refine (alphaW_iff_extend hW).2 ⟨hCW, hAW, 1, one_pos, ?_⟩
      convert hP using 1
      rw [hCdef]; module
    have hAC : AlphaW W A C := by
      refine (alphaW_iff_extend hW).2 ⟨hAW, hCW, 2 / ε, by positivity, ?_⟩
      convert hB using 1
      rw [hCdef]
      have : (2 / ε) * ((1 / 2) * ε) = 1 := by field_simp
      simp only [smul_smul, sub_add_cancel_left]
      rw [smul_neg, smul_smul, this, one_smul]; abel
    have hCF : C ∈ F := by
      rw [hF.eq_facetteOf hW hA]; exact ⟨hAC, hCA⟩
    have key : (-(2 / ε)) • (C -ᵥ A) +ᵥ A = B := by
      rw [vsub_eq_sub, vadd_eq_add, hCdef, add_sub_cancel_left, smul_smul, smul_smul]
      have : -(2 / ε) * (1 / 2) * ε = -1 := by field_simp
      rw [this]; module
    rw [← key]
    exact AffineSubspace.smul_vsub_vadd_mem _ _ (subset_affineSpan ℝ F hCF)
      (subset_affineSpan ℝ F hA) (subset_affineSpan ℝ F hA)
  · intro hBL
    have hle : vectorSpan ℝ F ≤ dirW hW hAW := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      have hx' : x - A ∈ dirW hW hAW := isDirW_sub_of_alphaW hW
        (by rw [hF.eq_facetteOf hW hA] at hx; exact hx.1)
      have hy' : y - A ∈ dirW hW hAW := isDirW_sub_of_alphaW hW
        (by rw [hF.eq_facetteOf hW hA] at hy; exact hy.1)
      have := sub_mem hx' hy'
      simpa [vsub_eq_sub] using this
    have hBA : B - A ∈ vectorSpan ℝ F := by
      have := AffineSubspace.vsub_mem_direction hBL (subset_affineSpan ℝ F hA)
      rwa [direction_affineSpan] at this
    exact alphaW_of_isDirW hW hB (hle hBA)

/-- **Prop. 3**, first part: `F α F′ ↔ L′ ⊆ L`. -/
theorem facetteLE_iff_support_le {W : Set E} (hW : Convex ℝ W) {F F' : Set E}
    (hF : IsFacette W F) (hF' : IsFacette W F') :
    FacetteLE W F F' ↔ affineSpan ℝ F' ≤ affineSpan ℝ F := by
  obtain ⟨A, hA⟩ := hF.nonempty
  constructor
  · intro h
    rw [affineSpan_le]
    intro B' hB'
    exact (alphaW_iff_mem_support hW hF hA (hF'.subset hB')).1
      ((facetteLE_iff_forall hW hF hF').1 h A hA B' hB')
  · intro h
    obtain ⟨A', hA'⟩ := hF'.nonempty
    exact ⟨A, hA, A', hA', (alphaW_iff_mem_support hW hF hA (hF'.subset hA')).2
      (h (subset_affineSpan ℝ F' hA'))⟩

/-- **Prop. 3**, second part: `L = L′ ↔ F = F′`. -/
theorem support_eq_iff {W : Set E} (hW : Convex ℝ W) {F F' : Set E}
    (hF : IsFacette W F) (hF' : IsFacette W F') :
    affineSpan ℝ F = affineSpan ℝ F' ↔ F = F' := by
  constructor
  · intro h
    exact FacetteLE.antisymm hW hF hF' ((facetteLE_iff_support_le hW hF hF').2 h.ge)
      ((facetteLE_iff_support_le hW hF' hF).2 h.le)
  · rintro rfl; rfl

/-- The point of Prop. 4's proof: the midpoint `B` of `A A'` satisfies `B α A`. -/
theorem alphaW_midpoint {W : Set E} (hW : Convex ℝ W) {A A' : E} (hA : A ∈ W) (hA' : A' ∈ W) :
    AlphaW W ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • A') A := by
  have hM : (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • A' ∈ W := hW hA hA' (by norm_num) (by norm_num)
    (by norm_num)
  refine (alphaW_iff_extend hW).2 ⟨hM, hA, 1, one_pos, ?_⟩
  convert hA' using 1
  module

/-- **Prop. 4.** The facettes, ordered by α, are directed downwards (« filtrant à gauche »). -/
theorem facettes_filtrant {W : Set E} (hW : Convex ℝ W) :
    DirectedOn (fun F G => FacetteLE W G F) {F | IsFacette W F} := by
  intro F hF F' hF'
  obtain ⟨A, hA⟩ := hF.nonempty
  obtain ⟨A', hA'⟩ := hF'.nonempty
  have hAW := hF.subset hA
  have hA'W := hF'.subset hA'
  have hM : (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • A' ∈ W := hW hAW hA'W (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨_, isFacette_facetteOf hM, ⟨_, mem_facetteOf_self hM, A, hA, alphaW_midpoint hW hAW hA'W⟩,
    ⟨_, mem_facetteOf_self hM, A', hA', ?_⟩⟩
  have := alphaW_midpoint hW hA'W hAW
  rwa [add_comm] at this

/-- Prop. 4 on the ordered set of facettes (Déf. 2's order): it is directed downwards. -/
theorem facettes_isDirected {W : Set E} (hW : Convex ℝ W) :
    letI := facettePartialOrder hW; IsDirected (Facette W) (· ≥ ·) := by
  letI := facettePartialOrder hW
  refine ⟨fun F G => ?_⟩
  obtain ⟨H, hH, h1, h2⟩ := facettes_filtrant hW F.1 F.2 G.1 G.2
  exact ⟨⟨H, hH⟩, h1, h2⟩

/-- The linear varieties (affine subspaces) that are supports of facettes of `W`. -/
def supportsFacettes (W : Set E) : Set (AffineSubspace ℝ E) :=
  {L | ∃ F, IsFacette W F ∧ L = affineSpan ℝ F}

/-- **Corollaire.** The supports of facettes are directed upwards for inclusion. -/
theorem supports_filtrant {W : Set E} (hW : Convex ℝ W) :
    DirectedOn (· ≤ ·) (supportsFacettes W) := by
  rintro _ ⟨F, hF, rfl⟩ _ ⟨F', hF', rfl⟩
  obtain ⟨F'', hF'', h1, h2⟩ := facettes_filtrant hW F hF F' hF'
  exact ⟨_, ⟨F'', hF'', rfl⟩, (facetteLE_iff_support_le hW hF'' hF).1 h1,
    (facetteLE_iff_support_le hW hF'' hF').1 h2⟩

/-! ### The instance: the segment [0, 1] -/

/-- α on `[0, 1]`: `a α b` iff `a = b` or `a` is an interior point. -/
theorem alphaW_Icc_iff {a b : ℝ} :
    AlphaW (Icc 0 1) a b ↔ a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ (a = b ∨ a ∈ Ioo (0 : ℝ) 1) := by
  rw [alphaW_iff_extend (convex_Icc 0 1)]
  constructor
  · rintro ⟨ha, hb, ε, hε, hP⟩
    refine ⟨ha, hb, ?_⟩
    by_contra hne
    obtain ⟨h1, h2⟩ := not_or.1 hne
    simp only [mem_Ioo, mem_Icc, not_and_or, not_lt, smul_eq_mul] at h2 ha hb hP
    rcases h2 with h2 | h2
    · have : b ≤ 0 := by nlinarith
      exact h1 (by linarith)
    · have : 1 ≤ b := by nlinarith
      exact h1 (by linarith)
  · rintro ⟨ha, hb, h | h⟩
    · subst h; exact ⟨ha, ha, 1, one_pos, by simpa using ha⟩
    · refine ⟨ha, hb, min a (1 - a) / 2, by have := h.1; have := h.2; positivity, ?_⟩
      simp only [mem_Ioo, mem_Icc, smul_eq_mul] at ha hb h ⊢
      have e1 : min a (1 - a) / 2 ≤ a / 2 := by linarith [min_le_left a (1 - a)]
      have e2 : min a (1 - a) / 2 ≤ (1 - a) / 2 := by linarith [min_le_right a (1 - a)]
      have e0 : 0 < min a (1 - a) / 2 := by have := lt_min h.1 (by linarith : 0 < 1 - a); linarith
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left (by linarith : -1 ≤ a - b) e0.le]
      · nlinarith [mul_le_mul_of_nonneg_left (by linarith : a - b ≤ 1) e0.le]

theorem facetteOf_Icc_zero : facetteOf (Icc (0 : ℝ) 1) 0 = {0} := by
  ext b
  simp only [facetteOf, FW, mem_setOf_eq, alphaW_Icc_iff, mem_singleton_iff, mem_Icc, mem_Ioo]
  constructor
  · rintro ⟨⟨-, -, h | h⟩, -⟩
    · exact h.symm
    · exact absurd h.1 (lt_irrefl 0)
  · rintro rfl; norm_num

theorem facetteOf_Icc_one : facetteOf (Icc (0 : ℝ) 1) 1 = {1} := by
  ext b
  simp only [facetteOf, FW, mem_setOf_eq, alphaW_Icc_iff, mem_singleton_iff, mem_Icc, mem_Ioo]
  constructor
  · rintro ⟨⟨-, -, h | h⟩, -⟩
    · exact h.symm
    · exact absurd h.2 (lt_irrefl 1)
  · rintro rfl; norm_num

theorem facetteOf_Icc_of_mem_Ioo {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    facetteOf (Icc (0 : ℝ) 1) a = Ioo 0 1 := by
  ext b
  have haI : a ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ha
  simp only [facetteOf, FW, mem_setOf_eq, alphaW_Icc_iff]
  constructor
  · rintro ⟨-, -, -, h | h⟩
    · rw [h]; exact ha
    · exact h
  · intro hb
    exact ⟨⟨haI, Ioo_subset_Icc_self hb, Or.inr ha⟩, ⟨Ioo_subset_Icc_self hb, haI, Or.inr hb⟩⟩

/-- **The instance.** The closed segment `[0, 1] ⊂ ℝ` has exactly three facettes. -/
theorem isFacette_Icc_iff {F : Set ℝ} :
    IsFacette (Icc 0 1) F ↔ F = {0} ∨ F = {1} ∨ F = Ioo 0 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases eq_or_lt_of_le ha.1 with h0 | h0
    · subst h0; exact Or.inl facetteOf_Icc_zero
    rcases eq_or_lt_of_le ha.2 with h1 | h1
    · subst h1; exact Or.inr (Or.inl facetteOf_Icc_one)
    exact Or.inr (Or.inr (facetteOf_Icc_of_mem_Ioo ⟨h0, h1⟩))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, facetteOf_Icc_zero.symm⟩
    · exact ⟨1, by norm_num, facetteOf_Icc_one.symm⟩
    · exact ⟨1 / 2, by norm_num, (facetteOf_Icc_of_mem_Ioo (by norm_num)).symm⟩

/-- **The instance**, the order: `]0, 1[ α {0}`, and not conversely. -/
theorem segment01_order :
    FacetteLE (Icc (0 : ℝ) 1) (Ioo 0 1) {0} ∧ ¬ FacetteLE (Icc (0 : ℝ) 1) {0} (Ioo 0 1) := by
  constructor
  · exact ⟨1 / 2, by norm_num, 0, rfl, alphaW_Icc_iff.2 ⟨by norm_num, by norm_num,
      Or.inr (by norm_num)⟩⟩
  · rintro ⟨a, ha, b, hb, h⟩
    rw [mem_singleton_iff] at ha
    subst ha
    obtain ⟨-, -, h | h⟩ := alphaW_Icc_iff.1 h
    · rw [← h] at hb; exact lt_irrefl 0 hb.1
    · exact absurd h.1 (lt_irrefl 0)

/-- The supports of the three facettes of `[0, 1]`: `{0}`, `{1}` and the line `ℝ`. -/
theorem affineSpan_Ioo01 : affineSpan ℝ (Ioo (0 : ℝ) 1) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : AffineMap.lineMap (1 / 4 : ℝ) (3 / 4) (2 * (x - 1 / 4)) = x := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]; ring
  have hsub : ({1 / 4, 3 / 4} : Set ℝ) ⊆ Ioo 0 1 := by
    rintro y (rfl | rfl) <;> norm_num
  rw [← hx]
  exact affineSpan_mono ℝ hsub (AffineMap.lineMap_mem_affineSpan_pair _ _ _)

end Benzecri
