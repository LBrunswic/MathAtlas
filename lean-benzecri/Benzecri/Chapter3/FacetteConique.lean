import Benzecri.Chapter3.BooleProjectif
import Benzecri.Chapter3.FacetteDuale
import Benzecri.Chapter3.PointsExtremaux
import Benzecri.Chapter2.Hilbert
import Benzecri.Chapter2.Poches

/-!
# Chapter 3 § 4 — conical facettes (Déf. 5), the contingent at a conical facette (Prop. 10), the base of a conical facette (Déf. 6)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 4, journal p. 276; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR, OQ-160),
checked against the page image (PDF p. 49). Target T-bz-c3-facette-conique. The contingent is
`Benzecri.Sphere.contingent` (Chapter3/ConeAppui), facettes `facetteK`/`IsFacetteK`, supports
`supportK`, noyaux `noyau` (Chapter3/FacettesSphere), `S(E)/l` is `quotient`/`quotientImage`
(Projective/Subvariety).

* **`bzdef:c3s4d5_facette_conique`** — `benzecri1960_ch3.tex:1117` (Déf. 5, l.1117–1120) —
  `Benzecri.Sphere.IsFacetteConique` (a facette `F` of `W` and a point `a ∈ F` with
  `noyau (contingent W a) = supportK F`). « en un point » is not a reading: the supporting cone,
  hence the contingent, is the same at every point of a facette (`coneAppui_eq_of_mem_facetteK`,
  from § 4 Prop. 1 (1) ⇔ (4), valid under both half-line conventions of OQ-164;
  `IsFacetteK.contingent_eq`), so « at one point » and « at every point » agree
  (`isFacetteConique_iff_forall`). Instances: the vertex of the closed triangle is conical
  (`FacetteConiqueInstance.isFacetteConique_vertex0`); the boundary point of a closed round cap
  is a facette that is not (`FacetteConiqueInstance.cap_facette_example`).
* `bzprop:c3s4p10_contingent_conique` — `benzecri1960_ch3.tex:1122` (Prop. 10, l.1122–1125;
  proof l.1127–1130) — NOT marked: imprecise. `Benzecri.prop10_contingent_conique` proves it for
  a conical facette of support `L ≠ S(n)`: the contingent is a convex part containing `L`,
  identified (`convexQuotientEquiv`) with its image in `S(n)/L`, and under any linear
  identification `E/L ≃ ℝᵐ⁺¹` (one exists, `m + 1 + dim L = n + 1`) that image is a convex body of
  `S(m)`. The printed statement fails at the interior facette, which is always conical with
  support `S(n)`, and `S(n)/S(n)` is empty (`Benzecri.interior_facette_conique`): no convex body
  lives there. The core: `Benzecri.isCorpsConvexeS_image_quotient`.
* `bzdef:c3s4d6_base_facette_conique` — `benzecri1960_ch3.tex:1132` (Déf. 6, l.1132–1140) — NOT
  marked: a reading. `Benzecri.Sphere.IsBaseFacetteConique` with « `S(n)` somme de `L` et de
  `L′` » read through the printed bracket « [L ∩ L′ = ∅, S(n) enveloppe convexe de L et L′] »
  (`EstSommeLineaire`, equivalent to `IsCompl L L′`: `estSommeLineaire_iff`). Read literally
  « au sens de la définition 6 [5] du paragraphe 2 » (`EstSomme2`, the union of the open segments
  joining `l` to `l′`), `S(n)` is the sum of `l`, `l′` only when one of them is empty
  (`estSomme2_univ_linearSubvariety_iff`). The base does not depend on the point of `F`
  (`IsBaseFacetteConique.eq`). Instance: the base in `L′ = span(e₁, e₂)` of the vertex of the
  closed triangle is the opposite closed edge (`isBaseFacetteConique_vertex0`).

> **Définition 5.** Une facette $F$ d'un convexe fermé $W$ est dite *conique* si le noyau du
> contingent en un point de cette facette n'est autre que le support de la facette.
>
> **Proposition 10.** Soient $W$ un corps convexe, $F$ une facette conique de $W$, $L$ son
> support; le contingent à $W$ en un point de $F$ s'identifie à un corps convexe de $S(n)/L$.
>
> Parce que $W$ est d'intérieur non vide, il en est de même du contingent considéré comme partie
> de $S(n)/L$; que le noyau de cette partie soit vide résulte de ce que $F$ est conique.
>
> **Définition 6.** Soit $F$ une facette conique de support $L$ d'un corps convexe de $W$; soit
> $L'$ une sous-variété linéaire de $S(n)$ telle que $S(n)$ soit somme de $L$ et de $L'$ au sens
> de la définition 6 du paragraphe 2 [$L\cap L'=E$, $S(n)$ enveloppe convexe de $L$ et $L'$].
> L'intersection de $L'$ avec le contingent à $W$ en un point de $F$ est appelée base dans $L'$ de
> la facette conique $F$.

## The proofs formalized

Prop. 10, following the printed proof. Write `C` for the contingent and `K = F(C) ∪ {O}` its
closed convex cone. Conicity gives `K ∩ −K = L` (`noyau_eq`), and `L ⊆ K` makes `K` stable under
`+ L` (`add_mem_kPrime_of_subset`). For `φ : E → E/L ≃ ℝᵐ⁺¹`: `φ(K) − O` is convex, because a
convex combination of `φ u, φ u′ ≠ O` vanishing would put `−u` in `K + L = K`, so `u ∈ L`
(« le noyau de cette partie est vide »); `φ(K)` is closed since `K = φ⁻¹(φ(K))` and `φ` is open,
so the image is compact; and the interior of `F(W) ⊆ F(C)` maps onto an open set of `ℝᵐ⁺¹`,
which is not `{O}` (« d'intérieur non vide »). Interior facette: at `a ∈ int W`,
`A ± t v ∈ F(W)` for small `t`, so `W_a = S(n)` and `A + t v` lies in the facette of `a`.
Déf. 6: `l ∩ l′ = ∅` iff `L ⊓ L′ = 0`, and the convex hull of `l ∪ l′` is `S(E)` iff
`L ⊔ L′ = E` (`s(L ⊔ L′ − O)` is a convex part containing both; conversely a convex part
containing both contains `s(y + z)`); the open segments joining `l` to `l′` miss `l`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 5: « Une facette $F$ » | ✓ carried: `IsFacetteK W F` |
| Déf. 5: « d'un convexe fermé $W$ » | generalised: `IsFacetteConique W F` is defined for every `W`; `IsConvexPart W` is used where « un point » is shown indifferent |
| Déf. 5: « en un point de cette facette » | ✓ carried: `∃ a ∈ F`; equivalent to `∀ a ∈ F` (`isFacetteConique_iff_forall`) |
| Déf. 5: « le noyau du contingent … n'est autre que le support » | ✓ carried: equality of parts of `S(E)`, `noyau (contingent W a) = supportK F` |
| Prop. 10: « $W$ un corps convexe » | ✓ carried: `IsCorpsConvexeS n W` |
| Prop. 10: « $F$ une facette conique de $W$, $L$ son support » | ✓ carried: `IsFacetteConique W F`, `L = span F(F)` (`supportK F = s(L − O)`) |
| Prop. 10: (unstated) `L ≠ S(n)` | **added** (finding): `supportK F ≠ univ`; it excludes the interior facette (whose support is `S(n)`, `interior_facette_conique`), where the statement fails |
| Prop. 10: « s'identifie à un corps convexe de $S(n)/L$ » | reading (question): `C ⊇ l` is identified with `quotientImage L C` (`convexQuotientEquiv`), and `S(n)/L = S(E/L)` with `S(m)` by any linear `E/L ≃ ℝᵐ⁺¹` (`mapEquiv`); proved for every such identification |
| Déf. 6: « d'un corps convexe de $W$ » | [sic] read « d'un corps convexe $W$ » (transcription comment): `W` arbitrary in the definition |
| Déf. 6: « $S(n)$ somme de $L$ et de $L'$ au sens de la définition 6 du paragraphe 2 » | reading (question): the printed bracket, `EstSommeLineaire L L′` (⇔ `IsCompl L L′`); the literal § 2 sense is degenerate (`estSomme2_univ_linearSubvariety_iff`) |
| Déf. 6: « $L\cap L'=E$ » | [sic] read `L ∩ L′ = ∅` (transcription comment) |
| Déf. 6: « en un point de $F$ » | ✓ carried: `∃ a ∈ F`; independent of the point (`IsBaseFacetteConique.eq`) |

## SCOPE (disclosed)

* Prop. 10 is not marked: it is imprecise at the interior facette (support `S(n)`, empty
  quotient sphere), the degenerate case its proof (« il en est de même du contingent ») silently
  excludes. Every conical facette of support `≠ S(n)` is covered, with no further hypothesis
  (whether the interior facette is the only facette of support `S(n)` is not formalized here).
* Déf. 6 is not marked: its cross-reference (« au sens de la définition 6 du paragraphe 2 »; the
  sum is § 2 Déf. 5) read literally makes `S(n)` a sum of two linear subvarieties only in the
  degenerate splittings; the bracket's reading is taken.
* Instances (`Benzecri.FacetteConiqueInstance`), on `S(2)`: the closed triangle `T = simplexS 2`
  (Chapter3/FacetteDuale) is a convex body, its vertex `{s(e₀)}` is a conical facette with
  contingent `{x₁ ≥ 0, x₂ ≥ 0}` (`contingent_vertex0`) and noyau `{±s(e₀)}`
  (`noyau_contingent_vertex0`), it satisfies Prop. 10's hypotheses (`prop10_instance`), and
  its base in `L′ = {x₀ = 0}` is the closed edge `T ∩ L′`. The closed round cap
  `{x₀ ≥ 0, x₂ ≥ 0, x₁² ≤ x₀ x₂}` is a convex body (`isCorpsConvexeS_cap`) whose boundary point
  `s(e₀)` has a facette that is not conical: `s(e₁)` lies in the noyau of the contingent
  (`mk_eB_mem_noyau`) and not in the support of the facette (`facetteK_capPt_subset`).
* General facts proved here (candidates to move upstream): `isClosed_kPrime_of_isClosed`,
  `add_mem_kPrime_of_subset`, `mapEquiv_image_ofCone`, `isClosed_ofCone`,
  `coneAppui_subset_of_alphaK`, `linearSubvariety_eq_univ_iff`, `enveloppeConvexeS`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The contingent is the same at every point of a facette -/

/-- § 4 Prop. 1, (1) ⇒ (4), in every case: `a α(W) b` gives `W_b ⊆ W_a`. -/
theorem coneAppui_subset_of_alphaK {W : Set (Sphere E)} (hW : IsConvexPart W) {a b : Sphere E}
    (h : AlphaK W a b) : coneAppui W b ⊆ coneAppui W a := by
  have ha := h.mem_left
  have hb := h.mem_right
  obtain ⟨h1, h2⟩ := prop1_coneAppui hW ha hb
  by_cases hab : b = a ∨ b = -a
  · exact ((h2 hab).out 0 2).1 h
  · push Not at hab
    exact ((h1 hab.1 hab.2).out 0 3).1 h

/-- **The supporting cone is the same at every point of a facette** (§ 4 Prop. 1, (1) ⇔ (4)). -/
theorem coneAppui_eq_of_mem_facetteK {W : Set (Sphere E)} (hW : IsConvexPart W) {a b : Sphere E}
    (hb : b ∈ facetteK W a) : coneAppui W b = coneAppui W a :=
  Subset.antisymm (coneAppui_subset_of_alphaK hW hb.1) (coneAppui_subset_of_alphaK hW hb.2)

section Topo

variable [TopologicalSpace E]

/-- **The contingent is the same at every point of a facette.** -/
theorem IsFacetteK.contingent_eq {W F : Set (Sphere E)} (hW : IsConvexPart W)
    (hF : IsFacetteK W F) {a b : Sphere E} (ha : a ∈ F) (hb : b ∈ F) :
    contingent W a = contingent W b := by
  obtain ⟨a₀, -, rfl⟩ := hF
  unfold contingent
  rw [coneAppui_eq_of_mem_facetteK hW ha, coneAppui_eq_of_mem_facetteK hW hb]

/-- **Déf. 5**: a facette `F` of `W` is *conical* if the noyau of the contingent at a point of `F`
is the support of `F`. -/
def IsFacetteConique (W F : Set (Sphere E)) : Prop :=
  IsFacetteK W F ∧ ∃ a ∈ F, noyau (contingent W a) = supportK F

/-- **Déf. 5, « en un point »**: at one point of the facette iff at every point. -/
theorem isFacetteConique_iff_forall {W F : Set (Sphere E)} (hW : IsConvexPart W) :
    IsFacetteConique W F ↔ IsFacetteK W F ∧ ∀ a ∈ F, noyau (contingent W a) = supportK F := by
  constructor
  · rintro ⟨hF, a, ha, h⟩
    exact ⟨hF, fun b hb => by rw [hF.contingent_eq hW hb ha]; exact h⟩
  · rintro ⟨hF, h⟩
    obtain ⟨a, ha⟩ := hF.nonempty
    exact ⟨hF, a, ha, h a ha⟩

end Topo

/-! ### Déf. 6 — `S(n)` sum of `L` and `L′` -/

/-- The convex hull of a part of `S(E)`: the intersection of the convex parts containing it. -/
def enveloppeConvexeS (A : Set (Sphere E)) : Set (Sphere E) := ⋂₀ {k | IsConvexPart k ∧ A ⊆ k}

/-- « `S(E)` est somme de `L` et de `L′` », in the bracket's reading: `L ∩ L′ = ∅` and `S(E)` is
the convex hull of `L ∪ L′`. -/
def EstSommeLineaire (L L' : Submodule ℝ E) : Prop :=
  linearSubvariety L ∩ linearSubvariety L' = ∅ ∧
    enveloppeConvexeS (linearSubvariety L ∪ linearSubvariety L') = univ

/-- **Déf. 6's bracket**: `l ∩ l′ = ∅` and `S(E)` the convex hull of `l ∪ l′` iff
`E = L ⊕ L′`. -/
theorem estSommeLineaire_iff {L L' : Submodule ℝ E} : EstSommeLineaire L L' ↔ IsCompl L L' := by
  have hdisj : linearSubvariety L ∩ linearSubvariety L' = ∅ ↔ Disjoint L L' := by
    rw [Submodule.disjoint_def]
    constructor
    · intro h v hv hv'
      by_contra h0
      have : mk v h0 ∈ linearSubvariety L ∩ linearSubvariety L' :=
        ⟨(mk_mem_linearSubvariety h0).2 hv, (mk_mem_linearSubvariety h0).2 hv'⟩
      rw [h] at this
      exact this
    · intro h
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      induction x using ind with
      | h v hv =>
      exact hv (h v ((mk_mem_linearSubvariety hv).1 hx.1) ((mk_mem_linearSubvariety hv).1 hx.2))
  have hcod : enveloppeConvexeS (linearSubvariety L ∪ linearSubvariety L') = univ ↔
      Codisjoint L L' := by
    rw [codisjoint_iff]
    constructor
    · intro h
      rw [eq_top_iff]
      intro v _
      by_cases hv : v = 0
      · rw [hv]; exact Submodule.zero_mem _
      have hsub : enveloppeConvexeS (linearSubvariety L ∪ linearSubvariety L') ⊆
          linearSubvariety (L ⊔ L') :=
        sInter_subset_of_mem ⟨isConvexPart_linearSubvariety _, union_subset
          (ofCone_subset_ofCone (SetLike.coe_subset_coe.2 le_sup_left))
          (ofCone_subset_ofCone (SetLike.coe_subset_coe.2 le_sup_right))⟩
      rw [h] at hsub
      exact (mk_mem_linearSubvariety hv).1 (hsub (mem_univ (mk v hv)))
    · intro h
      refine eq_univ_of_univ_subset (subset_sInter ?_)
      rintro k ⟨hk, hLk⟩ x -
      induction x using ind with
      | h v hv =>
      have hv' : v ∈ L ⊔ L' := h ▸ Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv'
      have hmem : ∀ (M : Submodule ℝ E) (w : E), w ∈ M → linearSubvariety M ⊆ k →
          w ∈ kPrime k := by
        intro M w hw hM
        by_cases hw0 : w = 0
        · rw [hw0]; exact zero_mem_kPrime k
        · exact mem_kPrime_of_isRep (isRep_mk w hw0) (hM ((mk_mem_linearSubvariety hw0).2 hw))
      have := add_mem_kPrime hk (hmem L y hy (subset_union_left.trans hLk))
        (hmem L' z hz (subset_union_right.trans hLk))
      exact mem_of_isRep_of_mem_kPrime (isRep_mk _ hv) this
  rw [EstSommeLineaire, hdisj, hcod]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.disjoint, h.codisjoint⟩⟩

/-- In the sense of § 2, Déf. 5 (two summands), `S(E)` is the sum of two nonempty linear
subvarieties `l, l′` only if one of them is empty: the open segments joining `l` to `l′` miss `l`
(a point of `l` on such a segment would put a point in `l ∩ l′`). -/
theorem estSomme2_univ_linearSubvariety_degenerate {L L' : Submodule ℝ E}
    (h : EstSomme2 univ (linearSubvariety L) (linearSubvariety L')) : L = ⊥ ∨ L' = ⊥ := by
  by_contra hc
  push Not at hc
  obtain ⟨hL, hL'⟩ := hc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  obtain ⟨v', hv', hv'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL'
  revert h
  rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨-, -, hdisj, hj⟩)
  · have := (mk_mem_linearSubvariety hv'0).2 hv'
    rw [h] at this; exact this
  · have := (mk_mem_linearSubvariety hv0).2 hv
    rw [h] at this; exact this
  · have hF : v ∈ F (joint (linearSubvariety L) (linearSubvariety L')) := by
      rw [← hj]; exact ⟨hv0, mem_univ _⟩
    rw [F_joint, F_linearSubvariety, F_linearSubvariety] at hF
    obtain ⟨⟨x, ⟨hx, -⟩, y, ⟨hy, hy0⟩, hxy⟩, -⟩ := hF
    have hyL : y ∈ L := by
      have : y = v - x := by rw [← hxy]; simp
      rw [this]; exact L.sub_mem hv hx
    have : mk y hy0 ∈ supportK (linearSubvariety L) ∩ supportK (linearSubvariety L') :=
      ⟨subset_supportK _ ((mk_mem_linearSubvariety hy0).2 hyL),
        subset_supportK _ ((mk_mem_linearSubvariety hy0).2 hy)⟩
    rw [hdisj] at this
    exact this

theorem linearSubvariety_eq_univ_iff {L : Submodule ℝ E} : linearSubvariety L = univ ↔ L = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro v _
    by_cases hv : v = 0
    · rw [hv]; exact L.zero_mem
    · exact (mk_mem_linearSubvariety hv).1 (h ▸ mem_univ (mk v hv))
  · rintro rfl
    rw [eq_univ_iff_forall]
    intro x
    induction x using ind with
    | h v hv => exact (mk_mem_linearSubvariety hv).2 Submodule.mem_top

/-- **« `S(n)` somme de `L` et de `L′` au sens du paragraphe 2 », read literally** (§ 2, Déf. 5,
two summands, with its convention): it holds only in the degenerate cases `L = E, L′ = 0` and
`L = 0, L′ = E`. So Déf. 6 is read through its bracket (`EstSommeLineaire`). -/
theorem estSomme2_univ_linearSubvariety_iff {L L' : Submodule ℝ E} :
    EstSomme2 univ (linearSubvariety L) (linearSubvariety L') ↔
      (L = ⊤ ∧ L' = ⊥) ∨ (L = ⊥ ∧ L' = ⊤) := by
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hn1, hn2, h3⟩
    · exact Or.inl ⟨linearSubvariety_eq_univ_iff.1 h1, linearSubvariety_eq_empty_iff.1 h2⟩
    · exact Or.inr ⟨linearSubvariety_eq_empty_iff.1 h1, linearSubvariety_eq_univ_iff.1 h2⟩
    · exfalso
      rcases estSomme2_univ_linearSubvariety_degenerate (Or.inr (Or.inr ⟨hn1, hn2, h3⟩)) with
        h | h
      · rw [← linearSubvariety_eq_empty_iff] at h
        exact hn1.ne_empty h
      · rw [← linearSubvariety_eq_empty_iff] at h
        exact hn2.ne_empty h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨linearSubvariety_eq_univ_iff.2 rfl, linearSubvariety_eq_empty_iff.2 rfl⟩
    · exact Or.inr (Or.inl
        ⟨linearSubvariety_eq_empty_iff.2 rfl, linearSubvariety_eq_univ_iff.2 rfl⟩)

section Topo2

variable [TopologicalSpace E]

/-- **Déf. 6**: `B` is the base in `L′` of the conical facette `F` of `W`. -/
def IsBaseFacetteConique (W F : Set (Sphere E)) (L' : Submodule ℝ E) (B : Set (Sphere E)) :
    Prop :=
  IsFacetteConique W F ∧ EstSommeLineaire (Submodule.span ℝ (Sphere.F F)) L' ∧
    ∃ a ∈ F, B = linearSubvariety L' ∩ contingent W a

/-- **Déf. 6, « en un point de F »**: the base does not depend on the point. -/
theorem IsBaseFacetteConique.eq {W F : Set (Sphere E)} (hW : IsConvexPart W) {L' : Submodule ℝ E}
    {B : Set (Sphere E)} (h : IsBaseFacetteConique W F L' B) {b : Sphere E} (hb : b ∈ F) :
    B = linearSubvariety L' ∩ contingent W b := by
  obtain ⟨hFc, -, a, ha, rfl⟩ := h
  rw [hFc.1.contingent_eq hW ha hb]

end Topo2

end Sphere

/-! ### Prop. 10 -/

section Prop10

open Sphere

variable {n : ℕ}

/-- The cone `F(k) ∪ {O}` of a closed part of `S(E)` is closed. -/
theorem isClosed_kPrime_of_isClosed {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul ℝ E] {k : Set (Sphere E)} (hk : IsClosed k) :
    IsClosed (kPrime k) := by
  have h := F_closure k
  rw [hk.closure_eq] at h
  have e : kPrime k = {0} ∪ closure (F k) := by
    unfold kPrime
    conv_lhs => rw [h]
    ext v
    by_cases hv : v = 0 <;> simp [hv]
  rw [e]
  exact isClosed_singleton.union isClosed_closure

/-- The cone of a convex part containing `l = s(L − O)` is `L`-saturated. -/
theorem add_mem_kPrime_of_subset {E : Type*} [AddCommGroup E] [Module ℝ E] {L : Submodule ℝ E}
    {k : Set (Sphere E)} (hk : IsConvexPart k) (hl : linearSubvariety L ⊆ k) {v m : E}
    (hv : v ∈ kPrime k) (hm : m ∈ L) : v + m ∈ kPrime k := by
  by_cases hvm : v + m = 0
  · rw [hvm]; exact zero_mem_kPrime k
  rcases mem_insert_iff.1 hv with rfl | hvF
  · rw [zero_add] at hvm ⊢
    exact mem_kPrime_of_isRep (isRep_mk m hvm) (hl ((mk_mem_linearSubvariety hvm).2 hm))
  · exact mem_insert_of_mem _ (add_mem_F_of_isConvexPart hk hl hvF hm hvm)

/-- `mapEquiv e '' ofCone C = ofCone (e '' C)`. -/
theorem mapEquiv_image_ofCone {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E']
    [Module ℝ E'] (e : E ≃ₗ[ℝ] E') {C : Set E} (hC : IsPosCone C) :
    mapEquiv e '' ofCone C = ofCone (e '' C) := by
  ext x
  induction x using ind with
  | h w hw =>
  have hC' : IsPosCone (e '' C) := isPosCone_image e.toLinearMap hC
  rw [Equiv.image_eq_preimage_symm, mem_preimage, mapEquiv_symm, mapEquiv_mk,
    mk_mem_ofCone_iff hC, mk_mem_ofCone_iff hC']
  constructor
  · intro h; exact ⟨_, h, by simp⟩
  · rintro ⟨u, hu, rfl⟩; simpa using hu

/-- **The core of Prop. 10**: a closed convex part `C` of `S(n)` whose noyau is `s(L − O)`, with
`F(C)` of nonempty interior, projects, under any linear identification `E/L ≃ ℝᵐ⁺¹`, onto a
convex body of `S(m)`. -/
theorem isCorpsConvexeS_image_quotient {n m : ℕ} {C : Set (S n)} (hC : IsConvexPart C)
    (hCc : IsClosed C) {L : Submodule ℝ (Fin (n + 1) → ℝ)} (hnoy : noyau C = linearSubvariety L)
    (hint : (interior (Sphere.F C)).Nonempty)
    (e : ((Fin (n + 1) → ℝ) ⧸ L) ≃ₗ[ℝ] (Fin (m + 1) → ℝ)) :
    IsCorpsConvexeS m (mapEquiv e '' quotientImage L C) := by
  set K := kPrime C with hKdef
  have hLC : linearSubvariety L ⊆ C := hnoy ▸ noyau_subset
  have hKconv : Convex ℝ K := convex_kPrime hC
  have hKadd : ∀ v ∈ K, ∀ m ∈ L, v + m ∈ K := fun v hv m hm =>
    add_mem_kPrime_of_subset hC hLC hv hm
  have hKpt : ∀ v ∈ K, -v ∈ K → v ∈ L := by
    intro v hv hnv
    by_cases hv0 : v = 0
    · rw [hv0]; exact L.zero_mem
    have h1 : mk v hv0 ∈ C := mem_of_isRep_of_mem_kPrime (isRep_mk v hv0) hv
    have h2 : -mk v hv0 ∈ C := by
      rw [neg_mk]; exact mem_of_isRep_of_mem_kPrime (isRep_mk _ _) hnv
    have : mk v hv0 ∈ noyau C := by rw [noyau_eq hC]; exact ⟨h1, h2⟩
    rw [hnoy] at this
    exact (mk_mem_linearSubvariety hv0).1 this
  have hKc : IsClosed K := isClosed_kPrime_of_isClosed hCc
  set φ : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) := e.toLinearMap ∘ₗ L.mkQ with hφdef
  have hφ0 : ∀ v, φ v = 0 ↔ v ∈ L := by
    intro v
    simp [hφdef, Submodule.Quotient.mk_eq_zero]
  have hφs : Function.Surjective φ := e.surjective.comp L.mkQ_surjective
  have hX : mapEquiv e '' quotientImage L C = ofCone (φ '' F C) := by
    rw [quotientImage, mapEquiv_image_ofCone e (isPosCone_image _ (isPosCone_F C)), image_image]
    rfl
  have hDpos : IsPosCone (φ '' F C) := isPosCone_image φ (isPosCone_F C)
  have hFX : F (ofCone (φ '' F C)) = φ '' F C \ {0} := F_ofCone hDpos
  have hins : insert 0 (φ '' F C) = φ '' K := by rw [hKdef, kPrime, image_insert_eq, map_zero]
  rw [hX, isCorpsConvexeS_iff, hFX]
  refine ⟨?_, ?_, ?_⟩
  · -- convexity
    rintro _ ⟨⟨u, hu, rfl⟩, hu0⟩ _ ⟨⟨u', hu', rfl⟩, hu'0⟩ t s ht hs hts
    have huK : u ∈ K := mem_insert_of_mem _ hu
    have hu'K : u' ∈ K := mem_insert_of_mem _ hu'
    have hwK : t • u + s • u' ∈ K := hKconv huK hu'K ht hs hts
    have hφw : φ (t • u + s • u') = t • φ u + s • φ u' := by simp
    have hne : t • φ u + s • φ u' ≠ 0 := by
      intro h0
      rcases ht.eq_or_lt with rfl | htp
      · rw [zero_add] at hts
        rw [hts, zero_smul, zero_add, one_smul] at h0
        exact hu'0 h0
      · have hwL : t • u + s • u' ∈ L := (hφ0 _).1 (hφw ▸ h0)
        have hneg : -u ∈ K := by
          have e1 : -u = (t⁻¹ * s) • u' + (-t⁻¹) • (t • u + s • u') := by
            rw [smul_add, smul_smul, smul_smul, neg_mul, inv_mul_cancel₀ htp.ne']
            module
          rw [e1]
          exact hKadd _ (smul_mem_kPrime hu'K (by positivity)) _ (L.smul_mem _ hwL)
        exact hu0 ((hφ0 u).2 (hKpt u huK hneg))
    refine ⟨⟨t • u + s • u', ?_, hφw⟩, hne⟩
    refine (mem_kPrime_of_ne ?_).1 hwK
    intro h; apply hne; rw [← hφw, h, map_zero]
  · -- compactness
    refine IsClosed.isCompact ?_
    rw [← isOpen_compl_iff, isOpen_iff_F, F_compl, hFX]
    have hsat : (φ '' K)ᶜ = φ '' Kᶜ := by
      ext y
      constructor
      · intro hy
        obtain ⟨v, rfl⟩ := hφs y
        exact ⟨v, fun hv => hy ⟨v, hv, rfl⟩, rfl⟩
      · rintro ⟨v, hv, rfl⟩ ⟨k, hk, hkv⟩
        apply hv
        have : v - k ∈ L := (hφ0 _).1 (by rw [map_sub, hkv, sub_self])
        have := hKadd k hk _ this
        simpa using this
    have hopen : IsOpen (φ '' K)ᶜ := by
      rw [hsat]
      exact LinearMap.isOpenMap_of_finiteDimensional φ hφs _ hKc.isOpen_compl
    convert hopen using 1
    rw [← hins]
    ext y
    by_cases hy : y = 0 <;> simp [hy]
  · -- interior
    obtain ⟨v, hv⟩ := hint
    set U := interior (F C)
    have hUo : IsOpen (φ '' U) := LinearMap.isOpenMap_of_finiteDimensional φ hφs _ isOpen_interior
    have hne : (φ '' U \ {0}).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
      have hv' : φ v ∈ φ '' U := ⟨v, hv, rfl⟩
      have h1 : φ '' U = {0} := by
        refine Subset.antisymm h ?_
        rintro _ rfl
        have := h hv'
        rw [mem_singleton_iff] at this
        rw [← this]; exact hv'
      exact not_isOpen_singleton (0 : Fin (m + 1) → ℝ) (h1 ▸ hUo)
    obtain ⟨y, hyU, hy0⟩ := hne
    have hsub : φ '' U \ {0} ⊆ φ '' F C \ {0} :=
      sdiff_subset_sdiff_left (image_mono interior_subset)
    have hyi : y ∈ interior (F (ofCone (φ '' F C))) := by
      rw [hFX]
      exact interior_maximal hsub (hUo.sdiff isClosed_singleton) ⟨hyU, hy0⟩
    rw [← F_interior] at hyi
    exact ⟨_, (mk_mem_iff_mem_F hy0).2 hyi⟩

/-- **Prop. 10** (`bzprop:c3s4p10_contingent_conique`, not marked: the interior facette, support
`S(n)`, is excluded by `supportK F ≠ univ`, see `interior_facette_conique`): for a conical facette
`F` of support `l = s(L − O) ≠ S(n)` of a convex body `W` and `a ∈ F`, the contingent `C` at `a`
is a convex part containing `l`, identified with its image in `S(n)/l` (`convexQuotientEquiv`),
and under every linear identification `E/L ≃ ℝᵐ⁺¹` (one exists) this image is a convex body of
`S(m)`. -/
theorem prop10_contingent_conique {W F : Set (S n)} (hW : IsCorpsConvexeS n W)
    (hF : IsFacetteConique W F) (hL : supportK F ≠ univ) {a : S n} (ha : a ∈ F) :
    (IsConvexPart (contingent W a) ∧
      linearSubvariety (Submodule.span ℝ (Sphere.F F)) ⊆ contingent W a ∧
      quotientPreimage (Submodule.span ℝ (Sphere.F F))
        (quotientImage (Submodule.span ℝ (Sphere.F F)) (contingent W a)) = contingent W a) ∧
    (∃ m : ℕ, m + 1 + Module.finrank ℝ (Submodule.span ℝ (Sphere.F F)) = n + 1 ∧
      Nonempty (((Fin (n + 1) → ℝ) ⧸ Submodule.span ℝ (Sphere.F F)) ≃ₗ[ℝ] (Fin (m + 1) → ℝ))) ∧
    ∀ (m : ℕ) (e : ((Fin (n + 1) → ℝ) ⧸ Submodule.span ℝ (Sphere.F F)) ≃ₗ[ℝ] (Fin (m + 1) → ℝ)),
      IsCorpsConvexeS m
        (mapEquiv e '' quotientImage (Submodule.span ℝ (Sphere.F F)) (contingent W a)) := by
  set L := Submodule.span ℝ (Sphere.F F) with hLdef
  have hWc : IsConvexPart W := hW.1.1
  have hnoy : noyau (contingent W a) = linearSubvariety L :=
    ((isFacetteConique_iff_forall hWc).1 hF).2 a ha
  have hC := isConvexPart_contingent W a
  have hLC : linearSubvariety L ⊆ contingent W a := hnoy ▸ noyau_subset
  have hLtop : L ≠ ⊤ := by
    intro h
    apply hL
    show linearSubvariety L = univ
    rw [h, eq_univ_iff_forall]
    intro x
    induction x using ind with
    | h v hv => exact (mk_mem_linearSubvariety hv).2 Submodule.mem_top
  refine ⟨⟨hC, hLC, quotientPreimage_quotientImage hC hLC⟩, ?_, ?_⟩
  · haveI : Nontrivial ((Fin (n + 1) → ℝ) ⧸ L) := Submodule.Quotient.nontrivial_iff.2 hLtop
    have hpos : 0 < Module.finrank ℝ ((Fin (n + 1) → ℝ) ⧸ L) := Module.finrank_pos
    have hsum := Submodule.finrank_quotient_add_finrank L
    rw [Module.finrank_fin_fun] at hsum
    refine ⟨Module.finrank ℝ ((Fin (n + 1) → ℝ) ⧸ L) - 1, by omega,
      ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩⟩
    rw [Module.finrank_fin_fun]
    omega
  · intro m e
    refine isCorpsConvexeS_image_quotient hC (isClosed_contingent W a) hnoy ?_ e
    obtain ⟨x, hx⟩ := hW.2.2
    obtain ⟨v, hv0, rfl⟩ := exists_isRep x
    have hWC : W ⊆ contingent W a :=
      (isLeast_coneAppui W a).1.2.1.trans (coneAppui_subset_contingent W a)
    refine ⟨v, ?_⟩
    rw [← F_interior]
    exact (mk_mem_iff_mem_F hv0).1 (interior_mono hWC hx)

/-- **Prop. 10 at the interior facette** (finding): the facette of a point of the interior of a
convex body is conical, its support is `S(n)`, and `S(n)/S(n)` is empty, so it carries no convex
body. -/
theorem interior_facette_conique {W : Set (S n)} (hW : IsCorpsConvexeS n W) {a : S n}
    (ha : a ∈ interior W) :
    IsFacetteConique W (facetteK W a) ∧ supportK (facetteK W a) = univ ∧
      IsEmpty (quotient (Submodule.span ℝ (Sphere.F (facetteK W a)))) := by
  have hWc : IsConvexPart W := hW.1.1
  obtain ⟨A, hA0, rfl⟩ := exists_isRep a
  have hAi : A ∈ interior (Sphere.F W) := by
    rw [← F_interior]; exact (mk_mem_iff_mem_F hA0).1 ha
  -- along every direction `v`, `A + t v ∈ F(W)` for `|t| < ε`
  have hdir : ∀ v : Fin (n + 1) → ℝ, ∃ ε > 0, ∀ t : ℝ, |t| < ε → A + t • v ∈ Sphere.F W := by
    intro v
    have hc : Continuous fun t : ℝ => A + t • v := by fun_prop
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), A + t • v ∈ interior (Sphere.F W) :=
      hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hAi)
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨ε, hε, fun t ht => interior_subset (h (by simpa [Real.dist_eq] using ht))⟩
  have hK : ∀ {u : Fin (n + 1) → ℝ}, u ∈ Sphere.F W → u ∈ kPrime W := fun h => mem_insert_of_mem _ h
  have haW : mk A hA0 ∈ W := interior_subset ha
  have hAF : A ∈ Sphere.F W := ⟨hA0, haW⟩
  -- the supporting cone, hence the contingent, is `S(n)`
  have hcone : coneAppui W (mk A hA0) = univ := by
    rw [coneAppui_eq_ofCone hWc haW ⟨hA0, rfl⟩, eq_univ_iff_forall]
    intro x
    induction x using ind with
    | h v hv =>
    obtain ⟨ε, hε, h⟩ := hdir v
    have hδ : |ε / 2| < ε := by rw [abs_of_pos (by positivity)]; linarith
    refine mk_mem_ofCone hv ⟨-(2 / ε), (2 / ε) • (A + (ε / 2) • v),
      smul_mem_F (h _ hδ) (by positivity), ?_⟩
    rw [smul_add, smul_smul, div_mul_div_comm, mul_comm 2 ε, div_self (by positivity), one_smul]
    module
  have hC : contingent W (mk A hA0) = univ := by
    rw [contingent, hcone, closure_univ]
  have hnoy : noyau (contingent W (mk A hA0)) = univ := by
    rw [noyau_eq (isConvexPart_contingent _ _), hC]
    ext; simp
  -- the support of the facette is `S(n)`
  have hspan : Submodule.span ℝ (Sphere.F (facetteK W (mk A hA0))) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨ε, hε, h⟩ := hdir v
    set δ := ε / 3 with hδ
    have hδp : 0 < δ := by positivity
    have h1 : A + δ • v ∈ Sphere.F W := h δ (by rw [abs_of_pos hδp]; linarith)
    have h2 : A + (2 * δ) • v ∈ Sphere.F W :=
      h (2 * δ) (by rw [abs_of_pos (by positivity)]; linarith)
    have h3 : A + (-δ) • v ∈ Sphere.F W := h (-δ) (by rw [abs_neg, abs_of_pos hδp]; linarith)
    have hB0 : A + δ • v ≠ 0 := h1.1
    have hconv : Convex ℝ (kPrime W) := convex_kPrime hWc
    have hBf : A + δ • v ∈ Sphere.F (facetteK W (mk A hA0)) := by
      refine ⟨hB0, ?_, ?_⟩
      · rw [alphaK_iff hWc ⟨hA0, rfl⟩ ⟨hB0, rfl⟩, alphaW_iff_extend hconv]
        refine ⟨hK hAF, hK h1, 1, one_pos, ?_⟩
        convert hK h3 using 1; module
      · rw [alphaK_iff hWc ⟨hB0, rfl⟩ ⟨hA0, rfl⟩, alphaW_iff_extend hconv]
        refine ⟨hK h1, hK hAF, 1, one_pos, ?_⟩
        convert hK h2 using 1; module
    have hAf : A ∈ Sphere.F (facetteK W (mk A hA0)) := ⟨hA0, mem_facetteK_self haW⟩
    have : v = δ⁻¹ • ((A + δ • v) - A) := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hδp.ne', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span hBf)
      (Submodule.subset_span hAf))
  have hsupp : supportK (facetteK W (mk A hA0)) = univ := by
    show linearSubvariety _ = univ
    rw [hspan, eq_univ_iff_forall]
    intro x
    induction x using ind with
    | h v hv => exact (mk_mem_linearSubvariety hv).2 Submodule.mem_top
  refine ⟨⟨⟨mk A hA0, haW, rfl⟩, mk A hA0, mem_facetteK_self haW, by rw [hnoy, hsupp]⟩, hsupp, ?_⟩
  rw [hspan]
  refine ⟨fun x => ?_⟩
  induction x using ind with
  | h v hv =>
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact hv ((Submodule.Quotient.mk_eq_zero _).2 Submodule.mem_top)

end Prop10


/-! ### Instances -/

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T1Space E]

/-- `s(C − O)` is closed for a closed cone `C ∋ O`. -/
theorem isClosed_ofCone {C : Set E} (hC : IsPosCone C) (hCc : IsClosed C) (h0 : (0 : E) ∈ C) :
    IsClosed (ofCone C) := by
  rw [← isOpen_compl_iff, isOpen_iff_F, F_compl, F_ofCone hC]
  convert hCc.isOpen_compl using 1
  ext v
  by_cases hv : v = 0
  · subst hv; simp [h0]
  · simp [hv]

end Sphere

namespace FacetteConiqueInstance

open Sphere FacetteDualeInstance

/-! #### The vertex of the closed triangle: a conical facette -/

/-- `e₀ = (1, 0, 0)`. -/
abbrev eA : Fin 3 → ℝ := Pi.single 0 1

theorem eA_ne_zero : eA ≠ 0 := by intro h; simpa using congrFun h 0

/-- The closed cone `{x₁ ≥ 0, x₂ ≥ 0}` of `ℝ³`. -/
def coin : Set (Fin 3 → ℝ) := {v | 0 ≤ v 1 ∧ 0 ≤ v 2}

theorem isPosCone_coin : IsPosCone coin := fun c hc v hv =>
  ⟨by simpa using mul_nonneg hc.le hv.1, by simpa using mul_nonneg hc.le hv.2⟩

theorem isClosed_coin : IsClosed coin :=
  (isClosed_le continuous_const (continuous_apply 1)).inter
    (isClosed_le continuous_const (continuous_apply 2))

theorem vertex0_mem : vertex0 2 ∈ simplexS 2 := isFacetteK_vertex0.subset (mem_singleton _)

theorem coneAppuiVec_simplexS : coneAppuiVec (simplexS 2) eA = coin := by
  ext M
  constructor
  · rintro ⟨l, P, hP, rfl⟩
    have hPo := (mk_mem_simplexS_iff hP.1).1 hP.2
    exact ⟨by simpa using hPo 1, by simpa using hPo 2⟩
  · rintro ⟨h1, h2⟩
    set c : ℝ := |M 0| + 1
    have hc : 0 < c := by positivity
    have hP0 : 0 < (M + c • eA) 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, c]
      linarith [neg_abs_le (M 0)]
    have hPne : M + c • eA ≠ 0 := fun h => by rw [h] at hP0; simp at hP0
    refine ⟨-c, M + c • eA, ⟨hPne, (mk_mem_simplexS_iff hPne).2 fun i => ?_⟩, by module⟩
    fin_cases i
    · exact hP0.le
    · simpa using h1
    · simpa using h2

/-- **The contingent at the vertex `s(e₀)` of the closed triangle** is `{x₁ ≥ 0, x₂ ≥ 0}`. -/
theorem contingent_vertex0 : contingent (simplexS 2) (vertex0 2) = ofCone coin := by
  have h : coneAppui (simplexS 2) (vertex0 2) = ofCone coin := by
    rw [coneAppui_eq_ofCone isConvexPart_simplexS vertex0_mem (isRep_mk eA eA_ne_zero),
      coneAppuiVec_simplexS]
  rw [contingent, h]
  exact (isClosed_ofCone isPosCone_coin isClosed_coin ⟨le_rfl, le_rfl⟩).closure_eq

/-- The line `{x₁ = x₂ = 0}` of `e₀`. -/
abbrev L0 : Submodule ℝ (Fin 3 → ℝ) := Submodule.span ℝ {eA}

theorem mem_L0_iff {v : Fin 3 → ℝ} : v ∈ L0 ↔ v 1 = 0 ∧ v 2 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩; simp
  · rintro ⟨h1, h2⟩
    refine ⟨v 0, funext fun i => ?_⟩
    fin_cases i <;> simp [h1, h2]

theorem supportK_vertex0 : supportK {vertex0 2} = linearSubvariety L0 := by
  have h := supportK_pair (isRep_mk eA eA_ne_zero) (isRep_mk eA eA_ne_zero)
  rw [pair_eq_singleton, pair_eq_singleton] at h
  exact h

theorem noyau_contingent_vertex0 :
    noyau (contingent (simplexS 2) (vertex0 2)) = linearSubvariety L0 := by
  rw [noyau_eq (isConvexPart_contingent _ _), contingent_vertex0]
  ext x
  induction x using ind with
  | h v hv =>
  rw [mem_setOf_eq, neg_mk, mk_mem_ofCone_iff isPosCone_coin, mk_mem_ofCone_iff isPosCone_coin,
    mk_mem_linearSubvariety, mem_L0_iff]
  simp only [coin, mem_setOf_eq, Pi.neg_apply, Left.nonneg_neg_iff]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨le_antisymm c a, le_antisymm d b⟩
  · rintro ⟨a, b⟩; exact ⟨⟨a.ge, b.ge⟩, a.le, b.le⟩

/-- **Déf. 5, instance**: the vertex `{s(e₀)}` of the closed triangle is a conical facette. -/
theorem isFacetteConique_vertex0 : IsFacetteConique (simplexS 2) {vertex0 2} :=
  ⟨isFacetteK_vertex0, vertex0 2, mem_singleton _, by
    rw [noyau_contingent_vertex0, supportK_vertex0]⟩

/-- The closed triangle is a convex body of `S(2)`. -/
theorem isCorpsConvexeS_simplexS : IsCorpsConvexeS 2 (simplexS 2) :=
  TriangleInstance.isCorpsConvexeS_simplexS

theorem supportK_vertex0_ne_univ : supportK {vertex0 2} ≠ univ := by
  rw [supportK_vertex0]
  intro h
  have hne : (Pi.single 1 1 : Fin 3 → ℝ) ≠ 0 := by intro h; simpa using congrFun h 1
  have := (mk_mem_linearSubvariety hne).1 (h ▸ mem_univ (mk _ hne))
  simp [mem_L0_iff] at this

/-- **Prop. 10, instance**: its hypotheses hold at the vertex of the triangle. -/
theorem prop10_instance :
    IsCorpsConvexeS 2 (simplexS 2) ∧ IsFacetteConique (simplexS 2) {vertex0 2} ∧
      supportK {vertex0 2} ≠ univ :=
  ⟨isCorpsConvexeS_simplexS, isFacetteConique_vertex0, supportK_vertex0_ne_univ⟩

/-- The plane `L′ = {x₀ = 0} = span(e₁, e₂)`. -/
abbrev L1 : Submodule ℝ (Fin 3 → ℝ) := LinearMap.ker (LinearMap.proj 0)

theorem isCompl_L0_L1 : IsCompl L0 L1 := by
  rw [isCompl_iff, Submodule.disjoint_def, codisjoint_iff, eq_top_iff]
  refine ⟨fun v hv hv' => ?_, fun v _ => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have : a = 0 := by simpa using hv'
    simp [this]
  · refine Submodule.mem_sup.2 ⟨v 0 • eA,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      v - v 0 • eA, by simp, by abel⟩

theorem estSommeLineaire_L0_L1 : EstSommeLineaire L0 L1 := estSommeLineaire_iff.2 isCompl_L0_L1

/-- **Déf. 6, instance**: the base in `L′ = span(e₁, e₂)` of the vertex `{s(e₀)}` of the closed
triangle is the opposite closed edge `T ∩ L′`. -/
theorem isBaseFacetteConique_vertex0 :
    IsBaseFacetteConique (simplexS 2) {vertex0 2} L1 (simplexS 2 ∩ linearSubvariety L1) := by
  refine ⟨isFacetteConique_vertex0, ?_, vertex0 2, mem_singleton _, ?_⟩
  · have : Submodule.span ℝ (Sphere.F {vertex0 2}) = L0 := by
      have h := supportK_vertex0
      unfold supportK at h
      exact (ofCone_eq_ofCone_iff (isPosCone_submodule _) (isPosCone_submodule _)).1 h |> fun h' =>
        SetLike.coe_injective (by
          ext v; by_cases hv : v = 0
          · simp [hv]
          · have := congrArg (v ∈ ·) h'; simpa [hv] using this)
    rw [this]; exact estSommeLineaire_L0_L1
  · rw [contingent_vertex0]
    ext x
    induction x using ind with
    | h v hv =>
    rw [mem_inter_iff, mem_inter_iff, mk_mem_simplexS_iff, mk_mem_linearSubvariety,
      mk_mem_ofCone_iff isPosCone_coin]
    simp only [coin, mem_setOf_eq, LinearMap.mem_ker, LinearMap.proj_apply]
    constructor
    · rintro ⟨h, h0⟩
      exact ⟨h0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun i => ?_, h0⟩
      fin_cases i
      · simp [h0]
      · exact h1
      · exact h2

/-! #### A closed round cap: a facette that is not conical -/

/-- The closed convex cone `{x₀ ≥ 0, x₂ ≥ 0, x₁² ≤ x₀ x₂}` of `ℝ³`, a circular cone (in the
coordinates `x₀ + x₂`, `x₀ − x₂`, `2x₁` it is `‖(x₀ − x₂, 2x₁)‖ ≤ x₀ + x₂`); its trace on `S(2)`
is a closed round cap, a projective image of a closed disc. -/
def capCone : Set (Fin 3 → ℝ) := {v | 0 ≤ v 0 ∧ 0 ≤ v 2 ∧ v 1 ^ 2 ≤ v 0 * v 2}

/-- The closed round cap of `S(2)`. -/
def cap : Set (S 2) := ofCone capCone

theorem isPosCone_capCone : IsPosCone capCone := by
  rintro c hc v ⟨h0, h2, h1⟩
  refine ⟨by simpa using mul_nonneg hc.le h0, by simpa using mul_nonneg hc.le h2, ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_pos hc hc]

theorem zero_mem_capCone : (0 : Fin 3 → ℝ) ∈ capCone := by simp [capCone]

theorem convex_capCone : Convex ℝ capCone := by
  rintro x ⟨hx0, hx2, hx1⟩ y ⟨hy0, hy2, hy1⟩ t s ht hs hts
  simp only [capCone, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  -- `2 x₁ y₁ ≤ x₀ y₂ + y₀ x₂`, from `(x₁ y₁)² ≤ (x₀ y₂)(y₀ x₂)`
  have hprod : (x 1 * y 1) ^ 2 ≤ (x 0 * y 2) * (y 0 * x 2) := by
    have := mul_le_mul hx1 hy1 (sq_nonneg _) (by positivity)
    nlinarith [this]
  have hcross : 2 * (x 1 * y 1) ≤ x 0 * y 2 + y 0 * x 2 := by
    have h1 : 0 ≤ x 0 * y 2 := by positivity
    have h2 : 0 ≤ y 0 * x 2 := by positivity
    nlinarith [sq_nonneg (x 0 * y 2 - y 0 * x 2), sq_nonneg (x 1 * y 1),
      abs_le_of_sq_le_sq' (show (2 * (x 1 * y 1)) ^ 2 ≤ (x 0 * y 2 + y 0 * x 2) ^ 2 by
        nlinarith [sq_nonneg (x 0 * y 2 - y 0 * x 2)]) (by positivity)]
  nlinarith [mul_nonneg ht hs, mul_nonneg (mul_nonneg ht hs) (sub_nonneg.2 hcross),
    mul_le_mul_of_nonneg_left hx1 (mul_nonneg ht ht),
    mul_le_mul_of_nonneg_left hy1 (mul_nonneg hs hs)]

theorem kPrime_cap : kPrime cap = capCone := by
  rw [kPrime, cap, F_ofCone isPosCone_capCone, insert_sdiff_singleton,
    insert_eq_of_mem zero_mem_capCone]

theorem isConvexPart_cap : IsConvexPart cap := by
  show Convex ℝ (kPrime cap)
  rw [kPrime_cap]; exact convex_capCone

theorem isClosed_capCone : IsClosed capCone := by
  refine (isClosed_le continuous_const (continuous_apply 0)).inter
    ((isClosed_le continuous_const (continuous_apply 2)).inter ?_)
  exact isClosed_le (f := fun v : Fin 3 → ℝ => v 1 ^ 2) (g := fun v => v 0 * v 2)
    (by fun_prop) (by fun_prop)

theorem isClosed_cap : IsClosed cap :=
  isClosed_ofCone isPosCone_capCone isClosed_capCone zero_mem_capCone

theorem eq_zero_of_mem_capCone {x : Fin 3 → ℝ} (hx : x ∈ capCone) (h0 : x 0 = 0) (h2 : x 2 = 0) :
    x = 0 := by
  obtain ⟨-, -, h1⟩ := hx
  rw [h0, zero_mul] at h1
  have : x 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h1 (sq_nonneg _))
  funext i
  fin_cases i <;> simp [h0, h2, this]

/-- The closed round cap is a convex body of `S(2)`. -/
theorem isCorpsConvexeS_cap : IsCorpsConvexeS 2 cap := by
  rw [isCorpsConvexeS_iff]
  refine ⟨?_, isClosed_cap.isCompact, ?_⟩
  · rw [cap, F_ofCone isPosCone_capCone]
    rintro x ⟨hx, hx0⟩ y ⟨hy, hy0⟩ t s ht hs hts
    refine ⟨convex_capCone hx hy ht hs hts, fun h => ?_⟩
    have h := mem_singleton_iff.1 h
    have e0 := congrFun h 0
    have e2 := congrFun h 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 e2
    rcases ht.eq_or_lt with rfl | htp
    · rw [zero_add] at hts
      subst hts
      apply hy0; rw [mem_singleton_iff]; simpa using h
    · have a0 : x 0 = 0 := by nlinarith [hx.1, hy.1, mul_nonneg hs hy.1]
      have a2 : x 2 = 0 := by nlinarith [hx.2.1, hy.2.1, mul_nonneg hs hy.2.1]
      exact hx0 (eq_zero_of_mem_capCone hx a0 a2)
  · set O : Set (Fin 3 → ℝ) := {v | 0 < v 0 ∧ 0 < v 2 ∧ v 1 ^ 2 < v 0 * v 2}
    have hOpos : IsPosCone O := by
      rintro c hc v ⟨h0, h2, h1⟩
      refine ⟨by simpa using mul_pos hc h0, by simpa using mul_pos hc h2, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_pos hc hc]
    have hOo : IsOpen O := by
      refine (isOpen_lt continuous_const (continuous_apply 0)).inter
        ((isOpen_lt continuous_const (continuous_apply 2)).inter ?_)
      exact isOpen_lt (f := fun v : Fin 3 → ℝ => v 1 ^ 2) (g := fun v => v 0 * v 2)
        (by fun_prop) (by fun_prop)
    have hv : (![1, 0, 1] : Fin 3 → ℝ) ≠ 0 := by intro h; simpa using congrFun h 0
    have hsub : O ⊆ capCone := fun v hv => ⟨hv.1.le, hv.2.1.le, hv.2.2.le⟩
    refine ⟨mk _ hv, interior_maximal (ofCone_subset_ofCone hsub) (isOpen_ofCone hOpos hOo) ?_⟩
    exact (mk_mem_ofCone_iff hOpos hv).2 (by simp [O])

/-- The boundary point `p = s(e₀)` of the cap. -/
def capPt : S 2 := mk eA eA_ne_zero

theorem eA_mem_capCone : eA ∈ capCone := by simp [capCone]

theorem capPt_mem : capPt ∈ cap := (mk_mem_ofCone_iff isPosCone_capCone _).2 eA_mem_capCone

/-- The axis `{x₁ = x₂ = 0}` contains the facette of `p` (in fact the facette is `{p}`). -/
theorem facetteK_capPt_subset : facetteK cap capPt ⊆ linearSubvariety L0 := by
  intro x hx
  induction x using ind with
  | h B hB =>
  have h := hx.1
  rw [capPt, alphaK_iff isConvexPart_cap (isRep_mk eA eA_ne_zero) (isRep_mk B hB), kPrime_cap,
    alphaW_iff_extend convex_capCone] at h
  obtain ⟨-, ⟨hB0, hB2, hB1⟩, ε, hε, hX⟩ := h
  have hX2 := hX.2.1
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hX2
  have : B 2 = 0 := by
    have : ε * B 2 ≤ 0 := by simpa using hX2
    exact le_antisymm (nonpos_of_mul_nonpos_right this hε) hB2
  rw [this, mul_zero] at hB1
  rw [mk_mem_linearSubvariety, mem_L0_iff]
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hB1 (sq_nonneg _)), this⟩

/-- `e₁ = (0, 1, 0)`, `e₂ = (0, 0, 1)`. -/
abbrev eB : Fin 3 → ℝ := Pi.single 1 1
abbrev eC : Fin 3 → ℝ := Pi.single 2 1

theorem linearIndependent_eB_eC : LinearIndependent ℝ ![eB, eC] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp at h1 h2
  exact ⟨h1, h2⟩

/-- The open half-plane `{s(a e₁ + b e₂) | b > 0}` lies in the supporting cone at `p`. -/
theorem halfLine_subset_coneAppui_capPt : halfLine eB eC ⊆ coneAppui cap capPt := by
  rw [coneAppui_eq_ofCone isConvexPart_cap capPt_mem (isRep_mk eA eA_ne_zero)]
  refine ofCone_subset_ofCone ?_
  rintro _ ⟨a, b, hb, rfl⟩
  set c : ℝ := a ^ 2 / b + 1
  have hc : 0 < c := by positivity
  have hP : c • eA + a • eB + b • eC ∈ capCone := by
    simp only [capCone, mem_setOf_eq]
    refine ⟨by simp; positivity, by simp; positivity, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp
    have : c * b = a ^ 2 + b := by simp only [c]; field_simp
    nlinarith
  have hP0 : c • eA + a • eB + b • eC ≠ 0 := by
    intro h; have := congrFun h 0; simp at this; linarith
  exact ⟨-c, c • eA + a • eB + b • eC, ⟨hP0, (mk_mem_ofCone_iff isPosCone_capCone hP0).2 hP⟩,
    by module⟩

/-- `s(e₁)` lies in the noyau of the contingent at `p` (with `s(−e₁)`: the tangent great circle
`{x₂ = 0}` is in the noyau). -/
theorem mk_eB_mem_noyau : mk eB (linearIndependent_eB_eC.ne_zero 0) ∈
    noyau (contingent cap capPt) := by
  have hcl := closure_mono halfLine_subset_coneAppui_capPt
  have h1 := mk_smul_mem_closure_halfLine linearIndependent_eB_eC (one_ne_zero (α := ℝ))
  have h2 := mk_smul_mem_closure_halfLine linearIndependent_eB_eC
    (neg_ne_zero.2 (one_ne_zero (α := ℝ)))
  rw [noyau_eq (isConvexPart_contingent _ _)]
  refine ⟨?_, ?_⟩
  · have := hcl h1
    simpa [contingent] using this
  · have := hcl h2
    rw [neg_mk]
    simpa [contingent] using this

/-- **Déf. 5, a facette that is not conical**: at the boundary point `p` of the closed round cap,
the noyau of the contingent contains `s(e₁)`, which the support of the facette of `p` misses. -/
theorem cap_facette_example :
    IsCorpsConvexeS 2 cap ∧ IsFacetteK cap (facetteK cap capPt) ∧
      ¬ IsFacetteConique cap (facetteK cap capPt) := by
  refine ⟨isCorpsConvexeS_cap, ⟨capPt, capPt_mem, rfl⟩, ?_⟩
  intro h
  have h' := ((isFacetteConique_iff_forall isConvexPart_cap).1 h).2 capPt
    (mem_facetteK_self capPt_mem)
  have hm := mk_eB_mem_noyau
  rw [h'] at hm
  have := (mk_mem_linearSubvariety _).1 (supportK_subset facetteK_capPt_subset hm)
  simp [mem_L0_iff] at this

end FacetteConiqueInstance

end Benzecri
