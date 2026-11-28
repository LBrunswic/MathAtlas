import Benzecri.Chapter3.FacetteConique
import Benzecri.Chapter3.Appui

/-!
# Chapter 3 § 4, Prop. 10 — a facette of support `S(n)` is the interior facette

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 4, journal p. 276; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR, OQ-160).
Target T-bz-c3-facette-interieure. It makes exact the hypothesis `supportK F ≠ univ` of
`Benzecri.prop10_contingent_conique` (Chapter3/FacetteConique): that hypothesis says exactly
« `F` is not the interior facette ».

* `bzprop:c3s4p10_contingent_conique` — `benzecri1960_ch3.tex:1122` (Prop. 10, l.1122–1125;
  proof l.1127–1130) — NOT marked: OQ-169 (a) is OPEN. Proved here:
  `Benzecri.Sphere.facetteK_eq_interior` (for a convex part `W` of `S(n)` and `a ∈ int W`, the
  facette of `a` is `int W`), `Benzecri.Sphere.eq_interior_of_supportK_eq_univ` (a facette of a
  convex part `W` with support `S(n)` is `int W`), `Benzecri.isFacetteK_supportK_eq_univ_iff`
  (for a convex body: `F` is a facette of support `S(n)` iff `F = int W`, and then `F` is
  conical), and the corollary `Benzecri.prop10_contingent_conique_of_ne_interior`, Prop. 10 with
  the hypothesis « `F ≠ int W` » in place of `supportK F ≠ univ`. So the two readings of OQ-169 (a)
  are exactly « every conical facette » (false at `F = int W`, `interior_facette_conique`) and
  « every conical facette but the interior one » (proved).

> **Proposition 10.** Soient $W$ un corps convexe, $F$ une facette conique de $W$, $L$ son
> support; le contingent à $W$ en un point de $F$ s'identifie à un corps convexe de $S(n)/L$.
>
> Parce que $W$ est d'intérieur non vide, il en est de même du contingent considéré comme partie
> de $S(n)/L$; que le noyau de cette partie soit vide résulte de ce que $F$ est conique.

## The proofs formalized

Write `K′ = F(W) ∪ {O}`, a convex cone of `ℝⁿ⁺¹`, and `A` a representative of `a`.
`facetteK_eq_interior`: for `a, b ∈ int W`, `A + ε (A − B) ∈ K′` for small `ε` since `A` is
interior, so `a α b` and symmetrically; conversely if `b` is in the facette of `a`, `b α a` gives
`P = B + ε (B − A) ∈ K′`, so `B = P/(1+ε) + ε A/(1+ε)` is interior to `K′` (a combination with a
positive weight on an interior point), and `B ≠ O`, so `b ∈ int W` (`F(int W) = int F(W)`).
`eq_interior_of_supportK_eq_univ`: the `K′`-facette `G` of `A` spans `ℝⁿ⁺¹`
(`coe_affineSpan_facetteOf`); by Chapter 3 § 3 Remark 1° (`remarque_facette_interieur`) the facette
of `K′` whose support is the support of `K′` is its intrinsic interior; `G` is that facette
(facettes are ordered by their supports, `facetteLE_iff_support_le`), and the support is the whole
space, so `A ∈ int K′`, `a ∈ int W`, and `F = facetteK W a = int W`. The planner's route (« F is
relatively open in its support, hence open ») is this one, through Remark 1°.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Prop. 10: « $W$ un corps convexe » | ✓ carried in the iff and the corollary (`IsCorpsConvexeS n W`); ⚠ weakened to `IsConvexPart W` in `facetteK_eq_interior` and `eq_interior_of_supportK_eq_univ` |
| Prop. 10: « $F$ une facette conique de $W$ » | ✓ carried: `IsFacetteConique W F` (corollary); `IsFacetteK W F` suffices for the converse |
| Prop. 10: « $L$ son support » | ✓ carried: `supportK F` |
| Prop. 10: (unstated, OQ-169 (a)) `L ≠ S(n)` | **added** (finding, as in FacetteConique): now as `F ≠ interior W`, equivalent to `supportK F ≠ univ` for a facette of a convex body |

## SCOPE (disclosed)

* Prop. 10 is not marked: the corollary still adds a hypothesis (« `F` is not the interior
  facette »), the reading (a) of OQ-169, which is OPEN. What this file adds is that the added
  hypothesis excludes exactly one facette, `int W`, and nothing else.
* Instances (`Benzecri.FacetteInterieureInstance`), on `S(2)`: the closed triangle
  `T = simplexS 2` has the interior facette `int T`, a facette of support `S(2)`
  (`interior_simplexS_facette`), and the vertex facette `{s(e₀)}` is not `int T`
  (`vertex0_ne_interior`), so it meets the corollary's hypotheses (`prop10_of_ne_interior_instance`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology

namespace Benzecri

namespace Sphere

variable {n : ℕ}

/-- `a ∈ int W` iff a representative is interior to `F(W)`. -/
theorem mem_interior_iff_isRep {W : Set (S n)} {a : S n} {A : Fin (n + 1) → ℝ}
    (hA : IsRep A a) : a ∈ interior W ↔ A ∈ interior (F W) := by
  obtain ⟨hA0, rfl⟩ := hA
  rw [← F_interior]
  exact mk_mem_iff_mem_F hA0

/-- Off `O`, the interior of `K′ = F(W) ∪ {O}` is the interior of `F(W)`. -/
theorem mem_interior_kPrime_iff {W : Set (S n)} {v : Fin (n + 1) → ℝ} (hv : v ≠ 0) :
    v ∈ interior (kPrime W) ↔ v ∈ interior (F W) := by
  constructor
  · intro h
    have hsub : interior (kPrime W) ∩ {0}ᶜ ⊆ F W := fun x ⟨hx, hx0⟩ =>
      (show x ∈ insert 0 (F W) from interior_subset hx).resolve_left hx0
    exact interior_maximal hsub (isOpen_interior.inter isOpen_compl_singleton) ⟨h, hv⟩
  · exact fun h => interior_mono (subset_insert _ _) h

/-- A point of the interior is `α`-below every point of `W`. -/
theorem alphaK_of_mem_interior {W : Set (S n)} (hW : IsConvexPart W) {a b : S n}
    (ha : a ∈ interior W) (hb : b ∈ W) : AlphaK W a b := by
  obtain ⟨A, hA⟩ := exists_isRep a
  obtain ⟨B, hB⟩ := exists_isRep b
  have hAi : A ∈ interior (kPrime W) :=
    (mem_interior_kPrime_iff hA.ne_zero).2 ((mem_interior_iff_isRep hA).1 ha)
  rw [alphaK_iff hW hA hB, alphaW_iff_extend (convex_kPrime hW)]
  refine ⟨interior_subset hAi, mem_kPrime_of_isRep hB hb, ?_⟩
  have hc : Continuous fun t : ℝ => A + t • (A - B) := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), A + t • (A - B) ∈ interior (kPrime W) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hAi)
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  exact ⟨t, htpos, interior_subset ht⟩

/-- **The interior facette**: for a convex part `W` of `S(n)` and `a ∈ int W`, the facette of `a`
is `int W`. -/
theorem facetteK_eq_interior {W : Set (S n)} (hW : IsConvexPart W) {a : S n}
    (ha : a ∈ interior W) : facetteK W a = interior W := by
  ext b
  constructor
  · intro hb
    obtain ⟨A, hA⟩ := exists_isRep a
    obtain ⟨B, hB⟩ := exists_isRep b
    have hAi : A ∈ interior (kPrime W) :=
      (mem_interior_kPrime_iff hA.ne_zero).2 ((mem_interior_iff_isRep hA).1 ha)
    have h : AlphaK W b a := hb.2
    rw [alphaK_iff hW hB hA, alphaW_iff_extend (convex_kPrime hW)] at h
    obtain ⟨-, -, ε, hε, hP⟩ := h
    have hcomb := (convex_kPrime hW).combo_self_interior_mem_interior hP hAi
      (a := 1 / (1 + ε)) (b := ε / (1 + ε)) (by positivity) (by positivity) (by field_simp)
    have e : (1 / (1 + ε)) • (B + ε • (B - A)) + (ε / (1 + ε)) • A = B := by
      rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, one_smul, ← smul_add]
      have : B + ε • (B - A) + ε • A = (1 + ε) • B := by module
      rw [this, inv_smul_smul₀ (by positivity)]
    rw [e] at hcomb
    exact (mem_interior_iff_isRep hB).2 ((mem_interior_kPrime_iff hB.ne_zero).1 hcomb)
  · intro hb
    exact ⟨alphaK_of_mem_interior hW ha (interior_subset hb),
      alphaK_of_mem_interior hW hb (interior_subset ha)⟩

/-- **A facette of support `S(n)` is the interior facette**: for a convex part `W` of `S(n)`, a
facette `F` with `supportK F = S(n)` is `int W` (in particular `int W ≠ ∅`). -/
theorem eq_interior_of_supportK_eq_univ {W F : Set (S n)} (hW : IsConvexPart W)
    (hF : IsFacetteK W F) (hL : supportK F = univ) : F = interior W := by
  obtain ⟨a, haF⟩ := hF.nonempty
  have haW := hF.subset haF
  obtain ⟨A, hA⟩ := exists_isRep a
  have hFa := hF.eq_facetteK hW haF
  have hK : Convex ℝ (kPrime W) := convex_kPrime hW
  have hAK := mem_kPrime_of_isRep hA haW
  have hG : IsFacette (kPrime W) (facetteOf (kPrime W) A) := isFacette_facetteOf hAK
  have hGspan : affineSpan ℝ (facetteOf (kPrime W) A) = ⊤ := by
    have h1 := coe_affineSpan_facetteOf hW hA haW
    rw [← hFa, linearSubvariety_eq_univ_iff.1 hL, Submodule.top_coe] at h1
    exact SetLike.coe_injective (h1.trans (AffineSubspace.top_coe ℝ _ _).symm)
  have hKspan : affineSpan ℝ (kPrime W) = ⊤ :=
    top_le_iff.1 (hGspan ▸ affineSpan_mono ℝ hG.subset)
  obtain ⟨F0, hF0, hspan0, hF0eq⟩ :=
    remarque_facette_interieur hK ⟨0, zero_mem_kPrime W⟩ inferInstance
  have hGF0 : facetteOf (kPrime W) A = F0 :=
    FacetteLE.antisymm hK hG hF0 ((facetteLE_iff_support_le hK hG hF0).2 (by rw [hGspan]; exact le_top))
      ((facetteLE_iff_support_le hK hF0 hG).2 (by rw [hspan0, hKspan]; exact le_top))
  have hAi : A ∈ interior (kPrime W) := by
    have hAG : A ∈ intrinsicInterior ℝ (kPrime W) := hF0eq ▸ hGF0 ▸ mem_facetteOf_self hAK
    obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.1 hAG
    have hN : kPrime W ∈ 𝓝[(affineSpan ℝ (kPrime W) : Set (Fin (n + 1) → ℝ))] ((y : Fin (n + 1) → ℝ)) :=
      preimage_coe_mem_nhds_subtype.1 (mem_interior_iff_mem_nhds.1 hy)
    have hS : ((affineSpan ℝ (kPrime W) : Set (Fin (n + 1) → ℝ))) = univ := by
      rw [hKspan]; rfl
    rw [hS, nhdsWithin_univ] at hN
    exact mem_interior_iff_mem_nhds.2 hN
  have hai : a ∈ interior W :=
    (mem_interior_iff_isRep hA).2 ((mem_interior_kPrime_iff hA.ne_zero).1 hAi)
  rw [hFa, facetteK_eq_interior hW hai]

end Sphere

open Sphere

variable {n : ℕ}

/-- **The facettes of support `S(n)` of a convex body** (Prop. 10's hypothesis made exact): `F` is
a facette of `W` with support `S(n)` iff `F = int W`; the interior facette is then conical. -/
theorem isFacetteK_supportK_eq_univ_iff {W F : Set (S n)} (hW : IsCorpsConvexeS n W) :
    (IsFacetteK W F ∧ supportK F = univ) ↔ F = interior W := by
  constructor
  · rintro ⟨hF, hL⟩
    exact eq_interior_of_supportK_eq_univ hW.1.1 hF hL
  · rintro rfl
    obtain ⟨a, ha⟩ := hW.2.2
    have h := (interior_facette_conique hW ha).2.1
    rw [facetteK_eq_interior hW.1.1 ha] at h
    exact ⟨⟨a, interior_subset ha, (facetteK_eq_interior hW.1.1 ha).symm⟩, h⟩

/-- The interior of a convex body is a conical facette of support `S(n)`. -/
theorem interior_isFacetteConique {W : Set (S n)} (hW : IsCorpsConvexeS n W) :
    IsFacetteConique W (interior W) ∧ supportK (interior W) = univ := by
  obtain ⟨a, ha⟩ := hW.2.2
  have h := interior_facette_conique hW ha
  rw [facetteK_eq_interior hW.1.1 ha] at h
  exact ⟨h.1, h.2.1⟩

/-- For a facette of a convex body, `supportK F ≠ S(n)` iff `F` is not the interior facette. -/
theorem supportK_ne_univ_iff {W F : Set (S n)} (hW : IsCorpsConvexeS n W) (hF : IsFacetteK W F) :
    supportK F ≠ univ ↔ F ≠ interior W := by
  exact not_congr ⟨fun h => (isFacetteK_supportK_eq_univ_iff hW).1 ⟨hF, h⟩,
    fun h => ((isFacetteK_supportK_eq_univ_iff hW).2 h).2⟩

/-- **Prop. 10, every conical facette but the interior one** (`bzprop:c3s4p10_contingent_conique`,
not marked, OQ-169 (a)): `Benzecri.prop10_contingent_conique` with « `F ≠ int W` » in place of
`supportK F ≠ univ`. -/
theorem prop10_contingent_conique_of_ne_interior {W F : Set (S n)} (hW : IsCorpsConvexeS n W)
    (hF : IsFacetteConique W F) (hFi : F ≠ interior W) {a : S n} (ha : a ∈ F) :
    (IsConvexPart (contingent W a) ∧
      linearSubvariety (Submodule.span ℝ (Sphere.F F)) ⊆ contingent W a ∧
      quotientPreimage (Submodule.span ℝ (Sphere.F F))
        (quotientImage (Submodule.span ℝ (Sphere.F F)) (contingent W a)) = contingent W a) ∧
    (∃ m : ℕ, m + 1 + Module.finrank ℝ (Submodule.span ℝ (Sphere.F F)) = n + 1 ∧
      Nonempty (((Fin (n + 1) → ℝ) ⧸ Submodule.span ℝ (Sphere.F F)) ≃ₗ[ℝ] (Fin (m + 1) → ℝ))) ∧
    ∀ (m : ℕ) (e : ((Fin (n + 1) → ℝ) ⧸ Submodule.span ℝ (Sphere.F F)) ≃ₗ[ℝ] (Fin (m + 1) → ℝ)),
      IsCorpsConvexeS m
        (mapEquiv e '' quotientImage (Submodule.span ℝ (Sphere.F F)) (contingent W a)) := by
  exact prop10_contingent_conique hW hF ((supportK_ne_univ_iff hW hF.1).2 hFi) ha

namespace FacetteInterieureInstance

open FacetteDualeInstance FacetteConiqueInstance

/-- The interior of the closed triangle is a facette of support `S(2)`. -/
theorem interior_simplexS_facette :
    IsFacetteK (simplexS 2) (interior (simplexS 2)) ∧ supportK (interior (simplexS 2)) = univ := by
  exact (isFacetteK_supportK_eq_univ_iff isCorpsConvexeS_simplexS).2 rfl

/-- The vertex facette `{s(e₀)}` of the closed triangle is not its interior facette. -/
theorem vertex0_ne_interior : ({vertex0 2} : Set (S 2)) ≠ interior (simplexS 2) := by
  intro h
  exact supportK_vertex0_ne_univ (by rw [h]; exact interior_simplexS_facette.2)

/-- **The corollary's hypotheses hold** at the vertex of the closed triangle. -/
theorem prop10_of_ne_interior_instance :
    IsCorpsConvexeS 2 (simplexS 2) ∧ IsFacetteConique (simplexS 2) {vertex0 2} ∧
      ({vertex0 2} : Set (S 2)) ≠ interior (simplexS 2) :=
  ⟨isCorpsConvexeS_simplexS, isFacetteConique_vertex0, vertex0_ne_interior⟩

end FacetteInterieureInstance

end Benzecri
