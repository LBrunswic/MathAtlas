import Benzecri.Chapter3.Appui
import Benzecri.Chapter3.DualiteSn

/-!
# Chapter 3 § 1 (sphere) — variétés d'appui of a convex part of S(E) (Déf. 6), the noyau is one, and the transfers of Props. 5 and 6

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 1, journal p. 262; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR, OQ-160).
Target T-bz-c3-appui-sphere. Over an arbitrary real vector space `E`, no topology.

* **`bzdef:c3s1d6_variete_appui_sphere`** — `benzecri1960_ch3.tex:283` (Déf. 6, l.283–287; the
  commentary l.289–290) — `Benzecri.Sphere.IsVarieteAppuiK`, read through a subspace
  (`isVarieteAppuiK_linearSubvariety_iff`, the subspace is unique: `linearSubvariety_injective`),
  and directly on `S(E)` (`isVarieteAppuiK_iff_alphaK`); « le noyau de $k$ est une variété
  d'appui de $k$ » `isVarieteAppuiK_noyau`; « si ce noyau est vide, il constitue une variété
  d'appui, ou encore une facette, de $k$ de dimension $(-1)$ » `noyau_eq_empty_facette_dim`,
  `isVarieteAppuiK_empty_iff`, the facettes in the extended sense `IsFacetteKExt`
  (`isFacetteKExt_iff`).
* The transfers of l.292–293 (no label, OQ-160 (c)), through `k′`: Prop. 5
  `exists_facetteKExt_supportK_inter_eq` (the paper's hypothesis),
  `exists_facetteKExt_supportK_inter_eq_of_finiteDimensional` (only `l ∩ k` finite-dimensional),
  `exists_facetteK_supportK_inter_eq` (a genuine k-facette when `l ∩ k ≠ ∅`); Prop. 6
  `alphaK_inter_iff`, `alphaK_induit`, and its proof's consequence `facetteK_inter_eq`.
* Instances (the closed quarter arc `ConeAppuiInstance.arcS1` of `S(1)`): the line `ℝe₀` gives the
  variété d'appui `{s(e₀), −s(e₀)}` (`AppuiSphereInstance.isVarieteAppuiK_lineE0`,
  `lineE0_eq`, `lineE0_inter_arcS1`), the diagonal line does not
  (`AppuiSphereInstance.diag_not_isVarieteAppuiK`); `∅` is a variété d'appui of the arc
  (`AppuiSphereInstance.isVarieteAppuiK_empty_arcS1`), met by no genuine k-facette
  (`supportK_inter_nonempty_of_isFacetteK`), so that Prop. 5 on `S(E)` needs the facette of
  dimension `−1`.

> **Définition 6.** Une variété linéaire $l$ est dite *variété d'appui pour $k$* s'il existe un
> sous-espace vectoriel $L$ de $E$, variété d'appui de $F(k)+\{O\}$, et
> $l=F^{-1}(L-\{O\})$.
>
> En particulier, le noyau de $k$ est une variété d'appui de $k$. Si ce noyau est vide, il
> constitue une variété d'appui, ou encore une facette, de $k$ de dimension $(-1)$.
>
> Les propositions 5 et 6 sont également valables pour les convexes de $S(E)$.

## The proofs formalized

`l = F⁻¹(L − {O})` is the projection `linearSubvariety L` of `L − {O}`. Déf. 6 asks `L` to be a
variété d'appui (Déf. 3, strict `Chapter3/Appui`) of the convex cone `k′ = kPrime k`. Since
`O ∈ L ∩ k′`, the non-emptiness of Déf. 3 always holds; the saturation at `O` says the facette of
`O` in `k′` lies in `L`, i.e. `noyau k ⊆ l`; at the other points of `L ∩ k′` it is the
saturation of `l ∩ k` for `α(k)` (`alphaK_iff`). The noyau is the projection of the subspace
`noyauSub`, the facette of `O`, which is saturated. When the noyau is empty, the facette of `O`
in `k′` is `{O}`, projecting to `∅`, of dimension `dimS ∅ = −1` (strict `Chapter3/DualiteSn`).
Prop. 5: the strict `exists_facette_support_inter_eq_of_finiteDimensional` on `k′` gives a
`k′`-facette `G` with `aff(G) ∩ k′ = L ∩ k′`; `G` is a cone, so `aff(G) = span G` and the support
of `ofCone G` is `s(span G − {O})`. When `G = {O}` that facette of `S(E)` is `∅`, the facette of
dimension `−1`. Prop. 6: `kPrime (k ∩ l) = k′ ∩ L` and the strict `alphaW_inter_iff`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $k$ » a convex part of $S(E)$ (§ 1, Déf. 4) | ✓ carried: `IsConvexPart k` where used; `IsVarieteAppuiK` is defined for every `k` |
| « une variété linéaire $l$ » | ✓ carried: `l = linearSubvariety L` (Chapter 1 Déf. 4) is part of the definition |
| « un sous-espace vectoriel $L$ de $E$, variété d'appui de $F(k)+\{O\}$ » | ✓ carried: `L : Submodule ℝ E`, `IsVarieteAppui (kPrime k) L` (Déf. 3, `kPrime k = F(k) ∪ {O}`, DEC-120) |
| « $l=F^{-1}(L-\{O\})$ » | ✓ carried: `l = linearSubvariety L = ofCone L` |
| « une facette, de $k$ de dimension $(-1)$ » | reading: the projection `ofCone G` of a `k′`-facette `G` (`IsFacetteKExt`); `G = {O}` gives `∅`, `dimS ∅ = −1` |
| Prop. 5: « $W$ … dont le support $E$ est de dimension finie » | ✓ carried: `FiniteDimensional ℝ (span ℝ (F k))` (the support `supportK k` of `k`); ⚠ weakened in the second form (only `l ∩ k`) |
| Prop. 5: « une facette $F$ dont le support $S$ » | reading: a facette in the extended sense (`IsFacetteKExt`), support `supportK`; a genuine k-facette when `l ∩ k ≠ ∅` |
| Prop. 6: « $W'=W\cap L\neq\emptyset$ » ([sic] « $=\emptyset$ ») | ⚠ weakened: `alphaK_inter_iff` holds without it; `alphaK_induit` carries it as read |

## SCOPE (disclosed)

* « une facette de $k$ de dimension $(-1)$ »: the k-facettes of Déf. 4 (`IsFacetteK`) are
  nonempty, so `∅` is a facette only under the convention the sentence introduces. We read it as:
  the facettes of `k` are the projections of the facettes of `k′`, the empty one being the
  projection of `{O}` (`IsFacetteKExt`, `isFacetteKExt_iff`). Prop. 5 on `S(E)` holds in this
  sense and fails for genuine k-facettes exactly when `l ∩ k = ∅` (the arc and `l = ∅`).
* « Les propositions 5 et 6 sont également valables »: no ledger row (OQ-160 (c)); proved here as
  lemmas, with the strict `Chapter3/Appui` read through `k′`. Prop. 6 keeps the affine
  `[sic]` reading « $\neq\emptyset$ ».
* The support of a part of `S(E)` is `supportK` (strict `Chapter3/FacettesSphere`), the least
  linear subvariety containing it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Déf. 6 -/

/-- **Déf. 6.** `l` is a *variété d'appui* of `k ⊆ S(E)`: there is a vector subspace `L` of `E`,
variété d'appui (Déf. 3) of `k′ = F(k) + {O}`, with `l = F⁻¹(L − {O})`. -/
def IsVarieteAppuiK (k l : Set (Sphere E)) : Prop :=
  ∃ L : Submodule ℝ E, IsVarieteAppui (kPrime k) L.toAffineSubspace ∧ l = linearSubvariety L

theorem ofCone_singleton_zero : ofCone ({0} : Set E) = ∅ := by
  ext x
  simp only [mem_ofCone, mem_singleton_iff, mem_empty_iff_false, iff_false]
  rintro ⟨v, hv, rfl, -⟩
  exact hv rfl

theorem mem_linearSubvariety_of_isRep {L : Submodule ℝ E} {a : Sphere E} {A : E}
    (hA : IsRep A a) : a ∈ linearSubvariety L ↔ A ∈ L := by
  obtain ⟨hA0, rfl⟩ := hA
  exact mk_mem_linearSubvariety hA0

/-- The noyau is empty exactly when the facette of `O` in `k′` is `{O}`. -/
theorem noyau_eq_empty_iff {k : Set (Sphere E)} :
    noyau k = ∅ ↔ facetteOf (kPrime k) 0 = {0} := by
  constructor
  · intro h
    ext B
    rw [mem_singleton_iff]
    constructor
    · intro hB
      by_contra hB0
      have : mk B hB0 ∈ noyau k := mk_mem_ofCone hB0 hB
      rw [h] at this
      exact this
    · rintro rfl
      exact mem_facetteOf_self (zero_mem_kPrime k)
  · intro h
    rw [noyau, h, ofCone_singleton_zero]

/-- The subspace of Déf. 6 is that of `l`. -/
theorem isVarieteAppuiK_linearSubvariety_iff {k : Set (Sphere E)} {L : Submodule ℝ E} :
    IsVarieteAppuiK k (linearSubvariety L) ↔ IsVarieteAppui (kPrime k) L.toAffineSubspace := by
  refine ⟨fun ⟨M, hM, hLM⟩ => ?_, fun h => ⟨L, h, rfl⟩⟩
  obtain rfl := linearSubvariety_injective hLM
  exact hM

/-- **Déf. 6, directly on `S(E)`**: `l` is a linear subvariety containing the noyau, and
`a ∈ l ∩ k`, `a α(k) b` imply `b ∈ l`. -/
theorem isVarieteAppuiK_iff_alphaK {k l : Set (Sphere E)} (hk : IsConvexPart k) :
    IsVarieteAppuiK k l ↔ (∃ L : Submodule ℝ E, l = linearSubvariety L) ∧ noyau k ⊆ l ∧
      ∀ ⦃a b : Sphere E⦄, a ∈ l ∩ k → AlphaK k a b → b ∈ l := by
  have hW := convex_kPrime hk
  constructor
  · rintro ⟨L, hL, rfl⟩
    have hα := ((isVarieteAppui_iff_alphaW hW).1 hL).2
    have h0 : (0 : E) ∈ ((L.toAffineSubspace : AffineSubspace ℝ E) : Set E) ∩ kPrime k :=
      ⟨Submodule.mem_toAffineSubspace.2 L.zero_mem, zero_mem_kPrime k⟩
    refine ⟨⟨L, rfl⟩, ?_, ?_⟩
    · intro x hx
      obtain ⟨v, hv, hvN, rfl⟩ := mem_ofCone.1 hx
      exact (mk_mem_linearSubvariety hv).2 (Submodule.mem_toAffineSubspace.1 (hα h0 hvN.1).1)
    · rintro a b ⟨hal, hak⟩ hab
      have hA := exists_isRep_someVector a
      have hB := exists_isRep_someVector b
      have hAL : Module.Ray.someVector a ∈ L := (mem_linearSubvariety_of_isRep hA).1 hal
      have := hα ⟨Submodule.mem_toAffineSubspace.2 hAL, mem_kPrime_of_isRep hA hak⟩ hab
      exact (mem_linearSubvariety_of_isRep hB).2 (Submodule.mem_toAffineSubspace.1 this.1)
  · rintro ⟨⟨L, rfl⟩, hN, hsat⟩
    have h0 : (0 : E) ∈ ((L.toAffineSubspace : AffineSubspace ℝ E) : Set E) ∩ kPrime k :=
      ⟨Submodule.mem_toAffineSubspace.2 L.zero_mem, zero_mem_kPrime k⟩
    refine ⟨L, (isVarieteAppui_iff_alphaW hW).2 ⟨⟨0, h0⟩, ?_⟩, rfl⟩
    rintro A B ⟨hAL, hAk⟩ hAB
    refine ⟨Submodule.mem_toAffineSubspace.2 ?_, hAB.mem_right⟩
    have hAL' : A ∈ L := Submodule.mem_toAffineSubspace.1 hAL
    by_cases hB : B = 0
    · rw [hB]; exact L.zero_mem
    by_cases hA : A = 0
    · subst hA
      have hsp := (alphaW_iff_mem_support hW (isFacette_facetteOf (zero_mem_kPrime k))
        (mem_facetteOf_self (zero_mem_kPrime k)) hAB.mem_right).1 hAB
      have he : affineSpan ℝ (facetteOf (kPrime k) 0) = (noyauSub hk).toAffineSubspace :=
        AffineSubspace.affineSpan_coe (noyauSub hk).toAffineSubspace
      rw [he] at hsp
      have hBN : mk B hB ∈ noyau k := mk_mem_ofCone hB hsp
      exact (mk_mem_linearSubvariety hB).1 (hN hBN)
    · have hab : AlphaK k (mk A hA) (mk B hB) :=
        (alphaK_iff hk (isRep_mk A hA) (isRep_mk B hB)).2 hAB
      exact (mk_mem_linearSubvariety hB).1 (hsat ⟨(mk_mem_linearSubvariety hA).2 hAL',
        mem_of_isRep_of_mem_kPrime (isRep_mk A hA) hAk⟩ hab)

/-- **« le noyau de $k$ est une variété d'appui de $k$ »**. -/
theorem isVarieteAppuiK_noyau {k : Set (Sphere E)} (hk : IsConvexPart k) :
    IsVarieteAppuiK k (noyau k) := by
  refine ⟨noyauSub hk, ⟨⟨0, Submodule.mem_toAffineSubspace.2 (noyauSub hk).zero_mem,
    zero_mem_kPrime k⟩, fun A B hA hAB => ?_⟩, noyau_eq_linearSubvariety hk⟩
  have hA' : FW (kPrime k) 0 A := Submodule.mem_toAffineSubspace.1 hA.1
  exact ⟨Submodule.mem_toAffineSubspace.2 (FW.trans (convex_kPrime hk) hA' hAB),
    hAB.1.mem_right⟩

/-- `∅` is a variété d'appui of `k` exactly when the noyau is empty. -/
theorem isVarieteAppuiK_empty_iff {k : Set (Sphere E)} (hk : IsConvexPart k) :
    IsVarieteAppuiK k ∅ ↔ noyau k = ∅ := by
  rw [isVarieteAppuiK_iff_alphaK hk]
  constructor
  · rintro ⟨-, h, -⟩
    exact subset_empty_iff.1 h
  · intro h
    exact ⟨⟨⊥, linearSubvariety_bot.symm⟩, h ▸ subset_refl _, fun a _ hab => hab.1.elim⟩

/-- The facettes of `k` in the extended sense of l.289–290: the projections of the facettes of
`k′`; `{O}`, when it is one, projects to the facette `∅` of dimension `−1`. -/
def IsFacetteKExt (k f : Set (Sphere E)) : Prop :=
  ∃ G, IsFacette (kPrime k) G ∧ f = ofCone G

/-- The extended facettes are the k-facettes of Déf. 4, and `∅` when the noyau is empty. -/
theorem isFacetteKExt_iff {k f : Set (Sphere E)} (hk : IsConvexPart k) :
    IsFacetteKExt k f ↔ IsFacetteK k f ∨ (f = ∅ ∧ noyau k = ∅) := by
  constructor
  · rintro ⟨G, hG, rfl⟩
    by_cases hG0 : G = {0}
    · subst hG0
      refine Or.inr ⟨ofCone_singleton_zero, ?_⟩
      rw [noyau, ← hG.eq_facetteOf (convex_kPrime hk) (mem_singleton 0), ofCone_singleton_zero]
    · exact Or.inl ((isFacetteK_iff hk).2 ⟨G, hG, hG0, rfl⟩)
  · rintro (hf | ⟨rfl, hN⟩)
    · obtain ⟨G, hG, -, rfl⟩ := (isFacetteK_iff hk).1 hf
      exact ⟨G, hG, rfl⟩
    · refine ⟨{0}, ?_, ofCone_singleton_zero.symm⟩
      rw [← noyau_eq_empty_iff.1 hN]
      exact isFacette_facetteOf (zero_mem_kPrime k)

/-- **« Si ce noyau est vide, il constitue une variété d'appui, ou encore une facette, de $k$ de
dimension $(-1)$ »**: the noyau is a variété d'appui, the projection of the `k′`-facette `{O}`,
and has dimension `−1`. -/
theorem noyau_eq_empty_facette_dim {k : Set (Sphere E)} (hk : IsConvexPart k)
    (h : noyau k = ∅) :
    IsVarieteAppuiK k (noyau k) ∧ IsFacette (kPrime k) {0} ∧ noyau k = ofCone {0} ∧
      IsFacetteKExt k (noyau k) ∧ dimS (noyau k) = -1 := by
  refine ⟨isVarieteAppuiK_noyau hk, ?_, by rw [h, ofCone_singleton_zero],
    (isFacetteKExt_iff hk).2 (Or.inr ⟨h, h⟩), by rw [h]; exact dimS_empty⟩
  rw [← noyau_eq_empty_iff.1 h]
  exact isFacette_facetteOf (zero_mem_kPrime k)

/-- A genuine k-facette meets its support inside `k`. -/
theorem supportK_inter_nonempty_of_isFacetteK {k f : Set (Sphere E)} (hf : IsFacetteK k f) :
    (supportK f ∩ k).Nonempty := by
  obtain ⟨a, ha⟩ := hf.nonempty
  exact ⟨a, subset_supportK f ha, hf.subset ha⟩

/-! ### Prop. 5 for the convexes of `S(E)` -/

/-- The affine span of a nonempty positive cone is its linear span. -/
theorem coe_affineSpan_eq_span_of_isPosCone {G : Set E} (hG : IsPosCone G) (hne : G.Nonempty) :
    (affineSpan ℝ G : Set E) = Submodule.span ℝ G := by
  obtain ⟨A, hAG⟩ := hne
  have h0 : (0 : E) ∈ affineSpan ℝ G := by
    have e : (0 : E) = (-1 : ℝ) • ((2 : ℝ) • A -ᵥ A) +ᵥ A := by
      rw [vsub_eq_sub, vadd_eq_add]; module
    rw [e]
    exact AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ G) (-1 : ℝ)
      (subset_affineSpan ℝ G (hG 2 two_pos A hAG)) (subset_affineSpan ℝ G hAG)
      (subset_affineSpan ℝ G hAG)
  have hle : Submodule.span ℝ G = vectorSpan ℝ G := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      have e : x = (2 : ℝ) • x -ᵥ x := by rw [vsub_eq_sub]; module
      rw [e]
      exact vsub_mem_vectorSpan ℝ (hG 2 two_pos x hx) hx
    · rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact sub_mem (Submodule.subset_span hx) (Submodule.subset_span hy)
  ext v
  rw [SetLike.mem_coe, SetLike.mem_coe, hle]
  constructor
  · intro hv
    have := AffineSubspace.vsub_mem_direction hv h0
    rwa [direction_affineSpan, vsub_eq_sub, sub_zero] at this
  · intro hv
    have := AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan]) h0
    rwa [vadd_eq_add, add_zero] at this

/-- **Prop. 5 on `S(E)`**, under the weaker hypothesis that `l ∩ k` has a finite-dimensional
support: some facette `f` (extended sense) has a support `s` with `s ∩ k = l ∩ k`. -/
theorem exists_facetteKExt_supportK_inter_eq_of_finiteDimensional {k l : Set (Sphere E)}
    (hk : IsConvexPart k) (hl : IsVarieteAppuiK k l)
    (hfin : FiniteDimensional ℝ (Submodule.span ℝ (F (l ∩ k)))) :
    ∃ f, IsFacetteKExt k f ∧ supportK f ∩ k = l ∩ k := by
  obtain ⟨L, hL, rfl⟩ := hl
  have hW := convex_kPrime hk
  set T : Set E := ((L.toAffineSubspace : AffineSubspace ℝ E) : Set E) ∩ kPrime k with hT
  have hsub : T ⊆ insert 0 (F (linearSubvariety L ∩ k)) := by
    rintro x ⟨hxL, hxk⟩
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ⟨hx, (mk_mem_linearSubvariety hx).2 (Submodule.mem_toAffineSubspace.1 hxL),
        (mk_mem_iff_mem_F hx).2 ((mem_kPrime_of_ne hx).1 hxk)⟩
  have hfin' : FiniteDimensional ℝ (affineSpan ℝ T).direction := by
    have h1 := AffineSubspace.direction_le (affineSpan_le_toAffineSubspace_span (k := ℝ) (s := T))
    rw [Submodule.toAffineSubspace_direction] at h1
    exact Submodule.finiteDimensional_of_le (h1.trans ((Submodule.span_mono hsub).trans
      (by rw [Submodule.span_insert_zero])))
  obtain ⟨G, hG, -, hGL⟩ := exists_facette_support_inter_eq_of_finiteDimensional hW hL hfin'
  refine ⟨ofCone G, ⟨G, hG, rfl⟩, ?_⟩
  have hpos : IsPosCone G := by
    obtain ⟨A, -, rfl⟩ := hG
    exact isPosCone_facetteOf_kPrime hk A
  have hsupp : supportK (ofCone G) = linearSubvariety (Submodule.span ℝ G) := by
    rw [supportK, F_ofCone hpos, Submodule.span_sdiff_singleton_zero]
  ext x
  induction x using ind with
  | h X hX =>
  rw [mem_inter_iff, mem_inter_iff, hsupp, mk_mem_linearSubvariety, mk_mem_linearSubvariety,
    mk_mem_iff_mem_F hX, ← mem_kPrime_of_ne hX, ← SetLike.mem_coe,
    ← coe_affineSpan_eq_span_of_isPosCone hpos hG.nonempty]
  have := Set.ext_iff.1 hGL X
  rw [mem_inter_iff, mem_inter_iff] at this
  rw [this, SetLike.mem_coe, Submodule.mem_toAffineSubspace]

/-- **Prop. 5 on `S(E)`.** If the support of the convex `k` is finite-dimensional, for every
variété d'appui `l` some facette `f` (extended sense) has a support `s` with `s ∩ k = l ∩ k`. -/
theorem exists_facetteKExt_supportK_inter_eq {k : Set (Sphere E)} (hk : IsConvexPart k)
    (hfin : FiniteDimensional ℝ (Submodule.span ℝ (F k))) {l : Set (Sphere E)}
    (hl : IsVarieteAppuiK k l) :
    ∃ f, IsFacetteKExt k f ∧ supportK f ∩ k = l ∩ k := by
  haveI := hfin
  refine exists_facetteKExt_supportK_inter_eq_of_finiteDimensional hk hl
    (Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℝ (F k)) (Submodule.span_mono ?_))
  rintro v ⟨hv, h⟩
  exact ⟨hv, h.2⟩

/-- **Prop. 5 on `S(E)`**, with a genuine k-facette when `l ∩ k ≠ ∅`. -/
theorem exists_facetteK_supportK_inter_eq {k : Set (Sphere E)} (hk : IsConvexPart k)
    (hfin : FiniteDimensional ℝ (Submodule.span ℝ (F k))) {l : Set (Sphere E)}
    (hl : IsVarieteAppuiK k l) (hne : (l ∩ k).Nonempty) :
    ∃ f, IsFacetteK k f ∧ supportK f ∩ k = l ∩ k := by
  obtain ⟨f, hf, hfl⟩ := exists_facetteKExt_supportK_inter_eq hk hfin hl
  rcases (isFacetteKExt_iff hk).1 hf with hf | ⟨rfl, -⟩
  · exact ⟨f, hf, hfl⟩
  · exfalso
    rw [supportK, F_empty, Submodule.span_empty, linearSubvariety_bot, empty_inter] at hfl
    exact hne.ne_empty hfl.symm

/-! ### Prop. 6 for the convexes of `S(E)` -/

theorem kPrime_inter_linearSubvariety (k : Set (Sphere E)) (L : Submodule ℝ E) :
    kPrime (k ∩ linearSubvariety L) = kPrime k ∩ (L : Set E) := by
  ext v
  by_cases hv : v = 0
  · subst hv
    exact ⟨fun _ => ⟨zero_mem_kPrime k, L.zero_mem⟩, fun _ => zero_mem_kPrime _⟩
  · rw [mem_kPrime_of_ne hv, mem_inter_iff, mem_kPrime_of_ne hv, F_inter, mem_inter_iff,
      F_linearSubvariety]
    simp [hv]

theorem isConvexPart_inter_linearSubvariety {k : Set (Sphere E)} (hk : IsConvexPart k)
    (L : Submodule ℝ E) : IsConvexPart (k ∩ linearSubvariety L) := by
  show Convex ℝ (kPrime _)
  rw [kPrime_inter_linearSubvariety]
  exact (convex_kPrime hk).inter L.convex

/-- **Prop. 6 on `S(E)`** (no non-emptiness needed): `α(k ∩ l)` is the trace of `α(k)`. -/
theorem alphaK_inter_iff {k : Set (Sphere E)} (hk : IsConvexPart k) (L : Submodule ℝ E)
    {a b : Sphere E} :
    AlphaK (k ∩ linearSubvariety L) a b ↔
      a ∈ linearSubvariety L ∧ b ∈ linearSubvariety L ∧ AlphaK k a b := by
  have hA := exists_isRep_someVector a
  have hB := exists_isRep_someVector b
  show AlphaW (kPrime (k ∩ linearSubvariety L)) _ _ ↔ _
  rw [kPrime_inter_linearSubvariety, mem_linearSubvariety_of_isRep hA,
    mem_linearSubvariety_of_isRep hB]
  exact alphaW_inter_iff (convex_kPrime hk) L.toAffineSubspace

/-- **Prop. 6 on `S(E)`** as printed (the `[sic]` read « $k\cap l\neq\emptyset$ »): for `l` a
linear subvariety, `α(k ∩ l)` is induced by `α(k)`. -/
theorem alphaK_induit {k l : Set (Sphere E)} (hk : IsConvexPart k)
    (hl : ∃ L : Submodule ℝ E, l = linearSubvariety L) (_hne : (k ∩ l).Nonempty) :
    ∀ a ∈ k ∩ l, ∀ b ∈ k ∩ l, (AlphaK (k ∩ l) a b ↔ AlphaK k a b) := by
  obtain ⟨L, rfl⟩ := hl
  intro a ha b hb
  rw [alphaK_inter_iff hk L]
  exact ⟨fun h => h.2.2, fun h => ⟨ha.2, hb.2, h⟩⟩

/-- The consequence drawn in Prop. 6's proof, on `S(E)`: for `l` a variété d'appui of `k`, the
facette of `m ∈ l ∩ k` relative to `k` is its facette relative to `k ∩ l`. -/
theorem facetteK_inter_eq {k l : Set (Sphere E)} (hk : IsConvexPart k)
    (hl : IsVarieteAppuiK k l) {m : Sphere E} (hm : m ∈ k ∩ l) :
    facetteK (k ∩ l) m = facetteK k m := by
  have hsat := ((isVarieteAppuiK_iff_alphaK hk).1 hl).2.2
  obtain ⟨L, -, rfl⟩ := hl
  ext b
  simp only [facetteK, mem_setOf_eq, FK, alphaK_inter_iff hk L]
  constructor
  · rintro ⟨⟨-, -, h1⟩, -, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hb := hsat ⟨hm.2, hm.1⟩ h1
    exact ⟨⟨hm.2, hb, h1⟩, hb, hm.2, h2⟩

end Sphere

/-! ### Instances on `S(1)`: the closed quarter arc -/

namespace AppuiSphereInstance

open Sphere ConeAppuiInstance FacettesSphereInstance

/-- The line `ℝe₀` of `S(1)`: `s(ℝe₀ − {O})`. -/
def lineE0 : Set (S 1) := linearSubvariety (ℝ ∙ e0)

theorem lineE0_eq : lineE0 = {a0, -a0} := by
  exact linearSubvariety_span_singleton e0_ne_zero

/-- **Instance of Déf. 6**: `ℝe₀` gives a variété d'appui of the quarter arc. -/
theorem isVarieteAppuiK_lineE0 : IsVarieteAppuiK arcS1 lineE0 := by
  rw [isVarieteAppuiK_iff_alphaK isConvexPart_arcS1, noyau_arcS1]
  refine ⟨⟨_, rfl⟩, empty_subset _, ?_⟩
  rintro a b ⟨ha, -⟩ hab
  induction a using ind with
  | h v hv =>
  induction b using ind with
  | h w hw =>
  rw [alphaK_iff isConvexPart_arcS1 (isRep_mk v hv) (isRep_mk w hw), kPrime_arcS1,
    alphaW_quadrant_iff] at hab
  rw [lineE0, mk_mem_linearSubvariety, Submodule.mem_span_singleton] at ha ⊢
  obtain ⟨c, rfl⟩ := ha
  have hw1 : w 1 = 0 := hab.2.2.2 (by simp [e0])
  refine ⟨w 0, ?_⟩
  ext i; fin_cases i <;> simp [e0, hw1]

theorem lineE0_inter_arcS1 : lineE0 ∩ arcS1 = {a0} := by
  rw [lineE0_eq]
  ext x
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · rfl
    · exfalso
      rw [a0, neg_mk, mk_mem_arcS1_iff] at h
      simp [e0] at h
      linarith
  · rintro rfl
    exact ⟨Or.inl rfl, a0_mem_arcS1⟩

/-- **Instance of Déf. 6**: the diagonal line `ℝ(e₀ + e₁)` does not give a variété d'appui. -/
theorem diag_not_isVarieteAppuiK : ¬ IsVarieteAppuiK arcS1 (linearSubvariety (ℝ ∙ (e0 + e1))) := by
  intro h
  obtain ⟨-, -, hsat⟩ := (isVarieteAppuiK_iff_alphaK isConvexPart_arcS1).1 h
  have hs : e0 + e1 ≠ 0 := fun h => by simpa [e0, e1] using congrFun h 0
  have hal : mk (e0 + e1) hs ∈ linearSubvariety (ℝ ∙ (e0 + e1)) :=
    (mk_mem_linearSubvariety hs).2 (Submodule.mem_span_singleton_self _)
  have hak : mk (e0 + e1) hs ∈ arcS1 := (mk_mem_arcS1_iff hs).2 (by simp [e0, e1])
  have hab : AlphaK arcS1 (mk (e0 + e1) hs) a0 := by
    rw [a0, alphaK_iff isConvexPart_arcS1 (isRep_mk _ hs) (isRep_mk e0 e0_ne_zero), kPrime_arcS1,
      alphaW_quadrant_iff]
    simp [e0, e1]
  have h0 := hsat ⟨hal, hak⟩ hab
  rw [a0, mk_mem_linearSubvariety, Submodule.mem_span_singleton] at h0
  obtain ⟨c, hc⟩ := h0
  have h0' := congrFun hc 0
  have h1' := congrFun hc 1
  simp [e0, e1] at h0' h1'
  simp [h1'] at h0'

/-- **Instance of l.289–290**: the noyau of the arc is empty, so `∅` is a variété d'appui of it;
no genuine k-facette has a support meeting the arc in `∅`, so Prop. 5 on `S(E)` needs the facette
of dimension `−1`. -/
theorem isVarieteAppuiK_empty_arcS1 :
    IsVarieteAppuiK arcS1 ∅ ∧ ∀ f, IsFacetteK arcS1 f → supportK f ∩ arcS1 ≠ ∅ := by
  exact ⟨(isVarieteAppuiK_empty_iff isConvexPart_arcS1).2 noyau_arcS1,
    fun f hf => (supportK_inter_nonempty_of_isFacetteK hf).ne_empty⟩

end AppuiSphereInstance

end Benzecri
