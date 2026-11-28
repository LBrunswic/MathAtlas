import Benzecri.Chapter3.Facettes
import Benzecri.Chapter3.ConeAppui

/-!
# Chapter 3 § 1 (sphere) — α(k) and the k-facettes of a convex part of S(E), the noyau, and the transfers of Props. 2–4 and the Corollary

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 1, journal p. 262; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (checked against the scan, PDF p. 35).
Target T-bz-c3-facettes-sphere. Over an arbitrary real vector space `E`, no topology.

* **`bzdef:c3s1d4_facettes_sphere`** — `benzecri1960_ch3.tex:246` (Déf. 4, l.246–261) — the
  cone `kPrime k = F(k) ∪ {O}`, convex (`convex_kPrime`); the restriction of `α(k′)` to `F(k)` is
  a preorder (`alphaFPreorder`) compatible with the projection (`alphaW_kPrime_compat`); `AlphaK`,
  read on any representatives (`alphaK_iff`), the preorder `alphaKPreorder`; `FK` (an
  equivalence, `fkSetoid`), `facetteK`, `IsFacetteK` (the classes, `isFacetteK_iff_quotient`),
  `FacetteKLE`, well defined (`facetteKLE_iff_forall`), the order `facetteKPartialOrder`; the
  direct form `AlphaKDirect`, equivalent (`alphaK_iff_direct`, also `alphaK_iff_direct_any`).
  The k-facettes are the projections of the `k′`-facettes other than `{O}` (`isFacetteK_iff`,
  `facetteK_eq_ofCone`).
* **`bzdef:c3s1d5_noyau`** — `benzecri1960_ch3.tex:264` (Déf. 5, l.264–270) — the facette of
  `O` in `k′` is `k′ ∩ −k′` (`facetteOf_zero_kPrime`), a vector subspace `noyauSub`; `noyau`, a
  linear subvariety (`noyau_eq_linearSubvariety`), the points of `k` with their antipode
  (`noyau_eq`); `isStrictConvexPart_iff_noyau_eq_empty` (Chapter 1, Déf. 9).
* The p. 262 transfers (`benzecri1960_ch3.tex:274–278`, no label, OQ-160 (c)), through `k′`:
  Prop. 2 `alphaK_iff_mem_supportK`, Prop. 3 `facetteKLE_iff_supportK_subset`, `supportK_eq_iff`,
  Prop. 4 `facettesK_filtrant`, `facettesK_isDirected`, the Corollary `supportsK_filtrant`.
* Instances: the closed quarter arc of `S(1)` has exactly three k-facettes and an empty noyau
  (`FacettesSphereInstance.facettesK_arcS1`, `facettesK_arcS1_distinct`, `noyau_arcS1`); the
  noyau of a closed hemisphere is its boundary great sphere (`noyau_closedHemisphere`).

> **Définition 4.** Soit $k$ une partie convexe de $S(E)$; $k'=F(k)+\{O\}$ est un convexe de $E$;
> $\alpha(k')$ (*cf.* § 1, déf. 1) induit sur $F(k)$ une relation de préordre compatible avec la
> projection sur $k$. Nous noterons $\alpha(k)$ la relation de préordre ainsi définie sur $k$.
> La relation d'équivalence associée à la relation $\alpha(k)$ se note $F(\alpha(k))$; les classes
> d'équivalence correspondantes sont appelées *$k$-facettes* et la relation de préordre $\alpha$
> définit canoniquement sur l'ensemble des facettes une relation d'ordre que nous noterons aussi
> $\alpha$. La relation $\alpha(k)$ peut être définie directement : $a\,\alpha(k)\,b$ s'il existe
> un segment $(a', b)\subset k$ tel que $a\in)a', b($ ou si $a$ et $b$ sont identiques ou
> diamétralement opposés.
>
> **Définition 5.** Soit $L$ le sous-espace vectoriel facette de $O$ dans le convexe
> $k'=F(k)+\{O\}$; la projection sur $k$ de $L-\{O\}$ est une sous-variété linéaire,
> éventuellement vide, ensemble de tous les points de $S(E)$ qui appartiennent à $k$ avec leur
> point diamétralement opposé. Cette sous-variété est appelée le *noyau* de $k$. Un convexe
> strict est un convexe de noyau vide (*cf.* § 1, déf. 9).
>
> Les propositions 2, 3, 4 et le corollaire sont valables pour les convexes de $S(E)$.

## The proofs formalized

`k′` is a convex cone, so a point of `k′` and its positive multiples lie in one `k′`-facette
(`fw_kPrime_smul`): that is the compatibility with the projection, and every `k′`-facette is a
cone (`isPosCone_facetteOf_kPrime`). The direct form, forward: if `a ≠ ±b`, the end
`A + ε(A − B)` of the extension of `(b, a)` beyond `a` is not `O` nor opposite to `b`
(independence of `A`, `B`), and its segment to `B` lies in `k′`; backward, a segment of `k`
lifts to a segment of `k′`. The support of a k-facette (`supportK`, the least linear
subvariety containing it, `subset_supportK`, `supportK_subset`) is the projection of the affine
support of the `k′`-facette, which contains `O` and is a vector subspace
(`coe_affineSpan_facetteOf`); Props. 2–3 and the Corollary then come from the strict
`Chapter3/Facettes` through `k′`. Prop. 4: the printed midpoint of `A`, `A′`, unless it is `O`
(`a′ = −a`), where `a` itself is below both (`a α(k) −a`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $E$ » (a real vector space, § 1) | ✓ carried: `[AddCommGroup E] [Module ℝ E]`, any dimension, no topology |
| « $k$ une partie convexe de $S(E)$ » | ✓ carried: `IsConvexPart k` (Ch. 1 Déf. 8, DEC-120's `∪` reading of `+`) where used; the relations are defined for every `k` |
| « $k'=F(k)+\{O\}$ » | ✓ carried: `kPrime k = insert 0 (F k)` (DEC-120) |
| Déf. 4: « compatible avec la projection » | ✓ carried: `alphaW_kPrime_compat`, any representatives |
| Déf. 4, direct form: « un segment $(a', b)\subset k$ » | ✓ carried: Ch. 1 Déf. 7's `closedSeg a' b` with `a' ≠ −b` (`AlphaKDirect`); the same relation without `a' ≠ −b` (`alphaK_iff_direct_any`) |
| Déf. 4, direct form: « identiques ou diamétralement opposés » | ✓ carried: `a, b ∈ k` and `a = b ∨ a = −b` (a relation on `k`) |
| Déf. 5: « $L$ le sous-espace vectoriel facette de $O$ » | ✓ carried: `noyauSub` has carrier `facetteOf (kPrime k) 0` |
| Déf. 5: « convexe strict » (*cf.* § 1, déf. 9) | ✓ carried: Chapter 1's `IsStrictConvexPart` (OQ-160 (b)) |
| transfers: « support » of a k-facette | reading: `supportK f`, the least linear subvariety of `S(E)` containing `f` |

## SCOPE (disclosed)

* Two forced readings, not narrowings: in Déf. 4's direct form « a et b identiques ou
  diamétralement opposés » is read with `a, b ∈ k` (otherwise the clause relates points outside
  `k` and the claimed equivalence fails); Déf. 5's « cf. § 1, déf. 9 » is Chapter 1 Déf. 9
  (`IsStrictConvexPart`), as the transcription's `\ref` already says (OQ-160 (b)).
* Nothing is omitted; no `sorry`. Déf. 4's « relation d'ordre » on k-facettes is
  `FacetteKLE` (some, equivalently every, pair of representatives).
* « $F(\alpha(k))$ » is named `FK` (`F` is the correspondence of Chapter 1 Déf. 3).
* The transfers of p. 262 carry no label (OQ-160 (c)); they are proved here as lemmas. Prop. 1's
  transfer (finest locally convex topology) waits on T-bz-c3-facette-ouverte; Déf. 6 and the
  transfers of Props. 5–6 are T-bz-c3-appui-sphere's.
* The noyau, when nonempty, is the greatest k-facette (`isFacetteK_noyau`, `facetteKLE_noyau`);
  when empty, the `k′`-facette `{O}` has no k-facette (`isFacetteK_iff` excludes it), which is
  Déf. 6's « facette de dimension (−1) » remark (not this target).
* General lemmas proved here (`smul_mem_kPrime`, `add_mem_kPrime`,
  `ofCone_subset_of_subset_kPrime`, `isConvexPart_closedHemisphere`) may move upstream.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set
open scoped Pointwise

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The cone `k′ = F(k) + {O}` -/

/-- **`k′ = F(k) + {O}`** (Déf. 4), in DEC-120's reading of `+` (OQ-24): `F(k) ∪ {O}`. -/
def kPrime (k : Set (Sphere E)) : Set E := insert 0 (F k)

/-- « $k'$ est un convexe de $E$ »: this is Déf. 8 of Chapter 1. -/
theorem convex_kPrime {k : Set (Sphere E)} (hk : IsConvexPart k) : Convex ℝ (kPrime k) := hk

theorem zero_mem_kPrime (k : Set (Sphere E)) : (0 : E) ∈ kPrime k := mem_insert _ _

theorem mem_kPrime_of_ne {k : Set (Sphere E)} {v : E} (hv : v ≠ 0) :
    v ∈ kPrime k ↔ v ∈ F k :=
  ⟨fun h => (mem_insert_iff.1 h).resolve_left hv, mem_insert_of_mem _⟩

theorem smul_mem_kPrime {k : Set (Sphere E)} {v : E} (hv : v ∈ kPrime k) {c : ℝ} (hc : 0 ≤ c) :
    c • v ∈ kPrime k := by
  rcases mem_insert_iff.1 hv with rfl | hvF
  · rw [smul_zero]; exact zero_mem_kPrime k
  rcases hc.lt_or_eq with hc | rfl
  · exact mem_insert_of_mem _ (smul_mem_F hvF hc)
  · rw [zero_smul]; exact zero_mem_kPrime k

theorem add_mem_kPrime {k : Set (Sphere E)} (hk : IsConvexPart k) {v w : E}
    (hv : v ∈ kPrime k) (hw : w ∈ kPrime k) : v + w ∈ kPrime k := by
  have := convex_kPrime hk hv hw (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  convert smul_mem_kPrime this (by norm_num : (0 : ℝ) ≤ 2) using 1
  rw [smul_add, smul_smul, smul_smul]; norm_num

/-- Parts of `k′` project into `k`. -/
theorem ofCone_subset_of_subset_kPrime {k : Set (Sphere E)} {C : Set E} (h : C ⊆ kPrime k) :
    ofCone C ⊆ k := by
  intro x hx
  obtain ⟨v, hv, hvC, rfl⟩ := mem_ofCone.1 hx
  exact (mk_mem_iff_mem_F hv).2 ((mem_kPrime_of_ne hv).1 (h hvC))

theorem mem_kPrime_of_isRep {k : Set (Sphere E)} {a : Sphere E} {A : E} (hA : IsRep A a)
    (ha : a ∈ k) : A ∈ kPrime k := by
  obtain ⟨hA0, rfl⟩ := hA
  exact mem_insert_of_mem _ ⟨hA0, ha⟩

theorem mem_of_isRep_of_mem_kPrime {k : Set (Sphere E)} {a : Sphere E} {A : E} (hA : IsRep A a)
    (h : A ∈ kPrime k) : a ∈ k := by
  obtain ⟨hA0, rfl⟩ := hA
  exact (mk_mem_iff_mem_F hA0).2 ((mem_kPrime_of_ne hA0).1 h)

/-! ### Déf. 4 — α(k) through `k′` -/

/-- In `k′`, a point and its positive multiples are α-related. -/
theorem alphaW_kPrime_smul {k : Set (Sphere E)} (hk : IsConvexPart k) {A : E}
    (hA : A ∈ kPrime k) {c : ℝ} (hc : 0 < c) : AlphaW (kPrime k) A (c • A) := by
  refine (alphaW_iff_extend (convex_kPrime hk)).2 ⟨hA, smul_mem_kPrime hA hc.le, 1 / (2 * c),
    by positivity, ?_⟩
  convert smul_mem_kPrime hA (c := (c + 1) / (2 * c)) (by positivity) using 1
  match_scalars
  field_simp
  ring

/-- In `k′`, a point and its positive multiples lie in the same facette. -/
theorem fw_kPrime_smul {k : Set (Sphere E)} (hk : IsConvexPart k) {A : E}
    (hA : A ∈ kPrime k) {c : ℝ} (hc : 0 < c) : FW (kPrime k) A (c • A) := by
  refine ⟨alphaW_kPrime_smul hk hA hc, ?_⟩
  have := alphaW_kPrime_smul hk (smul_mem_kPrime hA hc.le) (inv_pos.2 hc)
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this

/-- The facettes of `k′` are stable under the positive homotheties. -/
theorem isPosCone_facetteOf_kPrime {k : Set (Sphere E)} (hk : IsConvexPart k) (A : E) :
    IsPosCone (facetteOf (kPrime k) A) := fun _ hc _ hB =>
  FW.trans (convex_kPrime hk) hB (fw_kPrime_smul hk hB.1.mem_right hc)

theorem alphaW_kPrime_of_smul {k : Set (Sphere E)} (hk : IsConvexPart k) {A B : E}
    (h : AlphaW (kPrime k) A B) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    AlphaW (kPrime k) (c • A) (d • B) :=
  alphaW_trans (convex_kPrime hk) (fw_kPrime_smul hk h.mem_left hc).2
    (alphaW_trans (convex_kPrime hk) h (fw_kPrime_smul hk h.mem_right hd).1)

/-- **Déf. 4, « compatible avec la projection sur $k$ »**: `α(k′)` on `F(k)` depends only on the
rays. -/
theorem alphaW_kPrime_compat {k : Set (Sphere E)} (hk : IsConvexPart k) {A A' B B' : E}
    (hA : A ≠ 0) (hA' : A' ≠ 0) (hB : B ≠ 0) (hB' : B' ≠ 0) (h₁ : mk A hA = mk A' hA')
    (h₂ : mk B hB = mk B' hB') :
    AlphaW (kPrime k) A B ↔ AlphaW (kPrime k) A' B' := by
  obtain ⟨c, hc, rfl⟩ := (mk_eq_mk_iff_exists_pos hA hA').1 h₁
  obtain ⟨d, hd, rfl⟩ := (mk_eq_mk_iff_exists_pos hB hB').1 h₂
  refine ⟨fun h => alphaW_kPrime_of_smul hk h hc hd, fun h => ?_⟩
  have := alphaW_kPrime_of_smul hk h (inv_pos.2 hc) (inv_pos.2 hd)
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hc.ne', inv_mul_cancel₀ hd.ne', one_smul,
    one_smul] at this

/-- **Déf. 4, « $\alpha(k')$ induit sur $F(k)$ une relation de préordre »**. -/
@[reducible] def alphaFPreorder {k : Set (Sphere E)} (hk : IsConvexPart k) : Preorder (F k) where
  le A B := AlphaW (kPrime k) A B
  le_refl A := alphaW_refl (mem_insert_of_mem _ A.2)
  le_trans _ _ _ h₁ h₂ := alphaW_trans (convex_kPrime hk) h₁ h₂

/-- **Déf. 4, `α(k)`**: the relation induced on `k` by `α(k′)` through the projection (read on the
chosen representatives; any representatives give the same relation, `alphaK_iff`). -/
def AlphaK (k : Set (Sphere E)) (a b : Sphere E) : Prop :=
  AlphaW (kPrime k) (Module.Ray.someVector a) (Module.Ray.someVector b)

theorem exists_isRep_someVector (a : Sphere E) : IsRep (Module.Ray.someVector a) a :=
  ⟨Module.Ray.someVector_ne_zero a, mk_someVector a⟩

/-- `α(k)` read on any representatives. -/
theorem alphaK_iff {k : Set (Sphere E)} (hk : IsConvexPart k) {a b : Sphere E} {A B : E}
    (hA : IsRep A a) (hB : IsRep B b) : AlphaK k a b ↔ AlphaW (kPrime k) A B := by
  obtain ⟨hA0, rfl⟩ := hA
  obtain ⟨hB0, rfl⟩ := hB
  exact alphaW_kPrime_compat hk _ hA0 _ hB0 (mk_someVector _) (mk_someVector _)

theorem AlphaK.mem_left {k : Set (Sphere E)} {a b : Sphere E} (h : AlphaK k a b) : a ∈ k :=
  mem_of_isRep_of_mem_kPrime (exists_isRep_someVector a) (AlphaW.mem_left h)

theorem AlphaK.mem_right {k : Set (Sphere E)} {a b : Sphere E} (h : AlphaK k a b) : b ∈ k :=
  mem_of_isRep_of_mem_kPrime (exists_isRep_someVector b) (AlphaW.mem_right h)

theorem alphaK_refl {k : Set (Sphere E)} {a : Sphere E} (ha : a ∈ k) : AlphaK k a a :=
  alphaW_refl (mem_kPrime_of_isRep (exists_isRep_someVector a) ha)

theorem alphaK_trans {k : Set (Sphere E)} (hk : IsConvexPart k) {a b c : Sphere E}
    (h₁ : AlphaK k a b) (h₂ : AlphaK k b c) : AlphaK k a c :=
  alphaW_trans (convex_kPrime hk) h₁ h₂

/-- **Déf. 4, « la relation de préordre ainsi définie sur $k$ »**. -/
@[reducible] def alphaKPreorder {k : Set (Sphere E)} (hk : IsConvexPart k) : Preorder k where
  le a b := AlphaK k a b
  le_refl a := alphaK_refl a.2
  le_trans _ _ _ h₁ h₂ := alphaK_trans hk h₁ h₂

/-! ### Déf. 4 — the direct form -/

/-- **Déf. 4, the direct form**: `a α(k) b` iff there is a segment `(a′, b) ⊆ k` (Déf. 7 of
Chapter 1: `a′`, `b` not diametrically opposite) with `a ∈ )a′, b(`, or `a`, `b` (points of
`k`) are identical or diametrically opposite. -/
def AlphaKDirect (k : Set (Sphere E)) (a b : Sphere E) : Prop :=
  (∃ a' : Sphere E, a' ≠ -b ∧ closedSeg a' b ⊆ k ∧ a ∈ openSeg a' b) ∨
    (a ∈ k ∧ b ∈ k ∧ (a = b ∨ a = -b))

/-- A segment `(a′, b) ⊆ k` with `a ∈ )a′, b(` gives `a α(k) b` (any `a′`). -/
theorem alphaK_of_closedSeg {k : Set (Sphere E)} (hk : IsConvexPart k) {a a' b : Sphere E}
    (hs : closedSeg a' b ⊆ k) (ha : a ∈ openSeg a' b) : AlphaK k a b := by
  induction a' using ind with
  | h A' hA' =>
  induction b using ind with
  | h B hB =>
  rw [closedSeg_mk, segOf] at hs
  rw [openSeg_mk, openSegOf] at ha
  obtain ⟨z, hz, hzseg, rfl⟩ := mem_ofCone.1 ha
  have hseg : segment ℝ A' B ⊆ kPrime k := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact zero_mem_kPrime k
    · exact mem_insert_of_mem _ ⟨hv0, hs (mk_mem_ofCone hv0 hv)⟩
  exact (alphaK_iff hk (isRep_mk z hz) (isRep_mk B hB)).2
    (alphaW_iff_openSegment.2 ⟨A', hseg, hzseg⟩)

/-- Identical or diametrically opposite points of `k` are α(k)-related. -/
theorem alphaK_of_eq_or_neg {k : Set (Sphere E)} (hk : IsConvexPart k) {a b : Sphere E}
    (ha : a ∈ k) (hb : b ∈ k) (h : a = b ∨ a = -b) : AlphaK k a b := by
  rcases h with rfl | rfl
  · exact alphaK_refl ha
  · induction b using ind with
    | h B hB =>
    rw [neg_mk] at ha ⊢
    have hA := mem_kPrime_of_isRep (isRep_mk _ _) ha
    refine (alphaK_iff hk (isRep_mk _ _) (isRep_mk B hB)).2
      ((alphaW_iff_extend (convex_kPrime hk)).2
        ⟨hA, mem_kPrime_of_isRep (isRep_mk B hB) hb, 1, one_pos, ?_⟩)
    convert smul_mem_kPrime hA (c := 3) (by norm_num) using 1
    module

/-- The direct form, forward: from `a α(k) b`, the segment `(a′, b)` with `a′` the end of the
extension of `(b, a)` beyond `a`. -/
theorem alphaKDirect_of_alphaK {k : Set (Sphere E)} (hk : IsConvexPart k) {a b : Sphere E}
    (h : AlphaK k a b) : AlphaKDirect k a b := by
  have ha := h.mem_left
  have hb := h.mem_right
  by_cases h1 : a = b
  · exact Or.inr ⟨ha, hb, Or.inl h1⟩
  by_cases h2 : a = -b
  · exact Or.inr ⟨ha, hb, Or.inr h2⟩
  left
  induction a using ind with
  | h A hA =>
  induction b using ind with
  | h B hB =>
  have hAB := (alphaK_iff hk (isRep_mk A hA) (isRep_mk B hB)).1 h
  obtain ⟨-, hBk, ε, hε, hC⟩ := (alphaW_iff_extend (convex_kPrime hk)).1 hAB
  have hli : LinearIndependent ℝ ![B, A] :=
    linearIndependent_of_ne (isRep_mk B hB) (isRep_mk A hA) h1 h2
  have hC0 : A + ε • (A - B) ≠ 0 := by
    intro h0
    have := (LinearIndependent.pair_iff.1 hli) (-ε) (1 + ε) (by rw [← h0]; module)
    linarith [this.2]
  refine ⟨mk _ hC0, ?_, ?_, ?_⟩
  · rw [neg_mk]
    intro heq
    obtain ⟨c, hc, hcC⟩ := (mk_eq_mk_iff_exists_pos hC0 _).1 heq
    have := (LinearIndependent.pair_iff.1 hli) (1 - c * ε) (c * (1 + ε)) (by
      calc (1 - c * ε) • B + (c * (1 + ε)) • A = c • (A + ε • (A - B)) + B := by module
        _ = 0 := by rw [hcC, neg_add_cancel])
    nlinarith [this.2]
  · rw [closedSeg_mk]
    exact ofCone_subset_of_subset_kPrime ((convex_kPrime hk).segment_subset hC hBk)
  · rw [openSeg_mk]
    refine mk_mem_ofCone hA ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity,
      by field_simp, ?_⟩
    have h1 : (A + ε • (A - B)) + ε • B = (1 + ε) • A := by module
    rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, one_smul, ← smul_add, h1,
      inv_smul_smul₀ (by positivity)]

/-- **Déf. 4: the direct form defines `α(k)`.** -/
theorem alphaK_iff_direct {k : Set (Sphere E)} (hk : IsConvexPart k) {a b : Sphere E} :
    AlphaK k a b ↔ AlphaKDirect k a b :=
  ⟨alphaKDirect_of_alphaK hk, fun h => h.elim (fun ⟨_, _, hs, ha⟩ => alphaK_of_closedSeg hk hs ha)
    (fun ⟨ha, hb, h⟩ => alphaK_of_eq_or_neg hk ha hb h)⟩

/-- The direct form with the library's segment for every pair (antipodal `a′ = −b` allowed,
`closedSeg (−b) b = {−b, b}`): the same relation. -/
theorem alphaK_iff_direct_any {k : Set (Sphere E)} (hk : IsConvexPart k) {a b : Sphere E} :
    AlphaK k a b ↔ (∃ a' : Sphere E, closedSeg a' b ⊆ k ∧ a ∈ openSeg a' b) ∨
      (a ∈ k ∧ b ∈ k ∧ (a = b ∨ a = -b)) :=
  ⟨fun h => (alphaKDirect_of_alphaK hk h).imp (fun ⟨a', _, hs, ha⟩ => ⟨a', hs, ha⟩) id,
    fun h => h.elim (fun ⟨_, hs, ha⟩ => alphaK_of_closedSeg hk hs ha)
      (fun ⟨ha, hb, h⟩ => alphaK_of_eq_or_neg hk ha hb h)⟩

/-! ### Déf. 4 — the k-facettes and their order -/

/-- **Déf. 4, `F(α(k))`**: the equivalence relation associated with `α(k)`. -/
def FK (k : Set (Sphere E)) (a b : Sphere E) : Prop := AlphaK k a b ∧ AlphaK k b a

/-- The k-facette of `a`. -/
def facetteK (k : Set (Sphere E)) (a : Sphere E) : Set (Sphere E) := {b | FK k a b}

/-- **Déf. 4, the k-facettes**: the classes of `F(α(k))`. -/
def IsFacetteK (k f : Set (Sphere E)) : Prop := ∃ a ∈ k, f = facetteK k a

/-- **Déf. 4, the order α on k-facettes.** -/
def FacetteKLE (k f f' : Set (Sphere E)) : Prop := ∃ a ∈ f, ∃ a' ∈ f', AlphaK k a a'

/-- The set of k-facettes, as a type. -/
def FacetteK (k : Set (Sphere E)) : Type _ := {f : Set (Sphere E) // IsFacetteK k f}

theorem fk_refl {k : Set (Sphere E)} {a : Sphere E} (ha : a ∈ k) : FK k a a :=
  ⟨alphaK_refl ha, alphaK_refl ha⟩

/-- `F(α(k))` is an equivalence on the points of `k`. -/
def fkSetoid {k : Set (Sphere E)} (hk : IsConvexPart k) : Setoid k where
  r a b := FK k a b
  iseqv := ⟨fun a => fk_refl a.2, fun h => ⟨h.2, h.1⟩,
    fun h₁ h₂ => ⟨alphaK_trans hk h₁.1 h₂.1, alphaK_trans hk h₂.2 h₁.2⟩⟩

theorem mem_facetteK_self {k : Set (Sphere E)} {a : Sphere E} (ha : a ∈ k) : a ∈ facetteK k a :=
  fk_refl ha

theorem facetteK_eq_of_fk {k : Set (Sphere E)} (hk : IsConvexPart k) {a b : Sphere E}
    (h : FK k a b) : facetteK k a = facetteK k b := by
  ext c
  exact ⟨fun hc => ⟨alphaK_trans hk h.2 hc.1, alphaK_trans hk hc.2 h.1⟩,
    fun hc => ⟨alphaK_trans hk h.1 hc.1, alphaK_trans hk hc.2 h.2⟩⟩

theorem IsFacetteK.subset {k f : Set (Sphere E)} (hf : IsFacetteK k f) : f ⊆ k := by
  obtain ⟨a, -, rfl⟩ := hf
  exact fun b hb => hb.1.mem_right

theorem IsFacetteK.nonempty {k f : Set (Sphere E)} (hf : IsFacetteK k f) : f.Nonempty := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨a, mem_facetteK_self ha⟩

theorem IsFacetteK.eq_facetteK {k f : Set (Sphere E)} (hk : IsConvexPart k) (hf : IsFacetteK k f)
    {a : Sphere E} (ha : a ∈ f) : f = facetteK k a := by
  obtain ⟨b, -, rfl⟩ := hf
  exact facetteK_eq_of_fk hk ha

/-- The k-facettes are the classes of the setoid `fkSetoid`. -/
theorem isFacetteK_iff_quotient {k f : Set (Sphere E)} (hk : IsConvexPart k) :
    IsFacetteK k f ↔ ∃ q : Quotient (fkSetoid hk),
      f = Subtype.val '' {a : k | Quotient.mk (fkSetoid hk) a = q} := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Quotient.mk _ ⟨a, ha⟩, ?_⟩
    ext b
    constructor
    · intro hb
      exact ⟨⟨b, hb.1.mem_right⟩, Quotient.sound ⟨hb.2, hb.1⟩, rfl⟩
    · rintro ⟨b', hb', rfl⟩
      have := Quotient.exact hb'
      exact ⟨this.2, this.1⟩
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h a =>
      refine ⟨a, a.2, ?_⟩
      ext b
      constructor
      · rintro ⟨b', hb', rfl⟩
        have := Quotient.exact hb'
        exact ⟨this.2, this.1⟩
      · intro hb
        exact ⟨⟨b, hb.1.mem_right⟩, Quotient.sound ⟨hb.2, hb.1⟩, rfl⟩

/-- The k-facette of `a` is the projection of the `k′`-facette of a representative. -/
theorem facetteK_eq_ofCone {k : Set (Sphere E)} (hk : IsConvexPart k) {a : Sphere E} {A : E}
    (hA : IsRep A a) : facetteK k a = ofCone (facetteOf (kPrime k) A) := by
  ext x
  induction x using ind with
  | h X hX =>
  rw [mk_mem_ofCone_iff (isPosCone_facetteOf_kPrime hk A) hX]
  exact and_congr (alphaK_iff hk hA (isRep_mk X hX)) (alphaK_iff hk (isRep_mk X hX) hA)

theorem F_facetteK {k : Set (Sphere E)} (hk : IsConvexPart k) {a : Sphere E} {A : E}
    (hA : IsRep A a) : F (facetteK k a) = facetteOf (kPrime k) A \ {0} := by
  rw [facetteK_eq_ofCone hk hA, F_ofCone (isPosCone_facetteOf_kPrime hk A)]

/-- The k-facettes are the projections of the `k′`-facettes other than `{O}`. -/
theorem isFacetteK_iff {k f : Set (Sphere E)} (hk : IsConvexPart k) :
    IsFacetteK k f ↔ ∃ G, IsFacette (kPrime k) G ∧ G ≠ {0} ∧ f = ofCone G := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hA := exists_isRep_someVector a
    refine ⟨_, isFacette_facetteOf (mem_kPrime_of_isRep hA ha), fun h0 => ?_,
      facetteK_eq_ofCone hk hA⟩
    have := mem_facetteOf_self (mem_kPrime_of_isRep hA ha)
    rw [h0] at this
    exact hA.ne_zero this
  · rintro ⟨G, hG, hG0, rfl⟩
    obtain ⟨X, hXG, hX0⟩ : ∃ X ∈ G, X ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hG0 ((hG.nonempty.subset_singleton_iff).1 fun x hx => hne x hx)
    have hXk : X ∈ kPrime k := hG.subset hXG
    refine ⟨mk X hX0, mem_of_isRep_of_mem_kPrime (isRep_mk X hX0) hXk, ?_⟩
    rw [facetteK_eq_ofCone hk (isRep_mk X hX0), ← hG.eq_facetteOf (convex_kPrime hk) hXG]

theorem facetteKLE_iff_forall {k f f' : Set (Sphere E)} (hk : IsConvexPart k)
    (hf : IsFacetteK k f) (hf' : IsFacetteK k f') :
    FacetteKLE k f f' ↔ ∀ a ∈ f, ∀ a' ∈ f', AlphaK k a a' := by
  constructor
  · rintro ⟨a₀, ha₀, a₀', ha₀', h⟩ a ha a' ha'
    have h1 : FK k a₀ a := by rw [hf.eq_facetteK hk ha₀] at ha; exact ha
    have h2 : FK k a₀' a' := by rw [hf'.eq_facetteK hk ha₀'] at ha'; exact ha'
    exact alphaK_trans hk h1.2 (alphaK_trans hk h h2.1)
  · intro h
    obtain ⟨a, ha⟩ := hf.nonempty
    obtain ⟨a', ha'⟩ := hf'.nonempty
    exact ⟨a, ha, a', ha', h a ha a' ha'⟩

theorem FacetteKLE.antisymm {k f f' : Set (Sphere E)} (hk : IsConvexPart k)
    (hf : IsFacetteK k f) (hf' : IsFacetteK k f') (h : FacetteKLE k f f')
    (h' : FacetteKLE k f' f) : f = f' := by
  obtain ⟨a, ha⟩ := hf.nonempty
  obtain ⟨a', ha'⟩ := hf'.nonempty
  rw [hf.eq_facetteK hk ha, hf'.eq_facetteK hk ha']
  exact facetteK_eq_of_fk hk ⟨(facetteKLE_iff_forall hk hf hf').1 h a ha a' ha',
    (facetteKLE_iff_forall hk hf' hf).1 h' a' ha' a ha⟩

/-- **Déf. 4, « une relation d'ordre que nous noterons aussi α »** on the k-facettes. -/
@[reducible] def facetteKPartialOrder {k : Set (Sphere E)} (hk : IsConvexPart k) :
    PartialOrder (FacetteK k) where
  le f g := FacetteKLE k f.1 g.1
  le_refl f := by
    obtain ⟨a, ha⟩ := f.2.nonempty
    exact ⟨a, ha, a, ha, alphaK_refl (f.2.subset ha)⟩
  le_trans f g h hfg hgh := by
    obtain ⟨b, hb⟩ := g.2.nonempty
    obtain ⟨a, ha⟩ := f.2.nonempty
    obtain ⟨c, hc⟩ := h.2.nonempty
    exact ⟨a, ha, c, hc, alphaK_trans hk
      ((facetteKLE_iff_forall hk f.2 g.2).1 hfg a ha b hb)
      ((facetteKLE_iff_forall hk g.2 h.2).1 hgh b hb c hc)⟩
  le_antisymm f g h₁ h₂ := Subtype.ext (FacetteKLE.antisymm hk f.2 g.2 h₁ h₂)

/-! ### p. 262: Props. 2, 3, 4 and the Corollary for the convexes of S(E) -/

/-- The support of a part `f` of `S(E)`: the linear subvariety `s(span F(f) − {O})`. -/
def supportK (f : Set (Sphere E)) : Set (Sphere E) := linearSubvariety (Submodule.span ℝ (F f))

theorem subset_supportK (f : Set (Sphere E)) : f ⊆ supportK f := by
  intro x hx
  induction x using ind with
  | h X hX =>
  exact (mk_mem_linearSubvariety hX).2 (Submodule.subset_span ⟨hX, hx⟩)

/-- The support is the least linear subvariety containing `f`. -/
theorem supportK_subset {f : Set (Sphere E)} {L : Submodule ℝ E} (h : f ⊆ linearSubvariety L) :
    supportK f ⊆ linearSubvariety L :=
  ofCone_subset_ofCone (SetLike.coe_subset_coe.2 (Submodule.span_le.2
    fun _ ⟨hX, hXf⟩ => (mk_mem_linearSubvariety hX).1 (h hXf)))

/-- The support of a k-facette is the projection of the affine support of the `k′`-facette,
which is a vector subspace. -/
theorem coe_affineSpan_facetteOf {k : Set (Sphere E)} (hk : IsConvexPart k) {a : Sphere E}
    {A : E} (hA : IsRep A a) (ha : a ∈ k) :
    (affineSpan ℝ (facetteOf (kPrime k) A) : Set E) = Submodule.span ℝ (F (facetteK k a)) := by
  have hAG : A ∈ facetteOf (kPrime k) A := mem_facetteOf_self (mem_kPrime_of_isRep hA ha)
  have hpos := isPosCone_facetteOf_kPrime hk A
  rw [F_facetteK hk hA]
  set G := facetteOf (kPrime k) A
  have h0 : (0 : E) ∈ affineSpan ℝ G := by
    have e : (0 : E) = (-1 : ℝ) • ((2 : ℝ) • A -ᵥ A) +ᵥ A := by
      rw [vsub_eq_sub, vadd_eq_add]; module
    rw [e]
    exact AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ G) (-1 : ℝ)
      (subset_affineSpan ℝ G (hpos 2 two_pos A hAG)) (subset_affineSpan ℝ G hAG)
      (subset_affineSpan ℝ G hAG)
  have hspan : Submodule.span ℝ (G \ {0}) = Submodule.span ℝ G := by
    rw [← Submodule.span_insert_zero, Set.insert_sdiff_singleton, Submodule.span_insert_zero]
  have hle : Submodule.span ℝ G = vectorSpan ℝ G := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      have e : x = (2 : ℝ) • x -ᵥ x := by rw [vsub_eq_sub]; module
      rw [e]
      exact vsub_mem_vectorSpan ℝ (hpos 2 two_pos x hx) hx
    · rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact sub_mem (Submodule.subset_span hx) (Submodule.subset_span hy)
  ext v
  rw [SetLike.mem_coe, SetLike.mem_coe, hspan, hle]
  constructor
  · intro hv
    have := AffineSubspace.vsub_mem_direction hv h0
    rwa [direction_affineSpan, vsub_eq_sub, sub_zero] at this
  · intro hv
    have := AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan]) h0
    rwa [vadd_eq_add, add_zero] at this

/-- **Prop. 2 for S(E).** For `a` in a k-facette `f` of support `l` and `b ∈ k`:
`a α(k) b ↔ b ∈ l`. -/
theorem alphaK_iff_mem_supportK {k f : Set (Sphere E)} (hk : IsConvexPart k)
    (hf : IsFacetteK k f) {a b : Sphere E} (ha : a ∈ f) (hb : b ∈ k) :
    AlphaK k a b ↔ b ∈ supportK f := by
  have ha' : a ∈ k := hf.subset ha
  obtain ⟨A, hA⟩ := exists_isRep a
  have hAk := mem_kPrime_of_isRep hA ha'
  induction b using ind with
  | h B hB =>
  rw [alphaK_iff hk hA (isRep_mk B hB), hf.eq_facetteK hk ha, supportK,
    mk_mem_linearSubvariety hB, ← SetLike.mem_coe, ← coe_affineSpan_facetteOf hk hA ha',
    SetLike.mem_coe]
  exact alphaW_iff_mem_support (convex_kPrime hk) (isFacette_facetteOf hAk)
    (mem_facetteOf_self hAk) (mem_kPrime_of_isRep (isRep_mk B hB) hb)

/-- **Prop. 3 for S(E)**, first part: `f α f′ ↔ l′ ⊆ l`. -/
theorem facetteKLE_iff_supportK_subset {k f f' : Set (Sphere E)} (hk : IsConvexPart k)
    (hf : IsFacetteK k f) (hf' : IsFacetteK k f') :
    FacetteKLE k f f' ↔ supportK f' ⊆ supportK f := by
  obtain ⟨a, ha⟩ := hf.nonempty
  constructor
  · intro h
    have : f' ⊆ supportK f := fun b' hb' =>
      (alphaK_iff_mem_supportK hk hf ha (hf'.subset hb')).1
        ((facetteKLE_iff_forall hk hf hf').1 h a ha b' hb')
    exact supportK_subset (L := Submodule.span ℝ (F f)) this
  · intro h
    obtain ⟨a', ha'⟩ := hf'.nonempty
    exact ⟨a, ha, a', ha', (alphaK_iff_mem_supportK hk hf ha (hf'.subset ha')).2
      (h (subset_supportK f' ha'))⟩

/-- **Prop. 3 for S(E)**, second part: `l = l′ ↔ f = f′`. -/
theorem supportK_eq_iff {k f f' : Set (Sphere E)} (hk : IsConvexPart k)
    (hf : IsFacetteK k f) (hf' : IsFacetteK k f') : supportK f = supportK f' ↔ f = f' := by
  constructor
  · intro h
    exact FacetteKLE.antisymm hk hf hf' ((facetteKLE_iff_supportK_subset hk hf hf').2 h.ge)
      ((facetteKLE_iff_supportK_subset hk hf' hf).2 h.le)
  · rintro rfl; rfl

/-- **Prop. 4 for S(E).** The k-facettes, ordered by α, are directed downwards. -/
theorem facettesK_filtrant {k : Set (Sphere E)} (hk : IsConvexPart k) :
    DirectedOn (fun f g => FacetteKLE k g f) {f | IsFacetteK k f} := by
  intro f hf f' hf'
  obtain ⟨a, ha⟩ := hf.nonempty
  obtain ⟨a', ha'⟩ := hf'.nonempty
  have hak := hf.subset ha
  have hak' := hf'.subset ha'
  obtain ⟨A, hA⟩ := exists_isRep a
  obtain ⟨A', hA'⟩ := exists_isRep a'
  have hAk := mem_kPrime_of_isRep hA hak
  have hAk' := mem_kPrime_of_isRep hA' hak'
  by_cases hM : (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • A' = 0
  · -- the printed midpoint is `O`: `a′ = −a`, and `a` itself is below both
    have hneg : a = -a' := by
      obtain ⟨hA0, rfl⟩ := hA
      obtain ⟨hA0', rfl⟩ := hA'
      have h2 : (1 / 2 : ℝ) • (A + A') = 0 := by rw [smul_add]; exact hM
      have hAA : A = -A' :=
        eq_neg_of_add_eq_zero_left ((smul_eq_zero.1 h2).resolve_left (by norm_num))
      subst hAA
      rw [neg_mk]
    exact ⟨facetteK k a, ⟨a, hak, rfl⟩, ⟨a, mem_facetteK_self hak, a, ha, alphaK_refl hak⟩,
      ⟨a, mem_facetteK_self hak, a', ha', alphaK_of_eq_or_neg hk hak hak' (Or.inr hneg)⟩⟩
  · have hMk : (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • A' ∈ kPrime k :=
      convex_kPrime hk hAk hAk' (by norm_num) (by norm_num) (by norm_num)
    have hm := mem_of_isRep_of_mem_kPrime (isRep_mk _ hM) hMk
    refine ⟨facetteK k (mk _ hM), ⟨_, hm, rfl⟩,
      ⟨_, mem_facetteK_self hm, a, ha,
        (alphaK_iff hk (isRep_mk _ hM) hA).2 (alphaW_midpoint (convex_kPrime hk) hAk hAk')⟩,
      ⟨_, mem_facetteK_self hm, a', ha', (alphaK_iff hk (isRep_mk _ hM) hA').2 ?_⟩⟩
    have := alphaW_midpoint (convex_kPrime hk) hAk' hAk
    rwa [add_comm] at this

/-- Prop. 4 for S(E) on the ordered set of k-facettes. -/
theorem facettesK_isDirected {k : Set (Sphere E)} (hk : IsConvexPart k) :
    letI := facetteKPartialOrder hk; IsDirected (FacetteK k) (· ≥ ·) := by
  letI := facetteKPartialOrder hk
  refine ⟨fun f g => ?_⟩
  obtain ⟨h, hh, h1, h2⟩ := facettesK_filtrant hk f.1 f.2 g.1 g.2
  exact ⟨⟨h, hh⟩, h1, h2⟩

/-- The supports of the k-facettes. -/
def supportsFacettesK (k : Set (Sphere E)) : Set (Set (Sphere E)) :=
  {l | ∃ f, IsFacetteK k f ∧ l = supportK f}

/-- **The Corollary for S(E).** The supports of k-facettes are directed upwards for inclusion. -/
theorem supportsK_filtrant {k : Set (Sphere E)} (hk : IsConvexPart k) :
    DirectedOn (· ⊆ ·) (supportsFacettesK k) := by
  rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
  obtain ⟨f'', hf'', h1, h2⟩ := facettesK_filtrant hk f hf f' hf'
  exact ⟨_, ⟨f'', hf'', rfl⟩, (facetteKLE_iff_supportK_subset hk hf'' hf).1 h1,
    (facetteKLE_iff_supportK_subset hk hf'' hf').1 h2⟩

/-! ### Déf. 5 — the noyau -/

/-- The facette of `O` in `k′` is `k′ ∩ −k′`. -/
theorem facetteOf_zero_kPrime {k : Set (Sphere E)} (hk : IsConvexPart k) :
    facetteOf (kPrime k) 0 = kPrime k ∩ -kPrime k := by
  ext B
  simp only [facetteOf, mem_setOf_eq, FW, mem_inter_iff, Set.mem_neg]
  rw [alphaW_iff_extend (convex_kPrime hk), alphaW_iff_extend (convex_kPrime hk)]
  constructor
  · rintro ⟨⟨-, hB, ε, hε, h1⟩, -⟩
    refine ⟨hB, ?_⟩
    have := smul_mem_kPrime h1 (inv_pos.2 hε).le
    rwa [zero_add, zero_sub, smul_smul, inv_mul_cancel₀ hε.ne', one_smul] at this
  · rintro ⟨hB, hB'⟩
    refine ⟨⟨zero_mem_kPrime k, hB, 1, one_pos, by simpa using hB'⟩,
      ⟨hB, zero_mem_kPrime k, 1, one_pos, ?_⟩⟩
    convert smul_mem_kPrime hB (c := 2) (by norm_num) using 1
    module

/-- **Déf. 5, « le sous-espace vectoriel facette de $O$ dans le convexe $k'$ »**: the facette of
`O` in `k′` is a vector subspace `L`. -/
def noyauSub {k : Set (Sphere E)} (hk : IsConvexPart k) : Submodule ℝ E where
  carrier := facetteOf (kPrime k) 0
  add_mem' {x y} hx hy := by
    have hx' : x ∈ kPrime k ∩ -kPrime k := by rw [← facetteOf_zero_kPrime hk]; exact hx
    have hy' : y ∈ kPrime k ∩ -kPrime k := by rw [← facetteOf_zero_kPrime hk]; exact hy
    show x + y ∈ facetteOf (kPrime k) 0
    rw [facetteOf_zero_kPrime hk, mem_inter_iff, Set.mem_neg, neg_add]
    rw [mem_inter_iff, Set.mem_neg] at hx' hy'
    exact ⟨add_mem_kPrime hk hx'.1 hy'.1, add_mem_kPrime hk hx'.2 hy'.2⟩
  zero_mem' := fw_refl (zero_mem_kPrime k)
  smul_mem' c x hx := by
    have hx' : x ∈ kPrime k ∩ -kPrime k := by rw [← facetteOf_zero_kPrime hk]; exact hx
    show c • x ∈ facetteOf (kPrime k) 0
    rw [facetteOf_zero_kPrime hk, mem_inter_iff, Set.mem_neg]
    rw [mem_inter_iff, Set.mem_neg] at hx'
    rcases le_total 0 c with hc | hc
    · exact ⟨smul_mem_kPrime hx'.1 hc, by rw [← smul_neg]; exact smul_mem_kPrime hx'.2 hc⟩
    · refine ⟨?_, ?_⟩
      · have := smul_mem_kPrime hx'.2 (neg_nonneg.2 hc)
        rwa [smul_neg, neg_smul, neg_neg] at this
      · have := smul_mem_kPrime hx'.1 (neg_nonneg.2 hc)
        rwa [neg_smul] at this

theorem coe_noyauSub {k : Set (Sphere E)} (hk : IsConvexPart k) :
    (noyauSub hk : Set E) = facetteOf (kPrime k) 0 := rfl

/-- **Déf. 5, the noyau of `k`**: the projection on `k` of `L − {O}`, `L` the facette of `O` in
`k′`. -/
def noyau (k : Set (Sphere E)) : Set (Sphere E) := ofCone (facetteOf (kPrime k) 0)

/-- **Déf. 5, « est une sous-variété linéaire »**. -/
theorem noyau_eq_linearSubvariety {k : Set (Sphere E)} (hk : IsConvexPart k) :
    noyau k = linearSubvariety (noyauSub hk) := rfl

theorem noyau_subset {k : Set (Sphere E)} : noyau k ⊆ k :=
  ofCone_subset_of_subset_kPrime fun _ hB => AlphaW.mem_right hB.1

/-- **Déf. 5, « ensemble de tous les points de $S(E)$ qui appartiennent à $k$ avec leur point
diamétralement opposé »**. -/
theorem noyau_eq {k : Set (Sphere E)} (hk : IsConvexPart k) :
    noyau k = {m | m ∈ k ∧ -m ∈ k} := by
  ext x
  induction x using ind with
  | h v hv =>
  rw [noyau, mk_mem_ofCone_iff (isPosCone_facetteOf_kPrime hk 0) hv, facetteOf_zero_kPrime hk,
    mem_inter_iff, Set.mem_neg, mem_kPrime_of_ne hv, mem_kPrime_of_ne (neg_ne_zero.2 hv),
    mem_setOf_eq, neg_mk, mk_mem_iff_mem_F, mk_mem_iff_mem_F]

/-- **Déf. 5, « Un convexe strict est un convexe de noyau vide »** (Chapter 1, Déf. 9). -/
theorem isStrictConvexPart_iff_noyau_eq_empty {k : Set (Sphere E)} :
    IsStrictConvexPart k ↔ IsConvexPart k ∧ noyau k = ∅ := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rw [noyau_eq h.1, eq_empty_iff_forall_notMem]
    rintro m ⟨hm, hm'⟩
    exact h.2 m hm hm'
  · rintro ⟨hk, h⟩
    refine ⟨hk, fun m hm hm' => ?_⟩
    rw [noyau_eq hk] at h
    exact (eq_empty_iff_forall_notMem.1 h) m ⟨hm, hm'⟩

/-- When nonempty, the noyau is a k-facette, the greatest one for α. -/
theorem isFacetteK_noyau {k : Set (Sphere E)} (hk : IsConvexPart k) (hn : (noyau k).Nonempty) :
    IsFacetteK k (noyau k) := by
  obtain ⟨m, hm⟩ := hn
  have hmk := noyau_subset hm
  obtain ⟨v, hv, hvN, rfl⟩ := mem_ofCone.1 hm
  refine ⟨mk v hv, hmk, ?_⟩
  rw [facetteK_eq_ofCone hk (isRep_mk v hv), noyau, facetteOf_eq_of_fw (convex_kPrime hk) hvN]

theorem facetteKLE_noyau {k f : Set (Sphere E)} (hk : IsConvexPart k) (hf : IsFacetteK k f)
    (hn : (noyau k).Nonempty) : FacetteKLE k f (noyau k) := by
  obtain ⟨a, ha⟩ := hf.nonempty
  obtain ⟨m, hm⟩ := hn
  refine ⟨a, ha, m, hm, ?_⟩
  obtain ⟨v, hv, hvN, rfl⟩ := mem_ofCone.1 hm
  obtain ⟨A, hA⟩ := exists_isRep a
  have hAk := mem_kPrime_of_isRep hA (hf.subset ha)
  rw [alphaK_iff hk hA (isRep_mk v hv)]
  refine alphaW_trans (convex_kPrime hk) ?_ hvN.1
  refine (alphaW_iff_extend (convex_kPrime hk)).2 ⟨hAk, zero_mem_kPrime k, 1, one_pos, ?_⟩
  convert smul_mem_kPrime hAk (c := 2) (by norm_num) using 1
  module

/-- The closed hemisphere is a convex part. -/
theorem isConvexPart_closedHemisphere (l : Module.Dual ℝ E) :
    IsConvexPart (closedHemisphere l) := by
  unfold IsConvexPart closedHemisphere
  rw [F_ofCone (isPosCone_nonneg l), Set.insert_sdiff_singleton,
    Set.insert_eq_of_mem (by simp)]
  intro x hx y hy a b ha hb _
  simp only [mem_setOf_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

/-- **Instance of Déf. 5**: the noyau of the closed hemisphere `{l ≥ 0}` is its boundary great
sphere `s(ker l − {O})` (a hyperplane of `S(E)` when `l ≠ 0`). -/
theorem noyau_closedHemisphere (l : Module.Dual ℝ E) :
    noyau (closedHemisphere l) = linearSubvariety (LinearMap.ker l) := by
  rw [noyau_eq (isConvexPart_closedHemisphere l)]
  ext x
  induction x using ind with
  | h v hv =>
  rw [mem_setOf_eq, neg_mk, mk_mem_closedHemisphere, mk_mem_closedHemisphere,
    mk_mem_linearSubvariety hv, LinearMap.mem_ker, map_neg]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; rw [h]; simp

end Sphere

/-! ### The instance on `S(1)`: the closed quarter arc -/

namespace FacettesSphereInstance

open Sphere ConeAppuiInstance

/-- The end `b = s(e₁)` of the arc. -/
def b1 : S 1 := mk e1 e1_ne_zero

theorem eq_zero_of_coords {v : Fin 2 → ℝ} (h0 : v 0 = 0) (h1 : v 1 = 0) : v = 0 := by
  ext i; fin_cases i <;> simp [h0, h1]

/-- The closed quadrant. -/
def quadrant : Set (Fin 2 → ℝ) := {v | 0 ≤ v 0 ∧ 0 ≤ v 1}

theorem isPosCone_quadrant : IsPosCone quadrant := fun c hc v hv => by
  simp only [quadrant, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
  exact ⟨mul_nonneg hc.le hv.1, mul_nonneg hc.le hv.2⟩

theorem convex_quadrant : Convex ℝ quadrant := by
  intro x hx y hy a b ha hb _
  simp only [quadrant, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  exact ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)⟩

/-- The quarter arc is the projection of the quadrant. -/
theorem arcS1_eq : arcS1 = ofCone quadrant := by
  rw [arcS1, a0, closedSeg_mk, segOf]
  apply Subset.antisymm
  · apply ofCone_subset_ofCone
    rintro _ ⟨s, t, hs, ht, -, rfl⟩
    simp [quadrant, e0, e1, hs, ht]
  · apply ofCone_subset_of_forall
    rintro x ⟨h0, h1⟩ hx
    have hpos : 0 < x 0 + x 1 := by
      rcases h0.lt_or_eq with h | h
      · linarith
      rcases h1.lt_or_eq with h' | h'
      · linarith
      exact absurd (eq_zero_of_coords h.symm h'.symm) hx
    refine ⟨x 0 + x 1, hpos, (x 0 / (x 0 + x 1)) • e0 + (x 1 / (x 0 + x 1)) • e1,
      ⟨_, _, by positivity, by positivity, by field_simp, rfl⟩, ?_⟩
    ext i; fin_cases i <;> simp [e0, e1] <;> field_simp

/-- `k′` for the quarter arc is the closed quadrant. -/
theorem kPrime_arcS1 : kPrime arcS1 = quadrant := by
  rw [kPrime, arcS1_eq, F_ofCone isPosCone_quadrant, Set.insert_sdiff_singleton,
    Set.insert_eq_of_mem (by simp [quadrant])]

theorem mk_mem_arcS1_iff {v : Fin 2 → ℝ} (hv : v ≠ 0) : mk v hv ∈ arcS1 ↔ 0 ≤ v 0 ∧ 0 ≤ v 1 := by
  rw [mk_mem_iff_mem_F, ← mem_kPrime_of_ne hv, kPrime_arcS1]; rfl

/-- α in the quadrant: `A α B` iff every coordinate vanishing at `A` vanishes at `B`. -/
theorem alphaW_quadrant_iff {A B : Fin 2 → ℝ} :
    AlphaW quadrant A B ↔
      (0 ≤ A 0 ∧ 0 ≤ A 1) ∧ (0 ≤ B 0 ∧ 0 ≤ B 1) ∧ (A 0 = 0 → B 0 = 0) ∧
        (A 1 = 0 → B 1 = 0) := by
  rw [alphaW_iff_extend convex_quadrant]
  simp only [quadrant, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  constructor
  · rintro ⟨hA, hB, ε, hε, h0, h1⟩
    refine ⟨hA, hB, fun h => ?_, fun h => ?_⟩
    · rw [h] at h0; nlinarith [hB.1]
    · rw [h] at h1; nlinarith [hB.2]
  · rintro ⟨hA, hB, h0, h1⟩
    have hc : ∀ i, 0 ≤ A i → 0 < (if A i = 0 then (1 : ℝ) else A i) := fun i hi => by
      split_ifs with h
      · norm_num
      · exact lt_of_le_of_ne hi (Ne.symm h)
    set m := min (if A 0 = 0 then (1 : ℝ) else A 0) (if A 1 = 0 then (1 : ℝ) else A 1) with hm
    have hm0 : 0 < m := lt_min (hc 0 hA.1) (hc 1 hA.2)
    have hD : 0 < 1 + B 0 + B 1 := by linarith [hB.1, hB.2]
    have hε0 : 0 < m / (1 + B 0 + B 1) := div_pos hm0 hD
    have key : ∀ i, 0 ≤ A i → 0 ≤ B i → B i ≤ 1 + B 0 + B 1 → (A i = 0 → B i = 0) →
        m ≤ (if A i = 0 then 1 else A i) → 0 ≤ A i + m / (1 + B 0 + B 1) * (A i - B i) := by
      intro i hAi hBi hBD himp hmi
      by_cases hz : A i = 0
      · rw [hz, himp hz]; simp
      · rw [if_neg hz] at hmi
        have : m / (1 + B 0 + B 1) * B i ≤ m := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hD]
          exact mul_le_mul_of_nonneg_left hBD hm0.le
        nlinarith [mul_nonneg hε0.le hAi]
    exact ⟨hA, hB, _, hε0, key 0 hA.1 hB.1 (by linarith [hB.2]) h0 (min_le_left _ _),
      key 1 hA.2 hB.2 (by linarith [hB.1]) h1 (min_le_right _ _)⟩

theorem mk_mem_facetteK_arcS1 {v w : Fin 2 → ℝ} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk w hw ∈ facetteK arcS1 (mk v hv) ↔ (0 ≤ v 0 ∧ 0 ≤ v 1) ∧ (0 ≤ w 0 ∧ 0 ≤ w 1) ∧
      (v 0 = 0 ↔ w 0 = 0) ∧ (v 1 = 0 ↔ w 1 = 0) := by
  show FK arcS1 _ _ ↔ _
  rw [FK, alphaK_iff isConvexPart_arcS1 (isRep_mk v hv) (isRep_mk w hw),
    alphaK_iff isConvexPart_arcS1 (isRep_mk w hw) (isRep_mk v hv), kPrime_arcS1,
    alphaW_quadrant_iff, alphaW_quadrant_iff]
  tauto

theorem mk_eq_a0_iff {w : Fin 2 → ℝ} (hw : w ≠ 0) : mk w hw = a0 ↔ 0 < w 0 ∧ w 1 = 0 := by
  rw [a0, mk_eq_mk_iff_exists_pos hw e0_ne_zero]
  constructor
  · rintro ⟨c, hc, h⟩
    have h0 : c * w 0 = 1 := by simpa [e0] using congrFun h 0
    have h1 : c * w 1 = 0 := by simpa [e0] using congrFun h 1
    exact ⟨by nlinarith, (mul_eq_zero.1 h1).resolve_left hc.ne'⟩
  · rintro ⟨h0, h1⟩
    refine ⟨1 / w 0, by positivity, ?_⟩
    ext i; fin_cases i
    · simp [e0]; field_simp
    · simp [e0, h1]

theorem mk_eq_b1_iff {w : Fin 2 → ℝ} (hw : w ≠ 0) : mk w hw = b1 ↔ w 0 = 0 ∧ 0 < w 1 := by
  rw [b1, mk_eq_mk_iff_exists_pos hw e1_ne_zero]
  constructor
  · rintro ⟨c, hc, h⟩
    have h0 : c * w 0 = 0 := by simpa [e1] using congrFun h 0
    have h1 : c * w 1 = 1 := by simpa [e1] using congrFun h 1
    exact ⟨(mul_eq_zero.1 h0).resolve_left hc.ne', by nlinarith⟩
  · rintro ⟨h0, h1⟩
    refine ⟨1 / w 1, by positivity, ?_⟩
    ext i; fin_cases i
    · simp [e1, h0]
    · simp [e1]; field_simp

theorem mk_mem_openSeg_iff {w : Fin 2 → ℝ} (hw : w ≠ 0) :
    mk w hw ∈ openSeg a0 b1 ↔ 0 < w 0 ∧ 0 < w 1 := by
  rw [a0, b1, openSeg_mk, openSegOf, mem_ofCone]
  constructor
  · rintro ⟨z, hz, ⟨s, t, hs, ht, -, rfl⟩, hzw⟩
    obtain ⟨c, hc, hcz⟩ := (mk_eq_mk_iff_exists_pos hz hw).1 hzw
    have h0 : c * s = w 0 := by simpa [e0, e1] using congrFun hcz 0
    have h1 : c * t = w 1 := by simpa [e0, e1] using congrFun hcz 1
    exact ⟨by rw [← h0]; positivity, by rw [← h1]; positivity⟩
  · rintro ⟨h0, h1⟩
    have hS : 0 < w 0 + w 1 := by linarith
    have hy0 : ((w 0 / (w 0 + w 1)) • e0 + (w 1 / (w 0 + w 1)) • e1) 0 = w 0 / (w 0 + w 1) := by
      simp [e0, e1]
    have hpos : 0 < w 0 / (w 0 + w 1) := by positivity
    have hy : (w 0 / (w 0 + w 1)) • e0 + (w 1 / (w 0 + w 1)) • e1 ≠ 0 := fun h => by
      rw [h, Pi.zero_apply] at hy0; linarith
    refine ⟨_, hy, ⟨_, _, by positivity, by positivity, by field_simp, rfl⟩, ?_⟩
    rw [mk_eq_mk_iff_exists_pos hy hw]
    refine ⟨w 0 + w 1, hS, ?_⟩
    ext i; fin_cases i <;> simp [e0, e1] <;> field_simp

/-- The k-facette of a point of the arc. -/
theorem facetteK_arcS1_eq {v : Fin 2 → ℝ} (hv : v ≠ 0) (hx : 0 ≤ v 0 ∧ 0 ≤ v 1) :
    facetteK arcS1 (mk v hv) =
      if v 0 = 0 then {b1} else if v 1 = 0 then {a0} else openSeg a0 b1 := by
  ext y
  induction y using ind with
  | h w hw =>
  rw [mk_mem_facetteK_arcS1]
  split_ifs with h0 h1
  · have hv1 : 0 < v 1 := lt_of_le_of_ne hx.2 fun h => hv (eq_zero_of_coords h0 h.symm)
    rw [mem_singleton_iff, mk_eq_b1_iff]
    constructor
    · rintro ⟨-, hw', e0', e1'⟩
      exact ⟨e0'.1 h0, lt_of_le_of_ne hw'.2 fun h => hv1.ne' (e1'.2 h.symm)⟩
    · rintro ⟨hw0, hw1⟩
      exact ⟨hx, ⟨hw0.ge, hw1.le⟩, ⟨fun _ => hw0, fun _ => h0⟩,
        ⟨fun h => absurd h hv1.ne', fun h => absurd h hw1.ne'⟩⟩
  · have hv0 : 0 < v 0 := lt_of_le_of_ne hx.1 (Ne.symm h0)
    rw [mem_singleton_iff, mk_eq_a0_iff]
    constructor
    · rintro ⟨-, hw', e0', e1'⟩
      exact ⟨lt_of_le_of_ne hw'.1 fun h => hv0.ne' (e0'.2 h.symm), e1'.1 h1⟩
    · rintro ⟨hw0, hw1⟩
      exact ⟨hx, ⟨hw0.le, hw1.ge⟩, ⟨fun h => absurd h hv0.ne', fun h => absurd h hw0.ne'⟩,
        ⟨fun _ => hw1, fun _ => h1⟩⟩
  · have hv0 : 0 < v 0 := lt_of_le_of_ne hx.1 (Ne.symm h0)
    have hv1 : 0 < v 1 := lt_of_le_of_ne hx.2 (Ne.symm h1)
    rw [mk_mem_openSeg_iff]
    constructor
    · rintro ⟨-, hw', e0', e1'⟩
      exact ⟨lt_of_le_of_ne hw'.1 fun h => h0 (e0'.2 h.symm),
        lt_of_le_of_ne hw'.2 fun h => h1 (e1'.2 h.symm)⟩
    · rintro ⟨hw0, hw1⟩
      exact ⟨hx, ⟨hw0.le, hw1.le⟩, ⟨fun h => absurd h h0, fun h => absurd h hw0.ne'⟩,
        ⟨fun h => absurd h h1, fun h => absurd h hw1.ne'⟩⟩

/-- **Instance of Déf. 4**: the quarter arc has exactly three k-facettes, its two ends and the
open arc. -/
theorem facettesK_arcS1 :
    {f | IsFacetteK arcS1 f} = {{a0}, {b1}, openSeg a0 b1} := by
  ext f
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    induction x using ind with
    | h v hv =>
    rw [mk_mem_arcS1_iff] at hx
    rw [facetteK_arcS1_eq hv hx]
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  · have he0 : (0 ≤ e0 0 ∧ 0 ≤ e0 1) := by simp [e0]
    have he1 : (0 ≤ e1 0 ∧ 0 ≤ e1 1) := by simp [e1]
    have hs : e0 + e1 ≠ 0 := fun h => by simpa [e0, e1] using congrFun h 0
    have hse : (0 ≤ (e0 + e1) 0 ∧ 0 ≤ (e0 + e1) 1) := by simp [e0, e1]
    rintro (rfl | rfl | rfl)
    · refine ⟨a0, (mk_mem_arcS1_iff e0_ne_zero).2 he0, ?_⟩
      rw [a0, facetteK_arcS1_eq e0_ne_zero he0]
      simp [e0]; rfl
    · refine ⟨b1, (mk_mem_arcS1_iff e1_ne_zero).2 he1, ?_⟩
      rw [b1, facetteK_arcS1_eq e1_ne_zero he1]
      simp [e1]; rfl
    · refine ⟨mk _ hs, (mk_mem_arcS1_iff hs).2 hse, ?_⟩
      rw [facetteK_arcS1_eq hs hse]
      simp [e0, e1]

/-- The three k-facettes of the arc are distinct. -/
theorem facettesK_arcS1_distinct :
    ({a0} : Set (S 1)) ≠ {b1} ∧ ({a0} : Set (S 1)) ≠ openSeg a0 b1 ∧
      ({b1} : Set (S 1)) ≠ openSeg a0 b1 := by
  have ha0 : a0 ∉ openSeg a0 b1 := by
    show mk e0 e0_ne_zero ∉ openSeg a0 b1
    rw [mk_mem_openSeg_iff]; simp [e0]
  have hb1 : b1 ∉ openSeg a0 b1 := by
    show mk e1 e1_ne_zero ∉ openSeg a0 b1
    rw [mk_mem_openSeg_iff]; simp [e1]
  refine ⟨fun h => ?_, fun h => ha0 (h ▸ rfl), fun h => hb1 (h ▸ rfl)⟩
  have : a0 = b1 := Set.singleton_eq_singleton_iff.1 h
  rw [a0, mk_eq_b1_iff] at this
  simp [e0] at this

/-- **Instance of Déf. 5**: the noyau of the arc is empty. -/
theorem noyau_arcS1 : noyau arcS1 = ∅ := by
  rw [noyau_eq isConvexPart_arcS1, eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hx'⟩
  induction x using ind with
  | h v hv =>
  rw [neg_mk, mk_mem_arcS1_iff] at hx'
  rw [mk_mem_arcS1_iff] at hx
  simp only [Pi.neg_apply, neg_nonneg] at hx'
  exact hv (eq_zero_of_coords (le_antisymm hx'.1 hx.1) (le_antisymm hx'.2 hx.2))

end FacettesSphereInstance

end Benzecri
