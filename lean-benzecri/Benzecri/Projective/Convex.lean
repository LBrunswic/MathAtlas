import Benzecri.Projective.Subvariety
import Mathlib.Analysis.Convex.Body
import Mathlib.Geometry.Convex.Cone.Basic

/-!
# `Benzecri.Projective.Convex` — segments, convex parts, strict convex parts, convex bodies (Déf. 7, 8, 9, 11)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal pp. 235–236; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45g (wave 2, layer L2).

* **`bzdef:c1s1d7_segment`** — `benzecri1960_ch1.tex:234` (Déf. 7, l.234–244, p. 235): the closed
  and open segments `Benzecri.Sphere.closedSeg`, `Benzecri.Sphere.openSeg`, `s([M, M'])` and
  `s(]M, M'[)`; « le choix de $M$ et $M'$ est indifférent »: `closedSeg_mk`, `openSeg_mk` (for any
  representatives); for non-antipodal points `[M, M']` avoids `O` (`zero_notMem_segment`); why
  antipodal pairs are excluded: `closedSeg_neg_self` (the "segment" would be `{m, -m}`).
* **`bzdef:c1s1d8_partie_convexe`** — `benzecri1960_ch1.tex:246` (Déf. 8, l.246–253, p. 235),
  under DEC-120's ruling of OQ-24 (« $F(k)+\{O\}$ » is `F(k) ∪ {O}`, the period's `+` for a
  disjoint union): its first form is wave 1's `Sphere.IsConvexPart` (`F(k) ∪ {O}` convex), reused;
  its second form is `Sphere.IsSegConvex`; the two are proved EQUAL (`isConvexPart_iff_isSegConvex`),
  so the two sentences of Déf. 8 define one class. Remarks supporting the ruling: under the
  Minkowski reading (`IsConvexPartMinkowski`) the two sentences disagree (`isSegConvex_univ` against
  `not_isConvexPartMinkowski_univ`) and no part containing a nonzero linear subvariety is convex
  (`not_isConvexPartMinkowski_of_linearSubvariety_subset`), which would empty Déf. 10.
* **`bzdef:c1s1d9_convexe_strict`** — `benzecri1960_ch1.tex:255` (Déf. 9, l.255–258, p. 235):
  `Sphere.IsStrictConvexPart`. It does not depend on the reading of OQ-24 (now ruled, DEC-120): it is
  « `F(k)` convex »
  (`isStrictConvexPart_iff_convex_F`), the same notion over the segment form
  (`isStrictConvexPart_iff_isSegConvex`) and over the Minkowski reading
  (`isStrictConvexPart_iff_minkowski`); and it is the salience of the cone `F(k) ∪ {O}`
  (`IsConvexPart.salient_cone_iff`, Mathlib's `ConvexCone.Salient`).
* **`bzdef:c1s1d11_corps_convexe`** — `benzecri1960_ch1.tex:285` (Déf. 11, l.285–292, p. 236):
  `Benzecri.IsCorpsConvexe` (ℝⁿ), `Benzecri.IsCorpsConvexeS` (`S(n)`, through Déf. 9 only, hence
  independent of OQ-24: `isCorpsConvexeS_iff`), the sets `EA n`, `ES n` (the paper's `E(n)`),
  `CA n`; `mem_EA_iff_convexBody` (Mathlib's `ConvexBody` lacks the interior condition).
* The prose of pp. 235–236 (`benzecri1960_ch1.tex:269–272`, no label): `K(E)`, `C(E)`
  (`Sphere.KE`, `Sphere.CE`) and `K(S(E))`, `C(S(E))` (`Sphere.KS`, `Sphere.CS`, over Déf. 8 in
  DEC-120's `∪` reading).

> **Déf. 7.** Soient $m$, $m'$ deux points *non diamétralement opposés* de $S(E)$, nous allons
> définir le segment de droite fermé $(m, m')$.
> Soient $M$, $M'$ deux points de $E-\{O\}$ appartenant à l'image réciproque de $m$ et $m'$
> respectivement; on pose $(m, m')=s(M, M')$. Il est clair que le choix de $M$ et $M'$ est
> indifférent. On définit de même le segment ouvert $)m, m'($.
>
> **Déf. 8.** On appelle *partie convexe* $k\subset S(E)$ une partie $k$ telle que $F(k)+\{O\}$
> soit un convexe de $E$.
> Une partie convexe de $S(E)$ est une partie $k$ de $S(E)$ telle que, quels que soient $m$ et
> $m'$ non diamétralement opposés dans $k$, le segment $(m, m')$ soit inclus dans $k$.
>
> **Déf. 9.** Une partie convexe de $S(E)$ est dite *stricte* si elle ne contient pas de couples de
> points diamétralement opposés.
>
> **Déf. 11.** On appelle *corps convexe* de $\R^n$ [resp. $S(n)$] un convexe de $\R^n$ [resp. un
> convexe strict de $S(n)$] qui est compact et d'intérieur non vide.
> On note $EA(n)$ [resp. $E(n)$] l'ensemble des corps convexes de $\R^n$ [resp. de $S(n)$].
> On note $CA(n)$ l'ensemble des parties convexes compactes de $\R^n$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 7: `m, m'` not diametrically opposite | generalised: `closedSeg` is defined for every pair and the independence of the representatives holds for every pair; non-antipodality is used only where the paper uses it (`zero_notMem_segment`), and `closedSeg_neg_self` shows what the excluded case gives |
| Déf. 8: « $F(k)+\{O\}$ » | reading (OQ-24 RULED, DEC-120): `F(k) ∪ {O}`, `IsConvexPart` (wave 1); the Minkowski reading `IsConvexPartMinkowski` is kept only for the remarks |
| Déf. 7: « segment de droite » | ✓ carried: `closedSeg_subset_linearSubvariety_span` |
| Déf. 9: a convex part (Déf. 8) | ✓ carried over the `∪` reading, and proved equivalent to the same condition over the segment form and over the Minkowski reading, so no reading is needed |
| Déf. 11: `ℝⁿ` and `S(n)` with their topologies | ✓ carried: the product topology of `Fin n → ℝ`, the quotient topology of `S n` |
| `E` a real vector space | ✓ carried, any dimension, no topology (Déf. 7–9) |

## SCOPE (disclosed)

* **Déf. 8 is marked** under DEC-120 (OQ-24 ruled: `+` is `∪`), with no code change: the `∪`
  reading of the first sentence is equivalent to the unambiguous second sentence
  (`isConvexPart_iff_isSegConvex`). The Minkowski reading is kept as remarks only: it contradicts the
  segment form on `S(E)` itself (`not_isConvexPartMinkowski_univ`) and on every nonzero linear
  subvariety (`not_isConvexPartMinkowski_linearSubvariety`, against `isConvexPart_linearSubvariety`),
  and makes Déf. 10's « convexes contenant $l$ » empty
  (`not_isConvexPartMinkowski_of_linearSubvariety_subset`). On the scan (PDF p. 8 = journal p. 235)
  the same page prints « F(h) ∪ {O} » with the `∪` glyph ten lines above Déf. 8's `+`, so `+` is
  the printed symbol: the period's notation for a union of disjoint sets (`O ∉ F(k)`), or a misprint.
* **Déf. 9 and Déf. 11 are marked** although they say « partie convexe » / « convexe strict »:
  strictness collapses both readings to « `F(k)` convex » (`isStrictConvexPart_iff_convex_F`,
  `isStrictConvexPart_iff_minkowski`), so their content does not depend on OQ-24 (DEC-120 accepts the
  marks as independent of it).
* `E(n)` is named `ES n` (an identifier `E` is the ambient space everywhere else).
* `K(S(E))`, `C(S(E))` are over Déf. 8 (`∪` reading, DEC-120); they are unlabelled prose.
* Déf. 7's « segment de droite »: `(m, m')` lies on the linear subvariety spanned by `M, M'`
  (`closedSeg_subset_linearSubvariety_span`), a line of `S(E)` (Déf. 4's `IsLine`) when `M, M'` are
  independent.
* General Sphere/Subvariety facts proved here (`ofCone_subset_of_forall`, `mk_someVector`,
  `exists_pos_someVector`, `isConvexPart_linearSubvariety`) move upstream at graduation (REPORT
  `upstream_moves`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology
open scoped Pointwise

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Déf. 7 — segments -/

/-- Two parts of `E` define the same rays when each nonzero point of one is a positive multiple of
a point of the other. -/
theorem ofCone_subset_of_forall {C D : Set E}
    (h : ∀ x ∈ C, x ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ y ∈ D, x = c • y) : ofCone C ⊆ ofCone D := by
  intro z hz
  obtain ⟨x, hx, hxC, rfl⟩ := mem_ofCone.1 hz
  obtain ⟨c, hc, y, hyD, rfl⟩ := h x hxC hx
  have hy : y ≠ 0 := fun h0 => hx (by rw [h0, smul_zero])
  rw [mk_smul hy hc]
  exact mk_mem_ofCone hy hyD

/-- A point of the segment `[a M, b M']` (`a, b > 0`) is a positive multiple of a point of `[M, M']`. -/
theorem exists_smul_mem_segment {M M' : E} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : E}
    (hz : z ∈ segment ℝ (a • M) (b • M')) :
    ∃ c : ℝ, 0 < c ∧ ∃ w ∈ segment ℝ M M', z = c • w := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
  have hc : 0 < α * a + β * b := by
    rcases hα.lt_or_eq with hα' | hα'
    · exact add_pos_of_pos_of_nonneg (mul_pos hα' ha) (mul_nonneg hβ hb.le)
    · subst hα'; simp only [zero_add] at hαβ; subst hαβ; simpa using hb
  refine ⟨α * a + β * b, hc, ((α * a) / (α * a + β * b)) • M + ((β * b) / (α * a + β * b)) • M',
    ⟨_, _, by positivity, by positivity, by field_simp, rfl⟩, ?_⟩
  have e1 : (α * a + β * b) * (α * a / (α * a + β * b)) = α * a := by field_simp
  have e2 : (α * a + β * b) * (β * b / (α * a + β * b)) = β * b := by field_simp
  simp only [smul_add, smul_smul, e1, e2]

/-- The same for open segments. -/
theorem exists_smul_mem_openSegment {M M' : E} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : E}
    (hz : z ∈ openSegment ℝ (a • M) (b • M')) :
    ∃ c : ℝ, 0 < c ∧ ∃ w ∈ openSegment ℝ M M', z = c • w := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
  have hc : 0 < α * a + β * b := by positivity
  refine ⟨α * a + β * b, hc, ((α * a) / (α * a + β * b)) • M + ((β * b) / (α * a + β * b)) • M',
    ⟨_, _, by positivity, by positivity, by field_simp, rfl⟩, ?_⟩
  have e1 : (α * a + β * b) * (α * a / (α * a + β * b)) = α * a := by field_simp
  have e2 : (α * a + β * b) * (β * b / (α * a + β * b)) = β * b := by field_simp
  simp only [smul_add, smul_smul, e1, e2]

/-- The closed segment of rays `s([M, M'])` of two vectors. -/
def segOf (M M' : E) : Set (Sphere E) := ofCone (segment ℝ M M')

/-- The open segment of rays `s(]M, M'[)` of two vectors. -/
def openSegOf (M M' : E) : Set (Sphere E) := ofCone (openSegment ℝ M M')

theorem segOf_smul_smul (M M' : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    segOf (a • M) (b • M') = segOf M M' := by
  refine Subset.antisymm (ofCone_subset_of_forall fun z hz _ => exists_smul_mem_segment ha hb hz)
    (ofCone_subset_of_forall fun z hz _ => ?_)
  have hz' : z ∈ segment ℝ (a⁻¹ • a • M) (b⁻¹ • b • M') := by
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ ha.ne', inv_mul_cancel₀ hb.ne', one_smul, one_smul]
  exact exists_smul_mem_segment (inv_pos.2 ha) (inv_pos.2 hb) hz'

theorem openSegOf_smul_smul (M M' : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    openSegOf (a • M) (b • M') = openSegOf M M' := by
  refine Subset.antisymm
    (ofCone_subset_of_forall fun z hz _ => exists_smul_mem_openSegment ha hb hz)
    (ofCone_subset_of_forall fun z hz _ => ?_)
  have hz' : z ∈ openSegment ℝ (a⁻¹ • a • M) (b⁻¹ • b • M') := by
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ ha.ne', inv_mul_cancel₀ hb.ne', one_smul, one_smul]
  exact exists_smul_mem_openSegment (inv_pos.2 ha) (inv_pos.2 hb) hz'

theorem mk_someVector (x : Sphere E) :
    mk (Module.Ray.someVector x) (Module.Ray.someVector_ne_zero x) = x :=
  Module.Ray.someVector_ray x

theorem exists_pos_someVector {M : E} (hM : M ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ Module.Ray.someVector (mk M hM) = c • M := by
  obtain ⟨c, hc, h⟩ := (mk_eq_mk_iff_exists_pos hM (Module.Ray.someVector_ne_zero (mk M hM))).1
    (mk_someVector (mk M hM)).symm
  exact ⟨c, hc, h.symm⟩

/-- **The closed segment `(m, m')` of Déf. 7** (`bzdef:c1s1d7_segment`): `s([M, M'])` for
representatives `M ∈ F(m)`, `M' ∈ F(m')` (here Mathlib's chosen ones; the choice is indifferent,
`closedSeg_mk`). The paper defines it for `m, m'` not diametrically opposite. -/
def closedSeg (m m' : Sphere E) : Set (Sphere E) :=
  segOf (Module.Ray.someVector m) (Module.Ray.someVector m')

/-- **The open segment `)m, m'(` of Déf. 7.** -/
def openSeg (m m' : Sphere E) : Set (Sphere E) :=
  openSegOf (Module.Ray.someVector m) (Module.Ray.someVector m')

/-- **Déf. 7, « Il est clair que le choix de $M$ et $M'$ est indifférent »**: for ANY
representatives, `(s(M), s(M')) = s([M, M'])`. -/
theorem closedSeg_mk {M M' : E} (hM : M ≠ 0) (hM' : M' ≠ 0) :
    closedSeg (mk M hM) (mk M' hM') = segOf M M' := by
  obtain ⟨a, ha, h⟩ := exists_pos_someVector hM
  obtain ⟨b, hb, h'⟩ := exists_pos_someVector hM'
  rw [closedSeg, h, h', segOf_smul_smul _ _ ha hb]

/-- The same for the open segment. -/
theorem openSeg_mk {M M' : E} (hM : M ≠ 0) (hM' : M' ≠ 0) :
    openSeg (mk M hM) (mk M' hM') = openSegOf M M' := by
  obtain ⟨a, ha, h⟩ := exists_pos_someVector hM
  obtain ⟨b, hb, h'⟩ := exists_pos_someVector hM'
  rw [openSeg, h, h', openSegOf_smul_smul _ _ ha hb]

/-- **« segment de droite »**: the segment `(m, m')` lies on the line through `m` and `m'`, the
linear subvariety `s(span{M, M'} - {O})` (Déf. 4; a line of `S(E)` when `M, M'` are independent). -/
theorem closedSeg_subset_linearSubvariety_span {M M' : E} (hM : M ≠ 0) (hM' : M' ≠ 0) :
    closedSeg (mk M hM) (mk M' hM') ⊆ linearSubvariety (Submodule.span ℝ {M, M'}) := by
  rw [closedSeg_mk]
  exact ofCone_subset_ofCone ((Submodule.span ℝ {M, M'}).convex.segment_subset
    (Submodule.subset_span (mem_insert _ _)) (Submodule.subset_span (mem_insert_of_mem _ rfl)))

/-- For `m, m'` not diametrically opposite, the segment `[M, M']` avoids `O`: every point of it is
a point of `(m, m')`. -/
theorem zero_notMem_segment {M M' : E} (hM : M ≠ 0) (hM' : M' ≠ 0)
    (h : mk M' hM' ≠ -mk M hM) : (0 : E) ∉ segment ℝ M M' := by
  rintro ⟨a, b, ha, hb, hab, h0⟩
  by_cases ha0 : a = 0
  · subst ha0; rw [zero_add] at hab; subst hab
    rw [zero_smul, zero_add, one_smul] at h0; exact hM' h0
  by_cases hb0 : b = 0
  · subst hb0; rw [add_zero] at hab; subst hab
    rw [zero_smul, add_zero, one_smul] at h0; exact hM h0
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  apply h
  rw [neg_mk, mk_eq_mk_iff_exists_pos]
  refine ⟨b / a, div_pos hb' ha', ?_⟩
  have : a • M = -(b • M') := eq_neg_of_add_eq_zero_left h0
  calc (b / a) • M' = a⁻¹ • (b • M') := by rw [smul_smul, div_eq_inv_mul]
    _ = -M := by
      rw [← neg_neg (b • M'), ← this, smul_neg, smul_smul, inv_mul_cancel₀ ha'.ne', one_smul]

theorem left_mem_closedSeg (m m' : Sphere E) : m ∈ closedSeg m m' := by
  have := mk_mem_ofCone (Module.Ray.someVector_ne_zero m)
    (left_mem_segment ℝ (Module.Ray.someVector m) (Module.Ray.someVector m'))
  rw [mk_someVector] at this
  exact this

theorem right_mem_closedSeg (m m' : Sphere E) : m' ∈ closedSeg m m' := by
  have := mk_mem_ofCone (Module.Ray.someVector_ne_zero m')
    (right_mem_segment ℝ (Module.Ray.someVector m) (Module.Ray.someVector m'))
  rw [mk_someVector] at this
  exact this

theorem closedSeg_comm (m m' : Sphere E) : closedSeg m m' = closedSeg m' m := by
  rw [closedSeg, closedSeg, segOf, segOf, segment_symm]

/-! ### Déf. 8 — convex parts -/

/-- **Déf. 8, second printed form** (« quels que soient $m$ et $m'$ non diamétralement opposés dans
$k$, le segment $(m, m')$ soit inclus dans $k$ »). -/
def IsSegConvex (k : Set (Sphere E)) : Prop :=
  ∀ m ∈ k, ∀ m' ∈ k, m' ≠ -m → closedSeg m m' ⊆ k

/-- **Déf. 8's two printed forms agree, in the `∪` reading of « $F(k)+\{O\}$ »**: `F(k) ∪ {O}` is
convex iff `k` contains the segment of any two of its non-antipodal points. No hypothesis on `E`.
(`IsConvexPart` is wave 1's, `Projective/Subvariety`.) -/
theorem isConvexPart_iff_isSegConvex {k : Set (Sphere E)} : IsConvexPart k ↔ IsSegConvex k := by
  constructor
  · intro hk m hm m' hm' _ x hx
    induction m using ind with
    | h M hM =>
    induction m' using ind with
    | h M' hM' =>
    rw [closedSeg_mk] at hx
    obtain ⟨z, hz, hzseg, rfl⟩ := mem_ofCone.1 hx
    have := hk.segment_subset (mem_insert_of_mem _ ⟨hM, hm⟩) (mem_insert_of_mem _ ⟨hM', hm'⟩) hzseg
    exact ((mem_insert_iff.1 this).resolve_left hz).2
  · intro hk x hx y hy a b ha hb hab
    rcases mem_insert_iff.1 hx with rfl | hxF
    · rw [smul_zero, zero_add]
      rcases mem_insert_iff.1 hy with rfl | hyF
      · simp
      · rcases hb.lt_or_eq with hb' | rfl
        · exact mem_insert_of_mem _ (smul_mem_F hyF hb')
        · simp
    rcases mem_insert_iff.1 hy with rfl | hyF
    · rw [smul_zero, add_zero]
      rcases ha.lt_or_eq with ha' | rfl
      · exact mem_insert_of_mem _ (smul_mem_F hxF ha')
      · simp
    by_cases hz : a • x + b • y = 0
    · rw [hz]; exact mem_insert _ _
    refine mem_insert_of_mem _ ?_
    obtain ⟨hx0, hxk⟩ := hxF
    obtain ⟨hy0, hyk⟩ := hyF
    by_cases hopp : mk y hy0 = -mk x hx0
    · rw [neg_mk, mk_eq_mk_iff_exists_pos] at hopp
      obtain ⟨c, hc, hcy⟩ := hopp
      have hy' : y = c⁻¹ • -x := by rw [← hcy, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      have hz' : a • x + b • y = (a - b * c⁻¹) • x := by
        rw [hy', smul_neg, smul_neg, smul_smul, sub_smul, sub_eq_add_neg]
      rw [hz'] at hz ⊢
      have hd : a - b * c⁻¹ ≠ 0 := fun h => hz (by rw [h, zero_smul])
      rcases hd.lt_or_gt with hneg | hpos
      · have hx' : x = -(c • y) := by rw [hcy, neg_neg]
        have : (a - b * c⁻¹) • x = ((b * c⁻¹ - a) * c) • y := by
          rw [hx', smul_neg, smul_smul, ← neg_smul]; congr 1; ring
        rw [this]
        exact smul_mem_F ⟨hy0, hyk⟩ (mul_pos (by linarith) hc)
      · exact smul_mem_F ⟨hx0, hxk⟩ hpos
    · have hseg := hk _ hxk _ hyk hopp
      rw [closedSeg_mk] at hseg
      exact ⟨hz, hseg (mk_mem_ofCone hz ⟨a, b, ha, hb, hab, rfl⟩)⟩

/-- **Why Déf. 7 excludes antipodal points**: the "segment" of `m` and `-m` computed from
representatives is the pair `{m, -m}`, not an arc (every half great circle from `m` to `-m` is a
candidate). -/
theorem closedSeg_neg_self (m : Sphere E) : closedSeg m (-m) = {m, -m} := by
  induction m using ind with
  | h M hM =>
  rw [neg_mk, closedSeg_mk]
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, ⟨a, b, ha, hb, hab, rfl⟩, rfl⟩ := mem_ofCone.1 hx
    have hz' : a • M + b • -M = (a - b) • M := by rw [smul_neg, sub_smul, sub_eq_add_neg]
    have hd : a - b ≠ 0 := fun h => hz (by rw [hz', h, zero_smul])
    rcases hd.lt_or_gt with hneg | hpos
    · right
      rw [mem_singleton_iff, mk_eq_mk_iff_exists_pos]
      exact ⟨(b - a)⁻¹, inv_pos.2 (by linarith), by
        rw [hz', smul_smul, ← neg_neg (((b - a)⁻¹ * (a - b)) • M), ← neg_smul]
        congr 1
        rw [show -((b - a)⁻¹ * (a - b)) = (b - a)⁻¹ * (b - a) by ring,
          inv_mul_cancel₀ (by linarith), one_smul]⟩
    · left
      rw [mk_eq_mk_iff_exists_pos]
      exact ⟨(a - b)⁻¹, inv_pos.2 hpos, by rw [hz', smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]⟩
  · rintro (rfl | rfl)
    · exact mk_mem_ofCone hM (left_mem_segment ℝ M (-M))
    · exact mk_mem_ofCone _ (right_mem_segment ℝ M (-M))

/-! #### The Minkowski reading of « $F(k)+\{O\}$ » (OQ-24, ruled against by DEC-120: a remark) -/

/-- **Déf. 8, first printed form, read as a Minkowski sum** (the alternative of OQ-24):
`F(k) + {O}` convex. Since `F(k) + {O} = F(k)`, this is `F(k)` convex. Recorded to show what the
reading would do, not adopted. -/
def IsConvexPartMinkowski (k : Set (Sphere E)) : Prop := Convex ℝ (F k + ({0} : Set E))

theorem isConvexPartMinkowski_iff {k : Set (Sphere E)} :
    IsConvexPartMinkowski k ↔ Convex ℝ (F k) := by
  rw [IsConvexPartMinkowski, Set.add_singleton]
  simp only [add_zero, image_id']

/-- Under the Minkowski reading, a convex part never contains two antipodal points — so Déf. 9's
condition would be vacuous. -/
theorem IsConvexPartMinkowski.neg_notMem {k : Set (Sphere E)} (hk : IsConvexPartMinkowski k)
    {m : Sphere E} (hm : m ∈ k) : -m ∉ k := by
  rw [isConvexPartMinkowski_iff] at hk
  intro hm'
  induction m using ind with
  | h M hM =>
  rw [neg_mk] at hm'
  have := hk ⟨hM, hm⟩ ⟨neg_ne_zero.2 hM, hm'⟩ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [smul_neg, add_neg_cancel] at this
  exact zero_notMem_F k this

/-- The whole sphere satisfies Déf. 8's segment form. -/
theorem isSegConvex_univ : IsSegConvex (univ : Set (Sphere E)) := fun _ _ _ _ _ => subset_univ _

/-- **Déf. 8's two printed forms disagree under the Minkowski reading**: `S(E)` itself satisfies
the segment form but not « `F(k) + {O}` convex » read as a Minkowski sum (`E ≠ 0`). This was
evidence on OQ-24 for the `∪` reading, under which the two forms agree
(`isConvexPart_iff_isSegConvex`); DEC-120 adopts it. -/
theorem not_isConvexPartMinkowski_univ [Nontrivial E] :
    ¬ IsConvexPartMinkowski (univ : Set (Sphere E)) := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  exact h.neg_notMem (m := mk v hv) (mem_univ _) (mem_univ _)

/-- A linear subvariety is a convex part (`∪` reading): `F(l) ∪ {O} = L`. -/
theorem isConvexPart_linearSubvariety (L : Submodule ℝ E) : IsConvexPart (linearSubvariety L) := by
  unfold IsConvexPart
  rw [F_linearSubvariety]
  have : insert (0 : E) ((L : Set E) \ {0}) = L := by
    ext v; by_cases h : v = 0 <;> simp [h]
  rw [this]
  exact L.convex

/-- Under the Minkowski reading, no nonzero linear subvariety is convex. -/
theorem not_isConvexPartMinkowski_linearSubvariety {L : Submodule ℝ E} (hL : L ≠ ⊥) :
    ¬ IsConvexPartMinkowski (linearSubvariety L) := by
  intro h
  obtain ⟨v, hvL, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  exact h.neg_notMem ((mk_mem_linearSubvariety hv).2 hvL) (neg_mem_linearSubvariety
    ((mk_mem_linearSubvariety hv).2 hvL))

/-- **Under the Minkowski reading, NO part containing a nonzero linear subvariety is convex**
(the WP-45g audit's lemma, a remark supporting DEC-120's ruling of OQ-24): Déf. 10's « les
convexes de $S(E)$ contenant $l$ » would be the empty family for every `l ≠ ∅`, contradicting
DEC-114's ruling that Déf. 10's sphere statement holds as printed. -/
theorem not_isConvexPartMinkowski_of_linearSubvariety_subset {L : Submodule ℝ E} (hL : L ≠ ⊥)
    {k : Set (Sphere E)} (hk : linearSubvariety L ⊆ k) : ¬ IsConvexPartMinkowski k := by
  intro h
  obtain ⟨v, hvL, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  have hm := (mk_mem_linearSubvariety hv).2 hvL
  exact h.neg_notMem (hk hm) (hk (neg_mem_linearSubvariety hm))

/-! ### Déf. 9 — strict convex parts -/

/-- **Déf. 9** (`bzdef:c1s1d9_convexe_strict`): a convex part of `S(E)` is *strict* if it contains
no pair of diametrically opposite points. Stated over the `∪` reading of Déf. 8; it does not depend
on OQ-24 (`isStrictConvexPart_iff_convex_F`, `isStrictConvexPart_iff_minkowski`). -/
def IsStrictConvexPart (k : Set (Sphere E)) : Prop := IsConvexPart k ∧ ∀ m ∈ k, -m ∉ k

/-- **A strict convex part is a part whose cone `F(k)` is convex**: Déf. 9 in one condition. -/
theorem isStrictConvexPart_iff_convex_F {k : Set (Sphere E)} :
    IsStrictConvexPart k ↔ Convex ℝ (F k) := by
  constructor
  · rintro ⟨hk, hanti⟩ x hx y hy a b ha hb hab
    have := hk (mem_insert_of_mem _ hx) (mem_insert_of_mem _ hy) ha hb hab
    refine (mem_insert_iff.1 this).resolve_left fun h0 => ?_
    obtain ⟨hx0, hxk⟩ := hx
    obtain ⟨hy0, hyk⟩ := hy
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_add] at hab; subst hab; simp at h0; exact hy0 h0
    have hb0 : b ≠ 0 := by rintro rfl; rw [add_zero] at hab; subst hab; simp at h0; exact hx0 h0
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    apply hanti _ hxk
    have : mk y hy0 = -mk x hx0 := by
      rw [neg_mk, mk_eq_mk_iff_exists_pos]
      refine ⟨b / a, div_pos hb' ha', ?_⟩
      have h' : b • y = -(a • x) := eq_neg_of_add_eq_zero_right h0
      calc (b / a) • y = a⁻¹ • (b • y) := by rw [smul_smul, div_eq_inv_mul]
        _ = -x := by rw [h', smul_neg, smul_smul, inv_mul_cancel₀ ha'.ne', one_smul]
    rw [← this]; exact hyk
  · intro h
    refine ⟨fun x hx y hy a b ha hb hab => ?_, fun m hm hm' => ?_⟩
    · rcases mem_insert_iff.1 hx with rfl | hxF
      · rw [smul_zero, zero_add]
        rcases mem_insert_iff.1 hy with rfl | hyF
        · simp
        · rcases hb.lt_or_eq with hb' | rfl
          · exact mem_insert_of_mem _ (smul_mem_F hyF hb')
          · simp
      rcases mem_insert_iff.1 hy with rfl | hyF
      · rw [smul_zero, add_zero]
        rcases ha.lt_or_eq with ha' | rfl
        · exact mem_insert_of_mem _ (smul_mem_F hxF ha')
        · simp
      exact mem_insert_of_mem _ (h hxF hyF ha hb hab)
    · induction m using ind with
      | h M hM =>
      rw [neg_mk] at hm'
      have := h ⟨hM, hm⟩ ⟨neg_ne_zero.2 hM, hm'⟩ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      rw [smul_neg, add_neg_cancel] at this
      exact zero_notMem_F k this

/-- Déf. 9 over the segment form of Déf. 8 (the form that does not involve « $F(k)+\{O\}$ »). -/
theorem isStrictConvexPart_iff_isSegConvex {k : Set (Sphere E)} :
    IsStrictConvexPart k ↔ IsSegConvex k ∧ ∀ m ∈ k, -m ∉ k := by
  rw [IsStrictConvexPart, isConvexPart_iff_isSegConvex]

/-- **Déf. 9 does not depend on OQ-24**: over the Minkowski reading of Déf. 8, « convex and
strict » is the same notion (there, every convex part is strict). -/
theorem isStrictConvexPart_iff_minkowski {k : Set (Sphere E)} :
    IsStrictConvexPart k ↔ IsConvexPartMinkowski k ∧ ∀ m ∈ k, -m ∉ k := by
  rw [isStrictConvexPart_iff_convex_F, isConvexPartMinkowski_iff]
  constructor
  · intro h
    exact ⟨h, fun m hm => IsConvexPartMinkowski.neg_notMem (isConvexPartMinkowski_iff.2 h) hm⟩
  · exact fun h => h.1

/-- The convex cone `F(k) ∪ {O}` of a convex part (Mathlib's `ConvexCone`). -/
def IsConvexPart.cone {k : Set (Sphere E)} (hk : IsConvexPart k) : ConvexCone ℝ E where
  carrier := insert 0 (F k)
  smul_mem' c hc x hx := by
    rcases mem_insert_iff.1 hx with rfl | hxF
    · rw [smul_zero]; exact mem_insert _ _
    · exact mem_insert_of_mem _ (smul_mem_F hxF hc)
  add_mem' x hx y hy := by
    have := hk hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [← smul_add] at this
    rcases mem_insert_iff.1 this with h0 | hF
    · have : x + y = 0 := by
        have := congrArg (fun v => (2 : ℝ) • v) h0
        simpa [smul_smul] using this
      rw [this]; exact mem_insert _ _
    · have := smul_mem_F hF (two_pos (α := ℝ))
      rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at this
      exact mem_insert_of_mem _ this

theorem IsConvexPart.mem_cone {k : Set (Sphere E)} (hk : IsConvexPart k) {v : E} :
    v ∈ hk.cone ↔ v ∈ insert 0 (F k) := Iff.rfl

/-- **Déf. 9 as salience** (plan: `ConvexCone.Salient`): a convex part is strict iff its cone
`F(k) ∪ {O}` is salient. -/
theorem IsConvexPart.salient_cone_iff {k : Set (Sphere E)} (hk : IsConvexPart k) :
    hk.cone.Salient ↔ ∀ m ∈ k, -m ∉ k := by
  constructor
  · intro h m hm hm'
    induction m using ind with
    | h M hM =>
    rw [neg_mk] at hm'
    exact h M (mem_insert_of_mem _ ⟨hM, hm⟩) hM (mem_insert_of_mem _ ⟨neg_ne_zero.2 hM, hm'⟩)
  · intro h v hv hv0 hnv
    rw [hk.mem_cone] at hv hnv
    have hvF := (mem_insert_iff.1 hv).resolve_left hv0
    have hnvF := (mem_insert_iff.1 hnv).resolve_left (neg_ne_zero.2 hv0)
    obtain ⟨_, hvk⟩ := hvF
    obtain ⟨_, hnvk⟩ := hnvF
    exact h _ hvk (by rw [neg_mk]; exact hnvk)

/-! ### The prose of pp. 235–236: `K(E)`, `C(E)`, `K(S(E))`, `C(S(E))` -/

variable (E) in
/-- `K(E)`: the convex parts of `E`. -/
def KE : Set (Set E) := {C | Convex ℝ C}

variable (E) in
/-- `C(E)`: the closed convex parts of `E`. -/
def CE [TopologicalSpace E] : Set (Set E) := {C | Convex ℝ C ∧ IsClosed C}

variable (E) in
/-- `K(S(E))`: the convex parts of `S(E)` (Déf. 8, `∪` reading, DEC-120). -/
def KS : Set (Set (Sphere E)) := {k | IsConvexPart k}

variable (E) in
/-- `C(S(E))`: the closed convex parts of `S(E)` (Déf. 8, `∪` reading, DEC-120). -/
def CS [TopologicalSpace E] : Set (Set (Sphere E)) := {k | IsConvexPart k ∧ IsClosed k}

end Sphere

/-! ### Déf. 11 — convex bodies -/

section Def11

variable (n : ℕ)

/-- **A convex body of `ℝⁿ`** (Déf. 11, `bzdef:c1s1d11_corps_convexe`): a convex part of `ℝⁿ`,
compact, with nonempty interior. -/
def IsCorpsConvexe (K : Set (Fin n → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- **A convex body of `S(n)`** (Déf. 11): a strict convex part of `S(n)` (Déf. 9), compact, with
nonempty interior. Independent of OQ-24 (`isCorpsConvexeS_iff`). -/
def IsCorpsConvexeS (k : Set (S n)) : Prop :=
  Sphere.IsStrictConvexPart k ∧ IsCompact k ∧ (interior k).Nonempty

/-- **`EA(n)`**: the convex bodies of `ℝⁿ`. -/
def EA : Set (Set (Fin n → ℝ)) := {K | IsCorpsConvexe n K}

/-- **`E(n)`** (named `ES` here): the convex bodies of `S(n)`. -/
def ES : Set (Set (S n)) := {k | IsCorpsConvexeS n k}

/-- **`CA(n)`**: the compact convex parts of `ℝⁿ`. -/
def CA : Set (Set (Fin n → ℝ)) := {K | Convex ℝ K ∧ IsCompact K}

variable {n}

theorem EA_subset_CA : EA n ⊆ CA n := fun _ h => ⟨h.1, h.2.1⟩

/-- `EA(n)` in terms of Mathlib's `ConvexBody` (compact, convex, nonempty): the convex bodies with
nonempty interior. -/
theorem mem_EA_iff_convexBody {K : Set (Fin n → ℝ)} :
    K ∈ EA n ↔ ∃ B : ConvexBody (Fin n → ℝ), (B : Set (Fin n → ℝ)) = K ∧ (interior K).Nonempty := by
  constructor
  · rintro ⟨hc, hk, hi⟩
    exact ⟨⟨K, hc, hk, hi.mono interior_subset⟩, rfl, hi⟩
  · rintro ⟨B, rfl, hi⟩
    exact ⟨B.convex, B.isCompact, hi⟩

/-- A convex body of `S(n)`, in one condition on the cone: `F(k)` convex, `k` compact with
nonempty interior. The definition does not depend on the reading of Déf. 8 (OQ-24). -/
theorem isCorpsConvexeS_iff {k : Set (S n)} :
    IsCorpsConvexeS n k ↔ Convex ℝ (Sphere.F k) ∧ IsCompact k ∧ (interior k).Nonempty := by
  rw [IsCorpsConvexeS, Sphere.isStrictConvexPart_iff_convex_F]

end Def11

end Benzecri
