import Benzecri.Chapter2.Mesure
import Benzecri.Chapter2.Poches
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Chapter 2 § 2, Props. 2 and 3 — in a convex body the pseudo-length is the projective measure relative to the chord, continuous and separating; every point has a majorised neighbourhood

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal pp. 249–251; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-hilbert (DEC-137).

* **`bzprop:c2s2p2_pseudo_longueur_corps_convexe`** — `benzecri1960_ch2.tex:306` (Prop. 2,
  l.306–313, proof l.315–317) — marked under DEC-177 (n ≥ 1 is implied throughout Chapter 2; dimension 0 excluded, recorded), on `Benzecri.pseudo_longueur_corps_convexe`
  (SCOPE, « Dimension 0 »; OQ-56 is ruled by the same DEC-177). Proved, sorry-free, for `n ≥ 1`: `Benzecri.pseudo_longueur_corps_convexe` (the segment of `V`
  from `A` to `B` is unique; for `A ≠ B` the line `AB` meets the frontier in two points `F ≠ F'`;
  `l_V(A, B)` is the projective measure of `AB` relative to `FF'`; `l_V` is continuous on `V × V`
  and vanishes exactly on the diagonal). In every dimension: `pseudoLength_eq_projMeasure`,
  `exists_frontier_pair`, `continuous_hilbertLength`, `hilbertLength_ne_zero`: under the literal
  reading of « ne s'annule que sur la diagonale » Prop. 2 holds in every dimension, by these lemmas
  (no single theorem assembles them). The printed form under the « iff » reading,
  `PseudoLongueurCorpsConvexePrinted n`, holds iff `0 < n` (`pseudoLongueurCorpsConvexePrinted_iff`).
* **`bzprop:c2s2p3_voisinage_majore`** — `benzecri1960_ch2.tex:365` (Prop. 3, l.365–368, proof
  l.370–379) — marked under DEC-177 (n ≥ 1 is implied throughout Chapter 2; dimension 0 excluded, recorded), on `Benzecri.voisinage_majore`. Proved, sorry-free, for `n ≥ 1`:
  `Benzecri.voisinage_majore` (with an open neighbourhood: `exists_isOpen_isMajorePart`), on every
  `V` charted on `S(n)` with the projective groupoid. The printed form `VoisinageMajorePrinted n`
  holds iff `0 < n` (`voisinageMajorePrinted_iff`; for `n = 0`: `not_isMajorePart_dim_zero`).
* Properties 5° and 6° of the editorial enonce `bzthm:c2s2_proprietes_pseudo_longueur`
  (`benzecri1960_ch2.tex:229`, l.245–251; proof of 5° l.322–329), as lemmas, not marked (their
  row is T-bz-c2-proprietes): 5° `propriete_cinq` (the printed proof's form) and
  `propriete_cinq_limsup`, any dimension; 6° `propriete_six` (`n ≥ 1`).

> **Proposition 2.** Soient $\overline{V}$ un corps convexe de $S(n)$ d'intérieur $V$; $A$, $B$
> deux points de $V$; $F$, $F'$ les points d'intersection de la droite $AB$ avec la frontière de
> $\overline{V}$ : $l_V(A, B)$ n'est autre que la mesure projective de $AB$ relativement à $FF'$;
> $l_V(A, B)$ est une fonction continue sur $V\times V$ qui ne s'annule que sur la diagonale.
> La proposition résulte de ce que $F$, $F'$ dépendent continûment de $A$, $B$.
>
> **Proposition 3.** Soit $V$ une variété localement projective, $k$ un nombre réel strictement
> positif. Tout point $M$ de $V$ possède un voisinage qui est majoré par $k$.
> Si $V$ est l'intérieur d'un corps convexe, la propriété est une conséquence facile de la sixième
> propriété de la pseudo-longueur. Si $V$ n'est pas l'intérieur d'un corps convexe, choisissons un
> voisinage $U$ de $M$ dont il existe une carte compatible dans l'intérieur d'un corps convexe. On
> peut, d'après ce qui précède, trouver un voisinage $W$ de $M$, borné par $k$ dans $U$. D'après la
> quatrième propriété de la pseudo-longueur, $W$ est *a fortiori* majoré par $k$ dans $V$.
>
> 5° La pseudo-longueur est une fonction semi-continue supérieurement du segment, c'est-à-dire
> que, si un segment $(M_i, N_i)$ tend vers $(M, N)$, on a
> $\overline{\lim}\, l_V(M_i, N_i)\leqq l_V(M, N)$; 6° Si $V$ est l'intérieur d'un corps convexe,
> $l_V(M, N)$ est une fonction continue en $M$ et $N$ sur le produit $V\times V$; $l_V(M, N)$ est
> nulle si et seulement si $M=N$; […] Pour démontrer 5°, nous démontrerons que, si $MN$ est un
> segment borné par $k$ dans $V$, il en est de même de tout segment assez voisin de $MN$. […] Il
> suffit de montrer, d'après 4°, que la pseudo-longueur $l_U$ de tout segment suffisamment voisin
> de $MN$ est inférieure à $k$. Or, cela résulte aisément de la proposition 2.

## The proofs formalized

*A convex body lies in an open hemisphere* (`IsCorpsConvexeS.exists_forall_pos`: for each point,
Hahn–Banach separates the opposite ray from the closed cone `F(K) ∪ {O}`; a finite subcover and a
sum). On `ℓ = 1` the line `AB` is `t ↦ a + t (b − a)`, the points of `K` on it are the parameters
`[t₋, t₊]`, `t₋ < 0 < 1 < t₊` (`paramSet_eq_Icc`), the open chord is interior and its ends are the
two frontier points (`lineThrough_inter_frontier`). Every segment majorising `(A, B)` in `V` lies
in the chord, so Prop. 1 bounds `l_V` below by the measure relative to `FF'`; sub-chords bound it
above (`pseudoLength_eq_param`). Continuity is proved as two semicontinuities, moving four points
of the same parameters, whose cross-ratio is constant: the lower one because the points of `K`'s
complement beyond the chord stay outside (`K` closed), the upper one because a compact sub-chord
stays interior (tube lemma); on the diagonal, the affine-ball estimate
`exists_nhds_projMeasure_lt`. Prop. 3 and 5° are proved in one chart, by the same two estimates
(`eventually_exists_projMeasure_lt`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Prop. 2: `V̄` a convex body of `S(n)` (Déf. 11) | ✓ carried: `IsCorpsConvexeS n K` |
| Prop. 2: `V` its interior, a locally projective manifold | ✓ carried: `corpsInterior K` (`Opens.interior K`, Mathlib's charted structure on an open set, as for 4°) |
| Prop. 2: `l_V(A, B)` | ✓ carried: the pseudo-length of a segment of `V` from `A` to `B`; there is exactly one (`isProjSegment_corpsInterior_iff`), so `l_V` is `hilbertLength K` |
| Prop. 2: « la droite $AB$ » | ✓ carried for `A ≠ B`: `Sphere.lineThrough A B`, a line of Déf. 4 (`isLine_lineThrough`); for `A = B` it is `{A, −A}`, the hypothesis on `F`, `F'` fails, the assertion is vacuous (question) |
| Prop. 2: « $F$, $F'$ les points d'intersection … avec la frontière » | ✓ carried: any `F ≠ F'` with `lineThrough A B ∩ frontier K = {F, F'}`; they exist (`exists_frontier_pair`) |
| Prop. 2: « une fonction continue sur $V\times V$ » | ✓ carried: continuous `V × V → EReal` (`continuous_hilbertLength`, any dimension); for `n ≥ 1` finite, and continuous as a real function (`continuous_hilbertLength_toReal`) |
| Prop. 2: « ne s'annule que sur la diagonale » | ⚠ strengthened: read « `= 0 ↔ A = B` », as 6° (question); the literal `→` holds in every dimension |
| Prop. 2, Prop. 3, 6°: the dimension `n` | ⚠ strengthened: `[NeZero n]` in `pseudo_longueur_corps_convexe`, `voisinage_majore`, `propriete_six`; both printed forms fail for `n = 0` (finding, OQ-45) |
| Prop. 3: `V` a locally projective manifold | ⚠ weakened: `[ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]`; Hausdorff, connected, countable never used |
| Prop. 3: `k > 0`; « un voisinage majoré par $k$ » (Déf. 4) | ✓ carried: `W ∈ 𝓝 M ∧ IsMajorePart n k W` |
| 5°: « un segment $(M_i, N_i)$ tend vers $(M, N)$ » | ✓ carried, a reading (question): the endpoints converge and the segments eventually lie in every open neighbourhood of `(M, N)`; `propriete_cinq` is the proof's « tout segment assez voisin » |
| 6°: `V` the interior of a convex body | ✓ carried, as in Prop. 2 |

## SCOPE (disclosed)

* **Dimension 0** (finding; OQ-45 bears on both rows). For `n = 0` both printed statements fail,
  and only because Déf. 1 gives coincident points no measure (as for 1°, Mesure's
  `pseudoLength_self_eq_top_dim_zero`): every pseudo-length on a `V` charted on `S(0)` is `+∞`
  (`pseudoLength_eq_top_dim_zero`). Prop. 2: `{x}` is a convex body of `S(0)`
  (`isCorpsConvexeS_singleton_S0`), its interior is `{x}`, and `l_V(x, x) = +∞`
  (`hilbertLength_self_dim_zero`), so « nulle si et seulement si $M = N$ » fails, while the
  literal « ne s'annule que sur la diagonale » holds. Prop. 3: no part containing a point is
  majorised (`not_isMajorePart_dim_zero`), already on the one-point open set `{x}` of `S(0)`,
  Hausdorff and connected. Routing: OQ-45 (a), ruled by DEC-177, marks both rows on
  `pseudo_longueur_corps_convexe` and `voisinage_majore` with no Lean change.
* **In the printed proof of Prop. 2** (l.316, finding; statement unaffected): « $F$, $F'$
  dépendent continûment de $A$, $B$ » does not reach the diagonal, where the line `AB`, hence
  `F`, `F'`, is undefined; continuity at `(A, A)` needs a separate estimate (here the affine
  ball). The formalized proof uses two semicontinuities, not the continuity of `F`, `F'`.
* **Prop. 3 and 5° are proved in one chart**, not through 6° and 4°: no chart onto the interior
  of a convex body is constructed. The printed proof of Prop. 3 also needs the neighbourhood `W`
  to contain the segments joining its points (`W` convex in a chart), which 6° alone does not give.
* `F(int K) = int F(K)` (`Sphere.F_interior`) and the hemisphere lemma are general facts proved
  here. Tools for later targets (T-bz-c2-lignes, T-bz-c2-proprietes): `isProjSegment_opens_iff`,
  `pseudoLength_le_projMeasure_opens`, `projMeasure_le_pseudoLength_opens`,
  `exists_nhds_projMeasure_lt`, `eventually_exists_projMeasure_lt`, `Sphere.lineThrough`,
  `Sphere.mem_lineThrough_of_mem_closedSeg`, `isCompatibleChart_subtypeCoe`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u

/-! ### Complements on `S(E)` -/

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The two inner points of a cross-ratio lie in the open segment. -/
theorem IsCrossRatio.mem_openSeg {A' B' B A : Sphere E} {r : ℝ} (h : IsCrossRatio A' B' B A r) :
    A' ∈ openSeg A B ∧ B' ∈ openSeg A B := by
  obtain ⟨hr, a, b, -, ha, hb, h1, h2⟩ := h
  exact ⟨(mem_openSeg_iff ha hb).2 ⟨1, 1, one_pos, one_pos, by simpa using h1⟩,
    (mem_openSeg_iff ha hb).2 ⟨1, r, one_pos, hr, by simpa using h2⟩⟩

/-- A point of a closed segment other than its endpoints lies in the open segment. -/
theorem mem_openSeg_of_mem_closedSeg {A B X : Sphere E} (hX : X ∈ closedSeg A B) (hXA : X ≠ A)
    (hXB : X ≠ B) : X ∈ openSeg A B := by
  obtain ⟨a, ha⟩ := exists_isRep A
  obtain ⟨b, hb⟩ := exists_isRep B
  obtain ⟨s, t, hs, ht, hX⟩ := (mem_closedSeg_iff ha hb).1 hX
  refine (mem_openSeg_iff ha hb).2 ⟨s, t, lt_of_le_of_ne hs ?_, lt_of_le_of_ne ht ?_, hX⟩
  · rintro rfl
    rw [zero_smul, zero_add] at hX
    have ht0 : t ≠ 0 := by rintro rfl; exact hX.ne_zero (by simp)
    exact hXB (hX.eq (hb.smul (lt_of_le_of_ne ht (Ne.symm ht0))))
  · rintro rfl
    rw [zero_smul, add_zero] at hX
    have hs0 : s ≠ 0 := by rintro rfl; exact hX.ne_zero (by simp)
    exact hXA (hX.eq (ha.smul (lt_of_le_of_ne hs (Ne.symm hs0))))

/-- A closed segment whose endpoints have representatives in a convex set `C ⊆ F(T)` lies in
`T`. -/
theorem closedSeg_subset_of_convex {a b : E} {A B : Sphere E} (ha : IsRep a A) (hb : IsRep b B)
    {C : Set E} (hC : Convex ℝ C) (haC : a ∈ C) (hbC : b ∈ C) {T : Set (Sphere E)}
    (hCT : C ⊆ F T) : closedSeg A B ⊆ T := by
  intro X hX
  obtain ⟨s, t, hs, ht, hX⟩ := (mem_closedSeg_iff ha hb).1 hX
  have hst : 0 < s + t := by
    rcases (add_nonneg hs ht).lt_or_eq with h | h
    · exact h
    · exfalso
      have e1 : s = 0 := by linarith
      have e2 : t = 0 := by linarith
      subst e1 e2
      exact hX.ne_zero (by simp)
  have hmem : (s / (s + t)) • a + (t / (s + t)) • b ∈ C :=
    hC haC hbC (by positivity) (by positivity) (by field_simp)
  have hrep : IsRep ((s / (s + t)) • a + (t / (s + t)) • b) X := by
    convert hX.smul (inv_pos.2 hst) using 1
    rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  obtain ⟨h0, hk⟩ := hCT hmem
  obtain ⟨_, rfl⟩ := hrep
  exact hk

/-- **The line `AB`** of `S(E)` (Déf. 4: `s(L − {O})`, `L` spanned by representatives of `A` and
`B`; a line when `A ≠ B` are not diametrically opposite). -/
def lineThrough (A B : Sphere E) : Set (Sphere E) :=
  linearSubvariety (Submodule.span ℝ {Module.Ray.someVector A, Module.Ray.someVector B})

theorem mem_lineThrough_iff {a b : E} {A B X : Sphere E} (ha : IsRep a A) (hb : IsRep b B) :
    X ∈ lineThrough A B ↔ ∃ x y : ℝ, IsRep (x • a + y • b) X := by
  obtain ⟨c, hc, hca⟩ := ha.exists_pos ⟨Module.Ray.someVector_ne_zero A, mk_someVector A⟩
  obtain ⟨d, hd, hdb⟩ := hb.exists_pos ⟨Module.Ray.someVector_ne_zero B, mk_someVector B⟩
  induction X using ind with
  | h v hv =>
  rw [lineThrough, mk_mem_linearSubvariety, Submodule.mem_span_pair, hca, hdb]
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨x * c, y * d, ?_⟩
    convert isRep_mk v hv using 1
    rw [← hxy, smul_smul, smul_smul]
  · rintro ⟨x, y, hw, he⟩
    obtain ⟨e, he0, hev⟩ := (mk_eq_mk_iff_exists_pos hw hv).1 he
    refine ⟨e * x / c, e * y / d, ?_⟩
    rw [← hev, smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
    congr 2 <;> field_simp

/-- **`lineThrough A B` is a line** (Déf. 4: `s(L − {O})`, `dim L = 2`) when `A ≠ B` are not
diametrically opposite. -/
theorem isLine_lineThrough {A B : Sphere E} (h1 : B ≠ A) (h2 : B ≠ -A) :
    IsLine (lineThrough A B) := by
  have hli := linearIndependent_of_ne
    (⟨Module.Ray.someVector_ne_zero A, mk_someVector A⟩ : IsRep (Module.Ray.someVector A) A)
    (⟨Module.Ray.someVector_ne_zero B, mk_someVector B⟩ : IsRep (Module.Ray.someVector B) B)
    h1 h2
  refine ⟨_, ?_, rfl⟩
  have := finrank_span_eq_card hli
  rw [Matrix.range_cons_cons_empty] at this
  rw [this, Fintype.card_fin]

/-- **Points of a segment containing `A ≠ B` lie on the line `AB`**: if `A`, `B` (distinct, not
diametrically opposite) lie on the segment `(A₁, B₁)`, then `A₁` and `B₁` lie on the line `AB`. -/
theorem mem_lineThrough_of_mem_closedSeg {A B A₁ B₁ : Sphere E} (hAB : B ≠ A) (hAB' : B ≠ -A)
    (hA : A ∈ closedSeg A₁ B₁) (hB : B ∈ closedSeg A₁ B₁) :
    A₁ ∈ lineThrough A B ∧ B₁ ∈ lineThrough A B := by
  obtain ⟨a, ha⟩ := exists_isRep A
  obtain ⟨b, hb⟩ := exists_isRep B
  obtain ⟨a₁, ha₁⟩ := exists_isRep A₁
  obtain ⟨b₁, hb₁⟩ := exists_isRep B₁
  have hli := linearIndependent_of_ne ha hb hAB hAB'
  obtain ⟨s₁, t₁, -, -, hA'⟩ := (mem_closedSeg_iff ha₁ hb₁).1 hA
  obtain ⟨s₂, t₂, -, -, hB'⟩ := (mem_closedSeg_iff ha₁ hb₁).1 hB
  obtain ⟨c, hc, hca⟩ := ha.exists_pos hA'
  obtain ⟨d, hd, hdb⟩ := hb.exists_pos hB'
  set Δ := s₁ * t₂ - s₂ * t₁ with hΔ
  have e1 : Δ • a₁ = (t₂ * c) • a - (t₁ * d) • b := by
    rw [← smul_smul, ← smul_smul, ← hca, ← hdb]; module
  have e2 : Δ • b₁ = (s₁ * d) • b - (s₂ * c) • a := by
    rw [← smul_smul, ← smul_smul, ← hca, ← hdb]; module
  by_cases hΔ0 : Δ = 0
  · exfalso
    rw [hΔ0, zero_smul] at e1 e2
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hli (t₂ * c) (-(t₁ * d))
      (by rw [neg_smul, ← sub_eq_add_neg]; exact e1.symm)
    obtain ⟨h3, -⟩ := LinearIndependent.pair_iff.1 hli (-(s₂ * c)) (s₁ * d)
      (by rw [neg_smul, add_comm, ← sub_eq_add_neg]; exact e2.symm)
    have ht₁ : t₁ = 0 := (mul_eq_zero.1 (neg_eq_zero.1 h2)).resolve_right hd.ne'
    have hs₁ : s₁ = 0 := by
      have hs₂ : s₂ = 0 := (mul_eq_zero.1 (neg_eq_zero.1 h3)).resolve_right hc.ne'
      have ht₂ : t₂ = 0 := (mul_eq_zero.1 h1).resolve_right hc.ne'
      subst hs₂ ht₂
      have := hB'.ne_zero
      simp at this
    subst ht₁ hs₁
    have := hA'.ne_zero
    simp at this
  refine ⟨(mem_lineThrough_iff ha hb).2 ⟨Δ⁻¹ * (t₂ * c), -(Δ⁻¹ * (t₁ * d)), ?_⟩,
    (mem_lineThrough_iff ha hb).2 ⟨-(Δ⁻¹ * (s₂ * c)), Δ⁻¹ * (s₁ * d), ?_⟩⟩
  · convert ha₁ using 1
    calc _ = Δ⁻¹ • (Δ • a₁) := by rw [e1]; module
      _ = a₁ := by rw [smul_smul, inv_mul_cancel₀ hΔ0, one_smul]
  · convert hb₁ using 1
    calc _ = Δ⁻¹ • (Δ • b₁) := by rw [e2]; module
      _ = b₁ := by rw [smul_smul, inv_mul_cancel₀ hΔ0, one_smul]

/-- The "line" `AA` is `{A, −A}`. -/
theorem lineThrough_self_subset (A : Sphere E) : lineThrough A A ⊆ {A, -A} := by
  obtain ⟨a, ha⟩ := exists_isRep A
  intro X hX
  obtain ⟨x, y, hX⟩ := (mem_lineThrough_iff ha ha).1 hX
  rw [← add_smul] at hX
  rcases lt_trichotomy (x + y) 0 with h | h | h
  · right
    rw [mem_singleton_iff]
    have : (x + y) • a = (-(x + y)) • (-a) := by rw [smul_neg, neg_smul, neg_neg]
    rw [this] at hX
    exact hX.eq (ha.neg.smul (neg_pos.2 h))
  · rw [h, zero_smul] at hX
    exact absurd rfl hX.ne_zero
  · left
    exact hX.eq (ha.smul h)

section Topology

variable [TopologicalSpace E] [T1Space E] [ContinuousConstSMul ℝ E]

/-- **The cone of the interior**: `F(int A) = int F(A)`. -/
theorem F_interior (A : Set (Sphere E)) : F (interior A) = interior (F A) := by
  have h1 : s ⁻¹' interior A = interior (s ⁻¹' A) :=
    isOpenMap_s.preimage_interior_eq_interior_preimage continuous_s A
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have h2 : (Subtype.val : {v : E // v ≠ 0} → E) ⁻¹' interior (F A) =
      interior (Subtype.val ⁻¹' F A) :=
    hopen.isOpenEmbedding_subtypeVal.isOpenMap.preimage_interior_eq_interior_preimage
      continuous_subtype_val _
  rw [F_eq_image, h1, s_preimage_eq, ← h2, image_preimage_eq_inter_range,
    Subtype.range_coe_subtype]
  exact inter_eq_left.2 fun v hv => F_subset_compl_zero A (interior_subset hv)

end Topology

end Sphere

/-! ### Dimension -/

section Dimension

variable {n : ℕ}

/-- Two points of `S(n)` neither equal nor diametrically opposite exist only for `n ≥ 1`. -/
theorem one_le_of_ne_of_ne_neg {A B : S n} (h1 : B ≠ A) (h2 : B ≠ -A) : 1 ≤ n := by
  obtain ⟨a, ha⟩ := Sphere.exists_isRep A
  obtain ⟨b, hb⟩ := Sphere.exists_isRep B
  have := (Sphere.linearIndependent_of_ne ha hb h1 h2).fintype_card_le_finrank
  simp at this
  omega

/-- In `S(0)` a point is an open set. -/
theorem isOpen_singleton_S0 (x : S 0) : IsOpen ({x} : Set (S 0)) := by
  have : ({x} : Set (S 0)) = {-x}ᶜ := by
    ext y
    simp only [mem_singleton_iff, mem_compl_iff]
    constructor
    · rintro rfl h
      exact Module.Ray.ne_neg_self y h
    · intro h
      exact (S0_eq_or_eq_neg x y).resolve_right h
  rw [this]
  exact isOpen_compl_singleton

variable {V : Type u} [TopologicalSpace V]

/-- **In dimension `0` no segment is majorised** (Déf. 1 gives coincident points no measure, and in
`S(0)` the endpoints of a segment coincide). -/
theorem not_isMajoreSeg_dim_zero [ChartedSpace (S 0) V] (k : ℝ) (Sg : Set V) (M N : V) :
    ¬ IsMajoreSeg 0 k Sg M N := by
  rintro ⟨-, Sg₁, A, B, ⟨φ, hφ, hS, -, -, hadm, -⟩, -, hall⟩
  have hlt := hall φ hφ hS
  rcases S0_eq_or_eq_neg (φ A) (φ B) with h | h
  · rw [h, Sphere.projMeasure_same_eq_top] at hlt
    exact not_top_lt hlt
  · exact hadm h

/-- **In dimension `0` every pseudo-length is `+∞`**, on every `V` charted on `S(0)` (Mesure's
`pseudoLength_self_eq_top_dim_zero` is the case `V = S(0)`, `Sg = {m}`). -/
theorem pseudoLength_eq_top_dim_zero [ChartedSpace (S 0) V] (Sg : Set V) (M N : V) :
    pseudoLength 0 Sg M N = ⊤ := by
  simp [pseudoLength, not_isMajoreSeg_dim_zero]

/-- **In dimension `0` no part containing a point is majorised**: Prop. 3 fails for `n = 0`. -/
theorem not_isMajorePart_dim_zero [ChartedSpace (S 0) V] (k : ℝ) {W : Set V} {M : V}
    (hM : M ∈ W) : ¬ IsMajorePart 0 k W := by
  intro h
  obtain ⟨Sg, -, hmaj⟩ := h M hM M hM
  exact not_isMajoreSeg_dim_zero k Sg M M hmaj

end Dimension

/-! ### Small segments around a point of `S(n)` (the affine-ball estimate) -/

section Ball

variable {n : ℕ}

/-- Two points with representatives on which a linear form is positive are not diametrically
opposite. -/
theorem ne_neg_of_map_pos {E : Type*} [AddCommGroup E] [Module ℝ E] (ℓ : E →ₗ[ℝ] ℝ) {a b : E}
    {A B : Sphere E} (ha : Sphere.IsRep a A) (hb : Sphere.IsRep b B) (hla : 0 < ℓ a)
    (hlb : 0 < ℓ b) : B ≠ -A := by
  rintro rfl
  obtain ⟨c, hc, hcb⟩ := ha.neg.exists_pos hb
  rw [hcb, map_smul, map_neg, smul_eq_mul] at hlb
  nlinarith

/-- `p`, `u` with `ℓ p = 1`, `ℓ u = 0`, `u ≠ 0` are independent. -/
theorem linearIndependent_of_map_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (ℓ : E →ₗ[ℝ] ℝ)
    {p u : E} (hp : ℓ p = 1) (hu : ℓ u = 0) (hu0 : u ≠ 0) : LinearIndependent ℝ ![p, u] := by
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  have h1 : s = 0 := by
    have := congrArg ℓ hst
    simpa [hp, hu] using this
  subst h1
  simp only [zero_smul, zero_add] at hst
  exact ⟨rfl, (smul_eq_zero.1 hst).resolve_right hu0⟩

/-- **The affine-ball estimate.** Around a point `X` of an open set `T` of `S(n)`, `n ≥ 1`, there
is an open `W ⊆ T`, convex in the sense of segments, such that any two points `P`, `Q` of `W` lie on
a segment `(A, B) ⊆ T` relative to which the projective measure of `PQ` is `< k`. (In an affine
chart `W` is a small ball and `(A, B)` the chord `PQ` extended by a fixed length.) -/
theorem exists_nhds_projMeasure_lt (hn : 1 ≤ n) {T : Set (S n)} (hT : IsOpen T) {X : S n}
    (hX : X ∈ T) {k : ℝ} (hk : 0 < k) :
    ∃ W : Set (S n), IsOpen W ∧ X ∈ W ∧ W ⊆ T ∧ ∀ P ∈ W, ∀ Q ∈ W, Q ≠ -P ∧
      Sphere.closedSeg P Q ⊆ W ∧ ∃ A B : S n, B ≠ -A ∧ Sphere.closedSeg A B ⊆ T ∧
        P ∈ Sphere.closedSeg A B ∧ Q ∈ Sphere.closedSeg A B ∧
        Sphere.projMeasure A P Q B < k := by
  obtain ⟨x, hx⟩ := Sphere.exists_isRep X
  obtain ⟨ℓ, hℓx⟩ := SeparatingDual.exists_eq_one (R := ℝ) hx.ne_zero
  have hFT : IsOpen (Sphere.F T) := Sphere.isOpen_iff_F.1 hT
  have hxF : x ∈ Sphere.F T := ⟨hx.ne_zero, by rw [hx.2]; exact hX⟩
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hFT x hxF
  set ρ := R / 2 with hρ
  have hρ0 : 0 < ρ := half_pos hR
  set ε := min ρ (k * ρ / 4) with hε
  have hε0 : 0 < ε := lt_min hρ0 (by positivity)
  have hερ : ε ≤ ρ := min_le_left _ _
  have hεk : ε ≤ k * ρ / 4 := min_le_right _ _
  set C : Set (Fin (n + 1) → ℝ) := {v | 0 < ℓ v ∧ ‖(ℓ v)⁻¹ • v - x‖ < ε} with hC
  set C₁ : Set (Fin (n + 1) → ℝ) := {v | ℓ v = 1} ∩ Metric.ball x ε with hC₁
  have hC₁conv : Convex ℝ C₁ :=
    (convex_hyperplane ℓ.toLinearMap.isLinear 1).inter (convex_ball x ε)
  set W := Sphere.ofCone C with hW
  have hmemW : ∀ P : S n, P ∈ W ↔ ∃ p, Sphere.IsRep p P ∧ ℓ p = 1 ∧ ‖p - x‖ < ε := by
    intro P
    rw [hW, Sphere.mem_ofCone]
    constructor
    · rintro ⟨v, hv, ⟨hlv, hvx⟩, rfl⟩
      refine ⟨(ℓ v)⁻¹ • v, (Sphere.isRep_mk v hv).smul (inv_pos.2 hlv), ?_, hvx⟩
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hlv.ne']
    · rintro ⟨p, ⟨hp0, rfl⟩, hlp, hpx⟩
      exact ⟨p, hp0, ⟨by rw [hlp]; exact one_pos, by rw [hlp, inv_one, one_smul]; exact hpx⟩, rfl⟩
  have hC₁W : C₁ ⊆ Sphere.F W := by
    rintro v ⟨hlv, hvx⟩
    simp only [mem_setOf_eq] at hlv
    have hv0 : v ≠ 0 := fun h => by rw [h, map_zero] at hlv; exact zero_ne_one hlv
    refine ⟨hv0, (hmemW _).2 ⟨v, Sphere.isRep_mk v hv0, hlv, ?_⟩⟩
    rwa [Metric.mem_ball, dist_eq_norm] at hvx
  have hballT : ∀ y : Fin (n + 1) → ℝ, ‖y - x‖ < R → ∀ Y : S n, Sphere.IsRep y Y → Y ∈ T := by
    intro y hy Y hY
    have := hball (by rwa [Metric.mem_ball, dist_eq_norm])
    obtain ⟨_, hmem⟩ := this
    obtain ⟨_, rfl⟩ := hY
    exact hmem
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · -- `W` is open
    refine Sphere.isOpen_ofCone ?_ ?_
    · rintro c hc v ⟨hlv, hvx⟩
      refine ⟨by rw [map_smul, smul_eq_mul]; positivity, ?_⟩
      have h0 := hlv.ne'
      have hc0 := hc.ne'
      rwa [map_smul, smul_eq_mul, smul_smul, show (c * ℓ v)⁻¹ * c = (ℓ v)⁻¹ by field_simp]
    · have hcont : ContinuousOn (fun v : Fin (n + 1) → ℝ => (ℓ v)⁻¹ • v) {v | 0 < ℓ v} :=
        (ℓ.continuous.continuousOn.inv₀ fun v hv => ne_of_gt hv).smul continuousOn_id
      have := hcont.isOpen_inter_preimage (isOpen_lt continuous_const ℓ.continuous)
        (Metric.isOpen_ball (x := x) (ε := ε))
      convert this using 1
      ext v
      simp [hC, Metric.mem_ball, dist_eq_norm]
  · exact (hmemW X).2 ⟨x, hx, hℓx, by simpa using hε0⟩
  · intro Y hY
    obtain ⟨y, hy, -, hyx⟩ := (hmemW Y).1 hY
    exact hballT y (by linarith) Y hy
  · intro P hP Q hQ
    obtain ⟨p, hp, hlp, hpx⟩ := (hmemW P).1 hP
    obtain ⟨q, hq, hlq, hqx⟩ := (hmemW Q).1 hQ
    have hPT : P ∈ T := hballT p (by linarith) P hp
    refine ⟨ne_neg_of_map_pos ℓ.toLinearMap hp hq (by simp [hlp]) (by simp [hlq]),
      Sphere.closedSeg_subset_of_convex hp hq hC₁conv
        ⟨hlp, by rwa [Metric.mem_ball, dist_eq_norm]⟩
        ⟨hlq, by rwa [Metric.mem_ball, dist_eq_norm]⟩ hC₁W, ?_⟩
    by_cases hpq : p = q
    · -- `P = Q`: a segment of `T` through `P`
      subst hpq
      have hPQ : Q = P := hq.eq hp
      subst hPQ
      obtain ⟨a, b, hba, hba', hm, hsub⟩ := exists_closedSeg_subset hn hT hPT
      exact ⟨a, b, hba', hsub, Sphere.openSeg_subset_closedSeg a b hm,
        Sphere.openSeg_subset_closedSeg a b hm,
        by rw [Sphere.projMeasure_self hba hba' hm]; exact EReal.coe_pos.2 hk⟩
    -- `P ≠ Q`: the chord `PQ` extended by `ρ` on both sides
    set L := ‖q - p‖ with hL
    have hL0 : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hpq))
    set u := L⁻¹ • (q - p) with hu
    have hnu : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hL0.ne']
    have hlu : ℓ u = 0 := by rw [hu, map_smul, map_sub, hlp, hlq, sub_self, smul_zero]
    have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hnu; exact zero_ne_one hnu
    have hqu : q = p + L • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hL0.ne', one_smul, add_sub_cancel]
    have hli := linearIndependent_of_map_eq ℓ.toLinearMap hlp hlu hu0
    have hne : ∀ t : ℝ, p + t • u ≠ 0 := fun t h => by
      have := congrArg ℓ h
      simp [hlp, hlu] at this
    set A' : S n := Sphere.mk (p + (-ρ) • u) (hne _) with hA'
    set B' : S n := Sphere.mk (p + (L + ρ) • u) (hne _) with hB'
    have hcr : Sphere.IsCrossRatio P Q B' A' (crossRatio 0 L (L + ρ) (-ρ)) :=
      Sphere.isCrossRatio_affine hli (by linarith) (by linarith) (by linarith) (by linarith)
        (by simpa using hp) (by rwa [← hqu]) (Sphere.isRep_mk _ _) (Sphere.isRep_mk _ _)
    have hval : crossRatio 0 L (L + ρ) (-ρ) = ((L + ρ) / ρ) * ((L + ρ) / ρ) := by
      have hρne := hρ0.ne'
      have hd : (L + ρ - L) * (-ρ - 0) ≠ 0 := by
        rw [show (L + ρ - L) * (-ρ - 0) = -(ρ * ρ) by ring]
        exact neg_ne_zero.2 (mul_ne_zero hρne hρne)
      unfold crossRatio
      rw [div_mul_div_comm, div_mul_div_comm, div_eq_div_iff hd (mul_ne_zero hρne hρne)]
      ring
    have hy1 : 1 ≤ (L + ρ) / ρ := by rw [le_div_iff₀ hρ0]; linarith
    have hlogy : Real.log ((L + ρ) / ρ) ≤ L / ρ := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < (L + ρ) / ρ)
      rwa [show (L + ρ) / ρ - 1 = L / ρ by field_simp; ring] at this
    have hLε : L < 2 * ε := by
      calc L = ‖(q - x) - (p - x)‖ := by rw [hL]; congr 1; abel
        _ ≤ ‖q - x‖ + ‖p - x‖ := norm_sub_le _ _
        _ < ε + ε := add_lt_add hqx hpx
        _ = 2 * ε := by ring
    have hlt : |Real.log (crossRatio 0 L (L + ρ) (-ρ))| < k := by
      rw [hval, Real.log_mul (by positivity) (by positivity),
        abs_of_nonneg (add_nonneg (Real.log_nonneg hy1) (Real.log_nonneg hy1))]
      have h1 : L / ρ < 2 * ε / ρ := div_lt_div_of_pos_right hLε hρ0
      have h2 : 2 * ε / ρ ≤ k / 2 := by
        rw [div_le_iff₀ hρ0]; linarith
      linarith
    have hmem := hcr.mem_openSeg
    have hRa : ‖(p + (-ρ) • u) - x‖ < R := by
      calc ‖(p + (-ρ) • u) - x‖ = ‖(p - x) + (-ρ) • u‖ := by congr 1; abel
        _ ≤ ‖p - x‖ + ‖(-ρ) • u‖ := norm_add_le _ _
        _ = ‖p - x‖ + ρ := by rw [norm_smul, hnu, mul_one, Real.norm_eq_abs, abs_neg,
              abs_of_pos hρ0]
        _ < ε + ρ := by linarith
        _ ≤ R := by linarith
    have hRb : ‖(p + (L + ρ) • u) - x‖ < R := by
      calc ‖(p + (L + ρ) • u) - x‖ = ‖(q - x) + ρ • u‖ := by rw [hqu]; congr 1; module
        _ ≤ ‖q - x‖ + ‖ρ • u‖ := norm_add_le _ _
        _ = ‖q - x‖ + ρ := by rw [norm_smul, hnu, mul_one, Real.norm_eq_abs, abs_of_pos hρ0]
        _ < ε + ρ := by linarith
        _ ≤ R := by linarith
    refine ⟨A', B',
      ne_neg_of_map_pos ℓ.toLinearMap (Sphere.isRep_mk _ _) (Sphere.isRep_mk _ _)
        (by simp [hlp, hlu]) (by simp [hlp, hlu]),
      Sphere.closedSeg_subset_of_convex (Sphere.isRep_mk _ _) (Sphere.isRep_mk _ _)
        (convex_ball x R) (by rwa [Metric.mem_ball, dist_eq_norm])
        (by rwa [Metric.mem_ball, dist_eq_norm]) hball,
      Sphere.openSeg_subset_closedSeg _ _ hmem.1, Sphere.openSeg_subset_closedSeg _ _ hmem.2, ?_⟩
    rw [Sphere.projMeasure_eq hcr]
    exact EReal.coe_lt_coe_iff.2 hlt

end Ball

/-! ### Prop. 3 — every point has a neighbourhood majorised by `k` -/

section Prop3

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]

/-- **Prop. 3, with an open neighbourhood** (`n ≥ 1`): every point `M` of a locally projective `V`
has an open neighbourhood majorised by `k` (Déf. 4). -/
theorem exists_isOpen_isMajorePart [NeZero n] {k : ℝ} (hk : 0 < k) (M : V) :
    ∃ W : Set V, IsOpen W ∧ M ∈ W ∧ IsMajorePart n k W := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  set φ := chartAt (S n) M with hφdef
  have hφ : IsCompatibleChart (GSR n) φ :=
    isCompatibleChart_iff.2 ((gxGroupoid _ _).chart_mem_maximalAtlas M)
  have hM : M ∈ φ.source := mem_chart_source _ M
  obtain ⟨W₀, hW₀o, hMW₀, hW₀T, hW₀⟩ :=
    exists_nhds_projMeasure_lt hn φ.open_target (φ.map_source hM) hk
  refine ⟨φ.source ∩ φ ⁻¹' W₀, φ.isOpen_inter_preimage hW₀o, ⟨hM, hMW₀⟩, ?_⟩
  rintro P ⟨hPs, hPW⟩ Q ⟨hQs, hQW⟩
  obtain ⟨hQP, hsegW, A, B, hBA, hABT, hPAB, hQAB, hlt⟩ := hW₀ _ hPW _ hQW
  refine ⟨φ.symm '' Sphere.closedSeg (φ P) (φ Q), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hyT : y ∈ φ.target := hW₀T (hsegW hy)
    exact ⟨φ.map_target hyT, by rw [mem_preimage, φ.right_inv hyT]; exact hsegW hy⟩
  · have := isMajoreSeg_of_chart hφ hBA hABT hPAB hQAB hQP hlt
    rwa [φ.left_inv hPs, φ.left_inv hQs] at this

/-- **Prop. 3** (`bzprop:c2s2p3_voisinage_majore`, for `n ≥ 1`): « Soit $V$ une variété localement
projective, $k$ un nombre réel strictement positif. Tout point $M$ de $V$ possède un voisinage qui
est majoré par $k$. » -/
theorem voisinage_majore [NeZero n] {k : ℝ} (hk : 0 < k) (M : V) :
    ∃ W ∈ 𝓝 M, IsMajorePart n k W := by
  obtain ⟨W, hWo, hMW, hW⟩ := exists_isOpen_isMajorePart (n := n) hk M
  exact ⟨W, hWo.mem_nhds hMW, hW⟩

end Prop3

/-- **Prop. 3 as printed**, for the manifolds of dimension `n` (Hausdorff and connected; `V : Type`).
Second countability, also part of the standing reading of « variété », is not required here; the
dimension-0 witness (a one-point open set) has it, so the failure stands under the full reading. -/
def VoisinageMajorePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V], ∀ k : ℝ, 0 < k → ∀ M : V, ∃ W ∈ 𝓝 M, IsMajorePart n k W

/-- **Prop. 3 holds as printed exactly in dimension `n ≥ 1`.** For `n = 0`, the one-point open set
`{x}` of `S(0)` (Hausdorff, connected) is a locally projective `0`-manifold whose point has no
majorised neighbourhood (`not_isMajorePart_dim_zero`). -/
theorem voisinageMajorePrinted_iff {n : ℕ} : VoisinageMajorePrinted n ↔ 0 < n := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      obtain ⟨x⟩ : Nonempty (S 0) := inferInstance
      let U : TopologicalSpace.Opens (S 0) := ⟨{x}, isOpen_singleton_S0 x⟩
      haveI : ConnectedSpace U := isConnected_iff_connectedSpace.1 isConnected_singleton
      obtain ⟨W, hW, hmaj⟩ := h U 1 one_pos ⟨x, rfl⟩
      exact not_isMajorePart_dim_zero 1 (mem_of_mem_nhds hW) hmaj
    · exact hn
  · intro hn V _ _ _ _ _ k hk M
    haveI : NeZero n := ⟨hn.ne'⟩
    exact voisinage_majore (n := n) hk M

/-! ### Open sets of `S(n)` as locally projective manifolds: their segments, and two bounds on the
pseudo-length -/

section Opens

variable {n : ℕ}

/-- The inclusion of an open set of `S(n)` is a compatible chart. -/
theorem isCompatibleChart_subtypeCoe (U : TopologicalSpace.Opens (S n)) (h : Nonempty U) :
    IsCompatibleChart (GSR n) (U.openPartialHomeomorphSubtypeCoe h) := by
  have := IsCompatibleChart.subtypeRestr h (n := n) (V := S n)
    (ψ := OpenPartialHomeomorph.refl (S n))
    (isCompatibleChart_iff.2 (gxGroupoid _ _).id_mem_maximalAtlas)
  rwa [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_refl] at this

/-- **The segments of an open set `U` of `S(n)`** are the segments `(A, B)` of `S(n)` contained in
`U` (in particular a segment of `U` is determined by its endpoints). -/
theorem isProjSegment_opens_iff {U : TopologicalSpace.Opens (S n)} {Sg : Set U} {A B : U} :
    IsProjSegment n Sg A B ↔ (B : S n) ≠ -(A : S n) ∧ Sphere.closedSeg (A : S n) B ⊆ U ∧
      Sg = Subtype.val ⁻¹' Sphere.closedSeg (A : S n) B := by
  constructor
  · intro h
    have h' := h.lift
    obtain ⟨himg, hne⟩ := h'.image_eq_closedSeg
      (isCompatibleChart_iff.2 (gxGroupoid _ _).id_mem_maximalAtlas)
      (ψ := OpenPartialHomeomorph.refl (S n)) (subset_univ _)
    simp only [OpenPartialHomeomorph.refl_apply, id_eq, image_id'] at himg hne
    refine ⟨hne, ?_, ?_⟩
    · rw [← himg]
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rw [← himg, Subtype.val_injective.preimage_image]
  · rintro ⟨hne, hsub, rfl⟩
    set ψ := U.openPartialHomeomorphSubtypeCoe ⟨A⟩
    have hψ := isCompatibleChart_subtypeCoe U ⟨A⟩
    have hT : Sphere.closedSeg (ψ A) (ψ B) ⊆ ψ.target := by
      simpa [ψ] using hsub
    have := isProjSegment_of_chart hψ (by simpa [ψ] using hne) hT
    have e1 : ψ.symm (ψ A) = A := ψ.left_inv (mem_univ _)
    have e2 : ψ.symm (ψ B) = B := ψ.left_inv (mem_univ _)
    rw [e1, e2, ψ.symm_image_eq_source_inter_preimage hT] at this
    simpa [ψ] using this

variable {U : TopologicalSpace.Opens (S n)}

/-- **Upper bound**: if `(A, B) ⊆ (A₁, B₁) ⊆ U`, then `l_U(A, B)` is at most the projective measure
of `AB` relative to `A₁B₁`. -/
theorem pseudoLength_le_projMeasure_opens {Sg : Set U} {A B : U} (hSg : IsProjSegment n Sg A B)
    {A₁ B₁ : S n} (hB₁ : B₁ ≠ -A₁) (hsub : Sphere.closedSeg A₁ B₁ ⊆ U)
    (hA : (A : S n) ∈ Sphere.closedSeg A₁ B₁) (hB : (B : S n) ∈ Sphere.closedSeg A₁ B₁) :
    pseudoLength n Sg A B ≤ Sphere.projMeasure A₁ A B B₁ := by
  obtain ⟨hne, -, rfl⟩ := isProjSegment_opens_iff.1 hSg
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  induction c using EReal.rec with
  | bot => exact absurd hc not_lt_bot
  | top => exact le_top
  | coe k =>
    set ψ := U.openPartialHomeomorphSubtypeCoe ⟨A⟩
    have hψ := isCompatibleChart_subtypeCoe U ⟨A⟩
    have hT : Sphere.closedSeg A₁ B₁ ⊆ ψ.target := by simpa [ψ] using hsub
    have hmaj := isMajoreSeg_of_chart (a' := ψ A) (b' := ψ B) hψ hB₁ hT hA hB hne hc
    have e1 : ψ.symm (ψ A) = A := ψ.left_inv (mem_univ _)
    have e2 : ψ.symm (ψ B) = B := ψ.left_inv (mem_univ _)
    have hT' : Sphere.closedSeg (ψ A) (ψ B) ⊆ ψ.target := by
      simpa [ψ] using (isProjSegment_opens_iff.1 hSg).2.1
    rw [e1, e2, ψ.symm_image_eq_source_inter_preimage hT'] at hmaj
    simp only [ψ, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe, univ_inter] at hmaj
    exact pseudoLength_le hmaj

/-- **Lower bound**: if `U ⊆ K` and every point of `K` on the line `AB` lies on the segment
`(G, G')`, then `l_U(A, B)` is at least the projective measure of `AB` relative to `GG'`
(Prop. 1: every segment majorising `(A, B)` in `U` lies in `(G, G')`). -/
theorem projMeasure_le_pseudoLength_opens {K : Set (S n)} (hUK : (U : Set (S n)) ⊆ K)
    {Sg : Set U} {A B : U} (hSg : IsProjSegment n Sg A B) (hAB : A ≠ B) {G G' : S n}
    (hG : ∀ X ∈ K, X ∈ Sphere.lineThrough (A : S n) B → X ∈ Sphere.closedSeg G G') :
    Sphere.projMeasure G A B G' ≤ pseudoLength n Sg A B := by
  refine le_iInf₂ fun k hk => ?_
  obtain ⟨hseg, Sg₁, A₁, B₁, hseg₁, hsub, hall⟩ := hk
  obtain ⟨hne, -, rfl⟩ := isProjSegment_opens_iff.1 hseg
  obtain ⟨hne₁, hsub₁, rfl⟩ := isProjSegment_opens_iff.1 hseg₁
  have hlt := hall (U.openPartialHomeomorphSubtypeCoe ⟨A⟩) (isCompatibleChart_subtypeCoe U ⟨A⟩)
    (by simp)
  simp only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] at hlt
  have hA₁ : (A : S n) ∈ Sphere.closedSeg (A₁ : S n) B₁ :=
    hsub (Sphere.left_mem_closedSeg (A : S n) B)
  have hB₁ : (B : S n) ∈ Sphere.closedSeg (A₁ : S n) B₁ :=
    hsub (Sphere.right_mem_closedSeg (A : S n) B)
  have hBA : (B : S n) ≠ A := fun h => hAB (Subtype.ext h.symm)
  obtain ⟨hl₁, hl₂⟩ := Sphere.mem_lineThrough_of_mem_closedSeg hBA hne hA₁ hB₁
  have hG₁ := hG _ (hUK A₁.2) hl₁
  have hG₂ := hG _ (hUK B₁.2) hl₂
  exact ((Sphere.projMeasure_le_outer hG₁ hG₂).trans_lt hlt).le

end Opens

/-! ### Convex bodies of `S(n)`: a hemisphere containing them, and their interior -/

section Body

variable {n : ℕ} {K : Set (S n)}

namespace IsCorpsConvexeS

theorem isClosed (hK : IsCorpsConvexeS n K) : IsClosed K := hK.2.1.isClosed

theorem convex_F (hK : IsCorpsConvexeS n K) : Convex ℝ (Sphere.F K) :=
  Sphere.isStrictConvexPart_iff_convex_F.1 hK.1

theorem neg_notMem (hK : IsCorpsConvexeS n K) {X : S n} (hX : X ∈ K) : -X ∉ K := hK.1.2 X hX

/-- `F(K) ∪ {O}` is closed (`K` is compact). -/
theorem isClosed_insert_zero_F (hK : IsCorpsConvexeS n K) :
    IsClosed (insert (0 : Fin (n + 1) → ℝ) (Sphere.F K)) := by
  have h := Sphere.F_closure K
  rw [hK.isClosed.closure_eq] at h
  have e : insert (0 : Fin (n + 1) → ℝ) (Sphere.F K) =
      {0} ∪ closure (Sphere.F K) := by
    conv_lhs => rw [h]
    ext v
    by_cases hv : v = 0 <;> simp [hv]
  rw [e]
  exact isClosed_singleton.union isClosed_closure

/-- The interior of a convex body is a convex cone: `F(int K) = int F(K)` is convex. -/
theorem convex_F_interior (hK : IsCorpsConvexeS n K) : Convex ℝ (Sphere.F (interior K)) := by
  rw [Sphere.F_interior]
  exact hK.convex_F.interior

/-- **A convex body lies in an open hemisphere**: some linear form is positive on `F(K)`. (For
each point of `K`, separate the opposite ray from the closed convex cone `F(K) ∪ {O}`; finitely
many of the resulting forms suffice, by compactness, and their sum works.) -/
theorem exists_forall_pos (hK : IsCorpsConvexeS n K) :
    ∃ ℓ : StrongDual ℝ (Fin (n + 1) → ℝ), ∀ v ∈ Sphere.F K, 0 < ℓ v := by
  have hloc : ∀ X ∈ K, ∃ f : StrongDual ℝ (Fin (n + 1) → ℝ), (∀ v ∈ Sphere.F K, 0 ≤ f v) ∧
      X ∈ Sphere.openHemisphere (f : Module.Dual ℝ (Fin (n + 1) → ℝ)) := by
    intro X hX
    obtain ⟨x, hx0, rfl⟩ := Sphere.exists_isRep X
    have hnx : -x ∉ insert (0 : Fin (n + 1) → ℝ) (Sphere.F K) := by
      rintro (h | ⟨h0, hk⟩)
      · exact hx0 (neg_eq_zero.1 h)
      · apply hK.neg_notMem hX
        rwa [Sphere.neg_mk]
    obtain ⟨f, u, hfu, hf⟩ :=
      geometric_hahn_banach_point_closed hK.1.1 hK.isClosed_insert_zero_F hnx
    have hu : u < 0 := by simpa using hf 0 (mem_insert _ _)
    refine ⟨f, fun v hv => ?_, ?_⟩
    · by_contra hneg
      push Not at hneg
      have := hf ((u / f v) • v)
        (mem_insert_of_mem _ (Sphere.smul_mem_F hv (div_pos_of_neg_of_neg hu hneg)))
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
      exact lt_irrefl _ this
    · rw [Sphere.mk_mem_openHemisphere]
      have : f (-x) < 0 := hfu.trans hu
      simpa using this
  choose! f hf0 hfX using hloc
  obtain ⟨t, ht⟩ := hK.2.1.elim_finite_subcover
    (fun X : K => Sphere.openHemisphere (f X : Module.Dual ℝ (Fin (n + 1) → ℝ)))
    (fun X => Sphere.isOpen_openHemisphere (f X)) (fun X hX => mem_iUnion.2 ⟨⟨X, hX⟩, hfX X hX⟩)
  refine ⟨∑ i ∈ t, f i, fun v hv => ?_⟩
  rw [_root_.sum_apply]
  refine Finset.sum_pos' (fun i _ => hf0 i i.2 v hv) ?_
  obtain ⟨hv0, hvK⟩ := hv
  obtain ⟨i, hi, hiv⟩ := mem_iUnion₂.1 (ht hvK)
  exact ⟨i, hi, by simpa using (Sphere.mk_mem_openHemisphere hv0).1 hiv⟩

/-- On the cone of a convex body a positive form is bounded below by a multiple of the norm. -/
theorem exists_mul_norm_le (hK : IsCorpsConvexeS n K) {ℓ : StrongDual ℝ (Fin (n + 1) → ℝ)}
    (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v) :
    ∃ c > 0, ∀ v ∈ Sphere.F K, c * ‖v‖ ≤ ℓ v := by
  let g : S n → ℝ := fun X => ℓ (Sphere.homeomorphUnitSphere X : Fin (n + 1) → ℝ)
  have hg : Continuous g :=
    ℓ.continuous.comp (continuous_subtype_val.comp Sphere.homeomorphUnitSphere.continuous)
  have hgK : ∀ X ∈ K, 0 < g X := by
    intro X hX
    obtain ⟨x, hx0, rfl⟩ := Sphere.exists_isRep X
    simp only [g, Sphere.homeomorphUnitSphere_mk]
    exact hℓ _ (Sphere.smul_mem_F ⟨hx0, hX⟩ (inv_pos.2 (norm_pos_iff.2 hx0)))
  obtain ⟨X₀, hX₀, hmin⟩ := hK.2.1.exists_isMinOn
    (hK.2.2.mono interior_subset) hg.continuousOn
  refine ⟨g X₀, hgK X₀ hX₀, fun v hv => ?_⟩
  obtain ⟨hv0, hvK⟩ := hv
  have h1 : g X₀ ≤ g (Sphere.mk v hv0) := hmin hvK
  simp only [g, Sphere.homeomorphUnitSphere_mk, map_smul, smul_eq_mul] at h1
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  rwa [le_inv_mul_iff₀ hn, mul_comm] at h1

end IsCorpsConvexeS

/-! #### The line `AB` in the hemisphere `ℓ > 0`, parametrised by `t ↦ a + t (b − a)` -/

variable {ℓ : StrongDual ℝ (Fin (n + 1) → ℝ)} {a b : Fin (n + 1) → ℝ}

/-- The parameters `t` for which `a + t (b − a)` lies in the cone `F(K)`. -/
def paramSet (K : Set (S n)) (a b : Fin (n + 1) → ℝ) : Set ℝ :=
  {t | a + t • (b - a) ∈ Sphere.F K}

theorem map_param (hla : ℓ a = 1) (hlb : ℓ b = 1) (t : ℝ) : ℓ (a + t • (b - a)) = 1 := by
  simp [hla, hlb]

theorem param_ne_zero (hla : ℓ a = 1) (hlb : ℓ b = 1) (t : ℝ) : a + t • (b - a) ≠ 0 := fun h => by
  have := map_param hla hlb t
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem convex_paramSet (hK : IsCorpsConvexeS n K) (a b : Fin (n + 1) → ℝ) :
    Convex ℝ (paramSet K a b) := by
  intro t₁ h₁ t₂ h₂ θ₁ θ₂ hθ₁ hθ₂ hθ
  have := hK.convex_F h₁ h₂ hθ₁ hθ₂ hθ
  have e : θ₁ • (a + t₁ • (b - a)) + θ₂ • (a + t₂ • (b - a)) =
      (θ₁ + θ₂) • a + (θ₁ * t₁ + θ₂ * t₂) • (b - a) := by module
  rw [e, hθ, one_smul] at this
  simpa [paramSet, smul_eq_mul] using this

theorem isClosed_paramSet (hK : IsCorpsConvexeS n K) (hla : ℓ a = 1) (hlb : ℓ b = 1) :
    IsClosed (paramSet K a b) := by
  have e : paramSet K a b = (fun t : ℝ => a + t • (b - a)) ⁻¹' insert 0 (Sphere.F K) := by
    ext t
    simp only [paramSet, mem_setOf_eq, mem_preimage, mem_insert_iff]
    exact ⟨Or.inr, fun h => h.resolve_left (param_ne_zero hla hlb t)⟩
  rw [e]
  exact hK.isClosed_insert_zero_F.preimage (by fun_prop)

theorem paramSet_subset_Icc (hK : IsCorpsConvexeS n K) (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v)
    (hla : ℓ a = 1) (hlb : ℓ b = 1) (hab : a ≠ b) : ∃ M : ℝ, paramSet K a b ⊆ Icc (-M) M := by
  obtain ⟨c, hc, hcv⟩ := hK.exists_mul_norm_le hℓ
  have hba : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hab))
  refine ⟨(1 / c + ‖a‖) / ‖b - a‖, fun t ht => ?_⟩
  have h1 := hcv _ ht
  rw [map_param hla hlb] at h1
  have h2 : ‖a + t • (b - a)‖ ≤ 1 / c := by rw [le_div_iff₀ hc]; linarith
  have h3 : |t| * ‖b - a‖ ≤ 1 / c + ‖a‖ := by
    calc |t| * ‖b - a‖ = ‖t • (b - a)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖(a + t • (b - a)) - a‖ := by congr 1; abel
      _ ≤ ‖a + t • (b - a)‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ 1 / c + ‖a‖ := by linarith
  have h4 : |t| ≤ (1 / c + ‖a‖) / ‖b - a‖ := by rw [le_div_iff₀ hba]; exact h3
  exact ⟨(abs_le.1 h4).1, (abs_le.1 h4).2⟩

/-- Near a parameter whose point is interior, the parameters stay interior. -/
theorem eventually_mem_interior_param {t₀ : ℝ}
    (h : a + t₀ • (b - a) ∈ interior (Sphere.F K)) :
    ∀ᶠ t in 𝓝 t₀, a + t • (b - a) ∈ interior (Sphere.F K) :=
  ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt (x := t₀)).eventually
    (isOpen_interior.mem_nhds h)

/-- **The parameters of the chord**: for `A ≠ B` interior, with representatives `a`, `b` on
`ℓ = 1`, the parameters of the points of `K` on the line `AB` form an interval `[t₋, t₊]` with
`t₋ < 0` and `t₊ > 1` (`t₋ = inf`, `t₊ = sup`). -/
theorem paramSet_eq_Icc (hK : IsCorpsConvexeS n K) (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v)
    (hla : ℓ a = 1) (hlb : ℓ b = 1) (hab : a ≠ b) (ha : a ∈ interior (Sphere.F K))
    (hb : b ∈ interior (Sphere.F K)) :
    paramSet K a b = Icc (sInf (paramSet K a b)) (sSup (paramSet K a b)) ∧
      sInf (paramSet K a b) < 0 ∧ 1 < sSup (paramSet K a b) := by
  set T := paramSet K a b with hT
  obtain ⟨M, hM⟩ := paramSet_subset_Icc hK hℓ hla hlb hab
  have hbdA : BddAbove T := ⟨M, fun t ht => (hM ht).2⟩
  have hbdB : BddBelow T := ⟨-M, fun t ht => (hM ht).1⟩
  have h0 : (0 : ℝ) ∈ T := by
    show a + (0 : ℝ) • (b - a) ∈ Sphere.F K
    rw [zero_smul, add_zero]; exact interior_subset ha
  have hne : T.Nonempty := ⟨0, h0⟩
  have hcl := isClosed_paramSet hK hla hlb
  have hmin := hcl.csInf_mem hne hbdB
  have hmax := hcl.csSup_mem hne hbdA
  refine ⟨Subset.antisymm (fun t ht => ⟨csInf_le hbdB ht, le_csSup hbdA ht⟩)
    ((convex_iff_ordConnected.1 (convex_paramSet hK a b)).out hmin hmax), ?_, ?_⟩
  · have h := eventually_mem_interior_param (K := K) (a := a) (b := b) (t₀ := 0)
      (by rwa [zero_smul, add_zero])
    obtain ⟨t, ht, ht0⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Iio (0 : ℝ)))).exists
    exact (csInf_le hbdB (show t ∈ T from interior_subset (s := Sphere.F K) ht)).trans_lt ht0
  · have h := eventually_mem_interior_param (K := K) (a := a) (b := b) (t₀ := 1)
      (by rwa [one_smul, add_sub_cancel])
    obtain ⟨t, ht, ht1⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))).exists
    exact (show (1 : ℝ) < t from ht1).trans_le
      (le_csSup hbdA (show t ∈ T from interior_subset (s := Sphere.F K) ht))

/-- Between `a` and a parameter of `K`, the points are interior. -/
theorem mem_interior_param_of_mem_openSegment (hK : IsCorpsConvexeS n K)
    (ha : a ∈ interior (Sphere.F K)) {t₀ : ℝ} (ht₀ : t₀ ∈ paramSet K a b) {θ : ℝ} (hθ₀ : 0 < θ)
    (hθ₁ : θ < 1) : a + (θ * t₀) • (b - a) ∈ interior (Sphere.F K) := by
  refine hK.convex_F.openSegment_interior_self_subset_interior ha ht₀
    ⟨1 - θ, θ, by linarith, hθ₀, by ring, ?_⟩
  module

/-- **The open chord is interior**: the points of parameter `t ∈ (t₋, t₊)` are in `int K`. -/
theorem mem_interior_of_mem_Ioo (hK : IsCorpsConvexeS n K) (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v)
    (hla : ℓ a = 1) (hlb : ℓ b = 1) (hab : a ≠ b) (ha : a ∈ interior (Sphere.F K))
    (hb : b ∈ interior (Sphere.F K)) {t : ℝ}
    (ht : t ∈ Ioo (sInf (paramSet K a b)) (sSup (paramSet K a b))) :
    a + t • (b - a) ∈ interior (Sphere.F K) := by
  obtain ⟨hIcc, hm, hp⟩ := paramSet_eq_Icc hK hℓ hla hlb hab ha hb
  set T := paramSet K a b
  have hmT : sInf T ∈ T := hIcc.symm.subset ⟨le_rfl, by linarith⟩
  have hpT : sSup T ∈ T := hIcc.symm.subset ⟨by linarith, le_rfl⟩
  rcases lt_trichotomy t 0 with h | rfl | h
  · have := mem_interior_param_of_mem_openSegment hK ha hmT (θ := t / sInf T)
      (div_pos_of_neg_of_neg h hm) (by rw [div_lt_one_of_neg hm]; exact ht.1)
    rwa [div_mul_cancel₀ _ hm.ne] at this
  · rwa [zero_smul, add_zero]
  · have := mem_interior_param_of_mem_openSegment hK ha hpT (θ := t / sSup T)
      (div_pos h (by linarith)) (by rw [div_lt_one (by linarith)]; exact ht.2)
    rwa [div_mul_cancel₀ _ (by linarith)] at this

/-- **The ends of the chord are not interior.** -/
theorem notMem_interior_of_extreme (hK : IsCorpsConvexeS n K) (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v)
    (hla : ℓ a = 1) (hlb : ℓ b = 1) (hab : a ≠ b) :
    a + sInf (paramSet K a b) • (b - a) ∉ interior (Sphere.F K) ∧
      a + sSup (paramSet K a b) • (b - a) ∉ interior (Sphere.F K) := by
  obtain ⟨M, hM⟩ := paramSet_subset_Icc hK hℓ hla hlb hab
  have hbdA : BddAbove (paramSet K a b) := ⟨M, fun t ht => (hM ht).2⟩
  have hbdB : BddBelow (paramSet K a b) := ⟨-M, fun t ht => (hM ht).1⟩
  constructor
  · intro h
    obtain ⟨t, ht, hlt⟩ := (((eventually_mem_interior_param h).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Iio (sInf (paramSet K a b))))).exists
    exact (not_le.2 (show t < sInf (paramSet K a b) from hlt))
      (csInf_le hbdB (show t ∈ paramSet K a b from interior_subset (s := Sphere.F K) ht))
  · intro h
    obtain ⟨t, ht, hlt⟩ := (((eventually_mem_interior_param h).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (sSup (paramSet K a b))))).exists
    exact (not_le.2 (show sSup (paramSet K a b) < t from hlt))
      (le_csSup hbdA (show t ∈ paramSet K a b from interior_subset (s := Sphere.F K) ht))

/-- **The cross-ratio in the parameter**: `(A, B, G', G) = (0, 1, τ₊, τ₋)` for the points of
parameters `τ₋ < 0 < 1 < τ₊`. -/
theorem isCrossRatio_param (hla : ℓ a = 1) (hlb : ℓ b = 1) (hab : a ≠ b) {τm τp : ℝ}
    (hm : τm < 0) (hp : 1 < τp) {A B G G' : S n} (ha : Sphere.IsRep a A) (hb : Sphere.IsRep b B)
    (hG : Sphere.IsRep (a + τm • (b - a)) G) (hG' : Sphere.IsRep (a + τp • (b - a)) G') :
    Sphere.IsCrossRatio A B G' G (crossRatio 0 1 τp τm) := by
  have hli := linearIndependent_of_map_eq ℓ.toLinearMap hla (by simp [hla, hlb])
    (sub_ne_zero.2 (Ne.symm hab))
  exact Sphere.isCrossRatio_affine hli hm (by linarith) (by linarith) hp
    (by simpa using ha) (by simpa using hb) hG' hG

/-- A point of `K` on the line `AB` has a representative `a + t (b − a)`, `t` a parameter of `K`. -/
theorem exists_param_of_mem_lineThrough (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v) (hla : ℓ a = 1)
    (hlb : ℓ b = 1) {A B X : S n} (ha : Sphere.IsRep a A) (hb : Sphere.IsRep b B) (hXK : X ∈ K)
    (hXl : X ∈ Sphere.lineThrough A B) :
    ∃ t ∈ paramSet K a b, Sphere.IsRep (a + t • (b - a)) X := by
  obtain ⟨x, y, hX⟩ := (Sphere.mem_lineThrough_iff ha hb).1 hXl
  have hF : x • a + y • b ∈ Sphere.F K := ⟨hX.ne_zero, by rw [hX.2]; exact hXK⟩
  have hpos : 0 < x + y := by
    have := hℓ _ hF
    simpa [hla, hlb] using this
  have e : a + (y / (x + y)) • (b - a) = (x + y)⁻¹ • (x • a + y • b) := by
    have := hpos.ne'
    match_scalars
    · field_simp
      ring
    · field_simp
  refine ⟨y / (x + y), ?_, ?_⟩
  · show a + (y / (x + y)) • (b - a) ∈ Sphere.F K
    rw [e]; exact Sphere.smul_mem_F hF (inv_pos.2 hpos)
  · rw [e]; exact hX.smul (inv_pos.2 hpos)

/-- If the parameters of `K` lie in `[τ₋, τ₊]`, every point of `K` on the line `AB` lies on the
segment `(G, G')` of the points of parameters `τ₋`, `τ₊`. -/
theorem mem_closedSeg_of_paramSet_subset (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v) (hla : ℓ a = 1)
    (hlb : ℓ b = 1) {A B G G' : S n} (ha : Sphere.IsRep a A) (hb : Sphere.IsRep b B)
    {τm τp : ℝ} (hττ : τm < τp) (hT : paramSet K a b ⊆ Icc τm τp)
    (hG : Sphere.IsRep (a + τm • (b - a)) G) (hG' : Sphere.IsRep (a + τp • (b - a)) G') :
    ∀ X ∈ K, X ∈ Sphere.lineThrough A B → X ∈ Sphere.closedSeg G G' := by
  intro X hXK hXl
  obtain ⟨t, ht, hX⟩ := exists_param_of_mem_lineThrough hℓ hla hlb ha hb hXK hXl
  obtain ⟨h1, h2⟩ := hT ht
  refine (Sphere.mem_closedSeg_iff hG hG').2 ⟨(τp - t) / (τp - τm), (t - τm) / (τp - τm),
    div_nonneg (by linarith) (by linarith), div_nonneg (by linarith) (by linarith), ?_⟩
  convert hX using 1
  have hne : τp - τm ≠ 0 := by linarith
  match_scalars <;> field_simp <;> ring

/-! #### The cross-ratio `(0, 1, τ₊, τ₋)` as a function of `τ₋ < 0 < 1 < τ₊` -/

theorem one_lt_crossRatio {τm τp : ℝ} (hm : τm < 0) (hp : 1 < τp) :
    1 < crossRatio 0 1 τp τm := by
  unfold crossRatio
  rw [sub_zero, sub_zero]
  have h1 : 1 < τp / (τp - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have h2 : 1 < (τm - 1) / τm := by rw [lt_div_iff_of_neg hm]; linarith
  calc (1 : ℝ) < τp / (τp - 1) := h1
    _ = τp / (τp - 1) * 1 := (mul_one _).symm
    _ < τp / (τp - 1) * ((τm - 1) / τm) := mul_lt_mul_of_pos_left h2 (by linarith)

theorem continuousAt_log_crossRatio {τm τp : ℝ} (hm : τm < 0) (hp : 1 < τp) :
    ContinuousAt (fun q : ℝ × ℝ => |Real.log (crossRatio 0 1 q.2 q.1)|) (τm, τp) := by
  have h1 : ContinuousAt (fun q : ℝ × ℝ => (q.2 - 0) / (q.2 - 1)) (τm, τp) :=
    (continuousAt_snd.sub continuousAt_const).div (continuousAt_snd.sub continuousAt_const)
      (by simp only; linarith)
  have h2 : ContinuousAt (fun q : ℝ × ℝ => (q.1 - 1) / (q.1 - 0)) (τm, τp) :=
    (continuousAt_fst.sub continuousAt_const).div (continuousAt_fst.sub continuousAt_const)
      (by simp only; linarith)
  have hne : (fun q : ℝ × ℝ => (q.2 - 0) / (q.2 - 1) * ((q.1 - 1) / (q.1 - 0))) (τm, τp) ≠ 0 :=
    (zero_lt_one.trans (one_lt_crossRatio hm hp)).ne'
  exact ((h1.mul h2).log hne).abs

/-- Moving the outer parameters inwards: the measure tends to the value at `(τ₋, τ₊)`. -/
theorem exists_inner_param {τm τp : ℝ} (hm : τm < 0) (hp : 1 < τp) {k : ℝ}
    (hk : |Real.log (crossRatio 0 1 τp τm)| < k) :
    ∃ σm σp : ℝ, τm < σm ∧ σm < 0 ∧ 1 < σp ∧ σp < τp ∧
      |Real.log (crossRatio 0 1 σp σm)| < k := by
  have hc := continuousAt_log_crossRatio hm hp
  have hpath : Tendsto (fun ε : ℝ => (τm + ε, τp - ε)) (𝓝 0) (𝓝 (τm, τp)) := by
    have : Continuous (fun ε : ℝ => (τm + ε, τp - ε)) := by fun_prop
    simpa using this.tendsto 0
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), |Real.log (crossRatio 0 1 (τp - ε) (τm + ε))| < k :=
    (hc.tendsto.comp hpath).eventually (eventually_lt_nhds hk)
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), τm + ε < 0 := by
    have : Tendsto (fun ε : ℝ => τm + ε) (𝓝 0) (𝓝 τm) := by
      simpa using (by fun_prop : Continuous fun ε : ℝ => τm + ε).tendsto (0 : ℝ)
    exact this.eventually (eventually_lt_nhds hm)
  have h3 : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 < τp - ε := by
    have : Tendsto (fun ε : ℝ => τp - ε) (𝓝 0) (𝓝 τp) := by
      simpa using (by fun_prop : Continuous fun ε : ℝ => τp - ε).tendsto (0 : ℝ)
    exact this.eventually (eventually_gt_nhds hp)
  obtain ⟨ε, ⟨⟨h1, h2⟩, h3⟩, hε⟩ := ((((h1.and h2).and h3).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  have hε' : (0 : ℝ) < ε := hε
  exact ⟨τm + ε, τp - ε, by linarith, h2, h3, by linarith, h1⟩

/-- Moving the outer parameters outwards: the measure tends to the value at `(τ₋, τ₊)`. -/
theorem exists_outer_param {τm τp : ℝ} (hm : τm < 0) (hp : 1 < τp) {k : ℝ}
    (hk : k < |Real.log (crossRatio 0 1 τp τm)|) :
    ∃ σm σp : ℝ, σm < τm ∧ τp < σp ∧ k < |Real.log (crossRatio 0 1 σp σm)| := by
  have hc := continuousAt_log_crossRatio hm hp
  have hpath : Tendsto (fun ε : ℝ => (τm - ε, τp + ε)) (𝓝 0) (𝓝 (τm, τp)) := by
    have : Continuous (fun ε : ℝ => (τm - ε, τp + ε)) := by fun_prop
    simpa using this.tendsto 0
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), k < |Real.log (crossRatio 0 1 (τp + ε) (τm - ε))| :=
    (hc.tendsto.comp hpath).eventually (eventually_gt_nhds hk)
  obtain ⟨ε, h1, hε⟩ := ((h1.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  have hε' : (0 : ℝ) < ε := hε
  exact ⟨τm - ε, τp + ε, by linarith, by linarith, h1⟩

/-! #### The interior `V` of a convex body as a locally projective manifold -/

/-- **The interior `V` of a part `K` of `S(n)`**, an open set, hence a locally projective manifold
(Mathlib's charted structure on an open subset). -/
abbrev corpsInterior (K : Set (S n)) : TopologicalSpace.Opens (S n) :=
  TopologicalSpace.Opens.interior K

/-- The segment of two points of the interior of a convex body lies in the interior. -/
theorem closedSeg_subset_interior (hK : IsCorpsConvexeS n K) {A B : S n} (hA : A ∈ interior K)
    (hB : B ∈ interior K) : Sphere.closedSeg A B ⊆ interior K := by
  obtain ⟨a, ha⟩ := Sphere.exists_isRep A
  obtain ⟨b, hb⟩ := Sphere.exists_isRep B
  exact Sphere.closedSeg_subset_of_convex ha hb hK.convex_F_interior
    ⟨ha.ne_zero, by rw [ha.2]; exact hA⟩ ⟨hb.ne_zero, by rw [hb.2]; exact hB⟩ subset_rfl

/-- **The segments of `V`**: two points of `V` are joined by exactly one segment of `V`, the
segment `(A, B)` of `S(n)`. So `l_V(A, B)` is a function of the pair of points. -/
theorem isProjSegment_corpsInterior_iff (hK : IsCorpsConvexeS n K) {A B : corpsInterior K}
    {Sg : Set (corpsInterior K)} :
    IsProjSegment n Sg A B ↔ Sg = Subtype.val ⁻¹' Sphere.closedSeg (A : S n) B := by
  rw [isProjSegment_opens_iff]
  refine ⟨fun h => h.2.2, fun h => ⟨fun hBA => hK.neg_notMem (interior_subset A.2)
    (hBA ▸ interior_subset B.2), closedSeg_subset_interior hK A.2 B.2, h⟩⟩

/-- **`l_V(A, B)`** on the interior `V` of a convex body: the pseudo-length (Déf. 3) of the segment
`(A, B)` of `V`, the only one (`isProjSegment_corpsInterior_iff`). -/
def hilbertLength (K : Set (S n)) (A B : corpsInterior K) : EReal :=
  pseudoLength n (Subtype.val ⁻¹' Sphere.closedSeg (A : S n) B : Set (corpsInterior K)) A B

theorem isProjSegment_hilbert (hK : IsCorpsConvexeS n K) (A B : corpsInterior K) :
    IsProjSegment n (Subtype.val ⁻¹' Sphere.closedSeg (A : S n) B : Set (corpsInterior K)) A B :=
  (isProjSegment_corpsInterior_iff hK).2 rfl

theorem pseudoLength_eq_hilbertLength (hK : IsCorpsConvexeS n K) {A B : corpsInterior K}
    {Sg : Set (corpsInterior K)} (hSg : IsProjSegment n Sg A B) :
    pseudoLength n Sg A B = hilbertLength K A B := by
  rw [(isProjSegment_corpsInterior_iff hK).1 hSg, hilbertLength]

/-- A point of `K` has a representative on `ℓ = 1`. -/
theorem exists_isRep_map_eq_one (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v) {X : S n} (hX : X ∈ K) :
    ∃ x, Sphere.IsRep x X ∧ ℓ x = 1 := by
  obtain ⟨x, hx⟩ := Sphere.exists_isRep X
  have hpos : 0 < ℓ x := hℓ x ⟨hx.ne_zero, by rw [hx.2]; exact hX⟩
  exact ⟨(ℓ x)⁻¹ • x, hx.smul (inv_pos.2 hpos), by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hpos.ne']⟩

theorem mem_interior_F_of_isRep {x : Fin (n + 1) → ℝ} {X : S n} (hx : Sphere.IsRep x X)
    (hX : X ∈ interior K) : x ∈ interior (Sphere.F K) := by
  rw [← Sphere.F_interior]
  exact ⟨hx.ne_zero, by rw [hx.2]; exact hX⟩

/-- **Prop. 2, first assertion, in the parameter**: for `A ≠ B` in `V`, with representatives `a`,
`b` on `ℓ = 1`, `l_V(A, B) = |log (0, 1, t₊, t₋)|`, `t₋ < 0 < 1 < t₊` the parameters of the ends of
the chord. -/
theorem pseudoLength_eq_param (hK : IsCorpsConvexeS n K) (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v)
    {A B : corpsInterior K} (hAB : A ≠ B) (ha : Sphere.IsRep a (A : S n))
    (hb : Sphere.IsRep b (B : S n)) (hla : ℓ a = 1) (hlb : ℓ b = 1) {Sg : Set (corpsInterior K)}
    (hSg : IsProjSegment n Sg A B) :
    pseudoLength n Sg A B =
      ((|Real.log (crossRatio 0 1 (sSup (paramSet K a b)) (sInf (paramSet K a b)))| : ℝ) :
        EReal) := by
  have hab : a ≠ b := fun h => hAB (Subtype.ext (ha.eq (h ▸ hb)))
  have ha' := mem_interior_F_of_isRep ha A.2
  have hb' := mem_interior_F_of_isRep hb B.2
  obtain ⟨hIcc, hm, hp⟩ := paramSet_eq_Icc hK hℓ hla hlb hab ha' hb'
  set tm := sInf (paramSet K a b)
  set tp := sSup (paramSet K a b)
  have hG := Sphere.isRep_mk _ (param_ne_zero hla hlb tm)
  have hG' := Sphere.isRep_mk _ (param_ne_zero hla hlb tp)
  have hcr := isCrossRatio_param hla hlb hab hm hp ha hb hG hG'
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    induction c using EReal.rec with
    | bot => exact absurd hc not_lt_bot
    | top => exact le_top
    | coe k =>
      obtain ⟨σm, σp, h1, h2, h3, h4, h5⟩ := exists_inner_param hm hp (EReal.coe_lt_coe_iff.1 hc)
      have hS := Sphere.isRep_mk _ (param_ne_zero hla hlb σm)
      have hS' := Sphere.isRep_mk _ (param_ne_zero hla hlb σp)
      have hcr₁ := isCrossRatio_param hla hlb hab h2 h3 ha hb hS hS'
      have hmem := hcr₁.mem_openSeg
      have hsub : Sphere.closedSeg (Sphere.mk _ (param_ne_zero hla hlb σm))
          (Sphere.mk _ (param_ne_zero hla hlb σp)) ⊆ (corpsInterior K : Set (S n)) := by
        refine Sphere.closedSeg_subset_of_convex hS hS' hK.convex_F_interior ?_ ?_ subset_rfl
        · rw [Sphere.F_interior]
          exact mem_interior_of_mem_Ioo hK hℓ hla hlb hab ha' hb' ⟨h1, by linarith⟩
        · rw [Sphere.F_interior]
          exact mem_interior_of_mem_Ioo hK hℓ hla hlb hab ha' hb' ⟨by linarith, h4⟩
      have := pseudoLength_le_projMeasure_opens hSg
        (ne_neg_of_map_pos ℓ.toLinearMap hS hS' (by simp [hla, hlb]) (by simp [hla, hlb])) hsub
        (Sphere.openSeg_subset_closedSeg _ _ hmem.1) (Sphere.openSeg_subset_closedSeg _ _ hmem.2)
      rw [Sphere.projMeasure_eq hcr₁] at this
      exact this.trans (EReal.coe_le_coe_iff.2 h5.le)
  · have := projMeasure_le_pseudoLength_opens (K := K) interior_subset hSg hAB
      (mem_closedSeg_of_paramSet_subset hℓ hla hlb ha hb (by linarith) hIcc.subset hG hG')
    rwa [Sphere.projMeasure_eq hcr] at this

/-- **The chord of `AB`**: for `A ≠ B` in `V`, the line `AB` meets the frontier of `K` in exactly
two points, those of parameters `t₋`, `t₊`. -/
theorem lineThrough_inter_frontier (hK : IsCorpsConvexeS n K) (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v)
    {A B : corpsInterior K} (hAB : A ≠ B) (ha : Sphere.IsRep a (A : S n))
    (hb : Sphere.IsRep b (B : S n)) (hla : ℓ a = 1) (hlb : ℓ b = 1) :
    Sphere.lineThrough (A : S n) B ∩ frontier K =
        {Sphere.mk _ (param_ne_zero hla hlb (sInf (paramSet K a b))),
          Sphere.mk _ (param_ne_zero hla hlb (sSup (paramSet K a b)))} ∧
      Sphere.mk _ (param_ne_zero hla hlb (sInf (paramSet K a b))) ≠
        Sphere.mk _ (param_ne_zero hla hlb (sSup (paramSet K a b))) := by
  have hab : a ≠ b := fun h => hAB (Subtype.ext (ha.eq (h ▸ hb)))
  have ha' := mem_interior_F_of_isRep ha A.2
  have hb' := mem_interior_F_of_isRep hb B.2
  obtain ⟨hIcc, hm, hp⟩ := paramSet_eq_Icc hK hℓ hla hlb hab ha' hb'
  obtain ⟨hnm, hnp⟩ := notMem_interior_of_extreme hK hℓ hla hlb hab
  set tm := sInf (paramSet K a b)
  set tp := sSup (paramSet K a b)
  have hG := Sphere.isRep_mk _ (param_ne_zero hla hlb tm)
  have hG' := Sphere.isRep_mk _ (param_ne_zero hla hlb tp)
  rw [hK.isClosed.frontier_eq]
  -- the point of parameter `t` is on the line, in `K` iff `t ∈ [t₋, t₊]`,
  -- interior iff `t ∈ (t₋, t₊)`
  have hline : ∀ t : ℝ, Sphere.mk _ (param_ne_zero hla hlb t) ∈ Sphere.lineThrough (A : S n) B :=
    fun t => (Sphere.mem_lineThrough_iff ha hb).2 ⟨1 - t, t, by
      convert Sphere.isRep_mk _ (param_ne_zero hla hlb t) using 1; module⟩
  have hK' : ∀ t ∈ paramSet K a b, Sphere.mk _ (param_ne_zero hla hlb t) ∈ K := fun t ht => ht.2
  have hint : ∀ t : ℝ, Sphere.mk _ (param_ne_zero hla hlb t) ∈ interior K ↔
      a + t • (b - a) ∈ interior (Sphere.F K) := by
    intro t
    rw [← Sphere.F_interior]
    exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  have hmT : tm ∈ paramSet K a b := hIcc.symm.subset ⟨le_rfl, by linarith⟩
  have hpT : tp ∈ paramSet K a b := hIcc.symm.subset ⟨by linarith, le_rfl⟩
  refine ⟨Subset.antisymm ?_ ?_, ?_⟩
  · rintro X ⟨hXl, hXK, hXi⟩
    obtain ⟨t, ht, hX⟩ := exists_param_of_mem_lineThrough hℓ hla hlb ha hb hXK hXl
    have hX' : X = Sphere.mk _ (param_ne_zero hla hlb t) := hX.eq (Sphere.isRep_mk _ _)
    rw [hIcc] at ht
    rcases eq_or_lt_of_le ht.1 with h1 | h1
    · left; rw [hX', h1]
    rcases eq_or_lt_of_le ht.2 with h2 | h2
    · right; rw [mem_singleton_iff, hX', h2]
    exact absurd (hX' ▸ (hint t).2 (mem_interior_of_mem_Ioo hK hℓ hla hlb hab ha' hb' ⟨h1, h2⟩))
      hXi
  · rintro X (rfl | h)
    · exact ⟨hline tm, hK' tm hmT, fun h => hnm ((hint tm).1 h)⟩
    · rw [mem_singleton_iff] at h
      subst h
      exact ⟨hline tp, hK' tp hpT, fun h => hnp ((hint tp).1 h)⟩
  · intro h
    obtain ⟨c, hc, hce⟩ := hG.exists_pos (h ▸ hG')
    have h1 := congrArg ℓ hce
    rw [map_param hla hlb, map_smul, map_param hla hlb, smul_eq_mul, mul_one] at h1
    rw [← h1, one_smul] at hce
    have h2 : (tp - tm) • (b - a) = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 (add_left_cancel hce)
    rcases smul_eq_zero.1 h2 with h3 | h3
    · linarith [sub_eq_zero.1 h3]
    · exact hab (sub_eq_zero.1 h3).symm

/-- **Prop. 2, first assertion** (any dimension): if `F ≠ F'` are the points where the line `AB`
meets the frontier of `K`, then `l_V(A, B)` is the projective measure of `AB` relative to `FF'`
(for every segment of `V` from `A` to `B`; there is only one). For `A = B` the hypothesis cannot
hold (`{A, −A}` misses the frontier). -/
theorem pseudoLength_eq_projMeasure (hK : IsCorpsConvexeS n K) {A B : corpsInterior K}
    {Sg : Set (corpsInterior K)} (hSg : IsProjSegment n Sg A B) {F F' : S n} (hFF' : F ≠ F')
    (hline : Sphere.lineThrough (A : S n) B ∩ frontier K = {F, F'}) :
    pseudoLength n Sg A B = Sphere.projMeasure F A B F' := by
  obtain ⟨ℓ, hℓ⟩ := hK.exists_forall_pos
  by_cases hAB : A = B
  · subst hAB
    exfalso
    have hF : F ∈ Sphere.lineThrough (A : S n) A ∩ frontier K := hline ▸ mem_insert _ _
    obtain ⟨hFl, hFf⟩ := hF
    rcases Sphere.lineThrough_self_subset _ hFl with h | h
    · rw [mem_singleton_iff.1 (mem_singleton_iff.2 h)] at hFf
      exact hFf.2 A.2
    · rw [mem_singleton_iff] at h
      rw [h, hK.isClosed.frontier_eq] at hFf
      exact hK.neg_notMem (interior_subset A.2) hFf.1
  obtain ⟨a, ha, hla⟩ := exists_isRep_map_eq_one hℓ (interior_subset A.2)
  obtain ⟨b, hb, hlb⟩ := exists_isRep_map_eq_one hℓ (interior_subset B.2)
  have hab : a ≠ b := fun h => hAB (Subtype.ext (ha.eq (h ▸ hb)))
  obtain ⟨-, hm, hp⟩ := paramSet_eq_Icc hK hℓ hla hlb hab (mem_interior_F_of_isRep ha A.2)
    (mem_interior_F_of_isRep hb B.2)
  obtain ⟨hlf, -⟩ := lineThrough_inter_frontier hK hℓ hAB ha hb hla hlb
  rw [hline] at hlf
  rw [pseudoLength_eq_param hK hℓ hAB ha hb hla hlb hSg]
  have hcr := isCrossRatio_param hla hlb hab hm hp ha hb
    (Sphere.isRep_mk _ (param_ne_zero hla hlb (sInf (paramSet K a b))))
    (Sphere.isRep_mk _ (param_ne_zero hla hlb (sSup (paramSet K a b))))
  rcases Set.pair_eq_pair_iff.1 hlf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [Sphere.projMeasure_eq hcr]
  · rw [Sphere.projMeasure_reverse, Sphere.projMeasure_swap, Sphere.projMeasure_eq hcr]

/-- **The line `AB` meets the frontier in two points** (the « $F$, $F'$ » of Prop. 2), for
`A ≠ B` in `V`; and `A`, `B` lie strictly between them. -/
theorem exists_frontier_pair (hK : IsCorpsConvexeS n K) {A B : corpsInterior K} (hAB : A ≠ B) :
    ∃ F F' : S n, F ≠ F' ∧ Sphere.lineThrough (A : S n) B ∩ frontier K = {F, F'} ∧
      (A : S n) ∈ Sphere.openSeg F F' ∧ (B : S n) ∈ Sphere.openSeg F F' := by
  obtain ⟨ℓ, hℓ⟩ := hK.exists_forall_pos
  obtain ⟨a, ha, hla⟩ := exists_isRep_map_eq_one hℓ (interior_subset A.2)
  obtain ⟨b, hb, hlb⟩ := exists_isRep_map_eq_one hℓ (interior_subset B.2)
  have hab : a ≠ b := fun h => hAB (Subtype.ext (ha.eq (h ▸ hb)))
  obtain ⟨-, hm, hp⟩ := paramSet_eq_Icc hK hℓ hla hlb hab (mem_interior_F_of_isRep ha A.2)
    (mem_interior_F_of_isRep hb B.2)
  obtain ⟨hlf, hne⟩ := lineThrough_inter_frontier hK hℓ hAB ha hb hla hlb
  have hcr := isCrossRatio_param hla hlb hab hm hp ha hb
    (Sphere.isRep_mk _ (param_ne_zero hla hlb (sInf (paramSet K a b))))
    (Sphere.isRep_mk _ (param_ne_zero hla hlb (sSup (paramSet K a b))))
  exact ⟨_, _, hne, hlf, hcr.mem_openSeg⟩

/-! #### Continuity of `l_V` on `V × V` -/

/-- The representative of `X` on `ℓ = 1`, through the unit sphere (continuous where `ℓ > 0`). -/
def nrm (ℓ : StrongDual ℝ (Fin (n + 1) → ℝ)) (X : S n) : Fin (n + 1) → ℝ :=
  (ℓ (Sphere.homeomorphUnitSphere X : Fin (n + 1) → ℝ))⁻¹ •
    (Sphere.homeomorphUnitSphere X : Fin (n + 1) → ℝ)

theorem isRep_homeomorphUnitSphere (X : S n) :
    Sphere.IsRep (Sphere.homeomorphUnitSphere X : Fin (n + 1) → ℝ) X := by
  have := Sphere.homeomorphUnitSphere_symm_apply (Sphere.homeomorphUnitSphere X)
  rw [Homeomorph.symm_apply_apply] at this
  exact ⟨_, this.symm⟩

theorem nrm_spec (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v) {X : S n} (hX : X ∈ K) :
    Sphere.IsRep (nrm ℓ X) X ∧ ℓ (nrm ℓ X) = 1 := by
  have hu := isRep_homeomorphUnitSphere X
  have hpos : 0 < ℓ (Sphere.homeomorphUnitSphere X : Fin (n + 1) → ℝ) :=
    hℓ _ ⟨hu.ne_zero, by rw [hu.2]; exact hX⟩
  exact ⟨hu.smul (inv_pos.2 hpos), by rw [nrm, map_smul, smul_eq_mul, inv_mul_cancel₀ hpos.ne']⟩

theorem continuous_nrm_corpsInterior (hℓ : ∀ v ∈ Sphere.F K, 0 < ℓ v) :
    Continuous (fun P : corpsInterior K => nrm ℓ (P : S n)) := by
  have hu : Continuous (fun P : corpsInterior K =>
      (Sphere.homeomorphUnitSphere (P : S n) : Fin (n + 1) → ℝ)) :=
    continuous_subtype_val.comp (Sphere.homeomorphUnitSphere.continuous.comp continuous_subtype_val)
  have hpos : ∀ P : corpsInterior K,
      ℓ (Sphere.homeomorphUnitSphere (P : S n) : Fin (n + 1) → ℝ) ≠ 0 := fun P => by
    have hu' := isRep_homeomorphUnitSphere (P : S n)
    exact (hℓ _ ⟨hu'.ne_zero, by rw [hu'.2]; exact interior_subset P.2⟩).ne'
  exact ((ℓ.continuous.comp hu).inv₀ hpos).smul hu

/-- **Prop. 2, second assertion, continuity** (any dimension): `l_V` is continuous on `V × V`.
Lower semicontinuity: the chord of a nearby pair cannot reach beyond points of `K`'s complement
fixed in advance (`K` is closed); upper semicontinuity: a compact sub-chord stays interior (tube
lemma); in both the cross-ratio is the same constant, being read off the same parameters. On the
diagonal, the affine-ball estimate. -/
theorem continuous_hilbertLength (hK : IsCorpsConvexeS n K) :
    Continuous (fun p : corpsInterior K × corpsInterior K => hilbertLength K p.1 p.2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- dimension `0`: `V` has at most one point
    refine continuous_of_const fun p q => ?_
    have hsub : ∀ P Q : corpsInterior K, P = Q := fun P Q => Subtype.ext <| by
      rcases S0_eq_or_eq_neg (P : S 0) Q with h | h
      · exact h.symm
      · exact absurd (h ▸ interior_subset Q.2) (hK.neg_notMem (interior_subset P.2))
    rw [hsub p.1 q.1, hsub p.2 q.2]
  obtain ⟨ℓ, hℓ⟩ := hK.exists_forall_pos
  have hn' : 1 ≤ n := hn
  refine continuous_iff_continuousAt.2 fun ⟨A, B⟩ => ?_
  rw [ContinuousAt, tendsto_order]
  have hN : Continuous (fun P : corpsInterior K => nrm ℓ (P : S n)) :=
    continuous_nrm_corpsInterior hℓ
  by_cases hAB : A = B
  · subst hAB
    have h0 : hilbertLength K A A = 0 := pseudoLength_self hn' (isProjSegment_hilbert hK A A)
    refine ⟨fun k' hk' => Eventually.of_forall fun p => ?_, fun k' hk' => ?_⟩
    · exact (h0 ▸ hk').trans_le (pseudoLength_nonneg _ _ _)
    · change hilbertLength K A A < k' at hk'
      rw [h0] at hk'
      obtain ⟨k, hk0, hkk'⟩ := EReal.lt_iff_exists_real_btwn.1 hk'
      obtain ⟨W, hWo, hAW, hWT, hW⟩ :=
        exists_nhds_projMeasure_lt hn' isOpen_interior A.2 (EReal.coe_pos.1 hk0)
      have hev1 : ∀ᶠ p : corpsInterior K × corpsInterior K in 𝓝 (A, A), (p.1 : S n) ∈ W :=
        (hWo.preimage (continuous_subtype_val.comp continuous_fst)).mem_nhds hAW
      have hev2 : ∀ᶠ p : corpsInterior K × corpsInterior K in 𝓝 (A, A), (p.2 : S n) ∈ W :=
        (hWo.preimage (continuous_subtype_val.comp continuous_snd)).mem_nhds hAW
      filter_upwards [hev1, hev2] with p hp1 hp2
      obtain ⟨-, -, A', B', hBA', hsub, hPA, hQA, hlt⟩ := hW _ hp1 _ hp2
      exact (pseudoLength_le_projMeasure_opens (isProjSegment_hilbert hK p.1 p.2) hBA' hsub hPA
        hQA).trans_lt (hlt.trans hkk')
  -- `A ≠ B`
  obtain ⟨ha, hla⟩ := nrm_spec hℓ (interior_subset A.2)
  obtain ⟨hb, hlb⟩ := nrm_spec hℓ (interior_subset B.2)
  have hab : nrm ℓ (A : S n) ≠ nrm ℓ (B : S n) := fun h =>
    hAB (Subtype.ext (ha.eq (by rw [h]; exact hb)))
  have ha' := mem_interior_F_of_isRep ha A.2
  have hb' := mem_interior_F_of_isRep hb B.2
  obtain ⟨hIcc, hm, hp⟩ := paramSet_eq_Icc hK hℓ hla hlb hab ha' hb'
  have hval : hilbertLength K A B = _ :=
    pseudoLength_eq_param hK hℓ hAB ha hb hla hlb (isProjSegment_hilbert hK A B)
  have hne : ∀ᶠ p : corpsInterior K × corpsInterior K in 𝓝 (A, B), p.1 ≠ p.2 :=
    (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hAB
  have hΦ : ∀ σ : ℝ, Continuous (fun p : corpsInterior K × corpsInterior K =>
      nrm ℓ (p.1 : S n) + σ • (nrm ℓ (p.2 : S n) - nrm ℓ (p.1 : S n))) := fun σ =>
    (hN.comp continuous_fst).add (continuous_const.smul
      ((hN.comp continuous_snd).sub (hN.comp continuous_fst)))
  have hspec : ∀ p : corpsInterior K × corpsInterior K, p.1 ≠ p.2 →
      Sphere.IsRep (nrm ℓ (p.1 : S n)) (p.1 : S n) ∧ ℓ (nrm ℓ (p.1 : S n)) = 1 ∧
        Sphere.IsRep (nrm ℓ (p.2 : S n)) (p.2 : S n) ∧ ℓ (nrm ℓ (p.2 : S n)) = 1 ∧
        nrm ℓ (p.1 : S n) ≠ nrm ℓ (p.2 : S n) := fun p hp => by
    obtain ⟨hp1, hlp1⟩ := nrm_spec hℓ (interior_subset p.1.2)
    obtain ⟨hp2, hlp2⟩ := nrm_spec hℓ (interior_subset p.2.2)
    exact ⟨hp1, hlp1, hp2, hlp2, fun h => hp (Subtype.ext (hp1.eq (by rw [h]; exact hp2)))⟩
  refine ⟨fun k' hk' => ?_, fun k' hk' => ?_⟩
  · -- lower semicontinuity
    change k' < hilbertLength K A B at hk'
    rw [hval] at hk'
    obtain ⟨k, hk'k, hkv⟩ := EReal.lt_iff_exists_real_btwn.1 hk'
    obtain ⟨σm, σp, h1, h2, h3⟩ := exists_outer_param hm hp (EReal.coe_lt_coe_iff.1 hkv)
    have hout : ∀ σ, σ ∉ paramSet K (nrm ℓ (A : S n)) (nrm ℓ (B : S n)) →
        nrm ℓ (A : S n) + σ • (nrm ℓ (B : S n) - nrm ℓ (A : S n)) ∈
          (insert (0 : Fin (n + 1) → ℝ) (Sphere.F K))ᶜ :=
      fun σ hσ h => h.elim (param_ne_zero hla hlb σ) hσ
    have hσm : σm ∉ paramSet K (nrm ℓ (A : S n)) (nrm ℓ (B : S n)) := fun h => by
      rw [hIcc] at h; linarith [h.1]
    have hσp : σp ∉ paramSet K (nrm ℓ (A : S n)) (nrm ℓ (B : S n)) := fun h => by
      rw [hIcc] at h; linarith [h.2]
    have e1 : ∀ᶠ p : corpsInterior K × corpsInterior K in 𝓝 (A, B),
        nrm ℓ (p.1 : S n) + σm • (nrm ℓ (p.2 : S n) - nrm ℓ (p.1 : S n)) ∈
          (insert (0 : Fin (n + 1) → ℝ) (Sphere.F K))ᶜ :=
      (hK.isClosed_insert_zero_F.isOpen_compl.preimage (hΦ σm)).mem_nhds (hout σm hσm)
    have e2 : ∀ᶠ p : corpsInterior K × corpsInterior K in 𝓝 (A, B),
        nrm ℓ (p.1 : S n) + σp • (nrm ℓ (p.2 : S n) - nrm ℓ (p.1 : S n)) ∈
          (insert (0 : Fin (n + 1) → ℝ) (Sphere.F K))ᶜ :=
      (hK.isClosed_insert_zero_F.isOpen_compl.preimage (hΦ σp)).mem_nhds (hout σp hσp)
    filter_upwards [e1, e2, hne] with p h1' h2' h3'
    obtain ⟨hp1, hlp1, hp2, hlp2, hpq⟩ := hspec p h3'
    have hconv := convex_iff_ordConnected.1
      (convex_paramSet hK (nrm ℓ (p.1 : S n)) (nrm ℓ (p.2 : S n)))
    have h0 : (0 : ℝ) ∈ paramSet K (nrm ℓ (p.1 : S n)) (nrm ℓ (p.2 : S n)) := by
      show nrm ℓ (p.1 : S n) + (0 : ℝ) • (nrm ℓ (p.2 : S n) - nrm ℓ (p.1 : S n)) ∈ Sphere.F K
      rw [zero_smul, add_zero]
      exact ⟨hp1.ne_zero, by rw [hp1.2]; exact interior_subset p.1.2⟩
    have hsubI : paramSet K (nrm ℓ (p.1 : S n)) (nrm ℓ (p.2 : S n)) ⊆ Icc σm σp := by
      intro t ht
      constructor
      · by_contra hlt
        push Not at hlt
        exact h1' (Or.inr (hconv.out ht h0 ⟨hlt.le, by linarith⟩))
      · by_contra hlt
        push Not at hlt
        exact h2' (Or.inr (hconv.out h0 ht ⟨by linarith, hlt.le⟩))
    have hlow := projMeasure_le_pseudoLength_opens (K := K) interior_subset
      (isProjSegment_hilbert hK p.1 p.2) h3'
      (mem_closedSeg_of_paramSet_subset hℓ hlp1 hlp2 hp1 hp2 (by linarith) hsubI
        (Sphere.isRep_mk _ (param_ne_zero hlp1 hlp2 σm))
        (Sphere.isRep_mk _ (param_ne_zero hlp1 hlp2 σp)))
    rw [Sphere.projMeasure_eq (isCrossRatio_param hlp1 hlp2 hpq (by linarith) (by linarith) hp1
      hp2 (Sphere.isRep_mk _ (param_ne_zero hlp1 hlp2 σm))
      (Sphere.isRep_mk _ (param_ne_zero hlp1 hlp2 σp)))] at hlow
    exact hk'k.trans ((EReal.coe_lt_coe_iff.2 h3).trans_le hlow)
  · -- upper semicontinuity
    change hilbertLength K A B < k' at hk'
    rw [hval] at hk'
    obtain ⟨k, hvk, hkk'⟩ := EReal.lt_iff_exists_real_btwn.1 hk'
    obtain ⟨σm, σp, h1, h2, h3, h4, h5⟩ := exists_inner_param hm hp (EReal.coe_lt_coe_iff.1 hvk)
    have hin : ∀ t ∈ Icc σm σp,
        nrm ℓ (A : S n) + t • (nrm ℓ (B : S n) - nrm ℓ (A : S n)) ∈ interior (Sphere.F K) :=
      fun t ht => mem_interior_of_mem_Ioo hK hℓ hla hlb hab ha' hb'
        ⟨h1.trans_le ht.1, ht.2.trans_lt h4⟩
    have hc : Continuous (fun z : (corpsInterior K × corpsInterior K) × ℝ =>
        nrm ℓ (z.1.1 : S n) + z.2 • (nrm ℓ (z.1.2 : S n) - nrm ℓ (z.1.1 : S n))) :=
      (hN.comp (continuous_fst.comp continuous_fst)).add (continuous_snd.smul
        ((hN.comp (continuous_snd.comp continuous_fst)).sub
          (hN.comp (continuous_fst.comp continuous_fst))))
    have htube : ∀ᶠ p : corpsInterior K × corpsInterior K in 𝓝 (A, B), ∀ t ∈ Icc σm σp,
        nrm ℓ (p.1 : S n) + t • (nrm ℓ (p.2 : S n) - nrm ℓ (p.1 : S n)) ∈
          interior (Sphere.F K) :=
      isCompact_Icc.eventually_forall_of_forall_eventually fun t ht =>
        (isOpen_interior.preimage hc).mem_nhds (hin t ht)
    filter_upwards [htube, hne] with p h h3'
    obtain ⟨hp1, hlp1, hp2, hlp2, hpq⟩ := hspec p h3'
    have hS := Sphere.isRep_mk _ (param_ne_zero hlp1 hlp2 σm)
    have hS' := Sphere.isRep_mk _ (param_ne_zero hlp1 hlp2 σp)
    have hcr := isCrossRatio_param hlp1 hlp2 hpq h2 h3 hp1 hp2 hS hS'
    have hmem := hcr.mem_openSeg
    have hsub : Sphere.closedSeg (Sphere.mk _ (param_ne_zero hlp1 hlp2 σm))
        (Sphere.mk _ (param_ne_zero hlp1 hlp2 σp)) ⊆ (corpsInterior K : Set (S n)) := by
      refine Sphere.closedSeg_subset_of_convex hS hS' hK.convex_F_interior ?_ ?_ subset_rfl
      · rw [Sphere.F_interior]; exact h σm ⟨le_rfl, by linarith⟩
      · rw [Sphere.F_interior]; exact h σp ⟨by linarith, le_rfl⟩
    have := pseudoLength_le_projMeasure_opens (isProjSegment_hilbert hK p.1 p.2)
      (ne_neg_of_map_pos ℓ.toLinearMap hS hS' (by simp [hlp1, hlp2]) (by simp [hlp1, hlp2])) hsub
      (Sphere.openSeg_subset_closedSeg _ _ hmem.1) (Sphere.openSeg_subset_closedSeg _ _ hmem.2)
    rw [Sphere.projMeasure_eq hcr] at this
    exact this.trans_lt ((EReal.coe_lt_coe_iff.2 h5).trans hkk')

/-- **`l_V` vanishes only on the diagonal** (any dimension). -/
theorem hilbertLength_ne_zero (hK : IsCorpsConvexeS n K) {A B : corpsInterior K} (hAB : A ≠ B) :
    hilbertLength K A B ≠ 0 := by
  obtain ⟨ℓ, hℓ⟩ := hK.exists_forall_pos
  obtain ⟨a, ha, hla⟩ := exists_isRep_map_eq_one hℓ (interior_subset A.2)
  obtain ⟨b, hb, hlb⟩ := exists_isRep_map_eq_one hℓ (interior_subset B.2)
  have hab : a ≠ b := fun h => hAB (Subtype.ext (ha.eq (h ▸ hb)))
  obtain ⟨-, hm, hp⟩ := paramSet_eq_Icc hK hℓ hla hlb hab (mem_interior_F_of_isRep ha A.2)
    (mem_interior_F_of_isRep hb B.2)
  rw [hilbertLength, pseudoLength_eq_param hK hℓ hAB ha hb hla hlb (isProjSegment_hilbert hK A B)]
  intro h
  have h' := EReal.coe_eq_zero.1 h
  rw [abs_eq_zero] at h'
  have := Real.log_pos (one_lt_crossRatio hm hp)
  linarith

/-- **`l_V(A, B) = 0` iff `A = B`** (`n ≥ 1`; for `n = 0`, `l_V(A, A) = +∞`,
`hilbertLength_self_dim_zero`). -/
theorem hilbertLength_eq_zero_iff [NeZero n] (hK : IsCorpsConvexeS n K) (A B : corpsInterior K) :
    hilbertLength K A B = 0 ↔ A = B := by
  refine ⟨fun h => by_contra fun hAB => hilbertLength_ne_zero hK hAB h, ?_⟩
  rintro rfl
  exact pseudoLength_self (Nat.one_le_iff_ne_zero.2 (NeZero.ne n)) (isProjSegment_hilbert hK A A)

end Body

/-- **In dimension `0`, `l_V(A, A) = +∞`** on the interior of every convex body of `S(0)`. -/
theorem hilbertLength_self_dim_zero {K : Set (S 0)} (A : corpsInterior K) :
    hilbertLength K A A = ⊤ :=
  pseudoLength_eq_top_dim_zero _ _ _

/-! ### Prop. 2 and property 6° -/

section Prop2

variable {n : ℕ} {K : Set (S n)}

/-- **Prop. 2** (`bzprop:c2s2p2_pseudo_longueur_corps_convexe`, for `n ≥ 1`). Let `K` be a convex
body of `S(n)` with interior `V`. (0) The segments of `V` from `A` to `B` reduce to `(A, B)`, so
`l_V(A, B)` is `hilbertLength K A B`. (1) For `A ≠ B` the line `AB` meets the frontier of `K` in
two points `F ≠ F'`, and (2) `l_V(A, B)` is the projective measure of `AB` relative to `FF'`.
(3) `l_V` is continuous on `V × V` and (4) vanishes exactly on the diagonal. -/
theorem pseudo_longueur_corps_convexe [NeZero n] (hK : IsCorpsConvexeS n K) :
    (∀ (A B : corpsInterior K) (Sg : Set (corpsInterior K)),
      IsProjSegment n Sg A B ↔ Sg = Subtype.val ⁻¹' Sphere.closedSeg (A : S n) B) ∧
    (∀ A B : corpsInterior K, A ≠ B →
      ∃ F F' : S n, F ≠ F' ∧ Sphere.lineThrough (A : S n) B ∩ frontier K = {F, F'}) ∧
    (∀ (A B : corpsInterior K) (Sg : Set (corpsInterior K)), IsProjSegment n Sg A B →
      ∀ F F' : S n, F ≠ F' → Sphere.lineThrough (A : S n) B ∩ frontier K = {F, F'} →
        pseudoLength n Sg A B = Sphere.projMeasure F A B F') ∧
    Continuous (fun p : corpsInterior K × corpsInterior K => hilbertLength K p.1 p.2) ∧
    ∀ A B : corpsInterior K, hilbertLength K A B = 0 ↔ A = B :=
  ⟨fun _ _ _ => isProjSegment_corpsInterior_iff hK,
    fun _ _ hAB => (exists_frontier_pair hK hAB).imp fun _ h => h.imp fun _ h => ⟨h.1, h.2.1⟩,
    fun _ _ _ hSg _ _ hFF' hline => pseudoLength_eq_projMeasure hK hSg hFF' hline,
    continuous_hilbertLength hK, hilbertLength_eq_zero_iff hK⟩

/-- `l_V` is finite (`n ≥ 1`). -/
theorem hilbertLength_lt_top [NeZero n] (hK : IsCorpsConvexeS n K) (A B : corpsInterior K) :
    hilbertLength K A B < ⊤ :=
  pseudoLength_lt_top (Nat.one_le_iff_ne_zero.2 (NeZero.ne n)) (isProjSegment_hilbert hK A B)

/-- **`l_V` as a real function is continuous on `V × V`** (`n ≥ 1`, where it is finite). -/
theorem continuous_hilbertLength_toReal [NeZero n] (hK : IsCorpsConvexeS n K) :
    Continuous (fun p : corpsInterior K × corpsInterior K => (hilbertLength K p.1 p.2).toReal) ∧
      ∀ A B : corpsInterior K, ((hilbertLength K A B).toReal : EReal) = hilbertLength K A B := by
  have hfin : ∀ A B : corpsInterior K, hilbertLength K A B ≠ ⊥ ∧ hilbertLength K A B ≠ ⊤ :=
    fun A B => ⟨ne_bot_of_le_ne_bot EReal.zero_ne_bot (pseudoLength_nonneg _ _ _),
      (hilbertLength_lt_top hK A B).ne⟩
  refine ⟨EReal.continuousOn_toReal.comp_continuous (continuous_hilbertLength hK) fun p => ?_,
    fun A B => EReal.coe_toReal (hfin A B).2 (hfin A B).1⟩
  simp [(hfin p.1 p.2).1, (hfin p.1 p.2).2]

/-- **Property 6°** of the editorial enonce (`bzthm:c2s2_proprietes_pseudo_longueur`, l.249–251;
a lemma here, unmarked): « Si $V$ est l'intérieur d'un corps convexe, $l_V(M, N)$ est une fonction
continue en $M$ et $N$ sur le produit $V\times V$; $l_V(M, N)$ est nulle si et seulement si
$M=N$ » (`n ≥ 1`). -/
theorem propriete_six [NeZero n] (hK : IsCorpsConvexeS n K) :
    Continuous (fun p : corpsInterior K × corpsInterior K => hilbertLength K p.1 p.2) ∧
      ∀ M N : corpsInterior K, hilbertLength K M N = 0 ↔ M = N :=
  ⟨continuous_hilbertLength hK, hilbertLength_eq_zero_iff hK⟩

end Prop2

/-- A point of `S(0)` is a convex body of `S(0)`. -/
theorem isCorpsConvexeS_singleton_S0 (x : S 0) : IsCorpsConvexeS 0 {x} := by
  rw [isCorpsConvexeS_iff]
  refine ⟨?_, isCompact_singleton, ?_⟩
  · intro v hv w hw θ θ' hθ hθ' hθθ'
    obtain ⟨hv0, hvx⟩ := hv
    obtain ⟨hw0, hwx⟩ := hw
    rw [mem_singleton_iff] at hvx hwx
    obtain ⟨c, hc, rfl⟩ := (show Sphere.IsRep v x from ⟨hv0, hvx⟩).exists_pos ⟨hw0, hwx⟩
    have e : θ • v + θ' • (c • v) = (θ + θ' * c) • v := by module
    rw [e]
    have hpos : 0 < θ + θ' * c := by
      rcases hθ.lt_or_eq with h | h
      · positivity
      · rw [← h, zero_add] at hθθ' ⊢
        rw [hθθ', one_mul]
        exact hc
    exact Sphere.smul_mem_F ⟨hv0, by rw [mem_singleton_iff]; exact hvx⟩ hpos
  · rw [(isOpen_singleton_S0 x).interior_eq]
    exact singleton_nonempty x

/-- **Prop. 2 as printed** (assertions (2)–(4) of `pseudo_longueur_corps_convexe`, the last read
with 6°'s « si et seulement si »), for the convex bodies of `S(n)`. -/
def PseudoLongueurCorpsConvexePrinted (n : ℕ) : Prop :=
  ∀ K : Set (S n), IsCorpsConvexeS n K →
    (∀ (A B : corpsInterior K) (Sg : Set (corpsInterior K)), IsProjSegment n Sg A B →
      ∀ F F' : S n, F ≠ F' → Sphere.lineThrough (A : S n) B ∩ frontier K = {F, F'} →
        pseudoLength n Sg A B = Sphere.projMeasure F A B F') ∧
    Continuous (fun p : corpsInterior K × corpsInterior K => hilbertLength K p.1 p.2) ∧
    ∀ A B : corpsInterior K, hilbertLength K A B = 0 ↔ A = B

/-- **Prop. 2 holds as printed exactly in dimension `n ≥ 1`.** For `n = 0` a point `{x}` of `S(0)`
is a convex body, its interior is `{x}`, and `l_V(x, x) = +∞ ≠ 0`; the other assertions hold in
every dimension (`pseudoLength_eq_projMeasure`, `continuous_hilbertLength`, and « ne s'annule que
sur la diagonale » read literally, `hilbertLength_ne_zero`). -/
theorem pseudoLongueurCorpsConvexePrinted_iff {n : ℕ} :
    PseudoLongueurCorpsConvexePrinted n ↔ 0 < n := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      obtain ⟨x⟩ : Nonempty (S 0) := inferInstance
      have hK := isCorpsConvexeS_singleton_S0 x
      have hx : x ∈ interior ({x} : Set (S 0)) := by
        rw [(isOpen_singleton_S0 x).interior_eq]; exact mem_singleton x
      have h0 := ((h {x} hK).2.2 ⟨x, hx⟩ ⟨x, hx⟩).2 rfl
      rw [hilbertLength_self_dim_zero] at h0
      exact EReal.top_ne_zero h0
    · exact hn
  · intro hn K hK
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨-, -, h2, h3, h4⟩ := pseudo_longueur_corps_convexe hK
    exact ⟨h2, h3, h4⟩

/-! ### Property 5°: upper semicontinuity of the pseudo-length -/

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A closed segment whose representative chord lies in `F(T)` lies in `T`. -/
theorem closedSeg_subset_of_forall {a b : E} {A B : Sphere E} (ha : IsRep a A) (hb : IsRep b B)
    {T : Set (Sphere E)} (h : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • a + t • b ∈ F T) :
    closedSeg A B ⊆ T :=
  closedSeg_subset_of_convex ha hb (convex_segment a b) (left_mem_segment ℝ a b)
    (right_mem_segment ℝ a b) (by rw [segment_eq_image]; rintro _ ⟨t, ht, rfl⟩; exact h t ht)

end Sphere

section Five

variable {n : ℕ}

/-- **Nearby segments, in `S(n)`.** If `(M, N) ⊆ (A₀, B₀) ⊆ T`, `T` open, with projective measure
`< k`, then every pair `(P, Q)` close to `(M, N)` lies on a segment `(A, B) ⊆ T` relative to which
the measure of `PQ` is `< k`. For `M ≠ N` the segment `(A, B)` is moved with `(P, Q)` so that the
cross-ratio stays the same; for `M = N`, the affine-ball estimate. -/
theorem eventually_exists_projMeasure_lt {T : Set (S n)} (hT : IsOpen T) {A₀ B₀ M N : S n}
    (hsub : Sphere.closedSeg A₀ B₀ ⊆ T) {k : ℝ} (hk : Sphere.projMeasure A₀ M N B₀ < k) :
    ∀ᶠ p : S n × S n in 𝓝 (M, N), ∃ A B : S n, B ≠ -A ∧ Sphere.closedSeg A B ⊆ T ∧
      p.1 ∈ Sphere.closedSeg A B ∧ p.2 ∈ Sphere.closedSeg A B ∧
        Sphere.projMeasure A p.1 p.2 B < k := by
  obtain ⟨r, hr⟩ := Sphere.projMeasure_lt_top_iff.1 (hk.trans (EReal.coe_lt_top k))
  have hval := Sphere.projMeasure_eq hr
  have hMT : M ∈ T := hsub (Sphere.openSeg_subset_closedSeg _ _ hr.mem_openSeg.1)
  obtain ⟨hr0, a, b, hli, ha, hb, hm, hn⟩ := hr
  have hn1 : 1 ≤ n := by
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  by_cases hr1 : r = 1
  · -- `M = N`
    subst hr1
    have hNM : N = M := (by simpa using hn : Sphere.IsRep (a + b) N).eq hm
    subst hNM
    have hk0 : 0 < k := by
      rw [hval, Real.log_one, abs_zero] at hk
      exact EReal.coe_pos.1 hk
    obtain ⟨W, hWo, hMW, -, hW⟩ := exists_nhds_projMeasure_lt hn1 hT hMT hk0
    filter_upwards [prod_mem_nhds (hWo.mem_nhds hMW) (hWo.mem_nhds hMW)] with p hp
    obtain ⟨-, -, A, B, hBA, hABT, h1, h2, h3⟩ := hW _ hp.1 _ hp.2
    exact ⟨A, B, hBA, hABT, h1, h2, h3⟩
  -- `M ≠ N`
  have hMN : M ≠ N := by
    rintro rfl
    obtain ⟨c, hc, hce⟩ := hm.exists_pos hn
    obtain ⟨h1, h2⟩ := Sphere.coeffs_eq hli (s := 1) (t := r) (s' := c) (t' := c)
      (by rw [one_smul, hce, smul_add])
    exact hr1 (by rw [h2, ← h1])
  have hm0 := hm.ne_zero
  have hn0 := hn.ne_zero
  set u : S n → Fin (n + 1) → ℝ := fun X => (Sphere.homeomorphUnitSphere X : Fin (n + 1) → ℝ)
    with hudef
  have hu : Continuous u :=
    continuous_subtype_val.comp Sphere.homeomorphUnitSphere.continuous
  have hρ : ∀ {v : Fin (n + 1) → ℝ} {X : S n}, Sphere.IsRep v X → ‖v‖ • u X = v := by
    intro v X hv
    obtain ⟨hv0, rfl⟩ := hv
    simp only [hudef, Sphere.homeomorphUnitSphere_mk, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0), one_smul]
  have hr1' : r - 1 ≠ 0 := sub_ne_zero.2 hr1
  set bb : S n × S n → Fin (n + 1) → ℝ := fun p =>
    (r - 1)⁻¹ • (‖a + r • b‖ • u p.2 - ‖a + b‖ • u p.1) with hbbdef
  set aa : S n × S n → Fin (n + 1) → ℝ := fun p => ‖a + b‖ • u p.1 - bb p with haadef
  have hbbMN : bb (M, N) = b := by
    simp only [hbbdef, hρ hm, hρ hn]
    rw [show a + r • b - (a + b) = (r - 1) • b by module, smul_smul, inv_mul_cancel₀ hr1',
      one_smul]
  have haaMN : aa (M, N) = a := by
    simp only [haadef, hρ hm, hbbMN, add_sub_cancel_right]
  have hcont : Continuous (fun z : (S n × S n) × ℝ => (1 - z.2) • aa z.1 + z.2 • bb z.1) := by
    simp only [haadef, hbbdef]
    fun_prop
  have hFT : IsOpen (Sphere.F T) := Sphere.isOpen_iff_F.1 hT
  have htube : ∀ᶠ p : S n × S n in 𝓝 (M, N), ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • aa p + t • bb p ∈ Sphere.F T := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t ht => ?_
    refine (hFT.preimage hcont).mem_nhds ?_
    show (1 - t) • aa (M, N) + t • bb (M, N) ∈ Sphere.F T
    rw [haaMN, hbbMN]
    have h0 : (1 - t) • a + t • b ≠ 0 := fun h => by
      obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hli _ _ h
      linarith
    refine ⟨h0, hsub ((Sphere.mem_closedSeg_iff ha hb).2 ⟨1 - t, t, by linarith [ht.2], ht.1,
      Sphere.isRep_mk _ h0⟩)⟩
  have hne : ∀ᶠ p : S n × S n in 𝓝 (M, N), p.1 ≠ p.2 :=
    (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hMN
  filter_upwards [htube, hne] with p htp hpne
  have haa0 : aa p ≠ 0 := by
    have := (htp 0 ⟨le_rfl, zero_le_one⟩).1
    simpa using this
  have hbb0 : bb p ≠ 0 := by
    have := (htp 1 ⟨zero_le_one, le_rfl⟩).1
    simpa using this
  have hsum : aa p + bb p = ‖a + b‖ • u p.1 := sub_add_cancel _ _
  have hsumr : aa p + r • bb p = ‖a + r • b‖ • u p.2 := by
    rw [haadef, hbbdef]
    simp only
    rw [smul_smul, show r * (r - 1)⁻¹ = 1 + (r - 1)⁻¹ by field_simp; ring, add_smul, one_smul]
    abel
  have hP : Sphere.IsRep (aa p + bb p) p.1 := by
    rw [hsum]; exact (isRep_homeomorphUnitSphere p.1).smul (norm_pos_iff.2 hm0)
  have hQ : Sphere.IsRep (aa p + r • bb p) p.2 := by
    rw [hsumr]; exact (isRep_homeomorphUnitSphere p.2).smul (norm_pos_iff.2 hn0)
  have hA := Sphere.isRep_mk _ haa0
  have hB := Sphere.isRep_mk _ hbb0
  have hBA' : Sphere.mk _ hbb0 ≠ -Sphere.mk _ haa0 := by
    intro h
    obtain ⟨c, hc, hce⟩ := hA.neg.exists_pos (h ▸ hB)
    have := (htp (1 / (1 + c)) ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩).1
    apply this
    rw [hce]
    field_simp
    module
  have hBA : Sphere.mk _ hbb0 ≠ Sphere.mk _ haa0 := by
    intro h
    obtain ⟨c, hc, hce⟩ := hA.exists_pos (h ▸ hB)
    apply hpne
    have h1 : Sphere.IsRep ((1 + c) • aa p) p.1 := by
      convert hP using 1; rw [hce]; module
    have h2 : Sphere.IsRep ((1 + r * c) • aa p) p.2 := by
      convert hQ using 1; rw [hce]; module
    exact (h1.eq (hA.smul (by positivity))).trans (h2.eq (hA.smul (by positivity))).symm
  have hcr : Sphere.IsCrossRatio p.1 p.2 (Sphere.mk _ hbb0) (Sphere.mk _ haa0) r :=
    ⟨hr0, aa p, bb p, Sphere.linearIndependent_of_ne hA hB hBA hBA', hA, hB, hP, hQ⟩
  refine ⟨_, _, hBA', Sphere.closedSeg_subset_of_forall hA hB fun t ht => htp t ht,
    Sphere.openSeg_subset_closedSeg _ _ hcr.mem_openSeg.1,
    Sphere.openSeg_subset_closedSeg _ _ hcr.mem_openSeg.2, ?_⟩
  rw [Sphere.projMeasure_eq hcr, ← hval]
  exact hk

variable {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]

/-- **Property 5°, in the form of its printed proof** (l.322–323: « si $MN$ est un segment borné par
$k$ dans $V$, il en est de même de tout segment assez voisin de $MN$ »): if `l_V(M, N) < k`, there
is an open `U ⊇ (M, N)` such that every segment of `V` inside `U` with endpoints close enough to
`(M, N)` has pseudo-length `< k`. Any dimension. -/
theorem propriete_cinq {Sg : Set V} {M N : V} (hSg : IsProjSegment n Sg M N) {k : EReal}
    (hk : pseudoLength n Sg M N < k) :
    ∃ U : Set V, IsOpen U ∧ Sg ⊆ U ∧ ∀ᶠ p : V × V in 𝓝 (M, N), ∀ Sg' : Set V,
      IsProjSegment n Sg' p.1 p.2 → Sg' ⊆ U → pseudoLength n Sg' p.1 p.2 < k := by
  obtain ⟨k₁, hk₁, hk₁k⟩ := EReal.lt_iff_exists_real_btwn.1 hk
  obtain ⟨k₂, hk₂, hk₂k⟩ := EReal.lt_iff_exists_real_btwn.1 hk₁
  -- a segment majorising `(M, N)` by `k₂`
  have hmaj : IsMajoreSeg n k₂ Sg M N := by
    by_contra hno
    have : (k₂ : EReal) ≤ pseudoLength n Sg M N := by
      refine le_iInf₂ fun c hc => ?_
      by_contra hlt
      push Not at hlt
      exact hno (hc.mono (EReal.coe_le_coe_iff.1 hlt.le))
    exact absurd hk₂ (not_lt.2 this)
  obtain ⟨-, Sg₁, A, B, hseg₁, hsub, hall⟩ := hmaj
  obtain ⟨φ, hφ, hS₁, hA, hB, hadm, himg⟩ := id hseg₁
  have hlt := hall φ hφ hS₁
  have hT : Sphere.closedSeg (φ A) (φ B) ⊆ φ.target := by
    rw [← himg]
    rintro _ ⟨x, hx, rfl⟩
    exact φ.map_source (hS₁ hx)
  have hM : M ∈ φ.source := hS₁ (hsub hSg.left_mem)
  have hN : N ∈ φ.source := hS₁ (hsub hSg.right_mem)
  have hev := eventually_exists_projMeasure_lt φ.open_target hT (k := k₁) (hlt.trans hk₂k)
  have hcont : ContinuousAt (fun p : V × V => (φ p.1, φ p.2)) (M, N) :=
    ((φ.continuousAt hM).comp continuousAt_fst).prodMk ((φ.continuousAt hN).comp continuousAt_snd)
  refine ⟨φ.source, φ.open_source, hsub.trans hS₁, ?_⟩
  filter_upwards [hcont.eventually hev] with p hp Sg' hSg' hSg'U
  obtain ⟨A', B', hBA', hABT, hP, hQ, hmeas⟩ := hp
  obtain ⟨himg', hne'⟩ := hSg'.image_eq_closedSeg hφ hSg'U
  have h1 := isMajoreSeg_of_chart hφ hBA' hABT hP hQ hne' hmeas
  have e : φ.symm '' (φ '' Sg') = Sg' := φ.symm_image_image_of_subset_source hSg'U
  rw [φ.left_inv (hSg'U hSg'.left_mem), φ.left_inv (hSg'U hSg'.right_mem), ← himg', e] at h1
  exact (pseudoLength_le h1).trans_lt hk₁k

/-- **Property 5°** (l.245–247, a lemma here, unmarked): « si un segment $(M_i, N_i)$ tend vers
$(M, N)$, on a $\overline{\lim}\, l_V(M_i, N_i)\leqq l_V(M, N)$ », with « tend vers » read as: the
endpoints converge, and the segments eventually lie in every open neighbourhood of `(M, N)`. -/
theorem propriete_cinq_limsup {Sg : Set V} {M N : V} (hSg : IsProjSegment n Sg M N) {ι : Type*}
    {l : Filter ι} {Sgs : ι → Set V} {Ms Ns : ι → V}
    (hseg : ∀ i, IsProjSegment n (Sgs i) (Ms i) (Ns i)) (hM : Tendsto Ms l (𝓝 M))
    (hN : Tendsto Ns l (𝓝 N)) (hS : ∀ U : Set V, IsOpen U → Sg ⊆ U → ∀ᶠ i in l, Sgs i ⊆ U) :
    limsup (fun i => pseudoLength n (Sgs i) (Ms i) (Ns i)) l ≤ pseudoLength n Sg M N := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨U, hUo, hSgU, hev⟩ := propriete_cinq hSg hc
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [(hM.prodMk_nhds hN).eventually hev, hS U hUo hSgU] with i hi hiU
  exact (hi (Sgs i) (hseg i) hiU).le

end Five


end Benzecri
