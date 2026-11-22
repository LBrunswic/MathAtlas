import Benzecri.Chapter2.Hilbert

/-!
# Chapter 2 § 2, Prop. 2 under the literal reading of « ne s'annule que sur la diagonale »: one theorem, in every dimension

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal p. 250; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-prop2-literal (OQ-56).

* `bzprop:c2s2p2_pseudo_longueur_corps_convexe` — `benzecri1960_ch2.tex:306` (Prop. 2,
  l.306–313, proof l.315–317) — marked in `Benzecri.Chapter2.Hilbert` on the strict
  `pseudo_longueur_corps_convexe` (DEC-177 rules OQ-56 with OQ-45: `n ≥ 1` is implied, and there
  both readings hold). Under the literal reading (`l_V(A, B) = 0 → A = B`) Prop. 2 holds in
  every dimension, with no `[NeZero n]`: `Benzecri.pseudo_longueur_corps_convexe_literal`, the five
  clauses of the strict `pseudo_longueur_corps_convexe` with the literal last clause, and its
  printed-format `Prop` `PseudoLongueurCorpsConvexeLiteral n`, true for every `n`
  (`pseudoLongueurCorpsConvexeLiteral_holds`). Under the « iff » reading the row stays with
  `Benzecri.pseudo_longueur_corps_convexe` (`n ≥ 1`) and OQ-45 (a). The two readings part ways
  exactly in dimension `0` (`pseudoLongueurCorpsConvexePrinted_iff_literal`); the zero set of
  `l_V` is the diagonal for `n ≥ 1` and empty for `n = 0` (`hilbertLength_eq_zero_iff_and_pos`).

> **Proposition 2.** Soient $\overline{V}$ un corps convexe de $S(n)$ d'intérieur $V$; $A$, $B$
> deux points de $V$; $F$, $F'$ les points d'intersection de la droite $AB$ avec la frontière de
> $\overline{V}$ :
>
> $l_V(A, B)$ n'est autre que la mesure projective de $AB$ relativement à $FF'$;
>
> $l_V(A, B)$ est une fonction continue sur $V\times V$ qui ne s'annule que sur la diagonale.
>
> La proposition résulte de ce que $F$, $F'$ dépendent continûment de $A$, $B$.
>
> 6° Si $V$ est l'intérieur d'un corps convexe, $l_V(M, N)$ est une fonction continue en $M$ et
> $N$ sur le produit $V\times V$; $l_V(M, N)$ est nulle si et seulement si $M=N$;

(The transcription of Prop. 2 was checked against the scan, journal p. 250, PDF p. 23: l.312
reads « qui ne s'annule que sur la diagonale ». Property 6° is `benzecri1960_ch2.tex:249–251`;
the paper derives it from Prop. 2, l.303: « La propriété 6° résulte de la » [proposition 2].)

## The two readings (OQ-56)

« ne s'annule que sur la diagonale », read literally, says that the zeros of `l_V` lie on the
diagonal: `l_V(A, B) = 0 → A = B`. Read as 6° says it (« nulle si et seulement si »), it also says
that `l_V(A, A) = 0`, which is property 1° (l.232), false in dimension `0` (OQ-45: Déf. 1 gives
coincident points no measure, `l_V(A, A) = +∞`). This file assembles the literal reading in every
dimension from the strict lemmas of `Benzecri.Chapter2.Hilbert` that carry no `[NeZero n]`:
`isProjSegment_corpsInterior_iff` (clause 0), `exists_frontier_pair` (clause 1),
`pseudoLength_eq_projMeasure` (clause 2), `continuous_hilbertLength` (clause 3),
`hilbertLength_ne_zero` (clause 4). The segment clause (0) needs no `n ≥ 1`: none of the five does.
Under either reading 6° (l.249–251) follows from Prop. 2 as l.303 says, under the literal one
together with 1°'s `l_V(M, M) = 0` (l.232), which carries OQ-45 in dimension `0`.

How much the literal statement says depends on the dimension, and both ends are proved: a convex
body of `S(n)` exists in every dimension (`isCorpsConvexeS_stdCorpsConvexe`, the rays of the cone
`|vᵢ| ≤ v₀`), and some convex body has two distinct interior points iff `n ≥ 1`
(`exists_ne_corpsInterior_iff`). So for `n ≥ 1` clauses 1, 2 and 4 apply to actual pairs `A ≠ B`;
for `n = 0` they are vacuous.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V̄` a convex body of `S(n)` (Déf. 11) | ✓ carried: `IsCorpsConvexeS n K` |
| `V` its interior, a locally projective manifold | ✓ carried: `corpsInterior K` (`Opens.interior K`, Mathlib's charted structure on an open set), as in the strict assembly |
| `l_V(A, B)` | ✓ carried: the pseudo-length of every segment of `V` from `A` to `B`; there is exactly one (clause 0), so `l_V` is `hilbertLength K` on `V × V` |
| « $F$, $F'$ les points d'intersection de la droite $AB$ avec la frontière » | ✓ carried: for `A ≠ B`, `F ≠ F'` with `lineThrough A B ∩ frontier K = {F, F'}` exist (clause 1, with `A`, `B` in the open segment `)F, F'(`), and clause 2 holds for every such pair, in both orders |
| « une fonction continue sur $V\times V$ » | ✓ carried: continuous `V × V → EReal`, as in the strict assembly; real-valued iff `n ≥ 1` (`hilbertLength_ne_top_iff_pos`), so at `n = 0` only with values in `[0, +∞]` (question) |
| « qui ne s'annule que sur la diagonale » | ✓ carried, literal reading (question, OQ-56): `hilbertLength K A B = 0 → A = B` |
| the dimension `n` | ✓ carried: every `n`, no `[NeZero n]`; the clauses on `A ≠ B` have instances iff `n ≥ 1` (`exists_ne_corpsInterior_iff`) |

## SCOPE (disclosed)

* **Not marked here.** DEC-177 (OQ-45, OQ-56) put the mark on the strict
  `pseudo_longueur_corps_convexe` (« iff », `n ≥ 1`); this theorem is the literal reading's
  every-dimension form.
* **Dimension 0 is vacuous under the literal reading.** A convex body of `S(0)` has a one-point
  interior (`subsingleton_corpsInterior_dim_zero`; the example is `isCorpsConvexeS_singleton_S0`),
  so clauses 1 and 4 hold there because no `A ≠ B` exists, clause 2 because its frontier hypothesis
  can never hold for `A = B` (in any dimension), and clause 3 because `V` is a point.
  The literal Prop. 2 is true at `n = 0` for this reason only. The « iff » form fails there because
  `l_V(A, A) = +∞` (`hilbertLength_self_dim_zero`), Déf. 1 giving coincident points no measure;
  for the same reason `l_V` is not real-valued at `n = 0` (`hilbertLength_ne_top_iff_pos`), and
  « une fonction continue » holds there only for `EReal`-valued functions.
* **For `n ≥ 1`** the literal form is weaker than the strict assembly, which also gives
  `l_V(A, A) = 0`; `pseudoLongueurCorpsConvexePrinted_iff_literal` compares their truth values
  (Printed `n` ↔ Literal `n` ∧ `0 < n`), restating the strict `pseudoLongueurCorpsConvexePrinted_iff`.
* The printed proof (l.316) is not followed; the strict lemmas use two semicontinuities, as
  `Benzecri.Chapter2.Hilbert` discloses.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology

namespace Benzecri

section Literal

variable {n : ℕ} {K : Set (S n)}

/-- **In dimension `0` the interior of a convex body is (at most) one point**: two points of
`S(0)` are equal or opposite, and a convex body never contains a point and its opposite. -/
theorem subsingleton_corpsInterior_dim_zero {K : Set (S 0)} (hK : IsCorpsConvexeS 0 K) :
    Subsingleton (corpsInterior K) := by
  refine ⟨fun P Q => Subtype.ext ?_⟩
  rcases S0_eq_or_eq_neg (P : S 0) Q with h | h
  · exact h.symm
  · exact absurd (h ▸ interior_subset Q.2) (hK.neg_notMem (interior_subset P.2))

/-- **The zero set of `l_V` in every dimension**: `l_V(A, B) = 0` iff `A = B` and `n ≥ 1`. For
`n ≥ 1` it is the diagonal; for `n = 0` it is empty (`l_V(A, A) = +∞`). -/
theorem hilbertLength_eq_zero_iff_and_pos (hK : IsCorpsConvexeS n K) (A B : corpsInterior K) :
    hilbertLength K A B = 0 ↔ A = B ∧ 0 < n := by
  constructor
  · intro h
    have hAB : A = B := by_contra fun hAB => hilbertLength_ne_zero hK hAB h
    refine ⟨hAB, Nat.pos_of_ne_zero fun hn => ?_⟩
    subst hn hAB
    rw [hilbertLength_self_dim_zero] at h
    exact EReal.top_ne_zero h
  · rintro ⟨rfl, hn⟩
    haveI : NeZero n := ⟨hn.ne'⟩
    exact (hilbertLength_eq_zero_iff hK A A).2 rfl

/-- **`l_V` is real-valued exactly for `n ≥ 1`**: for `n = 0`, `l_V(A, A) = +∞` at the point of
`V`, so the continuity of Prop. 2 in dimension `0` is that of an `EReal`-valued function. -/
theorem hilbertLength_ne_top_iff_pos (hK : IsCorpsConvexeS n K) :
    (∀ A B : corpsInterior K, hilbertLength K A B ≠ ⊤) ↔ 0 < n := by
  constructor
  · intro h
    refine Nat.pos_of_ne_zero fun hn => ?_
    subst hn
    obtain ⟨x, hx⟩ := hK.2.2
    exact h ⟨x, hx⟩ ⟨x, hx⟩ (hilbertLength_self_dim_zero _)
  · intro hn A B
    haveI : NeZero n := ⟨hn.ne'⟩
    exact (hilbertLength_lt_top hK A B).ne

/-- **Prop. 2 under the literal reading of « ne s'annule que sur la diagonale »**
(`bzprop:c2s2p2_pseudo_longueur_corps_convexe`, OQ-56), in every dimension. Let `K` be a convex
body of `S(n)` with interior `V`. (0) The segments of `V` from `A` to `B` reduce to `(A, B)`, so
`l_V(A, B)` is `hilbertLength K A B`. (1) For `A ≠ B` the line `AB` meets the frontier of `K` in
two points `F ≠ F'`, and `A`, `B` lie in the open segment `)F, F'(`. (2) `l_V(A, B)` is the
projective measure of `AB` relative to `FF'`. (3) `l_V` is continuous on `V × V`, and (4) its
zeros lie on the diagonal. -/
theorem pseudo_longueur_corps_convexe_literal (hK : IsCorpsConvexeS n K) :
    (∀ (A B : corpsInterior K) (Sg : Set (corpsInterior K)),
      IsProjSegment n Sg A B ↔ Sg = Subtype.val ⁻¹' Sphere.closedSeg (A : S n) B) ∧
    (∀ A B : corpsInterior K, A ≠ B →
      ∃ F F' : S n, F ≠ F' ∧ Sphere.lineThrough (A : S n) B ∩ frontier K = {F, F'} ∧
        (A : S n) ∈ Sphere.openSeg F F' ∧ (B : S n) ∈ Sphere.openSeg F F') ∧
    (∀ (A B : corpsInterior K) (Sg : Set (corpsInterior K)), IsProjSegment n Sg A B →
      ∀ F F' : S n, F ≠ F' → Sphere.lineThrough (A : S n) B ∩ frontier K = {F, F'} →
        pseudoLength n Sg A B = Sphere.projMeasure F A B F') ∧
    Continuous (fun p : corpsInterior K × corpsInterior K => hilbertLength K p.1 p.2) ∧
    ∀ A B : corpsInterior K, hilbertLength K A B = 0 → A = B :=
  ⟨fun _ _ _ => isProjSegment_corpsInterior_iff hK,
    fun _ _ hAB => exists_frontier_pair hK hAB,
    fun _ _ _ hSg _ _ hFF' hline => pseudoLength_eq_projMeasure hK hSg hFF' hline,
    continuous_hilbertLength hK,
    fun _ _ h => by_contra fun hAB => hilbertLength_ne_zero hK hAB h⟩

end Literal

/-- **Prop. 2 as printed, literal reading** (assertions (2)–(4) of
`pseudo_longueur_corps_convexe_literal`, the format of `PseudoLongueurCorpsConvexePrinted`, with
« ne s'annule que sur la diagonale » read `l_V(A, B) = 0 → A = B`), for the convex bodies of
`S(n)`. -/
def PseudoLongueurCorpsConvexeLiteral (n : ℕ) : Prop :=
  ∀ K : Set (S n), IsCorpsConvexeS n K →
    (∀ (A B : corpsInterior K) (Sg : Set (corpsInterior K)), IsProjSegment n Sg A B →
      ∀ F F' : S n, F ≠ F' → Sphere.lineThrough (A : S n) B ∩ frontier K = {F, F'} →
        pseudoLength n Sg A B = Sphere.projMeasure F A B F') ∧
    Continuous (fun p : corpsInterior K × corpsInterior K => hilbertLength K p.1 p.2) ∧
    ∀ A B : corpsInterior K, hilbertLength K A B = 0 → A = B

/-- **The literal Prop. 2 holds in every dimension.** -/
theorem pseudoLongueurCorpsConvexeLiteral_holds (n : ℕ) : PseudoLongueurCorpsConvexeLiteral n := by
  intro K hK
  obtain ⟨-, -, h2, h3, h4⟩ := pseudo_longueur_corps_convexe_literal hK
  exact ⟨h2, h3, h4⟩

/-- **The two readings of Prop. 2 part ways exactly in dimension `0`**: the « iff » form
(`PseudoLongueurCorpsConvexePrinted n`) holds iff the literal form holds and `n ≥ 1`; the literal
form holds in every dimension. -/
theorem pseudoLongueurCorpsConvexePrinted_iff_literal {n : ℕ} :
    PseudoLongueurCorpsConvexePrinted n ↔ PseudoLongueurCorpsConvexeLiteral n ∧ 0 < n := by
  refine ⟨fun h => ⟨pseudoLongueurCorpsConvexeLiteral_holds n,
    pseudoLongueurCorpsConvexePrinted_iff.1 h⟩, fun h => pseudoLongueurCorpsConvexePrinted_iff.2 h.2⟩

/-! ### When the literal clauses have content: a convex body in every dimension -/

section Witness

variable (n : ℕ)

/-- The closed cone `|vᵢ| ≤ v₀` of `ℝⁿ⁺¹`. -/
def stdCorpsCone : Set (Fin (n + 1) → ℝ) := {v | ∀ i, |v i| ≤ v 0}

/-- **A convex body of `S(n)` in every dimension** (`isCorpsConvexeS_stdCorpsConvexe`): the rays of
the cone `|vᵢ| ≤ v₀`. For `n = 0` it is the point of `e₀`. -/
def stdCorpsConvexe : Set (S n) := Sphere.ofCone (stdCorpsCone n)

/-- The open cone `0 < v₀`, `|vᵢ₊₁| < v₀`, inside `stdCorpsCone n`. -/
def stdCorpsConeOpen : Set (Fin (n + 1) → ℝ) := {v | 0 < v 0 ∧ ∀ i : Fin n, |v i.succ| < v 0}

variable {n}

theorem stdCorpsCone_smul {c : ℝ} (hc : 0 < c) {v : Fin (n + 1) → ℝ} (hv : v ∈ stdCorpsCone n) :
    c • v ∈ stdCorpsCone n := fun i => by
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hv i) hc.le

theorem stdCorpsConeOpen_smul {c : ℝ} (hc : 0 < c) {v : Fin (n + 1) → ℝ}
    (hv : v ∈ stdCorpsConeOpen n) : c • v ∈ stdCorpsConeOpen n := by
  refine ⟨by simpa using mul_pos hc hv.1, fun i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
  exact mul_lt_mul_of_pos_left (hv.2 i) hc

theorem F_stdCorpsConvexe : Sphere.F (stdCorpsConvexe n) = stdCorpsCone n \ {0} :=
  Sphere.F_ofCone fun _ hc _ hv => stdCorpsCone_smul hc hv

theorem pos_of_mem_stdCorpsCone {v : Fin (n + 1) → ℝ} (hv : v ∈ stdCorpsCone n) (h0 : v ≠ 0) :
    0 < v 0 := by
  refine lt_of_le_of_ne ((abs_nonneg _).trans (hv 0)) fun h => h0 (funext fun i => ?_)
  have := hv i
  rw [← h] at this
  exact abs_nonpos_iff.1 this

theorem isClosed_stdCorpsCone : IsClosed (stdCorpsCone n) := by
  simp only [stdCorpsCone, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs (continuous_apply 0)

theorem isOpen_stdCorpsConeOpen : IsOpen (stdCorpsConeOpen n) := by
  simp only [stdCorpsConeOpen, Set.setOf_and, Set.setOf_forall]
  exact (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply _).abs (continuous_apply 0))

theorem stdCorpsConeOpen_subset : stdCorpsConeOpen n ⊆ stdCorpsCone n := fun v hv i =>
  Fin.cases (by rw [abs_of_pos hv.1]) (fun j => (hv.2 j).le) i

/-- **`stdCorpsConvexe n` is a convex body of `S(n)`** (Déf. 11), in every dimension. -/
theorem isCorpsConvexeS_stdCorpsConvexe : IsCorpsConvexeS n (stdCorpsConvexe n) := by
  rw [isCorpsConvexeS_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [F_stdCorpsConvexe]
    intro x hx y hy a b ha hb hab
    have hx0 := pos_of_mem_stdCorpsCone hx.1 hx.2
    have hy0 := pos_of_mem_stdCorpsCone hy.1 hy.2
    have hpos : 0 < a * x 0 + b * y 0 := by
      rcases ha.eq_or_lt with rfl | ha'
      · rw [zero_add] at hab
        subst hab
        simpa using hy0
      · have := mul_pos ha' hx0
        have := mul_nonneg hb hy0.le
        linarith
    refine ⟨fun i => ?_, fun h => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
        _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * x 0 + b * y 0 := add_le_add (mul_le_mul_of_nonneg_left (hx.1 i) ha)
            (mul_le_mul_of_nonneg_left (hy.1 i) hb)
    · have := congrFun (mem_singleton_iff.1 h) 0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      linarith
  · refine IsClosed.isCompact ?_
    rw [← isOpen_compl_iff, Sphere.isOpen_iff_F, Sphere.F_compl, F_stdCorpsConvexe]
    convert isClosed_stdCorpsCone.isOpen_compl using 1
    ext v
    have h0 : (0 : Fin (n + 1) → ℝ) ∈ stdCorpsCone n := fun i => by simp
    simp only [mem_sdiff, mem_compl_iff, mem_singleton_iff, not_and, not_not]
    constructor
    · rintro ⟨hv, h⟩ hC
      exact hv (h hC)
    · intro hC
      exact ⟨fun hv => hC (hv ▸ h0), fun h => absurd h hC⟩
  · refine ⟨Sphere.mk (Pi.single 0 1) (by simp), interior_maximal
      (image_mono (preimage_mono stdCorpsConeOpen_subset))
      (Sphere.isOpen_ofCone (fun _ hc _ hv => stdCorpsConeOpen_smul hc hv)
        isOpen_stdCorpsConeOpen) (Sphere.mk_mem_ofCone _ ?_)⟩
    refine ⟨by simp, fun i => ?_⟩
    simp [Fin.succ_ne_zero]

/-- **A convex body of `S(n)` exists in every dimension.** -/
theorem exists_isCorpsConvexeS (n : ℕ) : ∃ K : Set (S n), IsCorpsConvexeS n K :=
  ⟨_, isCorpsConvexeS_stdCorpsConvexe⟩

/-- **The clauses of Prop. 2 about `A ≠ B` have content exactly for `n ≥ 1`**: some convex body of
`S(n)` has two distinct interior points iff `0 < n`. For `n = 0` they are vacuous
(`subsingleton_corpsInterior_dim_zero`). -/
theorem exists_ne_corpsInterior_iff :
    (∃ K : Set (S n), IsCorpsConvexeS n K ∧ ∃ A B : corpsInterior K, A ≠ B) ↔ 0 < n := by
  constructor
  · rintro ⟨K, hK, A, B, hAB⟩
    refine Nat.pos_of_ne_zero fun hn => ?_
    subst hn
    exact hAB ((subsingleton_corpsInterior_dim_zero hK).elim A B)
  · intro hn
    set j : Fin (n + 1) := (⟨0, hn⟩ : Fin n).succ with hj
    have hU : Sphere.ofCone (stdCorpsConeOpen n) ⊆ interior (stdCorpsConvexe n) :=
      interior_maximal (image_mono (preimage_mono stdCorpsConeOpen_subset))
        (Sphere.isOpen_ofCone (fun _ hc _ hv => stdCorpsConeOpen_smul hc hv)
          isOpen_stdCorpsConeOpen)
    have hv0 : (Pi.single 0 1 : Fin (n + 1) → ℝ) ≠ 0 := by simp
    set w : Fin (n + 1) → ℝ := Pi.single 0 1 + Pi.single j (1 / 2) with hw
    have hj0 : j ≠ 0 := Fin.succ_ne_zero _
    have hw0 : w 0 = 1 := by simp [hw, hj0.symm]
    have hwj : w j = 1 / 2 := by simp [hw, hj0]
    have hw0' : w ≠ 0 := fun h => by simp [h] at hw0
    refine ⟨stdCorpsConvexe n, isCorpsConvexeS_stdCorpsConvexe,
      ⟨Sphere.mk _ hv0, hU (Sphere.mk_mem_ofCone _ ?_)⟩,
      ⟨Sphere.mk w hw0', hU (Sphere.mk_mem_ofCone _ ?_)⟩, fun h => ?_⟩
    · exact ⟨by simp, fun i => by simp [Fin.succ_ne_zero]⟩
    · refine ⟨by rw [hw0]; exact one_pos, fun i => ?_⟩
      rw [hw0]
      by_cases hi : i.succ = j
      · rw [hi, hwj]; norm_num
      · simp [hw, hi, Fin.succ_ne_zero]
    · obtain ⟨c, -, hc⟩ := (Sphere.mk_eq_mk_iff_exists_pos _ _).1 (congrArg Subtype.val h)
      have := congrFun hc j
      rw [hwj] at this
      simp [hj0] at this

end Witness

end Benzecri
