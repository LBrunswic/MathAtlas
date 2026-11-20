import Benzecri.Projective.Convex
import Benzecri.Projective.Groups
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic

/-!
# `Benzecri.Chapter2.CrossRatio` — the cross-ratio on a segment of `S(E)`, the projective measure (Ch. 2 § 2, Déf. 1) and its monotonicity (Prop. 1)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal pp. 249–250; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-mesure (DEC-137).

* **`bzdef:c2s2d1_mesure_projective`** — `benzecri1960_ch2.tex:262` (Déf. 1, l.262–268, p. 249):
  the cross-ratio `(A', B', B, A) = r` of four points of a segment of `S(E)`
  (`Benzecri.Sphere.IsCrossRatio`, well defined: `IsCrossRatio.unique`; the classical ratio of
  algebraic measures in an affine chart: `isCrossRatio_affine`, with `Benzecri.crossRatio`); the
  projective measure `Benzecri.Sphere.projMeasure A A' B' B`, valued in `EReal`. The two claims of
  the definition: « Ce rapport anharmonique est une quantité supérieure ou égale à l'unité »
  (`IsCrossRatio.one_le`; existence `exists_isCrossRatio`; the measure is its logarithm,
  `projMeasure_eq_log`) and « la notion de mesure projective est invariante par les
  automorphismes de GS(n, R) » (`projMeasure_smul`).
* **`bzprop:c2s2p1_mesure_projective_monotone`** — `benzecri1960_ch2.tex:270` (Prop. 1,
  l.270–273, p. 249; no proof printed): `Benzecri.Sphere.projMeasure_antitone` (the paper's
  form), from the stronger `projMeasure_le_inner` and `projMeasure_le_outer`, which only ask the
  new endpoints to lie on the segment.

> **Déf. 1.** Soient $A$, $A'$, $B'$, $B$ quatre points d'un segment $(AB)$ de $S(n)$ écrits comme
> ils se rencontrent si l'on ordonne de $A$ vers $B$ : on appelle *mesure projective* de $A'B'$
> *relativement* à $AB$ le logarithme du rapport anharmonique $(A', B', B, A)$. Ce rapport
> anharmonique est une quantité supérieure ou égale à l'unité; la notion de mesure projective est
> invariante par les automorphismes de $GS(n, \R)$.
>
> **Prop. 1.** La mesure projective décroît si l'on remplace le segment $(A', B')$ par un segment
> contenu dans $(A', B')$; elle décroît encore si l'on remplace le segment $AB$ par un segment le
> contenant.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 1: `S(n)` | ⚠ weakened: `S(E)` for any real vector space `E` (`S n` is `E = ℝⁿ⁺¹`); `GS(n, ℝ)` is `GSE E` |
| Déf. 1: `A, A', B', B` on a segment `(AB)`, in this order | ✓ carried where used: `projMeasure_eq_log` takes `A ≠ B` not opposite, `A'`, `B'` in the open segment and `B' ∈ (A', B)`; the definition itself is total (SCOPE) |
| Déf. 1: « rapport anharmonique » | ✓ the classical one: `isCrossRatio_affine` gives it as the ratio of algebraic measures `(pr/qr)·(qs/ps)` on any affine line `p₀ + t d`, the formula of p. 250 (the `[sic]` read as flagged) |
| Prop. 1: `(A'', B'') ⊂ (A', B')`, `AB ⊂ (A₁, B₁)` | ⚠ weakened in `projMeasure_le_inner` / `_outer`: only `A'', B'' ∈ (A', B')`, resp. `A, B ∈ (A₁, B₁)`, and no order or position hypothesis on `A'`, `B'`; `projMeasure_antitone` states the printed inclusions |

## SCOPE (disclosed)

* **No cross-ratio in Mathlib at this pin** (grep `cross`, `anharmon`): it is defined here, as a
  relation. `IsCrossRatio A' B' B A r` says: some representatives `a` of `A`, `b` of `B`,
  independent, with `a + b` representing `A'` and `a + r b` representing `B'`, `r > 0`; so it
  is the cross-ratio of four points of the segment `(A, B)` with `A'`, `B'` interior, and it is
  `odds(B') / odds(A')` in any coordinates (`isCrossRatio_of_coords`).
* **The degenerate configurations**, two cases, `projMeasure` being `⊤` in both
  (`projMeasure_left_eq_top`, `projMeasure_right_eq_top`, `projMeasure_same_eq_top`):
  (i) `A' = A` with `B' ≠ A`, or `B' = B` with `A' ≠ B`: the printed formula `(pr/qr)·(qs/ps)`
  has a zero denominator and a nonzero numerator, the cross-ratio is infinite, and `⊤` is the
  printed value `log ∞` extended; (ii) **coincident points**, `A' = B' = A` or `A' = B' = B`
  (the formula is `0/0`) or `A = B` (four equal points): the paper defines no cross-ratio and
  `⊤` is a convention (reported under `questions`). Case (ii) matters only in dimension `0`,
  where every segment is a point (see `Mesure.lean`, `pseudoLength_self_eq_top_dim_zero`).
* **The order of `A'`, `B'`.** `projMeasure` is `|log (A', B', B, A)|`: in the printed order it is
  `log (A', B', B, A)` (`projMeasure_eq_log`, `≥ 0`), and it does not depend on which of the two
  inner points is named first (`projMeasure_swap`) nor on the direction of `(A, B)`
  (`projMeasure_reverse`). Outside the paper's configuration (points off the segment) the value is
  `⊤` or this absolute value; Déf. 2 only uses it for `(A', B') ⊂ (A, B)`.
* **Prop. 1 has no printed proof**; it is proved here: every point of `(A', B')` is `x a + y b`
  with `y / x` between `1` and `r` (`exists_coords_of_mem_closedSeg`), and
  `|log (v / u)| ≤ |log r|` for `u, v` between `1` and `r` (`abs_log_div_le`).
* **The `[sic]` of p. 250** (« af × ff′ » read « af × bf′ ») is not a finding: `crossRatio` is
  the corrected `(af′ / bf′) · (bf / af)`, as the transcription's comment gives.
* General facts proved here (`IsRep` and its API, `mem_closedSeg_iff`, `mem_openSeg_iff`,
  `closedSeg_self`, `linearIndependent_of_ne`, `coeffs_eq`) could move upstream to
  `Benzecri.Projective.Convex` at graduation.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set

namespace Benzecri

/-! ### The cross-ratio of four points of an affine line -/

/-- **The cross-ratio of four real numbers** (four points of an affine line), Benzécri's
convention (p. 250, proof of 7°, with the `[sic]` read): `(p, q, r, s) = (pr / qr) · (qs / ps)`,
where `xy = y − x` is the algebraic measure of the segment `xy`. -/
def crossRatio (p q r s : ℝ) : ℝ := (r - p) / (r - q) * ((s - q) / (s - p))

/-! ### Three facts about real numbers -/

/-- A weighted mean of `1` and `r` lies between them. -/
theorem wavg_mem_uIcc (r : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 0 < s + t) :
    (s + t * r) / (s + t) ∈ uIcc 1 r := by
  rw [← segment_eq_uIcc]
  refine ⟨s / (s + t), t / (s + t), by positivity, by positivity, by field_simp, ?_⟩
  simp only [smul_eq_mul]
  field_simp

theorem pos_of_mem_uIcc {r x : ℝ} (hr : 0 < r) (hx : x ∈ uIcc 1 r) : 0 < x := by
  rcases le_total 1 r with h | h
  · rw [uIcc_of_le h] at hx; linarith [hx.1]
  · rw [uIcc_of_ge h] at hx; linarith [hx.1]

theorem log_mem_uIcc {r x : ℝ} (hr : 0 < r) (hx : x ∈ uIcc 1 r) :
    Real.log x ∈ uIcc 0 (Real.log r) := by
  rcases le_total 1 r with h | h
  · rw [uIcc_of_le h] at hx
    rw [uIcc_of_le (Real.log_nonneg h)]
    exact ⟨Real.log_nonneg hx.1, Real.log_le_log (by linarith [hx.1]) hx.2⟩
  · rw [uIcc_of_ge h] at hx
    rw [uIcc_of_ge (Real.log_nonpos hr.le h)]
    exact ⟨Real.log_le_log hr hx.1, Real.log_nonpos (by linarith [hx.1]) hx.2⟩

/-- **The real inequality behind Prop. 1**: if `u` and `v` lie between `1` and `r > 0`, then
`|log (v / u)| ≤ |log r|`. -/
theorem abs_log_div_le {r u v : ℝ} (hr : 0 < r) (hu : u ∈ uIcc 1 r) (hv : v ∈ uIcc 1 r) :
    |Real.log (v / u)| ≤ |Real.log r| := by
  rw [Real.log_div (pos_of_mem_uIcc hr hv).ne' (pos_of_mem_uIcc hr hu).ne']
  have := abs_sub_le_of_uIcc_subset_uIcc
    (uIcc_subset_uIcc (log_mem_uIcc hr hu) (log_mem_uIcc hr hv))
  simpa using this

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Representatives of points of `S(E)` -/

/-- `v` represents the point `x` of `S(E)`: `v ≠ 0` and `s(v) = x`, i.e. `v ∈ F(x)`. -/
def IsRep (v : E) (x : Sphere E) : Prop := ∃ hv : v ≠ 0, mk v hv = x

theorem isRep_mk (v : E) (hv : v ≠ 0) : IsRep v (mk v hv) := ⟨hv, rfl⟩

theorem IsRep.ne_zero {v : E} {x : Sphere E} (h : IsRep v x) : v ≠ 0 := h.1

theorem exists_isRep (x : Sphere E) : ∃ v : E, IsRep v x :=
  ⟨_, Module.Ray.someVector_ne_zero x, mk_someVector x⟩

theorem IsRep.smul {v : E} {x : Sphere E} (h : IsRep v x) {c : ℝ} (hc : 0 < c) :
    IsRep (c • v) x := by
  obtain ⟨hv, rfl⟩ := h
  exact ⟨smul_ne_zero hc.ne' hv, mk_smul hv hc _⟩

theorem IsRep.exists_pos {v w : E} {x : Sphere E} (hv : IsRep v x) (hw : IsRep w x) :
    ∃ c : ℝ, 0 < c ∧ w = c • v := by
  obtain ⟨hv0, rfl⟩ := hv
  obtain ⟨hw0, h⟩ := hw
  obtain ⟨c, hc, e⟩ := (mk_eq_mk_iff_exists_pos hv0 hw0).1 h.symm
  exact ⟨c, hc, e.symm⟩

theorem IsRep.eq {v : E} {x y : Sphere E} (hx : IsRep v x) (hy : IsRep v y) : x = y := by
  obtain ⟨_, rfl⟩ := hx
  obtain ⟨_, rfl⟩ := hy
  rfl

theorem IsRep.neg {v : E} {x : Sphere E} (h : IsRep v x) : IsRep (-v) (-x) := by
  obtain ⟨hv, rfl⟩ := h
  exact ⟨neg_ne_zero.2 hv, (neg_mk v hv).symm⟩

theorem IsRep.linearEquiv {v : E} {x : Sphere E} (h : IsRep v x) (f : E ≃ₗ[ℝ] E) :
    IsRep (f v) (f • x) := by
  obtain ⟨hv, rfl⟩ := h
  exact ⟨f.map_ne_zero_iff.2 hv, (smul_mk f v hv).symm⟩

/-! ### Pairs of independent vectors -/

theorem coeffs_eq {a b : E} (h : LinearIndependent ℝ ![a, b]) {s t s' t' : ℝ}
    (e : s • a + t • b = s' • a + t' • b) : s = s' ∧ t = t' := by
  have h0 : (s - s') • a + (t - t') • b = 0 := by
    rw [sub_smul, sub_smul, sub_add_sub_comm, e, sub_self]
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 h _ _ h0
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

theorem linearIndependent_pair_smul {a b : E} (h : LinearIndependent ℝ ![a, b]) {c d : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) : LinearIndependent ℝ ![c • a, d • b] := by
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  rw [smul_smul, smul_smul] at hst
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 h _ _ hst
  exact ⟨(mul_eq_zero.1 h1).resolve_right hc, (mul_eq_zero.1 h2).resolve_right hd⟩

/-- Two representatives of one point are dependent. -/
theorem not_linearIndependent_of_isRep {a b : E} {A : Sphere E} (ha : IsRep a A)
    (hb : IsRep b A) : ¬ LinearIndependent ℝ ![a, b] := by
  intro h
  obtain ⟨c, -, rfl⟩ := ha.exists_pos hb
  have := (LinearIndependent.pair_iff.1 h c (-1) (by rw [neg_one_smul, add_neg_cancel])).2
  norm_num at this

/-- Representatives of two diametrically opposite points are dependent. -/
theorem not_linearIndependent_of_isRep_neg {a b : E} {A : Sphere E} (ha : IsRep a A)
    (hb : IsRep b (-A)) : ¬ LinearIndependent ℝ ![a, b] := by
  intro h
  obtain ⟨c, -, rfl⟩ := ha.neg.exists_pos hb
  have := (LinearIndependent.pair_iff.1 h c 1 (by rw [one_smul, smul_neg, add_neg_cancel])).2
  norm_num at this

/-- Representatives of two points which are neither equal nor diametrically opposite are
independent. -/
theorem linearIndependent_of_ne {a b : E} {A B : Sphere E} (ha : IsRep a A) (hb : IsRep b B)
    (h1 : B ≠ A) (h2 : B ≠ -A) : LinearIndependent ℝ ![a, b] := by
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right ha.ne_zero, rfl⟩
  · exfalso
    have hb' : b = (-s / t) • a := by
      have : t • b = -(s • a) := eq_neg_of_add_eq_zero_right hst
      calc b = t⁻¹ • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = (-s / t) • a := by
          rw [this, smul_neg, smul_smul, ← neg_smul, neg_mul_eq_mul_neg, div_eq_inv_mul]
    rcases lt_trichotomy (-s / t) 0 with hneg | hzero | hpos
    · apply h2
      have : IsRep b (-A) := by
        rw [hb']
        have := ha.neg.smul (neg_pos.2 hneg)
        rwa [smul_neg, neg_smul, neg_neg] at this
      exact hb.eq this
    · rw [hzero, zero_smul] at hb'
      exact hb.ne_zero hb'
    · apply h1
      rw [hb'] at hb
      exact hb.eq (ha.smul hpos)

/-- If `a`, `b` are independent and positive combinations of `u`, `w`, then the two sums of
coefficients are positive. -/
theorem coeff_sums_pos {u w : E} {S₁ T₁ S₂ T₂ : ℝ}
    (h : LinearIndependent ℝ ![S₁ • u + T₁ • w, S₂ • u + T₂ • w]) (hS₁ : 0 ≤ S₁) (hT₁ : 0 ≤ T₁)
    (hS₂ : 0 ≤ S₂) (hT₂ : 0 ≤ T₂) : 0 < S₁ + S₂ ∧ 0 < T₁ + T₂ := by
  have hne := h.ne_zero 0
  simp only [Matrix.cons_val_zero] at hne
  constructor
  · by_contra hS
    have e1 : S₁ = 0 := by linarith
    have e2 : S₂ = 0 := by linarith
    subst e1 e2
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 h T₂ (-T₁) (by module)
    have : T₁ = 0 := by linarith
    subst this
    exact hne (by simp)
  · by_contra hT
    have e1 : T₁ = 0 := by linarith
    have e2 : T₂ = 0 := by linarith
    subst e1 e2
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 h S₂ (-S₁) (by module)
    have : S₁ = 0 := by linarith
    subst this
    exact hne (by simp)

/-! ### Segments in coordinates -/

/-- The points of the closed segment `(A, B)` are the positive combinations of representatives. -/
theorem mem_closedSeg_iff {a b : E} {A B X : Sphere E} (ha : IsRep a A) (hb : IsRep b B) :
    X ∈ closedSeg A B ↔ ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ IsRep (s • a + t • b) X := by
  obtain ⟨ha0, rfl⟩ := ha
  obtain ⟨hb0, rfl⟩ := hb
  rw [closedSeg_mk, segOf, mem_ofCone]
  constructor
  · rintro ⟨v, hv, ⟨s, t, hs, ht, -, rfl⟩, rfl⟩
    exact ⟨s, t, hs, ht, hv, rfl⟩
  · rintro ⟨s, t, hs, ht, hv, rfl⟩
    have hst : 0 < s + t := by
      rcases (add_nonneg hs ht).lt_or_eq with h | h
      · exact h
      · exfalso
        have hs0 : s = 0 := by linarith
        have ht0 : t = 0 := by linarith
        subst hs0 ht0
        simp at hv
    refine ⟨(s + t)⁻¹ • (s • a + t • b), smul_ne_zero (inv_ne_zero hst.ne') hv,
      ⟨s / (s + t), t / (s + t), by positivity, by positivity, by field_simp, ?_⟩,
      mk_smul hv (inv_pos.2 hst) _⟩
    rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

/-- The points of the open segment `)A, B(` are the strictly positive combinations. -/
theorem mem_openSeg_iff {a b : E} {A B X : Sphere E} (ha : IsRep a A) (hb : IsRep b B) :
    X ∈ openSeg A B ↔ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ IsRep (s • a + t • b) X := by
  obtain ⟨ha0, rfl⟩ := ha
  obtain ⟨hb0, rfl⟩ := hb
  rw [openSeg_mk, openSegOf, mem_ofCone]
  constructor
  · rintro ⟨v, hv, ⟨s, t, hs, ht, -, rfl⟩, rfl⟩
    exact ⟨s, t, hs, ht, hv, rfl⟩
  · rintro ⟨s, t, hs, ht, hv, rfl⟩
    have hst : 0 < s + t := by positivity
    refine ⟨(s + t)⁻¹ • (s • a + t • b), smul_ne_zero (inv_ne_zero hst.ne') hv,
      ⟨s / (s + t), t / (s + t), by positivity, by positivity, by field_simp, ?_⟩,
      mk_smul hv (inv_pos.2 hst) _⟩
    rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

/-- **Déf. 7's degenerate segment**: `(m, m) = {m}`. -/
theorem closedSeg_self (m : Sphere E) : closedSeg m m = {m} := by
  induction m using ind with
  | h v hv =>
    rw [closedSeg_mk, segOf, segment_same]
    ext x
    rw [mem_ofCone, mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, hwv, rfl⟩
      rw [mem_singleton_iff] at hwv
      subst hwv
      rfl
    · rintro rfl
      exact ⟨v, hv, mem_singleton v, rfl⟩

/-- If two independent points `A`, `B` lie on the segment `(A₁, B₁)`, then `A₁`, `B₁` are
independent too. -/
theorem linearIndependent_of_mem_closedSeg {a b a₁ b₁ : E} {A B A₁ B₁ : Sphere E}
    (ha : IsRep a A) (hb : IsRep b B) (hab : LinearIndependent ℝ ![a, b]) (ha₁ : IsRep a₁ A₁)
    (hb₁ : IsRep b₁ B₁) (hA : A ∈ closedSeg A₁ B₁) (hB : B ∈ closedSeg A₁ B₁) :
    LinearIndependent ℝ ![a₁, b₁] := by
  refine linearIndependent_of_ne ha₁ hb₁ (fun h => ?_) (fun h => ?_)
  · rw [h, closedSeg_self, mem_singleton_iff] at hA hB
    rw [hA] at ha
    rw [hB] at hb
    exact not_linearIndependent_of_isRep ha hb hab
  · rw [h, closedSeg_neg_self] at hA hB
    simp only [mem_insert_iff, mem_singleton_iff] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact not_linearIndependent_of_isRep ha hb hab
    · exact not_linearIndependent_of_isRep_neg ha hb hab
    · exact not_linearIndependent_of_isRep_neg ha (by rwa [neg_neg]) hab
    · exact not_linearIndependent_of_isRep ha hb hab

/-! ### The cross-ratio of four points of a segment of `S(E)` -/

/-- **The cross-ratio `(A', B', B, A) = r` of four points of a segment `(A, B)` of `S(E)`**, `A'`
and `B'` interior: there are representatives `a` of `A` and `b` of `B`, linearly independent
(`A ≠ B`, `A`, `B` not diametrically opposite), with `a + b` representing `A'` and `a + r b`
representing `B'`, `r > 0`. In an affine chart it is the classical cross-ratio of algebraic
measures (`isCrossRatio_affine`). -/
def IsCrossRatio (A' B' B A : Sphere E) (r : ℝ) : Prop :=
  0 < r ∧ ∃ a b : E, LinearIndependent ℝ ![a, b] ∧ IsRep a A ∧ IsRep b B ∧ IsRep (a + b) A' ∧
    IsRep (a + r • b) B'

theorem IsCrossRatio.pos {A' B' B A : Sphere E} {r : ℝ} (h : IsCrossRatio A' B' B A r) : 0 < r :=
  h.1

/-- **The cross-ratio is well defined** (it does not depend on the representatives). -/
theorem IsCrossRatio.unique {A' B' B A : Sphere E} {r r' : ℝ} (h : IsCrossRatio A' B' B A r)
    (h' : IsCrossRatio A' B' B A r') : r = r' := by
  obtain ⟨-, a, b, hab, ha, hb, h1, h2⟩ := h
  obtain ⟨-, a', b', -, ha', hb', h1', h2'⟩ := h'
  obtain ⟨c, hc, rfl⟩ := ha.exists_pos ha'
  obtain ⟨d, hd, rfl⟩ := hb.exists_pos hb'
  obtain ⟨e, he, he'⟩ := h1.exists_pos h1'
  obtain ⟨hce, hde⟩ := coeffs_eq hab (s := c) (t := d) (s' := e) (t' := e)
    (by rw [he', smul_add])
  obtain ⟨f, hf, hf'⟩ := h2.exists_pos h2'
  obtain ⟨hcf, hrd⟩ := coeffs_eq hab (s := c) (t := r' * d) (s' := f) (t' := f * r)
    (by rw [← smul_smul, hf', smul_add, smul_smul])
  have hdf : d = f := by rw [hde, ← hce, hcf]
  rw [hdf, mul_comm f r] at hrd
  exact (mul_right_cancel₀ hf.ne' hrd).symm

/-- **The cross-ratio in coordinates**: for independent representatives `a₁`, `b₁` of `A₁`, `B₁`,
if `x₁ a₁ + y₁ b₁` represents `A'` and `x₂ a₁ + y₂ b₁` represents `B'` (all coefficients
positive), then `(A', B', B₁, A₁) = (y₂/x₂) / (y₁/x₁)`. -/
theorem isCrossRatio_of_coords {a₁ b₁ : E} {A₁ B₁ A' B' : Sphere E}
    (hli : LinearIndependent ℝ ![a₁, b₁]) (ha₁ : IsRep a₁ A₁) (hb₁ : IsRep b₁ B₁)
    {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (h1 : IsRep (x₁ • a₁ + y₁ • b₁) A') (h2 : IsRep (x₂ • a₁ + y₂ • b₁) B') :
    IsCrossRatio A' B' B₁ A₁ (y₂ / x₂ / (y₁ / x₁)) := by
  refine ⟨by positivity, x₁ • a₁, y₁ • b₁, linearIndependent_pair_smul hli hx₁.ne' hy₁.ne',
    ha₁.smul hx₁, hb₁.smul hy₁, h1, ?_⟩
  have := h2.smul (c := x₁ / x₂) (by positivity)
  convert this using 1
  match_scalars <;> field_simp

/-- **Déf. 1, « Ce rapport anharmonique est une quantité supérieure ou égale à l'unité »**: for
`A, A', B', B` met in this order from `A` to `B` (`B' ∈ (A', B)`), `(A', B', B, A) ≥ 1`. -/
theorem IsCrossRatio.one_le {A' B' B A : Sphere E} {r : ℝ} (h : IsCrossRatio A' B' B A r)
    (hord : B' ∈ closedSeg A' B) : 1 ≤ r := by
  obtain ⟨hr, a, b, hab, ha, hb, h1, h2⟩ := h
  obtain ⟨s, t, hs, ht, hst⟩ := (mem_closedSeg_iff h1 hb).1 hord
  obtain ⟨c, hc, hc'⟩ := h2.exists_pos hst
  obtain ⟨e1, e2⟩ := coeffs_eq hab (s := s) (t := s + t) (s' := c) (t' := c * r)
    (by rw [← smul_smul, ← smul_add, ← hc']; module)
  by_contra hlt
  push Not at hlt
  nlinarith [mul_lt_mul_of_pos_left hlt hc]

/-- **The cross-ratio exists** for two interior points of a segment `(A, B)`, `A ≠ B` not
diametrically opposite. -/
theorem exists_isCrossRatio {A B A' B' : Sphere E} (hAB : B ≠ A) (hAB' : B ≠ -A)
    (hA' : A' ∈ openSeg A B) (hB' : B' ∈ openSeg A B) : ∃ r, IsCrossRatio A' B' B A r := by
  obtain ⟨a, ha⟩ := exists_isRep A
  obtain ⟨b, hb⟩ := exists_isRep B
  have hab := linearIndependent_of_ne ha hb hAB hAB'
  obtain ⟨s, t, hs, ht, h1⟩ := (mem_openSeg_iff ha hb).1 hA'
  obtain ⟨s', t', hs', ht', h2⟩ := (mem_openSeg_iff ha hb).1 hB'
  exact ⟨_, isCrossRatio_of_coords hab ha hb hs ht hs' ht' h1 h2⟩

/-- **The classical cross-ratio**: on an affine line `t ↦ p₀ + t d` (`p₀`, `d` independent), the
points of parameters `s < p, q < r` have cross-ratio `(p, q, r, s)` (`crossRatio`), the ratio of
algebraic measures of p. 250. -/
theorem isCrossRatio_affine {p₀ d : E} (hli : LinearIndependent ℝ ![p₀, d]) {p q r s : ℝ}
    (hsp : s < p) (hpr : p < r) (hsq : s < q) (hqr : q < r) {A' B' B A : Sphere E}
    (hA' : IsRep (p₀ + p • d) A') (hB' : IsRep (p₀ + q • d) B') (hB : IsRep (p₀ + r • d) B)
    (hA : IsRep (p₀ + s • d) A) : IsCrossRatio A' B' B A (crossRatio p q r s) := by
  have hrs : r - s ≠ 0 := by linarith
  have hrq : r - q ≠ 0 := by linarith
  have hsp' : s - p ≠ 0 := by linarith
  have hps : p - s ≠ 0 := by linarith
  have hrp : r - p ≠ 0 := by linarith
  have hqs : q - s ≠ 0 := by linarith
  have hsq' : s - q ≠ 0 := by linarith
  have hli' : LinearIndependent ℝ ![p₀ + s • d, p₀ + r • d] := by
    refine LinearIndependent.pair_iff.2 fun x y hxy => ?_
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hli (x + y) (x * s + y * r)
      (by rw [← hxy]; module)
    have hy : y * (r - s) = 0 := by linear_combination h2 - s * h1
    have hy0 : y = 0 := (mul_eq_zero.1 hy).resolve_right hrs
    exact ⟨by linear_combination h1 - hy0, hy0⟩
  have hcr := isCrossRatio_of_coords hli' hA hB (x₁ := (r - p) / (r - s)) (y₁ := (p - s) / (r - s))
    (x₂ := (r - q) / (r - s)) (y₂ := (q - s) / (r - s))
    (div_pos (by linarith) (by linarith)) (div_pos (by linarith) (by linarith))
    (div_pos (by linarith) (by linarith)) (div_pos (by linarith) (by linarith))
    (by convert hA' using 1; match_scalars <;> field_simp <;> ring)
    (by convert hB' using 1; match_scalars <;> field_simp <;> ring)
  convert hcr using 1
  unfold crossRatio
  field_simp
  ring

/-! ### The action of `GS(E)` -/

theorem IsCrossRatio.linearEquiv {A' B' B A : Sphere E} {r : ℝ} (h : IsCrossRatio A' B' B A r)
    (f : E ≃ₗ[ℝ] E) : IsCrossRatio (f • A') (f • B') (f • B) (f • A) r := by
  obtain ⟨hr, a, b, hab, ha, hb, h1, h2⟩ := h
  refine ⟨hr, f a, f b, ?_, ha.linearEquiv f, hb.linearEquiv f, ?_, ?_⟩
  · refine LinearIndependent.pair_iff.2 fun s t hst => LinearIndependent.pair_iff.1 hab s t ?_
    apply f.injective
    rw [map_add, map_smul, map_smul, hst, map_zero]
  · rw [← map_add]
    exact h1.linearEquiv f
  · rw [← map_smul, ← map_add]
    exact h2.linearEquiv f

/-- **`GS(E)` preserves the cross-ratio.** -/
theorem IsCrossRatio.smul {A' B' B A : Sphere E} {r : ℝ} (h : IsCrossRatio A' B' B A r)
    (g : GSE E) : IsCrossRatio (g • A') (g • B') (g • B) (g • A) r := by
  induction g using QuotientGroup.induction_on with
  | H f => simpa only [GSE.mk_smul] using h.linearEquiv f

theorem isCrossRatio_smul_iff (g : GSE E) {A' B' B A : Sphere E} {r : ℝ} :
    IsCrossRatio (g • A') (g • B') (g • B) (g • A) r ↔ IsCrossRatio A' B' B A r := by
  refine ⟨fun h => ?_, fun h => h.smul g⟩
  simpa only [inv_smul_smul] using h.smul g⁻¹

/-! ### Exchanging the points -/

/-- Exchanging `A'` and `B'` inverts the cross-ratio. -/
theorem IsCrossRatio.swap {A' B' B A : Sphere E} {r : ℝ} (h : IsCrossRatio A' B' B A r) :
    IsCrossRatio B' A' B A r⁻¹ := by
  obtain ⟨hr, a, b, hab, ha, hb, h1, h2⟩ := h
  refine ⟨inv_pos.2 hr, a, r • b, ?_, ha, hb.smul hr, h2, ?_⟩
  · simpa using linearIndependent_pair_smul hab one_ne_zero hr.ne'
  · rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- Reading the segment from `B` to `A` leaves the cross-ratio unchanged. -/
theorem IsCrossRatio.reverse {A' B' B A : Sphere E} {r : ℝ} (h : IsCrossRatio A' B' B A r) :
    IsCrossRatio B' A' A B r := by
  obtain ⟨hr, a, b, hab, ha, hb, h1, h2⟩ := h
  refine ⟨hr, r • b, a, ?_, hb.smul hr, ha, ?_, ?_⟩
  · refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    have := LinearIndependent.pair_iff.1 hab t (s * r) (by rw [← smul_smul, add_comm]; exact hst)
    exact ⟨(mul_eq_zero.1 this.2).resolve_right hr.ne', this.1⟩
  · rwa [add_comm]
  · have := h1.smul hr
    rwa [smul_add, add_comm] at this

/-! ### Déf. 1 — the projective measure -/

/-- **Déf. 1, the projective measure of `A'B'` relative to `AB`** (`bzdef:c2s2d1_mesure_projective`):
`log (A', B', B, A)`, valued in `EReal`. It is `⊤` when the cross-ratio is not a positive real
number: when it is infinite (`A' = A` with `B' ≠ A`, or `B' = B` with `A' ≠ B`), and, by
convention, when it is undefined (`0/0`: `A' = B' = A`, `A' = B' = B`, or `A = B`). The absolute
value makes it
independent of the order in which `A'`, `B'` are named (`projMeasure_swap`); in the order of
Déf. 1 it is `log (A', B', B, A)` itself (`projMeasure_eq_log`). -/
def projMeasure (A A' B' B : Sphere E) : EReal :=
  ⨅ (r : ℝ) (_ : IsCrossRatio A' B' B A r), ((|Real.log r| : ℝ) : EReal)

theorem projMeasure_eq {A A' B' B : Sphere E} {r : ℝ} (h : IsCrossRatio A' B' B A r) :
    projMeasure A A' B' B = ((|Real.log r| : ℝ) : EReal) :=
  le_antisymm (iInf₂_le r h) (le_iInf₂ fun r' h' => by rw [h.unique h'])

theorem projMeasure_eq_top {A A' B' B : Sphere E} (h : ∀ r, ¬ IsCrossRatio A' B' B A r) :
    projMeasure A A' B' B = ⊤ := by
  simp [projMeasure, h]

theorem projMeasure_nonneg (A A' B' B : Sphere E) : 0 ≤ projMeasure A A' B' B :=
  le_iInf₂ fun _ _ => EReal.coe_nonneg.2 (abs_nonneg _)

theorem projMeasure_lt_top_iff {A A' B' B : Sphere E} :
    projMeasure A A' B' B < ⊤ ↔ ∃ r, IsCrossRatio A' B' B A r := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    rw [projMeasure_eq_top h'] at h
    exact lt_irrefl _ h
  · rintro ⟨r, hr⟩
    rw [projMeasure_eq hr]
    exact EReal.coe_lt_top _

/-- **Déf. 1**: for `A ≠ B` not diametrically opposite and `A, A', B', B` met in this order from
`A` to `B`, `A'`, `B'` interior, the cross-ratio `(A', B', B, A)` exists, is `≥ 1`, and the
projective measure is its logarithm. -/
theorem projMeasure_eq_log {A A' B' B : Sphere E} (hAB : B ≠ A) (hAB' : B ≠ -A)
    (hA' : A' ∈ openSeg A B) (hB' : B' ∈ openSeg A B) (hord : B' ∈ closedSeg A' B) :
    ∃ r : ℝ, IsCrossRatio A' B' B A r ∧ 1 ≤ r ∧
      projMeasure A A' B' B = ((Real.log r : ℝ) : EReal) := by
  obtain ⟨r, hr⟩ := exists_isCrossRatio hAB hAB' hA' hB'
  refine ⟨r, hr, hr.one_le hord, ?_⟩
  rw [projMeasure_eq hr, abs_of_nonneg (Real.log_nonneg (hr.one_le hord))]

/-- The measure of a segment with endpoint `A` is `⊤`: the cross-ratio `(A, B', B, A)` is infinite
when `B' ≠ A`, and undefined (`0/0`) when `B' = A`, where `⊤` is a convention. -/
theorem projMeasure_left_eq_top (A B' B : Sphere E) : projMeasure A A B' B = ⊤ := by
  refine projMeasure_eq_top fun r ⟨_, a, b, hab, ha, _, h1, _⟩ => ?_
  obtain ⟨c, _, hc⟩ := ha.exists_pos h1
  have := (coeffs_eq hab (s := 1) (t := 1) (s' := c) (t' := 0)
    (by rw [one_smul, one_smul, zero_smul, add_zero, hc])).2
  exact one_ne_zero this

/-- The measure of a segment with endpoint `B` is `⊤`: the cross-ratio `(A', B, B, A)` is infinite
when `A' ≠ B`, and undefined (`0/0`) when `A' = B`, where `⊤` is a convention. -/
theorem projMeasure_right_eq_top (A A' B : Sphere E) : projMeasure A A' B B = ⊤ := by
  refine projMeasure_eq_top fun r ⟨_, a, b, hab, _, hb, _, h2⟩ => ?_
  obtain ⟨c, _, hc⟩ := hb.exists_pos h2
  have := (coeffs_eq hab (s := 1) (t := r) (s' := 0) (t' := c)
    (by rw [one_smul, zero_smul, zero_add, hc])).1
  exact one_ne_zero this

/-- There is no cross-ratio on a degenerate segment `(A, A)` (four equal points, `0/0`); `⊤` is a
convention. -/
theorem projMeasure_same_eq_top (A A' B' : Sphere E) : projMeasure A A' B' A = ⊤ :=
  projMeasure_eq_top fun _ ⟨_, _, _, hab, ha, hb, _, _⟩ => not_linearIndependent_of_isRep ha hb hab

/-- **The projective measure is invariant by `GS(E)`** (Déf. 1, « la notion de mesure projective
est invariante par les automorphismes de $GS(n, \R)$ »). -/
theorem projMeasure_smul (g : GSE E) (A A' B' B : Sphere E) :
    projMeasure (g • A) (g • A') (g • B') (g • B) = projMeasure A A' B' B := by
  simp only [projMeasure, isCrossRatio_smul_iff]

/-- The projective measure does not depend on the order in which `A'`, `B'` are named. -/
theorem projMeasure_swap (A A' B' B : Sphere E) :
    projMeasure A A' B' B = projMeasure A B' A' B := by
  by_cases h : ∃ r, IsCrossRatio A' B' B A r
  · obtain ⟨r, hr⟩ := h
    rw [projMeasure_eq hr, projMeasure_eq hr.swap, Real.log_inv, abs_neg]
  · push Not at h
    rw [projMeasure_eq_top h, projMeasure_eq_top fun r hr => h _ hr.swap]

/-- The projective measure does not depend on the direction in which the segment is read. -/
theorem projMeasure_reverse (A A' B' B : Sphere E) :
    projMeasure A A' B' B = projMeasure B B' A' A := by
  by_cases h : ∃ r, IsCrossRatio A' B' B A r
  · obtain ⟨r, hr⟩ := h
    rw [projMeasure_eq hr, projMeasure_eq hr.reverse]
  · push Not at h
    rw [projMeasure_eq_top h, projMeasure_eq_top fun r hr => h _ hr.reverse]

/-- The measure of a point relative to a segment containing it in its interior is `0`. -/
theorem projMeasure_self {A A' B : Sphere E} (hAB : B ≠ A) (hAB' : B ≠ -A)
    (hA' : A' ∈ openSeg A B) : projMeasure A A' A' B = 0 := by
  obtain ⟨a, ha⟩ := exists_isRep A
  obtain ⟨b, hb⟩ := exists_isRep B
  obtain ⟨s, t, hs, ht, h1⟩ := (mem_openSeg_iff ha hb).1 hA'
  have hcr := isCrossRatio_of_coords (linearIndependent_of_ne ha hb hAB hAB') ha hb hs ht hs ht
    h1 h1
  rw [projMeasure_eq hcr, div_self (by positivity), Real.log_one, abs_zero]
  rfl

/-! ### Prop. 1 — monotonicity -/

/-- The points of a segment `(A', B')`, `A'`, `B'` represented by `a + b`, `a + r b`, are the
`x a + y b` with `y / x` between `1` and `r`. -/
theorem exists_coords_of_mem_closedSeg {a b : E} {A' B' X : Sphere E} {r : ℝ} (hr : 0 < r)
    (h1 : IsRep (a + b) A') (h2 : IsRep (a + r • b) B') (hX : X ∈ closedSeg A' B') :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ y / x ∈ uIcc 1 r ∧ IsRep (x • a + y • b) X := by
  obtain ⟨σ, τ, hσ, hτ, hX⟩ := (mem_closedSeg_iff h1 h2).1 hX
  have hστ : 0 < σ + τ := by
    rcases (add_nonneg hσ hτ).lt_or_eq with h | h
    · exact h
    · exfalso
      have e1 : σ = 0 := by linarith
      have e2 : τ = 0 := by linarith
      subst e1 e2
      exact hX.ne_zero (by simp)
  have hmem := wavg_mem_uIcc r hσ hτ hστ
  have hy : 0 < σ + τ * r := by
    have := pos_of_mem_uIcc hr hmem
    rwa [div_pos_iff_of_pos_right hστ] at this
  refine ⟨σ + τ, σ + τ * r, hστ, hy, hmem, ?_⟩
  convert hX using 1
  module

/-- **Prop. 1, first assertion**: replacing `(A', B')` by a segment contained in it decreases the
projective measure (`A''`, `B''` only need to lie on `(A', B')`). -/
theorem projMeasure_le_inner {A A' B' B A'' B'' : Sphere E} (hA'' : A'' ∈ closedSeg A' B')
    (hB'' : B'' ∈ closedSeg A' B') : projMeasure A A'' B'' B ≤ projMeasure A A' B' B := by
  by_cases h : ∃ r, IsCrossRatio A' B' B A r
  swap
  · push Not at h
    rw [projMeasure_eq_top h]
    exact le_top
  obtain ⟨r, hr⟩ := h
  rw [projMeasure_eq hr]
  obtain ⟨hr0, a, b, hab, ha, hb, h1, h2⟩ := hr
  obtain ⟨x₁, y₁, hx₁, hy₁, hu, hA⟩ := exists_coords_of_mem_closedSeg hr0 h1 h2 hA''
  obtain ⟨x₂, y₂, hx₂, hy₂, hv, hB⟩ := exists_coords_of_mem_closedSeg hr0 h1 h2 hB''
  rw [projMeasure_eq (isCrossRatio_of_coords hab ha hb hx₁ hy₁ hx₂ hy₂ hA hB)]
  exact EReal.coe_le_coe_iff.2 (abs_log_div_le hr0 hu hv)

/-- **Prop. 1, second assertion**: replacing `AB` by a segment containing it decreases the
projective measure (`A`, `B` only need to lie on `(A₁, B₁)`). -/
theorem projMeasure_le_outer {A B A₁ B₁ A' B' : Sphere E} (hA : A ∈ closedSeg A₁ B₁)
    (hB : B ∈ closedSeg A₁ B₁) : projMeasure A₁ A' B' B₁ ≤ projMeasure A A' B' B := by
  by_cases h : ∃ r, IsCrossRatio A' B' B A r
  swap
  · push Not at h
    rw [projMeasure_eq_top h]
    exact le_top
  obtain ⟨r, hr⟩ := h
  rw [projMeasure_eq hr]
  obtain ⟨hr0, a, b, hab, ha, hb, h1, h2⟩ := hr
  obtain ⟨a₁, ha₁⟩ := exists_isRep A₁
  obtain ⟨b₁, hb₁⟩ := exists_isRep B₁
  have hli₁ := linearIndependent_of_mem_closedSeg ha hb hab ha₁ hb₁ hA hB
  obtain ⟨s₁, t₁, hs₁, ht₁, hA'⟩ := (mem_closedSeg_iff ha₁ hb₁).1 hA
  obtain ⟨s₂, t₂, hs₂, ht₂, hB'⟩ := (mem_closedSeg_iff ha₁ hb₁).1 hB
  obtain ⟨c₁, hc₁, hca⟩ := hA'.exists_pos ha
  obtain ⟨c₂, hc₂, hcb⟩ := hB'.exists_pos hb
  have ea : a = (c₁ * s₁) • a₁ + (c₁ * t₁) • b₁ := by rw [hca]; module
  have eb : b = (c₂ * s₂) • a₁ + (c₂ * t₂) • b₁ := by rw [hcb]; module
  have hS₁ : 0 ≤ c₁ * s₁ := by positivity
  have hT₁ : 0 ≤ c₁ * t₁ := by positivity
  have hS₂ : 0 ≤ c₂ * s₂ := by positivity
  have hT₂ : 0 ≤ c₂ * t₂ := by positivity
  generalize c₁ * s₁ = S₁ at ea hS₁
  generalize c₁ * t₁ = T₁ at ea hT₁
  generalize c₂ * s₂ = S₂ at eb hS₂
  generalize c₂ * t₂ = T₂ at eb hT₂
  subst ea eb
  obtain ⟨hS, hT⟩ := coeff_sums_pos hab hS₁ hT₁ hS₂ hT₂
  have hσ := wavg_mem_uIcc r hS₁ hS₂ hS
  have hτ := wavg_mem_uIcc r hT₁ hT₂ hT
  have hx₂ : 0 < S₁ + S₂ * r := by
    have := pos_of_mem_uIcc hr0 hσ
    rwa [div_pos_iff_of_pos_right hS] at this
  have hy₂ : 0 < T₁ + T₂ * r := by
    have := pos_of_mem_uIcc hr0 hτ
    rwa [div_pos_iff_of_pos_right hT] at this
  have hcr := isCrossRatio_of_coords hli₁ ha₁ hb₁ hS hT hx₂ hy₂
    (by convert h1 using 1; module) (by convert h2 using 1; module)
  rw [projMeasure_eq hcr]
  refine EReal.coe_le_coe_iff.2 ?_
  have e : (T₁ + T₂ * r) / (S₁ + S₂ * r) / ((T₁ + T₂) / (S₁ + S₂)) =
      ((T₁ + T₂ * r) / (T₁ + T₂)) / ((S₁ + S₂ * r) / (S₁ + S₂)) := by
    field_simp
  rw [e]
  exact abs_log_div_le hr0 hσ hτ

/-- **Prop. 1** (`bzprop:c2s2p1_mesure_projective_monotone`), in the paper's words: the projective
measure decreases if `(A', B')` is replaced by a segment contained in `(A', B')`, and decreases
again if `AB` is replaced by a segment containing it. -/
theorem projMeasure_antitone {A A' B' B A'' B'' A₁ B₁ : Sphere E} :
    (closedSeg A'' B'' ⊆ closedSeg A' B' → projMeasure A A'' B'' B ≤ projMeasure A A' B' B) ∧
    (closedSeg A B ⊆ closedSeg A₁ B₁ → projMeasure A₁ A' B' B₁ ≤ projMeasure A A' B' B) :=
  ⟨fun h => projMeasure_le_inner (h (left_mem_closedSeg _ _)) (h (right_mem_closedSeg _ _)),
    fun h => projMeasure_le_outer (h (left_mem_closedSeg _ _)) (h (right_mem_closedSeg _ _))⟩

end Sphere

end Benzecri
