import Benzecri.Chapter2.CrossRatio
import Benzecri.Structure.Classes

/-!
# `Benzecri.Chapter2.Mesure` — majorised segments and parts, the pseudo-length `l_V` (Ch. 2 § 2, Déf. 2–4) and its properties 1°–4°

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal pp. 249–251; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-mesure (DEC-137).

* **`bzdef:c2s2d2_segment_majore`** — `benzecri1960_ch2.tex:277` (Déf. 2, l.277–282, p. 250):
  `Benzecri.IsMajoreSeg n k Sg' A' B'`; every compatible chart is quantified, as printed, and one
  chart suffices (`isMajoreSeg_iff_exists_chart`).
* **`bzdef:c2s2d3_pseudo_longueur`** — `benzecri1960_ch2.tex:284` (Déf. 3, l.284–287, p. 250):
  `Benzecri.pseudoLength n Sg M N : EReal`, the infimum of the `k` majorising the segment; it is
  finite for `n ≥ 1` (`pseudoLength_lt_top`).
* **`bzdef:c2s2d4_partie_majoree`** — `benzecri1960_ch2.tex:359` (Déf. 4, l.359–363, p. 251):
  `Benzecri.IsMajorePart n k C`.
* Properties 1°–4° of the editorial enonce `bzthm:c2s2_proprietes_pseudo_longueur`
  (`benzecri1960_ch2.tex:229`, l.232–243; proof l.293–301), as lemmas, NOT marked (their row waits
  on OQ-38(a), target T-bz-c2-proprietes): 1° `pseudoLength_nonneg`, `pseudoLength_self` (`n ≥ 1`;
  for `n = 0` see the question below, `pseudoLength_self_eq_top_dim_zero`), 2° `pseudoLength_smul`,
  3° `pseudoLength_mono`, 4° `pseudoLength_le_opens`, `pseudoLength_le_opens'`.

> **Déf. 2.** Soit $(A', B')$ un segment d'une variété localement projective $V$; on dit que
> $(A', B')$ est *majoré par $k$ dans $V$* s'il existe un segment $(A, B)$ de $V$ contenant
> $(A', B')$ tel que, si $\varphi$ est une carte compatible d'un voisinage de $(A, B)$ sur un ouvert
> de $S(n)$, on ait : mesure projective de $\varphi(A', B')$ relativement à $\varphi(A, B)<k$.
>
> **Déf. 3.** La *pseudo-longueur* $l_V(M, N)$ d'un segment $(M, N)$ d'une variété localement
> projective est la borne inférieure des nombres $k$ qui majorent $(M, N)$ dans $V$.
>
> **Déf. 4.** Soit $C$ une partie d'une variété localement projective $V$ : on dit que $C$ est
> majoré par $k$ dans $V$, si deux points quelconques de $C$ peuvent être joints par un segment qui
> est inclus dans $C$ et est majoré par $k$ dans $V$.
>
> 1° $l_V(M, N)\geqq 0$; $l_V(M, M)=0$; 2° Soit $g$ un automorphisme projectif de $V$, on a
> $l_V(gM, gN)=l_V(M, N)$; 3° Soit $(M, N)\subset(M', N')$, on a $l_V(M, N)\leqq l_V(M', N')$;
> 4° Soit $V'$ un ouvert de $V$ considéré comme variété localement projective, on a
> $l_V(M, N)\leqq l_{V'}(M, N)$ pour tout segment $(M, N)$ inclus dans $V'$; […]
> Les propriétés 1° et 2° résultent trivialement de la définition. Les propriétés 3° et 4°
> résultent de la proposition 1.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 2–4: `V` a locally projective manifold | ✓ `[ChartedSpace (S n) V]`, and `[HasGroupoid V (projGroupoid n)]` wherever a theorem uses it; definitions need no more |
| Déf. 2: `(A', B')` a segment of `V` (Déf. 14) | ✓ carried: `IsProjSegment n Sg' A' B'` is the first conjunct of `IsMajoreSeg` |
| Déf. 2: a segment `(A, B)` of `V` containing `(A', B')` | ✓ `IsProjSegment n Sg A B ∧ Sg' ⊆ Sg` |
| Déf. 2: « si φ est une carte compatible d'un voisinage de (A, B) sur un ouvert de S(n), on ait » | ✓ carried as printed: for EVERY compatible chart `φ` with `Sg ⊆ φ.source`; the existential reading is equivalent (`isMajoreSeg_iff_exists_chart`), so no reading is needed |
| Déf. 3: « borne inférieure des nombres k » | ✓ `⨅ k : ℝ` in `EReal` (`⊤` for an empty set); the set is nonempty for every segment when `n ≥ 1` (`pseudoLength_lt_top`) |
| Déf. 4: « joints par un segment inclus dans C et majoré par k » | ✓ |
| 1°: `l_V(M, M) = 0` | ⚠ `1 ≤ n` assumed (a question for the author, SCOPE « Dimension 0 »); `l_V ≥ 0` needs nothing |
| 2°: `g` a projective automorphism of `V` | ✓ `g : GXAut (GSR n) (S n) V` (Déf. 15) |
| 3°: `(M, N) ⊂ (M', N')` | ✓ `Sg ⊆ Sg'` with `(M, N)` a segment; `(M', N')` need not be assumed one |
| 4°: `V'` open, with its induced structure; `(M, N)` a segment included in `V'` | ✓ `W : TopologicalSpace.Opens V` with Mathlib's charted structure; for a segment of `W` (`pseudoLength_le_opens`) and for a segment of `V` included in `W` (`pseudoLength_le_opens'`) |

## SCOPE (disclosed)

* **The pseudo-length is a function of the segment `(Sg, M, N)`**, not of the pair of points: in
  a manifold two points may be joined by several segments, and Déf. 3 defines `l_V(M, N)` « d'un
  segment $(M, N)$ » (reported under `questions`). A segment with both endpoints `M` is `{M}`
  (`IsProjSegment.eq_singleton`).
* **Chart independence** (implicit in Déf. 2): two compatible charts of a neighbourhood of a
  segment differ by one element of `GS(n, ℝ)` on it (`exists_smul_eq_on_of_isPreconnected`, the
  segment being connected, `IsProjSegment.isPreconnected_seg`); every compatible chart maps the
  segment onto the segment of `S(n)` of its endpoints (`IsProjSegment.image_eq_closedSeg`).
* **1°–4° are lemmas, unmarked** (DEC-137, OQ-38(a)). The printed proof (« 1° et 2° résultent
  trivialement de la définition … 3° et 4° résultent de la proposition 1 ») is followed for 1°,
  2°, 3° (3° uses Prop. 1's first assertion, `projMeasure_le_inner`); 4° is proved directly, a
  segment majorised in `V'` being majorised in `V` with the same witness (`IsMajoreSeg.lift`).
  `l_V(M, M) = 0` needs a segment through `M` in a chart (`exists_closedSeg_subset`), hence
  `n ≥ 1`.
* **Dimension 0** (a question for the author, not a finding as such): 1° « l_V(M, M) = 0 » is
  not literally true for `n = 0`, because Déf. 1 assigns no measure to coincident points, and in
  dimension `0` that is the only configuration: `S(0)` has two diametrically opposite points
  (`S0_eq_or_eq_neg`), every segment is a point, its only majorising candidate is itself
  (`A = B`), and no `k` majorises `(M, M)`, so `l(M, M) = ⊤`. It holds for `n ≥ 1`
  (`pseudoLength_self`), and it would hold in every dimension if a point were given measure `0`.
  The paper never says `n ≥ 1` (Ch. 1 names `S(0)`). Three choices for the author: (a) `n ≥ 1` is
  implied; (b) a point has measure `0` (then 1° holds for every `n`); (c) a finding as printed.
  Prop. 3 (T-bz-c2-hilbert) inherits the same question: with the convention here, a point of a
  `0`-manifold has no majorised neighbourhood. `pseudoLength_self_eq_top_dim_zero` is stated on
  `V = S(0)`; the same proof works on every `V` charted on `S(0)`, a single point included.
* Tools for the later targets (T-bz-c2-hilbert, T-bz-c2-lignes): `isProjSegment_of_chart`,
  `isMajoreSeg_of_chart` (a segment majorised through one chart), `exists_closedSeg_extend` (a
  segment of `S(n)` in an open set extends beyond both endpoints), `IsMajoreSeg.mono`,
  `IsMajorePart.mono`, `pseudoLength_le`; and `IsCompatibleChart.trans_aut`, `.subtypeRestr`,
  `.lift_openEmbedding`, `Sphere.gse_image_closedSeg`, `Sphere.isPreconnected_closedSeg_of_ne_neg`,
  `Sphere.closedSeg_subset_closedSeg` (candidates to move upstream at graduation).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u

/-! ### Complements on `S(E)`: the action of `GS(E)` on segments, connectedness of segments -/

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem openSeg_subset_closedSeg (A B : Sphere E) : openSeg A B ⊆ closedSeg A B := by
  obtain ⟨a, ha⟩ := exists_isRep A
  obtain ⟨b, hb⟩ := exists_isRep B
  intro X hX
  obtain ⟨s, t, hs, ht, hX⟩ := (mem_openSeg_iff ha hb).1 hX
  exact (mem_closedSeg_iff ha hb).2 ⟨s, t, hs.le, ht.le, hX⟩

/-- **A closed segment contains the segment of any two of its points.** -/
theorem closedSeg_subset_closedSeg {A B A' B' : Sphere E} (hA' : A' ∈ closedSeg A B)
    (hB' : B' ∈ closedSeg A B) : closedSeg A' B' ⊆ closedSeg A B := by
  obtain ⟨a, ha⟩ := exists_isRep A
  obtain ⟨b, hb⟩ := exists_isRep B
  obtain ⟨s₁, t₁, hs₁, ht₁, h1⟩ := (mem_closedSeg_iff ha hb).1 hA'
  obtain ⟨s₂, t₂, hs₂, ht₂, h2⟩ := (mem_closedSeg_iff ha hb).1 hB'
  intro X hX
  obtain ⟨σ, τ, hσ, hτ, hX⟩ := (mem_closedSeg_iff h1 h2).1 hX
  refine (mem_closedSeg_iff ha hb).2
    ⟨σ * s₁ + τ * s₂, σ * t₁ + τ * t₂, by positivity, by positivity, ?_⟩
  convert hX using 1
  module

/-- Two points with independent representatives are distinct and not diametrically opposite. -/
theorem ne_of_linearIndependent {a b : E} {A B : Sphere E} (ha : IsRep a A) (hb : IsRep b B)
    (hab : LinearIndependent ℝ ![a, b]) : B ≠ A ∧ B ≠ -A :=
  ⟨fun h => not_linearIndependent_of_isRep ha (h ▸ hb) hab,
    fun h => not_linearIndependent_of_isRep_neg ha (h ▸ hb) hab⟩

theorem linearEquiv_image_closedSeg_subset (f : E ≃ₗ[ℝ] E) (A B : Sphere E) :
    (f • ·) '' closedSeg A B ⊆ closedSeg (f • A) (f • B) := by
  obtain ⟨a, ha⟩ := exists_isRep A
  obtain ⟨b, hb⟩ := exists_isRep B
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨s, t, hs, ht, hX⟩ := (mem_closedSeg_iff ha hb).1 hX
  refine (mem_closedSeg_iff (ha.linearEquiv f) (hb.linearEquiv f)).2 ⟨s, t, hs, ht, ?_⟩
  have := hX.linearEquiv f
  rwa [map_add, map_smul, map_smul] at this

theorem gse_image_closedSeg_subset (g : GSE E) (A B : Sphere E) :
    (g • ·) '' closedSeg A B ⊆ closedSeg (g • A) (g • B) := by
  induction g using QuotientGroup.induction_on with
  | H f => simpa only [GSE.mk_smul] using linearEquiv_image_closedSeg_subset f A B

/-- **`GS(E)` maps segments onto segments**: `g (A, B) = (gA, gB)`. -/
theorem gse_image_closedSeg (g : GSE E) (A B : Sphere E) :
    (g • ·) '' closedSeg A B = closedSeg (g • A) (g • B) := by
  refine Subset.antisymm (gse_image_closedSeg_subset g A B) fun X hX => ?_
  refine ⟨g⁻¹ • X, ?_, smul_inv_smul g X⟩
  have := gse_image_closedSeg_subset g⁻¹ (g • A) (g • B) ⟨X, hX, rfl⟩
  rwa [inv_smul_smul, inv_smul_smul] at this

theorem gse_smul_neg (g : GSE E) (x : Sphere E) : g • (-x) = -(g • x) := by
  induction g using QuotientGroup.induction_on with
  | H f => simp only [GSE.mk_smul, smul_eq_mapEquiv, mapEquiv_neg]

/-- **A segment of `S(E)` is connected** (its endpoints not diametrically opposite). -/
theorem isPreconnected_closedSeg_of_ne_neg [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {A B : Sphere E} (h : B ≠ -A) : IsPreconnected (closedSeg A B) := by
  obtain ⟨v, hv, rfl⟩ := exists_isRep A
  obtain ⟨w, hw, rfl⟩ := exists_isRep B
  have h0 : (0 : E) ∉ segment ℝ v w := zero_notMem_segment hv hw h
  rw [closedSeg_mk, segOf, ofCone]
  refine IsPreconnected.image ?_ _ continuous_s.continuousOn
  have him : (Subtype.val : {v : E // v ≠ 0} → E) '' (Subtype.val ⁻¹' segment ℝ v w) =
      segment ℝ v w := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, fun h' => h0 (h' ▸ hx)⟩, hx, rfl⟩
  have hpc : IsPreconnected (segment ℝ v w) := (convex_segment v w).isPreconnected
  rw [← him] at hpc
  exact Topology.IsInducing.subtypeVal.isPreconnected_image.1 hpc

end Sphere

/-! ### Charts and segments of a locally projective manifold -/

section Charts

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

/-- A segment of `V` is connected. -/
theorem IsProjSegment.isPreconnected_seg {Sg : Set V} {A B : V} (h : IsProjSegment n Sg A B) :
    IsPreconnected Sg := by
  obtain ⟨φ, -, hS, -, -, hadm, himg⟩ := h
  have hT : φ '' Sg ⊆ φ.target := image_subset_iff.2 fun x hx => φ.map_source (hS hx)
  rw [← φ.symm_image_image_of_subset_source hS]
  refine IsPreconnected.image ?_ _ (φ.continuousOn_symm.mono hT)
  have h2 : IsPreconnected (φ '' Sg) := himg ▸ Sphere.isPreconnected_closedSeg_of_ne_neg hadm
  exact h2

/-- **A segment of `S(n)` inside the target of a compatible chart is the image of a segment of
`V`.** -/
theorem isProjSegment_of_chart {φ : OpenPartialHomeomorph V (S n)}
    (hφ : IsCompatibleChart (GSR n) φ) {a b : S n} (hab : b ≠ -a)
    (hsub : Sphere.closedSeg a b ⊆ φ.target) :
    IsProjSegment n (φ.symm '' Sphere.closedSeg a b) (φ.symm a) (φ.symm b) := by
  have ha := hsub (Sphere.left_mem_closedSeg a b)
  have hb := hsub (Sphere.right_mem_closedSeg a b)
  refine ⟨φ, hφ, ?_, φ.map_target ha, φ.map_target hb, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact φ.map_target (hsub hy)
  · rw [φ.right_inv ha, φ.right_inv hb]
    exact hab
  · rw [φ.right_inv ha, φ.right_inv hb]
    exact φ.image_symm_image_of_subset_target hsub

/-- The only segment with endpoints `M`, `M` is `{M}`. -/
theorem IsProjSegment.eq_singleton {Sg : Set V} {M : V} (h : IsProjSegment n Sg M M) :
    Sg = {M} := by
  have hM := h.left_mem
  obtain ⟨φ, -, hS, -, -, -, himg⟩ := h
  rw [Sphere.closedSeg_self] at himg
  refine Subset.antisymm (fun x hx => ?_) (singleton_subset_iff.2 hM)
  have : φ x ∈ ({φ M} : Set (S n)) := himg ▸ mem_image_of_mem φ hx
  exact φ.injOn (hS hx) (hS hM) this

variable [HasGroupoid V (projGroupoid n)]

/-- **Two compatible charts differ by one element of `GS(n, ℝ)` on a connected set** in both
sources (Ch. 1, Prop. 1, through `exists_smul_eq_on_connectedComponentIn`). -/
theorem exists_smul_eq_on_of_isPreconnected {φ ψ : OpenPartialHomeomorph V (S n)}
    (hφ : IsCompatibleChart (GSR n) φ) (hψ : IsCompatibleChart (GSR n) ψ) {C : Set V}
    (hC : IsPreconnected C) (hne : C.Nonempty) (hCφ : C ⊆ φ.source) (hCψ : C ⊆ ψ.source) :
    ∃ g : GSR n, ∀ y ∈ C, ψ y = g • φ y := by
  rw [isCompatibleChart_iff] at hφ hψ
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, hg⟩ := exists_smul_eq_on_connectedComponentIn
    ((gxGroupoid _ _).compatible_of_mem_maximalAtlas hφ hψ) ⟨hCφ hx, hCψ hx⟩
  exact ⟨g, fun y hy => hg y (hC.subset_connectedComponentIn hx (subset_inter hCφ hCψ) hy)⟩

/-- **Every compatible chart defined on a segment maps it onto the segment of its endpoints**
(the chart of Déf. 14 is any compatible chart). -/
theorem IsProjSegment.image_eq_closedSeg {Sg : Set V} {A B : V} (h : IsProjSegment n Sg A B)
    {ψ : OpenPartialHomeomorph V (S n)} (hψ : IsCompatibleChart (GSR n) ψ) (hS : Sg ⊆ ψ.source) :
    ψ '' Sg = Sphere.closedSeg (ψ A) (ψ B) ∧ ψ B ≠ -ψ A := by
  have hA := h.left_mem
  have hB := h.right_mem
  have hc := h.isPreconnected_seg
  obtain ⟨φ, hφ, hSφ, -, -, hadm, himg⟩ := h
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected hφ hψ hc ⟨A, hA⟩ hSφ hS
  refine ⟨?_, ?_⟩
  · rw [hg A hA, hg B hB, ← Sphere.gse_image_closedSeg, ← himg, image_image]
    exact image_congr fun y hy => hg y hy
  · rw [hg A hA, hg B hB, ← Sphere.gse_smul_neg]
    exact fun h' => hadm (smul_left_cancel g h')

/-- A segment with endpoints `M`, `M` exists: `{M}`. -/
theorem isProjSegment_singleton (M : V) : IsProjSegment n {M} M M :=
  ⟨chartAt (S n) M, isCompatibleChart_iff.2 ((gxGroupoid _ _).chart_mem_maximalAtlas M),
    singleton_subset_iff.2 (mem_chart_source _ M), mem_chart_source _ M, mem_chart_source _ M,
    Module.Ray.ne_neg_self _, by rw [image_singleton, Sphere.closedSeg_self]⟩

/-- A compatible chart composed with an automorphism of `V` is compatible. -/
theorem IsCompatibleChart.trans_aut {φ : OpenPartialHomeomorph V (S n)}
    (hφ : IsCompatibleChart (GSR n) φ) (g : GXAut (GSR n) (S n) V) :
    IsCompatibleChart (GSR n) (g.toHomeomorph.toOpenPartialHomeomorph.trans φ) := by
  rw [isCompatibleChart_iff] at hφ ⊢
  rw [mem_maximalAtlas_iff_eventually]
  intro x hx
  have hx' : g • x ∈ φ.source := by simpa [GXAut.smul_def] using hx
  obtain ⟨h, hh⟩ := g.isGXMorphism.exists_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid _ _).chart_mem_maximalAtlas x) hφ (mem_chart_source _ x) hx'
  exact ⟨h, by simpa [GXAut.smul_def] using hh⟩

/-- The restriction of a compatible chart to an open subset is compatible. -/
theorem IsCompatibleChart.subtypeRestr {W : TopologicalSpace.Opens V} (hW : Nonempty W)
    {ψ : OpenPartialHomeomorph V (S n)} (hψ : IsCompatibleChart (GSR n) ψ) :
    IsCompatibleChart (GSR n) (ψ.subtypeRestr hW) := by
  rw [isCompatibleChart_iff] at hψ ⊢
  rw [mem_maximalAtlas_iff_eventually] at hψ ⊢
  intro x hx
  rw [OpenPartialHomeomorph.subtypeRestr_source] at hx
  obtain ⟨g, hg⟩ := hψ x.1 hx
  refine ⟨g, ?_⟩
  filter_upwards [(continuous_subtype_val.tendsto x).eventually hg] with z hz
  rw [TopologicalSpace.Opens.chartAt_eq]
  exact hz

/-- A compatible chart of an open subset, extended to `V`, is compatible. -/
theorem IsCompatibleChart.lift_openEmbedding {W : TopologicalSpace.Opens V}
    {φ : OpenPartialHomeomorph W (S n)} (hφ : IsCompatibleChart (GSR n) φ) :
    IsCompatibleChart (GSR n) (φ.lift_openEmbedding W.isOpen.isOpenEmbedding_subtypeVal) := by
  rw [isCompatibleChart_iff] at hφ ⊢
  rw [mem_maximalAtlas_iff_eventually] at hφ ⊢
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg⟩ := hφ x hx
  refine ⟨g, ?_⟩
  rw [← W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x, Filter.eventually_map]
  filter_upwards [hg] with z hz
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply, hz, TopologicalSpace.Opens.chartAt_eq]
  rfl

end Charts

/-! ### Déf. 2–4 -/

section Defs

variable {V : Type u} [TopologicalSpace V]

/-- **Déf. 2, a segment majorised by `k` in `V`** (`bzdef:c2s2d2_segment_majore`): `(Sg', A', B')`
is a segment of `V` (Déf. 14) and there is a segment `(Sg, A, B)` of `V` containing it such that,
for **every** compatible chart `φ` defined on a neighbourhood of `Sg`, the projective measure of
`φ(A', B')` relative to `φ(A, B)` is `< k` (« si $\varphi$ est une carte compatible … on ait »).
One chart suffices: `isMajoreSeg_iff_exists_chart`. -/
def IsMajoreSeg (n : ℕ) [ChartedSpace (S n) V] (k : ℝ) (Sg' : Set V) (A' B' : V) : Prop :=
  IsProjSegment n Sg' A' B' ∧ ∃ (Sg : Set V) (A B : V), IsProjSegment n Sg A B ∧ Sg' ⊆ Sg ∧
    ∀ φ : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ → Sg ⊆ φ.source →
      Sphere.projMeasure (φ A) (φ A') (φ B') (φ B) < k

/-- **Déf. 3, the pseudo-length `l_V(M, N)`** (`bzdef:c2s2d3_pseudo_longueur`) of a segment
`(Sg, M, N)` of `V`: the infimum, in `EReal`, of the real numbers `k` which majorise it in `V`. -/
def pseudoLength (n : ℕ) [ChartedSpace (S n) V] (Sg : Set V) (M N : V) : EReal :=
  ⨅ (k : ℝ) (_ : IsMajoreSeg n k Sg M N), (k : EReal)

/-- **Déf. 4, a part majorised by `k` in `V`** (`bzdef:c2s2d4_partie_majoree`): any two points of
`C` are joined by a segment included in `C` and majorised by `k` in `V`. -/
def IsMajorePart (n : ℕ) [ChartedSpace (S n) V] (k : ℝ) (C : Set V) : Prop :=
  ∀ M ∈ C, ∀ N ∈ C, ∃ Sg : Set V, Sg ⊆ C ∧ IsMajoreSeg n k Sg M N

end Defs

/-! ### Elementary facts -/

section Basic

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

theorem IsMajoreSeg.isProjSegment {k : ℝ} {Sg : Set V} {M N : V} (h : IsMajoreSeg n k Sg M N) :
    IsProjSegment n Sg M N :=
  h.1

theorem IsMajoreSeg.mono {k k' : ℝ} {Sg : Set V} {M N : V} (h : IsMajoreSeg n k Sg M N)
    (hk : k ≤ k') : IsMajoreSeg n k' Sg M N := by
  obtain ⟨h', Sg₁, A, B, h₁, hsub, hall⟩ := h
  exact ⟨h', Sg₁, A, B, h₁, hsub, fun φ hφ hS =>
    (hall φ hφ hS).trans_le (EReal.coe_le_coe_iff.2 hk)⟩

theorem IsMajorePart.mono {k k' : ℝ} {C : Set V} (h : IsMajorePart n k C) (hk : k ≤ k') :
    IsMajorePart n k' C := fun M hM N hN => by
  obtain ⟨Sg, hSg, hmaj⟩ := h M hM N hN
  exact ⟨Sg, hSg, hmaj.mono hk⟩

theorem pseudoLength_le {k : ℝ} {Sg : Set V} {M N : V} (h : IsMajoreSeg n k Sg M N) :
    pseudoLength n Sg M N ≤ k :=
  iInf₂_le k h

/-- **1°, first half: `l_V(M, N) ≥ 0`.** -/
theorem pseudoLength_nonneg (Sg : Set V) (M N : V) : 0 ≤ pseudoLength n Sg M N := by
  refine le_iInf₂ fun k hk => ?_
  obtain ⟨-, Sg₁, A, B, ⟨φ, hφ, hS, -⟩, -, hall⟩ := hk
  exact (Sphere.projMeasure_nonneg _ _ _ _).trans (hall φ hφ hS).le

end Basic

/-! ### Chart independence (Déf. 2) and 1°–4° -/

section Props

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]

/-- **Déf. 2 does not depend on the chart**: one compatible chart of a neighbourhood of `(A, B)`
suffices (the measure is `GS(n, ℝ)`-invariant and two compatible charts differ by an element of
`GS(n, ℝ)` on the connected set `(A, B)`). -/
theorem isMajoreSeg_iff_exists_chart {k : ℝ} {Sg' : Set V} {A' B' : V} :
    IsMajoreSeg n k Sg' A' B' ↔ IsProjSegment n Sg' A' B' ∧ ∃ (Sg : Set V) (A B : V),
      IsProjSegment n Sg A B ∧ Sg' ⊆ Sg ∧ ∃ φ : OpenPartialHomeomorph V (S n),
        IsCompatibleChart (GSR n) φ ∧ Sg ⊆ φ.source ∧
        Sphere.projMeasure (φ A) (φ A') (φ B') (φ B) < k := by
  constructor
  · rintro ⟨h', Sg, A, B, h, hsub, hall⟩
    obtain ⟨φ, hφ, hS, -⟩ := id h
    exact ⟨h', Sg, A, B, h, hsub, φ, hφ, hS, hall φ hφ hS⟩
  · rintro ⟨h', Sg, A, B, h, hsub, φ, hφ, hS, hlt⟩
    refine ⟨h', Sg, A, B, h, hsub, fun ψ hψ hSψ => ?_⟩
    obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected hφ hψ h.isPreconnected_seg
      ⟨A, h.left_mem⟩ hS hSψ
    rwa [hg A h.left_mem, hg B h.right_mem, hg A' (hsub h'.left_mem), hg B' (hsub h'.right_mem),
      Sphere.projMeasure_smul]

/-- **A majorised segment from a chart**: if `(a', b') ⊆ (a, b) ⊆ φ(target)` for a compatible
chart `φ` and the projective measure of `a'b'` relative to `ab` is `< k`, then the segment
`φ⁻¹(a', b')` of `V` is majorised by `k`. -/
theorem isMajoreSeg_of_chart {φ : OpenPartialHomeomorph V (S n)}
    (hφ : IsCompatibleChart (GSR n) φ) {a b a' b' : S n} (hab : b ≠ -a)
    (hsub : Sphere.closedSeg a b ⊆ φ.target) (ha' : a' ∈ Sphere.closedSeg a b)
    (hb' : b' ∈ Sphere.closedSeg a b) (hab' : b' ≠ -a') {k : ℝ}
    (hk : Sphere.projMeasure a a' b' b < k) :
    IsMajoreSeg n k (φ.symm '' Sphere.closedSeg a' b') (φ.symm a') (φ.symm b') := by
  have hsub' := Sphere.closedSeg_subset_closedSeg ha' hb'
  have hsrc : φ.symm '' Sphere.closedSeg a b ⊆ φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact φ.map_target (hsub hy)
  refine isMajoreSeg_iff_exists_chart.2 ⟨isProjSegment_of_chart hφ hab' (hsub'.trans hsub), _, _,
    _, isProjSegment_of_chart hφ hab hsub, image_mono hsub', φ, hφ, hsrc, ?_⟩
  rwa [φ.right_inv (hsub (Sphere.left_mem_closedSeg a b)), φ.right_inv (hsub ha'),
    φ.right_inv (hsub hb'), φ.right_inv (hsub (Sphere.right_mem_closedSeg a b))]

/-- **A segment of `S(n)` in an open set extends beyond both endpoints inside the open set.** -/
theorem exists_closedSeg_extend {U : Set (S n)} (hU : IsOpen U) {m₁ m₂ : S n} (h12 : m₂ ≠ m₁)
    (h12' : m₂ ≠ -m₁) (hsub : Sphere.closedSeg m₁ m₂ ⊆ U) :
    ∃ a b : S n, b ≠ a ∧ b ≠ -a ∧ m₁ ∈ Sphere.openSeg a b ∧ m₂ ∈ Sphere.openSeg a b ∧
      Sphere.closedSeg a b ⊆ U := by
  obtain ⟨v₁, hv₁⟩ := Sphere.exists_isRep m₁
  obtain ⟨v₂, hv₂⟩ := Sphere.exists_isRep m₂
  have hli := Sphere.linearIndependent_of_ne hv₁ hv₂ h12 h12'
  let f : ℝ × ℝ → (Fin (n + 1) → ℝ) := fun p =>
    ((1 - p.2) * (1 + p.1) - p.2 * p.1) • v₁ + (p.2 * (1 + p.1) - (1 - p.2) * p.1) • v₂
  have hf0 : ∀ p, f p ≠ 0 := fun p h => by
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hli _ _ h
    have e : ((1 - p.2) * (1 + p.1) - p.2 * p.1) + (p.2 * (1 + p.1) - (1 - p.2) * p.1) = 1 := by
      ring
    rw [h1, h2] at e
    norm_num at e
  let F : ℝ × ℝ → S n := fun p => Sphere.mk (f p) (hf0 p)
  have hF : Continuous F := Sphere.continuous_mk_comp (by fun_prop) hf0
  have hK : ({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆ F ⁻¹' U := by
    rintro ⟨e, t⟩ ⟨he, ht⟩
    rw [mem_singleton_iff] at he
    subst he
    apply hsub
    refine (Sphere.mem_closedSeg_iff hv₁ hv₂).2 ⟨1 - t, t, by linarith [ht.2], ht.1, ?_⟩
    convert Sphere.isRep_mk _ (hf0 (0, t)) using 1
    simp only [f]
    module
  obtain ⟨u, w, hu, -, h0u, htw, huw⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc (hU.preimage hF) hK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu 0 (h0u rfl)
  have hδ : 0 < ε / 2 := half_pos hε
  have hδu : ε / 2 ∈ u := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ]
    linarith
  set δ := ε / 2
  have hA := Sphere.isRep_mk _ (hf0 (δ, 0))
  have hB := Sphere.isRep_mk _ (hf0 (δ, 1))
  have hliAB : LinearIndependent ℝ ![f (δ, 0), f (δ, 1)] := by
    refine LinearIndependent.pair_iff.2 fun x y hxy => ?_
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hli (x * (1 + δ) - y * δ) (y * (1 + δ) - x * δ)
      (by rw [← hxy]; simp only [f]; module)
    have hxy0 : x + y = 0 := by linear_combination h1 + h2
    have hx : x * (1 + 2 * δ) = 0 := by linear_combination h1 + δ * hxy0
    have hx0 : x = 0 := (mul_eq_zero.1 hx).resolve_right (by linarith)
    exact ⟨hx0, by linarith⟩
  obtain ⟨hBA, hBA'⟩ := Sphere.ne_of_linearIndependent hA hB hliAB
  refine ⟨F (δ, 0), F (δ, 1), hBA, hBA', ?_, ?_, ?_⟩
  · refine (Sphere.mem_openSeg_iff hA hB).2 ⟨1 + δ, δ, by linarith, hδ, ?_⟩
    convert hv₁.smul (c := 1 + 2 * δ) (by linarith) using 1
    simp only [f]
    module
  · refine (Sphere.mem_openSeg_iff hA hB).2 ⟨δ, 1 + δ, hδ, by linarith, ?_⟩
    convert hv₂.smul (c := 1 + 2 * δ) (by linarith) using 1
    simp only [f]
    module
  · intro X hX
    obtain ⟨s, t, hs, ht, hX⟩ := (Sphere.mem_closedSeg_iff hA hB).1 hX
    have hst : 0 < s + t := by
      rcases (add_nonneg hs ht).lt_or_eq with h | h
      · exact h
      · exfalso
        have e1 : s = 0 := by linarith
        have e2 : t = 0 := by linarith
        subst e1 e2
        exact hX.ne_zero (by simp)
    have hX' := hX.smul (inv_pos.2 hst)
    have heq : (s + t)⁻¹ • (s • f (δ, 0) + t • f (δ, 1)) = f (δ, t / (s + t)) := by
      simp only [f]
      match_scalars <;> field_simp <;> ring
    rw [heq] at hX'
    rw [hX'.eq (Sphere.isRep_mk _ (hf0 (δ, t / (s + t))))]
    exact huw ⟨hδu, htw ⟨by positivity, (div_le_one hst).2 (by linarith)⟩⟩

/-- In `S(n)`, `n ≥ 1`, every point `m` of an open set `U` is interior to a segment `(a, b) ⊆ U`,
`a ≠ b` not diametrically opposite. -/
theorem exists_closedSeg_subset (hn : 1 ≤ n) {U : Set (S n)} (hU : IsOpen U) {m : S n}
    (hm : m ∈ U) : ∃ a b : S n, b ≠ a ∧ b ≠ -a ∧ m ∈ Sphere.openSeg a b ∧
      Sphere.closedSeg a b ⊆ U := by
  obtain ⟨v, hv, rfl⟩ := Sphere.exists_isRep m
  have hrank : 1 < Module.finrank ℝ (Fin (n + 1) → ℝ) := by simp; omega
  obtain ⟨w, hvw⟩ := exists_linearIndependent_pair_of_one_lt_finrank hrank hv
  have hne : ∀ t : ℝ, v + t • w ≠ 0 := fun t h => one_ne_zero
    (LinearIndependent.pair_iff.1 hvw 1 t (by rw [one_smul]; exact h)).1
  let c : ℝ → S n := fun t => Sphere.mk (v + t • w) (hne t)
  have hc : Continuous c := Sphere.continuous_mk_comp (by fun_prop) hne
  have hc0 : c 0 = Sphere.mk v hv := by simp only [c, zero_smul, add_zero]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hc) 0
    (by rw [mem_preimage, hc0]; exact hm)
  have hδ : 0 < ε / 2 := half_pos hε
  have hli : LinearIndependent ℝ ![v + (-(ε / 2)) • w, v + (ε / 2) • w] := by
    refine LinearIndependent.pair_iff.2 fun x y hxy => ?_
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 hvw (x + y) ((y - x) * (ε / 2))
      (by rw [← hxy]; module)
    have hyx : y - x = 0 := (mul_eq_zero.1 h2).resolve_right hδ.ne'
    exact ⟨by linarith, by linarith⟩
  have hA := Sphere.isRep_mk _ (hne (-(ε / 2)))
  have hB := Sphere.isRep_mk _ (hne (ε / 2))
  obtain ⟨hBA, hBA'⟩ := Sphere.ne_of_linearIndependent hA hB hli
  refine ⟨c (-(ε / 2)), c (ε / 2), hBA, hBA', ?_, ?_⟩
  · refine (Sphere.mem_openSeg_iff hA hB).2 ⟨1 / 2, 1 / 2, by norm_num, by norm_num, ?_⟩
    convert Sphere.isRep_mk v hv using 1
    module
  · intro X hX
    obtain ⟨s, t, hs, ht, hX⟩ := (Sphere.mem_closedSeg_iff hA hB).1 hX
    have hst : 0 < s + t := by
      rcases (add_nonneg hs ht).lt_or_eq with h | h
      · exact h
      · exfalso
        have e1 : s = 0 := by linarith
        have e2 : t = 0 := by linarith
        subst e1 e2
        exact hX.ne_zero (by simp)
    have hX' := hX.smul (inv_pos.2 hst)
    have heq : (s + t)⁻¹ • (s • (v + (-(ε / 2)) • w) + t • (v + (ε / 2) • w)) =
        v + ((t - s) / (s + t) * (ε / 2)) • w := by
      match_scalars <;> field_simp
      ring
    rw [heq] at hX'
    have hXc : X = c ((t - s) / (s + t) * (ε / 2)) := hX'.eq (Sphere.isRep_mk _ _)
    rw [hXc]
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_mul, abs_of_pos hδ]
    have : |(t - s) / (s + t)| ≤ 1 := by
      rw [abs_div, abs_of_pos hst, div_le_one hst, abs_le]
      constructor <;> linarith
    nlinarith [abs_nonneg ((t - s) / (s + t))]

/-- **The point segment `(M, M)` is majorised by every `k > 0`** (`n ≥ 1`). -/
theorem isMajoreSeg_singleton (hn : 1 ≤ n) (M : V) {k : ℝ} (hk : 0 < k) :
    IsMajoreSeg n k {M} M M := by
  set φ := chartAt (S n) M
  have hφ : IsCompatibleChart (GSR n) φ :=
    isCompatibleChart_iff.2 ((gxGroupoid _ _).chart_mem_maximalAtlas M)
  have hMs : M ∈ φ.source := mem_chart_source _ M
  obtain ⟨a, b, hba, hba', hm, hsub⟩ :=
    exists_closedSeg_subset hn φ.open_target (φ.map_source hMs)
  have ha := hsub (Sphere.left_mem_closedSeg a b)
  have hb := hsub (Sphere.right_mem_closedSeg a b)
  have hsrc : φ.symm '' Sphere.closedSeg a b ⊆ φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact φ.map_target (hsub hy)
  have hseg : IsProjSegment n (φ.symm '' Sphere.closedSeg a b) (φ.symm a) (φ.symm b) := by
    refine ⟨φ, hφ, hsrc, φ.map_target ha, φ.map_target hb, ?_, ?_⟩
    · rw [φ.right_inv ha, φ.right_inv hb]
      exact hba'
    · rw [φ.right_inv ha, φ.right_inv hb]
      exact φ.image_symm_image_of_subset_target hsub
  refine ⟨isProjSegment_singleton M, _, _, _, hseg, singleton_subset_iff.2
    ⟨φ M, Sphere.openSeg_subset_closedSeg a b hm, φ.left_inv hMs⟩, fun ψ hψ hS => ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected hφ hψ hseg.isPreconnected_seg
    ⟨_, hseg.left_mem⟩ hsrc hS
  have hM' : M ∈ φ.symm '' Sphere.closedSeg a b :=
    ⟨φ M, Sphere.openSeg_subset_closedSeg a b hm, φ.left_inv hMs⟩
  rw [hg _ hseg.left_mem, hg _ hM', hg _ hseg.right_mem, Sphere.projMeasure_smul,
    φ.right_inv ha, φ.right_inv hb, Sphere.projMeasure_self hba hba' hm]
  exact EReal.coe_pos.2 hk

/-- **Déf. 4 is inhabited**: a point is a part majorised by every `k > 0` (`n ≥ 1`). -/
theorem isMajorePart_singleton (hn : 1 ≤ n) (M : V) {k : ℝ} (hk : 0 < k) :
    IsMajorePart n k {M} := by
  intro x hx y hy
  rw [mem_singleton_iff] at hx hy
  rw [hx, hy]
  exact ⟨{M}, subset_rfl, isMajoreSeg_singleton hn M hk⟩

/-- **1°, second half: `l_V(M, M) = 0`** (for `n ≥ 1`; for `n = 0` the literal value is `⊤`,
`pseudoLength_self_eq_top_dim_zero`, a question for the author, see SCOPE). -/
theorem pseudoLength_self (hn : 1 ≤ n) {Sg : Set V} {M : V} (h : IsProjSegment n Sg M M) :
    pseudoLength n Sg M M = 0 := by
  refine le_antisymm ?_ (pseudoLength_nonneg Sg M M)
  have hSg := h.eq_singleton
  subst hSg
  have hmaj : ∀ k : ℝ, 0 < k → IsMajoreSeg n k {M} M M := fun k hk =>
    isMajoreSeg_singleton hn M hk
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  induction c using EReal.rec with
  | bot => exact absurd hc not_lt_bot
  | coe k => exact pseudoLength_le (hmaj k (EReal.coe_pos.1 hc))
  | top => exact le_top

/-- **The pseudo-length of a segment is finite** (`n ≥ 1`): the infimum of Déf. 3 is over a
nonempty set of real numbers. -/
theorem pseudoLength_lt_top (hn : 1 ≤ n) {Sg : Set V} {M N : V} (h : IsProjSegment n Sg M N) :
    pseudoLength n Sg M N < ⊤ := by
  by_cases hMN : M = N
  · subst hMN
    rw [pseudoLength_self hn h]
    exact EReal.zero_lt_top
  obtain ⟨φ, hφ, hS, hM, hN, hadm, himg⟩ := id h
  have hne : φ N ≠ φ M := fun e => hMN (φ.injOn hM hN e.symm)
  have hT : Sphere.closedSeg (φ M) (φ N) ⊆ φ.target :=
    himg ▸ image_subset_iff.2 fun x hx => φ.map_source (hS hx)
  obtain ⟨a, b, hba, hba', hma, hmb, hsub⟩ := exists_closedSeg_extend φ.open_target hne hadm hT
  have hfin : Sphere.projMeasure a (φ M) (φ N) b < ⊤ :=
    Sphere.projMeasure_lt_top_iff.2 (Sphere.exists_isCrossRatio hba hba' hma hmb)
  obtain ⟨k, hk, -⟩ := EReal.lt_iff_exists_real_btwn.1 hfin
  have hmaj := isMajoreSeg_of_chart hφ hba' hsub (Sphere.openSeg_subset_closedSeg a b hma)
    (Sphere.openSeg_subset_closedSeg a b hmb) hadm hk
  have hSg : φ.symm '' Sphere.closedSeg (φ M) (φ N) = Sg := by
    rw [← himg]
    exact φ.symm_image_image_of_subset_source hS
  rw [hSg, φ.left_inv hM, φ.left_inv hN] at hmaj
  exact (pseudoLength_le hmaj).trans_lt (EReal.coe_lt_top k)

/-- An automorphism maps segments onto segments. -/
theorem IsProjSegment.smul (g : GXAut (GSR n) (S n) V) {Sg : Set V} {A B : V}
    (h : IsProjSegment n Sg A B) : IsProjSegment n ((g • ·) '' Sg) (g • A) (g • B) := by
  obtain ⟨φ, hφ, hS, hA, hB, hadm, himg⟩ := h
  have hval : ∀ x, (g⁻¹.toHomeomorph.toOpenPartialHomeomorph.trans φ) (g • x) = φ x := by
    intro x
    simp [GXAut.smul_def]
  have hsrc : ∀ x, x ∈ φ.source → g • x ∈ (g⁻¹.toHomeomorph.toOpenPartialHomeomorph.trans φ).source := by
    intro x hx
    simpa [GXAut.smul_def] using hx
  refine ⟨_, hφ.trans_aut g⁻¹, ?_, hsrc A hA, hsrc B hB, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hsrc x (hS hx)
  · rwa [hval, hval]
  · rw [hval, hval, image_image]
    simp only [hval]
    exact himg

/-- An automorphism maps majorised segments onto majorised segments. -/
theorem IsMajoreSeg.smul (g : GXAut (GSR n) (S n) V) {k : ℝ} {Sg : Set V} {M N : V}
    (h : IsMajoreSeg n k Sg M N) : IsMajoreSeg n k ((g • ·) '' Sg) (g • M) (g • N) := by
  obtain ⟨hseg, Sg₁, A, B, hseg₁, hsub, hall⟩ := h
  refine ⟨hseg.smul g, (g • ·) '' Sg₁, g • A, g • B, hseg₁.smul g, image_mono hsub,
    fun ψ hψ hS => ?_⟩
  have := hall _ (hψ.trans_aut g) fun x hx => by
    simpa [GXAut.smul_def] using hS ⟨x, hx, rfl⟩
  simpa [GXAut.smul_def] using this

/-- **2°: `l_V(gM, gN) = l_V(M, N)`** for every projective automorphism `g` of `V`. -/
theorem pseudoLength_smul (g : GXAut (GSR n) (S n) V) (Sg : Set V) (M N : V) :
    pseudoLength n ((g • ·) '' Sg) (g • M) (g • N) = pseudoLength n Sg M N := by
  refine le_antisymm (le_iInf₂ fun k hk => pseudoLength_le (hk.smul g))
    (le_iInf₂ fun k hk => pseudoLength_le ?_)
  have := hk.smul g⁻¹
  simp only [image_image, inv_smul_smul, image_id'] at this
  exact this

/-- A majorised segment majorises every segment it contains. -/
theorem IsMajoreSeg.of_subset {k : ℝ} {Sg Sg' : Set V} {M N M' N' : V}
    (h' : IsMajoreSeg n k Sg' M' N') (hSg : Sg ⊆ Sg') (h : IsProjSegment n Sg M N) :
    IsMajoreSeg n k Sg M N := by
  obtain ⟨hseg', Sg₁, A, B, hseg₁, hsub, hall⟩ := h'
  refine ⟨h, Sg₁, A, B, hseg₁, hSg.trans hsub, fun ψ hψ hS => ?_⟩
  have himg := (hseg'.image_eq_closedSeg hψ (hsub.trans hS)).1
  have hM : ψ M ∈ Sphere.closedSeg (ψ M') (ψ N') := himg ▸ mem_image_of_mem ψ (hSg h.left_mem)
  have hN : ψ N ∈ Sphere.closedSeg (ψ M') (ψ N') := himg ▸ mem_image_of_mem ψ (hSg h.right_mem)
  exact (Sphere.projMeasure_le_inner hM hN).trans_lt (hall ψ hψ hS)

/-- **3°: `(M, N) ⊂ (M', N')` implies `l_V(M, N) ≤ l_V(M', N')`.** -/
theorem pseudoLength_mono {Sg Sg' : Set V} {M N M' N' : V} (hSg : Sg ⊆ Sg')
    (h : IsProjSegment n Sg M N) : pseudoLength n Sg M N ≤ pseudoLength n Sg' M' N' :=
  le_iInf₂ fun _ hk => pseudoLength_le (hk.of_subset hSg h)

/-- A segment of an open subset is a segment of `V`. -/
theorem IsProjSegment.lift {W : TopologicalSpace.Opens V} {Sg : Set W} {A B : W}
    (h : IsProjSegment n Sg A B) : IsProjSegment n (Subtype.val '' Sg) (A : V) B := by
  obtain ⟨φ, hφ, hS, hA, hB, hadm, himg⟩ := h
  have hval : ∀ x : W, (φ.lift_openEmbedding W.isOpen.isOpenEmbedding_subtypeVal) x = φ x :=
    fun x => φ.lift_openEmbedding_apply _
  refine ⟨_, hφ.lift_openEmbedding, image_mono hS, ⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩, ?_, ?_⟩
  · rwa [hval, hval]
  · rw [hval, hval, image_image]
    simp only [hval]
    exact himg

/-- A segment majorised in an open subset is majorised in `V`. -/
theorem IsMajoreSeg.lift {W : TopologicalSpace.Opens V} {k : ℝ} {Sg : Set W} {M N : W}
    (h : IsMajoreSeg n k Sg M N) : IsMajoreSeg n k (Subtype.val '' Sg) (M : V) N := by
  obtain ⟨hseg, Sg₁, A, B, hseg₁, hsub, hall⟩ := h
  refine ⟨hseg.lift, Subtype.val '' Sg₁, A, B, hseg₁.lift, image_mono hsub, fun ψ hψ hS => ?_⟩
  have hW : Nonempty W := ⟨A⟩
  have := hall (ψ.subtypeRestr hW) (hψ.subtypeRestr hW) fun x hx => by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hS ⟨x, hx, rfl⟩
  simpa using this

/-- **4°: for an open `V' ⊆ V` and a segment `(M, N)` of `V'`, `l_V(M, N) ≤ l_{V'}(M, N)`.** -/
theorem pseudoLength_le_opens (W : TopologicalSpace.Opens V) (Sg : Set W) (M N : W) :
    pseudoLength n (Subtype.val '' Sg) (M : V) (N : V) ≤ pseudoLength n Sg M N :=
  le_iInf₂ fun _ hk => pseudoLength_le hk.lift

/-- **4°, for a segment of `V` included in `V'`** (« pour tout segment $(M, N)$ inclus dans
$V'$ »). -/
theorem pseudoLength_le_opens' (W : TopologicalSpace.Opens V) {Sg : Set V} (hSg : Sg ⊆ W)
    {M N : V} (hM : M ∈ W) (hN : N ∈ W) :
    pseudoLength n Sg M N ≤ pseudoLength n (Subtype.val ⁻¹' Sg : Set W) ⟨M, hM⟩ ⟨N, hN⟩ := by
  have := pseudoLength_le_opens (n := n) W (Subtype.val ⁻¹' Sg) ⟨M, hM⟩ ⟨N, hN⟩
  have e : (Subtype.val : W → V) '' (Subtype.val ⁻¹' Sg) = Sg := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hSg hx⟩, hx, rfl⟩
  rwa [e] at this

end Props

/-! ### Dimension `0` -/

/-- In `S(0)` two points are equal or diametrically opposite. -/
theorem S0_eq_or_eq_neg (x y : S 0) : y = x ∨ y = -x := by
  obtain ⟨v, hv⟩ := Sphere.exists_isRep x
  obtain ⟨w, hw⟩ := Sphere.exists_isRep y
  by_contra h
  push Not at h
  have := (Sphere.linearIndependent_of_ne hv hw h.1 h.2).fintype_card_le_finrank
  simp at this

/-- **1° in dimension `0`, literally**: in the locally projective manifold `S(0)`, the segment
`(m, m)` is majorised by no `k`, so `l(m, m) = +∞`. This holds only because Déf. 1 gives coincident
points no measure (`projMeasure_same_eq_top`); with a point given measure `0`, 1° would hold for
every `n`. The same proof works on every `V` charted on `S(0)`, a single point included. Reported
as a question (SCOPE « Dimension 0 »), not as a finding. -/
theorem pseudoLength_self_eq_top_dim_zero (m : S 0) :
    pseudoLength 0 ({m} : Set (S 0)) m m = ⊤ := by
  have hno : ∀ k : ℝ, ¬ IsMajoreSeg 0 k ({m} : Set (S 0)) m m := by
    rintro k ⟨-, Sg, A, B, ⟨φ, hφ, hS, -, -, hadm, -⟩, -, hall⟩
    have hlt := hall φ hφ hS
    rcases S0_eq_or_eq_neg (φ A) (φ B) with h | h
    · rw [h, Sphere.projMeasure_same_eq_top] at hlt
      exact not_top_lt hlt
    · exact hadm h
  simp [pseudoLength, hno]

end Benzecri
