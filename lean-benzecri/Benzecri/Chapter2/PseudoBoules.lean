import Benzecri.Chapter2.Hilbert
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Separation.Connected

/-!
# Chapter 2 § 2, Déf. 6 and Prop. 5 — pseudo-balls are open and connected, form a neighbourhood basis in a convex body, and an open set containing the pseudo-balls of its points is the whole manifold

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 2, journal p. 252; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex` (l.411–435 checked against the scan, PDF
p. 25). Target T-bz-c2-pseudo-boules (DEC-137).

* **`bzdef:c2s2d6_pseudo_boule`** — `benzecri1960_ch2.tex:411` (Déf. 6, l.411–415):
  `Benzecri.pseudoBoule n M r`, the points `N` joined to `M` by a closed segment majorised by `r`
  (Déf. 2, `IsMajoreSeg`); equivalently, at pseudo-length `< r` along some segment
  (`mem_pseudoBoule_iff`). In dimension `0` every pseudo-ball is empty, Déf. 2 majorising no
  segment there (`pseudoBoule_dim_zero`; OQ-45).
* The two unlabelled sentences after Déf. 6 (l.417–423), as lemmas, unmarked (no label):
  the pseudo-ball is open and connected (`pseudoBoule_ouvert_connexe`: every dimension, every `r`,
  « connexe » in Bourbaki's sense; `isConnected_pseudoBoule_iff` for the non-empty sense); in the
  interior of a convex body the pseudo-balls of centre `M` form a basis of neighbourhoods of `M`
  (`hasBasis_pseudoBoule`, `n ≥ 1`; `baseVoisinagesPrinted_iff`: exactly for `n ≥ 1`).
* `bzprop:c2s2p5_ouvert_plein` — `benzecri1960_ch2.tex:425` (Prop. 5, l.425–429, proof
  l.431–435) — not marked, pending the reading of « positif » (question). Prop. 5's `r` is the
  radius of a pseudo-ball, a Déf. 6 radius, « un nombre réel positif »; in the paper's usage
  « positif » is `> 0`, and then `Benzecri.ouvert_plein` (the printed hypotheses, `0 < r`) is
  Prop. 5 as printed, in every dimension; `eq_univ_of_forall_pseudoBoule_subset` drops « ouvert ».
  Only if « positif » includes `0` does the case `r = 0` fail (`ouvert_plein_counterexample`:
  `S(n) ∖ {x}`, `n ≥ 1`; `OuvertPleinPrinted n`, with `pseudoBoule` extended to every real radius,
  holds iff `n = 0`, `ouvertPleinPrinted_iff`).

> **Définition 6.** Soient $V$ une variété localement projective, $M\in V$, $r$ un nombre réel
> positif. On appelle pseudo-boule de centre $M$ et de rayon $r$ l'ensemble des points $N$ de $V$
> tels qu'il existe au moins un segment fermé d'extrémités $M$, $N$, majoré par $r$.
>
> La pseudo-boule de centre $M$ et de rayon $r$, est un ouvert connexe (*cf.* 3°, 5°).
>
> Si $V$ est l'intérieur d'un corps convexe, il résulte du 6° que lcs pseudo-boules de centre $M$
> et de rayon quelconque forment une base de voisinages de $M$. [sic « lcs » : lire « les »]
>
> **Proposition 5.** Soient $V$ une variété localement projective connexe, $U$ un ouvert non vide
> de $V$ et $r$ un nombre réel, tels que, quel que soit $M\in U$, la pseudo-boule de centre $M$ et
> de rayon $r$ soit incluse dans $U$. Alors $U=V$.
> Soit $M\in U$; $N\in V$ : nous allons montrer que $N\in U$. En effet, $M$ et $N$ peuvent être
> joints par une ligne brisée formée de segments tous majorés par $r$ : on démontre de proche en
> proche à partir de $M$ que tous les sommets de cette ligne appartiennent à $U$.
>
> 3° Soit $(M, N)\subset(M', N')$, on a $l_V(M, N)\leqq l_V(M', N')$; 5° La pseudo-longueur est
> une fonction semi-continue supérieurement du segment […]; 6° Si $V$ est l'intérieur d'un corps
> convexe, $l_V(M, N)$ est une fonction continue en $M$ et $N$ sur le produit $V\times V$;
> $l_V(M, N)$ est nulle si et seulement si $M=N$.

## The proofs formalized

*Open* (sentence 1): a majorising segment `(A, B) ⊇ (M, N)` lies in one chart `φ`; the
constant-cross-ratio estimate behind 5° (`eventually_exists_projMeasure_lt`) puts, for every `N'`
near `N`, the chart segment `(φM, φN')` inside a segment of `φ`'s target relative to which its
measure is `< r`, and `isMajoreSeg_of_chart` pulls it back (`isOpen_pseudoBoule`). *Connected*
(3°): every point `P` of a segment `(M, N)` majorised by `r` is joined to `M` by the sub-segment
`(M, P)` (`IsProjSegment.exists_subset_left`), of pseudo-length `≤ l_V(M, N) < r`
(`pseudoLength_mono`), so the pseudo-ball is the union of segments through its centre
(`isPreconnected_pseudoBoule`). *Neighbourhood basis* (6°): in `V = int K`, the pseudo-ball is the
`l_V`-ball (`mem_pseudoBoule_corpsInterior_iff`, the segment of `V` being unique); given a
neighbourhood `W` of `M`, take a compact neighbourhood `C ⊆ W`; `l_V(M, ·)` is continuous and
`> 0` off `M` (6°), so `≥ r > 0` on the frontier of `C`; the ball `B(M, r)` is connected, contains
`M` and misses that frontier, so it lies in `C` (`hasBasis_pseudoBoule`). *Prop. 5* (the
planner's route, checked; no broken line): `U` is closed, since a point `N` of its closure has an
`r`-majorised neighbourhood `W` (Prop. 3, `voisinage_majore`), a point `M'` of `W ∩ U` is joined
to `N` by a segment in `W` majorised by `r`, and so `N ∈ B(M', r) ⊆ U`; `U` is open, so `U = V`.
In dimension `0`, `V` is discrete (`discreteTopology_dim_zero`), so a connected `V` is at most a
point (`subsingleton_dim_zero`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 6: `V` a locally projective manifold, `M ∈ V` | ✓ carried: `[ChartedSpace (S n) V]` for the definition, `[HasGroupoid V (projGroupoid n)]` where a theorem uses it |
| Déf. 6: `r` « un nombre réel positif » (`r > 0` in the paper's usage, `r ≥ 0` under Bourbaki's; question) | ⚠ weakened: `r : ℝ` arbitrary, an extension of Déf. 6; for `r ≤ 0` the pseudo-ball is empty (`pseudoBoule_eq_empty_of_nonpos`) |
| Déf. 6: « au moins un segment fermé d'extrémités $M$, $N$, majoré par $r$ » | ✓ carried: `∃ Sg, IsMajoreSeg n r Sg M N` (Déf. 14 closed segment from `M` to `N`, Déf. 2); the order of the endpoints is immaterial (`mem_pseudoBoule_comm`) |
| Sentence 1: `V`, `M`, `r` as in Déf. 6 | ⚠ weakened: no Hausdorff, connectedness or countability; every `n`, every real `r` |
| Sentence 1: « un ouvert connexe » | ✓ carried under either reading of « connexe » (question). Bourbaki's (not the union of two disjoint non-empty open sets; the empty set is connected): `IsOpen ∧ IsPreconnected` in every dimension (`pseudoBoule_ouvert_connexe`). The non-empty sense: for every Déf. 6 radius `r > 0` when `n ≥ 1`; it fails only at `n = 0` (OQ-45), and at `r = 0` if « positif » includes `0` (`isConnected_pseudoBoule_iff`) |
| Sentence 2: `V` the interior of a convex body | ✓ carried: `corpsInterior K` with `IsCorpsConvexeS n K`, as Prop. 2 (`Benzecri.Chapter2.Hilbert`) |
| Sentence 2: « de rayon quelconque … forment une base de voisinages de $M$ » | ✓ carried, radii read `r > 0` (question): `(𝓝 M).HasBasis (fun r => 0 < r) (pseudoBoule n M)` |
| Sentence 2: the dimension | ⚠ strengthened: `[NeZero n]` in `hasBasis_pseudoBoule`; the sentence fails for `n = 0` (`baseVoisinagesPrinted_iff`; OQ-45) |
| Prop. 5: `V` a connected locally projective manifold | ⚠ weakened: `[PreconnectedSpace V]` with the charted structure and the groupoid; Hausdorff and countability never used |
| Prop. 5: `U` « un ouvert non vide » | ✓ carried in `ouvert_plein`; ⚠ weakened in `eq_univ_of_forall_pseudoBoule_subset` (openness follows) |
| Prop. 5: « $r$ un nombre réel », the radius of a pseudo-ball | ✓ carried: `0 < r`, `r` being a Déf. 6 radius and « positif » read `> 0` (question); if « positif » includes `0`, the case `r = 0` fails (`ouvert_plein_counterexample`) |
| Prop. 5: the dimension | ✓ carried: every `n` |

## SCOPE (disclosed)

* **The radius of Prop. 5** (question, not a finding). The scan, p. 252, prints « $r$ un nombre
  réel »; but Prop. 5 speaks of « la pseudo-boule … de rayon $r$ », which Déf. 6 defines only for
  « $r$ un nombre réel positif », so `r` is a Déf. 6 radius and negative radii are outside the
  paper under any reading. The paper's usage reads « positif » as `> 0`: Ch. 1 Déf. 3 (« Le groupe
  multiplicatif $\R^+$ … homothéties positives », ch1 l.168–169; « Le groupe $\R^+$ des réels
  positifs », ch1 l.527); the open hemisphere `F(H) = l⁻¹(ℝ⁺)` (ch1 l.205, read `0 < l v` by
  `Sphere.openHemisphere`, `Benzecri.Projective.Subvariety`); « positif ou nul » (ch2 l.82); « Soit $k$ un nombre réel
  positif » (ch2 l.669, where `ma/ab < k` forces `k > 0`). « strictement positif » also occurs
  (ch2 l.366, 383, 470), so the usage is not uniform, but no occurrence includes `0`. Under `> 0`,
  `Benzecri.ouvert_plein` is Prop. 5 as printed, in every dimension, and its printed broken-line
  proof (Prop. 4, `k > 0`) agrees. Under `≥ 0` (Bourbaki), `r = 0` refutes it in every dimension
  `n ≥ 1` (`ouvert_plein_counterexample`). The Lean `pseudoBoule` takes every real radius (empty for
  `r ≤ 0`), so `ouvertPleinPrinted_iff` refutes the `r ≤ 0` extension of Prop. 5, which is the
  paper only for `r = 0` and only under `≥ 0`. Routing: if the author rules `> 0`, the mark goes on
  `Benzecri.ouvert_plein` with no Lean change.
* **Prop. 5 is not proved through broken lines** (those are T-bz-c2-lignes's, Déf. 5, Prop. 4):
  the clopen route above uses Prop. 3 only, and is sorry-free in every dimension.
* **The printed justifications of the two sentences** (findings; statements unaffected). « *cf.*
  3°, 5° »: 5° bounds the pseudo-length of segments near `(M, N)` but does not produce a segment
  from `M` to each point near `N`; openness needs the chart of a majorising segment for that.
  « il résulte du 6° »: continuity and vanishing exactly on the diagonal do not by themselves make
  small balls small (a continuous function may tend to `0` away from `M`); the proof here adds the
  connectedness of the balls (sentence 1) and the local compactness of `V`.
* **Dimension 0** (OQ-45): every pseudo-ball is empty; sentence 1 holds only in Bourbaki's sense of
  « connexe » (the only place, with `r = 0` under `≥ 0`, where the reading matters); sentence 2 fails (`baseVoisinagesPrinted_iff`); Prop. 5 with `r > 0` holds (`V` is a
  point). Déf. 6 is marked as a definition, like Déf. 2–4 in `Benzecri.Chapter2.Mesure`: under
  OQ-45 (b) it would change with Déf. 2.
* General lemmas proved here, candidates to move upstream: `Sphere.ne_neg_of_mem_closedSeg`,
  `IsProjSegment.exists_subset_left`, `IsProjSegment.symm`, `IsMajoreSeg.symm`,
  `isMajoreSeg_iff_pseudoLength_lt`, `discreteTopology_dim_zero`, `connectedSpace_S`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u

/-! ### Two facts on segments of `S(E)` and of a manifold -/

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Two points of a closed segment `(A, B)`, `B ≠ −A`, are not diametrically opposite. -/
theorem ne_neg_of_mem_closedSeg {A B X Y : Sphere E} (hAB : B ≠ -A) (hX : X ∈ closedSeg A B)
    (hY : Y ∈ closedSeg A B) : Y ≠ -X := by
  by_cases hBA : B = A
  · rw [hBA, closedSeg_self, mem_singleton_iff] at hX hY
    rw [hX, hY]
    exact Module.Ray.ne_neg_self A
  obtain ⟨a, ha⟩ := exists_isRep A
  obtain ⟨b, hb⟩ := exists_isRep B
  have hli := linearIndependent_of_ne ha hb hBA hAB
  obtain ⟨s, t, hs, ht, hX⟩ := (mem_closedSeg_iff ha hb).1 hX
  obtain ⟨s', t', hs', ht', hY⟩ := (mem_closedSeg_iff ha hb).1 hY
  intro hYX
  rw [hYX] at hY
  obtain ⟨c, hc, hce⟩ := hX.neg.exists_pos hY
  obtain ⟨h1, h2⟩ := coeffs_eq hli (s := s') (t := t') (s' := -(c * s)) (t' := -(c * t))
    (by rw [hce]; module)
  have hs0 : s = 0 := by nlinarith
  have ht0 : t = 0 := by nlinarith
  exact hX.ne_zero (by rw [hs0, ht0]; simp)

end Sphere

section Segments

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

/-- **The sub-segment `(M, P)`**: every point `P` of a segment `(M, N)` of `V` is joined to `M` by
a segment of `V` contained in `(M, N)`. -/
theorem IsProjSegment.exists_subset_left {Sg : Set V} {M N P : V} (h : IsProjSegment n Sg M N)
    (hP : P ∈ Sg) : ∃ Sg' ⊆ Sg, IsProjSegment n Sg' M P := by
  obtain ⟨φ, hφ, hS, hM, -, hadm, himg⟩ := id h
  have hT : Sphere.closedSeg (φ M) (φ N) ⊆ φ.target := by
    rw [← himg]
    rintro _ ⟨x, hx, rfl⟩
    exact φ.map_source (hS hx)
  have hPseg : φ P ∈ Sphere.closedSeg (φ M) (φ N) := himg ▸ mem_image_of_mem φ hP
  have hsub := Sphere.closedSeg_subset_closedSeg (Sphere.left_mem_closedSeg _ _) hPseg
  have hne : φ P ≠ -φ M :=
    Sphere.ne_neg_of_mem_closedSeg hadm (Sphere.left_mem_closedSeg _ _) hPseg
  have hseg := isProjSegment_of_chart hφ hne (hsub.trans hT)
  rw [φ.left_inv hM, φ.left_inv (hS hP)] at hseg
  refine ⟨_, ?_, hseg⟩
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ φ '' Sg := himg ▸ hsub hy
  obtain ⟨x, hx, rfl⟩ := hy'
  rw [φ.left_inv (hS hx)]
  exact hx

/-- A segment read backwards is a segment. -/
theorem IsProjSegment.symm {Sg : Set V} {M N : V} (h : IsProjSegment n Sg M N) :
    IsProjSegment n Sg N M := by
  obtain ⟨φ, hφ, hS, hM, hN, hadm, himg⟩ := h
  refine ⟨φ, hφ, hS, hN, hM, fun e => hadm ?_, by rw [himg, Sphere.closedSeg_comm]⟩
  rw [e, neg_neg]

/-- A majorised segment read backwards is majorised by the same `k`. -/
theorem IsMajoreSeg.symm {k : ℝ} {Sg : Set V} {M N : V} (h : IsMajoreSeg n k Sg M N) :
    IsMajoreSeg n k Sg N M := by
  obtain ⟨hseg, Sg₁, A, B, hseg₁, hsub, hall⟩ := h
  refine ⟨hseg.symm, Sg₁, B, A, hseg₁.symm, hsub, fun φ hφ hS => ?_⟩
  rw [Sphere.projMeasure_reverse]
  exact hall φ hφ hS

end Segments

/-! ### Déf. 6 -/

section Def

variable {V : Type u} [TopologicalSpace V]

/-- **Déf. 6, the pseudo-ball of centre `M` and radius `r`** (`bzdef:c2s2d6_pseudo_boule`): the
points `N` of `V` such that at least one closed segment with endpoints `M`, `N` is majorised by `r`
in `V` (Déf. 2, `IsMajoreSeg`). -/
def pseudoBoule (n : ℕ) [ChartedSpace (S n) V] (M : V) (r : ℝ) : Set V :=
  {N | ∃ Sg : Set V, IsMajoreSeg n r Sg M N}

end Def

section Basic

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]

theorem mem_pseudoBoule {M N : V} {r : ℝ} :
    N ∈ pseudoBoule n M r ↔ ∃ Sg : Set V, IsMajoreSeg n r Sg M N :=
  Iff.rfl

/-- A pseudo-ball of radius `r ≤ 0` is empty (a projective measure is `≥ 0`). -/
theorem pseudoBoule_eq_empty_of_nonpos (M : V) {r : ℝ} (hr : r ≤ 0) : pseudoBoule n M r = ∅ := by
  refine eq_empty_of_forall_notMem fun N ⟨Sg, hmaj⟩ => ?_
  obtain ⟨-, Sg₁, A, B, ⟨φ, hφ, hS, -⟩, -, hall⟩ := hmaj
  have := (Sphere.projMeasure_nonneg _ _ _ _).trans_lt (hall φ hφ hS)
  exact absurd (EReal.coe_pos.1 this) (not_lt.2 hr)

/-- **In dimension `0` every pseudo-ball is empty** (no segment is majorised,
`not_isMajoreSeg_dim_zero`). -/
theorem pseudoBoule_dim_zero {W : Type u} [TopologicalSpace W] [ChartedSpace (S 0) W] (M : W)
    (r : ℝ) : pseudoBoule 0 M r = ∅ :=
  eq_empty_of_forall_notMem fun N ⟨Sg, hmaj⟩ => not_isMajoreSeg_dim_zero r Sg M N hmaj

theorem pseudoBoule_mono (M : V) {r r' : ℝ} (h : r ≤ r') :
    pseudoBoule n M r ⊆ pseudoBoule n M r' :=
  fun _ ⟨Sg, hmaj⟩ => ⟨Sg, hmaj.mono h⟩

/-- « d'extrémités $M$, $N$ » does not depend on the order: `N` is in the pseudo-ball of `M` iff
`M` is in the pseudo-ball of `N`. -/
theorem mem_pseudoBoule_comm {M N : V} {r : ℝ} : N ∈ pseudoBoule n M r ↔ M ∈ pseudoBoule n N r :=
  ⟨fun ⟨Sg, h⟩ => ⟨Sg, h.symm⟩, fun ⟨Sg, h⟩ => ⟨Sg, h.symm⟩⟩

end Basic

section Props

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]

/-- **Majorised by `k` iff of pseudo-length `< k`** (Déf. 2 and 3: the measure of a majorising
segment is one number `< k`, so a smaller `k'` majorises too). -/
theorem isMajoreSeg_iff_pseudoLength_lt {k : ℝ} {Sg : Set V} {M N : V} :
    IsMajoreSeg n k Sg M N ↔ pseudoLength n Sg M N < k := by
  constructor
  · intro h
    obtain ⟨hseg, Sg₁, A, B, hseg₁, hsub, φ, hφ, hS, hlt⟩ := isMajoreSeg_iff_exists_chart.1 h
    obtain ⟨k', hk', hk'k⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hmaj : IsMajoreSeg n k' Sg M N :=
      isMajoreSeg_iff_exists_chart.2 ⟨hseg, Sg₁, A, B, hseg₁, hsub, φ, hφ, hS, hk'⟩
    exact (pseudoLength_le hmaj).trans_lt hk'k
  · intro h
    rw [pseudoLength, iInf_lt_iff] at h
    obtain ⟨k', hk'⟩ := h
    rw [iInf_lt_iff] at hk'
    obtain ⟨hmaj, hlt⟩ := hk'
    exact hmaj.mono (EReal.coe_le_coe_iff.1 hlt.le)

/-- **The pseudo-ball is the set of points at pseudo-length `< r` along some segment from `M`.** -/
theorem mem_pseudoBoule_iff {M N : V} {r : ℝ} :
    N ∈ pseudoBoule n M r ↔ ∃ Sg : Set V, IsProjSegment n Sg M N ∧ pseudoLength n Sg M N < r := by
  constructor
  · rintro ⟨Sg, hmaj⟩
    exact ⟨Sg, hmaj.1, isMajoreSeg_iff_pseudoLength_lt.1 hmaj⟩
  · rintro ⟨Sg, -, hlt⟩
    exact ⟨Sg, isMajoreSeg_iff_pseudoLength_lt.2 hlt⟩

/-- **3°: a majorised segment from `M` lies in the pseudo-ball of `M`.** -/
theorem IsMajoreSeg.subset_pseudoBoule {r : ℝ} {Sg : Set V} {M N : V} (h : IsMajoreSeg n r Sg M N) :
    Sg ⊆ pseudoBoule n M r := by
  intro P hP
  obtain ⟨Sg', hSg', hseg'⟩ := h.1.exists_subset_left hP
  refine mem_pseudoBoule_iff.2 ⟨Sg', hseg', ?_⟩
  exact (pseudoLength_mono hSg' hseg').trans_lt (isMajoreSeg_iff_pseudoLength_lt.1 h)

/-- A non-empty pseudo-ball contains its centre. -/
theorem self_mem_pseudoBoule_of_nonempty {M : V} {r : ℝ} (h : (pseudoBoule n M r).Nonempty) :
    M ∈ pseudoBoule n M r := by
  obtain ⟨N, Sg, hmaj⟩ := h
  exact hmaj.subset_pseudoBoule hmaj.1.left_mem

/-- For `n ≥ 1` and `r > 0` the centre lies in the pseudo-ball. -/
theorem self_mem_pseudoBoule (hn : 1 ≤ n) (M : V) {r : ℝ} (hr : 0 < r) : M ∈ pseudoBoule n M r :=
  ⟨{M}, isMajoreSeg_singleton hn M hr⟩

/-- **A pseudo-ball is non-empty exactly when `n ≥ 1` and `r > 0`.** -/
theorem nonempty_pseudoBoule_iff (M : V) (r : ℝ) :
    (pseudoBoule n M r).Nonempty ↔ 0 < n ∧ 0 < r := by
  constructor
  · intro h
    refine ⟨Nat.pos_of_ne_zero fun hn => ?_, lt_of_not_ge fun hr => ?_⟩
    · subst hn
      rw [pseudoBoule_dim_zero] at h
      exact not_nonempty_empty h
    · rw [pseudoBoule_eq_empty_of_nonpos M hr] at h
      exact not_nonempty_empty h
  · rintro ⟨hn, hr⟩
    exact ⟨M, self_mem_pseudoBoule hn M hr⟩

/-- **The pseudo-ball is open** (any dimension, any `r`). -/
theorem isOpen_pseudoBoule (M : V) (r : ℝ) : IsOpen (pseudoBoule n M r) := by
  rw [isOpen_iff_mem_nhds]
  rintro N ⟨Sg, hmaj⟩
  obtain ⟨hSg, Sg₁, A, B, hseg₁, hsub, hall⟩ := hmaj
  obtain ⟨φ, hφ, hS₁, -, -, -, himg⟩ := id hseg₁
  have hlt := hall φ hφ hS₁
  have hT : Sphere.closedSeg (φ A) (φ B) ⊆ φ.target := by
    rw [← himg]
    rintro _ ⟨x, hx, rfl⟩
    exact φ.map_source (hS₁ hx)
  have hM : M ∈ φ.source := hS₁ (hsub hSg.left_mem)
  have hN : N ∈ φ.source := hS₁ (hsub hSg.right_mem)
  have hev := eventually_exists_projMeasure_lt φ.open_target hT hlt
  have hcont : ContinuousAt (fun N' : V => (φ M, φ N')) N :=
    continuousAt_const.prodMk (φ.continuousAt hN)
  filter_upwards [hcont.eventually hev, φ.open_source.mem_nhds hN] with N' hp hN'
  obtain ⟨A', B', hBA', hABT, hP, hQ, hmeas⟩ := hp
  have hne : φ N' ≠ -φ M := Sphere.ne_neg_of_mem_closedSeg hBA' hP hQ
  have h1 : IsMajoreSeg n r (φ.symm '' Sphere.closedSeg (φ M) (φ N')) (φ.symm (φ M))
      (φ.symm (φ N')) := isMajoreSeg_of_chart hφ hBA' hABT hP hQ hne hmeas
  rw [φ.left_inv hM, φ.left_inv hN'] at h1
  exact ⟨_, h1⟩

/-- **The pseudo-ball is connected**, in Bourbaki's sense (the empty set is connected; Mathlib's
`IsPreconnected`), any dimension, any `r`: it is the union of the segments majorised by `r` from
its centre (3°). -/
theorem isPreconnected_pseudoBoule (M : V) (r : ℝ) : IsPreconnected (pseudoBoule n M r) :=
  isPreconnected_of_forall M fun _ ⟨Sg, hmaj⟩ =>
    ⟨Sg, hmaj.subset_pseudoBoule, hmaj.1.left_mem, hmaj.1.right_mem, hmaj.1.isPreconnected_seg⟩

/-- **The first sentence after Déf. 6** (l.417–418, a lemma here): « La pseudo-boule de centre $M$
et de rayon $r$, est un ouvert connexe », « connexe » in Bourbaki's sense (`IsPreconnected`);
every dimension, every `r`. -/
theorem pseudoBoule_ouvert_connexe (M : V) (r : ℝ) :
    IsOpen (pseudoBoule n M r) ∧ IsPreconnected (pseudoBoule n M r) :=
  ⟨isOpen_pseudoBoule M r, isPreconnected_pseudoBoule M r⟩

/-- With « connexe » read as Mathlib's `IsConnected` (non-empty), the pseudo-ball is connected
exactly when `n ≥ 1` and `r > 0`. -/
theorem isConnected_pseudoBoule_iff (M : V) (r : ℝ) :
    IsConnected (pseudoBoule n M r) ↔ 0 < n ∧ 0 < r :=
  ⟨fun h => (nonempty_pseudoBoule_iff M r).1 h.1,
    fun h => ⟨(nonempty_pseudoBoule_iff M r).2 h, isPreconnected_pseudoBoule M r⟩⟩

end Props

/-! ### The interior of a convex body: the pseudo-balls form a neighbourhood basis -/

section Body

variable {n : ℕ} {K : Set (S n)}

/-- In the interior `V` of a convex body the pseudo-ball is the `l_V`-ball. -/
theorem mem_pseudoBoule_corpsInterior_iff (hK : IsCorpsConvexeS n K) {M N : corpsInterior K}
    {r : ℝ} : N ∈ pseudoBoule n M r ↔ hilbertLength K M N < r := by
  rw [mem_pseudoBoule_iff]
  constructor
  · rintro ⟨Sg, hseg, hlt⟩
    rwa [pseudoLength_eq_hilbertLength hK hseg] at hlt
  · intro h
    exact ⟨_, isProjSegment_hilbert hK M N, h⟩

/-- **The second sentence after Déf. 6** (l.420–423, [sic] « lcs » read « les »; a lemma here):
« Si $V$ est l'intérieur d'un corps convexe, il résulte du 6° que les pseudo-boules de centre $M$
et de rayon quelconque forment une base de voisinages de $M$ » (`n ≥ 1`; radii `r > 0`). -/
theorem hasBasis_pseudoBoule [NeZero n] (hK : IsCorpsConvexeS n K) (M : corpsInterior K) :
    (𝓝 M).HasBasis (fun r : ℝ => 0 < r) (pseudoBoule n M) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  refine ⟨fun W => ⟨fun hW => ?_, fun ⟨r, hr, hsub⟩ =>
    mem_of_superset ((isOpen_pseudoBoule M r).mem_nhds (self_mem_pseudoBoule hn M hr)) hsub⟩⟩
  haveI : LocallyCompactSpace (corpsInterior K) := (corpsInterior K).isOpen.locallyCompactSpace
  obtain ⟨C, hC, hCW, hCc⟩ := local_compact_nhds hW
  have hCcl : IsClosed C := hCc.isClosed
  have hf : Continuous fun P : corpsInterior K => hilbertLength K M P := by
    have h2 : Continuous fun P : corpsInterior K => (M, P) := continuous_const.prodMk continuous_id
    have h3 := (continuous_hilbertLength hK).comp h2
    simp only [Function.comp_def] at h3
    exact h3
  have hfr : IsCompact (frontier C) :=
    hCc.of_isClosed_subset isClosed_frontier (frontier_subset_closure.trans hCcl.closure_eq.le)
  have hMi : M ∈ interior C := mem_interior_iff_mem_nhds.2 hC
  -- a positive lower bound of `l_V(M, ·)` on the frontier of `C`
  obtain ⟨r, hr, hrfr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ P ∈ frontier C, (r : EReal) ≤ hilbertLength K M P := by
    rcases (frontier C).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨P₀, hP₀, hmin⟩ := hfr.exists_isMinOn h hf.continuousOn
    have hne : M ≠ P₀ := fun e => hP₀.2 (e ▸ hMi)
    have hpos : 0 < hilbertLength K M P₀ :=
      lt_of_le_of_ne (pseudoLength_nonneg _ _ _) (Ne.symm (hilbertLength_ne_zero hK hne))
    obtain ⟨r, hr0, hr⟩ := EReal.lt_iff_exists_real_btwn.1 hpos
    exact ⟨r, EReal.coe_pos.1 hr0, fun P hP => hr.le.trans (isMinOn_iff.1 hmin P hP)⟩
  -- the pseudo-ball, connected, contains `M` and misses the frontier of `C`
  refine ⟨r, hr, ?_⟩
  have hsub : pseudoBoule n M r ⊆ interior C := by
    refine (isPreconnected_pseudoBoule M r).subset_left_of_subset_union isOpen_interior
      hCcl.isOpen_compl (disjoint_compl_right.mono_left interior_subset) ?_
      ⟨M, self_mem_pseudoBoule hn M hr, hMi⟩
    intro P hP
    by_cases hPC : P ∈ C
    · left
      by_contra hPi
      have hPfr : P ∈ frontier C := ⟨subset_closure hPC, hPi⟩
      exact absurd ((mem_pseudoBoule_corpsInterior_iff hK).1 hP) (not_lt.2 (hrfr P hPfr))
    · exact Or.inr hPC
  exact hsub.trans (interior_subset.trans hCW)

end Body

/-- **The second sentence as printed**, for the convex bodies of `S(n)`. -/
def BaseVoisinagesPrinted (n : ℕ) : Prop :=
  ∀ K : Set (S n), IsCorpsConvexeS n K → ∀ M : corpsInterior K,
    (𝓝 M).HasBasis (fun r : ℝ => 0 < r) (pseudoBoule n M)

/-- **The second sentence holds exactly in dimension `n ≥ 1`.** For `n = 0`, `{x}` is a convex body
of `S(0)` and its pseudo-balls are empty. -/
theorem baseVoisinagesPrinted_iff {n : ℕ} : BaseVoisinagesPrinted n ↔ 0 < n := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      obtain ⟨x⟩ : Nonempty (S 0) := inferInstance
      have hx : x ∈ interior ({x} : Set (S 0)) := by
        rw [(isOpen_singleton_S0 x).interior_eq]; exact mem_singleton x
      have hmem := (h {x} (isCorpsConvexeS_singleton_S0 x) ⟨x, hx⟩).mem_of_mem one_pos
      rw [pseudoBoule_dim_zero] at hmem
      exact (nhds_neBot (x := (⟨x, hx⟩ : corpsInterior ({x} : Set (S 0))))).ne
        (empty_mem_iff_bot.1 hmem)
    · exact hn
  · intro hn K hK M
    haveI : NeZero n := ⟨hn.ne'⟩
    exact hasBasis_pseudoBoule hK M

/-! ### Prop. 5 -/

section Dim0

variable {V : Type u} [TopologicalSpace V]

/-- A manifold charted on `S(0)` is discrete. -/
theorem discreteTopology_dim_zero [ChartedSpace (S 0) V] : DiscreteTopology V := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
  set φ := chartAt (S 0) x
  have hx : x ∈ φ.source := mem_chart_source _ x
  have e : ({x} : Set V) = φ.source ∩ φ ⁻¹' {φ x} := by
    ext y
    simp only [mem_singleton_iff, mem_inter_iff, mem_preimage]
    constructor
    · intro hy
      rw [hy]
      exact ⟨hx, rfl⟩
    · rintro ⟨hy, hφy⟩
      exact φ.injOn hy hx hφy
  rw [e]
  exact φ.isOpen_inter_preimage (isOpen_singleton_S0 _)

/-- A connected manifold charted on `S(0)` has at most one point. -/
theorem subsingleton_dim_zero [ChartedSpace (S 0) V] [PreconnectedSpace V] : Subsingleton V := by
  haveI := discreteTopology_dim_zero (V := V)
  exact PreconnectedSpace.trivial_of_discrete

end Dim0

section Prop5

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]

/-- A set containing the pseudo-ball of radius `r > 0` of each of its points is closed
(`n ≥ 1`; Prop. 3 gives each point of its closure an `r`-majorised neighbourhood). -/
theorem isClosed_of_forall_pseudoBoule_subset [NeZero n] {U : Set V} {r : ℝ} (hr : 0 < r)
    (h : ∀ M ∈ U, pseudoBoule n M r ⊆ U) : IsClosed U := by
  refine isClosed_of_closure_subset fun N hN => ?_
  obtain ⟨W, hW, hWmaj⟩ := voisinage_majore (n := n) hr N
  obtain ⟨M, hMW, hMU⟩ := mem_closure_iff_nhds.1 hN W hW
  obtain ⟨Sg, -, hmaj⟩ := hWmaj M hMW N (mem_of_mem_nhds hW)
  exact h M hMU ⟨Sg, hmaj⟩

/-- A set containing the pseudo-ball of radius `r > 0` of each of its points is open (`n ≥ 1`). -/
theorem isOpen_of_forall_pseudoBoule_subset [NeZero n] {U : Set V} {r : ℝ} (hr : 0 < r)
    (h : ∀ M ∈ U, pseudoBoule n M r ⊆ U) : IsOpen U :=
  isOpen_iff_mem_nhds.2 fun M hM => mem_of_superset ((isOpen_pseudoBoule M r).mem_nhds
    (self_mem_pseudoBoule (Nat.one_le_iff_ne_zero.2 (NeZero.ne n)) M hr)) (h M hM)

/-- **Prop. 5** (`bzprop:c2s2p5_ouvert_plein`; any dimension), `r > 0` being a Déf. 6 radius
(« positif » read `> 0`, the paper's usage; a question for the author): « Soient $V$ une
variété localement projective connexe, $U$ un ouvert non vide de $V$ et $r$ un nombre réel, tels
que, quel que soit $M\in U$, la pseudo-boule de centre $M$ et de rayon $r$ soit incluse dans $U$.
Alors $U=V$. » -/
theorem ouvert_plein [PreconnectedSpace V] {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) {r : ℝ}
    (hr : 0 < r) (h : ∀ M ∈ U, pseudoBoule n M r ⊆ U) : U = univ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI := subsingleton_dim_zero (V := V)
    obtain ⟨x, hx⟩ := hne
    exact eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
  · haveI : NeZero n := ⟨hn.ne'⟩
    exact IsClopen.eq_univ ⟨isClosed_of_forall_pseudoBoule_subset hr h, hU⟩ hne

/-- **Prop. 5 without « ouvert »**: the openness of `U` follows from the other hypotheses. -/
theorem eq_univ_of_forall_pseudoBoule_subset [PreconnectedSpace V] {U : Set V} (hne : U.Nonempty)
    {r : ℝ} (hr : 0 < r) (h : ∀ M ∈ U, pseudoBoule n M r ⊆ U) : U = univ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI := subsingleton_dim_zero (V := V)
    obtain ⟨x, hx⟩ := hne
    exact eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
  · haveI : NeZero n := ⟨hn.ne'⟩
    exact ouvert_plein (isOpen_of_forall_pseudoBoule_subset hr h) hne hr h

end Prop5

/-- `S(n)` is connected for `n ≥ 1`. -/
theorem connectedSpace_S {n : ℕ} (hn : 0 < n) : ConnectedSpace (S n) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  haveI := isConnected_iff_connectedSpace.1
    (isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin (n + 1))) zero_le_one)
  exact (S.homeomorphEuclideanSphere n).symm.surjective.connectedSpace
    (S.homeomorphEuclideanSphere n).symm.continuous

/-- **If « positif » includes `0`, the case `r = 0` of Prop. 5 fails** (`n ≥ 1`): in the connected locally projective manifold
`S(n)`, the open set `S(n) ∖ {x}` is non-empty, contains the pseudo-ball of radius `0` of each of
its points (they are empty), and is not `S(n)`. A counterexample to the paper only if Déf. 6's
« positif » includes `0`; in the paper's usage (`> 0`) a radius `0` is not a Déf. 6 radius. -/
theorem ouvert_plein_counterexample {n : ℕ} (hn : 0 < n) (x : S n) :
    ConnectedSpace (S n) ∧ IsOpen ({x}ᶜ : Set (S n)) ∧ ({x}ᶜ : Set (S n)).Nonempty ∧
      (∀ M ∈ ({x}ᶜ : Set (S n)), pseudoBoule n M 0 ⊆ {x}ᶜ) ∧ ({x}ᶜ : Set (S n)) ≠ univ := by
  refine ⟨connectedSpace_S hn, isOpen_compl_singleton, ⟨-x, Sphere.neg_ne_self x⟩,
    fun M _ => ?_, fun h => ?_⟩
  · rw [pseudoBoule_eq_empty_of_nonpos M le_rfl]
    exact empty_subset _
  · have hx : x ∈ ({x}ᶜ : Set (S n)) := h ▸ mem_univ x
    exact hx rfl

/-- **Prop. 5 with `pseudoBoule` extended to every real radius** (« $r$ un nombre réel » taken
literally), over the manifolds of dimension `n` (Hausdorff, connected, second countable;
`V : Type`). It is the printed Prop. 5 only if Déf. 6's « positif » includes `0`, and then only
through `r = 0`: negative radii are outside Déf. 6 under any reading. -/
def OuvertPleinPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V], ∀ U : Set V, IsOpen U →
    U.Nonempty → ∀ r : ℝ, (∀ M ∈ U, pseudoBoule n M r ⊆ U) → U = univ

/-- **The extension to every real radius holds exactly in dimension `0`.** For `n ≥ 1`, `r = 0`
makes every pseudo-ball empty, and the open set `S(n) ∖ {x}` of the connected `S(n)` satisfies the
hypothesis without being `S(n)` (`ouvert_plein_counterexample`): a counterexample to the paper
only if « positif » includes `0`. -/
theorem ouvertPleinPrinted_iff {n : ℕ} : OuvertPleinPrinted n ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨x⟩ : Nonempty (S n) := inferInstance
    obtain ⟨hconn, hUo, hUne, hball, hUne'⟩ := ouvert_plein_counterexample (Nat.pos_of_ne_zero hn) x
    haveI := hconn
    haveI : SecondCountableTopology (S n) := (S.homeomorphEuclideanSphere n).secondCountableTopology
    exact hUne' (h (S n) _ hUo hUne 0 hball)
  · rintro rfl V _ _ _ _ _ _ U _ hne r _
    haveI := subsingleton_dim_zero (V := V)
    obtain ⟨x, hx⟩ := hne
    exact eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx

end Benzecri
