import Benzecri.Chapter2.Developpement

/-!
# Chapter 2 § 3, the Theorem (projective) — 2°–4° and the assembly: `P` simply connected ⇒ `V` simply connected; a shell gives a convex `φ̃(V)`; a strict shell gives the interior of a convex body

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 3, journal pp. 253–255; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-theoreme (DEC-137).

* `bzthm:c2s3t1_poche_balayable` — `benzecri1960_ch2.tex:517` (statement l.517–533, proof
  l.535–622; 2°–4° at l.526–532, their proofs at l.593–619). Not marked: OQ-71 is open (1°'s
  second sentence, SCOPE). The Theorem is assembled here in both forms: `theoremeComposantePrinted`
  (1° in component form, with 2°–4°, proved in every dimension) and `theoremePrinted_iff` (1° in
  the printed full form, with 2°–4°, equivalent to `ConnexePrinted`, the connectedness the proof
  of 1°c presumes). Under the component-form answer to OQ-71 the row is marked with no Lean change;
  under the full-form answer the mark waits on a proof of `ConnexePrinted` (open), which needs no
  change here.

> **Théorème.** Soit $V$ une variété localement projective connexe balayable. Soit
> $(P, \mathring{H}, \varphi, z)$ une poche de $V$.
>
> 1° Il existe une carte compatible $\tilde{\varphi}$ de $V$ sur un ouvert de $S(n)$, induisant
> $\varphi$ sur $P$. $P$ n'est autre que l'image réciproque par $\tilde{\varphi}$ de l'ensemble des
> points de $\mathring{H}$ où $z<1$.
>
> 2° Si $P$ est simplement connexe, il en est de même de $V$.
>
> 3° Si $\varphi(P)$ est convexe (*i. e.* si $(P, \mathring{H}, \varphi, z)$ est une coque),
> $\tilde{\varphi}(V)$ est un convexe.
>
> 4° Si $(P, \mathring{H}, \varphi, z)$ est une coque stricte, $\tilde{\varphi}(V)$ est
> l'intérieur d'un corps convexe.
>
> […] Dans la suite, nous supposerons, pour simplifier les notations, que $\tilde{\varphi}$ est
> l'identité, et donc que $P$ et $V$ sont des parties de $S(n)$.
>
> *Démontrons* 2°. — Soit $L$ un lacet de $V$ : il faut montrer que $L$ est homotope à un point.
> Or il existe un automorphisme de $V$ qui envoie le compact $L$ dans $P$ : comme $P$ est
> simplement connexe, $L$ est homotope à un point.
>
> *Démontrons* 3°. — Soit $M$ et $N$ deux points de $V$ : il faut montrer que, dans $V$, il existe
> un segment fermé d'extrémités $M$, $N$. Or, soit $g$ un automorphisme projectif tel que
> $gM\in P$, $gN\in P$ : il existe un segment $(gM, gN)$ puisque $\varphi(P)$ est convexe; donc il
> existe un segment $(M, N)$.
>
> *Démontrons* 4°. — Si $V$ n'est pas l'intérieur d'un corps convexe, on peut trouver dans $V$ une
> demi-droite $L$, c'est-à-dire une portion de droite limitée à deux points diamétralement opposés
> de la frontière de $V$.
>
> Soit $g$ un automorphisme projectif de $V$ qui envoie dans $P$ un point $M$ de $L$ : il résulte
> de la condition $b$ de la définition des poches que $gL$ est une demi-droite incluse dans
> $\mathring{H}$, c'est-à-dire une droite de la géométrie affine de $\mathring{H}$ : nous allons
> montrer que cette inclusion est incompatible avec l'hypothèse faite que $P$ ne contient pas de
> droite de $\mathring{H}$.
>
> En effet (§ 1, déf. 1′, *b*), tout point de $gL$ de cote $z$ inférieure à $1$ appartient à $P$ :
> donc tous les points de $gL$ ont une cote supérieure ou égale à $0$, puisque la borne inférieure
> de $z$ sur $P$ est $0$. Mais alors, $gL$ est une droite (pour la géométrie affine de
> $\mathring{H}$) de cote constante égale à $z(M)$ et $gL$ est incluse dans $P$, ce qui contredit
> l'hypothèse faite sur $P$.
>
> La démonstration du théorème est achevée.

## What is proved (no `sorry`)

* The « demi-droite » lemma (l.605–607), convex geometry of `S(n)`: `exists_demiDroite` (an open,
  nonempty, strict convex part of `S(n)` which is not the interior of a convex body contains a
  half-line `s({a x + b p | b > 0})` whose ends `±s(x)` lie on its frontier); the same with the
  paper's « convexe » and `C ≠ S(n)`, `exists_demiDroite_of_ne_univ` (an open convex part other
  than `S(n)` is strict, `Sphere.isStrictConvexPart_of_isOpen`); its converse
  (`eq_interior_corpsConvexe_iff_not_demiDroite`); its two halves
  `isCorpsConvexeS_closure_of_salient`, `demiDroite_of_not_salient`; it fails for `S(n)` itself
  (`univ_not_demiDroite`); an instance, the open hemisphere of `S(1)` (`demiDroite_hemisphere`).
* 2°: `theoreme_deuxieme`. 3°: `theoreme_troisieme` (`φ̃(V)` is even a strict convex part; for
  every pocket it has no antipodal pair, `neg_notMem_range_of_poche`), with the paper's segment
  form `exists_isProjSegment_of_coque`. 4°: `theoreme_quatrieme`. The pocket of a strict shell is
  simply connected (`simplyConnectedSpace_of_coqueStricte`), so 2° applies to it.
* The assembly: `theoreme_poche_balayable` (general `V`); over the paper's manifolds,
  `TheoremeComposantePrinted`, `theoremeComposantePrinted`, `TheoremePrinted`,
  `theoremePrinted_iff`.
* Non-vacuity: `theoreme_poche_balayable_model` (`ℝⁿ`, the shell of cote `0`, `P = V`) and
  `theoreme_poche_balayable_demiDroite` (`]0, ∞[` with the strict shell `]0, 1[ ≠ V`, every
  hypothesis of 2°–4° met).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « une variété localement projective » | ⚠ weakened: `[ChartedSpace (S n) V]`, `[HasGroupoid V (projGroupoid n)]`; Hausdorff and second countable never used (the printed forms carry them) |
| `V` connexe | ⚠ weakened: `[PreconnectedSpace V]` (the pocket makes `V` nonempty) |
| `V` balayable | ✓ carried: `IsBalayable (GSR n) (S n) V` |
| `(P, H̊, φ, z)` une poche de `V` | ✓ carried: `IsPocheProj P l φ z` |
| the dimension | ✓ every `n`, `n = 0` included |
| 2°: « $P$ est simplement connexe » | ✓ carried: `SimplyConnectedSpace P` (Mathlib) |
| 3°: « $\varphi(P)$ est convexe (*i. e.* … une coque) » | ✓ carried: `IsCoqueProj P l φ z` (Déf. 2) |
| 4°: « une coque stricte » | ✓ carried: `IsCoqueStricteProj P l φ z` (Déf. 3) |
| 2°: « il en est de même de $V$ » | ✓ carried: `SimplyConnectedSpace V` |
| 3°: « $\tilde\varphi(V)$ est un convexe » | ✓ carried: `Sphere.IsConvexPart (range φ̃)` (Déf. 8); proved even strict (Déf. 9) |
| 4°: « l'intérieur d'un corps convexe » | ✓ carried: `∃ K, IsCorpsConvexeS n K ∧ range φ̃ = interior K` (Déf. 11), `K = closure (range φ̃)` |

## SCOPE (disclosed)

* **1°'s second sentence** is carried in component form (`theoreme_premier`); the printed full
  form is equivalent to `ConnexePrinted` (OQ-71, T-bz-c2-developpement); it is proved for every
  shell, for every pocket when `n ≤ 1`, and open only for `ConnexeOuvertPrinted`
  (`Benzecri.Chapter2.PremierFull`, T-bz-c2-premier-full-proj). 2°–4° do not use it: after 1°c the paper sets `φ̃ = id` (l.593–594) and
  argues by Prop. 7 and condition *b* only.
* **4°, the base point of the demi-droite.** The paper takes any demi-droite `L` of `V` and moves a
  point of it into `P` by an automorphism `g` (l.609). The lemma gives a demi-droite through EVERY
  point of `φ̃(V)` (`demiDroite_of_not_salient`), so the proof takes one through a point of `φ(P)`,
  and `g` is not needed in this step. Condition *b* along the sub-segments from that point, the
  cote bounded below on a line, and `¬ ContainsAffLine` are the paper's argument.
* **The demi-droite lemma needs `V ≠ S(n)`** (for a nonempty open convex part, the same as strict,
  `Sphere.isStrictConvexPart_of_isOpen`; « convex part » in Déf. 8's `∪` reading, DEC-120, in
  whose Minkowski reading `S(n)` is not a convex part): `S(n)` itself is an open convex part, not the interior of
  a convex body, with an empty frontier (`univ_not_demiDroite`). The paper applies the lemma to `V`
  without saying why `V ≠ S(n)`; here `φ̃(V)` is strict because two antipodal points of it would be
  moved by one `γ` into `φ(P) ⊆ H̊` (`neg_notMem_range_of_poche`). An exposition remark (REPORT,
  findings); the statement is unaffected.
* 3°'s « convexe » is Déf. 8 in the `∪` reading (DEC-120); `φ̃(V)` is proved strict, so the
  conclusion holds in the Minkowski reading as well.
* 2°–4° call Prop. 7 and its corollary only (`compact_dans_poche`, `deux_points_dans_poche`, which
  hold for `n = 0` and depend on neither OQ-45 nor OQ-61), never Prop. 4 or Prop. 6 directly.
* **`[sic]`, not a finding**: « $z(M)$ » (l.618, as printed on the scan, p. 255) is read
  « $z(gM)$ » (the transcription's comment at l.620); here, the cote of the base point in `φ(P)`.
* « demi-droite » (l.605–607) is Remarque 1's half-line `Sphere.halfLine x p`, its two ends
  `±s(x)` « deux points diamétralement opposés de la frontière de $V$ ».

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology unitInterval
open scoped Pointwise

namespace Benzecri

universe u

/-! ### The « demi-droite » lemma: open convex parts of `S(n)` -/

section DemiDroite

variable {n : ℕ}

/-- In the open convex cone `F(C)` of an open strict convex part `C`, adding a vector of the
closure of the cone keeps one in the cone: `p ∈ F(C)`, `q ∈ closure F(C)` ⇒ `p + q ∈ F(C)`. -/
theorem Sphere.add_mem_F_of_mem_closure_F {C : Set (S n)} (hCo : IsOpen C)
    (hconv : Convex ℝ (Sphere.F C)) {p q : Fin (n + 1) → ℝ} (hp : p ∈ Sphere.F C)
    (hq : q ∈ closure (Sphere.F C)) : p + q ∈ Sphere.F C := by
  have hFo : IsOpen (Sphere.F C) := Sphere.isOpen_iff_F.1 hCo
  have h2p : (2 : ℝ) • p ∈ Sphere.F C := Sphere.smul_mem_F hp two_pos
  have h2q : (2 : ℝ) • q ∈ closure (Sphere.F C) := by
    refine closure_mono ?_ (smul_closure_subset (2 : ℝ) _ (smul_mem_smul_set hq))
    rintro _ ⟨y, hy, rfl⟩
    exact Sphere.smul_mem_F hy two_pos
  have hseg := hconv.openSegment_interior_closure_subset_interior
    (hFo.interior_eq.symm ▸ h2p) h2q
  rw [hFo.interior_eq] at hseg
  refine hseg ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  module

/-- **An open strict convex part is the interior of its closure.** -/
theorem interior_closure_eq_of_convex_F {C : Set (S n)} (hCo : IsOpen C)
    (hconv : Convex ℝ (Sphere.F C)) : interior (closure C) = C := by
  have hFo : IsOpen (Sphere.F C) := Sphere.isOpen_iff_F.1 hCo
  refine Subset.antisymm ?_ (interior_maximal subset_closure hCo)
  intro m hm
  obtain ⟨v, hv0, rfl⟩ := Sphere.exists_isRep m
  have hvF : v ∈ Sphere.F (interior (closure C)) := ⟨hv0, hm⟩
  have hsub : Sphere.F (interior (closure C)) ⊆ closure (Sphere.F C) := by
    refine (Sphere.F_mono interior_subset).trans ?_
    rw [Sphere.F_closure]
    exact sdiff_subset
  have hvi : v ∈ interior (closure (Sphere.F C)) :=
    interior_maximal hsub (Sphere.isOpen_iff_F.1 isOpen_interior) hvF
  rcases (Sphere.F C).eq_empty_or_nonempty with he | hne
  · rw [he, closure_empty, interior_empty] at hvi
    exact hvi.elim
  rw [hconv.interior_closure_eq_interior_of_nonempty_interior (hFo.interior_eq.symm ▸ hne),
    hFo.interior_eq] at hvi
  exact (Sphere.mk_mem_iff_mem_F hv0).2 hvi

/-- **The demi-droite lemma, first half**: an open, nonempty, strict convex part `C` of `S(n)`
whose closed cone `closure F(C)` is salient (contains no line through `O`) has a convex body as
its closure, and is its interior. -/
theorem isCorpsConvexeS_closure_of_salient {C : Set (S n)} (hCo : IsOpen C) (hne : C.Nonempty)
    (hconv : Convex ℝ (Sphere.F C))
    (hsal : ∀ x ∈ closure (Sphere.F C), -x ∈ closure (Sphere.F C) → x = 0) :
    IsCorpsConvexeS n (closure C) ∧ interior (closure C) = C := by
  refine ⟨?_, interior_closure_eq_of_convex_F hCo hconv⟩
  rw [isCorpsConvexeS_iff, Sphere.F_closure]
  refine ⟨?_, isClosed_closure.isCompact, hne.mono (interior_maximal subset_closure hCo)⟩
  set K := closure (Sphere.F C) with hKdef
  have hKc : Convex ℝ K := hconv.closure
  have hKsmul : ∀ c : ℝ, 0 < c → ∀ x ∈ K, c • x ∈ K := by
    intro c hc x hx
    refine closure_mono ?_ (smul_closure_subset c _ (smul_mem_smul_set hx))
    rintro _ ⟨y, hy, rfl⟩
    exact Sphere.smul_mem_F hy hc
  intro x hx y hy a b ha hb hab
  refine ⟨hKc hx.1 hy.1 ha hb hab, fun h0 => ?_⟩
  have h0 : a • x + b • y = 0 := h0
  rcases ha.lt_or_eq with ha' | rfl
  · rcases hb.lt_or_eq with hb' | rfl
    · -- `y = -(a/b) x`, so `-x ∈ K`
      have hy' : y = -((a / b) • x) := by
        have h1 : b • y = -(a • x) := eq_neg_of_add_eq_zero_right h0
        have h2 : y = b⁻¹ • (b • y) := by rw [smul_smul, inv_mul_cancel₀ hb'.ne', one_smul]
        rw [h2, h1, smul_neg, smul_smul, div_eq_inv_mul]
      have hnx : -x ∈ K := by
        have := hKsmul (b / a) (div_pos hb' ha') _ hy.1
        rwa [hy', smul_neg, smul_smul, div_mul_div_cancel₀ ha'.ne', div_self hb'.ne',
          one_smul] at this
      exact hx.2 (hsal x hx.1 hnx)
    · rw [add_zero] at hab
      rw [hab, one_smul, zero_smul, add_zero] at h0
      exact hx.2 h0
  · rw [zero_add] at hab
    rw [hab, one_smul, zero_smul, zero_add] at h0
    exact hy.2 h0

/-- **The demi-droite lemma, second half**: if `±x ∈ closure F(C)`, `x ≠ 0`, for an open strict
convex part `C`, then through every point `s(p)` of `C` the whole line `p + ℝ x` stays in `F(C)`,
`x, p` are independent, `C` contains the half-line `s({a x + b p | b > 0})` (a « demi-droite »),
and its two ends `±s(x)`, diametrically opposite, lie on the frontier of `C`. -/
theorem demiDroite_of_not_salient {C : Set (S n)} (hCo : IsOpen C) (hconv : Convex ℝ (Sphere.F C))
    {x : Fin (n + 1) → ℝ} (hx0 : x ≠ 0) (hx : x ∈ closure (Sphere.F C))
    (hnx : -x ∈ closure (Sphere.F C)) {p : Fin (n + 1) → ℝ} (hp : p ∈ Sphere.F C) :
    (∀ t : ℝ, p + t • x ∈ Sphere.F C) ∧ ∃ _ : LinearIndependent ℝ ![x, p],
      Sphere.halfLine x p ⊆ C ∧ Sphere.mk x hx0 ∈ frontier C ∧
        -Sphere.mk x hx0 ∈ frontier C := by
  have hKsmul : ∀ c : ℝ, 0 < c → ∀ y ∈ closure (Sphere.F C), c • y ∈ closure (Sphere.F C) := by
    intro c hc y hy
    refine closure_mono ?_ (smul_closure_subset c _ (smul_mem_smul_set hy))
    rintro _ ⟨w, hw, rfl⟩
    exact Sphere.smul_mem_F hw hc
  have hline : ∀ t : ℝ, p + t • x ∈ Sphere.F C := by
    intro t
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have := hKsmul (-t) (neg_pos.2 ht) _ hnx
      rw [smul_neg, ← neg_smul, neg_neg] at this
      exact Sphere.add_mem_F_of_mem_closure_F hCo hconv hp this
    · rwa [zero_smul, add_zero]
    · exact Sphere.add_mem_F_of_mem_closure_F hCo hconv hp (hKsmul t ht _ hx)
  have hxp : LinearIndependent ℝ ![x, p] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hx0, rfl⟩
    · exfalso
      have h1 : p + (s / t) • x = t⁻¹ • (s • x + t • p) := by
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul, div_eq_inv_mul]
        exact add_comm _ _
      rw [hst, smul_zero] at h1
      exact Sphere.zero_notMem_F C (h1 ▸ hline (s / t))
  have hsub : Sphere.halfLine x p ⊆ C := by
    intro y hy
    induction y using Sphere.ind with
    | h u hu =>
      obtain ⟨a, b, hb, rfl⟩ := (Sphere.mk_mem_halfLine hu).1 hy
      refine (Sphere.mk_mem_iff_mem_F hu).2 ?_
      have : a • x + b • p = b • (p + (a / b) • x) := by
        rw [smul_add, smul_smul, mul_div_cancel₀ _ hb.ne']
        exact add_comm _ _
      rw [this]
      exact Sphere.smul_mem_F (hline (a / b)) hb
  have hxC : x ∉ Sphere.F C := fun h => by
    have := Sphere.add_mem_F_of_mem_closure_F hCo hconv h hnx
    rw [add_neg_cancel] at this
    exact Sphere.zero_notMem_F C this
  have hnxC : -x ∉ Sphere.F C := fun h => by
    have := Sphere.add_mem_F_of_mem_closure_F hCo hconv h hx
    rw [neg_add_cancel] at this
    exact Sphere.zero_notMem_F C this
  refine ⟨hline, hxp, hsub, ?_, ?_⟩
  · rw [hCo.frontier_eq]
    refine ⟨closure_mono hsub ?_, fun h => hxC ⟨hx0, h⟩⟩
    convert Sphere.mk_smul_mem_closure_halfLine hxp (one_ne_zero (α := ℝ)) using 1
    exact Sphere.mk_eq_mk_of_eq' (one_smul ℝ x).symm
  · rw [hCo.frontier_eq, Sphere.neg_mk]
    refine ⟨closure_mono hsub ?_, fun h => hnxC ⟨neg_ne_zero.2 hx0, h⟩⟩
    convert Sphere.mk_smul_mem_closure_halfLine hxp (neg_ne_zero.2 (one_ne_zero (α := ℝ))) using 1
    exact Sphere.mk_eq_mk_of_eq' (by rw [neg_smul, one_smul])

/-- **An open convex part of `S(n)` other than `S(n)` is strict** (Déf. 8, Déf. 9): if `m, -m ∈ C`,
the convex `F(C) ∪ {O}` contains a ball around `O`, so every ray is in `C`. -/
theorem Sphere.isStrictConvexPart_of_isOpen {C : Set (S n)} (hCo : IsOpen C)
    (hC : Sphere.IsConvexPart C) (hCu : C ≠ univ) : Sphere.IsStrictConvexPart C := by
  refine ⟨hC, fun m hm hnm => hCu ?_⟩
  have hFo : IsOpen (Sphere.F C) := Sphere.isOpen_iff_F.1 hCo
  obtain ⟨v, hv0, rfl⟩ := Sphere.exists_isRep m
  have hvF : v ∈ Sphere.F C := ⟨hv0, hm⟩
  have hnvF : -v ∈ Sphere.F C := ⟨neg_ne_zero.2 hv0, by rw [← Sphere.neg_mk]; exact hnm⟩
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.1 hFo v hvF
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.1 hFo (-v) hnvF
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  -- every `w ≠ 0` with `‖w‖ < ε` is in `F(C)`: `w = ½ (v + w) + ½ (-v + w)`
  have hball : ∀ w : Fin (n + 1) → ℝ, ‖w‖ < min ε₁ ε₂ → w ≠ 0 → w ∈ Sphere.F C := by
    intro w hw hw0
    have ha : v + w ∈ Sphere.F C := h₁ (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hw.trans_le (min_le_left _ _))
    have hb : -v + w ∈ Sphere.F C := h₂ (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hw.trans_le (min_le_right _ _))
    have hmid := hC (mem_insert_of_mem _ ha) (mem_insert_of_mem _ hb)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have heq : (1 / 2 : ℝ) • (v + w) + (1 / 2 : ℝ) • (-v + w) = w := by module
    rw [heq] at hmid
    exact (mem_insert_iff.1 hmid).resolve_left hw0
  -- so every ray is in `C`
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨u, hu0, rfl⟩ := Sphere.exists_isRep x
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hc : 0 < min ε₁ ε₂ / 2 / ‖u‖ := by positivity
  have hcu : (min ε₁ ε₂ / 2 / ‖u‖) • u ∈ Sphere.F C := hball _ (by
    rw [norm_smul, Real.norm_of_nonneg hc.le, div_mul_cancel₀ _ hun.ne']
    linarith) (smul_ne_zero hc.ne' hu0)
  have hu := Sphere.smul_mem_F hcu (inv_pos.2 hc)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hu
  exact (Sphere.mk_mem_iff_mem_F hu0).2 hu

/-- **The demi-droite lemma** (l.605–607, « Si $V$ n'est pas l'intérieur d'un corps convexe, on
peut trouver dans $V$ une demi-droite $L$, c'est-à-dire une portion de droite limitée à deux
points diamétralement opposés de la frontière de $V$ »), for an open, nonempty, strict convex part
`C` of `S(n)`. -/
theorem exists_demiDroite {C : Set (S n)} (hCo : IsOpen C) (hne : C.Nonempty)
    (hC : Sphere.IsStrictConvexPart C) (hnot : ¬ ∃ K, IsCorpsConvexeS n K ∧ C = interior K) :
    ∃ (x p : Fin (n + 1) → ℝ) (hxp : LinearIndependent ℝ ![x, p]),
      Sphere.halfLine x p ⊆ C ∧ Sphere.mk x (hxp.ne_zero 0) ∈ frontier C ∧
        -Sphere.mk x (hxp.ne_zero 0) ∈ frontier C := by
  have hconv := Sphere.isStrictConvexPart_iff_convex_F.1 hC
  by_cases hsal : ∀ x ∈ closure (Sphere.F C), -x ∈ closure (Sphere.F C) → x = 0
  · obtain ⟨hK, hint⟩ := isCorpsConvexeS_closure_of_salient hCo hne hconv hsal
    exact absurd ⟨closure C, hK, hint.symm⟩ hnot
  push Not at hsal
  obtain ⟨x, hx, hnx, hx0⟩ := hsal
  obtain ⟨m, hm⟩ := hne
  obtain ⟨p, hp0, rfl⟩ := Sphere.exists_isRep m
  obtain ⟨-, hxp, hsub, h1, h2⟩ := demiDroite_of_not_salient hCo hconv hx0 hx hnx ⟨hp0, hm⟩
  exact ⟨x, p, hxp, hsub, h1, h2⟩

/-- **The demi-droite lemma, with the paper's hypothesis** « $V$ convexe » (3°) and `V ≠ S(n)`,
which the lemma needs (`univ_not_demiDroite`): an open, nonempty convex part of `S(n)` other than
`S(n)`, not the interior of a convex body, contains a half-line with its two ends on its
frontier. -/
theorem exists_demiDroite_of_ne_univ {C : Set (S n)} (hCo : IsOpen C) (hne : C.Nonempty)
    (hC : Sphere.IsConvexPart C) (hCu : C ≠ univ)
    (hnot : ¬ ∃ K, IsCorpsConvexeS n K ∧ C = interior K) :
    ∃ (x p : Fin (n + 1) → ℝ) (hxp : LinearIndependent ℝ ![x, p]),
      Sphere.halfLine x p ⊆ C ∧ Sphere.mk x (hxp.ne_zero 0) ∈ frontier C ∧
        -Sphere.mk x (hxp.ne_zero 0) ∈ frontier C :=
  exists_demiDroite hCo hne (Sphere.isStrictConvexPart_of_isOpen hCo hC hCu) hnot

/-- **The demi-droite lemma is a characterisation**: an open, nonempty, strict convex part of
`S(n)` is the interior of a convex body iff it contains no half-line. -/
theorem eq_interior_corpsConvexe_iff_not_demiDroite {C : Set (S n)} (hCo : IsOpen C)
    (hne : C.Nonempty) (hC : Sphere.IsStrictConvexPart C) :
    (∃ K, IsCorpsConvexeS n K ∧ C = interior K) ↔
      ¬ ∃ (x p : Fin (n + 1) → ℝ), LinearIndependent ℝ ![x, p] ∧ Sphere.halfLine x p ⊆ C := by
  constructor
  · rintro ⟨K, hK, rfl⟩ ⟨x, p, hxp, hsub⟩
    have hKc : IsClosed K := hK.2.1.isClosed
    have hcl : closure (Sphere.halfLine x p) ⊆ K := closure_minimal (hsub.trans interior_subset) hKc
    have h1 := hcl (Sphere.mk_smul_mem_closure_halfLine hxp (one_ne_zero (α := ℝ)))
    have h2 := hcl (Sphere.mk_smul_mem_closure_halfLine hxp (neg_ne_zero.2 (one_ne_zero (α := ℝ))))
    refine hK.1.2 _ h1 ?_
    convert h2 using 1
    rw [Sphere.neg_mk]
    exact Sphere.mk_eq_mk_of_eq' (by rw [neg_smul])
  · intro h
    by_contra hnot
    obtain ⟨x, p, hxp, hsub, -⟩ := exists_demiDroite hCo hne hC hnot
    exact h ⟨x, p, hxp, hsub⟩

/-- **The demi-droite lemma needs « strict »** (equivalently `C ≠ S(n)`): `S(n)` is an open convex
part (Déf. 8), not the interior of a convex body, and its frontier is empty, so it contains no
« portion de droite limitée à deux points … de la frontière ». -/
theorem univ_not_demiDroite :
    IsOpen (univ : Set (S n)) ∧ Sphere.IsConvexPart (univ : Set (S n)) ∧
      (¬ ∃ K, IsCorpsConvexeS n K ∧ (univ : Set (S n)) = interior K) ∧
      frontier (univ : Set (S n)) = ∅ := by
  refine ⟨isOpen_univ, Sphere.isConvexPart_iff_isSegConvex.2 Sphere.isSegConvex_univ, ?_,
    frontier_univ⟩
  rintro ⟨K, hK, hKu⟩
  have hK' : K = univ := eq_univ_of_univ_subset (hKu ▸ interior_subset)
  obtain ⟨m⟩ := (inferInstance : Nonempty (S n))
  exact hK.1.2 m (hK' ▸ mem_univ m) (hK' ▸ mem_univ _)

/-- **Non-vacuity of the demi-droite lemma**: the open hemisphere `H₀ = {x₁ > 0}` of `S(1)` is an
open, nonempty, strict convex part which is not the interior of a convex body; the half-line
`s({a e₀ + b e₁ | b > 0})` lies in it. -/
theorem demiDroite_hemisphere :
    IsOpen (Sphere.openHemisphere (Sphere.lastForm 1)) ∧
      (Sphere.openHemisphere (Sphere.lastForm 1)).Nonempty ∧
      Sphere.IsStrictConvexPart (Sphere.openHemisphere (Sphere.lastForm 1)) ∧
      (∃ (x p : Fin (1 + 1) → ℝ), LinearIndependent ℝ ![x, p] ∧
        Sphere.halfLine x p ⊆ Sphere.openHemisphere (Sphere.lastForm 1)) ∧
      ¬ ∃ K, IsCorpsConvexeS 1 K ∧ Sphere.openHemisphere (Sphere.lastForm 1) = interior K := by
  have hF : Sphere.F (Sphere.openHemisphere (Sphere.lastForm 1)) =
      {v : Fin (1 + 1) → ℝ | 0 < v (Fin.last 1)} := by
    rw [Sphere.F_openHemisphere]
    rfl
  have hHo : IsOpen (Sphere.openHemisphere (Sphere.lastForm 1)) :=
    Sphere.isOpen_iff_F.2 (by rw [hF]; exact isOpen_lt continuous_const (continuous_apply _))
  have hp0 : (Pi.single 1 1 : Fin (1 + 1) → ℝ) ≠ 0 := fun h => by
    simpa using congrFun h 1
  have hpH : Sphere.mk _ hp0 ∈ Sphere.openHemisphere (Sphere.lastForm 1) :=
    (Sphere.mk_mem_openHemisphere hp0).2 (by simp [Sphere.lastForm_apply])
  have hHs : Sphere.IsStrictConvexPart (Sphere.openHemisphere (Sphere.lastForm 1)) :=
    Sphere.isStrictConvexPart_iff_convex_F.2 (by
      rw [hF]
      exact convex_halfSpace_gt (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + 1) => ℝ)
        (Fin.last 1)).isLinear 0)
  have hline : ∃ (x p : Fin (1 + 1) → ℝ), LinearIndependent ℝ ![x, p] ∧
      Sphere.halfLine x p ⊆ Sphere.openHemisphere (Sphere.lastForm 1) := by
    refine ⟨Pi.single 0 1, Pi.single 1 1, ?_, ?_⟩
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have h0 := congrFun hst 0
      have h1 := congrFun hst 1
      simp at h0 h1
      exact ⟨h0, h1⟩
    · intro y hy
      induction y using Sphere.ind with
      | h u hu =>
        obtain ⟨a, b, hb, rfl⟩ := (Sphere.mk_mem_halfLine hu).1 hy
        refine (Sphere.mk_mem_openHemisphere hu).2 ?_
        simpa [Sphere.lastForm_apply] using hb
  refine ⟨hHo, ⟨_, hpH⟩, hHs, hline, ?_⟩
  rw [eq_interior_corpsConvexe_iff_not_demiDroite hHo ⟨_, hpH⟩ hHs, not_not]
  obtain ⟨x, p, hxp, hsub⟩ := hline
  exact ⟨x, p, hxp, hsub⟩

end DemiDroite

/-! ### 2°–4° -/

section Theoreme

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- A loop homotopic to the constant loop, read at an equal base point. -/
theorem path_homotopic_refl_of_eq {X : Type*} [TopologicalSpace X] {x y : X} (h : y = x)
    (γ : Path x x) (δ ε : Path y y) (hδ : ∀ t, δ t = γ t) (hε : ∀ t, ε t = y)
    (hh : δ.Homotopic ε) : γ.Homotopic (Path.refl x) := by
  subst h
  have h1 : δ = γ := Path.ext (funext hδ)
  have h2 : ε = Path.refl y := Path.ext (funext hε)
  rw [← h1, ← h2]
  exact hh

/-- **2°** (`bzthm:c2s3t1_poche_balayable`, l.526, proof l.596–598): in a connected sweepable `V`
with a pocket `(P, H̊, φ, z)`, if `P` is simply connected, so is `V`. -/
theorem theoreme_deuxieme [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) (hsc : SimplyConnectedSpace P) : SimplyConnectedSpace V := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : ConnectedSpace V := { toNonempty := ⟨x₀⟩ }
  haveI : LocPathConnectedSpace V := locPathConnectedSpace_of_proj (n := n)
  haveI : PathConnectedSpace V := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x γ => ?_⟩
  -- Prop. 7: an automorphism `g` moves the compact `L = γ(I)` into `P`
  obtain ⟨g, -, hg⟩ := compact_dans_poche (G := ⊤) hbal hP (isCompact_range γ.continuous)
  have hgγ : ∀ t, g • γ t ∈ P := fun t => hg (smul_mem_smul_set (mem_range_self t))
  -- the loop `g L` is null-homotopic in `P`, hence in `V`
  have hPsc : IsSimplyConnected P := hsc
  obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.1 hPsc).2 (g • x)
    (γ.map (continuous_const_smul g)) hgγ
  have h1 : (γ.map (continuous_const_smul g)).Homotopic (Path.refl (g • x)) := ⟨F⟩
  -- and `g⁻¹` carries the null-homotopy back to `L`
  have h2 := h1.map ⟨fun y => g⁻¹ • y, continuous_const_smul _⟩
  exact path_homotopic_refl_of_eq (inv_smul_smul g x) γ _ _
    (fun t => inv_smul_smul g (γ t)) (fun _ => rfl) h2

/-- **`φ̃(V)` has no pair of diametrically opposite points**, for every pocket: two such points
would be moved by one `γ ∈ GS(n, ℝ)` (with `φ̃ ∘ g = γ ∘ φ̃`, `gM, gN ∈ P`) into `φ(P) ⊆ H̊`. -/
theorem neg_notMem_range_of_poche [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) {p : V → S n} (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P)
    (M N : V) : p N ≠ -p M := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  intro hMN
  obtain ⟨g, -, hgM, hgN⟩ := deux_points_dans_poche (G := ⊤) hbal hP M N
  have hpg : IsDeveloping (GSR n) (fun y => p (g • y)) :=
    isDeveloping_iff_isGXMorphism.2 ((isDeveloping_iff_isGXMorphism.1 hp).comp g.isGXMorphism)
  obtain ⟨γ, hγ, -⟩ := hp.existsUnique_smul_eq hpg
  have h1 : φ (g • N) = -φ (g • M) := by
    rw [← hpφ hgN, ← hpφ hgM, hγ N, hγ M, hMN, Sphere.GSE.smul_neg]
  exact Sphere.ne_neg_of_mem_openHemisphere (hP.mapsTo_hemi hgM) (hP.mapsTo_hemi hgN) h1

/-- **3°** (l.528–529, proof l.600–603): if the pocket is a shell (`φ(P)` convex), then `φ̃(V)` is
a convex part of `S(n)`, and even a strict one (Déf. 9), for the chart `φ̃` of 1° (every developing
map equal to `φ` on `P`). -/
theorem theoreme_troisieme [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hC : IsCoqueProj P l φ z) {p : V → S n} (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) :
    Sphere.IsStrictConvexPart (range p) := by
  have hP := hC.1
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  have hφconv : Sphere.IsSegConvex (φ '' P) := Sphere.isConvexPart_iff_isSegConvex.1 hC.2
  rw [Sphere.isStrictConvexPart_iff_isSegConvex]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩ - y hy
    -- `g` with `gM, gN ∈ P` (Prop. 7, corollary), `γ` with `φ̃ ∘ g = γ ∘ φ̃`
    obtain ⟨g, -, hgM, hgN⟩ := deux_points_dans_poche (G := ⊤) hbal hP M N
    have hpg : IsDeveloping (GSR n) (fun y => p (g • y)) :=
      isDeveloping_iff_isGXMorphism.2 ((isDeveloping_iff_isGXMorphism.1 hp).comp g.isGXMorphism)
    obtain ⟨γ, hγ, -⟩ := hp.existsUnique_smul_eq hpg
    -- the segment `(gM, gN)` lies in the convex `φ(P)`
    have hseg : Sphere.closedSeg (γ • p M) (γ • p N) ⊆ φ '' P := by
      rw [← hγ M, ← hγ N, hpφ hgM, hpφ hgN]
      exact hφconv _ (mem_image_of_mem φ hgM) _ (mem_image_of_mem φ hgN)
        (Sphere.ne_neg_of_mem_openHemisphere (hP.mapsTo_hemi hgM) (hP.mapsTo_hemi hgN))
    have hγy : γ • y ∈ φ '' P := by
      apply hseg
      rw [← Sphere.GSE.image_smul_closedSeg]
      exact mem_image_of_mem _ hy
    -- so `(M, N) = γ⁻¹ (gM, gN) ⊆ φ̃(g⁻¹ P)`
    obtain ⟨Q, hQ, hQy⟩ := hγy
    refine ⟨g⁻¹ • Q, ?_⟩
    apply MulAction.injective γ
    show γ • p (g⁻¹ • Q) = γ • y
    rw [← hγ, smul_inv_smul, hpφ hQ, hQy]
  · rintro _ ⟨M, rfl⟩ ⟨N, hN⟩
    exact neg_notMem_range_of_poche hbal hP hp hpφ M N hN

/-- **3°, in the form its proof states** (l.600–601, « il faut montrer que, dans $V$, il existe un
segment fermé d'extrémités $M$, $N$ »): if the pocket is a shell, any two points of `V` are the
ends of a segment of `V` (Ch. 1, Déf. 14). -/
theorem exists_isProjSegment_of_coque [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hC : IsCoqueProj P l φ z) (M N : V) : ∃ Sg : Set V, IsProjSegment n Sg M N := by
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche hbal hC.1
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  have ht : φ'.target = range φ' := by rw [← φ'.image_source_eq_target, hs, image_univ]
  have hstr := theoreme_troisieme hbal hC hp hφ'φ
  have hab : φ' N ≠ -φ' M := neg_notMem_range_of_poche hbal hC.1 hp hφ'φ M N
  have hsub : Sphere.closedSeg (φ' M) (φ' N) ⊆ φ'.target := by
    rw [ht]
    exact (Sphere.isStrictConvexPart_iff_isSegConvex.1 hstr).1 _ (mem_range_self M) _
      (mem_range_self N) hab
  have hseg := isProjSegment_of_chart hφ' hab hsub
  rw [φ'.left_inv (hs.symm ▸ mem_univ M), φ'.left_inv (hs.symm ▸ mem_univ N)] at hseg
  exact ⟨_, hseg⟩

/-- **4°** (l.531–532, proof l.605–619): if the pocket is a strict shell, then `φ̃(V)` is the
interior of a convex body of `S(n)`, namely of its closure, for the chart `φ̃` of 1° (every
developing map equal to `φ` on `P`). -/
theorem theoreme_quatrieme [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hC : IsCoqueStricteProj P l φ z) {p : V → S n} (hp : IsDeveloping (GSR n) p)
    (hpφ : EqOn p φ P) :
    IsCorpsConvexeS n (closure (range p)) ∧ interior (closure (range p)) = range p := by
  have hP := hC.1.1
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  haveI : Nonempty V := ⟨x₀⟩
  have hstr := theoreme_troisieme hbal hC.1 hp hpφ
  have hconv : Convex ℝ (Sphere.F (range p)) := Sphere.isStrictConvexPart_iff_convex_F.1 hstr
  have hWo : IsOpen (range p) := hp.isLocalHomeomorph.isOpenMap.isOpen_range
  refine isCorpsConvexeS_closure_of_salient hWo (range_nonempty p) hconv ?_
  -- if `±x ∈ closure F(φ̃(V))`, `x ≠ 0`, the demi-droite through a point of `φ(P)` gives a line of
  -- `H̊` inside `φ(P)`
  intro x hx hnx
  by_contra hx0
  obtain ⟨φ', hφ', hs, ht, he⟩ :=
    exists_chart_of_injective hp (injective_of_isDeveloping_of_poche hbal hP hp)
  subst he
  have hm₀ : φ' x₀ ∈ Sphere.openHemisphere l := hpφ hx₀ ▸ hP.mapsTo_hemi hx₀
  set m : Sphere.openHemisphere l := ⟨φ' x₀, hm₀⟩ with hm
  set v₀ := Sphere.nrep l (φ' x₀) with hv₀
  have hlv₀ : l v₀ = 1 := Sphere.l_nrep hm₀
  have hv₀0 : v₀ ≠ 0 := Sphere.nrep_ne_zero hm₀
  have hv₀F : v₀ ∈ Sphere.F (range φ') :=
    ⟨hv₀0, by rw [Sphere.mk_nrep hm₀]; exact mem_range_self x₀⟩
  -- the demi-droite `s(v₀ + ℝ x)` through `φ(M₀)`, `M₀ = x₀ ∈ P`
  obtain ⟨hline, -⟩ := demiDroite_of_not_salient hWo hconv hx0 hx hnx hv₀F
  have hgerm : (φ' : V → S n) =ᶠ[𝓝 x₀] φ :=
    Filter.eventuallyEq_of_mem (hP.isOpen.mem_nhds hx₀) hpφ
  -- condition `b` along the segment `(M₀, N_t)` of `V`, `φ̃(N_t) = s(v₀ + t x)`
  have hb : ∀ t : ℝ, ∃ N : V, φ' N = Sphere.mk (v₀ + t • x) (hline t).1 ∧
      φ' N ∈ Sphere.openHemisphere l ∧
      ∀ hN : φ' N ∈ Sphere.openHemisphere l, z ⟨φ' N, hN⟩ < 1 → N ∈ P := by
    intro t
    obtain ⟨N, hN⟩ := (hline t).2
    have hab : φ' N ≠ -φ' x₀ := neg_notMem_range_of_poche hbal hP hp hpφ x₀ N
    have hsub : Sphere.closedSeg (φ' x₀) (φ' N) ⊆ φ'.target := by
      rw [ht]
      exact (Sphere.isStrictConvexPart_iff_isSegConvex.1 hstr).1 _ (mem_range_self _) _
        (mem_range_self _) hab
    have hseg := isProjSegment_of_chart hφ' hab hsub
    rw [φ'.left_inv (hs.symm ▸ mem_univ x₀), φ'.left_inv (hs.symm ▸ mem_univ N)] at hseg
    have h := hP.mem_of_segment _ x₀ N hseg hx₀ φ' hφ' (hs.symm ▸ subset_univ _) hgerm
    exact ⟨N, hN, h.1 (mem_image_of_mem φ' hseg.right_mem), h.2⟩
  -- the demi-droite lies in `H̊`: `l x = 0`
  have hlpos : ∀ t : ℝ, 0 < 1 + t * l x := by
    intro t
    obtain ⟨N, hN, hH, -⟩ := hb t
    rw [hN, Sphere.mk_mem_openHemisphere] at hH
    rwa [map_add, map_smul, hlv₀, smul_eq_mul] at hH
  have hlx : l x = 0 := by
    by_contra hne
    have := hlpos (-2 / l x)
    rw [div_mul_cancel₀ _ hne] at this
    linarith
  -- so it is the line `m + ℝ u` of the affine space `H̊` (Remarque 1)
  let u : Sphere.HemiTrans l := (Sphere.lbar l).smulRight (⟨x, hlx⟩ : LinearMap.ker l)
  have hum : (u (Sphere.hq l (Sphere.nrep l (m : S n))) : Fin (n + 1) → ℝ) = x := by
    simp only [u, m, LinearMap.smulRight_apply, Sphere.lbar_hq, ← hv₀, hlv₀, one_smul]
  have hu : u ≠ 0 := by
    intro h0
    have : (u (Sphere.hq l (Sphere.nrep l (m : S n))) : Fin (n + 1) → ℝ) = 0 := by
      rw [h0]; rfl
    exact hx0 (hum ▸ this)
  have hcoe : ∀ t : ℝ, ((t • u +ᵥ m : Sphere.openHemisphere l) : S n) =
      Sphere.mk (v₀ + t • x) (hline t).1 := by
    intro t
    rw [Sphere.coe_smul_vadd]
    exact Sphere.mk_eq_mk_of_eq' (by rw [hum]; exact add_comm _ _)
  -- condition `b`: its points of cote `< 1` are in `φ(P)`, where `z ≥ 0`
  have hmemP : ∀ t : ℝ, z (t • u +ᵥ m) < 1 →
      ((t • u +ᵥ m : Sphere.openHemisphere l) : S n) ∈ φ '' P := by
    intro t hzt
    obtain ⟨N, hN, hH, hz⟩ := hb t
    have hNe : (⟨φ' N, hH⟩ : Sphere.openHemisphere l) = t • u +ᵥ m :=
      Subtype.ext (by rw [hcoe]; exact hN)
    have hNP : N ∈ P := hz hH (by rw [hNe]; exact hzt)
    exact ⟨N, hNP, by rw [← hpφ hNP, hN, hcoe]⟩
  have hz0 : ∀ t : ℝ, z (t • u +ᵥ m) < 1 → 0 ≤ z (t • u +ᵥ m) := fun t hzt =>
    hP.isGLB.1 ⟨t • u +ᵥ m, hmemP t hzt, rfl⟩
  -- an affine function bounded below on a line is constant, `= z(φ(M₀)) < 1`
  have hzm : z m < 1 := by
    have := hP.cote_lt_one hx₀
    convert this using 2
    exact Subtype.ext (hpφ hx₀)
  have hcz : ∀ t : ℝ, z (t • u +ᵥ m) = t * z.linear u + z m := fun t => by
    rw [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
  have hc : z.linear u = 0 := by
    by_contra hne
    have h1 := hz0 (-(z m + 1) / z.linear u) (by rw [hcz, div_mul_cancel₀ _ hne]; linarith)
    rw [hcz, div_mul_cancel₀ _ hne] at h1
    linarith
  -- so the whole line is in `φ(P)`, against `¬ ContainsAffLine`
  apply hC.2
  refine ⟨range fun t : ℝ => t • u +ᵥ m, ⟨m, u, hu, rfl⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hmemP t (by rw [hcz, hc, mul_zero, zero_add]; exact hzm)

omit [HasGroupoid V (projGroupoid n)] in
/-- **The pocket of a strict shell is simply connected**: `φ(P)` is the interior of the convex
body `closure φ(P)` (Remarque 2). So 2° applies to every strict shell. -/
theorem simplyConnectedSpace_of_coqueStricte (hC : IsCoqueStricteProj P l φ z) :
    SimplyConnectedSpace P := by
  have hP := hC.1.1
  have hK : IsCorpsConvexeS n (closure (φ '' P)) := hC.1.isCoqueStricte_iff.1 hC
  have hko : IsOpen (φ '' P) := by
    rw [← hP.source_eq, φ.image_source_eq_target]
    exact φ.open_target
  have hkconv : Convex ℝ (Sphere.F (φ '' P)) := Sphere.isStrictConvexPart_iff_convex_F.1
    ⟨hC.1.2, fun m hm hm' => Sphere.ne_neg_of_mem_openHemisphere (hP.image_subset hm)
      (hP.image_subset hm') rfl⟩
  have hint : interior (closure (φ '' P)) = φ '' P := interior_closure_eq_of_convex_F hko hkconv
  haveI := simplyConnectedSpace_corpsInterior hK
  have htgt : φ.target = (corpsInterior (closure (φ '' P)) : Set (S n)) := by
    rw [TopologicalSpace.Opens.coe_interior, hint, ← hP.source_eq, φ.image_source_eq_target]
  let e : P ≃ₜ corpsInterior (closure (φ '' P)) :=
    ((Homeomorph.setCongr hP.source_eq.symm).trans φ.toHomeomorphSourceTarget).trans
      (Homeomorph.setCongr htgt)
  exact e.toHomotopyEquiv.simplyConnectedSpace

/-- **The Theorem** (`bzthm:c2s3t1_poche_balayable`, l.517–533), 1° in component form with 2°–4°:
a connected sweepable `V` with a pocket `(P, H̊, φ, z)` has a compatible chart `φ̃` with source
`V`, inducing `φ` on `P`; `P` is the connected component of each of its points in `φ̃⁻¹(D)`,
`D = {z < 1}`, and `P = φ̃⁻¹(D ∩ φ̃(V))` iff `D ∩ φ̃(V)` is preconnected (1°); if `P` is simply
connected so is `V` (2°); if the pocket is a shell, `φ̃(V)` is convex (3°); if it is a strict
shell, `φ̃(V)` is the interior of a convex body (4°). -/
theorem theoreme_poche_balayable [PreconnectedSpace V] (hbal : IsBalayable (GSR n) (S n) V)
    (hP : IsPocheProj P l φ z) :
    ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧
      EqOn φ' φ P ∧ (∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' demiEspace z) x) ∧
      (P = φ' ⁻¹' (demiEspace z ∩ range φ') ↔ IsPreconnected (demiEspace z ∩ range φ')) ∧
      (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧
      (IsCoqueProj P l φ z → Sphere.IsConvexPart (range φ')) ∧
      (IsCoqueStricteProj P l φ z →
        ∃ K : Set (S n), IsCorpsConvexeS n K ∧ range φ' = interior K) := by
  obtain ⟨φ', hφ', hs, hφ'φ, hcomp, hiff⟩ := theoreme_premier hbal hP
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  refine ⟨φ', hφ', hs, hφ'φ, hcomp, hiff, theoreme_deuxieme hbal hP,
    fun hC => (theoreme_troisieme hbal hC hp hφ'φ).1, fun hC => ?_⟩
  obtain ⟨hK, hint⟩ := theoreme_quatrieme hbal hC hp hφ'φ
  exact ⟨_, hK, hint.symm⟩

end Theoreme

/-! ### The printed statements, over the paper's manifolds -/

/-- **The Theorem with 1° in component form** (« $P$ n'est autre que » read as a connected
component, the forward reference l.181–186), 2°–4° as printed, over the paper's manifolds
(Hausdorff, connected, second countable; `V : Type`). -/
def TheoremeComposantePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V], IsBalayable (GSR n) (S n) V →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsPocheProj P l φ z → ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧
        (∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' demiEspace z) x) ∧
        (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧
        (IsCoqueProj P l φ z → Sphere.IsConvexPart (range φ')) ∧
        (IsCoqueStricteProj P l φ z → ∃ K : Set (S n), IsCorpsConvexeS n K ∧ range φ' = interior K)

/-- **The Theorem as printed** (1° with « $P=\tilde{\varphi}^{-1}(D\cap\tilde{\varphi}(V))$ »,
l.522–524 and l.586; 2°–4°), over the paper's manifolds. Equivalent to `ConnexePrinted n`
(`theoremePrinted_iff`), which is open (OQ-71). -/
def TheoremePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V], IsBalayable (GSR n) (S n) V →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsPocheProj P l φ z → ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧ P = φ' ⁻¹' (demiEspace z ∩ range φ') ∧
        (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧
        (IsCoqueProj P l φ z → Sphere.IsConvexPart (range φ')) ∧
        (IsCoqueStricteProj P l φ z → ∃ K : Set (S n), IsCorpsConvexeS n K ∧ range φ' = interior K)

/-- **The Theorem with 1° in component form holds in every dimension**, `n = 0` included. -/
theorem theoremeComposantePrinted (n : ℕ) : TheoremeComposantePrinted n := by
  intro V _ _ _ _ _ _ hbal P l _ φ z hP
  obtain ⟨φ', h1, h2, h3, h4, -, h5, h6, h7⟩ := theoreme_poche_balayable hbal hP
  exact ⟨φ', h1, h2, h3, h4, h5, h6, h7⟩

/-- **The Theorem as printed is exactly the connectedness the proof of 1°c presumes**:
`TheoremePrinted n ↔ ConnexePrinted n` (2°–4° hold unconditionally). -/
theorem theoremePrinted_iff (n : ℕ) : TheoremePrinted n ↔ ConnexePrinted n := by
  constructor
  · intro h
    rw [← premierPrinted_iff]
    intro V _ _ _ _ _ _ hbal P l _ φ z hP
    obtain ⟨φ', h1, h2, h3, h4, -⟩ := h V hbal P l φ z hP
    exact ⟨φ', h1, h2, h3, h4⟩
  · intro h V _ _ _ _ _ _ hbal P l _ φ z hP
    obtain ⟨φ', h1, h2, h3, -, hiff, h5, h6, h7⟩ := theoreme_poche_balayable hbal hP
    exact ⟨φ', h1, h2, h3, hiff.2 (h V hbal P l φ z hP φ' h1 h2 h3), h5, h6, h7⟩

/-! ### Non-vacuity -/

section Model

variable (n : ℕ)

attribute [local instance] projOfAff hasGroupoid_projOfAff

/-- **The Theorem at the model** `ℝⁿ` (canonical projective structure, every `n`): the shell
`(ℝⁿ, H₀, j, 0)` meets the hypotheses of 1°–3°; its pocket `P = V` is simply connected, and the
conclusions hold. -/
theorem theoreme_poche_balayable_model :
    ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (S n))
      (z : Sphere.openHemisphere (Sphere.lastForm n) →ᵃ[ℝ] ℝ),
      IsCoqueProj (univ : Set (Fin n → ℝ)) (Sphere.lastForm n) φ z ∧
      SimplyConnectedSpace (univ : Set (Fin n → ℝ)) ∧
      ∃ φ' : OpenPartialHomeomorph (Fin n → ℝ) (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ univ ∧ SimplyConnectedSpace (Fin n → ℝ) ∧
        Sphere.IsConvexPart (range φ') := by
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm n)
    (Module.finrank_fin_fun ℝ)
  have hCa : IsCoqueAff (univ : Set (Fin n → ℝ)) (OpenPartialHomeomorph.refl _) 0 :=
    ⟨isPocheAff_model n, by simpa using (convex_univ : Convex ℝ (univ : Set (Fin n → ℝ)))⟩
  have hC := hCa.toCoqueProj e.symm
  haveI : SimplyConnectedSpace (univ : Set (Fin n → ℝ)) :=
    haveI := (convex_univ : Convex ℝ (univ : Set (Fin n → ℝ))).contractibleSpace univ_nonempty
    inferInstance
  obtain ⟨φ', h1, h2, h3, -, -, h5, h6, -⟩ := theoreme_poche_balayable (isBalayable_model n) hC.1
  exact ⟨_, _, hC, inferInstance, φ', h1, h2, h3, h5 inferInstance, h6 hC⟩

/-- **The strict shell `]0, 1[` of `]0, ∞[`, with `P ≠ V`** (the affine strict shell of
`exists_isCoqueStricteAff_demiDroite`, `Chapter2/Poches.lean`, with `P ≠ univ` recorded): the
component `P = ]0, 1[` of `z < 1`, `z = x₀`, with the inclusion as chart. -/
theorem exists_isCoqueStricteAff_demiDroite_ne_univ :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (Fin 1 → ℝ)),
      IsCoqueStricteAff P φ (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧
      P ≠ univ := by
  set z : (Fin 1 → ℝ) →ᵃ[ℝ] ℝ := (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).toAffineMap with hz
  let x₀ : demiDroiteOuverte := ⟨fun _ => 1 / 2, show (0 : ℝ) < 1 / 2 by norm_num⟩
  set U := (Subtype.val : demiDroiteOuverte → Fin 1 → ℝ) ⁻¹' {y | z y < 1} with hU
  have himgU : (Subtype.val '' U : Set (Fin 1 → ℝ)) = {x | 0 < x 0 ∧ x 0 < 1} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1⟩, h2, rfl⟩
  have hC : Convex ℝ {x : Fin 1 → ℝ | 0 < x 0 ∧ x 0 < 1} :=
    (convex_Ioo (0 : ℝ) 1).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  have hUconn : IsPreconnected U := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    convert hC.isPreconnected using 1
    exact himgU
  have hx₀ : z (x₀ : Fin 1 → ℝ) < 1 := show (1 / 2 : ℝ) < 1 by norm_num
  have hP : connectedComponentIn U x₀ = U := hUconn.connectedComponentIn hx₀
  have hinf : IsGLB (z '' (Subtype.val '' connectedComponentIn U x₀)) 0 := by
    rw [hP, himgU]
    have : z '' {x : Fin 1 → ℝ | 0 < x 0 ∧ x 0 < 1} = Ioo 0 1 := by
      ext t
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro ht
        exact ⟨fun _ => t, ht, rfl⟩
    rw [this]
    exact isGLB_Ioo zero_lt_one
  obtain ⟨φ, hφeq, hφ⟩ := exemple_poche_affine isDeveloping_val_demiDroiteOuverte z hx₀ hinf
    Subtype.val_injective.injOn
  have hφimg : φ '' connectedComponentIn U x₀ = {x | 0 < x 0 ∧ x 0 < 1} := by
    rw [image_congr hφeq, hP, himgU]
  have hne : connectedComponentIn U x₀ ≠ univ := by
    rw [hP]
    intro h
    have h2 : (⟨fun _ => 2, show (0 : ℝ) < 2 by norm_num⟩ : demiDroiteOuverte) ∈ U :=
      h ▸ mem_univ _
    exact absurd (show (2 : ℝ) < 1 from h2) (by norm_num)
  refine ⟨_, φ, ⟨⟨hφ, by rw [hφimg]; exact hC⟩, ?_⟩, hne⟩
  rintro ⟨A, ⟨p, w, hw, rfl⟩, hA⟩
  rw [hφimg] at hA
  have hw0 : w 0 ≠ 0 := fun h => hw (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
  have h2 := (hA ⟨(2 - p 0) / w 0, rfl⟩).2
  simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hw0] at h2
  linarith

/-- **The Theorem on a strict shell with `P ≠ V`** (`n = 1`): the half-line `]0, ∞[` (canonical
projective structure), sweepable by its homotheties, with the strict shell `P = ]0, 1[`; `P` is
simply connected; the chart `φ̃` of 1° exists, `V` is simply connected (2°), `φ̃(V)` is convex
(3°) and the interior of a convex body (4°). -/
theorem theoreme_poche_balayable_demiDroite :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (S 1))
      (z : Sphere.openHemisphere (Sphere.lastForm 1) →ᵃ[ℝ] ℝ),
      IsCoqueStricteProj P (Sphere.lastForm 1) φ z ∧ P ≠ univ ∧ SimplyConnectedSpace P ∧
      ∃ φ' : OpenPartialHomeomorph demiDroiteOuverte (S 1), IsCompatibleChart (GSR 1) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧
        (∀ x ∈ P, P = connectedComponentIn (φ' ⁻¹' demiEspace z) x) ∧
        SimplyConnectedSpace demiDroiteOuverte ∧ Sphere.IsConvexPart (range φ') ∧
        ∃ K : Set (S 1), IsCorpsConvexeS 1 K ∧ range φ' = interior K := by
  obtain ⟨P, φ, hCa, hne⟩ := exists_isCoqueStricteAff_demiDroite_ne_univ
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm 1) (Module.finrank_fin_fun ℝ)
  have hC := hCa.toCoqueStricteProj e.symm
  have hconv : IsPreconnected ((demiDroiteOuverte : Set (Fin 1 → ℝ))) :=
    ((convex_Ioi (0 : ℝ)).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).isPreconnected
  haveI : PreconnectedSpace demiDroiteOuverte := Subtype.preconnectedSpace hconv
  have hsc := simplyConnectedSpace_of_coqueStricte hC
  obtain ⟨φ', h1, h2, h3, h4, -, h5, h6, h7⟩ :=
    theoreme_poche_balayable isBalayable_demiDroite hC.1.1
  exact ⟨P, _, _, hC, hne, hsc, φ', h1, h2, h3, h4, h5 hsc, h6 hC.1, h7 hC⟩

end Model

end Benzecri
