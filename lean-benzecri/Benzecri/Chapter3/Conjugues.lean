import Benzecri.Chapter3.Fibres
import Mathlib.LinearAlgebra.Projection

/-!
# Chapter 3 § 2 — Théorème 1, its Lemme and Corollaire: conjugate pairs and their projections

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal pp. 265–267; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-conjugues. Any real vector space `E`, any dimension, no topology.

* **`bzthm:c3s2t1_conjugues_intersection`** — `benzecri1960_ch3.tex:452` (Théorème 1,
  l.452–456, proof l.460–463 and l.480–501): `Benzecri.theoreme1` (as printed, reading (a) of OQ-163, the
  formalization of record of Déf. 4: `L, L', D, D'` distinguished, `SontConjugues W L L'`,
  `SontConjugues W D D'`, no supplementarity), from `Benzecri.theoreme1_distingues` (the same
  with `D'` dropped); reading (b), the supplementary pairs, `Benzecri.theoreme1_supplementaires`
  (also: `L ⊓ D`, `L' ⊓ D` supplementary in `D`, `span (W ∩ D) = D`); reading (c), Déf. 1's sum,
  `Benzecri.theoreme1_sommeConvexes`. True under all three readings.
* `bzlem:c3s2l1_projection_somme` — `benzecri1960_ch3.tex:466` (Lemme, l.466–469, proof
  l.471–477), NOT marked (reading (b) of OQ-163, see SCOPE): `Benzecri.lemme_projection_somme`.
* `bzcor:c3s2t1c_projections_commutent` — `benzecri1960_ch3.tex:503` (Corollaire, l.503–509,
  proof l.511–521), NOT marked (reading (b) of OQ-163, see SCOPE):
  `Benzecri.corollaire_projections_commutent`; the four-fold decomposition of the proof,
  `Benzecri.corollaire_decomposition`.

The key step of the printed proof (l.481), « `P_L(a)` et `P_{L'}(a)` appartiennent à `D` », is
`Benzecri.projection_mem_of_mem_inter` (for `a ∈ W ∩ D`) and `Benzecri.projection_mem_of_mem`
(for `a ∈ D`, through `span (D ∩ W) = D`).

Instance: the cube `[−1,1]³` with `L = ⟨e₁⟩`, `D = ⟨e₁, e₂⟩` and their coordinate complements
(`Benzecri.cube3_theoreme1`, `Benzecri.cube3_corollaire`).

> **Théorème 1.** Soient $W$ un convexe de $E$ contenant l'origine $O$, engendrant $E$, et ne
> contenant aucune droite, $L$ et $L'$, $D$ et $D'$ deux couples de sous-espaces distingués
> conjugués relativement à $W$. Alors $L\cap D$ et $L'\cap D$ sont conjugués relativement à
> $W\cap D$.
>
> Désignons par $P_L$ (resp. $P_{L'}$, $P_D$, $P_{D'}$) la projection sur $L$ (resp. $L'$, $D$,
> $D'$) parallèlement à $L'$ (resp. $L$, $D'$, $D$); la démonstration repose sur le
>
> **Lemme.** Soient $a$ et $b$ deux éléments tels que $b$ et $a+b$ appartiennent à $W$. Alors
> $u=P_L(a)+b\in W$.
>
> **Corollaire.** Soient $W$ un convexe de $E$ contenant $O$, engendrant $E$, ne contenant aucune
> droite, $(L, L')$, $(D, D')$ deux couples de sous-espaces conjugués relativement à $W$, $P_L$
> (resp. $P_{L'}$, $P_D$, $P_{D'}$) la projection sur $L$ (resp. $L'$, $D$, $D'$) parallèlement
> à $L'$ (resp. $L$, $D'$, $D$) : $P_L$, $P_{L'}$, $P_D$, $P_{D'}$ commutent deux à deux, et
> l'on a $\text{Identité}=P_LP_D+P_LP_{D'}+P_{L'}P_D+P_{L'}P_{D'}$.

## The proof formalized

The Lemme (`lemme_projection_somme`) as printed: `P_L(a + b)` and `P_{L'}(b)` are the
components of points of `W = L ∩ W + L' ∩ W`, so lie in `W` (`projection_mem_inter`), and
`u = P_L u + P_{L'} u`. Théorème 1 under (b) as printed: for `a ∈ W ∩ D` the translations
`P_{D'}P_L(a)`, `P_{D'}P_{L'}(a)` are opposite and leave `D' ∩ W` stable (the Lemme twice), so
vanish (`eq_zero_of_vadd_eq`: `D' ∩ W` contains no line); then `P_L` maps `D` into `D` because
`D ∩ W` spans `D` (`span_inter_eq_of_conjugues`). Théorème 1 under (a), which the printed proof
does not cover (it uses `P_L`, which needs `L ⊕ L' = E`): write `a ∈ W ∩ D` as `x + y`,
`x ∈ L ∩ W`, `y ∈ L' ∩ W`, and project along the supplementary conjugate `N` of `D`: `P_D`
maps `L` into `L` and `L'` into `L'` (the (b) step applied to `(D, N)` and the supplementary
conjugates of `L`, `L'`), so `a = P_D x + P_D y` with `P_D x ∈ L ∩ D ∩ W`, `P_D y ∈ L' ∩ D ∩ W`.
The Corollaire: `P_L` preserves `D` and `D'`, hence commutes with `P_D`
(`commute_projection_of_mapsTo`); the identity is `(P_L + P_{L'})(P_D + P_{D'}) = Id`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `E` (real vector space) | ✓ carried: any real vector space, any dimension |
| Th. 1: `W` convexe, contenant `O`, engendrant `E`, sans droite | ✓ carried (`Convex ℝ W`, `0 ∈ W`, `Submodule.span ℝ W = ⊤`, `¬ ContientDroite W`) |
| Th. 1: `L, L'`, `D, D'` distingués (Déf. 3) | ✓ carried by `theoreme1`; ⚠ weakened in `theoreme1_distingues` (`D'` not used); in (b) implied by `IsCompl ∧ SontConjugues` |
| Th. 1: « conjugués » (Déf. 4) | (a) `SontConjugues` (record); (b) `IsCompl ∧ SontConjugues`; (c) `IsSommeConvexes W ![L ∩ W, L' ∩ W]` |
| Th. 1's conclusion « conjugués relativement à `W ∩ D` » | (a) `SontConjugues (W ∩ D) (L ⊓ D) (L' ⊓ D)` and `L ⊓ D ⊔ L' ⊓ D = D`; (b) the same, `Disjoint`, `span (W ∩ D) = D`; (c) `IsSommeConvexes (W ∩ D) ![…]` |
| Lemme: `P_L` « parallèlement à `L'` » | ⚠ strengthened against reading (a) (OQ-163): `L.projection L' h`, `h : IsCompl L L'` (the projection exists only for a supplementary pair) |
| Lemme: the standing hypotheses on `W` | ⚠ weakened: only `IsCompl L L' ∧ SontConjugues W L L'` is used |
| Cor.: `W` convexe, `∋ O`, engendrant, sans droite; `(L, L')`, `(D, D')` conjugués | ⚠ strengthened against reading (a) (OQ-163): carried in reading (b) |

## SCOPE (disclosed)

* OQ-163 (Déf. 4: (a) as printed, (b) supplementary, (c) Déf. 1's sum) is OPEN. Théorème 1 is
  proved under all three, so its mark does not depend on the ruling; the formalization of record
  is `theoreme1`, reading (a).
* The Lemme and the Corollaire are stated with `IsCompl L L'` (and `IsCompl D D'`), reading (b):
  « la projection sur `L` parallèlement à `L'` » is defined only when `L ⊕ L' = E`. Under (a)
  they have no meaning for a non-supplementary pair (`demiDroite_conjugues_non_supplementaires`).
  They are left unmarked until the ruling; the question is whether the notation `P_L` itself
  carries the supplementarity (then the (b) statements are the printed ones).
* The Corollary's proof's « `V'` » (l.514) is read `D' ∩ W`, as the transcription's comment (l.522) says;
  the four-fold decomposition `W = Σ (L^± ⊓ D^±) ∩ W` of the proof is `corollaire_decomposition`
  (the sum; its uniqueness follows from the four subspaces being independent, not formalized).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function
open scoped Pointwise

namespace Benzecri

section Conjugues

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Projections along a supplementary conjugate -/

/-- A subset of a set with no line has no line. -/
theorem not_contientDroite_mono {W C : Set E} (hd : ¬ ContientDroite W) (hC : C ⊆ W) :
    ¬ ContientDroite C := by
  rintro ⟨x, v, hv, h⟩
  exact hd ⟨x, v, hv, fun t => hC (h t)⟩

/-- For `W = L ∩ W + L' ∩ W` with `L ⊕ L' = E`, the projection on `L` parallel to `L'` maps `W`
into `L ∩ W`. -/
theorem projection_mem_inter {W : Set E} {L L' : Submodule ℝ E} (h : IsCompl L L')
    (hc : SontConjugues W L L') {w : E} (hw : w ∈ W) :
    L.projection L' h w ∈ (L : Set E) ∩ W := by
  have hw' := hw
  rw [hc, Set.mem_add] at hw'
  obtain ⟨x, hx, y, hy, rfl⟩ := hw'
  rw [map_add, Submodule.projection_apply_of_mem_left h hx.1,
    Submodule.projection_apply_of_mem_right h hy.1, add_zero]
  exact hx

/-- **Lemme** (l.466): « Soient `a` et `b` deux éléments tels que `b` et `a+b` appartiennent à
`W`. Alors `u = P_L(a) + b ∈ W` » (reading (b): `P_L` the projection on `L` parallel to `L'`). -/
theorem lemme_projection_somme {W : Set E} {L L' : Submodule ℝ E} (h : IsCompl L L')
    (hc : SontConjugues W L L') {a b : E} (hb : b ∈ W) (hab : a + b ∈ W) :
    L.projection L' h a + b ∈ W := by
  have h1 : L.projection L' h (L.projection L' h a + b) ∈ (L : Set E) ∩ W := by
    rw [map_add, Submodule.projection_apply_of_mem_left h (Submodule.projection_apply_mem h a),
      ← map_add]
    exact projection_mem_inter h hc hab
  have h2 : L'.projection L h.symm (L.projection L' h a + b) ∈ (L' : Set E) ∩ W := by
    rw [map_add, Submodule.projection_apply_of_mem_right h.symm
      (Submodule.projection_apply_mem h a), zero_add]
    exact projection_mem_inter h.symm hc.symm hb
  have e := Submodule.projection_add_projection_eq_self h (L.projection L' h a + b)
  rw [← e, hc]
  exact Set.add_mem_add h1 h2

/-- The key step of Théorème 1 (l.481): for `a ∈ W ∩ D`, `P_L(a) ∈ D`. -/
theorem projection_mem_of_mem_inter {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hd : ¬ ContientDroite W) {L L' D D' : Submodule ℝ E} (hL : IsCompl L L')
    (hcL : SontConjugues W L L') (hD : IsCompl D D') (hcD : SontConjugues W D D') {a : E}
    (ha : a ∈ W ∩ (D : Set E)) : L.projection L' hL a ∈ D := by
  obtain ⟨haW, haD⟩ := ha
  have hCc : Convex ℝ ((D' : Set E) ∩ W) := D'.convex.inter hW
  have h0C : (0 : E) ∈ (D' : Set E) ∩ W := ⟨D'.zero_mem, h0⟩
  have hdC : ¬ ContientDroite ((D' : Set E) ∩ W) :=
    not_contientDroite_mono hd Set.inter_subset_right
  have hsum : D'.projection D hD.symm (L.projection L' hL a) +
      D'.projection D hD.symm (L'.projection L hL.symm a) = 0 := by
    rw [← map_add, Submodule.projection_add_projection_eq_self hL]
    exact Submodule.projection_apply_of_mem_right hD.symm haD
  have stab : ∀ {M M' : Submodule ℝ E} (hM : IsCompl M M'), SontConjugues W M M' →
      ∀ w ∈ (D' : Set E) ∩ W, D'.projection D hD.symm (M.projection M' hM a) + w ∈
        (D' : Set E) ∩ W := by
    intro M M' hM hcM w hw
    have haw : a + w ∈ W := by
      rw [hcD]; exact Set.add_mem_add ⟨haD, haW⟩ hw
    have h1 : M.projection M' hM a + w ∈ W := lemme_projection_somme hM hcM hw.2 haw
    exact ⟨D'.add_mem (Submodule.projection_apply_mem _ _) hw.1,
      lemme_projection_somme hD.symm hcD.symm hw.2 h1⟩
  have hneg : -(D'.projection D hD.symm (L.projection L' hL a)) =
      D'.projection D hD.symm (L'.projection L hL.symm a) := neg_eq_of_add_eq_zero_right hsum
  have ht : D'.projection D hD.symm (L.projection L' hL a) +ᵥ ((D' : Set E) ∩ W) =
      (D' : Set E) ∩ W := by
    apply Set.Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact stab hL hcL w hw
    · intro c hc
      refine ⟨-(D'.projection D hD.symm (L.projection L' hL a)) + c, ?_, ?_⟩
      · rw [hneg]; exact stab hL.symm hcL.symm c hc
      · show _ +ᵥ _ = c
        rw [vadd_eq_add, add_neg_cancel_left]
  have := eq_zero_of_vadd_eq hCc h0C hdC ht
  exact (Submodule.projection_apply_eq_zero_iff hD.symm).1 this

/-- `P_L` maps `D` into `D` (through `span (D ∩ W) = D`). -/
theorem projection_mem_of_mem {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L L' D D' : Submodule ℝ E}
    (hL : IsCompl L L') (hcL : SontConjugues W L L') (hD : IsCompl D D')
    (hcD : SontConjugues W D D') {a : E} (ha : a ∈ D) : L.projection L' hL a ∈ D := by
  have hs : Submodule.span ℝ ((D : Set E) ∩ W) = D :=
    span_inter_eq_of_conjugues hD.symm hcD.symm hspan
  have hle : Submodule.span ℝ ((D : Set E) ∩ W) ≤ D.comap (L.projection L' hL) :=
    Submodule.span_le.2 fun x hx => projection_mem_of_mem_inter hW h0 hd hL hcL hD hcD ⟨hx.2, hx.1⟩
  rw [hs] at hle
  exact hle ha

/-! ### Théorème 1 -/

/-- **Théorème 1**, reading (b) of OQ-163 (supplementary conjugate pairs): `L ∩ D` and `L' ∩ D`
are conjugate relative to `W ∩ D`, supplementary in `D`, and `W ∩ D` spans `D`. -/
theorem theoreme1_supplementaires {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L L' D D' : Submodule ℝ E}
    (hL : IsCompl L L') (hcL : SontConjugues W L L') (hD : IsCompl D D')
    (hcD : SontConjugues W D D') :
    SontConjugues (W ∩ D) (L ⊓ D) (L' ⊓ D) ∧ Disjoint (L ⊓ D) (L' ⊓ D) ∧
      L ⊓ D ⊔ L' ⊓ D = D ∧ Submodule.span ℝ (W ∩ (D : Set E)) = D := by
  have hPD : ∀ x ∈ D, L.projection L' hL x ∈ D := fun x hx =>
    projection_mem_of_mem hW h0 hspan hd hL hcL hD hcD hx
  have hQD : ∀ x ∈ D, L'.projection L hL.symm x ∈ D := fun x hx =>
    projection_mem_of_mem hW h0 hspan hd hL.symm hcL.symm hD hcD hx
  refine ⟨?_, hL.disjoint.mono inf_le_left inf_le_left, ?_, ?_⟩
  · unfold SontConjugues
    ext x
    constructor
    · rintro ⟨hxW, hxD⟩
      exact Set.mem_add.2 ⟨L.projection L' hL x,
        ⟨Submodule.mem_inf.2 ⟨Submodule.projection_apply_mem _ _, hPD x hxD⟩,
          (projection_mem_inter hL hcL hxW).2, hPD x hxD⟩,
        L'.projection L hL.symm x,
        ⟨Submodule.mem_inf.2 ⟨Submodule.projection_apply_mem _ _, hQD x hxD⟩,
          (projection_mem_inter hL.symm hcL.symm hxW).2, hQD x hxD⟩,
        Submodule.projection_add_projection_eq_self hL x⟩
    · intro hx
      obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_add.1 hx
      refine ⟨?_, D.add_mem hp.2.2 hq.2.2⟩
      rw [hcL]
      exact Set.add_mem_add ⟨(Submodule.mem_inf.1 hp.1).1, hp.2.1⟩
        ⟨(Submodule.mem_inf.1 hq.1).1, hq.2.1⟩
  · refine le_antisymm (sup_le inf_le_right inf_le_right) fun x hx => ?_
    have := Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨Submodule.projection_apply_mem hL x, hPD x hx⟩)
      (Submodule.mem_inf.2 ⟨Submodule.projection_apply_mem hL.symm x, hQD x hx⟩)
    rwa [Submodule.projection_add_projection_eq_self hL] at this
  · rw [Set.inter_comm]
    exact span_inter_eq_of_conjugues hD.symm hcD.symm hspan

/-- **Théorème 1**, reading (a) of OQ-163, with `D'` dropped: `L`, `L'`, `D` distinguished and
`W = L ∩ W + L' ∩ W` (no supplementarity of `L`, `L'`); then `L ∩ D` and `L' ∩ D` are conjugate
relative to `W ∩ D`, and `L ⊓ D ⊔ L' ⊓ D = D`. -/
theorem theoreme1_distingues {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L L' D : Submodule ℝ E}
    (hL : EstDistingue W L) (hL' : EstDistingue W L') (hc : SontConjugues W L L')
    (hD : EstDistingue W D) :
    SontConjugues (W ∩ D) (L ⊓ D) (L' ⊓ D) ∧ L ⊓ D ⊔ L' ⊓ D = D := by
  obtain ⟨N, hDN, hcDN⟩ := hD
  obtain ⟨M, hLM, hcLM⟩ := hL
  obtain ⟨M', hLM', hcLM'⟩ := hL'
  have hQL : ∀ x ∈ L, D.projection N hDN x ∈ L := fun x hx =>
    projection_mem_of_mem hW h0 hspan hd hDN hcDN hLM hcLM hx
  have hQL' : ∀ x ∈ L', D.projection N hDN x ∈ L' := fun x hx =>
    projection_mem_of_mem hW h0 hspan hd hDN hcDN hLM' hcLM' hx
  have hspanD : Submodule.span ℝ ((D : Set E) ∩ W) = D :=
    span_inter_eq_of_conjugues hDN.symm hcDN.symm hspan
  have hsub : W ∩ (D : Set E) ⊆ ((L ⊓ D : Submodule ℝ E) : Set E) ∩ (W ∩ D) +
      ((L' ⊓ D : Submodule ℝ E) : Set E) ∩ (W ∩ D) := by
    rintro x ⟨hxW, hxD⟩
    have hxW' := hxW
    rw [hc, Set.mem_add] at hxW'
    obtain ⟨p, hp, q, hq, hpq⟩ := hxW'
    have e : D.projection N hDN p + D.projection N hDN q = x := by
      rw [← map_add, hpq]; exact Submodule.projection_apply_of_mem_left hDN hxD
    have hQp := projection_mem_inter hDN hcDN hp.2
    have hQq := projection_mem_inter hDN hcDN hq.2
    exact Set.mem_add.2 ⟨D.projection N hDN p,
      ⟨Submodule.mem_inf.2 ⟨hQL p hp.1, hQp.1⟩, hQp.2, hQp.1⟩, D.projection N hDN q,
      ⟨Submodule.mem_inf.2 ⟨hQL' q hq.1, hQq.1⟩, hQq.2, hQq.1⟩, e⟩
  refine ⟨?_, ?_⟩
  · unfold SontConjugues
    refine Set.Subset.antisymm hsub fun x hx => ?_
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_add.1 hx
    refine ⟨?_, D.add_mem hp.2.2 hq.2.2⟩
    rw [hc]
    exact Set.add_mem_add ⟨(Submodule.mem_inf.1 hp.1).1, hp.2.1⟩
      ⟨(Submodule.mem_inf.1 hq.1).1, hq.2.1⟩
  · refine le_antisymm (sup_le inf_le_right inf_le_right) fun x hx => ?_
    rw [← hspanD] at hx
    refine (Submodule.span_le.2 (fun y hy => ?_) : Submodule.span ℝ ((D : Set E) ∩ W) ≤ _) hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_add.1 (hsub ⟨hy.2, hy.1⟩)
    exact Submodule.add_mem_sup hp.1 hq.1

/-- **Théorème 1** as printed (reading (a) of OQ-163, Déf. 4 of record): « Soient `W` un convexe
de `E` contenant l'origine `O`, engendrant `E`, et ne contenant aucune droite, `L` et `L'`, `D`
et `D'` deux couples de sous-espaces distingués conjugués relativement à `W`. Alors `L ∩ D` et
`L' ∩ D` sont conjugués relativement à `W ∩ D`. » -/
theorem theoreme1 {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L L' D D' : Submodule ℝ E}
    (hL : EstDistingue W L) (hL' : EstDistingue W L') (hc : SontConjugues W L L')
    (hD : EstDistingue W D) (_hD' : EstDistingue W D') (_hcD : SontConjugues W D D') :
    SontConjugues (W ∩ D) (L ⊓ D) (L' ⊓ D) := by
  exact (theoreme1_distingues hW h0 hspan hd hL hL' hc hD).1

/-- **Théorème 1**, reading (c) of OQ-163 (Déf. 4's « + » as Déf. 1's sum). -/
theorem theoreme1_sommeConvexes {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L L' D D' : Submodule ℝ E}
    (hL : EstDistingue W L) (hL' : EstDistingue W L')
    (hc : IsSommeConvexes W ![(L : Set E) ∩ W, (L' : Set E) ∩ W])
    (hD : EstDistingue W D) (_hD' : EstDistingue W D')
    (_hcD : IsSommeConvexes W ![(D : Set E) ∩ W, (D' : Set E) ∩ W]) :
    IsSommeConvexes (W ∩ D)
      ![((L ⊓ D : Submodule ℝ E) : Set E) ∩ (W ∩ D), ((L' ⊓ D : Submodule ℝ E) : Set E) ∩ (W ∩ D)] := by
  have hc' : SontConjugues W L L' := IsSommeConvexes.sontConjugues hc
  have hmain := (theoreme1_distingues hW h0 hspan hd hL hL' hc' hD).1
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hc
  rw [isSommeConvexes_iff_bijOn]
  refine ⟨fun i => ?_, fun x hx => ?_, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
  · fin_cases i
    · exact (L ⊓ D).convex.inter (hW.inter D.convex)
    · exact (L' ⊓ D).convex.inter (hW.inter D.convex)
  · have h0 := hx 0 trivial
    have h1 := hx 1 trivial
    simp only [Fin.sum_univ_two]
    unfold SontConjugues at hmain
    rw [hmain]
    exact Set.add_mem_add (by simpa using h0) (by simpa using h1)
  · have pi : ∀ u : Fin 2 → E, u ∈ Set.univ.pi
        ![((L ⊓ D : Submodule ℝ E) : Set E) ∩ (W ∩ D),
          ((L' ⊓ D : Submodule ℝ E) : Set E) ∩ (W ∩ D)] →
        u ∈ Set.univ.pi ![(L : Set E) ∩ W, (L' : Set E) ∩ W] := by
      intro u hu i _
      have h0 : u 0 ∈ ((L ⊓ D : Submodule ℝ E) : Set E) ∩ (W ∩ D) := by simpa using hu 0 trivial
      have h1 : u 1 ∈ ((L' ⊓ D : Submodule ℝ E) : Set E) ∩ (W ∩ D) := by simpa using hu 1 trivial
      fin_cases i
      · simpa using (⟨(Submodule.mem_inf.1 h0.1).1, h0.2.1⟩ : u 0 ∈ (L : Set E) ∩ W)
      · simpa using (⟨(Submodule.mem_inf.1 h1.1).1, h1.2.1⟩ : u 1 ∈ (L' : Set E) ∩ W)
    exact hbij.injOn (pi x hx) (pi y hy) hxy
  · unfold SontConjugues at hmain
    rw [hmain] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
    refine ⟨![a, b], fun i _ => ?_, by simp [Fin.sum_univ_two]⟩
    fin_cases i
    · simpa using ha
    · simpa using hb

/-! ### The Corollaire -/

/-- A linear map preserving both `D` and `D'` commutes with the projection on `D` parallel to
`D'`. -/
theorem commute_projection_of_mapsTo {D D' : Submodule ℝ E} (hD : IsCompl D D')
    (f : E →ₗ[ℝ] E) (h1 : ∀ x ∈ D, f x ∈ D) (h2 : ∀ x ∈ D', f x ∈ D') :
    D.projection D' hD ∘ₗ f = f ∘ₗ D.projection D' hD := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  conv_lhs => rw [← Submodule.projection_add_projection_eq_self hD x]
  rw [map_add, map_add,
    Submodule.projection_apply_of_mem_left hD (h1 _ (Submodule.projection_apply_mem hD x)),
    Submodule.projection_apply_of_mem_right hD (h2 _ (Submodule.projection_apply_mem hD.symm x)),
    add_zero]

/-- **Corollaire** (l.503), reading (b) of OQ-163: « `P_L`, `P_{L'}`, `P_D`, `P_{D'}` commutent
deux à deux, et l'on a `Identité = P_L P_D + P_L P_{D'} + P_{L'} P_D + P_{L'} P_{D'}` ». -/
theorem corollaire_projections_commutent {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L L' D D' : Submodule ℝ E}
    (hL : IsCompl L L') (hcL : SontConjugues W L L') (hD : IsCompl D D')
    (hcD : SontConjugues W D D') :
    L.projection L' hL ∘ₗ L'.projection L hL.symm = L'.projection L hL.symm ∘ₗ L.projection L' hL ∧
    D.projection D' hD ∘ₗ D'.projection D hD.symm = D'.projection D hD.symm ∘ₗ D.projection D' hD ∧
    L.projection L' hL ∘ₗ D.projection D' hD = D.projection D' hD ∘ₗ L.projection L' hL ∧
    L.projection L' hL ∘ₗ D'.projection D hD.symm =
      D'.projection D hD.symm ∘ₗ L.projection L' hL ∧
    L'.projection L hL.symm ∘ₗ D.projection D' hD =
      D.projection D' hD ∘ₗ L'.projection L hL.symm ∧
    L'.projection L hL.symm ∘ₗ D'.projection D hD.symm =
      D'.projection D hD.symm ∘ₗ L'.projection L hL.symm ∧
    LinearMap.id = L.projection L' hL ∘ₗ D.projection D' hD +
      L.projection L' hL ∘ₗ D'.projection D hD.symm +
      L'.projection L hL.symm ∘ₗ D.projection D' hD +
      L'.projection L hL.symm ∘ₗ D'.projection D hD.symm := by
  have hPD := fun x (hx : x ∈ D) => projection_mem_of_mem hW h0 hspan hd hL hcL hD hcD hx
  have hPD' := fun x (hx : x ∈ D') =>
    projection_mem_of_mem hW h0 hspan hd hL hcL hD.symm hcD.symm hx
  have hQD := fun x (hx : x ∈ D) =>
    projection_mem_of_mem hW h0 hspan hd hL.symm hcL.symm hD hcD hx
  have hQD' := fun x (hx : x ∈ D') =>
    projection_mem_of_mem hW h0 hspan hd hL.symm hcL.symm hD.symm hcD.symm hx
  refine ⟨?_, ?_, (commute_projection_of_mapsTo hD _ hPD hPD').symm,
    (commute_projection_of_mapsTo hD.symm _ hPD' hPD).symm,
    (commute_projection_of_mapsTo hD _ hQD hQD').symm,
    (commute_projection_of_mapsTo hD.symm _ hQD' hQD).symm, ?_⟩
  · refine commute_projection_of_mapsTo hL _ (fun x hx => ?_) fun x _ =>
      Submodule.projection_apply_mem _ _
    rw [Submodule.projection_apply_of_mem_right hL.symm hx]; exact L.zero_mem
  · refine commute_projection_of_mapsTo hD _ (fun x hx => ?_) fun x _ =>
      Submodule.projection_apply_mem _ _
    rw [Submodule.projection_apply_of_mem_right hD.symm hx]; exact D.zero_mem
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    have e1 := Submodule.projection_add_projection_eq_self hD x
    have e2 := Submodule.projection_add_projection_eq_self hL (D.projection D' hD x)
    have e3 := Submodule.projection_add_projection_eq_self hL (D'.projection D hD.symm x)
    calc x = D.projection D' hD x + D'.projection D hD.symm x := e1.symm
      _ = (L.projection L' hL (D.projection D' hD x) +
            L'.projection L hL.symm (D.projection D' hD x)) +
          (L.projection L' hL (D'.projection D hD.symm x) +
            L'.projection L hL.symm (D'.projection D hD.symm x)) := by rw [e2, e3]
      _ = _ := by abel

/-- The decomposition of the Corollary's proof (l.512–518): every point of `W` is a sum of points
of `L ∩ D ∩ W`, `L ∩ D' ∩ W`, `L' ∩ D ∩ W`, `L' ∩ D' ∩ W`, namely its images by `P_L P_D`,
`P_L P_{D'}`, `P_{L'} P_D`, `P_{L'} P_{D'}`. -/
theorem corollaire_decomposition {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L L' D D' : Submodule ℝ E}
    (hL : IsCompl L L') (hcL : SontConjugues W L L') (hD : IsCompl D D')
    (hcD : SontConjugues W D D') :
    W = ((L ⊓ D : Submodule ℝ E) : Set E) ∩ W + ((L ⊓ D' : Submodule ℝ E) : Set E) ∩ W +
      ((L' ⊓ D : Submodule ℝ E) : Set E) ∩ W + ((L' ⊓ D' : Submodule ℝ E) : Set E) ∩ W := by
  have hid := (corollaire_projections_commutent hW h0 hspan hd hL hcL hD hcD).2.2.2.2.2.2
  have mem : ∀ {M M' F F' : Submodule ℝ E} (hM : IsCompl M M') (hcM : SontConjugues W M M')
      (hF : IsCompl F F') (hcF : SontConjugues W F F') (w : E), w ∈ W →
      M.projection M' hM (F.projection F' hF w) ∈ ((M ⊓ F : Submodule ℝ E) : Set E) ∩ W := by
    intro M M' F F' hM hcM hF hcF w hw
    have h1 := projection_mem_inter hF hcF hw
    have h2 := projection_mem_inter hM hcM h1.2
    exact ⟨Submodule.mem_inf.2 ⟨h2.1,
      projection_mem_of_mem hW h0 hspan hd hM hcM hF hcF h1.1⟩, h2.2⟩
  ext w
  constructor
  · intro hw
    have e := LinearMap.congr_fun hid w
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at e
    rw [e]
    exact Set.add_mem_add (Set.add_mem_add (Set.add_mem_add (mem hL hcL hD hcD w hw)
      (mem hL hcL hD.symm hcD.symm w hw)) (mem hL.symm hcL.symm hD hcD w hw))
      (mem hL.symm hcL.symm hD.symm hcD.symm w hw)
  · intro hw
    obtain ⟨abc, habc, d, hd4, rfl⟩ := Set.mem_add.1 hw
    obtain ⟨ab, hab, c, hc3, rfl⟩ := Set.mem_add.1 habc
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hab
    have hac : a + c ∈ (D : Set E) ∩ W := by
      refine ⟨D.add_mem (Submodule.mem_inf.1 ha.1).2 (Submodule.mem_inf.1 hc3.1).2, ?_⟩
      rw [hcL]
      exact Set.add_mem_add ⟨(Submodule.mem_inf.1 ha.1).1, ha.2⟩ ⟨(Submodule.mem_inf.1 hc3.1).1, hc3.2⟩
    have hbd : b + d ∈ (D' : Set E) ∩ W := by
      refine ⟨D'.add_mem (Submodule.mem_inf.1 hb.1).2 (Submodule.mem_inf.1 hd4.1).2, ?_⟩
      rw [hcL]
      exact Set.add_mem_add ⟨(Submodule.mem_inf.1 hb.1).1, hb.2⟩ ⟨(Submodule.mem_inf.1 hd4.1).1, hd4.2⟩
    have e : a + b + c + d = (a + c) + (b + d) := by abel
    rw [e, hcD]
    exact Set.add_mem_add hac hbd

end Conjugues

/-! ### The instance: the cube `[−1, 1]³` -/

/-- Théorème 1 on the cube `[−1,1]³`, `L = ⟨e₁⟩`, `D = ⟨e₁, e₂⟩`, their coordinate complements. -/
theorem cube3_theoreme1 :
    SontConjugues (cube 3 ∩ ((coord ({0, 1} : Set (Fin 3)) : Set (Fin 3 → ℝ))))
      (coord {0} ⊓ coord {0, 1}) (coord {0}ᶜ ⊓ coord {0, 1}) ∧
    coord {0} ⊓ coord {0, 1} ⊔ coord {0}ᶜ ⊓ coord {0, 1} = coord ({0, 1} : Set (Fin 3)) := by
  obtain ⟨hc, h0, hspan, hd⟩ := cube_hyps 3
  have hd' : ¬ ContientDroite (cube 3) := fun h => hd h.contientDemiDroite
  obtain ⟨h1, -, h2, -⟩ := theoreme1_supplementaires hc h0 hspan hd' (isCompl_coord {0})
    (cube_sontConjugues {0}) (isCompl_coord {0, 1}) (cube_sontConjugues {0, 1})
  exact ⟨h1, h2⟩

/-- The Corollaire on the cube `[−1,1]³`, same subspaces. -/
theorem cube3_corollaire :
    (coord ({0} : Set (Fin 3))).projection (coord {0}ᶜ) (isCompl_coord _) ∘ₗ
        (coord ({0, 1} : Set (Fin 3))).projection (coord {0, 1}ᶜ) (isCompl_coord _) =
      (coord ({0, 1} : Set (Fin 3))).projection (coord {0, 1}ᶜ) (isCompl_coord _) ∘ₗ
        (coord ({0} : Set (Fin 3))).projection (coord {0}ᶜ) (isCompl_coord _) := by
  obtain ⟨hc, h0, hspan, hd⟩ := cube_hyps 3
  have hd' : ¬ ContientDroite (cube 3) := fun h => hd h.contientDemiDroite
  exact (corollaire_projections_commutent hc h0 hspan hd' (isCompl_coord {0})
    (cube_sontConjugues {0}) (isCompl_coord {0, 1}) (cube_sontConjugues {0, 1})).2.2.1

end Benzecri
