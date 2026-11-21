import Benzecri.Chapter2.Theoreme
import Benzecri.Chapter2.PremierAffine

/-!
# Chapter 2 § 3, the projective Theorem's 1°c in its full form `P = φ̃⁻¹(D ∩ φ̃(V))`, where it is proved: for every shell (every `n`), for every pocket when `n ≤ 1`, and when `φ̃(V) ∩ H̊` is star-shaped about a point of cote `< 1`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 3, journal pp. 253–255; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-premier-full-proj.

* `bzthm:c2s3t1_poche_balayable` — `benzecri1960_ch2.tex:517` (1° at l.522–524, its proof *c* at
  l.582–590; 3° at l.528–529, its proof l.600–603). Not marked: OQ-71 stays open. This file proves
  the full form of 1°c in three cases the paper does not separate, and sharpens OQ-71 to the case
  that remains (SCOPE).

> **Théorème.** Soit $V$ une variété localement projective connexe balayable. Soit
> $(P, \mathring{H}, \varphi, z)$ une poche de $V$.
>
> 1° Il existe une carte compatible $\tilde{\varphi}$ de $V$ sur un ouvert de $S(n)$, induisant
> $\varphi$ sur $P$. $P$ n'est autre que l'image réciproque par $\tilde{\varphi}$ de l'ensemble des
> points de $\mathring{H}$ où $z<1$.
>
> […] 3° Si $\varphi(P)$ est convexe (*i. e.* si $(P, \mathring{H}, \varphi, z)$ est une coque),
> $\tilde{\varphi}(V)$ est un convexe.
>
> […] *c*. $P$ est l'image réciproque par $\tilde{\varphi}$ de l'ensemble $D$ des points de
> $\mathring{H}$, où $z<1$. Montrons que $P=\tilde{\varphi}^{-1}(D\cap\tilde{\varphi}(V))$. Soit
> $M\in\tilde{\varphi}^{-1}(D\cap\tilde{\varphi}(V))$ nous : allons montrer que $M\in P$. Soit
> $N\in P$; on peut construire dans $D\cap\tilde{\varphi}(V)$ une ligne brisée allant de
> $\tilde{\varphi}(M)$ à $\tilde{\varphi}(N)$. De la condition $b$ de la définition des poches, il
> résulte que $M$ appartient à $P$.

And Déf. 2 (l.188–190): « Une poche $(P, \mathring{H}, \varphi, z)$ […] est appelée *coque* si
$\varphi(P)$ est un convexe. »

## What is proved (no `sorry`)

The full form `P = φ̃⁻¹(D ∩ φ̃(V))`, `D = {z < 1} ⊆ H̊`, for every developing map `φ̃` equal to
`φ` on `P` (the chart of 1° is one), in each of these cases:

* (ii) `φ̃(V) ∩ H̊` star-shaped, for the affine structure of `H̊` (Déf. 6), about a point `c` with
  `z(c) < 1`: `poche_eq_preimage_of_starConvex_proj`. Then `D ∩ φ̃(V)` is star-shaped about `c`,
  so connected, which is the connectedness l.588 presumes. Special cases: `φ̃(V) ∩ H̊` convex in
  `H̊` (`poche_eq_preimage_of_isAffConvex_proj`); `φ̃(V)` a convex part of `S(n)`, Déf. 8
  (`poche_eq_preimage_of_isConvexPart_proj`).
* (iii) every shell, through 3°: `poche_eq_preimage_of_coque_proj`; with 2°–4°, the companion of
  `theoreme_poche_balayable` for shells, `theoreme_poche_balayable_coque_proj`, and over the paper's
  manifolds `TheoremeCoquePrinted`, `theoremeCoquePrinted` (every `n`).
* (i) every pocket in dimension `n ≤ 1`, because there every pocket is a shell (`φ(P)` is a
  connected part of the affine line or point `H̊`): `isCoqueProj_of_le_one_proj`,
  `poche_eq_preimage_of_le_one_proj`; printed: `connexePrinted_of_le_one_proj`,
  `premierPrinted_of_le_one_proj`, `theoremePrinted_of_le_one_proj` (the Theorem holds as printed,
  full form included, for `n ≤ 1`).
  For `n = 0` this is the degenerate case the library already had (`H̊` is a point, so `z ≡ 0`
  and `P = V`, `poche_eq_preimage_of_cote_eq_zero`): (i) adds only `n = 1`.
* `P = V` (trivially, `poche_eq_preimage_of_eq_univ_proj`); `P ≠ V` forces a non-constant cote
  (`not_cote_eq_zero_of_ne_univ_proj`), so this case contains the constant cote of
  `poche_eq_preimage_of_cote_eq_zero`.
* OQ-71 sharpened: `ConnexeOuvertPrinted n` is `ConnexePrinted n` restricted to the pockets that
  are not shells, are not all of `V` (hence have a non-constant cote), and for whose chart
  `φ̃(V) ∩ H̊` is star-shaped about no point of cote `< 1`; `connexePrinted_iff_ouvert_proj` and
  `theoremePrinted_iff_ouvert_proj` show that nothing else is open, and
  `connexeOuvertPrinted_of_le_one_proj` that it holds (vacuously) for `n ≤ 1`.
* Every shell meets the hypothesis of (ii) (`exists_starConvex_of_coque_proj`), so the third
  restriction of `ConnexeOuvertPrinted` implies the first.
* Non-vacuity: `poche_eq_preimage_demiDroite_coque_proj` ((iii) and the companion assembly at the
  strict shell `]0, 1[` of `]0, ∞[`, a non-constant cote, `P ≠ V`) and
  `poche_eq_preimage_demiDroite_le_one_proj` ((i) at the pocket `]0, 1[` of
  `theoreme_premier_demiDroite`, given as a pocket only: its shell structure is recovered by the
  dimension, `isCoqueProj_of_le_one_proj`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « une variété localement projective » | ⚠ weakened: `[ChartedSpace (S n) V]`, `[HasGroupoid V (projGroupoid n)]`; the printed forms carry Hausdorff and second countable |
| `V` connexe | ⚠ weakened: `[PreconnectedSpace V]` |
| `V` balayable | ✓ carried: `IsBalayable (GSR n) (S n) V` |
| `(P, H̊, φ, z)` une poche de `V` | ✓ carried: `IsPocheProj P l φ z` |
| the dimension | ✓ every `n` for (ii), (iii) and `P = V`; ⚠ strengthened: `n ≤ 1` for (i), which is that case |
| (ii) `φ̃(V) ∩ H̊` star-shaped about a point of `D` | ⚠ strengthened: not a hypothesis of the paper, a sufficient condition for the full form, stated as its own lemma |
| (iii) « une coque » | ⚠ strengthened: `IsCoqueProj P l φ z` (Déf. 2), the hypothesis of 3°, added to 1° |
| 1°: « $P$ n'est autre que l'image réciproque par $\tilde\varphi$ de … $z<1$ » | ⚠ strengthened (the case hypotheses): full form `P = φ̃⁻¹(D ∩ φ̃(V))`, in these cases only (SCOPE) |

## SCOPE (disclosed)

* **The full form of 1°c is not proved for every pocket.** It is proved for every shell, in every
  dimension `n ≤ 1`, for `P = V` (which contains the constant cote,
  `poche_eq_preimage_of_cote_eq_zero`, Developpement), and when `φ̃(V) ∩ H̊` is star-shaped about a
  point of cote `< 1`. What remains of OQ-71 is `ConnexeOuvertPrinted n` for `n ≥ 2`: a pocket
  `P ≠ V` (so with a non-constant cote) that is not a shell, whose `φ̃(V) ∩ H̊` is star-shaped about
  no point of `D`. Neither proved nor refuted.
* (ii) is a sufficient condition added for that analysis; it is not a reading of the paper.
* (i) does not use the antipodal-point argument the roadmap block sketches (two arcs of length
  `≤ π`): in dimension `≤ 1` the open hemisphere `H̊` is an affine line or a point, a connected part
  of it is convex, so `φ(P)` is convex and every pocket is a shell; (iii) then applies.
* (iii) uses 3° (`theoreme_troisieme`) before 1°c, the reverse of the paper's order; there is no
  circularity, since 3° rests on Prop. 7's corollary and on the developing map, never on 1°c. Only the
  convexity of `φ̃(V)` is used, not its strictness.
* `ConnexeOuvertPrinted` keeps « not a shell » although its third restriction implies it
  (`exists_starConvex_of_coque_proj`), so that it reads as the roadmap's sharpened form of OQ-71;
  it uses `P ≠ V` where the roadmap says « a non-constant cote », a stronger restriction
  (`not_cote_eq_zero_of_ne_univ_proj`), since `P = V` is settled.
* `[sic]`, not findings: « nous : allons » (l.587).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u

/-! ### Star-shaped parts of the affine space `H̊` -/

section Hemi

variable {n : ℕ} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]

/-- `D ∩ A` is the image in `S(n)` of the points of `H̊` of cote `< 1` lying over `A`. -/
theorem demiEspace_inter_eq_image_proj (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ) (A : Set (S n)) :
    demiEspace z ∩ A =
      (↑) '' {q : Sphere.openHemisphere l | z q < 1 ∧ (q : S n) ∈ A} := by
  ext q
  constructor
  · rintro ⟨⟨m, hm, rfl⟩, hA⟩
    exact ⟨m, ⟨hm, hA⟩, rfl⟩
  · rintro ⟨m, ⟨hm, hA⟩, rfl⟩
    exact ⟨⟨m, hm, rfl⟩, hA⟩

/-- **A part of the affine space `H̊` star-shaped about one of its points is connected in
`S(n)`** (through an affine isomorphism `H̊ ≃ ℝⁿ`, an open embedding into `S(n)`). -/
theorem isPreconnected_coe_image_of_starConvex_proj {W : Set (Sphere.openHemisphere l)}
    {c : Sphere.openHemisphere l} (hc : c ∈ W) (hW : ∀ y ∈ W, affineSegment ℝ c y ⊆ W) :
    IsPreconnected ((↑) '' W : Set (S n)) := by
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := l) (Module.finrank_fin_fun ℝ)
  have hj := isOpenEmbedding_coe_affineEquiv e.symm
  have hstar : StarConvex ℝ (e c) (e '' W) := by
    rw [starConvex_iff_segment_subset]
    rintro _ ⟨y, hy, rfl⟩ w hw
    have h := affineSegment_image (e : Sphere.openHemisphere l →ᵃ[ℝ] (Fin n → ℝ)) c y
    rw [← affineSegment_eq_segment] at hw
    simp only [AffineEquiv.coe_toAffineMap] at h
    rw [← h] at hw
    exact image_mono (hW y hy) hw
  have himg : (fun y => (e.symm y : S n)) '' (e '' W) = (↑) '' W := by
    rw [image_image]
    simp only [AffineEquiv.symm_apply_apply]
  rw [← himg]
  exact (hstar.isPathConnected (mem_image_of_mem e hc)).isConnected.isPreconnected.image _
    hj.continuous.continuousOn

/-- **In dimension `n ≤ 1`, a part of `H̊` that is connected in `S(n)` is convex** for the affine
structure of `H̊` (`H̊` is an affine line or a point). -/
theorem isAffConvex_of_isPreconnected_of_le_one_proj (hn : n ≤ 1)
    {W : Set (Sphere.openHemisphere l)} (hW : IsPreconnected ((↑) '' W : Set (S n))) :
    IsAffConvex (Sphere.HemiTrans l) W := by
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := l) (Module.finrank_fin_fun ℝ)
  have hj := isOpenEmbedding_coe_affineEquiv e.symm
  have himg : (fun y => (e.symm y : S n)) '' (e '' W) = (↑) '' W := by
    rw [image_image]
    simp only [AffineEquiv.symm_apply_apply]
  have hT : IsPreconnected (e '' W) := by
    rw [← hj.isInducing.isPreconnected_image, himg]
    exact hW
  have hconv : Convex ℝ (e '' W) := convex_of_isPreconnected_of_le_one hn hT
  intro x hx y hy w hw
  have h := affineSegment_image (e : Sphere.openHemisphere l →ᵃ[ℝ] (Fin n → ℝ)) x y
  simp only [AffineEquiv.coe_toAffineMap] at h
  have hew : e w ∈ segment ℝ (e x) (e y) := by
    rw [← affineSegment_eq_segment, ← h]
    exact mem_image_of_mem e hw
  obtain ⟨w', hw', hww'⟩ :=
    hconv.segment_subset (mem_image_of_mem e hx) (mem_image_of_mem e hy) hew
  rwa [← e.injective hww']

/-- **The trace on `H̊` of a convex part of `S(n)`** (Déf. 8) **is convex in the affine space
`H̊`** (Déf. 6): two points of `H̊` are never antipodal, and their segment in `S(n)` is their affine
segment in `H̊` (`Sphere.coe_image_affineSegment`). -/
theorem isAffConvex_preimage_of_isConvexPart_proj {A : Set (S n)} (hA : Sphere.IsConvexPart A) :
    IsAffConvex (Sphere.HemiTrans l) ((↑) ⁻¹' A : Set (Sphere.openHemisphere l)) := by
  intro x hx y hy w hw
  have h1 : (w : S n) ∈ Sphere.closedSeg (x : S n) y := by
    rw [← Sphere.coe_image_affineSegment]
    exact mem_image_of_mem _ hw
  exact Sphere.isConvexPart_iff_isSegConvex.1 hA _ hx _ hy
    (Sphere.ne_neg_of_mem_openHemisphere x.2 y.2) h1

end Hemi

/-! ### The full form of 1°c: star-shaped, convex, shells, `n ≤ 1` -/

section PremierFull

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]
  {P : Set V} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
  {φ : OpenPartialHomeomorph V (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}

/-- **(ii) 1°c, the full form, when `φ̃(V) ∩ H̊` is star-shaped about a point `c` of cote `< 1`**,
for the affine structure of `H̊` (Déf. 6): `D` is convex in `H̊`, so `D ∩ φ̃(V)` is star-shaped
about `c`, hence connected, and `P = φ̃⁻¹(D ∩ φ̃(V))`. -/
theorem poche_eq_preimage_of_starConvex_proj [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) {c : Sphere.openHemisphere l} (hc : z c < 1)
    (hstar : ∀ y ∈ ((↑) ⁻¹' range p : Set (Sphere.openHemisphere l)),
      affineSegment ℝ c y ⊆ (↑) ⁻¹' range p) :
    P = p ⁻¹' (demiEspace z ∩ range p) := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  have hy₀ : (⟨φ x₀, hP.mapsTo_hemi hx₀⟩ : Sphere.openHemisphere l) ∈
      ((↑) ⁻¹' range p : Set (Sphere.openHemisphere l)) := ⟨x₀, hpφ hx₀⟩
  have hcW : c ∈ ((↑) ⁻¹' range p : Set (Sphere.openHemisphere l)) :=
    hstar _ hy₀ (left_mem_affineSegment ℝ _ _)
  have hWDstar : ∀ y ∈ {q : Sphere.openHemisphere l | z q < 1 ∧ (q : S n) ∈ range p},
      affineSegment ℝ c y ⊆ {q : Sphere.openHemisphere l | z q < 1 ∧ (q : S n) ∈ range p} := by
    rintro y ⟨hzy, hyW⟩ w hw
    refine ⟨?_, hstar y hyW hw⟩
    have h := affineSegment_image z c y
    have hzw : z w ∈ segment ℝ (z c) (z y) := by
      rw [← affineSegment_eq_segment, ← h]
      exact mem_image_of_mem z hw
    exact (convex_Iio (1 : ℝ)).segment_subset hc hzy hzw
  refine (poche_eq_preimage_iff hbal hP hp hpφ).2 ?_
  rw [demiEspace_inter_eq_image_proj]
  exact isPreconnected_coe_image_of_starConvex_proj ⟨hc, hcW⟩ hWDstar

/-- **1°c, the full form, when `φ̃(V) ∩ H̊` is convex in the affine space `H̊`.** -/
theorem poche_eq_preimage_of_isAffConvex_proj [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P)
    (hconv : IsAffConvex (Sphere.HemiTrans l) ((↑) ⁻¹' range p : Set (Sphere.openHemisphere l))) :
    P = p ⁻¹' (demiEspace z ∩ range p) := by
  obtain ⟨x₀, hx₀⟩ := hP.isConnected.nonempty
  have hc : (⟨φ x₀, hP.mapsTo_hemi hx₀⟩ : Sphere.openHemisphere l) ∈
      ((↑) ⁻¹' range p : Set (Sphere.openHemisphere l)) := ⟨x₀, hpφ hx₀⟩
  exact poche_eq_preimage_of_starConvex_proj hbal hP hp hpφ (hP.cote_lt_one hx₀)
    fun y hy => hconv _ hc y hy

/-- **1°c, the full form, when `φ̃(V)` is a convex part of `S(n)`** (Déf. 8; what 3° proves for a
shell). -/
theorem poche_eq_preimage_of_isConvexPart_proj [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) (hconv : Sphere.IsConvexPart (range p)) :
    P = p ⁻¹' (demiEspace z ∩ range p) :=
  poche_eq_preimage_of_isAffConvex_proj hbal hP hp hpφ
    (isAffConvex_preimage_of_isConvexPart_proj hconv)

/-- **(iii) 1°c, the full form, for every shell** (`φ(P)` convex, Déf. 2): by 3°
(`theoreme_troisieme`) `φ̃(V)` is a convex part of `S(n)`. -/
theorem poche_eq_preimage_of_coque_proj [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hC : IsCoqueProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) :
    P = p ⁻¹' (demiEspace z ∩ range p) :=
  poche_eq_preimage_of_isConvexPart_proj hbal hC.1 hp hpφ (theoreme_troisieme hbal hC hp hpφ).1

/-- **Every shell meets the hypothesis of (ii)**: for a shell, `φ̃(V) ∩ H̊` is star-shaped (in the
affine space `H̊`) about every point of `φ(P)`, whose cote is `< 1`. So a pocket for whose chart
`φ̃(V) ∩ H̊` is star-shaped about no point of cote `< 1` is not a shell. -/
theorem exists_starConvex_of_coque_proj [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hC : IsCoqueProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) :
    ∃ c : Sphere.openHemisphere l, z c < 1 ∧
      ∀ y ∈ ((↑) ⁻¹' range p : Set (Sphere.openHemisphere l)),
        affineSegment ℝ c y ⊆ (↑) ⁻¹' range p := by
  obtain ⟨x₀, hx₀⟩ := hC.1.isConnected.nonempty
  have hconv := isAffConvex_preimage_of_isConvexPart_proj (l := l)
    (theoreme_troisieme hbal hC hp hpφ).1
  have hc : (⟨φ x₀, hC.1.mapsTo_hemi hx₀⟩ : Sphere.openHemisphere l) ∈
      ((↑) ⁻¹' range p : Set (Sphere.openHemisphere l)) := ⟨x₀, hpφ hx₀⟩
  exact ⟨_, hC.1.cote_lt_one hx₀, fun y hy => hconv _ hc y hy⟩

omit [HasGroupoid V (projGroupoid n)] in
/-- **1°c, the full form, when the pocket is all of `V`** (`P ⊆ φ̃⁻¹(D)` always). -/
theorem poche_eq_preimage_of_eq_univ_proj (hP : IsPocheProj P l φ z) {p : V → S n}
    (hpφ : EqOn p φ P) (hPu : P = univ) : P = p ⁻¹' (demiEspace z ∩ range p) := by
  rw [preimage_inter_range]
  refine Subset.antisymm (fun y hy => ?_) (fun y _ => hPu ▸ mem_univ y)
  rw [mem_preimage, hpφ hy]
  exact hP.mapsTo_demiEspace hy

/-- **A pocket other than `V` has a non-constant cote** (`z ≡ 0` forces `P = V`,
`poche_eq_preimage_of_cote_eq_zero`). -/
theorem not_cote_eq_zero_of_ne_univ_proj [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) (hne : P ≠ univ) :
    ¬ ∀ y, z y = 0 := by
  intro hz
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche hbal hP
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  exact hne (poche_eq_preimage_of_cote_eq_zero hbal hP hp hφ'φ hz).1

omit [HasGroupoid V (projGroupoid n)] in
/-- **In dimension `n ≤ 1` every pocket is a shell**: `φ(P)` is a connected part of `H̊`, an affine
line or a point, hence convex. -/
theorem isCoqueProj_of_le_one_proj (hn : n ≤ 1) (hP : IsPocheProj P l φ z) :
    IsCoqueProj P l φ z := by
  refine ⟨hP, (Sphere.isConvexPart_iff_isAffConvex hP.image_subset).2 ?_⟩
  refine isAffConvex_of_isPreconnected_of_le_one_proj hn ?_
  rw [image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hP.image_subset)]
  refine hP.isConnected.isPreconnected.image _ ?_
  rw [← hP.source_eq]
  exact φ.continuousOn

/-- **(i) 1°c, the full form, in every dimension `n ≤ 1`**, for every pocket. -/
theorem poche_eq_preimage_of_le_one_proj (hn : n ≤ 1) [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hP : IsPocheProj P l φ z) {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hpφ : EqOn p φ P) :
    P = p ⁻¹' (demiEspace z ∩ range p) :=
  poche_eq_preimage_of_coque_proj hbal (isCoqueProj_of_le_one_proj hn hP) hp hpφ

/-- **The Theorem for a shell, 1° in its full form** (the companion of `theoreme_poche_balayable`,
whose statement is unchanged): a connected sweepable `V` with a shell `(P, H̊, φ, z)` has a
compatible chart `φ̃` with source `V`, inducing `φ` on `P`, with `P = φ̃⁻¹(D ∩ φ̃(V))` (1°); if `P`
is simply connected so is `V` (2°); `φ̃(V)` is convex (3°); if the shell is strict, `φ̃(V)` is the
interior of a convex body (4°). -/
theorem theoreme_poche_balayable_coque_proj [PreconnectedSpace V]
    (hbal : IsBalayable (GSR n) (S n) V) (hC : IsCoqueProj P l φ z) :
    ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧
      EqOn φ' φ P ∧ P = φ' ⁻¹' (demiEspace z ∩ range φ') ∧
      (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧ Sphere.IsConvexPart (range φ') ∧
      (IsCoqueStricteProj P l φ z →
        ∃ K : Set (S n), IsCorpsConvexeS n K ∧ range φ' = interior K) := by
  obtain ⟨φ', hφ', hs, hφ'φ, -, -, h2, h3, h4⟩ := theoreme_poche_balayable hbal hC.1
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  exact ⟨φ', hφ', hs, hφ'φ, poche_eq_preimage_of_coque_proj hbal hC hp hφ'φ, h2, h3 hC, h4⟩

end PremierFull

/-! ### The printed statements, over the paper's manifolds -/

/-- **The Theorem as printed, 1° in its full form, for the shells**, over the paper's manifolds
(Hausdorff, connected, second countable; `V : Type`). -/
def TheoremeCoquePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V], IsBalayable (GSR n) (S n) V →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsCoqueProj P l φ z → ∃ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧ P = φ' ⁻¹' (demiEspace z ∩ range φ') ∧
        (SimplyConnectedSpace P → SimplyConnectedSpace V) ∧ Sphere.IsConvexPart (range φ') ∧
        (IsCoqueStricteProj P l φ z → ∃ K : Set (S n), IsCorpsConvexeS n K ∧ range φ' = interior K)

/-- **The Theorem as printed holds for every shell, in every dimension.** -/
theorem theoremeCoquePrinted (n : ℕ) : TheoremeCoquePrinted n := by
  intro V _ _ _ _ _ _ hbal P l _ φ z hC
  exact theoreme_poche_balayable_coque_proj hbal hC

/-- **The connectedness the proof of 1°c presumes holds in dimension `n ≤ 1`.** -/
theorem connexePrinted_of_le_one_proj {n : ℕ} (hn : n ≤ 1) : ConnexePrinted n := by
  intro V _ _ _ _ _ _ hbal P l _ φ z hP φ' hφ' hs hφ'φ
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  exact (poche_eq_preimage_iff hbal hP hp hφ'φ).1
    (poche_eq_preimage_of_le_one_proj hn hbal hP hp hφ'φ)

/-- **1° holds as printed, full form included, in dimension `n ≤ 1`.** -/
theorem premierPrinted_of_le_one_proj {n : ℕ} (hn : n ≤ 1) : PremierPrinted n :=
  (premierPrinted_iff n).2 (connexePrinted_of_le_one_proj hn)

/-- **The Theorem holds as printed, full form of 1° included, in dimension `n ≤ 1`.** -/
theorem theoremePrinted_of_le_one_proj {n : ℕ} (hn : n ≤ 1) : TheoremePrinted n :=
  (theoremePrinted_iff n).2 (connexePrinted_of_le_one_proj hn)

/-- **What remains open of OQ-71**: the connectedness of `D ∩ φ̃(V)` for the pockets that are not
shells, are not all of `V` (so have a non-constant cote, `not_cote_eq_zero_of_ne_univ_proj`), and
for whose chart `φ̃` the trace `φ̃(V) ∩ H̊` is star-shaped (in the affine space `H̊`) about no point
of cote `< 1`, over the paper's manifolds. The third restriction implies the first
(`exists_starConvex_of_coque_proj`); « not a shell » is kept so that the definition reads as the
roadmap's sharpened form. -/
def ConnexeOuvertPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V], IsBalayable (GSR n) (S n) V →
    ∀ (P : Set V) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph V (S n)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsPocheProj P l φ z → ¬ IsCoqueProj P l φ z → P ≠ univ →
      ∀ φ' : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ' → φ'.source = univ →
        EqOn φ' φ P →
        (∀ c : Sphere.openHemisphere l, z c < 1 →
          ¬ ∀ y ∈ ((↑) ⁻¹' range φ' : Set (Sphere.openHemisphere l)),
            affineSegment ℝ c y ⊆ (↑) ⁻¹' range φ') →
        IsPreconnected (demiEspace z ∩ range φ')

/-- **OQ-71 sharpened**: the connectedness the proof of 1°c presumes is equivalent to its case
`ConnexeOuvertPrinted n` (a pocket that is not a shell, other than `V`, `φ̃(V) ∩ H̊` star-shaped
about no point of `D`); every other pocket is settled here. -/
theorem connexePrinted_iff_ouvert_proj (n : ℕ) : ConnexePrinted n ↔ ConnexeOuvertPrinted n := by
  constructor
  · intro h V _ _ _ _ _ _ hbal P l _ φ z hP _ _ φ' hφ' hs hφ'φ _
    exact h V hbal P l φ z hP φ' hφ' hs hφ'φ
  · intro h V _ _ _ _ _ _ hbal P l _ φ z hP φ' hφ' hs hφ'φ
    have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
    by_cases hC : IsCoqueProj P l φ z
    · exact (poche_eq_preimage_iff hbal hP hp hφ'φ).1
        (poche_eq_preimage_of_coque_proj hbal hC hp hφ'φ)
    by_cases hPu : P = univ
    · exact (poche_eq_preimage_iff hbal hP hp hφ'φ).1
        (poche_eq_preimage_of_eq_univ_proj hP hφ'φ hPu)
    by_cases hst : ∃ c : Sphere.openHemisphere l, z c < 1 ∧
        ∀ y ∈ ((↑) ⁻¹' range φ' : Set (Sphere.openHemisphere l)),
          affineSegment ℝ c y ⊆ (↑) ⁻¹' range φ'
    · obtain ⟨c, hc, hstar⟩ := hst
      exact (poche_eq_preimage_iff hbal hP hp hφ'φ).1
        (poche_eq_preimage_of_starConvex_proj hbal hP hp hφ'φ hc hstar)
    exact h V hbal P l φ z hP hC hPu φ' hφ' hs hφ'φ fun c hc hstar => hst ⟨c, hc, hstar⟩

/-- **The Theorem as printed is exactly the open case of OQ-71.** -/
theorem theoremePrinted_iff_ouvert_proj (n : ℕ) : TheoremePrinted n ↔ ConnexeOuvertPrinted n :=
  (theoremePrinted_iff n).trans (connexePrinted_iff_ouvert_proj n)

/-- **The open case is empty in dimension `n ≤ 1`**: there every pocket is a shell. -/
theorem connexeOuvertPrinted_of_le_one_proj {n : ℕ} (hn : n ≤ 1) : ConnexeOuvertPrinted n := by
  intro V _ _ _ _ _ _ _ P l _ φ z hP hC
  exact absurd (isCoqueProj_of_le_one_proj hn hP) hC

/-! ### Non-vacuity: the strict shell `]0, 1[` of `]0, ∞[`, a non-constant cote -/

section DemiDroite

attribute [local instance] projOfAff hasGroupoid_projOfAff

/-- **(iii) and the companion assembly at a shell with a non-constant cote and `P ≠ V`**: the half
line `]0, ∞[` (canonical projective structure), sweepable by its homotheties, with the strict shell
`P = ]0, 1[`; the cote is not constant, and `P = φ̃⁻¹(D ∩ φ̃(V))`, with 2°–4°. -/
theorem poche_eq_preimage_demiDroite_coque_proj :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (S 1))
      (z : Sphere.openHemisphere (Sphere.lastForm 1) →ᵃ[ℝ] ℝ),
      IsCoqueStricteProj P (Sphere.lastForm 1) φ z ∧ P ≠ univ ∧ (¬ ∀ y, z y = 0) ∧
      ∃ φ' : OpenPartialHomeomorph demiDroiteOuverte (S 1), IsCompatibleChart (GSR 1) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧ P = φ' ⁻¹' (demiEspace z ∩ range φ') ∧
        SimplyConnectedSpace demiDroiteOuverte ∧ Sphere.IsConvexPart (range φ') ∧
        ∃ K : Set (S 1), IsCorpsConvexeS 1 K ∧ range φ' = interior K := by
  obtain ⟨P, φ, z, hC, hne, hsc, -⟩ := theoreme_poche_balayable_demiDroite
  have hconv : IsPreconnected ((demiDroiteOuverte : Set (Fin 1 → ℝ))) :=
    ((convex_Ioi (0 : ℝ)).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).isPreconnected
  haveI : PreconnectedSpace demiDroiteOuverte := Subtype.preconnectedSpace hconv
  obtain ⟨φ', h1, h2, h3, h4, h5, h6, h7⟩ :=
    theoreme_poche_balayable_coque_proj isBalayable_demiDroite hC.1
  have hz := not_cote_eq_zero_of_ne_univ_proj isBalayable_demiDroite hC.1.1 hne
  exact ⟨P, φ, z, hC, hne, hz, φ', h1, h2, h3, h4, h5 hsc, h6, h7 hC⟩

/-- **(i) at an `n = 1` pocket with a non-constant cote and `P ≠ V`**: the pocket `]0, 1[` of
`]0, ∞[` of `theoreme_premier_demiDroite`, given as a pocket only, through the dimension argument
(`poche_eq_preimage_of_le_one_proj`, which recovers its shell structure). -/
theorem poche_eq_preimage_demiDroite_le_one_proj :
    ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (S 1))
      (z : Sphere.openHemisphere (Sphere.lastForm 1) →ᵃ[ℝ] ℝ),
      IsPocheProj P (Sphere.lastForm 1) φ z ∧ P ≠ univ ∧ (¬ ∀ y, z y = 0) ∧
      ∃ φ' : OpenPartialHomeomorph demiDroiteOuverte (S 1), IsCompatibleChart (GSR 1) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧ P = φ' ⁻¹' (demiEspace z ∩ range φ') := by
  obtain ⟨P, φ, z, hP, hne, φ', h1, h2, h3, -⟩ := theoreme_premier_demiDroite
  have hconv : IsPreconnected ((demiDroiteOuverte : Set (Fin 1 → ℝ))) :=
    ((convex_Ioi (0 : ℝ)).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).isPreconnected
  haveI : PreconnectedSpace demiDroiteOuverte := Subtype.preconnectedSpace hconv
  have hp : IsDeveloping (GSR 1) φ' := fun x => h1 x (h2.symm ▸ mem_univ x)
  have hz := not_cote_eq_zero_of_ne_univ_proj isBalayable_demiDroite hP hne
  exact ⟨P, φ, z, hP, hne, hz, φ', h1, h2, h3,
    poche_eq_preimage_of_le_one_proj le_rfl isBalayable_demiDroite hP hp h3⟩

end DemiDroite

end Benzecri
