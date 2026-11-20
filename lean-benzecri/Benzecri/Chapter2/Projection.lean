import Benzecri.Chapter2.Poches

/-!
# Chapter 2 § 3, Prop. 1 — a sweepable affine manifold étalé over `ℝⁿ` has a segment from a compact generating domain whose end leaves any given compact set

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 3, journal pp. 256–257; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex`. Target T-bz-c2-projection (DEC-137).

* `bzprop:c2s3p1_projection_non_bornee` — `benzecri1960_ch2.tex:648` (Prop. 1, l.648–654, proof
  l.656–716) — **not marked** (see SCOPE, first item): the printed statement is false in dimension
  `0` (`projectionNonBorneePrinted_iff`: the printed form `ProjectionNonBorneePrinted n` holds iff
  `0 < n`). Proved, sorry-free: `Benzecri.projection_non_bornee` (the statement for `n ≥ 1` and
  `V` nonempty, with no Hausdorffness, connectedness or countability of `V`), and in
  every dimension `Benzecri.projection_non_bornee_of_ne_univ` (`K ≠ ℝⁿ`, automatic for `n ≥ 1`).
  Corollary for result B (« une projection non bornée »): `not_isBounded_range_of_isBalayable`.
  The hypotheses are satisfiable: `projection_non_bornee_hypotheses_model` (`ℝⁿ`, `p = id`,
  `E = {0}`, swept by the translations `translationAut`).

> **Proposition 1.** Soit $V$ une variété localement affine balayable munie d'une projection $p$
> sur $\R^n$ compatible avec la structure affine ($V$ est un ouvert étalé au-dessus de $\R^n$).
> Soit $E$ un domaine générateur compact de $V$; soit $K$ un compact de $\R^n$. Il existe un
> segment $(M, N)$ de $V$, tel que $M\in E$, $p(N)\notin K$.
>
> [Proof, l.669–714:] 1° Soit $k$ un nombre réel positif. Il existe un segment $(A, B)$ de $V$
> jouissant de la propriété suivante : Soit $(M, B)$ un segment de $V$ tel que
> $(A, B)\subset(M, B)$. Alors on a $\overline{ma}/\overline{ab}<k$ […]. Soit $(a, b)$ un
> segment fermé de $l$ tel que $\overline{fa}/\overline{fb}<k$. […]
> 2° Supposons désormais $\R^n$ muni d'une métrique euclidienne. Il existe un nombre $r$ positif
> tel que tout point de $E$ admette un voisinage $U$, tel que la restriction de $p$ à $U$
> définisse une carte sur une boule fermée de rayon $r$. […]
> 3° Il existe un segment $(A', B')$ de $V$ dont l'origine $A'$ appartient à $E$ et qui se projette
> par $p$ sur un segment de longueur supérieure à $r/k$. […]
> 4° […] Soit $R$ le diamètre du compact $p(E)\cup K$ de $\R^n$. Choisissons $k$ tel que
> $r/k>R$. Le segment $(A', B')$ construit dans 3° vérifie la propriété $A'\in E$;
> $p(B')\notin K$.

## The proof formalized (the paper's 1°–4°, without its case distinction a / b)

Fix `x ∈ E` and a direction `u ≠ 0` (here `n ≥ 1`), and let `T` be the set of `t` such that some
segment `(x, N)` has `p(N) = p(x) + t·u`. If `T` is unbounded, a segment from `x` already leaves
`K`. Otherwise let `τ = sup T > 0` and take a segment `(x, A)` of length `t₀` close to `τ`: this
is 1°'s segment, `(A, B) = (A, x)`: its extensions `(M, x)` beyond `A` have `ma/ax ≤ (τ − t₀)/t₀`.
Move `A` into `E` by an automorphism `h` (sweepability);
`h(x, A)` is a segment (`IsAffSegment.image_smul_aut`); extend it beyond `hA ∈ E` by the uniform
radius `r` of 2° (`exists_uniform_chart_radius`, `IsAffSegment.extend`); pull the extension back
by `h⁻¹`. Along a segment, `p ∘ h⁻¹ = γ ∘ p` for one `γ ∈ GA(n, ℝ)` (`IsAffSegment.exists_eqOn_smul`,
Ch. 1 Prop. 1), so ratios on the line are kept: the pulled-back segment from `x` ends over
`p(x) + (1 + r/|a'b'|) t₀ u`, so `(1 + r/|a'b'|) t₀ ≤ τ` (3°), with `a' = p(hA)`, `b' = p(hx)`,
i.e. `|a'b'| ≥ r t₀/(τ − t₀)`, which exceeds the diameter of
`p(E) ∪ K` when `t₀` is close to `τ` (4°). The components of `p⁻¹(l)`, the closed lines `L` of
case a, and the Hausdorffness of `V` they need are never used.

Segments are handled through the developing map: `(M, N)` is a segment of `V` iff it is a compact
set containing `M`, `N`, on which `p` is injective with image `[p M, p N]`
(`isAffSegment_iff_of_isDeveloping`, from Mathlib's `Set.InjOn.exists_mem_nhdsSet`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $V$ une variété localement affine » | ⚠ weakened: `[ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]`; Hausdorff, connected, second countable never used. `[Nonempty V]`: « variété » is nonempty (DEC-128; for `V = ∅`, `E = ∅` and no segment exists) |
| the dimension `n` | ⚠ strengthened: `[NeZero n]` in `projection_non_bornee`: the printed statement is false for `n = 0` (finding; `projectionNonBorneePrinted_iff`); `projection_non_bornee_of_ne_univ` holds for every `n` with `K ≠ ℝⁿ` |
| « balayable » | ✓ implied by the next row (`⟨E, hEc, hE⟩ : IsBalayable …`, Déf. 15), not assumed separately |
| « une projection $p$ sur $\R^n$ compatible avec la structure affine ($V$ est un ouvert étalé au-dessus de $\R^n$) » | ✓ carried: `IsDeveloping (GAR n) p` (every jet of `p` in `J(V)`, Ch. 1 Prop. 2; equivalently a morphism to `ℝⁿ`, `isDeveloping_iff_isGXMorphism`); « sur » is not read as « onto » (an « ouvert étalé au-dessus de »), so no surjectivity |
| « $E$ un domaine générateur compact de $V$ » | ✓ carried: `IsCompact E` and `⋃ g ∈ ⊤, g • E = univ` over `GXAut (GAR n) (Fin n → ℝ) V`, the affine automorphisms (Déf. 15) |
| « $K$ un compact de $\R^n$ » | ✓ carried |
| « un segment $(M, N)$ de $V$ » | ✓ carried: `IsAffSegment n Sg M N` (Ch. 1, Déf. 14), the set `Sg` existential |
| « $M\in E$, $p(N)\notin K$ » | ✓ carried |
| 2°: « $\R^n$ muni d'une métrique euclidienne » | the proof uses the sup norm of `Fin n → ℝ`; the statement involves no metric |

## SCOPE (disclosed)

* **Finding: the statement is false in dimension `0`** (no row mark until a ruling). For
  `n = 0`, `V = ℝ⁰` (a point), `p = id`, `E = K = ℝ⁰` satisfy every hypothesis, and no `N` has
  `p(N) ∉ ℝ⁰` (`projectionNonBorneePrinted_iff`, `→`). The printed proof uses a line of `ℝⁿ`
  (cases a and b, 1°), so `n ≥ 1`. This is the question of OQ-45 (a) (« `n ≥ 1` is implied
  throughout »): if the author so rules, `projection_non_bornee` is the paper's statement with
  fewer hypotheses and the label can be marked on it as it stands.
* **Finding in the proof, l.682–683**: « $\overline{fa}/\overline{fb}<k$ » (checked on the scan,
  p. 256: printed so) does not give 1°'s « $\overline{ma}/\overline{ab}<k$ ». With `f, a, b` in
  this order, the points `m` of the segments `(M, B) ⊇ (A, B)` fill `)f, a]`, so 1° holds for
  `(a, b)` iff `fa/ab ≤ k`; `fa/fb < k` gives only `fa/ab < k/(1 − k)` for `k < 1`, and nothing for
  `k ≥ 1` (`fa < fb` always). Read `fa/ab < k`, or take `a` close enough to `f`. The statement is
  unaffected; the formalized proof does not follow 1° (above).
* **The printed proof uses Hausdorffness, the statement does not** (argued, not formalized). In
  case b, 1°, the planner's reading [r] (a component `S` of `p⁻¹(l)` is an arc on which `p` is
  injective) holds for `V` Hausdorff, and 1° needs it: the line with two origins, étalé over `ℝ`,
  is sweepable (the generating domain `{0₁, 1}` under the maps `x ↦ a x`, `a ≠ 0`, and the exchange
  of the two origins), has no closed `L` as in case a (a copy of `ℝ` has the other origin in its
  closure), and its `p⁻¹(ℝ)` is all of `V`, with `p(S) = ℝ`, neither `)f, g(` nor `)f, ∞(`. The
  formalized proof needs neither Hausdorffness nor connectedness.
* `ProjectionNonBorneePrinted n` quantifies over `V : Type`: enough for the counterexample; the
  theorems are universe-polymorphic.
* Tools of general use (candidates to move upstream at graduation): `isAffSegment_iff_of_isDeveloping`,
  `isAffSegment_of_isDeveloping`, `IsAffSegment.isCompact_injOn_image`, `IsAffSegment.image_smul_aut`,
  `IsAffSegment.exists_eqOn_smul`, `IsDeveloping.exists_eqOn_smul_chart`, `IsAffSegment.extend`,
  `isAffSegment_chart_piece`, `exists_uniform_chart_radius`, `IsAffSegment.symm`,
  `isCompact_segment_real`, `exists_smul_mem_of_iUnion_eq_univ`, `translationAut`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

namespace Benzecri

universe u

/-! ### Segments of `ℝⁿ` are compact -/

/-- A segment of a real normed space is compact. -/
theorem isCompact_segment_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : F) :
    IsCompact (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

section Segments

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]

/-- A segment `(M, N)` is the segment `(N, M)`. -/
theorem IsAffSegment.symm {Sg : Set V} {M N : V} (h : IsAffSegment n Sg M N) :
    IsAffSegment n Sg N M := by
  obtain ⟨φ, hφ, hS, hM, hN, -, himg⟩ := h
  exact ⟨φ, hφ, hS, hN, hM, trivial, by rw [himg, segment_symm]⟩

variable [HasGroupoid V (affGroupoid n)]

/-- A developing map is, on a preconnected part of the source of a compatible chart, one affine
image `γ ∘ φ` of the chart. -/
theorem IsDeveloping.exists_eqOn_smul_chart {q : V → Fin n → ℝ} (hq : IsDeveloping (GAR n) q)
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} (hφ : IsCompatibleChart (GAR n) φ) {Sg : Set V}
    (hS : IsPreconnected Sg) (hSφ : Sg ⊆ φ.source) {x : V} (hx : x ∈ Sg) :
    ∃ γ : GAR n, ∀ y ∈ Sg, q y = γ • φ y := by
  obtain ⟨γ, hγ⟩ := (isJetStructure_jets (G := GAR n) (X := Fin n → ℝ) (M := V)).transitive x _ _
    (hφ x (hSφ hx)) (hq x)
  rw [Germ.map_coe] at hγ
  have hev : ∀ᶠ y in 𝓝 x, q y = γ • φ y := Germ.coe_eq.1 hγ
  have hψ := hφ.transHomeomorph_smul γ
  have heq := eqOn_of_germ_eq_isDeveloping hψ hq hS hSφ hx (hev.mono fun y hy => hy.symm)
  exact ⟨γ, fun y hy => (heq hy).symm⟩

/-- Two developing maps differ on a segment by one element of `GA(n, ℝ)`. -/
theorem IsAffSegment.exists_eqOn_smul {q₁ q₂ : V → Fin n → ℝ} (h₁ : IsDeveloping (GAR n) q₁)
    (h₂ : IsDeveloping (GAR n) q₂) {Sg : Set V} {M N : V} (hS : IsAffSegment n Sg M N) :
    ∃ γ : GAR n, ∀ y ∈ Sg, q₁ y = γ • q₂ y := by
  have hpre := hS.isPreconnected
  have hM := hS.left_mem
  obtain ⟨φ, hφ, hSφ, -⟩ := hS
  obtain ⟨γ₁, hγ₁⟩ := h₁.exists_eqOn_smul_chart hφ hpre hSφ hM
  obtain ⟨γ₂, hγ₂⟩ := h₂.exists_eqOn_smul_chart hφ hpre hSφ hM
  refine ⟨γ₁ * γ₂⁻¹, fun y hy => ?_⟩
  rw [hγ₁ y hy, hγ₂ y hy, mul_smul, inv_smul_smul]

/-- **A segment read through a developing map**: it is compact, the developing map is injective
on it and maps it onto the segment of `ℝⁿ` of its endpoints. -/
theorem IsAffSegment.isCompact_injOn_image {q : V → Fin n → ℝ} (hq : IsDeveloping (GAR n) q)
    {Sg : Set V} {M N : V} (hS : IsAffSegment n Sg M N) :
    IsCompact Sg ∧ InjOn q Sg ∧ q '' Sg = segment ℝ (q M) (q N) := by
  have hpre := hS.isPreconnected
  have hM := hS.left_mem
  have hN := hS.right_mem
  obtain ⟨φ, hφ, hSφ, -, -, -, himg⟩ := hS
  obtain ⟨γ, hγ⟩ := hq.exists_eqOn_smul_chart hφ hpre hSφ hM
  refine ⟨?_, ?_, ?_⟩
  · have hsub : segment ℝ (φ M) (φ N) ⊆ φ.target := by
      rw [← himg]
      exact (φ.mapsTo.mono_left hSφ).image_subset
    have : Sg = φ.symm '' (φ '' Sg) :=
      (φ.toPartialEquiv.symm_image_image_of_subset_source hSφ).symm
    rw [this, himg]
    exact (isCompact_segment_real _ _).image_of_continuousOn (φ.continuousOn_symm.mono hsub)
  · intro y₁ hy₁ y₂ hy₂ heq
    rw [hγ y₁ hy₁, hγ y₂ hy₂] at heq
    exact φ.injOn (hSφ hy₁) (hSφ hy₂) (MulAction.injective γ heq)
  · have : q '' Sg = γ.toAffineMap '' (φ '' Sg) := by
      rw [image_image]
      exact image_congr fun y hy => hγ y hy
    rw [this, himg, image_segment, hγ M hM, hγ N hN]
    rfl

/-- **Conversely**, a compact part on which a developing map is injective, with image the segment
of `ℝⁿ` between the images of two of its points, is a segment of `V` (Déf. 14): the developing map
is injective on a neighbourhood of a compact set on which it is (`Set.InjOn.exists_mem_nhdsSet`),
and there it is a compatible chart. -/
theorem isAffSegment_of_isDeveloping {q : V → Fin n → ℝ} (hq : IsDeveloping (GAR n) q)
    {Sg : Set V} {M N : V} (hc : IsCompact Sg) (hM : M ∈ Sg) (hN : N ∈ Sg) (hinj : InjOn q Sg)
    (himg : q '' Sg = segment ℝ (q M) (q N)) : IsAffSegment n Sg M N := by
  haveI : Nonempty V := ⟨M⟩
  have hloc := hq.isLocalHomeomorph
  obtain ⟨t, ht, htinj⟩ := hinj.exists_mem_nhdsSet hc (fun _ _ => hq.continuous.continuousAt)
    (fun x _ => by
      obtain ⟨e, hx, he⟩ := hloc x
      refine ⟨e.source, e.open_source.mem_nhds hx, ?_⟩
      rw [he]
      exact e.injOn)
  have hSO : Sg ⊆ interior t := subset_interior_iff_mem_nhdsSet.2 ht
  let φ : OpenPartialHomeomorph V (Fin n → ℝ) :=
    OpenPartialHomeomorph.ofContinuousOpen
      ((htinj.mono interior_subset).toPartialEquiv q (interior t))
      hq.continuous.continuousOn hloc.isOpenMap isOpen_interior
  exact ⟨φ, fun x _ => hq x, hSO, hSO hM, hSO hN, trivial, himg⟩

/-- **Segments through a developing map** (Déf. 14 read off an étalé projection). -/
theorem isAffSegment_iff_of_isDeveloping {q : V → Fin n → ℝ} (hq : IsDeveloping (GAR n) q)
    {Sg : Set V} {M N : V} :
    IsAffSegment n Sg M N ↔
      IsCompact Sg ∧ M ∈ Sg ∧ N ∈ Sg ∧ InjOn q Sg ∧ q '' Sg = segment ℝ (q M) (q N) := by
  refine ⟨fun h => ?_, fun ⟨hc, hM, hN, hinj, himg⟩ =>
    isAffSegment_of_isDeveloping hq hc hM hN hinj himg⟩
  obtain ⟨hc, hinj, himg⟩ := h.isCompact_injOn_image hq
  exact ⟨hc, h.left_mem, h.right_mem, hinj, himg⟩

/-- **An automorphism carries segments to segments**: `g(M, N) = (gM, gN)`. -/
theorem IsAffSegment.image_smul_aut {p : V → Fin n → ℝ} (hp : IsDeveloping (GAR n) p)
    {Sg : Set V} {M N : V} (hS : IsAffSegment n Sg M N) (g : GXAut (GAR n) (Fin n → ℝ) V) :
    IsAffSegment n ((g • ·) '' Sg) (g • M) (g • N) := by
  have hq : IsDeveloping (GAR n) (fun y => p (g⁻¹ • y)) :=
    isDeveloping_iff_isGXMorphism.2
      ((isDeveloping_iff_isGXMorphism.1 hp).comp (GXAut.isGXMorphism g⁻¹))
  obtain ⟨hc, hinj, himg⟩ := hS.isCompact_injOn_image hp
  refine isAffSegment_of_isDeveloping hq (hc.image (continuous_const_smul g))
    (mem_image_of_mem _ hS.left_mem) (mem_image_of_mem _ hS.right_mem) ?_ ?_
  · rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ heq
    simp only [inv_smul_smul] at heq
    rw [hinj hy₁ hy₂ heq]
  · rw [image_image]
    simp only [inv_smul_smul]
    exact himg

omit [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)] in
/-- **The proof's 2°** (l.688–692): for a local homeomorphism `p` and a compact `E`, there is
`r > 0` such that every point `y` of `E` is in the source of a chart equal to `p` on its source
whose target contains the closed ball of radius `r` about `p y`. -/
theorem exists_uniform_chart_radius {p : V → Fin n → ℝ} (hp : IsLocalHomeomorph p) {E : Set V}
    (hE : IsCompact E) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ E, ∃ φ : OpenPartialHomeomorph V (Fin n → ℝ), y ∈ φ.source ∧
      EqOn φ p φ.source ∧ Metric.closedBall (p y) r ⊆ φ.target := by
  have hpc : Continuous p := hp.continuous
  choose e hxe hpe using hp
  have hε : ∀ y, ∃ ε > 0, Metric.ball (p y) ε ⊆ (e y).target := fun y =>
    Metric.isOpen_iff.1 (e y).open_target (p y) (by rw [hpe y]; exact (e y).map_source (hxe y))
  choose ε hεpos hεsub using hε
  let W : V → Set V := fun y => (e y).source ∩ p ⁻¹' Metric.ball (p y) (ε y / 2)
  have hW : ∀ y ∈ E, W y ∈ 𝓝 y := fun y _ =>
    inter_mem ((e y).open_source.mem_nhds (hxe y))
      (hpc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos (hεpos y))))
  obtain ⟨t, -, htcov⟩ := hE.elim_nhds_subcover W hW
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y ∈ t, r < ε y / 2 :=
    (Filter.eventually_all_finset t).2 fun y _ =>
      nhdsWithin_le_nhds (eventually_lt_nhds (half_pos (hεpos y)))
  obtain ⟨r, hr, hrpos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨r, hrpos, fun z hz => ?_⟩
  obtain ⟨y, hyt, hzW⟩ := mem_iUnion₂.1 (htcov hz)
  refine ⟨e y, hzW.1, fun w _ => (congrFun (hpe y) w).symm, fun w hw => hεsub y ?_⟩
  rw [Metric.mem_ball]
  have h1 : dist w (p z) ≤ r := hw
  have h2 : dist (p z) (p y) < ε y / 2 := hzW.2
  have h3 := hr y hyt
  linarith [dist_triangle w (p z) (p y)]

/-- **A segment inside a chart equal to the developing map**: the lift of `[p A, w]`. -/
theorem isAffSegment_chart_piece {p : V → Fin n → ℝ} (hp : IsDeveloping (GAR n) p)
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} (hφp : EqOn φ p φ.source) {A : V}
    (hA : A ∈ φ.source) {w : Fin n → ℝ} (hw : segment ℝ (p A) w ⊆ φ.target) :
    IsAffSegment n (φ.symm '' segment ℝ (p A) w) A (φ.symm w) ∧ p (φ.symm w) = w := by
  have hwt : w ∈ φ.target := hw (right_mem_segment ℝ _ _)
  have hinv : ∀ z ∈ segment ℝ (p A) w, p (φ.symm z) = z := fun z hz => by
    rw [← hφp (φ.map_target (hw hz)), φ.right_inv (hw hz)]
  have hpw : p (φ.symm w) = w := hinv w (right_mem_segment ℝ _ _)
  have hAeq : φ.symm (p A) = A := by rw [← hφp hA, φ.left_inv hA]
  refine ⟨isAffSegment_of_isDeveloping hp
    ((isCompact_segment_real _ _).image_of_continuousOn (φ.continuousOn_symm.mono hw))
    ⟨p A, left_mem_segment ℝ _ _, hAeq⟩ ⟨w, right_mem_segment ℝ _ _, rfl⟩ ?_ ?_, hpw⟩
  · rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩ heq
    rw [hinv z₁ hz₁, hinv z₂ hz₂] at heq
    rw [heq]
  · rw [hpw, image_image, image_congr hinv, image_id']

/-- **Extending a segment beyond an endpoint** (the step of the proof's 3°, l.698–700): a segment
`(A, B)` with `p A ≠ p B`, and a chart equal to `p` at `A` whose target contains the segment from
`p A` to `p B + (1 + c)(p A − p B)`, give a segment `(M', B) ⊇ (A, B)` with
`p M' = p B + (1 + c)(p A − p B)`. -/
theorem IsAffSegment.extend {p : V → Fin n → ℝ} (hp : IsDeveloping (GAR n) p) {Sg : Set V}
    {A B : V} (hS : IsAffSegment n Sg A B) (hAB : p A ≠ p B)
    {φ : OpenPartialHomeomorph V (Fin n → ℝ)} (hφp : EqOn φ p φ.source) (hA : A ∈ φ.source)
    {c : ℝ} (hc : 0 ≤ c)
    (hw : segment ℝ (p A) (AffineMap.lineMap (p B) (p A) (1 + c)) ⊆ φ.target) :
    ∃ (Sg' : Set V) (M' : V), IsAffSegment n Sg' M' B ∧ Sg ⊆ Sg' ∧
      p M' = AffineMap.lineMap (p B) (p A) (1 + c) := by
  set ℓ : ℝ →ᵃ[ℝ] (Fin n → ℝ) := AffineMap.lineMap (p B) (p A) with hℓ
  have hℓinj : Function.Injective ℓ := AffineMap.lineMap_injective ℝ hAB.symm
  have hℓ0 : ℓ 0 = p B := AffineMap.lineMap_apply_zero _ _
  have hℓ1 : ℓ 1 = p A := AffineMap.lineMap_apply_one _ _
  obtain ⟨hP, hpM⟩ := isAffSegment_chart_piece hp hφp hA hw
  set P := φ.symm '' segment ℝ (p A) (ℓ (1 + c)) with hPdef
  set M' := φ.symm (ℓ (1 + c)) with hM'def
  obtain ⟨hPc, hPinj, hPimg⟩ := hP.isCompact_injOn_image hp
  obtain ⟨hSc, hSinj, hSimg⟩ := hS.isCompact_injOn_image hp
  have hPimg' : p '' P = ℓ '' Icc 1 (1 + c) := by
    rw [hPimg, hpM, ← hℓ1, ← image_segment, segment_eq_Icc (by linarith)]
  have hSimg' : p '' Sg = ℓ '' Icc 0 1 := by
    rw [hSimg, ← hℓ1, ← hℓ0, ← image_segment, segment_symm, segment_eq_Icc zero_le_one]
  have key : ∀ y₁ ∈ P, ∀ y₂ ∈ Sg, p y₁ = p y₂ → y₁ = y₂ := by
    intro y₁ h₁ y₂ h₂ heq
    obtain ⟨s₁, hs₁, e₁⟩ : p y₁ ∈ ℓ '' Icc 1 (1 + c) := hPimg' ▸ mem_image_of_mem p h₁
    obtain ⟨s₂, hs₂, e₂⟩ : p y₂ ∈ ℓ '' Icc 0 1 := hSimg' ▸ mem_image_of_mem p h₂
    have h12 : s₁ = s₂ := hℓinj (e₁.trans (heq.trans e₂.symm))
    have hs1 : s₁ = 1 := le_antisymm (h12 ▸ hs₂.2) hs₁.1
    have hpy₁ : p y₁ = p A := by rw [← e₁, hs1, hℓ1]
    have hpy₂ : p y₂ = p A := by rw [← heq, hpy₁]
    rw [hPinj h₁ hP.left_mem hpy₁, hSinj h₂ hS.left_mem hpy₂]
  refine ⟨P ∪ Sg, M', isAffSegment_of_isDeveloping hp (hPc.union hSc)
    (Or.inl hP.right_mem) (Or.inr hS.right_mem) ?_ ?_, subset_union_right, hpM⟩
  · rintro y₁ (h₁ | h₁) y₂ (h₂ | h₂) heq
    · exact hPinj h₁ h₂ heq
    · exact key y₁ h₁ y₂ h₂ heq
    · exact (key y₂ h₂ y₁ h₁ heq.symm).symm
    · exact hSinj h₁ h₂ heq
  · rw [image_union, hPimg', hSimg', ← image_union, union_comm,
      Icc_union_Icc_eq_Icc zero_le_one (by linarith), hpM, ← hℓ0, ← image_segment, segment_symm,
      segment_eq_Icc (by linarith)]

end Segments

/-! ### Prop. 1 -/

section Prop1

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  [HasGroupoid V (affGroupoid n)]

omit [HasGroupoid V (affGroupoid n)] in
/-- A generating domain meets every orbit: every point is moved into `E` by an automorphism. -/
theorem exists_smul_mem_of_iUnion_eq_univ {E : Set V}
    (hE : ⋃ g ∈ (⊤ : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)), g • E = univ) (y : V) :
    ∃ g : GXAut (GAR n) (Fin n → ℝ) V, g • y ∈ E := by
  have hy : y ∈ ⋃ g ∈ (⊤ : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)), g • E := hE ▸ mem_univ y
  obtain ⟨g, -, hyg⟩ := mem_iUnion₂.1 hy
  obtain ⟨e, he, rfl⟩ := mem_smul_set.1 hyg
  exact ⟨g⁻¹, by rwa [inv_smul_smul]⟩

/-- **Chapter 2 § 3, Prop. 1** (`bzprop:c2s3p1_projection_non_bornee`), in dimension `n ≥ 1`:
let `V` be a nonempty locally affine `n`-manifold with a projection `p` to `ℝⁿ` compatible with
the affine structure (a developing map), `E` a compact generating domain of `V` (so `V` is
sweepable), `K` a compact of `ℝⁿ`; there is a segment `(M, N)` of `V` with `M ∈ E`, `p(N) ∉ K`. -/
theorem projection_non_bornee [NeZero n] [Nonempty V] {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) {E : Set V} (hEc : IsCompact E)
    (hE : ⋃ g ∈ (⊤ : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)), g • E = univ)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    ∃ (Sg : Set V) (M N : V), IsAffSegment n Sg M N ∧ M ∈ E ∧ p N ∉ K := by
  -- a point `x` of `E`, a uniform radius `r` on `E` (2°), a bound `ρ` of `p(E) ∪ K`
  obtain ⟨y₀⟩ := ‹Nonempty V›
  obtain ⟨h₀, hx⟩ := exists_smul_mem_of_iUnion_eq_univ hE y₀
  set x := h₀ • y₀ with hxdef
  obtain ⟨r, hr, hrE⟩ := exists_uniform_chart_radius hp.isLocalHomeomorph hEc
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ z ∈ p '' E ∪ K, ‖z‖ ≤ ρ :=
    ((hEc.image hp.continuous).union hK).isBounded.exists_norm_le
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ (p x) (Or.inl (mem_image_of_mem p hx)))
  -- a direction `u ≠ 0` (here `n ≥ 1` is used)
  set u : Fin n → ℝ := fun _ => 1 with hudef
  have hu : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [hudef] at this
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  -- `T`: the lengths of the segments from `x` in the direction `u`
  set T : Set ℝ := {t | ∃ (Sg : Set V) (N : V), IsAffSegment n Sg x N ∧ p N = p x + t • u}
    with hTdef
  obtain ⟨φx, hxφ, hφxp, hφxball⟩ := hrE x hx
  have hs₀ : 0 < r / ‖u‖ := div_pos hr hupos
  have hs₀T : r / ‖u‖ ∈ T := by
    have hmem : p x + (r / ‖u‖) • u ∈ Metric.closedBall (p x) r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hs₀.le, div_mul_cancel₀ _ hupos.ne']
    have hw : segment ℝ (p x) (p x + (r / ‖u‖) • u) ⊆ φx.target :=
      ((convex_closedBall (p x) r).segment_subset (Metric.mem_closedBall_self hr.le) hmem).trans
        hφxball
    obtain ⟨hseg, hpw⟩ := isAffSegment_chart_piece hp hφxp hxφ hw
    exact ⟨_, _, hseg, hpw⟩
  by_cases hT : BddAbove T
  swap
  · -- unbounded `T`: a segment from `x ∈ E` already leaves `K`
    obtain ⟨t, ⟨Sg, N, hSg, hpN⟩, ht⟩ := not_bddAbove_iff.1 hT ((ρ + ‖p x‖) / ‖u‖)
    refine ⟨Sg, x, N, hSg, hx, fun hNK => ?_⟩
    have h1 := hρ (p N) (Or.inr hNK)
    have hsub : t • u = p N - p x := by rw [hpN]; abel
    have h2 : t * ‖u‖ ≤ ‖p N‖ + ‖p x‖ :=
      calc t * ‖u‖ ≤ ‖t‖ * ‖u‖ := mul_le_mul_of_nonneg_right (Real.le_norm_self t) (norm_nonneg _)
        _ = ‖t • u‖ := (norm_smul t u).symm
        _ = ‖p N - p x‖ := by rw [hsub]
        _ ≤ ‖p N‖ + ‖p x‖ := norm_sub_le _ _
    have h3 : ρ + ‖p x‖ < t * ‖u‖ := (div_lt_iff₀ hupos).1 ht
    linarith
  -- bounded `T`, `τ = sup T`: the ratio argument of 1° and 3°
  set τ := sSup T with hτdef
  have hTne : T.Nonempty := ⟨_, hs₀T⟩
  have hτ : 0 < τ := hs₀.trans_le (le_csSup hT hs₀T)
  set D := 2 * ρ with hDdef
  have hrD : 0 < r + D := by positivity
  have hlt : τ * D / (r + D) < τ := by
    rw [div_lt_iff₀ hrD]
    nlinarith
  obtain ⟨t₀, ht₀T, ht₀⟩ := exists_lt_of_lt_csSup hTne hlt
  have ht₀τ : t₀ ≤ τ := le_csSup hT ht₀T
  obtain ⟨Sg₀, A, hSg₀, hpA⟩ := ht₀T
  have ht₀pos : 0 < t₀ := lt_of_le_of_lt (by positivity) ht₀
  -- move `A` into `E`
  obtain ⟨h, hAE⟩ := exists_smul_mem_of_iUnion_eq_univ hE A
  have hSh : IsAffSegment n ((h • ·) '' Sg₀) (h • A) (h • x) := (hSg₀.image_smul_aut hp h).symm
  obtain ⟨-, hShinj, -⟩ := hSh.isCompact_injOn_image hp
  have hne : p (h • A) ≠ p (h • x) := by
    intro heq
    have hAx : A = x := MulAction.injective h (hShinj hSh.left_mem hSh.right_mem heq)
    rw [hAx] at hpA
    have h0 : t₀ • u = 0 := by
      have := congrArg (· - p x) hpA
      simpa using this.symm
    rcases smul_eq_zero.1 h0 with h0 | h0
    · exact ht₀pos.ne' h0
    · exact hu h0
  set a' := p (h • A) with ha'def
  set b' := p (h • x) with hb'def
  set d' := ‖a' - b'‖ with hd'def
  have hd' : 0 < d' := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set c := r / d' with hcdef
  have hc : 0 < c := div_pos hr hd'
  have hcd : c * d' = r := div_mul_cancel₀ _ hd'.ne'
  -- extend `(hA, hx)` beyond `hA ∈ E` by `r` (3°)
  obtain ⟨φ, hAφ, hφp, hφball⟩ := hrE (h • A) hAE
  have hm' : AffineMap.lineMap b' a' (1 + c) ∈ Metric.closedBall a' r := by
    rw [Metric.mem_closedBall, dist_eq_norm, AffineMap.lineMap_apply_module']
    have : (1 + c) • (a' - b') + b' - a' = c • (a' - b') := by module
    rw [this, norm_smul, Real.norm_of_nonneg hc.le, hcd]
  have hw : segment ℝ a' (AffineMap.lineMap b' a' (1 + c)) ⊆ φ.target :=
    ((convex_closedBall a' r).segment_subset (Metric.mem_closedBall_self hr.le) hm').trans hφball
  obtain ⟨Sg', M', hSg', hsub, hpM'⟩ := hSh.extend hp hne hφp hAφ hc.le hw
  -- pull the extension back by `h⁻¹`: a segment from `x`, in the direction `u`
  have hSg'' : IsAffSegment n ((h⁻¹ • ·) '' Sg') x (h⁻¹ • M') := by
    have := hSg'.image_smul_aut hp h⁻¹
    rw [inv_smul_smul] at this
    exact this.symm
  have hq : IsDeveloping (GAR n) (fun y => p (h⁻¹ • y)) :=
    isDeveloping_iff_isGXMorphism.2
      ((isDeveloping_iff_isGXMorphism.1 hp).comp (GXAut.isGXMorphism h⁻¹))
  obtain ⟨γ, hγ⟩ := hSg'.exists_eqOn_smul hq hp
  have hγx : p x = γ • b' := by
    have := hγ (h • x) hSg'.right_mem
    rwa [inv_smul_smul] at this
  have hγA : p A = γ • a' := by
    have := hγ (h • A) (hsub hSh.left_mem)
    rwa [inv_smul_smul] at this
  have hγM : p (h⁻¹ • M') = p x + ((1 + c) * t₀) • u := by
    rw [hγ M' hSg'.left_mem, hpM', affineEquiv_smul_def, AffineEquiv.apply_lineMap,
      ← affineEquiv_smul_def, ← affineEquiv_smul_def, ← hγx, ← hγA, hpA,
      AffineMap.lineMap_apply_module']
    module
  have hle : (1 + c) * t₀ ≤ τ := le_csSup hT ⟨_, _, hSg'', hγM⟩
  -- so `|a' b'|` is large, and `p(hx) ∉ K` (4°)
  refine ⟨_, _, _, hSh, hAE, fun hbK => ?_⟩
  have ha' : ‖a'‖ ≤ ρ := hρ a' (Or.inl (mem_image_of_mem p hAE))
  have hb' : ‖b'‖ ≤ ρ := hρ b' (Or.inr hbK)
  have hdD : d' ≤ D := (norm_sub_le a' b').trans (by linarith)
  have h1 : r * t₀ ≤ (τ - t₀) * d' := by
    have : (1 + c) * t₀ * d' ≤ τ * d' := mul_le_mul_of_nonneg_right hle hd'.le
    nlinarith
  have h2 : (τ - t₀) * d' ≤ (τ - t₀) * D := mul_le_mul_of_nonneg_left hdD (by linarith)
  have h4 : t₀ ≤ τ * D / (r + D) := by
    rw [le_div_iff₀ hrD]
    nlinarith
  linarith

/-- **Prop. 1 in every dimension, for `K ≠ ℝⁿ`** (automatic for `n ≥ 1`, `ℝⁿ` not being
compact; in dimension `0` it leaves `K = ∅`). -/
theorem projection_non_bornee_of_ne_univ [Nonempty V] {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) {E : Set V} (hEc : IsCompact E)
    (hE : ⋃ g ∈ (⊤ : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)), g • E = univ)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKu : K ≠ univ) :
    ∃ (Sg : Set V) (M N : V), IsAffSegment n Sg M N ∧ M ∈ E ∧ p N ∉ K := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨y₀⟩ := ‹Nonempty V›
    obtain ⟨g, hx⟩ := exists_smul_mem_of_iUnion_eq_univ hE y₀
    have hK0 : K = ∅ := by
      rcases Set.eq_empty_or_nonempty K with h | ⟨z, hz⟩
      · exact h
      · exact absurd (eq_univ_of_forall fun w => (Subsingleton.elim w z) ▸ hz) hKu
    refine ⟨{g • y₀}, g • y₀, g • y₀, isAffSegment_of_isDeveloping hp isCompact_singleton rfl rfl
      (injOn_singleton _ _) (by rw [image_singleton, segment_same]), hx, by simp [hK0]⟩
  · haveI : NeZero n := ⟨hn.ne'⟩
    exact projection_non_bornee hp hEc hE hK

/-- **« une projection non bornée »** (result B of the introduction; « la proposition 1 énonce
un résultat plus fort »): a nonempty sweepable locally affine `n`-manifold, `n ≥ 1`, with a
developing map `p`, has `p(V)` unbounded. -/
theorem not_isBounded_range_of_isBalayable [NeZero n] [Nonempty V] {p : V → Fin n → ℝ}
    (hp : IsDeveloping (GAR n) p) (hV : IsBalayable (GAR n) (Fin n → ℝ) V) :
    ¬ Bornology.IsBounded (range p) := by
  intro hb
  obtain ⟨E, hEc, hE⟩ := hV
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  obtain ⟨-, -, N, -, -, hN⟩ := projection_non_bornee hp hEc hE (isCompact_closedBall 0 R)
  exact hN (hR (mem_range_self N))

end Prop1

/-! ### Non-vacuity: the model `ℝⁿ`, swept from one point by its translations -/

section Model

variable {n : ℕ}

/-- The translation `v ↦ w + v`, an automorphism of the model `ℝⁿ` (Déf. 15). -/
def translationAut (w : Fin n → ℝ) : GXAut (GAR n) (Fin n → ℝ) (Fin n → ℝ) :=
  GXAut.ofBijective (f := fun v => w + v)
    (isGXMorphism_iff_model.2 ⟨continuous_const.add continuous_id, fun _ =>
      ⟨GAR.translation w, Eventually.of_forall fun y => by
        simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq,
          affineEquiv_smul_def, GAR.translation, AffineEquiv.constVAdd_apply, vadd_eq_add]⟩⟩)
    (Equiv.addLeft w).bijective

theorem translationAut_smul (w v : Fin n → ℝ) : translationAut w • v = w + v := rfl

/-- **The hypotheses of Prop. 1 are satisfiable**: the model `ℝⁿ`, with `p = id`, is swept by its
translations from the compact generating domain `{0}`. -/
theorem projection_non_bornee_hypotheses_model :
    IsDeveloping (GAR n) (id : (Fin n → ℝ) → Fin n → ℝ) ∧ IsCompact ({0} : Set (Fin n → ℝ)) ∧
      ⋃ g ∈ (⊤ : Subgroup (GXAut (GAR n) (Fin n → ℝ) (Fin n → ℝ))),
        g • ({0} : Set (Fin n → ℝ)) = univ :=
  ⟨isDeveloping_iff_isGXMorphism.2 isGXMorphism_id, isCompact_singleton,
    eq_univ_of_forall fun y => mem_iUnion₂.2 ⟨translationAut y, Subgroup.mem_top _,
      by rw [smul_set_singleton, translationAut_smul, add_zero]; rfl⟩⟩

end Model

/-! ### The printed form, and dimension `0` -/

/-- **The printed statement of Prop. 1** in dimension `n` (l.648–654), as a proposition, for
every locally affine `n`-manifold `V` in `Type`. The reading « variété » ⇒ nonempty is built in
(`[Nonempty V]`), so that what fails below is the dimension, not the empty manifold. -/
def ProjectionNonBorneePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [Nonempty V] (p : V → Fin n → ℝ), IsDeveloping (GAR n) p → ∀ E : Set V, IsCompact E →
    ⋃ g ∈ (⊤ : Subgroup (GXAut (GAR n) (Fin n → ℝ) V)), g • E = univ →
    ∀ K : Set (Fin n → ℝ), IsCompact K →
      ∃ (Sg : Set V) (M N : V), IsAffSegment n Sg M N ∧ M ∈ E ∧ p N ∉ K

/-- **The printed form holds exactly in dimension `n ≥ 1`**: in dimension `0`, `V = ℝ⁰` (a
point, `p = id`, `E = K = ℝ⁰`) satisfies every hypothesis and no `N` has `p(N) ∉ ℝ⁰`. -/
theorem projectionNonBorneePrinted_iff (n : ℕ) : ProjectionNonBorneePrinted n ↔ 0 < n := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have hdev : IsDeveloping (GAR 0) (id : (Fin 0 → ℝ) → Fin 0 → ℝ) :=
        isDeveloping_iff_isGXMorphism.2 isGXMorphism_id
      obtain ⟨-, -, N, -, -, hN⟩ := h (Fin 0 → ℝ) id hdev univ isCompact_univ
        (eq_univ_of_forall fun y => mem_iUnion₂.2 ⟨1, Subgroup.mem_top 1, by simp⟩)
        univ isCompact_univ
      exact hN (mem_univ _)
    · exact hn
  · intro hn V _ _ _ _ p hp E hEc hE K hK
    haveI : NeZero n := ⟨hn.ne'⟩
    exact projection_non_bornee hp hEc hE hK

end Benzecri
