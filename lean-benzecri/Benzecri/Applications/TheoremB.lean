import Benzecri.Chapter2.Theoreme
import Benzecri.Chapter2.Projection
import Benzecri.UniversalCoverRow
import Benzecri.Applications.TheoremA

/-!
# `Benzecri.Applications.TheoremB` — the introduction's result B, all but the affine half of its first sentence

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Introduction, § 1 « Les résultats », journal pp. 230–231; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Roadmap target `T-bz-result-b-proj`.

* `bzthm:intro_B` — `benzecri1960_ch1.tex:86` (l.86–105, résumé B; its three sentences l.87–99,
  introduced by l.80–84). **Not marked** (SCOPE): the affine half of sentence 1 is
  T-bz-result-b's, and sentence 3 holds for `n ≥ 1` only (OQ-45 (a)). Proved here, sorry-free,
  for every simply connected covering `π : N → V` of a compact Hausdorff `V`, `N` carrying a
  structure for which `π` is a morphism, then for the universal cover `W = UniversalCover V v₀`:
  - l.81–84, `W` is a connected, Hausdorff, divisible, sweepable « ouvert étalé » over `S(n)`
    (resp. `ℝⁿ`): `resultB_revetement_proj`, `_aff`, `resultB_revetementUniversel_proj`, `_aff`;
  - sentence 1, projective half: `resultB_poche_proj`, `resultB_premiere_proj`;
  - sentence 2: `resultB_coque_stricte`, `resultB_hemisphere`, `resultB_deuxieme`; the strict
    shell gives the hemisphere condition, `resultB_coque_stricte_hemisphere`;
  - sentence 3, `n ≥ 1`: `resultB_projection_non_bornee`, `resultB_troisieme`; Prop. 1 on `N`
    (« un résultat plus fort »): `resultB_projection_plus_forte`;
  - sentence 3 fails for `n = 0`: `resultB_isBounded_dim_zero`, `resultBTroisiemePrinted_iff`;
  - over the paper's manifolds: `ResultBProjPrinted`, `resultBProjPrinted` (every `n`),
    `ResultBTroisiemePrinted`, `resultBTroisiemePrinted_iff` (`↔ 0 < n`);
  - non-vacuity: `resultB_nonVacuite_hopf` (the Hopf circle `]0, ∞[ / 2^ℤ`, `n = 1`, a strict
    shell `P ≠ W` and the hemisphere condition), `resultB_troisieme_hopf` (`S(m) × S¹`, every
    `m`), `resultB_revetementUniversel_sphere`, `resultB_nonVacuite_dim_zero` (`S(0)`).

> Les deux autres résultats concernent le revêtement universel d'une variété localement affine
> (resp. projective) compacte : ce revêtement est muni d'une structure d'ouvert étalé au-dessus de
> l'espace affin (resp. de la sphère projective) (*cf.* chap. 1, § 1).
>
> **B.** Si le revêtement universel d'une variété localement affine ou projective compacte possède
> une poche (resp. coque), ce revêtement s'identifie à un ouvert (resp. à un convexe) de l'espace
> affin, ou de la sphère projective (*cf.* chap. 2, § 3, théorème).
>
> Si le revêtement universel $W$ d'une variété localement projective compacte possède une coque
> stricte, ou si $W$ considéré comme ouvert étalé, a une projection sur la sphère projective dont
> la fermeture est incluse dans un hémisphère ouvert, $W$ s'identifie à l'intérieur d'un corps
> convexe de la sphère projective (*cf.* chap. 2, § 3, théorème et prop. 2).
>
> Le revêtement universel d'une variété localement affine compacte, considérée comme ouvert étalé
> au-dessus de l'espace affin, a une projection non bornée (*cf.* chap. 2, § 3 : la proposition 1
> énonce un résultat plus fort).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` « une variété localement projective (resp. affine) » | ✓ carried: `[ChartedSpace (S n) V]` (resp. `Fin n → ℝ`); `[HasGroupoid V _]` for the universal cover (its structure is pulled back); « variété »: Hausdorff ✓ carried (`[T2Space V]`: `W` Hausdorff, divisibility); connected, second countable ⚠ weakened (unused; the printed forms carry them) |
| `V` « compacte » | ✓ carried: `[CompactSpace V]` |
| « le revêtement universel » `W` | ✓ carried: `UniversalCover V v₀`, pulled-back structure; and more (Lean ≥ paper): every simply connected covering `π : N → V`, `N` locally projective (resp. affine), `π` a morphism |
| `W` « possède une poche (resp. coque) » | ✓ carried: `IsPocheProj P l φ z` (resp. `IsCoqueProj`) on `W` (Ch. 2 Déf. 1′, 2) |
| `W` « possède une coque stricte » | ✓ carried: `IsCoqueStricteProj P l φ z` (Ch. 2 Déf. 3) |
| « $W$ … a une projection … dont la fermeture est incluse dans un hémisphère ouvert » | ✓ carried for EVERY projection: `IsDeveloping (GSR n) p`, `Sphere.IsOpenHemisphere H`, `closure (range p) ⊆ H` |
| « considérée comme ouvert étalé au-dessus de l'espace affin » | ✓ carried: the developing maps `p : W → ℝⁿ` (one exists, Ch. 1 Prop. 2); the conclusion for EVERY one |
| « s'identifie à un ouvert (resp. à un convexe) » | ✓ carried: a compatible chart `φ̃`, `φ̃.source = univ` (open target), `φ̃ = φ` on `P`; for a shell `Sphere.IsConvexPart φ̃.target`, and more: strict |
| « s'identifie à l'intérieur d'un corps convexe » | ✓ carried: `∃ K, IsCorpsConvexeS n K ∧ ∃ φ̃, IsCompatibleChart (GSR n) φ̃ ∧ φ̃.source = univ ∧ φ̃.target = interior K`, with `φ̃ = φ` on `P` (resp. `⇑φ̃ = p`) |
| « une projection non bornée » | `¬ Bornology.IsBounded (range p)`; ⚠ strengthened by `[NeZero n]` (finding: false for `n = 0`) |
| the dimension | sentences 1–2: every `n`, `n = 0` included; sentence 3: `n ≥ 1` |

## SCOPE (disclosed)

* **The affine half of sentence 1 is not here** (the roadmap split): its pocket part is Ch. 2
  § 3's affine 1° (`Chapter2/PremierAffine.lean`), its shell part the affine 3°
  (T-bz-c2-theoreme-affine). T-bz-result-b assembles the three sentences and marks the row.
* **Sentence 3 is false for `n = 0`** (finding): a compact locally affine `0`-manifold is finite,
  its universal cover a point, and every subset of `ℝ⁰` is bounded (`resultB_isBounded_dim_zero`;
  `resultBTroisiemePrinted_iff`, witness `V = ℝ⁰`). OQ-45 (a)'s question (is `n ≥ 1` implied
  throughout?); no new OQ.
* **What result B uses of Ch. 2 § 3's Theorem**: 1°'s first sentence (the chart,
  `exists_chart_poche`: 1°a, 1°b), 3° and 4° (`theoreme_troisieme`, `theoreme_quatrieme`), and
  Prop. 2 (`hemisphere_corps_convexe`); never 1°'s second sentence (OQ-71, OQ-75), checked on the
  proof terms of every principal declaration (REPORT, notes).
* `W` Hausdorff is not in the strict library: `resultB_t2Space_of_isCoveringMap`, from Mathlib's
  `IsCoveringMap.isSeparatedMap`; the local version of lean-gx's `t2Space_of_isCoveringMap`
  (`GX/Branched/Universality.lean`). Prop. 2 needs it.
* « s'identifie à » is read « is mapped onto by a compatible chart with source `W` », as in
  Ch. 2 § 3, 1° (`theoreme_premier`); « le revêtement universel » of a `V` that is not connected
  is that of the component of `v₀` (as in `Benzecri.UniversalCoverRow`).
* The résumé's closing gloss (l.100–104, « Poche, coque, coque stricte, sont définis … univalent
  (resp. convexe) au voisinage d'un point de sa frontière ») describes Ch. 2 Déf. 1–3 informally
  and is not formalized; the definitions themselves are `IsPocheProj`, `IsCoqueProj`,
  `IsCoqueStricteProj`.
* The Hopf circle is built here (`resultBHopfGroup`, the quotient `V/Γ` of
  `Structure/Quotient.lean`) only as a witness; its charts on `S(1)` are pinned by a `letI`, since
  `projOfAff` also applies to the quotient's affine charts.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

namespace Benzecri

universe u v

/-! ### Simply connected coverings of a compact manifold (l.81–84) -/

section Covering

variable {n : ℕ} {V : Type u} [TopologicalSpace V] {N : Type v} [TopologicalSpace N]
  {π : N → V}

/-- **A covering of a Hausdorff space is Hausdorff**: two points of one fibre are separated by
the sheets of the covering (Mathlib's `IsCoveringMap.isSeparatedMap`), two points of different
fibres by the preimages of disjoint open sets. Local version of lean-gx's
`t2Space_of_isCoveringMap` (`GX/Branched/Universality.lean`). -/
theorem resultB_t2Space_of_isCoveringMap [T2Space V] (hπ : IsCoveringMap π) : T2Space N := by
  refine ⟨fun a b hab => ?_⟩
  by_cases h : π a = π b
  · exact hπ.isSeparatedMap a b h hab
  · obtain ⟨u, w, hu, hw, hau, hbw, huw⟩ := t2_separation h
    exact ⟨π ⁻¹' u, π ⁻¹' w, hu.preimage hπ.continuous, hw.preimage hπ.continuous, hau, hbw,
      huw.preimage π⟩

/-- **l.81–84, projective case** (« ce revêtement est muni d'une structure d'ouvert étalé
au-dessus de … la sphère projective »): a simply connected covering `π : N → V` of a compact
Hausdorff locally projective `V`, with a locally projective structure for which `π` is a morphism,
is path connected, Hausdorff, divisible (p. 238), sweepable, and has a developing map
`p : N → S(n)`, a local homeomorphism (Ch. 1 Prop. 2). -/
theorem resultB_revetement_proj [ChartedSpace (S n) V] [CompactSpace V] [T2Space V]
    [ChartedSpace (S n) N] [HasGroupoid N (projGroupoid n)] [SimplyConnectedSpace N]
    (hπ : IsCoveringMap π) (hπG : IsGXMorphism (GSR n) (S n) π) :
    PathConnectedSpace N ∧ T2Space N ∧ IsDivisible (GSR n) (S n) N ∧
      IsBalayable (GSR n) (S n) N ∧
      ∃ p : N → S n, IsDeveloping (GSR n) p ∧ IsLocalHomeomorph p := by
  haveI := locPathConnectedSpace_of_proj (n := n) (V := V)
  have hdiv : IsDivisible (GSR n) (S n) N := isDivisible_of_isCoveringMap hπ hπG
  obtain ⟨p, hp⟩ := (prop2_developpement_proj (n := n) (V := N)).1
  exact ⟨inferInstance, resultB_t2Space_of_isCoveringMap hπ, hdiv, hdiv.isBalayable_proj, p, hp,
    hp.isLocalHomeomorph⟩

/-- **l.81–84, affine case**: the same over `ℝⁿ`. -/
theorem resultB_revetement_aff [ChartedSpace (Fin n → ℝ) V] [CompactSpace V] [T2Space V]
    [ChartedSpace (Fin n → ℝ) N] [HasGroupoid N (affGroupoid n)] [SimplyConnectedSpace N]
    (hπ : IsCoveringMap π) (hπG : IsGXMorphism (GAR n) (Fin n → ℝ) π) :
    PathConnectedSpace N ∧ T2Space N ∧ IsDivisible (GAR n) (Fin n → ℝ) N ∧
      IsBalayable (GAR n) (Fin n → ℝ) N ∧
      ∃ p : N → (Fin n → ℝ), IsDeveloping (GAR n) p ∧ IsLocalHomeomorph p := by
  haveI := locPathConnectedSpace_of_aff (n := n) (V := V)
  have hdiv : IsDivisible (GAR n) (Fin n → ℝ) N := isDivisible_of_isCoveringMap hπ hπG
  obtain ⟨p, hp⟩ := (prop2_developpement_aff (n := n) (V := N)).1
  exact ⟨inferInstance, resultB_t2Space_of_isCoveringMap hπ, hdiv, hdiv.isBalayable_aff, p, hp,
    hp.isLocalHomeomorph⟩

/-- **The closure of the interior of a convex body lies in an open hemisphere**: if a chart `φ̃`
with source `N` has target `int K`, `K` a convex body, then `closure φ̃(N) ⊆ K` lies in an open
hemisphere (`IsCorpsConvexeS.exists_forall_pos`). -/
theorem resultB_exists_hemisphere_of_target {K : Set (S n)} (hK : IsCorpsConvexeS n K)
    {φ' : OpenPartialHomeomorph N (S n)} (hs : φ'.source = univ) (ht : φ'.target = interior K) :
    ∃ H : Set (S n), Sphere.IsOpenHemisphere H ∧ closure (range φ') ⊆ H := by
  obtain ⟨ℓ, hℓ⟩ := hK.exists_forall_pos
  refine ⟨Sphere.openHemisphere (ℓ : Module.Dual ℝ (Fin (n + 1) → ℝ)),
    Sphere.isOpenHemisphere_iff.2 ⟨_, rfl⟩, ?_⟩
  have hrange : range φ' = interior K := by
    rw [← ht, ← φ'.image_source_eq_target, hs, image_univ]
  have hclK : closure (range φ') ⊆ K := by
    rw [hrange]
    exact (closure_mono interior_subset).trans hK.2.1.isClosed.closure_subset
  intro X hX
  obtain ⟨x, hx0, rfl⟩ := Sphere.exists_isRep X
  exact (Sphere.mk_mem_openHemisphere hx0).2 (hℓ x ⟨hx0, hclK hX⟩)

section Proj

variable [ChartedSpace (S n) V] [CompactSpace V] [T2Space V]
  [ChartedSpace (S n) N] [HasGroupoid N (projGroupoid n)] [SimplyConnectedSpace N]

/-- **Sentence 1, projective half** (l.87–89): if `N` has a pocket `(P, H̊, φ, z)`, it is
identified with an open set of `S(n)` by a compatible chart `φ̃` with source `N`, inducing `φ` on
`P` (Ch. 2 § 3, 1°, first sentence); if the pocket is a shell, `φ̃(N)` is a convex part of `S(n)`
(3°), and even a strict one. -/
theorem resultB_poche_proj (hπ : IsCoveringMap π) (hπG : IsGXMorphism (GSR n) (S n) π)
    {P : Set N} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    {φ : OpenPartialHomeomorph N (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}
    (hP : IsPocheProj P l φ z) :
    ∃ φ' : OpenPartialHomeomorph N (S n), IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧
      EqOn φ' φ P ∧
      (IsCoqueProj P l φ z →
        Sphere.IsConvexPart φ'.target ∧ Sphere.IsStrictConvexPart φ'.target) := by
  obtain ⟨-, -, -, hbal, -⟩ := resultB_revetement_proj hπ hπG
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche hbal hP
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  have ht : φ'.target = range φ' := by rw [← φ'.image_source_eq_target, hs, image_univ]
  refine ⟨φ', hφ', hs, hφ'φ, fun hC => ?_⟩
  have h := theoreme_troisieme hbal hC hp hφ'φ
  rw [ht]
  exact ⟨h.1, h⟩

/-- **Sentence 2, the strict shell** (l.91, 93–94; Ch. 2 § 3, 4°): if `N` has a strict shell
`(P, H̊, φ, z)`, it is identified with the interior of a convex body `K` of `S(n)` by a
compatible chart with source `N`, inducing `φ` on `P`. -/
theorem resultB_coque_stricte (hπ : IsCoveringMap π) (hπG : IsGXMorphism (GSR n) (S n) π)
    {P : Set N} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    {φ : OpenPartialHomeomorph N (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}
    (hC : IsCoqueStricteProj P l φ z) :
    ∃ K : Set (S n), IsCorpsConvexeS n K ∧
      ∃ φ' : OpenPartialHomeomorph N (S n), IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧
        φ'.target = interior K ∧ EqOn φ' φ P := by
  obtain ⟨-, -, -, hbal, -⟩ := resultB_revetement_proj hπ hπG
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche hbal hC.1.1
  have hp : IsDeveloping (GSR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  have ht : φ'.target = range φ' := by rw [← φ'.image_source_eq_target, hs, image_univ]
  obtain ⟨hK, hint⟩ := theoreme_quatrieme hbal hC hp hφ'φ
  exact ⟨_, hK, φ', hφ', hs, by rw [ht, hint], hφ'φ⟩

/-- **Sentence 2, the hemisphere** (l.91–94; Ch. 2 § 3, Prop. 2): if a projection `p` of `N`
(a developing map) has `closure p(N)` inside an open hemisphere, `p` is a compatible chart of `N`
onto the interior of a convex body of `S(n)`. -/
theorem resultB_hemisphere (hπ : IsCoveringMap π) (hπG : IsGXMorphism (GSR n) (S n) π)
    {p : N → S n} (hp : IsDeveloping (GSR n) p) {H : Set (S n)}
    (hH : Sphere.IsOpenHemisphere H) (hcl : closure (range p) ⊆ H) :
    ∃ K : Set (S n), IsCorpsConvexeS n K ∧
      ∃ φ' : OpenPartialHomeomorph N (S n), IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧
        φ'.target = interior K ∧ ⇑φ' = p := by
  obtain ⟨-, hT2, -, hbal, -⟩ := resultB_revetement_proj hπ hπG
  haveI := hT2
  obtain ⟨K, hK, -, hφ⟩ := hemisphere_corps_convexe hp hbal hH hcl
  exact ⟨K, hK, hφ⟩

/-- **In sentence 2 the strict shell gives the hemisphere condition** (through 4°): the chart
`φ̃` of a strict shell is a projection of `N` (a developing map, equal to `φ` on `P`) whose closure
lies in an open hemisphere. -/
theorem resultB_coque_stricte_hemisphere (hπ : IsCoveringMap π)
    (hπG : IsGXMorphism (GSR n) (S n) π)
    {P : Set N} {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    {φ : OpenPartialHomeomorph N (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}
    (hC : IsCoqueStricteProj P l φ z) :
    ∃ p : N → S n, IsDeveloping (GSR n) p ∧ EqOn p φ P ∧
      ∃ H : Set (S n), Sphere.IsOpenHemisphere H ∧ closure (range p) ⊆ H := by
  obtain ⟨K, hK, φ', h1, h2, h3, h4⟩ := resultB_coque_stricte hπ hπG hC
  exact ⟨φ', fun x => h1 x (h2.symm ▸ mem_univ x), h4,
    resultB_exists_hemisphere_of_target hK h2 h3⟩

end Proj

section Aff

variable [ChartedSpace (Fin n → ℝ) V] [CompactSpace V] [T2Space V]
  [ChartedSpace (Fin n → ℝ) N] [HasGroupoid N (affGroupoid n)] [SimplyConnectedSpace N]

/-- **Sentence 3** (l.96–98), `n ≥ 1`: every projection `p : N → ℝⁿ` (developing map; one
exists) of a simply connected covering of a compact locally affine `V` is unbounded. -/
theorem resultB_projection_non_bornee [NeZero n] (hπ : IsCoveringMap π)
    (hπG : IsGXMorphism (GAR n) (Fin n → ℝ) π) :
    (∃ p : N → (Fin n → ℝ), IsDeveloping (GAR n) p) ∧
      ∀ p : N → (Fin n → ℝ), IsDeveloping (GAR n) p → ¬ Bornology.IsBounded (range p) := by
  obtain ⟨-, -, -, hbal, p, hp, -⟩ := resultB_revetement_aff hπ hπG
  exact ⟨⟨p, hp⟩, fun q hq => not_isBounded_range_of_isBalayable hq hbal⟩

/-- **« la proposition 1 énonce un résultat plus fort »** (l.97–98), on `N`, `n ≥ 1`: for every
compact generating domain `E` of `N` (one exists: `N` is sweepable) and every compact `K` of `ℝⁿ`,
some segment `(M, M')` of `N` has `M ∈ E` and `p(M') ∉ K`. -/
theorem resultB_projection_plus_forte [NeZero n] (hπ : IsCoveringMap π)
    (hπG : IsGXMorphism (GAR n) (Fin n → ℝ) π) {p : N → (Fin n → ℝ)}
    (hp : IsDeveloping (GAR n) p) :
    (∃ E : Set N, IsCompact E ∧
      ⋃ g ∈ (⊤ : Subgroup (GXAut (GAR n) (Fin n → ℝ) N)), g • E = univ) ∧
    ∀ E : Set N, IsCompact E →
      ⋃ g ∈ (⊤ : Subgroup (GXAut (GAR n) (Fin n → ℝ) N)), g • E = univ →
      ∀ K : Set (Fin n → ℝ), IsCompact K →
        ∃ (Sg : Set N) (M M' : N), IsAffSegment n Sg M M' ∧ M ∈ E ∧ p M' ∉ K := by
  obtain ⟨-, -, -, hbal, -⟩ := resultB_revetement_aff hπ hπG
  exact ⟨hbal, fun E hEc hE K hK => projection_non_bornee hp hEc hE hK⟩

end Aff

omit [TopologicalSpace N] in
/-- **Sentence 3 fails in dimension `0`**: every projection of a `0`-dimensional affine manifold
is bounded (`ℝ⁰` is a point). -/
theorem resultB_isBounded_dim_zero (p : N → (Fin 0 → ℝ)) : Bornology.IsBounded (range p) := by
  exact (Set.subsingleton_of_subsingleton).finite.isBounded

end Covering

/-! ### The universal cover `W = UniversalCover V v₀` -/

section UniversalCoverProj

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V)

/-- **l.81–84, projective case, for the universal cover**: `W = UniversalCover V v₀` of a compact
Hausdorff locally projective `V` is path connected, Hausdorff, divisible, sweepable and an ouvert
étalé over `S(n)` (a developing map, a local homeomorphism, unique up to `GS(n, ℝ)`). -/
theorem resultB_revetementUniversel_proj :
    PathConnectedSpace (UniversalCover V v₀) ∧ T2Space (UniversalCover V v₀) ∧
      IsDivisible (GSR n) (S n) (UniversalCover V v₀) ∧
      IsBalayable (GSR n) (S n) (UniversalCover V v₀) ∧
      (∃ p : UniversalCover V v₀ → S n, IsDeveloping (GSR n) p ∧ IsLocalHomeomorph p) ∧
      ∀ p p' : UniversalCover V v₀ → S n, IsDeveloping (GSR n) p → IsDeveloping (GSR n) p' →
        ∃! g : GSR n, ∀ y, p' y = g • p y := by
  obtain ⟨hcov, hsc, -, hG, hdiv⟩ := revetement_universel_divisible_proj (n := n) v₀
  haveI := hsc
  obtain ⟨h1, h2, -, h4, h5⟩ := resultB_revetement_proj hcov hG
  exact ⟨h1, h2, hdiv, h4, h5, (prop2_developpement_proj (n := n)).2.2.1⟩

/-- **Result B, sentence 1, projective half, for the universal cover** (l.87–89). -/
theorem resultB_premiere_proj {P : Set (UniversalCover V v₀)}
    {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    {φ : OpenPartialHomeomorph (UniversalCover V v₀) (S n)} {z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ}
    (hP : IsPocheProj P l φ z) :
    ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n), IsCompatibleChart (GSR n) φ' ∧
      φ'.source = univ ∧ EqOn φ' φ P ∧
      (IsCoqueProj P l φ z →
        Sphere.IsConvexPart φ'.target ∧ Sphere.IsStrictConvexPart φ'.target) := by
  obtain ⟨hcov, hsc, -, hG, -⟩ := revetement_universel_divisible_proj (n := n) v₀
  haveI := hsc
  exact resultB_poche_proj hcov hG hP

/-- **Result B, sentence 2, for the universal cover** (l.91–94): a strict shell of `W`, or a
projection of `W` whose closure lies in an open hemisphere, identifies `W` with the interior of a
convex body of `S(n)`. -/
theorem resultB_deuxieme :
    (∀ (P : Set (UniversalCover V v₀)) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph (UniversalCover V v₀) (S n))
      (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ), IsCoqueStricteProj P l φ z →
      ∃ K : Set (S n), IsCorpsConvexeS n K ∧
        ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n), IsCompatibleChart (GSR n) φ' ∧
          φ'.source = univ ∧ φ'.target = interior K ∧ EqOn φ' φ P) ∧
    (∀ p : UniversalCover V v₀ → S n, IsDeveloping (GSR n) p → ∀ H : Set (S n),
      Sphere.IsOpenHemisphere H → closure (range p) ⊆ H →
      ∃ K : Set (S n), IsCorpsConvexeS n K ∧
        ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n), IsCompatibleChart (GSR n) φ' ∧
          φ'.source = univ ∧ φ'.target = interior K ∧ ⇑φ' = p) := by
  obtain ⟨hcov, hsc, -, hG, -⟩ := revetement_universel_divisible_proj (n := n) v₀
  haveI := hsc
  exact ⟨fun P l _ φ z hC => resultB_coque_stricte hcov hG hC,
    fun p hp H hH hcl => resultB_hemisphere hcov hG hp hH hcl⟩

end UniversalCoverProj

section UniversalCoverAff

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  [HasGroupoid V (affGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V)

/-- **l.81–84, affine case, for the universal cover**: `W = UniversalCover V v₀` of a compact
Hausdorff locally affine `V` is path connected, Hausdorff, divisible, sweepable and an ouvert étalé
over `ℝⁿ` (a developing map, a local homeomorphism, unique up to `GA(n, ℝ)`). -/
theorem resultB_revetementUniversel_aff :
    PathConnectedSpace (UniversalCover V v₀) ∧ T2Space (UniversalCover V v₀) ∧
      IsDivisible (GAR n) (Fin n → ℝ) (UniversalCover V v₀) ∧
      IsBalayable (GAR n) (Fin n → ℝ) (UniversalCover V v₀) ∧
      (∃ p : UniversalCover V v₀ → (Fin n → ℝ), IsDeveloping (GAR n) p ∧ IsLocalHomeomorph p) ∧
      ∀ p p' : UniversalCover V v₀ → (Fin n → ℝ), IsDeveloping (GAR n) p →
        IsDeveloping (GAR n) p' → ∃! g : GAR n, ∀ y, p' y = g • p y := by
  obtain ⟨hcov, hsc, -, hG, hdiv⟩ := revetement_universel_divisible_aff (n := n) v₀
  haveI := hsc
  obtain ⟨h1, h2, -, h4, h5⟩ := resultB_revetement_aff hcov hG
  exact ⟨h1, h2, hdiv, h4, h5, (prop2_developpement_aff (n := n)).2.2.1⟩

/-- **Result B, sentence 3, for the universal cover** (l.96–98), `n ≥ 1`: `W`, considered as an
ouvert étalé over `ℝⁿ`, has an unbounded projection — every one of its projections is unbounded. -/
theorem resultB_troisieme [NeZero n] :
    (∃ p : UniversalCover V v₀ → (Fin n → ℝ), IsDeveloping (GAR n) p) ∧
      ∀ p : UniversalCover V v₀ → (Fin n → ℝ), IsDeveloping (GAR n) p →
        ¬ Bornology.IsBounded (range p) := by
  obtain ⟨hcov, hsc, -, hG, -⟩ := revetement_universel_divisible_aff (n := n) v₀
  haveI := hsc
  exact resultB_projection_non_bornee hcov hG

end UniversalCoverAff

/-! ### The printed statements, over the paper's manifolds -/

/-- **Result B, sentence 1 (projective half) and sentence 2, as printed**, over the paper's
manifolds (Hausdorff, connected, second countable, compact; `V : Type`), for the universal cover
`W = UniversalCover V v₀`. -/
def ResultBProjPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V] [CompactSpace V] (v₀ : V),
    (∀ (P : Set (UniversalCover V v₀)) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph (UniversalCover V v₀) (S n))
      (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ), IsPocheProj P l φ z →
      ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ (IsCoqueProj P l φ z → Sphere.IsConvexPart φ'.target)) ∧
    (∀ (P : Set (UniversalCover V v₀)) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph (UniversalCover V v₀) (S n))
      (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ), IsCoqueStricteProj P l φ z →
      ∃ K : Set (S n), IsCorpsConvexeS n K ∧
        ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n), IsCompatibleChart (GSR n) φ' ∧
          φ'.source = univ ∧ φ'.target = interior K) ∧
    (∀ p : UniversalCover V v₀ → S n, IsDeveloping (GSR n) p → ∀ H : Set (S n),
      Sphere.IsOpenHemisphere H → closure (range p) ⊆ H →
      ∃ K : Set (S n), IsCorpsConvexeS n K ∧
        ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n), IsCompatibleChart (GSR n) φ' ∧
          φ'.source = univ ∧ φ'.target = interior K)

/-- **Sentences 1 (projective half) and 2 hold as printed in every dimension**, `n = 0`
included. -/
theorem resultBProjPrinted (n : ℕ) : ResultBProjPrinted n := by
  intro V _ _ _ _ _ _ _ v₀
  refine ⟨fun P l _ φ z hP => ?_, fun P l _ φ z hC => ?_, fun p hp H hH hcl => ?_⟩
  · obtain ⟨φ', h1, h2, -, h3⟩ := resultB_premiere_proj v₀ hP
    exact ⟨φ', h1, h2, fun hC => (h3 hC).1⟩
  · obtain ⟨K, hK, φ', h1, h2, h3, -⟩ := (resultB_deuxieme v₀).1 P l φ z hC
    exact ⟨K, hK, φ', h1, h2, h3⟩
  · obtain ⟨K, hK, φ', h1, h2, h3, -⟩ := (resultB_deuxieme v₀).2 p hp H hH hcl
    exact ⟨K, hK, φ', h1, h2, h3⟩

/-- **Result B, sentence 3, as printed**, over the paper's manifolds (Hausdorff, connected, second
countable, compact; `V : Type`): every projection of the universal cover is unbounded. -/
def ResultBTroisiemePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V] [CompactSpace V] (v₀ : V),
    (∃ p : UniversalCover V v₀ → (Fin n → ℝ), IsDeveloping (GAR n) p) ∧
      ∀ p : UniversalCover V v₀ → (Fin n → ℝ), IsDeveloping (GAR n) p →
        ¬ Bornology.IsBounded (range p)

/-- **Sentence 3 holds as printed exactly in dimension `n ≥ 1`**: in dimension `0`, `V = ℝ⁰` (a
point, compact) satisfies every hypothesis and the projection of its universal cover is bounded. -/
theorem resultBTroisiemePrinted_iff (n : ℕ) : ResultBTroisiemePrinted n ↔ 0 < n := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      obtain ⟨⟨p, hp⟩, hunb⟩ := h (Fin 0 → ℝ) 0
      exact hunb p hp (resultB_isBounded_dim_zero p)
    · exact hn
  · intro hn V _ _ _ _ _ _ _ v₀
    haveI : NeZero n := ⟨hn.ne'⟩
    exact resultB_troisieme v₀


/-! ### Non-vacuity -/

section NonVacuity

/-- **The compact manifolds of the statement exist in every dimension**: `S(n)`, charted on
itself, is a compact Hausdorff locally projective manifold, and the conclusions of l.81–84 hold for
its universal cover. For `n = 0`, `S(0)` is two points, so not connected: outside the paper's
« variété », a degenerate case. -/
theorem resultB_revetementUniversel_sphere (n : ℕ) (x : S n) :
    PathConnectedSpace (UniversalCover (S n) x) ∧ T2Space (UniversalCover (S n) x) ∧
      IsBalayable (GSR n) (S n) (UniversalCover (S n) x) ∧
      ∃ p : UniversalCover (S n) x → S n, IsDeveloping (GSR n) p ∧ IsLocalHomeomorph p := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := resultB_revetementUniversel_proj (n := n) (V := S n) x
  exact ⟨h1, h2, h4, h5⟩

/-- **Sentence 3 on a compact locally affine manifold of every dimension `m + 1 ≥ 1`**: the Hopf
manifold `S(m) × S¹` of Theorem A (`theoremA_affine`, Ch. 1 § 3 Prop. 1's corollary, applied to
`S(m)`) is a compact Hausdorff locally affine manifold, and every projection of its universal cover
(one exists) is unbounded. -/
theorem resultB_troisieme_hopf (m : ℕ) :
    ∃ cs : ChartedSpace (Fin (m + 1) → ℝ) (S m × Circle),
      ∃ _ : @HasGroupoid _ _ _ _ cs (affGroupoid (m + 1)), ∀ v₀ : S m × Circle,
        (∃ p : UniversalCover (S m × Circle) v₀ → (Fin (m + 1) → ℝ), IsDeveloping (GAR (m + 1)) p) ∧
        ∀ p : UniversalCover (S m × Circle) v₀ → (Fin (m + 1) → ℝ), IsDeveloping (GAR (m + 1)) p →
          ¬ Bornology.IsBounded (range p) := by
  obtain ⟨cs, hcs⟩ := theoremA_affine (S m) ⟨chartedSpaceSelf (S m), inferInstance⟩
  exact ⟨cs, hcs, fun v₀ => resultB_troisieme v₀⟩

/-- **In dimension `0` every connected manifold with a developing map has a strict shell**, with
`P` the whole manifold and the cote `0`, and the closure of its projection lies in an open
hemisphere. -/
theorem resultB_exists_coqueStricte_dim_zero {W : Type*} [TopologicalSpace W]
    [ChartedSpace (S 0) W] [HasGroupoid W (projGroupoid 0)] [ConnectedSpace W] {p : W → S 0}
    (hp : IsDeveloping (GSR 0) p) :
    ∃ (l : Module.Dual ℝ (Fin (0 + 1) → ℝ)) (_ : Fact (l ≠ 0))
      (φ : OpenPartialHomeomorph W (S 0)) (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsCoqueStricteProj (univ : Set W) l φ z ∧ closure (range p) ⊆ Sphere.openHemisphere l := by
  haveI := subsingleton_dim_zero (V := W)
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  obtain ⟨l, hl, hmem⟩ := exists_mem_openHemisphere (p w₀)
  haveI : Fact (l ≠ 0) := ⟨hl⟩
  obtain ⟨φ, hφ, hs, -, he⟩ := exists_chart_of_injective hp (fun x y _ => Subsingleton.elim x y)
  have hrange : range p = {p w₀} := by
    ext y
    constructor
    · rintro ⟨M, rfl⟩
      rw [Subsingleton.elim M w₀]
      exact mem_singleton _
    · intro hy
      rw [mem_singleton_iff.1 hy]
      exact mem_range_self w₀
  have himg : φ '' univ = {p w₀} := by rw [image_univ, he, hrange]
  set z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ := AffineMap.const ℝ _ (0 : ℝ) with hz
  have hP : IsPocheProj (univ : Set W) l φ z := by
    refine ⟨isOpen_univ, isConnected_univ, hs, hφ, ?_, ?_, fun _ _ => zero_le_one, ?_⟩
    · rw [himg]
      exact singleton_subset_iff.2 hmem
    · have hS : z '' ((↑) ⁻¹' (φ '' univ)) = {0} := by
        ext t
        constructor
        · rintro ⟨y, -, rfl⟩
          rfl
        · rintro rfl
          exact ⟨⟨p w₀, hmem⟩, by rw [himg]; rfl, rfl⟩
      rw [hS]
      exact isGLB_singleton
    · intro Sg M N _ _ ψ _ _ hgerm
      refine ⟨?_, fun _ _ => mem_univ N⟩
      rintro _ ⟨y, -, rfl⟩
      rw [Subsingleton.elim y M, hgerm.eq_of_nhds, he, Subsingleton.elim M w₀]
      exact hmem
  have hC : IsCoqueProj (univ : Set W) l φ z := ⟨hP, by
    rw [himg]
    exact (isCorpsConvexeS_singleton_S0 (p w₀)).1.1⟩
  refine ⟨l, inferInstance, φ, z, ⟨hC, ?_⟩, ?_⟩
  · rintro ⟨A, ⟨q, w, hw, rfl⟩, hA⟩
    have h0 := hA ⟨0, rfl⟩
    have h1 := hA ⟨1, rfl⟩
    have hsub : (φ '' univ).Subsingleton := by rw [himg]; exact subsingleton_singleton
    have h01 : (0 : ℝ) • w +ᵥ q = (1 : ℝ) • w +ᵥ q := Subtype.ext (hsub h0 h1)
    rw [zero_smul, one_smul] at h01
    exact hw (vadd_right_cancel q h01).symm
  · rw [hrange, closure_singleton]
    exact singleton_subset_iff.2 hmem

/-- **The hypotheses of sentences 1 and 2 are jointly satisfiable** (`n = 0`, `V = S(0)`, compact
and Hausdorff, but two points, so not connected: outside the paper's « variété », a degenerate
witness; the connected one is `resultB_nonVacuite_hopf`, `n = 1`, through the general-covering form): the universal cover `W` of `S(0)` at `x` has a strict shell, and a projection with
closure in an open hemisphere; so `W` is identified with the interior of a convex body of `S(0)`. -/
theorem resultB_nonVacuite_dim_zero (x : S 0) :
    ∃ (l : Module.Dual ℝ (Fin (0 + 1) → ℝ)) (_ : Fact (l ≠ 0))
      (φ : OpenPartialHomeomorph (UniversalCover (S 0) x) (S 0))
      (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ),
      IsCoqueStricteProj (univ : Set (UniversalCover (S 0) x)) l φ z ∧
      (∃ p : UniversalCover (S 0) x → S 0, IsDeveloping (GSR 0) p ∧
        closure (range p) ⊆ Sphere.openHemisphere l) ∧
      ∃ K : Set (S 0), IsCorpsConvexeS 0 K ∧
        ∃ φ' : OpenPartialHomeomorph (UniversalCover (S 0) x) (S 0), IsCompatibleChart (GSR 0) φ' ∧
          φ'.source = univ ∧ φ'.target = interior K := by
  obtain ⟨hcov, hsc, -, hG, -⟩ := revetement_universel_divisible_proj (n := 0) x
  haveI := hsc
  obtain ⟨p, hp⟩ := (prop2_developpement_proj (n := 0) (V := UniversalCover (S 0) x)).1
  obtain ⟨l, hl, φ, z, hC, hcl⟩ := resultB_exists_coqueStricte_dim_zero hp
  obtain ⟨K, hK, φ', h1, h2, h3, -⟩ := resultB_coque_stricte hcov hG hC
  exact ⟨l, hl, φ, z, hC, ⟨p, hp, hcl⟩, K, hK, φ', h1, h2, h3⟩

end NonVacuity

/-! ### A non-degenerate witness: the Hopf circle `]0, ∞[ / 2^ℤ` -/

section Hopf

attribute [local instance] projOfAff hasGroupoid_projOfAff

/-- The homothety of ratio `2` of the half-line `]0, ∞[`, a projective automorphism for its
canonical projective structure (`homothetieDemiDroite`, Ch. 2 § 3). -/
def resultBHopfGen : GXAut (GSR 1) (S 1) demiDroiteOuverte :=
  GXAut.ofBijective (isGXMorphism_homothetieDemiDroite 2 two_pos)
    (bijective_homothetieDemiDroite 2 two_pos)

/-- **The group `2^ℤ`** of homotheties of `]0, ∞[`, the deck group of the Hopf circle
`]0, ∞[ / 2^ℤ` (a compact locally projective manifold whose universal cover is `]0, ∞[`). -/
def resultBHopfGroup : Subgroup (GXAut (GSR 1) (S 1) demiDroiteOuverte) :=
  Subgroup.zpowers resultBHopfGen

theorem resultBHopfGen_smul (x : demiDroiteOuverte) :
    ((resultBHopfGen • x : demiDroiteOuverte) : Fin 1 → ℝ) = (2 : ℝ) • (x : Fin 1 → ℝ) := rfl

/-- `2^k` acts as the homothety of ratio `2^k`. -/
theorem resultBHopfGen_zpow_smul (k : ℤ) (x : demiDroiteOuverte) :
    ((resultBHopfGen ^ k • x : demiDroiteOuverte) : Fin 1 → ℝ) =
      (2 : ℝ) ^ k • (x : Fin 1 → ℝ) := by
  induction k using Int.induction_on generalizing x with
  | zero => rw [zpow_zero, one_smul, zpow_zero, one_smul]
  | succ i ih =>
    rw [zpow_add_one, mul_smul, ih, resultBHopfGen_smul, smul_smul, ← zpow_add_one₀ two_ne_zero]
  | pred i ih =>
    have hinv : ((resultBHopfGen⁻¹ • x : demiDroiteOuverte) : Fin 1 → ℝ) =
        (2 : ℝ)⁻¹ • (x : Fin 1 → ℝ) := by
      have h := resultBHopfGen_smul (resultBHopfGen⁻¹ • x)
      rw [smul_inv_smul] at h
      rw [h, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    rw [zpow_sub_one, mul_smul, ih, hinv, smul_smul, ← zpow_sub_one₀ two_ne_zero]

/-- An integer `k` with `2^k ≤ C` is at most `⌈C⌉₊`. -/
theorem resultB_le_natCeil_of_two_zpow_le {C : ℝ} {k : ℤ} (h : (2 : ℝ) ^ k ≤ C) :
    k ≤ (⌈C⌉₊ : ℤ) := by
  rcases le_or_gt k 0 with hk | hk
  · exact hk.trans (Nat.cast_nonneg _)
  · lift k to ℕ using hk.le
    rw [zpow_natCast] at h
    have h1 : (k : ℝ) < 2 ^ k := by exact_mod_cast k.lt_two_pow_self
    exact_mod_cast (h1.le.trans h).trans (Nat.le_ceil C)

/-- `2^ℤ` acts properly discontinuously on `]0, ∞[`. -/
theorem resultB_hopf_properlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul resultBHopfGroup demiDroiteOuverte := by
  refine ⟨fun {K L} hK hL => ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  rcases L.eq_empty_or_nonempty with rfl | hLne
  · simp
  set f : demiDroiteOuverte → ℝ := fun x => (x : Fin 1 → ℝ) 0 with hf_def
  have hf : Continuous f := (continuous_apply 0).comp continuous_subtype_val
  have hpos : ∀ x, 0 < f x := fun x => x.2
  obtain ⟨a, -, ha⟩ := hK.exists_isMinOn hKne hf.continuousOn
  obtain ⟨b, -, hb⟩ := hK.exists_isMaxOn hKne hf.continuousOn
  obtain ⟨c, -, hc⟩ := hL.exists_isMinOn hLne hf.continuousOn
  obtain ⟨d, -, hd⟩ := hL.exists_isMaxOn hLne hf.continuousOn
  set C := max (f d / f a) (f b / f c) with hC
  refine ((Set.finite_Icc (-(⌈C⌉₊ : ℤ)) ⌈C⌉₊).image
    (fun k : ℤ => (⟨resultBHopfGen ^ k, Subgroup.zpow_mem_zpowers _ k⟩ :
      resultBHopfGroup))).subset ?_
  rintro ⟨γ, hγ⟩ hne
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hγ
  obtain ⟨_, ⟨x, hxK, rfl⟩, hxL⟩ := hne
  have hfy : f ((⟨resultBHopfGen ^ k, hγ⟩ : resultBHopfGroup) • x) = 2 ^ k * f x := by
    show ((resultBHopfGen ^ k • x : demiDroiteOuverte) : Fin 1 → ℝ) 0 = _
    rw [resultBHopfGen_zpow_smul]
    rfl
  have h2k : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  have hax := isMinOn_iff.1 ha x hxK
  have hxb := isMaxOn_iff.1 hb x hxK
  have hcy := isMinOn_iff.1 hc _ hxL
  have hyd := isMaxOn_iff.1 hd _ hxL
  rw [hfy] at hcy hyd
  have hup : (2 : ℝ) ^ k ≤ C := by
    refine le_trans ?_ (le_max_left _ _)
    rw [le_div_iff₀ (hpos a)]
    exact (mul_le_mul_of_nonneg_left hax h2k.le).trans hyd
  have hdown : (2 : ℝ) ^ (-k) ≤ C := by
    refine le_trans ?_ (le_max_right _ _)
    rw [le_div_iff₀ (hpos c), zpow_neg]
    calc (2 ^ k)⁻¹ * f c ≤ (2 ^ k)⁻¹ * (2 ^ k * f x) :=
          mul_le_mul_of_nonneg_left hcy (inv_nonneg.2 h2k.le)
      _ = f x := by rw [← mul_assoc, inv_mul_cancel₀ h2k.ne', one_mul]
      _ ≤ f b := hxb
  have h1 := resultB_le_natCeil_of_two_zpow_le hup
  have h2 := resultB_le_natCeil_of_two_zpow_le hdown
  exact ⟨k, ⟨by omega, h1⟩, rfl⟩

/-- `2^ℤ` acts freely on `]0, ∞[` (« sans point fixe »). -/
theorem resultB_hopf_isCancelSMul : IsCancelSMul resultBHopfGroup demiDroiteOuverte := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨γ, hγ⟩ x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hγ
  have h1 : (2 : ℝ) ^ k • (x : Fin 1 → ℝ) = x := by
    rw [← resultBHopfGen_zpow_smul]
    exact congrArg Subtype.val hx
  have h2 : (2 : ℝ) ^ k * (x : Fin 1 → ℝ) 0 = 1 * (x : Fin 1 → ℝ) 0 := by
    rw [one_mul]
    exact congrFun h1 0
  have h3 : (2 : ℝ) ^ k = 2 ^ (0 : ℤ) := by
    rw [zpow_zero]
    exact mul_right_cancel₀ (ne_of_gt x.2) h2
  have hk : k = 0 := zpow_right_injective₀ two_pos (by norm_num) h3
  subst hk
  exact Subtype.ext (zpow_zero _)

/-- A compact fundamental domain: every orbit of `2^ℤ` meets `[1, 2]`. -/
theorem resultB_hopf_exists_isCompact : ∃ K₀ : Set demiDroiteOuverte, IsCompact K₀ ∧
    ∀ x : demiDroiteOuverte, ∃ γ : resultBHopfGroup, γ • x ∈ K₀ := by
  set K₀ : Set demiDroiteOuverte :=
    {x | 1 ≤ (x : Fin 1 → ℝ) 0 ∧ (x : Fin 1 → ℝ) 0 ≤ 2} with hK₀
  refine ⟨K₀, ?_, fun x => ?_⟩
  · rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    convert isCompact_univ_pi (fun _ : Fin 1 => (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)))
      using 1
    ext v
    simp only [hK₀, mem_image, mem_univ_pi, mem_Icc, Fin.forall_fin_one]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hv
      exact ⟨⟨v, show (0 : ℝ) < v 0 by linarith [hv.1]⟩, hv, rfl⟩
  · have ht : (0 : ℝ) < (x : Fin 1 → ℝ) 0 := x.2
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow ht one_lt_two
    have h2m : (0 : ℝ) < 2 ^ m := zpow_pos two_pos m
    refine ⟨⟨resultBHopfGen ^ (-m), Subgroup.zpow_mem_zpowers _ _⟩, ?_⟩
    show 1 ≤ ((resultBHopfGen ^ (-m) • x : demiDroiteOuverte) : Fin 1 → ℝ) 0 ∧
      ((resultBHopfGen ^ (-m) • x : demiDroiteOuverte) : Fin 1 → ℝ) 0 ≤ 2
    rw [resultBHopfGen_zpow_smul, Pi.smul_apply, smul_eq_mul, zpow_neg]
    constructor
    · rw [le_inv_mul_iff₀ h2m, mul_one]
      exact hm1
    · rw [inv_mul_le_iff₀ h2m]
      rw [zpow_add_one₀ two_ne_zero] at hm2
      linarith

/-- **The hypotheses of sentences 1 and 2 are satisfiable in dimension `1`, non-degenerately**:
the Hopf circle `V = ]0, ∞[ / 2^ℤ` is a compact Hausdorff locally projective manifold, and
`π : ]0, ∞[ → V` is a simply connected covering and a projective morphism. Its universal cover
`]0, ∞[` has the strict shell `P = ]0, 1[ ≠ ]0, ∞[` with the non-constant cote `x₀`
(`exists_isCoqueStricteAff_demiDroite_ne_univ`, read projectively); so (`resultB_coque_stricte`) `]0, ∞[` is identified with
the interior of a convex body `K` of `S(1)`, by a chart `φ̃` inducing `φ` on `P`, and the closure
of the projection `φ̃` lies in an open hemisphere (the hypothesis of the hemisphere case holds
too). -/
theorem resultB_nonVacuite_hopf :
    ∃ (V : Type) (_ : TopologicalSpace V) (_ : ChartedSpace (S 1) V)
      (_ : HasGroupoid V (projGroupoid 1)), CompactSpace V ∧ T2Space V ∧
      ∃ π : demiDroiteOuverte → V, IsCoveringMap π ∧ IsGXMorphism (GSR 1) (S 1) π ∧
        SimplyConnectedSpace demiDroiteOuverte ∧
        ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (S 1))
          (z : Sphere.openHemisphere (Sphere.lastForm 1) →ᵃ[ℝ] ℝ),
          IsCoqueStricteProj P (Sphere.lastForm 1) φ z ∧ P ≠ univ ∧
          ∃ K : Set (S 1), IsCorpsConvexeS 1 K ∧
            ∃ φ' : OpenPartialHomeomorph demiDroiteOuverte (S 1), IsCompatibleChart (GSR 1) φ' ∧
              φ'.source = univ ∧ φ'.target = interior K ∧ EqOn φ' φ P ∧
              ∃ H : Set (S 1), Sphere.IsOpenHemisphere H ∧ closure (range φ') ⊆ H := by
  haveI := resultB_hopf_properlyDiscontinuousSMul
  haveI := resultB_hopf_isCancelSMul
  have hΓ : ∀ γ : resultBHopfGroup,
      IsGXMorphism (GSR 1) (S 1) fun v : demiDroiteOuverte => γ • v :=
    fun γ => (γ : GXAut (GSR 1) (S 1) demiDroiteOuverte).isGXMorphism
  haveI := continuousConstSMul_of_isGXMorphism hΓ
  haveI : LocallyCompactSpace demiDroiteOuverte :=
    ChartedSpace.locallyCompactSpace (S 1) demiDroiteOuverte
  -- the projective charts of the quotient (`projOfAff` would also apply to its affine charts)
  letI : ChartedSpace (S 1) (MulAction.orbitRel.Quotient resultBHopfGroup demiDroiteOuverte) :=
    MulAction.instChartedSpaceQuotient
  have hcov : IsCoveringMap (Quotient.mk (MulAction.orbitRel resultBHopfGroup demiDroiteOuverte)) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
  have hG := isGXMorphism_quotientMk hΓ
  have hgr := hasGroupoid_quotient hΓ
  obtain ⟨K₀, hK₀, hK₀x⟩ := resultB_hopf_exists_isCompact
  have hcpt : CompactSpace (MulAction.orbitRel.Quotient resultBHopfGroup demiDroiteOuverte) := by
    refine ⟨?_⟩
    have huniv : Quotient.mk (MulAction.orbitRel resultBHopfGroup demiDroiteOuverte) '' K₀ =
        univ := by
      refine eq_univ_of_forall fun q => ?_
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
      obtain ⟨γ, hγ⟩ := hK₀x x
      exact ⟨γ • x, hγ, Quotient.sound (MulAction.orbitRel_apply.2 ⟨γ, rfl⟩)⟩
    rw [← huniv]
    exact hK₀.image continuous_quotient_mk'
  -- the strict shell `]0, 1[` of `]0, ∞[` (Ch. 2 § 1), read projectively by the Remarque
  obtain ⟨P, φa, hCa, hne⟩ := exists_isCoqueStricteAff_demiDroite_ne_univ
  obtain ⟨e⟩ := Sphere.nonempty_hemi_affineEquiv (l := Sphere.lastForm 1) (Module.finrank_fin_fun ℝ)
  have hC := hCa.toCoqueStricteProj e.symm
  -- `]0, ∞[` is convex, hence simply connected
  have hsc : SimplyConnectedSpace demiDroiteOuverte := by
    have hconv : Convex ℝ (demiDroiteOuverte : Set (Fin 1 → ℝ)) :=
      (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
    haveI := hconv.contractibleSpace ⟨fun _ => 1, show (0 : ℝ) < 1 from one_pos⟩
    infer_instance
  haveI := hsc
  obtain ⟨K, hK, φ', h1, h2, h3, h4⟩ := resultB_coque_stricte hcov hG hC
  exact ⟨_, inferInstance, inferInstance, hgr, hcpt, inferInstance, _, hcov, hG, hsc, P, _, _, hC,
    hne, K, hK, φ', h1, h2, h3, h4, resultB_exists_hemisphere_of_target hK h2 h3⟩

end Hopf

end Benzecri
