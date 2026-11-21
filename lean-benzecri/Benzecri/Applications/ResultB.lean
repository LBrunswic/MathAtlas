import Benzecri.Applications.TheoremB
import Benzecri.Chapter2.TheoremeAffine

/-!
# `Benzecri.Applications.ResultB` — the introduction's result B, assembled: the affine half of its first sentence, and one theorem for its three sentences

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Introduction, § 1 « Les résultats », journal pp. 230–231; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Roadmap target `T-bz-result-b`.

* `bzthm:intro_B` — `benzecri1960_ch1.tex:86` (l.86–105, résumé B; its three sentences l.87–99,
  introduced by l.80–84). **Not marked** (SCOPE): sentence 3 holds for `n ≥ 1` only, and the mark
  waits on OQ-45 (a). Everything else is proved, sorry-free:
  - sentence 1, affine half, for every simply connected covering `π : N → V` of a compact
    Hausdorff locally affine `V` (`resultB_poche_aff`), then for the universal cover
    `W = UniversalCover V v₀` (`resultB_premiere_aff`);
  - **the assembly**: `theoremB`, one theorem for the three sentences (sentences 1–2 in every
    dimension, sentence 3 under `0 < n`), next to `Benzecri.theoremA`;
  - over the paper's manifolds: `ResultBAffPrinted`, `resultBAffPrinted` (every `n`), and
    `ResultBPrinted n` (the three sentences as printed), `resultBPrinted` (`0 < n`),
    `resultBPrinted_iff` (`↔ 0 < n`);
  - non-vacuity of the affine half: `resultB_nonVacuite_hopf_aff` (the Hopf circle `]0, ∞[ / 2^ℤ`
    as a compact locally affine manifold, `n = 1`, the strict shell `]0, 1[ ≠ ]0, ∞[`, through the
    general-covering form), and `resultB_nonVacuite_aff_dim_zero` (`V = ℝ⁰`, on
    `UniversalCover V v₀` itself, degenerate: `P = W`, cote `0`).

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
| `V` « une variété localement affine (resp. projective) » | ✓ carried: `[ChartedSpace (Fin n → ℝ) V]` (resp. `S n`), `[HasGroupoid V _]`; « variété »: Hausdorff ✓ carried (`[T2Space V]`); connected, second countable ⚠ weakened (unused; the printed forms carry them) |
| `V` « compacte » | ✓ carried: `[CompactSpace V]` |
| « le revêtement universel » `W` | ✓ carried: `UniversalCover V v₀` with the pulled-back structure; in `resultB_poche_aff`, more (Lean ≥ paper): every simply connected covering `π : N → V`, `π` a morphism |
| `W` « possède une poche (resp. coque) », affine | ✓ carried: `IsPocheAff P φ z` (resp. `IsCoqueAff`) on `W` (Ch. 2 Déf. 1, 2) |
| « s'identifie à un ouvert (resp. à un convexe) de l'espace affin » | ✓ carried: a compatible chart `φ̃`, `φ̃.source = univ` (open target), and more, `φ̃ = φ` on `P`; for a shell `Convex ℝ φ̃.target` (the convexity of `ℝⁿ` of Ch. 2 Déf. 2–3, `isAffConvex_iff_convex`), and more: no line for a strict shell (Ch. 2 § 3, 4°) |
| sentences 1 (projective half), 2, 3 | as in `Benzecri.Applications.TheoremB` (its checklist) |
| the dimension | sentences 1–2: every `n`, `n = 0` included; ⚠ strengthened: sentence 3 under `0 < n` (finding: false for `n = 0`) |

## SCOPE (disclosed)

* **Sentence 3 is false for `n = 0`** (the finding of `Benzecri.Applications.TheoremB`): a
  compact locally affine `0`-manifold is finite, its universal cover a point, and every subset of
  `ℝ⁰` is bounded (`resultBTroisiemePrinted_iff`, witness `V = ℝ⁰`). So `ResultBPrinted n ↔ 0 < n`
  (`resultBPrinted_iff`). OQ-45 (a)'s question (is `n ≥ 1` implied throughout?), not ruled. Under
  (a), `theoremB` and `resultBPrinted` are the statement of record with no Lean change.
* **What the affine half uses of Ch. 2 § 3's affine Theorem**: 1°'s first sentence
  (`exists_chart_poche_affine`: 1°a, 1°b), 3° (`theoreme_troisieme_affine`) and 4°
  (`theoreme_quatrieme_affine`); never 1°'s second sentence (OQ-75, OQ-79), checked on the proof
  terms (REPORT, notes).
* « s'identifie à un ouvert (resp. à un convexe) » is read « is mapped onto an open (resp. convex)
  set by a compatible chart with source `W` », as in Ch. 2 § 3, 1° (`exists_chart_poche_affine`);
  « un convexe » of the affine space is the usual convexity of `ℝⁿ` (Ch. 1 Déf. 8 is that of
  `S(E)`; Ch. 2 Déf. 3 names the affine one, « le convexe $\varphi(P)$ de $\R^n$ », l.195–196 of
  `benzecri1960_ch2.tex`), Mathlib's `Convex ℝ`, equal to the segment form `IsAffConvex`
  (`isAffConvex_iff_convex`), as in `Benzecri.Chapter2.TheoremeAffine`.
* « le revêtement universel » of a `V` that is not connected is that of the component of `v₀` (as
  in `Benzecri.UniversalCoverRow`).
* The Hopf circle is built here (`resultBHopfAffGroup`, the quotient `V/Γ` of
  `Structure/Quotient.lean`) only as a witness, in the general-covering form (`kb/0043`): its
  universal cover is not computed inside `UniversalCover`. The witness on `UniversalCover` itself
  is `V = ℝ⁰` (`resultB_nonVacuite_aff_dim_zero`), where a connected manifold is a point
  (`resultB_subsingleton_aff_dim_zero`).
* The résumé's closing gloss (l.100–104) is explanatory and not formalized, as in
  `Benzecri.Applications.TheoremB`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

namespace Benzecri

universe u v

/-! ### Sentence 1, affine half, for a simply connected covering (l.87–89) -/

section Covering

variable {n : ℕ} {V : Type u} [TopologicalSpace V] {N : Type v} [TopologicalSpace N]
  {π : N → V} [ChartedSpace (Fin n → ℝ) V] [CompactSpace V] [T2Space V]
  [ChartedSpace (Fin n → ℝ) N] [HasGroupoid N (affGroupoid n)] [SimplyConnectedSpace N]

/-- **Sentence 1, affine half** (l.87–89): if a simply connected covering `N` of a compact
Hausdorff locally affine `V` (`π` a morphism) has a pocket `(P, φ, z)`, it is identified with an
open set of `ℝⁿ` by a compatible chart `φ̃` with source `N`, inducing `φ` on `P` (Ch. 2 § 3, the
affine 1°, first sentence); if the pocket is a shell, `φ̃(N)` is convex (the affine 3°); and, beyond
the sentence, if it is a strict shell, `φ̃(N)` contains no line (the affine 4°). -/
theorem resultB_poche_aff (hπ : IsCoveringMap π) (hπG : IsGXMorphism (GAR n) (Fin n → ℝ) π)
    {P : Set N} {φ : OpenPartialHomeomorph N (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}
    (hP : IsPocheAff P φ z) :
    ∃ φ' : OpenPartialHomeomorph N (Fin n → ℝ), IsCompatibleChart (GAR n) φ' ∧
      φ'.source = univ ∧ EqOn φ' φ P ∧
      (IsCoqueAff P φ z → Convex ℝ φ'.target) ∧
      (IsCoqueStricteAff P φ z → ¬ ContainsAffLine (Fin n → ℝ) φ'.target) := by
  obtain ⟨-, -, -, hbal, -⟩ := resultB_revetement_aff hπ hπG
  obtain ⟨φ', hφ', hs, hφ'φ⟩ := exists_chart_poche_affine hbal hP
  have hp : IsDeveloping (GAR n) φ' := fun x => hφ' x (hs.symm ▸ mem_univ x)
  have ht : φ'.target = range φ' := by rw [← φ'.image_source_eq_target, hs, image_univ]
  refine ⟨φ', hφ', hs, hφ'φ, fun hC => ?_, fun hC => ?_⟩
  · rw [ht]
    exact theoreme_troisieme_affine hbal hC hp hφ'φ
  · rw [ht]
    exact theoreme_quatrieme_affine hbal hC hp hφ'φ

end Covering

/-! ### The universal cover `W = UniversalCover V v₀` -/

section UniversalCoverAff

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
  [HasGroupoid V (affGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V)

/-- **Result B, sentence 1, affine half, for the universal cover** (l.87–89). -/
theorem resultB_premiere_aff {P : Set (UniversalCover V v₀)}
    {φ : OpenPartialHomeomorph (UniversalCover V v₀) (Fin n → ℝ)} {z : (Fin n → ℝ) →ᵃ[ℝ] ℝ}
    (hP : IsPocheAff P φ z) :
    ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (Fin n → ℝ), IsCompatibleChart (GAR n) φ' ∧
      φ'.source = univ ∧ EqOn φ' φ P ∧
      (IsCoqueAff P φ z → Convex ℝ φ'.target) ∧
      (IsCoqueStricteAff P φ z → ¬ ContainsAffLine (Fin n → ℝ) φ'.target) := by
  obtain ⟨hcov, hsc, -, hG, -⟩ := revetement_universel_divisible_aff (n := n) v₀
  haveI := hsc
  exact resultB_poche_aff hcov hG hP

end UniversalCoverAff

/-! ### Result B: one theorem for the three sentences -/

/-- **Result B** (`bzthm:intro_B`, l.87–99), its three sentences, for the universal cover
`W = UniversalCover V v₀` of a compact Hausdorff manifold `V`:
1. (l.87–89) a pocket (resp. shell) of `W` identifies `W` with an open (resp. convex) set of `ℝⁿ`,
   or of `S(n)`, by a compatible chart with source `W` inducing `φ` on `P` (every `n`);
2. (l.91–94) a strict shell of `W`, or a projection of `W` whose closure lies in an open
   hemisphere, identifies `W` with the interior of a convex body of `S(n)` (every `n`);
3. (l.96–98) for `0 < n`, `W` has a projection to `ℝⁿ`, and every one is unbounded (false for
   `n = 0`: `resultBTroisiemePrinted_iff`). -/
theorem theoremB :
    -- sentence 1, affine half
    (∀ (n : ℕ) (V : Type u) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
      [HasGroupoid V (affGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V)
      (P : Set (UniversalCover V v₀)) (φ : OpenPartialHomeomorph (UniversalCover V v₀) (Fin n → ℝ))
      (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ), IsPocheAff P φ z →
      ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (Fin n → ℝ),
        IsCompatibleChart (GAR n) φ' ∧ φ'.source = univ ∧ EqOn φ' φ P ∧
        (IsCoqueAff P φ z → Convex ℝ φ'.target) ∧
        (IsCoqueStricteAff P φ z → ¬ ContainsAffLine (Fin n → ℝ) φ'.target)) ∧
    -- sentence 1, projective half
    (∀ (n : ℕ) (V : Type u) [TopologicalSpace V] [ChartedSpace (S n) V]
      [HasGroupoid V (projGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V)
      (P : Set (UniversalCover V v₀)) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
      (φ : OpenPartialHomeomorph (UniversalCover V v₀) (S n))
      (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ), IsPocheProj P l φ z →
      ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n), IsCompatibleChart (GSR n) φ' ∧
        φ'.source = univ ∧ EqOn φ' φ P ∧
        (IsCoqueProj P l φ z →
          Sphere.IsConvexPart φ'.target ∧ Sphere.IsStrictConvexPart φ'.target)) ∧
    -- sentence 2
    (∀ (n : ℕ) (V : Type u) [TopologicalSpace V] [ChartedSpace (S n) V]
      [HasGroupoid V (projGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V),
      (∀ (P : Set (UniversalCover V v₀)) (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) [Fact (l ≠ 0)]
        (φ : OpenPartialHomeomorph (UniversalCover V v₀) (S n))
        (z : Sphere.openHemisphere l →ᵃ[ℝ] ℝ), IsCoqueStricteProj P l φ z →
        ∃ K : Set (S n), IsCorpsConvexeS n K ∧
          ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n),
            IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧ φ'.target = interior K ∧
            EqOn φ' φ P) ∧
      (∀ p : UniversalCover V v₀ → S n, IsDeveloping (GSR n) p → ∀ H : Set (S n),
        Sphere.IsOpenHemisphere H → closure (range p) ⊆ H →
        ∃ K : Set (S n), IsCorpsConvexeS n K ∧
          ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (S n),
            IsCompatibleChart (GSR n) φ' ∧ φ'.source = univ ∧ φ'.target = interior K ∧
            ⇑φ' = p)) ∧
    -- sentence 3, `0 < n`
    (∀ (n : ℕ), 0 < n → ∀ (V : Type u) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V]
      [HasGroupoid V (affGroupoid n)] [CompactSpace V] [T2Space V] (v₀ : V),
      (∃ p : UniversalCover V v₀ → (Fin n → ℝ), IsDeveloping (GAR n) p) ∧
      ∀ p : UniversalCover V v₀ → (Fin n → ℝ), IsDeveloping (GAR n) p →
        ¬ Bornology.IsBounded (range p)) := by
  refine ⟨fun n V _ _ _ _ _ v₀ P φ z hP => resultB_premiere_aff v₀ hP,
    fun n V _ _ _ _ _ v₀ P l _ φ z hP => resultB_premiere_proj v₀ hP,
    fun n V _ _ _ _ _ v₀ => resultB_deuxieme v₀, fun n hn V _ _ _ _ _ v₀ => ?_⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  exact resultB_troisieme v₀

/-! ### The printed statements, over the paper's manifolds -/

/-- **Result B, sentence 1, affine half, as printed**, over the paper's manifolds (Hausdorff,
connected, second countable, compact; `V : Type`), for the universal cover
`W = UniversalCover V v₀`. -/
def ResultBAffPrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (Fin n → ℝ) V] [HasGroupoid V (affGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V] [CompactSpace V] (v₀ : V)
    (P : Set (UniversalCover V v₀)) (φ : OpenPartialHomeomorph (UniversalCover V v₀) (Fin n → ℝ))
    (z : (Fin n → ℝ) →ᵃ[ℝ] ℝ), IsPocheAff P φ z →
    ∃ φ' : OpenPartialHomeomorph (UniversalCover V v₀) (Fin n → ℝ), IsCompatibleChart (GAR n) φ' ∧
      φ'.source = univ ∧ (IsCoqueAff P φ z → Convex ℝ φ'.target)

/-- **Sentence 1's affine half holds as printed in every dimension**, `n = 0` included. -/
theorem resultBAffPrinted (n : ℕ) : ResultBAffPrinted n := by
  intro V _ _ _ _ _ _ _ v₀ P φ z hP
  obtain ⟨φ', h1, h2, -, h3, -⟩ := resultB_premiere_aff v₀ hP
  exact ⟨φ', h1, h2, h3⟩

/-- **Result B as printed** (l.87–99), its three sentences over the paper's manifolds: sentence
1's affine half (`ResultBAffPrinted`), sentence 1's projective half and sentence 2
(`ResultBProjPrinted`), sentence 3 (`ResultBTroisiemePrinted`). -/
def ResultBPrinted (n : ℕ) : Prop :=
  ResultBAffPrinted n ∧ ResultBProjPrinted n ∧ ResultBTroisiemePrinted n

/-- **Result B holds as printed in every dimension `n ≥ 1`** (the statement of record under
OQ-45 (a)). -/
theorem resultBPrinted {n : ℕ} (hn : 0 < n) : ResultBPrinted n :=
  ⟨resultBAffPrinted n, resultBProjPrinted n, (resultBTroisiemePrinted_iff n).2 hn⟩

/-- **Result B holds as printed exactly in dimension `n ≥ 1`**: sentences 1–2 hold in every
dimension, sentence 3 fails at `n = 0` (`resultBTroisiemePrinted_iff`, witness `V = ℝ⁰`). -/
theorem resultBPrinted_iff (n : ℕ) : ResultBPrinted n ↔ 0 < n :=
  ⟨fun h => (resultBTroisiemePrinted_iff n).1 h.2.2, resultBPrinted⟩

/-! ### Non-vacuity of the affine half on the universal cover itself: dimension `0` -/

section DimZero

/-- **A connected manifold modelled on `ℝ⁰` is a point**: every chart source is a singleton
(`ℝ⁰` is a point and a chart is injective on its source), so the topology is discrete (the
affine twin of `subsingleton_dim_zero`). -/
theorem resultB_subsingleton_aff_dim_zero {W : Type*} [TopologicalSpace W]
    [ChartedSpace (Fin 0 → ℝ) W] [PreconnectedSpace W] : Subsingleton W := by
  haveI : DiscreteTopology W := by
    refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
    have h : (chartAt (Fin 0 → ℝ) x).source = {x} := by
      ext y
      constructor
      · intro hy
        exact (chartAt (Fin 0 → ℝ) x).injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)
      · rintro rfl
        exact mem_chart_source _ y
    rw [← h]
    exact (chartAt (Fin 0 → ℝ) x).open_source
  exact PreconnectedSpace.trivial_of_discrete

/-- **The affine half of sentence 1 on `UniversalCover V v₀` itself, in dimension `0`**: for
`V = ℝ⁰` (a point: compact, Hausdorff, connected, second countable, so a « variété » in the paper's
sense), the universal cover `W` has the strict shell `(W, φ, 0)` (cote `0`), and the conclusion of
sentence 1 holds for it. Degenerate (`P = W`, constant cote), but it is the universal cover, and
in the dimension where sentence 3 fails (`resultBTroisiemePrinted_iff`). -/
theorem resultB_nonVacuite_aff_dim_zero :
    ∃ φ : OpenPartialHomeomorph (UniversalCover (Fin 0 → ℝ) (0 : Fin 0 → ℝ)) (Fin 0 → ℝ),
      IsCoqueStricteAff (univ : Set (UniversalCover (Fin 0 → ℝ) (0 : Fin 0 → ℝ))) φ 0 ∧
      ∃ φ' : OpenPartialHomeomorph (UniversalCover (Fin 0 → ℝ) (0 : Fin 0 → ℝ)) (Fin 0 → ℝ),
        IsCompatibleChart (GAR 0) φ' ∧ φ'.source = univ ∧ EqOn φ' φ univ ∧
        Convex ℝ φ'.target ∧ ¬ ContainsAffLine (Fin 0 → ℝ) φ'.target := by
  obtain ⟨-, hsc, -, -, -⟩ :=
    revetement_universel_divisible_aff (n := 0) (V := Fin 0 → ℝ) (0 : Fin 0 → ℝ)
  haveI := hsc
  haveI := resultB_subsingleton_aff_dim_zero
    (W := UniversalCover (Fin 0 → ℝ) (0 : Fin 0 → ℝ))
  obtain ⟨p, hp⟩ :=
    (prop2_developpement_aff (n := 0) (V := UniversalCover (Fin 0 → ℝ) (0 : Fin 0 → ℝ))).1
  obtain ⟨φ, hφ, hs, -, -⟩ :=
    PremierGX.exists_chart_of_injective hp (fun x y _ => Subsingleton.elim x y)
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (UniversalCover (Fin 0 → ℝ) (0 : Fin 0 → ℝ)))
  have hglb : IsGLB ((0 : (Fin 0 → ℝ) →ᵃ[ℝ] ℝ) '' (φ '' univ)) 0 := by
    have h0 : (0 : (Fin 0 → ℝ) →ᵃ[ℝ] ℝ) '' (φ '' univ) = {0} := by
      ext t
      constructor
      · rintro ⟨y, -, rfl⟩
        rfl
      · rintro rfl
        exact ⟨φ w₀, mem_image_of_mem φ (mem_univ w₀), rfl⟩
    rw [h0]
    exact isGLB_singleton
  have hP : IsPocheAff (univ : Set (UniversalCover (Fin 0 → ℝ) (0 : Fin 0 → ℝ))) φ 0 :=
    ⟨isOpen_univ, isConnected_univ, hs, hφ, hglb, fun _ _ => zero_le_one,
      fun _ _ N _ _ _ _ _ _ _ => mem_univ N⟩
  have hC : IsCoqueStricteAff (univ : Set (UniversalCover (Fin 0 → ℝ) (0 : Fin 0 → ℝ))) φ 0 :=
    ⟨⟨hP, Set.subsingleton_of_subsingleton.convex⟩,
      fun ⟨_, ⟨_, w, hw, _⟩, _⟩ => hw (Subsingleton.elim _ _)⟩
  obtain ⟨φ', h1, h2, h3, h4, h5⟩ := resultB_premiere_aff (0 : Fin 0 → ℝ) hP
  exact ⟨φ, hC, φ', h1, h2, h3, h4 hC.1, h5 hC⟩

end DimZero

/-! ### Non-vacuity of the affine half: the Hopf circle `]0, ∞[ / 2^ℤ`, affinely -/

section HopfAff

/-- The homothety of ratio `2` of `ℝ¹`, an element of `GA(1, ℝ)`. -/
def resultBHopfAffMap : GAR 1 :=
  (LinearEquiv.smulOfNeZero ℝ (Fin 1 → ℝ) 2 two_ne_zero).toAffineEquiv

theorem resultBHopfAffMap_apply (x : Fin 1 → ℝ) : resultBHopfAffMap • x = (2 : ℝ) • x :=
  rfl

/-- The homothety of ratio `2` preserves the half-line `]0, ∞[`. -/
theorem resultBHopfAffMap_mem_iff (x : Fin 1 → ℝ) :
    resultBHopfAffMap • x ∈ demiDroiteOuverte ↔ x ∈ demiDroiteOuverte := by
  show 0 < ((2 : ℝ) • x) 0 ↔ 0 < x 0
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_pos_iff_of_pos_left two_pos

/-- The homothety of ratio `2` of `]0, ∞[`, an affine automorphism of `]0, ∞[`. -/
def resultBHopfAffGen : GXAut (GAR 1) (Fin 1 → ℝ) demiDroiteOuverte :=
  GXAut.ofOpens demiDroiteOuverte resultBHopfAffMap resultBHopfAffMap_mem_iff

/-- **The group `2^ℤ`** of affine homotheties of `]0, ∞[`, the deck group of the affine Hopf
circle `]0, ∞[ / 2^ℤ`. -/
def resultBHopfAffGroup : Subgroup (GXAut (GAR 1) (Fin 1 → ℝ) demiDroiteOuverte) :=
  Subgroup.zpowers resultBHopfAffGen

theorem resultBHopfAffGen_smul (x : demiDroiteOuverte) :
    ((resultBHopfAffGen • x : demiDroiteOuverte) : Fin 1 → ℝ) = (2 : ℝ) • (x : Fin 1 → ℝ) :=
  rfl

/-- `2^k` acts as the homothety of ratio `2^k`. -/
theorem resultBHopfAffGen_zpow_smul (k : ℤ) (x : demiDroiteOuverte) :
    ((resultBHopfAffGen ^ k • x : demiDroiteOuverte) : Fin 1 → ℝ) =
      (2 : ℝ) ^ k • (x : Fin 1 → ℝ) := by
  induction k using Int.induction_on generalizing x with
  | zero => rw [zpow_zero, one_smul, zpow_zero, one_smul]
  | succ i ih =>
    rw [zpow_add_one, mul_smul, ih, resultBHopfAffGen_smul, smul_smul,
      ← zpow_add_one₀ two_ne_zero]
  | pred i ih =>
    have hinv : ((resultBHopfAffGen⁻¹ • x : demiDroiteOuverte) : Fin 1 → ℝ) =
        (2 : ℝ)⁻¹ • (x : Fin 1 → ℝ) := by
      have h := resultBHopfAffGen_smul (resultBHopfAffGen⁻¹ • x)
      rw [smul_inv_smul] at h
      rw [h, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    rw [zpow_sub_one, mul_smul, ih, hinv, smul_smul, ← zpow_sub_one₀ two_ne_zero]

/-- `2^ℤ` acts properly discontinuously on `]0, ∞[` (the argument of
`resultB_hopf_properlyDiscontinuousSMul`, for the affine group). -/
theorem resultB_hopfAff_properlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul resultBHopfAffGroup demiDroiteOuverte := by
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
    (fun k : ℤ => (⟨resultBHopfAffGen ^ k, Subgroup.zpow_mem_zpowers _ k⟩ :
      resultBHopfAffGroup))).subset ?_
  rintro ⟨γ, hγ⟩ hne
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hγ
  obtain ⟨_, ⟨x, hxK, rfl⟩, hxL⟩ := hne
  have hfy : f ((⟨resultBHopfAffGen ^ k, hγ⟩ : resultBHopfAffGroup) • x) = 2 ^ k * f x := by
    show ((resultBHopfAffGen ^ k • x : demiDroiteOuverte) : Fin 1 → ℝ) 0 = _
    rw [resultBHopfAffGen_zpow_smul]
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
theorem resultB_hopfAff_isCancelSMul : IsCancelSMul resultBHopfAffGroup demiDroiteOuverte := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨γ, hγ⟩ x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hγ
  have h1 : (2 : ℝ) ^ k • (x : Fin 1 → ℝ) = x := by
    rw [← resultBHopfAffGen_zpow_smul]
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
theorem resultB_hopfAff_exists_isCompact : ∃ K₀ : Set demiDroiteOuverte, IsCompact K₀ ∧
    ∀ x : demiDroiteOuverte, ∃ γ : resultBHopfAffGroup, γ • x ∈ K₀ := by
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
    refine ⟨⟨resultBHopfAffGen ^ (-m), Subgroup.zpow_mem_zpowers _ _⟩, ?_⟩
    show 1 ≤ ((resultBHopfAffGen ^ (-m) • x : demiDroiteOuverte) : Fin 1 → ℝ) 0 ∧
      ((resultBHopfAffGen ^ (-m) • x : demiDroiteOuverte) : Fin 1 → ℝ) 0 ≤ 2
    rw [resultBHopfAffGen_zpow_smul, Pi.smul_apply, smul_eq_mul, zpow_neg]
    constructor
    · rw [le_inv_mul_iff₀ h2m, mul_one]
      exact hm1
    · rw [inv_mul_le_iff₀ h2m]
      rw [zpow_add_one₀ two_ne_zero] at hm2
      linarith

/-- **The hypotheses of sentence 1's affine half are satisfiable, non-degenerately** (`n = 1`):
the Hopf circle `V = ]0, ∞[ / 2^ℤ` is a compact, Hausdorff, connected, second countable locally
affine manifold, and `π : ]0, ∞[ → V` is a simply connected covering and an affine morphism. The
cover `]0, ∞[` has the strict shell `P = ]0, 1[ ≠ ]0, ∞[` with the non-constant cote `x₀`
(`exists_isCoqueStricteAff_demiDroite_ne_univ`); so (`resultB_poche_aff`) `]0, ∞[` is identified
by a chart `φ̃` inducing `φ` on `P` with an open convex set of `ℝ¹` containing no line; and the
projection `φ̃` is unbounded (sentence 3, `resultB_projection_non_bornee`). -/
theorem resultB_nonVacuite_hopf_aff :
    ∃ (V : Type) (_ : TopologicalSpace V) (_ : ChartedSpace (Fin 1 → ℝ) V)
      (_ : HasGroupoid V (affGroupoid 1)), CompactSpace V ∧ T2Space V ∧ ConnectedSpace V ∧
      SecondCountableTopology V ∧
      ∃ π : demiDroiteOuverte → V, IsCoveringMap π ∧ IsGXMorphism (GAR 1) (Fin 1 → ℝ) π ∧
        SimplyConnectedSpace demiDroiteOuverte ∧
        ∃ (P : Set demiDroiteOuverte) (φ : OpenPartialHomeomorph demiDroiteOuverte (Fin 1 → ℝ)),
          IsCoqueStricteAff P φ (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).toAffineMap ∧
          P ≠ univ ∧
          ∃ φ' : OpenPartialHomeomorph demiDroiteOuverte (Fin 1 → ℝ),
            IsCompatibleChart (GAR 1) φ' ∧ φ'.source = univ ∧ EqOn φ' φ P ∧
            Convex ℝ φ'.target ∧ ¬ ContainsAffLine (Fin 1 → ℝ) φ'.target ∧
            ¬ Bornology.IsBounded (range φ') := by
  haveI := resultB_hopfAff_properlyDiscontinuousSMul
  haveI := resultB_hopfAff_isCancelSMul
  have hΓ : ∀ γ : resultBHopfAffGroup,
      IsGXMorphism (GAR 1) (Fin 1 → ℝ) fun v : demiDroiteOuverte => γ • v :=
    fun γ => (γ : GXAut (GAR 1) (Fin 1 → ℝ) demiDroiteOuverte).isGXMorphism
  haveI := continuousConstSMul_of_isGXMorphism hΓ
  haveI : LocallyCompactSpace demiDroiteOuverte :=
    ChartedSpace.locallyCompactSpace (Fin 1 → ℝ) demiDroiteOuverte
  have hcov :
      IsCoveringMap (Quotient.mk (MulAction.orbitRel resultBHopfAffGroup demiDroiteOuverte)) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
  have hG := isGXMorphism_quotientMk hΓ
  have hgr := hasGroupoid_quotient hΓ
  obtain ⟨K₀, hK₀, hK₀x⟩ := resultB_hopfAff_exists_isCompact
  have hcpt :
      CompactSpace (MulAction.orbitRel.Quotient resultBHopfAffGroup demiDroiteOuverte) := by
    refine ⟨?_⟩
    have huniv : Quotient.mk (MulAction.orbitRel resultBHopfAffGroup demiDroiteOuverte) '' K₀ =
        univ := by
      refine eq_univ_of_forall fun q => ?_
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
      obtain ⟨γ, hγ⟩ := hK₀x x
      exact ⟨γ • x, hγ, Quotient.sound (MulAction.orbitRel_apply.2 ⟨γ, rfl⟩)⟩
    rw [← huniv]
    exact hK₀.image continuous_quotient_mk'
  haveI := hcpt
  -- `]0, ∞[` is convex, hence simply connected
  have hsc : SimplyConnectedSpace demiDroiteOuverte := by
    have hconv : Convex ℝ (demiDroiteOuverte : Set (Fin 1 → ℝ)) :=
      (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
    haveI := hconv.contractibleSpace ⟨fun _ => 1, show (0 : ℝ) < 1 from one_pos⟩
    infer_instance
  haveI := hsc
  have hsc2 : SecondCountableTopology
      (MulAction.orbitRel.Quotient resultBHopfAffGroup demiDroiteOuverte) :=
    ContinuousConstSMul.secondCountableTopology
  -- the strict shell `]0, 1[` of `]0, ∞[` (Ch. 2 § 1)
  obtain ⟨P, φ, hC, hne⟩ := exists_isCoqueStricteAff_demiDroite_ne_univ
  obtain ⟨φ', h1, h2, h3, h4, h5⟩ := resultB_poche_aff hcov hG hC.1.1
  have hp : IsDeveloping (GAR 1) φ' := fun x => h1 x (h2.symm ▸ mem_univ x)
  exact ⟨_, inferInstance, inferInstance, hgr, hcpt, inferInstance, inferInstance, hsc2, _, hcov,
    hG, hsc, P, φ, hC, hne, φ', h1, h2, h3, h4 hC.1, h5 hC,
    (resultB_projection_non_bornee hcov hG).2 φ' hp⟩

end HopfAff

end Benzecri
