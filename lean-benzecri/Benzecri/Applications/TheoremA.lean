import Benzecri.Applications.Products

/-!
# `Benzecri.Applications.TheoremA` — the introduction's result A

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Introduction, § 1 « Les résultats », journal p. 230; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45w (wave 5).

* **`bzthm:intro_A`** — `benzecri1960_ch1.tex:69` (l.69–80, p. 230). **MARKED.**
  `Benzecri.theoremA`: both assertions, `theoremA_affine` (a compact `V` with a locally projective
  structure of dimension `n`: `V × S¹` locally affine, of dimension `n + 1`) and
  `theoremA_projective` (compact `V₁, …, V_p`, `p = q + 1`, with locally projective structures of
  dimensions `n i`: `V₁ × … × V_p × (S¹)^{p−1}` locally projective, of dimension `Σ n i + q`). The
  assembly of § 3's two corollaries (`produit_cercle`, `produit_projectif`), which need no
  compactness; compactness supplies their « variété » hypotheses (paracompact, σ-compact).

> **A.** Si une variété compacte $V$ peut être munie d'une structure localement projective, le
> produit $V\times S_1$ peut être muni d'une structure localement affine ($S_1$ désigne le cercle;
> cf. chap. 1, § 3, prop. 1, corrolaire [sic]). Si chacune des $p$ variétés compactes $V_i$ peut
> être munie d'une structure localement projective, le produit
> $V_1\times\ldots\times V_i\times\ldots\times V_p\times S_1^{(p-1)}$ peut être muni d'une
> structure localement projective (chap. 1, § 3, prop. 3, corollaire).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V`, `V_i` compact | ✓ carried (`[CompactSpace _]`) |
| « variété »: Hausdorff | ✓ carried (`[T2Space _]`) |
| « variété »: connected, second countable | not needed (compact ⇒ paracompact, σ-compact) |
| dimensions | arbitrary, per factor |
| `S₁` | Mathlib's `Circle`; `S₁^{(p−1)}` is `Fin q → Circle` |

## SCOPE (disclosed)

* « peut être munie d'une structure » is an existential over charted spaces with `HasGroupoid`
  (DEC-112 conventions); the structures produced are the quotient structures of § 3 (see
  `FCone.exists_affine_prod_circle`, `exists_proj_prod_circle`).
* `p ≥ 1` (`p = q + 1`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

namespace Benzecri

universe u

/-- **Theorem A, first assertion** (`bzthm:intro_A`, first sentence). -/
theorem theoremA_affine {n : ℕ} (V : Type u) [TopologicalSpace V] [CompactSpace V] [T2Space V]
    (h : ∃ cs : ChartedSpace (S n) V, @HasGroupoid _ _ V _ cs (projGroupoid n)) :
    ∃ cs : ChartedSpace (Fin (n + 1) → ℝ) (V × Circle),
      @HasGroupoid _ _ (V × Circle) _ cs (affGroupoid (n + 1)) :=
  produit_cercle V h

/-- **Theorem A, second assertion** (`bzthm:intro_A`, second sentence). -/
theorem theoremA_projective {q : ℕ} (V : Fin (q + 1) → Type u) [∀ i, TopologicalSpace (V i)]
    [∀ i, CompactSpace (V i)] [∀ i, T2Space (V i)] (n : Fin (q + 1) → ℕ)
    (h : ∀ i, ∃ cs : ChartedSpace (S (n i)) (V i), @HasGroupoid _ _ (V i) _ cs (projGroupoid (n i))) :
    ∃ cs : ChartedSpace (S (∑ i, n i + q)) ((∀ i, V i) × (Fin q → Circle)),
      @HasGroupoid _ _ ((∀ i, V i) × (Fin q → Circle)) _ cs (projGroupoid (∑ i, n i + q)) :=
  produit_projectif V n h

/-- **Theorem A** (`bzthm:intro_A`): both assertions. -/
theorem theoremA :
    (∀ (n : ℕ) (V : Type u) [TopologicalSpace V] [CompactSpace V] [T2Space V],
      (∃ cs : ChartedSpace (S n) V, @HasGroupoid _ _ V _ cs (projGroupoid n)) →
      ∃ cs : ChartedSpace (Fin (n + 1) → ℝ) (V × Circle),
        @HasGroupoid _ _ (V × Circle) _ cs (affGroupoid (n + 1))) ∧
    (∀ (q : ℕ) (V : Fin (q + 1) → Type u) [∀ i, TopologicalSpace (V i)]
      [∀ i, CompactSpace (V i)] [∀ i, T2Space (V i)] (n : Fin (q + 1) → ℕ),
      (∀ i, ∃ cs : ChartedSpace (S (n i)) (V i),
        @HasGroupoid _ _ (V i) _ cs (projGroupoid (n i))) →
      ∃ cs : ChartedSpace (S (∑ i, n i + q)) ((∀ i, V i) × (Fin q → Circle)),
        @HasGroupoid _ _ ((∀ i, V i) × (Fin q → Circle)) _ cs (projGroupoid (∑ i, n i + q))) :=
  ⟨fun _ V _ _ _ h => theoremA_affine V h, fun _ V _ _ _ n h => theoremA_projective V n h⟩

end Benzecri
