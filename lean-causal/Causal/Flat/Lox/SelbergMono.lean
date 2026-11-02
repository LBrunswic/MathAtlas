import CausalScaffold.Flat.Externals

/-!
# Selberg's lemma descends along an injective linear map, hence from `𝐌ⁿ` to `𝐌ⁿ¹` for `n₁ ≤ n`

Monotonicity of DEC-44's external `SelbergLemma` (`Flat/Externals.lean`, gap G5 / finding F2),
for `loxo_generic_torusProduct` (`Flat/Loxodromic.lean`, family (a)). **No label is marked**:
Selberg's lemma has no paper environment, and this file proves a transfer lemma about the
external, not the external itself.

* No label, **no `sorry`**: `selbergLemma_of_injective`. If `f : W →ₗ V` is injective and
  `SelbergLemma V`, then `SelbergLemma W`.
* No label, **no `sorry`**: `selbergLemma_minkowski_of_le`. `d₁ ≤ d` and
  `SelbergLemma (Minkowski d)` give `SelbergLemma (Minkowski d₁)`.

It serves the conclusion of [10.G] (`GHFspace.tex:3454–3456`):

> \emph{Conclusion:\/} $M(S) = \Gamma\backslash\Omega(\widetilde{S})$
> is a twisted product of a Cauchy-hyperbolic spacetime
> by a flat torus.

Why it is needed: family (a) asks for torsion-free linear parts in the group of `M₁`, a subgroup
of `isom d₁` (the restriction of `Γ'` to `U`), not of `isom d`. A torsion-free `L(Γ)` does not
give a torsion-free `L_U(Γ)`: `L(γ)|_U` can have finite order while `L(γ)` does not, because
`U^⊥` carries an arbitrary rotation. So Selberg's lemma is used directly in dimension `d₁`,
and this file derives that instance from the given one in dimension `d`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Selberg's lemma for `GL(n, ℝ)` (cited, not stated in the paper) | ✓ carried as `hS : SelbergLemma V` (DEC-44 external) |
| `U ⊆ 𝐌ⁿ` of dimension `n₁ + 1 ≤ n + 1` | ⚠ weakened: any injective linear `f : W → V`; for Minkowski, any `d₁ ≤ d` |

## SCOPE (disclosed)

Nothing is left open. The proof is purely group-theoretic: `φ : GL(W) →* GL(V)` sends `g` to
`g ⊕ id_C`, with `C` a complement of `range f`, conjugated by `V ≃ₗ W × C`. It is injective, so
it maps finitely generated `G` to finitely generated `φ(G)`, and pulling back the torsion-free
finite-index `H' ≤ φ(G)` given by `hS` yields `G ⊓ φ⁻¹(H')`. That subgroup has finite relative
index (`Subgroup.relIndex_comap`) and is torsion-free (finite order maps to finite order, and
`φ` is injective). The Minkowski embedding is `id_ℝ × (extension by zero along Fin.castLE)`.
Nothing here relates `SelbergLemma (Minkowski d₁)` to the restriction map `isom d → isom d₁`;
that link (GR) is the consumer's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Proof plan from the
Lox planner (`/tmp/loxplan/S1_SelbergMono.lean`).
-/

namespace Causal.Flat.Lox
open Causal.Flat

/-- Block-diagonal extension by the identity: `g ↦ e ∘ (g × id_C) ∘ e⁻¹`, for `e : W × C ≃ₗ V`. -/
noncomputable def extByIdHom {V W C : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup C] [Module ℝ C] (e : (W × C) ≃ₗ[ℝ] V) :
    (W ≃ₗ[ℝ] W) →* (V ≃ₗ[ℝ] V) where
  toFun g := e.symm.trans ((g.prodCongr (LinearEquiv.refl ℝ C)).trans e)
  map_one' := LinearEquiv.ext fun v => by simp
  map_mul' g h := LinearEquiv.ext fun v => by simp

/-- `extByIdHom e` is injective: evaluate at `e (w, 0)`. -/
theorem extByIdHom_injective {V W C : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup C] [Module ℝ C] (e : (W × C) ≃ₗ[ℝ] V) :
    Function.Injective (extByIdHom e) := by
  intro g h hgh
  ext w
  have := congrArg (fun φ : V ≃ₗ[ℝ] V => e.symm (φ (e (w, 0)))) hgh
  simpa [extByIdHom] using congrArg Prod.fst this

/-- Selberg's lemma descends along an injective linear map `W ↪ V`. -/
theorem selbergLemma_of_injective {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (f : W →ₗ[ℝ] V) (hf : Function.Injective f) (hS : SelbergLemma V) : SelbergLemma W := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range f)
  let e : (W × C) ≃ₗ[ℝ] V :=
    ((LinearEquiv.ofInjective f hf).prodCongr (LinearEquiv.refl ℝ C)).trans
      (Submodule.prodEquivOfIsCompl _ _ hC)
  set φ := extByIdHom e
  have hφ : Function.Injective φ := extByIdHom_injective e
  intro G hG
  obtain ⟨H', -, hi, htf⟩ := hS (G.map φ) (fg_map_of_fg hG φ)
  refine ⟨G ⊓ H'.comap φ, inf_le_left, ?_, fun g hg hfin => ?_⟩
  · rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
    exact hi
  · have h1 : φ g = 1 := htf _ hg.2 (φ.isOfFinOrder hfin)
    exact hφ (h1.trans φ.map_one.symm)

/-- Selberg's lemma for `𝐌ⁿ` gives it for `𝐌ⁿ¹`, `n₁ ≤ n` (consumer: `loxo_generic_torusProduct`,
family (a), `GHFspace.tex:3454–3456`). -/
theorem selbergLemma_minkowski_of_le {d d₁ : ℕ} (h : d₁ ≤ d) (hS : SelbergLemma (Minkowski d)) :
    SelbergLemma (Minkowski d₁) := by
  let g : EuclideanSpace ℝ (Fin d₁) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.toLinearEquiv.toLinearMap ∘ₗ
      Function.ExtendByZero.linearMap ℝ (Fin.castLE h) ∘ₗ
        (EuclideanSpace.equiv (Fin d₁) ℝ).toLinearEquiv.toLinearMap
  have hg : Function.Injective g := by
    refine (EuclideanSpace.equiv (Fin d) ℝ).symm.injective.comp ?_
    refine (Function.extend_injective (Fin.castLE_injective h) 0).comp ?_
    exact (EuclideanSpace.equiv (Fin d₁) ℝ).injective
  refine selbergLemma_of_injective ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap g) ?_ hS
  exact Function.injective_id.prodMap hg

end Causal.Flat.Lox
