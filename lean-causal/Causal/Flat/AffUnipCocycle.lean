import Causal.Flat.AffUnipFitting
import Causal.Flat.MaxUnipHirsch
import Mathlib.RepresentationTheory.Basic

/-!
# `Causal.Flat.AffUnipCocycle` — `F ≠ ∅` for a nilpotent group of affine transformations

Step module of Prop 5.2 in the PRINTED generality (`bthm:unip`, DEC-123, generalizing DEC-121's
`Flat/MaxUnipCocycle` §2 from `Isom(𝐌ⁿ)` to `V ≃ᵃ[k] V`). **No label is marked.** For a nilpotent
`N ≤ V ≃ᵃ[k] V`, `V` finite-dimensional over a field `k`:

* `affEquiv_mul_apply_zero` — the translation part is a cocycle: `(γ η) 0 = L γ (η 0) + γ 0`.
* `affFittingRep N` — the representation of `↥N` on `V ⧸ affFitting N` (`Submodule.mapQ`).
* `exists_mem_affFitting_of_isNilpotent` — `F := {x | ∀ γ ∈ N, γ x − x ∈ V₁}` is nonempty: the
  cocycle `u γ := [γ 0]` is a coboundary `δ[w]` by Hirsch (`exists_coboundary_of_isNilpotent`,
  `Flat/MaxUnipHirsch`, already for any group and field), the invariants vanishing by
  `mem_affFitting_of_forall`; take `x₀ := −w`.

> Lemma 1.6. If $G$ is nilpotent, some coset of $E_u$ is invariant. (Fried–Goldman–Hirsch 1981,
> §1, as read for the survey; the proof: the translational part mod $E_u$ is a crossed
> homomorphism, and $H^1 = 0$ by 1.1 and 1.4)

> Let $\Gamma$ be a nilpotent group of affine transformations of ${\mathbb R}^{n}$. Then, there
> exist a maximal $\Gamma$-invariant affine subspace ${\bf U}$ of ${\mathbb R}^{n}$ such that the
> restriction of the action of $\Gamma$ to ${\bf U}$ is unipotent. Moreover, this maximal
> unipotent affine subspace is unique. (`GHFspace.tex` l.1712–1717, the statement this serves)

**Proof plan (port).** `exists_mem_fitting_of_h1` of `Flat/MaxUnipCocycle`, with `trOf γ ↦ γ 0`,
`trOf_mul' ↦ affEquiv_mul_apply_zero`, `fittingRep ↦ affFittingRep`, and the bare `hH1`
discharged in place by `exists_coboundary_of_isNilpotent` (universes: `W := V ⧸ affFitting N`
lives in `V`'s universe, `↥N` in `max u v`; `HirschH1.{u, v}` is universe-polymorphic in `G`).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| 5.2: `Γ` nilpotent | ✓ carried: `Group.IsNilpotent N` |
| 5.2: affine transformations of `ℝⁿ` | ⚠ weakened: `V ≃ᵃ[k] V`, any field `k`, any finite-dimensional `V` |

## SCOPE (disclosed)
* Sorry-free (both tagged skeleton sorries filled, DEC-123); `affFittingRep` rests on
  `affFitting_linear_mem` of `Flat/AffUnipFitting`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. DEC-123.
-/

namespace Causal.Flat

open Module

universe u v

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- **The translation part is a cocycle**: `(γ η) 0 = L γ (η 0) + γ 0`. -/
theorem affEquiv_mul_apply_zero (γ η : V ≃ᵃ[k] V) : (γ * η) 0 = γ.linear (η 0) + γ 0 := by
  have h := congrFun (AffineMap.decomp γ.toAffineMap) (η 0)
  rw [AffineEquiv.coe_mul, Function.comp_apply]
  simpa only [AffineEquiv.coe_toAffineMap, AffineEquiv.linear_toAffineMap, Pi.add_apply,
      LinearEquiv.coe_coe] using h

/-- The representation of `↥N` on `V ⧸ V₁` induced by the linear parts. -/
noncomputable def affFittingRep (N : Subgroup (V ≃ᵃ[k] V)) :
    Representation k N (V ⧸ affFitting N) where
  toFun γ := Submodule.mapQ _ _ ((γ : V ≃ᵃ[k] V).linear : V →ₗ[k] V)
    fun _ hw => affFitting_linear_mem γ.2 hw
  map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

theorem affFittingRep_mk (N : Subgroup (V ≃ᵃ[k] V)) (γ : N) (x : V) :
    affFittingRep N γ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((γ : V ≃ᵃ[k] V).linear x) :=
  rfl

/-- **`F ≠ ∅` for nilpotent `N`** (FGH Lemma 1.6, affine form): some `x₀` has `γ x₀ − x₀ ∈ V₁` for
every `γ ∈ N`. -/
theorem exists_mem_affFitting_of_isNilpotent [FiniteDimensional k V] (N : Subgroup (V ≃ᵃ[k] V))
    [Group.IsNilpotent N] : ∃ x₀ : V, ∀ γ ∈ N, γ x₀ - x₀ ∈ affFitting N := by
  -- `exists_coboundary_of_isNilpotent` at `affFittingRep N`; cocycle `c γ := [γ 0]`; from
  -- `c = δ[w]` take `x₀ := −w` (port of `exists_mem_fitting_of_h1`)
  have hinv : ∀ y : V ⧸ affFitting N, (∀ g, affFittingRep N g y = y) → y = 0 := by
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      refine (Submodule.Quotient.mk_eq_zero _).2 (mem_affFitting_of_forall fun γ hγ => ?_)
      have := hy ⟨γ, hγ⟩
      rw [affFittingRep_mk, Submodule.Quotient.eq] at this
      exact this
  have hcoc : ∀ g h : N,
      (Submodule.Quotient.mk (((g * h : N) : V ≃ᵃ[k] V) 0) : V ⧸ affFitting N)
        = Submodule.Quotient.mk ((g : V ≃ᵃ[k] V) 0)
          + affFittingRep N g (Submodule.Quotient.mk ((h : V ≃ᵃ[k] V) 0)) := by
    intro g h
    rw [affFittingRep_mk, ← Submodule.Quotient.mk_add, Subgroup.coe_mul,
      affEquiv_mul_apply_zero, add_comm]
  obtain ⟨w, hw⟩ := exists_coboundary_of_isNilpotent (affFittingRep N) hinv
    (fun g => Submodule.Quotient.mk ((g : V ≃ᵃ[k] V) 0)) hcoc
  induction w using Submodule.Quotient.induction_on with
  | H w =>
    refine ⟨-w, fun γ hγ => ?_⟩
    have e := hw ⟨γ, hγ⟩
    rw [affFittingRep_mk, ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at e
    have hd : γ (-w) = γ.linear (-w) + γ 0 := by
      simpa only [AffineEquiv.coe_toAffineMap, AffineEquiv.linear_toAffineMap, Pi.add_apply,
        LinearEquiv.coe_coe] using congrFun (AffineMap.decomp γ.toAffineMap) (-w)
    have : γ (-w) - -w = γ 0 - (γ.linear w - w) := by
      rw [hd, map_neg]; abel
    rw [this]
    exact e

end Causal.Flat
