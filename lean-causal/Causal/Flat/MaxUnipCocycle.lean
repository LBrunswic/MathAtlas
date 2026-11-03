import Causal.Flat.Externals
import Mathlib.RepresentationTheory.Basic

/-!
# `Causal.Flat.MaxUnipCocycle` — the joint unipotent part `V₁` of `L(N)`, and `F ≠ ∅` from `H¹ = 0`

Step module of Prop 5.2 (`bthm:unip`, DEC-121, route P1 of `docs/CARRIERE-DALBO-SURVEY.md`
§2.1). **No label is marked.** For any subgroup `N ≤ Isom(𝐌ⁿ)` let
`V₁ := ⨅ γ ∈ N, maxGenEigenspace (L γ) 1` (the Fitting submodule of FGH, the joint generalized
`1`-eigenspace). This module proves, for **every** `N` (no nilpotency):

* `fitting_linOf_mem` — `V₁` is `L(N)`-invariant (`L h` maps `maxGenEigenspace (L γ) 1` onto
  `maxGenEigenspace (L (h γ h⁻¹)) 1`, and conjugation by `h ∈ N` permutes `N`).
* `mem_fitting_of_forall` — `(𝐌ⁿ ⧸ V₁)^N = 0` (FGH Lemma 1.4): if `(L γ − 1) x ∈ V₁` for all
  `γ ∈ N` then `x ∈ V₁`.
* `fittingRep N` — the representation of `↥N` on `𝐌ⁿ ⧸ V₁` (`Submodule.mapQ`).
* `exists_mem_fitting_of_h1` — **if `H¹(N; 𝐌ⁿ ⧸ V₁) = 0` when the invariants vanish** (the bare
  hypothesis `hH1`, supplied by `Flat/MaxUnipHirsch` for nilpotent `N`), then
  `F := {x | ∀ γ ∈ N, γ x − x ∈ V₁}` is nonempty. Proof: `u γ := [trOf γ]` is a cocycle
  (`trOf (g h) = L g (trOf h) + trOf g`), `u = δ[w]`, and `x₀ := −w`.

> Lemma 1.6. If $G$ is nilpotent, some coset of $E_u$ is invariant. (Fried–Goldman–Hirsch 1981,
> §1, as read for the survey; the proof: the translational part mod $E_u$ is a crossed
> homomorphism, and $H^1 = 0$ by 1.1 and 1.4)

> Let $\Gamma$ be a nilpotent group of affine transformations of ${\mathbb R}^{n}$. Then, there
> exist a maximal $\Gamma$-invariant affine subspace ${\bf U}$ of ${\mathbb R}^{n}$ such that the
> restriction of the action of $\Gamma$ to ${\bf U}$ is unipotent. Moreover, this maximal
> unipotent affine subspace is unique. (`GHFspace.tex` l.1712–1717, the statement this serves)

**Pitfall (survey §4.4).** Only the *joint* `V₁` is `N`-invariant; the generalized eigenspaces
of a single `L γ` are not, for non-connected nilpotent `N` (`D₈` on `ℝ²`, `Q₈`).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| FGH 1.6: `G` nilpotent | ⚠ weakened: any `N ≤ Isom(𝐌ⁿ)`, nilpotency entering only through `hH1` |
| FGH 1.4: `E_u` the Fitting submodule | `V₁ = ⨅ γ ∈ N, maxGenEigenspace (L γ) 1` |

## SCOPE (disclosed)
* `V₁` is written out (no definition), so that `Flat/MaxUnipFitting`, which does not import this
  module, states the same set; the glue `Flat/MaxUnipProof` composes them.
* `trOf (g h) = L g (trOf h) + trOf g` is reproved privately (`trOf_mul'`), since `TitsNull`
  (which has `trOf_mul`) is not imported.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. DEC-121.
-/

namespace Causal.Flat

open Module

variable {d : ℕ}

/-- `L − 1•1` is Barbot's `pOf L`, so `Module.End.mem_maxGenEigenspace` reads through `pOf`. -/
private theorem mem_maxGenEigenspace_one_iff_pOf (A : Minkowski d ≃ₗ[ℝ] Minkowski d)
    (x : Minkowski d) :
    x ∈ Module.End.maxGenEigenspace A.toLinearMap 1 ↔ ∃ k : ℕ, (pOf A ^ k) x = 0 := by
  rw [Module.End.mem_maxGenEigenspace, one_smul]
  rfl

/-- The translation part of a product (`TitsNull.trOf_mul`, reproved here: `TitsNull` is not
imported). -/
private theorem trOf_mul' (g h : isom d) : trOf (g * h) = linOf g (trOf h) + trOf g := by
  have h0 : ∀ k : isom d, k • (0 : Minkowski d) = trOf k := fun k => by
    rw [smul_eq_lin_add, map_zero, zero_add]
  rw [← h0, mul_smul, h0, smul_eq_lin_add]

/-- **`V₁` is `L(N)`-invariant.** -/
theorem fitting_linOf_mem {N : Subgroup (isom d)} {γ : isom d} (hγ : γ ∈ N) {v : Minkowski d}
    (hv : v ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1) :
    linOf γ v ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1 := by
  -- for `η ∈ N`, `γ⁻¹ η γ ∈ N` and `(L η − 1)^k (L γ v) = L γ ((L (γ⁻¹ η γ) − 1)^k v)`
  simp only [Submodule.mem_iInf] at hv ⊢
  intro η hη
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace_one_iff_pOf _ _).1
    (hv _ (N.mul_mem (N.mul_mem (N.inv_mem hγ) hη) hγ))
  refine (mem_maxGenEigenspace_one_iff_pOf _ _).2 ⟨k, ?_⟩
  have hc : linOf η = linOf γ * linOf (γ⁻¹ * η * γ) * (linOf γ)⁻¹ := by
    rw [linOf_inv_conj]; group
  rw [hc, pow_pOf_conj, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, hk, map_zero]

/-- **`(𝐌ⁿ ⧸ V₁)^N = 0`** (FGH Lemma 1.4, affine form). -/
theorem mem_fitting_of_forall {N : Subgroup (isom d)} {x : Minkowski d}
    (hx : ∀ γ ∈ N, linOf γ x - x ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1) :
    x ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1 := by
  -- `(L γ − 1) x ∈ V₁ ≤ maxGenEigenspace (L γ) 1` gives `(L γ − 1)^(k+1) x = 0`
  simp only [Submodule.mem_iInf] at hx ⊢
  intro γ hγ
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace_one_iff_pOf _ _).1 (hx γ hγ γ hγ)
  refine (mem_maxGenEigenspace_one_iff_pOf _ _).2 ⟨k + 1, ?_⟩
  rw [pow_succ, Module.End.mul_apply, pOf_apply]
  exact hk

/-- The representation of `↥N` on `𝐌ⁿ ⧸ V₁` induced by the linear parts. -/
noncomputable def fittingRep (N : Subgroup (isom d)) :
    Representation ℝ N
      (Minkowski d ⧸ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1) where
  toFun γ := Submodule.mapQ _ _ (linOf (γ : isom d)).toLinearMap
    fun _ hv => fitting_linOf_mem γ.2 hv
  map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

theorem fittingRep_mk (N : Subgroup (isom d)) (γ : N) (x : Minkowski d) :
    fittingRep N γ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (linOf (γ : isom d) x) :=
  rfl

/-- **`F ≠ ∅` from `H¹ = 0`** (FGH Lemma 1.6, affine form): some `x₀` has `γ x₀ − x₀ ∈ V₁` for
every `γ ∈ N`. -/
theorem exists_mem_fitting_of_h1 (N : Subgroup (isom d))
    (hH1 : ∀ (W : Type) [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
      (ρ : Representation ℝ N W), (∀ x : W, (∀ g, ρ g x = x) → x = 0) →
      ∀ c : N → W, (∀ g h, c (g * h) = c g + ρ g (c h)) → ∃ x : W, ∀ g, c g = ρ g x - x) :
    ∃ x₀ : Minkowski d, ∀ γ ∈ N,
      γ • x₀ - x₀ ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1 := by
  -- `hH1` at `fittingRep N`; cocycle `c γ := [trOf γ]`; from `c = δ[w]` take `x₀ := −w`
  set V₁ := ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1 with hV₁
  have hinv : ∀ y : Minkowski d ⧸ V₁, (∀ g, fittingRep N g y = y) → y = 0 := by
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      refine (Submodule.Quotient.mk_eq_zero _).2 (mem_fitting_of_forall fun γ hγ => ?_)
      have := hy ⟨γ, hγ⟩
      rw [fittingRep_mk, Submodule.Quotient.eq] at this
      exact this
  have hcoc : ∀ g h : N, (Submodule.Quotient.mk (trOf ((g * h : N) : isom d)) : Minkowski d ⧸ V₁)
      = Submodule.Quotient.mk (trOf (g : isom d))
        + fittingRep N g (Submodule.Quotient.mk (trOf (h : isom d))) := by
    intro g h
    rw [fittingRep_mk, ← Submodule.Quotient.mk_add, Subgroup.coe_mul, trOf_mul', add_comm]
  obtain ⟨w, hw⟩ := hH1 (Minkowski d ⧸ V₁) (fittingRep N) hinv
    (fun g => Submodule.Quotient.mk (trOf (g : isom d))) hcoc
  induction w using Submodule.Quotient.induction_on with
  | H w =>
    refine ⟨-w, fun γ hγ => ?_⟩
    have e := hw ⟨γ, hγ⟩
    rw [fittingRep_mk, ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at e
    have : γ • (-w) - -w = trOf γ - (linOf γ w - w) := by
      rw [smul_eq_lin_add, map_neg]; abel
    rw [this]
    exact e

end Causal.Flat
