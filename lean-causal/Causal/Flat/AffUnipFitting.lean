import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.Nilpotent

/-!
# `Causal.Flat.AffUnipFitting` — the Fitting coset `x₀ + V₁` for a group of affine transformations

Step module of Prop 5.2 in the PRINTED generality (`bthm:unip`, DEC-123, generalizing DEC-121's
`Flat/MaxUnipCocycle` §1 and `Flat/MaxUnipFitting` from `Isom(𝐌ⁿ)` to `V ≃ᵃ[k] V`). **No label is
marked.** For a field `k`, a finite-dimensional `k`-vector space `V` and **any** subgroup
`N ≤ V ≃ᵃ[k] V` (no nilpotency), let `affFitting N := ⨅ γ ∈ N, maxGenEigenspace (γ.linear) 1`
(the Fitting submodule `E_u` of Fried–Goldman–Hirsch, the joint generalized `1`-eigenspace).

* `AffIsUnipotentInvariant N U`, `AffIsMaxUnipotent N U` — the affine forms of `Flat/Externals`'
  `IsUnipotentInvariant`, `IsMaxUnipotent` (same two clauses; `pOf (linOf γ)` read as
  `(γ.linear : V →ₗ[k] V) - 1`).
* `affFitting_linear_mem` — `affFitting N` is `L(N)`-invariant.
* `mem_affFitting_of_forall` — `(V ⧸ affFitting N)^N = 0` (FGH Lemma 1.4).
* `affIsUnipotentInvariant_mk'_affFitting` — for `x₀ ∈ F := {x | ∀ γ ∈ N, γ x − x ∈ V₁}`,
  `x₀ + V₁` is unipotent-invariant (uniform exponent `finrank k V`).
* `le_mk'_affFitting_of_affIsUnipotentInvariant` — every unipotent-invariant `U` (`⊥` included)
  lies in `x₀ + V₁`.
* `affMaxUnipotent_of_mem_affFitting` — hence `x₀ + V₁` is nonempty, maximal, the only maximal one.

> Let $\Gamma$ be a nilpotent group of affine transformations of ${\mathbb R}^{n}$. Then, there
> exist a maximal $\Gamma$-invariant affine subspace ${\bf U}$ of ${\mathbb R}^{n}$ such that the
> restriction of the action of $\Gamma$ to ${\bf U}$ is unipotent. Moreover, this maximal
> unipotent affine subspace is unique. (`GHFspace.tex` l.1712–1717, the statement this serves)

> […] there is a unique maximal submodule $E_u \subset E$ upon which $G$ acts unipotently.
> (Fried–Goldman–Hirsch 1981, §1, as read for the survey)

**Proof plan (port, not new mathematics).** Each statement is the `isom d` statement of
`Flat/MaxUnipCocycle` / `Flat/MaxUnipFitting` with `linOf γ ↦ γ.linear`, `γ • x ↦ γ x`,
`pOf A ↦ (A : V →ₗ[k] V) - 1`, `smul_eq_lin_add ↦ AffineMap.decomp` (`γ x = γ.linear x + γ 0`),
`linOf_inv_conj ↦` `AffineEquiv.linearHom` is a monoid hom, `pow_pOf_conj ↦`
`(C A C⁻¹ − 1)^k = C (A − 1)^k C⁻¹` (`LinearEquiv.conj_pow`-style, or by `induction k`).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| 5.2: `Γ` nilpotent | ⚠ weakened: any `N`; nilpotency is spent only on `F ≠ ∅` (`hx₀`, `Flat/AffUnipCocycle`) |
| 5.2: affine transformations of `ℝⁿ` | ⚠ weakened: `V ≃ᵃ[k] V`, any field `k`, any finite-dimensional `V` |
| 5.2: "maximal", "unique" | ✓ carried, as `AffIsMaxUnipotent` and uniqueness among maximal ones |

## SCOPE (disclosed)
* PROVED (DEC-123 prover): every statement is the named DEC-121 proof, ported; no `sorry`. The
  one new lemma is the local conjugation identity `pow_sub_one_conj` (`A ∘ C = C ∘ B` gives
  `(A − 1)^m ∘ C = C ∘ (B − 1)^m`, by induction on `m`), in place of `pow_pOf_conj`.
* `le_mk'_affFitting_of_affIsUnipotentInvariant` does not use `[FiniteDimensional k V]` and is
  stated without it (`omit … in`; strictly more general, every call site unaffected).
* `V` acts on itself (the affine space is the vector space): the printed `ℝⁿ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. DEC-123 (DEC-121's
FGH route, `docs/CARRIERE-DALBO-SURVEY.md` §2.1 P1, in affine generality).
-/

namespace Causal.Flat

open Module

universe u v

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- `U` is `N`-invariant and `N` acts unipotently on it: for `γ ∈ N`, `(L(γ) − id)^m` vanishes on
the direction of `U` for some `m` (the affine form of `IsUnipotentInvariant`). -/
def AffIsUnipotentInvariant (N : Subgroup (V ≃ᵃ[k] V)) (U : AffineSubspace k V) : Prop :=
  (∀ γ ∈ N, ∀ x : V, γ x ∈ U ↔ x ∈ U) ∧
    ∀ γ ∈ N, ∃ m : ℕ, ∀ w ∈ U.direction, (((γ.linear : V →ₗ[k] V) - 1) ^ m) w = 0

/-- `U` is a **maximal** `N`-invariant affine subspace on which `N` acts unipotently (the affine
form of `IsMaxUnipotent`). -/
def AffIsMaxUnipotent (N : Subgroup (V ≃ᵃ[k] V)) (U : AffineSubspace k V) : Prop :=
  AffIsUnipotentInvariant N U ∧ ∀ U', AffIsUnipotentInvariant N U' → U ≤ U' → U' = U

/-- **The Fitting submodule** `V₁ = E_u`: the joint generalized `1`-eigenspace of `L(N)`. -/
noncomputable def affFitting (N : Subgroup (V ≃ᵃ[k] V)) : Submodule k V :=
  ⨅ γ ∈ N, Module.End.maxGenEigenspace (γ.linear : V →ₗ[k] V) 1

/-- `γ x = L γ x + γ 0` (the affine decomposition, `AffineMap.decomp` read pointwise). -/
private theorem aff_apply_eq_linear_add (γ : V ≃ᵃ[k] V) (x : V) : γ x = γ.linear x + γ 0 := by
  have := γ.map_vadd 0 x
  rwa [vadd_eq_add, add_zero, vadd_eq_add] at this

/-- `γ x − γ y = L γ (x − y)`. -/
private theorem aff_sub_eq_linear (γ : V ≃ᵃ[k] V) (x y : V) : γ x - γ y = γ.linear (x - y) := by
  rw [aff_apply_eq_linear_add γ x, aff_apply_eq_linear_add γ y, map_sub]; abel

/-- `w ∈ maxGenEigenspace A 1 ↔ ∃ m, (A − 1)^m w = 0`. -/
private theorem mem_maxGenEigenspace_one_iff (A : V →ₗ[k] V) (w : V) :
    w ∈ Module.End.maxGenEigenspace A 1 ↔ ∃ m : ℕ, ((A - 1) ^ m) w = 0 := by
  rw [Module.End.mem_maxGenEigenspace, one_smul]

/-- **The local conjugation identity** (replaces `pow_pOf_conj`): if `A ∘ C = C ∘ B` then
`(A − 1)^m (C w) = C ((B − 1)^m w)`. -/
private theorem pow_sub_one_conj (A B C : V →ₗ[k] V) (h : ∀ x, A (C x) = C (B x)) (m : ℕ)
    (w : V) : ((A - 1) ^ m) (C w) = C (((B - 1) ^ m) w) := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
    congr 1
    simp [h, map_sub]

/-- **`V₁` is `L(N)`-invariant** (port of `fitting_linOf_mem`). -/
theorem affFitting_linear_mem {N : Subgroup (V ≃ᵃ[k] V)} {γ : V ≃ᵃ[k] V} (hγ : γ ∈ N) {w : V}
    (hw : w ∈ affFitting N) : γ.linear w ∈ affFitting N := by
  -- port of `fitting_linOf_mem`: for `η ∈ N`, `γ⁻¹ η γ ∈ N` and
  -- `(L η − 1)^m (L γ w) = L γ ((L (γ⁻¹ η γ) − 1)^m w)`, `L` = `AffineEquiv.linearHom`
  simp only [affFitting, Submodule.mem_iInf] at hw ⊢
  intro η hη
  obtain ⟨m, hm⟩ := (mem_maxGenEigenspace_one_iff _ _).1
    (hw _ (N.mul_mem (N.mul_mem (N.inv_mem hγ) hη) hγ))
  refine (mem_maxGenEigenspace_one_iff _ _).2 ⟨m, ?_⟩
  have hc : ∀ x, η.linear (γ.linear x) = γ.linear ((γ⁻¹ * η * γ).linear x) := by
    intro x
    have e : (γ⁻¹ * η * γ).linear = (γ.linear)⁻¹ * η.linear * γ.linear := by
      change AffineEquiv.linearHom (γ⁻¹ * η * γ) = _
      rw [map_mul, map_mul, map_inv]; rfl
    rw [e]
    simp [LinearEquiv.coe_inv]
  exact (pow_sub_one_conj (η.linear : V →ₗ[k] V) ((γ⁻¹ * η * γ).linear : V →ₗ[k] V)
    (γ.linear : V →ₗ[k] V) hc m w).trans (by rw [hm, map_zero])

/-- **`(V ⧸ V₁)^N = 0`** (FGH Lemma 1.4, affine form; port of `mem_fitting_of_forall`). -/
theorem mem_affFitting_of_forall {N : Subgroup (V ≃ᵃ[k] V)} {x : V}
    (hx : ∀ γ ∈ N, γ.linear x - x ∈ affFitting N) : x ∈ affFitting N := by
  -- port of `mem_fitting_of_forall`: `(L γ − 1) x ∈ V₁ ≤ maxGenEigenspace (L γ) 1` gives
  -- `(L γ − 1)^(m+1) x = 0`
  simp only [affFitting, Submodule.mem_iInf] at hx ⊢
  intro γ hγ
  obtain ⟨m, hm⟩ := (mem_maxGenEigenspace_one_iff _ _).1 (hx γ hγ γ hγ)
  refine (mem_maxGenEigenspace_one_iff _ _).2 ⟨m + 1, ?_⟩
  rw [pow_succ, Module.End.mul_apply]
  simpa using hm

variable [FiniteDimensional k V]

/-- **`x₀ + V₁` is unipotent-invariant** (port of `isUnipotentInvariant_mk'_fitting`). -/
theorem affIsUnipotentInvariant_mk'_affFitting {N : Subgroup (V ≃ᵃ[k] V)} {x₀ : V}
    (hx₀ : ∀ γ ∈ N, γ x₀ - x₀ ∈ affFitting N) :
    AffIsUnipotentInvariant N (AffineSubspace.mk' x₀ (affFitting N)) := by
  -- port of `isUnipotentInvariant_mk'_fitting`: `γ y − x₀ = (γ x₀ − x₀) + L γ (y − x₀)`,
  -- exponent `finrank k V` by `maxGenEigenspace_eq_genEigenspace_finrank`
  set V₁ := affFitting N with hV₁
  have fwd : ∀ γ ∈ N, ∀ y : V, y ∈ AffineSubspace.mk' x₀ V₁ → γ y ∈ AffineSubspace.mk' x₀ V₁ := by
    intro γ hγ y hy
    rw [AffineSubspace.mem_mk', vsub_eq_sub] at hy ⊢
    have e : γ y - x₀ = (γ x₀ - x₀) + γ.linear (y - x₀) := by
      rw [← aff_sub_eq_linear]; abel
    rw [e]
    exact V₁.add_mem (hx₀ γ hγ) (affFitting_linear_mem hγ hy)
  refine ⟨fun γ hγ y => ⟨fun h => ?_, fwd γ hγ y⟩, fun γ hγ => ⟨finrank k V, fun w hw => ?_⟩⟩
  · have := fwd γ⁻¹ (N.inv_mem hγ) _ h
    rwa [AffineEquiv.inv_def, AffineEquiv.symm_apply_apply] at this
  · rw [AffineSubspace.direction_mk'] at hw
    have hw' : w ∈ Module.End.maxGenEigenspace (γ.linear : V →ₗ[k] V) 1 :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hw γ) hγ
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat, LinearMap.mem_ker, one_smul] at hw'
    exact hw'

omit [FiniteDimensional k V] in
/-- **Every unipotent-invariant subspace lies in `x₀ + V₁`** (`⊥` included; port of
`le_mk'_fitting_of_isUnipotentInvariant`). -/
theorem le_mk'_affFitting_of_affIsUnipotentInvariant {N : Subgroup (V ≃ᵃ[k] V)} {x₀ : V}
    (hx₀ : ∀ γ ∈ N, γ x₀ - x₀ ∈ affFitting N) {U : AffineSubspace k V}
    (hU : AffIsUnipotentInvariant N U) : U ≤ AffineSubspace.mk' x₀ (affFitting N) := by
  -- port of `le_mk'_fitting_of_isUnipotentInvariant`: `U.direction ≤ V₁`, then
  -- `(L γ − 1)(x₀ − y) = (γ x₀ − x₀) − (γ y − y) ∈ V₁` and `mem_affFitting_of_forall`
  set V₁ := affFitting N with hV₁
  have hdir : U.direction ≤ V₁ := by
    intro w hw
    refine (Submodule.mem_iInf _).2 fun γ => (Submodule.mem_iInf _).2 fun hγ => ?_
    obtain ⟨m, hm⟩ := hU.2 γ hγ
    exact (mem_maxGenEigenspace_one_iff _ _).2 ⟨m, hm w hw⟩
  intro y hy
  rw [AffineSubspace.mem_mk', vsub_eq_sub, ← neg_mem_iff, neg_sub]
  refine mem_affFitting_of_forall fun γ hγ => ?_
  have hγy : γ y - y ∈ V₁ :=
    hdir (by simpa using AffineSubspace.vsub_mem_direction ((hU.1 γ hγ y).2 hy) hy)
  have e : γ.linear (x₀ - y) - (x₀ - y) = (γ x₀ - x₀) - (γ y - y) := by
    rw [← aff_sub_eq_linear]; abel
  rw [e]
  exact V₁.sub_mem (hx₀ γ hγ) hγy

/-- **The conclusion of Prop 5.2 for `N`**, from a point of `F` (port of
`maxUnipotent_of_mem_fitting`). -/
theorem affMaxUnipotent_of_mem_affFitting {N : Subgroup (V ≃ᵃ[k] V)} {x₀ : V}
    (hx₀ : ∀ γ ∈ N, γ x₀ - x₀ ∈ affFitting N) :
    ∃ U : AffineSubspace k V, (U : Set V).Nonempty ∧ AffIsMaxUnipotent N U ∧
      ∀ U', AffIsMaxUnipotent N U' → U' = U := by
  -- port of `maxUnipotent_of_mem_fitting`, verbatim from the two theorems above
  have hU := affIsUnipotentInvariant_mk'_affFitting hx₀
  have hgr := fun U' (hU' : AffIsUnipotentInvariant N U') =>
    le_mk'_affFitting_of_affIsUnipotentInvariant hx₀ hU'
  exact ⟨_, ⟨x₀, AffineSubspace.self_mem_mk' _ _⟩,
    ⟨hU, fun U' hU' hle => le_antisymm (hgr U' hU') hle⟩,
    fun U' hU' => (hU'.2 _ hU (hgr U' hU'.1)).symm⟩

end Causal.Flat
