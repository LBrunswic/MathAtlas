import Causal.Flat.Externals

/-!
# `Causal.Flat.MaxUnipFitting` — the coset `x₀ + V₁` is the greatest unipotent-invariant subspace

Step module of Prop 5.2 (`bthm:unip`, DEC-121, route P0 of `docs/CARRIERE-DALBO-SURVEY.md`
§2.1, the group-agnostic half of P1). **No label is marked.** For any subgroup `N ≤ Isom(𝐌ⁿ)`
(no nilpotency) let `V₁ := ⨅ γ ∈ N, maxGenEigenspace (L γ) 1`. Given the two facts on `V₁`
proved in `Flat/MaxUnipCocycle` (taken here as hypotheses `hinv`, `hfix`, so that the two step
modules are independent) and a point `x₀` of `F := {x | ∀ γ ∈ N, γ x − x ∈ V₁}`:

* `isUnipotentInvariant_mk'_fitting` — `x₀ + V₁` is `N`-invariant, and `N` is unipotent on `V₁`
  with the uniform exponent `m = finrank` (`maxGenEigenspace_eq_genEigenspace_finrank`).
* `le_mk'_fitting_of_isUnipotentInvariant` — **every** unipotent-invariant `U` (`⊥` included)
  lies in `x₀ + V₁`: `dir U ≤ V₁`, so `U ⊆ F`, and `F` is a single coset of `V₁` by `hfix`
  (`(L γ − 1)(x₀ − y) = (γ x₀ − x₀) − (γ y − y) ∈ V₁`). FGH Lemma 1.4, affine form.
* `maxUnipotent_of_mem_fitting` — hence `x₀ + V₁` is nonempty, maximal, and the only maximal one
  (the conclusion of `MaxUnipotentSubspace` for this `N`).

> […] there is a unique maximal submodule $E_u \subset E$ upon which $G$ acts unipotently.
> (Fried–Goldman–Hirsch 1981, §1, as read for the survey)

> Let $\Gamma$ be a nilpotent group of affine transformations of ${\mathbb R}^{n}$. Then, there
> exist a maximal $\Gamma$-invariant affine subspace ${\bf U}$ of ${\mathbb R}^{n}$ such that the
> restriction of the action of $\Gamma$ to ${\bf U}$ is unipotent. Moreover, this maximal
> unipotent affine subspace is unique. (`GHFspace.tex` l.1712–1717, the statement this serves)

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| 5.2: `Γ` nilpotent | ⚠ weakened: any `N`; nilpotency is spent only on `F ≠ ∅` (`hx₀`, from `Flat/MaxUnipCocycle` + `Flat/MaxUnipHirsch`) |
| 5.2: "maximal", "unique" | ✓ carried, as `IsMaxUnipotent` and uniqueness among maximal ones (in fact `x₀ + V₁` is greatest) |

## SCOPE (disclosed)
* `hinv`, `hfix` are hypotheses here and theorems of `Flat/MaxUnipCocycle`
  (`fitting_linOf_mem`, `mem_fitting_of_forall`); the glue `Flat/MaxUnipProof` discharges them.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. DEC-121.
-/

namespace Causal.Flat

open Module

variable {d : ℕ}

/-- `pOf A = A − 1 • 1`, the form in which mathlib's generalized eigenspaces are stated. -/
theorem pOf_eq_sub_smul_one (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    pOf A = (A : Module.End ℝ (Minkowski d)) - (1 : ℝ) • (1 : Module.End ℝ (Minkowski d)) := by
  rw [one_smul]; rfl

/-- **`x₀ + V₁` is unipotent-invariant.** -/
theorem isUnipotentInvariant_mk'_fitting {N : Subgroup (isom d)} {x₀ : Minkowski d}
    (hinv : ∀ γ ∈ N, ∀ v ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1,
      linOf γ v ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1)
    (hx₀ : ∀ γ ∈ N,
      γ • x₀ - x₀ ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1) :
    IsUnipotentInvariant N
      (AffineSubspace.mk' x₀ (⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1)) := by
  set V₁ := ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1 with hV₁
  have fwd : ∀ γ ∈ N, ∀ y : Minkowski d, y ∈ AffineSubspace.mk' x₀ V₁ →
      γ • y ∈ AffineSubspace.mk' x₀ V₁ := by
    intro γ hγ y hy
    rw [AffineSubspace.mem_mk', vsub_eq_sub] at hy ⊢
    have e : γ • y - x₀ = (γ • x₀ - x₀) + linOf γ (y - x₀) := by
      rw [smul_eq_lin_add, smul_eq_lin_add, map_sub]; abel
    rw [e]
    exact V₁.add_mem (hx₀ γ hγ) (hinv γ hγ _ hy)
  refine ⟨fun γ hγ y => ⟨fun h => ?_, fwd γ hγ y⟩, fun γ hγ => ⟨finrank ℝ (Minkowski d),
    fun w hw => ?_⟩⟩
  · have := fwd γ⁻¹ (N.inv_mem hγ) _ h
    rwa [inv_smul_smul] at this
  · rw [AffineSubspace.direction_mk'] at hw
    have hw' : w ∈ Module.End.maxGenEigenspace (linOf γ).toLinearMap 1 :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hw γ) hγ
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hw'
    rwa [pOf_eq_sub_smul_one]

/-- **Every unipotent-invariant subspace lies in `x₀ + V₁`** (`⊥` included). -/
theorem le_mk'_fitting_of_isUnipotentInvariant {N : Subgroup (isom d)} {x₀ : Minkowski d}
    (hfix : ∀ x : Minkowski d, (∀ γ ∈ N,
      linOf γ x - x ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1) →
      x ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1)
    (hx₀ : ∀ γ ∈ N,
      γ • x₀ - x₀ ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1)
    {U : AffineSubspace ℝ (Minkowski d)} (hU : IsUnipotentInvariant N U) :
    U ≤ AffineSubspace.mk' x₀ (⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1) := by
  set V₁ := ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1 with hV₁
  have hdir : U.direction ≤ V₁ := by
    intro w hw
    refine (Submodule.mem_iInf _).2 fun γ => (Submodule.mem_iInf _).2 fun hγ => ?_
    obtain ⟨m, hm⟩ := hU.2 γ hγ
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨m, by rw [← pOf_eq_sub_smul_one]; exact hm w hw⟩
  intro y hy
  rw [AffineSubspace.mem_mk', vsub_eq_sub, ← neg_mem_iff, neg_sub]
  refine hfix _ fun γ hγ => ?_
  have hγy : γ • y - y ∈ V₁ :=
    hdir (by simpa using AffineSubspace.vsub_mem_direction ((hU.1 γ hγ y).2 hy) hy)
  have e : linOf γ (x₀ - y) - (x₀ - y) = (γ • x₀ - x₀) - (γ • y - y) := by
    rw [smul_eq_lin_add, smul_eq_lin_add, map_sub]; abel
  rw [e]
  exact V₁.sub_mem (hx₀ γ hγ) hγy

/-- **The conclusion of `MaxUnipotentSubspace` for `N`**, from a point of `F`. -/
theorem maxUnipotent_of_mem_fitting {N : Subgroup (isom d)} {x₀ : Minkowski d}
    (hinv : ∀ γ ∈ N, ∀ v ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1,
      linOf γ v ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1)
    (hfix : ∀ x : Minkowski d, (∀ γ ∈ N,
      linOf γ x - x ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1) →
      x ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1)
    (hx₀ : ∀ γ ∈ N,
      γ • x₀ - x₀ ∈ ⨅ η ∈ N, Module.End.maxGenEigenspace (linOf η).toLinearMap 1) :
    ∃ U : AffineSubspace ℝ (Minkowski d), (U : Set (Minkowski d)).Nonempty ∧ IsMaxUnipotent N U ∧
      ∀ U', IsMaxUnipotent N U' → U' = U := by
  have hU := isUnipotentInvariant_mk'_fitting hinv hx₀
  have hgr := fun U' (hU' : IsUnipotentInvariant N U') =>
    le_mk'_fitting_of_isUnipotentInvariant hfix hx₀ hU'
  exact ⟨_, ⟨x₀, AffineSubspace.self_mem_mk' _ _⟩,
    ⟨hU, fun U' hU' hle => le_antisymm (hgr U' hU') hle⟩,
    fun U' hU' => (hU'.2 _ hU (hgr U' hU'.1)).symm⟩

end Causal.Flat
