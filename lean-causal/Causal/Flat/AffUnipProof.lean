import Causal.Flat.AffUnipCocycle
import Causal.Flat.Externals

/-!
# `Causal.Flat.AffUnipProof` — Carrière–Dal'bo's maximal unipotent subspace, for affine groups

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5,
Proposition 5.2 (cited by Barbot as `cardal` Proposition 1.2.2), in the PRINTED generality
(DEC-123). Label certified (line in `papers/barbot/legacy/labeled/GHFspace.tex`):

* **`bthm:unip`** — `GHFspace.tex:1710` (`affMaxUnipotent_real`: every nilpotent `N ≤ Aff(ℝⁿ)`,
  `ℝⁿ = Fin n → ℝ`; `affMaxUnipotent`: any field `k`, any finite-dimensional `V`)

For every nilpotent `N ≤ V ≃ᵃ[k] V` a nonempty maximal `N`-invariant affine subspace on which `N`
acts unipotently exists, and it is the only maximal one. DEC-121's `Isom(𝐌ⁿ)` form
`MaxUnipotentSubspace d` (`Flat/Externals`) is a corollary, `maxUnipotentSubspace_aff`, through
`maxUnipotentSubspace_of_affMaxUnipotent` and `isom d ≤ Minkowski d ≃ᵃ[ℝ] Minkowski d`.

> Let $\Gamma$ be a nilpotent group of affine transformations of
> ${\mathbb R}^{n}$. Then, there exist a maximal $\Gamma$-invariant
> affine subspace ${\bf U}$
> of ${\mathbb R}^{n}$ such that the restriction of the action
> of $\Gamma$ to ${\bf U}$ is unipotent. Moreover, this maximal
> unipotent affine subspace is unique. (l.1712–1717)

**Route** (`docs/CARRIERE-DALBO-SURVEY.md` §2.1 P1, Fried–Goldman–Hirsch, as DEC-121): with
`V₁ := affFitting N`, a point `x₀` of `F` makes `x₀ + V₁` the greatest unipotent-invariant
subspace (`Flat/AffUnipFitting`, any `N`); `F ≠ ∅` for nilpotent `N` is `Flat/AffUnipCocycle`
(Hirsch's `H¹ = 0`, `Flat/MaxUnipHirsch`, for any group and field).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` nilpotent (l.1712) | ✓ carried: `Group.IsNilpotent N` |
| "group of affine transformations of $\mathbb R^n$" (l.1712) | ✓ carried (`affMaxUnipotent_real`, `Fin n → ℝ`); ⚠ weakened in `affMaxUnipotent`: any field, any finite-dimensional `V` |
| "there exist a maximal … ${\bf U}$" (l.1713) | ✓ carried, with `U` **nonempty** (the empty subspace is always unipotent-invariant) |
| "this maximal unipotent affine subspace is unique" (l.1716–1717) | ✓ carried: every maximal `U'` equals `U` |

## SCOPE (disclosed)

* Sorry-free, axiom-clean (`#print axioms affMaxUnipotent`, `affMaxUnipotent_real`,
  `maxUnipotentSubspace_aff`: `[propext, Classical.choice, Quot.sound]`); the step modules
  `Flat/AffUnipFitting`, `Flat/AffUnipCocycle` are sorry-free (DEC-123 provers, 2026-11-08).
* "A nilpotent group of affine transformations" is read as a nilpotent subgroup `N` of the affine
  group: an abstract group acting through a homomorphism has the same invariant subspaces and the
  same linear parts as its image, which is nilpotent.
* "Unipotent" is read per element (`∃ m, (L γ − 1)^m = 0` on the direction), as in DEC-121's
  `IsUnipotentInvariant`; the proof gives the uniform exponent `finrank k V`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-123 (generalizing DEC-121's `Flat/MaxUnipProof`).
-/

namespace Causal.Flat

open Module

universe u v

section Affine

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

variable (k V) in
/-- **Prop 5.2 as printed**, for nilpotent groups of affine transformations of `V`: a nonempty
maximal invariant unipotent affine subspace exists, and it is the only maximal one. -/
def AffMaxUnipotentSubspace : Prop :=
  ∀ N : Subgroup (V ≃ᵃ[k] V), Group.IsNilpotent N →
    ∃ U : AffineSubspace k V, (U : Set V).Nonempty ∧ AffIsMaxUnipotent N U ∧
      ∀ U', AffIsMaxUnipotent N U' → U' = U

/-- **Carrière–Dal'bo's maximal unipotent subspace** (`bthm:unip`, Fried–Goldman–Hirsch), for
any field and any finite-dimensional `V`. -/
theorem affMaxUnipotent [FiniteDimensional k V] : AffMaxUnipotentSubspace k V := by
  intro N hN
  haveI := hN
  obtain ⟨x₀, hx₀⟩ := exists_mem_affFitting_of_isNilpotent N
  exact affMaxUnipotent_of_mem_affFitting hx₀

/-- **`bthm:unip` on `ℝⁿ`**, the printed form. -/
theorem affMaxUnipotent_real (n : ℕ) : AffMaxUnipotentSubspace ℝ (Fin n → ℝ) :=
  affMaxUnipotent

end Affine

/-! ### The `Isom(𝐌ⁿ)` form (DEC-121) as a corollary -/

variable {d : ℕ}

/-- `IsUnipotentInvariant` is `AffIsUnipotentInvariant` of the image of `N` in the affine group. -/
theorem isUnipotentInvariant_iff_aff {N : Subgroup (isom d)} {U : AffineSubspace ℝ (Minkowski d)} :
    IsUnipotentInvariant N U ↔ AffIsUnipotentInvariant (N.map (isom d).subtype) U := by
  simp only [IsUnipotentInvariant, AffIsUnipotentInvariant, Subgroup.mem_map,
    Subgroup.coe_subtype, forall_exists_index, and_imp]
  refine and_congr ⟨fun h _ γ hγ e x => e ▸ h γ hγ x, fun h γ hγ x => h γ γ hγ rfl x⟩
    ⟨fun h _ γ hγ e => e ▸ h γ hγ, fun h γ hγ => h γ γ hγ rfl⟩

/-- `IsMaxUnipotent` is `AffIsMaxUnipotent` of the image of `N` in the affine group. -/
theorem isMaxUnipotent_iff_aff {N : Subgroup (isom d)} {U : AffineSubspace ℝ (Minkowski d)} :
    IsMaxUnipotent N U ↔ AffIsMaxUnipotent (N.map (isom d).subtype) U := by
  simp only [IsMaxUnipotent, AffIsMaxUnipotent, isUnipotentInvariant_iff_aff]

/-- **DEC-121's `Isom(𝐌ⁿ)` form from the affine one**: `isom d` is a subgroup of
`Minkowski d ≃ᵃ[ℝ] Minkowski d`, and nilpotency passes to the image. -/
theorem maxUnipotentSubspace_of_affMaxUnipotent (h : AffMaxUnipotentSubspace ℝ (Minkowski d)) :
    MaxUnipotentSubspace d := by
  intro N hN
  have hN' : Group.IsNilpotent (N.map (isom d).subtype) :=
    (Group.isNilpotent_congr (N.equivMapOfInjective _ Subtype.val_injective)).1 hN
  obtain ⟨U, hne, hU, huniq⟩ := h _ hN'
  exact ⟨U, hne, isMaxUnipotent_iff_aff.2 hU,
    fun U' hU' => huniq U' (isMaxUnipotent_iff_aff.1 hU')⟩

variable (d) in
/-- **`MaxUnipotentSubspace d` re-derived from the printed form** (DEC-123); the DEC-121 proof
`maxUnipotentSubspace` (`Flat/MaxUnipProof`) is untouched. -/
theorem maxUnipotentSubspace_aff : MaxUnipotentSubspace d :=
  maxUnipotentSubspace_of_affMaxUnipotent affMaxUnipotent

end Causal.Flat
