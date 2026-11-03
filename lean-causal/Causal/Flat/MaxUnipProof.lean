import Causal.Flat.MaxUnipHirsch
import Causal.Flat.MaxUnipCocycle
import Causal.Flat.MaxUnipFitting

/-!
# `Causal.Flat.MaxUnipProof` — Carrière–Dal'bo's maximal unipotent subspace, proved for isometries

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5,
Proposition 5.2, `bthm:unip` — `GHFspace.tex:1710` (cited by Barbot as `cardal` Proposition
1.2.2), in the form of the named external `MaxUnipotentSubspace d` (`Flat/Externals`, DEC-36),
is **proved, for every `d`** (DEC-121): `maxUnipotentSubspace d`. **The label is not marked**
(kb/0011): the Lean statement is for nilpotent groups of *isometries* of `𝐌ⁿ`, narrower than
the paper's affine transformations of `ℝⁿ` (a candidate for the author's mark in a reading; the
ledger row is curated).

> Let $\Gamma$ be a nilpotent group of affine transformations of
> ${\mathbb R}^{n}$. Then, there exist a maximal $\Gamma$-invariant
> affine subspace ${\bf U}$
> of ${\mathbb R}^{n}$ such that the restriction of the action
> of $\Gamma$ to ${\bf U}$ is unipotent. Moreover, this maximal
> unipotent affine subspace is unique. (l.1712–1717)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

The route is Fried–Goldman–Hirsch's (`docs/CARRIERE-DALBO-SURVEY.md` §2.1 P1): with
`V₁ := ⨅ γ ∈ N, maxGenEigenspace (L γ) 1`, a point `x₀` with `γ x₀ − x₀ ∈ V₁` for all `γ ∈ N`
makes `x₀ + V₁` the greatest unipotent-invariant subspace (`Flat/MaxUnipFitting`, any `N`); the
facts on `V₁` and the reduction of `x₀`'s existence to `H¹(N; 𝐌ⁿ/V₁) = 0` are
`Flat/MaxUnipCocycle`; the vanishing for nilpotent `N` (`W^N = 0 ⇒ H¹ = 0`, Hirsch) is
`Flat/MaxUnipHirsch`, by centre induction. Nilpotency enters only there.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` nilpotent (l.1712) | ✓ carried: `Group.IsNilpotent N` |
| "group of affine transformations of $\mathbb R^n$" (l.1712) | ⚠ strengthened (as `MaxUnipotentSubspace`): `N ≤ Isom(𝐌ⁿ)` |
| "there exist a maximal … ${\bf U}$" (l.1713) | ✓ carried, with `U` **nonempty** (the empty subspace is always unipotent-invariant) |
| "this maximal unipotent affine subspace is unique" (l.1716–1717) | ✓ carried: every maximal `U'` equals `U` |

## SCOPE (disclosed)

* Nothing open: the three step modules and this one are sorry-free and axiom-free.
* No finite generation and no discreteness are used. The argument is affine-general except
  that `MaxUnipotentSubspace` (and `Flat/MaxUnipFitting`, `Flat/MaxUnipCocycle`) are stated for
  `isom d`; `Flat/MaxUnipHirsch` is for any group and field.
* The proof gives more than the statement: `x₀ + V₁` is the *greatest* unipotent-invariant
  subspace.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-121 (integrator of the FGH route: `Flat/MaxUnipHirsch`, `…Cocycle`, `…Fitting`).
-/

namespace Causal.Flat

variable {d : ℕ}

variable (d) in
/-- **Carrière–Dal'bo's maximal unipotent subspace, proved** (DEC-121, Fried–Goldman–Hirsch;
was the named external of DEC-36). -/
theorem maxUnipotentSubspace : MaxUnipotentSubspace d := by
  intro N hN
  haveI := hN
  obtain ⟨x₀, hx₀⟩ := exists_mem_fitting_of_h1 N
    (fun W _ _ _ ρ h0 c hc => exists_coboundary_of_isNilpotent ρ h0 c hc)
  exact maxUnipotent_of_mem_fitting (fun γ hγ v hv => fitting_linOf_mem hγ hv)
    (fun x hx => mem_fitting_of_forall hx) hx₀

end Causal.Flat
