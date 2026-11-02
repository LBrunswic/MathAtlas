import Causal.Flat.Form
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# `Causal.Flat.Isometries` — Barbot §6, the classification of isometries of `𝐌ⁿ`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §6
"Classification of isometries" (`GHFspace.tex` l.1848–2017 of the labelled file; l.1824–1993 of
`legacy/orig`). §6 is prose with no environment, hence **no ledger label is certified here**; the
items are cited unmarked: [6.N] normal forms through `p = L(g) − id` (l.1851–1901), [6.U] unipotent
linear parts (l.1906–1969, with Rem 6.1), [6.P] parabolic linear parts (l.1971–2017). This module
is the vocabulary §7–§10 (`Flat/AchronalDomains`, …) run on.

> Let `g` be a isometry of `𝐌ⁿ`. We denote by `L(g)` its linear part, `p` the element `L(g)−id`
> of `SO₀(1,n−1)`, and `τ` the translation part: `g(x)=L(g)(x)+τ`. Observe that:
> `(∗) ⟨x | p(y)⟩ + ⟨p(x) | y⟩ + ⟨p(x) | p(y)⟩ = 0`. In particular, if we denote by `I` the image
> of `p`, the kernel of `p` is the orthogonal `I^⊥`. Moreover, `τ` is defined modulo `I`, since it
> can be modified through conjugacies by translations. (l.1851–1864)

> Up to conjugacy, every isometry is of the following form: Elliptic: `L(g)` preserves some
> euclidean norm on `𝐌ⁿ`. […] `I` is spacelike, except if `R` is the identity map. […]
> Hyperbolic: of the form [a boost]. […] Unipotent: `p` is nilpotent. […] Loxodromic: of the form
> `R∘A`, where `R` is elliptic, `A` hyperbolic, and `R∘A = A∘R`. […] Parabolic: of the form `R∘A`,
> where `R` is elliptic, `A` unipotent, and `R∘A = A∘R`. (l.1868–1899)

> Observe that a parabolic element is nontransverse if and only if it preserves every affine
> hyperplane with direction `J^⊥`. (l.2016–2017)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1` and his `SO₀(1, n−1)` is `lorentz d`.

* [6.N] `minkForm`, `minkOrth` (the `minkB`-orthogonal), `pOf` (`p`), `star_identity` (`(∗)`),
  `ker_pOf_eq_minkOrth` (`ker p = I^⊥`), `transPart` (`τ`), `transConj`,
  `exists_transConj_iff` (`τ` is defined modulo `I`, exactly), `exists_fixed_iff`.
* The classes `IsElliptic`, `IsHyperbolic`, `IsUnipotent`, `IsLoxodromic`, `IsParabolic`;
  `classes_conj_iff` (conjugation invariance); pairwise disjointness
  (`IsLoxodromic.not_isElliptic`, `IsParabolic.not_isElliptic`, `IsParabolic.not_isLoxodromic`);
  `isElliptic_iff_exists_fixed_timelike` (a fixed point in `𝐇ⁿ⁻¹`); `IsElliptic.range_spacelike`;
  `τ` fixed by `L(g)` up to conjugacy for elliptic, hyperbolic and loxodromic `g`.
  `lorentz_trichotomy`: every element of `SO₀(1, d)` is elliptic, loxodromic or parabolic,
  Brouwer-free (SCOPE).
* [6.U] `nullPart` (`J = I ∩ I^⊥`), `unipotent_frame`, `pOf_pOf_mem_nullPart` (`Im p² ⊂ J`),
  `minkOrth_nullPart_eq_sup` (`J^⊥ = I + I^⊥`), the cases `IsLinearCase`, `IsTangentCase`,
  `IsTransverseCase` and their normal forms; Rem 6.1 `not_isTangentCase_of_dim_three`;
  `nullPart_one` (`J = 0` for `p = 0`: the counterexample to l.1908 as written);
  `two_le_of_unipotent` (a nontrivial unipotent needs `n ≥ 3`).
* [6.P] `parabolic_R_fix_range` (`R = id` on `I`), `range_pOf_mul_parabolic`
  (`Im (R − id + p) = I ⊕ 𝓘`), `parabolic_exists_transConj_normal`, `parabolic_not_transverse_iff`.
* Non-vacuity: `isElliptic_one`; the boosts `stdBoost` (`stdBoost_mem_lorentz`,
  `stdBoost_isHyperbolic`, `stdBoost_isLoxodromic`, `d ≥ 1`) and the null rotations `stdNullRot`
  (`stdNullRot_mem_lorentz`, `stdNullRot_isParabolic`, `d ≥ 2`); the criterion `mem_lorentz_of`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `g ∈ Isom(𝐌ⁿ)`, `L(g) ∈ SO₀(1,n−1)` ([6.N]) | ⚠ weakened: `(∗)`, `ker p = I^⊥` and [6.U] use only `minkQ ∘ A = minkQ` |
| unipotent: `p` nilpotent ([6.U]) | ⚠ strengthened (strongest true form, DEC-27): plus `p ≠ 0`, which "`J` nontrivial" (l.1908) needs; counterexample `nullPart_one` (finding) |
| parabolic: `R` elliptic, `A` unipotent, commuting ([6.N], [6.P]) | ⚠ strengthened (reading): plus `U ≠ id` (SCOPE, question); factors in `SO₀` as Barbot's `R`, `A` are |
| parabolic §6.2: `R` non-trivial (l.1974) | ⚠ weakened: `R` any elliptic element, so `R = id` (pure unipotent) is covered |
| hyperbolic: the boost matrix | ⚠ strengthened (reading): plus rapidity `ζ ≠ 0` (SCOPE, question) |
| `L(g) ∈ SO₀(1,n−1)` for the trichotomy ("Up to conjugacy, every isometry is of the following form", l.1868) | ✓ carried: `A ∈ lorentz d`, every `d` (for `d ≤ 1` the parabolic alternative is empty) |

## SCOPE (disclosed)
* `lorentz_trichotomy` is proved without Brouwer, Perron–Frobenius or Krein–Rutman (absent from
  mathlib). The cone eigenvector comes from a variational argument
  (`lorentz.exists_null_eigen_or_fixed_timelike`): absent a null eigenvector,
  `x ↦ |x|² / ⟨A x | x⟩` attains its maximum on the compact section `{x₀ = 1}` of the future cone
  at a timelike `v`, whose first variation makes `span {v, A v}` invariant. The loxodromic factor
  is `boost` in the null frame of the two null eigenvectors (`isLoxodromic_of_null_eigen`); the
  parabolic factor comes from the Fitting decomposition `ker pᴺ ⊕ Im pᴺ` of `p = A − id`
  (mathlib `LinearMap.eventually_isCompl_ker_pow_range_pow`), whose summands are
  `minkB`-orthogonal (`isElliptic_or_isParabolic_of_null_fixed`). The decomposition `A = R ∘ U` is
  not shown unique.
* Readings: `ζ ≠ 0` in `IsHyperbolic`; `U ≠ id` in `IsParabolic` (else every elliptic element is
  parabolic); `τ`-cases relative to the unipotent factor `U`, the linear case being
  `τ ∈ Im (L(g) − id)`, which is Barbot's `τ ∈ I` after his normalisation `R τ = τ`
  (`parabolic_mem_range_iff`). `J` is defined from `U`, so for a parabolic `g` it depends on the
  chosen decomposition (uniqueness of the decomposition is not proved).
* Barbot finds `vₙ` `R`-invariant through an `R`-invariant euclidean orthogonal (l.1985–1989);
  `parabolic_exists_fixed_not_mem` argues by `(𝓘^⊥)^⊥ = 𝓘` instead. Barbot's `p̄ = 0` on `J^⊥/J`
  (l.1912–1916) is proved by a descent on `(∗)`, not through the quotient norm.
* Witnesses are given for every class in the dimensions where it is inhabited: elliptic always,
  hyperbolic and loxodromic for `d ≥ 1`, unipotent and parabolic for `d ≥ 2`; for `d ≤ 1` no
  nontrivial unipotent exists (`two_le_of_unipotent`). Their determinant is `1` because each is
  the square of a `minkQ`-preserving map (`det_eq_one_of_eq_sq`, from `det_sq_of_minkQ`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. WP-30d (wave 1b of the
Barbot campaign, DEC-34); `lorentz_trichotomy` closed by the WP-30d fixer pass (2026-10-31).
-/

namespace Causal.Flat

open Module Submodule

variable {d : ℕ}

/-! ### The form as a bilinear form -/

theorem minkB_add_left (u v w : Minkowski d) : minkB (u + v) w = minkB u w + minkB v w := by
  simp only [minkB, Prod.fst_add, Prod.snd_add, inner_add_left]; ring

theorem minkB_smul_left (c : ℝ) (v w : Minkowski d) : minkB (c • v) w = c * minkB v w := by
  simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_left]; ring

theorem minkB_add_right (u v w : Minkowski d) : minkB u (v + w) = minkB u v + minkB u w := by
  rw [minkB_comm, minkB_add_left, minkB_comm v, minkB_comm w]

theorem minkB_smul_right (c : ℝ) (v w : Minkowski d) : minkB v (c • w) = c * minkB v w := by
  rw [minkB_comm, minkB_smul_left, minkB_comm]

/-- `minkB` as a bilinear form, so that mathlib's orthogonal complements apply. -/
noncomputable def minkForm (d : ℕ) : LinearMap.BilinForm ℝ (Minkowski d) :=
  LinearMap.mk₂ ℝ minkB minkB_add_left minkB_smul_left minkB_add_right
    (fun c v w => minkB_smul_right c v w)

@[simp] theorem minkForm_apply (v w : Minkowski d) : minkForm d v w = minkB v w := rfl

@[simp] theorem minkB_neg_left (v w : Minkowski d) : minkB (-v) w = -minkB v w :=
  LinearMap.map_neg₂ (minkForm d) v w

@[simp] theorem minkB_neg_right (v w : Minkowski d) : minkB v (-w) = -minkB v w :=
  (minkForm d v).map_neg w

theorem minkB_sub_left (u v w : Minkowski d) : minkB (u - v) w = minkB u w - minkB v w :=
  LinearMap.map_sub₂ (minkForm d) u v w

theorem minkB_sub_right (u v w : Minkowski d) : minkB u (v - w) = minkB u v - minkB u w :=
  (minkForm d u).map_sub v w

@[simp] theorem minkB_zero_left (w : Minkowski d) : minkB 0 w = 0 :=
  LinearMap.map_zero₂ (minkForm d) w

@[simp] theorem minkB_zero_right (v : Minkowski d) : minkB v 0 = 0 := (minkForm d v).map_zero

theorem minkQ_add (v w : Minkowski d) : minkQ (v + w) = minkQ v + 2 * minkB v w + minkQ w := by
  rw [minkQ_eq_minkB, minkQ_eq_minkB, minkQ_eq_minkB, minkB_add_left, minkB_add_right,
    minkB_add_right, minkB_comm w v]; ring

/-- **`minkB` is nondegenerate**: a vector orthogonal to everything is `0`. -/
theorem eq_zero_of_forall_minkB {w : Minkowski d} (h : ∀ z, minkB z w = 0) : w = 0 := by
  have h1 := h ((1 : ℝ), 0)
  have h2 := h (0, w.2)
  simp only [minkB, one_mul, inner_zero_left, add_zero, zero_mul, neg_zero, zero_add,
    real_inner_self_eq_norm_sq] at h1 h2
  have h1' : w.1 = 0 := by linarith
  have h2' : w.2 = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  exact Prod.ext h1' h2'

theorem minkForm_isRefl : (minkForm d).IsRefl := fun v w h => by
  simpa [minkB_comm] using h

theorem minkForm_nondegenerate : (minkForm d).Nondegenerate :=
  ⟨fun v h => eq_zero_of_forall_minkB fun z => by rw [minkB_comm]; exact h z,
    fun w h => eq_zero_of_forall_minkB h⟩

theorem finrank_minkowski : finrank ℝ (Minkowski d) = d + 1 := by
  rw [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self, add_comm]

/-- **The `minkB`-orthogonal** `W^⊥` of a subspace (Barbot's `^⊥`, for the Lorentzian form). -/
noncomputable def minkOrth (W : Submodule ℝ (Minkowski d)) : Submodule ℝ (Minkowski d) :=
  (minkForm d).orthogonal W

theorem mem_minkOrth {W : Submodule ℝ (Minkowski d)} {x : Minkowski d} :
    x ∈ minkOrth W ↔ ∀ w ∈ W, minkB w x = 0 := Iff.rfl

theorem mem_minkOrth' {W : Submodule ℝ (Minkowski d)} {x : Minkowski d} :
    x ∈ minkOrth W ↔ ∀ w ∈ W, minkB x w = 0 := by
  rw [mem_minkOrth]; exact forall₂_congr fun w _ => by rw [minkB_comm]

theorem minkOrth_antitone {W W' : Submodule ℝ (Minkowski d)} (h : W ≤ W') :
    minkOrth W' ≤ minkOrth W :=
  LinearMap.BilinForm.orthogonal_le h

theorem minkOrth_minkOrth (W : Submodule ℝ (Minkowski d)) : minkOrth (minkOrth W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal minkForm_nondegenerate minkForm_isRefl W

theorem finrank_minkOrth (W : Submodule ℝ (Minkowski d)) :
    finrank ℝ (minkOrth W) = d + 1 - finrank ℝ W := by
  rw [minkOrth, LinearMap.BilinForm.finrank_orthogonal minkForm_nondegenerate, finrank_minkowski]

theorem mem_minkOrth_span_singleton {v x : Minkowski d} :
    x ∈ minkOrth (ℝ ∙ v) ↔ minkB v x = 0 := by
  rw [mem_minkOrth]
  refine ⟨fun h => h v (mem_span_singleton_self v), fun h w hw => ?_⟩
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hw
  rw [minkB_smul_left, h, mul_zero]

/-- A linear map preserving `minkQ` preserves `minkB` (polarisation). -/
theorem minkB_map_of_minkQ {A : Minkowski d →ₗ[ℝ] Minkowski d} (hA : ∀ v, minkQ (A v) = minkQ v)
    (v w : Minkowski d) : minkB (A v) (A w) = minkB v w := by
  have h := hA (v + w)
  rw [map_add, minkQ_add, minkQ_add, hA, hA] at h
  linarith

/-- **A null vector's orthogonal is spacelike, and degenerate exactly along it.** If `u ≠ 0` is
null and `minkB u w = 0`, then `minkQ w ≥ 0`, with equality only on the line `ℝ u`. -/
theorem minkQ_nonneg_of_null_orth {u w : Minkowski d} (hu : minkQ u = 0) (hu0 : u ≠ 0)
    (huw : minkB u w = 0) : 0 ≤ minkQ w ∧ (minkQ w = 0 → ∃ c : ℝ, w = c • u) := by
  have hu1 : u.1 ≠ 0 := fun h => hu0 (eq_zero_of_fst_eq_zero h hu.le)
  set c := w.1 / u.1
  set z := w - c • u
  have hz1 : z.1 = 0 := by
    simp only [z, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, c]; field_simp; ring
  have hzQ : minkQ z = minkQ w := by
    have : z = w + (-c) • u := by simp [z, sub_eq_add_neg, neg_smul]
    rw [this, minkQ_add, minkQ_smul, hu, minkB_smul_right, minkB_comm, huw]; ring
  have hnn : 0 ≤ minkQ z := minkQ_nonneg_of_fst_eq_zero hz1
  refine ⟨hzQ ▸ hnn, fun hw => ⟨c, ?_⟩⟩
  have : z = 0 := eq_zero_of_fst_eq_zero hz1 (by rw [hzQ, hw])
  exact sub_eq_zero.1 this

/-- **Two orthogonal null vectors are proportional** (a totally isotropic subspace of `𝐌ⁿ` has
dimension `≤ 1`). -/
theorem eq_smul_of_null_orth {u w : Minkowski d} (hu : minkQ u = 0) (hu0 : u ≠ 0)
    (hw : minkQ w = 0) (huw : minkB u w = 0) : ∃ c : ℝ, w = c • u :=
  (minkQ_nonneg_of_null_orth hu hu0 huw).2 hw

/-! ### [6.N] `p = L(g) − id`, the identity `(∗)`, `ker p = (Im p)^⊥`, the translation part -/

/-- Barbot's `p = L(g) − id` (l.1852), for a linear map `A` (in practice `A = L(g)`). -/
noncomputable def pOf (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Module.End ℝ (Minkowski d) :=
  (A : Minkowski d →ₗ[ℝ] Minkowski d) - LinearMap.id

@[simp] theorem pOf_apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    pOf A x = A x - x := rfl

theorem apply_eq_add_pOf (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    A x = x + pOf A x := by simp

section star

variable {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : ∀ v, minkQ (A v) = minkQ v)
include hA

theorem minkB_map (v w : Minkowski d) : minkB (A v) (A w) = minkB v w :=
  minkB_map_of_minkQ (A := (A : Minkowski d →ₗ[ℝ] Minkowski d)) hA v w

/-- **`(∗)`** (l.1857): `⟨x | p y⟩ + ⟨p x | y⟩ + ⟨p x | p y⟩ = 0`. -/
theorem star_identity (x y : Minkowski d) :
    minkB x (pOf A y) + minkB (pOf A x) y + minkB (pOf A x) (pOf A y) = 0 := by
  have h := minkB_map hA x y
  rw [apply_eq_add_pOf A x, apply_eq_add_pOf A y, minkB_add_left, minkB_add_right,
    minkB_add_right] at h
  linarith

/-- **`ker p = (Im p)^⊥`** (l.1860–1861). -/
theorem ker_pOf_eq_minkOrth : LinearMap.ker (pOf A) = minkOrth (LinearMap.range (pOf A)) := by
  ext x
  rw [LinearMap.mem_ker, mem_minkOrth]
  constructor
  · rintro hx _ ⟨y, rfl⟩
    have := star_identity hA y x
    rw [hx, minkB_zero_right, minkB_zero_right, add_zero, zero_add] at this
    exact this
  · intro hx
    refine eq_zero_of_forall_minkB fun z => ?_
    obtain ⟨y, rfl⟩ := A.surjective z
    have h := star_identity hA y x
    rw [hx _ ⟨y, rfl⟩, add_zero] at h
    rw [apply_eq_add_pOf, minkB_add_left]
    exact h

theorem mem_minkOrth_range_iff {x : Minkowski d} :
    x ∈ minkOrth (LinearMap.range (pOf A)) ↔ A x = x := by
  rw [← ker_pOf_eq_minkOrth hA, LinearMap.mem_ker, pOf_apply, sub_eq_zero]

end star

/-- Barbot's translation part `τ` (l.1853), read in the origin chart: `g x = L(g) x + τ`. -/
noncomputable def transPart (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) : Minkowski d := g 0

theorem apply_eq_linear_add_transPart (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) (x : Minkowski d) :
    g x = g.linear x + transPart g := by
  have := isom_sub g 0 x
  rw [sub_zero] at this
  rw [transPart, ← this]; abel

/-- Conjugation of `g` by the translation of vector `v`: `x ↦ g (x − v) + v`. -/
noncomputable def transConj (v : Minkowski d) (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    Minkowski d ≃ᵃ[ℝ] Minkowski d :=
  AffineEquiv.constVAdd ℝ (Minkowski d) v * g * (AffineEquiv.constVAdd ℝ (Minkowski d) v)⁻¹

theorem transConj_apply (v : Minkowski d) (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) (x : Minkowski d) :
    transConj v g x = v + g (-v + x) := rfl

theorem transConj_mem_isom {v : Minkowski d} {g : Minkowski d ≃ᵃ[ℝ] Minkowski d}
    (hg : g ∈ isom d) : transConj v g ∈ isom d :=
  (isom d).mul_mem ((isom d).mul_mem (constVAdd_mem_isom v) hg)
    ((isom d).inv_mem (constVAdd_mem_isom v))

@[simp] theorem linear_transConj (v : Minkowski d) (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    (transConj v g).linear = g.linear := by
  rw [transConj, ← AffineEquiv.linearHom_apply, map_mul, map_mul, map_inv]
  have h1 : AffineEquiv.linearHom (AffineEquiv.constVAdd ℝ (Minkowski d) v) = 1 := rfl
  rw [h1, inv_one, one_mul, mul_one, AffineEquiv.linearHom_apply]

/-- **Conjugating by a translation moves `τ` by an element of `Im p`** (l.1863–1864). -/
theorem transPart_transConj (v : Minkowski d) (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    transPart (transConj v g) = transPart g - pOf g.linear v := by
  rw [transPart, transConj_apply, add_zero, apply_eq_linear_add_transPart, map_neg, pOf_apply]
  abel

/-- **`τ` is defined modulo `I = Im p`** (l.1863): the translation parts of the conjugates of `g`
by translations are exactly `τ + I`. -/
theorem exists_transConj_iff (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) (τ' : Minkowski d) :
    (∃ v, transPart (transConj v g) = τ') ↔ transPart g - τ' ∈ LinearMap.range (pOf g.linear) := by
  simp only [transPart_transConj]
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨v, by abel⟩
  · rintro ⟨v, hv⟩; exact ⟨v, by rw [hv]; abel⟩

/-- `g` has a fixed point iff its translation part lies in `Im p`. -/
theorem exists_fixed_iff (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    (∃ x, g x = x) ↔ transPart g ∈ LinearMap.range (pOf g.linear) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨-x, ?_⟩
    rw [apply_eq_linear_add_transPart] at hx
    have h : transPart g = x - g.linear x := eq_sub_of_add_eq' hx
    rw [h, pOf_apply, map_neg]; abel
  · rintro ⟨v, hv⟩
    refine ⟨-v, ?_⟩
    rw [apply_eq_linear_add_transPart, ← hv, pOf_apply, map_neg]; abel

/-- If `τ ∈ Im p ⊔ W`, a conjugate of `g` by a translation has its translation part in `W`. -/
theorem exists_transConj_mem_of_mem_sup (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)
    {W : Submodule ℝ (Minkowski d)} (h : transPart g ∈ LinearMap.range (pOf g.linear) ⊔ W) :
    ∃ v, transPart (transConj v g) ∈ W := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.1 h
  obtain ⟨v, hv⟩ := (exists_transConj_iff g b).2 (by rw [← hab, add_sub_cancel_right]; exact ha)
  exact ⟨v, hv ▸ hb⟩

/-! ### The classes (l.1868–1901) -/

/-- **Elliptic** (l.1872): `A` preserves some euclidean norm on `𝐌ⁿ` — a symmetric, positive
definite bilinear form `E` with `E (A v) (A w) = E v w`. -/
def IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Prop :=
  ∃ E : LinearMap.BilinForm ℝ (Minkowski d), (∀ v w, E v w = E w v) ∧
    (∀ v, v ≠ 0 → 0 < E v v) ∧ ∀ v w, E (A v) (A w) = E v w

/-- **Hyperbolic** (l.1880–1887): in some `minkB`-orthonormal pair `e₀` (timelike), `e₁`
(spacelike), `A` is the boost of rapidity `ζ` on `span {e₀, e₁}` and the identity on its
orthogonal. `ζ ≠ 0` is a reading (Barbot's matrix allows `ζ = 0`, the identity; SCOPE). -/
def IsHyperbolic (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Prop :=
  ∃ (e₀ e₁ : Minkowski d) (ζ : ℝ), ζ ≠ 0 ∧ minkQ e₀ = -1 ∧ minkQ e₁ = 1 ∧ minkB e₀ e₁ = 0 ∧
    A e₀ = Real.cosh ζ • e₀ + Real.sinh ζ • e₁ ∧ A e₁ = Real.sinh ζ • e₀ + Real.cosh ζ • e₁ ∧
    ∀ w, minkB e₀ w = 0 → minkB e₁ w = 0 → A w = w

/-- **Unipotent** (l.1890): `p = A − id` is nilpotent. As written this includes `A = id`
(`isUnipotent_one`), for which `J = 0` (`nullPart_one`). -/
def IsUnipotent (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Prop := IsNilpotent (pOf A)

/-- **Loxodromic** (l.1894–1896): `A = R ∘ H` with `R` elliptic, `H` hyperbolic, commuting,
both in `SO₀(1, d)`. -/
def IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Prop :=
  ∃ R H : Minkowski d ≃ₗ[ℝ] Minkowski d, R ∈ lorentz d ∧ H ∈ lorentz d ∧ IsElliptic R ∧
    IsHyperbolic H ∧ A = R * H ∧ R * H = H * R

/-- **Parabolic** (l.1898–1899, l.1973–1974): `A = R ∘ U` with `R` elliptic, `U` unipotent and
**nontrivial**, commuting, both in `SO₀(1, d)`. `U ≠ id` is a reading (SCOPE): without it every
elliptic element is parabolic. `R = id` is allowed, so a nontrivial unipotent is parabolic. -/
def IsParabolic (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Prop :=
  ∃ R U : Minkowski d ≃ₗ[ℝ] Minkowski d, R ∈ lorentz d ∧ U ∈ lorentz d ∧ IsElliptic R ∧
    IsUnipotent U ∧ U ≠ 1 ∧ A = R * U ∧ R * U = U * R

theorem pOf_one : pOf (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) = 0 :=
  LinearMap.ext fun x => by simp

theorem pOf_ne_zero {U : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : U ≠ 1) : pOf U ≠ 0 := by
  intro h0; apply h; refine LinearEquiv.ext fun x => ?_
  have := LinearMap.congr_fun h0 x
  simp only [pOf_apply, LinearMap.zero_apply, sub_eq_zero] at this
  simpa using this

theorem isUnipotent_one : IsUnipotent (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) := ⟨1, by
  rw [pow_one, pOf_one]⟩

/-! ### The elliptic case (l.1872–1878) -/

/-- **The core of the elliptic case**: if `A` preserves a positive definite form, then
`Im p ∩ ker p = 0` (if `p y = x` and `p x = 0`, then `Aᵏ y = y + k x` would be unbounded). -/
theorem range_inf_ker_eq_bot_of_preserves {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (E : LinearMap.BilinForm ℝ (Minkowski d)) (hEpos : ∀ v, v ≠ 0 → 0 < E v v)
    (hE : ∀ v w, E (A v) (A w) = E v w) :
    LinearMap.range (pOf A) ⊓ LinearMap.ker (pOf A) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨y, rfl⟩, hx⟩
  rw [mem_bot]
  by_contra hne
  have hAx : A (pOf A y) = pOf A y := by
    have hx' : pOf A (pOf A y) = 0 := hx
    rw [pOf_apply, sub_eq_zero] at hx'; exact hx'
  have h1 : A y = y + pOf A y := apply_eq_add_pOf A y
  have h2 : A (A y) = y + pOf A y + pOf A y := by rw [h1, map_add, hAx, ← h1]
  have e1 := hE y y
  have e2 := hE (A y) (A y)
  rw [h2, h1] at e2
  rw [h1] at e1
  have hpos := hEpos _ hne
  simp only [map_add, LinearMap.add_apply] at e1 e2
  linarith

theorem IsElliptic.range_inf_ker {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsElliptic A) :
    LinearMap.range (pOf A) ⊓ LinearMap.ker (pOf A) = ⊥ := by
  obtain ⟨E, -, hpos, hE⟩ := h
  exact range_inf_ker_eq_bot_of_preserves E hpos hE

/-- **`𝐌ⁿ = I ⊕ I^⊥` in the elliptic case** (l.1873). -/
theorem IsElliptic.isCompl {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : ∀ v, minkQ (A v) = minkQ v) (h : IsElliptic A) :
    IsCompl (LinearMap.range (pOf A)) (minkOrth (LinearMap.range (pOf A))) := by
  rw [minkOrth, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint minkForm_isRefl,
    disjoint_iff, ← minkOrth, ← ker_pOf_eq_minkOrth hA]
  exact h.range_inf_ker

/-- **Elliptic: `τ` can be selected in `I^⊥`, i.e. fixed by `L(g)`** (l.1873–1874). -/
theorem IsElliptic.exists_transConj_fixed {g : Minkowski d ≃ᵃ[ℝ] Minkowski d}
    (hg : g ∈ isom d) (h : IsElliptic g.linear) :
    ∃ v, g.linear (transPart (transConj v g)) = transPart (transConj v g) := by
  have hA : ∀ v, minkQ (g.linear v) = minkQ v := hg.1
  have hc := h.isCompl hA
  obtain ⟨v, hv⟩ := exists_transConj_mem_of_mem_sup g
    (W := minkOrth (LinearMap.range (pOf g.linear))) (by rw [hc.sup_eq_top]; exact mem_top)
  exact ⟨v, (mem_minkOrth_range_iff hA).1 hv⟩

/-! ### [6.U] Unipotent linear parts (l.1906–1969) -/

/-- Barbot's **`J = I ∩ I^⊥`** (l.1908), for `I = Im p`. -/
noncomputable def nullPart (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Submodule ℝ (Minkowski d) :=
  LinearMap.range (pOf A) ⊓ minkOrth (LinearMap.range (pOf A))

theorem minkB_eq_zero_of_mem_nullPart {A : Minkowski d ≃ₗ[ℝ] Minkowski d} {x y : Minkowski d}
    (hx : x ∈ nullPart A) (hy : y ∈ nullPart A) : minkB x y = 0 :=
  hy.2 x hx.1

theorem nullPart_le_range (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    nullPart A ≤ LinearMap.range (pOf A) := inf_le_left

/-- **`J = 0` for `p = 0`** — the counterexample (DEC-27) to "`J` is nontrivial" (l.1908) for a
unipotent `L(g)` as Barbot writes it: `L(g) = id` is unipotent (`isUnipotent_one`), and its `J`
is `0`. Hence the hypothesis `p ≠ 0` of the [6.U] theorems. -/
theorem nullPart_one : nullPart (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) = ⊥ :=
  eq_bot_iff.2 ((nullPart_le_range 1).trans (by rw [pOf_one, LinearMap.range_zero]))

theorem range_le_minkOrth_nullPart (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    LinearMap.range (pOf A) ≤ minkOrth (nullPart A) := fun x hx j hj => by
  show minkB j x = 0
  rw [minkB_comm]; exact hj.2 x hx

theorem minkOrth_range_le_minkOrth_nullPart (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    minkOrth (LinearMap.range (pOf A)) ≤ minkOrth (nullPart A) :=
  minkOrth_antitone (nullPart_le_range A)

theorem pOf_apply_mem_minkOrth_nullPart (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    pOf A x ∈ minkOrth (nullPart A) := range_le_minkOrth_nullPart A ⟨x, rfl⟩

section unipotent

variable {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : ∀ v, minkQ (A v) = minkQ v)
include hA

theorem nullPart_le_ker : nullPart A ≤ LinearMap.ker (pOf A) := by
  rw [ker_pOf_eq_minkOrth hA]; exact inf_le_right

theorem pOf_eq_zero_of_mem_nullPart {x : Minkowski d} (hx : x ∈ nullPart A) : pOf A x = 0 :=
  nullPart_le_ker hA hx

/-- **`J ≠ 0` when `p` is nilpotent and nonzero** (l.1908): the last nonzero power of `p` has
its image in `I ∩ ker p = I ∩ I^⊥`. -/
theorem exists_mem_nullPart_ne_zero (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) :
    ∃ v ∈ nullPart A, v ≠ 0 := by
  classical
  obtain ⟨n, hn⟩ := hn
  have hex : ∃ m, pOf A ^ (m + 1) = 0 := ⟨n, by rw [pow_succ, hn, zero_mul]⟩
  set m := Nat.find hex with hmdef
  have hm : pOf A ^ (m + 1) = 0 := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; apply hp; rw [h, zero_add, pow_one] at hm; exact hm
    · exact h
  have hm' : pOf A ^ m ≠ 0 := by
    intro h0
    have := Nat.find_min hex (show m - 1 < m by omega)
    apply this; rw [show m - 1 + 1 = m by omega]; exact h0
  obtain ⟨x, hx⟩ : ∃ x, (pOf A ^ m) x ≠ 0 := by
    by_contra h; push Not at h; exact hm' (LinearMap.ext h)
  refine ⟨(pOf A ^ m) x, ⟨⟨(pOf A ^ (m - 1)) x, ?_⟩, ?_⟩, hx⟩
  · rw [← Module.End.mul_apply, ← pow_succ', show m - 1 + 1 = m by omega]
  · show (pOf A ^ m) x ∈ minkOrth (LinearMap.range (pOf A))
    rw [← ker_pOf_eq_minkOrth hA, LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', hm]
    rfl

omit hA in
/-- **`J` is isotropic, hence a line** (l.1908–1910): any nonzero `v₀ ∈ J` spans it. -/
theorem nullPart_eq_span_of_mem {v₀ : Minkowski d} (hv : v₀ ∈ nullPart A) (hv0 : v₀ ≠ 0) :
    nullPart A = ℝ ∙ v₀ := by
  have hq0 : minkQ v₀ = 0 := by rw [minkQ_eq_minkB]; exact minkB_eq_zero_of_mem_nullPart hv hv
  apply le_antisymm
  · intro w hw
    have hqw : minkQ w = 0 := by rw [minkQ_eq_minkB]; exact minkB_eq_zero_of_mem_nullPart hw hw
    obtain ⟨c, rfl⟩ := eq_smul_of_null_orth hq0 hv0 hqw (minkB_eq_zero_of_mem_nullPart hv hw)
    exact smul_mem _ _ (mem_span_singleton_self _)
  · rw [span_singleton_le_iff_mem]; exact hv

omit hA in
theorem minkQ_eq_zero_of_mem_nullPart {v : Minkowski d} (hv : v ∈ nullPart A) : minkQ v = 0 := by
  rw [minkQ_eq_minkB]; exact minkB_eq_zero_of_mem_nullPart hv hv

/-- One step of the descent: on `J^⊥`, if `p (p z) ∈ J` then `p z ∈ J`. -/
theorem pOf_mem_nullPart_of_pOf_pOf {v₀ : Minkowski d} (hv : v₀ ∈ nullPart A) (hv0 : v₀ ≠ 0)
    {z : Minkowski d} (hz : z ∈ minkOrth (nullPart A)) (h2 : pOf A (pOf A z) ∈ nullPart A) :
    pOf A z ∈ nullPart A := by
  have hpz := pOf_apply_mem_minkOrth_nullPart A z
  have hs := star_identity hA z (pOf A z)
  have e1 : minkB z (pOf A (pOf A z)) = 0 := by rw [minkB_comm]; exact hz _ h2
  have e2 : minkB (pOf A z) (pOf A (pOf A z)) = 0 := by rw [minkB_comm]; exact hpz _ h2
  rw [e1, e2, zero_add, add_zero] at hs
  have hq : minkQ (pOf A z) = 0 := by rw [minkQ_eq_minkB]; exact hs
  obtain ⟨c, hc⟩ := eq_smul_of_null_orth (minkQ_eq_zero_of_mem_nullPart hv) hv0 hq (hpz _ hv)
  rw [hc]; exact smul_mem _ _ hv

/-- **`p̄ = 0` on `J^⊥/J`** (l.1912–1916): `p` maps `J^⊥` into `J`. Barbot argues through the
euclidean norm `J^⊥/J` inherits; here the descent `pᵏ⁺¹ z ∈ J ⇒ p z ∈ J` uses `(∗)` directly. -/
theorem pOf_mem_nullPart (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) {z : Minkowski d}
    (hz : z ∈ minkOrth (nullPart A)) : pOf A z ∈ nullPart A := by
  obtain ⟨v₀, hv, hv0⟩ := exists_mem_nullPart_ne_zero hA hn hp
  obtain ⟨n, hn⟩ := hn
  have key : ∀ k : ℕ, ∀ z ∈ minkOrth (nullPart A), (pOf A ^ (k + 1)) z ∈ nullPart A →
      pOf A z ∈ nullPart A := by
    intro k
    induction k with
    | zero => intro z _ h; simpa using h
    | succ k ih =>
      intro z hz h
      rw [pow_succ, Module.End.mul_apply] at h
      exact pOf_mem_nullPart_of_pOf_pOf hA hv hv0 hz
        (ih _ (pOf_apply_mem_minkOrth_nullPart A z) h)
  refine key n z hz ?_
  rw [pow_succ, Module.End.mul_apply, hn, LinearMap.zero_apply]; exact zero_mem _

/-- **`Im p² ⊂ J`** (l.1916–1917). -/
theorem pOf_pOf_mem_nullPart (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) (x : Minkowski d) :
    pOf A (pOf A x) ∈ nullPart A :=
  pOf_mem_nullPart hA hn hp (pOf_apply_mem_minkOrth_nullPart A x)

/-- Consequently `p³ = 0`. -/
theorem pOf_pOf_pOf (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) (x : Minkowski d) :
    pOf A (pOf A (pOf A x)) = 0 :=
  pOf_eq_zero_of_mem_nullPart hA (pOf_pOf_mem_nullPart hA hn hp x)

/-- **`v₁` with `p v₁ ∈ J` lies in `J^⊥`** (l.1920–1927): `0 = 2⟨v₁|p v₁⟩ + |p v₁|²`. -/
theorem mem_minkOrth_nullPart_of_pOf_mem {v₁ : Minkowski d} (h : pOf A v₁ ∈ nullPart A) :
    minkB v₁ (pOf A v₁) = 0 := by
  have hs := star_identity hA v₁ v₁
  rw [minkB_comm (pOf A v₁) v₁, minkB_eq_zero_of_mem_nullPart h h] at hs
  linarith

/-- **The unipotent frame** (l.1906–1952). For `p` nilpotent and nonzero there is `vₙ` such that,
with `v₁ = p vₙ` and `v₀ = p v₁`: `v₀` is null, nonzero and spans `J`; `v₁` is spacelike and
orthogonal to `v₀`; `⟨vₙ | v₀⟩ = −|v₁|² ≠ 0`; `p v₀ = 0`; and `I = span {v₀, v₁}`. In the frame
`(v₀, v₁, …, vₙ)` the matrix of `p` (l.1946–1951) is `p vₙ = v₁`, `p v₁ = v₀`, `p = 0` on
`ker p = I^⊥`. -/
theorem unipotent_frame (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) :
    ∃ vₙ v₁ v₀ : Minkowski d, pOf A vₙ = v₁ ∧ pOf A v₁ = v₀ ∧ v₀ ≠ 0 ∧ minkQ v₀ = 0 ∧
      nullPart A = ℝ ∙ v₀ ∧ 0 < minkQ v₁ ∧ minkB v₁ v₀ = 0 ∧ minkB vₙ v₀ = -minkQ v₁ ∧
      pOf A v₀ = 0 ∧ LinearMap.range (pOf A) = span ℝ {v₀, v₁} := by
  obtain ⟨w₀, hw, hw0⟩ := exists_mem_nullPart_ne_zero hA hn hp
  have hJ := nullPart_eq_span_of_mem hw hw0
  have hwq := minkQ_eq_zero_of_mem_nullPart hw
  -- a vector non-orthogonal to `w₀`
  obtain ⟨vₙ, hvn⟩ : ∃ vₙ, minkB vₙ w₀ ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (eq_zero_of_forall_minkB h)
  set v₁ := pOf A vₙ with hv₁
  set v₀ := pOf A v₁ with hv₀
  have hv1J : v₁ ∈ minkOrth (nullPart A) := pOf_apply_mem_minkOrth_nullPart A vₙ
  have hv0J : v₀ ∈ nullPart A := pOf_pOf_mem_nullPart hA hn hp vₙ
  -- `v₁` is spacelike
  have hq1 : 0 < minkQ v₁ := by
    obtain ⟨hnn, hz⟩ := minkQ_nonneg_of_null_orth hwq hw0 (hv1J _ hw)
    refine lt_of_le_of_ne hnn fun h0 => ?_
    obtain ⟨c, hc⟩ := hz h0.symm
    have hmem : pOf A vₙ ∈ nullPart A := by rw [← hv₁, hc]; exact smul_mem _ _ hw
    have h1 := mem_minkOrth_nullPart_of_pOf_mem hA hmem
    rw [← hv₁, hc, minkB_smul_right] at h1
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hvn
    have hker : vₙ ∈ LinearMap.ker (pOf A) := by
      rw [LinearMap.mem_ker, ← hv₁, hc, hc0, zero_smul]
    rw [ker_pOf_eq_minkOrth hA] at hker
    exact hvn (by rw [minkB_comm]; exact hker _ (nullPart_le_range A hw))
  -- `⟨vₙ | v₀⟩ = −|v₁|²`
  have hb : minkB vₙ v₀ = -minkQ v₁ := by
    have hs := star_identity hA vₙ v₁
    have e : minkB v₁ v₀ = 0 := by rw [minkB_comm]; exact hv1J _ hv0J
    rw [← hv₁, ← hv₀, e, ← minkQ_eq_minkB] at hs
    linarith
  have hv00 : v₀ ≠ 0 := by
    intro h; rw [h, minkB_zero_right] at hb; linarith
  have hJ0 := nullPart_eq_span_of_mem hv0J hv00
  have hb10 : minkB v₁ v₀ = 0 := by rw [minkB_comm]; exact hv1J _ hv0J
  refine ⟨vₙ, v₁, v₀, rfl, rfl, hv00, minkQ_eq_zero_of_mem_nullPart hv0J, hJ0, hq1, hb10, hb,
    pOf_eq_zero_of_mem_nullPart hA hv0J, le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, rfl⟩
    -- `y = c vₙ + z` with `z ∈ J^⊥`
    have hbn : minkB v₀ vₙ ≠ 0 := by rw [minkB_comm, hb]; linarith
    set c := minkB v₀ y / minkB v₀ vₙ
    have hz : y - c • vₙ ∈ minkOrth (nullPart A) := by
      rw [hJ0, mem_minkOrth_span_singleton, minkB_sub_right, minkB_smul_right]
      simp only [c]; field_simp; ring
    obtain ⟨e, he⟩ := mem_span_singleton.1 (hJ0 ▸ pOf_mem_nullPart hA hn hp hz)
    have : pOf A y = e • v₀ + c • v₁ := by
      rw [he, map_sub, map_smul, ← hv₁]; abel
    rw [this]
    exact add_mem (smul_mem _ _ (subset_span (by simp)))
      (smul_mem _ _ (subset_span (by simp)))
  · rw [span_le]
    rintro x (rfl | rfl)
    · exact ⟨v₁, rfl⟩
    · exact ⟨vₙ, rfl⟩

/-- **`J^⊥ = I + I^⊥`** (l.1961). -/
theorem minkOrth_nullPart_eq_sup (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) :
    minkOrth (nullPart A) = LinearMap.range (pOf A) ⊔ minkOrth (LinearMap.range (pOf A)) := by
  obtain ⟨vₙ, v₁, v₀, h1, h0, -, -, hJ, -⟩ := unipotent_frame hA hn hp
  refine le_antisymm (fun x hx => ?_)
    (sup_le (range_le_minkOrth_nullPart A) (minkOrth_range_le_minkOrth_nullPart A))
  obtain ⟨c, hc⟩ := mem_span_singleton.1 (hJ ▸ pOf_mem_nullPart hA hn hp hx)
  have hk : x - c • v₁ ∈ minkOrth (LinearMap.range (pOf A)) := by
    rw [← ker_pOf_eq_minkOrth hA, LinearMap.mem_ker, map_sub, map_smul, h0, hc, sub_self]
  have : x = c • v₁ + (x - c • v₁) := by abel
  rw [this]
  exact add_mem_sup (smul_mem _ _ ⟨vₙ, h1⟩) hk

theorem finrank_nullPart (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) :
    finrank ℝ (nullPart A) = 1 := by
  obtain ⟨-, -, v₀, -, -, hv0, -, hJ, -⟩ := unipotent_frame hA hn hp
  rw [hJ, finrank_span_singleton hv0]

/-- **`dim I = 2`**. -/
theorem finrank_range_pOf (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) :
    finrank ℝ (LinearMap.range (pOf A)) = 2 := by
  obtain ⟨-, v₁, v₀, -, -, hv0, -, -, hq1, hb, -, -, hI⟩ := unipotent_frame hA hn hp
  have hv1 : v₁ ≠ 0 := by rintro rfl; simp at hq1
  have hinf : (ℝ ∙ v₀) ⊓ (ℝ ∙ v₁) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨h0, h1⟩
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 h0
    obtain ⟨b, hb'⟩ := mem_span_singleton.1 h1
    have := congrArg (fun z => minkB z v₁) hb'
    simp only [minkB_smul_left, minkB_comm v₀ v₁, hb, mul_zero, ← minkQ_eq_minkB] at this
    have hb0 : b = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hq1.ne'
    rw [mem_bot, ← hb', hb0, zero_smul]
  have := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ v₀) (ℝ ∙ v₁)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0, finrank_span_singleton hv1,
    ← span_insert] at this
  rw [hI]; exact this

theorem finrank_minkOrth_nullPart (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) :
    finrank ℝ (minkOrth (nullPart A)) = d := by
  rw [finrank_minkOrth, finrank_nullPart hA hn hp]; omega

/-- **Rem 6.1** (l.1966–1969): for `n = 3` (`d = 2`), `I = J^⊥`. -/
theorem range_eq_minkOrth_nullPart_of_dim_three (hd : d = 2) (hn : IsNilpotent (pOf A))
    (hp : pOf A ≠ 0) : LinearMap.range (pOf A) = minkOrth (nullPart A) :=
  Submodule.eq_of_le_of_finrank_eq (range_le_minkOrth_nullPart A)
    (by rw [finrank_range_pOf hA hn hp, finrank_minkOrth_nullPart hA hn hp, hd])

/-- **A nontrivial unipotent needs `n ≥ 3`** (`d ≥ 2`): `I` (dimension `2`) lies in `J^⊥`
(dimension `d`). So `stdNullRot_isParabolic`'s `d ≥ 2` is necessary. -/
theorem two_le_of_unipotent (hn : IsNilpotent (pOf A)) (hp : pOf A ≠ 0) : 2 ≤ d := by
  have := Submodule.finrank_mono (range_le_minkOrth_nullPart A)
  rwa [finrank_range_pOf hA hn hp, finrank_minkOrth_nullPart hA hn hp] at this

end unipotent

/-! ### The translation trichotomy (l.1954–1964, l.2008–2017) -/

/-- The **linear case**: `τ ∈ Im (L(g) − id)`, i.e. `g` has a fixed point (`exists_fixed_iff`).
For a unipotent `g` this is Barbot's `τ ∈ I` (l.1956); for a parabolic one it is `τ ∈ I` after
the normalisation `R τ = τ` (`parabolic_mem_range_iff`, l.2010). -/
def IsLinearCase (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) : Prop :=
  transPart g ∈ LinearMap.range (pOf g.linear)

/-- The **transverse case** relative to the unipotent factor `U`: `τ ∉ J^⊥` (l.1963, l.2014). -/
def IsTransverseCase (U : Minkowski d ≃ₗ[ℝ] Minkowski d) (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    Prop :=
  transPart g ∉ minkOrth (nullPart U)

/-- The **tangent case** relative to `U`: `τ ∈ J^⊥`, not linear (l.1959, l.2012). -/
def IsTangentCase (U : Minkowski d ≃ₗ[ℝ] Minkowski d) (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    Prop :=
  transPart g ∈ minkOrth (nullPart U) ∧ ¬IsLinearCase g

theorem linear_or_tangent_or_transverse (U : Minkowski d ≃ₗ[ℝ] Minkowski d)
    (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    IsLinearCase g ∨ IsTangentCase U g ∨ IsTransverseCase U g := by
  by_cases h : IsLinearCase g
  · exact Or.inl h
  · by_cases h' : transPart g ∈ minkOrth (nullPart U)
    · exact Or.inr (Or.inl ⟨h', h⟩)
    · exact Or.inr (Or.inr h')

theorem isLinearCase_transConj_iff (v : Minkowski d) (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    IsLinearCase (transConj v g) ↔ IsLinearCase g := by
  unfold IsLinearCase
  rw [linear_transConj, transPart_transConj]
  refine ⟨fun h => ?_, fun h => sub_mem h ⟨v, rfl⟩⟩
  simpa using add_mem h (⟨v, rfl⟩ : pOf g.linear v ∈ LinearMap.range (pOf g.linear))

/-- Membership of `τ` in a subspace containing `Im p` does not depend on the conjugate. -/
theorem transPart_transConj_mem_iff {g : Minkowski d ≃ᵃ[ℝ] Minkowski d}
    {W : Submodule ℝ (Minkowski d)} (hW : LinearMap.range (pOf g.linear) ≤ W) (v : Minkowski d) :
    transPart (transConj v g) ∈ W ↔ transPart g ∈ W := by
  rw [transPart_transConj]
  exact sub_mem_iff_left W (hW ⟨v, rfl⟩)

theorem IsLinearCase.exists_transConj_eq_zero {g : Minkowski d ≃ᵃ[ℝ] Minkowski d}
    (h : IsLinearCase g) : ∃ v, transPart (transConj v g) = 0 :=
  (exists_transConj_iff g 0).2 (by rw [sub_zero]; exact h)

/-- **The hyperplane criterion.** If `Im (L(g) − id) ⊂ W`, then `τ ∈ W` iff `g` preserves every
affine subspace with direction `W`. With `W = J^⊥` this is l.2016–2017. -/
theorem transPart_mem_iff_map_eq {g : Minkowski d ≃ᵃ[ℝ] Minkowski d}
    {W : Submodule ℝ (Minkowski d)} (hW : LinearMap.range (pOf g.linear) ≤ W) :
    transPart g ∈ W ↔ ∀ H : AffineSubspace ℝ (Minkowski d), H.direction = W →
      (H : Set (Minkowski d)).Nonempty → H.map (g : Minkowski d →ᵃ[ℝ] Minkowski d) = H := by
  have key : ∀ x, g x - x ∈ W ↔ transPart g ∈ W := fun x => by
    have : g x - x = pOf g.linear x + transPart g := by
      rw [apply_eq_linear_add_transPart, pOf_apply]; abel
    rw [this]; exact add_mem_cancel_left (hW ⟨x, rfl⟩)
  constructor
  · intro hτ H hdir _
    ext y
    rw [AffineSubspace.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine (AffineSubspace.vsub_right_mem_direction_iff_mem hx _).1 ?_
      rw [hdir, vsub_eq_sub]; exact (key x).2 hτ
    · intro hy
      refine ⟨g.symm y, (AffineSubspace.vsub_right_mem_direction_iff_mem hy _).1 ?_, by simp⟩
      rw [hdir, vsub_eq_sub]
      have := neg_mem ((key (g.symm y)).2 hτ)
      simpa using this
  · intro h
    have hH := h (AffineSubspace.mk' 0 W) (AffineSubspace.direction_mk' 0 W)
      ⟨0, AffineSubspace.self_mem_mk' 0 W⟩
    have hmem : g 0 ∈ AffineSubspace.mk' 0 W := by
      rw [← hH, AffineSubspace.mem_map]; exact ⟨0, AffineSubspace.self_mem_mk' 0 W, rfl⟩
    have := (AffineSubspace.vsub_right_mem_direction_iff_mem (AffineSubspace.self_mem_mk' 0 W)
      (g 0)).2 hmem
    rw [AffineSubspace.direction_mk', vsub_eq_sub, sub_zero] at this
    exact this

section unipotentCases

variable {g : Minkowski d ≃ᵃ[ℝ] Minkowski d} (hA : ∀ v, minkQ (g.linear v) = minkQ v)
  (hn : IsNilpotent (pOf g.linear)) (hp : pOf g.linear ≠ 0)
include hA hn hp

/-- **Unipotent, tangent case: `τ` can be assumed in `I^⊥`** (l.1959–1961, since
`J^⊥ = I + I^⊥`). -/
theorem IsTangentCase.exists_transConj_mem_minkOrth (h : IsTangentCase g.linear g) :
    ∃ v, transPart (transConj v g) ∈ minkOrth (LinearMap.range (pOf g.linear)) :=
  exists_transConj_mem_of_mem_sup g (by rw [← minkOrth_nullPart_eq_sup hA hn hp]; exact h.1)

/-- **Rem 6.1** (l.1966–1969): for `n = 3` (`d = 2`) the tangent case does not occur. -/
theorem not_isTangentCase_of_dim_three (hd : d = 2) : ¬IsTangentCase g.linear g := by
  rintro ⟨h1, h2⟩
  apply h2
  unfold IsLinearCase
  rw [range_eq_minkOrth_nullPart_of_dim_three hA hd hn hp]
  exact h1

omit hA hn hp in
/-- **Unipotent: nontransverse iff every affine hyperplane with direction `J^⊥` is preserved**
(l.2016–2017, the case `R = id`). -/
theorem unipotent_not_transverse_iff :
    ¬IsTransverseCase g.linear g ↔ ∀ H : AffineSubspace ℝ (Minkowski d),
      H.direction = minkOrth (nullPart g.linear) → (H : Set (Minkowski d)).Nonempty →
        H.map (g : Minkowski d →ᵃ[ℝ] Minkowski d) = H := by
  rw [IsTransverseCase, not_not]
  exact transPart_mem_iff_map_eq (range_le_minkOrth_nullPart _)

end unipotentCases

/-! ### Null eigenvectors -/

/-- An element of `SO₀(1, d)` scales a null eigenvector by a **positive** factor. -/
theorem lorentz.eigen_pos_of_null {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    {v : Minkowski d} (hv0 : v ≠ 0) (hq : minkQ v = 0) {c : ℝ} (h : A v = c • v) : 0 < c := by
  have hv1 : v.1 ≠ 0 := fun h' => hv0 (eq_zero_of_fst_eq_zero h' hq.le)
  have aux : ∀ w : Minkowski d, 0 < w.1 → minkQ w = 0 → A w = c • w → 0 < c := by
    intro w hw hwq hAw
    have hf := lorentz.isFutureCausal_apply hA (v := w) ⟨hw.le, hwq.le⟩
    rw [hAw] at hf
    have h1 : 0 ≤ c * w.1 := by simpa using hf.1
    have hc0 : 0 ≤ c := nonneg_of_mul_nonneg_left h1 hw
    refine lt_of_le_of_ne hc0 fun hc => ?_
    rw [← hc, zero_smul] at hAw
    have : w = 0 := A.injective (by rw [hAw, map_zero])
    rw [this] at hw; simp at hw
  rcases lt_or_gt_of_ne hv1 with h1 | h1
  · exact aux (-v) (by simpa using h1) (by simpa using hq) (by rw [map_neg, h, smul_neg])
  · exact aux v h1 hq h

/-- An elliptic element scales an eigenvector by `±1`. -/
theorem IsElliptic.eigen_sq {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (he : IsElliptic A)
    {v : Minkowski d} (hv0 : v ≠ 0) {c : ℝ} (h : A v = c • v) : c * c = 1 := by
  obtain ⟨E, -, hpos, hE⟩ := he
  have h1 := hE v v
  simp only [h, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 := hpos v hv0
  have : (c * c - 1) * E v v = 0 := by linarith
  rcases mul_eq_zero.1 this with h3 | h3
  · linarith
  · linarith

/-- An elliptic element of `SO₀(1, d)` fixes each of its null eigenvectors. -/
theorem IsElliptic.eigen_eq_one {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    (he : IsElliptic A) {v : Minkowski d} (hv0 : v ≠ 0) (hq : minkQ v = 0) {c : ℝ}
    (h : A v = c • v) : c = 1 := by
  have h1 := he.eigen_sq hv0 h
  have h2 := lorentz.eigen_pos_of_null hA hv0 hq h
  nlinarith

/-! ### [6.P] Parabolic linear parts (l.1971–2017) -/

section parabolic

variable {R U : Minkowski d ≃ₗ[ℝ] Minkowski d}

theorem pOf_comm_of_comm (hc : R * U = U * R) (x : Minkowski d) :
    R (pOf U x) = pOf U (R x) := by
  have := DFunLike.congr_fun hc x
  simp only [LinearEquiv.mul_apply] at this
  rw [pOf_apply, pOf_apply, map_sub, this]

variable (hR : R ∈ lorentz d) (hU : U ∈ lorentz d) (hRe : IsElliptic R)
  (hn : IsNilpotent (pOf U)) (hU1 : U ≠ 1) (hc : R * U = U * R)

include hU hc in
/-- **`J` is `R`-invariant** (l.1976–1978). -/
theorem parabolic_R_mem_nullPart {x : Minkowski d} (hx : x ∈ nullPart U) : R x ∈ nullPart U := by
  obtain ⟨⟨y, rfl⟩, h2⟩ := hx
  have h2' : pOf U y ∈ minkOrth (LinearMap.range (pOf U)) := h2
  rw [← ker_pOf_eq_minkOrth hU.1, LinearMap.mem_ker] at h2'
  refine ⟨⟨R y, (pOf_comm_of_comm hc y).symm⟩, ?_⟩
  have h3 : pOf U (R (pOf U y)) = 0 := by rw [← pOf_comm_of_comm hc, h2', map_zero]
  show R (pOf U y) ∈ minkOrth (LinearMap.range (pOf U))
  rw [← ker_pOf_eq_minkOrth hU.1]; exact h3

include hU hc in
/-- **`I^⊥ = ker p` is `R`-invariant** (l.1976–1978). -/
theorem parabolic_R_mem_minkOrth_range {x : Minkowski d}
    (hx : x ∈ minkOrth (LinearMap.range (pOf U))) : R x ∈ minkOrth (LinearMap.range (pOf U)) := by
  rw [← ker_pOf_eq_minkOrth hU.1, LinearMap.mem_ker] at hx ⊢
  rw [← pOf_comm_of_comm hc, hx, map_zero]

include hc in
/-- **`I` is `R`-invariant** (l.1976–1978). -/
theorem parabolic_R_mem_range {x : Minkowski d} (hx : x ∈ LinearMap.range (pOf U)) :
    R x ∈ LinearMap.range (pOf U) := by
  obtain ⟨y, rfl⟩ := hx; exact ⟨R y, (pOf_comm_of_comm hc y).symm⟩

include hU hn hU1 hc in
/-- **`J^⊥ = I + I^⊥` is `R`-invariant** (l.1976–1978). -/
theorem parabolic_R_mem_minkOrth_nullPart {x : Minkowski d}
    (hx : x ∈ minkOrth (nullPart U)) : R x ∈ minkOrth (nullPart U) := by
  rw [minkOrth_nullPart_eq_sup hU.1 hn (pOf_ne_zero hU1)] at hx ⊢
  obtain ⟨i, hi, k, hk, rfl⟩ := mem_sup.1 hx
  rw [map_add]
  exact add_mem_sup (parabolic_R_mem_range hc hi) (parabolic_R_mem_minkOrth_range hU hc hk)

include hR hU hRe hc in
/-- **`R v₀ = v₀`** (l.1978–1979): `R` preserves the null line `J`, and an elliptic element of
the orthochronous group fixes a null eigenvector. -/
theorem parabolic_R_fix_nullPart {v₀ : Minkowski d} (hv : v₀ ∈ nullPart U) : R v₀ = v₀ := by
  by_cases hv0 : v₀ = 0
  · rw [hv0, map_zero]
  have hm := parabolic_R_mem_nullPart hU hc hv
  rw [nullPart_eq_span_of_mem hv hv0] at hm
  obtain ⟨c, hc'⟩ := mem_span_singleton.1 hm
  have := hRe.eigen_eq_one hR hv0 (minkQ_eq_zero_of_mem_nullPart hv) hc'.symm
  rw [← hc', this, one_smul]

include hR hU hRe hn hU1 hc in
/-- **`R` is the identity on `I = ⟨v₀, v₁⟩`** (l.1979–1980). -/
theorem parabolic_R_fix_range {x : Minkowski d} (hx : x ∈ LinearMap.range (pOf U)) : R x = x := by
  obtain ⟨vₙ, v₁, v₀, h1, h0, hv00, -, hJ, -, -, -, hp0, hI⟩ :=
    unipotent_frame hU.1 hn (pOf_ne_zero hU1)
  have hv0J : v₀ ∈ nullPart U := hJ ▸ mem_span_singleton_self v₀
  have hR0 : R v₀ = v₀ := parabolic_R_fix_nullPart hR hU hRe hc hv0J
  have hRv1mem : R v₁ ∈ span ℝ {v₀, v₁} := hI ▸ ⟨R vₙ, by rw [← pOf_comm_of_comm hc, h1]⟩
  obtain ⟨a, b, hab⟩ := mem_span_pair.1 hRv1mem
  have hb : b = 1 := by
    have h' : R v₀ = b • v₀ := by
      rw [← h0, pOf_comm_of_comm hc, ← hab, map_add, map_smul, map_smul, hp0, h0, smul_zero,
        zero_add]
    rw [hR0] at h'
    have h'' : (1 - b) • v₀ = 0 := by rw [sub_smul, one_smul, ← h', sub_self]
    rcases smul_eq_zero.1 h'' with h | h
    · linarith
    · exact absurd h hv00
  have hRv1 : R v₁ = v₁ := by
    have hmem : a • v₀ ∈ LinearMap.range (pOf R) ⊓ LinearMap.ker (pOf R) := by
      refine ⟨⟨v₁, ?_⟩, ?_⟩
      · rw [pOf_apply, ← hab, hb, one_smul, add_sub_cancel_right]
      · show pOf R (a • v₀) = 0
        rw [pOf_apply, map_smul, hR0, sub_self]
    rw [hRe.range_inf_ker, mem_bot] at hmem
    rw [← hab, hmem, zero_add, hb, one_smul]
  rw [hI] at hx
  obtain ⟨s, t, rfl⟩ := mem_span_pair.1 hx
  rw [map_add, map_smul, map_smul, hR0, hRv1]

include hR hU hRe hn hU1 hc in
/-- **`R ∘ p = p`** (l.1982). -/
theorem parabolic_R_pOf (x : Minkowski d) : R (pOf U x) = pOf U x :=
  parabolic_R_fix_range hR hU hRe hn hU1 hc ⟨x, rfl⟩

include hR hU hRe hn hU1 hc in
/-- **`I ⊂ 𝓘^⊥`** (l.1984), `𝓘 = Im (R − id)`, whose orthogonal is the fixed set of `R`. -/
theorem parabolic_range_le_minkOrth :
    LinearMap.range (pOf U) ≤ minkOrth (LinearMap.range (pOf R)) := fun x hx => by
  rw [mem_minkOrth_range_iff hR.1]; exact parabolic_R_fix_range hR hU hRe hn hU1 hc hx

include hR hU hRe hn hU1 hc in
/-- **`𝓘 ⊂ I^⊥`** (l.1984–1985). -/
theorem parabolic_rangeR_le_minkOrth :
    LinearMap.range (pOf R) ≤ minkOrth (LinearMap.range (pOf U)) := by
  rintro _ ⟨z, rfl⟩ i hi
  show minkB i (pOf R z) = 0
  have h := minkB_map hR.1 i z
  rw [parabolic_R_fix_range hR hU hRe hn hU1 hc hi] at h
  rw [pOf_apply, minkB_sub_right, h, sub_self]

include hR hU hRe hn hU1 hc in
/-- **`vₙ` can be selected `R`-invariant** (l.1985–1989): some fixed point of `R` is not in
`J^⊥`. Barbot takes the `E`-orthogonal of `J^⊥`; here: otherwise `v₀ ∈ (𝓘^⊥)^⊥ = 𝓘`, and
`v₀ ∈ 𝓘 ∩ 𝓘^⊥ = 0` for elliptic `R`. -/
theorem parabolic_exists_fixed_not_mem :
    ∃ vₙ, R vₙ = vₙ ∧ vₙ ∉ minkOrth (nullPart U) := by
  obtain ⟨v₀, hv, hv0⟩ := exists_mem_nullPart_ne_zero hU.1 hn (pOf_ne_zero hU1)
  by_contra h
  push Not at h
  have hmem : v₀ ∈ minkOrth (minkOrth (LinearMap.range (pOf R))) := by
    intro x hx
    have hx' : R x = x := (mem_minkOrth_range_iff hR.1).1 hx
    show minkB x v₀ = 0
    rw [minkB_comm]; exact h x hx' v₀ hv
  rw [minkOrth_minkOrth] at hmem
  have hk : v₀ ∈ LinearMap.ker (pOf R) := by
    rw [LinearMap.mem_ker, pOf_apply, parabolic_R_fix_nullPart hR hU hRe hc hv, sub_self]
  have hbot := hRe.range_inf_ker
  rw [eq_bot_iff] at hbot
  exact hv0 ((mem_bot ℝ).1 (hbot ⟨hmem, hk⟩))

include hR hU hRe hn hU1 hc in
/-- `L(g) − id = (R − id) + p` (l.1991). -/
theorem pOf_mul_parabolic (x : Minkowski d) : pOf (R * U) x = pOf R x + pOf U x := by
  rw [pOf_apply, LinearEquiv.mul_apply, apply_eq_add_pOf U x, map_add,
    parabolic_R_pOf hR hU hRe hn hU1 hc]
  simp only [pOf_apply]; abel

include hR hU hRe hn hU1 hc in
/-- **`Im (R − id + p) = I ⊕ 𝓘`** (l.1991–2002). -/
theorem range_pOf_mul_parabolic :
    LinearMap.range (pOf (R * U)) = LinearMap.range (pOf U) ⊔ LinearMap.range (pOf R) := by
  have hcR := hRe.isCompl hR.1
  have dec : ∀ x : Minkowski d, x ∈ LinearMap.range (pOf R) ⊔
      minkOrth (LinearMap.range (pOf R)) := fun x => by rw [hcR.sup_eq_top]; exact mem_top
  have hR0 : ∀ w ∈ minkOrth (LinearMap.range (pOf R)), pOf R w = 0 := fun w hw => by
    rw [← LinearMap.mem_ker, ker_pOf_eq_minkOrth hR.1]; exact hw
  have hU0 : ∀ w ∈ LinearMap.range (pOf R), pOf U w = 0 := fun w hw => by
    rw [← LinearMap.mem_ker, ker_pOf_eq_minkOrth hU.1]
    exact parabolic_rangeR_le_minkOrth hR hU hRe hn hU1 hc hw
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [pOf_mul_parabolic hR hU hRe hn hU1 hc, add_comm]
    exact add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  · apply sup_le
    · rintro _ ⟨x, rfl⟩
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := mem_sup.1 (dec x)
      refine ⟨w₂, ?_⟩
      rw [pOf_mul_parabolic hR hU hRe hn hU1 hc, hR0 w₂ hw₂, zero_add, map_add, hU0 w₁ hw₁,
        zero_add]
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := mem_sup.1 (dec z)
      refine ⟨w₁, ?_⟩
      rw [pOf_mul_parabolic hR hU hRe hn hU1 hc, hU0 w₁ hw₁, add_zero, map_add, hR0 w₂ hw₂,
        add_zero]

include hR hU hRe hn hU1 hc in
/-- **The sum `I ⊕ 𝓘` is direct** (l.2001–2002); it is orthogonal by
`parabolic_range_le_minkOrth`. -/
theorem parabolic_range_inf_rangeR :
    LinearMap.range (pOf U) ⊓ LinearMap.range (pOf R) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  have hk : x ∈ LinearMap.ker (pOf R) := by
    rw [LinearMap.mem_ker, pOf_apply, parabolic_R_fix_range hR hU hRe hn hU1 hc hx, sub_self]
  rw [← hRe.range_inf_ker]; exact ⟨hx', hk⟩

include hR hU hRe hn hU1 hc in
theorem parabolic_range_le_minkOrth_nullPart :
    LinearMap.range (pOf (R * U)) ≤ minkOrth (nullPart U) := by
  rw [range_pOf_mul_parabolic hR hU hRe hn hU1 hc]
  exact sup_le (range_le_minkOrth_nullPart U)
    ((parabolic_rangeR_le_minkOrth hR hU hRe hn hU1 hc).trans
      (minkOrth_range_le_minkOrth_nullPart U))

variable {g : Minkowski d ≃ᵃ[ℝ] Minkowski d} (hg : g.linear = R * U)

include hR hU hRe hn hU1 hc hg in
/-- **The parabolic normal form of `τ`** (l.2004–2006): up to conjugacy by a translation, `τ` is
fixed by `R` and orthogonal to `v₁` (any spacelike `v₁ ∈ I`). -/
theorem parabolic_exists_transConj_normal {v₁ : Minkowski d}
    (hv₁ : v₁ ∈ LinearMap.range (pOf U)) (hq : minkQ v₁ ≠ 0) :
    ∃ v, R (transPart (transConj v g)) = transPart (transConj v g) ∧
      minkB (transPart (transConj v g)) v₁ = 0 := by
  have hcR := hRe.isCompl hR.1
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.1
    (show transPart g ∈ LinearMap.range (pOf R) ⊔ minkOrth (LinearMap.range (pOf R)) by
      rw [hcR.sup_eq_top]; exact mem_top)
  set c := minkB b v₁ / minkQ v₁
  have hbR : R b = b := (mem_minkOrth_range_iff hR.1).1 hb
  obtain ⟨v, hv⟩ := (exists_transConj_iff g (b - c • v₁)).2 (by
    rw [hg, range_pOf_mul_parabolic hR hU hRe hn hU1 hc]
    have : transPart g - (b - c • v₁) = c • v₁ + a := by rw [← hab]; abel
    rw [this]; exact add_mem_sup (smul_mem _ _ hv₁) ha)
  refine ⟨v, ?_, ?_⟩
  · rw [hv, map_sub, map_smul, hbR, parabolic_R_fix_range hR hU hRe hn hU1 hc hv₁]
  · rw [hv, minkB_sub_left, minkB_smul_left, ← minkQ_eq_minkB]
    simp only [c]; field_simp; ring

include hR hU hRe hn hU1 hc hg in
/-- **For `τ` fixed by `R`, the linear case is `τ ∈ I`** (l.2010). -/
theorem parabolic_mem_range_iff {τ : Minkowski d} (hτ : R τ = τ) :
    τ ∈ LinearMap.range (pOf g.linear) ↔ τ ∈ LinearMap.range (pOf U) := by
  rw [hg, range_pOf_mul_parabolic hR hU hRe hn hU1 hc]
  refine ⟨fun h => ?_, fun h => mem_sup_left h⟩
  obtain ⟨i, hi, j, hj, rfl⟩ := mem_sup.1 h
  have hiR := parabolic_R_fix_range hR hU hRe hn hU1 hc hi
  have hjR : pOf R j = 0 := by
    rw [map_add, hiR] at hτ
    rw [pOf_apply, sub_eq_zero]; exact add_left_cancel hτ
  have hj0 : j = 0 := by
    rw [← mem_bot ℝ, ← hRe.range_inf_ker]; exact ⟨hj, hjR⟩
  rw [hj0, add_zero]; exact hi

include hR hU hRe hn hU1 hc hg in
/-- **A parabolic element is nontransverse iff it preserves every affine hyperplane with
direction `J^⊥`** (l.2016–2017). -/
theorem parabolic_not_transverse_iff :
    ¬IsTransverseCase U g ↔ ∀ H : AffineSubspace ℝ (Minkowski d),
      H.direction = minkOrth (nullPart U) → (H : Set (Minkowski d)).Nonempty →
        H.map (g : Minkowski d →ᵃ[ℝ] Minkowski d) = H := by
  rw [IsTransverseCase, not_not]
  exact transPart_mem_iff_map_eq (hg ▸ parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc)

include hR hU hRe hn hU1 hc hg in
/-- The transverse case is well defined on the conjugacy class by translations. -/
theorem parabolic_isTransverseCase_transConj_iff (v : Minkowski d) :
    IsTransverseCase U (transConj v g) ↔ IsTransverseCase U g := by
  unfold IsTransverseCase
  rw [transPart_transConj_mem_iff
    (hg ▸ parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc) v]

end parabolic

/-! ### Elementary inclusions between the classes -/

/-- The euclidean form `t t' + ⟪x, x'⟫` on `Minkowski d`. -/
noncomputable def euclForm (d : ℕ) : LinearMap.BilinForm ℝ (Minkowski d) :=
  LinearMap.mk₂ ℝ (fun v w => v.1 * w.1 + inner ℝ v.2 w.2)
    (fun u v w => by simp only [Prod.fst_add, Prod.snd_add, inner_add_left]; ring)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_left]; ring)
    (fun u v w => by simp only [Prod.fst_add, Prod.snd_add, inner_add_right]; ring)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]; ring)

theorem euclForm_pos {v : Minkowski d} (hv : v ≠ 0) : 0 < euclForm d v v := by
  show 0 < v.1 * v.1 + inner ℝ v.2 v.2
  rw [real_inner_self_eq_norm_sq]
  by_contra h
  push Not at h
  apply hv
  have h1 : v.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg ‖v.2‖]
  have h2 : ‖v.2‖ = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg ‖v.2‖, norm_nonneg v.2]
  exact Prod.ext h1 (norm_eq_zero.1 h2)

/-- The identity is elliptic. -/
theorem isElliptic_one : IsElliptic (1 : Minkowski d ≃ₗ[ℝ] Minkowski d) :=
  ⟨euclForm d, fun v w => by
    show v.1 * w.1 + inner ℝ v.2 w.2 = w.1 * v.1 + inner ℝ w.2 v.2
    rw [mul_comm, real_inner_comm], fun _ hv => euclForm_pos hv, fun _ _ => rfl⟩

/-- A hyperbolic element of `SO₀(1, d)` is loxodromic (`R = id`). -/
theorem IsHyperbolic.isLoxodromic {H : Minkowski d ≃ₗ[ℝ] Minkowski d} (hH : H ∈ lorentz d)
    (h : IsHyperbolic H) : IsLoxodromic H :=
  ⟨1, H, (lorentz d).one_mem, hH, isElliptic_one, h, (one_mul H).symm, by rw [one_mul, mul_one]⟩

/-- A nontrivial unipotent element of `SO₀(1, d)` is parabolic (`R = id`). -/
theorem IsUnipotent.isParabolic {U : Minkowski d ≃ₗ[ℝ] Minkowski d} (hU : U ∈ lorentz d)
    (h : IsUnipotent U) (h1 : U ≠ 1) : IsParabolic U :=
  ⟨1, U, (lorentz d).one_mem, hU, isElliptic_one, h, h1, (one_mul U).symm,
    by rw [one_mul, mul_one]⟩

/-! ### Conjugation invariance -/

section conj

variable {A : Minkowski d ≃ₗ[ℝ] Minkowski d}

theorem IsElliptic.conj (h : IsElliptic A) (C : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    IsElliptic (C * A * C⁻¹) := by
  obtain ⟨E, hs, hpos, hE⟩ := h
  refine ⟨E.compl₁₂ (C.symm : Minkowski d →ₗ[ℝ] Minkowski d)
    (C.symm : Minkowski d →ₗ[ℝ] Minkowski d), fun v w => ?_, fun v hv => ?_, fun v w => ?_⟩
  · simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]; exact hs _ _
  · simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    exact hpos _ (fun h0 => hv (by simpa using congrArg C h0))
  · simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact hE _ _

theorem pOf_conj (C : Minkowski d ≃ₗ[ℝ] Minkowski d) (x : Minkowski d) :
    pOf (C * A * C⁻¹) x = C (pOf A (C⁻¹ x)) := by
  simp [pOf_apply, map_sub]

theorem pow_pOf_conj (C : Minkowski d ≃ₗ[ℝ] Minkowski d) (n : ℕ) (x : Minkowski d) :
    (pOf (C * A * C⁻¹) ^ n) x = C ((pOf A ^ n) (C⁻¹ x)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pOf_conj, pow_succ', Module.End.mul_apply]
    simp

theorem IsUnipotent.conj (h : IsUnipotent A) (C : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    IsUnipotent (C * A * C⁻¹) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, LinearMap.ext fun x => by rw [pow_pOf_conj, hn]; simp⟩

theorem IsHyperbolic.conj (h : IsHyperbolic A) {C : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hC : C ∈ lorentz d) : IsHyperbolic (C * A * C⁻¹) := by
  obtain ⟨e₀, e₁, ζ, hζ, h0, h1, h01, hA0, hA1, hW⟩ := h
  have hB := minkB_map (A := C) hC.1
  refine ⟨C e₀, C e₁, ζ, hζ, by rw [hC.1, h0], by rw [hC.1, h1], by rw [hB, h01], ?_, ?_,
    fun w hw0 hw1 => ?_⟩
  · simp [hA0]
  · simp [hA1]
  · have e0 : minkB e₀ (C⁻¹ w) = 0 := by
      rw [← hB, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]; exact hw0
    have e1 : minkB e₁ (C⁻¹ w) = 0 := by
      rw [← hB, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]; exact hw1
    have h2 := hW _ e0 e1
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h2, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply]

theorem lorentz.conj_mem {C B : Minkowski d ≃ₗ[ℝ] Minkowski d} (hC : C ∈ lorentz d)
    (hB : B ∈ lorentz d) : C * B * C⁻¹ ∈ lorentz d :=
  (lorentz d).mul_mem ((lorentz d).mul_mem hC hB) ((lorentz d).inv_mem hC)

theorem IsLoxodromic.conj (h : IsLoxodromic A) {C : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hC : C ∈ lorentz d) : IsLoxodromic (C * A * C⁻¹) := by
  obtain ⟨R, H, hR, hH, hRe, hHh, rfl, hc⟩ := h
  refine ⟨C * R * C⁻¹, C * H * C⁻¹, lorentz.conj_mem hC hR, lorentz.conj_mem hC hH, hRe.conj C,
    hHh.conj hC, by group, ?_⟩
  calc C * R * C⁻¹ * (C * H * C⁻¹) = C * (R * H) * C⁻¹ := by group
    _ = C * (H * R) * C⁻¹ := by rw [hc]
    _ = C * H * C⁻¹ * (C * R * C⁻¹) := by group

theorem IsParabolic.conj (h : IsParabolic A) {C : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hC : C ∈ lorentz d) : IsParabolic (C * A * C⁻¹) := by
  obtain ⟨R, U, hR, hU, hRe, hUn, hU1, rfl, hc⟩ := h
  refine ⟨C * R * C⁻¹, C * U * C⁻¹, lorentz.conj_mem hC hR, lorentz.conj_mem hC hU, hRe.conj C,
    hUn.conj C, fun h1 => hU1 ?_, by group, ?_⟩
  · calc U = C⁻¹ * (C * U * C⁻¹) * C := by group
      _ = 1 := by rw [h1]; group
  · calc C * R * C⁻¹ * (C * U * C⁻¹) = C * (R * U) * C⁻¹ := by group
      _ = C * (U * R) * C⁻¹ := by rw [hc]
      _ = C * U * C⁻¹ * (C * R * C⁻¹) := by group

theorem conj_conj_inv (C : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    C⁻¹ * (C * A * C⁻¹) * C⁻¹⁻¹ = A := by group

/-- **The five classes are invariant under conjugation in `SO₀(1, d)`.** -/
theorem classes_conj_iff {C : Minkowski d ≃ₗ[ℝ] Minkowski d} (hC : C ∈ lorentz d) :
    (IsElliptic (C * A * C⁻¹) ↔ IsElliptic A) ∧ (IsHyperbolic (C * A * C⁻¹) ↔ IsHyperbolic A) ∧
      (IsUnipotent (C * A * C⁻¹) ↔ IsUnipotent A) ∧
      (IsLoxodromic (C * A * C⁻¹) ↔ IsLoxodromic A) ∧
      (IsParabolic (C * A * C⁻¹) ↔ IsParabolic A) := by
  have hC' := (lorentz d).inv_mem hC
  refine ⟨⟨fun h => ?_, fun h => h.conj C⟩, ⟨fun h => ?_, fun h => h.conj hC⟩,
    ⟨fun h => ?_, fun h => h.conj C⟩, ⟨fun h => ?_, fun h => h.conj hC⟩,
    ⟨fun h => ?_, fun h => h.conj hC⟩⟩
  · simpa only [conj_conj_inv] using h.conj C⁻¹
  · simpa only [conj_conj_inv] using h.conj hC'
  · simpa only [conj_conj_inv] using h.conj C⁻¹
  · simpa only [conj_conj_inv] using h.conj hC'
  · simpa only [conj_conj_inv] using h.conj hC'

end conj

/-- The linear part of a conjugate isometry is the conjugate linear part. -/
theorem linear_conj (h g : Minkowski d ≃ᵃ[ℝ] Minkowski d) :
    (h * g * h⁻¹).linear = h.linear * g.linear * h.linear⁻¹ := by
  rw [← AffineEquiv.linearHom_apply, map_mul, map_mul, map_inv]; rfl

/-! ### The loxodromic frame -/

/-- Eigenvectors for an eigenvalue `l` with `l² ≠ 1` of a `minkQ`-preserving map are null and
mutually orthogonal, hence form a line. -/
theorem eigen_line {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : ∀ v, minkQ (A v) = minkQ v)
    {l : ℝ} (hl : l * l ≠ 1) {u w : Minkowski d} (hu0 : u ≠ 0) (hu : A u = l • u)
    (hw : A w = l • w) : ∃ c : ℝ, w = c • u := by
  have hnull : ∀ z, A z = l • z → minkQ z = 0 := fun z hz => by
    have h1 := hA z
    rw [hz, minkQ_smul] at h1
    have h2 : (l * l - 1) * minkQ z = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hl)
  have hB := minkB_map hA u w
  rw [hu, hw, minkB_smul_left, minkB_smul_right] at hB
  have hB0 : minkB u w = 0 := by
    have h2 : (l * l - 1) * minkB u w = 0 := by linear_combination hB
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hl)
  exact eq_smul_of_null_orth (hnull u hu) hu0 (hnull w hw) hB0

/-- **The loxodromic frame.** If `A = R ∘ H` is loxodromic, with `H` the boost in `(e₀, e₁)`, then
`u = e₀ + e₁` and `u' = e₀ − e₁` are null, non-orthogonal, eigenvectors of `A` for `l = e^ζ` and
`l⁻¹`, fixed by `R`, and `A = R` on `{u, u'}^⊥`. -/
theorem IsLoxodromic.frame {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsLoxodromic A) :
    ∃ (R : Minkowski d ≃ₗ[ℝ] Minkowski d) (u u' : Minkowski d) (l : ℝ),
      R ∈ lorentz d ∧ IsElliptic R ∧ A ∈ lorentz d ∧ u ≠ 0 ∧ u' ≠ 0 ∧ minkQ u = 0 ∧
      minkQ u' = 0 ∧ minkB u u' ≠ 0 ∧ 0 < l ∧ l ≠ 1 ∧ A u = l • u ∧ A u' = l⁻¹ • u' ∧
      R u = u ∧ R u' = u' ∧ ∀ w, minkB u w = 0 → minkB u' w = 0 → A w = R w := by
  obtain ⟨R, H, hR, hH, hRe, ⟨e₀, e₁, ζ, hζ, h0, h1, h01, hH0, hH1, hW⟩, rfl, hc⟩ := h
  set u := e₀ + e₁ with hu
  set u' := e₀ - e₁ with hu'
  have hHu : H u = Real.exp ζ • u := by
    rw [hu, map_add, hH0, hH1, ← Real.cosh_add_sinh]; module
  have hHu' : H u' = Real.exp (-ζ) • u' := by
    rw [hu', map_sub, hH0, hH1, ← Real.cosh_sub_sinh]; module
  have hq : minkQ u = 0 := by rw [hu, minkQ_add, h0, h1, h01]; ring
  have hq' : minkQ u' = 0 := by
    rw [hu', sub_eq_add_neg, minkQ_add, minkQ_neg, minkB_neg_right, h0, h1, h01]; ring
  have huu' : minkB u u' = -2 := by
    rw [hu, hu', minkB_add_left, minkB_sub_right, minkB_sub_right, ← minkQ_eq_minkB,
      ← minkQ_eq_minkB, minkB_comm e₁ e₀, h0, h1, h01]; ring
  have hu0 : u ≠ 0 := fun h => by rw [h, minkB_zero_left] at huu'; norm_num at huu'
  have hu0' : u' ≠ 0 := fun h => by rw [h, minkB_zero_right] at huu'; norm_num at huu'
  have hexp : Real.exp ζ * Real.exp ζ ≠ 1 := by
    rw [← Real.exp_add]; intro h; rw [Real.exp_eq_one_iff] at h; exact hζ (by linarith)
  have hexp' : Real.exp (-ζ) * Real.exp (-ζ) ≠ 1 := by
    rw [← Real.exp_add]; intro h; rw [Real.exp_eq_one_iff] at h; exact hζ (by linarith)
  have hRH : ∀ x, H (R x) = R (H x) := fun x => by
    rw [← LinearEquiv.mul_apply, ← hc, LinearEquiv.mul_apply]
  have hRu : R u = u := by
    obtain ⟨c, hc'⟩ := eigen_line hH.1 hexp hu0 hHu (w := R u) (by rw [hRH, hHu, map_smul])
    rw [hc', hRe.eigen_eq_one hR hu0 hq hc', one_smul]
  have hRu' : R u' = u' := by
    obtain ⟨c, hc'⟩ := eigen_line hH.1 hexp' hu0' hHu' (w := R u') (by rw [hRH, hHu', map_smul])
    rw [hc', hRe.eigen_eq_one hR hu0' hq' hc', one_smul]
  refine ⟨R, u, u', Real.exp ζ, hR, hRe, (lorentz d).mul_mem hR hH, hu0, hu0', hq, hq',
    by rw [huu']; norm_num, Real.exp_pos ζ, fun h => hζ (Real.exp_eq_one_iff ζ |>.1 h), ?_, ?_,
    hRu, hRu', fun w hw hw' => ?_⟩
  · rw [LinearEquiv.mul_apply, hHu, map_smul, hRu]
  · rw [LinearEquiv.mul_apply, hHu', map_smul, hRu', Real.exp_neg]
  · have e0 : minkB e₀ w = 0 := by
      rw [hu, minkB_add_left] at hw; rw [hu', minkB_sub_left] at hw'; linarith
    have e1 : minkB e₁ w = 0 := by
      rw [hu, minkB_add_left] at hw; rw [hu', minkB_sub_left] at hw'; linarith
    rw [LinearEquiv.mul_apply, hW w e0 e1]

theorem IsLoxodromic.exists_eigen {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsLoxodromic A) :
    ∃ u : Minkowski d, u ≠ 0 ∧ minkQ u = 0 ∧ ∃ l : ℝ, 0 < l ∧ l ≠ 1 ∧ A u = l • u := by
  obtain ⟨-, u, -, l, -, -, -, hu0, -, hq, -, -, hl, hl1, hAu, -⟩ := h.frame
  exact ⟨u, hu0, hq, l, hl, hl1, hAu⟩

/-- **A parabolic element has a Jordan block**: `A v₁ = v₁ + v₀`, `A v₀ = v₀`, `v₀ ≠ 0`. -/
theorem IsParabolic.exists_jordan {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsParabolic A) :
    ∃ v₁ v₀ : Minkowski d, v₀ ≠ 0 ∧ A v₁ = v₁ + v₀ ∧ A v₀ = v₀ := by
  obtain ⟨R, U, hR, hU, hRe, hn, hU1, rfl, hc⟩ := h
  obtain ⟨vₙ, v₁, v₀, h1, h0, hv00, -, -, -, -, -, hp0, -⟩ :=
    unipotent_frame hU.1 hn (pOf_ne_zero hU1)
  have fix := fun {x} (hx : x ∈ LinearMap.range (pOf U)) =>
    parabolic_R_fix_range hR hU hRe hn hU1 hc hx
  refine ⟨v₁, v₀, hv00, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, apply_eq_add_pOf U v₁, h0, map_add, fix ⟨vₙ, h1⟩, fix ⟨v₁, h0⟩]
  · rw [LinearEquiv.mul_apply, apply_eq_add_pOf U v₀, hp0, add_zero, fix ⟨v₁, h0⟩]

/-! ### The classes are disjoint -/

theorem IsLoxodromic.not_isElliptic {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsLoxodromic A) :
    ¬IsElliptic A := fun he => by
  obtain ⟨u, hu0, -, l, hl, hl1, hu⟩ := h.exists_eigen
  have := he.eigen_sq hu0 hu
  apply hl1; nlinarith

theorem IsParabolic.not_isElliptic {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsParabolic A) :
    ¬IsElliptic A := fun he => by
  obtain ⟨v₁, v₀, hv0, h1, h0⟩ := h.exists_jordan
  have hmem : v₀ ∈ LinearMap.range (pOf A) ⊓ LinearMap.ker (pOf A) :=
    ⟨⟨v₁, by rw [pOf_apply, h1, add_sub_cancel_left]⟩,
      by show pOf A v₀ = 0; rw [pOf_apply, h0, sub_self]⟩
  rw [he.range_inf_ker, mem_bot] at hmem
  exact hv0 hmem

theorem IsParabolic.not_isLoxodromic {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsParabolic A) :
    ¬IsLoxodromic A := fun hl => by
  obtain ⟨u, hu0, -, l, hl0, hl1, hu⟩ := hl.exists_eigen
  obtain ⟨R, U, hR, hU, hRe, ⟨n, hn⟩, -, rfl, hc⟩ := h
  have hAQ : ∀ v, minkQ ((R * U) v) = minkQ v := ((lorentz d).mul_mem hR hU).1
  have hll : l * l ≠ 1 := by intro h; apply hl1; nlinarith
  have hUu : (R * U) (U u) = l • U u := by
    have e : U * (R * U) = (R * U) * U := by rw [← mul_assoc, ← hc]
    rw [← LinearEquiv.mul_apply, ← e, LinearEquiv.mul_apply, hu, map_smul]
  obtain ⟨c, hc'⟩ := eigen_line hAQ hll hu0 hu hUu
  have hpow : ∀ k : ℕ, (pOf U ^ k) u = (c - 1) ^ k • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, pOf_apply, hc', pow_succ]
      module
  have hc1 : c = 1 := by
    have h0 := hpow n
    rw [hn, LinearMap.zero_apply] at h0
    rcases smul_eq_zero.1 h0.symm with h | h
    · have := (pow_eq_zero_iff'.1 h).1; linarith
    · exact absurd h hu0
  have hRu : R u = l • u := by rw [← hu, LinearEquiv.mul_apply, hc', hc1, one_smul]
  exact hll (hRe.eigen_sq hu0 hRu)

/-! ### Where the translation part can be put -/

/-- If `Im p ∩ ker p = 0`, then `𝐌ⁿ = I ⊕ I^⊥` and `τ` can be selected fixed by `L(g)`. -/
theorem exists_transConj_fixed_of_range_inf_ker {g : Minkowski d ≃ᵃ[ℝ] Minkowski d}
    (hA : ∀ v, minkQ (g.linear v) = minkQ v)
    (h : LinearMap.range (pOf g.linear) ⊓ LinearMap.ker (pOf g.linear) = ⊥) :
    ∃ v, g.linear (transPart (transConj v g)) = transPart (transConj v g) := by
  have hc : IsCompl (LinearMap.range (pOf g.linear)) (minkOrth (LinearMap.range (pOf g.linear))) := by
    rw [minkOrth, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint minkForm_isRefl,
      disjoint_iff, ← minkOrth, ← ker_pOf_eq_minkOrth hA]
    exact h
  obtain ⟨v, hv⟩ := exists_transConj_mem_of_mem_sup g
    (W := minkOrth (LinearMap.range (pOf g.linear))) (by rw [hc.sup_eq_top]; exact mem_top)
  exact ⟨v, (mem_minkOrth_range_iff hA).1 hv⟩

/-- **Loxodromic: `Im p ∩ ker p = 0`.** -/
theorem IsLoxodromic.range_inf_ker {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsLoxodromic A) :
    LinearMap.range (pOf A) ⊓ LinearMap.ker (pOf A) = ⊥ := by
  obtain ⟨R, u, u', l, hR, hRe, hA, hu0, hu0', hq, hq', huu', hl, hl1, hAu, hAu', hRu, hRu',
    hW⟩ := h.frame
  have hB := minkB_map (A := A) hA.1
  have hBR := minkB_map (A := R) hR.1
  rw [eq_bot_iff]
  rintro x ⟨⟨y, rfl⟩, hx⟩
  rw [mem_bot]
  have hAx : A (pOf A y) = pOf A y := by
    have hx' : pOf A (pOf A y) = 0 := hx
    rw [pOf_apply, sub_eq_zero] at hx'; exact hx'
  have hl' : l⁻¹ ≠ 1 := by intro h; apply hl1; rw [← inv_inv l, h, inv_one]
  have hxu : minkB (pOf A y) u = 0 := by
    have h1 := hB (pOf A y) u
    rw [hAx, hAu, minkB_smul_right] at h1
    have h2 : (l - 1) * minkB (pOf A y) u = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hl1)
  have hxu' : minkB (pOf A y) u' = 0 := by
    have h1 := hB (pOf A y) u'
    rw [hAx, hAu', minkB_smul_right] at h1
    have h2 : (l⁻¹ - 1) * minkB (pOf A y) u' = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hl')
  set α := minkB y u' / minkB u u'
  set β := minkB y u / minkB u u'
  set w := y - α • u - β • u' with hw
  have hwu : minkB u w = 0 := by
    rw [hw, minkB_sub_right, minkB_sub_right, minkB_smul_right, minkB_smul_right,
      ← minkQ_eq_minkB, hq, minkB_comm u y]
    simp only [β]; field_simp; ring
  have hwu' : minkB u' w = 0 := by
    rw [hw, minkB_sub_right, minkB_sub_right, minkB_smul_right, minkB_smul_right,
      ← minkQ_eq_minkB, hq', minkB_comm u' y, minkB_comm u' u]
    simp only [α]; field_simp; ring
  have hy : y = α • u + β • u' + w := by rw [hw]; abel
  have hAy : A y = (α * l) • u + (β * l⁻¹) • u' + R w := by
    conv_lhs => rw [hy]
    rw [map_add, map_add, map_smul, map_smul, hAu, hAu', hW w hwu hwu', smul_smul, smul_smul]
  have hxe : pOf A y = (α * (l - 1)) • u + (β * (l⁻¹ - 1)) • u' + (R w - w) := by
    rw [pOf_apply, hAy]
    conv_lhs => rw [hy]
    module
  have hRwu : minkB (R w) u = 0 := by rw [← hRu, hBR, minkB_comm, hwu]
  have hRwu' : minkB (R w) u' = 0 := by rw [← hRu', hBR, minkB_comm, hwu']
  have hα : α = 0 := by
    have h1 := hxu'
    rw [hxe, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left, minkB_sub_left,
      ← minkQ_eq_minkB, hq', hRwu', minkB_comm w u', hwu'] at h1
    have h2 : α * ((l - 1) * minkB u u') = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_right (mul_ne_zero (sub_ne_zero.2 hl1) huu')
  have hβ : β = 0 := by
    have h1 := hxu
    rw [hxe, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left, minkB_sub_left,
      ← minkQ_eq_minkB, hq, hRwu, minkB_comm w u, hwu, minkB_comm u' u] at h1
    have h2 : β * ((l⁻¹ - 1) * minkB u u') = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_right (mul_ne_zero (sub_ne_zero.2 hl') huu')
  rw [hα, hβ, zero_mul, zero_mul, zero_smul, zero_smul, zero_add, zero_add] at hxe
  have hxR : R (pOf A y) = pOf A y := by
    rw [← hW _ (by rw [minkB_comm]; exact hxu) (by rw [minkB_comm]; exact hxu'), hAx]
  have hmem : pOf A y ∈ LinearMap.range (pOf R) ⊓ LinearMap.ker (pOf R) :=
    ⟨⟨w, by rw [hxe, pOf_apply]⟩, by show pOf R (pOf A y) = 0; rw [pOf_apply, hxR, sub_self]⟩
  rw [hRe.range_inf_ker, mem_bot] at hmem
  exact hmem

/-- **Loxodromic: `τ` can be assumed fixed by `L(g)`** (l.1896). -/
theorem IsLoxodromic.exists_transConj_fixed {g : Minkowski d ≃ᵃ[ℝ] Minkowski d}
    (hg : g ∈ isom d) (h : IsLoxodromic g.linear) :
    ∃ v, g.linear (transPart (transConj v g)) = transPart (transConj v g) :=
  exists_transConj_fixed_of_range_inf_ker hg.1 h.range_inf_ker

/-- **Hyperbolic: `τ` can be assumed in `I^⊥`** (l.1888). -/
theorem IsHyperbolic.exists_transConj_fixed {g : Minkowski d ≃ᵃ[ℝ] Minkowski d}
    (hg : g ∈ isom d) (h : IsHyperbolic g.linear) :
    ∃ v, g.linear (transPart (transConj v g)) = transPart (transConj v g) :=
  IsLoxodromic.exists_transConj_fixed hg (h.isLoxodromic hg)

/-! ### Elliptic elements and the hyperbolic space (l.1875–1878) -/

/-- A vector orthogonal to a timelike vector is spacelike or zero. -/
theorem minkQ_pos_of_orth_timelike {u x : Minkowski d} (hu : minkQ u < 0) (hux : minkB u x = 0)
    (hx : x ≠ 0) : 0 < minkQ x := by
  by_contra hle
  push Not at hle
  have hx1 : x.1 ≠ 0 := fun h => hx (eq_zero_of_fst_eq_zero h hle)
  have hux' : u.1 * x.1 = inner ℝ u.2 x.2 := by simp only [minkB] at hux; linarith
  have hcs := abs_real_inner_le_norm u.2 x.2
  rw [← hux', abs_mul] at hcs
  have h1 : ‖x.2‖ ≤ |x.1| := by
    have := sq_le_sq.1 (minkQ_le_zero_iff.1 hle); rwa [abs_norm] at this
  have h2 : ‖u.2‖ < |u.1| := by
    have := sq_lt_sq.1 (minkQ_lt_zero_iff.1 hu); rwa [abs_norm] at this
  have h3 : 0 < |x.1| := abs_pos.2 hx1
  nlinarith [mul_nonneg (norm_nonneg u.2) (sub_nonneg.2 h1), mul_pos (sub_pos.2 h2) h3]

/-- The diagonal `v ↦ E v v` of a bilinear form on `Minkowski d` is continuous. -/
theorem continuous_bilin_diag (E : LinearMap.BilinForm ℝ (Minkowski d)) :
    Continuous fun v : Minkowski d => E v v := by
  let Φ : Minkowski d →ₗ[ℝ] (Minkowski d →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (Minkowski d →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ E
  have := (LinearMap.continuous_of_finiteDimensional Φ).clm_apply continuous_id
  exact this

/-- A positive definite form on `Minkowski d` is coercive: `E v v ≥ m ‖v‖²` for some `m > 0`. -/
theorem exists_coercive (E : LinearMap.BilinForm ℝ (Minkowski d))
    (hpos : ∀ v, v ≠ 0 → 0 < E v v) : ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ E v v := by
  have hS : IsCompact (Metric.sphere (0 : Minkowski d) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : Minkowski d) 1).Nonempty := ⟨((1 : ℝ), 0), by simp⟩
  obtain ⟨v₀, hv₀, hmin⟩ := hS.exists_isMinOn hne (continuous_bilin_diag E).continuousOn
  have hv₀0 : v₀ ≠ 0 := by rintro rfl; simp at hv₀
  refine ⟨E v₀ v₀, hpos v₀ hv₀0, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Minkowski d) 1 := by
      simp [norm_smul, hn.ne']
    have h1 := isMinOn_iff.1 hmin _ hmem
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : ‖v‖⁻¹ * (‖v‖⁻¹ * E v v) = E v v / ‖v‖ ^ 2 := by field_simp
    rw [h2, le_div_iff₀ (by positivity)] at h1
    linarith

/-- **An elliptic element of `SO₀(1, d)` fixes a future timelike vector** (l.1876–1877: "`L(g)`
considered as an isometry of `𝐇ⁿ⁻¹` has a fixed point there"). -/
theorem IsElliptic.exists_fixed_timelike {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    (h : IsElliptic A) : ∃ u, IsFutureTimelike u ∧ A u = u := by
  obtain ⟨E, hs, hpos, hE⟩ := h
  have hqc := continuous_bilin_diag E
  obtain ⟨m, hm, hcoer⟩ := exists_coercive E hpos
  set S : Set (Minkowski d) := {v | 0 ≤ v.1 ∧ minkQ v = -1} with hSdef
  set v₀ : Minkowski d := ((1 : ℝ), 0)
  have hv₀ : v₀ ∈ S := ⟨zero_le_one, by simp [minkQ, v₀]⟩
  set c := E v₀ v₀
  set K := S ∩ {v | E v v ≤ c}
  have hK : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_eq continuous_minkQ continuous_const)).inter (isClosed_le hqc continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨max 1 (c / m), fun v hv => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : m * ‖v‖ ^ 2 ≤ c := (hcoer v).trans hv.2
      have h2 : ‖v‖ ^ 2 ≤ c / m := by rw [le_div_iff₀ hm]; linarith
      rcases le_or_gt ‖v‖ 1 with h3 | h3
      · exact h3.trans (le_max_left _ _)
      · exact (by nlinarith : ‖v‖ ≤ c / m).trans (le_max_right _ _)
  obtain ⟨u, huK, humin⟩ := hK.exists_isMinOn ⟨v₀, hv₀, show E v₀ v₀ ≤ c from le_refl _⟩
    hqc.continuousOn
  have hminS : ∀ w ∈ S, E u u ≤ E w w := fun w hw => by
    by_cases hw' : E w w ≤ c
    · exact isMinOn_iff.1 humin w ⟨hw, hw'⟩
    · push Not at hw'; exact huK.2.trans hw'.le
  have hAS : ∀ w ∈ S, A w ∈ S := fun w hw =>
    ⟨(lorentz.isFutureCausal_apply hA (v := w) ⟨hw.1, by rw [hw.2]; norm_num⟩).1,
      by rw [hA.1 w, hw.2]⟩
  -- the time component on `S` is `√(1 + ‖x‖²)`
  have hS2 : ∀ w ∈ S, w.1 ^ 2 = 1 + ‖w.2‖ ^ 2 := fun w hw => by
    have := hw.2; simp only [minkQ] at this; linarith
  -- reverse Cauchy–Schwarz on `S`
  have hrcs : ∀ v ∈ S, ∀ w ∈ S, minkB v w ≤ -1 := by
    intro v hv w hw
    have hv2 := hS2 v hv
    have hw2 := hS2 w hw
    have hX2 : (v.1 * w.1) ^ 2 ≥ (1 + ‖v.2‖ * ‖w.2‖) ^ 2 := by
      rw [mul_pow, hv2, hw2]; nlinarith [sq_nonneg (‖v.2‖ - ‖w.2‖)]
    have hX0 : 0 ≤ v.1 * w.1 := mul_nonneg hv.1 hw.1
    have hY0 : 0 ≤ 1 + ‖v.2‖ * ‖w.2‖ := by positivity
    have hXY : 1 + ‖v.2‖ * ‖w.2‖ ≤ v.1 * w.1 := by nlinarith
    have hin := real_inner_le_norm v.2 w.2
    simp only [minkB]; linarith
  -- uniqueness of the minimiser
  have huniq : ∀ w ∈ S, E w w = E u u → w = u := by
    intro w hw hwE
    by_contra hne
    set z : Minkowski d := (1 / 2 : ℝ) • (u + w)
    have hBuw := hrcs u huK.1 w hw
    have hzQ : minkQ z ≤ -1 := by
      simp only [z, minkQ_smul, minkQ_add, huK.1.2, hw.2]; nlinarith
    set q := -minkQ z
    have hq1 : 1 ≤ q := by simp only [q]; linarith
    have hq0 : 0 < q := by linarith
    set z' : Minkowski d := (Real.sqrt q)⁻¹ • z
    have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
    have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
    have hz'S : z' ∈ S := by
      refine ⟨?_, ?_⟩
      · simp only [z', z, Prod.smul_fst, Prod.fst_add, smul_eq_mul]
        have := huK.1.1; have := hw.1; positivity
      · simp only [z']
        have hz0 : minkQ z ≠ 0 := by linarith
        rw [minkQ_smul, inv_pow, hsq]
        simp only [q]; field_simp
    have hEz' : E z' z' ≤ E z z := by
      simp only [z', map_smul, LinearMap.smul_apply, smul_eq_mul]
      have h0 : 0 ≤ E z z := by
        rcases eq_or_ne z 0 with h0 | h0
        · rw [h0]; simp
        · exact (hpos z h0).le
      have hi : (Real.sqrt q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hq1)
      have hi0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.2 hsq0.le
      calc (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * E z z) ≤ 1 * (1 * E z z) := by
            apply mul_le_mul hi _ (by positivity) zero_le_one
            exact mul_le_mul hi le_rfl h0 zero_le_one
        _ = E z z := by ring
    have hdiff := hpos (u - w) (sub_ne_zero.2 (Ne.symm hne))
    have hEz : E z z < E u u := by
      simp only [z, map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.sub_apply, smul_eq_mul] at hdiff ⊢
      rw [hs w u] at hdiff ⊢
      nlinarith
    linarith [hminS z' hz'S]
  have hAu := huniq (A u) (hAS u huK.1) (by rw [hE])
  have hu2 := hS2 u huK.1
  refine ⟨u, ⟨?_, by rw [huK.1.2]; norm_num⟩, hAu⟩
  rcases huK.1.1.eq_or_lt with h0 | h0
  · rw [← h0] at hu2; nlinarith [sq_nonneg ‖u.2‖]
  · exact h0

/-- The euclidean norm `⟨v | w⟩ + (2/k) ⟨u | v⟩⟨u | w⟩` attached to a timelike `u`, `k = −|u|²`. -/
noncomputable def timelikeForm (u : Minkowski d) : LinearMap.BilinForm ℝ (Minkowski d) :=
  LinearMap.mk₂ ℝ (fun v w => minkB v w + 2 / (-minkQ u) * (minkB u v * minkB u w))
    (fun a b w => by simp only [minkB_add_left, minkB_add_right]; ring)
    (fun c v w => by simp only [minkB_smul_left, minkB_smul_right, smul_eq_mul]; ring)
    (fun v a b => by simp only [minkB_add_right]; ring)
    (fun c v w => by simp only [minkB_smul_right, smul_eq_mul]; ring)

/-- **Conversely, fixing a timelike vector makes `A` elliptic.** -/
theorem isElliptic_of_fixed_timelike {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : ∀ v, minkQ (A v) = minkQ v) {u : Minkowski d} (hu : minkQ u < 0) (hAu : A u = u) :
    IsElliptic A := by
  have hk : 0 < -minkQ u := by linarith
  have hq0 : minkQ u ≠ 0 := hu.ne
  refine ⟨timelikeForm u, fun v w => ?_, fun v hv => ?_, fun v w => ?_⟩
  · show minkB v w + _ * (minkB u v * minkB u w) = minkB w v + _ * (minkB u w * minkB u v)
    rw [minkB_comm v w, mul_comm (minkB u v)]
  · show 0 < minkB v v + 2 / (-minkQ u) * (minkB u v * minkB u v)
    set a := minkB u v
    set x := v + (a / -minkQ u) • u
    have hx : minkB u x = 0 := by
      simp only [x, minkB_add_right, minkB_smul_right, ← minkQ_eq_minkB, a]; field_simp; ring
    have hvx : minkB v v = minkQ x - a ^ 2 / -minkQ u := by
      have : v = x + (-(a / -minkQ u)) • u := by simp [x]
      rw [this, ← minkQ_eq_minkB, minkQ_add, minkQ_smul, minkB_smul_right, minkB_comm, hx]
      field_simp; ring
    rw [hvx]
    rcases eq_or_ne x 0 with h0 | h0
    · have ha : a ≠ 0 := by
        intro ha; apply hv
        have : v = x + (-(a / -minkQ u)) • u := by simp [x]
        rw [this, h0, ha]; simp
      rw [h0, minkQ_zero]
      have : 0 < a ^ 2 / -minkQ u := div_pos (by positivity) hk
      have e : 2 / -minkQ u * (a * a) = 2 * (a ^ 2 / -minkQ u) := by ring
      rw [e]; linarith
    · have := minkQ_pos_of_orth_timelike hu hx h0
      have h2 : 0 ≤ a ^ 2 / -minkQ u := div_nonneg (sq_nonneg a) hk.le
      have e : 2 / -minkQ u * (a * a) = 2 * (a ^ 2 / -minkQ u) := by ring
      rw [e]; linarith
  · show minkB (A v) (A w) + _ * (minkB u (A v) * minkB u (A w)) =
      minkB v w + _ * (minkB u v * minkB u w)
    conv_lhs => rw [← hAu]
    rw [minkB_map hA, minkB_map hA, minkB_map hA, hAu]

/-- **Elliptic ⇔ a fixed point in `𝐇ⁿ⁻¹`**, for elements of `SO₀(1, d)`. -/
theorem isElliptic_iff_exists_fixed_timelike {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) : IsElliptic A ↔ ∃ u, IsFutureTimelike u ∧ A u = u :=
  ⟨fun h => h.exists_fixed_timelike hA, fun ⟨_, hu, hAu⟩ => isElliptic_of_fixed_timelike hA.1 hu.2 hAu⟩

/-- **Elliptic: `I` is spacelike** (l.1875–1878), with `I = 0` exactly when `L(g) = id`. -/
theorem IsElliptic.range_spacelike {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    (h : IsElliptic A) {x : Minkowski d} (hx : x ∈ LinearMap.range (pOf A)) (hx0 : x ≠ 0) :
    0 < minkQ x := by
  obtain ⟨u, hu, hAu⟩ := h.exists_fixed_timelike hA
  obtain ⟨y, rfl⟩ := hx
  refine minkQ_pos_of_orth_timelike hu.2 ?_ hx0
  rw [pOf_apply, minkB_sub_right, ← minkB_map hA.1 u y, hAu, sub_self]

theorem range_pOf_eq_bot_iff {A : Minkowski d ≃ₗ[ℝ] Minkowski d} :
    LinearMap.range (pOf A) = ⊥ ↔ A = 1 := by
  rw [LinearMap.range_eq_bot]
  refine ⟨fun h => ?_, fun h => h ▸ pOf_one⟩
  by_contra h1; exact pOf_ne_zero h1 h

/-! ### Non-vacuity: boosts and null rotations in `SO₀(1, d)` -/

/-- **A `minkQ`-preserving linear map has determinant `±1`**: `det A ^ 2 = 1` (the Gram matrix
of `minkB` is invertible and `Aᵀ G A = G`). -/
theorem det_sq_of_minkQ {A : Minkowski d →ₗ[ℝ] Minkowski d} (hA : ∀ v, minkQ (A v) = minkQ v) :
    LinearMap.det A ^ 2 = 1 := by
  classical
  let b := Module.finBasis ℝ (Minkowski d)
  have hc : (minkForm d).compl₁₂ A A = minkForm d := LinearMap.ext₂ fun v w => by
    simp [minkB_map_of_minkQ hA]
  have hm :=
    LinearMap.toMatrix₂_compl₁₂ (b₁ := b) (b₂ := b) (b₁' := b) (b₂' := b) (minkForm d) A A
  rw [hc] at hm
  have hdet := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  have hne : (LinearMap.toMatrix₂ b b (minkForm d)).det ≠ 0 :=
    (LinearMap.nondegenerate_iff_det_ne_zero b).1 minkForm_nondegenerate
  have h2 : (LinearMap.det A ^ 2 - 1) * (LinearMap.toMatrix₂ b b (minkForm d)).det = 0 := by
    linear_combination -hdet
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)

/-- A `minkQ`-preserving map which is a square `B ∘ B` of a `minkQ`-preserving map has
determinant `1`. -/
theorem det_eq_one_of_eq_sq {A B : Minkowski d →ₗ[ℝ] Minkowski d}
    (hA : ∀ v, minkQ (A v) = minkQ v) (h : A = B ∘ₗ B) : LinearMap.det A = 1 := by
  have h1 := det_sq_of_minkQ hA
  have h2 : 0 ≤ LinearMap.det A := by rw [h, LinearMap.det_comp]; exact mul_self_nonneg _
  nlinarith

/-- A nonzero future causal vector and a future timelike one have `minkB < 0`. -/
theorem minkB_neg_of_future {z w : Minkowski d} (hz : IsFutureCausal z) (hz0 : z ≠ 0)
    (hw : IsFutureTimelike w) : minkB z w < 0 := by
  have hz1 : 0 < z.1 := lt_of_le_of_ne hz.1 fun h => hz0 (eq_zero_of_fst_eq_zero h.symm hz.2)
  have hzn : ‖z.2‖ ≤ z.1 := by nlinarith [norm_nonneg z.2, minkQ_le_zero_iff.1 hz.2]
  have hwn : ‖w.2‖ < w.1 := by nlinarith [norm_nonneg w.2, minkQ_lt_zero_iff.1 hw.2, hw.1]
  have hin := real_inner_le_norm z.2 w.2
  simp only [minkB]
  nlinarith [norm_nonneg w.2, norm_nonneg z.2]

/-- The time unit `(1, 0)`. -/
noncomputable def timeUnit (d : ℕ) : Minkowski d := ((1 : ℝ), 0)

@[simp] theorem minkQ_timeUnit : minkQ (timeUnit d) = -1 := by simp [minkQ, timeUnit]

/-- **A criterion for `SO₀(1, d)`**: a `minkQ`-preserving automorphism of determinant `1`
sending the time unit into the future lies in `lorentz d`. -/
theorem mem_lorentz_of {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hQ : ∀ v, minkQ (A v) = minkQ v)
    (h0 : 0 < (A (timeUnit d)).1)
    (hdet : LinearMap.det (A : Minkowski d →ₗ[ℝ] Minkowski d) = 1) : A ∈ lorentz d := by
  refine ⟨hQ, fun v hv => ?_, hdet⟩
  have hq : minkQ (A v) ≤ 0 := by rw [hQ]; exact hv.2
  refine ⟨?_, hq⟩
  by_contra hneg
  push Not at hneg
  have he : IsFutureTimelike (A (timeUnit d)) := ⟨h0, by rw [hQ]; simp⟩
  have hz : IsFutureCausal (-(A v)) := ⟨by simp; linarith, by simpa using hq⟩
  have hz0 : -(A v) ≠ 0 := fun h => by
    have : (A v).1 = 0 := by simpa using congrArg Prod.fst h
    linarith
  have h1 := minkB_neg_of_future hz hz0 he
  rw [minkB_neg_left, minkB_map hQ] at h1
  have : minkB v (timeUnit d) = -v.1 := by simp [minkB, timeUnit]
  linarith [hv.1]

section boost

variable (e₀ e₁ : Minkowski d)

/-- **The boost of rapidity `ζ`** in the pair `(e₀, e₁)`: with `a = −⟨x|e₀⟩`, `b = ⟨x|e₁⟩`,
`x ↦ x + ((ch ζ − 1) a + sh ζ b) e₀ + ((ch ζ − 1) b + sh ζ a) e₁`. For a `minkB`-orthonormal
pair (`e₀` timelike) it is Barbot's hyperbolic matrix (l.1881–1887) in a frame `(e₀, e₁, …)`. -/
noncomputable def boostLin (ζ : ℝ) : Minkowski d →ₗ[ℝ] Minkowski d where
  toFun x := x + ((Real.cosh ζ - 1) * -minkB x e₀ + Real.sinh ζ * minkB x e₁) • e₀ +
    ((Real.cosh ζ - 1) * minkB x e₁ + Real.sinh ζ * -minkB x e₀) • e₁
  map_add' x y := by simp only [minkB_add_left]; module
  map_smul' c x := by simp only [minkB_smul_left, RingHom.id_apply]; module

theorem boostLin_apply (ζ : ℝ) (x : Minkowski d) : boostLin e₀ e₁ ζ x =
    x + ((Real.cosh ζ - 1) * -minkB x e₀ + Real.sinh ζ * minkB x e₁) • e₀ +
      ((Real.cosh ζ - 1) * minkB x e₁ + Real.sinh ζ * -minkB x e₀) • e₁ := rfl

variable {e₀ e₁} (h0 : minkQ e₀ = -1) (h1 : minkQ e₁ = 1) (h01 : minkB e₀ e₁ = 0)
include h0 h1 h01

omit h1 in
theorem minkB_boostLin_e₀ (ζ : ℝ) (x : Minkowski d) :
    minkB (boostLin e₀ e₁ ζ x) e₀ = Real.cosh ζ * minkB x e₀ - Real.sinh ζ * minkB x e₁ := by
  rw [minkQ_eq_minkB] at h0
  rw [boostLin_apply, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left, h0,
    minkB_comm e₁ e₀, h01]; ring

omit h0 in
theorem minkB_boostLin_e₁ (ζ : ℝ) (x : Minkowski d) :
    minkB (boostLin e₀ e₁ ζ x) e₁ = Real.cosh ζ * minkB x e₁ - Real.sinh ζ * minkB x e₀ := by
  rw [minkQ_eq_minkB] at h1
  rw [boostLin_apply, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left, h1,
    h01]; ring

theorem boostLin_comp (ζ η : ℝ) :
    boostLin e₀ e₁ ζ ∘ₗ boostLin e₀ e₁ η = boostLin e₀ e₁ (ζ + η) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, boostLin_apply e₀ e₁ ζ, minkB_boostLin_e₀ h0 h01,
    minkB_boostLin_e₁ h1 h01, boostLin_apply e₀ e₁ η, boostLin_apply e₀ e₁ (ζ + η),
    Real.cosh_add, Real.sinh_add]
  module

omit h0 h1 h01 in
theorem boostLin_zero : boostLin e₀ e₁ 0 = LinearMap.id :=
  LinearMap.ext fun x => by simp [boostLin_apply]

theorem minkQ_boostLin (ζ : ℝ) (x : Minkowski d) : minkQ (boostLin e₀ e₁ ζ x) = minkQ x := by
  have hc := Real.cosh_sq ζ
  rw [minkQ_eq_minkB] at h0 h1
  rw [boostLin_apply, minkQ_add, minkQ_add]
  simp only [minkB_add_left, minkB_smul_left, minkB_smul_right, minkQ_smul, minkQ_eq_minkB e₀,
    minkQ_eq_minkB e₁, h0, h1, h01]
  linear_combination (-1) * (minkB x e₀ ^ 2 - minkB x e₁ ^ 2) * hc

/-- The boost as a linear automorphism (inverse: rapidity `−ζ`). -/
noncomputable def boost (ζ : ℝ) : Minkowski d ≃ₗ[ℝ] Minkowski d :=
  LinearEquiv.ofLinear (boostLin e₀ e₁ ζ) (boostLin e₀ e₁ (-ζ))
    (by rw [boostLin_comp h0 h1 h01, add_neg_cancel, boostLin_zero])
    (by rw [boostLin_comp h0 h1 h01, neg_add_cancel, boostLin_zero])

theorem boost_apply (ζ : ℝ) (x : Minkowski d) : boost h0 h1 h01 ζ x = boostLin e₀ e₁ ζ x := rfl

/-- **A boost of nonzero rapidity is hyperbolic.** -/
theorem isHyperbolic_boost {ζ : ℝ} (hζ : ζ ≠ 0) : IsHyperbolic (boost h0 h1 h01 ζ) := by
  have h0' := h0; have h1' := h1
  rw [minkQ_eq_minkB] at h0' h1'
  refine ⟨e₀, e₁, ζ, hζ, h0, h1, h01, ?_, ?_, fun w hw0 hw1 => ?_⟩
  · rw [boost_apply, boostLin_apply, h0', h01]; module
  · rw [boost_apply, boostLin_apply, h1', minkB_comm e₁ e₀, h01]; module
  · rw [boost_apply, boostLin_apply, minkB_comm w e₀, minkB_comm w e₁, hw0, hw1]; simp

end boost

/-- The spatial unit vector along the coordinate `i`. -/
noncomputable def spaceUnit {d : ℕ} (i : Fin d) : Minkowski d :=
  ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))

theorem minkQ_spaceUnit (i : Fin d) : minkQ (spaceUnit i) = 1 := by
  simp [minkQ, spaceUnit, (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).1 i]

theorem minkB_timeUnit_spaceUnit (i : Fin d) : minkB (timeUnit d) (spaceUnit i) = 0 := by
  simp [minkB, timeUnit, spaceUnit]

theorem minkB_spaceUnit_spaceUnit {i j : Fin d} (hij : i ≠ j) :
    minkB (spaceUnit i) (spaceUnit j) = 0 := by
  simp [minkB, spaceUnit, (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).2 hij]

/-- The standard boost along the coordinate `i`. -/
noncomputable def stdBoost (i : Fin d) (ζ : ℝ) : Minkowski d ≃ₗ[ℝ] Minkowski d :=
  boost minkQ_timeUnit (minkQ_spaceUnit i) (minkB_timeUnit_spaceUnit i) ζ

/-- **Boosts lie in `SO₀(1, d)`.** -/
theorem stdBoost_mem_lorentz (i : Fin d) (ζ : ℝ) : stdBoost i ζ ∈ lorentz d := by
  have hQ : ∀ v, minkQ (stdBoost i ζ v) = minkQ v :=
    minkQ_boostLin minkQ_timeUnit (minkQ_spaceUnit i) (minkB_timeUnit_spaceUnit i) ζ
  refine mem_lorentz_of hQ ?_ ?_
  · have : (stdBoost i ζ (timeUnit d)).1 = Real.cosh ζ := by
      simp [stdBoost, boost_apply, boostLin_apply, minkB, timeUnit, spaceUnit]
    rw [this]; exact Real.cosh_pos ζ
  · refine det_eq_one_of_eq_sq (B := boostLin (timeUnit d) (spaceUnit i) (ζ / 2)) hQ ?_
    rw [boostLin_comp minkQ_timeUnit (minkQ_spaceUnit i) (minkB_timeUnit_spaceUnit i), add_halves]
    rfl

/-- **Non-vacuity of the hyperbolic and loxodromic classes** (`d ≥ 1`, Barbot's `n ≥ 2`): the
standard boost of rapidity `ζ ≠ 0` is hyperbolic, in `SO₀(1, d)`, hence loxodromic. -/
theorem stdBoost_isHyperbolic (i : Fin d) {ζ : ℝ} (hζ : ζ ≠ 0) : IsHyperbolic (stdBoost i ζ) :=
  isHyperbolic_boost _ _ _ hζ

theorem stdBoost_isLoxodromic (i : Fin d) {ζ : ℝ} (hζ : ζ ≠ 0) : IsLoxodromic (stdBoost i ζ) :=
  (stdBoost_isHyperbolic i hζ).isLoxodromic (stdBoost_mem_lorentz i ζ)

section nullRotation

variable (u e : Minkowski d)

/-- **The null rotation** of parameter `s` about the null vector `u`, in the direction of the unit
spacelike `e ⊥ u`: `x ↦ x + s⟨x|u⟩ e − (s⟨x|e⟩ + s²/2 ⟨x|u⟩) u`. It is `exp (s (u ∧ e))`. -/
noncomputable def nullRotLin (s : ℝ) : Minkowski d →ₗ[ℝ] Minkowski d where
  toFun x := x + (s * minkB x u) • e + (-(s * minkB x e) - s ^ 2 / 2 * minkB x u) • u
  map_add' x y := by simp only [minkB_add_left]; module
  map_smul' c x := by simp only [minkB_smul_left, RingHom.id_apply]; module

theorem nullRotLin_apply (s : ℝ) (x : Minkowski d) : nullRotLin u e s x =
    x + (s * minkB x u) • e + (-(s * minkB x e) - s ^ 2 / 2 * minkB x u) • u := rfl

variable {u e} (hu : minkQ u = 0) (he : minkQ e = 1) (hue : minkB u e = 0)
include hu he hue

omit he in
theorem minkB_nullRotLin_u (s : ℝ) (x : Minkowski d) :
    minkB (nullRotLin u e s x) u = minkB x u := by
  rw [minkQ_eq_minkB] at hu
  rw [nullRotLin_apply, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left,
    minkB_comm e u, hue, hu]; ring

omit hu in
theorem minkB_nullRotLin_e (s : ℝ) (x : Minkowski d) :
    minkB (nullRotLin u e s x) e = minkB x e + s * minkB x u := by
  rw [minkQ_eq_minkB] at he
  rw [nullRotLin_apply, minkB_add_left, minkB_add_left, minkB_smul_left, minkB_smul_left, he,
    hue]; ring

theorem nullRotLin_comp (s t : ℝ) :
    nullRotLin u e s ∘ₗ nullRotLin u e t = nullRotLin u e (s + t) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, nullRotLin_apply u e s, minkB_nullRotLin_u hu hue,
    minkB_nullRotLin_e he hue, nullRotLin_apply u e t, nullRotLin_apply u e (s + t)]
  module

omit hu he hue in
theorem nullRotLin_zero : nullRotLin u e 0 = LinearMap.id :=
  LinearMap.ext fun x => by simp [nullRotLin_apply]

theorem minkQ_nullRotLin (s : ℝ) (x : Minkowski d) : minkQ (nullRotLin u e s x) = minkQ x := by
  rw [minkQ_eq_minkB] at hu he
  rw [nullRotLin_apply, minkQ_add, minkQ_add]
  simp only [minkB_add_left, minkB_smul_left, minkB_smul_right, minkQ_smul, minkQ_eq_minkB e,
    minkQ_eq_minkB u, hu, he, minkB_comm e u, hue]
  ring

/-- The null rotation as a linear automorphism (inverse: parameter `−s`). -/
noncomputable def nullRot (s : ℝ) : Minkowski d ≃ₗ[ℝ] Minkowski d :=
  LinearEquiv.ofLinear (nullRotLin u e s) (nullRotLin u e (-s))
    (by rw [nullRotLin_comp hu he hue, add_neg_cancel, nullRotLin_zero])
    (by rw [nullRotLin_comp hu he hue, neg_add_cancel, nullRotLin_zero])

theorem nullRot_apply (s : ℝ) (x : Minkowski d) : nullRot hu he hue s x = nullRotLin u e s x :=
  rfl

/-- **A null rotation is unipotent**: `p³ = 0`. -/
theorem isUnipotent_nullRot (s : ℝ) : IsUnipotent (nullRot hu he hue s) := by
  have hu' := hu; have he' := he
  rw [minkQ_eq_minkB] at hu' he'
  have hp : ∀ x, pOf (nullRot hu he hue s) x =
      (s * minkB x u) • e + (-(s * minkB x e) - s ^ 2 / 2 * minkB x u) • u := fun x => by
    rw [pOf_apply, nullRot_apply, nullRotLin_apply]; abel
  refine ⟨3, LinearMap.ext fun x => ?_⟩
  rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, hp x, hp, hp]
  simp only [minkB_add_left, minkB_smul_left, minkB_comm e u, hue, hu', he', LinearMap.zero_apply]
  module

/-- A null rotation of parameter `s ≠ 0` is not the identity (`u ≠ 0`). -/
theorem nullRot_ne_one (hu0 : u ≠ 0) {s : ℝ} (hs : s ≠ 0) : nullRot hu he hue s ≠ 1 := by
  intro h1
  have h := LinearEquiv.congr_fun h1 e
  rw [nullRot_apply, nullRotLin_apply, minkB_comm e u, hue, ← minkQ_eq_minkB, he,
    LinearEquiv.coe_one, id] at h
  have h' : (-s) • u = 0 := by
    have e1 : (-(s * 1) - s ^ 2 / 2 * 0) = -s := by ring
    rw [e1, mul_zero, zero_smul, add_zero] at h
    exact add_eq_left.1 h
  rcases smul_eq_zero.1 h' with h2 | h2
  · exact hs (neg_eq_zero.1 h2)
  · exact hu0 h2

end nullRotation

/-- The standard null rotation in the coordinates `i ≠ j`: `u = (1, eᵢ)`, `e = (0, eⱼ)`. -/
noncomputable def stdNullRot {i j : Fin d} (hij : i ≠ j) (s : ℝ) : Minkowski d ≃ₗ[ℝ] Minkowski d :=
  nullRot (u := timeUnit d + spaceUnit i) (e := spaceUnit j)
    (by rw [minkQ_add, minkQ_timeUnit, minkQ_spaceUnit, minkB_timeUnit_spaceUnit]; ring)
    (minkQ_spaceUnit j)
    (by rw [minkB_add_left, minkB_timeUnit_spaceUnit, minkB_spaceUnit_spaceUnit hij, add_zero]) s

/-- **Null rotations lie in `SO₀(1, d)`.** -/
theorem stdNullRot_mem_lorentz {i j : Fin d} (hij : i ≠ j) (s : ℝ) :
    stdNullRot hij s ∈ lorentz d := by
  have hu : minkQ (timeUnit d + spaceUnit i) = 0 := by
    rw [minkQ_add, minkQ_timeUnit, minkQ_spaceUnit, minkB_timeUnit_spaceUnit]; ring
  have hue : minkB (timeUnit d + spaceUnit i) (spaceUnit j) = 0 := by
    rw [minkB_add_left, minkB_timeUnit_spaceUnit, minkB_spaceUnit_spaceUnit hij, add_zero]
  have hQ : ∀ v, minkQ (stdNullRot hij s v) = minkQ v :=
    minkQ_nullRotLin hu (minkQ_spaceUnit j) hue s
  refine mem_lorentz_of hQ ?_ ?_
  · have : (stdNullRot hij s (timeUnit d)).1 = 1 + s ^ 2 / 2 := by
      simp [stdNullRot, nullRot_apply, nullRotLin_apply, minkB, timeUnit, spaceUnit]
    rw [this]; positivity
  · refine det_eq_one_of_eq_sq (B := nullRotLin (timeUnit d + spaceUnit i) (spaceUnit j) (s / 2))
      hQ ?_
    rw [nullRotLin_comp hu (minkQ_spaceUnit j) hue, add_halves]
    rfl

/-- **Non-vacuity of the unipotent and parabolic classes** (`d ≥ 2`, Barbot's `n ≥ 3`): the
standard null rotation of parameter `s ≠ 0` is unipotent, nontrivial, in `SO₀(1, d)`, hence
parabolic (with `R = id`). -/
theorem stdNullRot_isParabolic {i j : Fin d} (hij : i ≠ j) {s : ℝ} (hs : s ≠ 0) :
    IsParabolic (stdNullRot hij s) := by
  refine IsUnipotent.isParabolic (stdNullRot_mem_lorentz hij s) (isUnipotent_nullRot _ _ _ s)
    (nullRot_ne_one _ _ _ ?_ hs)
  intro h
  have := congrArg Prod.fst h
  simp [timeUnit, spaceUnit] at this

/-! ### The trichotomy (l.1868–1901): a cone eigenvector, the boost factor, the Fitting split -/

/-- Two future causal vectors have `minkB ≤ 0`. -/
theorem minkB_le_zero_of_isFutureCausal {z w : Minkowski d} (hz : IsFutureCausal z)
    (hw : IsFutureCausal w) : minkB z w ≤ 0 := by
  have hzn : ‖z.2‖ ≤ z.1 := by nlinarith [norm_nonneg z.2, minkQ_le_zero_iff.1 hz.2, hz.1]
  have hwn : ‖w.2‖ ≤ w.1 := by nlinarith [norm_nonneg w.2, minkQ_le_zero_iff.1 hw.2, hw.1]
  have hin := real_inner_le_norm z.2 w.2
  simp only [minkB]
  nlinarith [norm_nonneg w.2, norm_nonneg z.2]

/-- A future causal vector which is timelike is future timelike. -/
theorem IsFutureCausal.isFutureTimelike_of_neg {v : Minkowski d} (hv : IsFutureCausal v)
    (hq : minkQ v < 0) : IsFutureTimelike v :=
  ⟨lt_of_le_of_ne hv.1 fun h => absurd hq (not_lt.2 (minkQ_nonneg_of_fst_eq_zero h.symm)), hq⟩

/-- A timelike vector pairing negatively with a future causal vector is future timelike. -/
theorem isFutureTimelike_of_minkB_neg {w u : Minkowski d} (hw : minkQ w < 0)
    (hu : IsFutureCausal u) (h : minkB w u < 0) : IsFutureTimelike w := by
  rcases isFutureTimelike_or_neg hw with h1 | h1
  · exact h1
  · exfalso
    have hu0 : u ≠ 0 := by rintro rfl; simp at h
    have := minkB_neg_of_future hu hu0 h1
    rw [minkB_neg_right, minkB_comm] at this
    linarith

/-- **A criterion for `SO₀(1, d)`** (`mem_lorentz_of` for any future timelike `e`): a
`minkQ`-preserving automorphism of determinant `1` sending one future timelike vector to a future
timelike vector lies in `lorentz d`. -/
theorem mem_lorentz_of_future {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hQ : ∀ v, minkQ (A v) = minkQ v) {e : Minkowski d} (he : IsFutureTimelike e)
    (hAe : IsFutureTimelike (A e))
    (hdet : LinearMap.det (A : Minkowski d →ₗ[ℝ] Minkowski d) = 1) : A ∈ lorentz d := by
  refine ⟨hQ, fun v hv => ?_, hdet⟩
  have hq : minkQ (A v) ≤ 0 := by rw [hQ]; exact hv.2
  refine ⟨?_, hq⟩
  by_contra hneg
  push Not at hneg
  have hz : IsFutureCausal (-(A v)) := ⟨by simp; linarith, by simpa using hq⟩
  have hz0 : -(A v) ≠ 0 := fun h => by
    have : (A v).1 = 0 := by simpa using congrArg Prod.fst h
    linarith
  have h1 := minkB_neg_of_future hz hz0 hAe
  rw [minkB_neg_left, minkB_map hQ] at h1
  have h2 := minkB_le_zero_of_isFutureCausal hv ⟨he.1.le, he.2.le⟩
  linarith

/-- **Reverse Cauchy–Schwarz**: for `v` timelike, `|v|² |w|² ≤ ⟨v | w⟩²`. -/
theorem minkQ_mul_le_minkB_sq {v w : Minkowski d} (hv : minkQ v < 0) :
    minkQ v * minkQ w ≤ minkB v w ^ 2 := by
  have hv' : minkQ v ≠ 0 := hv.ne
  set t := minkB v w / minkQ v with ht
  set z := w - t • v with hz
  have hvz : minkB v z = 0 := by
    rw [hz, minkB_sub_right, minkB_smul_right, ← minkQ_eq_minkB, ht]; field_simp; ring
  have hzq : 0 ≤ minkQ z := by
    rcases eq_or_ne z 0 with h | h
    · rw [h, minkQ_zero]
    · exact (minkQ_pos_of_orth_timelike hv hvz h).le
  have e : minkQ z * minkQ v = minkQ w * minkQ v - minkB v w ^ 2 := by
    have : z = w + (-t) • v := by rw [hz, sub_eq_add_neg, neg_smul]
    rw [this, minkQ_add, minkQ_smul, minkB_smul_right, minkB_comm w v, ht]
    field_simp; ring
  nlinarith


/-- A quadratic polynomial `C + a t + b t²` with a local minimum at `0` has `a = 0`. -/
theorem quadratic_linCoeff_eq_zero {f : ℝ → ℝ} {C a b : ℝ} (hf : ∀ t, f t = C + a * t + b * t ^ 2)
    (hmin : IsLocalMin f 0) : a = 0 := by
  have hd : HasDerivAt f a 0 := by
    have h1 : HasDerivAt (fun t : ℝ => C + a * t + b * t ^ 2) (a * 1 + b * (2 * 0 ^ 1)) 0 :=
      (HasDerivAt.const_add C (HasDerivAt.const_mul a (hasDerivAt_id' (0 : ℝ)))).add
        (HasDerivAt.const_mul b (hasDerivAt_pow 2 (0 : ℝ)))
    have e : f = fun t : ℝ => C + a * t + b * t ^ 2 := funext hf
    rw [e]; simpa using h1
  exact hmin.hasDerivAt_eq_zero hd

/-- The future timelike cone `{x | IsFutureTimelike x}` is open. -/
theorem isOpen_futureTimelikeCone : IsOpen {x : Minkowski d | IsFutureTimelike x} :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_minkQ continuous_const)


/-- **A cone eigenvector, Brouwer-free.** An element of `SO₀(1, d)` has a nonzero null
eigenvector, or fixes a timelike vector. If it has no null eigenvector, `⟨A x | x⟩ < 0` on the
closed future cone, so `x ↦ |x|² / ⟨A x | x⟩` (homogeneous of degree `0`) is continuous on the
compact section `{x₀ = 1}` of the cone and attains its maximum `m > 0` at a timelike `v`. The first
variation at `v` (the cone is open there) gives `2 v = m (A v + A⁻¹ v)`, so `span {v, A v}` is
`A`-invariant; reverse Cauchy–Schwarz gives `m ≤ 1`; `m < 1` produces a null eigenvector in that
plane (excluded), and `m = 1` gives `A v = v`. -/
theorem lorentz.exists_null_eigen_or_fixed_timelike {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) :
    (∃ u : Minkowski d, u ≠ 0 ∧ minkQ u = 0 ∧ ∃ c : ℝ, A u = c • u) ∨
      ∃ v : Minkowski d, minkQ v < 0 ∧ A v = v := by
  by_cases hnull : ∃ u : Minkowski d, u ≠ 0 ∧ minkQ u = 0 ∧ ∃ c : ℝ, A u = c • u
  · exact Or.inl hnull
  right
  push Not at hnull
  have hQ := hA.1
  -- `D x = ⟨A x | x⟩ < 0` on the nonzero future causal vectors
  have hD : ∀ x, IsFutureCausal x → x ≠ 0 → minkB (A x) x < 0 := by
    intro x hx hx0
    have hAx := lorentz.isFutureCausal_apply hA hx
    have hAx0 : A x ≠ 0 := fun h => hx0 (A.injective (by rw [h, map_zero]))
    refine lt_of_le_of_ne (minkB_le_zero_of_isFutureCausal hAx hx) fun h0 => ?_
    by_cases hxq : minkQ x < 0
    · exact (minkB_neg_of_future hAx hAx0 (hx.isFutureTimelike_of_neg hxq)).ne h0
    · have hxq' : minkQ x = 0 := le_antisymm hx.2 (not_lt.1 hxq)
      obtain ⟨c, hc⟩ := eq_smul_of_null_orth hxq' hx0 (by rw [hQ, hxq'])
        (by rw [minkB_comm]; exact h0)
      exact hnull x hx0 hxq' c hc
  -- the compact section `K` of the closed future cone
  set K : Set (Minkowski d) := {x | x.1 = 1 ∧ minkQ x ≤ 0} with hKdef
  have hKf : ∀ x ∈ K, IsFutureCausal x ∧ x ≠ 0 := fun x hx =>
    ⟨⟨by rw [hx.1]; norm_num, hx.2⟩, fun h => by
      have := hx.1; rw [h] at this; simp at this⟩
  have hK : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_eq continuous_fst continuous_const).inter
        (isClosed_le continuous_minkQ continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      have h1 := minkQ_le_zero_iff.1 hx.2
      rw [hx.1] at h1
      refine max_le (by rw [hx.1]; simp) ?_
      nlinarith [norm_nonneg x.2]
  have hAc : Continuous A := (A : Minkowski d →ₗ[ℝ] Minkowski d).continuous_of_finiteDimensional
  have hDc : Continuous fun x : Minkowski d => minkB (A x) x := by
    unfold minkB
    exact ((continuous_fst.comp hAc).mul continuous_fst).neg.add
      ((continuous_snd.comp hAc).inner continuous_snd)
  set φ : Minkowski d → ℝ := fun x => minkQ x / minkB (A x) x with hφ
  have hφc : ContinuousOn φ K :=
    continuous_minkQ.continuousOn.div hDc.continuousOn fun x hx =>
      (hD x (hKf x hx).1 (hKf x hx).2).ne
  have hτK : timeUnit d ∈ K := ⟨rfl, by simp⟩
  obtain ⟨v, hvK, hvmax⟩ := hK.exists_isMaxOn ⟨_, hτK⟩ hφc
  set m := φ v with hm
  have hDv := hD v (hKf v hvK).1 (hKf v hvK).2
  have hm0 : 0 < m := by
    have h1 := isMaxOn_iff.1 hvmax _ hτK
    have h2 : 0 < φ (timeUnit d) := by
      simp only [hφ, minkQ_timeUnit]
      exact div_pos_of_neg_of_neg (by norm_num) (hD _ (hKf _ hτK).1 (hKf _ hτK).2)
    linarith
  have hvq : minkQ v < 0 := by
    rcases div_pos_iff.1 hm0 with h | h
    · exact absurd h.2 (not_lt.2 hDv.le)
    · exact h.1
  have hvF : IsFutureTimelike v := (hKf v hvK).1.isFutureTimelike_of_neg hvq
  have hmv : m * minkB (A v) v = minkQ v := div_mul_cancel₀ _ hDv.ne
  -- `m ⟨A x | x⟩ ≤ |x|²` on the closed future cone
  have hF : ∀ x, IsFutureCausal x → m * minkB (A x) x ≤ minkQ x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have hx1 : 0 < x.1 := lt_of_le_of_ne hx.1 fun h => hx0 (eq_zero_of_fst_eq_zero h.symm hx.2)
    set y := x.1⁻¹ • x with hy
    have hyK : y ∈ K := ⟨by simp [hy, hx1.ne'], by
      rw [hy, minkQ_smul]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hx.2⟩
    have hφy : φ y = φ x := by
      simp only [hφ, hy, map_smul, minkQ_smul, minkB_smul_left, minkB_smul_right]
      rw [← mul_assoc, ← pow_two]
      exact mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hx1.ne'))
    have h1 := isMaxOn_iff.1 hvmax y hyK
    rw [hφy] at h1
    exact (div_le_iff_of_neg (hD x hx hx0)).1 h1
  -- first variation at the maximum: `2 v = m (A v + A⁻¹ v)`
  have hvar : ∀ w, 2 * minkB v w - m * (minkB (A v) w + minkB (A w) v) = 0 := by
    intro w
    set f : ℝ → ℝ := fun t => minkQ (v + t • w) - m * minkB (A (v + t • w)) (v + t • w)
    have hf : ∀ t, f t = (minkQ v - m * minkB (A v) v) +
        (2 * minkB v w - m * (minkB (A v) w + minkB (A w) v)) * t +
        (minkQ w - m * minkB (A w) w) * t ^ 2 := fun t => by
      simp only [f, map_add, map_smul, minkQ_add, minkQ_smul, minkB_add_left, minkB_add_right,
        minkB_smul_left, minkB_smul_right]
      ring
    refine quadratic_linCoeff_eq_zero hf ?_
    have hcont : Continuous fun t : ℝ => v + t • w := by fun_prop
    have hev : ∀ᶠ t in nhds (0 : ℝ), v + t • w ∈ {x : Minkowski d | IsFutureTimelike x} :=
      hcont.continuousAt.eventually_mem (isOpen_futureTimelikeCone.mem_nhds (by simpa using hvF))
    refine hev.mono fun t ht => ?_
    have h0 : f 0 = 0 := by simp only [f, zero_smul, add_zero]; linarith
    have h1 := hF _ ⟨ht.1.le, ht.2.le⟩
    show f 0 ≤ f t
    rw [h0]; simp only [f]; linarith
  have hinv : ∀ w, minkB (A w) v = minkB w (A.symm v) := fun w => by
    conv_lhs => rw [← A.apply_symm_apply v]
    exact minkB_map hQ _ _
  have hkey : (2 : ℝ) • v = m • (A v + A.symm v) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_minkB fun w => ?_
    have := hvar w
    rw [hinv, minkB_comm v w, minkB_comm (A v) w] at this
    simp only [minkB_sub_right, minkB_smul_right, minkB_add_right]
    linarith
  -- reverse Cauchy–Schwarz: `m ≤ 1`
  have hrcs := minkQ_mul_le_minkB_sq (w := A v) hvq
  rw [hQ, minkB_comm] at hrcs
  have hm1 : m ≤ 1 := by
    by_contra h
    push Not at h
    have : minkQ v * minkQ v ≤ (minkQ v / m) ^ 2 := by
      rwa [show minkB (A v) v = minkQ v / m by field_simp; linarith] at hrcs
    rw [div_pow] at this
    have hq2 : 0 < minkQ v ^ 2 := by have := hvq.ne; positivity
    rw [le_div_iff₀ (pow_pos hm0 2)] at this
    have hm2 : 1 < m ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hm2 hq2]
  rcases hm1.lt_or_eq with hm1 | hm1
  · -- `m < 1`: a null eigenvector in the plane `span {v, A v}`, excluded
    exfalso
    set c := 2 / m with hc
    have hc2 : 2 < c := by rw [hc, lt_div_iff₀ hm0]; linarith
    have hAAv : A (A v) = c • A v - v := by
      have h1 := congrArg A hkey
      rw [map_smul, map_smul, map_add, A.apply_symm_apply] at h1
      rw [hc, eq_sub_iff_add_eq]
      have : A (A v) + v = (2 / m) • A v := by
        rw [div_eq_inv_mul, mul_smul, h1, smul_smul, inv_mul_cancel₀ hm0.ne', one_smul]
      exact this
    set s := Real.sqrt (c ^ 2 - 4) with hs
    have hs2 : s ^ 2 = c ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    set l := (c + s) / 2
    set μ := (c - s) / 2
    have hlμ : l * μ = 1 := by simp only [l, μ]; nlinarith
    have hl1 : 1 < l := by simp only [l]; linarith
    set u := A v - μ • v with hu
    have hAu : A u = l • u := by
      rw [hu, map_sub, map_smul, hAAv, smul_sub, smul_smul, hlμ, one_smul]
      have : l = c - μ := by simp only [l, μ]; ring
      rw [this, sub_smul]; abel
    have hu0 : u ≠ 0 := by
      intro h0
      have hAv : A v = μ • v := by rw [hu, sub_eq_zero] at h0; exact h0
      have h1 := hQ v
      rw [hAv, minkQ_smul] at h1
      have hμ2 : μ ^ 2 = 1 := by
        have : (μ ^ 2 - 1) * minkQ v = 0 := by linarith
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hvq.ne)
      have hμ0 : 0 < μ := by nlinarith
      nlinarith
    have huq : minkQ u = 0 := by
      have h1 := hQ u
      rw [hAu, minkQ_smul] at h1
      have : (l ^ 2 - 1) * minkQ u = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (by nlinarith)
    exact hnull u hu0 huq l hAu
  · -- `m = 1`: `A v = v`
    refine ⟨v, hvq, ?_⟩
    rw [hm1, one_mul] at hmv
    set w := A v - v with hw
    have hwq : minkQ w = 0 := by
      rw [hw, sub_eq_add_neg, minkQ_add, minkQ_neg, minkB_neg_right, hQ, hmv]; ring
    have hvw : minkB v w = 0 := by
      rw [hw, minkB_sub_right, minkB_comm, hmv, ← minkQ_eq_minkB, sub_self]
    by_contra hne
    have hw0 : w ≠ 0 := fun h => hne (sub_eq_zero.1 h)
    have := minkQ_pos_of_orth_timelike hvq hvw hw0
    linarith


/-- **A null eigenvector of eigenvalue `l ≠ 1` makes `A` loxodromic.** `A − l⁻¹` maps into
`u^⊥`, so it is not surjective, hence has a kernel: a second null eigenvector `u'` for `l⁻¹`, with
`⟨u | u'⟩ ≠ 0`. In the frame `e₀, e₁ = (u ± u'')/2` (`⟨u | u''⟩ = −2`) the boost `H` of rapidity
`log l` agrees with `A` on `span {e₀, e₁}` and commutes with `A`, and `R = A H⁻¹` fixes the
timelike `e₀`, hence is elliptic. -/
theorem isLoxodromic_of_null_eigen {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    {u : Minkowski d} (hu0 : u ≠ 0) (hq : minkQ u = 0) {l : ℝ} (hl : 0 < l) (hl1 : l ≠ 1)
    (hAu : A u = l • u) : IsLoxodromic A := by
  have hQ := hA.1
  have hl0 : l ≠ 0 := hl.ne'
  have hll : l * l ≠ 1 := fun h => hl1 (by nlinarith)
  have hll' : l⁻¹ * l⁻¹ ≠ 1 := by
    rw [← mul_inv]; intro h; exact hll (inv_eq_one.1 h)
  -- the second null eigenvector, for `l⁻¹`
  have hmB : ∀ w, minkB u (A w) = l⁻¹ * minkB u w := fun w => by
    have h1 := minkB_map hQ u w
    rw [hAu, minkB_smul_left] at h1
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
  set T : Minkowski d →ₗ[ℝ] Minkowski d :=
    (A : Minkowski d →ₗ[ℝ] Minkowski d) - l⁻¹ • LinearMap.id with hT
  have hTs : ¬ Function.Surjective T := by
    intro hs
    obtain ⟨w₀, hw₀⟩ : ∃ w, minkB u w ≠ 0 := by
      by_contra h; push Not at h
      exact hu0 (eq_zero_of_forall_minkB fun z => by rw [minkB_comm]; exact h z)
    obtain ⟨y, hy⟩ := hs w₀
    apply hw₀
    rw [← hy, hT, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, minkB_sub_right,
      minkB_smul_right, LinearEquiv.coe_coe, hmB, sub_self]
  have hTi : ¬ Function.Injective T := fun hi => hTs (LinearMap.injective_iff_surjective.1 hi)
  rw [injective_iff_map_eq_zero] at hTi
  push Not at hTi
  obtain ⟨u', hTu', hu'0⟩ := hTi
  have hAu' : A u' = l⁻¹ • u' := by
    rw [hT, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      sub_eq_zero] at hTu'
    exact hTu'
  have hq' : minkQ u' = 0 := by
    have h1 := hQ u'
    rw [hAu', minkQ_smul] at h1
    have : (l⁻¹ * l⁻¹ - 1) * minkQ u' = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hll')
  have hb : minkB u u' ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := eq_smul_of_null_orth hq hu0 hq' h0
    have h1 := hAu'
    rw [hc, map_smul, hAu, smul_smul, smul_smul] at h1
    have h2 : (c * l - l⁻¹ * c) • u = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · have hc0 : c = 0 := by
        have : c * (l - l⁻¹) = 0 := by linear_combination h3
        refine (mul_eq_zero.1 this).resolve_right fun h4 => hll ?_
        have : l = l⁻¹ := sub_eq_zero.1 h4
        calc l * l = l * l⁻¹ := by rw [← this]
          _ = 1 := mul_inv_cancel₀ hl0
      exact hu'0 (by rw [hc, hc0, zero_smul])
    · exact hu0 h3
  -- the null frame, normalised by `⟨u | u''⟩ = −2`
  set b := minkB u u' with hbdef
  set u'' := (-2 / b) • u' with hu''
  have hq'' : minkQ u'' = 0 := by rw [hu'', minkQ_smul, hq', mul_zero]
  have hb'' : minkB u u'' = -2 := by rw [hu'', minkB_smul_right, ← hbdef]; field_simp
  have hAu'' : A u'' = l⁻¹ • u'' := by rw [hu'', map_smul, hAu', smul_comm]
  obtain ⟨e₀, he₀⟩ : ∃ e : Minkowski d, e = (1 / 2 : ℝ) • (u + u'') := ⟨_, rfl⟩
  obtain ⟨e₁, he₁⟩ : ∃ e : Minkowski d, e = (1 / 2 : ℝ) • (u - u'') := ⟨_, rfl⟩
  have h0 : minkQ e₀ = -1 := by
    rw [he₀, minkQ_smul, minkQ_add, hq, hq'', hb'']; ring
  have h1 : minkQ e₁ = 1 := by
    rw [he₁, minkQ_smul, sub_eq_add_neg, minkQ_add, minkQ_neg, minkB_neg_right, hq, hq'', hb'']
    ring
  have h01 : minkB e₀ e₁ = 0 := by
    rw [he₀, he₁, minkB_smul_left, minkB_smul_right, minkB_add_left, minkB_sub_right,
      minkB_sub_right, ← minkQ_eq_minkB, ← minkQ_eq_minkB, hq, hq'', minkB_comm u'' u]; ring
  set ζ := Real.log l with hζdef
  have hexp : Real.exp ζ = l := Real.exp_log hl
  have hch : Real.cosh ζ = (l + l⁻¹) / 2 := by rw [Real.cosh_eq, Real.exp_neg, hexp]
  have hsh : Real.sinh ζ = (l - l⁻¹) / 2 := by rw [Real.sinh_eq, Real.exp_neg, hexp]
  have hζ : ζ ≠ 0 := fun h => hl1 (by rw [← hexp, h, Real.exp_zero])
  have hAe₀ : A e₀ = Real.cosh ζ • e₀ + Real.sinh ζ • e₁ := by
    rw [he₀, he₁, map_smul, map_add, hAu, hAu'', hch, hsh]; module
  have hAe₁ : A e₁ = Real.sinh ζ • e₀ + Real.cosh ζ • e₁ := by
    rw [he₀, he₁, map_smul, map_sub, hAu, hAu'', hch, hsh]; module
  -- the boost
  obtain ⟨H, hH⟩ : ∃ H : Minkowski d ≃ₗ[ℝ] Minkowski d, H = boost h0 h1 h01 ζ := ⟨_, rfl⟩
  have hQH : ∀ v, minkQ (H v) = minkQ v := fun v => by
    rw [hH]; exact minkQ_boostLin h0 h1 h01 ζ v
  have h0' : minkB e₀ e₀ = -1 := by rw [← minkQ_eq_minkB, h0]
  have h1' : minkB e₁ e₁ = 1 := by rw [← minkQ_eq_minkB, h1]
  have hHe₀ : H e₀ = Real.cosh ζ • e₀ + Real.sinh ζ • e₁ := by
    rw [hH, boost_apply, boostLin_apply, h0', h01]; module
  have hHyp : IsHyperbolic H := by rw [hH]; exact isHyperbolic_boost h0 h1 h01 hζ
  have hHmem : H ∈ lorentz d := by
    have hdet : LinearMap.det (H : Minkowski d →ₗ[ℝ] Minkowski d) = 1 :=
      det_eq_one_of_eq_sq (B := boostLin e₀ e₁ (ζ / 2)) hQH
        (by rw [boostLin_comp h0 h1 h01, add_halves, hH]; rfl)
    have hHB : minkB (H e₀) e₀ < 0 := by
      rw [hHe₀, minkB_add_left, minkB_smul_left, minkB_smul_left, h0', minkB_comm, h01]
      have := Real.cosh_pos ζ
      linarith
    rcases isFutureTimelike_or_neg (show minkQ e₀ < 0 by rw [h0]; norm_num) with he | he
    · exact mem_lorentz_of_future hQH he
        (isFutureTimelike_of_minkB_neg (by rw [hQH, h0]; norm_num) ⟨he.1.le, he.2.le⟩ hHB) hdet
    · refine mem_lorentz_of_future hQH he
        (isFutureTimelike_of_minkB_neg (by rw [hQH, minkQ_neg, h0]; norm_num)
          ⟨he.1.le, he.2.le⟩ ?_) hdet
      rw [map_neg, minkB_neg_left, minkB_neg_right, neg_neg]; exact hHB
  -- `A` commutes with the boost
  have hcomm : ∀ x, A (H x) = H (A x) := by
    intro x
    have ha := minkB_map hQ x e₀
    have hb := minkB_map hQ x e₁
    rw [hAe₀, minkB_add_right, minkB_smul_right, minkB_smul_right] at ha
    rw [hAe₁, minkB_add_right, minkB_smul_right, minkB_smul_right] at hb
    have hcs := Real.cosh_sq_sub_sinh_sq ζ
    have ha' : minkB (A x) e₀ = Real.cosh ζ * minkB x e₀ - Real.sinh ζ * minkB x e₁ := by
      linear_combination Real.cosh ζ * ha - Real.sinh ζ * hb - minkB (A x) e₀ * hcs
    have hb' : minkB (A x) e₁ = Real.cosh ζ * minkB x e₁ - Real.sinh ζ * minkB x e₀ := by
      linear_combination Real.cosh ζ * hb - Real.sinh ζ * ha - minkB (A x) e₁ * hcs
    rw [hH, boost_apply, boost_apply, boostLin_apply, boostLin_apply, map_add, map_add, map_smul,
      map_smul, hAe₀, hAe₁, ha', hb']
    module
  have hc : A * H = H * A := LinearEquiv.ext fun x => hcomm x
  set R := A * H⁻¹ with hR
  have hRmem : R ∈ lorentz d := (lorentz d).mul_mem hA ((lorentz d).inv_mem hHmem)
  have hRe₀ : R e₀ = e₀ := by
    have hc' : A * H⁻¹ = H⁻¹ * A := (Commute.inv_right hc)
    rw [hR, hc', LinearEquiv.mul_apply, hAe₀, ← hHe₀, ← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  refine ⟨R, H, hRmem, hHmem, isElliptic_of_fixed_timelike hRmem.1 (by rw [h0]; norm_num) hRe₀,
    hHyp, (inv_mul_cancel_right A H).symm, ?_⟩
  rw [hR, inv_mul_cancel_right, ← mul_assoc, ← hc, mul_inv_cancel_right]


/-- **A fixed null vector makes `A` elliptic or parabolic.** Fitting decomposition of
`p = A − id`: `M = ker pᴺ ⊕ Im pᴺ`, the two summands are `minkB`-orthogonal (the adjoint of `p`
is `−A⁻¹ p`) and `A`-invariant. `U = A` on `ker pᴺ`, `id` on `Im pᴺ` is unipotent, preserves
`minkQ`, has determinant `1` (it is the square of `1 + p_U/2 − p_U²/8`, `p_U³ = 0`) and fixes the
future null vector, hence lies in `SO₀(1, d)`; `R = A U⁻¹` is `id` on `ker pᴺ`, which is
nondegenerate and contains the fixed null vector, hence a timelike vector: `R` is elliptic. Then
`A = R U = U R`, parabolic if `U ≠ id`, elliptic otherwise. This is the multiplicative
Jordan–Chevalley decomposition restricted to the eigenvalue `1`, without the uniqueness of the
decomposition. -/
theorem isElliptic_or_isParabolic_of_null_fixed {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) {u : Minkowski d} (hu0 : u ≠ 0) (hq : minkQ u = 0) (hAu : A u = u) :
    IsElliptic A ∨ IsParabolic A := by
  have hQ := hA.1
  -- a future representative of the fixed null line
  obtain ⟨uf, huf0, hufF, hufq, hAuf⟩ : ∃ uf : Minkowski d, uf ≠ 0 ∧ IsFutureCausal uf ∧
      minkQ uf = 0 ∧ A uf = uf := by
    have hu1 : u.1 ≠ 0 := fun h => hu0 (eq_zero_of_fst_eq_zero h hq.le)
    rcases lt_or_gt_of_ne hu1 with h | h
    · exact ⟨-u, neg_ne_zero.2 hu0, ⟨by simp; linarith, by simp [hq]⟩, by simp [hq],
        by rw [map_neg, hAu]⟩
    · exact ⟨u, hu0, ⟨h.le, hq.le⟩, hq, hAu⟩
  -- the Fitting decomposition of `p = A − id`
  set p := pOf A with hp
  obtain ⟨N, hN, hN1⟩ := ((LinearMap.eventually_isCompl_ker_pow_range_pow p).and
    (Filter.eventually_ge_atTop 1)).exists
  set G := LinearMap.ker (p ^ N) with hG
  set G' := LinearMap.range (p ^ N) with hG'
  have hpA : ∀ x, p (A x) = A (p x) := fun x => by simp [hp, pOf_apply]
  have hpowA : ∀ k x, (p ^ k) (A x) = A ((p ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, hpA]
  have hGA : ∀ g ∈ G, A g ∈ G := fun g hg => by
    rw [hG, LinearMap.mem_ker] at hg ⊢; rw [hpowA, hg, map_zero]
  have hG'A : ∀ g ∈ G', A g ∈ G' := by
    rintro _ ⟨z, rfl⟩; exact ⟨A z, hpowA N z⟩
  have hGp : ∀ g ∈ G, p g ∈ G := fun g hg => by
    rw [hG, LinearMap.mem_ker] at hg ⊢
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hg, map_zero]
  have hufG : uf ∈ G := by
    rw [hG, LinearMap.mem_ker]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN1
    rw [pow_succ, Module.End.mul_apply, show p uf = 0 by simp [hp, pOf_apply, hAuf], map_zero]
  -- `ker pᴺ ⊥ Im pᴺ`: the `minkB`-adjoint of `p` is `−A⁻¹ p`
  have hpinv : ∀ y, p (A.symm y) = A.symm (p y) := fun y => by
    simp [hp, pOf_apply]
  have hpowinv : ∀ k y, (p ^ k) (A.symm y) = A.symm ((p ^ k) y) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y; rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, hpinv]
  have hadj : ∀ x z, minkB x (p z) = -minkB (A.symm (p x)) z := fun x z => by
    have h1 : minkB x (A z) = minkB (A.symm x) z := by
      conv_lhs => rw [← A.apply_symm_apply x]
      exact minkB_map hQ _ _
    rw [hp, pOf_apply, pOf_apply, map_sub, LinearEquiv.symm_apply_apply, minkB_sub_right,
      minkB_sub_left, h1]
    ring
  have horth_aux : ∀ k x, (p ^ k) x = 0 → ∀ z, minkB x ((p ^ k) z) = 0 := by
    intro k
    induction k with
    | zero => intro x hx z; rw [pow_zero] at hx; rw [show x = 0 from hx, minkB_zero_left]
    | succ k ih =>
      intro x hx z
      rw [pow_succ', Module.End.mul_apply, hadj, ih (A.symm (p x)) ?_ z, neg_zero]
      rw [hpowinv, ← Module.End.mul_apply, ← pow_succ, hx, map_zero]
  have horth : ∀ g ∈ G, ∀ g' ∈ G', minkB g g' = 0 := by
    rintro g hg _ ⟨z, rfl⟩; exact horth_aux N g hg z
  have hdec : ∀ x, ∃ g ∈ G, ∃ g' ∈ G', x = g + g' := fun x => by
    have : x ∈ G ⊔ G' := by rw [hN.sup_eq_top]; exact mem_top
    obtain ⟨g, hg, g', hg', h⟩ := mem_sup.1 this
    exact ⟨g, hg, g', hg', h.symm⟩
  -- `U = A` on `ker pᴺ`, `id` on `Im pᴺ`
  set U₀ : Minkowski d →ₗ[ℝ] Minkowski d :=
    LinearMap.ofIsCompl hN ((A : Minkowski d →ₗ[ℝ] Minkowski d) ∘ₗ G.subtype) G'.subtype
    with hU₀def
  have hU₀ : ∀ g ∈ G, ∀ g' ∈ G', U₀ (g + g') = A g + g' := by
    intro g hg g' hg'
    have e1 := LinearMap.ofIsCompl_apply_left hN
      (φ := (A : Minkowski d →ₗ[ℝ] Minkowski d) ∘ₗ G.subtype) (ψ := G'.subtype) ⟨g, hg⟩
    have e2 := LinearMap.ofIsCompl_apply_right hN
      (φ := (A : Minkowski d →ₗ[ℝ] Minkowski d) ∘ₗ G.subtype) (ψ := G'.subtype) ⟨g', hg'⟩
    rw [map_add, hU₀def, e1, e2]
    rfl
  have hU₀G : ∀ g ∈ G, U₀ g = A g := fun g hg => by
    simpa using hU₀ g hg 0 (zero_mem _)
  have hQU : ∀ x, minkQ (U₀ x) = minkQ x := fun x => by
    obtain ⟨g, hg, g', hg', rfl⟩ := hdec x
    rw [hU₀ g hg g' hg', minkQ_add, minkQ_add, hQ, horth g hg g' hg', horth _ (hGA g hg) g' hg']
  have hinj : Function.Injective U₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine eq_zero_of_forall_minkB fun z => ?_
    rw [← minkB_map_of_minkQ hQU z x, hx, minkB_zero_right]
  set U := LinearEquiv.ofInjectiveEndo U₀ hinj with hUdef
  have hUapp : ∀ x, U x = U₀ x := fun x => rfl
  have hQU' : ∀ x, minkQ (U x) = minkQ x := hQU
  have hpU : ∀ g ∈ G, pOf U g = p g := fun g hg => by
    rw [pOf_apply, hUapp, hU₀G g hg, hp, pOf_apply]
  have hpU' : ∀ g ∈ G, ∀ g' ∈ G', pOf U (g + g') = p g := fun g hg g' hg' => by
    rw [pOf_apply, hUapp, hU₀ g hg g' hg', hp, pOf_apply]; abel
  -- `U` is unipotent
  have hpowU : ∀ k, ∀ g ∈ G, (pOf U ^ k) g = (p ^ k) g := by
    intro k
    induction k with
    | zero => intro g _; rfl
    | succ k ih =>
      intro g hg
      rw [pow_succ, Module.End.mul_apply, hpU g hg, ih _ (hGp g hg), pow_succ,
        Module.End.mul_apply]
  have hnil : IsNilpotent (pOf U) := by
    refine ⟨N + 1, LinearMap.ext fun x => ?_⟩
    obtain ⟨g, hg, g', hg', rfl⟩ := hdec x
    rw [pow_succ, Module.End.mul_apply, hpU' g hg g' hg', hpowU N _ (hGp g hg),
      ← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply,
      show (p ^ N) g = 0 from hg, map_zero, LinearMap.zero_apply]
  -- `det U = 1`: `U` is the square of `1 + p_U/2 − p_U²/8`
  have h3 : ∀ x, pOf U (pOf U (pOf U x)) = 0 := fun x => by
    by_cases hp0 : pOf U = 0
    · simp [hp0]
    · exact pOf_pOf_pOf hQU' hnil hp0 x
  set B : Minkowski d →ₗ[ℝ] Minkowski d :=
    LinearMap.id + (1 / 2 : ℝ) • pOf U - (1 / 8 : ℝ) • (pOf U ∘ₗ pOf U) with hB
  have hBB : (U : Minkowski d →ₗ[ℝ] Minkowski d) = B ∘ₗ B := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.coe_coe, apply_eq_add_pOf U x]
    simp only [hB, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_add, map_sub, map_smul, h3, map_zero,
      smul_zero, sub_zero]
    module
  have hdet : LinearMap.det (U : Minkowski d →ₗ[ℝ] Minkowski d) = 1 :=
    det_eq_one_of_eq_sq hQU' hBB
  -- `U` preserves the future cone (it fixes `uf`)
  have hτ : IsFutureTimelike (timeUnit d) := ⟨by simp [timeUnit], by simp⟩
  have hUuf : U uf = uf := by rw [hUapp, hU₀G uf hufG, hAuf]
  have hUτ : IsFutureTimelike (U (timeUnit d)) := by
    refine isFutureTimelike_of_minkB_neg (by rw [hQU', minkQ_timeUnit]; norm_num) hufF ?_
    conv_lhs => rw [← hUuf]
    rw [minkB_map hQU', minkB_comm]
    exact minkB_neg_of_future hufF huf0 hτ
  have hUmem : U ∈ lorentz d := mem_lorentz_of_future hQU' hτ hUτ hdet
  -- `A` and `U` commute
  have hcomm : A * U = U * A := by
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨g, hg, g', hg', rfl⟩ := hdec x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hUapp, hUapp, hU₀ g hg g' hg', map_add,
      map_add, hU₀ _ (hGA g hg) _ (hG'A g' hg')]
  -- a timelike vector in `ker pᴺ`
  obtain ⟨z, hzG, hzq⟩ : ∃ z ∈ G, minkQ z < 0 := by
    obtain ⟨y, hy⟩ : ∃ y, minkB uf y ≠ 0 := by
      by_contra h; push Not at h
      exact huf0 (eq_zero_of_forall_minkB fun z => by rw [minkB_comm]; exact h z)
    obtain ⟨g, hg, g', hg', rfl⟩ := hdec y
    rw [minkB_add_right, horth uf hufG g' hg', add_zero] at hy
    refine ⟨(1 + minkQ g / 2) • uf + (-minkB uf g) • g, add_mem (smul_mem _ _ hufG)
      (smul_mem _ _ hg), ?_⟩
    rw [minkQ_add, minkQ_smul, minkQ_smul, minkB_smul_left, minkB_smul_right, hufq]
    have : 0 < minkB uf g ^ 2 := by positivity
    nlinarith
  -- `R = A U⁻¹` fixes the timelike `A z`
  set R := A * U⁻¹ with hR
  have hRmem : R ∈ lorentz d := (lorentz d).mul_mem hA ((lorentz d).inv_mem hUmem)
  have hRfix : R (A z) = A z := by
    have h1 : R (U z) = A z := by
      rw [hR, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply U⁻¹, inv_mul_cancel]; rfl
    rwa [hUapp, hU₀G z hzG] at h1
  have hRe : IsElliptic R := isElliptic_of_fixed_timelike hRmem.1 (by rw [hQ]; exact hzq) hRfix
  by_cases hU1 : U = 1
  · left
    have : R = A := by rw [hR, hU1, inv_one, mul_one]
    rw [← this]; exact hRe
  · right
    refine ⟨R, U, hRmem, hUmem, hRe, hnil, hU1, (inv_mul_cancel_right A U).symm, ?_⟩
    rw [hR, inv_mul_cancel_right, ← mul_assoc, ← hcomm, mul_inv_cancel_right]

/-- **"Up to conjugacy, every isometry is of the following form"** (l.1868–1901), on linear
parts: every element of `SO₀(1, d)` is elliptic, loxodromic or parabolic (and exactly one, by
`IsLoxodromic.not_isElliptic`, `IsParabolic.not_isElliptic`, `IsParabolic.not_isLoxodromic`).
Brouwer-free: a nonzero null eigenvector or a fixed timelike vector
(`lorentz.exists_null_eigen_or_fixed_timelike`); a fixed timelike vector is elliptic
(`isElliptic_of_fixed_timelike`); a null eigenvalue `l > 0` (`lorentz.eigen_pos_of_null`) with
`l ≠ 1` is loxodromic (`isLoxodromic_of_null_eigen`), with `l = 1` elliptic or parabolic
(`isElliptic_or_isParabolic_of_null_fixed`). The proof is uniform in `d`, no dimension being
excluded or treated apart; for `d ≤ 1` the parabolic alternative is empty
(`two_le_of_unipotent`). -/
theorem lorentz_trichotomy {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d) :
    IsElliptic A ∨ IsLoxodromic A ∨ IsParabolic A := by
  rcases lorentz.exists_null_eigen_or_fixed_timelike hA with ⟨u, hu0, hq, c, hc⟩ | ⟨v, hv, hAv⟩
  · have hc0 := lorentz.eigen_pos_of_null hA hu0 hq hc
    by_cases hc1 : c = 1
    · rw [hc1, one_smul] at hc
      rcases isElliptic_or_isParabolic_of_null_fixed hA hu0 hq hc with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (isLoxodromic_of_null_eigen hA hu0 hq hc0 hc1 hc))
  · exact Or.inl (isElliptic_of_fixed_timelike hA.1 hv hAv)

end Causal.Flat
