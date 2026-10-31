import CausalScaffold.Flat.Quotient
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# `CausalScaffold.Flat.TwistedProduct` — linear twisted products (Barbot §5.S, Lemma 5.5)

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5.S
"Twisted product by euclidean manifolds" (`produi`) and Lemma 5.5. Line numbers are those of the
**labelled** `papers/barbot/legacy/labeled/GHFspace.tex` (`docs/BARBOT.md` uses the original's).

* `blem:suspendre` — `GHFspace.tex:1833–1845` — **partial** (not marked): proved
  (`suspendre`) under one added hypothesis, `RestrictsIn` (every element of `Γ` restricts to `U`
  as an element of `Isom(𝐌^{d₁+1})`, i.e. preserves the orientation of `U`), without which the
  statement is false as written (`TwistedProduct.not_restrictsIn_glideGroup`, and for every
  parametrization of `U`, `TwistedProduct.not_restrictsIn_glideGroup_of_range`; DEC-27); `U` is
  given through an orthochronous parametrization `ι`.
* §5.S (prose, l.1751–1797) — the notion **linear twisted product** in the quotient form of
  `docs/BARBOT-THEOREMS.md` §1: `IsLTPOver`, `IsLTPData`.
* Rem 5.3 (prose, l.1800–1814), causal half, **linear twisted products only** (the remark is
  about twisted products by all euclidean manifolds, flat tori included) — stated
  (`gh_of_isLTPOver`, one `sorry`); its linear core is proved (`coproj_isFutureCausal`,
  `retract_le_top`). Rem 5.4 (l.1816–1828) is about Bieberbach and finite index, not causal: not
  attempted.

> Let $B$ be a flat spacetime, quotient of an open subset $\Omega$ of \mink by a group of
> isometries acting freely and properly discontinuously. Assume that $\Gamma$ preserves a timelike
> affine subspace $\bf U$, and that $\Omega$ is invariant by translations by vectors contained in
> the orthogonal linear space ${\bf U}^{\perp}$. Then, the quotient of ${\bf U} \cap \Omega$ by
> $\Gamma$ is a flat spacetime $M$, and $B$ is the linear twisted product of $M$ by the euclidean
> space ${\bf U}^{\perp}$. (l.1836–1844)

> The following lemma will be useful to recognize twisted products, and its proof should be
> obvious to the reader: (l.1830–1831)

> It should be clear to the reader that a similar procedure can be defined when $M$ is a flat
> lorentzian manifold; the result is then a canonical flat lorentzian structure on $B$, which is
> called once more \emph{the twisted product of $M$ by the euclidean manifold $N$, with monodromy
> $r$.\/} When $N$ is an euclidean linear space and $r$ takes value in linear isometries (i.e.,
> $r(\Gamma)$ admits a global fixed point in $N$), then we say that $B$ is a \emph{linear twisted
> product over $M$.} (l.1789–1797)

> If $t: M \rightarrow {\mathbb R}$ is a proper time function expressing $M$ as a GH spacetime,
> the composition $t \circ q$ satisfies the same properties. Hence, \emph{the twisted products by
> euclidean manifolds of flat GH spacetimes are still flat GH spacetimes.\/} (l.1801–1805)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's `n` is `d + 1`; the subspace
`U` has dimension `d₁ + 1` and `U^⊥` dimension `d − d₁`.

## What is proved

* **Timelike affine subspaces and their parametrizations.** `IsTimelikeSubspace U` (the direction
  contains `v` with `minkQ v < 0`); `AffineMinkEmbedding d₁ d` (an affine map whose linear part
  preserves `minkQ`): `injective`, `continuous`, `minkB_lin` (polarization), its image
  `range` is timelike (`timelikeImage`, automatic); `Orthochronous`. **Conversely** every
  timelike affine subspace is such a range with `ι` orthochronous
  (`exists_affineMinkEmbedding_of_isTimelike`: a **future** unit timelike vector of the direction
  and a `minkB`-orthonormal basis of its euclidean orthogonal, by
  `LinearMap.BilinForm.exists_orthogonal_basis`), so reading `U` as `range ι`, `ι` orthochronous,
  loses nothing.
* **`U^⊥` and the projection.** `perp` (`minkB`-orthogonal to the direction of `U`), closed under
  the vector operations, closed; `coproj` (the `minkB`-adjoint `P` of `ι.lin`, by Riesz on the
  spatial part: `minkB (P v) u = minkB v (ι.lin u)`), `coproj_lin`, `coproj_eq_zero_of_mem_perp`,
  `sub_lin_coproj_mem_perp`, `lin_mem_perp_iff` (`U^⊥ ∩ (U − U) = 0`); **`U^⊥` is euclidean**
  (`minkQ_pos_of_mem_perp`: `minkQ > 0` off `0`, because `U` is timelike).
* **The splitting `𝐌ⁿ ≅ 𝐌^{d₁+1} × U^⊥`.** `retract` (`q`, the foot on `U` along `U^⊥`),
  `retract_apply_add`, `split` (a homeomorphism, `p ↦ (q p, p − ι(q p))`), and
  `mem_iff_retract_mem`: under the `U^⊥`-invariance, **`Ω = (U ∩ Ω) × U^⊥`**.
* **Restriction to `U`.** `Restricts ι γ g` (`ι ∘ g = γ ∘ ι`), unique, multiplicative;
  `Restricts.lin`; the monodromy `L(γ)|_{U^⊥}` is linear (`linear_mem_perp`; `L(γ) ∈ SO₀(1,d)`
  preserves `minkQ`, so it is a linear isometry of the euclidean `U^⊥`: Barbot's `r`, fixed point
  `0`); `smul_apply_add`, `retract_smul` and `split_smul` (**`γ` acts on `𝐌^{d₁+1} × U^⊥`
  diagonally by `(g, L(γ)|_{U^⊥})`**); `RestrictsIn Γ` and `RestrictsIn.preserves`;
  `restrictGroup Γ` (the subgroup of `Isom(𝐌^{d₁+1})` of restrictions), `preimageOpens Ω`
  (`U ∩ Ω` read in `𝐌^{d₁+1}`), with the instances `Invariant`, `IsCancelSMul` (free) and
  `ProperlyDiscontinuousSMul` inherited from `Γ`, and `connectedSpace_base`.
* **Lemma 5.5** (`suspendre`): `IsLTPOver B (ι.baseSpacetime B hB hres hperp)`, for `ι`
  orthochronous (`IsLTPData.orthochronous`: `M₁` carries the time orientation `B` induces on `U`).
* **Rem 5.3, linear core**: `coproj_isFutureCausal`, `retract_le_top` — for orthochronous `ι`
  the retraction is a causal map `𝐌ⁿ → 𝐌^{d₁+1}` (Pythagoras with the spacelike `U^⊥`).
* **Non-vacuity** (kb/0011): `isLTPOver_refl` (`ι = id`, every quotient over itself),
  `isLTPOver_refl_minkowski`; `isLTPOver_bot_timeAxis` (a product, `Γ` trivial, over the time
  axis `timeAxis`); `isLTPOver_timeGroup` (`ℤ e₀\𝐌ⁿ` over the timelike circle, `Γ ≠ 1`).
* **The counterexample** `TwistedProduct.not_restrictsIn_glideGroup`: in `𝐌³` the glide
  `γ(t, x) = (t + 1, −x)` (`glide ∈ Isom(𝐌³)`, determinant `1`) generates a free, properly
  discontinuous group (instances proved) on `Ω = 𝐌³`, preserving the timelike plane `U = {x₂ = 0}`,
  whose generator restricts to `U` as `(t, x) ↦ (t + 1, −x)`, of determinant `−1`
  (`not_restricts_glide`): not in `Isom(𝐌²)`, and `Γ\U` is a non-orientable Möbius strip. The
  refutation is independent of the parametrization (`not_restricts_glide_of_range`,
  `not_restrictsIn_glideGroup_of_range`: through any `ι'` with image `U` the restriction is
  linearly conjugate to the flip, so its determinant is `−1`).

## Hypothesis checklist (`blem:suspendre`)

| paper | here |
|---|---|
| `B` a flat spacetime (l.1836) | ✓ carried: `B : FlatSpacetime d` |
| quotient of an open `Ω` by isometries acting freely and properly discontinuously (l.1837–1838) | ✓ carried: `IsQuotientOf B Γ Ω`, `[Invariant Γ Ω]`, `[IsCancelSMul Γ Ω]`, `[ProperlyDiscontinuousSMul Γ Ω]` |
| `Γ` preserves a timelike affine subspace `U` (l.1839) | ⚠ strengthened: `RestrictsIn ι Γ` (restriction in `SO₀`-affine isometries, i.e. `Γ` preserves the orientation of `U`); implies the preservation (`RestrictsIn.preserves`); necessary (`not_restrictsIn_glideGroup_of_range`, every parametrization). `U` is read as `range ι`, `ι : AffineMinkEmbedding d₁ d` orthochronous (`hι`); this loses no timelike affine subspace (`timelikeImage`, `exists_affineMinkEmbedding_of_isTimelike`) |
| `Ω` invariant by translations by `U^⊥` (l.1840–1841) | ✓ carried: `∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω` (`perpInvariant_iff`: the form `Ω + w = Ω`) |

Note (not a paper hypothesis): `Ω` is not asked to be connected; `M` is connected because `B` is
(`connectedSpace_base`).

## SCOPE (disclosed)

* **The orientation of `U`** (finding). Barbot's isometries are `SO₀`-affine (l.469–480), and a
  flat spacetime is an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold; `γ ∈ SO₀(1, d)` preserving `U` restricts to `U`
  in `O⁺(1, d₁)` only, with determinant `±1` (the same sign as on `U^⊥`). So the "flat spacetime
  `M`" of l.1842–1843 exists in Barbot's sense only when `Γ` preserves the orientation of `U`, which
  holds after passing to a subgroup of index `≤ 2` (consistent with Theorem A's "up to finite
  coverings"). `IsLTPData` therefore carries `restricts` beside BARBOT-THEOREMS §1's sketch, which
  needs it to define `Γ.restrict ι` as a subgroup of `isom d₁`. That the Möbius strip `Γ\U` carries
  **no** `(Isom(𝐌²), 𝐌²)`-structure (non-orientability) is not formalized; what is proved is that
  the restriction is not in `Isom(𝐌²)`.
* **`U` through `ι`, and orientations.** The paper's `U` is an affine subspace; here it is
  `range ι`. Every such range is a timelike affine subspace (`timelikeImage`), and conversely every
  timelike affine subspace is a range with `ι` orthochronous
  (`exists_affineMinkEmbedding_of_isTimelike`, proved). `IsLTPData` asks `ι` orthochronous:
  without it a time-reversing `ι` (e.g. `(t, x) ↦ (−t, x)`, `Γ = 1`, `Ω = {t > 0}`) would make
  `{t > 0}` "a linear twisted product over" `{t < 0}`, its time reverse, which is not isometric to
  it as a time-oriented flat spacetime (future-complete against past-complete). The *spatial*
  orientation of `ι` is not asked: it is not canonical (it depends on an orientation of `U^⊥`), and `RestrictsIn` (orientation of `U` preserved by `Γ`) does not depend
  on it. That `RestrictsIn` does not depend on the choice of `ι` for a given `U` is not proved in
  general (it is for the counterexample, `not_restrictsIn_glideGroup_of_range`).
* **The quotient form.** `IsLTPOver` is BARBOT-THEOREMS §1's quotient form (adopted by DEC-43's
  reading R1), not §5.S's suspension of `M̃ × N` by `π₁(M)`: the base is `Γ_U\(U ∩ Ω)`, and
  `U ∩ Ω` need not be the universal cover of `M`, nor `Γ_U` its fundamental group. The suspension
  structure is proved at the level of `Ω` (`split`, `split_smul`, `mem_iff_retract_mem`) and not
  descended to a fibre-bundle map `q : B → M` (only its continuity and surjectivity, inside
  `connectedSpace_base`). `restrictGroup Γ` is the image of `Γ`; the injectivity of `γ ↦ g`
  (true when `U ∩ Ω ≠ ∅`, by freeness) is not stated.
* **`U^⊥`-invariance of `Ω` (BARBOT-THEOREMS §6, G6)** is *carried* here as the hypothesis
  `perp_invariant`; its proof for the domains `Ω(S̃)` where Lemma 5.5 is applied is owed
  downstream, not discharged in this file.
* **Rem 5.3** (`gh_of_isLTPOver`) is stated for *linear* twisted products only (the remark covers
  twisted products by every euclidean manifold, flat tori included), and rests on a tagged
  `sorry`: the causality of `Γ\Ω` is not available (`Flat.Quotient`'s SCOPE), and comparing `≤_Ω`
  with `≤_{U∩Ω}` along the retraction needs the image of a causal curve (a graph over the time of
  `𝐌ⁿ`) reparametrized as a graph over the time of `𝐌^{d₁+1}`. Its linear core, the causality of
  the retraction for orthochronous `ι`, is proved. Rem 5.3's Cauchy-completeness half (D, DEC-35) and Rem 5.4 are not attempted.
* Generic `minkB` algebra is `private` (`tp_…`), to avoid colliding with `Flat/AchronalDomains`;
  it duplicates `Flat/Isometries`' public `minkB` lemmas and `minkForm` (`tpBilinOn` is `minkForm`
  restricted to `W`). `Flat/Isometries` is deliberately not imported: it is being edited in
  parallel, and the import closure is kept to `Flat.Quotient`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 2, package WP-31d-TwistedProduct.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Function

universe u v

variable {d d₁ : ℕ}

/-! ### The bilinear form (private helpers) -/

private theorem tp_minkB_add_left (v v' w : Minkowski d) :
    minkB (v + v') w = minkB v w + minkB v' w := by
  simp only [minkB, Prod.fst_add, Prod.snd_add, inner_add_left]; ring

private theorem tp_minkB_add_right (v w w' : Minkowski d) :
    minkB v (w + w') = minkB v w + minkB v w' := by
  simp only [minkB, Prod.fst_add, Prod.snd_add, inner_add_right]; ring

private theorem tp_minkB_smul_left (c : ℝ) (v w : Minkowski d) :
    minkB (c • v) w = c * minkB v w := by
  simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_left]; ring

private theorem tp_minkB_smul_right (c : ℝ) (v w : Minkowski d) :
    minkB v (c • w) = c * minkB v w := by
  simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]; ring

private theorem tp_minkB_neg_left (v w : Minkowski d) : minkB (-v) w = -minkB v w := by
  simpa using tp_minkB_smul_left (-1) v w

private theorem tp_minkB_sub_left (v v' w : Minkowski d) :
    minkB (v - v') w = minkB v w - minkB v' w := by
  rw [sub_eq_add_neg, tp_minkB_add_left, tp_minkB_neg_left]; ring

private theorem tp_minkB_sub_right (v w w' : Minkowski d) :
    minkB v (w - w') = minkB v w - minkB v w' := by
  rw [minkB_comm, tp_minkB_sub_left, minkB_comm, minkB_comm w']

private theorem tp_minkB_zero_left (w : Minkowski d) : minkB 0 w = 0 := by simp [minkB]

private theorem tp_minkQ_add (v w : Minkowski d) :
    minkQ (v + w) = minkQ v + 2 * minkB v w + minkQ w := by
  rw [minkQ_eq_minkB, minkQ_eq_minkB, minkQ_eq_minkB, tp_minkB_add_left, tp_minkB_add_right,
    tp_minkB_add_right, minkB_comm w v]; ring

/-- **Nondegeneracy** of `minkB`. -/
private theorem tp_eq_zero_of_minkB {v : Minkowski d} (h : ∀ w, minkB v w = 0) : v = 0 := by
  have h1 := h (1, 0)
  have h2 := h (0, v.2)
  simp only [minkB, mul_one, inner_zero_right, add_zero, neg_eq_zero, mul_zero, neg_zero,
    zero_add, real_inner_self_eq_norm_sq] at h1 h2
  have : v.2 = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  exact Prod.ext h1 this

/-- A linear map preserving `minkQ` preserves `minkB` (polarization). -/
private theorem tp_minkB_map {d' : ℕ} (f : Minkowski d' →ₗ[ℝ] Minkowski d)
    (hf : ∀ v, minkQ (f v) = minkQ v) (v w : Minkowski d') :
    minkB (f v) (f w) = minkB v w := by
  have h1 := tp_minkQ_add (f v) (f w)
  have h2 := tp_minkQ_add v w
  rw [← map_add, hf, hf, hf] at h1
  linarith

/-- `minkB v ·` as a linear form. -/
private noncomputable def tpMinkBR (v : Minkowski d) : Minkowski d →ₗ[ℝ] ℝ where
  toFun w := minkB v w
  map_add' w w' := tp_minkB_add_right v w w'
  map_smul' c w := by rw [tp_minkB_smul_right]; rfl

/-- **A vector orthogonal to a unit timelike vector is spacelike** (`minkQ > 0` off `0`). -/
private theorem tp_minkQ_pos_of_orth {f w : Minkowski d} (hf : minkQ f = -1)
    (hB : minkB w f = 0) (hne : w ≠ 0) : 0 < minkQ w := by
  simp only [minkQ] at hf ⊢
  simp only [minkB] at hB
  have hcs : (inner ℝ w.2 f.2) ^ 2 ≤ ‖w.2‖ ^ 2 * ‖f.2‖ ^ 2 := by
    have := abs_real_inner_le_norm w.2 f.2
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hwi : inner ℝ w.2 f.2 = w.1 * f.1 := by linarith
  rw [hwi] at hcs
  rcases eq_or_ne w.2 0 with h2 | h2
  · exfalso
    have hw1 : w.1 * f.1 = 0 := by rw [← hwi, h2, inner_zero_left]
    have hf1 : f.1 ≠ 0 := by
      intro h; rw [h] at hf; nlinarith [sq_nonneg ‖f.2‖]
    have : w.1 = 0 := by
      rcases mul_eq_zero.1 hw1 with h | h
      · exact h
      · exact absurd h hf1
    exact hne (Prod.ext this h2)
  · have hn : 0 < ‖w.2‖ ^ 2 := by positivity
    nlinarith [sq_nonneg w.1, sq_nonneg f.1, sq_nonneg ‖f.2‖]

private theorem tp_minkB_sum_right {α : Type*} (s : Finset α) (v : Minkowski d)
    (w : α → Minkowski d) : minkB v (∑ i ∈ s, w i) = ∑ i ∈ s, minkB v (w i) :=
  map_sum (tpMinkBR v) w s

/-- `minkB` restricted to a submodule, as a bilinear form. -/
private noncomputable def tpBilinOn (W : Submodule ℝ (Minkowski d)) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y : W => minkB (x : Minkowski d) (y : Minkowski d))
    (fun _ _ _ => tp_minkB_add_left _ _ _) (fun _ _ _ => tp_minkB_smul_left _ _ _)
    (fun _ _ _ => tp_minkB_add_right _ _ _) (fun _ _ _ => tp_minkB_smul_right _ _ _)

/-! ### Isometric affine embeddings and timelike affine subspaces -/

/-- **An isometric affine embedding** `ι : 𝐌^{d₁+1} → 𝐌^{d+1}`: an affine map whose linear part
preserves the Minkowski form. (It is automatically injective, `AffineMinkEmbedding.injective`.)
No time orientation is asked here; `Orthochronous` is asked where it is used (`IsLTPData`,
`suspendre`, `retract_le_top`). -/
structure AffineMinkEmbedding (d₁ d : ℕ) where
  /-- The underlying affine map. -/
  toAffineMap : Minkowski d₁ →ᵃ[ℝ] Minkowski d
  /-- The linear part preserves `minkQ`. -/
  minkQ_linear : ∀ v, minkQ (toAffineMap.linear v) = minkQ v

/-- **A timelike affine subspace** of `𝐌ⁿ`: its direction contains a vector of negative `minkQ`. -/
def IsTimelikeSubspace (U : AffineSubspace ℝ (Minkowski d)) : Prop :=
  ∃ v ∈ U.direction, minkQ v < 0

namespace AffineMinkEmbedding

variable (ι : AffineMinkEmbedding d₁ d)

noncomputable instance : CoeFun (AffineMinkEmbedding d₁ d) (fun _ => Minkowski d₁ → Minkowski d) :=
  ⟨fun ι => ι.toAffineMap⟩

/-- The linear part. -/
noncomputable abbrev lin : Minkowski d₁ →ₗ[ℝ] Minkowski d := ι.toAffineMap.linear

theorem coe_toAffineMap : ⇑ι.toAffineMap = ι := rfl

theorem apply_eq (p : Minkowski d₁) : ι p = ι.lin p + ι 0 := by
  show ι.toAffineMap p = ι.toAffineMap.linear p + ι.toAffineMap 0
  have h := ι.toAffineMap.linearMap_vsub p 0
  simp only [vsub_eq_sub, sub_zero] at h
  rw [h]; abel

theorem apply_add (p v : Minkowski d₁) : ι (p + v) = ι p + ι.lin v := by
  rw [ι.apply_eq, ι.apply_eq p, map_add]; abel

theorem apply_sub (p q : Minkowski d₁) : ι q - ι p = ι.lin (q - p) := by
  rw [ι.apply_eq, ι.apply_eq p, map_sub]; abel

theorem minkQ_lin (v : Minkowski d₁) : minkQ (ι.lin v) = minkQ v := ι.minkQ_linear v

theorem minkB_lin (v w : Minkowski d₁) : minkB (ι.lin v) (ι.lin w) = minkB v w :=
  tp_minkB_map ι.lin ι.minkQ_linear v w

theorem lin_injective : Injective ι.lin := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  refine tp_eq_zero_of_minkB fun w => ?_
  rw [← ι.minkB_lin, hv, tp_minkB_zero_left]

/-- **An isometric affine embedding is injective.** -/
theorem injective : Injective ι := by
  intro p q h
  have : ι.lin (q - p) = 0 := by rw [← ι.apply_sub, h, sub_self]
  exact (sub_eq_zero.1 (ι.lin_injective (this.trans (map_zero _).symm))).symm

theorem continuous : Continuous ι := ι.toAffineMap.continuous_of_finiteDimensional

/-- Its image, as an affine subspace. -/
noncomputable def range : AffineSubspace ℝ (Minkowski d) := AffineSubspace.map ι.toAffineMap ⊤

/-- The image `range ι` is a timelike affine subspace. -/
def TimelikeImage : Prop := IsTimelikeSubspace ι.range

/-- Time orientation: `ι` maps `(1, 0)` to a future vector. -/
def Orthochronous : Prop := 0 < (ι.lin (1, 0)).1

theorem minkQ_lin_timeVec : minkQ (ι.lin (1, 0)) = -1 := by
  rw [ι.minkQ_lin]; simp [minkQ]

/-- **The image of an isometric affine embedding is a timelike affine subspace** (automatic):
`ι` maps the time vector `(1, 0)` to a vector of `minkQ = −1`. -/
theorem timelikeImage : ι.TimelikeImage := by
  refine ⟨ι.lin (1, 0), ?_, by rw [ι.minkQ_lin_timeVec]; norm_num⟩
  rw [range, AffineSubspace.map_direction, AffineSubspace.direction_top, Submodule.map_top]
  exact LinearMap.mem_range_self _ _

/-! ### The orthogonal space `U^⊥` and the projection onto `U` -/

/-- **`U^⊥`**, `U = range ι`: the vectors `minkB`-orthogonal to the direction of `U`. -/
def perp : Set (Minkowski d) := {w | ∀ u, minkB w (ι.lin u) = 0}

theorem mem_perp {w : Minkowski d} : w ∈ ι.perp ↔ ∀ u, minkB w (ι.lin u) = 0 := Iff.rfl

theorem zero_mem_perp : (0 : Minkowski d) ∈ ι.perp := fun _ => tp_minkB_zero_left _

theorem add_mem_perp {w w' : Minkowski d} (hw : w ∈ ι.perp) (hw' : w' ∈ ι.perp) :
    w + w' ∈ ι.perp := fun u => by rw [tp_minkB_add_left, hw u, hw' u, add_zero]

theorem smul_mem_perp (c : ℝ) {w : Minkowski d} (hw : w ∈ ι.perp) : c • w ∈ ι.perp :=
  fun u => by rw [tp_minkB_smul_left, hw u, mul_zero]

theorem neg_mem_perp {w : Minkowski d} (hw : w ∈ ι.perp) : -w ∈ ι.perp := by
  simpa using ι.smul_mem_perp (-1) hw

theorem sub_mem_perp {w w' : Minkowski d} (hw : w ∈ ι.perp) (hw' : w' ∈ ι.perp) :
    w - w' ∈ ι.perp := by
  rw [sub_eq_add_neg]; exact ι.add_mem_perp hw (ι.neg_mem_perp hw')

theorem isClosed_perp : IsClosed ι.perp := by
  have : ι.perp = ⋂ u, {w | minkB w (ι.lin u) = 0} := by ext; simp [perp]
  rw [this]
  refine isClosed_iInter fun u => isClosed_eq ?_ continuous_const
  unfold minkB; fun_prop

/-- The spatial half of `coproj`, by the Riesz representation in `EuclideanSpace`. -/
private noncomputable def spatialPart (v : Minkowski d) : EuclideanSpace ℝ (Fin d₁) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d₁))).symm
    (LinearMap.toContinuousLinearMap
      ((tpMinkBR v) ∘ₗ ι.lin ∘ₗ LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d₁))))

private theorem inner_spatialPart (v : Minkowski d) (y : EuclideanSpace ℝ (Fin d₁)) :
    inner ℝ (ι.spatialPart v) y = minkB v (ι.lin (0, y)) := by
  rw [spatialPart, InnerProductSpace.toDual_symm_apply]; rfl

/-- The coordinates of `v` along `U` (raw form). -/
private noncomputable def coprojFun (v : Minkowski d) : Minkowski d₁ :=
  (-minkB v (ι.lin (1, 0)), ι.spatialPart v)

private theorem minkB_coprojFun (v : Minkowski d) (u : Minkowski d₁) :
    minkB (ι.coprojFun v) u = minkB v (ι.lin u) := by
  have hu : u = u.1 • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d₁))) + (0, u.2) := by
    ext <;> simp
  conv_rhs => rw [hu, map_add, map_smul, tp_minkB_add_right, tp_minkB_smul_right]
  simp only [minkB, coprojFun, inner_spatialPart]
  ring

private theorem coprojFun_unique {v : Minkowski d} {x : Minkowski d₁}
    (h : ∀ u, minkB x u = minkB v (ι.lin u)) : x = ι.coprojFun v := by
  rw [← sub_eq_zero]
  exact tp_eq_zero_of_minkB fun u => by rw [tp_minkB_sub_left, h, minkB_coprojFun, sub_self]

/-- **The coordinates along `U`**: the linear map `P` with `minkB (P v) u = minkB v (ι.lin u)`
(the `minkB`-adjoint of `ι.lin`); `ι.lin ∘ P` is the orthogonal projection onto `ι.lin`'s range. -/
noncomputable def coproj : Minkowski d →ₗ[ℝ] Minkowski d₁ where
  toFun := ι.coprojFun
  map_add' v v' := (ι.coprojFun_unique fun u => by
    rw [tp_minkB_add_left, minkB_coprojFun, minkB_coprojFun, tp_minkB_add_left]).symm
  map_smul' c v := (ι.coprojFun_unique fun u => by
    rw [RingHom.id_apply, tp_minkB_smul_left, minkB_coprojFun, tp_minkB_smul_left]).symm

theorem minkB_coproj (v : Minkowski d) (u : Minkowski d₁) :
    minkB (ι.coproj v) u = minkB v (ι.lin u) := ι.minkB_coprojFun v u

theorem coproj_lin (u : Minkowski d₁) : ι.coproj (ι.lin u) = u := by
  rw [← sub_eq_zero]
  exact tp_eq_zero_of_minkB fun w => by
    rw [tp_minkB_sub_left, minkB_coproj, minkB_lin, sub_self]

theorem coproj_eq_zero_of_mem_perp {w : Minkowski d} (hw : w ∈ ι.perp) : ι.coproj w = 0 :=
  tp_eq_zero_of_minkB fun u => by rw [minkB_coproj, hw u]

theorem sub_lin_coproj_mem_perp (v : Minkowski d) : v - ι.lin (ι.coproj v) ∈ ι.perp :=
  fun u => by rw [tp_minkB_sub_left, minkB_lin, minkB_coproj, sub_self]

/-- `U^⊥ ∩ (U − U) = 0`. -/
theorem lin_mem_perp_iff {u : Minkowski d₁} : ι.lin u ∈ ι.perp ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]; exact ι.zero_mem_perp⟩
  rw [← ι.coproj_lin u, ι.coproj_eq_zero_of_mem_perp h]

theorem continuous_coproj : Continuous ι.coproj := ι.coproj.continuous_of_finiteDimensional

/-- **`U^⊥` is spacelike** — the euclidean space of the twisted product: a nonzero vector
orthogonal to the timelike `U` has `minkQ > 0`. -/
theorem minkQ_pos_of_mem_perp {w : Minkowski d} (hw : w ∈ ι.perp) (hne : w ≠ 0) :
    0 < minkQ w :=
  tp_minkQ_pos_of_orth ι.minkQ_lin_timeVec (hw (1, 0)) hne

theorem minkQ_nonneg_of_mem_perp {w : Minkowski d} (hw : w ∈ ι.perp) : 0 ≤ minkQ w := by
  rcases eq_or_ne w 0 with rfl | hne
  · simp
  · exact (ι.minkQ_pos_of_mem_perp hw hne).le


/-! ### The retraction onto `U` and the splitting `𝐌ⁿ ≅ U × U^⊥` -/

/-- **The retraction `q : 𝐌ⁿ → 𝐌^{d₁+1}` along `U^⊥`**: `ι (q p)` is the foot of `p` on `U`. -/
noncomputable def retract (p : Minkowski d) : Minkowski d₁ := ι.coproj (p - ι 0)

theorem continuous_retract : Continuous ι.retract :=
  ι.continuous_coproj.comp (continuous_id.sub continuous_const)

theorem retract_apply_add (x : Minkowski d₁) {w : Minkowski d} (hw : w ∈ ι.perp) :
    ι.retract (ι x + w) = x := by
  rw [retract, ι.apply_eq x, show ι.lin x + ι 0 + w - ι 0 = ι.lin x + w by abel, map_add,
    ι.coproj_lin, ι.coproj_eq_zero_of_mem_perp hw, add_zero]

theorem retract_apply (x : Minkowski d₁) : ι.retract (ι x) = x := by
  simpa using ι.retract_apply_add x ι.zero_mem_perp

theorem sub_apply_retract_mem_perp (p : Minkowski d) : p - ι (ι.retract p) ∈ ι.perp := by
  have h := ι.sub_lin_coproj_mem_perp (p - ι 0)
  rwa [show p - ι 0 - ι.lin (ι.coproj (p - ι 0)) = p - ι (ι.retract p) by
    rw [ι.apply_eq (ι.retract p), retract]; abel] at h

theorem apply_retract_add (p : Minkowski d) : ι (ι.retract p) + (p - ι (ι.retract p)) = p := by
  abel

/-- **The splitting** `𝐌ⁿ ≅ 𝐌^{d₁+1} × U^⊥`, `p ↦ (q p, p − ι (q p))`, inverse `(x, w) ↦ ι x + w`:
a homeomorphism (the product structure of a linear twisted product, before the quotient). -/
noncomputable def split : Minkowski d ≃ₜ Minkowski d₁ × ι.perp where
  toFun p := (ι.retract p, ⟨p - ι (ι.retract p), ι.sub_apply_retract_mem_perp p⟩)
  invFun z := ι z.1 + z.2
  left_inv p := ι.apply_retract_add p
  right_inv z := by
    obtain ⟨x, w, hw⟩ := z
    simp only [ι.retract_apply_add x hw, add_sub_cancel_left]
  continuous_toFun := by
    refine ι.continuous_retract.prodMk (Continuous.subtype_mk ?_ _)
    exact continuous_id.sub (ι.continuous.comp ι.continuous_retract)
  continuous_invFun := (ι.continuous.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)

@[simp] theorem split_apply_fst (p : Minkowski d) : (ι.split p).1 = ι.retract p := rfl

@[simp] theorem split_symm_apply (z : Minkowski d₁ × ι.perp) : ι.split.symm z = ι z.1 + z.2 := rfl

/-- **The orthogonal projection is a causal map**, for an orthochronous `ι`: it maps the future
causal cone of `𝐌ⁿ` into that of `𝐌^{d₁+1}` (`minkQ (P v) ≤ minkQ v`, by Pythagoras with the
spacelike `U^⊥`). The linear core of Rem 5.3. -/
theorem coproj_isFutureCausal (hι : ι.Orthochronous) {v : Minkowski d}
    (hv : IsFutureCausal v) : IsFutureCausal (ι.coproj v) := by
  set f := ι.lin (1, 0)
  have hf : minkQ f = -1 := ι.minkQ_lin_timeVec
  have h1 : minkB (ι.coproj v) (1, 0) = minkB v f := ι.minkB_coproj v (1, 0)
  simp only [minkB, mul_one, inner_zero_right, add_zero] at h1
  -- `minkB v f ≤ 0`
  have hvf : minkB v f ≤ 0 := by
    have hv2 : ‖v.2‖ ≤ v.1 := (sq_le_sq₀ (norm_nonneg _) hv.1).1 (minkQ_le_zero_iff.1 hv.2)
    have hf2 : ‖f.2‖ ≤ f.1 := (sq_le_sq₀ (norm_nonneg _) hι.le).1
      (minkQ_le_zero_iff.1 (by rw [hf]; norm_num))
    have hin := real_inner_le_norm v.2 f.2
    have : ‖v.2‖ * ‖f.2‖ ≤ v.1 * f.1 :=
      mul_le_mul hv2 hf2 (norm_nonneg _) hv.1
    simp only [minkB]; linarith
  simp only [minkB] at hvf
  refine ⟨by linarith, ?_⟩
  -- Pythagoras: `minkQ v = minkQ (P v) + minkQ w`, `w ∈ U^⊥`
  set w := v - ι.lin (ι.coproj v)
  have hw : w ∈ ι.perp := ι.sub_lin_coproj_mem_perp v
  have hdec : v = ι.lin (ι.coproj v) + w := by simp [w]
  have hQ : minkQ v = minkQ (ι.coproj v) + minkQ w := by
    conv_lhs => rw [hdec]
    rw [tp_minkQ_add, minkB_comm, hw, ι.minkQ_lin]; ring
  have := ι.minkQ_nonneg_of_mem_perp hw
  have := hv.2
  linarith

/-- **The retraction is a causal map** of `𝐌ⁿ` onto `𝐌^{d₁+1}` (`≤` on `⊤`), for an orthochronous
`ι`. -/
theorem retract_le_top (hι : ι.Orthochronous) {p p' : Minkowski d}
    (h : (minkowski d).le ⊤ p p') : (minkowski d₁).le ⊤ (ι.retract p) (ι.retract p') := by
  rw [le_top_iff_minkQ] at h ⊢
  rw [retract, retract, ← map_sub, show p' - ι 0 - (p - ι 0) = p' - p by abel]
  exact ι.coproj_isFutureCausal hι h

/-! ### Restricting an isometry to `U` -/

/-- `g ∈ Isom(𝐌^{d₁+1})` is the restriction of `γ ∈ Isom(𝐌ⁿ)` to `U` read through `ι`:
`ι ∘ g = γ ∘ ι`. -/
def Restricts (γ : isom d) (g : isom d₁) : Prop := ∀ p, ι (g • p) = γ • ι p

/-- **Every element of `Γ` restricts to `U` as an element of `Isom(𝐌^{d₁+1})`.** Implies that `Γ`
preserves `U` (`RestrictsIn.preserves`); the converse fails exactly on the orientation of `U`
(`TwistedProduct.not_restrictsIn_glideGroup`, below). -/
def RestrictsIn (Γ : Subgroup (isom d)) : Prop := ∀ γ ∈ Γ, ∃ g : isom d₁, ι.Restricts γ g

variable {ι}

theorem Restricts.unique {γ : isom d} {g g' : isom d₁} (h : ι.Restricts γ g)
    (h' : ι.Restricts γ g') : g = g' :=
  Subtype.ext (AffineEquiv.ext fun p => ι.injective ((h p).trans (h' p).symm))

theorem Restricts.one : ι.Restricts 1 1 := fun p => by simp

theorem Restricts.mul {γ γ' : isom d} {g g' : isom d₁} (h : ι.Restricts γ g)
    (h' : ι.Restricts γ' g') : ι.Restricts (γ * γ') (g * g') := fun p => by
  rw [mul_smul, h, h', mul_smul]

theorem Restricts.inv {γ : isom d} {g : isom d₁} (h : ι.Restricts γ g) :
    ι.Restricts γ⁻¹ g⁻¹ := fun p => by
  rw [eq_inv_smul_iff, ← h, smul_inv_smul]

/-- The linear parts intertwine: `ι.lin ∘ L(g) = L(γ) ∘ ι.lin`. -/
theorem Restricts.lin {γ : isom d} {g : isom d₁} (h : ι.Restricts γ g) (u : Minkowski d₁) :
    ι.lin ((g : Minkowski d₁ ≃ᵃ[ℝ] Minkowski d₁).linear u) =
      (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (ι.lin u) := by
  calc ι.lin ((g : Minkowski d₁ ≃ᵃ[ℝ] Minkowski d₁).linear u)
      = ι.lin (g • u - g • 0) := by rw [isom_smul_def, isom_smul_def, isom_sub, sub_zero]
    _ = ι (g • u) - ι (g • 0) := (ι.apply_sub _ _).symm
    _ = γ • ι u - γ • ι 0 := by rw [h, h]
    _ = (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (ι.lin u) := by
      rw [isom_smul_def, isom_smul_def, isom_sub, ι.apply_sub, sub_zero]

/-- **The monodromy is linear on `U^⊥`**: the linear part of `γ` maps `U^⊥` into itself (and
preserves `minkQ` there, being in `SO₀(1,d)`: a linear isometry of the euclidean `U^⊥`). -/
theorem Restricts.linear_mem_perp {γ : isom d} {g : isom d₁} (h : ι.Restricts γ g)
    {w : Minkowski d} (hw : w ∈ ι.perp) :
    (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear w ∈ ι.perp := by
  intro u
  set L := (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear
  set Lg := (g : Minkowski d₁ ≃ᵃ[ℝ] Minkowski d₁).linear
  have hu : ι.lin u = L (ι.lin (Lg.symm u)) := by
    rw [← h.lin, LinearEquiv.apply_symm_apply]
  rw [hu]
  have := tp_minkB_map (L : Minkowski d →ₗ[ℝ] Minkowski d) (lorentz.minkQ_apply γ.2) w
    (ι.lin (Lg.symm u))
  rw [LinearEquiv.coe_coe] at this
  rw [this, hw]

/-- `γ` acts on the splitting diagonally: `γ (ι x + w) = ι (g x) + L(γ) w`. -/
theorem Restricts.smul_apply_add {γ : isom d} {g : isom d₁} (h : ι.Restricts γ g)
    (x : Minkowski d₁) (w : Minkowski d) :
    γ • (ι x + w) = ι (g • x) + (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear w := by
  have := isom_sub (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d) (ι x) (ι x + w)
  rw [add_sub_cancel_left] at this
  rw [h, isom_smul_def, isom_smul_def, ← this]; abel

/-- **The retraction is equivariant**: `q (γ p) = g (q p)`. -/
theorem Restricts.retract_smul {γ : isom d} {g : isom d₁} (h : ι.Restricts γ g)
    (p : Minkowski d) : ι.retract (γ • p) = g • ι.retract p := by
  conv_lhs => rw [← ι.apply_retract_add p, h.smul_apply_add]
  exact ι.retract_apply_add _ (h.linear_mem_perp (ι.sub_apply_retract_mem_perp p))

/-- **The splitting is equivariant**: `γ` acts on `𝐌^{d₁+1} × U^⊥` by `(g, L(γ)|_{U^⊥})`. -/
theorem Restricts.split_smul {γ : isom d} {g : isom d₁} (h : ι.Restricts γ g)
    (p : Minkowski d) :
    ι.split (γ • p) = (g • (ι.split p).1,
      ⟨(γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (ι.split p).2,
        h.linear_mem_perp (ι.split p).2.2⟩) := by
  refine Prod.ext (h.retract_smul p) (Subtype.ext ?_)
  show γ • p - ι (ι.retract (γ • p)) = _
  have e := h.smul_apply_add (ι.retract p) (p - ι (ι.retract p))
  rw [ι.apply_retract_add] at e
  rw [h.retract_smul p, e, add_sub_cancel_left]; rfl

theorem RestrictsIn.preserves {Γ : Subgroup (isom d)} (h : ι.RestrictsIn Γ) :
    ∀ γ ∈ Γ, (fun p => γ • p) '' Set.range ι = Set.range ι := by
  intro γ hγ
  obtain ⟨g, hg⟩ := h γ hγ
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨g • x, hg x⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨ι (g⁻¹ • x), ⟨_, rfl⟩, ?_⟩
    show γ • ι (g⁻¹ • x) = ι x
    rw [hg.inv, smul_inv_smul]

variable (ι)

/-- **The restriction of `Γ` to `U`**, as a subgroup of `Isom(𝐌^{d₁+1})`: the `g` with
`ι ∘ g = γ ∘ ι` for some `γ ∈ Γ`. Under `RestrictsIn`, `γ ↦ g` maps `Γ` onto it. -/
def restrictGroup (Γ : Subgroup (isom d)) : Subgroup (isom d₁) where
  carrier := {g | ∃ γ ∈ Γ, ι.Restricts γ g}
  one_mem' := ⟨1, Γ.one_mem, Restricts.one⟩
  mul_mem' := by
    rintro g g' ⟨γ, hγ, h⟩ ⟨γ', hγ', h'⟩
    exact ⟨γ * γ', Γ.mul_mem hγ hγ', h.mul h'⟩
  inv_mem' := by
    rintro g ⟨γ, hγ, h⟩
    exact ⟨γ⁻¹, Γ.inv_mem hγ, h.inv⟩

theorem mem_restrictGroup {Γ : Subgroup (isom d)} {g : isom d₁} :
    g ∈ ι.restrictGroup Γ ↔ ∃ γ ∈ Γ, ι.Restricts γ g := Iff.rfl

/-- **`ι⁻¹ Ω`**, the open set `U ∩ Ω` read in `𝐌^{d₁+1}`. -/
def preimageOpens (Ω : Opens (Minkowski d)) : Opens (Minkowski d₁) :=
  ⟨ι ⁻¹' Ω, Ω.isOpen.preimage ι.continuous⟩

@[simp] theorem mem_preimageOpens {Ω : Opens (Minkowski d)} {x : Minkowski d₁} :
    x ∈ ι.preimageOpens Ω ↔ ι x ∈ Ω := Iff.rfl

/-- Under the `U^⊥`-invariance of `Ω`, `p ∈ Ω ↔ q p ∈ ι⁻¹ Ω`: **`Ω = (U ∩ Ω) × U^⊥`** through
`split`. -/
theorem mem_iff_retract_mem {Ω : Opens (Minkowski d)}
    (hperp : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω) {p : Minkowski d} :
    p ∈ Ω ↔ ι.retract p ∈ ι.preimageOpens Ω := by
  have hw := ι.sub_apply_retract_mem_perp p
  rw [mem_preimageOpens]
  refine ⟨fun hp => ?_, fun hq => ?_⟩
  · have := hperp _ (ι.neg_mem_perp hw) p hp
    rwa [show p + -(p - ι (ι.retract p)) = ι (ι.retract p) by abel] at this
  · have := hperp _ hw _ hq
    rwa [ι.apply_retract_add] at this


/-! ### The restricted action on `U ∩ Ω` -/

open FlatQuotient

variable (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d))

/-- `ι⁻¹ Ω` is invariant under the restricted group. -/
instance instInvariantRestrict [Invariant Γ Ω] :
    Invariant (ι.restrictGroup Γ) (ι.preimageOpens Ω) :=
  ⟨fun g p hp => by
    obtain ⟨γ, hγ, h⟩ := g.2
    show ι ((g : isom d₁) • p) ∈ Ω
    rw [h]
    exact Invariant.smul_mem ⟨γ, hγ⟩ _ hp⟩

/-- A choice of `γ ∈ Γ` restricting to `g`. -/
private noncomputable def liftElt (g : ι.restrictGroup Γ) : Γ :=
  ⟨Classical.choose g.2, (Classical.choose_spec g.2).1⟩

private theorem liftElt_restricts (g : ι.restrictGroup Γ) :
    ι.Restricts (liftElt ι Γ g : isom d) g :=
  (Classical.choose_spec g.2).2

private theorem liftElt_injective : Injective (liftElt ι Γ) := fun g g' h =>
  Subtype.ext ((liftElt_restricts ι Γ g).unique (h ▸ liftElt_restricts ι Γ g'))

/-- **The restricted action is free** when `Γ` acts freely on `Ω`. -/
instance instIsCancelSMulRestrict [Invariant Γ Ω] [IsCancelSMul Γ Ω] :
    IsCancelSMul (ι.restrictGroup Γ) (ι.preimageOpens Ω) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g x hx
  have hx' : (g : isom d₁) • (x : Minkowski d₁) = x := by
    have := congrArg Subtype.val hx; rwa [coe_smul] at this
  have hγ : (liftElt ι Γ g) • (⟨ι x, x.2⟩ : Ω) = ⟨ι x, x.2⟩ := Subtype.ext (by
    rw [coe_smul, ← liftElt_restricts ι Γ g, hx'])
  have h1 := (isCancelSMul_iff_eq_one_of_smul_eq.1 (inferInstance : IsCancelSMul Γ Ω)) _ _ hγ
  have h2 := liftElt_restricts ι Γ g
  rw [h1, Subgroup.coe_one] at h2
  exact Subtype.ext (h2.unique Restricts.one)

/-- **The restricted action is properly discontinuous** when `Γ` acts properly discontinuously
on `Ω`: `x ↦ ι x` is a continuous map `ι⁻¹ Ω → Ω` intertwining the actions, and `g ↦ γ` is
injective. -/
instance instProperlyDiscontinuousSMulRestrict [Invariant Γ Ω] [ProperlyDiscontinuousSMul Γ Ω] :
    ProperlyDiscontinuousSMul (ι.restrictGroup Γ) (ι.preimageOpens Ω) := by
  refine ⟨fun {K L} hK hL => ?_⟩
  set φ : ι.preimageOpens Ω → Ω := fun x => ⟨ι x, x.2⟩
  have hφ : Continuous φ := (ι.continuous.comp continuous_subtype_val).subtype_mk _
  have hS := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) (hK.image hφ)
    (hL.image hφ)
  refine Set.Finite.of_injOn (f := liftElt ι Γ) ?_ (liftElt_injective ι Γ).injOn hS
  rintro g ⟨_, ⟨k, hk, rfl⟩, hl⟩
  refine ⟨φ (g • k), ⟨φ k, ⟨k, hk, rfl⟩, Subtype.ext ?_⟩, ⟨g • k, hl, rfl⟩⟩
  show (liftElt ι Γ g : isom d) • ι k = ι ((g : isom d₁) • (k : Minkowski d₁))
  rw [liftElt_restricts ι Γ g]

variable {Γ Ω}

/-- **`U ∩ Ω` with the restricted group is connected** when `B = Γ\Ω` is: under `RestrictsIn`
and the `U^⊥`-invariance, the equivariant retraction descends to a continuous surjection
`Γ\Ω → Γ_U\(ι⁻¹ Ω)`. -/
theorem connectedSpace_base {B : Type u} [TopologicalSpace B] [ConnectedSpace B]
    [ChartedSpace (Minkowski d) B] [Invariant Γ Ω] (hB : IsQuotientOf B Γ Ω)
    (hres : ι.RestrictsIn Γ) (hperp : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω) :
    ConnectedSpace (FlatQuotient (ι.restrictGroup Γ) (ι.preimageOpens Ω)) := by
  obtain ⟨-, -, -, Φ, -⟩ := hB.exists_homeomorph
  haveI : ConnectedSpace (FlatQuotient Γ Ω) := Φ.symm.surjective.connectedSpace Φ.symm.continuous
  let f : Ω → FlatQuotient (ι.restrictGroup Γ) (ι.preimageOpens Ω) := fun p =>
    proj _ _ ⟨ι.retract p, (ι.mem_iff_retract_mem hperp).1 p.2⟩
  have hf : Continuous f := (continuous_proj _ _).comp
    ((ι.continuous_retract.comp continuous_subtype_val).subtype_mk _)
  have hrel : ∀ a b : Ω, (MulAction.orbitRel Γ Ω) a b → f a = f b := by
    intro a b hab
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    obtain ⟨g, hg⟩ := hres γ γ.2
    refine proj_eq_proj_iff'.2 ⟨g⁻¹, (ι.restrictGroup Γ).inv_mem ⟨γ, γ.2, hg⟩, ?_⟩
    show g⁻¹ • ι.retract a = ι.retract b
    rw [← hγ, coe_smul, hg.retract_smul, inv_smul_smul]
  let F : FlatQuotient Γ Ω → FlatQuotient (ι.restrictGroup Γ) (ι.preimageOpens Ω) :=
    Quotient.lift f hrel
  have hF : Continuous F := hf.quotient_lift hrel
  have hFs : Surjective F := by
    intro z
    obtain ⟨x, rfl⟩ := proj_surjective _ _ z
    refine ⟨proj Γ Ω ⟨ι x, x.2⟩, ?_⟩
    show f ⟨ι x, x.2⟩ = _
    exact congrArg (proj _ _) (Subtype.ext (ι.retract_apply x))
  exact hFs.connectedSpace hF

end AffineMinkEmbedding

/-! ### Every timelike affine subspace is the image of an isometric affine embedding -/

private theorem tp_inv_sqrt_aux {s q : ℝ} (hs : 0 < s) (h : s ^ 2 = q) : s⁻¹ * (s⁻¹ * q) = 1 := by
  subst h; field_simp

/-- **Sylvester for a timelike affine subspace**: every timelike affine subspace `U` of `𝐌ⁿ` is
the image `range ι` of an isometric affine embedding `ι : 𝐌^{d₁+1} → 𝐌ⁿ` (a unit timelike `f` in
the direction `D` of `U`, and a `minkB`-orthonormal basis of the euclidean `f^⊥ ∩ D`). So
`IsLTPOver`'s `U = range ι` loses no timelike affine subspace; `f` is chosen future, so `ι` is
orthochronous and `IsLTPData.orthochronous` loses nothing either. -/
theorem exists_affineMinkEmbedding_of_isTimelike {U : AffineSubspace ℝ (Minkowski d)}
    (hU : IsTimelikeSubspace U) :
    ∃ (d₁ : ℕ) (ι : AffineMinkEmbedding d₁ d), ι.Orthochronous ∧ ι.range = U := by
  obtain ⟨v, hvD, hv, hvpos⟩ : ∃ v ∈ U.direction, minkQ v < 0 ∧ 0 < v.1 := by
    obtain ⟨v₀, hvD₀, hv₀⟩ := hU
    have h1 : v₀.1 ≠ 0 := by
      intro h; simp only [minkQ, h] at hv₀; nlinarith [sq_nonneg ‖v₀.2‖]
    rcases lt_or_gt_of_ne h1 with h | h
    · refine ⟨-v₀, U.direction.neg_mem hvD₀, ?_, by simpa using neg_pos.2 h⟩
      simpa [minkQ] using hv₀
    · exact ⟨v₀, hvD₀, hv₀, h⟩
  have hc : 0 < -minkQ v := by linarith
  set c := Real.sqrt (-minkQ v) with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.2 hc
  set f : Minkowski d := c⁻¹ • v with hfdef
  have hf : minkQ f = -1 := by
    rw [hfdef, minkQ_eq_minkB, tp_minkB_smul_left, tp_minkB_smul_right, ← minkQ_eq_minkB]
    have h := tp_inv_sqrt_aux hcpos (Real.sq_sqrt hc.le)
    have : c⁻¹ * (c⁻¹ * minkQ v) = -(c⁻¹ * (c⁻¹ * -minkQ v)) := by ring
    rw [this, h]
  have hfD : f ∈ U.direction := U.direction.smul_mem _ hvD
  let W : Submodule ℝ (Minkowski d) := U.direction ⊓ LinearMap.ker (tpMinkBR f)
  have hWD : ∀ {w : Minkowski d}, w ∈ W → w ∈ U.direction := fun h => (Submodule.mem_inf.1 h).1
  have hWf : ∀ {w : Minkowski d}, w ∈ W → minkB f w = 0 := fun h =>
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 h).2
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := tpBilinOn W)
    ⟨fun x y => minkB_comm (x : Minkowski d) y⟩
  have hbpos : ∀ i, 0 < minkQ (b i : Minkowski d) := fun i =>
    tp_minkQ_pos_of_orth hf (by rw [minkB_comm]; exact hWf (b i).2)
      (fun h => b.ne_zero i (Subtype.ext h))
  let e : Fin (Module.finrank ℝ W) → Minkowski d := fun i =>
    (Real.sqrt (minkQ (b i : Minkowski d)))⁻¹ • (b i : Minkowski d)
  have he : ∀ i j, minkB (e i) (e j) = if i = j then 1 else 0 := by
    intro i j
    simp only [e, tp_minkB_smul_left, tp_minkB_smul_right]
    split_ifs with h
    · subst h
      rw [← minkQ_eq_minkB]
      exact tp_inv_sqrt_aux (Real.sqrt_pos.2 (hbpos i)) (Real.sq_sqrt (hbpos i).le)
    · have : minkB (b i : Minkowski d) (b j) = 0 := hb h
      rw [this, mul_zero, mul_zero]
  have hef : ∀ i, minkB f (e i) = 0 := fun i => by
    simp only [e, tp_minkB_smul_right, hWf (b i).2, mul_zero]
  let L : Minkowski (Module.finrank ℝ W) →ₗ[ℝ] Minkowski d :=
    (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ W)))).smulRight f +
      ∑ i, ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) →L[ℝ] ℝ).toLinearMap ∘ₗ
        LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ W)))).smulRight (e i)
  have hL : ∀ x : Minkowski (Module.finrank ℝ W), L x = x.1 • f + ∑ i, x.2 i • e i := by
    intro x
    simp [L, LinearMap.sum_apply]
  have hQ : ∀ x : Minkowski (Module.finrank ℝ W), minkQ (L x) = minkQ x := by
    intro x
    rw [hL, tp_minkQ_add]
    have h1 : minkB (x.1 • f) (∑ i, x.2 i • e i) = 0 := by
      rw [tp_minkB_smul_left, tp_minkB_sum_right]
      simp [tp_minkB_smul_right, hef]
    have h2 : minkQ (∑ i, x.2 i • e i) = ∑ i, x.2 i ^ 2 := by
      rw [minkQ_eq_minkB, tp_minkB_sum_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [minkB_comm, tp_minkB_smul_left, tp_minkB_sum_right]
      simp [tp_minkB_smul_right, he, sq]
    have h3 : minkQ (x.1 • f) = -x.1 ^ 2 := by
      rw [minkQ_eq_minkB, tp_minkB_smul_left, tp_minkB_smul_right, ← minkQ_eq_minkB, hf]; ring
    rw [h1, h2, h3]
    simp only [minkQ, EuclideanSpace.real_norm_sq_eq]
    ring
  have hLD : ∀ x, L x ∈ U.direction := fun x => by
    rw [hL]
    exact U.direction.add_mem (U.direction.smul_mem _ hfD)
      (U.direction.sum_mem fun i _ => U.direction.smul_mem _
        (U.direction.smul_mem _ (hWD (b i).2)))
  have surj : ∀ u ∈ U.direction, ∃ x, L x = u := by
    intro u hu
    set a := -minkB u f
    have hw : u - a • f ∈ W := by
      refine Submodule.mem_inf.2 ⟨U.direction.sub_mem hu (U.direction.smul_mem _ hfD),
        LinearMap.mem_ker.2 ?_⟩
      show minkB f (u - a • f) = 0
      rw [tp_minkB_sub_right, tp_minkB_smul_right, ← minkQ_eq_minkB, hf, minkB_comm]
      simp [a]
    set w : W := ⟨_, hw⟩
    refine ⟨(a, WithLp.toLp 2 fun i => b.repr w i * Real.sqrt (minkQ (b i : Minkowski d))), ?_⟩
    rw [hL]
    have hs : ∑ i, (b.repr w i * Real.sqrt (minkQ (b i : Minkowski d))) • e i = u - a • f := by
      calc ∑ i, (b.repr w i * Real.sqrt (minkQ (b i : Minkowski d))) • e i
          = ((∑ i, b.repr w i • b i : W) : Minkowski d) := by
            rw [Submodule.coe_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [e, smul_smul, Submodule.coe_smul]
            rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 (hbpos i)).ne', mul_one]
        _ = u - a • f := by rw [b.sum_repr w]
    rw [hs, add_sub_cancel]
  have hne : (U : Set (Minkowski d)).Nonempty := by
    rcases (U : Set (Minkowski d)).eq_empty_or_nonempty with h | h
    · rw [AffineSubspace.coe_eq_bot_iff] at h
      subst h
      rw [AffineSubspace.direction_bot, Submodule.mem_bot] at hvD
      subst hvD
      simp [minkQ] at hv
    · exact h
  obtain ⟨p₀, hp₀⟩ := hne
  refine ⟨Module.finrank ℝ W,
    ⟨L.toAffineMap + AffineMap.const ℝ (Minkowski (Module.finrank ℝ W)) p₀, fun w => ?_⟩, ?_, ?_⟩
  · simpa using hQ w
  · show 0 < ((L.toAffineMap + AffineMap.const ℝ _ p₀).linear (1, 0)).1
    have hL1 : L (1, 0) = f := by rw [hL]; simp
    simpa [hL1, hfdef] using mul_pos (inv_pos.2 hcpos) hvpos
  · ext q
    simp only [AffineMinkEmbedding.range, AffineSubspace.mem_map, AffineSubspace.mem_top,
      true_and]
    constructor
    · rintro ⟨x, rfl⟩
      have := AffineSubspace.vadd_mem_of_mem_direction (hLD x) hp₀
      simpa [vadd_eq_add] using this
    · intro hq
      obtain ⟨x, hx⟩ := surj (q - p₀) (AffineSubspace.vsub_mem_direction hq hp₀)
      exact ⟨x, by simp [hx]⟩

/-! ### Linear twisted products, in quotient form -/

open FlatQuotient

/-- **The data of a linear twisted product** (BARBOT-THEOREMS §1, quotient form of Lemma 5.5):
`B = Γ\Ω` and `M₁ = Γ_U\(ι⁻¹ Ω)`, where the orthochronous `ι` parametrizes the timelike affine
subspace `U`, every
element of `Γ` restricts to `U` as an element of `Isom(𝐌^{d₁+1})`, and `Ω` is invariant under
the translations by `U^⊥`. -/
structure IsLTPData (B : Type u) [TopologicalSpace B] [ChartedSpace (Minkowski d) B]
    (M₁ : Type v) [TopologicalSpace M₁] [ChartedSpace (Minkowski d₁) M₁]
    (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) (ι : AffineMinkEmbedding d₁ d) : Prop where
  /-- `U = range ι` is timelike (redundant: `AffineMinkEmbedding.timelikeImage`; kept to mirror
  BARBOT-THEOREMS §1). -/
  timelike : ι.TimelikeImage
  /-- `ι` preserves the time orientation (Barbot's spacetimes are time-oriented and his
  isometries `SO₀`-affine, l.469–480): `M₁` carries the time orientation `B` induces on `U`. -/
  orthochronous : ι.Orthochronous
  /-- `Γ` preserves `U` (redundant: `RestrictsIn.preserves`; kept to mirror BARBOT-THEOREMS §1). -/
  preserves : ∀ γ ∈ Γ, (fun p => γ • p) '' Set.range ι = Set.range ι
  /-- Every element of `Γ` restricts to `U` as an isometry of `𝐌^{d₁+1}` (orientation of `U`). -/
  restricts : ι.RestrictsIn Γ
  /-- `Ω + w = Ω` for `w ∈ U^⊥`. -/
  perp_invariant : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω
  /-- `B = Γ\Ω`. -/
  quotient : IsQuotientOf B Γ Ω
  /-- `M₁ = Γ_U\(U ∩ Ω)`. -/
  quotient_base : IsQuotientOf M₁ (ι.restrictGroup Γ) (ι.preimageOpens Ω)

/-- **`B` is a linear twisted product over `M₁`** (Barbot §5.S, l.1789–1797, in the quotient form
of Lemma 5.5, BARBOT-THEOREMS §1). -/
def IsLTPOver (B : FlatSpacetime.{u} d) (M₁ : FlatSpacetime.{v} d₁) : Prop :=
  ∃ (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) (ι : AffineMinkEmbedding d₁ d),
    IsLTPData B M₁ Γ Ω ι

/-- The invariance of `IsLTPData` in BARBOT-THEOREMS' form `Ω + w = Ω`. -/
theorem perpInvariant_iff {Ω : Opens (Minkowski d)} {ι : AffineMinkEmbedding d₁ d} :
    (∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω) ↔
      ∀ w ∈ ι.perp, (fun p => p + w) '' (Ω : Set (Minkowski d)) = Ω := by
  constructor
  · intro h w hw
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩; exact h w hw p hp
    · intro p hp
      exact ⟨p + -w, h _ (ι.neg_mem_perp hw) p hp, by simp⟩
  · intro h w hw p hp
    show p + w ∈ (Ω : Set (Minkowski d))
    rw [← h w hw]; exact ⟨p, hp, rfl⟩

namespace AffineMinkEmbedding

variable (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}

/-- **The base `M = Γ_U\(U ∩ Ω)` of Lemma 5.5**, as a flat spacetime of dimension `d₁ + 1`. -/
noncomputable def baseSpacetime (B : FlatSpacetime.{u} d) [Invariant Γ Ω] [IsCancelSMul Γ Ω]
    [ProperlyDiscontinuousSMul Γ Ω] (hB : IsQuotientOf B Γ Ω) (hres : ι.RestrictsIn Γ)
    (hperp : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω) : FlatSpacetime.{0} d₁ :=
  haveI := ι.connectedSpace_base hB hres hperp
  FlatSpacetime.of (FlatQuotient (ι.restrictGroup Γ) (ι.preimageOpens Ω))

theorem isQuotientOf_baseSpacetime (B : FlatSpacetime.{u} d) [Invariant Γ Ω] [IsCancelSMul Γ Ω]
    [ProperlyDiscontinuousSMul Γ Ω] (hB : IsQuotientOf B Γ Ω) (hres : ι.RestrictsIn Γ)
    (hperp : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω) :
    IsQuotientOf (ι.baseSpacetime B hB hres hperp) (ι.restrictGroup Γ) (ι.preimageOpens Ω) :=
  isQuotientOf _ _

end AffineMinkEmbedding

/-- **Lemma 5.5 (`blem:suspendre`), in its strongest true form**: let `B` be a flat spacetime,
quotient of an open `Ω ⊆ 𝐌ⁿ` by `Γ ≤ Isom(𝐌ⁿ)` acting freely and properly discontinuously; let
`Γ` preserve the timelike affine subspace `U = range ι` (`ι` orthochronous, which loses nothing:
`exists_affineMinkEmbedding_of_isTimelike`), every element restricting to `U` as an
element of `Isom(𝐌^{d₁+1})` (**added**: see `TwistedProduct.not_restrictsIn_glideGroup_of_range`),
and let `Ω` be invariant under the translations by `U^⊥`. Then the quotient `M` of `U ∩ Ω` by `Γ`
is a flat spacetime (`baseSpacetime`) and `B` is the linear twisted product of `M` by `U^⊥`. -/
theorem suspendre {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} (B : FlatSpacetime.{u} d)
    [Invariant Γ Ω] [IsCancelSMul Γ Ω] [ProperlyDiscontinuousSMul Γ Ω] (hB : IsQuotientOf B Γ Ω)
    (ι : AffineMinkEmbedding d₁ d) (hι : ι.Orthochronous) (hres : ι.RestrictsIn Γ)
    (hperp : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω) :
    IsLTPOver B (ι.baseSpacetime B hB hres hperp) :=
  ⟨Γ, Ω, ι, ι.timelikeImage, hι, hres.preserves, hres, hperp, hB,
    ι.isQuotientOf_baseSpacetime B hB hres hperp⟩

/-- **Rem 5.3, causal half** (l.1800–1805): a linear twisted product over a GH flat spacetime is
GH. -/
theorem gh_of_isLTPOver {B : FlatSpacetime.{u} d} {M₁ : FlatSpacetime.{v} d₁}
    (h : IsLTPOver B M₁) (hM : GH M₁) : GH B := by
  sorry -- SORRY(rem:5.3): the causality of a quotient Γ\Ω is not available (Flat.Quotient SCOPE: it needs lifting ≤ on ⊤ through chains of local relations), and comparing ≤_Ω with ≤_{U∩Ω} along the retraction needs reparametrizing the image of a causal curve (a graph over the time of 𝐌ⁿ) as a graph over the time of 𝐌^{d₁+1}; only the linear core `retract_le_top` is proved

/-! ### Non-vacuity: the trivial twisted product, products, a circle bundle -/

namespace AffineMinkEmbedding

/-- The identity of `𝐌ⁿ`, as an isometric affine embedding. -/
noncomputable def refl (d : ℕ) : AffineMinkEmbedding d d := ⟨AffineMap.id ℝ _, fun _ => rfl⟩

@[simp] theorem refl_apply (p : Minkowski d) : refl d p = p := rfl

theorem refl_orthochronous : (refl d).Orthochronous := by
  show (0 : ℝ) < 1; exact one_pos

theorem mem_perp_refl {w : Minkowski d} : w ∈ (refl d).perp ↔ w = 0 :=
  ⟨fun hw => tp_eq_zero_of_minkB fun u => hw u, fun h => h ▸ (refl d).zero_mem_perp⟩

theorem restrictGroup_refl (Γ : Subgroup (isom d)) : (refl d).restrictGroup Γ = Γ := by
  ext g
  refine ⟨fun ⟨γ, hγ, h⟩ => ?_, fun hg => ⟨g, hg, fun _ => rfl⟩⟩
  have : g = γ := Subtype.ext (AffineEquiv.ext h)
  rwa [this]

theorem preimageOpens_refl (Ω : Opens (Minkowski d)) : (refl d).preimageOpens Ω = Ω := rfl

theorem restrictsIn_refl (Γ : Subgroup (isom d)) : (refl d).RestrictsIn Γ :=
  fun γ _ => ⟨γ, fun _ => rfl⟩

/-- Every isometric affine embedding restricts the trivial group. -/
theorem restrictsIn_bot (ι : AffineMinkEmbedding d₁ d) : ι.RestrictsIn ⊥ := fun γ hγ =>
  ⟨1, by rw [Subgroup.mem_bot.1 hγ]; exact Restricts.one⟩

/-- **The time axis** `t ↦ (t, 0)`, `𝐌¹ → 𝐌ⁿ` (`d₁ = 0`). -/
noncomputable def timeAxis (d : ℕ) : AffineMinkEmbedding 0 d where
  toAffineMap := ((LinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin d))) ∘ₗ
    (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 0)))).toAffineMap
  minkQ_linear v := by
    have : v.2 = 0 := Subsingleton.elim _ _
    simp [minkQ, this]

@[simp] theorem timeAxis_apply (p : Minkowski 0) : timeAxis d p = (p.1, 0) := rfl

theorem timeAxis_orthochronous : (timeAxis d).Orthochronous := by
  show (0 : ℝ) < 1; exact one_pos

/-- The time translations of `𝐌ⁿ` restrict to the time axis as the time translations of `𝐌¹`. -/
theorem restrictsIn_timeGroup : (timeAxis d).RestrictsIn (timeGroup d) := by
  rintro _ ⟨n, rfl⟩
  refine ⟨timeTranslation 0 n, fun p => ?_⟩
  rw [timeTranslation_smul, timeTranslation_smul, timeAxis_apply, timeAxis_apply]
  ext <;> simp [timeVec]

end AffineMinkEmbedding

open AffineMinkEmbedding

/-- **The trivial linear twisted product** (`d₁ = d`, `ι = id`, `U^⊥ = 0`): every quotient flat
spacetime is a linear twisted product over itself. -/
theorem isLTPOver_refl (B : FlatSpacetime.{u} d) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hB : IsQuotientOf B Γ Ω) : IsLTPOver B B :=
  ⟨Γ, Ω, refl d, (refl d).timelikeImage, refl_orthochronous, (restrictsIn_refl Γ).preserves,
    restrictsIn_refl Γ,
    fun w hw p hp => by rw [mem_perp_refl.1 hw, add_zero]; exact hp, hB,
    by rw [restrictGroup_refl, preimageOpens_refl]; exact hB⟩

namespace TwistedProduct

/-- The trivial group acts on any open set. -/
instance instInvariantBot (Ω : Opens (Minkowski d)) : Invariant (⊥ : Subgroup (isom d)) Ω :=
  ⟨fun γ p hp => by rw [Subgroup.mem_bot.1 γ.2, one_smul]; exact hp⟩

/-- … freely. -/
instance instIsCancelSMulBot (Ω : Opens (Minkowski d)) :
    IsCancelSMul (⊥ : Subgroup (isom d)) Ω := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  exact fun _ _ _ => Subsingleton.elim _ _

/-- … and properly discontinuously. -/
instance instProperlyDiscontinuousSMulBot (Ω : Opens (Minkowski d)) :
    ProperlyDiscontinuousSMul (⊥ : Subgroup (isom d)) Ω :=
  ⟨fun _ _ => Set.toFinite _⟩

end TwistedProduct

/-- **`𝐌ⁿ` (as `{1}\𝐌ⁿ`) is the trivial linear twisted product over itself.** -/
theorem isLTPOver_refl_minkowski :
    IsLTPOver (toFlatSpacetime (⊥ : Subgroup (isom d)) ⊤ isConnected_top)
      (toFlatSpacetime (⊥ : Subgroup (isom d)) ⊤ isConnected_top) :=
  isLTPOver_refl _ (isQuotientOf_toFlatSpacetime _ _ _)

/-- **A product with `Γ` trivial**: `𝐌ⁿ = 𝐌¹ × ℝᵈ` is the linear twisted product, given by
Lemma 5.5, over the time axis. -/
theorem isLTPOver_bot_timeAxis :
    IsLTPOver (toFlatSpacetime (⊥ : Subgroup (isom d)) ⊤ isConnected_top)
      ((timeAxis d).baseSpacetime _ (isQuotientOf_toFlatSpacetime _ _ isConnected_top)
        (restrictsIn_bot _) fun _ _ _ _ => trivial) :=
  suspendre _ _ _ timeAxis_orthochronous _ _

/-- **A nontrivial `Γ`**: `ℤ e₀\𝐌ⁿ` (a timelike translation) is the linear twisted product, given
by Lemma 5.5, of the timelike circle `ℤ\𝐌¹` by `ℝᵈ`. -/
theorem isLTPOver_timeGroup :
    IsLTPOver (toFlatSpacetime (timeGroup d) ⊤ isConnected_top)
      ((timeAxis d).baseSpacetime _ (isQuotientOf_toFlatSpacetime _ _ isConnected_top)
        restrictsIn_timeGroup fun _ _ _ _ => trivial) :=
  suspendre _ _ _ timeAxis_orthochronous _ _

/-! ### The orientation of `U`: a counterexample to Lemma 5.5 as printed -/

namespace TwistedProduct

/-- The spatial flip `(t, x) ↦ (t, −x)`. -/
noncomputable def flipLin (d : ℕ) : Minkowski d ≃ₗ[ℝ] Minkowski d :=
  LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ) (LinearEquiv.neg ℝ)

@[simp] theorem flipLin_apply (p : Minkowski d) : flipLin d p = (p.1, -p.2) := rfl

theorem det_flipLin : LinearMap.det (flipLin d : Minkowski d →ₗ[ℝ] Minkowski d) = (-1) ^ d := by
  have h : (flipLin d : Minkowski d →ₗ[ℝ] Minkowski d) =
      LinearMap.prodMap LinearMap.id ((-1 : ℝ) • LinearMap.id) :=
    LinearMap.ext fun p => Prod.ext (by simp) (by simp)
  rw [h, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_smul, LinearMap.det_id,
    mul_one, finrank_euclideanSpace_fin]

/-- In even spatial dimension the flip is in `SO₀(1, d)`. -/
theorem flipLin_mem_lorentz (hd : Even d) : flipLin d ∈ lorentz d :=
  ⟨fun v => by simp [minkQ], fun v hv => by simpa [IsFutureCausal, minkQ] using hv,
    by rw [det_flipLin, hd.neg_one_pow]⟩

/-- In odd spatial dimension it is not (determinant `−1`). -/
theorem flipLin_not_mem_lorentz (hd : Odd d) : flipLin d ∉ lorentz d := fun h => by
  have := lorentz.det_eq_one h
  rw [det_flipLin, hd.neg_one_pow] at this
  norm_num at this

/-- The glide `γ (t, x) = (t + 1, −x)` of `𝐌³` (`d = 2`). -/
noncomputable def glideAff : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2 :=
  (flipLin 2).toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (Minkowski 2) (1, 0))

theorem glideAff_apply (p : Minkowski 2) : glideAff p = ((1, 0) : Minkowski 2) + (p.1, -p.2) :=
  rfl

/-- **The glide is an isometry of `𝐌³`** (linear part `diag(1, −1, −1)`, determinant `1`). -/
noncomputable def glide : isom 2 :=
  ⟨glideAff, by
    rw [mem_isom_iff, show glideAff.linear = flipLin 2 from LinearEquiv.ext fun _ => rfl]
    exact flipLin_mem_lorentz even_two⟩

theorem glide_smul (p : Minkowski 2) : glide • p = ((1, 0) : Minkowski 2) + (p.1, -p.2) := rfl

/-- The spatial line `x ↦ x₀ e₁`, `ℝ¹ → ℝ²`. -/
private noncomputable def lineLin : Minkowski 1 →ₗ[ℝ] Minkowski 2 where
  toFun p := (p.1, (p.2 0) • EuclideanSpace.single 0 1)
  map_add' p q := by
    refine Prod.ext rfl ?_
    simp only [Prod.snd_add, PiLp.add_apply, add_smul]
  map_smul' c p := by
    refine Prod.ext rfl ?_
    simp only [Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul]

/-- **The timelike plane `U = {x₂ = 0}` of `𝐌³`**, parametrized by `𝐌²`. -/
noncomputable def plane : AffineMinkEmbedding 1 2 where
  toAffineMap := lineLin.toAffineMap
  minkQ_linear v := by
    simp only [LinearMap.toAffineMap_linear, minkQ, lineLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp

theorem plane_apply (p : Minkowski 1) :
    plane p = (p.1, (p.2 0) • EuclideanSpace.single 0 1) := rfl

theorem glide_smul_plane (p : Minkowski 1) :
    glide • plane p = plane (((1, 0) : Minkowski 1) + (p.1, -p.2)) := by
  rw [glide_smul, plane_apply, plane_apply]
  refine Prod.ext rfl ?_
  simp [neg_smul]

theorem glide_inv_smul_plane (p : Minkowski 1) :
    glide⁻¹ • plane p = plane (((-1, 0) : Minkowski 1) + (p.1, -p.2)) := by
  rw [inv_smul_eq_iff, glide_smul_plane]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp

/-- **The glide preserves `U` and does not restrict to it as an isometry of `𝐌²`**: its restriction
is `(t, x) ↦ (t + 1, −x)`, of determinant `−1`. -/
theorem not_restricts_glide : ¬ ∃ g : isom 1, plane.Restricts glide g := by
  rintro ⟨g, hg⟩
  have hgp : ∀ p, g • p = ((1, 0) : Minkowski 1) + (p.1, -p.2) := fun p =>
    plane.injective (by rw [hg p, glide_smul_plane])
  have hlin : (g : Minkowski 1 ≃ᵃ[ℝ] Minkowski 1).linear = flipLin 1 := LinearEquiv.ext fun v => by
    have := isom_sub (g : Minkowski 1 ≃ᵃ[ℝ] Minkowski 1) 0 v
    rw [sub_zero] at this
    rw [← this, ← isom_smul_def, ← isom_smul_def, hgp, hgp, flipLin_apply]
    refine Prod.ext ?_ ?_ <;> simp
  exact flipLin_not_mem_lorentz odd_one (hlin ▸ g.2)

/-- The group `⟨γ⟩ ≅ ℤ` generated by the glide. -/
noncomputable def glideGroup : Subgroup (isom 2) := Subgroup.zpowers glide

theorem fst_glide_zpow_smul (k : ℤ) (p : Minkowski 2) : ((glide ^ k) • p).1 = p.1 + k := by
  induction k using Int.induction_on generalizing p with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, mul_smul, ih, glide_smul]
    simp only [Prod.fst_add]; push_cast; ring
  | pred n ih =>
    rw [zpow_sub_one, mul_smul, ih]
    have h1 : (glide⁻¹ • p).1 = p.1 - 1 := by
      have := congrArg Prod.fst (smul_inv_smul glide p)
      rw [glide_smul] at this
      simp only [Prod.fst_add] at this
      linarith
    rw [h1]; push_cast; ring

/-- The glide preserves `U`: every power maps `U` into `U`. -/
theorem glide_zpow_smul_plane (k : ℤ) (p : Minkowski 1) :
    ∃ x, (glide ^ k) • plane p = plane x := by
  induction k using Int.induction_on generalizing p with
  | zero => exact ⟨p, by simp⟩
  | succ n ih =>
    rw [zpow_add_one, mul_smul, glide_smul_plane]
    exact ih _
  | pred n ih =>
    rw [zpow_sub_one, mul_smul, glide_inv_smul_plane]
    exact ih _

instance instInvariantGlideGroup : Invariant glideGroup ⊤ := ⟨fun _ _ _ => trivial⟩

/-- The glide group acts freely. -/
instance instIsCancelSMulGlideGroup : IsCancelSMul glideGroup (⊤ : Opens (Minkowski 2)) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨_, k, rfl⟩ x hx
  have h := congrArg (fun q : (⊤ : Opens (Minkowski 2)) => (q : Minkowski 2).1) hx
  simp only [coe_smul, fst_glide_zpow_smul] at h
  have hk : (k : ℝ) = 0 := by linarith
  have hk' : k = 0 := by exact_mod_cast hk
  apply Subtype.ext
  show glide ^ k = 1
  rw [hk', zpow_zero]

/-- The glide group acts properly discontinuously. -/
instance instProperlyDiscontinuousSMulGlideGroup :
    ProperlyDiscontinuousSMul glideGroup (⊤ : Opens (Minkowski 2)) := by
  refine ⟨fun {K L} hK hL => ?_⟩
  have hf : Continuous fun q : (⊤ : Opens (Minkowski 2)) => (q : Minkowski 2).1 :=
    continuous_fst.comp continuous_subtype_val
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨R', hR'⟩ := hL.exists_bound_of_continuousOn hf.continuousOn
  set N : ℤ := ⌈R + R'⌉
  refine ((Set.finite_Icc (-N) N).image fun m : ℤ =>
    (⟨glide ^ m, m, rfl⟩ : glideGroup)).subset ?_
  rintro ⟨_, k, rfl⟩ ⟨_, ⟨q, hq, rfl⟩, hl⟩
  have h1 := hR q hq
  have h2 := hR' _ hl
  simp only [coe_smul, fst_glide_zpow_smul, Real.norm_eq_abs] at h1 h2
  refine ⟨k, ?_, rfl⟩
  have hN : R + R' ≤ (N : ℝ) := Int.le_ceil _
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  have habs : |(k : ℝ)| ≤ (N : ℝ) := abs_le.2 ⟨by linarith, by linarith⟩
  have habs' : |k| ≤ N := by exact_mod_cast habs
  exact ⟨by linarith [neg_abs_le k], (le_abs_self _).trans habs'⟩

/-- **Lemma 5.5 needs the orientation hypothesis** (DEC-27): `Γ = ⟨γ⟩`, `γ (t, x) = (t + 1, −x)`,
acts freely (`instIsCancelSMulGlideGroup`) and properly discontinuously
(`instProperlyDiscontinuousSMulGlideGroup`) on `Ω = 𝐌³`, which is invariant under every
translation; `Γ` preserves the timelike plane `U = {x₂ = 0}`; yet `γ` does not restrict to `U` as
an element of `Isom(𝐌²)` (`SO₀`-affine): its restriction reverses the orientation of `U`, and
`Γ\U` is a non-orientable timelike Möbius strip. -/
theorem not_restrictsIn_glideGroup :
    (∀ γ ∈ glideGroup, (fun p => γ • p) '' Set.range plane = Set.range plane) ∧
      ¬ plane.RestrictsIn glideGroup := by
  refine ⟨?_, fun h => not_restricts_glide (h glide (Subgroup.mem_zpowers glide))⟩
  rintro _ ⟨k, rfl⟩
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    obtain ⟨x, hx⟩ := glide_zpow_smul_plane k p
    exact ⟨x, hx.symm⟩
  · rintro _ ⟨p, rfl⟩
    obtain ⟨x, hx⟩ := glide_zpow_smul_plane (-k) p
    refine ⟨plane x, ⟨x, rfl⟩, ?_⟩
    show glide ^ k • plane x = plane p
    rw [← hx, ← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]

/-- **The counterexample does not depend on the parametrization of `U`**: for every isometric
affine embedding `ι'` with image the plane `U = {x₂ = 0}` (orthochronous or not), the glide does
not restrict to `U` through `ι'` as an element of `Isom(𝐌²)`. Through `ι'` the restriction is
conjugate, by the linear isomorphism `A = P ∘ ι'.lin` (`P` the coordinates along `plane`), to
`(t, x) ↦ (t + 1, −x)`, so its linear part has determinant `det (flipLin 1) = −1`. -/
theorem not_restricts_glide_of_range {ι' : AffineMinkEmbedding 1 2}
    (hU : Set.range ι' = Set.range plane) : ¬ ∃ g : isom 1, ι'.Restricts glide g := by
  rintro ⟨g, hg⟩
  set φ : Minkowski 1 → Minkowski 1 := fun p => plane.retract (ι' p) with hφdef
  have hφ : ∀ p, plane (φ p) = ι' p := fun p => by
    obtain ⟨x, hx⟩ : ι' p ∈ Set.range plane := hU ▸ ⟨p, rfl⟩
    simp only [hφdef, ← hx, AffineMinkEmbedding.retract_apply]
  set A : Minkowski 1 →ₗ[ℝ] Minkowski 1 := plane.coproj ∘ₗ ι'.lin with hAdef
  have hA : ∀ p q, φ q - φ p = A (q - p) := fun p q => by
    simp only [hφdef, hAdef, AffineMinkEmbedding.retract, LinearMap.comp_apply, ← ι'.apply_sub,
      ← map_sub]
    congr 1; abel
  have hA0 : ∀ v, A v = φ v - φ 0 := fun v => by rw [hA, sub_zero]
  have hkey : ∀ p, φ (g • p) = ((1, 0) : Minkowski 1) + ((φ p).1, -(φ p).2) := fun p =>
    plane.injective (by rw [hφ, hg, ← hφ p, glide_smul_plane])
  have hcomm : A ∘ₗ ((g : Minkowski 1 ≃ᵃ[ℝ] Minkowski 1).linear : Minkowski 1 →ₗ[ℝ] Minkowski 1) =
      (flipLin 1 : Minkowski 1 →ₗ[ℝ] Minkowski 1) ∘ₗ A := LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hs := isom_sub (g : Minkowski 1 ≃ᵃ[ℝ] Minkowski 1) 0 v
    rw [sub_zero] at hs
    rw [← hs, ← isom_smul_def, ← isom_smul_def, ← hA, hkey, hkey, hA0, flipLin_apply]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, Prod.snd_sub]; abel
  have hinj : Injective A := by
    have hl : ∀ w, plane.lin (A w) = ι'.lin w := fun w => by
      rw [hA0, ← plane.apply_sub, hφ, hφ, ι'.apply_sub, sub_zero]
    intro u v huv
    apply ι'.lin_injective
    rw [← hl, ← hl, huv]
  have hdet := congrArg LinearMap.det hcomm
  rw [LinearMap.det_comp, LinearMap.det_comp, lorentz.det_eq_one (mem_isom_iff.1 g.2),
    det_flipLin] at hdet
  have h0 : LinearMap.det A = 0 := by norm_num at hdet; linarith
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h0) (LinearMap.ker_eq_bot.2 hinj)

/-- **No parametrization of `U` makes Lemma 5.5's hypotheses (with `RestrictsIn`) hold for the glide
group**: the refutation of `RestrictsIn` is independent of the choice of `ι`. -/
theorem not_restrictsIn_glideGroup_of_range {ι' : AffineMinkEmbedding 1 2}
    (hU : Set.range ι' = Set.range plane) : ¬ ι'.RestrictsIn glideGroup := fun h =>
  not_restricts_glide_of_range hU (h glide (Subgroup.mem_zpowers glide))

end TwistedProduct

end Causal.Flat
