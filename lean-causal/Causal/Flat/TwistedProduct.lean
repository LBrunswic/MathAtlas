import Causal.Flat.Quotient
import Causal.Flat.Examples
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# `Causal.Flat.TwistedProduct` — linear twisted products (Barbot §5.S, Lemma 5.5)

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5.S
"Twisted product by euclidean manifolds" (`produi`) and Lemma 5.5. Line numbers are those of the
**labelled** `papers/barbot/legacy/labeled/GHFspace.tex` (`docs/BARBOT.md` uses the original's).

* **`blem:suspendre`** — `GHFspace.tex:1834` (Lemma 5.5, l.1833–1845), marked (DEC-99: the
  orientation hypothesis `RestrictsIn`, read at the level of `Ω` in the twisted-product form of
  DEC-43; **no `sorry`**) — proved
  (`suspendre`) under one added hypothesis, `RestrictsIn` (every element of `Γ` restricts to `U`
  as an element of `Isom(𝐌^{d₁+1})`, i.e. preserves the orientation of `U`), without which the
  statement is false as written (`TwistedProduct.not_restrictsIn_glideGroup`, and for every
  parametrization of `U`, `TwistedProduct.not_restrictsIn_glideGroup_of_range`; DEC-27); `U` is
  given through an orthochronous parametrization `ι`.
* §5.S (prose, l.1751–1797) — the notion **linear twisted product** in the quotient form of
  `docs/BARBOT-THEOREMS.md` §1: `IsLTPOver`, `IsLTPData`.
* Rem 5.3 (prose, l.1800–1814), causal half, **linear twisted products only** (the remark is
  about twisted products by all euclidean manifolds, flat tori included) — **proved, no
  `sorry`** (`gh_of_isLTPOver`: a linear twisted product over a GH flat spacetime is GH), unmarked
  because narrowed to the linear case: causality (`isCausal_of_isLTPData`) and compact diamonds
  (`isCompact_diamond_of_isLTPData`, through GH lifting to the cover `ι⁻¹ Ω` of `M₁`,
  `TwistedProduct.cover_gh_of_isQuotientOf`, and closed diamonds of `Ω = ι⁻¹ Ω × U^⊥`,
  `isClosed_diamond_of_retract`). Rem 5.4 (l.1816–1828) is about Bieberbach and finite index, not
  causal: not attempted.

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
* **Rem 5.3, causality of the twisted product**: `retract_le_of_le` (`p ≤_Ω p'` gives
  `q p ≤_{ι⁻¹Ω} q p'`: chains in convex balls of `Ω`, segments mapped to segments of `ι⁻¹ Ω`);
  `eq_of_le_top_of_retract_eq` (the fibres of `q` are acausal, `U^⊥` being spacelike); for any
  presentation `π : Ω → M` of a quotient (`IsQuotientOf`'s data, not the constructed
  `FlatQuotient`): `TwistedProduct.exists_lift_le` (the order of `Γ\Ω` lifts) and
  `TwistedProduct.smul_eq_of_le_of_isCausal` (in a causal quotient no `x ≤ γ x` with
  `γ x ≠ x`); hence `isCausal_of_isLTPData`: a linear twisted product over a causal flat
  spacetime is causal.
* **Rem 5.3, descent of compact diamonds**: `isCompact_diamond_of_isLTPData` from the
  cover-level `cover_gh_of_isLTPData`: `J_B(π x, π y)` is the image of
  `⋃_{x ≤ γ y} J_Ω(x, γ y)`, for an arbitrary presentation `π`. `cover_gh_of_isLTPData` is
  proved from `TwistedProduct.cover_gh_of_isQuotientOf` (GH lifts from `M₁` to its cover
  `W = ι⁻¹ Ω`: compact diamonds, finitely many `g` with `a ≤_W g b`) and
  `isClosed_diamond_of_retract` (the diamonds of `Ω = W × U^⊥` are closed); compactness
  (`isCompact_diamond_of_retract`: `J_Ω(x, z) ⊆ J_{𝐌ⁿ}(x, z) ∩ q⁻¹ J_W(q x, q z)`) and
  finiteness (restriction `γ ↦ g`, injective by freeness,
  `TwistedProduct.smul_left_injective_of_isCoveringMap`) are proved from them.
* **Rem 5.3, straight causal segments** (no limit-curve theorem, no time separation): an open
  `W ⊆ 𝐌ⁿ` with compact diamonds is convex along its causal relations
  (`TwistedProduct.le_top_and_segment_subset_of_le`: `p ≤_W q` ⟹ `[p, q] ⊆ W`; two causal
  segments span the third side, `segment_subset_trans_of_isCompact_diamond`), so
  `J_Ω(x, z) = {p : x ≤ p ≤ z in 𝐌ⁿ, q p ∈ J_W(q x, q z)}` is closed
  (`isClosed_diamond_of_retract`). For a GH quotient `M = π(Ω)` the same convexity holds in `Ω`
  (`segment_subset_trans_of_isQuotientOf`), the compact diamond replaced by `π⁻¹ J_M`: a causal
  segment of `Ω` whose image stays in a compact set of `M` cannot leave `Ω`
  (`segment_subset_of_subset_closure`: a causally monotone path imprisoned in a compact set of
  `M` converges in `Ω`, `exists_tendsto_of_monotone`, by uniqueness of lifts; `J^±` of `M` are
  closed, `isClosed_le_of_isCompact_diamond`), nor run to infinity (`not_forall_ray`); hence
  `cover_gh_of_isQuotientOf` (diamonds of `Ω` closed and bounded; the `g b` with `a ≤_Ω g b` lie
  in a compact set of `Ω` and in one fibre of `π`, so finitely many).
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
| `blem:suspendre` (**marked**, DEC-99) | ⚠ strengthened by ruling: the orientation hypothesis `RestrictsIn ι Γ` (next row), carried; the glide/Möbius counterexample (`not_restrictsIn_glideGroup_of_range`) is a **finding**. ⚠ reading: "`B` is the linear twisted product of `M` by `U^⊥`" in DEC-43's quotient form `IsLTPOver` (the base `Γ_U\(U ∩ Ω)`), the suspension proved at the level of `Ω` (`split`, `split_smul`, `mem_iff_retract_mem`: `Ω = (U ∩ Ω) × U^⊥`, `Γ` diagonal), not descended to a bundle map `B → M` |
| `Γ` preserves a timelike affine subspace `U` (l.1839) | ⚠ strengthened: `RestrictsIn ι Γ` (restriction in `SO₀`-affine isometries, i.e. `Γ` preserves the orientation of `U`); implies the preservation (`RestrictsIn.preserves`); necessary (`not_restrictsIn_glideGroup_of_range`, every parametrization). `U` is read as `range ι`, `ι : AffineMinkEmbedding d₁ d` orthochronous (`hι`); this loses no timelike affine subspace (`timelikeImage`, `exists_affineMinkEmbedding_of_isTimelike`) |
| `Ω` invariant by translations by `U^⊥` (l.1840–1841) | ✓ carried: `∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω` (`perpInvariant_iff`: the form `Ω + w = Ω`) |

Note (not a paper hypothesis): `Ω` is not asked to be connected; `M` is connected because `B` is
(`connectedSpace_base`).

## SCOPE (disclosed)

* **Ruled DEC-99 (2026-11-02):** `blem:suspendre` is marked with the orientation hypothesis
  `RestrictsIn`, read at the level of `Ω` in the twisted-product form of DEC-43; the glide/Möbius
  counterexample stays as a finding (next bullet).
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
  orientation of `ι` is not asked: it is not canonical (it depends on an orientation of `U^⊥`),
  and `RestrictsIn` (orientation of `U` preserved by `Γ`) does not depend
  on it. That `RestrictsIn` does not depend on the choice of `ι` for a given `U` is not proved in
  general (it is for the counterexample, `not_restrictsIn_glideGroup_of_range`).
* **The quotient form.** `IsLTPOver` is BARBOT-THEOREMS §1's quotient form (adopted by DEC-43's
  reading R1), not §5.S's suspension of `M̃ × N` by `π₁(M)`: the base is `Γ_U\(U ∩ Ω)`, and
  `U ∩ Ω` need not be the universal cover of `M`, nor `Γ_U` its fundamental group. The suspension
  structure is proved at the level of `Ω` (`split`, `split_smul`, `mem_iff_retract_mem`) and not
  descended to a fibre-bundle map `q : B → M` (only its continuity and surjectivity, inside
  `connectedSpace_base`). `restrictGroup Γ` is the image of `Γ`; the injectivity of `γ ↦ g`
  (true when `U ∩ Ω ≠ ∅`, by freeness) is not stated as a lemma; it is used, at a point of
  `U ∩ Ω`, inside `cover_gh_of_isLTPData` (`TwistedProduct.smul_left_injective_of_isCoveringMap`).
* **`U^⊥`-invariance of `Ω` (BARBOT-THEOREMS §6, G6)** is *carried* here as the hypothesis
  `perp_invariant`; its proof for the domains `Ω(S̃)` where Lemma 5.5 is applied is owed
  downstream, not discharged in this file.
* **Rem 5.3** (`gh_of_isLTPOver`, proved, no `sorry`) is stated for *linear* twisted products
  only (the remark covers twisted products by every euclidean manifold, flat tori included), so
  it is not marked. It is not proved by Barbot's route (`t ∘ q` a proper time function,
  l.1801–1804, which would need Geroch (iii)⇒(i), a cited `sorry` in `GerochEquiv`), but at the
  level of the cover: `cover_gh_of_isLTPData` (compact diamonds of `Ω`, finiteness of
  `{γ | x ≤_Ω γ y}`), the hypotheses of the descent `isCompact_diamond_of_isLTPData`, from the
  general `TwistedProduct.cover_gh_of_isQuotientOf` (GH lifts from any `IsQuotientOf`
  presentation to its cover; the converse of `FlatQuotient.globallyHyperbolic_quotient`) and
  `isClosed_diamond_of_retract`. Neither uses a limit-curve theorem nor the time separation: in
  a flat setting the causal relations of a GH open set are straight segments, which is what
  replaces them. `exists_isOpen_le_and_ge` stands in for the tarentin property of a flat
  quotient, which the library does not prove. Rem 5.3's Cauchy-completeness half (D, DEC-35) and
  Rem 5.4 are not attempted.
* Generic `minkB` algebra is `private` (`tp_…`), to avoid colliding with `Flat/AchronalDomains`;
  it duplicates `Flat/Isometries`' public `minkB` lemmas and `minkForm` (`tpBilinOn` is `minkForm`
  restricted to `W`). `Flat/Isometries` is deliberately not imported: it is being edited in
  parallel. The import closure is `Flat.Quotient` and `Flat.Examples` (the earlier policy of
  keeping the closure at `Flat.Quotient` is deliberately reversed for `Flat.Examples`, whose
  concurrent edits this wave are proofs-only, so the statements used here cannot move; for
  `flat_le_top_subtype_iff`, `FlatQuotient.le_top_smul`, `FlatQuotient.isCausal_subtype`, and,
  through `Flat.Penrose`, `le_of_le_top_of_segment_subset`); `TwistedProduct.exists_lift_le`
  re-proves `FlatQuotient.exists_lift_le` for an arbitrary presentation `π` (it is stated there
  for the constructed quotient only, under its instances).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 2, package WP-31d-TwistedProduct; closer pass 2026-11-01 (causality half of Rem 5.3;
descent of the compact diamonds from `Ω`); second closer pass 2026-11-01 (the cover-level
`sorry` split: finiteness and compactness proved from GH of the cover `ι⁻¹ Ω` and closed
diamonds of `Ω`); third closer pass 2026-11-01 (both remaining `sorry`s closed by straight
causal segments: the file is `sorry`-free).
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

/-! ### Rem 5.3, causal half: the causality of a linear twisted product -/

/-! #### Causal segments of an open set of `𝐌ⁿ` with compact diamonds -/

namespace TwistedProduct

/-- **Two causal segments of an open `W ⊆ 𝐌ⁿ` with compact diamonds span the third side**: if
`a ≤ c ≤ b` in `𝐌ⁿ` and `[a, c]`, `[c, b] ⊆ W`, then `[a, b] ⊆ W`. Sweep `[a, c]` to `[a, b]`
through the segments `[a, c_s]`, `c_s = c + s (b − c)`: the set of `s` with `[a, c_s] ⊆ W` is
open (`W` open, `[0, 1]` compact) and closed in `[0, 1]`, because each such segment lies in the
compact diamond `J_W(a, b)` (`a ≤_W y ≤_W c_s ≤_W b` along straight segments of `W`). -/
theorem segment_subset_trans_of_isCompact_diamond {W : Opens (Minkowski d)}
    (hW : ∀ a b : W, IsCompact ((flatCausality d W).diamond ⊤ a b))
    {a c b : Minkowski d} (hac : (minkowski d).le ⊤ a c) (hcb : (minkowski d).le ⊤ c b)
    (hsac : segment ℝ a c ⊆ W) (hscb : segment ℝ c b ⊆ W) : segment ℝ a b ⊆ W := by
  have haW : a ∈ W := hsac (left_mem_segment ℝ a c)
  have hbW : b ∈ W := hscb (right_mem_segment ℝ c b)
  set K : Set (Minkowski d) := ((↑) : W → Minkowski d) ''
    (flatCausality d W).diamond ⊤ ⟨a, haW⟩ ⟨b, hbW⟩ with hKdef
  have hKc : IsClosed K := ((hW _ _).image continuous_subtype_val).isClosed
  have hKW : K ⊆ W := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hmemK : ∀ y (hy : y ∈ W), (minkowski d).le W a y → (minkowski d).le W y b → y ∈ K := by
    intro y hy h1 h2
    refine ⟨⟨y, hy⟩, Causality.mem_diamond.2 ⟨?_, ?_⟩, rfl⟩
    · rw [flat_le_top_subtype_iff]; exact h1
    · rw [flat_le_top_subtype_iff]; exact h2
  set g : ℝ → ℝ := fun s => max 0 (min s 1) with hgdef
  have hg : Continuous g := continuous_const.max (continuous_id.min continuous_const)
  have hg01 : ∀ s, g s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  set cs : ℝ → Minkowski d := fun s => c + g s • (b - c) with hcsdef
  set F : ℝ × ℝ → Minkowski d := fun z => a + z.2 • (cs z.1 - a) with hFdef
  have hF : Continuous F :=
    continuous_const.add (continuous_snd.smul
      ((continuous_const.add ((hg.comp continuous_fst).smul continuous_const)).sub
        continuous_const))
  set u : Set ℝ := {s | ∀ θ ∈ Icc (0 : ℝ) 1, F (s, θ) ∈ W} with hudef
  have hcs : ∀ s, cs s ∈ segment ℝ c b := fun s => by
    rw [segment_eq_image']; exact ⟨g s, hg01 s, rfl⟩
  have hseg : ∀ s, segment ℝ a (cs s) = (fun θ => F (s, θ)) '' Icc 0 1 := fun s => by
    rw [segment_eq_image']
  have hacs : ∀ s, (minkowski d).le ⊤ a (cs s) := fun s =>
    (minkowski d).le_trans hac (le_top_of_mem_segment hcb (hcs s)).1
  -- `u` is open
  have huo : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    have : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ᶠ z : ℝ × ℝ in 𝓝 (s₀, θ), F z ∈ W := fun θ hθ =>
      hF.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds (hs₀ θ hθ))
    exact isCompact_Icc.eventually_forall_of_forall_eventually this
  -- the segments of `u` lie in the compact diamond `J_W(a, b)`
  have hmaps : ∀ θ ∈ Icc (0 : ℝ) 1, MapsTo (fun s => F (s, θ)) u K := by
    intro θ hθ s hs
    have hsW : segment ℝ a (cs s) ⊆ W := by
      rw [hseg]; rintro _ ⟨θ', hθ', rfl⟩; exact hs θ' hθ'
    have hy : F (s, θ) ∈ segment ℝ a (cs s) := by rw [hseg]; exact ⟨θ, hθ, rfl⟩
    obtain ⟨h1, h2⟩ := le_top_of_mem_segment (hacs s) hy
    have hcsb := (le_top_of_mem_segment hcb (hcs s)).2
    refine hmemK _ (hsW hy) (le_of_le_top_of_segment_subset h1 fun z hz =>
      hsW ((convex_segment _ _).segment_subset (left_mem_segment _ _ _) hy hz)) ?_
    exact (minkowski d).le_trans (le_of_le_top_of_segment_subset h2 fun z hz =>
        hsW ((convex_segment _ _).segment_subset hy (right_mem_segment _ _ _) hz))
      (le_of_le_top_of_segment_subset hcsb fun z hz =>
        hscb ((convex_segment _ _).segment_subset (hcs s) (right_mem_segment _ _ _) hz))
  -- `u` is closed in `[0, 1]`
  have hcl : closure u ∩ Icc 0 1 ⊆ u := by
    intro s hs θ hθ
    have := map_mem_closure (hF.comp (Continuous.prodMk_left θ)) hs.1 (hmaps θ hθ)
    rw [hKc.closure_eq] at this
    exact hKW this
  have h0 : (Icc (0 : ℝ) 1 ∩ u).Nonempty := by
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, fun θ hθ => hsac ?_⟩
    rw [segment_eq_image']
    exact ⟨θ, hθ, by simp [hFdef, hcsdef, hgdef]⟩
  have hsub := isPreconnected_Icc.subset_of_closure_inter_subset huo h0 hcl
  rw [segment_eq_image']
  rintro _ ⟨θ, hθ, rfl⟩
  have := hsub ⟨zero_le_one, le_rfl⟩ θ hθ
  simpa [hFdef, hcsdef, hgdef] using this

/-- **Causal relations are straight segments once two consecutive segments span a third**: on an
open `W ⊆ 𝐌ⁿ` in which `[a, c]`, `[c, b] ⊆ W` with `a ≤ c ≤ b` force `[a, b] ⊆ W`, a relation
`p ≤_W q` gives `p ≤ q` in `𝐌ⁿ` and `[p, q] ⊆ W`. A relation of `≤_W` is a chain of causal
segments in convex balls of `W` (absolute minimality), merged one at a time by the hypothesis. -/
theorem le_top_and_segment_subset_of_le_of_trans {W : Opens (Minkowski d)}
    (htrans : ∀ {a c b : Minkowski d}, (minkowski d).le ⊤ a c → (minkowski d).le ⊤ c b →
      segment ℝ a c ⊆ W → segment ℝ c b ⊆ W → segment ℝ a b ⊆ W) {p q : Minkowski d}
    (h : (minkowski d).le W p q) : (minkowski d).le ⊤ p q ∧ segment ℝ p q ⊆ W := by
  let S : Set (Opens (Minkowski d)) := {O | Convex ℝ (O : Set (Minkowski d)) ∧ O ≤ W}
  have hS : ∀ x ∈ W, ∃ O ∈ S, x ∈ O := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 W.isOpen x hx
    exact ⟨⟨Metric.ball x ε, Metric.isOpen_ball⟩, ⟨convex_ball x ε, hball⟩,
      Metric.mem_ball_self hε⟩
  have hch := ((minkowski_causallyArcConnected.absolutelyMinimalOn_all W) S hS W le_rfl p q).1 h
  have step : ∀ a b, (∃ O ∈ S, (minkowski d).le (W ⊓ O) a b) →
      (minkowski d).le ⊤ a b ∧ segment ℝ a b ⊆ W := by
    rintro a b ⟨O, ⟨hOc, hOW⟩, hab⟩
    rw [inf_eq_right.2 hOW] at hab
    obtain ⟨ha, hb, hab'⟩ := (le_iff_of_convex hOc).1 hab
    exact ⟨hab', fun y hy => hOW (hOc.segment_subset ha hb hy)⟩
  clear h
  induction hch with
  | single hab => exact step _ _ hab
  | tail _ hbc ih =>
    obtain ⟨h1, h2⟩ := step _ _ hbc
    exact ⟨(minkowski d).le_trans ih.1 h1, htrans ih.1 h1 ih.2 h2⟩

/-- **An open `W ⊆ 𝐌ⁿ` with compact diamonds is convex along its causal relations**: `p ≤_W q`
gives `p ≤ q` in `𝐌ⁿ` and `[p, q] ⊆ W` (`le_top_and_segment_subset_of_le_of_trans` with
`segment_subset_trans_of_isCompact_diamond`). (The flat shadow of Avez–Seifert: in a GH open
subset of `𝐌ⁿ` causally related points are joined by a straight causal segment.) -/
theorem le_top_and_segment_subset_of_le {W : Opens (Minkowski d)}
    (hW : ∀ a b : W, IsCompact ((flatCausality d W).diamond ⊤ a b)) {p q : Minkowski d}
    (h : (minkowski d).le W p q) : (minkowski d).le ⊤ p q ∧ segment ℝ p q ⊆ W :=
  le_top_and_segment_subset_of_le_of_trans
    (fun hac hcb hsac hscb => segment_subset_trans_of_isCompact_diamond hW hac hcb hsac hscb) h

/-- The closed future causal cone of `𝐌ⁿ`. -/
theorem isClosed_isFutureCausal : IsClosed {v : Minkowski d | IsFutureCausal v} :=
  (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_minkQ continuous_const)

end TwistedProduct

namespace AffineMinkEmbedding

variable (ι : AffineMinkEmbedding d₁ d)

/-- **The retraction is a causal map of the open sets** `Ω → U ∩ Ω` (orthochronous `ι`, `Ω`
invariant by `U^⊥`): `p ≤_Ω p'` in `𝐌ⁿ` gives `q p ≤_{ι⁻¹ Ω} q p'` in `𝐌^{d₁+1}`. A relation of
`≤_Ω` is a chain of relations in convex balls of `Ω` (absolute minimality); `q` maps each to a
causal relation (`retract_le_top`) whose segment is the image of a segment of `Ω`, hence lies in
`ι⁻¹ Ω` (`mem_iff_retract_mem`). -/
theorem retract_le_of_le (hι : ι.Orthochronous) {Ω : Opens (Minkowski d)}
    (hperp : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω) {p p' : Minkowski d}
    (h : (minkowski d).le Ω p p') :
    (minkowski d₁).le (ι.preimageOpens Ω) (ι.retract p) (ι.retract p') := by
  let S : Set (Opens (Minkowski d)) := {O | Convex ℝ (O : Set (Minkowski d)) ∧ O ≤ Ω}
  have hS : ∀ x ∈ Ω, ∃ O ∈ S, x ∈ O := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
    exact ⟨⟨Metric.ball x ε, Metric.isOpen_ball⟩, ⟨convex_ball x ε, hball⟩,
      Metric.mem_ball_self hε⟩
  have hch := ((minkowski_causallyArcConnected.absolutelyMinimalOn_all Ω) S hS Ω le_rfl p p').1 h
  have step : ∀ a b, (∃ O ∈ S, (minkowski d).le (Ω ⊓ O) a b) →
      (minkowski d₁).le (ι.preimageOpens Ω) (ι.retract a) (ι.retract b) := by
    rintro a b ⟨O, ⟨hOc, hOΩ⟩, hab⟩
    rw [inf_eq_right.2 hOΩ] at hab
    obtain ⟨ha, hb, hab'⟩ := (le_iff_of_convex hOc).1 hab
    refine le_of_le_top_of_segment_subset (ι.retract_le_top hι hab') ?_
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    have hmem : a + θ • (b - a) ∈ O := by
      apply hOc.segment_subset ha hb
      rw [segment_eq_image']
      exact ⟨θ, hθ, rfl⟩
    have he : ι.retract a + θ • (ι.retract b - ι.retract a) = ι.retract (a + θ • (b - a)) := by
      simp only [retract, map_sub, map_add, map_smul, smul_sub]
      abel
    show ι.retract a + θ • (ι.retract b - ι.retract a) ∈ ι.preimageOpens Ω
    rw [he]
    exact (ι.mem_iff_retract_mem hperp).1 (hOΩ hmem)
  clear h
  induction hch with
  | single hab => exact step _ _ hab
  | tail _ hbc ih => exact (minkowski d₁).le_trans ih (step _ _ hbc)

/-- **The fibres of the retraction are acausal**: a causal relation `p ≤ p'` of `𝐌ⁿ` with
`q p = q p'` is trivial, because `p' − p` then lies in the spacelike `U^⊥`. -/
theorem eq_of_le_top_of_retract_eq {p p' : Minkowski d} (h : (minkowski d).le ⊤ p p')
    (he : ι.retract p = ι.retract p') : p = p' := by
  have hv := le_top_iff_minkQ.1 h
  have h0 : ι.coproj (p' - p) = 0 := by
    have : ι.coproj (p' - p) = ι.retract p' - ι.retract p := by
      simp only [retract, ← map_sub]
      congr 1
      abel
    rw [this, he, sub_self]
  have hw : p' - p ∈ ι.perp := by
    have := ι.sub_lin_coproj_mem_perp (p' - p)
    rwa [h0, map_zero, sub_zero] at this
  by_contra hne
  have hpos := ι.minkQ_pos_of_mem_perp hw (sub_ne_zero.2 (Ne.symm hne))
  linarith [hv.2]

/-- **The diamonds of `Ω = (U ∩ Ω) × U^⊥` are closed** in `𝐌ⁿ` when those of `W = ι⁻¹ Ω` are
compact (`Ω` invariant by `U^⊥`, `ι` orthochronous): the Lorentzian product of a GH `W` with the
euclidean `U^⊥` is GH. A limit `p` of `J_Ω(x, z)` lies in the closed
`J_{𝐌ⁿ}(x, z) ∩ q⁻¹ J_W(q x, q z)`, so `q x ≤_W q p ≤_W q z`; `W` having compact diamonds, these
relations are straight segments of `W` (`TwistedProduct.le_top_and_segment_subset_of_le`), whose
`U^⊥`-translates `[x, p]`, `[p, z]` lie in `Ω` (`mem_iff_retract_mem`) and are causal in
`𝐌ⁿ`. -/
theorem isClosed_diamond_of_retract (hι : ι.Orthochronous) {Ω : Opens (Minkowski d)}
    (hperp : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω)
    (hW : ∀ a b : ι.preimageOpens Ω,
      IsCompact ((flatCausality d₁ (ι.preimageOpens Ω)).diamond ⊤ a b)) (x z : Ω) :
    IsClosed (((↑) : Ω → Minkowski d) '' (flatCausality d Ω).diamond ⊤ x z) := by
  have hmem : ∀ p : Ω, ι.retract p ∈ ι.preimageOpens Ω := fun p =>
    (ι.mem_iff_retract_mem hperp).1 p.2
  let a : ι.preimageOpens Ω := ⟨ι.retract x, hmem x⟩
  let b : ι.preimageOpens Ω := ⟨ι.retract z, hmem z⟩
  have hK : IsClosed ((minkowski d).diamond ⊤ (x : Minkowski d) z) :=
    (minkowski_globallyHyperbolic.2 _ _).isClosed
  have hC : IsClosed (ι.retract ⁻¹'
      (((↑) : ι.preimageOpens Ω → Minkowski d₁) '' (flatCausality d₁ _).diamond ⊤ a b)) :=
    ((hW a b).image continuous_subtype_val).isClosed.preimage ι.continuous_retract
  -- the diamond lies in the closed `J_{𝐌ⁿ}(x, z) ∩ q⁻¹ J_W(q x, q z)`
  have hsub : ((↑) : Ω → Minkowski d) '' (flatCausality d Ω).diamond ⊤ x z ⊆
      (minkowski d).diamond ⊤ (x : Minkowski d) z ∩ ι.retract ⁻¹'
        (((↑) : ι.preimageOpens Ω → Minkowski d₁) '' (flatCausality d₁ _).diamond ⊤ a b) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Causality.mem_diamond] at hp
    have h1 := (flat_le_top_subtype_iff Ω x p).1 hp.1
    have h2 := (flat_le_top_subtype_iff Ω p z).1 hp.2
    refine ⟨Causality.mem_diamond.2
      ⟨(minkowski d).le_mono le_top h1, (minkowski d).le_mono le_top h2⟩,
      ⟨ι.retract p, hmem p⟩, Causality.mem_diamond.2 ⟨?_, ?_⟩, rfl⟩
    · rw [flat_le_top_subtype_iff]; exact ι.retract_le_of_le hι hperp h1
    · rw [flat_le_top_subtype_iff]; exact ι.retract_le_of_le hι hperp h2
  -- a segment whose retraction lies in `W` lies in `Ω`
  have hseg : ∀ {u v : Minkowski d},
      segment ℝ (ι.retract u) (ι.retract v) ⊆ ι.preimageOpens Ω → segment ℝ u v ⊆ Ω := by
    intro u v h y hy
    rw [segment_eq_image'] at hy
    obtain ⟨θ, hθ, rfl⟩ := hy
    have he : ι.retract (u + θ • (v - u)) =
        ι.retract u + θ • (ι.retract v - ι.retract u) := by
      simp only [retract, map_sub, map_add, map_smul, smul_sub]
      abel
    refine (ι.mem_iff_retract_mem hperp).2 ?_
    rw [he]
    apply h
    rw [segment_eq_image']
    exact ⟨θ, hθ, rfl⟩
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨hpK, r, hr, hrp⟩ := closure_minimal hsub (hK.inter hC) hp
  rw [Causality.mem_diamond] at hpK hr
  have hpΩ : p ∈ Ω := (ι.mem_iff_retract_mem hperp).2 (hrp ▸ r.2)
  have h1 := (flat_le_top_subtype_iff _ a r).1 hr.1
  have h2 := (flat_le_top_subtype_iff _ r b).1 hr.2
  rw [hrp] at h1 h2
  have s1 := (TwistedProduct.le_top_and_segment_subset_of_le hW h1).2
  have s2 := (TwistedProduct.le_top_and_segment_subset_of_le hW h2).2
  refine ⟨⟨p, hpΩ⟩, Causality.mem_diamond.2 ⟨?_, ?_⟩, rfl⟩
  · rw [flat_le_top_subtype_iff]
    exact le_of_le_top_of_segment_subset hpK.1 (hseg (u := x) s1)
  · rw [flat_le_top_subtype_iff]
    exact le_of_le_top_of_segment_subset hpK.2 (hseg (v := z) s2)

/-- **The diamonds of `Ω = (U ∩ Ω) × U^⊥` are compact** when those of `W = ι⁻¹ Ω` are (`Ω`
invariant by `U^⊥`, `ι` orthochronous). `J_Ω(x, z)` lies in the compact
`J_{𝐌ⁿ}(x, z) ∩ q⁻¹ J_W(q x, q z)` (`retract_le_of_le`) and is closed
(`isClosed_diamond_of_retract`). -/
theorem isCompact_diamond_of_retract (hι : ι.Orthochronous) {Ω : Opens (Minkowski d)}
    (hperp : ∀ w ∈ ι.perp, ∀ p ∈ Ω, p + w ∈ Ω)
    (hW : ∀ a b : ι.preimageOpens Ω,
      IsCompact ((flatCausality d₁ (ι.preimageOpens Ω)).diamond ⊤ a b)) (x z : Ω) :
    IsCompact ((flatCausality d Ω).diamond ⊤ x z) := by
  have hmem : ∀ p : Ω, ι.retract p ∈ ι.preimageOpens Ω := fun p =>
    (ι.mem_iff_retract_mem hperp).1 p.2
  let a : ι.preimageOpens Ω := ⟨ι.retract x, hmem x⟩
  let b : ι.preimageOpens Ω := ⟨ι.retract z, hmem z⟩
  have hK : IsCompact ((minkowski d).diamond ⊤ (x : Minkowski d) z) :=
    minkowski_globallyHyperbolic.2 _ _
  have hC : IsClosed (ι.retract ⁻¹'
      (((↑) : ι.preimageOpens Ω → Minkowski d₁) '' (flatCausality d₁ _).diamond ⊤ a b)) :=
    ((hW a b).image continuous_subtype_val).isClosed.preimage ι.continuous_retract
  rw [Subtype.isCompact_iff]
  refine (hK.inter_right hC).of_isClosed_subset
    (ι.isClosed_diamond_of_retract hι hperp hW x z) ?_
  rintro _ ⟨p, hp, rfl⟩
  rw [Causality.mem_diamond] at hp
  have h1 := (flat_le_top_subtype_iff Ω x p).1 hp.1
  have h2 := (flat_le_top_subtype_iff Ω p z).1 hp.2
  refine ⟨Causality.mem_diamond.2
    ⟨(minkowski d).le_mono le_top h1, (minkowski d).le_mono le_top h2⟩,
    ⟨ι.retract p, hmem p⟩, Causality.mem_diamond.2 ⟨?_, ?_⟩, rfl⟩
  · rw [flat_le_top_subtype_iff]; exact ι.retract_le_of_le hι hperp h1
  · rw [flat_le_top_subtype_iff]; exact ι.retract_le_of_le hι hperp h2

end AffineMinkEmbedding

namespace TwistedProduct

open FlatQuotient

section Lift

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
  {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} [Invariant Γ Ω] {π : Ω → M}

omit [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
  [Invariant Γ Ω] in
/-- A covering map is injective on an open neighbourhood of every point. -/
theorem exists_injOn_of_isCoveringMap (hcov : IsCoveringMap π) (x : Ω) :
    ∃ U : Opens Ω, x ∈ U ∧ InjOn π U := by
  obtain ⟨e, hx, he⟩ := hcov.isLocalHomeomorph x
  exact ⟨⟨e.source, e.open_source⟩, hx, he ▸ e.injOn⟩

/-- **The causal order of a quotient lifts**, for any `π : Ω → M` presenting `M` as `Γ\Ω`
(`IsQuotientOf`'s data: a surjective covering map and local isometry whose fibres are the
`Γ`-orbits): if `π x ≤ q` on `⊤`, some lift `y` of `q` has `x ≤ y` in `Ω`. This is
`FlatQuotient.exists_lift_le` (`Flat/Examples`) for an arbitrary presentation, without the
instances of the constructed quotient. -/
theorem exists_lift_le (hcov : IsCoveringMap π) (hloc : IsLocalIsometry d π)
    (hsurj : Surjective π) (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q)
    {x : Ω} {q : M} (h : (flatCausality d M).le ⊤ (π x) q) :
    ∃ y : Ω, π y = q ∧ (flatCausality d Ω).le ⊤ x y := by
  let S : Set (Opens M) := {O | ∃ U : Opens Ω, InjOn π U ∧ (O : Set M) = π '' U}
  have hS : ∀ z ∈ (⊤ : Opens M), ∃ O ∈ S, z ∈ O := by
    intro z _
    obtain ⟨x', rfl⟩ := hsurj z
    obtain ⟨U, hxU, hU⟩ := exists_injOn_of_isCoveringMap hcov x'
    exact ⟨⟨π '' U, hloc.isOpenMap _ U.2⟩, ⟨U, hU, rfl⟩, x', hxU, rfl⟩
  have step : ∀ {O : Opens M}, O ∈ S → ∀ {a b : M}, (flatCausality d M).le O a b →
      ∀ {x : Ω}, π x = a → ∃ y : Ω, π y = b ∧ (flatCausality d Ω).le ⊤ x y := by
    rintro O ⟨U, hU, hOU⟩ a b hab x hx
    have hO' : O = ⟨π '' U, hloc.isOpenMap _ U.2⟩ := Opens.ext hOU
    subst hO'
    obtain ⟨u, hu, rfl⟩ := (flatCausality d M).le_mem_left hab
    obtain ⟨v, hv, rfl⟩ := (flatCausality d M).le_mem_right hab
    have hf : IsIsometricEmbedding d (π ∘ (Subtype.val : U → Ω)) :=
      ⟨hloc.comp (isLocalIsometry_subtype_val U), fun u v huv => Subtype.ext (hU u.2 v.2 huv)⟩
    have h1 := ((hf.rel_iff ⊤ ⟨π '' U, hloc.isOpenMap _ U.2⟩ (by
      simp only [Opens.coe_top, image_univ, Opens.coe_mk]
      rw [range_comp, Subtype.range_coe]) ⟨u, hu⟩ ⟨v, hv⟩).1).2 hab
    have h2 := (((isIsometricEmbedding_subtype_val (d := d) U).rel_iff ⊤ U
      (by rw [Opens.coe_top, image_univ, Subtype.range_coe]) ⟨u, hu⟩ ⟨v, hv⟩).1).1 h1
    have huv : (flatCausality d Ω).le ⊤ u v := (flatCausality d Ω).le_mono le_top h2
    obtain ⟨γ, hγ, hγx⟩ := (hfib u x).1 hx.symm
    have e1 : ((⟨γ, hγ⟩ : Γ) • u) = x := Subtype.ext (by rw [coe_smul]; exact hγx)
    refine ⟨(⟨γ, hγ⟩ : Γ) • v, ((hfib v _).2 ⟨γ, hγ, rfl⟩).symm, ?_⟩
    have := le_top_smul Γ Ω ⟨γ, hγ⟩ huv
    rwa [e1] at this
  have hch := ((Precausality.absolutelyMinimal_iff.1
    (flatCausality_absolutelyMinimal (d := d) (M := M))) S hS ⊤ le_rfl (π x) q).1 h
  clear h
  induction hch with
  | single hab =>
    obtain ⟨O, hO, hle⟩ := hab
    exact step hO ((flatCausality d M).le_mono inf_le_right hle) rfl
  | tail _ hbc ih =>
    obtain ⟨y, hy, hxy⟩ := ih
    obtain ⟨O, hO, hle⟩ := hbc
    obtain ⟨z, hz, hyz⟩ := step hO ((flatCausality d M).le_mono inf_le_right hle) hy
    exact ⟨z, hz, (flatCausality d Ω).le_trans hxy hyz⟩

/-- **A causal quotient has an acausal action**: if `M = Γ\Ω` (any presentation `π`) is causal,
no `x` is related to a distinct point `γ x` of its orbit. A relation `x ≤ γ x` of `Ω` is a chain
of relations in sheets of `π`; each intermediate point lies between `π x` and `π (γ x) = π x`,
hence projects to `π x` (causality of `M`), and two points of a sheet with the same projection
are equal. -/
theorem smul_eq_of_le_of_isCausal (hcov : IsCoveringMap π) (hloc : IsLocalIsometry d π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q)
    (hM : (flatCausality d M).IsCausal) {a : Ω} {g : Γ}
    (h : (flatCausality d Ω).le ⊤ a (g • a)) : g • a = a := by
  have hpush : ∀ {b c : Ω}, (flatCausality d Ω).le ⊤ b c → (flatCausality d M).le ⊤ (π b) (π c) :=
    fun hbc => hloc.strongMorphism.le_of_mapsTo (U := ⊤) (V := ⊤) (fun _ _ => trivial) hbc
  have hga : π (g • a) = π a := ((hfib a (g • a)).2 ⟨g, g.2, rfl⟩).symm
  let S : Set (Opens Ω) := {U | InjOn π U}
  have hS : ∀ z ∈ (⊤ : Opens Ω), ∃ O ∈ S, z ∈ O := by
    intro z _
    obtain ⟨U, hzU, hU⟩ := exists_injOn_of_isCoveringMap hcov z
    exact ⟨U, hU, hzU⟩
  have hch := ((Precausality.absolutelyMinimal_iff.1
    (flatCausality_absolutelyMinimal (d := d) (M := Ω))) S hS ⊤ le_rfl a (g • a)).1 h
  -- one step from `a` to a point below `g • a` does not move
  have step : ∀ {c : Ω}, (∃ O ∈ S, (flatCausality d Ω).le (⊤ ⊓ O) a c) →
      (flatCausality d Ω).le ⊤ c (g • a) → c = a := by
    rintro c ⟨O, hO, hle⟩ hc
    have hle' := (flatCausality d Ω).le_mono inf_le_right hle
    have h1 := hpush ((flatCausality d Ω).le_mono le_top hle')
    have h2 := hpush hc
    rw [hga] at h2
    exact hO ((flatCausality d Ω).le_mem_right hle') ((flatCausality d Ω).le_mem_left hle')
      (hM h2 h1)
  have key : ∀ {c : Ω},
      Relation.TransGen (fun x y => ∃ O ∈ S, (flatCausality d Ω).le (⊤ ⊓ O) x y) a c →
      (flatCausality d Ω).le ⊤ c (g • a) → c = a := by
    intro c hac
    induction hac with
    | single hab => exact step hab
    | tail _ hbc ih =>
      intro hc
      obtain ⟨O, hO, hle⟩ := hbc
      have hb : (flatCausality d Ω).le ⊤ _ (g • a) := (flatCausality d Ω).le_trans
        ((flatCausality d Ω).le_mono le_top hle) hc
      have := ih hb
      subst this
      exact step ⟨O, hO, hle⟩ hc
  exact key hch ((flatCausality d Ω).le_refl (show g • a ∈ (⊤ : Opens Ω) from trivial))

omit [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] in
/-- **The action of a presentation's group is free**: if `π : Ω → M` is a covering map whose
fibres are the `Γ`-orbits, `γ • P = γ' • P` forces `γ = γ'`. `δ = γ⁻¹ γ'` fixes `P`, hence (`π`
injective on a neighbourhood `V` of `P`, `π (δ z) = π z`) every point of the open
`V ∩ δ⁻¹ V ∋ P`; an affine map fixing a nonempty open set of `𝐌ⁿ` is the identity. -/
theorem smul_left_injective_of_isCoveringMap (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) {γ γ' : Γ} {P : Ω}
    (h : γ • P = γ' • P) : γ = γ' := by
  set δ : Γ := γ⁻¹ * γ' with hδ
  have hP : δ • P = P := by rw [hδ, mul_smul, ← h, inv_smul_smul]
  obtain ⟨V, hPV, hV⟩ := exists_injOn_of_isCoveringMap hcov P
  set N : Set Ω := (V : Set Ω) ∩ (fun z => δ • z) ⁻¹' V
  have hN : IsOpen N := V.2.inter (V.2.preimage (continuous_const_smul δ))
  have hfix : ∀ z ∈ N, δ • z = z := fun z hz =>
    hV hz.2 hz.1 ((hfib z (δ • z)).2 ⟨δ, δ.2, rfl⟩).symm
  have hU : IsOpen ((↑) '' N : Set (Minkowski d)) := Ω.isOpen.isOpenMap_subtype_val N hN
  have hne : ((↑) '' N : Set (Minkowski d)).Nonempty :=
    ⟨P, P, ⟨hPV, show δ • P ∈ V by rw [hP]; exact hPV⟩, rfl⟩
  have h1 : (δ : isom d) = 1 := by
    apply Subtype.ext
    refine AffineEquiv.ext_on (hU.affineSpan_eq_top hne) _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    have := congrArg Subtype.val (hfix z hz)
    rw [coe_smul, isom_smul_def] at this
    simpa using this
  have : δ = 1 := Subtype.ext h1
  rwa [hδ, inv_mul_eq_one] at this

end Lift

section CoverGH

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
  {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} [Invariant Γ Ω] {π : Ω → M}

omit [T2Space M] [Invariant Γ Ω] in
/-- A local isometry `π : Ω → M` maps the causal relation of `Ω` into that of `M`. -/
theorem le_top_map_of_isLocalIsometry (hloc : IsLocalIsometry d π) {b c : Ω}
    (h : (flatCausality d Ω).le ⊤ b c) :
    (flatCausality d M).le ⊤ (π b) (π c) :=
  hloc.strongMorphism.le_of_mapsTo (U := ⊤) (V := ⊤) (fun _ _ => trivial) h

omit [T2Space M] [Invariant Γ Ω] in
/-- **Every point of a quotient `M = π(Ω)` lies in an open set squeezed between two points**:
`b' ≤_M y ≤_M b` for every `y` in it. Lift `q` to `x ∈ Ω`, take a ball `B(x, r) ⊆ Ω`, put
`b = π(x + (r/2) e₀)`, `b' = π(x − (r/2) e₀)` and use the image of `B(x, r/4)`: its points are
joined to `x ± (r/2) e₀` by causal segments inside `B(x, r)` (the substitute, here, for the tarentin
property, which the library does not prove for flat spacetimes). -/
theorem exists_isOpen_le_and_ge (hloc : IsLocalIsometry d π) (hsurj : Surjective π) (q : M) :
    ∃ b b' : M, ∃ O : Set M, IsOpen O ∧ q ∈ O ∧
      ∀ y ∈ O, (flatCausality d M).le ⊤ y b ∧ (flatCausality d M).le ⊤ b' y := by
  obtain ⟨x, rfl⟩ := hsurj q
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen (x : Minkowski d) x.2
  set e₀ : Minkowski d := ((r / 2 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) with he₀def
  have he₀ : ‖e₀‖ = r / 2 := by
    rw [he₀def, Prod.norm_def]
    simp [abs_of_pos hr, (half_pos hr).le]
  have hbm : (x : Minkowski d) + e₀ ∈ Metric.ball (x : Minkowski d) r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, he₀]; linarith
  have hbm' : (x : Minkowski d) - e₀ ∈ Metric.ball (x : Minkowski d) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, he₀]; linarith
  let B : Ω := ⟨x + e₀, hball hbm⟩
  let B' : Ω := ⟨x - e₀, hball hbm'⟩
  let V : Set Ω := (↑) ⁻¹' Metric.ball (x : Minkowski d) (r / 4)
  have hV : IsOpen V := Metric.isOpen_ball.preimage continuous_subtype_val
  refine ⟨π B, π B', π '' V, hloc.isOpenMap _ hV,
    ⟨x, Metric.mem_ball_self (by linarith), rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hy' : dist (y : Minkowski d) x < r / 4 := hy
  rw [dist_eq_norm, Prod.norm_def, max_lt_iff, Real.norm_eq_abs, abs_lt] at hy'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy'
  have h3' : ‖(x : Minkowski d).2 - (y : Minkowski d).2‖ < r / 4 := by
    rw [norm_sub_rev]; simpa using h3
  have hfst : ((y : Minkowski d) - x).1 = (y : Minkowski d).1 - (x : Minkowski d).1 := rfl
  rw [hfst] at h1 h2
  have hyb : (y : Minkowski d) ∈ Metric.ball (x : Minkowski d) r :=
    Metric.ball_subset_ball (by linarith) hy
  refine ⟨le_top_map_of_isLocalIsometry hloc ?_, le_top_map_of_isLocalIsometry hloc ?_⟩
  · rw [flat_le_top_subtype_iff]
    refine le_of_le_top_of_segment_subset ?_ fun z hz =>
      hball ((convex_ball _ _).segment_subset hyb hbm hz)
    rw [minkowski_le_top_iff]
    show ‖((x : Minkowski d) + e₀).2 - (y : Minkowski d).2‖ ≤
      ((x : Minkowski d) + e₀).1 - (y : Minkowski d).1
    simp only [he₀def, Prod.fst_add, Prod.snd_add, add_zero]
    linarith
  · rw [flat_le_top_subtype_iff]
    refine le_of_le_top_of_segment_subset ?_ fun z hz =>
      hball ((convex_ball _ _).segment_subset hbm' hyb hz)
    rw [minkowski_le_top_iff]
    show ‖(y : Minkowski d).2 - ((x : Minkowski d) - e₀).2‖ ≤
      (y : Minkowski d).1 - ((x : Minkowski d) - e₀).1
    simp only [he₀def, Prod.fst_sub, Prod.snd_sub, sub_zero]
    rw [norm_sub_rev]
    linarith

omit [Invariant Γ Ω] in
/-- **On a quotient `M = π(Ω)` with compact diamonds, `J^±(p)` is closed**
(`prop:GH_Jferme`'s first step, with `exists_isOpen_le_and_ge` in place of the tarentin property):
a limit point `q` of `J^+(p)` lies in an open set below some `b`, hence in the closure of the
compact, so closed, diamond `J(p, b)`. -/
theorem isClosed_le_of_isCompact_diamond (hloc : IsLocalIsometry d π) (hsurj : Surjective π)
    (hD : ∀ p q : M, IsCompact ((flatCausality d M).diamond ⊤ p q)) (p : M) :
    IsClosed {q | (flatCausality d M).le ⊤ p q} ∧ IsClosed {q | (flatCausality d M).le ⊤ q p} := by
  constructor
  · refine isClosed_of_closure_subset fun q hq => ?_
    obtain ⟨b, _b', O, hO, hqO, hOb⟩ := exists_isOpen_le_and_ge hloc hsurj q
    have hc : q ∈ closure ((flatCausality d M).diamond ⊤ p b) := by
      rw [mem_closure_iff_nhds] at hq ⊢
      intro N hN
      obtain ⟨y, ⟨hyN, hyO⟩, hpy⟩ := hq (N ∩ O) (inter_mem hN (hO.mem_nhds hqO))
      exact ⟨y, hyN, Causality.mem_diamond.2 ⟨hpy, (hOb y hyO).1⟩⟩
    rw [(hD p b).isClosed.closure_eq] at hc
    exact (Causality.mem_diamond.1 hc).1
  · refine isClosed_of_closure_subset fun q hq => ?_
    obtain ⟨_b', b, O, hO, hqO, hOb⟩ := exists_isOpen_le_and_ge hloc hsurj q
    have hc : q ∈ closure ((flatCausality d M).diamond ⊤ b p) := by
      rw [mem_closure_iff_nhds] at hq ⊢
      intro N hN
      obtain ⟨y, ⟨hyN, hyO⟩, hpy⟩ := hq (N ∩ O) (inter_mem hN (hO.mem_nhds hqO))
      exact ⟨y, hyN, Causality.mem_diamond.2 ⟨(hOb y hyO).2, hpy⟩⟩
    rw [(hD b p).isClosed.closure_eq] at hc
    exact (Causality.mem_diamond.1 hc).2

/-- **A causally monotone path of `Ω` imprisoned in a compact set of `M = Γ\Ω` converges in
`Ω`.** `σ` continuous on `I ∈ l`, `π ∘ σ` in the compact `K` and eventually increasing along `l`
(a filter with a basis of preconnected sets, e.g. `𝓝[<] T` or `atTop`). `π ∘ σ` converges in
`M`: its cluster points `m` in `K` all satisfy `π σ t ≤ m` (`J^+(π σ t)` closed,
`isClosed_le_of_isCompact_diamond`), so two of them are related both ways and coincide (`M`
causal). A tail of `π ∘ σ` then lies in a chart `e` of `π` at a lift `y₀` of the limit; the
chart lift `e⁻¹ ∘ π ∘ σ`, moved by the deck transformation that matches it to `σ` at one time, is
a second lift of `π ∘ σ` on a preconnected set of times, so it equals `σ` (uniqueness of lifts,
`IsSeparatedMap.eqOn_of_comp_eqOn`), and it converges to `g • y₀`. -/
theorem exists_tendsto_of_monotone (hcov : IsCoveringMap π) (hloc : IsLocalIsometry d π)
    (hsurj : Surjective π) (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q)
    (hM : (flatCausality d M).IsCausal)
    (hD : ∀ p q : M, IsCompact ((flatCausality d M).diamond ⊤ p q))
    {l : Filter ℝ} [l.NeBot] (hl : ∀ V ∈ l, ∃ J ∈ l, J ⊆ V ∧ IsPreconnected J)
    {I : Set ℝ} (hI : I ∈ l) {σ : ℝ → Ω} (hσ : ContinuousOn σ I) {K : Set M}
    (hK : IsCompact K) (hσK : ∀ t ∈ I, π (σ t) ∈ K)
    (hmono : ∀ t ∈ I, ∀ᶠ s in l, (flatCausality d M).le ⊤ (π (σ t)) (π (σ s))) :
    ∃ y : Ω, Tendsto σ l (𝓝 y) := by
  set f : ℝ → M := fun t => π (σ t) with hfdef
  have hfK : ∀ᶠ t in l, f t ∈ K := Filter.mem_of_superset hI hσK
  have hclus : ∀ m, MapClusterPt m l f → ∀ {S : Set M}, IsClosed S → (∀ᶠ t in l, f t ∈ S) →
      m ∈ S := by
    intro m hm S hS hev
    by_contra hmS
    have := (mapClusterPt_iff_frequently.1 hm) _ (hS.isOpen_compl.mem_nhds hmS)
    obtain ⟨t, h1, h2⟩ := (this.and_eventually hev).exists
    exact h1 h2
  have hbelow : ∀ m, MapClusterPt m l f → ∀ t ∈ I, (flatCausality d M).le ⊤ (f t) m :=
    fun m hm t ht => hclus m hm (isClosed_le_of_isCompact_diamond hloc hsurj hD (f t)).1
      (hmono t ht)
  obtain ⟨m, hmK, hm⟩ := hK.exists_mapClusterPt (f := l) (u := f)
    (by rw [le_principal_iff]; exact hfK)
  have huniq : ∀ m' ∈ K, MapClusterPt m' l f → m' = m := by
    intro m' _ hm'
    exact hM (hclus m' hm' (isClosed_le_of_isCompact_diamond hloc hsurj hD m).2
        (mem_of_superset hI fun t ht => hbelow m hm t ht))
      (hclus m hm (isClosed_le_of_isCompact_diamond hloc hsurj hD m').2
        (mem_of_superset hI fun t ht => hbelow m' hm' t ht))
  have hf : Tendsto f l (𝓝 m) := hK.tendsto_nhds_of_unique_mapClusterPt hfK huniq
  obtain ⟨y₀, rfl⟩ := hsurj m
  obtain ⟨e, hy₀e, he⟩ := hcov.isLocalHomeomorph y₀
  have hmt : π y₀ ∈ e.target := by rw [he]; exact e.map_source hy₀e
  obtain ⟨J, hJl, hJV, hJc⟩ := hl _ (inter_mem hI (hf (e.open_target.mem_nhds hmt)))
  obtain ⟨t₀, ht₀⟩ := Filter.nonempty_of_mem hJl
  have hJI : J ⊆ I := fun t ht => (hJV ht).1
  have hJt : ∀ t ∈ J, f t ∈ e.target := fun t ht => (hJV ht).2
  set lift : ℝ → Ω := fun t => e.symm (f t) with hliftdef
  have hfc : ContinuousOn f J := hcov.continuous.comp_continuousOn (hσ.mono hJI)
  have hlc : ContinuousOn lift J := e.continuousOn_symm.comp hfc (fun t ht => hJt t ht)
  have hlq : ∀ t ∈ J, π (lift t) = f t := fun t ht => by
    show π (e.symm (f t)) = f t
    rw [he]; exact e.right_inv (hJt t ht)
  obtain ⟨γ, hγ, hγt⟩ := (hfib (lift t₀) (σ t₀)).1 (hlq t₀ ht₀)
  set g : Γ := ⟨γ, hγ⟩ with hgdef
  have hg0 : g • lift t₀ = σ t₀ := Subtype.ext (by rw [coe_smul]; exact hγt)
  have hμc : ContinuousOn (fun t => g • lift t) J :=
    (continuous_const_smul g).comp_continuousOn hlc
  have hμq : ∀ t ∈ J, π (g • lift t) = π (lift t) := fun t _ =>
    ((hfib (lift t) (g • lift t)).2 ⟨γ, hγ, by rw [coe_smul]⟩).symm
  have hEq : EqOn σ (fun t => g • lift t) J :=
    (T2Space.isSeparatedMap π).eqOn_of_comp_eqOn hcov.isLocalHomeomorph.isLocallyInjective hJc
      (hσ.mono hJI) hμc (fun t ht => by
        simp only [Function.comp_apply]; rw [hμq t ht, hlq t ht]) ht₀ hg0.symm
  have hkey : e.symm (π y₀) = y₀ := by rw [he]; exact e.left_inv hy₀e
  have h1 : Tendsto lift l (𝓝 y₀) := by
    have := (e.continuousAt_symm hmt).tendsto.comp hf
    rw [hkey] at this
    exact this
  have hlim : Tendsto (fun t => g • lift t) l (𝓝 (g • y₀)) :=
    ((continuous_const_smul g).tendsto y₀).comp h1
  exact ⟨g • y₀, hlim.congr' (mem_of_superset hJl fun t ht => (hEq ht).symm)⟩

omit [T2Space M] [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
  [Invariant Γ Ω] in
/-- A point of `Ω` in the closure (in `𝐌ⁿ`) of `π⁻¹ K`, `K` closed, lies in `π⁻¹ K`. -/
theorem mem_of_mem_closure_image (hπ : Continuous π) {K : Set M} (hK : IsClosed K) {x : Ω}
    (hx : (x : Minkowski d) ∈ closure (((↑) : Ω → Minkowski d) '' (π ⁻¹' K))) : π x ∈ K := by
  by_contra hxK
  have hU : IsOpen (((↑) : Ω → Minkowski d) '' (π ⁻¹' Kᶜ)) :=
    Ω.isOpen.isOpenMap_subtype_val _ (hK.isOpen_compl.preimage hπ)
  obtain ⟨_, ⟨y, hy, rfl⟩, ⟨y', hy', hyy'⟩⟩ := mem_closure_iff.1 hx _ hU ⟨x, hxK, rfl⟩
  have : y' = y := Subtype.ext hyy'
  subst this
  exact hy hy'

/-- **A causal segment from a point of `Ω` lying in the closure of `π⁻¹ K` (`K` compact) lies in
`Ω`**, when `M = π(Ω)` is causal with compact diamonds. Let `[p, P τ*]` be the maximal subsegment
in `Ω` (`τ*` the supremum): along it `t ↦ P t` is causally increasing in `Ω` with image in `K`
(`mem_of_mem_closure_image`), so it converges in `Ω` (`exists_tendsto_of_monotone`, along
`𝓝[<] τ*`), and its limit `P τ*` is a point of `Ω`; `Ω` being open, `τ* < 1` is impossible. -/
theorem segment_subset_of_subset_closure (hcov : IsCoveringMap π) (hloc : IsLocalIsometry d π)
    (hsurj : Surjective π) (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q)
    (hM : (flatCausality d M).IsCausal)
    (hD : ∀ p q : M, IsCompact ((flatCausality d M).diamond ⊤ p q))
    {K : Set M} (hK : IsCompact K) {p q : Minkowski d} (hp : p ∈ Ω)
    (hpq : (minkowski d).le ⊤ p q)
    (hs : segment ℝ p q ⊆ closure (((↑) : Ω → Minkowski d) '' (π ⁻¹' K))) :
    segment ℝ p q ⊆ Ω := by
  classical
  set P : ℝ → Minkowski d := fun t => p + t • (q - p) with hPdef
  have hPc : Continuous P := continuous_const.add (continuous_id.smul continuous_const)
  have hPs : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ segment ℝ p q := fun t ht => by
    rw [segment_eq_image']; exact ⟨t, ht, rfl⟩
  have hv : IsFutureCausal (q - p) := le_top_iff_minkQ.1 hpq
  have hP0 : P 0 = p := by simp [hPdef]
  set A : Set ℝ := {τ | τ ∈ Icc (0 : ℝ) 1 ∧ ∀ t ∈ Icc 0 τ, P t ∈ Ω} with hAdef
  have h0A : (0 : ℝ) ∈ A := ⟨⟨le_rfl, zero_le_one⟩, fun t ht => by
    rw [show t = 0 from le_antisymm ht.2 ht.1, hP0]; exact hp⟩
  have hAbdd : BddAbove A := ⟨1, fun τ hτ => hτ.1.2⟩
  set τs := sSup A with hτs
  have hτs0 : 0 ≤ τs := le_csSup hAbdd h0A
  have hτs1 : τs ≤ 1 := csSup_le ⟨0, h0A⟩ fun τ hτ => hτ.1.2
  have hlt : ∀ t, 0 ≤ t → t < τs → P t ∈ Ω := by
    intro t ht0 htτ
    obtain ⟨τ, hτA, htτ'⟩ := exists_lt_of_lt_csSup ⟨0, h0A⟩ htτ
    exact hτA.2 t ⟨ht0, htτ'.le⟩
  set σ : ℝ → Ω := fun t => if h : P t ∈ Ω then ⟨P t, h⟩ else ⟨p, hp⟩ with hσdef
  have hσP : ∀ t, P t ∈ Ω → ((σ t : Ω) : Minkowski d) = P t := fun t h => by
    simp [hσdef, h]
  have hσc : ∀ t, P t ∈ Ω → ContinuousAt σ t := by
    intro t ht
    rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
    refine hPc.continuousAt.congr ?_
    filter_upwards [hPc.continuousAt.preimage_mem_nhds (Ω.isOpen.mem_nhds ht)] with s hs
    exact (hσP s hs).symm
  have hσK : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ Ω → π (σ t) ∈ K := fun t ht h =>
    mem_of_mem_closure_image hcov.continuous hK.isClosed (by rw [hσP t h]; exact hs (hPs t ht))
  have hσle : ∀ t s, 0 ≤ t → t ≤ s → s < τs →
      (flatCausality d M).le ⊤ (π (σ t)) (π (σ s)) := by
    intro t s ht hts hs'
    apply le_top_map_of_isLocalIsometry hloc
    rw [flat_le_top_subtype_iff, hσP t (hlt t ht (hts.trans_lt hs')),
      hσP s (hlt s (ht.trans hts) hs')]
    have e1 : P s - P t = (s - t) • (q - p) := by simp only [hPdef, sub_smul]; abel
    refine le_of_le_top_of_segment_subset ?_ ?_
    · rw [le_top_iff_minkQ, e1]; exact isFutureCausal_smul (sub_nonneg.2 hts) hv
    · rw [segment_eq_image']
      rintro _ ⟨θ, hθ, rfl⟩
      have e2 : P t + θ • (P s - P t) = P (t + θ * (s - t)) := by
        rw [e1, smul_smul]; simp only [hPdef, add_smul]; abel
      show P t + θ • (P s - P t) ∈ Ω
      rw [e2]
      have h1 : 0 ≤ θ * (s - t) := mul_nonneg hθ.1 (sub_nonneg.2 hts)
      have h2 : θ * (s - t) ≤ s - t := by nlinarith [hθ.2]
      exact hlt _ (by linarith) (by linarith)
  -- the end of the maximal subsegment lies in `Ω`
  have hτΩ : P τs ∈ Ω := by
    rcases hτs0.eq_or_lt with h | hpos
    · rw [← h, hP0]; exact hp
    · have hI : Ico 0 τs ∈ 𝓝[<] τs :=
        mem_of_superset (Ioo_mem_nhdsLT hpos) Ioo_subset_Ico_self
      obtain ⟨y, hy⟩ := exists_tendsto_of_monotone hcov hloc hsurj hfib hM hD (l := 𝓝[<] τs)
        (fun V hV => by
          obtain ⟨l', hl', hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hV
          exact ⟨Ioo l' τs, Ioo_mem_nhdsLT hl', hsub, isPreconnected_Ioo⟩)
        hI (fun t ht => (hσc t (hlt t ht.1 ht.2)).continuousWithinAt) hK
        (fun t ht => hσK t ⟨ht.1, ht.2.le.trans hτs1⟩ (hlt t ht.1 ht.2))
        (fun t ht => by
          filter_upwards [Ioo_mem_nhdsLT ht.2] with s hs
          exact hσle t s ht.1 hs.1.le hs.2)
      have h1 : Tendsto (fun t => ((σ t : Ω) : Minkowski d)) (𝓝[<] τs) (𝓝 (y : Minkowski d)) :=
        (continuous_subtype_val.tendsto y).comp hy
      have h2 : Tendsto (fun t => ((σ t : Ω) : Minkowski d)) (𝓝[<] τs) (𝓝 (P τs)) := by
        refine (hPc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hpos] with t ht
        exact (hσP t (hlt t ht.1.le ht.2)).symm
      rw [tendsto_nhds_unique h2 h1]; exact y.2
  have hτA : τs ∈ A := ⟨⟨hτs0, hτs1⟩, fun t ht => by
    rcases ht.2.lt_or_eq with h | h
    · exact hlt t ht.1 h
    · rw [h]; exact hτΩ⟩
  have hτ1 : τs = 1 := by
    by_contra hne
    have hlt1 : τs < 1 := lt_of_le_of_ne hτs1 hne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (Ω.isOpen.preimage hPc) τs hτΩ
    have hmem : min 1 (τs + ε / 2) ∈ A := by
      refine ⟨⟨le_min zero_le_one (by linarith), min_le_left _ _⟩, fun t ht => ?_⟩
      rcases le_or_gt t τs with h | h
      · exact hτA.2 t ⟨ht.1, h⟩
      · refine hball ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
        linarith [ht.2.trans (min_le_right _ _)]
    have := le_csSup hAbdd hmem
    have : τs < min 1 (τs + ε / 2) := lt_min hlt1 (by linarith)
    linarith
  rw [segment_eq_image']
  rintro _ ⟨t, ht, rfl⟩
  exact hτA.2 t (by rw [hτ1]; exact ht)

/-- **No future causal ray of `Ω` is imprisoned in a compact set of `M = π(Ω)`** (`M` causal with
compact diamonds): along `atTop` the ray would converge in `Ω` (`exists_tendsto_of_monotone`),
while its norm tends to infinity. -/
theorem not_forall_ray (hcov : IsCoveringMap π) (hloc : IsLocalIsometry d π)
    (hsurj : Surjective π) (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q)
    (hM : (flatCausality d M).IsCausal)
    (hD : ∀ p q : M, IsCompact ((flatCausality d M).diamond ⊤ p q))
    {K : Set M} (hK : IsCompact K) {p v : Minkowski d} (hp : p ∈ Ω) (hv : IsFutureCausal v)
    (hv0 : v ≠ 0) (hray : ∀ t : ℝ, 0 ≤ t → p + t • v ∈ Ω)
    (hrayK : ∀ t (ht : 0 ≤ t), π ⟨p + t • v, hray t ht⟩ ∈ K) : False := by
  classical
  set P : ℝ → Minkowski d := fun t => p + t • v with hPdef
  have hPc : Continuous P := continuous_const.add (continuous_id.smul continuous_const)
  set σ : ℝ → Ω := fun t => if h : P t ∈ Ω then ⟨P t, h⟩ else ⟨p, hp⟩ with hσdef
  have hσP : ∀ t, P t ∈ Ω → ((σ t : Ω) : Minkowski d) = P t := fun t h => by
    simp [hσdef, h]
  have hσc : ∀ t, P t ∈ Ω → ContinuousAt σ t := by
    intro t ht
    rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
    refine hPc.continuousAt.congr ?_
    filter_upwards [hPc.continuousAt.preimage_mem_nhds (Ω.isOpen.mem_nhds ht)] with s hs
    exact (hσP s hs).symm
  have hσK : ∀ t ∈ Ici (0 : ℝ), π (σ t) ∈ K := fun t ht => by
    have : σ t = ⟨p + t • v, hray t ht⟩ := Subtype.ext (hσP t (hray t ht))
    rw [this]; exact hrayK t ht
  have hσle : ∀ t s, 0 ≤ t → t ≤ s → (flatCausality d M).le ⊤ (π (σ t)) (π (σ s)) := by
    intro t s ht hts
    apply le_top_map_of_isLocalIsometry hloc
    rw [flat_le_top_subtype_iff, hσP t (hray t ht), hσP s (hray s (ht.trans hts))]
    have e1 : P s - P t = (s - t) • v := by simp only [hPdef, sub_smul]; abel
    refine le_of_le_top_of_segment_subset ?_ ?_
    · rw [le_top_iff_minkQ, e1]; exact isFutureCausal_smul (sub_nonneg.2 hts) hv
    · rw [segment_eq_image']
      rintro _ ⟨θ, hθ, rfl⟩
      have e2 : P t + θ • (P s - P t) = P (t + θ * (s - t)) := by
        rw [e1, smul_smul]; simp only [hPdef, add_smul]; abel
      show P t + θ • (P s - P t) ∈ Ω
      rw [e2]
      exact hray _ (by nlinarith [hθ.1])
  obtain ⟨y, hy⟩ := exists_tendsto_of_monotone hcov hloc hsurj hfib hM hD (l := atTop)
    (fun V hV => by
      obtain ⟨N, hN⟩ := mem_atTop_sets.1 hV
      exact ⟨Ici N, Ici_mem_atTop N, fun t ht => hN t ht, isPreconnected_Ici⟩)
    (Ici_mem_atTop 0) (fun t ht => (hσc t (hray t ht)).continuousWithinAt) hK hσK
    (fun t ht => by
      filter_upwards [Ici_mem_atTop t] with s hs
      exact hσle t s ht hs)
  have h1 : Tendsto (fun t => ‖((σ t : Ω) : Minkowski d)‖) atTop (𝓝 ‖(y : Minkowski d)‖) :=
    ((continuous_subtype_val.tendsto y).comp hy).norm
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have h2 : Tendsto (fun t => ‖((σ t : Ω) : Minkowski d)‖) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (tendsto_atTop_add_const_right _ (-‖p‖) (tendsto_id.atTop_mul_const hvpos))
    filter_upwards [Ici_mem_atTop 0] with t ht
    rw [hσP t (hray t ht)]
    have : ‖t • v‖ ≤ ‖P t‖ + ‖p‖ := by
      have := norm_sub_le (P t) p
      simpa [hPdef] using this
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at this
    simp only [id]
    linarith
  exact not_tendsto_nhds_of_tendsto_atTop h2 _ h1

/-- **Two causal segments of `Ω` span the third side when `M = Γ\Ω` is causal with compact
diamonds**: the argument of `segment_subset_trans_of_isCompact_diamond`, the compact diamond of
`Ω` replaced by `π⁻¹ J_M(π a, π b)`, whose closure in `𝐌ⁿ` is controlled by
`segment_subset_of_subset_closure`. -/
theorem segment_subset_trans_of_isQuotientOf (hcov : IsCoveringMap π)
    (hloc : IsLocalIsometry d π) (hsurj : Surjective π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q)
    (hM : (flatCausality d M).IsCausal)
    (hD : ∀ p q : M, IsCompact ((flatCausality d M).diamond ⊤ p q))
    {a c b : Minkowski d} (hac : (minkowski d).le ⊤ a c) (hcb : (minkowski d).le ⊤ c b)
    (hsac : segment ℝ a c ⊆ Ω) (hscb : segment ℝ c b ⊆ Ω) : segment ℝ a b ⊆ Ω := by
  have haW : a ∈ Ω := hsac (left_mem_segment ℝ a c)
  have hbW : b ∈ Ω := hscb (right_mem_segment ℝ c b)
  set K : Set M := (flatCausality d M).diamond ⊤ (π ⟨a, haW⟩) (π ⟨b, hbW⟩) with hKdef
  set E : Set (Minkowski d) := ((↑) : Ω → Minkowski d) '' (π ⁻¹' K) with hEdef
  have hmemE : ∀ y (hy : y ∈ Ω), (minkowski d).le Ω a y → (minkowski d).le Ω y b → y ∈ E := by
    intro y hy h1 h2
    refine ⟨⟨y, hy⟩, Causality.mem_diamond.2 ⟨le_top_map_of_isLocalIsometry hloc ?_,
      le_top_map_of_isLocalIsometry hloc ?_⟩, rfl⟩
    · rw [flat_le_top_subtype_iff]; exact h1
    · rw [flat_le_top_subtype_iff]; exact h2
  set g : ℝ → ℝ := fun s => max 0 (min s 1) with hgdef
  have hg : Continuous g := continuous_const.max (continuous_id.min continuous_const)
  have hg01 : ∀ s, g s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  set cs : ℝ → Minkowski d := fun s => c + g s • (b - c) with hcsdef
  set F : ℝ × ℝ → Minkowski d := fun z => a + z.2 • (cs z.1 - a) with hFdef
  have hF : Continuous F :=
    continuous_const.add (continuous_snd.smul
      ((continuous_const.add ((hg.comp continuous_fst).smul continuous_const)).sub
        continuous_const))
  set u : Set ℝ := {s | ∀ θ ∈ Icc (0 : ℝ) 1, F (s, θ) ∈ Ω} with hudef
  have hcs : ∀ s, cs s ∈ segment ℝ c b := fun s => by
    rw [segment_eq_image']; exact ⟨g s, hg01 s, rfl⟩
  have hseg : ∀ s, segment ℝ a (cs s) = (fun θ => F (s, θ)) '' Icc 0 1 := fun s => by
    rw [segment_eq_image']
  have hacs : ∀ s, (minkowski d).le ⊤ a (cs s) := fun s =>
    (minkowski d).le_trans hac (le_top_of_mem_segment hcb (hcs s)).1
  have huo : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    have : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ᶠ z : ℝ × ℝ in 𝓝 (s₀, θ), F z ∈ Ω := fun θ hθ =>
      hF.continuousAt.preimage_mem_nhds (Ω.isOpen.mem_nhds (hs₀ θ hθ))
    exact isCompact_Icc.eventually_forall_of_forall_eventually this
  have hmaps : ∀ θ ∈ Icc (0 : ℝ) 1, MapsTo (fun s => F (s, θ)) u E := by
    intro θ hθ s hs
    have hsW : segment ℝ a (cs s) ⊆ Ω := by
      rw [hseg]; rintro _ ⟨θ', hθ', rfl⟩; exact hs θ' hθ'
    have hy : F (s, θ) ∈ segment ℝ a (cs s) := by rw [hseg]; exact ⟨θ, hθ, rfl⟩
    obtain ⟨h1, h2⟩ := le_top_of_mem_segment (hacs s) hy
    have hcsb := (le_top_of_mem_segment hcb (hcs s)).2
    refine hmemE _ (hsW hy) (le_of_le_top_of_segment_subset h1 fun z hz =>
      hsW ((convex_segment _ _).segment_subset (left_mem_segment _ _ _) hy hz)) ?_
    exact (minkowski d).le_trans (le_of_le_top_of_segment_subset h2 fun z hz =>
        hsW ((convex_segment _ _).segment_subset hy (right_mem_segment _ _ _) hz))
      (le_of_le_top_of_segment_subset hcsb fun z hz =>
        hscb ((convex_segment _ _).segment_subset (hcs s) (right_mem_segment _ _ _) hz))
  have hcl : closure u ∩ Icc 0 1 ⊆ u := by
    intro s hs
    have hsub : segment ℝ a (cs s) ⊆ closure E := by
      rw [hseg]; rintro _ ⟨θ, hθ, rfl⟩
      exact map_mem_closure (f := fun s => F (s, θ)) (hF.comp (Continuous.prodMk_left θ)) hs.1
        (hmaps θ hθ)
    have := segment_subset_of_subset_closure hcov hloc hsurj hfib hM hD (hD _ _) haW (hacs s) hsub
    intro θ hθ
    exact this (by rw [hseg]; exact ⟨θ, hθ, rfl⟩)
  have h0 : (Icc (0 : ℝ) 1 ∩ u).Nonempty := by
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, fun θ hθ => hsac ?_⟩
    rw [segment_eq_image']
    exact ⟨θ, hθ, by simp [hFdef, hcsdef, hgdef]⟩
  have hsub := isPreconnected_Icc.subset_of_closure_inter_subset huo h0 hcl
  rw [segment_eq_image']
  rintro _ ⟨θ, hθ, rfl⟩
  have := hsub ⟨zero_le_one, le_rfl⟩ θ hθ
  simpa [hFdef, hcsdef, hgdef] using this

end CoverGH

/-- **Global hyperbolicity lifts to the cover of a quotient** (the converse of
`FlatQuotient.globallyHyperbolic_quotient`): if the flat spacetime `M` is presented as `Γ\Ω`
(`IsQuotientOf`) and is GH, then (a) the diamonds of `Ω` are compact and (b) for all `a, b ∈ Ω`
only finitely many `g ∈ Γ` have `a ≤_Ω g b`. Classical (a covering of a GH spacetime is GH; the
lifts of the causal curves from `π a` to `π b` stay in a compact set of `Ω`). Proved by straight
segments: `≤_Ω` is convex (`segment_subset_trans_of_isQuotientOf`); (a) a limit `y` of
`J_Ω(a, b)` is joined to `a` and `b` by segments in the closure of `π⁻¹ J_M(π a, π b)`, hence in
`Ω` (`segment_subset_of_subset_closure`); (b) the points `y` with `[a, y]` in that closure form
a closed set, bounded (`not_forall_ray`, on a limit direction), hence a compact subset of `Ω`, and
the `g • b` with `a ≤_Ω g • b` are points of it in one fibre of the covering `π`, finitely many,
`g ↦ g • b` being injective (`smul_left_injective_of_isCoveringMap`). -/
theorem cover_gh_of_isQuotientOf {M : FlatSpacetime.{v} d} {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} [Invariant Γ Ω] (hq : IsQuotientOf M Γ Ω) (hM : GH M) :
    (∀ a b : Ω, IsCompact ((flatCausality d Ω).diamond ⊤ a b)) ∧
      ∀ a b : Ω, {g : Γ | (flatCausality d Ω).le ⊤ a (g • b)}.Finite := by
  obtain ⟨π, hcov, hloc, hsurj, hfib⟩ := hq.quot
  have hC := hM.1
  have hD := hM.2
  have hconv : ∀ {p q : Minkowski d}, (minkowski d).le Ω p q →
      (minkowski d).le ⊤ p q ∧ segment ℝ p q ⊆ Ω := fun h =>
    le_top_and_segment_subset_of_le_of_trans (fun hac hcb hsac hscb =>
      segment_subset_trans_of_isQuotientOf hcov hloc hsurj hfib hC hD hac hcb hsac hscb) h
  have hsegle : ∀ {u w y : Minkowski d}, (minkowski d).le ⊤ u w → segment ℝ u w ⊆ Ω →
      y ∈ segment ℝ u w → (minkowski d).le Ω u y ∧ (minkowski d).le Ω y w :=
    fun huw hs hy =>
      ⟨le_of_le_top_of_segment_subset (le_top_of_mem_segment huw hy).1 fun z hz =>
          hs ((convex_segment _ _).segment_subset (left_mem_segment _ _ _) hy hz),
        le_of_le_top_of_segment_subset (le_top_of_mem_segment huw hy).2 fun z hz =>
          hs ((convex_segment _ _).segment_subset hy (right_mem_segment _ _ _) hz)⟩
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · -- (a) compact diamonds
    set K := (flatCausality d M).diamond ⊤ (π a) (π b) with hKdef
    set E := ((↑) : Ω → Minkowski d) '' (π ⁻¹' K) with hEdef
    set J := ((↑) : Ω → Minkowski d) '' (flatCausality d Ω).diamond ⊤ a b with hJdef
    have hKm : IsCompact ((minkowski d).diamond ⊤ (a : Minkowski d) b) :=
      minkowski_globallyHyperbolic.2 _ _
    have hJsub : J ⊆ (minkowski d).diamond ⊤ (a : Minkowski d) b := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Causality.mem_diamond] at hz
      exact Causality.mem_diamond.2
        ⟨(minkowski d).le_mono le_top ((flat_le_top_subtype_iff Ω a z).1 hz.1),
          (minkowski d).le_mono le_top ((flat_le_top_subtype_iff Ω z b).1 hz.2)⟩
    have hJseg : ∀ z ∈ J, segment ℝ (a : Minkowski d) z ⊆ E ∧ segment ℝ z b ⊆ E := by
      rintro _ ⟨z, hz, rfl⟩
      rw [Causality.mem_diamond] at hz
      obtain ⟨h1t, h1s⟩ := hconv ((flat_le_top_subtype_iff Ω a z).1 hz.1)
      obtain ⟨h2t, h2s⟩ := hconv ((flat_le_top_subtype_iff Ω z b).1 hz.2)
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · obtain ⟨hay, hyz⟩ := hsegle h1t h1s hy
        refine ⟨⟨y, h1s hy⟩, Causality.mem_diamond.2 ⟨le_top_map_of_isLocalIsometry hloc ?_,
          le_top_map_of_isLocalIsometry hloc ?_⟩, rfl⟩
        · rw [flat_le_top_subtype_iff]; exact hay
        · exact (flatCausality d Ω).le_trans ((flat_le_top_subtype_iff _ _ _).2 hyz) hz.2
      · obtain ⟨hzy, hyb⟩ := hsegle h2t h2s hy
        refine ⟨⟨y, h2s hy⟩, Causality.mem_diamond.2 ⟨le_top_map_of_isLocalIsometry hloc ?_,
          le_top_map_of_isLocalIsometry hloc ?_⟩, rfl⟩
        · exact (flatCausality d Ω).le_trans hz.1 ((flat_le_top_subtype_iff _ _ _).2 hzy)
        · rw [flat_le_top_subtype_iff]; exact hyb
    have hJc : IsClosed J := by
      refine isClosed_of_closure_subset fun y hy => ?_
      have hyK := closure_minimal hJsub hKm.isClosed hy
      rw [Causality.mem_diamond] at hyK
      have hs1 : segment ℝ (a : Minkowski d) y ⊆ closure E := by
        rw [segment_eq_image']
        rintro _ ⟨θ, hθ, rfl⟩
        exact map_mem_closure (f := fun z => (a : Minkowski d) + θ • (z - a)) (by fun_prop) hy
          (fun z hz => (hJseg z hz).1 (by rw [segment_eq_image']; exact ⟨θ, hθ, rfl⟩))
      have hsa := segment_subset_of_subset_closure hcov hloc hsurj hfib hC hD (hD _ _) a.2
        hyK.1 hs1
      have hyΩ : y ∈ Ω := hsa (right_mem_segment _ _ _)
      have hs2 : segment ℝ y (b : Minkowski d) ⊆ closure E := by
        rw [segment_eq_image']
        rintro _ ⟨θ, hθ, rfl⟩
        exact map_mem_closure (f := fun z => z + θ • ((b : Minkowski d) - z)) (by fun_prop) hy
          (fun z hz => (hJseg z hz).2 (by rw [segment_eq_image']; exact ⟨θ, hθ, rfl⟩))
      have hsb := segment_subset_of_subset_closure hcov hloc hsurj hfib hC hD (hD _ _) hyΩ
        hyK.2 hs2
      refine ⟨⟨y, hyΩ⟩, Causality.mem_diamond.2 ⟨?_, ?_⟩, rfl⟩
      · rw [flat_le_top_subtype_iff]; exact le_of_le_top_of_segment_subset hyK.1 hsa
      · rw [flat_le_top_subtype_iff]; exact le_of_le_top_of_segment_subset hyK.2 hsb
    rw [Subtype.isCompact_iff]
    exact hKm.of_isClosed_subset hJc hJsub
  · -- (b) finiteness
    set K := (flatCausality d M).diamond ⊤ (π a) (π b) with hKdef
    set E := ((↑) : Ω → Minkowski d) '' (π ⁻¹' K) with hEdef
    set S : Set (Minkowski d) := {y | (minkowski d).le ⊤ (a : Minkowski d) y ∧
      segment ℝ (a : Minkowski d) y ⊆ closure E} with hSdef
    have hSΩ : ∀ y ∈ S, segment ℝ (a : Minkowski d) y ⊆ Ω := fun y hy =>
      segment_subset_of_subset_closure hcov hloc hsurj hfib hC hD (hD _ _) a.2 hy.1 hy.2
    have hSc : IsClosed S := by
      have hS : S = {y | IsFutureCausal (y - (a : Minkowski d))} ∩
          ⋂ θ ∈ Icc (0 : ℝ) 1, (fun y => (a : Minkowski d) + θ • (y - a)) ⁻¹' closure E := by
        ext y
        simp only [hSdef, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage,
          le_top_iff_minkQ, segment_eq_image', image_subset_iff]
        rfl
      rw [hS]
      exact (isClosed_isFutureCausal.preimage (continuous_id.sub continuous_const)).inter
        (isClosed_biInter fun θ _ => isClosed_closure.preimage (by fun_prop))
    have hbdd : ∃ R, ∀ y ∈ S, ‖y - (a : Minkowski d)‖ ≤ R := by
      by_contra hcon
      push Not at hcon
      choose y hyS hyR using fun n : ℕ => hcon n
      have hpos : ∀ n, 0 < ‖y n - (a : Minkowski d)‖ := fun n =>
        lt_of_le_of_lt (Nat.cast_nonneg n) (hyR n)
      set w : ℕ → Minkowski d := fun n => ‖y n - (a : Minkowski d)‖⁻¹ • (y n - a) with hwdef
      have hw : ∀ n, w n ∈ Metric.sphere (0 : Minkowski d) 1 := fun n => by
        rw [mem_sphere_zero_iff_norm, hwdef, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (hpos n).ne']
      obtain ⟨v, hv1, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Minkowski d) 1).tendsto_subseq hw
      have hv0 : v ≠ 0 := by
        rintro rfl; rw [mem_sphere_zero_iff_norm, norm_zero] at hv1; exact zero_ne_one hv1
      have hvc : IsFutureCausal v := isClosed_isFutureCausal.mem_of_tendsto hlim
        (Eventually.of_forall fun n => isFutureCausal_smul (inv_nonneg.2 (norm_nonneg _))
          (le_top_iff_minkQ.1 (hyS (φ n)).1))
      have hray : ∀ t : ℝ, 0 ≤ t → (a : Minkowski d) + t • v ∈ closure E := by
        intro t ht
        have hlim' : Tendsto (fun n => (a : Minkowski d) + t • w (φ n)) atTop
            (𝓝 ((a : Minkowski d) + t • v)) :=
          tendsto_const_nhds.add (hlim.const_smul t)
        refine isClosed_closure.mem_of_tendsto hlim' ?_
        obtain ⟨N, hN⟩ := exists_nat_gt t
        filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop N] with n hn
        have hyn := hyR (φ n)
        have hle : t ≤ ‖y (φ n) - (a : Minkowski d)‖ := by
          have : (N : ℝ) ≤ φ n := by exact_mod_cast hn
          linarith
        refine (hyS (φ n)).2 ?_
        rw [segment_eq_image']
        refine ⟨t * ‖y (φ n) - (a : Minkowski d)‖⁻¹, ⟨by positivity, ?_⟩, ?_⟩
        · rw [← div_eq_mul_inv]; exact div_le_one_of_le₀ hle (norm_nonneg _)
        · simp only [hwdef, smul_smul]
      have hrayΩ : ∀ t : ℝ, 0 ≤ t → (a : Minkowski d) + t • v ∈ Ω := fun t ht => by
        have hs : segment ℝ (a : Minkowski d) (a + t • v) ⊆ closure E := by
          rw [segment_eq_image']
          rintro _ ⟨θ, hθ, rfl⟩
          have : (a : Minkowski d) + θ • ((a + t • v) - a) = a + (θ * t) • v := by
            rw [add_sub_cancel_left, smul_smul]
          show (a : Minkowski d) + θ • ((a + t • v) - a) ∈ closure E
          rw [this]; exact hray _ (mul_nonneg hθ.1 ht)
        have hle : (minkowski d).le ⊤ (a : Minkowski d) (a + t • v) := by
          rw [le_top_iff_minkQ, add_sub_cancel_left]; exact isFutureCausal_smul ht hvc
        exact segment_subset_of_subset_closure hcov hloc hsurj hfib hC hD (hD _ _) a.2 hle hs
          (right_mem_segment _ _ _)
      exact not_forall_ray hcov hloc hsurj hfib hC hD (hD (π a) (π b)) a.2 hvc hv0 hrayΩ
        (fun t ht => mem_of_mem_closure_image hcov.continuous (hD _ _).isClosed (hray t ht))
    obtain ⟨R, hR⟩ := hbdd
    set S' := S ∩ Metric.closedBall (a : Minkowski d) R with hS'def
    have hS'c : IsCompact S' := (isCompact_closedBall _ _).inter_left hSc
    have hS'Ω : S' ⊆ Ω := fun y hy => hSΩ y hy.1 (right_mem_segment _ _ _)
    set K' : Set Ω := (↑) ⁻¹' S' with hK'def
    have hK'c : IsCompact K' := by
      rw [Subtype.isCompact_iff]
      have : ((↑) : Ω → Minkowski d) '' K' = S' := by
        ext y
        exact ⟨by rintro ⟨z, hz, rfl⟩; exact hz, fun hy => ⟨⟨y, hS'Ω hy⟩, hy, rfl⟩⟩
      rw [this]; exact hS'c
    choose U hxU hU using exists_injOn_of_isCoveringMap hcov
    obtain ⟨T, -, hcovT⟩ := hK'c.elim_nhds_subcover (fun x => (U x : Set Ω))
      (fun x _ => (U x).2.mem_nhds (hxU x))
    have hfin : (K' ∩ {x | π x = π b}).Finite := by
      refine Set.Finite.subset (Set.Finite.biUnion T.finite_toSet fun x _ =>
        (?_ : ((U x : Set Ω) ∩ {x | π x = π b}).Finite)) ?_
      · exact Set.Subsingleton.finite fun y hy z hz => hU x hy.1 hz.1 (hy.2.trans hz.2.symm)
      · rintro y ⟨hyK, hyb⟩
        obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 (hcovT hyK)
        exact mem_iUnion₂.2 ⟨x, hxT, hyx, hyb⟩
    have hinj : InjOn (fun g : Γ => g • b) {g : Γ | (flatCausality d Ω).le ⊤ a (g • b)} :=
      fun g _ g' _ h => smul_left_injective_of_isCoveringMap hcov hfib h
    refine Set.Finite.of_finite_image (hfin.subset ?_) hinj
    rintro _ ⟨g, hg, rfl⟩
    have hπ : π (g • b) = π b := ((hfib b (g • b)).2 ⟨g, g.2, by rw [coe_smul]⟩).symm
    obtain ⟨ht, hs⟩ := hconv ((flat_le_top_subtype_iff Ω a (g • b)).1 hg)
    have hgS : ((g • b : Ω) : Minkowski d) ∈ S := by
      refine ⟨ht, fun y hy => subset_closure ?_⟩
      obtain ⟨hay, hyg⟩ := hsegle ht hs hy
      refine ⟨⟨y, hs hy⟩, Causality.mem_diamond.2
        ⟨le_top_map_of_isLocalIsometry hloc ((flat_le_top_subtype_iff _ _ _).2 hay), ?_⟩, rfl⟩
      rw [← hπ]
      exact le_top_map_of_isLocalIsometry hloc ((flat_le_top_subtype_iff _ _ _).2 hyg)
    exact ⟨⟨hgS, Metric.mem_closedBall.2 (by rw [dist_eq_norm]; exact hR _ hgS)⟩, hπ⟩

end TwistedProduct

/-- **Rem 5.3, causal half, causality** (l.1800–1805): a linear twisted product over a causal flat
spacetime is causal. Through the lifts of `B = Γ\Ω` and `M₁ = Γ_U\(ι⁻¹ Ω)`: a loop
`b ≤ b' ≤ b` lifts to `x ≤ y ≤ γ x` in `Ω`; the retraction maps `x ≤ γ x` to `q x ≤ g (q x)` in
`ι⁻¹ Ω` (`retract_le_of_le`), which forces `g (q x) = q x` (`smul_eq_of_le_of_isCausal`, by the
causality of `M₁`); then `γ x − x ∈ U^⊥` is future causal, hence `0`
(`eq_of_le_top_of_retract_eq`), and `x ≤ y ≤ x` in `Ω ⊆ 𝐌ⁿ`. -/
theorem isCausal_of_isLTPData {B : Type u} [TopologicalSpace B] [ChartedSpace (Minkowski d) B]
    [HasGroupoid B (gxGroupoid (isom d) (Minkowski d))] {M₁ : Type v} [TopologicalSpace M₁]
    [ChartedSpace (Minkowski d₁) M₁] [HasGroupoid M₁ (gxGroupoid (isom d₁) (Minkowski d₁))]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} {ι : AffineMinkEmbedding d₁ d}
    (h : IsLTPData B M₁ Γ Ω ι) (hM : (flatCausality d₁ M₁).IsCausal) :
    (flatCausality d B).IsCausal := by
  haveI := h.quotient.invariant
  haveI : Invariant (ι.restrictGroup Γ) (ι.preimageOpens Ω) := h.quotient_base.invariant
  obtain ⟨π, hcov, hloc, hsurj, hfib⟩ := h.quotient.quot
  obtain ⟨π₁, hcov₁, hloc₁, -, hfib₁⟩ := h.quotient_base.quot
  intro b b' hbb' hb'b
  obtain ⟨x, rfl⟩ := hsurj b
  obtain ⟨y, rfl, hxy⟩ := TwistedProduct.exists_lift_le hcov hloc hsurj hfib hbb'
  obtain ⟨x', hx', hyx'⟩ := TwistedProduct.exists_lift_le hcov hloc hsurj hfib hb'b
  obtain ⟨γ, hγ, hγx⟩ := (hfib x x').1 hx'.symm
  have hm : (minkowski d).le Ω x x' :=
    (flat_le_top_subtype_iff Ω x x').1 ((flatCausality d Ω).le_trans hxy hyx')
  obtain ⟨g, hg⟩ := h.restricts γ hγ
  have hr := ι.retract_le_of_le h.orthochronous h.perp_invariant hm
  have hrx' : ι.retract x' = g • ι.retract x := by rw [← hγx, hg.retract_smul]
  let a : ι.preimageOpens Ω := ⟨ι.retract x, (ι.mem_iff_retract_mem h.perp_invariant).1 x.2⟩
  let g' : ι.restrictGroup Γ := ⟨g, γ, hγ, hg⟩
  have ha : (flatCausality d₁ (ι.preimageOpens Ω)).le ⊤ a (g' • a) := by
    rw [flat_le_top_subtype_iff]
    show (minkowski d₁).le _ (ι.retract x) (g • ι.retract x)
    rw [← hrx']
    exact hr
  have hga := TwistedProduct.smul_eq_of_le_of_isCausal hcov₁ hloc₁ hfib₁ hM ha
  have hrr : ι.retract x = ι.retract x' := by
    rw [hrx']
    exact (congrArg Subtype.val hga).symm
  have hxx : x = x' :=
    Subtype.ext (ι.eq_of_le_top_of_retract_eq ((minkowski d).le_mono le_top hm) hrr)
  subst hxx
  exact congrArg π (FlatQuotient.isCausal_subtype Ω hxy hyx')

/-- **Rem 5.3, causal half, at the level of the cover `Ω`** (l.1800–1805): for a linear twisted
product `B = Γ\Ω` over a GH flat spacetime `M₁ = Γ_U\(ι⁻¹ Ω)`, (a) the diamonds of `Ω` are
compact and (b) for all `x, y ∈ Ω` only finitely many `γ ∈ Γ` have `x ≤_Ω γ y`. These are the
two hypotheses under which global hyperbolicity descends to a quotient (as in
`FlatQuotient.globallyHyperbolic_quotient`); the descent itself is proved in
`isCompact_diamond_of_isLTPData`. The instance `[Invariant Γ Ω]` (to let `Γ` act on `Ω`) is not
an added hypothesis: it follows from `h.quotient` (`IsQuotientOf.invariant`). Proved from: GH
lifts to the cover `W = ι⁻¹ Ω` of `M₁`
(`TwistedProduct.cover_gh_of_isQuotientOf`), and the diamonds of `Ω = W × U^⊥` are closed
(`AffineMinkEmbedding.isClosed_diamond_of_retract`); (a) is `isCompact_diamond_of_retract`;
(b) maps `γ` to its restriction `g`, injectively
(`TwistedProduct.smul_left_injective_of_isCoveringMap`), into the finite set of `W`. -/
theorem cover_gh_of_isLTPData {B : FlatSpacetime.{u} d} {M₁ : FlatSpacetime.{v} d₁}
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} {ι : AffineMinkEmbedding d₁ d}
    [Invariant Γ Ω] (h : IsLTPData B M₁ Γ Ω ι) (hM : GH M₁) :
    (∀ x z : Ω, IsCompact ((flatCausality d Ω).diamond ⊤ x z)) ∧
      ∀ x y : Ω, {γ : Γ | (flatCausality d Ω).le ⊤ x (γ • y)}.Finite := by
  haveI : Invariant (ι.restrictGroup Γ) (ι.preimageOpens Ω) := h.quotient_base.invariant
  obtain ⟨hW, hWfin⟩ := TwistedProduct.cover_gh_of_isQuotientOf h.quotient_base hM
  refine ⟨ι.isCompact_diamond_of_retract h.orthochronous h.perp_invariant hW, fun x y => ?_⟩
  -- (b): `γ ↦ g` (`γ` restricts to `g`) maps the set into the finite one of `W = ι⁻¹ Ω`
  -- (`retract_le_of_le`, `retract_smul`), injectively (freeness at the point `ι (q x)` of `Ω`)
  obtain ⟨π, hcov, -, -, hfib⟩ := h.quotient.quot
  have hr : ∀ γ : Γ, ∃ g : isom d₁, ι.Restricts γ g := fun γ => h.restricts γ γ.2
  let r : Γ → ι.restrictGroup Γ := fun γ =>
    ⟨Classical.choose (hr γ), γ, γ.2, Classical.choose_spec (hr γ)⟩
  have hmem : ∀ p : Ω, ι.retract p ∈ ι.preimageOpens Ω := fun p =>
    (ι.mem_iff_retract_mem h.perp_invariant).1 p.2
  let a : ι.preimageOpens Ω := ⟨ι.retract x, hmem x⟩
  let b : ι.preimageOpens Ω := ⟨ι.retract y, hmem y⟩
  refine Set.Finite.of_injOn (f := r) ?_ ?_ (hWfin a b)
  · intro γ hγ
    have hm : (minkowski d).le Ω x (γ • y) :=
      (flat_le_top_subtype_iff Ω x (γ • y)).1 hγ
    have hq := ι.retract_le_of_le h.orthochronous h.perp_invariant hm
    show (flatCausality d₁ (ι.preimageOpens Ω)).le ⊤ a (r γ • b)
    rw [flat_le_top_subtype_iff]
    show (minkowski d₁).le _ (ι.retract x) (Classical.choose (hr γ) • ι.retract y)
    rw [← (Classical.choose_spec (hr γ)).retract_smul]
    exact hq
  · intro γ _ γ' _ hγγ'
    have hg : Classical.choose (hr γ) = Classical.choose (hr γ') := congrArg Subtype.val hγγ'
    let P : Ω := ⟨ι (ι.retract x), hmem x⟩
    refine TwistedProduct.smul_left_injective_of_isCoveringMap hcov hfib (P := P) ?_
    apply Subtype.ext
    show (γ : isom d) • ι (ι.retract x) = (γ' : isom d) • ι (ι.retract x)
    rw [← Classical.choose_spec (hr γ), ← Classical.choose_spec (hr γ'), hg]

/-- **Rem 5.3, causal half, compact diamonds** (l.1800–1805): the diamonds of a linear twisted
product over a GH flat spacetime are compact. Proved from the cover-level statement
`cover_gh_of_isLTPData` by descent through the presentation `π : Ω → B`:
`J_B(π x, π y) = π(⋃_{x ≤ γ y} J_Ω(x, γ y))`, a finite union of compact sets
(`TwistedProduct.exists_lift_le` lifts both relations). -/
theorem isCompact_diamond_of_isLTPData {B : FlatSpacetime.{u} d} {M₁ : FlatSpacetime.{v} d₁}
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} {ι : AffineMinkEmbedding d₁ d}
    (h : IsLTPData B M₁ Γ Ω ι) (hM : GH M₁) (p q : B) :
    IsCompact ((flatCausality d B).diamond ⊤ p q) := by
  haveI := h.quotient.invariant
  obtain ⟨hcpt, hfin⟩ := cover_gh_of_isLTPData h hM
  obtain ⟨π, hcov, hloc, hsurj, hfib⟩ := h.quotient.quot
  obtain ⟨x, rfl⟩ := hsurj p
  obtain ⟨y, rfl⟩ := hsurj q
  have hpush : ∀ {b c : Ω}, (flatCausality d Ω).le ⊤ b c → (flatCausality d B).le ⊤ (π b) (π c) :=
    fun hbc => hloc.strongMorphism.le_of_mapsTo (U := ⊤) (V := ⊤) (fun _ _ => trivial) hbc
  have hD : (flatCausality d B).diamond ⊤ (π x) (π y) =
      π '' ⋃ γ ∈ {γ : Γ | (flatCausality d Ω).le ⊤ x (γ • y)},
        (flatCausality d Ω).diamond ⊤ x (γ • y) := by
    ext z
    constructor
    · intro hz
      rw [Causality.mem_diamond] at hz
      obtain ⟨w, rfl, hxw⟩ := TwistedProduct.exists_lift_le hcov hloc hsurj hfib hz.1
      obtain ⟨y', hy', hwy'⟩ := TwistedProduct.exists_lift_le hcov hloc hsurj hfib hz.2
      obtain ⟨γ, hγ, hγy⟩ := (hfib y y').1 hy'.symm
      have e : ((⟨γ, hγ⟩ : Γ) • y) = y' :=
        Subtype.ext (by rw [FlatQuotient.coe_smul]; exact hγy)
      refine ⟨w, mem_iUnion₂.2 ⟨⟨γ, hγ⟩, ?_, ?_⟩, rfl⟩
      · show (flatCausality d Ω).le ⊤ x ((⟨γ, hγ⟩ : Γ) • y)
        rw [e]; exact (flatCausality d Ω).le_trans hxw hwy'
      · rw [Causality.mem_diamond, e]; exact ⟨hxw, hwy'⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨γ, -, hw⟩ := mem_iUnion₂.1 hw
      rw [Causality.mem_diamond] at hw ⊢
      refine ⟨hpush hw.1, ?_⟩
      have := hpush hw.2
      rwa [show π (γ • y) = π y from ((hfib y (γ • y)).2 ⟨γ, γ.2, rfl⟩).symm] at this
  rw [hD]
  exact ((hfin x y).isCompact_biUnion fun γ _ => hcpt _ _).image hcov.continuous

/-- **Rem 5.3, causal half** (l.1800–1805): a linear twisted product over a GH flat spacetime is
GH. Causality is proved (`isCausal_of_isLTPData`); compactness of diamonds is
`isCompact_diamond_of_isLTPData`, proved down to the cover-level `cover_gh_of_isLTPData`, itself
proved from `TwistedProduct.cover_gh_of_isQuotientOf` and `isClosed_diamond_of_retract`. -/
theorem gh_of_isLTPOver {B : FlatSpacetime.{u} d} {M₁ : FlatSpacetime.{v} d₁}
    (h : IsLTPOver B M₁) (hM : GH M₁) : GH B := by
  obtain ⟨Γ, Ω, ι, hd⟩ := h
  exact ⟨isCausal_of_isLTPData hd hM.1, isCompact_diamond_of_isLTPData hd hM⟩

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
