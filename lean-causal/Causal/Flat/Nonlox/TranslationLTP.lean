import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Bieberbach
import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.CauchyComplete

/-!
# `CausalScaffold.Flat.Nonlox.TranslationLTP` — a group of translations on `U` with spacelike span gives a linear twisted product over a translation spacetime

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9.E
(`GHFspace.tex` l.2611–2617), Lemma 5.5 (`blem:suspendre`, l.1833–1845) and [3.T] (l.586–593).
Line numbers are those of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`.

* `bthm:` none certified. `exists_isTranslationSpacetime_isLTPOver` is the last step of the
  elliptic case [9.E] (items (3) and (4) of `Causal.Flat.nonloxodromic_elliptic`'s
  obstruction), proved with **no `sorry`**: if `H` acts freely and properly discontinuously on
  `𝐌ⁿ`, preserves the timelike affine subspace `U` acting on it by translations `τ ∈ Λ ⊆ U − U`,
  and the span of `Λ` is spacelike (positive definite), then `B = H\𝐌ⁿ` is a linear twisted
  product over a translation spacetime of dimension `d₁ + 1 ≤ d + 1`.

> According to Bieberbach's Theorem, up to finite index, there is a unique maximal affine
> subspace ${\bf U}$ on which $\Gamma$ acts by translations. Moreover, $SO(n-1) \subset
> SO(1,n-1)$ is the stabilizer of a point in ${\bf H}^{n-1}$, i.e., preserves a timelike
> direction $\Delta_{0}$: it follows that ${\bf U}$ is timelike. According to lemma
> \ref{suspendre}, $M(S)$ is thus a linear twisted product over a translation spacetime.

## Proof

`V := span Λ ≤ U − U` is positive definite, so `U − U = V ⊕ V^⊥` (`minkForm`-orthogonal);
the `V^⊥`-component `v` of a timelike `t ∈ U − U` is timelike (`minkQ v = minkQ t − minkQ (t − v)`),
taken future. The construction of `TwistedProduct.exists_affineMinkEmbedding_of_isTimelike`,
re-run with this prescribed `v` (`exists_affineMinkEmbedding_of_orth`, private), gives an
orthochronous `ι` with `range ι = U` mapping `{0} × ℝ^{d₁}` onto `v^⊥ ∩ (U − U) ⊇ V`. Each
`γ ∈ H` then restricts to `U` as the horizontal translation by the `λ` with `ι.lin (0, λ) = τ_γ`
(`RestrictsIn`), `ι.restrictGroup H = horizGroup Λ₁` for the subgroup `Λ₁` of these `λ`, and
`Λ₁` is ball-finite by the proper discontinuity of `H` on a closed ball about `ι 0`. Lemma 5.5
(`suspendre`, `𝐌ⁿ` is trivially `U^⊥`-invariant) concludes, in the frame `φ = 1`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` acts freely, properly discontinuously on `𝐌ⁿ` (l.2609–2610) | ✓ carried (instances, `hprop`) |
| `Γ` acts on `U` by translations (l.2612–2613) | ✓ carried (`htr`, vectors in `Λ`) |
| `U` timelike (l.2613–2615) | ✓ carried (`hU`) |
| the translations are spacelike (l.586–593) | ⚠ strengthened: the **span** of `Λ` is spacelike (`hsp`); necessary, `Causal.Flat.spacelike_translations_null_span`; supplied by `Flat/Nonlox/SpacelikeSpan` |

## SCOPE (disclosed)

* The frame of [3.T] is `φ = 1`: the base is read in the coordinates of `ι`, where the
  translations are already horizontal.
* `d₁ ≤ d` (`dim U ≤ n`), from the injectivity of `ι.lin`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Nonlox

open Set Function TopologicalSpace Submodule
open scoped Pointwise

variable {d : ℕ}

/-- A vector orthogonal to a unit timelike vector is spacelike (`minkQ > 0` off `0`). -/
private theorem tl_minkQ_pos_of_orth {f w : Minkowski d} (hf : minkQ f = -1)
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

private theorem tl_minkB_sum_right {α : Type*} (s : Finset α) (v : Minkowski d)
    (w : α → Minkowski d) : minkB v (∑ i ∈ s, w i) = ∑ i ∈ s, minkB v (w i) :=
  map_sum (minkForm d v) w s

private theorem tl_inv_sqrt_aux {s q : ℝ} (hs : 0 < s) (h : s ^ 2 = q) : s⁻¹ * (s⁻¹ * q) = 1 := by
  subst h; field_simp

/-- **A future timelike vector of `U − U` orthogonal to a positive definite `V ≤ U − U`.** -/
private theorem exists_timelike_orth {U : AffineSubspace ℝ (Minkowski d)}
    (hU : IsTimelikeSubspace U) {V : Submodule ℝ (Minkowski d)} (hVU : V ≤ U.direction)
    (hV : ∀ w ∈ V, w ≠ 0 → 0 < minkQ w) :
    ∃ v ∈ U.direction, minkQ v < 0 ∧ 0 < v.1 ∧ ∀ u ∈ V, minkB v u = 0 := by
  obtain ⟨t, htD, ht⟩ := hU
  have key : ∀ m : V, (minkForm d).restrict V m m = 0 → m = 0 := by
    intro m hm
    by_contra hne
    have hne' : (m : Minkowski d) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have hpos := hV m m.2 hne'
    rw [minkQ_eq_minkB] at hpos
    exact hpos.ne' hm
  have hnd : ((minkForm d).restrict V).Nondegenerate :=
    ⟨fun m hm => key m (hm m), fun m hm => key m (hm m)⟩
  have hrefl : (minkForm d).IsRefl := fun x y h => by
    simp only [minkForm_apply] at h ⊢
    rw [minkB_comm]; exact h
  have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  have htop : t ∈ V ⊔ (minkForm d).orthogonal V := by
    rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 htop
  have hzV : ∀ u ∈ V, minkB z u = 0 := fun u hu => by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.1 hz) u hu
    rw [minkB_comm]; exact this
  have hyq : 0 ≤ minkQ y := by
    rcases eq_or_ne y 0 with h | h
    · simp [h, minkQ]
    · exact (hV y hy h).le
  have hzq : minkQ z < 0 := by
    have hq : minkQ t = minkQ y + 2 * minkB y z + minkQ z := by rw [← hyz, minkQ_add]
    rw [minkB_comm, hzV y hy] at hq
    linarith
  have hzD : z ∈ U.direction := by
    have : z = t - y := by rw [← hyz]; abel
    rw [this]; exact U.direction.sub_mem htD (hVU hy)
  have h1 : z.1 ≠ 0 := by
    intro h; simp only [minkQ, h] at hzq; nlinarith [sq_nonneg ‖z.2‖]
  rcases lt_or_gt_of_ne h1 with h | h
  · refine ⟨-z, U.direction.neg_mem hzD, by simpa [minkQ] using hzq,
      by simpa using neg_pos.2 h, fun u hu => ?_⟩
    rw [minkB_neg_left, hzV u hu, neg_zero]
  · exact ⟨z, hzD, hzq, h, hzV⟩

/-- **`exists_affineMinkEmbedding_of_isTimelike` with a prescribed future timelike direction**:
for a future timelike `v ∈ U − U`, an orthochronous `ι` with `range ι = U` maps `{0} × ℝ^{d₁}`
onto `v^⊥ ∩ (U − U)` (the proof of `TwistedProduct.exists_affineMinkEmbedding_of_isTimelike`,
with `f` the normalised `v`). -/
private theorem exists_affineMinkEmbedding_of_orth {U : AffineSubspace ℝ (Minkowski d)}
    {v : Minkowski d} (hvD : v ∈ U.direction) (hv : minkQ v < 0) (hvpos : 0 < v.1) :
    ∃ (d₁ : ℕ) (ι : AffineMinkEmbedding d₁ d), ι.Orthochronous ∧ ι.range = U ∧
      ∀ u ∈ U.direction, minkB v u = 0 → ∃ y, ι.lin ((0 : ℝ), y) = u := by
  have hc : 0 < -minkQ v := by linarith
  set c := Real.sqrt (-minkQ v) with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.2 hc
  set f : Minkowski d := c⁻¹ • v with hfdef
  have hf : minkQ f = -1 := by
    rw [hfdef, minkQ_eq_minkB, minkB_smul_left, minkB_smul_right, ← minkQ_eq_minkB]
    have h := tl_inv_sqrt_aux hcpos (Real.sq_sqrt hc.le)
    have : c⁻¹ * (c⁻¹ * minkQ v) = -(c⁻¹ * (c⁻¹ * -minkQ v)) := by ring
    rw [this, h]
  have hfD : f ∈ U.direction := U.direction.smul_mem _ hvD
  let W : Submodule ℝ (Minkowski d) := U.direction ⊓ LinearMap.ker (minkForm d f)
  have hWD : ∀ {w : Minkowski d}, w ∈ W → w ∈ U.direction := fun h => (Submodule.mem_inf.1 h).1
  have hWf : ∀ {w : Minkowski d}, w ∈ W → minkB f w = 0 := fun h =>
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 h).2
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := (minkForm d).restrict W)
    ⟨fun x y => minkB_comm (x : Minkowski d) y⟩
  have hbpos : ∀ i, 0 < minkQ (b i : Minkowski d) := fun i =>
    tl_minkQ_pos_of_orth hf (by rw [minkB_comm]; exact hWf (b i).2)
      (fun h => b.ne_zero i (Subtype.ext h))
  let e : Fin (Module.finrank ℝ W) → Minkowski d := fun i =>
    (Real.sqrt (minkQ (b i : Minkowski d)))⁻¹ • (b i : Minkowski d)
  have he : ∀ i j, minkB (e i) (e j) = if i = j then 1 else 0 := by
    intro i j
    simp only [e, minkB_smul_left, minkB_smul_right]
    split_ifs with h
    · subst h
      rw [← minkQ_eq_minkB]
      exact tl_inv_sqrt_aux (Real.sqrt_pos.2 (hbpos i)) (Real.sq_sqrt (hbpos i).le)
    · have : minkB (b i : Minkowski d) (b j) = 0 := hb h
      rw [this, mul_zero, mul_zero]
  have hef : ∀ i, minkB f (e i) = 0 := fun i => by
    simp only [e, minkB_smul_right, hWf (b i).2, mul_zero]
  let L : Minkowski (Module.finrank ℝ W) →ₗ[ℝ] Minkowski d :=
    (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ W)))).smulRight f +
      ∑ i, ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) →L[ℝ] ℝ).toLinearMap ∘ₗ
        LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ W)))).smulRight (e i)
  have hL : ∀ x : Minkowski (Module.finrank ℝ W), L x = x.1 • f + ∑ i, x.2 i • e i := by
    intro x
    simp [L, LinearMap.sum_apply]
  have hQ : ∀ x : Minkowski (Module.finrank ℝ W), minkQ (L x) = minkQ x := by
    intro x
    rw [hL, minkQ_add]
    have h1 : minkB (x.1 • f) (∑ i, x.2 i • e i) = 0 := by
      rw [minkB_smul_left, tl_minkB_sum_right]
      simp [minkB_smul_right, hef]
    have h2 : minkQ (∑ i, x.2 i • e i) = ∑ i, x.2 i ^ 2 := by
      rw [minkQ_eq_minkB, tl_minkB_sum_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [minkB_comm, minkB_smul_left, tl_minkB_sum_right]
      simp [minkB_smul_right, he, sq]
    have h3 : minkQ (x.1 • f) = -x.1 ^ 2 := by
      rw [minkQ_eq_minkB, minkB_smul_left, minkB_smul_right, ← minkQ_eq_minkB, hf]; ring
    rw [h1, h2, h3]
    simp only [minkQ, EuclideanSpace.real_norm_sq_eq]
    ring
  have hLD : ∀ x, L x ∈ U.direction := fun x => by
    rw [hL]
    exact U.direction.add_mem (U.direction.smul_mem _ hfD)
      (U.direction.sum_mem fun i _ => U.direction.smul_mem _
        (U.direction.smul_mem _ (hWD (b i).2)))
  have surj : ∀ u ∈ U.direction, ∃ y, L (-minkB u f, y) = u := by
    intro u hu
    set a := -minkB u f
    have hw : u - a • f ∈ W := by
      refine Submodule.mem_inf.2 ⟨U.direction.sub_mem hu (U.direction.smul_mem _ hfD),
        LinearMap.mem_ker.2 ?_⟩
      show minkB f (u - a • f) = 0
      rw [minkB_sub_right, minkB_smul_right, ← minkQ_eq_minkB, hf, minkB_comm]
      simp [a]
    set w : W := ⟨_, hw⟩
    refine ⟨WithLp.toLp 2 fun i => b.repr w i * Real.sqrt (minkQ (b i : Minkowski d)), ?_⟩
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
    ⟨L.toAffineMap + AffineMap.const ℝ (Minkowski (Module.finrank ℝ W)) p₀, fun w => ?_⟩, ?_, ?_,
    ?_⟩
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
      obtain ⟨y, hy⟩ := surj (q - p₀) (AffineSubspace.vsub_mem_direction hq hp₀)
      exact ⟨(-minkB (q - p₀) f, y), by simp [hy]⟩
  · intro u hu huv
    obtain ⟨y, hy⟩ := surj u hu
    have h0 : minkB u f = 0 := by
      rw [hfdef, minkB_smul_right, minkB_comm, huv, mul_zero]
    rw [h0, neg_zero] at hy
    refine ⟨y, ?_⟩
    show (L.toAffineMap + AffineMap.const ℝ _ p₀).linear ((0 : ℝ), y) = u
    simpa using hy

/-- The horizontal translation vectors `λ ∈ ℝ^{d₁}` whose translation is the restriction of some
`γ ∈ H` to `U = range ι`. -/
private def horizLattice {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) (H : Subgroup (isom d)) :
    AddSubgroup (EuclideanSpace ℝ (Fin d₁)) where
  carrier := {y | ∃ γ ∈ H, ι.Restricts γ (horizTranslation d₁ (Multiplicative.ofAdd y))}
  zero_mem' := ⟨1, H.one_mem, by
    rw [ofAdd_zero, map_one]; exact AffineMinkEmbedding.Restricts.one⟩
  add_mem' := by
    rintro a b ⟨γ, hγ, h⟩ ⟨γ', hγ', h'⟩
    exact ⟨γ * γ', H.mul_mem hγ hγ', by rw [ofAdd_add, map_mul]; exact h.mul h'⟩
  neg_mem' := by
    rintro a ⟨γ, hγ, h⟩
    exact ⟨γ⁻¹, H.inv_mem hγ, by rw [ofAdd_neg, map_inv]; exact h.inv⟩

/-- **[9.E], items (3)–(4)** (`GHFspace.tex` l.2611–2617, through Lemma 5.5 `blem:suspendre`,
l.1833–1845, and [3.T], l.586–593): if `H` acts freely and properly discontinuously on `𝐌ⁿ`,
acting on the timelike affine subspace `U` by translations from `Λ ⊆ U − U` whose span is
spacelike, then `B = H\𝐌ⁿ` is a linear twisted product over a translation spacetime. -/
theorem exists_isTranslationSpacetime_isLTPOver {H : Subgroup (isom d)}
    [FlatQuotient.Invariant H ⊤] [IsCancelSMul H (⊤ : TopologicalSpace.Opens (Minkowski d))]
    [ProperlyDiscontinuousSMul H (⊤ : TopologicalSpace.Opens (Minkowski d))]
    (B : FlatSpacetime.{0} d) (hB : IsQuotientOf B H ⊤)
    {U : AffineSubspace ℝ (Minkowski d)} (hU : IsTimelikeSubspace U)
    {Λ : AddSubgroup (Minkowski d)} (hΛU : (Λ : Set (Minkowski d)) ⊆ (U.direction : Set _))
    (htr : ∀ γ ∈ H, ∃ τ ∈ Λ, ∀ p ∈ U, γ • p = p + τ)
    (hsp : ∀ w ∈ span ℝ (Λ : Set (Minkowski d)), w ≠ 0 → 0 < minkQ w)
    (hprop : ∀ K : Set (Minkowski d), IsCompact K →
      {γ : isom d | γ ∈ H ∧ (γ • K ∩ K).Nonempty}.Finite) :
    ∃ d₁ : ℕ, d₁ ≤ d ∧ ∃ M₁ : FlatSpacetime.{0} d₁, IsTranslationSpacetime M₁ ∧
      IsLTPOver B M₁ := by
  classical
  have hVU : span ℝ (Λ : Set (Minkowski d)) ≤ U.direction := Submodule.span_le.2 hΛU
  obtain ⟨v, hvD, hvq, hv1, hvV⟩ := exists_timelike_orth hU hVU hsp
  obtain ⟨d₁, ι, hι, hrange, hlift⟩ := exists_affineMinkEmbedding_of_orth hvD hvq hv1
  have hdim : d₁ ≤ d := by
    have := LinearMap.finrank_le_finrank_of_injective ι.lin_injective
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace,
      Fintype.card_fin] at this
    omega
  have hmemU : ∀ p, ι p ∈ U := fun p => by
    rw [← hrange]
    exact AffineSubspace.mem_map.2 ⟨p, AffineSubspace.mem_top _ _ _, rfl⟩
  have hhor : ∀ γ ∈ H, ∃ y, ι.Restricts γ (horizTranslation d₁ (Multiplicative.ofAdd y)) := by
    intro γ hγ
    obtain ⟨τ, hτ, hγτ⟩ := htr γ hγ
    obtain ⟨y, hy⟩ := hlift τ (hΛU hτ) (hvV τ (Submodule.subset_span hτ))
    refine ⟨y, fun p => ?_⟩
    rw [horizTranslation_smul, toAdd_ofAdd, add_comm, ι.apply_add, hy, hγτ _ (hmemU p)]
  have hres : ι.RestrictsIn H := fun γ hγ => by
    obtain ⟨y, hy⟩ := hhor γ hγ
    exact ⟨_, hy⟩
  have hG : ι.restrictGroup H = horizGroup (horizLattice ι H) := by
    ext g
    rw [AffineMinkEmbedding.mem_restrictGroup, mem_horizGroup]
    constructor
    · rintro ⟨γ, hγ, hg⟩
      obtain ⟨y, hy⟩ := hhor γ hγ
      exact ⟨y, ⟨γ, hγ, hy⟩, hy.unique hg⟩
    · rintro ⟨y, ⟨γ, hγ, hy⟩, rfl⟩
      exact ⟨γ, hγ, hy⟩
  have hΩ : ι.preimageOpens (⊤ : Opens (Minkowski d)) = ⊤ := by
    ext x; simp
  have hball : BallFinite (horizLattice ι H) := ⟨fun R => by
    set Lc := LinearMap.toContinuousLinearMap ι.lin
    set K : Set (Minkowski d) := Metric.closedBall (ι 0) (‖Lc‖ * max R 0)
    have hK : IsCompact K := isCompact_closedBall _ _
    refine ((hprop K hK).image fun γ => (ι.coproj (γ • ι 0 - ι 0)).2).subset ?_
    rintro y ⟨⟨γ, hγ, hy⟩, hyR⟩
    have h0 : γ • ι 0 = ι 0 + ι.lin ((0 : ℝ), y) := by
      rw [← hy 0, horizTranslation_smul, toAdd_ofAdd, add_zero]
      simpa using ι.apply_add 0 ((0 : ℝ), y)
    have hin : γ • ι 0 ∈ K := by
      rw [Metric.mem_closedBall, dist_eq_norm, h0, add_sub_cancel_left]
      calc ‖ι.lin ((0 : ℝ), y)‖ = ‖Lc ((0 : ℝ), y)‖ := rfl
        _ ≤ ‖Lc‖ * ‖((0 : ℝ), y)‖ := Lc.le_opNorm _
        _ ≤ ‖Lc‖ * max R 0 := by
          gcongr
          rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg y)]
          exact le_max_of_le_left hyR
    have h0K : ι 0 ∈ K :=
      Metric.mem_closedBall_self (mul_nonneg (norm_nonneg _) (le_max_right _ _))
    refine ⟨γ, ⟨hγ, γ • ι 0, Set.smul_mem_smul_set h0K, hin⟩, ?_⟩
    show (ι.coproj (γ • ι 0 - ι 0)).2 = y
    rw [h0, add_sub_cancel_left, ι.coproj_lin]⟩
  have hperp : ∀ w ∈ ι.perp, ∀ p ∈ (⊤ : Opens (Minkowski d)),
      p + w ∈ (⊤ : Opens (Minkowski d)) := fun _ _ _ _ => by simp
  refine ⟨d₁, hdim, ι.baseSpacetime B hB hres hperp, ⟨1, horizLattice ι H, hball, ?_⟩,
    suspendre B hB ι hι hres hperp⟩
  have hq := ι.isQuotientOf_baseSpacetime B hB hres hperp
  rw [hG, hΩ] at hq
  rw [frameConj_one]
  exact hq

end Causal.Flat.Nonlox
