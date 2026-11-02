import Causal.Flat.TwistedProduct

/-!
# A group preserving a timelike `U` restricts to `U` on a subgroup of index `≤ 2`

The `RestrictsIn` reduction step of Barbot's Lemma 5.5 (`blem:suspendre`, `GHFspace.tex`
l.1834–1847), served to `loxo_elementary_misner` ([10.M], used at l.3279–3283),
`loxo_generic_centralExtension` and `loxo_generic_torusProduct` ([10.G], l.3391–3396) in
`Flat/Loxodromic.lean`. `Flat.TwistedProduct`'s `suspendre` needs `ι.RestrictsIn Γ`; its SCOPE
says that a `Γ` preserving `U = range ι` satisfies this on a subgroup of index `≤ 2`. This module
proves it. **No label is marked**: this is the orientation step of a lemma the paper calls obvious,
not a statement of the paper.

* `blem:suspendre`, `GHFspace.tex:1838–1843`, partial (the finite-index orientation step only;
  **no `sorry`**): `exists_restrictsIn_relIndex_le_two`.

> Assume that $\Gamma$ preserves a timelike affine subspace $\bf U$,
> and that $\Omega$ is invariant by translations by vectors contained
> in the orthogonal linear space ${\bf U}^{\perp}$. Then, the
> quotient of ${\bf U} \cap \Omega$ by $\Gamma$ is a
> flat spacetime $M$, and $B$ is the linear twisted product of
> $M$ by the euclidean space ${\bf U}^{\perp}$.

and at l.3279–3280 ([10.M]): "up to a linear twisted product, we can assume thanks to lemma
\ref{suspendre} that ${\bf U}$ is the entire \mink".

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` preserves the timelike affine subspace `U` (l.1838–1839) | ✓ carried (`hpres`, `U = range ι`) |
| `U` time-oriented compatibly (implicit) | ⚠ weakened: `ι` need not be orthochronous |
| conclusion: `Γ` acts on `U` by isometries of `U` (implicit in "flat spacetime `M`") | ⚠ weakened: on `Γ' ≤ Γ` of relative index `≤ 2` (`RestrictsIn Γ'`) |

## SCOPE (disclosed)

* The index `2` cannot be improved: `TwistedProduct.not_restrictsIn_glideGroup` is a `Γ` preserving
  a timelike line with no restriction to `Isom(𝐌²)`.
* `Γ'` is the kernel of `γ ↦ det L_γ` (`restrictDet`), hence normal in `Γ`; this is not stated.
* `ι` need not be orthochronous (the planner's orthochronous hypothesis is dropped): the sign of
  `ι.lin` on the future cone enters twice (`restrictLin_timeUnit_fst_pos`).
* `det_sq_of_minkQ_preserving` and `mem_lorentz_of_timeUnit` reprove `det_sq_of_minkQ` and
  `mem_lorentz_of` of `Flat/Isometries.lean`, which is not in this module's import closure.

Proof: for `γ ∈ Γ`, `L_γ = ι.coproj ∘ L(γ) ∘ ι.lin` (`restrictLin`) satisfies
`ι.lin ∘ L_γ = L(γ) ∘ ι.lin` (`lin_restrictLin`, from `hpres` and `coproj_lin`). It preserves
`minkQ`, so `det L_γ = ±1`, it sends `(1, 0)` to the future (`L(γ)` is orthochronous and `ι.lin`
preserves `minkB`), and it is multiplicative in `γ` (`ι.lin` injective). So `γ ↦ det L_γ` is a hom
`Γ →* ℝˣ` with range in `{±1}`; its kernel `Γ'` has index `≤ 2` (`Subgroup.index_ker`). For
`γ ∈ Γ'`, `p ↦ L_γ p + ι.retract (γ • ι 0)` lies in `Isom(𝐌^{d₁+1})` and restricts `γ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
planner proof plan (`/tmp/loxplan/GR_RestrictOrient.lean`).
-/

namespace Causal.Flat.Lox
open Set
variable {d d₁ : ℕ}

/-- The linear part of `γ` read on `U` through `ι`: `ι.coproj ∘ L(γ) ∘ ι.lin`. -/
noncomputable def restrictLin (ι : AffineMinkEmbedding d₁ d) (γ : isom d) :
    Minkowski d₁ →ₗ[ℝ] Minkowski d₁ :=
  ι.coproj ∘ₗ ((γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear : Minkowski d →ₗ[ℝ] Minkowski d) ∘ₗ ι.lin

theorem smul_mem_range {ι : AffineMinkEmbedding d₁ d} {γ : isom d}
    (h : (fun p => γ • p) '' Set.range ι = Set.range ι) (p : Minkowski d₁) :
    γ • ι p ∈ Set.range ι := h ▸ mem_image_of_mem _ (mem_range_self p)

theorem lin_restrictLin {ι : AffineMinkEmbedding d₁ d} {γ : isom d}
    (h : (fun p => γ • p) '' Set.range ι = Set.range ι) (u : Minkowski d₁) :
    ι.lin (restrictLin ι γ u) = (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (ι.lin u) := by
  obtain ⟨a, ha⟩ := smul_mem_range h u
  obtain ⟨b, hb⟩ := smul_mem_range h 0
  have e : (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (ι.lin u) = ι.lin (a - b) := by
    rw [← ι.apply_sub, ha, hb, isom_smul_def, isom_smul_def, isom_sub,
      show ι.toAffineMap u - ι.toAffineMap 0 = ι.lin (u - 0) from ι.apply_sub 0 u, sub_zero]
  simp only [restrictLin, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [e, ι.coproj_lin]


theorem minkQ_restrictLin {ι : AffineMinkEmbedding d₁ d} {γ : isom d}
    (h : (fun p => γ • p) '' Set.range ι = Set.range ι) (u : Minkowski d₁) :
    minkQ (restrictLin ι γ u) = minkQ u := by
  rw [← ι.minkQ_lin, lin_restrictLin h, ← linearPart_apply, lorentz.minkQ_apply (linearPart γ).2,
    ι.minkQ_lin]

theorem restrictLin_one (ι : AffineMinkEmbedding d₁ d) : restrictLin ι 1 = LinearMap.id :=
  LinearMap.ext fun u => by
    simp only [restrictLin, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    show ι.coproj ((1 : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (ι.lin u)) = u
    exact ι.coproj_lin u

theorem restrictLin_mul {ι : AffineMinkEmbedding d₁ d} {γ γ' : isom d}
    (h : (fun p => γ • p) '' Set.range ι = Set.range ι)
    (h' : (fun p => γ' • p) '' Set.range ι = Set.range ι) :
    restrictLin ι (γ * γ') = restrictLin ι γ ∘ₗ restrictLin ι γ' := by
  have hh : (fun p => (γ * γ') • p) '' Set.range ι = Set.range ι := by
    rw [show (fun p => (γ * γ') • p) = (fun p => γ • p) ∘ (fun p => γ' • p) from
      funext fun p => mul_smul _ _ _, image_comp, h', h]
  refine LinearMap.ext fun u => ι.lin_injective ?_
  rw [LinearMap.comp_apply, lin_restrictLin hh, lin_restrictLin h, lin_restrictLin h']
  rfl

/-- **Restricted linear parts are time-orientation preserving**, whatever `ι`'s orientation: the
time unit `(1, 0)` of `𝐌^{d₁+1}` goes to a vector with positive time coordinate. -/
theorem restrictLin_timeUnit_fst_pos {ι : AffineMinkEmbedding d₁ d} {γ : isom d}
    (h : (fun p => γ • p) '' Set.range ι = Set.range ι) :
    0 < (restrictLin ι γ ((1 : ℝ), 0)).1 := by
  set e : Minkowski d₁ := ((1 : ℝ), 0)
  set f := ι.lin e
  set L := linearPart γ
  have he : minkQ e = -1 := by simp [e, minkQ]
  have hLf : ι.lin (restrictLin ι γ e) = (L : Minkowski d ≃ₗ[ℝ] Minkowski d) f := by
    rw [lin_restrictLin h, linearPart_apply]
  have hfq : minkQ f < 0 := by rw [ι.minkQ_lin, he]; norm_num
  have hB : minkB f ((L : Minkowski d ≃ₗ[ℝ] Minkowski d) f) < 0 := by
    rcases isFutureTimelike_or_neg hfq with hf | hf
    · have h2 := lorentz.isFutureTimelike_apply L.2 hf
      exact minkB_neg_of_isFutureTimelike hf ⟨h2.1.le, h2.2.le⟩ (fun h0 => by
        have := h2.2; rw [h0, minkQ_zero] at this; exact lt_irrefl _ this)
    · have h2 := lorentz.isFutureTimelike_apply L.2 hf
      have := minkB_neg_of_isFutureTimelike hf ⟨h2.1.le, h2.2.le⟩ (fun h0 => by
        have := h2.2; rw [h0, minkQ_zero] at this; exact lt_irrefl _ this)
      rw [map_neg] at this
      simpa [minkB] using this
  have h3 : minkB e (restrictLin ι γ e) < 0 := by rw [← ι.minkB_lin, hLf]; exact hB
  simpa [minkB, e] using h3


/-! ### `minkQ`-preserving maps: determinant `±1`, and a criterion for `SO₀` -/

private theorem ro_minkB_add_left (u v w : Minkowski d) : minkB (u + v) w = minkB u w + minkB v w := by
  simp only [minkB, Prod.fst_add, Prod.snd_add, inner_add_left]; ring

private theorem ro_minkB_smul_left (c : ℝ) (v w : Minkowski d) :
    minkB (c • v) w = c * minkB v w := by
  simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_left]; ring

private theorem ro_minkB_add_right (u v w : Minkowski d) :
    minkB u (v + w) = minkB u v + minkB u w := by
  rw [minkB_comm, ro_minkB_add_left, minkB_comm v, minkB_comm w]

private theorem ro_minkB_smul_right (c : ℝ) (v w : Minkowski d) :
    minkB v (c • w) = c * minkB v w := by
  rw [minkB_comm, ro_minkB_smul_left, minkB_comm]

/-- `minkB` as a bilinear form. -/
private noncomputable def roForm (d : ℕ) : LinearMap.BilinForm ℝ (Minkowski d) :=
  LinearMap.mk₂ ℝ minkB ro_minkB_add_left ro_minkB_smul_left ro_minkB_add_right
    (fun c v w => ro_minkB_smul_right c v w)

private theorem ro_minkQ_add (v w : Minkowski d) :
    minkQ (v + w) = minkQ v + 2 * minkB v w + minkQ w := by
  rw [minkQ_eq_minkB, minkQ_eq_minkB, minkQ_eq_minkB, ro_minkB_add_left, ro_minkB_add_right,
    ro_minkB_add_right, minkB_comm w v]; ring

private theorem ro_minkB_map {A : Minkowski d →ₗ[ℝ] Minkowski d}
    (hA : ∀ v, minkQ (A v) = minkQ v) (v w : Minkowski d) : minkB (A v) (A w) = minkB v w := by
  have h := hA (v + w)
  rw [map_add, ro_minkQ_add, ro_minkQ_add, hA, hA] at h
  linarith

private theorem ro_eq_zero_of_minkB {v : Minkowski d} (h : ∀ w, minkB v w = 0) : v = 0 := by
  have h1 := h (1, 0)
  have h2 := h (0, v.2)
  simp only [minkB, mul_one, inner_zero_right, add_zero, neg_eq_zero, mul_zero, neg_zero,
    zero_add, real_inner_self_eq_norm_sq] at h1 h2
  have : v.2 = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  exact Prod.ext h1 this

private theorem roForm_nondegenerate : (roForm d).Nondegenerate :=
  ⟨fun v h => ro_eq_zero_of_minkB h,
    fun w h => ro_eq_zero_of_minkB fun z => by rw [minkB_comm]; exact h z⟩

/-- **A `minkQ`-preserving linear map has determinant `±1`**: `det A ^ 2 = 1` (the Gram matrix
of `minkB` is invertible and `Aᵀ G A = G`). -/
theorem det_sq_of_minkQ_preserving {A : Minkowski d →ₗ[ℝ] Minkowski d}
    (hA : ∀ v, minkQ (A v) = minkQ v) : LinearMap.det A ^ 2 = 1 := by
  classical
  let b := Module.finBasis ℝ (Minkowski d)
  have hc : (roForm d).compl₁₂ A A = roForm d := LinearMap.ext₂ fun v w => by
    simp [roForm, ro_minkB_map hA]
  have hm :=
    LinearMap.toMatrix₂_compl₁₂ (b₁ := b) (b₂ := b) (b₁' := b) (b₂' := b) (roForm d) A A
  rw [hc] at hm
  have hdet := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  have hne : (LinearMap.toMatrix₂ b b (roForm d)).det ≠ 0 :=
    (LinearMap.nondegenerate_iff_det_ne_zero b).1 roForm_nondegenerate
  have h2 : (LinearMap.det A ^ 2 - 1) * (LinearMap.toMatrix₂ b b (roForm d)).det = 0 := by
    linear_combination -hdet
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)

/-- **A criterion for `SO₀(1, d)`**: a `minkQ`-preserving automorphism of determinant `1` whose
image of the time unit `(1, 0)` has positive time coordinate lies in `lorentz d`. -/
theorem mem_lorentz_of_timeUnit {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hQ : ∀ v, minkQ (A v) = minkQ v) (h0 : 0 < (A ((1 : ℝ), 0)).1)
    (hdet : LinearMap.det (A : Minkowski d →ₗ[ℝ] Minkowski d) = 1) : A ∈ lorentz d := by
  refine ⟨hQ, fun v hv => ?_, hdet⟩
  have hq : minkQ (A v) ≤ 0 := by rw [hQ]; exact hv.2
  refine ⟨?_, hq⟩
  by_contra hneg
  push Not at hneg
  have he : IsFutureTimelike (A ((1 : ℝ), 0)) := ⟨h0, by rw [hQ]; simp [minkQ]⟩
  have hz : IsFutureCausal (-(A v)) := ⟨by simp; linarith, by simpa using hq⟩
  have hz0 : -(A v) ≠ 0 := fun h => by
    have : (A v).1 = 0 := by simpa using congrArg Prod.fst h
    linarith
  have h1 := minkB_neg_of_isFutureTimelike he hz hz0
  have h2 := ro_minkB_map (A := (A : Minkowski d →ₗ[ℝ] Minkowski d)) hQ ((1 : ℝ), 0) v
  simp only [LinearEquiv.coe_coe] at h2
  have h3 : minkB (A ((1 : ℝ), 0)) (-(A v)) = -minkB (A ((1 : ℝ), 0)) (A v) := by
    simpa using ro_minkB_smul_right (-1) (A ((1 : ℝ), 0)) (A v)
  rw [h3, h2] at h1
  simp [minkB] at h1
  linarith [hv.1]


/-! ### The restriction, on the determinant-one part -/

/-- **The restriction to `U`** of a `γ` preserving `U = range ι` whose restricted linear part has
determinant `1`: `p ↦ L_γ p + q(γ ι(0))`, an element of `Isom(𝐌^{d₁+1})` with `ι ∘ g = γ ∘ ι`. -/
theorem exists_restricts_of_det_eq_one {ι : AffineMinkEmbedding d₁ d} {γ : isom d}
    (h : (fun p => γ • p) '' Set.range ι = Set.range ι)
    (hdet : LinearMap.det (restrictLin ι γ) = 1) : ∃ g : isom d₁, ι.Restricts γ g := by
  set A := LinearMap.equivOfDetNeZero (restrictLin ι γ) (by rw [hdet]; norm_num)
  have hA : ∀ p, A p = restrictLin ι γ p := fun _ => rfl
  set c := ι.retract (γ • ι 0)
  let g : Minkowski d₁ ≃ᵃ[ℝ] Minkowski d₁ :=
    A.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (Minkowski d₁) c)
  have hg : ∀ p, g p = c + restrictLin ι γ p := fun p => by
    show c +ᵥ A p = _
    rw [hA, vadd_eq_add]
  have hgl : g.linear = A := by
    refine LinearEquiv.ext fun p => ?_
    have := isom_sub g 0 p
    rw [hg, hg, map_zero, add_zero, add_sub_cancel_left, sub_zero] at this
    rw [← this, hA]
  have hmem : g ∈ isom d₁ := by
    rw [mem_isom_iff, hgl]
    refine mem_lorentz_of_timeUnit (fun v => ?_) ?_ ?_
    · rw [hA]; exact minkQ_restrictLin h v
    · rw [hA]; exact restrictLin_timeUnit_fst_pos h
    · exact hdet
  refine ⟨⟨g, hmem⟩, fun p => ?_⟩
  obtain ⟨x, hx⟩ := smul_mem_range h 0
  have hc : ι c = γ • ι 0 := by
    show ι (ι.retract (γ • ι 0)) = _
    rw [← hx, ι.retract_apply]
  rw [isom_smul_def]
  show ι (g p) = _
  rw [hg, ι.apply_add, hc, lin_restrictLin h]
  have := isom_sub (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d) (ι 0) (ι p)
  rw [ι.apply_sub, sub_zero] at this
  rw [← this, isom_smul_def, isom_smul_def]
  abel


/-- **The determinant of the restricted linear part**, as a homomorphism `Γ →* ℝ` (multiplicative
because `L_{γγ'} = L_γ L_{γ'}` on `U`, `restrictLin_mul`). -/
noncomputable def restrictDet (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hpres : ∀ γ ∈ Γ, (fun p => γ • p) '' Set.range ι = Set.range ι) : Γ →* ℝ where
  toFun γ := LinearMap.det (restrictLin ι γ.1)
  map_one' := by
    show LinearMap.det (restrictLin ι 1) = 1
    rw [restrictLin_one, LinearMap.det_id]
  map_mul' γ γ' := by
    show LinearMap.det (restrictLin ι (γ.1 * γ'.1)) = _
    rw [restrictLin_mul (hpres _ γ.2) (hpres _ γ'.2), LinearMap.det_comp]

theorem exists_restrictsIn_relIndex_le_two (ι : AffineMinkEmbedding d₁ d)
    {Γ : Subgroup (isom d)}
    (hpres : ∀ γ ∈ Γ, (fun p => γ • p) '' Set.range ι = Set.range ι) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧ Γ'.relIndex Γ ≤ 2 ∧
      ι.RestrictsIn Γ' := by
  classical
  set φ := (restrictDet ι hpres).toHomUnits
  have hφ : ∀ γ : Γ, (φ γ : ℝ) = LinearMap.det (restrictLin ι γ.1) := fun _ => rfl
  have hrange : (φ.range : Set ℝˣ) ⊆ {1, -1} := by
    rintro _ ⟨γ, rfl⟩
    have h2 := det_sq_of_minkQ_preserving (minkQ_restrictLin (hpres _ γ.2))
    rw [← hφ] at h2
    rcases sq_eq_one_iff.1 h2 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h]; rfl))
  have hfin : (φ.range : Set ℝˣ).Finite := (Set.toFinite _).subset hrange
  have hcard : Nat.card φ.range ≤ 2 := by
    refine (Nat.card_mono (Set.toFinite _) hrange).trans ?_
    rw [Nat.card_coe_set_eq]
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have hpos : Nat.card φ.range ≠ 0 := by
    haveI : Finite φ.range := hfin.to_subtype
    exact Nat.card_pos.ne'
  have hrel : (φ.ker.map Γ.subtype).relIndex Γ = φ.ker.index := by
    rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective]
  refine ⟨φ.ker.map Γ.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [hrel, Subgroup.index_ker]; exact hpos
  · rw [hrel, Subgroup.index_ker]; exact hcard
  · rintro _ ⟨γ, hγ, rfl⟩
    have h1 : (φ γ : ℝ) = 1 := by rw [(MonoidHom.mem_ker).1 hγ]; rfl
    rw [hφ] at h1
    exact exists_restricts_of_det_eq_one (hpres _ γ.2) h1

end Causal.Flat.Lox
