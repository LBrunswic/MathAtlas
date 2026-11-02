import Causal.Flat.Develop
import Causal.Flat.Externals
import Causal.Flat.Bieberbach
import Causal.Flat.TwistedProduct
import Causal.Flat.Examples
import Causal.Flat.CauchyComplete

/-!
# `Causal.Flat.Nonlox.EllipticBieberbach` — the Bieberbach step of [9.E]

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9.1
"The elliptic case", lines of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`.
No ledger label is certified here: [9.E] (l.2604–2617) is prose. This module serves item (2) of
the obstruction of `Causal.Flat.nonloxodromic_elliptic` (`Flat/Nonloxodromic`).

* `exists_translationSubspace_of_fix_timelike` — the statement of item (2): closed, no `sorry`,
  from the external `BieberbachI` (DEC-36, `Flat/Bieberbach`).
* auxiliaries: `timelikeForm_pos'`, `timelikeForm_map`, `exists_euclEquiv_timelike` (the
  euclidean structure `⟨x | y⟩ + (2/k)⟨v | x⟩⟨v | y⟩`, `k = −|v|²`, as `⟪e x, e y⟫` for a linear
  `e : 𝐌ⁿ ≃ ℝⁿ`), `ellConj`, `ellHom` (the transport `γ ↦ e ∘ γ ∘ e⁻¹` of the stabiliser of `v`
  into `Isom(ℝⁿ)`), `isDiscreteEucl_ellHom_range` (properness on `𝐌ⁿ` ⇒ `IsDiscreteEucl`).

> There is a flat euclidean metric on \mink preserved by $\Gamma$. (l.2606)

> According to Bieberbach's Theorem, up to finite index, there is a unique maximal affine
> subspace ${\bf U}$ on which $\Gamma$ acts by translations. Moreover, $SO(n-1) \subset
> SO(1,n-1)$ is the stabilizer of a point in ${\bf H}^{n-1}$, i.e., preserves a timelike
> direction $\Delta_{0}$: it follows that ${\bf U}$ is timelike. (l.2611–2615)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`, and the euclidean model is `EuclideanSpace ℝ (Fin (d + 1))`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `L(Γ)` preserves a timelike direction (elliptic case, l.2612–2614) | ✓ carried: `hfix`, `L(γ) v = v`, `minkQ v < 0` |
| `Γ` discrete (Bieberbach, l.2611) | ✓ carried as properness on `𝐌ⁿ` (`hprop`), which is what the call site has (`CCAction.finite_of_fix_timelike`); `IsDiscreteEucl` of the transported group is proved from it |
| Bieberbach's theorem | carried as the external `BieberbachI (ℝ^{d+1})` (DEC-36) |
| "unique maximal `U`" | ⚠ weakened: uniqueness and maximality are not part of the conclusion; what is returned is `v ∈ U.direction` (so `U` is timelike, l.2615) and the translation lattice `Λ` |

## SCOPE (disclosed)

* No `sorry`. The conclusion does not state effectiveness, the `H`-invariance of `U`, or the
  normality of `H'`; Bieberbach delivers them (`BieberbachMaxConclusion`) but the consumer does
  not need them, so they are dropped.
* The euclidean structure is put on a type synonym `EllTl d` of `Minkowski d` inside the proof of
  `exists_euclEquiv_timelike` (local instances only); nothing global is changed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Nonlox

open Module Set Metric
open scoped Pointwise

variable {d : ℕ}

/-- A type synonym of `Minkowski d`, to carry the euclidean structure of `timelikeForm v`. -/
def EllTl (d : ℕ) : Type := Minkowski d

noncomputable instance : AddCommGroup (EllTl d) := inferInstanceAs (AddCommGroup (Minkowski d))
noncomputable instance : Module ℝ (EllTl d) := inferInstanceAs (Module ℝ (Minkowski d))

theorem timelikeForm_symm' (v x y : Minkowski d) : timelikeForm v x y = timelikeForm v y x := by
  show minkB x y + _ * (minkB v x * minkB v y) = minkB y x + _ * (minkB v y * minkB v x)
  rw [minkB_comm x y, mul_comm (minkB v x)]

theorem timelikeForm_pos' {v : Minkowski d} (hv : minkQ v < 0) {x : Minkowski d} (hx : x ≠ 0) :
    0 < timelikeForm v x x := by
  have hk : 0 < -minkQ v := by linarith
  have hq0 : minkQ v ≠ 0 := hv.ne
  show 0 < minkB x x + 2 / (-minkQ v) * (minkB v x * minkB v x)
  set a := minkB v x
  set z := x + (a / -minkQ v) • v
  have hz : minkB v z = 0 := by
    simp only [z, minkB_add_right, minkB_smul_right, ← minkQ_eq_minkB, a]; field_simp; ring
  have hxz : minkB x x = minkQ z - a ^ 2 / -minkQ v := by
    have : x = z + (-(a / -minkQ v)) • v := by simp [z]
    rw [this, ← minkQ_eq_minkB, minkQ_add, minkQ_smul, minkB_smul_right, minkB_comm, hz]
    field_simp; ring
  rw [hxz]
  have e : 2 / -minkQ v * (a * a) = 2 * (a ^ 2 / -minkQ v) := by ring
  rcases eq_or_ne z 0 with h0 | h0
  · have ha : a ≠ 0 := by
      intro ha; apply hx
      have : x = z + (-(a / -minkQ v)) • v := by simp [z]
      rw [this, h0, ha]; simp
    rw [h0, minkQ_zero]
    have : 0 < a ^ 2 / -minkQ v := div_pos (by positivity) hk
    rw [e]; linarith
  · have := minkQ_pos_of_orth_timelike hv hz h0
    have h2 : 0 ≤ a ^ 2 / -minkQ v := div_nonneg (sq_nonneg a) hk.le
    rw [e]; linarith

/-- A `minkQ`-preserving linear map fixing `v` preserves `timelikeForm v`. -/
theorem timelikeForm_map {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : ∀ w, minkQ (A w) = minkQ w)
    {v : Minkowski d} (hAv : A v = v) (x y : Minkowski d) :
    timelikeForm v (A x) (A y) = timelikeForm v x y := by
  show minkB (A x) (A y) + _ * (minkB v (A x) * minkB v (A y)) =
    minkB x y + _ * (minkB v x * minkB v y)
  conv_lhs => rw [← hAv]
  rw [minkB_map hA, minkB_map hA, minkB_map hA, hAv]

/-- **The euclidean structure fixed by the stabiliser of a timelike `v`**: a linear equivalence
`e : 𝐌ⁿ ≃ ℝⁿ` with `⟪e x, e y⟫ = ⟨x | y⟩ + (2/k)⟨v | x⟩⟨v | y⟩`, `k = −|v|²`. -/
theorem exists_euclEquiv_timelike {v : Minkowski d} (hv : minkQ v < 0) :
    ∃ e : Minkowski d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (d + 1)),
      ∀ x y, inner ℝ (e x) (e y) = timelikeForm v x y := by
  letI core : InnerProductSpace.Core ℝ (EllTl d) :=
    { inner := fun x y => timelikeForm v x y
      conj_inner_symm := fun x y => by
        simp only [starRingEnd_apply, star_trivial]; exact timelikeForm_symm' v y x
      re_inner_nonneg := fun x => by
        simp only [RCLike.re_to_real]
        rcases eq_or_ne (x : Minkowski d) 0 with h | h
        · exact le_of_eq (h ▸ LinearMap.map_zero₂ (timelikeForm v) (0 : Minkowski d)).symm
        · exact (timelikeForm_pos' hv h).le
      add_left := fun x y z => LinearMap.map_add₂ (timelikeForm v) (x : Minkowski d) y z
      smul_left := fun x y r => LinearMap.map_smul₂ (timelikeForm v) r (x : Minkowski d) y
      definite := fun x hx => by
        by_contra h
        exact (timelikeForm_pos' hv h).ne' hx }
  letI : NormedAddCommGroup (EllTl d) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (EllTl d) _ _ _ core
  letI : InnerProductSpace ℝ (EllTl d) := InnerProductSpace.ofCore core.toCore
  haveI : FiniteDimensional ℝ (EllTl d) :=
    inferInstanceAs (FiniteDimensional ℝ (Minkowski d))
  have hrank : finrank ℝ (EllTl d) = d + 1 := finrank_minkowski
  let b := (stdOrthonormalBasis ℝ (EllTl d)).reindex (finCongr hrank)
  let i : Minkowski d ≃ₗ[ℝ] EllTl d := LinearEquiv.refl ℝ (Minkowski d)
  refine ⟨i.trans b.repr.toLinearEquiv, fun x y => ?_⟩
  simp only [LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.inner_map_map]
  rfl

/-! ### Transport of the stabiliser of `v` to `Isom(ℝⁿ)` -/

section transport

variable {v : Minkowski d} (e : Minkowski d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  (he : ∀ x y, inner ℝ (e x) (e y) = timelikeForm v x y)

/-- `e ∘ g ∘ e⁻¹`, for `g` an isometry with `L(g) v = v`, as an isometry of `ℝⁿ`. -/
noncomputable def ellConj (g : isom d) (hg : linOf g v = v) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) where
  toAffineEquiv := (e.symm.toAffineEquiv.trans (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)).trans
    e.toAffineEquiv
  norm_map x := by
    have hA : ∀ w, minkQ (linOf g w) = minkQ w := lorentz.minkQ_apply (linOf_mem g)
    have key : inner ℝ (e (linOf g (e.symm x))) (e (linOf g (e.symm x))) = inner ℝ x x := by
      rw [he, timelikeForm_map hA hg, ← he, LinearEquiv.apply_symm_apply]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at key
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 key

include he in
theorem ellConj_apply (g : isom d) (hg : linOf g v = v) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ellConj e he g hg x = e (g • e.symm x) := rfl

theorem ellConj_linear (g : isom d) (hg : linOf g v = v) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    (ellConj e he g hg).linearIsometryEquiv x = e (linOf g (e.symm x)) := rfl

variable (H : Subgroup (isom d)) (hfix : ∀ γ ∈ H, linOf γ v = v)

/-- The transport `γ ↦ e ∘ γ ∘ e⁻¹`, a morphism `H → Isom(ℝⁿ)`. -/
noncomputable def ellHom :
    H →* (EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) where
  toFun γ := ellConj e he γ.1 (hfix _ γ.2)
  map_one' := by
    ext x
    rw [ellConj_apply]
    simp
  map_mul' a b := by
    ext x
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, ellConj_apply, ellConj_apply,
      ellConj_apply, LinearEquiv.symm_apply_apply]
    simp [mul_smul]

theorem ellHom_apply (γ : H) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ellHom e he H hfix γ x = e (γ.1 • e.symm x) := rfl

end transport

/-! ### Discreteness of the transported group -/

theorem isDiscreteEucl_ellHom_range {v : Minkowski d}
    (e : Minkowski d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (he : ∀ x y, inner ℝ (e x) (e y) = timelikeForm v x y) {H : Subgroup (isom d)}
    (hfix : ∀ γ ∈ H, linOf γ v = v)
    (hprop : ∀ K : Set (Minkowski d), IsCompact K →
      {γ : isom d | γ ∈ H ∧ (γ • K ∩ K).Nonempty}.Finite) :
    IsDiscreteEucl (ellHom e he H hfix).range := by
  rw [isDiscreteEucl_iff_exists]
  refine ⟨0, fun R => ?_⟩
  set K : Set (Minkowski d) := e.symm '' closedBall 0 R with hKdef
  have hcont : Continuous e.symm := e.symm.toContinuousLinearEquiv.continuous
  have hK : IsCompact K := (isCompact_closedBall 0 R).image hcont
  set S' : Set H := {γ | (γ.1 • K ∩ K).Nonempty}
  have hS' : S'.Finite := by
    refine ((hprop K hK).subset ?_).of_finite_image Subtype.val_injective.injOn
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨γ.2, hγ⟩
  refine (hS'.image (ellHom e he H hfix)).subset ?_
  rintro g ⟨hg, hd⟩
  obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hg
  refine ⟨γ, ?_, rfl⟩
  have hR : 0 ≤ R := dist_nonneg.trans hd
  have h0K : (0 : Minkowski d) ∈ K := ⟨0, mem_closedBall_self hR, map_zero _⟩
  refine ⟨γ.1 • (0 : Minkowski d), Set.smul_mem_smul_set h0K, ?_⟩
  refine ⟨ellHom e he H hfix γ 0, ?_, ?_⟩
  · rwa [mem_closedBall]
  · rw [ellHom_apply, LinearEquiv.symm_apply_apply, map_zero]

/-! ### The pulled-back translation subspace -/

/-- **[9.E], the Bieberbach step** (l.2606, l.2611–2615): a group `H` of isometries whose linear
parts fix a timelike `v` and which acts properly on `𝐌ⁿ` has a finite-index subgroup `H'` acting
by translations on an affine subspace `U` whose direction contains `v` (so `U` is timelike), the
translation vectors forming an additive subgroup `Λ` of `U`'s direction. -/
theorem exists_translationSubspace_of_fix_timelike
    (hBieb : BieberbachI (EuclideanSpace ℝ (Fin (d + 1)))) {H : Subgroup (isom d)}
    {v : Minkowski d} (hv : minkQ v < 0) (hfix : ∀ γ ∈ H, linOf γ v = v)
    (hprop : ∀ K : Set (Minkowski d), IsCompact K →
      {γ : isom d | γ ∈ H ∧ (γ • K ∩ K).Nonempty}.Finite) :
    ∃ H' : Subgroup (isom d), H' ≤ H ∧ H'.relIndex H ≠ 0 ∧
      ∃ U : AffineSubspace ℝ (Minkowski d), (U : Set (Minkowski d)).Nonempty ∧ v ∈ U.direction ∧
        ∃ Λ : AddSubgroup (Minkowski d), (Λ : Set (Minkowski d)) ⊆ (U.direction : Set _) ∧
          (∀ γ ∈ H', ∃ τ ∈ Λ, ∀ p ∈ U, γ • p = p + τ) ∧
          (∀ τ ∈ Λ, ∃ γ ∈ H', ∀ p ∈ U, γ • p = p + τ) := by
  obtain ⟨e, he⟩ := exists_euclEquiv_timelike hv
  set τ := ellHom e he H hfix
  obtain ⟨Γ', hle, -, hfi, Uₑ, hUne, -, htr, -, hmax⟩ :=
    bieberbachMaxConclusion_of_bieberbachI hBieb (isDiscreteEucl_ellHom_range e he hfix hprop)
  have hev : e v ∈ Uₑ.direction := by
    refine mem_direction_of_fixed hUne htr hmax fun g hg => ?_
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 (hle hg)
    show e (linOf γ.1 (e.symm (e v))) = e v
    rw [LinearEquiv.symm_apply_apply, hfix _ γ.2]
  set H' : Subgroup (isom d) := (Γ'.comap τ).map H.subtype with hH'
  set f : EuclideanSpace ℝ (Fin (d + 1)) →ᵃ[ℝ] Minkowski d :=
    (e.symm : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] Minkowski d).toAffineMap with hf
  set U : AffineSubspace ℝ (Minkowski d) := Uₑ.map f with hU
  have hUdir : U.direction = Uₑ.direction.map
      (e.symm : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] Minkowski d) := by
    rw [hU, AffineSubspace.map_direction, hf, LinearMap.toAffineMap_linear]
  have hmemU : ∀ p, p ∈ U ↔ e p ∈ Uₑ := by
    intro p
    rw [hU, AffineSubspace.mem_map]
    refine ⟨?_, fun h => ⟨e p, h, by simp [hf]⟩⟩
    rintro ⟨y, hy, rfl⟩
    simpa [hf] using hy
  have hmemD : ∀ w, w ∈ U.direction ↔ e w ∈ Uₑ.direction := by
    intro w
    rw [hUdir, Submodule.mem_map]
    refine ⟨?_, fun h => ⟨e w, h, by simp⟩⟩
    rintro ⟨y, hy, rfl⟩
    simpa using hy
  -- every element of `H'` translates `U` by a vector of its direction
  have hact : ∀ γ ∈ H', ∃ w ∈ U.direction, ∀ p ∈ U, γ • p = p + w := by
    intro γ hγ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hγ
    obtain ⟨w, hw, hwx⟩ := htr (τ x) hx
    refine ⟨e.symm w, (hmemD _).2 (by simpa using hw), fun p hp => ?_⟩
    have h1 := hwx (e p) ((hmemU p).1 hp)
    rw [show τ x (e p) = e (x.1 • e.symm (e p)) from rfl, LinearEquiv.symm_apply_apply,
      vadd_eq_add] at h1
    have h2 := congrArg e.symm h1
    rw [LinearEquiv.symm_apply_apply, map_add, LinearEquiv.symm_apply_apply] at h2
    exact h2.trans (add_comm _ _)
  obtain ⟨p₀, hp₀⟩ := hUne
  have hp₀' : e.symm p₀ ∈ U := (hmemU _).2 (by simpa using hp₀)
  have hsub : ∀ τ' γ, γ ∈ H' → (∀ p ∈ U, γ • p = p + τ') → τ' ∈ U.direction := by
    intro τ' γ hγ hτ'
    obtain ⟨w, hw, hwp⟩ := hact γ hγ
    have := (hτ' _ hp₀').symm.trans (hwp _ hp₀')
    rw [add_left_cancel_iff.1 this]
    exact hw
  let Λ : AddSubgroup (Minkowski d) :=
    { carrier := {τ' | ∃ γ ∈ H', ∀ p ∈ U, γ • p = p + τ'}
      zero_mem' := ⟨1, H'.one_mem, fun p _ => by simp⟩
      add_mem' := by
        rintro a b ⟨γa, hγa, ha⟩ ⟨γb, hγb, hb⟩
        refine ⟨γa * γb, H'.mul_mem hγa hγb, fun p hp => ?_⟩
        have hbU : p + b ∈ U := by
          have := AffineSubspace.vadd_mem_of_mem_direction (hsub b γb hγb hb) hp
          rwa [vadd_eq_add, add_comm] at this
        rw [mul_smul, hb p hp, ha _ hbU, add_assoc, add_comm b a]
      neg_mem' := by
        rintro a ⟨γ, hγ, ha⟩
        refine ⟨γ⁻¹, H'.inv_mem hγ, fun p hp => ?_⟩
        have hq : p + -a ∈ U := by
          have := AffineSubspace.vadd_mem_of_mem_direction
            (U.direction.neg_mem (hsub a γ hγ ha)) hp
          rwa [vadd_eq_add, add_comm] at this
        have := ha _ hq
        rw [neg_add_cancel_right] at this
        rw [inv_smul_eq_iff]
        exact this.symm }
  refine ⟨H', Subgroup.map_subtype_le _, ?_, U, ⟨_, hp₀'⟩, (hmemD v).2 hev, Λ,
    fun τ' ⟨γ, hγ, h⟩ => hsub τ' γ hγ h, fun γ hγ => ?_, fun τ' hτ' => hτ'⟩
  · show (((Γ'.comap τ).map H.subtype).comap H.subtype).index ≠ 0
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective, Subgroup.index_comap]
    exact hfi.index_ne_zero
  · obtain ⟨w, -, hw⟩ := hact γ hγ
    exact ⟨w, ⟨γ, hγ, hw⟩, hw⟩

end Causal.Flat.Nonlox
