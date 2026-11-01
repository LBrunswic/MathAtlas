import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Nonlox.UnipotentUpToFrame

/-!
# `CausalScaffold.Flat.Lox.MisnerRestrict` — [10.M]: the restriction to `U` is a Misner group

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
subsection "The elementary case", `papers/barbot/legacy/labeled/GHFspace.tex` l.3327–3330, and
[3.M] (l.597–629). **No label is marked**: [10.M] is prose; this file is one step of
`loxo_elementary_misner` (`Flat/Loxodromic.lean`, item (5) of its obstruction). Barbot's `𝐌ⁿ` is
`Minkowski (d + 1)` here (kb/0024); the Misner base is `Minkowski (d₁ + 1)`, `d₁ ≤ d`.

> Once more, an appropriate use of Bieberbach's theorem
> leads to the conclusion:
> the quotient space $M(S) = \Gamma\backslash\Omega(\widetilde{S})$
> is a linear twisted product over a Misner spacetime. (l.3327–3330)

`misner_restrict`: let every `γ ∈ Γ'` act on `U = φ(ℝ² × (z₀ + J(ℝ^{d₁})))` by
`φ (ofNull x y (z₀ + J w)) ↦ φ (ofNull (eᵃ x) (e⁻ᵃ y) (z₀ + J (w + v)))`, one of them with
`a ≠ 0`, and let `Γ'` act properly on an `Ω` containing a tube `{φ (ofNull (eᵇ x₀) (e⁻ᵇ y₀) z)}`.
Then the orthochronous isometric embedding `ι (ofNull x y w) = φ (ofNull x y (z₀ + J w))` of
`𝐌^{d₁+2}` restricts `Γ'`, and `Γ'_U = misnerGroup L` for a ball-finite `L ≤ ℝ × ℝ^{d₁}` with an
element of nonzero boost parameter (finding F1).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ'` acts by translations on `W` (the Bieberbach step, l.3327) | ✓ carried (`htr`; proved upstream, `Lox.misner_bieberbach`) |
| `γ₀` loxodromic (`a(γ₀) ≠ 0`) | ✓ carried (`hboost`; finding F1 needs it in the Misner family) |
| the action is properly discontinuous (l.3326–3327) | ✓ carried as properness on `Ω ⊇` tube (`hprop`, `htube`) |

## SCOPE (disclosed)

* `L` is `{(a, v) | misnerMap (a, v) ∈ Γ'_U}`; the frame of `IsMisnerSpacetime` is absorbed in
  `ι` (the consumer uses `φ = 1` there).
* **Proved, no `sorry`.** `ι = φ ∘ Nonlox.uftIota J z₀ 0` (private `mr_iota`); each `γ ∈ Γ'`
  restricts to `misnerMap (a, v)` for the `(a, v)` of `htr` (`mr_restricts`), so
  `Γ'_U = misnerGroup L`; ball-finiteness of `L` comes from `hprop` on the compact image of
  `[−R, R] × B̄(0, R)` in the tube, `misnerMap` being injective (`mr_misnerMap_injective`) and
  `(a, v)` determined by `γ` (`Restricts.unique`). Barbot's Bieberbach step (l.3327) is the
  hypothesis `htr`, proved upstream; no `IsMisnerSpacetime` frame is built here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Lox

open Causal.Flat Set
open scoped Pointwise

/-! ### Private helpers -/

/-- `ι = φ ∘ uftIota J z₀ 0`, an isometric affine embedding `𝐌^{d₁+2} → 𝐌^{d+2}`. -/
private noncomputable def mr_iota {d d₁ : ℕ} (φ : isom (d + 1))
    (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) : AffineMinkEmbedding (d₁ + 1) (d + 1) where
  toAffineMap := (φ : Minkowski (d + 1) ≃ᵃ[ℝ] Minkowski (d + 1)).toAffineMap.comp
    (Nonlox.uftIota J z₀ 0).toAffineMap
  minkQ_linear v := by
    show minkQ ((φ : Minkowski (d + 1) ≃ᵃ[ℝ] Minkowski (d + 1)).linear
      ((Nonlox.uftIota J z₀ 0).toAffineMap.linear v)) = minkQ v
    exact (lorentz.minkQ_apply φ.2 _).trans ((Nonlox.uftIota J z₀ 0).minkQ_linear v)

private theorem mr_iota_apply {d d₁ : ℕ} (φ : isom (d + 1))
    (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) (x y : ℝ) (w : EuclideanSpace ℝ (Fin d₁)) :
    mr_iota φ J z₀ (ofNull x y w) = φ • ofNull x y (z₀ + J w) := by
  show φ • (Nonlox.uftIota J z₀ 0 (ofNull x y w)) = _
  rw [Nonlox.uftIota_apply, add_zero]

private theorem mr_iota_orthochronous {d d₁ : ℕ} (φ : isom (d + 1))
    (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) : (mr_iota φ J z₀).Orthochronous := by
  have h1 : IsFutureTimelike ((Nonlox.uftIota J z₀ 0).lin (1, 0)) :=
    ⟨Nonlox.uftIota_orthochronous J z₀ 0, by
      rw [(Nonlox.uftIota J z₀ 0).minkQ_lin_timeVec]; norm_num⟩
  exact (lorentz.isFutureTimelike_apply φ.2 h1).1

private theorem mr_misner_ofNull {d : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin d)) (x y : ℝ)
    (w : EuclideanSpace ℝ (Fin d)) :
    misnerMap (a, v) • ofNull x y w = ofNull (Real.exp a * x) (Real.exp (-a) * y) (v + w) :=
  eq_of_null (by rw [nullX_misner, nullX_ofNull, nullX_ofNull])
    (by rw [nullY_misner, nullY_ofNull, nullY_ofNull])
    fun i => by rw [nullZ_misner, nullZ_ofNull, nullZ_ofNull]

private theorem mr_restricts {d d₁ : ℕ} (φ : isom (d + 1))
    (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d)) {γ : isom (d + 1)} {a : ℝ} {v : EuclideanSpace ℝ (Fin d₁)}
    (h : ∀ (x y : ℝ) (w : EuclideanSpace ℝ (Fin d₁)),
      γ • (φ • ofNull x y (z₀ + J w)) =
        φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (z₀ + J (w + v))) :
    (mr_iota φ J z₀).Restricts γ (misnerMap (a, v)) := by
  intro p
  rw [← Nonlox.nsl_ofNull_null p, mr_misner_ofNull, mr_iota_apply, mr_iota_apply, h, add_comm v]

private theorem mr_misnerMap_injective {d : ℕ} {x x' : ℝ × EuclideanSpace ℝ (Fin d)}
    (h : misnerMap x = misnerMap x') : x = x' := by
  have hp := congrArg (fun g : isom (d + 1) => g • ofNull (1 : ℝ) 0 (0 : EuclideanSpace ℝ (Fin d))) h
  have hX := congrArg nullX hp
  have hZ := congrArg nullZ hp
  rw [nullX_misner, nullX_misner, nullX_ofNull, mul_one, mul_one] at hX
  rw [nullZ_misner, nullZ_misner, nullZ_ofNull, add_zero, add_zero] at hZ
  exact Prod.ext (Real.exp_injective hX) hZ

/-- **[10.M] l.3327–3330: `Γ'_U` is a Misner group.** For `Γ'` acting by Misner maps on
`φ(ℝ² × (z₀ + J(ℝ^{d₁})))` and properly on a tube: the embedding
`ι (ofNull x y w) = φ (ofNull x y (z₀ + J w))` is orthochronous, restricts `Γ'`, and
`ι.restrictGroup Γ' = misnerGroup L`, `L` ball-finite with an element of nonzero boost. -/
theorem misner_restrict {d d₁ : ℕ} {Γ' : Subgroup (isom (d + 1))} (φ : isom (d + 1))
    (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z₀ : EuclideanSpace ℝ (Fin d))
    (htr : ∀ γ ∈ Γ', ∃ (a : ℝ) (v : EuclideanSpace ℝ (Fin d₁)),
      ∀ (x y : ℝ) (w : EuclideanSpace ℝ (Fin d₁)),
        γ • (φ • ofNull x y (z₀ + J w)) =
          φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (z₀ + J (w + v)))
    (hboost : ∃ γ ∈ Γ', ∃ a : ℝ, a ≠ 0 ∧ ∃ v : EuclideanSpace ℝ (Fin d₁),
      ∀ (x y : ℝ) (w : EuclideanSpace ℝ (Fin d₁)),
        γ • (φ • ofNull x y (z₀ + J w)) =
          φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (z₀ + J (w + v)))
    {Ω : Set (Minkowski (d + 1))}
    (hprop : ∀ K ⊆ Ω, IsCompact K →
      {γ : isom (d + 1) | γ ∈ Γ' ∧ (γ • K ∩ K).Nonempty}.Finite)
    {x₀ y₀ : ℝ}
    (htube : ∀ (b : ℝ) (z : EuclideanSpace ℝ (Fin d)),
      φ • ofNull (Real.exp b * x₀) (Real.exp (-b) * y₀) z ∈ Ω) :
    ∃ (ι : AffineMinkEmbedding (d₁ + 1) (d + 1))
      (L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin d₁))),
      (∀ (x y : ℝ) (w : EuclideanSpace ℝ (Fin d₁)), ι (ofNull x y w) = φ • ofNull x y (z₀ + J w)) ∧
      ι.Orthochronous ∧ ι.RestrictsIn Γ' ∧ ι.restrictGroup Γ' = misnerGroup L ∧
      BallFinite L ∧ ∃ x ∈ L, x.1 ≠ 0 := by
  classical
  set ι := mr_iota φ J z₀ with hι
  -- (3) the subgroup `L`
  let L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin d₁)) :=
    { carrier := {x | misnerMap x ∈ ι.restrictGroup Γ'}
      zero_mem' := by
        show misnerMap (0 : ℝ × EuclideanSpace ℝ (Fin d₁)) ∈ ι.restrictGroup Γ'
        rw [misnerMap_zero]; exact (ι.restrictGroup Γ').one_mem
      add_mem' := by
        intro x x' hx hx'
        show misnerMap (x + x') ∈ ι.restrictGroup Γ'
        rw [misnerMap_add]; exact (ι.restrictGroup Γ').mul_mem hx hx'
      neg_mem' := by
        intro x hx
        show misnerMap (-x) ∈ ι.restrictGroup Γ'
        have e : misnerMap (-x) = (misnerMap x)⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rw [← misnerMap_add, neg_add_cancel, misnerMap_zero])
        rw [e]; exact (ι.restrictGroup Γ').inv_mem hx }
  have hmemL : ∀ x, x ∈ L ↔ misnerMap x ∈ ι.restrictGroup Γ' := fun _ => Iff.rfl
  -- (2) every `γ ∈ Γ'` restricts as a Misner map
  have hres : ∀ γ ∈ Γ', ∃ x : ℝ × EuclideanSpace ℝ (Fin d₁), ι.Restricts γ (misnerMap x) := by
    intro γ hγ
    obtain ⟨a, v, h⟩ := htr γ hγ
    exact ⟨(a, v), mr_restricts φ J z₀ h⟩
  have hRG : ι.restrictGroup Γ' = misnerGroup L := by
    ext g
    rw [mem_misnerGroup]
    constructor
    · intro hg
      obtain ⟨γ, hγ, hr⟩ := hg
      obtain ⟨x, hx⟩ := hres γ hγ
      have e := hx.unique hr
      exact ⟨x, by rw [hmemL, e]; exact ⟨γ, hγ, hr⟩, e⟩
    · rintro ⟨x, hx, rfl⟩; exact hx
  refine ⟨ι, L, mr_iota_apply φ J z₀, mr_iota_orthochronous φ J z₀,
    fun γ hγ => let ⟨_, h⟩ := hres γ hγ; ⟨_, h⟩, hRG, ⟨fun R => ?_⟩, ?_⟩
  · -- (4) ball-finiteness
    by_cases hR : R < 0
    · convert Set.finite_empty
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      exact fun _ => lt_of_lt_of_le hR (norm_nonneg x)
    replace hR := not_lt.1 hR
    let f : ℝ × EuclideanSpace ℝ (Fin d₁) → Minkowski (d + 1) := fun q =>
      φ • ofNull (Real.exp q.1 * x₀) (Real.exp (-q.1) * y₀) (z₀ + J q.2)
    have hf : Continuous f := by
      refine (continuous_const_smul φ).comp ?_
      have hc : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin d₁) =>
          ((Real.exp q.1 * x₀, z₀ + J q.2, Real.exp (-q.1) * y₀) :
            ℝ × EuclideanSpace ℝ (Fin d) × ℝ)) := by
        have hJ : Continuous (J : EuclideanSpace ℝ (Fin d₁) → EuclideanSpace ℝ (Fin d)) :=
          J.continuous
        fun_prop
      exact (Nonlox.nsl_continuous_ofNull (d := d)).comp hc
    set K := f '' (Icc (-R) R ×ˢ Metric.closedBall 0 R) with hK
    have hKc : IsCompact K := (isCompact_Icc.prod (isCompact_closedBall _ _)).image hf
    have hKΩ : K ⊆ Ω := by rintro _ ⟨q, -, rfl⟩; exact htube _ _
    have hF := hprop K hKΩ hKc
    -- the Misner parameter recovered from `γ`
    let g : isom (d + 1) → ℝ × EuclideanSpace ℝ (Fin d₁) := fun γ =>
      if h : ∃ x : ℝ × EuclideanSpace ℝ (Fin d₁), ι.Restricts γ (misnerMap x) then h.choose
      else 0
    refine (hF.image g).subset ?_
    rintro x ⟨hxL, hxR⟩
    obtain ⟨γ, hγ, hr⟩ := (hmemL x).1 hxL
    have hex : ∃ x : ℝ × EuclideanSpace ℝ (Fin d₁), ι.Restricts γ (misnerMap x) := ⟨x, hr⟩
    have hgx : g γ = x := by
      simp only [g, dif_pos hex]
      exact mr_misnerMap_injective (hex.choose_spec.unique hr)
    refine ⟨γ, ⟨hγ, ?_⟩, hgx⟩
    have h1 : |x.1| ≤ R := (Real.norm_eq_abs x.1).symm ▸ (norm_fst_le x).trans hxR
    have h2 : ‖x.2‖ ≤ R := (norm_snd_le x).trans hxR
    have hp₀ : ι (ofNull x₀ y₀ 0) ∈ K := by
      refine ⟨(0, 0), ⟨⟨by linarith, hR⟩, Metric.mem_closedBall_self hR⟩, ?_⟩
      simp only [f, Real.exp_zero, neg_zero, one_mul, map_zero]
      rw [mr_iota_apply, map_zero]
    refine ⟨γ • ι (ofNull x₀ y₀ 0), Set.smul_mem_smul_set hp₀, ?_⟩
    rw [← hr, mr_misner_ofNull, mr_iota_apply, add_zero]
    exact ⟨x, ⟨abs_le.1 h1, mem_closedBall_zero_iff.2 h2⟩, rfl⟩
  · -- (5) the boost
    obtain ⟨γ, hγ, a, ha, v, h⟩ := hboost
    exact ⟨(a, v), (hmemL _).2 ⟨γ, hγ, mr_restricts φ J z₀ h⟩, ha⟩

end Causal.Flat.Lox
