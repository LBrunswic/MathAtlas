import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.CauchyComplete

/-!
# `CausalScaffold.Flat.Loxodromic` — Barbot §10, the loxodromic case

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10
"The loxodromic case" (`loxocase`), `GHFspace.tex` l.3133–3456 of the labelled file
`papers/barbot/legacy/labeled/GHFspace.tex`. **No label is marked**; each is partial (SCOPE).

* `blem:sanlox` — `GHFspace.tex:3141` (Lemma 10.1), partial: the inclusion `Ω(Γ) ⊆ Ω_lox(Γ)`
  (`omegaGamma_subset_omegaLox`) and the corrected core (`subset_UGamma_of_oneSided`,
  `omegaPlus_limitSetJ_subset_omegaGamma`, `…Minus…`) proved; the printed `blem_sanlox` is a
  `sorry` (its proof needs `Ω_lox(Γ)` convex, which fails).
* `blem:loxregular` — `GHFspace.tex:3170` (Lemma 10.2), partial (reading: §8's standing hypotheses
  `CCAction`; **no `sorry`**): `blem_loxregular`, `loxregular_sign`, `omegaS_eq_interior`; the
  "reader can easily check" (l.3191–3193) is `exists_line_avoiding`.
* `bcor:loxo_proper` — `GHFspace.tex:3214` (Cor 10.3), partial: freeness and the quotient
  (`bcor_loxo_proper`: GH, acausal Cauchy surface) proved; proper discontinuity
  (`loxo_properlyDiscontinuous`) and Cauchy-completeness (`loxo_cauchyComplete`) are `sorry`.
* `bprop:U_timelike` — `GHFspace.tex:3347` (Prop 10.4), partial: the lightlike case
  (`not_isNonelementary_of_lightlike`) proved, the spacelike case a `sorry` (Cor 8.4).
* `bprop:LU_discrete` — `GHFspace.tex:3368` (Prop 10.5), stated (`bprop_LU_discrete`, `sorry`).
* `bprop:admlox` — `GHFspace.tex:1230` (Prop 4.17), partial (nonempty added, external
  `LimitSetMinimal`; **no `sorry`**): invariance in `𝒥` (`isomPenrose_image_limitSetJ_subset`),
  minimality on `𝒮` (`fst_image_limitSetJ_subset`) and in `𝒥` (`limitSetJ_subset`, through the
  basin of repulsion `tendsto_isomPenrose_inv_pow`).
* `bdef:definitioncauchyhyp` — `GHFspace.tex:1277` (Def 4.18), partial (readings):
  `IsCauchyHyperbolic`, `IsFutureAdmissible`, `IsPastAdmissible`, `IsAdmissible`.
* Prose: [10.M] l.3235–3330 (`loxo_elementary_misner`, for a finite-index `Γ'`, `sorry`); [10.G] l.3333–3456
  (`generic_omegaS_eq`, `kerTranslations_spacelike`, `kerTranslations_ballFinite`,
  `linOf_mem_kerTranslations`, `omegaS_add_mem_span`, `span_kerTranslations_spacelike` proved;
  the conclusion `loxo_generic_centralExtension`, family (b), and `loxo_generic_torusProduct`,
  family (a) under `π₁` finitely generated through Selberg, are `sorry`).
* gx exports (the contract of `docs/BARBOT.md`): `uniformization_injective`,
  `uniformization_image`, `uniformization_properlyDiscontinuous`, and `uniformization`.

> If $\Gamma$ contains loxodromic elements, $\Omega_{lox}(\Gamma) = \Omega(\Gamma)$. (l.3143–3144)

> $\Omega(\widetilde{S})$ is a regular convex domain. (l.3172)

> The action of $\Gamma$ on $\Omega(\widetilde{S})$ is free and properly discontinuous, and the
> quotient space $M(S) = \Gamma \backslash \Omega(\widetilde{S})$ is a Cauchy-complete globally
> hyperbolic spacetime. (l.3215–3218)

> ${\bf U}$ is timelike. (l.3348) — $L_{U}(\Gamma)$ is discrete. (l.3369)

> But the reader can easily check that in all cases, there is always a timelike line avoiding the
> intersection $U^{+}(\gamma_{0}) \cap U^{-}(\gamma_{1})$. (l.3191–3193)

> $L$ might be noninjective! Let $\mathcal N$ be its kernel: its elements are translations, and the
> translation vectors form a lattice in some spacelike linear space $E$. (l.3406–3409)

> \emph{Conclusion:\/} $M(S) = \Gamma\backslash\Omega(\widetilde{S})$ is a twisted product of a
> Cauchy-hyperbolic spacetime by a flat torus. (l.3454–3456)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1` (the Misner branch works in `Minkowski (d' + 1)`).

## Main declarations

* `IsRepulsiveFixedJ γ w` (the repulsive fixed point in `𝒥 ≅ 𝒮 × ℝ` of a loxodromic `γ`: an
  eigenvector `(1,u)` for `λ < 1` and a `γ`-invariant hyperplane, `⟨(1,u)|γp⟩ − s = λ⁻¹(⟨(1,u)|p⟩ − s)`),
  `exists_isRepulsiveFixedJ`, `IsRepulsiveFixedJ.fst_ne`, `.conj`, `eigen_of_funEq`;
  `loxRepSet Γ` (Barbot's `Λ₀`), `limitSetJ Γ` (`Λ(Γ)`, its closure).
* [7.L] in `𝒥`: `quadrants_subset_achronalDomain`, **`interior_achronalDomain_eq_quadrants`**
  (`Int Ω_γ = U⁺(γ) ⊔ U⁻(γ)`, `U^±(γ) = P^±(w) ∩ P^±(w')`, `w`, `w'` the repulsive points of `γ`,
  `γ⁻¹`).
* Classes: `Ug_eq_achronalDomain_of_isLoxodromic`, `achronalDomain_eq_univ_of_isSpacelikeElliptic`,
  `…_of_isTangentParabolic`, the linear parabolic orbit `linearParabolic_orbit_fwd`/`_bwd`,
  `subset_compl_nullHyperplanes_of_oneSided`.
* The regular domains: `smul_mem_omegaPlus_limitSetJ` (and `Minus`), `preservesOmega_limitSetJ`,
  `exists_two_loxRepSet`, `cosmoRegular_limitSetJ`, `limitOpensPlus`/`Minus`.
* Cor 10.3: `ActsFreelyProperlyOn`, `isCancelSMul_of_free`, `properlyDiscontinuousSMul_of_finite`,
  `loxo_free`. Families: `IsNonelementary`, `IsFutureAdmissible`, `IsPastAdmissible`, `IsAdmissible`,
  `IsCauchyHyperbolic`, `kerTranslations`, `IsSpacelikeSubmodule`, `IsCHCentralExtensionOf`,
  `IsCHCentralExtension` (b), `IsCHTorusProduct` (a, for the same `Γ`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| §8's setting: `S` complete, `Γ = π₁(S)` acting on `S̃` | ⚠ strengthened (DEC-35 reading, as `Flat.Develop`): `CCAction Γ Σ` in `𝐌ⁿ`; on `M` through `DevelopsCC`, `ccAction_of_developsCC` |
| `Γ` contains a loxodromic element (l.3135) | ✓ carried (`hlox`) |
| Rem 8.9: no nonspacelike elliptic, no transverse parabolic (used in 10.1) | ✓ derived from `CCAction` (`nini`) |
| 10.2: "up to time reversing isometries" (l.3181–3183) | ⚠ reading: both cases kept (`isom d` is `SO₀`-affine); `Ω⁺` or `Ω⁻` |
| 10.2: 4.6, 4.8, 4.9 | ✓ through `omegaPlus_closure_eq_interior` (4.9 with no hypothesis) |
| 10.3: `bprop:agissons` (Γ discrete) | not available: properness is a `sorry`; the quotient statement takes it from there |
| 10.3: "`M(S)` is a Cauchy-complete GH spacetime" | ⚠ future case only (`bcor_loxo_proper` under `Ω(S̃) = Ω⁺(Λ)`; the past case is its time reversal, not formalized); Cauchy-completeness split off as `loxo_cauchyComplete`, which takes the quotient instances as hypotheses |
| gx uniformization: nonelementary, `ker L = 1` | ⚠ weakened: neither is used; only a loxodromic element |
| 10.4: `bthm:ausl`, `bthm:unip`, discreteness, nonelementary | ✓ carried (`AuslanderCarriereDalbo`, `MaxUnipotentSubspace`, `DiscreteTopology Γ`) |
| 10.4: `U` nonempty and `Γ`-invariant ("being unique", l.3343–3344) | ✓ derived (`exists_invariant_maxUnipotent` and the uniqueness of `MaxUnipotentSubspace`) |
| [10.M]: "up to finite index" `L(Γ)` fixes `Δ₀` (l.3236–3238) | ⚠ conclusion for a finite-index `Γ' ≤ Γ` (DEC-43's R1): the paper's conclusion for `Γ` itself (l.3326–3330) is false (finding) |
| Def 4.18 / family (b): `L(Γ)` without global fixed point (l.1212–1214) | ⚠ reading: Def 4.18's condition, weaker than `docs/BARBOT-THEOREMS.md` §1's "discrete nonelementary" (an infinite dihedral group with a loxodromic is elementary and has none) |
| Def 4.18: `Ω^±(Λ(ρ))` | ⚠ reading: sign tied to the side of admissibility (`IsFutureAdmissible` ↦ `Ω⁺`, `IsPastAdmissible` ↦ `Ω⁻`) |
| [10.G]: Selberg (DEC-44) for family (a) | ✓ carried (`SelbergLemma`, `ρ.range.FG`) |

## SCOPE (disclosed)

* **Sorries (8)**: `blem_sanlox` (printed form), `loxo_properlyDiscontinuous`, `loxo_cauchyComplete`,
  `loxo_elementary_misner` ([10.M]), `bprop_U_timelike` (spacelike case), `bprop_LU_discrete`,
  `loxo_generic_centralExtension`, `loxo_generic_torusProduct` ([10.G]). Each names its
  obstruction. `blem_loxregular`, `interior_achronalDomain_eq_quadrants`,
  `subset_UGamma_of_oneSided`, the proved [10.G] lemmas and all of `bprop:admlox`
  (`isomPenrose_image_limitSetJ_subset`, `fst_image_limitSetJ_subset`, `limitSetJ_subset`) use no
  `sorry`.
* **Upstream.** Through `ccAction_of_developsCC` and `bprop_danom`, the gx exports inherit
  `Flat.Develop`'s two `sorry`s (`holonomy_proper`; Prop 8.12 step 1); `uniformization_*` add
  Cor 10.3's properness. Under a given `CCAction` (in `𝐌ⁿ`) Lemma 10.2 is sorry-free.
* **Readings.** `Λ₀` is the set of all repulsive fixed points (`IsRepulsiveFixedJ`), not one per
  element; `U^±(γ)` are the two quadrants of `interior_achronalDomain_eq_quadrants`, whatever
  repulsive points are chosen; "nonelementary" is `IsNonelementary` (no finite-index subgroup of
  `L(Γ)` fixing a point of `𝒮`); "admissible" asks `L(Γ)` discrete (Externals' `lorentzTopology`)
  without global fixed point (Def 4.18, l.1212–1214 — weaker than BARBOT-THEOREMS §1's
  "nonelementary"; family (b) uses the same condition), future or past (`IsFutureAdmissible`,
  `IsPastAdmissible`), and Cauchy-hyperbolic takes `Ω⁺` for a future, `Ω⁻` for a past admissible
  group. Family (a) is (b) with `L(Γ)` torsion-free for the same `Γ` (BARBOT-THEOREMS §1), the
  bundle description not written. The Misner and generic conclusions are both stated in DEC-43's
  R1 form: the quotient by a finite-index `Γ' ≤ Γ` is an LTP over the model (for [10.M] the
  statement for `Γ` itself is false: finding below).
* **Cor 10.3's quotient** is stated in the future case only (the past one is its time reversal);
  `Flat.Examples` has the GH theory of `Γ\Ω⁺(Λ)` only.

## Findings (DEC-27)

* **`blem:sanlox`'s proof (l.3157–3165) treats `Ω_lox(Γ)` as convex; it is not** — for `Γ = ⟨γ⟩` it
  is the disjoint union `U⁺(γ) ⊔ U⁻(γ)`. The argument is correct for each `Γ`-invariant convex
  piece on which two null directions are one-sided, which covers `Ω^±(Λ(Γ))` and hence every use
  in §10; whether the printed equality holds on mixed-sign components is open.
* **The "convex hull of the orbit is a complete lightlike line" (l.3159–3163)** is replaced by an
  exact growth argument: along the orbit `⟨n|γᵏx⟩ = ⟨n|c⟩ + ⟨n|Rᵏy⟩ + k⟨n|p(y)⟩`, and `x` must first be
  moved off `ker p` inside the open set (a point of `P(γ₀) ∩ ker p` has a bounded orbit).
* **l.3191–3193 ("easily check") is easy, and is filled** (`exists_line_avoiding`).
* **[10.G] l.3409: "the translation vectors form a lattice in some spacelike linear space `E`" is not
  implied by the vectors being spacelike** (`ℤ(0,0,1) + ℤ(1,1,√2)` in `𝐌³` consists of spacelike
  vectors and spans a degenerate plane); it holds here because `Ω(S̃) = Ω^±(Λ(Γ))` is `E`-invariant
  and `Λ(Γ)` has two null directions (`span_kerTranslations_spacelike`).
* **[10.M]'s conclusion for `Γ` itself (l.3326–3330) is false; it holds up to finite index.** In `𝐌⁴`
  (form `xy + |z|²`, coordinates `(x, z₁, z₂, y)`), `γ₀(x,z,y) = (e⁻¹x, z, e y)` and the glide
  `σ(x,z₁,z₂,y) = (−y, z₁+1, −z₂, −x)` (in `SO₀`, spacelike elliptic, allowed by Rem 8.9) satisfy
  `σγ₀σ⁻¹ = γ₀⁻¹`; `Γ = ⟨γ₀, σ⟩` acts freely and properly on `Ω = {x > 0, y < 0} × ℝ²` and
  `Σ = {xy = −1} ∩ Ω` satisfies (CC′) with `Ω(S̃) = Ω`. `⟨γ₀, σ²⟩` has index 2 and fixes `Δ₀`, so `Γ`
  is elementary; but the direction of `U` contains the `(x, y)`-plane, so `Γ_U` is non-abelian, and
  no presentation as an LTP over a Misner spacetime (an abelian group) exists. `loxo_elementary_misner`
  is stated for a finite-index `Γ'` (DEC-43's R1).
* **Prop 4.17's proof (l.1255–1266) needs less than it uses**: the basin of repulsion of the
  repulsive point `x₀` of `γ` is all of `𝒥` off the fibre over the attractive point `v₁` of `γ`
  (not only some `δ⁻¹(U)`, `tendsto_isomPenrose_inv_pow`), so no closure of `δ(Λ)` is needed: if
  `Λ ⊆ δ⁻¹(v₁)`, then `{v₁}` is closed, nonempty and `L(Γ)`-invariant and the limit-set
  minimality puts `v₀ ≠ v₁` in it. The `s`-coordinate converges because the elliptic part grows
  linearly against the contraction `λᵏ` (`exists_abs_minkB_pow_smul_sub_le`).
* **Prop 10.4's folklore is false as printed** (`Flat.Externals`' `not_abelianPairAsPrinted`); its
  lightlike case does not use it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 5, package WP-34d-Loxodromic.
-/

namespace Causal.Flat

open Set Function TopologicalSpace Topology Filter
open scoped Pointwise

variable {d : ℕ}

/-! ## 0. Loxodromic isometries, their repulsive fixed points in `𝒥`, the limit set -/

section RepulsiveFixed

/-- An element of `SO₀(1, d)` whose inverse is loxodromic is loxodromic (`R⁻¹` elliptic, the boost
`H⁻¹` of rapidity `−ζ`). -/
theorem IsLoxodromic.inv' {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (h : IsLoxodromic A) :
    IsLoxodromic A⁻¹ := by
  obtain ⟨R, H, hR, hH, ⟨E, hEs, hEp, hE⟩, ⟨e₀, e₁, ζ, hζ, h0, h1, h01, hH0, hH1, hW⟩, rfl, hc⟩ := h
  have hinv : ∀ x y, H x = y → H⁻¹ y = x := fun x y hxy => by rw [← hxy]; simp
  refine ⟨R⁻¹, H⁻¹, (lorentz d).inv_mem hR, (lorentz d).inv_mem hH, ⟨E, hEs, hEp, fun v w => ?_⟩,
    ⟨e₀, e₁, -ζ, neg_ne_zero.2 hζ, h0, h1, h01, ?_, ?_, fun w hw0 hw1 => ?_⟩, ?_, ?_⟩
  · have := hE (R⁻¹ v) (R⁻¹ w)
    rw [← this]; simp
  · rw [Real.cosh_neg, Real.sinh_neg]
    refine hinv _ _ ?_
    rw [map_add, map_smul, map_smul, hH0, hH1]
    linear_combination (norm := module) (Real.cosh_sq_sub_sinh_sq ζ) • e₀
  · rw [Real.cosh_neg, Real.sinh_neg]
    refine hinv _ _ ?_
    rw [map_add, map_smul, map_smul, hH0, hH1]
    linear_combination (norm := module) (Real.cosh_sq_sub_sinh_sq ζ) • e₁
  · exact hinv _ _ (hW w hw0 hw1)
  · rw [hc, mul_inv_rev]
  · rw [← mul_inv_rev, ← mul_inv_rev, hc]

theorem isLoxodromic_linOf_inv {γ : isom d} (h : IsLoxodromic (linOf γ)) :
    IsLoxodromic (linOf γ⁻¹) := by
  rw [linOf_inv]; exact h.inv'

/-- A loxodromic isometry is not the identity (`id` is elliptic). -/
theorem ne_one_of_isLoxodromic {γ : isom d} (h : IsLoxodromic (linOf γ)) : γ ≠ 1 := by
  rintro rfl
  exact h.not_isElliptic (by
    have : linOf (1 : isom d) = 1 := by
      have := linOf_mul (1 : isom d) 1; rw [one_mul] at this
      exact LinearEquiv.ext fun v => by
        have h2 := congrArg (fun A : Minkowski d ≃ₗ[ℝ] Minkowski d => (linOf (1 : isom d))⁻¹ (A v)) this
        simpa using h2.symm
    rw [this]; exact isElliptic_one)

/-- **A repulsive fixed point in `𝒥 ≅ 𝒮 × ℝ` of an isometry `γ`** (l.1254–1258, l.3199–3200):
`L(γ)` is loxodromic, the future null vector `(1, u)` is an eigenvector of `L(γ)` for an eigenvalue
`0 < λ < 1`, and the lightlike hyperplane `{⟨(1,u) | ·⟩ = s}` is `γ`-invariant, with
`⟨(1,u) | γ p⟩ − s = λ⁻¹ (⟨(1,u) | p⟩ − s)`: `γ` pushes points away from it. On `𝒮` this is
Externals' `IsRepulsiveFixed` (`IsRepulsiveFixedJ.isRepulsiveFixed`). -/
def IsRepulsiveFixedJ (γ : isom d) (w : PenroseSphere d × ℝ) : Prop :=
  IsLoxodromic (linOf γ) ∧ ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
    ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 = l⁻¹ * (minkB (nullVec w.1) p - w.2)

/-- **`Λ₀(Γ)`**, the repulsive fixed points in `𝒥` of the loxodromic elements of `Γ`
(l.3199–3200). -/
def loxRepSet (Γ : Subgroup (isom d)) : Set (PenroseSphere d × ℝ) :=
  {w | ∃ γ ∈ Γ, IsRepulsiveFixedJ γ w}

/-- **`Λ(Γ)`, the closure of `Λ₀(Γ)` in `𝒥`** (l.3203–3205; the `Λ(ρ)` of `bprop:admlox` and
`bdef:definitioncauchyhyp`, l.1232–1238, l.1277–1280). -/
def limitSetJ (Γ : Subgroup (isom d)) : Set (PenroseSphere d × ℝ) := closure (loxRepSet Γ)

theorem isClosed_limitSetJ (Γ : Subgroup (isom d)) : IsClosed (limitSetJ Γ) := isClosed_closure

theorem loxRepSet_subset_limitSetJ (Γ : Subgroup (isom d)) : loxRepSet Γ ⊆ limitSetJ Γ :=
  subset_closure

/-- `⟨(1,u) | γ p⟩ = λ⁻¹ ⟨(1,u) | p⟩` along the linear part, from the eigenvector equation. -/
theorem minkB_linOf_of_eigen {γ : isom d} {n : Minkowski d} {l : ℝ} (hl : l ≠ 0)
    (hn : linOf γ n = l • n) (p : Minkowski d) : minkB n (linOf γ p) = l⁻¹ * minkB n p := by
  have h := lorentz.minkB_apply (linOf_mem γ) n p
  rw [hn, minkB_smul_left] at h
  field_simp; linarith

/-- **The functional equation gives the eigenvector equation**: if an affine function
`⟨n | ·⟩ − s` is multiplied by `c⁻¹` under `γ`, then `L(γ) n = c n`. -/
theorem eigen_of_funEq {γ : isom d} {n : Minkowski d} {s c : ℝ} (hc : c ≠ 0)
    (h : ∀ p, minkB n (γ • p) - s = c⁻¹ * (minkB n p - s)) : linOf γ n = c • n := by
  have hlin : ∀ p, minkB n (linOf γ p) = c⁻¹ * minkB n p := fun p => by
    have h1 := h p
    have h0 := h 0
    rw [smul_eq_lin_add] at h1 h0
    rw [map_zero, zero_add, minkB_zero_right] at h0
    rw [minkB_add_right] at h1
    linarith
  have hz : ∀ z, minkB z (linOf γ n - c • n) = 0 := fun z => by
    obtain ⟨p, rfl⟩ := (linOf γ).surjective z
    rw [minkB_sub_right, minkB_smul_right, lorentz.minkB_apply (linOf_mem γ), minkB_comm p n,
      minkB_comm (linOf γ p) n, hlin p]
    field_simp; ring
  exact sub_eq_zero.1 (eq_zero_of_forall_minkB hz)

/-- **Existence of the repulsive fixed point** of a loxodromic isometry. -/
theorem exists_isRepulsiveFixedJ {γ : isom d} (h : IsLoxodromic (linOf γ)) :
    ∃ w, IsRepulsiveFixedJ γ w := by
  obtain ⟨-, u, u', l, -, -, -, hu0, hu0', hq, hq', -, hl, hl1, hAu, hAu', -⟩ := h.frame
  obtain ⟨e, μ, he0, heq, hμ0, hμ1, hAe⟩ : ∃ e : Minkowski d, ∃ μ : ℝ, e ≠ 0 ∧ minkQ e = 0 ∧
      0 < μ ∧ μ < 1 ∧ linOf γ e = μ • e := by
    rcases lt_or_gt_of_ne hl1 with h1 | h1
    · exact ⟨u, l, hu0, hq, hl, h1, hAu⟩
    · exact ⟨u', l⁻¹, hu0', hq', inv_pos.2 hl, inv_lt_one_of_one_lt₀ h1, hAu'⟩
  have he1 : e.1 ≠ 0 := fun h0 => he0 (eq_zero_of_fst_eq_zero h0 heq.le)
  have hnorm : ‖e.2‖ = |e.1| := by
    have h2 : ‖e.2‖ ^ 2 = |e.1| ^ 2 := by
      have := heq; simp only [minkQ] at this; rw [sq_abs]; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 h2
  set û : PenroseSphere d := ⟨e.1⁻¹ • e.2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, hnorm,
      inv_mul_cancel₀ (abs_ne_zero.2 he1)]⟩
  have hn : nullVec û = e.1⁻¹ • e := by
    refine Prod.ext ?_ rfl
    simp [nullVec, inv_mul_cancel₀ he1]
  have hAn : linOf γ (nullVec û) = μ • nullVec û := by
    rw [hn, map_smul, hAe, smul_comm]
  have hμ1' : (1 : ℝ) - μ⁻¹ ≠ 0 := by
    have : 1 < μ⁻¹ := one_lt_inv_iff₀.2 ⟨hμ0, hμ1⟩
    linarith
  refine ⟨(û, minkB (nullVec û) (trOf γ) / (1 - μ⁻¹)), h, μ, hμ0, hμ1, hAn, fun p => ?_⟩
  simp only
  rw [smul_eq_lin_add, minkB_add_right, minkB_linOf_of_eigen hμ0.ne' hAn]
  have hs : minkB (nullVec û) (trOf γ) / (1 - μ⁻¹) * (1 - μ⁻¹) = minkB (nullVec û) (trOf γ) :=
    div_mul_cancel₀ _ hμ1'
  linear_combination -hs

/-- **The repulsive fixed points of `γ` and of `γ⁻¹` have distinct null directions**: their
eigenvalues for `L(γ)` are `λ < 1` and `λ'⁻¹ > 1`. -/
theorem IsRepulsiveFixedJ.fst_ne {γ : isom d} {w w' : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') : w.1 ≠ w'.1 := by
  obtain ⟨-, l, hl0, hl1, hAn, -⟩ := hw
  obtain ⟨-, l', hl0', hl1', hAn', -⟩ := hw'
  intro he
  rw [he] at hAn
  rw [linOf_inv] at hAn'
  have : linOf γ (nullVec w'.1) = l'⁻¹ • nullVec w'.1 := by
    have h2 := congrArg (linOf γ) hAn'
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, map_smul] at h2
    rw [eq_inv_smul_iff₀ hl0'.ne']; exact h2.symm
  rw [this] at hAn
  have hll : l'⁻¹ = l := smul_left_injective ℝ (nullVec_ne_zero w'.1) hAn
  have : 1 < l'⁻¹ := one_lt_inv_iff₀.2 ⟨hl0', hl1'⟩
  linarith

/-- The functional equation along iterates: `f(γⁿ p) = λ⁻ⁿ f(p)`. -/
theorem IsRepulsiveFixedJ.iterate {γ : isom d} {w : PenroseSphere d × ℝ} {l : ℝ}
    (h : ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 = l⁻¹ * (minkB (nullVec w.1) p - w.2))
    (n : ℕ) (p : Minkowski d) :
    minkB (nullVec w.1) ((γ ^ n) • p) - w.2 = (l⁻¹) ^ n * (minkB (nullVec w.1) p - w.2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_smul, h, ih, pow_succ']; ring

/-- The functional equation of a repulsive point of `γ⁻¹`, read along `γ`: `f(γ p) = λ f(p)`. -/
theorem funEq_of_inv {γ : isom d} {w : PenroseSphere d × ℝ} {l : ℝ} (hl : l ≠ 0)
    (h : ∀ p : Minkowski d,
      minkB (nullVec w.1) (γ⁻¹ • p) - w.2 = l⁻¹ * (minkB (nullVec w.1) p - w.2))
    (p : Minkowski d) :
    minkB (nullVec w.1) (γ • p) - w.2 = l * (minkB (nullVec w.1) p - w.2) := by
  have := h (γ • p)
  rw [inv_smul_smul] at this
  rw [this]; field_simp

end RepulsiveFixed

/-! ## 1. The achronal domain of a loxodromic isometry: two quadrants -/

section Quadrants

/-- A vector with `minkQ ≤ 0` is future causal or past causal. -/
theorem isFutureCausal_or_neg_of_minkQ_nonpos {y : Minkowski d} (h : minkQ y ≤ 0) :
    IsFutureCausal y ∨ IsFutureCausal (-y) := by
  rcases le_total 0 y.1 with h1 | h1
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr ⟨by simpa using h1, by rw [minkQ_neg]; exact h⟩

/-- **Two future null vectors separating `y`** (`⟨n | y⟩ < 0 < ⟨n' | y⟩`) force `y` spacelike. -/
theorem minkQ_pos_of_minkB_sign {n n' y : Minkowski d} (hn : IsFutureCausal n)
    (hn' : IsFutureCausal n') (h1 : minkB n y < 0) (h2 : 0 < minkB n' y) : 0 < minkQ y := by
  by_contra hle
  rcases isFutureCausal_or_neg_of_minkQ_nonpos (not_lt.1 hle) with hy | hy
  · have := minkB_nonpos_of_isFutureCausal hn' hy; linarith
  · have := minkB_nonpos_of_isFutureCausal hn hy
    rw [minkB_neg_right] at this; linarith

/-- **The two quadrants lie in `Ω_γ`** (the easy half of [7.L], read in `𝒥`): for `w` a
repulsive fixed point of `γ` and `w'` one of `γ⁻¹`, both `P⁺(w) ∩ P⁺(w')` and `P⁻(w) ∩ P⁻(w')`
lie in the achronal domain of `γ`. -/
theorem quadrants_subset_achronalDomain {γ : isom d} {w w' : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') :
    (halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2) ∪ (halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2) ⊆
      achronalDomain γ := by
  obtain ⟨-, l, hl0, hl1, -, hf⟩ := hw
  obtain ⟨-, l', hl0', hl1', -, hf'⟩ := hw'
  have hg' := funEq_of_inv hl0'.ne' hf'
  intro x hx
  rw [mem_achronalDomain_iff]
  intro n hn
  set y := (γ ^ n) • x - x
  have hB : minkB (nullVec w.1) y =
      ((l⁻¹) ^ n - 1) * (minkB (nullVec w.1) x - w.2) := by
    simp only [y, minkB_sub_right]
    have := IsRepulsiveFixedJ.iterate hf n x
    linarith
  have hB' : minkB (nullVec w'.1) y = (l' ^ n - 1) * (minkB (nullVec w'.1) x - w'.2) := by
    simp only [y, minkB_sub_right]
    have := IsRepulsiveFixedJ.iterate (l := l'⁻¹) (by simpa using hg') n x
    rw [inv_inv] at this
    linarith
  have hgt : 0 < (l⁻¹) ^ n - 1 := by
    have : 1 < l⁻¹ := one_lt_inv_iff₀.2 ⟨hl0, hl1⟩
    have := one_lt_pow₀ this hn.ne'
    linarith
  have hlt : l' ^ n - 1 < 0 := by
    have := pow_lt_one₀ hl0'.le hl1' hn.ne'
    linarith
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [mem_halfPlus] at h1 h2
    exact minkQ_pos_of_minkB_sign (isFutureCausal_nullVec w.1) (isFutureCausal_nullVec w'.1)
      (by rw [hB]; exact mul_neg_of_pos_of_neg hgt (by linarith))
      (by rw [hB']; exact mul_pos_of_neg_of_neg hlt (by linarith))
  · rw [mem_halfMinus] at h1 h2
    exact minkQ_pos_of_minkB_sign (isFutureCausal_nullVec w'.1) (isFutureCausal_nullVec w.1)
      (by rw [hB']; exact mul_neg_of_neg_of_pos hlt (by linarith))
      (by rw [hB]; exact mul_pos hgt (by linarith))

/-- **A null eigenvector of a loxodromic `L(γ)` lies on one of the two lines of its frame**, with
the frame's eigenvalue. -/
theorem null_eigen_cases {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    {u u' : Minkowski d} {l : ℝ} (hu0 : u ≠ 0) (hu : minkQ u = 0) (hu'0 : u' ≠ 0)
    (hB : minkB u u' ≠ 0) (hl : 0 < l) (hl1 : l ≠ 1) (hAu : A u = l • u)
    (hAu' : A u' = l⁻¹ • u') {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) {μ : ℝ}
    (hAe : A e = μ • e) : (∃ c : ℝ, e = c • u ∧ μ = l) ∨ (∃ c : ℝ, e = c • u' ∧ μ = l⁻¹) := by
  have hQ : ∀ v, minkQ (A v) = minkQ v := lorentz.minkQ_apply hA
  have h1 := lorentz.minkB_apply hA e u
  have h2 := lorentz.minkB_apply hA e u'
  rw [hAe, hAu, minkB_smul_left, minkB_smul_right] at h1
  rw [hAe, hAu', minkB_smul_left, minkB_smul_right] at h2
  have hll : l * l ≠ 1 := fun h => hl1 (by nlinarith)
  have hll' : l⁻¹ * l⁻¹ ≠ 1 := fun h => hl1 (by
    have : l⁻¹ = 1 := by nlinarith [inv_pos.2 hl]
    simpa using this)
  by_cases hb' : minkB e u' = 0
  · by_cases hb : minkB e u = 0
    · exfalso
      obtain ⟨c, rfl⟩ := eq_smul_of_null_orth hu hu0 he (by rw [minkB_comm]; exact hb)
      rw [minkB_smul_left] at hb'
      have hc : c = 0 := (mul_eq_zero.1 hb').resolve_right hB
      exact he0 (by rw [hc, zero_smul])
    · have hμ : μ = l⁻¹ := by
        have : μ * l = 1 := by
          have : (μ * l - 1) * minkB e u = 0 := by linear_combination h1
          exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hb)
        field_simp; linarith
      right
      obtain ⟨c, hc⟩ := eigen_line hQ hll' hu'0 hAu' (w := e) (by rw [hAe, hμ])
      exact ⟨c, hc, hμ⟩
  · have hμ : μ = l := by
      have : μ * l⁻¹ = 1 := by
        have : (μ * l⁻¹ - 1) * minkB e u' = 0 := by linear_combination h2
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hb')
      field_simp at this; linarith
    left
    obtain ⟨c, hc⟩ := eigen_line hQ hll hu0 hAu (w := e) (by rw [hAe, hμ])
    exact ⟨c, hc, hμ⟩

theorem nullXY_smul_smul (u u' z : Minkowski d) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    nullXY (a • u) (b • u') z = nullXY u u' z := by
  simp only [nullXY, minkB_smul_left, minkB_smul_right]
  by_cases h : minkB u u' = 0
  · simp [h]
  · field_simp

theorem nullXY_comm (u u' z : Minkowski d) : nullXY u u' z = nullXY u' u z := by
  simp only [nullXY, minkB_comm u u']; ring

/-- **[7.L] in `𝒥`, exactly**: the interior of the achronal domain of a loxodromic `γ` is the union
of the two quadrants `P⁺(w) ∩ P⁺(w')` (future complete) and `P⁻(w) ∩ P⁻(w')` (past complete),
`w` the repulsive fixed point of `γ` and `w'` that of `γ⁻¹` (any choice of either). These are
Barbot's `U⁺(γ)`, `U⁻(γ)` (l.3176–3178). -/
theorem interior_achronalDomain_eq_quadrants {γ : isom d} {w w' : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') :
    interior (achronalDomain γ) =
      (halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2) ∪ (halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2) := by
  have hopen : IsOpen ((halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2) ∪
      (halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2)) :=
    ((isOpen_halfPlus _ _).inter (isOpen_halfPlus _ _)).union
      ((isOpen_halfMinus _ _).inter (isOpen_halfMinus _ _))
  refine Subset.antisymm ?_ (interior_maximal (quadrants_subset_achronalDomain hw hw') hopen)
  have hfst := hw.fst_ne hw'
  obtain ⟨hlox, lw, hlw0, hlw1, hAn, hf⟩ := hw
  obtain ⟨-, lw', hlw0', hlw1', -, hf'⟩ := hw'
  have hg' := funEq_of_inv hlw0'.ne' hf'
  have hAn' : linOf γ (nullVec w'.1) = lw'⁻¹ • nullVec w'.1 :=
    eigen_of_funEq (inv_ne_zero hlw0'.ne') (by simpa using hg')
  set n := nullVec w.1
  set n' := nullVec w'.1
  -- the normal form `g' = isomConj v γ`
  obtain ⟨v, hv⟩ := IsLoxodromic.exists_transConj_fixed γ.2 hlox
  set g' := isomConj v γ
  have hτ : linOf g' (trOf g') = trOf g' := by rw [linOf_isomConj]; exact hv
  have htr : trOf g' = v + γ • (-v) := by
    show transPart (transConj v (γ : Minkowski d ≃ᵃ[ℝ] Minkowski d)) = _
    rw [transPart, transConj_apply, add_zero, isom_smul_def]
  have hQ : ∀ x, minkQ (linOf γ x) = minkQ x := lorentz.minkQ_apply (linOf_mem γ)
  have hτ' : linOf γ (trOf g') = trOf g' := by rw [← linOf_isomConj v γ]; exact hτ
  -- the constants vanish in the normal form: `⟨n | v + z⟩ = ⟨n | z⟩ − s`
  have hc : minkB n v + w.2 = 0 := by
    have h0 : minkB (trOf g') n = 0 := minkB_fixed_eigen hQ hlw1.ne hτ' hAn
    rw [htr, minkB_add_left, minkB_comm, minkB_comm (γ • -v)] at h0
    have h1 := hf (-v)
    rw [minkB_neg_right] at h1
    have hl : lw⁻¹ ≠ 1 := by
      have : 1 < lw⁻¹ := one_lt_inv_iff₀.2 ⟨hlw0, hlw1⟩
      exact this.ne'
    have : (minkB n v + w.2) * (1 - lw⁻¹) = 0 := by linear_combination h0 - h1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hl.symm)
  have hc' : minkB n' v + w'.2 = 0 := by
    have hne : lw'⁻¹ ≠ 1 := by
      have : 1 < lw'⁻¹ := one_lt_inv_iff₀.2 ⟨hlw0', hlw1'⟩
      exact this.ne'
    have h0 : minkB (trOf g') n' = 0 := minkB_fixed_eigen hQ hne hτ' hAn'
    rw [htr, minkB_add_left, minkB_comm, minkB_comm (γ • -v)] at h0
    have h1 := hg' (-v)
    rw [minkB_neg_right] at h1
    have : (minkB n' v + w'.2) * (1 - lw') = 0 := by linear_combination h0 - h1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hlw1'.ne')
  -- the frame of `L(γ)`, and `nullXY` in terms of `n`, `n'`
  obtain ⟨-, u, u', l, -, -, -, hu0, hu0', hu, hu', hB, hl, hl1, hAu, hAu', -⟩ := hlox.frame
  have hint := interior_achronalDomain_lox (g := g') hu hu' hB hl hl1
    (by rw [linOf_isomConj]; exact hAu) (by rw [linOf_isomConj]; exact hAu') hτ
  have hnn' : minkB n n' < 0 := by
    rw [minkB_nullVec_nullVec]
    have : 0 < ‖((w.1 : PenroseSphere d) : EuclideanSpace ℝ (Fin d)) - w'.1‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact fun h => hfst (Subtype.ext h)
    have := pow_pos this 2
    linarith
  have hXY : ∀ x, nullXY u u' x = 2 * minkB x n * minkB x n' / minkB n n' := by
    intro x
    have key : ∀ (a b : ℝ) (e e' : Minkowski d), a ≠ 0 → b ≠ 0 → n = a • e → n' = b • e' →
        nullXY e e' x = 2 * minkB x n * minkB x n' / minkB n n' := by
      intro a b e e' ha hb hn hn'
      rw [← nullXY_smul_smul e e' x ha hb, ← hn, ← hn', nullXY]
    rcases null_eigen_cases (linOf_mem γ) hu0 hu hu0' hB hl hl1 hAu hAu'
        (nullVec_ne_zero w.1) (minkQ_nullVec w.1) hAn with ⟨a, ha, hla⟩ | ⟨a, ha, hla⟩ <;>
      rcases null_eigen_cases (linOf_mem γ) hu0 hu hu0' hB hl hl1 hAu hAu'
        (nullVec_ne_zero w'.1) (minkQ_nullVec w'.1) hAn' with ⟨b, hb, hlb⟩ | ⟨b, hb, hlb⟩
    · exfalso
      have : 1 < lw'⁻¹ := one_lt_inv_iff₀.2 ⟨hlw0', hlw1'⟩
      linarith
    · have ha0 : a ≠ 0 := fun h => nullVec_ne_zero w.1 (by rw [ha, h, zero_smul])
      have hb0 : b ≠ 0 := fun h => nullVec_ne_zero w'.1 (by rw [hb, h, zero_smul])
      exact key a b u u' ha0 hb0 ha hb
    · have ha0 : a ≠ 0 := fun h => nullVec_ne_zero w.1 (by rw [ha, h, zero_smul])
      have hb0 : b ≠ 0 := fun h => nullVec_ne_zero w'.1 (by rw [hb, h, zero_smul])
      rw [nullXY_comm]; exact key a b u' u ha0 hb0 ha hb
    · exfalso
      have : 1 < lw'⁻¹ := one_lt_inv_iff₀.2 ⟨hlw0', hlw1'⟩
      have : lw = lw'⁻¹ := by rw [hla, hlb]
      linarith
  -- conclusion
  intro z hz
  have hz' : v + z ∈ interior (achronalDomain g') := by
    have e1 : achronalDomain γ = (Homeomorph.addLeft v) ⁻¹' achronalDomain g' :=
      achronalDomain_eq_preimage_isomConj v γ
    rw [e1, ← Homeomorph.preimage_interior] at hz
    exact hz
  rw [hint, mem_setOf_eq, hXY, div_neg_iff] at hz'
  have hpos : 0 < minkB (v + z) n * minkB (v + z) n' := by
    rcases hz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have e1 : minkB (v + z) n = minkB n z - w.2 := by
    rw [minkB_comm, minkB_add_right]; linarith
  have e2 : minkB (v + z) n' = minkB n' z - w'.2 := by
    rw [minkB_comm, minkB_add_right]; linarith
  rw [e1, e2] at hpos
  have hne : minkB n z - w.2 ≠ 0 := by
    intro h; rw [h, zero_mul] at hpos; exact lt_irrefl _ hpos
  rcases lt_or_gt_of_ne hne with h1 | h1
  · left
    refine ⟨mem_halfPlus.2 (by linarith), mem_halfPlus.2 ?_⟩
    by_contra h2; push Not at h2
    nlinarith
  · right
    refine ⟨mem_halfMinus.2 (by linarith), mem_halfMinus.2 ?_⟩
    by_contra h2; push Not at h2
    nlinarith

end Quadrants


/-! ## 2. `U(γ)` for the classes of §6, and the regular domains -/

section Classes

open Classical in
theorem Ug_eq_achronalDomain_of_isLoxodromic {g : isom d} (h : IsLoxodromic (linOf g)) :
    Ug g = achronalDomain g := by
  unfold Ug
  rw [if_neg (fun hN => h.not_isElliptic hN.1), if_neg (fun hL => hL.1.not_isLoxodromic h)]

/-- **[7.E] for a spacelike elliptic `g`, in any frame: `U(g) = Ω_g = 𝐌ⁿ`.** -/
theorem achronalDomain_eq_univ_of_isSpacelikeElliptic {g : isom d} (h : IsSpacelikeElliptic g) :
    achronalDomain g = univ := by
  obtain ⟨hE, x, hx1, hx2⟩ := h
  have htr : trOf (isomConj (-x) g) = g • x - x := by
    rw [trOf_isomConj, map_neg, pOf_apply, smul_eq_lin_add]; abel
  rw [achronalDomain_eq_preimage_isomConj (-x) g,
    achronalDomain_elliptic_spacelike (g := isomConj (-x) g) (by rw [linOf_isomConj]; exact hE)
      (by rw [linOf_isomConj, htr]; exact hx1) (by rw [htr]; exact hx2), preimage_univ]

/-- **[7.P] for a tangent parabolic `g`, in any frame: `Ω_g = 𝐌ⁿ`.** -/
theorem achronalDomain_eq_univ_of_isTangentParabolic {g : isom d} (h : IsTangentParabolic g) :
    achronalDomain g = univ := by
  obtain ⟨R, U, ⟨hR, hU, hRe, hn, hU1, hg, hc⟩, hT⟩ := h
  have hrange := parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc
  obtain ⟨vₙ, v₁, -, h1, -, -, -, -, hq1, -⟩ := unipotent_frame hU.1 hn (pOf_ne_zero hU1)
  obtain ⟨v, hv, -⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
    (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
  have hT' : IsTangentCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) := by
    refine ⟨?_, fun h' => hT.2 ((isLinearCase_transConj_iff v _).1 h')⟩
    have hr : LinearMap.range (pOf (linOf g)) ≤ minkOrth (nullPart U) := by
      rw [hg]; exact hrange
    rw [transPart_transConj_mem_iff hr v]; exact hT.1
  rw [achronalDomain_eq_preimage_isomConj v g,
    achronalDomain_parabolic_tangent hR hU hRe hn hU1 hc
      (g := isomConj v g) (by rw [linOf_isomConj]; exact hg) hv hT', preimage_univ]

/-- A real `β` with `kβ` bounded above on both sides of `0` (`k ∈ ℕ`) is `0`. -/
theorem eq_zero_of_nat_mul_le {β C : ℝ} (h1 : ∀ k : ℕ, (k : ℝ) * β ≤ C)
    (h2 : ∀ k : ℕ, -((k : ℝ) * β) ≤ C) : β = 0 := by
  by_contra hβ
  rcases lt_or_gt_of_ne hβ with hβ | hβ
  · obtain ⟨k, hk⟩ := exists_nat_gt (C / -β)
    have := h2 k
    rw [div_lt_iff₀ (by linarith)] at hk
    linarith
  · obtain ⟨k, hk⟩ := exists_nat_gt (C / β)
    have := h1 k
    rw [div_lt_iff₀ hβ] at hk
    linarith

section LinearParabolic

variable {γ : isom d} {R U : Minkowski d ≃ₗ[ℝ] Minkowski d} (hp : IsParabolicPair γ R U)
  {c : Minkowski d} (hc : γ • c = c) {y : Minkowski d} (hy : y ∈ minkOrth (nullPart U))
include hp hc hy

/-- **The forward orbit** of `c + y`, `y ∈ J^⊥`: `γᵏ(c + y) = c + Rᵏ y + k p(y)`. -/
theorem linearParabolic_orbit_fwd (k : ℕ) :
    (γ ^ k) • (c + y) = c + ((R ^ k) y + (k : ℝ) • pOf U y) := by
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩ := hp
  have hpy : pOf U y ∈ nullPart U := pOf_mem_nullPart hU.1 hn (pOf_ne_zero hU1) hy
  have hUpy : U (pOf U y) = pOf U y := by
    have := pOf_eq_zero_of_mem_nullPart hU.1 hpy
    rwa [pOf_apply, sub_eq_zero] at this
  have hRpy : R (pOf U y) = pOf U y := parabolic_R_fix_range hR hU hRe hn hU1 hcomm ⟨y, rfl⟩
  have hRk : ∀ k : ℕ, (R ^ k) (pOf U y) = pOf U y := fun k => pow_apply_eq_self hRpy k
  have hγp : ∀ p, γ • p = linOf γ (p - c) + c := fun p => by
    have := smul_sub_smul γ p c; rw [hc] at this; rw [← this]; abel
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, hγp, add_sub_cancel_left, hg, LinearEquiv.mul_apply,
      map_add, map_smul, hUpy, map_add, map_smul, hRpy]
    have hcomm' : U ((R ^ k) y) = (R ^ k) (U y) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply,
        ((Commute.pow_left (show Commute R U from hcomm) k).eq).symm]
    rw [hcomm', apply_eq_add_pOf U y, map_add, hRk, map_add, hRpy, ← LinearEquiv.mul_apply,
      ← pow_succ']
    push_cast
    module

/-- **The backward orbit**: `γ⁻ᵏ(c + y) = c + R⁻ᵏ y − k p(y)`. -/
theorem linearParabolic_orbit_bwd (k : ℕ) :
    (γ⁻¹ ^ k) • (c + y) = c + (((R⁻¹) ^ k) y - (k : ℝ) • pOf U y) := by
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩ := hp
  have hpy : pOf U y ∈ nullPart U := pOf_mem_nullPart hU.1 hn (pOf_ne_zero hU1) hy
  have hUpy : U (pOf U y) = pOf U y := by
    have := pOf_eq_zero_of_mem_nullPart hU.1 hpy
    rwa [pOf_apply, sub_eq_zero] at this
  have hRpy : R (pOf U y) = pOf U y := parabolic_R_fix_range hR hU hRe hn hU1 hcomm ⟨y, rfl⟩
  have hRipy : R⁻¹ (pOf U y) = pOf U y := by
    conv_lhs => rw [← hRpy]
    simp
  have hRik : ∀ k : ℕ, ((R⁻¹) ^ k) (pOf U y) = pOf U y := fun k => pow_apply_eq_self hRipy k
  have hUR : ∀ z, U (R⁻¹ z) = R⁻¹ (U z) := fun z => by
    apply R.injective
    have h1 : R (U (R⁻¹ z)) = U (R (R⁻¹ z)) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hcomm]
      simp only [LinearEquiv.mul_apply]
    rw [h1]; simp
  have hURk : ∀ k : ℕ, ∀ z, U (((R⁻¹) ^ k) z) = ((R⁻¹) ^ k) (U z) := by
    intro k; induction k with
    | zero => intro z; simp
    | succ k ih => intro z; rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hUR, ih]
  have hci : γ⁻¹ • c = c := by rw [inv_smul_eq_iff, hc]
  have hγp : ∀ p, γ⁻¹ • p = linOf γ⁻¹ (p - c) + c := fun p => by
    have := smul_sub_smul γ⁻¹ p c; rw [hci] at this; rw [← this]; abel
  -- `L(γ)⁻¹ (R⁻ᵏ y) = R⁻ᵏ⁻¹ y − p(y)`
  have hstep : ∀ k : ℕ, linOf γ⁻¹ (((R⁻¹) ^ k) y) = ((R⁻¹) ^ (k + 1)) y - pOf U y := by
    intro k
    rw [linOf_inv]
    have this : linOf γ (((R⁻¹) ^ (k + 1)) y - pOf U y) = ((R⁻¹) ^ k) y := by
      have e1 : U (((R⁻¹) ^ (k + 1)) y) = ((R⁻¹) ^ (k + 1)) y + pOf U y := by
        rw [hURk]
        conv_lhs => rw [apply_eq_add_pOf U y]
        rw [map_add, hRik]
      have e2 : R (((R⁻¹) ^ (k + 1)) y) = ((R⁻¹) ^ k) y := by
        rw [pow_succ', LinearEquiv.mul_apply]; simp
      rw [hg, LinearEquiv.mul_apply, map_sub, e1, hUpy, map_sub, map_add, e2, hRpy]
      abel
    rw [← this]; simp
  have hLpy : linOf γ⁻¹ (pOf U y) = pOf U y := by
    rw [linOf_inv]
    have : linOf γ (pOf U y) = pOf U y := by rw [hg, LinearEquiv.mul_apply, hUpy, hRpy]
    conv_lhs => rw [← this]
    simp
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, hγp, add_sub_cancel_left, map_sub, map_smul, hstep, hLpy]
    push_cast
    module

end LinearParabolic

/-- The iterates of an elliptic `R` (and of `R⁻¹`) keep a vector in a bounded set: they preserve
the euclidean form of `IsElliptic`, which is coercive. -/
theorem IsElliptic.bounded_orbit {R : Minkowski d ≃ₗ[ℝ] Minkowski d} (hRe : IsElliptic R)
    (y : Minkowski d) : ∃ K : ℝ, ∀ k : ℕ, ‖(R ^ k) y‖ ^ 2 ≤ K ∧ ‖((R⁻¹) ^ k) y‖ ^ 2 ≤ K := by
  obtain ⟨E, -, hEp, hE⟩ := hRe
  obtain ⟨m, hm, hcoer⟩ := exists_coercive E hEp
  have hE' : ∀ v w, E (R⁻¹ v) (R⁻¹ w) = E v w := fun v w => by
    rw [← hE (R⁻¹ v) (R⁻¹ w)]; simp
  have h1 : ∀ k : ℕ, E ((R ^ k) y) ((R ^ k) y) = E y y := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, hE, ih]
  have h2 : ∀ k : ℕ, E (((R⁻¹) ^ k) y) (((R⁻¹) ^ k) y) = E y y := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, hE', ih]
  refine ⟨E y y / m, fun k => ⟨?_, ?_⟩⟩
  · rw [le_div_iff₀ hm]; have := hcoer ((R ^ k) y); rw [h1] at this; linarith
  · rw [le_div_iff₀ hm]; have := hcoer (((R⁻¹) ^ k) y); rw [h2] at this; linarith

/-- `|⟨(1,u) | z⟩| ≤ (1 + 4‖z‖²)/2`, a bound with no square root. -/
theorem abs_minkB_nullVec_le_sq (u : PenroseSphere d) (z : Minkowski d) :
    |minkB (nullVec u) z| ≤ (1 + 4 * ‖z‖ ^ 2) / 2 := by
  have h := abs_minkB_nullVec_le_two_mul_norm u z
  nlinarith [norm_nonneg z, sq_nonneg (2 * ‖z‖ - 1)]


/-- A null function `⟨(1,u) | ·⟩` bounded on one side of a set. -/
def OneSidedOn (Ω : Set (Minkowski d)) (u : PenroseSphere d) : Prop :=
  (∃ M, ∀ p ∈ Ω, minkB (nullVec u) p ≤ M) ∨ ∃ M, ∀ p ∈ Ω, M ≤ minkB (nullVec u) p

/-- **The core of `blem:sanlox`, corrected** (l.3153–3165): an open set `Ω` invariant under a
linear parabolic `γ` and `γ⁻¹`, on which the null functions of two distinct directions are
bounded on one side, misses the null hyperplanes `c + J^⊥` of `γ`. Barbot's argument, made
exact: on the `γ`-orbit of a point `c + y`, `y ∈ J^⊥`, `⟨n | ·⟩` is `⟨n | c⟩ + ⟨n | Rᵏ y⟩ ± k ⟨n | p(y)⟩`
with the middle term bounded, so a one-sided bound forces `⟨n | p(y)⟩ = 0`; `p(y)` spans the null
line `J` once `y` is moved off `ker p` inside `Ω`, and two distinct null directions cannot both be
orthogonal to `J`. -/
theorem subset_compl_nullHyperplanes_of_oneSided {γ : isom d} {Ω : Set (Minkowski d)}
    (hΩ : IsOpen Ω) (hinv : ∀ p ∈ Ω, γ • p ∈ Ω) (hinv' : ∀ p ∈ Ω, γ⁻¹ • p ∈ Ω)
    {u₁ u₂ : PenroseSphere d} (hu : u₁ ≠ u₂) (hb₁ : OneSidedOn Ω u₁) (hb₂ : OneSidedOn Ω u₂) :
    Ω ⊆ (nullHyperplanes γ)ᶜ := by
  rintro x hx ⟨R, U, hp, c, hc, hy⟩
  obtain ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩ := hp
  have hp' : IsParabolicPair γ R U := ⟨hR, hU, hRe, hn, hU1, hg, hcomm⟩
  have hp0 := pOf_ne_zero hU1
  -- move `y = x − c` off `ker p` inside `Ω`
  obtain ⟨y, hyJ, hyΩ, hpy0⟩ : ∃ y, y ∈ minkOrth (nullPart U) ∧ c + y ∈ Ω ∧ pOf U y ≠ 0 := by
    by_cases h0 : pOf U (x - c) = 0
    · obtain ⟨vₙ, v₁, v₀, h1, h2, hv₀, -⟩ := unipotent_frame hU.1 hn hp0
      have hv₁ : v₁ ∈ minkOrth (nullPart U) := range_le_minkOrth_nullPart U ⟨vₙ, h1⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
      set ε : ℝ := r / (2 * (‖v₁‖ + 1))
      have hε : 0 < ε := by positivity
      refine ⟨x - c + ε • v₁, add_mem hy (Submodule.smul_mem _ _ hv₁), ?_, ?_⟩
      · refine hball ?_
        rw [Metric.mem_ball, show c + (x - c + ε • v₁) = x + ε • v₁ by abel, dist_eq_norm,
          add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        have : ε * ‖v₁‖ ≤ r / 2 := by
          simp only [ε]; rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
          nlinarith [norm_nonneg v₁]
        linarith
      · rw [map_add, h0, zero_add, map_smul, h2]
        exact smul_ne_zero hε.ne' hv₀
    · exact ⟨x - c, hy, by rwa [add_sub_cancel], h0⟩
  have hpyN : pOf U y ∈ nullPart U := pOf_mem_nullPart hU.1 hn hp0 hyJ
  have hpyQ : minkQ (pOf U y) = 0 := minkQ_eq_zero_of_mem_nullPart hpyN
  -- the orbit stays in `Ω`
  have hfwd : ∀ k : ℕ, (γ ^ k) • (c + y) ∈ Ω := by
    intro k; induction k with
    | zero => simpa using hyΩ
    | succ k ih => rw [pow_succ', mul_smul]; exact hinv _ ih
  have hbwd : ∀ k : ℕ, (γ⁻¹ ^ k) • (c + y) ∈ Ω := by
    intro k; induction k with
    | zero => simpa using hyΩ
    | succ k ih => rw [pow_succ', mul_smul]; exact hinv' _ ih
  obtain ⟨K, hK⟩ := hRe.bounded_orbit y
  -- a one-sided bound kills `⟨n | p(y)⟩`
  have hkill : ∀ u : PenroseSphere d, OneSidedOn Ω u → minkB (nullVec u) (pOf U y) = 0 := by
    intro u hb
    set β := minkB (nullVec u) (pOf U y)
    have hf : ∀ k : ℕ, minkB (nullVec u) ((γ ^ k) • (c + y)) =
        minkB (nullVec u) c + minkB (nullVec u) ((R ^ k) y) + (k : ℝ) * β := by
      intro k
      rw [linearParabolic_orbit_fwd hp' hc hyJ k, minkB_add_right, minkB_add_right,
        minkB_smul_right]; ring
    have hb' : ∀ k : ℕ, minkB (nullVec u) ((γ⁻¹ ^ k) • (c + y)) =
        minkB (nullVec u) c + minkB (nullVec u) (((R⁻¹) ^ k) y) - (k : ℝ) * β := by
      intro k
      rw [linearParabolic_orbit_bwd hp' hc hyJ k, minkB_add_right, minkB_sub_right,
        minkB_smul_right]; ring
    have hB1 : ∀ k : ℕ, |minkB (nullVec u) ((R ^ k) y)| ≤ (1 + 4 * K) / 2 := fun k =>
      (abs_minkB_nullVec_le_sq u _).trans (by linarith [(hK k).1])
    have hB2 : ∀ k : ℕ, |minkB (nullVec u) (((R⁻¹) ^ k) y)| ≤ (1 + 4 * K) / 2 := fun k =>
      (abs_minkB_nullVec_le_sq u _).trans (by linarith [(hK k).2])
    rcases hb with ⟨M, hM⟩ | ⟨M, hM⟩
    · refine eq_zero_of_nat_mul_le (C := M - minkB (nullVec u) c + (1 + 4 * K) / 2)
        (fun k => ?_) (fun k => ?_)
      · have := hM _ (hfwd k); rw [hf] at this
        linarith [neg_abs_le (minkB (nullVec u) ((R ^ k) y)), hB1 k]
      · have := hM _ (hbwd k); rw [hb'] at this
        linarith [neg_abs_le (minkB (nullVec u) (((R⁻¹) ^ k) y)), hB2 k]
    · refine eq_zero_of_nat_mul_le (C := minkB (nullVec u) c - M + (1 + 4 * K) / 2)
        (fun k => ?_) (fun k => ?_)
      · have := hM _ (hbwd k); rw [hb'] at this
        linarith [le_abs_self (minkB (nullVec u) (((R⁻¹) ^ k) y)), hB2 k]
      · have := hM _ (hfwd k); rw [hf] at this
        linarith [le_abs_self (minkB (nullVec u) ((R ^ k) y)), hB1 k]
  -- two distinct directions orthogonal to the null `p(y)`
  obtain ⟨c₁, hc₁⟩ := eq_smul_of_null_orth hpyQ hpy0 (minkQ_nullVec u₁)
    (by rw [minkB_comm]; exact hkill u₁ hb₁)
  obtain ⟨c₂, hc₂⟩ := eq_smul_of_null_orth hpyQ hpy0 (minkQ_nullVec u₂)
    (by rw [minkB_comm]; exact hkill u₂ hb₂)
  have hc₂0 : c₂ ≠ 0 := fun h => nullVec_ne_zero u₂ (by rw [hc₂, h, zero_smul])
  exact hu (nullVec_injective_smul (c := c₁ / c₂) (by
    rw [hc₁, hc₂, smul_smul, div_mul_cancel₀ _ hc₂0]))

end Classes


/-! ## 3. The limit set is invariant; the two regular domains `Ω^±(Λ(Γ))` -/

section Invariance

/-- **Conjugation carries repulsive fixed points**: `g.w` (the action `isomPenrose` on `𝒥`,
l.829–845) is the repulsive fixed point of `g γ g⁻¹`. -/
theorem IsRepulsiveFixedJ.conj {γ : isom d} {w : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (g : isom d) :
    IsRepulsiveFixedJ (g * γ * g⁻¹) (isomPenrose g w) := by
  obtain ⟨hlox, l, hl0, hl1, -, hf⟩ := hw
  have hfun : ∀ q : Minkowski d, minkB (nullVec (isomPenrose g w).1) ((g * γ * g⁻¹) • q) -
      (isomPenrose g w).2 = l⁻¹ * (minkB (nullVec (isomPenrose g w).1) q - (isomPenrose g w).2) := by
    intro q
    obtain ⟨p, rfl⟩ : ∃ p, q = g • p := ⟨g⁻¹ • q, by rw [smul_inv_smul]⟩
    rw [show (g * γ * g⁻¹) • (g • p) = g • (γ • p) by simp [mul_smul],
      minkB_isomPenrose, minkB_isomPenrose, hf]
    ring
  refine ⟨?_, l, hl0, hl1, eigen_of_funEq hl0.ne' hfun, hfun⟩
  rw [linOf_mul, linOf_mul, linOf_inv]
  exact hlox.conj (linOf_mem g)

variable {Γ : Subgroup (isom d)}

/-- `Λ₀(Γ)` is `Γ`-invariant under the action on `𝒥`. -/
theorem isomPenrose_mem_loxRepSet {η : isom d} (hη : η ∈ Γ) {w : PenroseSphere d × ℝ}
    (hw : w ∈ loxRepSet Γ) : isomPenrose η w ∈ loxRepSet Γ := by
  obtain ⟨γ, hγ, hr⟩ := hw
  exact ⟨_, Γ.mul_mem (Γ.mul_mem hη hγ) (Γ.inv_mem hη), hr.conj η⟩

/-- The pull-back of a null half-space through an isometry. -/
theorem smul_mem_halfPlus_iff (η : isom d) (w : PenroseSphere d × ℝ) (p : Minkowski d) :
    η • p ∈ halfPlus w.1 w.2 ↔ p ∈ halfPlus (isomPenrose η⁻¹ w).1 (isomPenrose η⁻¹ w).2 := by
  rw [← isom_preimage_halfPlus η⁻¹ w, mem_preimage, inv_smul_smul]

theorem smul_mem_halfMinus_iff (η : isom d) (w : PenroseSphere d × ℝ) (p : Minkowski d) :
    η • p ∈ halfMinus w.1 w.2 ↔ p ∈ halfMinus (isomPenrose η⁻¹ w).1 (isomPenrose η⁻¹ w).2 := by
  rw [← isom_preimage_halfMinus η⁻¹ w, mem_preimage, inv_smul_smul]

theorem smul_mem_omegaPlus_loxRepSet {η : isom d} (hη : η ∈ Γ) {p : Minkowski d}
    (hp : p ∈ omegaPlus (loxRepSet Γ)) : η • p ∈ omegaPlus (loxRepSet Γ) :=
  mem_omegaPlus.2 fun w hw => mem_halfPlus.1 ((smul_mem_halfPlus_iff η w p).2
    (mem_halfPlus.2 (mem_omegaPlus.1 hp _ (isomPenrose_mem_loxRepSet (Γ.inv_mem hη) hw))))

theorem smul_mem_omegaMinus_loxRepSet {η : isom d} (hη : η ∈ Γ) {p : Minkowski d}
    (hp : p ∈ omegaMinus (loxRepSet Γ)) : η • p ∈ omegaMinus (loxRepSet Γ) :=
  mem_omegaMinus.2 fun w hw => mem_halfMinus.1 ((smul_mem_halfMinus_iff η w p).2
    (mem_halfMinus.2 (mem_omegaMinus.1 hp _ (isomPenrose_mem_loxRepSet (Γ.inv_mem hη) hw))))

theorem smul_mem_interior_of {η : isom d} {A : Set (Minkowski d)} (hA : ∀ p ∈ A, η • p ∈ A)
    {p : Minkowski d} (hp : p ∈ interior A) : η • p ∈ interior A := by
  have : interior A ⊆ (fun q => η • q) ⁻¹' interior A := by
    rw [← isom.coe_toHomeomorph, Homeomorph.preimage_interior]
    exact interior_mono fun q hq => hA q hq
  exact this hp

/-- **`Ω⁺(Λ(Γ))` is `Γ`-invariant** (`Ω⁺(Λ(Γ)) = Int Ω⁺(Λ₀)`, `blem:fermonsbis`). -/
theorem smul_mem_omegaPlus_limitSetJ {η : isom d} (hη : η ∈ Γ) {p : Minkowski d}
    (hp : p ∈ omegaPlus (limitSetJ Γ)) : η • p ∈ omegaPlus (limitSetJ Γ) := by
  rw [limitSetJ, omegaPlus_closure_eq_interior] at hp ⊢
  exact smul_mem_interior_of (fun q hq => smul_mem_omegaPlus_loxRepSet hη hq) hp

theorem smul_mem_omegaMinus_limitSetJ {η : isom d} (hη : η ∈ Γ) {p : Minkowski d}
    (hp : p ∈ omegaMinus (limitSetJ Γ)) : η • p ∈ omegaMinus (limitSetJ Γ) := by
  rw [limitSetJ, omegaMinus_closure_eq_interior] at hp ⊢
  exact smul_mem_interior_of (fun q hq => smul_mem_omegaMinus_loxRepSet hη hq) hp

/-- `Γ` preserves `Ω⁺(Λ(Γ))`, in `Flat.Examples`' form. -/
theorem preservesOmega_limitSetJ (Γ : Subgroup (isom d)) :
    PreservesOmega (limitSetJ Γ) Γ := fun γ hγ => by
  ext p
  refine ⟨fun hp => ?_, fun hp => smul_mem_omegaPlus_limitSetJ hγ hp⟩
  have := smul_mem_omegaPlus_limitSetJ (Γ.inv_mem hγ) hp
  rwa [inv_smul_smul] at this

/-- The two distinct null directions of `Λ₀(Γ)` given by one loxodromic element. -/
theorem exists_two_loxRepSet {γ : isom d} (hγ : γ ∈ Γ) (hlox : IsLoxodromic (linOf γ)) :
    ∃ w ∈ loxRepSet Γ, ∃ w' ∈ loxRepSet Γ, IsRepulsiveFixedJ γ w ∧ IsRepulsiveFixedJ γ⁻¹ w' ∧
      w.1 ≠ w'.1 := by
  obtain ⟨w, hw⟩ := exists_isRepulsiveFixedJ hlox
  obtain ⟨w', hw'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hlox)
  exact ⟨w, ⟨γ, hγ, hw⟩, w', ⟨γ⁻¹, Γ.inv_mem hγ, hw'⟩, hw, hw', hw.fst_ne hw'⟩

end Invariance

/-! ## 4. `blem:sanlox` (Lemma 10.1) -/

section Sanlox

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- **Barbot's `U_lox(Γ)`** (l.3136–3138): the intersection of the `U(γ)` over the loxodromic
elements of `Γ`. -/
def UGammaLox (Γ : Subgroup (isom d)) : Set (Minkowski d) :=
  {x | ∀ γ ∈ Γ, IsLoxodromic (linOf γ) → x ∈ Ug γ}

/-- **Barbot's `Ω_lox(Γ)`** (l.3136–3138): the interior of `U_lox(Γ)`. -/
def omegaLox (Γ : Subgroup (isom d)) : Set (Minkowski d) := interior (UGammaLox Γ)

/-- **`blem:sanlox`, the inclusion "obvious" in the paper** (l.3148): `Ω(Γ) ⊆ Ω_lox(Γ)`. -/
theorem omegaGamma_subset_omegaLox (Γ : Subgroup (isom d)) : omegaGamma Γ ⊆ omegaLox Γ :=
  interior_mono fun _ hx γ hγ hlox => hx γ hγ (ne_one_of_isLoxodromic hlox)

/-- **`blem:sanlox` in its corrected, proved form**: every `Γ`-invariant open set `Ω ⊆ U_lox(Γ)`
on which two distinct null directions are bounded on one side lies in `U(Γ)`, hence in `Ω(Γ)`
(the standing hypotheses of §8, `CCAction`, are what exclude nonspacelike elliptic and
transverse parabolic elements, Rem 8.9). The two regular domains `Ω^±(Λ(Γ))` are such sets
(`omegaPlus_limitSetJ_subset_omegaGamma`). The class analysis is Barbot's (l.3150–3165): tangent
parabolic and spacelike elliptic `γ` have `U(γ) = 𝐌ⁿ`, a linear parabolic one is excluded by
`subset_compl_nullHyperplanes_of_oneSided`. -/
theorem subset_UGamma_of_oneSided (h : CCAction Γ S) {Ω : Set (Minkowski d)} (hΩ : IsOpen Ω)
    (hinv : ∀ η ∈ Γ, ∀ p ∈ Ω, η • p ∈ Ω)
    (hlox : ∀ γ ∈ Γ, IsLoxodromic (linOf γ) → Ω ⊆ achronalDomain γ)
    {u₁ u₂ : PenroseSphere d} (hu : u₁ ≠ u₂) (hb₁ : OneSidedOn Ω u₁) (hb₂ : OneSidedOn Ω u₂) :
    Ω ⊆ UGamma Γ := by
  intro x hx γ hγ h1
  obtain ⟨hN, hT, -⟩ := nini h hγ h1
  classical
  unfold Ug
  rw [if_neg hN]
  by_cases h3 : IsLinearParabolic γ
  · rw [if_pos h3]
    exact subset_compl_nullHyperplanes_of_oneSided hΩ (hinv γ hγ) (hinv γ⁻¹ (Γ.inv_mem hγ)) hu
      hb₁ hb₂ hx
  · rw [if_neg h3]
    rcases classes_of_not lorentzTrichotomy hN h3 with hX | hX | hX | hX
    · exact hlox γ hγ hX hx
    · rw [achronalDomain_eq_univ_of_isSpacelikeElliptic hX]; trivial
    · rw [achronalDomain_eq_univ_of_isTangentParabolic hX]; trivial
    · exact (hT hX).elim

theorem oneSidedOn_omegaPlus {Λ : Set (PenroseSphere d × ℝ)} {w : PenroseSphere d × ℝ}
    (hw : w ∈ Λ) : OneSidedOn (omegaPlus Λ) w.1 :=
  Or.inl ⟨w.2, fun _ hp => (mem_omegaPlus.1 hp w hw).le⟩

theorem oneSidedOn_omegaMinus {Λ : Set (PenroseSphere d × ℝ)} {w : PenroseSphere d × ℝ}
    (hw : w ∈ Λ) : OneSidedOn (omegaMinus Λ) w.1 :=
  Or.inr ⟨w.2, fun _ hp => (mem_omegaMinus.1 hp w hw).le⟩

/-- **`Ω⁺(Λ(Γ)) ⊆ Ω(Γ)`** when `Γ` has a loxodromic element (standing hypotheses of §8). -/
theorem omegaPlus_limitSetJ_subset_omegaGamma (h : CCAction Γ S) {γ₀ : isom d} (hγ₀ : γ₀ ∈ Γ)
    (hlox₀ : IsLoxodromic (linOf γ₀)) : omegaPlus (limitSetJ Γ) ⊆ omegaGamma Γ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  refine interior_maximal (subset_UGamma_of_oneSided h (isOpen_omegaPlus_of_isClosed
    (isClosed_limitSetJ Γ)) (fun η hη p hp => smul_mem_omegaPlus_limitSetJ hη hp)
    (fun γ hγ hlox => ?_) hne (oneSidedOn_omegaPlus (subset_closure hw₁))
    (oneSidedOn_omegaPlus (subset_closure hw₂))) (isOpen_omegaPlus_of_isClosed
      (isClosed_limitSetJ Γ))
  obtain ⟨w, hw, w', hw', hr, hr', -⟩ := exists_two_loxRepSet hγ hlox
  exact fun p hp => quadrants_subset_achronalDomain hr hr' (Or.inl
    ⟨mem_halfPlus.2 (mem_omegaPlus.1 hp w (subset_closure hw)),
      mem_halfPlus.2 (mem_omegaPlus.1 hp w' (subset_closure hw'))⟩)

/-- **`Ω⁻(Λ(Γ)) ⊆ Ω(Γ)`**, likewise. -/
theorem omegaMinus_limitSetJ_subset_omegaGamma (h : CCAction Γ S) {γ₀ : isom d} (hγ₀ : γ₀ ∈ Γ)
    (hlox₀ : IsLoxodromic (linOf γ₀)) : omegaMinus (limitSetJ Γ) ⊆ omegaGamma Γ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  refine interior_maximal (subset_UGamma_of_oneSided h (isOpen_omegaMinus_of_isClosed
    (isClosed_limitSetJ Γ)) (fun η hη p hp => smul_mem_omegaMinus_limitSetJ hη hp)
    (fun γ hγ hlox => ?_) hne (oneSidedOn_omegaMinus (subset_closure hw₁))
    (oneSidedOn_omegaMinus (subset_closure hw₂))) (isOpen_omegaMinus_of_isClosed
      (isClosed_limitSetJ Γ))
  obtain ⟨w, hw, w', hw', hr, hr', -⟩ := exists_two_loxRepSet hγ hlox
  exact fun p hp => quadrants_subset_achronalDomain hr hr' (Or.inr
    ⟨mem_halfMinus.2 (mem_omegaMinus.1 hp w (subset_closure hw)),
      mem_halfMinus.2 (mem_omegaMinus.1 hp w' (subset_closure hw'))⟩)

/-- **`blem:sanlox` as printed** (l.3143–3144): `Ω_lox(Γ) = Ω(Γ)` when `Γ` contains a loxodromic
element (under the standing hypotheses of §8). -/
theorem blem_sanlox (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    omegaLox Γ = omegaGamma Γ := by
  refine Subset.antisymm ?_ (omegaGamma_subset_omegaLox Γ)
  sorry -- SORRY(blem:sanlox): the printed proof (l.3157–3165) needs `Ω_lox(Γ)` convex ("the convex domain Ω_lox(Γ)", l.3136, l.3157), and it is not: for `Γ = ⟨γ⟩` it is the union of the two disjoint quadrants `U^±(γ)` (`interior_achronalDomain_eq_quadrants`). The argument runs on any Γ-invariant open set on which two null directions are one-sided (`subset_UGamma_of_oneSided`), which covers the future and past components `Ω^±(Λ(Γ))` (`omegaPlus_limitSetJ_subset_omegaGamma`, `omegaMinus_…`), all §10 uses; for a component of `Ω_lox(Γ)` of mixed sign (in `U⁺(γ) ∩ U⁻(γ')`), a linear parabolic `γ₁ ∈ Γ` may permute the components, the γ₁-orbit of a point of `P(γ₁)` need not stay in one convex piece, and no one-sided bound is available: whether `Ω_lox(Γ) ⊆ U(γ₁)` there is open

end Sanlox


/-! ## 5. `blem:loxregular` (Lemma 10.2): `Ω(S̃)` is a regular convex domain -/

section Loxregular

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

theorem isPreconnected_omegaS (h : CCAction Γ S) : IsPreconnected (omegaS Γ S) := by
  obtain ⟨x, hx⟩ := h.nonempty
  rw [omegaS_eq h hx]; exact isPreconnected_connectedComponentIn

theorem omegaS_subset_interior_achronalDomain {γ : isom d} (hγ : γ ∈ Γ)
    (hlox : IsLoxodromic (linOf γ)) : omegaS Γ S ⊆ interior (achronalDomain γ) := by
  have hsub : UGamma Γ ⊆ achronalDomain γ := fun x hx => by
    have := hx γ hγ (ne_one_of_isLoxodromic hlox)
    rwa [Ug_eq_achronalDomain_of_isLoxodromic hlox] at this
  exact (omegaS_subset_omegaGamma Γ S).trans (interior_mono hsub)

/-- **`Ω(S̃)` lies in one of the two components `U^±(γ)`** (l.3176–3180): it is connected and lies
in the interior of the achronal domain of every loxodromic `γ ∈ Γ`. -/
theorem omegaS_subset_quadrant (h : CCAction Γ S) {γ : isom d} (hγ : γ ∈ Γ)
    {w w' : PenroseSphere d × ℝ} (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') :
    omegaS Γ S ⊆ halfPlus w.1 w.2 ∩ halfPlus w'.1 w'.2 ∨
      omegaS Γ S ⊆ halfMinus w.1 w.2 ∩ halfMinus w'.1 w'.2 := by
  have hsub := omegaS_subset_interior_achronalDomain (S := S) hγ hw.1
  rw [interior_achronalDomain_eq_quadrants hw hw'] at hsub
  exact (isPreconnected_omegaS h).subset_or_subset
    ((isOpen_halfPlus _ _).inter (isOpen_halfPlus _ _))
    ((isOpen_halfMinus _ _).inter (isOpen_halfMinus _ _))
    (Set.disjoint_left.2 fun p hp hq => lt_asymm (mem_halfPlus.1 hp.1) (mem_halfMinus.1 hq.1))
    hsub

theorem minkB_nullVec_vertical (u : PenroseSphere d) :
    minkB (nullVec u) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) = -1 := by
  simp [minkB_nullVec]

/-- **Barbot's "the reader can easily check" (l.3191–3193), filled**: for two null directions
`a.1 ≠ c.1`, some vertical (timelike) line avoids `P⁻(a) ∩ P⁺(c)`, hence `U⁺(γ₀) ∩ U⁻(γ₁)`: its
point `p` with `⟨(1,a) | p⟩ = s_a`, `⟨(1,c) | p⟩ = s_c` is below `P⁺(c)` and above `P⁻(a)`, and the
line is monotone for both. -/
theorem exists_line_avoiding {a c : PenroseSphere d × ℝ} (hac : a.1 ≠ c.1) :
    ∃ p : Minkowski d, ∀ s : ℝ, p + s • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) ∉
      halfMinus a.1 a.2 ∩ halfPlus c.1 c.2 := by
  set κ := minkB (nullVec a.1) (nullVec c.1)
  have hκ : κ < 0 := by
    simp only [κ]; rw [minkB_nullVec_nullVec]
    have : 0 < ‖((a.1 : PenroseSphere d) : EuclideanSpace ℝ (Fin d)) - c.1‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact fun h => hac (Subtype.ext h)
    have := pow_pos this 2
    linarith
  have haa : minkB (nullVec a.1) (nullVec a.1) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have hcc : minkB (nullVec c.1) (nullVec c.1) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  set p : Minkowski d := (c.2 / κ) • nullVec a.1 + (a.2 / κ) • nullVec c.1
  have e1 : minkB (nullVec a.1) p = a.2 := by
    simp only [p, minkB_add_right, minkB_smul_right, haa, mul_zero, zero_add]
    exact div_mul_cancel₀ _ hκ.ne
  have e2 : minkB (nullVec c.1) p = c.2 := by
    simp only [p, minkB_add_right, minkB_smul_right, hcc, mul_zero, add_zero]
    rw [minkB_comm]; exact div_mul_cancel₀ _ hκ.ne
  refine ⟨p, fun s ⟨h1, h2⟩ => ?_⟩
  rw [mem_halfMinus, minkB_add_right, minkB_smul_right, minkB_nullVec_vertical, e1] at h1
  rw [mem_halfPlus, minkB_add_right, minkB_smul_right, minkB_nullVec_vertical, e2] at h2
  linarith

/-- **The claim of l.3185–3194**: either `Ω(S̃) ⊆ U⁺(γ)` for every loxodromic `γ ∈ Γ` or
`Ω(S̃) ⊆ U⁻(γ)` for every one — read on the repulsive fixed points: `Ω(S̃)` lies on the future side
of every hyperplane of `Λ₀(Γ)`, or on the past side of every one. Barbot normalises to the
first by a time-reversing isometry (l.3181–3183); `isom d` is `SO₀`-affine, so both are kept. -/
theorem loxregular_sign (h : CCAction Γ S) :
    (∀ w ∈ loxRepSet Γ, omegaS Γ S ⊆ halfPlus w.1 w.2) ∨
      ∀ w ∈ loxRepSet Γ, omegaS Γ S ⊆ halfMinus w.1 w.2 := by
  by_cases hA : ∀ w ∈ loxRepSet Γ, omegaS Γ S ⊆ halfPlus w.1 w.2
  · exact Or.inl hA
  right
  intro w₁ hw₁
  by_contra hn₁
  obtain ⟨w₀, hw₀, hn₀⟩ : ∃ w ∈ loxRepSet Γ, ¬omegaS Γ S ⊆ halfPlus w.1 w.2 := by
    by_contra hc
    exact hA fun w hw => by_contra fun hn => hc ⟨w, hw, hn⟩
  obtain ⟨γ₀, hγ₀, hr₀⟩ := hw₀
  obtain ⟨γ₁, hγ₁, hr₁⟩ := hw₁
  obtain ⟨w₀', hr₀'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hr₀.1)
  obtain ⟨w₁', hr₁'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hr₁.1)
  have h0 : omegaS Γ S ⊆ halfMinus w₀.1 w₀.2 ∩ halfMinus w₀'.1 w₀'.2 :=
    (omegaS_subset_quadrant h hγ₀ hr₀ hr₀').resolve_left
      fun h' => hn₀ (h'.trans inter_subset_left)
  have h1 : omegaS Γ S ⊆ halfPlus w₁.1 w₁.2 ∩ halfPlus w₁'.1 w₁'.2 :=
    (omegaS_subset_quadrant h hγ₁ hr₁ hr₁').resolve_right
      fun h' => hn₁ (h'.trans inter_subset_left)
  have hne := hr₀.fst_ne hr₀'
  obtain ⟨b, hbS, hb⟩ : ∃ b : PenroseSphere d × ℝ, omegaS Γ S ⊆ halfMinus b.1 b.2 ∧
      b.1 ≠ w₁.1 := by
    by_cases hc : w₀.1 = w₁.1
    · exact ⟨w₀', h0.trans inter_subset_right, fun e => hne (hc.trans e.symm)⟩
    · exact ⟨w₀, h0.trans inter_subset_left, hc⟩
  obtain ⟨p, hp⟩ := exists_line_avoiding hb
  obtain ⟨s, hs⟩ := h.cc.entire.meets p _ isFutureTimelike_vertical
  exact hp s ⟨hbS (subset_omegaS h hs), (h1.trans inter_subset_left) (subset_omegaS h hs)⟩

/-- `blem:loxregular` (Lemma 10.2, l.3170–3211): `Ω(S̃)` is a regular convex domain — the
future regular domain `Ω⁺(Λ(Γ))` or (time-reversed) the past regular domain `Ω⁻(Λ(Γ))` of the
closure `Λ(Γ)` of the repulsive fixed points (l.3196–3210, with 4.6/4.8/4.9 through
`blem:fermonsbis`). Standing hypotheses of §8 (`CCAction`) and a loxodromic element. -/
theorem blem_loxregular (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    (FutureRegular (limitSetJ Γ) ∧ omegaS Γ S = omegaPlus (limitSetJ Γ)) ∨
      (PastRegular (limitSetJ Γ) ∧ omegaS Γ S = omegaMinus (limitSetJ Γ)) := by
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  have hx₀Ω := subset_omegaS h hx₀
  rcases loxregular_sign h with hF | hP
  · have hsub : omegaS Γ S ⊆ omegaPlus (limitSetJ Γ) := by
      rw [limitSetJ, omegaPlus_closure_eq_interior]
      exact interior_maximal (fun p hp => mem_omegaPlus.2 fun w hw => mem_halfPlus.1 (hF w hw hp))
        (isOpen_omegaS Γ S)
    have heq : omegaS Γ S = omegaPlus (limitSetJ Γ) := by
      refine hsub.antisymm ?_
      rw [omegaS_eq h hx₀]
      exact (convex_omegaPlus _).isPreconnected.subset_connectedComponentIn (hsub hx₀Ω)
        (omegaPlus_limitSetJ_subset_omegaGamma h hγ₀ hlox₀)
    exact Or.inl ⟨⟨⟨x₀, hsub hx₀Ω⟩, isOpen_omegaPlus_of_isClosed (isClosed_limitSetJ Γ)⟩, heq⟩
  · have hsub : omegaS Γ S ⊆ omegaMinus (limitSetJ Γ) := by
      rw [limitSetJ, omegaMinus_closure_eq_interior]
      exact interior_maximal
        (fun p hp => mem_omegaMinus.2 fun w hw => mem_halfMinus.1 (hP w hw hp))
        (isOpen_omegaS Γ S)
    have heq : omegaS Γ S = omegaMinus (limitSetJ Γ) := by
      refine hsub.antisymm ?_
      rw [omegaS_eq h hx₀]
      exact (convex_omegaMinus _).isPreconnected.subset_connectedComponentIn (hsub hx₀Ω)
        (omegaMinus_limitSetJ_subset_omegaGamma h hγ₀ hlox₀)
    exact Or.inr ⟨⟨⟨x₀, hsub hx₀Ω⟩, isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)⟩, heq⟩

/-- Barbot's intermediate form (l.3196–3203): `Ω(S̃)` is the interior of the future (or past)
complete convex domain defined by `Λ₀(Γ)` itself. -/
theorem omegaS_eq_interior (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    omegaS Γ S = interior (omegaPlus (loxRepSet Γ)) ∨
      omegaS Γ S = interior (omegaMinus (loxRepSet Γ)) := by
  rcases blem_loxregular h hlox with ⟨-, he⟩ | ⟨-, he⟩
  · exact Or.inl (by rw [he, limitSetJ, omegaPlus_closure_eq_interior])
  · exact Or.inr (by rw [he, limitSetJ, omegaMinus_closure_eq_interior])

/-- **Two null directions in `Λ(Γ)`**: `Ω⁺(Λ(Γ))` is a regular domain in Bonsante's sense
(`Flat.Cosmological`'s `CosmoRegular`) once it is future regular. -/
theorem cosmoRegular_limitSetJ {γ₀ : isom d} (hγ₀ : γ₀ ∈ Γ) (hlox₀ : IsLoxodromic (linOf γ₀))
    (hF : FutureRegular (limitSetJ Γ)) : CosmoRegular (limitSetJ Γ) := by
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  exact ⟨hF, w₁, subset_closure hw₁, w₂, subset_closure hw₂, hne⟩

end Loxregular


/-! ## 6. `bcor:loxo_proper` (Corollary 10.3): `M(S) = Γ\Ω(S̃)` -/

section LoxoProper

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- **`Γ` acts freely and properly discontinuously on `Ω`** (in `𝐌ⁿ`, with compact subsets of `Ω`;
the form of `CCAction`). -/
def ActsFreelyProperlyOn (Γ : Subgroup (isom d)) (Ω : Set (Minkowski d)) : Prop :=
  (∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ Ω, γ • x ≠ x) ∧
    ∀ K ⊆ Ω, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite

/-- A free action gives mathlib's `IsCancelSMul` on the subtype. -/
theorem isCancelSMul_of_free {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω]
    (hfree : ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ Ω, γ • x ≠ x) : IsCancelSMul Γ Ω where
  left_cancel' a b c hbc := by
    have := congrArg (fun q : Ω => a⁻¹ • q) hbc
    simpa using this
  right_cancel' a b c habc := by
    by_contra hab
    have hab' : ((b : isom d)⁻¹ * a) ≠ 1 := fun e =>
      hab (Subtype.ext (by rw [inv_mul_eq_one] at e; exact e.symm))
    refine hfree _ (Γ.mul_mem (Γ.inv_mem b.2) a.2) hab' c c.2 ?_
    have := congrArg Subtype.val habc
    simp only [FlatQuotient.coe_smul] at this
    rw [mul_smul, this, inv_smul_smul]

/-- A properly discontinuous action in `𝐌ⁿ`'s form gives mathlib's `ProperlyDiscontinuousSMul` on
the subtype. -/
theorem properlyDiscontinuousSMul_of_finite {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω]
    (hprop : ∀ K ⊆ (Ω : Set (Minkowski d)), IsCompact K →
      {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite) :
    ProperlyDiscontinuousSMul Γ Ω where
  finite_disjoint_inter_image {K L} hK hL := by
    set K' : Set (Minkowski d) := Subtype.val '' (K ∪ L)
    have hK' : IsCompact K' := (hK.union hL).image continuous_subtype_val
    have hsub : K' ⊆ Ω := by rintro _ ⟨x, -, rfl⟩; exact x.2
    refine (Set.Finite.preimage (f := fun γ : Γ => (γ : isom d))
      Subtype.val_injective.injOn (hprop K' hsub hK')).subset ?_
    rintro γ ⟨_, ⟨x, hx, rfl⟩, hxL⟩
    exact ⟨γ.2, (γ : isom d) • (x : Minkowski d),
      Set.smul_mem_smul_set ⟨x, Or.inl hx, rfl⟩, ⟨γ • x, Or.inr hxL, rfl⟩⟩

/-- **Cor 10.3, freeness** (l.3225–3226: "by definition of `Ω(S̃)`"): Prop 8.10. -/
theorem loxo_free (h : CCAction Γ S) : ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ omegaS Γ S, γ • x ≠ x :=
  fun γ hγ h1 x hx => ((bprop_ghyp h).2.2.2.2 γ hγ h1 x hx).1

/-- **Cor 10.3, proper discontinuity** (l.3222–3224, through `bprop:agissons`). -/
theorem loxo_properlyDiscontinuous (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    ∀ K ⊆ omegaS Γ S, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite := by
  sorry -- SORRY(bcor:loxo_proper): Barbot cites `bprop:agissons` (4.16: a discrete group preserving a regular domain acts properly, since it acts isometrically on the complete Riemannian level sets `S_t`), which `Flat.Cosmological` does not attempt beyond invariance (`agissons_invariant`) — it needs the Riemannian metric of `S_t` and the properness of isometry groups of a proper metric space. The cheaper route from the standing hypotheses (`CCAction.proper`, `Γ` proper on `Σ`) needs a continuous `Γ`-equivariant retraction `Ω(S̃) → Σ`: along the Gauss map `n` of the cosmological time each normal line `p + ℝ n(p)` is a timelike line, so it meets `Σ` exactly once, inside `Ω(S̃)` (`blem_loxregular`); the continuity of `n` (of `cosmoRetract`) is not stated in `Flat.Cosmological`

/-- `bcor:loxo_proper` (Cor 10.3, l.3213–3228): `Γ` acts freely and properly discontinuously
on `Ω(S̃)`, and — in the future case of `blem_loxregular`, the past one being its time reversal
(l.3181–3183, not formalized) — the quotient `M(S) = Γ\Ω(S̃)` is a flat spacetime, globally
hyperbolic in ETT's sense, with an acausal Cauchy surface: the image of a level set of the
cosmological time (`Flat.Examples`' `gh_quotient_omegaPlus`, `isCauchySurface_quotient_cosmoLevel`).
Cauchy-completeness is `loxo_cauchyComplete`. -/
theorem bcor_loxo_proper (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    ActsFreelyProperlyOn Γ (omegaS Γ S) ∧
      (omegaS Γ S = omegaPlus (limitSetJ Γ) →
        ∃ M : FlatSpacetime.{0} d, IsQuotientOf M Γ (omegaSOpens Γ S) ∧ GH M ∧
          ∃ Sc : Set M, (flatCausality d M).IsCauchySurface Sc ∧
            (flatCausality d M).IsAcausal Sc) := by
  refine ⟨⟨loxo_free h, loxo_properlyDiscontinuous h hlox⟩, fun heq => ?_⟩
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  have hF : FutureRegular (limitSetJ Γ) :=
    ⟨⟨x₀, heq ▸ subset_omegaS h hx₀⟩, isOpen_omegaPlus_of_isClosed (isClosed_limitSetJ Γ)⟩
  have hc := cosmoRegular_limitSetJ hγ₀ hlox₀ hF
  have hP := preservesOmega_limitSetJ Γ
  haveI : FlatQuotient.Invariant Γ hc.regular.opens := hP.invariant (h := hc)
  have hΩ : ((hc.regular.opens : Opens (Minkowski d)) : Set (Minkowski d)) = omegaS Γ S := heq.symm
  haveI : IsCancelSMul Γ hc.regular.opens :=
    isCancelSMul_of_free fun γ hγ h1 x hx => loxo_free h γ hγ h1 x (hΩ ▸ hx)
  haveI : ProperlyDiscontinuousSMul Γ hc.regular.opens :=
    properlyDiscontinuousSMul_of_finite fun K hK hKc =>
      loxo_properlyDiscontinuous h ⟨γ₀, hγ₀, hlox₀⟩ K (hΩ ▸ hK) hKc
  have hopens : omegaSOpens Γ S = hc.regular.opens := Opens.ext hΩ.symm
  refine ⟨FlatQuotient.toFlatSpacetime Γ hc.regular.opens (isConnected_omegaPlus hc), ?_,
    gh_quotient_omegaPlus (h := hc) hP, _,
    (isCauchySurface_quotient_cosmoLevel (h := hc) hP one_pos).1,
    (isCauchySurface_quotient_cosmoLevel (h := hc) hP one_pos).2⟩
  rw [hopens]
  exact FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _

/-- **Cor 10.3, Cauchy-completeness of `M(S)`** (l.3217–3218, through `bprop:agissons` and
`bprop:regular_cauchy_complete`). -/
theorem loxo_cauchyComplete (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ))
    {Λ : Set (PenroseSphere d × ℝ)} (hc : CosmoRegular Λ) (hΛ : omegaS Γ S = omegaPlus Λ)
    [FlatQuotient.Invariant Γ hc.regular.opens] [ProperlyDiscontinuousSMul Γ hc.regular.opens]
    [IsCancelSMul Γ hc.regular.opens] :
    IsCauchyComplete d (FlatQuotient Γ hc.regular.opens) := by
  sorry -- SORRY(bcor:loxo_proper): the completeness of the level sets `S_t` of the cosmological time for their induced length (`bcor:level_sets_complete`, l.1109–1110) and its descent to `Γ\S_t` are not attempted upstream (`Flat.Cosmological` SCOPE: `bcor:level_sets_complete` not attempted, completeness of 4.14 and 4.16 not stated); `h`, `hlox`, `hΛ` are the paper's setting

end LoxoProper

/-! ## 7. The gx exports: uniformization (`docs/BARBOT-THEOREMS.md` §3, the contract with gx) -/

section Uniformization

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
  {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

/-- **Uniformization, injectivity** (gx): the developing map is injective (Prop 8.12,
`Flat.Develop`'s `bprop_danom`). Holds with no case hypothesis. -/
theorem uniformization_injective (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S) : Injective D :=
  (bprop_danom hpair hcaus h).1

/-- **Uniformization, image** (gx): when the holonomy group `Γ = ρ(π₁)` has a loxodromic element,
`𝒟(M̃) ⊆ Ω⁺(Λ(Γ))` with `Λ(Γ)` future regular, or (time reversal) `𝒟(M̃) ⊆ Ω⁻(Λ(Γ))` with `Λ(Γ)` past
regular (Prop 8.12 and Lemma 10.2). Neither nonelementarity nor `ker L = 1` is needed. -/
theorem uniformization_image (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) :
    (FutureRegular (limitSetJ ρ.range) ∧ range D ⊆ omegaPlus (limitSetJ ρ.range)) ∨
      (PastRegular (limitSetJ ρ.range) ∧ range D ⊆ omegaMinus (limitSetJ ρ.range)) := by
  have hD := (bprop_danom hpair hcaus h).2
  rcases blem_loxregular (ccAction_of_developsCC hpair h) hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨hF, he ▸ hD⟩
  · exact Or.inr ⟨hP, he ▸ hD⟩

/-- **Uniformization, the action** (gx): `ρ(Γ)` acts freely and properly discontinuously on
`Ω⁺(Λ(Γ))` (future case) or on `Ω⁻(Λ(Γ))` (past case), which is `Ω(S̃)` (Lemma 10.2, Cor 10.3). -/
theorem uniformization_properlyDiscontinuous (hpair : IsDevelopingPair x₀ D ρ)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) :
    (FutureRegular (limitSetJ ρ.range) ∧
        omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) = omegaPlus (limitSetJ ρ.range) ∧
        ActsFreelyProperlyOn ρ.range (omegaPlus (limitSetJ ρ.range))) ∨
      (PastRegular (limitSetJ ρ.range) ∧
        omegaS ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S)) = omegaMinus (limitSetJ ρ.range) ∧
        ActsFreelyProperlyOn ρ.range (omegaMinus (limitSetJ ρ.range))) := by
  have hcc := ccAction_of_developsCC hpair h
  have hfp := (bcor_loxo_proper hcc hlox).1
  rcases blem_loxregular hcc hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨hF, he, he ▸ hfp⟩
  · exact Or.inr ⟨hP, he, he ▸ hfp⟩

/-- **Uniformization, the three exports together**, on the same side (future or past). -/
theorem uniformization (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality d M).IsCausal)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) :
    Injective D ∧
      ((FutureRegular (limitSetJ ρ.range) ∧ range D ⊆ omegaPlus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaPlus (limitSetJ ρ.range))) ∨
        (PastRegular (limitSetJ ρ.range) ∧ range D ⊆ omegaMinus (limitSetJ ρ.range) ∧
          ActsFreelyProperlyOn ρ.range (omegaMinus (limitSetJ ρ.range)))) := by
  have hD := (bprop_danom hpair hcaus h).2
  have hcc := ccAction_of_developsCC hpair h
  have hfp := (bcor_loxo_proper hcc hlox).1
  refine ⟨(bprop_danom hpair hcaus h).1, ?_⟩
  rcases blem_loxregular hcc hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨hF, he ▸ hD, he ▸ hfp⟩
  · exact Or.inr ⟨hP, he ▸ hD, he ▸ hfp⟩

end Uniformization


/-! ## 8. Elementary and nonelementary groups; Def 4.18 and the families (a), (b) -/

section Families

universe u

/-- **Nonelementary** (l.3237–3239, l.3336–3337): no finite-index subgroup of `L(Γ)` preserves an
isotropic direction (a point of `𝒮`, for the conformal action `lorentzSphere`). Its negation is
Barbot's elementary case [10.M]. -/
def IsNonelementary (Γ : Subgroup (isom d)) : Prop :=
  ∀ H : Subgroup (lorentz d), H ≤ linearImage Γ → H.relIndex (linearImage Γ) ≠ 0 →
    ¬∃ u : PenroseSphere d, ∀ A ∈ H, lorentzSphere A u = u

/-- `Ω⁺(Λ(Γ))`, as an open set (`blem:closecool`). -/
def limitOpensPlus (Γ : Subgroup (isom d)) : Opens (Minkowski d) :=
  ⟨omegaPlus (limitSetJ Γ), isOpen_omegaPlus_of_isClosed (isClosed_limitSetJ Γ)⟩

/-- `Ω⁻(Λ(Γ))`, as an open set. -/
def limitOpensMinus (Γ : Subgroup (isom d)) : Opens (Minkowski d) :=
  ⟨omegaMinus (limitSetJ Γ), isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)⟩

/-- **A future admissible representation** (l.1212–1220), in subgroup form: `Γ ≤ Isom(𝐌ⁿ)` with `L`
injective on `Γ` (so `Γ = ρ(L(Γ))`, `L ∘ ρ = id`), `L(Γ)` discrete in `SO₀(1, d)` without global
fixed point on `𝐇̄ⁿ⁻¹` (l.1212–1214), preserving a future complete regular convex domain. -/
def IsFutureAdmissible (Γ : Subgroup (isom d)) : Prop :=
  Set.InjOn linearPart (Γ : Set (isom d)) ∧ DiscreteTopology (linearImage Γ) ∧
    ¬HasGlobalFixedPoint (linearImage Γ) ∧
    ∃ Λ : Set (PenroseSphere d × ℝ), FutureRegular Λ ∧ PreservesOmega Λ Γ

/-- **A past admissible representation** (l.1216–1220): as `IsFutureAdmissible`, preserving a past
complete regular convex domain. -/
def IsPastAdmissible (Γ : Subgroup (isom d)) : Prop :=
  Set.InjOn linearPart (Γ : Set (isom d)) ∧ DiscreteTopology (linearImage Γ) ∧
    ¬HasGlobalFixedPoint (linearImage Γ) ∧
    ∃ Λ : Set (PenroseSphere d × ℝ), PastRegular Λ ∧
      ∀ γ ∈ Γ, (fun p => γ • p) ⁻¹' omegaMinus Λ = omegaMinus Λ

/-- **An admissible representation** (l.1212–1220): future or past admissible. -/
def IsAdmissible (Γ : Subgroup (isom d)) : Prop :=
  IsFutureAdmissible Γ ∨ IsPastAdmissible Γ

/-- `bdef:definitioncauchyhyp` (Def 4.18, l.1277–1281): a **Cauchy-hyperbolic spacetime** is the
quotient of `Ω^±(Λ(ρ))` by `ρ(Γ)` for an admissible `ρ`, `Λ(ρ)` the closure of the repulsive fixed
points of its loxodromic elements (`bprop:admlox`). Reading of `±`: the sign is tied to the side of
admissibility — `Ω⁺` for a future admissible, `Ω⁻` for a past admissible `ρ`. -/
def IsCauchyHyperbolic (M : FlatSpacetime.{u} d) : Prop :=
  ∃ Γ : Subgroup (isom d),
    (IsFutureAdmissible Γ ∧ IsQuotientOf M Γ (limitOpensPlus Γ)) ∨
      (IsPastAdmissible Γ ∧ IsQuotientOf M Γ (limitOpensMinus Γ))

/-- A Cauchy-hyperbolic spacetime comes from an admissible representation. -/
theorem IsCauchyHyperbolic.exists_isAdmissible {M : FlatSpacetime.{u} d}
    (hM : IsCauchyHyperbolic M) : ∃ Γ : Subgroup (isom d), IsAdmissible Γ ∧
      (IsQuotientOf M Γ (limitOpensPlus Γ) ∨ IsQuotientOf M Γ (limitOpensMinus Γ)) := by
  obtain ⟨Γ, ⟨hF, hq⟩ | ⟨hP, hq⟩⟩ := hM
  · exact ⟨Γ, Or.inl hF, Or.inl hq⟩
  · exact ⟨Γ, Or.inr hP, Or.inr hq⟩

/-- The translation vectors of `ker L ∩ Γ` (Barbot's `𝒩`, l.3407–3409). -/
def kerTranslations (Γ : Subgroup (isom d)) : Set (Minkowski d) :=
  {v | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v}

/-- A **spacelike** linear subspace: `minkQ > 0` off `0`. -/
def IsSpacelikeSubmodule (E : Submodule ℝ (Minkowski d)) : Prop :=
  ∀ v ∈ E, v ≠ 0 → 0 < minkQ v

/-- **Family (b) for a given group `Γ`: a central extension over a Cauchy-hyperbolic spacetime**
(`docs/BARBOT-THEOREMS.md` §1, DEC-44; Barbot l.3405–3456): `M = Γ\Ω` with `E` spacelike, the
translation vectors of `ker L ∩ Γ` a lattice of `E` (ball-finite, spanning `E`), `L(γ)|_E = id` for
all `γ ∈ Γ` (the extension `0 → 𝒩 → Γ → L(Γ) → 0` central), `Ω = Ω^±(Λ(Γ))` invariant under `E`, and
`L(Γ)` discrete without global fixed point (its image in `Isom(𝐌ⁿ/E)`, l.3428–3430). Its quotient by
`E` is the Cauchy-hyperbolic `M(L)` when `L(Γ)` acts freely; the fibres are the tori `E/𝒩`.
Reading: "without global fixed point" is Def 4.18's condition (l.1212–1214), not
`docs/BARBOT-THEOREMS.md` §1's "nonelementary" (which is stronger: an infinite dihedral group with a
loxodromic has no global fixed point and is elementary). -/
def IsCHCentralExtensionOf (M : FlatSpacetime.{u} d) (Γ : Subgroup (isom d)) : Prop :=
  ∃ E : Submodule ℝ (Minkowski d),
    IsSpacelikeSubmodule E ∧ Submodule.span ℝ (kerTranslations Γ) = E ∧
    (∀ R : ℝ, (kerTranslations Γ ∩ Metric.closedBall 0 R).Finite) ∧
    (∀ γ ∈ Γ, ∀ v ∈ E, linOf γ v = v) ∧
    DiscreteTopology (linearImage Γ) ∧ ¬HasGlobalFixedPoint (linearImage Γ) ∧
    ((IsQuotientOf M Γ (limitOpensPlus Γ) ∧ ∀ v ∈ E, ∀ p ∈ omegaPlus (limitSetJ Γ),
        p + v ∈ omegaPlus (limitSetJ Γ)) ∨
      (IsQuotientOf M Γ (limitOpensMinus Γ) ∧ ∀ v ∈ E, ∀ p ∈ omegaMinus (limitSetJ Γ),
        p + v ∈ omegaMinus (limitSetJ Γ)))

/-- **Family (b): a central extension over a Cauchy-hyperbolic spacetime** — `IsCHCentralExtensionOf`
for some `Γ`. -/
def IsCHCentralExtension (M : FlatSpacetime.{u} d) : Prop :=
  ∃ Γ : Subgroup (isom d), IsCHCentralExtensionOf M Γ

/-- **Family (a): the literal twisted product "Cauchy-hyperbolic × torus"** (l.3454–3456), in the
form of `docs/BARBOT-THEOREMS.md` §1: family (b) with `L(Γ)` torsion-free, for the same `Γ` —
exactly when the quotient by `E` is a manifold, the Cauchy-hyperbolic base `L(Γ)\Ω(L(Γ))`, and `M`
the bundle over it with fibre the torus `E/𝒩` and translation monodromy ((b) = (a) iff `L(Γ)` is
torsion-free). -/
def IsCHTorusProduct (M : FlatSpacetime.{u} d) : Prop :=
  ∃ Γ : Subgroup (isom d), IsCHCentralExtensionOf M Γ ∧
    ∀ γ ∈ Γ, IsOfFinOrder (linOf γ) → linOf γ = 1

/-- Family (a) is a case of family (b). -/
theorem IsCHTorusProduct.isCHCentralExtension {M : FlatSpacetime.{u} d}
    (hM : IsCHTorusProduct M) : IsCHCentralExtension M :=
  let ⟨Γ, hΓ, _⟩ := hM
  ⟨Γ, hΓ⟩

end Families

/-! ## 9. [10.M] The elementary case: Misner spacetimes -/

section Misner

/-- **[10.M] (l.3235–3330): the elementary loxodromic case, up to finite index.** If, up to finite
index, `L(Γ)` preserves an isotropic direction and `Γ` has a loxodromic element, then for a
finite-index subgroup `Γ' ≤ Γ` the quotient `B = Γ'\Ω(S̃)` is a linear twisted product over a Misner
spacetime — with an element of nonzero boost parameter (finding F1). This is DEC-43's R1 (a finite
cover of `M(S)`); the paper states the conclusion for `Γ` itself (l.3326–3330), which fails (finding:
in `𝐌⁴` the group generated by a boost `γ₀` and a glide `σ(x,z₁,z₂,y) = (−y, z₁+1, −z₂, −x)` with
`σγ₀σ⁻¹ = γ₀⁻¹` is elementary up to index 2, satisfies `CCAction` on `{x > 0, y < 0} × ℝ²`, and its
restriction to the direction of `U` is non-abelian, while a Misner group is abelian). `d = d' + 1`
(`IsMisnerSpacetime` lives in `Minkowski (d' + 1)`); the Misner base has dimension
`d₁ + 1 ≤ d' + 1`. -/
theorem loxo_elementary_misner {d' : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski (d' + 1)) M]
    [HasGroupoid M (gxGroupoid (isom (d' + 1)) (Minkowski (d' + 1)))] {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski (d' + 1)}
    {ρ : Deck (UniversalCover.proj M x₀) →* isom (d' + 1)} {S : Set M}
    (hpair : IsDevelopingPair x₀ D ρ) (hcaus : (flatCausality (d' + 1) M).IsCausal)
    (h : DevelopsCC x₀ D S) (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ))
    (helem : ¬IsNonelementary ρ.range) :
    ∃ Γ' : Subgroup (isom (d' + 1)), Γ' ≤ ρ.range ∧ Γ'.relIndex ρ.range ≠ 0 ∧
      ∃ B : FlatSpacetime.{0} (d' + 1),
        IsQuotientOf B Γ' (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))) ∧
        ∃ (d₁ : ℕ) (M₁ : FlatSpacetime.{0} (d₁ + 1)), d₁ ≤ d' ∧ IsLTPOver B M₁ ∧
          IsMisnerSpacetime M₁ := by
  sorry -- SORRY([10.M]): l.3237–3330 is a chain of unproved steps: the finite-index reduction to `L(Γ)` fixing `Δ₀` and the second fixed direction `Δ₁` of `γ₀`; the induced action on `Q₀` and `b ≡ 0` (l.3250–3257); `Γ₀ = ker a` discrete and elliptic (the conjugation formula l.3264–3269); its nondiscrete part `Γ₀^nd`, the maximal unipotent `U` (Carrière–Dal'bo, `bthm:unip`) and "we recover the purely unipotent case" (§9, `Flat.Nonloxodromic`, in progress in this run); `blem:suspendre` (`Flat.TwistedProduct`, under its `RestrictsIn` hypothesis); `L(Γ₀)` finite and the totally geodesic `𝓗` of its fixed points (l.3286–3299); the normal form `γ(x,z,y) = (e^{-a}x, Rz + u, e^{a}y)` and finally "an appropriate use of Bieberbach's theorem" (l.3327, gap G7). Steps 1–2 rest on `blem_loxregular`'s quadrant description (proved here); the rest needs the §9 machinery and Bieberbach-light

end Misner

/-! ## 10. `bprop:U_timelike` (Prop 10.4), `bprop:LU_discrete` (Prop 10.5) -/

section UTimelike

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}


/-- A nonzero null vector spans the null direction of a point of `𝒮`. -/
theorem exists_nullVec_eq_smul {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) :
    ∃ (u : PenroseSphere d) (c : ℝ), c ≠ 0 ∧ nullVec u = c • e := by
  have he1 : e.1 ≠ 0 := fun h0 => he0 (eq_zero_of_fst_eq_zero h0 he.le)
  have hnorm : ‖e.2‖ = |e.1| := by
    have h2 : ‖e.2‖ ^ 2 = |e.1| ^ 2 := by
      have := he; simp only [minkQ] at this; rw [sq_abs]; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 h2
  refine ⟨⟨e.1⁻¹ • e.2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, hnorm,
      inv_mul_cancel₀ (abs_ne_zero.2 he1)]⟩, e.1⁻¹, inv_ne_zero he1, ?_⟩
  refine Prod.ext ?_ rfl
  simp [nullVec, inv_mul_cancel₀ he1]

/-- **Prop 10.4, the lightlike case** (l.3352–3353): a `Γ`-invariant affine subspace whose direction
contains a nonzero null vector and no timelike one has a unique isotropic direction, which `L(Γ)`
preserves: `Γ` is elementary. -/
theorem not_isNonelementary_of_lightlike {U : AffineSubspace ℝ (Minkowski d)}
    (hUne : (U : Set (Minkowski d)).Nonempty)
    (hinv : ∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) {v₀ : Minkowski d}
    (hv₀ : v₀ ∈ U.direction) (hv0 : v₀ ≠ 0) (hq : minkQ v₀ = 0) (hnt : ¬IsTimelikeSubspace U) :
    ¬IsNonelementary Γ := by
  obtain ⟨p, hp⟩ := hUne
  -- every null vector of the direction is a multiple of `v₀`
  have huniq : ∀ w ∈ U.direction, minkQ w = 0 → ∃ c : ℝ, w = c • v₀ := by
    intro w hw hwq
    refine eq_smul_of_null_orth hq hv0 hwq ?_
    by_contra hB
    set B := minkB v₀ w
    have ht : minkQ (v₀ + (-B) • w) < 0 := by
      rw [minkQ_add, minkQ_smul, hwq, hq, minkB_smul_right]
      nlinarith [sq_pos_of_ne_zero hB]
    exact hnt ⟨_, U.direction.add_mem hv₀ (U.direction.smul_mem _ hw), ht⟩
  -- `L(γ)` preserves the direction
  have hdir : ∀ γ ∈ Γ, ∀ w ∈ U.direction, linOf γ w ∈ U.direction := by
    intro γ hγ w hw
    obtain ⟨p₂, hp₂, rfl⟩ := (AffineSubspace.mem_direction_iff_eq_vsub_right hp w).1 hw
    rw [vsub_eq_sub, ← smul_sub_smul, ← vsub_eq_sub]
    exact AffineSubspace.vsub_mem_direction ((hinv γ hγ p₂).2 hp₂) ((hinv γ hγ p).2 hp)
  obtain ⟨u, c, hc0, hu⟩ := exists_nullVec_eq_smul hv0 hq
  intro hne
  refine hne (linearImage Γ) le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) ⟨u, ?_⟩
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨a, ha⟩ := huniq _ (hdir γ hγ v₀ hv₀)
    (by rw [lorentz.minkQ_apply (linOf_mem γ), hq])
  refine lorentzSphere_eq_of_eigen (c := a) ?_
  rw [← linOf_eq_linearPart, hu, map_smul, ha, smul_comm]

/-- `bprop:U_timelike` (Prop 10.4, l.3346–3362): in the nonelementary case, the maximal
`Γ_nd`-unipotent affine subspace `U` (`bthm:ausl`, `bthm:unip`) is timelike. Its nonemptiness and
`Γ`-invariance ("being unique", l.3343–3344) are derived from the uniqueness in `bthm:unip`
(`exists_invariant_maxUnipotent`), not assumed. -/
theorem bprop_U_timelike (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d)
    (hΓ : DiscreteTopology Γ) (h : CCAction Γ S) (hne : IsNonelementary Γ)
    {U : AffineSubspace ℝ (Minkowski d)} (hmax : IsMaxUnipotent (nonDiscretePart Γ) U) :
    IsTimelikeSubspace U := by
  -- "Being unique, `U` is also preserved by `Γ`" (l.3343–3344)
  obtain ⟨U₀, hUne, hmax₀, hinv⟩ := exists_invariant_maxUnipotent hA hU hΓ
  obtain ⟨U₁, -, -, huniq⟩ := hU _ (hA Γ hΓ).2
  obtain rfl : U = U₀ := (huniq U hmax).trans (huniq U₀ hmax₀).symm
  by_contra hnt
  by_cases hnull : ∃ v ∈ U.direction, v ≠ 0 ∧ minkQ v = 0
  · obtain ⟨v, hv, hv0, hq⟩ := hnull
    exact not_isNonelementary_of_lightlike hUne hinv hv hv0 hq hnt hne
  sorry -- SORRY(bprop:U_timelike): the lightlike case is closed above (`not_isNonelementary_of_lightlike`). Spacelike `U` (l.3355–3362): "according to corollary `abel`, a finite index subgroup of `Γ` is abelian" — `bcor:abel` (Cor 8.4) is not formalized (`docs/BARBOT.md`: G-class, "a step is under-justified, since Δ need not be Γ-invariant", W9); and the folklore used next is false as printed (`Flat.Externals`' `not_abelianPairAsPrinted`), its true form needing the trichotomy for abelian groups

/-- `bprop:LU_discrete` (Prop 10.5, l.3367–3388): `L_U(Γ)`, the linear parts of the restrictions
of `Γ` to the (timelike, Prop 10.4) maximal unipotent subspace `U`, is discrete. `U` is given through
a parametrization `ι : 𝐌^{d₁+1} → 𝐌ⁿ` on which every element of `Γ` restricts to an isometry
(`RestrictsIn`, as in `Flat.TwistedProduct`), and `L_U(Γ)` is the linear image of the restricted
group. -/
theorem bprop_LU_discrete (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d)
    (hΓ : DiscreteTopology Γ) (h : CCAction Γ S) (hne : IsNonelementary Γ)
    {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) (hmax : IsMaxUnipotent (nonDiscretePart Γ) ι.range)
    (hres : ι.RestrictsIn Γ) : DiscreteTopology (linearImage (ι.restrictGroup Γ)) := by
  sorry -- SORRY(bprop:LU_discrete): l.3372–3388: "the closure of `L_U(Γ)` in `SO₀(U)` is the restriction to `U` of the closure of `L(Γ)`" (the action on `𝐌ⁿ/U` being euclidean), then the identity component of that closure lies in `L_U(Γ_nd)` (Auslander–Carrière–Dal'bo), is nilpotent without elliptic part, and a central parabolic or hyperbolic element of it gives an `L(Γ)`-invariant isotropic direction or pair of directions. Needs closures of restricted groups, centres of nilpotent closed subgroups of `SO₀(1, d₁)` and their elements' classes: none is in the library

end UTimelike

/-! ## 11. [10.G] The nonelementary case -/

section Generic

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- **[10.G], l.3398–3403: `Ω(S̃)` is Def 4.18's regular domain `Ω^±(Λ(ρ))`** — `blem_loxregular`
restated: the domain of the Cauchy-hyperbolic spacetime of `Γ` (when `Γ` is admissible). -/
theorem generic_omegaS_eq (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    (omegaSOpens Γ S = limitOpensPlus Γ ∧ FutureRegular (limitSetJ Γ)) ∨
      (omegaSOpens Γ S = limitOpensMinus Γ ∧ PastRegular (limitSetJ Γ)) := by
  rcases blem_loxregular h hlox with ⟨hF, he⟩ | ⟨hP, he⟩
  · exact Or.inl ⟨Opens.ext he, hF⟩
  · exact Or.inr ⟨Opens.ext he, hP⟩

/-- **[10.G], l.3407–3408: the elements of `𝒩 = ker L` are translations by spacelike vectors.**
A causal translation `x ↦ x + v` would send a point of `Ω(S̃)` into its own causal future,
against Prop 8.10. -/
theorem kerTranslations_spacelike (h : CCAction Γ S) {v : Minkowski d}
    (hv : v ∈ kerTranslations Γ) (hv0 : v ≠ 0) : 0 < minkQ v := by
  obtain ⟨γ, hγ, hL, rfl⟩ := hv
  have hsm : ∀ x, γ • x = x + trOf γ := fun x => by rw [smul_eq_lin_add, hL]; rfl
  have h1 : γ ≠ 1 := fun e => hv0 (by
    have := hsm 0; rw [zero_add] at this; rw [← this, e, one_smul])
  obtain ⟨x, hx⟩ := h.nonempty
  have hxΩ := subset_omegaS h hx
  have hach := (bprop_ghyp h).2.2.2.2
  by_contra hle
  rcases isFutureCausal_or_neg_of_minkQ_nonpos (not_lt.1 hle) with hc | hc
  · exact (hach γ hγ h1 x hxΩ).2 (le_top_iff_minkQ.2 (by rw [hsm, add_sub_cancel_left]; exact hc))
  · have hsm' : γ⁻¹ • x = x + -trOf γ := by
      rw [inv_smul_eq_iff, hsm]; abel
    exact (hach γ⁻¹ (Γ.inv_mem hγ) (inv_ne_one.2 h1) x hxΩ).2
      (le_top_iff_minkQ.2 (by rw [hsm', add_sub_cancel_left]; exact hc))

/-- **[10.G], l.3409: the translation vectors of `𝒩` are discrete** (finitely many in each ball),
from the proper discontinuity of `Γ` on `Σ` (`CCAction.proper`). -/
theorem kerTranslations_ballFinite (h : CCAction Γ S) (R : ℝ) :
    (kerTranslations Γ ∩ Metric.closedBall 0 R).Finite := by
  obtain ⟨x, hx⟩ := h.nonempty
  obtain ⟨f, hf, hfS⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
  have hSc : IsClosed S := by rw [hfS]; exact isClosed_graph hf.lipschitzWith.continuous
  set K := S ∩ Metric.closedBall x R
  have hK : IsCompact K := (isCompact_closedBall x R).inter_left hSc
  refine ((h.proper K inter_subset_left hK).image trOf).subset ?_
  rintro v ⟨⟨γ, hγ, hL, rfl⟩, hvR⟩
  have hsm : γ • x = x + trOf γ := by rw [smul_eq_lin_add, hL]; rfl
  have hR : ‖trOf γ‖ ≤ R := by simpa using hvR
  have hxK : x ∈ K := ⟨hx, Metric.mem_closedBall_self ((norm_nonneg _).trans hR)⟩
  have hγxK : γ • x ∈ K := ⟨h.smul_mem hγ hx, by
    rw [Metric.mem_closedBall, hsm, dist_eq_norm, add_sub_cancel_left]; exact hR⟩
  exact ⟨γ, ⟨hγ, γ • x, Set.smul_mem_smul_set hxK, hγxK⟩, rfl⟩

/-- **[10.G], l.3432–3435: `Ω(S̃)` is invariant under the translations by `E = span 𝒩`** — it is
convex and invariant under the lattice `𝒩`, and a convex set invariant under `±v` is invariant
under `ℝ v`. -/
theorem omegaS_add_mem_span (h : CCAction Γ S) {v : Minkowski d}
    (hv : v ∈ Submodule.span ℝ (kerTranslations Γ)) {p : Minkowski d} (hp : p ∈ omegaS Γ S) :
    p + v ∈ omegaS Γ S := by
  have hconv := (bprop_ghyp h).2.1
  set Ω := omegaS Γ S
  -- the translations preserving `Ω` in both directions form a submodule
  let T : Submodule ℝ (Minkowski d) :=
    { carrier := {v | ∀ p ∈ Ω, p + v ∈ Ω ∧ p - v ∈ Ω}
      add_mem' := by
        intro a b ha hb p hp
        refine ⟨?_, ?_⟩
        · rw [← add_assoc]; exact (hb _ (ha p hp).1).1
        · rw [sub_add_eq_sub_sub]; exact (hb _ (ha p hp).2).2
      zero_mem' := fun p hp => by simpa using hp
      smul_mem' := by
        intro t a ha p hp
        have hnat : ∀ n : ℕ, ∀ q ∈ Ω, q + (n : ℝ) • a ∈ Ω ∧ q - (n : ℝ) • a ∈ Ω := by
          intro n; induction n with
          | zero => intro q hq; simpa using hq
          | succ n ih =>
            intro q hq
            obtain ⟨h1, h2⟩ := ih q hq
            push_cast
            refine ⟨?_, ?_⟩
            · rw [add_smul, one_smul, ← add_assoc]; exact (ha _ h1).1
            · rw [add_smul, one_smul, sub_add_eq_sub_sub]; exact (ha _ h2).2
        have key : ∀ s : ℝ, ∀ q ∈ Ω, q + s • a ∈ Ω := by
          intro s q hq
          obtain ⟨n, hn⟩ := exists_nat_gt |s|
          have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs_nonneg s) hn
          rcases le_total 0 s with hs | hs
          · have := hconv.add_smul_mem hq (hnat n q hq).1 (t := s / n)
              ⟨div_nonneg hs hn0.le, (div_le_one hn0).2 (by
                rw [abs_of_nonneg hs] at hn; exact hn.le)⟩
            rwa [smul_smul, div_mul_cancel₀ _ hn0.ne'] at this
          · have h2 : q + (n : ℝ) • (-a) ∈ Ω := by
              rw [smul_neg, ← sub_eq_add_neg]; exact (hnat n q hq).2
            have := hconv.add_smul_mem hq h2 (t := -s / n)
              ⟨div_nonneg (by linarith) hn0.le, (div_le_one hn0).2 (by
                rw [abs_of_nonpos hs] at hn; exact hn.le)⟩
            rwa [smul_smul, div_mul_cancel₀ _ hn0.ne', smul_neg, neg_smul, neg_neg] at this
        exact ⟨key t p hp, by rw [sub_eq_add_neg, ← neg_smul]; exact key (-t) p hp⟩ }
  have hsub : kerTranslations Γ ⊆ T := by
    rintro _ ⟨γ, hγ, hL, rfl⟩ q hq
    have hsm : ∀ x, γ • x = x + trOf γ := fun x => by rw [smul_eq_lin_add, hL]; rfl
    have h1 : γ • q ∈ Ω := (smul_omegaS h hγ).subset (Set.smul_mem_smul_set hq)
    have h2 : γ⁻¹ • q ∈ Ω := (smul_omegaS h (Γ.inv_mem hγ)).subset (Set.smul_mem_smul_set hq)
    refine ⟨by rw [← hsm]; exact h1, ?_⟩
    have : γ⁻¹ • q = q - trOf γ := by rw [inv_smul_eq_iff, hsm]; abel
    rw [← this]; exact h2
  exact ((Submodule.span_le.2 hsub) hv p hp).1

/-- **[10.G]: `E = span 𝒩` is spacelike.** Barbot asserts it (l.3409) without argument, and it does
not follow from the vectors of `𝒩` being spacelike (a lattice in a degenerate plane can consist of
spacelike vectors only). It follows from `blem:loxregular`: `Ω(S̃)` is invariant under `ℝ v` for
`v ∈ E` and lies on one side of every hyperplane of `Λ₀(Γ)`, so `v` is orthogonal to two distinct
null directions — impossible for a nonzero causal `v`. -/
theorem span_kerTranslations_spacelike (h : CCAction Γ S)
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    IsSpacelikeSubmodule (Submodule.span ℝ (kerTranslations Γ)) := by
  intro v hv hv0
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  obtain ⟨x, hx⟩ := h.nonempty
  have hxΩ := subset_omegaS h hx
  have hline : ∀ t : ℝ, x + t • v ∈ omegaS Γ S := fun t =>
    omegaS_add_mem_span h (Submodule.smul_mem _ t hv) hxΩ
  -- `⟨n_w | v⟩ = 0` for `w ∈ Λ₀`
  have hkill : ∀ w ∈ loxRepSet Γ, minkB (nullVec w.1) v = 0 := by
    intro w hw
    by_contra hB
    have hbd : (∀ t : ℝ, minkB (nullVec w.1) (x + t • v) < w.2) ∨
        ∀ t : ℝ, w.2 < minkB (nullVec w.1) (x + t • v) := by
      rcases loxregular_sign h with hF | hP
      · exact Or.inl fun t => mem_halfPlus.1 (hF w hw (hline t))
      · exact Or.inr fun t => mem_halfMinus.1 (hP w hw (hline t))
    have e : ∀ t : ℝ, minkB (nullVec w.1) (x + t • v) =
        minkB (nullVec w.1) x + t * minkB (nullVec w.1) v := fun t => by
      rw [minkB_add_right, minkB_smul_right]
    set β := minkB (nullVec w.1) v
    set a := minkB (nullVec w.1) x
    have ht : a + (w.2 - a) / β * β = w.2 := by rw [div_mul_cancel₀ _ hB]; ring
    rcases hbd with hb | hb
    · have := hb ((w.2 - a) / β); rw [e, ht] at this; exact lt_irrefl _ this
    · have := hb ((w.2 - a) / β); rw [e, ht] at this; exact lt_irrefl _ this
  have h1 := hkill w₁ hw₁
  have h2 := hkill w₂ hw₂
  have key : ∀ u : Minkowski d, u ≠ 0 → IsFutureCausal u → minkB (nullVec w₁.1) u = 0 →
      minkB (nullVec w₂.1) u = 0 → False := by
    intro u hu0 hc hu1 hu2
    rcases lt_or_eq_of_le hc.2 with hq | hq
    · have := minkB_neg_of_isFutureTimelike ⟨lt_of_le_of_ne hc.1 (fun e =>
        hu0 (eq_zero_of_fst_eq_zero e.symm hc.2)), hq⟩ (isFutureCausal_nullVec w₁.1)
        (nullVec_ne_zero w₁.1)
      rw [minkB_comm] at this; linarith
    · obtain ⟨c₁, hc₁⟩ := eq_smul_of_null_orth hq hu0 (minkQ_nullVec w₁.1)
        (by rw [minkB_comm]; exact hu1)
      obtain ⟨c₂, hc₂⟩ := eq_smul_of_null_orth hq hu0 (minkQ_nullVec w₂.1)
        (by rw [minkB_comm]; exact hu2)
      have hc₂0 : c₂ ≠ 0 := fun e => nullVec_ne_zero w₂.1 (by rw [hc₂, e, zero_smul])
      exact hne (nullVec_injective_smul (c := c₁ / c₂) (by
        rw [hc₁, hc₂, smul_smul, div_mul_cancel₀ _ hc₂0]))
  by_contra hle
  rcases isFutureCausal_or_neg_of_minkQ_nonpos (not_lt.1 hle) with hc | hc
  · exact key v hv0 hc h1 h2
  · exact key (-v) (neg_ne_zero.2 hv0) hc (by rw [minkB_neg_right, h1, neg_zero])
      (by rw [minkB_neg_right, h2, neg_zero])


/-- **[10.G], l.3410–3415: conjugation acts on `𝒩` linearly**: `γ t_v γ⁻¹ = t_{L(γ) v}`, so
`L(Γ)` preserves the translation vectors of `𝒩`. -/
theorem linOf_mem_kerTranslations {γ : isom d} (hγ : γ ∈ Γ) {v : Minkowski d}
    (hv : v ∈ kerTranslations Γ) : linOf γ v ∈ kerTranslations Γ := by
  obtain ⟨t, ht, hL, rfl⟩ := hv
  have hsm : ∀ x, t • x = x + trOf t := fun x => by rw [smul_eq_lin_add, hL]; rfl
  have hη : ∀ x, (γ * t * γ⁻¹) • x = x + linOf γ (trOf t) := fun x => by
    rw [mul_smul, mul_smul, hsm, show γ⁻¹ • x + trOf t = γ⁻¹ • x + (1 : ℝ) • trOf t by
      rw [one_smul], isom_smul_add_smul, smul_inv_smul, one_smul]
  refine ⟨γ * t * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ ht) (Γ.inv_mem hγ), ?_, ?_⟩
  · rw [linOf_mul, linOf_mul, hL, mul_one, linOf_inv, mul_inv_cancel]
  · show (γ * t * γ⁻¹) • (0 : Minkowski d) = _
    rw [hη, zero_add]

end Generic

section GenericConclusion

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))] {x₀ : M}
  {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
  {S : Set M}

/-- **[10.G], the conclusion in the central-extension form (b)** (l.3416–3456; DEC-43's R1, DEC-44):
in the nonelementary loxodromic case, a finite-index subgroup `Γ' ≤ Γ` (on which conjugation acts
trivially on `𝒩`) gives `B = Γ'\Ω(S̃)`, a linear twisted product (over the timelike `U` of
Prop 10.4, `blem:suspendre`) over a spacetime of family (b). -/
theorem loxo_generic_centralExtension (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) (hne : IsNonelementary ρ.range)
    (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ ρ.range ∧ Γ'.relIndex ρ.range ≠ 0 ∧
      ∃ B : FlatSpacetime.{0} d,
        IsQuotientOf B Γ' (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))) ∧
        ∃ (d₁ : ℕ) (M₁ : FlatSpacetime.{0} d₁), d₁ ≤ d ∧ IsLTPOver B M₁ ∧
          IsCHCentralExtension M₁ := by
  sorry -- SORRY([10.G]): proved here are the pieces that hold in `𝐌ⁿ`: `Ω(S̃) = Ω^±(Λ(Γ))` (`generic_omegaS_eq`), `𝒩` spacelike, discrete and `L(Γ)`-stable (`kerTranslations_spacelike`, `_ballFinite`, `linOf_mem_kerTranslations`), `E = span 𝒩` spacelike (`span_kerTranslations_spacelike`, a step the paper does not justify) and `Ω(S̃) + E = Ω(S̃)` (`omegaS_add_mem_span`). Missing: Prop 10.4/10.5 (`bprop_U_timelike`, `bprop_LU_discrete`, sorries) and `blem:suspendre` to reduce to `U = 𝐌ⁿ` (l.3391–3396, gap G6 for `Ω(S̃)`); the finite-index subgroup on which `L(Γ)|_E` is trivial (a finite group of isometries of the lattice `𝒩`, Bieberbach's `finite_latticeStab`, with the lattice structure of `𝒩` in `E` built from ball-finiteness); the quotient `𝐌ⁿ/E` as a Minkowski space `Minkowski d₁` (an orthochronous `AffineMinkEmbedding` onto `E^⊥`, not built) carrying the discrete group `L(Γ)` with `p(Ω(S̃))` its regular domain (l.3436–3446, "it should be clear to the reader"); and the quotient `M(S) = Γ'\Ω(S̃)` itself, which needs Cor 10.3's proper discontinuity (`loxo_properlyDiscontinuous`, sorry)

/-- **[10.G], family (a) under "`π₁` finitely generated"** (DEC-44, finding F2/gap G5): through
Selberg's lemma (a named external, `Flat.Externals`), a further finite-index subgroup has
torsion-free linear part, and family (b) with `L(Γ)` torsion-free is the literal
"Cauchy-hyperbolic × torus" (a). -/
theorem loxo_generic_torusProduct (hpair : IsDevelopingPair x₀ D ρ)
    (hcaus : (flatCausality d M).IsCausal) (h : DevelopsCC x₀ D S)
    (hlox : ∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)) (hne : IsNonelementary ρ.range)
    (hA : AuslanderCarriereDalbo d) (hU : MaxUnipotentSubspace d)
    (hS : SelbergLemma (Minkowski d)) (hfg : ρ.range.FG) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ ρ.range ∧ Γ'.relIndex ρ.range ≠ 0 ∧
      (∀ γ ∈ Γ', IsOfFinOrder (linOf γ) → linOf γ = 1) ∧
      ∃ B : FlatSpacetime.{0} d,
        IsQuotientOf B Γ' (omegaSOpens ρ.range (D '' (UniversalCover.proj M x₀ ⁻¹' S))) ∧
        ∃ (d₁ : ℕ) (M₁ : FlatSpacetime.{0} d₁), d₁ ≤ d ∧ IsLTPOver B M₁ ∧ IsCHTorusProduct M₁ := by
  obtain ⟨Γ₁, hle₁, hidx₁, htf₁⟩ := exists_finiteIndex_torsionFree_linOf hS hfg
  sorry -- SORRY([10.G]): Selberg's step is done (`Γ₁`, from `exists_finiteIndex_torsionFree_linOf`); what remains is `loxo_generic_centralExtension` run for the finite-index `Γ' ⊓ Γ₁` (its own sorry), whose linear part is then torsion-free, which is `IsCHTorusProduct` by definition

end GenericConclusion

/-! ## 12. `bprop:admlox` (Prop 4.17) in `𝒥`: invariance, and the link with `Flat.Externals` -/

section Admlox

variable {Γ : Subgroup (isom d)}

theorem continuous_isomPenrose (g : isom d) : Continuous (isomPenrose g) := by
  have h1 : Continuous fun w : PenroseSphere d × ℝ => lorentzSphere (linearPart g) w.1 :=
    (continuous_lorentzSphere _).comp continuous_fst
  have h2 : Continuous fun w : PenroseSphere d × ℝ => (lorentzScale (linearPart g) w.1)⁻¹ * w.2 :=
    (((continuous_lorentzScale _).comp continuous_fst).inv₀
      fun w => (lorentzScale_pos _ _).ne').mul continuous_snd
  have h3 : Continuous fun w : PenroseSphere d × ℝ =>
      minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski d)) :=
    (continuous_minkB_nullVec_param (g • (0 : Minkowski d))).comp
      (h1.prodMk (continuous_const (y := (0 : ℝ))))
  exact h1.prodMk (h2.add h3)

/-- **`bprop:admlox`, invariance** (l.1232–1236): `Λ(Γ)` is `Γ`-invariant in `𝒥`. -/
theorem isomPenrose_image_limitSetJ_subset {η : isom d} (hη : η ∈ Γ) :
    isomPenrose η '' limitSetJ Γ ⊆ limitSetJ Γ :=
  (image_closure_subset_closure_image (continuous_isomPenrose η)).trans
    (closure_mono (by rintro _ ⟨w, hw, rfl⟩; exact isomPenrose_mem_loxRepSet hη hw))

/-- On `𝒮`, a repulsive fixed point in `𝒥` is Externals' repulsive fixed point. -/
theorem IsRepulsiveFixedJ.isRepulsiveFixed {γ : isom d} {w : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) : IsRepulsiveFixed (linearPart γ) w.1 := by
  obtain ⟨hlox, l, hl0, hl1, hAn, -⟩ := hw
  refine ⟨by rw [← linOf_eq_linearPart]; exact hlox, l, hl0, hl1, ?_⟩
  rw [← linOf_eq_linearPart]; exact hAn

theorem fst_image_loxRepSet_subset (Γ : Subgroup (isom d)) :
    Prod.fst '' loxRepSet Γ ⊆ repulsiveSet (linearImage Γ) := by
  rintro _ ⟨w, ⟨γ, hγ, hw⟩, rfl⟩
  exact ⟨linearPart γ, ⟨γ, hγ, rfl⟩, hw.isRepulsiveFixed⟩

/-- **`bprop:admlox` on `𝒮`** (through `Flat.Externals`' `LimitSetMinimal`): `δ(Λ(Γ))` lies in every
nonempty closed `L(Γ)`-invariant subset of `𝒮`. -/
theorem fst_image_limitSetJ_subset (hL : LimitSetMinimal d) (hΓ : DiscreteTopology (linearImage Γ))
    (hfix : ¬HasGlobalFixedPoint (linearImage Γ)) {F : Set (PenroseSphere d)} (hF : IsClosed F)
    (hne : F.Nonempty) (hinv : IsSphereInvariant (linearImage Γ) F) :
    Prod.fst '' limitSetJ Γ ⊆ F := by
  have h1 : Prod.fst '' limitSetJ Γ ⊆ closure (Prod.fst '' loxRepSet Γ) :=
    image_closure_subset_closure_image continuous_fst
  exact h1.trans (closure_minimal ((fst_image_loxRepSet_subset Γ).trans
    (hL _ hΓ hfix F hF hne hinv)) hF)

/-- `minkQ` is positive semidefinite on the orthogonal of a nonzero null vector `n`
(`minkQ_nonneg_of_null_orth`), so there `|⟨v | z⟩| ≤ (|v|² + |z|²)/2`. -/
theorem abs_minkB_le_of_null_orth {n v z : Minkowski d} (hn : minkQ n = 0) (hn0 : n ≠ 0)
    (hv : minkB n v = 0) (hz : minkB n z = 0) : |minkB v z| ≤ (minkQ v + minkQ z) / 2 := by
  have h1 := (minkQ_nonneg_of_null_orth hn hn0 (w := v + z)
    (by rw [minkB_add_right, hv, hz, add_zero])).1
  have h2 := (minkQ_nonneg_of_null_orth hn hn0 (w := v - z)
    (by rw [minkB_sub_right, hv, hz, sub_zero])).1
  rw [minkQ_eq_minkB] at h1 h2
  rw [minkQ_eq_minkB v, minkQ_eq_minkB z]
  simp only [minkB_add_left, minkB_add_right, minkB_sub_left, minkB_sub_right] at h1 h2
  rw [minkB_comm z v] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- The functional equation of `w` along `γ` makes `nullVec w.1` an eigenvector of every `L(γᵏ)`. -/
theorem linOf_pow_nullVec_of_funEq {γ : isom d} {w : PenroseSphere d × ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ p, minkB (nullVec w.1) (γ • p) - w.2 = c⁻¹ * (minkB (nullVec w.1) p - w.2)) (k : ℕ) :
    linOf (γ ^ k) (nullVec w.1) = c ^ k • nullVec w.1 :=
  eigen_of_funEq (pow_ne_zero k hc) fun p => by
    rw [IsRepulsiveFixedJ.iterate h k p, inv_pow]

/-- Differences along `gᵏ` are moved by the linear part `L(gᵏ)`. -/
theorem pow_smul_sub_pow_smul (g : isom d) (k : ℕ) (a b : Minkowski d) :
    (g ^ k) • a - (g ^ k) • b = linOf (g ^ k) (a - b) := by
  rw [smul_eq_lin_add, smul_eq_lin_add, map_sub]; abel

/-- **The elliptic part grows at most linearly**: if `e` is orthogonal to the two null
eigenvectors `nullVec w.1`, `nullVec w'.1` of `L(γ)` (two distinct null directions), then
`⟨e | γᵏ q⟩ − ⟨e | q⟩` is `O(k)`: each step is `⟨e | L(γᵏ) z⟩` with `z ⊥ nullVec w.1`, bounded by
`(|e|² + |z|²)/2` (`abs_minkB_le_of_null_orth`, `L(γᵏ)` preserving `minkQ` and `(nullVec w.1)^⊥`). -/
theorem exists_abs_minkB_pow_smul_sub_le {γ : isom d} {w w' : PenroseSphere d × ℝ} {c c' : ℝ}
    (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ∀ p, minkB (nullVec w.1) (γ • p) - w.2 = c⁻¹ * (minkB (nullVec w.1) p - w.2))
    (h' : ∀ p, minkB (nullVec w'.1) (γ • p) - w'.2 = c'⁻¹ * (minkB (nullVec w'.1) p - w'.2))
    (hD : minkB (nullVec w.1) (nullVec w'.1) ≠ 0)
    {e : Minkowski d} (he : minkB (nullVec w.1) e = 0) (he' : minkB (nullVec w'.1) e = 0)
    (q : Minkowski d) :
    ∃ B : ℝ, ∀ k : ℕ, |minkB e ((γ ^ k) • q) - minkB e q| ≤ k * B := by
  obtain ⟨z, β, hv, hz⟩ : ∃ z : Minkowski d, ∃ β : ℝ, γ • q - q = z + β • nullVec w'.1 ∧
      minkB (nullVec w.1) z = 0 := by
    refine ⟨γ • q - q - (minkB (nullVec w.1) (γ • q - q) / minkB (nullVec w.1) (nullVec w'.1)) •
      nullVec w'.1, _, by abel, ?_⟩
    rw [minkB_sub_right, minkB_smul_right, div_mul_cancel₀ _ hD, sub_self]
  refine ⟨(minkQ e + minkQ z) / 2, fun k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : minkB e ((γ ^ (k + 1)) • q) - minkB e ((γ ^ k) • q) =
        minkB e (linOf (γ ^ k) z) := by
      rw [← minkB_sub_right, pow_succ, mul_smul, pow_smul_sub_pow_smul, hv, map_add, map_smul,
        linOf_pow_nullVec_of_funEq hc' h' k, minkB_add_right, minkB_smul_right, minkB_smul_right,
        minkB_comm e (nullVec w'.1), he', mul_zero, mul_zero, add_zero]
    have hLz : minkB (nullVec w.1) (linOf (γ ^ k) z) = 0 := by
      have h1 := lorentz.minkB_apply (linOf_mem (γ ^ k)) (nullVec w.1) z
      rw [linOf_pow_nullVec_of_funEq hc h k, minkB_smul_left, hz] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero k hc)
    have hb := abs_minkB_le_of_null_orth (minkQ_nullVec w.1) (nullVec_ne_zero w.1) he hLz
    rw [lorentz.minkQ_apply (linOf_mem (γ ^ k))] at hb
    rw [← hstep] at hb
    push_cast
    rw [abs_le] at hb ih ⊢
    constructor <;> nlinarith [hb.1, hb.2, ih.1, ih.2]


/-- **The basin of repulsion in `𝒥`** (l.1255–1264): for a loxodromic `γ` with repulsive point
`w` (and `w'` that of `γ⁻¹`), the negative iterates `γ⁻ᵏ x` of every `x ∈ 𝒥` off the fibre
`δ⁻¹(w'.1)` converge to `w`. Proof: write `nullVec x.1 = a n₀ + b n₁ + e` with `n₀, n₁` the null
eigenvectors and `e ⊥ n₀, n₁`, `a ≠ 0` exactly when `x.1 ≠ w'.1`; along `γᵏ`, the affine function
`⟨nullVec x.1 | ·⟩ − x.2`, rescaled by `λᵏ`, converges to `a (⟨n₀ | ·⟩ − w.2)` (the `n₁` term is
`O((λλ')ᵏ)`, the `e` term `O(kλᵏ)` by `exists_abs_minkB_pow_smul_sub_le`); the affine functions of
`γ⁻ᵏ x` are its positive multiples normalised by `⟨nullVec · | (1,0)⟩ = −1`, so they converge to
`⟨n₀ | ·⟩ − w.2`, which gives both coordinates (`‖u − v₀‖² = −2⟨nullVec u | nullVec v₀⟩`). -/
theorem tendsto_isomPenrose_inv_pow {γ : isom d} {w w' x : PenroseSphere d × ℝ}
    (hw : IsRepulsiveFixedJ γ w) (hw' : IsRepulsiveFixedJ γ⁻¹ w') (hx : x.1 ≠ w'.1) :
    Tendsto (fun k : ℕ => isomPenrose (γ⁻¹ ^ k) x) atTop (𝓝 w) := by
  have hne := hw.fst_ne hw'
  obtain ⟨-, l, hl0, hl1, -, hf⟩ := hw
  obtain ⟨-, l', hl0', hl1', -, hfi⟩ := hw'
  have hf' : ∀ p, minkB (nullVec w'.1) (γ • p) - w'.2 = (l'⁻¹)⁻¹ * (minkB (nullVec w'.1) p - w'.2) :=
    fun p => by rw [inv_inv]; exact funEq_of_inv hl0'.ne' hfi p
  set n₀ := nullVec w.1 with hn₀
  set n₁ := nullVec w'.1 with hn₁
  set n := nullVec x.1 with hn
  have hsub : ∀ {u u' : PenroseSphere d}, u ≠ u' → minkB (nullVec u) (nullVec u') ≠ 0 := by
    intro u u' huu h0
    rw [minkB_nullVec_nullVec] at h0
    have : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ = 0 := by
      have : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    exact huu (Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 this)))
  have hD : minkB n₀ n₁ ≠ 0 := hsub hne
  have hxa : minkB n n₁ ≠ 0 := hsub hx
  set a := minkB n n₁ / minkB n₀ n₁ with ha
  set b := minkB n n₀ / minkB n₀ n₁ with hb
  have ha0 : a ≠ 0 := div_ne_zero hxa hD
  set e := n - a • n₀ - b • n₁ with he
  have hq₀ : minkQ n₀ = 0 := minkQ_nullVec _
  have hq₁ : minkQ n₁ = 0 := minkQ_nullVec _
  have he₀ : minkB n₀ e = 0 := by
    rw [he, minkB_sub_right, minkB_sub_right, minkB_smul_right, minkB_smul_right,
      ← minkQ_eq_minkB, hq₀, hb, minkB_comm n₀ n]
    field_simp; ring
  have he₁ : minkB n₁ e = 0 := by
    rw [he, minkB_sub_right, minkB_sub_right, minkB_smul_right, minkB_smul_right,
      ← minkQ_eq_minkB n₁, hq₁, ha, minkB_comm n₁ n, minkB_comm n₁ n₀]
    field_simp; ring
  -- the rescaled affine function along the orbit
  set Φ : ℕ → Minkowski d → ℝ := fun k q => l ^ k * (minkB n ((γ ^ k) • q) - x.2) with hΦ
  have hdec : ∀ k q, Φ k q = a * (minkB n₀ q - w.2) + l ^ k * (a * w.2 + b * w'.2 - x.2) +
      b * (l * l') ^ k * (minkB n₁ q - w'.2) + l ^ k * minkB e ((γ ^ k) • q) := by
    intro k q
    have hA : minkB n₀ ((γ ^ k) • q) = w.2 + (l ^ k)⁻¹ * (minkB n₀ q - w.2) := by
      have := IsRepulsiveFixedJ.iterate hf k q; rw [inv_pow] at this; linarith
    have hB : minkB n₁ ((γ ^ k) • q) = w'.2 + l' ^ k * (minkB n₁ q - w'.2) := by
      have := IsRepulsiveFixedJ.iterate hf' k q; rw [inv_inv] at this; linarith
    have hE : minkB e ((γ ^ k) • q) = minkB n ((γ ^ k) • q) - a * minkB n₀ ((γ ^ k) • q) -
        b * minkB n₁ ((γ ^ k) • q) := by
      rw [he, minkB_sub_left, minkB_sub_left, minkB_smul_left, minkB_smul_left]
    simp only [hΦ]
    rw [hE, hA, hB, mul_pow]
    have : l ^ k ≠ 0 := pow_ne_zero k hl0.ne'
    field_simp; ring
  have hpow : Tendsto (fun k : ℕ => l ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1
  have hpow' : Tendsto (fun k : ℕ => (l * l') ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hl0.le hl0'.le)
      (mul_lt_one_of_nonneg_of_lt_one_left hl0.le hl1 hl1'.le)
  have hlim : ∀ q, Tendsto (fun k => Φ k q) atTop (𝓝 (a * (minkB n₀ q - w.2))) := by
    intro q
    obtain ⟨B, hB⟩ := exists_abs_minkB_pow_smul_sub_le hl0.ne'
      (inv_ne_zero hl0'.ne') hf hf' hD he₀ he₁ q
    have hE : Tendsto (fun k : ℕ => l ^ k * minkB e ((γ ^ k) • q)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k : ℕ => l ^ k * |minkB e q| + ((k : ℝ) * l ^ k) * B)
        (fun k => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hl0 k)]
        have := hB k
        have h2 : |minkB e ((γ ^ k) • q)| ≤ |minkB e q| + k * B := by
          have := abs_sub_abs_le_abs_sub (minkB e ((γ ^ k) • q)) (minkB e q); linarith
        nlinarith [pow_pos hl0 k]
      · have := (hpow.mul_const |minkB e q|).add
          ((tendsto_self_mul_const_pow_of_lt_one hl0.le hl1).mul_const B)
        simpa using this
    have := ((((tendsto_const_nhds (x := a * (minkB n₀ q - w.2))).add
      (hpow.mul_const (a * w.2 + b * w'.2 - x.2))).add
      (((hpow'.const_mul b).mul_const (minkB n₁ q - w'.2)))).add hE)
    simp only [zero_mul, mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    rw [hdec k q]
  -- the normalised affine functions of the iterates converge
  set xk : ℕ → PenroseSphere d × ℝ := fun k => isomPenrose (γ⁻¹ ^ k) x with hxk
  have hrel : ∀ k q, minkB (nullVec (xk k).1) q - (xk k).2 =
      (lorentzScale (linearPart (γ⁻¹ ^ k)) x.1)⁻¹ * (minkB n ((γ ^ k) • q) - x.2) := by
    intro k q
    have hs : (γ⁻¹ ^ k) • ((γ ^ k) • q) = q := by rw [inv_pow, inv_smul_smul]
    have := minkB_isomPenrose (γ⁻¹ ^ k) x ((γ ^ k) • q)
    rw [hs] at this
    exact this
  set r : ℕ → ℝ := fun k => (lorentzScale (linearPart (γ⁻¹ ^ k)) x.1)⁻¹ / l ^ k with hr
  have hrΦ : ∀ k q, minkB (nullVec (xk k).1) q - (xk k).2 = r k * Φ k q := by
    intro k q
    rw [hrel k q]
    simp only [hr, hΦ]
    have : l ^ k ≠ 0 := pow_ne_zero k hl0.ne'
    field_simp
  set et : Minkowski d := ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) with het
  have hmet : ∀ u : PenroseSphere d, minkB (nullVec u) et = -1 := fun u => by
    rw [minkB_nullVec]; simp [het]
  have hnorm : ∀ k, r k = -1 / (Φ k et - Φ k 0) := by
    intro k
    have h1 := hrΦ k et
    have h0 := hrΦ k 0
    rw [hmet] at h1
    rw [minkB_zero_right] at h0
    have hprod : r k * (Φ k et - Φ k 0) = -1 := by rw [mul_sub]; linarith
    have hD0 : Φ k et - Φ k 0 ≠ 0 := fun h => by rw [h, mul_zero] at hprod; norm_num at hprod
    exact eq_div_of_mul_eq hD0 hprod
  have hDlim : a * (minkB n₀ et - w.2) - a * (minkB n₀ 0 - w.2) = -a := by
    rw [hn₀, hmet, minkB_zero_right]; ring
  have hrlim : Tendsto r atTop (𝓝 (-1 / -a)) := by
    have := (tendsto_const_nhds (x := (-1 : ℝ))).div ((hlim et).sub (hlim 0))
      (by rw [hDlim]; exact neg_ne_zero.2 ha0)
    rw [hDlim] at this
    exact this.congr fun k => (hnorm k).symm
  have hφlim : ∀ q, Tendsto (fun k => minkB (nullVec (xk k).1) q - (xk k).2) atTop
      (𝓝 (minkB n₀ q - w.2)) := by
    intro q
    have := hrlim.mul (hlim q)
    rw [show -1 / -a * (a * (minkB n₀ q - w.2)) = minkB n₀ q - w.2 by field_simp] at this
    exact this.congr fun k => (hrΦ k q).symm
  -- the two coordinates
  have h2 : Tendsto (fun k => (xk k).2) atTop (𝓝 w.2) := by
    have := (hφlim 0).neg
    simp only [minkB_zero_right, zero_sub, neg_neg] at this
    exact this
  have h1 : Tendsto (fun k => (xk k).1) atTop (𝓝 w.1) := by
    rw [tendsto_subtype_rng, tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun k => ‖((xk k).1 : EuclideanSpace ℝ (Fin d)) - w.1‖ ^ 2) atTop
        (𝓝 0) := by
      have := ((hφlim n₀).sub (hφlim 0)).const_mul (-2)
      rw [show (-2) * ((minkB n₀ n₀ - w.2) - (minkB n₀ 0 - w.2)) = 0 by
        rw [← minkQ_eq_minkB, hq₀, minkB_zero_right]; ring] at this
      refine this.congr fun k => ?_
      rw [minkB_zero_right, hn₀, minkB_nullVec_nullVec]; ring
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    exact this.congr fun k => Real.sqrt_sq (norm_nonneg _)
  exact (Prod.tendsto_iff _ _).2 ⟨h1, h2⟩


/-- **`bprop:admlox`, minimality in `𝒥`** (l.1232–1238): `Λ(Γ)` is contained in every nonempty
closed `Γ`-invariant subset of `𝒥`. -/
theorem limitSetJ_subset (hL : LimitSetMinimal d) (hΓ : DiscreteTopology (linearImage Γ))
    (hfix : ¬HasGlobalFixedPoint (linearImage Γ)) {F : Set (PenroseSphere d × ℝ)}
    (hF : IsClosed F) (hne : F.Nonempty) (hinv : ∀ η ∈ Γ, isomPenrose η '' F ⊆ F) :
    limitSetJ Γ ⊆ F := by
  refine closure_minimal (fun w hw => ?_) hF
  obtain ⟨γ, hγ, hr⟩ := hw
  obtain ⟨w', hr'⟩ := exists_isRepulsiveFixedJ (isLoxodromic_linOf_inv hr.1)
  obtain ⟨x, hxF, hx⟩ : ∃ x ∈ F, x.1 ≠ w'.1 := by
    by_contra hall'
    have hall : ∀ x ∈ F, x.1 = w'.1 := fun x hx => by_contra fun h => hall' ⟨x, hx, h⟩
    have hsph : IsSphereInvariant (linearImage Γ) {w'.1} := by
      rintro A hA u rfl
      obtain ⟨η, hη, rfl⟩ := Subgroup.mem_map.1 hA
      obtain ⟨y, hy⟩ := hne
      have h1 : lorentzSphere (linearPart η) y.1 = w'.1 := hall _ (hinv η hη ⟨y, hy, rfl⟩)
      rw [hall y hy] at h1
      exact h1
    have hw1 := hL _ hΓ hfix {w'.1} isClosed_singleton (singleton_nonempty _) hsph
      (fst_image_loxRepSet_subset Γ ⟨w, ⟨γ, hγ, hr⟩, rfl⟩)
    exact hr.fst_ne hr' hw1
  exact hF.mem_of_tendsto (tendsto_isomPenrose_inv_pow hr hr' hx)
    (Eventually.of_forall fun k => hinv _ (Γ.pow_mem (Γ.inv_mem hγ) k) ⟨x, hxF, rfl⟩)

end Admlox


end Causal.Flat
