import GX.BBS.IPm
import GX.BBS.QuotientCircle
import GXScaffold.Interaction.FunnelGTilde
import GXScaffold.BBS.PSL2NormalForms

/-!
# BBS § 3.3: the classification of `ℝP¹`-circles and of HS-singularities, and the remark that positive and negative hyperbolic links are not isomorphic

Targets `T-bbs-hs-singularities` and `T-bbs-hs-remark-existence` (`roadmap/roadmap.toml`; BBS
layer L2 in lean-gx, DEC-192). `papers/bbs/legacy/labeled/colI_v1.tex`. 5 tagged `sorry`s, none
beneath the label (the time-like, light-like and degree-`0` types and the components of `I^±`).
Imports `GX.BBS.QuotientCircle` (the quotient circles `J/⟨f⟩`), `GXScaffold.BBS.PSL2NormalForms`
(sorry-free: the normal forms of `PSL(2,ℝ)` and `G̃`) and `GXScaffold.Interaction.FunnelGTilde`
(sorry-free: parabolic fixed points, `apply_lt_delta_of_fixed`, `le_conj_apply`).

* `bbsrem:previous_section_observed_only` — `colI_v1.tex:926` — partial (unmarked: every assertion
  is proved, no `sorry` beneath, in the readings OQ-120 (a)–(c) and OQ-116 (a); the mark waits on
  OQ-120): (i) `GX.rp1Iso_of_zpowers_eq`, (ii) `GX.conj_inv_swaps_timelike_spacelike` (with the
  `G̃` form `GX.GTilde.lt_apply_iff_of_conj_inv`), (iii) `GX.not_isIso_of_positive_of_negative`;
  "does not extend": `GX.exists_positive_negative` (at every `p ∈ dS²`, the quotients
  `ℝ/⟨δ² g⟩` and `ℝ/⟨δ² g⁻¹⟩`), with both halves `GX.exists_rp1Iso_not_isIso`.

> In the previous section we observed that there is only one $\R\PP^1$ hyperbolic circle of
> holonomy $\langle g \rangle$ up to $\R\PP^1$-isomorphism, but this remark does not extend to
> hyperbolic $(\Gamma_p, \ell(p))$-circles since a real projective conjugacy between $g$ and
> $g^{-1}$, if preserving the orientation, must permute time-like and space-like components. Hence
> positive hyperbolic $(\Gamma_p, \ell(p))$-circles and negative hyperbolic
> $(\Gamma_p, \ell(p))$-circles are not isomorphic. (l.927–931)

The unlabeled prose of § 3.3 (l.688–760, l.785–802, l.855–922), stated in full:

> These examples exhaust the list of real projective structures on the circle up to real
> projective isomorphism. [...] An easy case-by-case study leads to a proof of our claim.
> It follows that every cyclic subgroup of $\tilde{G}$ is the holonomy group of a real projective
> circle, and that two such real projective circles are projectively isomorphic if and only if
> their holonomy groups are conjugate one to the other. (l.712–723)

## Main declarations (proved unless marked `sorry`)

* **`ℝP¹`-circles.** `GX.IsRP1Iso`; **iso ⇔ conjugate lifted holonomies** `GX.rp1Iso_iff_conj`
  (`GX.conj_of_rp1Iso`, `GX.exists_rp1Iso_of_conj`, l.721–723 read for the oriented lifted
  holonomies, SCOPE (d)); **"exhaust the list"**
  `GX.IsLiftedDevPair.exhaust` (elliptic or central, onto; degree `k ≥ 1`, onto; degree `0`,
  onto `]x₀, x₁[` between successive fixed points, `x₁ = δx₀` parabolic, `x₁ < δx₀` hyperbolic);
  the developed image is a component (`GX.GTilde.IsComp`, `GX.GTilde.IsComp.exists_add_int`).
  `(k, [g])` parametrises degree `k` (`GX.rp1Iso_iff_of_degree_pos`, every `k`); positive or
  negative parabolic (`GX.GTilde.IsParabolic.le_or_ge`); degree-`0` parabolic is positive
  (`GX.HasLiftedHolonomy.le_apply_of_parabolic`); `x₀` repelling, `x₁` attracting
  (`GX.IsLiftedDevPair.repelling_attracting`); through the normal forms of
  `GXScaffold.BBS.PSL2NormalForms`, `GX.PSL2.IsHyperbolic.isConj_iff`,
  `GX.PSL2.IsParabolic.isConj_iff`, `GX.rp1Iso_of_angle_eq`; every non-trivial cyclic subgroup is a
  lifted holonomy group (`GX.exists_rp1Circle_of_ne_one`, by `GX.exists_rp1Circle_quotient`;
  l.721 corrected, SCOPE (g)).
* **`G̃`.** Three fixed points force `1` (`GX.PSL2.eq_one_of_three_fixed`); a hyperbolic element is
  conjugate to its inverse (`GX.PSL2.IsHyperbolic.exists_conj_inv`, `GX.GTilde.IsHyperbolic.exists_conj_inv`);
  its fixed points and directions (`GX.GTilde.IsHyperbolic.fixed_structure`).
* **`(Γ_p, ℓ(p))`-circles.** `GX.linkCover : ℝP̃¹ → ℓ(p)` (`δ` antipodal); lifted developing pairs
  `GX.GammaLinkCircle.IsLiftedDev`, existence, relation of two pairs
  (`GX.GammaLinkCircle.IsLiftedDev.relate`); at `p ∈ dS²` the fixed points of `A ≠ 1` are
  lightlike (`GX.eq_one_of_smul_eq_of_deSitter`) and time-like/space-like directions are moved in
  opposite directions (`GX.timelike_spacelike_dir`); hyperbolic at `dS²` (l.794–795, non-trivial
  holonomy: `GX.GammaLinkCircle.IsLiftedDev.isHyperbolic_of_deSitter`; counterexample for trivial
  holonomy `GX.regular_not_isHyperbolic`); **the degree is even** at non-timelike `p`
  (`…even_of_nonneg`, l.905); positive/negative (`GX.GammaLinkCircle.IsSpacelikePositive`,
  `…Negative`, independent of the choice of `θ, E, D` (`…forall`), **dichotomy** `…spacelike_dichotomy`; light-like
  `…lightlike_dichotomy`); the examples of l.928 (`GX.exists_gammaP_lift_fixed`: a lift with a
  fixed point of `A ∈ Γ_p ∖ {1}`; `GX.exists_isLiftedDev_delta_sq_mul`: the quotient `ℝ/⟨δ² g⟩`).
  `sorry`: the time-like and light-like types (`…isElliptic_of_timelike`,
  `…isParabolic_of_null`), the degree-`0` types (`…spacelike_degree_zero`, `…bdPlus_degree_zero`),
  the components of `I^±` (`…iPlus_components`).

## Hypothesis checklist

| BBS | here |
|---|---|
| `ℝP¹`-isomorphism (l.725–731) | ✓ `IsGXMorphism PSL(2,ℝ) ℝP¹` homeomorphism; the canonical orientation is the one of the increasing lifts (`GX.HasLiftedHolonomy`) |
| "holonomy `⟨g⟩`" (l.927) | ⚠ reading: the lifted holonomy group in `G̃` (SCOPE (a)) |
| `(Γ_p, ℓ(p))`-isomorphism (l.931) | ⚠ reading: same `p`, a `(Γ_p, ℓ(p))`-morphism homeomorphism (`GX.GammaLinkCircle.IsIso`) |
| positive / negative (l.908–915) | ⚠ reading: the l.915 form, `g x ≥ x` (`≤`) on `I⁺ = D(E⁻¹ i⁺(L))`, `f = δᵏ g`, `k ≥ 1`, `θ` oriented; independent of the choices (`…forall`); the repelling-endpoint form of l.908–913 not formalized (SCOPE (f)) |
| time-like / space-like components (l.929–930) | ⚠ `i^±` under OQ-116 (a) (time-like reading, `GX.BBS.IPm`); space-like: `Q(dsProj σ) > 0` |
| `p ∈ dS²` (the hyperbolic case) | ✓ `HS.piece 2 .deSitter` |

## SCOPE (disclosed)

* **(a)** l.927 "only one hyperbolic circle of holonomy `⟨g⟩`" is read in `G̃`: in `G = PSL(2,ℝ)`
  circles of every degree share `⟨g⟩` and are not isomorphic (the degree is an invariant,
  `GX.rp1Iso_iff_of_degree_pos`). The proof also uses `g ~ g⁻¹` for degree `0`.
* **(b)** OQ-116 open: `i^±` as in `GX.BBS.IPm` (time-like reading at `dS²`; the printed closed arc
  at `∂ℍ²±`, whence `iMinus \ tangentDirs` in `…bdPlus_degree_zero`). OQ-113 (a)/(d): only
  `GX.rp1Iso_of_angle_eq` reads the angle; "elliptic" includes central holonomy.
* **(c)** Not formalized: `𝔢(L)`, the HS-surface side of the singularity types (only their links),
  l.850–852 ("the `ℝP¹`-structure and `i^±(L)` determine the structure").
* **(d)** l.721–723 is formalized in the oriented form of l.723–731: isomorphism iff the oriented
  lifted holonomies (elements of `G̃`) are conjugate (`GX.rp1Iso_iff_conj`). The printed group form
  ("holonomy groups conjugate") is proved only for two equal hyperbolic groups
  (`GX.rp1Iso_of_zpowers_eq`).
* **(e)** An isomorphism of `(Γ_p, ℓ(p))`-circles is read with the same `p`
  (`GX.GammaLinkCircle.IsIso`); one through `B ∈ SO₀(1,2)` moving `p` preserves `i^±` and the
  orientation, so (iii) would be unchanged (argued, not formalized).
* **(f)** Positive / negative is the l.915 form ("`g x ≥ x` on `I⁺`"). Its equivalence with the
  primary definition of l.908–913 (left extremities of the components of `I⁺` repelling,
  resp. attracting) follows from `GX.GTilde.IsHyperbolic.fixed_structure` and
  `GX.timelike_spacelike_dir`, argued, not formalized.
* **(g)** l.721–722 "every cyclic subgroup of `G̃` is the holonomy group" is false for the trivial
  subgroup (`GX.not_every_cyclic_subgroup_is_holonomy`, `GX.BBS.QuotientCircle`; OQ-123); stated
  here for `f ≠ 1`.
* **(h)** "Does not extend" (l.928) is read as: there are two hyperbolic `(Γ_p, ℓ(p))`-circles
  whose underlying `ℝP¹`-circles are isomorphic (conjugate lifted holonomies in `G̃`, OQ-120 (b))
  and which are not isomorphic. The examples have degree `2` (`f = δ² g`, `f' = δ² g⁻¹`) and
  `Γ_p`-holonomies `A` and `A⁻¹`, which generate the same subgroup of `Γ_p`; the statements give
  the degree only as `k ≥ 1` and do not state the `Γ_p`-holonomy. The identifications `θ`, `θ'`
  in the isomorphism clause are not required to be oriented (the witnesses are).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology Real ComplexConjugate
open scoped MatrixGroups

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. `ℝP¹`-isomorphisms and the lifted holonomy (l.721–731) -/

section Iso

variable {L L' : Type*} [TopologicalSpace L] [ChartedSpace RP1 L]
  [HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1)] [TopologicalSpace L'] [ChartedSpace RP1 L']
  [HasGroupoid L' (gxGroupoid PSL(2, ℝ) RP1)]

/-- **An `ℝP¹`-isomorphism** (l.725–731): a homeomorphism which is a `(PSL(2,ℝ), ℝP¹)`-morphism.
It preserves the canonical orientations (which are read off the developing maps). -/
def IsRP1Iso (φ : L ≃ₜ L') : Prop := IsGXMorphism PSL(2, ℝ) RP1 φ

/-- `(E, D)` **witnesses the lifted holonomy** `f`: the data of `GX.HasLiftedHolonomy`. -/
def IsLiftedDevPair (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) : Prop :=
  IsPeriodicCover E ∧ Continuous D ∧ StrictMono D ∧ IsDevAlong E (RP1.proj ∘ D) ∧
    ∀ s, D (s + 1) = f (D s)

theorem hasLiftedHolonomy_iff {f : GTilde} :
    HasLiftedHolonomy L f ↔ ∃ E D, IsLiftedDevPair (L := L) E D f := Iff.rfl

theorem IsDevAlong.comp_rp1Iso {φ : L ≃ₜ L'} (hφ : IsRP1Iso φ) {E : ℝ → L} (hE : Continuous E)
    {D : ℝ → RP1} (hD : IsDevAlong E D) : IsDevAlong (φ ∘ E) D := fun s => by
  obtain ⟨g₁, h₁⟩ := hD s
  obtain ⟨g₂, h₂⟩ := hφ.exists_smul_eq (E s)
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  filter_upwards [h₁, hE.continuousAt.eventually h₂] with s' hs' hs''
  show D s' = (g₁ * g₂⁻¹) • chartAt RP1 (φ (E s)) (φ (E s'))
  rw [hs'', mul_smul, inv_smul_smul, hs']

theorem HasLiftedHolonomy.of_rp1Iso {φ : L ≃ₜ L'} (hφ : IsRP1Iso φ) {f : GTilde}
    (hf : HasLiftedHolonomy L f) : HasLiftedHolonomy L' f := by
  obtain ⟨E, D, hE, hDc, hDm, hDd, hDf⟩ := hf
  refine ⟨φ ∘ E, D, ⟨hE.isCoveringMap.homeomorph_comp φ, φ.surjective.comp hE.surjective,
    fun s => by simp only [Function.comp_apply, hE.add_one], fun s t h =>
      hE.fiber s t (φ.injective h)⟩, hDc, hDm, hDd.comp_rp1Iso hφ hE.isCoveringMap.continuous, hDf⟩

/-- **l.721–723, "only if"** (oriented form, l.723–731): isomorphic `ℝP¹`-circles have conjugate lifted holonomies. -/
theorem conj_of_rp1Iso {φ : L ≃ₜ L'} (hφ : IsRP1Iso φ) {f f' : GTilde}
    (hf : HasLiftedHolonomy L f) (hf' : HasLiftedHolonomy L' f') :
    ∃ h : GTilde, f' = h * f * h⁻¹ :=
  (hf.of_rp1Iso hφ).conj hf'

end Iso

/-! ## 2. Fixed points in `PSL(2,ℝ)` and `G̃` -/

/-- **A binary quadratic form vanishing at three pairwise independent vectors is zero** (Cramer's
rule on the `3 × 3` Vandermonde-type system). -/
theorem quadForm_eq_zero_of_three {u v w x₁ y₁ x₂ y₂ x₃ y₃ : ℝ}
    (e₁ : u * x₁ ^ 2 + v * (x₁ * y₁) + w * y₁ ^ 2 = 0)
    (e₂ : u * x₂ ^ 2 + v * (x₂ * y₂) + w * y₂ ^ 2 = 0)
    (e₃ : u * x₃ ^ 2 + v * (x₃ * y₃) + w * y₃ ^ 2 = 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0) (h13 : x₁ * y₃ - x₃ * y₁ ≠ 0) (h23 : x₂ * y₃ - x₃ * y₂ ≠ 0) :
    u = 0 ∧ v = 0 ∧ w = 0 := by
  have hdet : (x₁ * y₂ - x₂ * y₁) * (x₁ * y₃ - x₃ * y₁) * (x₂ * y₃ - x₃ * y₂) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h12 h13) h23
  refine ⟨?_, ?_, ?_⟩
  · have : u * ((x₁ * y₂ - x₂ * y₁) * (x₁ * y₃ - x₃ * y₁) * (x₂ * y₃ - x₃ * y₂)) = 0 := by
      linear_combination (y₂ * y₃ * (x₂ * y₃ - x₃ * y₂)) * e₁ +
        (-y₁ * y₃ * (x₁ * y₃ - x₃ * y₁)) * e₂ + (y₁ * y₂ * (x₁ * y₂ - x₂ * y₁)) * e₃
    exact (mul_eq_zero.1 this).resolve_right hdet
  · have : v * ((x₁ * y₂ - x₂ * y₁) * (x₁ * y₃ - x₃ * y₁) * (x₂ * y₃ - x₃ * y₂)) = 0 := by
      linear_combination (-(x₂ * y₃ - x₃ * y₂) * (x₂ * y₃ + x₃ * y₂)) * e₁ +
        ((x₁ * y₃ - x₃ * y₁) * (x₁ * y₃ + x₃ * y₁)) * e₂ +
        (-(x₁ * y₂ - x₂ * y₁) * (x₁ * y₂ + x₂ * y₁)) * e₃
    exact (mul_eq_zero.1 this).resolve_right hdet
  · have : w * ((x₁ * y₂ - x₂ * y₁) * (x₁ * y₃ - x₃ * y₁) * (x₂ * y₃ - x₃ * y₂)) = 0 := by
      linear_combination (x₂ * x₃ * (x₂ * y₃ - x₃ * y₂)) * e₁ +
        (-x₁ * x₃ * (x₁ * y₃ - x₃ * y₁)) * e₂ + (x₁ * x₂ * (x₁ * y₂ - x₂ * y₁)) * e₃
    exact (mul_eq_zero.1 this).resolve_right hdet

/-- Two points of `ℝP¹` whose representatives have zero cross product are equal. -/
theorem RP1.eq_of_cross_eq_zero {w w' : RP1}
    (h : (RP1.rep w).re * (RP1.rep w').im - (RP1.rep w').re * (RP1.rep w).im = 0) : w = w' := by
  rw [← RP1.mk_rep w, ← RP1.mk_rep w', RP1.mk_eq_mk_iff (RP1.rep_ne_zero w) (RP1.rep_ne_zero w')]
  set a := RP1.rep w
  set b := RP1.rep w'
  have ha : a ≠ 0 := RP1.rep_ne_zero w
  have hn : a.re ^ 2 + a.im ^ 2 ≠ 0 := by
    intro h0
    apply ha
    apply Complex.ext <;> simp <;> nlinarith [sq_nonneg a.re, sq_nonneg a.im]
  refine ⟨(a.re * b.re + a.im * b.im) / (a.re ^ 2 + a.im ^ 2), ?_⟩
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    field_simp
    linear_combination (-a.im) * h
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    field_simp
    linear_combination a.re * h

/-- The fixed-line equation of `A ∈ SL(2,ℝ)` at a fixed point of `ℝP¹`: the representative
`(x, y)` satisfies `c x² + (d − a) x y − b y² = 0`. -/
theorem fixed_quadForm {A : SL(2, ℝ)} {w : RP1} (hw : pslMk A • w = w) :
    (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (RP1.rep w).re ^ 2 +
      ((A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 - (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0) *
        ((RP1.rep w).re * (RP1.rep w).im) +
      (-(A : Matrix (Fin 2) (Fin 2) ℝ) 0 1) * (RP1.rep w).im ^ 2 = 0 := by
  have hw' : A • RP1.mk (RP1.rep w) = RP1.mk (RP1.rep w) := by
    rw [RP1.mk_rep]; exact hw
  obtain ⟨c, hc, hz⟩ := RP1.exists_eq_mul_of_smul_mk (RP1.rep_ne_zero w) hw'
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  rw [slLin_apply, Complex.re_ofReal_mul] at h1
  rw [slLin_apply, Complex.im_ofReal_mul] at h2
  have : c * ((A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (RP1.rep w).re ^ 2 +
      ((A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 - (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0) *
        ((RP1.rep w).re * (RP1.rep w).im) +
      (-(A : Matrix (Fin 2) (Fin 2) ℝ) 0 1) * (RP1.rep w).im ^ 2) = 0 := by
    linear_combination (-(RP1.rep w).re) * h2 + (RP1.rep w).im * h1
  exact (mul_eq_zero.1 this).resolve_left hc

namespace PSL2

/-- An element of `PSL(2,ℝ)` fixing three distinct points of `ℝP¹` is the identity. -/
theorem eq_one_of_three_fixed {g : PSL(2, ℝ)} {w₁ w₂ w₃ : RP1} (h₁ : g • w₁ = w₁)
    (h₂ : g • w₂ = w₂) (h₃ : g • w₃ = w₃) (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃) :
    g = 1 := by
  obtain ⟨A, rfl⟩ := pslMk_surjective g
  have hx : ∀ {w w' : RP1}, w ≠ w' →
      (RP1.rep w).re * (RP1.rep w').im - (RP1.rep w').re * (RP1.rep w).im ≠ 0 :=
    fun hne h0 => hne (RP1.eq_of_cross_eq_zero h0)
  obtain ⟨hc, hda, hb⟩ := quadForm_eq_zero_of_three (fixed_quadForm h₁) (fixed_quadForm h₂)
    (fixed_quadForm h₃) (hx h12) (hx h13) (hx h23)
  set M := (A : Matrix (Fin 2) (Fin 2) ℝ)
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have hb' : M 0 1 = 0 := by linarith
  have hd : M 1 1 = M 0 0 := by linarith
  have ha : M 0 0 ≠ 0 := by
    intro h0
    have h' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := hdet
    rw [hd, h0, hb'] at h'; simp at h'
  have hlin : ∀ z : ℂ, slLin A z = (M 0 0 : ℂ) * z := fun z => by
    rw [slLin_apply]
    apply Complex.ext <;> simp [M, hb', hd, hc]
  have hcen : A ∈ Subgroup.center SL(2, ℝ) := RP1.mem_center_of_eqOn isOpen_univ univ_nonempty
    fun w _ => by
      rw [← RP1.mk_rep w, RP1.sl_smul_mk A (RP1.rep_ne_zero w), hlin, RP1.mk_ofReal_mul ha]
  exact (QuotientGroup.eq_one_iff A).2 hcen

/-- An element `≠ 1` of `PSL(2,ℝ)` with two distinct fixed points is hyperbolic. -/
theorem isHyperbolic_of_two_fixed {g : PSL(2, ℝ)} (hg : g ≠ 1) {w w' : RP1} (hw : g • w = w)
    (hw' : g • w' = w') (hne : w ≠ w') : IsHyperbolic g := by
  rcases trichotomy g with h | h | h | h
  · exact absurd h hg
  · exact absurd hw (h.smul_ne w)
  · exact absurd (h.eq_of_smul_eq hw hw') hne
  · exact h

/-- A matrix `M` with `det M > 0` and `M A = adj(A) M` gives a conjugacy between `A` and `A⁻¹`
in `PSL(2,ℝ)`. -/
theorem exists_conj_inv_of_matrix (A : SL(2, ℝ)) (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : 0 < M.det)
    (hMA : M * (A : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) ℝ) * M) :
    ∃ c : PSL(2, ℝ), c * pslMk A * c⁻¹ = (pslMk A)⁻¹ := by
  set r := (Real.sqrt M.det)⁻¹
  have hr : r ^ 2 * M.det = 1 := by
    simp only [r, inv_pow, Real.sq_sqrt hM.le]
    exact inv_mul_cancel₀ hM.ne'
  let h : SL(2, ℝ) := ⟨r • M, by
    rw [Matrix.det_smul, Fintype.card_fin]; exact hr⟩
  have hh : h * A = A⁻¹ * h := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, h]
    rw [Matrix.smul_mul, hMA, Matrix.mul_smul]
  refine ⟨pslMk h, ?_⟩
  show (QuotientGroup.mk h * QuotientGroup.mk A * (QuotientGroup.mk h)⁻¹ : PSL(2, ℝ)) =
    (QuotientGroup.mk A)⁻¹
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_inv, hh, mul_inv_cancel_right]

/-- **A hyperbolic element of `PSL(2,ℝ)` is conjugate to its inverse** (l.929). -/
theorem IsHyperbolic.exists_conj_inv {g : PSL(2, ℝ)} (hg : IsHyperbolic g) :
    ∃ c : PSL(2, ℝ), c * g * c⁻¹ = g⁻¹ := by
  obtain ⟨A, rfl⟩ := pslMk_surjective g
  have htr : 4 < (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 := hg
  set M := (A : Matrix (Fin 2) (Fin 2) ℝ)
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  set α := (M 0 0 - M 1 1) / 2
  have hμ : 0 < α ^ 2 + M 0 1 * M 1 0 := by
    simp only [α]; nlinarith
  by_cases hb : M 0 1 = 0
  · by_cases hc : M 1 0 = 0
    · refine exists_conj_inv_of_matrix A !![0, -1; 1, 0] (by simp [Matrix.det_fin_two]) ?_
      rw [Matrix.adjugate_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, M, hb, hc]
    · refine exists_conj_inv_of_matrix A !![-α * M 1 0, 2 * α ^ 2 + M 0 1 * M 1 0;
        -(M 1 0) ^ 2, α * M 1 0] ?_ ?_
      · rw [Matrix.det_fin_two_of]
        have : 0 < M 1 0 ^ 2 := by positivity
        nlinarith [mul_pos this hμ]
      · rw [Matrix.adjugate_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, M, α] <;> ring
  · refine exists_conj_inv_of_matrix A !![α * M 0 1, M 0 1 ^ 2;
      -(M 0 1 * M 1 0 + 2 * α ^ 2), -α * M 0 1] ?_ ?_
    · rw [Matrix.det_fin_two_of]
      have : 0 < M 0 1 ^ 2 := by positivity
      nlinarith [mul_pos this hμ]
    · rw [Matrix.adjugate_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, M, α] <;> ring

end PSL2

namespace GTilde

/-- **A hyperbolic `g ∈ G̃` with a fixed point is conjugate in `G̃` to `g⁻¹`.** -/
theorem IsHyperbolic.exists_conj_inv {f : GTilde} (hf : IsHyperbolic f) (hfix : ∃ x, f x = x) :
    ∃ h : GTilde, h * f * h⁻¹ = f⁻¹ := by
  obtain ⟨c, hc⟩ := PSL2.IsHyperbolic.exists_conj_inv hf
  obtain ⟨h₀, rfl⟩ := toPSL_surjective c
  obtain ⟨x, hx⟩ := hfix
  have hk : h₀ * f * h₀⁻¹ * f ∈ toPSL.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hc, inv_mul_cancel]
  rw [ker_toPSL, Subgroup.mem_zpowers_iff] at hk
  obtain ⟨n, hn⟩ := hk
  have hfi : h₀ * f * h₀⁻¹ = delta ^ n * f⁻¹ := by rw [hn, mul_inv_cancel_right]
  have hfx : (h₀ * f * h₀⁻¹) (h₀ x) = h₀ x := by
    rw [coe_mul_apply, coe_mul_apply, inv_apply_apply, hx]
  have hfx' : f⁻¹ x = x := by
    have := inv_apply_apply f x; rwa [hx] at this
  have hn0 : (0 : ℤ) = n := delta_zpow_mul_unique ⟨h₀ x, hfx⟩ ⟨x, hfx'⟩
    (by rw [zpow_zero, one_mul, hfi])
  refine ⟨h₀, ?_⟩
  rw [hfi, ← hn0, zpow_zero, one_mul]

/-- An element of `G̃` conjugate to its inverse and moving every point in one direction is `1`. -/
theorem eq_one_of_conj_inv {f h : GTilde} (hh : h * f * h⁻¹ = f⁻¹)
    (hdir : (∀ x, x ≤ f x) ∨ (∀ x, f x ≤ x)) : f = 1 := by
  refine ext' fun x => ?_
  rw [one_apply]
  rcases hdir with hle | hge
  · have h1 : ∀ y, y ≤ f⁻¹ y := fun y => by
      have := le_conj_apply hle h y; rwa [hh] at this
    have h2 := (GTilde.strictMono f).monotone (h1 x)
    rw [apply_inv_apply] at h2
    exact le_antisymm h2 (hle x)
  · have h1 : ∀ y, f⁻¹ y ≤ y := fun y => by
      have := (GTilde.strictMono h).monotone (hge (h⁻¹ y))
      rw [apply_inv_apply] at this
      rw [← hh, coe_mul_apply, coe_mul_apply]
      exact this
    have h2 := (GTilde.strictMono f).monotone (h1 x)
    rw [apply_inv_apply] at h2
    exact le_antisymm (hge x) h2

/-- A hyperbolic `g ∈ G̃` with a fixed point moves some point to the left. -/
theorem IsHyperbolic.not_forall_le {f : GTilde} (hf : IsHyperbolic f) (hfix : ∃ x, f x = x) :
    ¬ ∀ x, x ≤ f x := fun hle => by
  obtain ⟨h, hh⟩ := hf.exists_conj_inv hfix
  exact hf.toPSL_ne_one (by rw [eq_one_of_conj_inv hh (Or.inl hle), map_one])

/-- A hyperbolic `g ∈ G̃` with a fixed point moves some point to the right. -/
theorem IsHyperbolic.not_forall_ge {f : GTilde} (hf : IsHyperbolic f) (hfix : ∃ x, f x = x) :
    ¬ ∀ x, f x ≤ x := fun hge => by
  obtain ⟨h, hh⟩ := hf.exists_conj_inv hfix
  exact hf.toPSL_ne_one (by rw [eq_one_of_conj_inv hh (Or.inr hge), map_one])

/-- **(the remark, l.929–930)**: a conjugacy `h` (an orientation-preserving real projective
transformation of `ℝP̃¹`) between `g` and `g⁻¹` exchanges the points moved to the right and the
points moved to the left. -/
theorem lt_apply_iff_of_conj_inv {g h : GTilde} (hh : h * g * h⁻¹ = g⁻¹) (x : ℝ) :
    x < g x ↔ g (h x) < h x := by
  have e : g⁻¹ (h x) = h (g x) := by
    rw [← hh, coe_mul_apply, coe_mul_apply, inv_apply_apply]
  constructor
  · intro hx
    have h1 : h x < g⁻¹ (h x) := e ▸ GTilde.strictMono h hx
    have := GTilde.strictMono g h1
    rwa [apply_inv_apply] at this
  · intro hx
    have h1 : h x < g⁻¹ (h x) := by
      have := GTilde.strictMono g⁻¹ hx
      rwa [inv_apply_apply] at this
    rw [e] at h1
    exact (GTilde.strictMono h).lt_iff_lt.1 h1

end GTilde

/-! ## 2b. Components of `{x | x < f x}` -/

/-- `J` is **a component of `{x | x < f x}` bounded by fixed points**: open, preconnected,
nonempty, moved to the right by `f`, and its frontier points are fixed by `f`. The developed image
of an `ℝP¹`-circle is one (`GX.IsLiftedDevPair.isComp`). -/
structure GTilde.IsComp (f : GTilde) (J : Set ℝ) : Prop where
  isOpen : IsOpen J
  isPreconnected : IsPreconnected J
  nonempty : J.Nonempty
  lt_apply : ∀ x ∈ J, x < f x
  fixed : ∀ y ∈ closure J, y ∉ J → f y = y

/-- A preconnected set of non-fixed points meeting a component lies in it. -/
theorem GTilde.IsComp.subset {f : GTilde} {J : Set ℝ} (hJ : GTilde.IsComp f J) {K : Set ℝ}
    (hK : IsPreconnected K) (hKf : ∀ x ∈ K, f x ≠ x) (hne : (K ∩ J).Nonempty) : K ⊆ J :=
  hK.subset_of_closure_inter_subset hJ.isOpen hne fun y ⟨hy, hyK⟩ => by
    by_contra hyJ
    exact hKf y hyK (hJ.fixed y hy hyJ)

/-- Two components which meet are equal. -/
theorem GTilde.IsComp.eq {f : GTilde} {J J' : Set ℝ} (hJ : GTilde.IsComp f J) (hJ' : GTilde.IsComp f J')
    (hne : (J ∩ J').Nonempty) : J = J' :=
  Subset.antisymm (hJ'.subset hJ.isPreconnected (fun x hx => (hJ.lt_apply x hx).ne') hne)
    (hJ.subset hJ'.isPreconnected (fun x hx => (hJ'.lt_apply x hx).ne')
      (by rwa [inter_comm] at hne))

/-- With no fixed point, the only component is `ℝ`. -/
theorem GTilde.IsComp.eq_univ {f : GTilde} {J : Set ℝ} (hJ : GTilde.IsComp f J) (hfix : ∀ x, f x ≠ x) :
    J = univ :=
  eq_univ_of_univ_subset (hJ.subset isPreconnected_univ (fun x _ => hfix x)
    (by obtain ⟨x, hx⟩ := hJ.nonempty; exact ⟨x, mem_univ x, hx⟩))

/-- A component containing no fixed point of `]c + m, c + m + 1[`... lies between two successive
integer translates of a fixed point. -/
theorem GTilde.IsComp.subset_Ioo {f : GTilde} {J : Set ℝ} (hJ : GTilde.IsComp f J) {c : ℝ}
    (hc : f c = c) {x : ℝ} (hx : x ∈ J) :
    J ⊆ Ioo (c + ⌊x - c⌋) (c + ⌊x - c⌋ + 1) := by
  have hfixn : ∀ n : ℤ, f (c + n) = c + n := fun n => by rw [map_add_int, hc]
  have hnot : ∀ n : ℤ, c + n ∉ J := fun n hn => (hJ.lt_apply _ hn).ne' (hfixn n)
  have h1 : c + ⌊x - c⌋ ≤ x := by have := Int.floor_le (x - c); linarith
  have h2 : x < c + ⌊x - c⌋ + 1 := by have := Int.lt_floor_add_one (x - c); linarith
  have h1' : c + ⌊x - c⌋ < x := lt_of_le_of_ne h1 fun h => hnot ⌊x - c⌋ (by rw [h]; exact hx)
  intro y hy
  constructor
  · by_contra hle
    push Not at hle
    exact hnot ⌊x - c⌋ (hJ.isPreconnected.Icc_subset hy hx ⟨hle, h1'.le⟩)
  · by_contra hle
    push Not at hle
    have := hJ.isPreconnected.Icc_subset hx hy ⟨h2.le, hle⟩
    exact hnot (⌊x - c⌋ + 1) (by push_cast; rwa [← add_assoc])

/-- `f ∈ G̃`, `f ≠ 1`, has at most one fixed point in `]c + m, c + m + 1[` when `c` is fixed. -/
theorem GTilde.eq_of_fixed_Ioo {f : GTilde} (hf : f ≠ 1) {c : ℝ} (hc : f c = c) (m : ℤ)
    {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Ioo (c + m) (c + m + 1)) (h₂ : c₂ ∈ Ioo (c + m) (c + m + 1))
    (hf₁ : f c₁ = c₁) (hf₂ : f c₂ = c₂) : c₁ = c₂ := by
  by_contra hne
  have hfix : ∀ {y : ℝ}, f y = y → toPSL f • RP1.proj y = RP1.proj y := fun hy => by
    rw [← proj_apply, hy]
  have hdist : ∀ {a b : ℝ}, (∀ n : ℤ, a ≠ b + n) → RP1.proj a ≠ RP1.proj b := fun hab h =>
    by obtain ⟨n, hn⟩ := RP1.proj_eq_proj_iff.1 h; exact hab n hn
  have hint : ∀ {a b : ℝ} (n : ℤ), |a - b| < 1 → a ≠ b → a ≠ b + n := fun {a b} n hab hne' h => by
    have : |(n : ℝ)| < 1 := by rw [h] at hab; simpa using hab
    have hn : n = 0 := by
      have := abs_lt.1 this
      have h1 : (-1 : ℝ) < n := this.1
      have h2 : (n : ℝ) < 1 := this.2
      have : -1 < n := by exact_mod_cast h1
      have : n < 1 := by exact_mod_cast h2
      omega
    exact hne' (by rw [h, hn]; simp)
  have hone : toPSL f = 1 := PSL2.eq_one_of_three_fixed (hfix hf₁) (hfix hf₂) (hfix hc)
    (hdist fun n => hint n (by rw [abs_lt]; constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]) hne)
    (hdist fun n h => by
      have : c₁ - c - m = n - m := by rw [h]; ring
      have hlo : (0 : ℝ) < n - m := by linarith [h₁.1]
      have hhi : (n : ℝ) - m < 1 := by linarith [h₁.2]
      have : (0 : ℤ) < n - m := by exact_mod_cast hlo
      have : n - m < (1 : ℤ) := by exact_mod_cast hhi
      omega)
    (hdist fun n h => by
      have hlo : (0 : ℝ) < n - m := by linarith [h₂.1]
      have hhi : (n : ℝ) - m < 1 := by linarith [h₂.2]
      have : (0 : ℤ) < n - m := by exact_mod_cast hlo
      have : n - m < (1 : ℤ) := by exact_mod_cast hhi
      omega)
  have hk : f ∈ toPSL.ker := hone
  rw [ker_toPSL, Subgroup.mem_zpowers_iff] at hk
  obtain ⟨j, rfl⟩ := hk
  rw [delta_zpow_apply] at hc
  have hj : (j : ℝ) = 0 := by linarith
  have : j = 0 := by exact_mod_cast hj
  exact hf (by rw [this, zpow_zero])

/-- An element of `G̃` moving every point of `[a, a + 1]` to the right, or fixing it, moves every
point to the right or fixes it. -/
theorem GTilde.le_apply_of_Icc {f : GTilde} {a : ℝ} (h : ∀ y ∈ Icc a (a + 1), y ≤ f y) (x : ℝ) :
    x ≤ f x := by
  set n := ⌊x - a⌋
  have h1 : a ≤ x - n := by have := Int.floor_le (x - a); linarith
  have h2 : x - n ≤ a + 1 := by have := Int.lt_floor_add_one (x - a); linarith
  have := h (x - n) ⟨h1, h2⟩
  have e : f x = f (x - n) + n := by
    rw [← map_add_int]; congr 1; ring
  linarith

/-- **Two components of the same `f` are translates of each other** by an integer. -/
theorem GTilde.IsComp.exists_add_int {f : GTilde} {J J' : Set ℝ} (hJ : GTilde.IsComp f J)
    (hJ' : GTilde.IsComp f J') : ∃ n : ℤ, (J' ∩ ((· + (n : ℝ)) '' J)).Nonempty := by
  have htr : ∀ n : ℤ, GTilde.IsComp f ((· + (n : ℝ)) '' J) := fun n => by
    have hh : IsOpenMap (· + (n : ℝ)) := (Homeomorph.addRight (n : ℝ)).isOpenMap
    refine ⟨hh _ hJ.isOpen, hJ.isPreconnected.image _ (continuous_add_const _).continuousOn,
      hJ.nonempty.image _, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [map_add_int]; linarith [hJ.lt_apply x hx]
    · intro y hy hyJ
      have hy' : y - n ∈ closure J := by
        have : (· + (n : ℝ)) '' J = (· - (n : ℝ)) ⁻¹' J := by
          ext z; simp only [mem_image, mem_preimage]
          exact ⟨fun ⟨x, hx, hz⟩ => by rw [← hz]; simpa using hx,
            fun hz => ⟨z - n, hz, by ring⟩⟩
        rw [this] at hy hyJ
        have := (continuous_sub_right (n : ℝ)).closure_preimage_subset J hy
        exact this
      have hyJ' : y - n ∉ J := fun h => hyJ ⟨y - n, h, by ring⟩
      have := hJ.fixed _ hy' hyJ'
      have e : f y = f (y - n) + n := by rw [← map_add_int]; congr 1; ring
      rw [e, this]; ring
  by_cases hfix : ∃ c, f c = c
  · obtain ⟨c, hc⟩ := hfix
    obtain ⟨x, hx⟩ := hJ.nonempty
    obtain ⟨x', hx'⟩ := hJ'.nonempty
    set m := ⌊x - c⌋
    set m' := ⌊x' - c⌋
    have hf1 : f ≠ 1 := fun h1 => by
      have := hJ.lt_apply x hx; rw [h1, one_apply] at this; exact lt_irrefl _ this
    have hJn := htr (m' - m)
    -- both lie in `K' = ]c + m', c + m' + 1[`
    have hsub' := hJ'.subset_Ioo hc hx'
    have hy : x + ((m' - m : ℤ) : ℝ) ∈ (· + ((m' - m : ℤ) : ℝ)) '' J := ⟨x, hx, rfl⟩
    have hsubn := GTilde.IsComp.subset_Ioo hJn hc hy
    have hm : ⌊x + ((m' - m : ℤ) : ℝ) - c⌋ = m' := by
      rw [show x + ((m' - m : ℤ) : ℝ) - c = (x - c) + ((m' - m : ℤ) : ℝ) by ring, Int.floor_add_intCast]
      ring
    rw [hm] at hsubn
    refine ⟨m' - m, ?_⟩
    by_cases hK : ∃ c₁ ∈ Ioo (c + m') (c + m' + 1), f c₁ = c₁
    · obtain ⟨c₁, hc₁K, hc₁⟩ := hK
      have huniq : ∀ y ∈ Ioo (c + m') (c + m' + 1), f y = y → y = c₁ := fun y hyK hfy =>
        GTilde.eq_of_fixed_Ioo hf1 hc m' hyK hc₁K hfy hc₁
      -- each component is one side of `c₁`
      have side : ∀ {I : Set ℝ}, GTilde.IsComp f I → I ⊆ Ioo (c + m') (c + m' + 1) →
          I = Ioo (c + m') c₁ ∨ I = Ioo c₁ (c + m' + 1) := fun {I} hI hIK => by
        have hnf : ∀ {S : Set ℝ}, S ⊆ Ioo (c + m') (c + m' + 1) → c₁ ∉ S → ∀ y ∈ S, f y ≠ y :=
          fun {S} hS hc₁S y hyS hfy => hc₁S (huniq y (hS hyS) hfy ▸ hyS)
        have hc₁I : c₁ ∉ I := fun h => (hI.lt_apply c₁ h).ne' hc₁
        obtain ⟨y, hyI⟩ := hI.nonempty
        rcases lt_or_gt_of_ne (show y ≠ c₁ from fun h => hc₁I (h ▸ hyI)) with hlt | hgt
        · left
          have h1 : I ⊆ Ioo (c + m') c₁ := fun z hz => ⟨(hIK hz).1, by
            by_contra hle; push Not at hle
            exact hc₁I (hI.isPreconnected.Icc_subset hyI hz ⟨hlt.le, hle⟩)⟩
          exact Subset.antisymm h1 (hI.subset isPreconnected_Ioo
            (hnf (Ioo_subset_Ioo_right (by linarith [hc₁K.2])) (fun h => lt_irrefl _ h.2))
            ⟨y, h1 hyI, hyI⟩)
        · right
          have h1 : I ⊆ Ioo c₁ (c + m' + 1) := fun z hz => ⟨by
            by_contra hle; push Not at hle
            exact hc₁I (hI.isPreconnected.Icc_subset hz hyI ⟨hle, hgt.le⟩), (hIK hz).2⟩
          exact Subset.antisymm h1 (hI.subset isPreconnected_Ioo
            (hnf (Ioo_subset_Ioo_left (by linarith [hc₁K.1])) (fun h => lt_irrefl _ h.1))
            ⟨y, h1 hyI, hyI⟩)
      rcases side hJ' hsub' with h1 | h1 <;> rcases side hJn hsubn with h2 | h2
      · rw [h1, ← h2, inter_self]; exact hJn.nonempty
      · exfalso
        -- `f` moves both sides to the right: `f ≥ id`
        have hle : ∀ x, x ≤ f x := GTilde.le_apply_of_Icc (a := c + m') fun y hy => by
          rcases eq_or_lt_of_le hy.1 with h | h
          · rw [← h, show c + (m' : ℝ) = c + ((m' : ℤ) : ℝ) from rfl, map_add_int, hc]
          rcases eq_or_lt_of_le hy.2 with h' | h'
          · rw [h', show c + (m' : ℝ) + 1 = c + ((m' + 1 : ℤ) : ℝ) by push_cast; ring,
              map_add_int, hc]
          rcases lt_trichotomy y c₁ with h3 | h3 | h3
          · exact (hJ'.lt_apply y (h1 ▸ ⟨h, h3⟩)).le
          · rw [h3, hc₁]
          · exact (hJn.lt_apply y (h2 ▸ ⟨h3, h'⟩)).le
        have hhyp : IsHyperbolic f := PSL2.isHyperbolic_of_two_fixed
          (fun h1' => hf1 (by
            have hk : f ∈ toPSL.ker := h1'
            rw [ker_toPSL, Subgroup.mem_zpowers_iff] at hk
            obtain ⟨j, rfl⟩ := hk
            rw [delta_zpow_apply] at hc
            have : (j : ℤ) = 0 := by exact_mod_cast (show (j : ℝ) = 0 by linarith)
            rw [this, zpow_zero]))
          (show toPSL f • RP1.proj c = RP1.proj c by rw [← proj_apply, hc])
          (show toPSL f • RP1.proj c₁ = RP1.proj c₁ by rw [← proj_apply, hc₁])
          (fun h => by
            obtain ⟨n, hn⟩ := RP1.proj_eq_proj_iff.1 h
            have hlo : (m' : ℝ) < -n := by linarith [hc₁K.1]
            have hhi : (-n : ℝ) < m' + 1 := by linarith [hc₁K.2]
            have : (m' : ℤ) < -n := by exact_mod_cast hlo
            have : -n < (m' + 1 : ℤ) := by exact_mod_cast hhi
            omega)
        exact hhyp.not_forall_le ⟨c, hc⟩ hle
      · exfalso
        have hle : ∀ x, x ≤ f x := GTilde.le_apply_of_Icc (a := c + m') fun y hy => by
          rcases eq_or_lt_of_le hy.1 with h | h
          · rw [← h, show c + (m' : ℝ) = c + ((m' : ℤ) : ℝ) from rfl, map_add_int, hc]
          rcases eq_or_lt_of_le hy.2 with h' | h'
          · rw [h', show c + (m' : ℝ) + 1 = c + ((m' + 1 : ℤ) : ℝ) by push_cast; ring,
              map_add_int, hc]
          rcases lt_trichotomy y c₁ with h3 | h3 | h3
          · exact (hJn.lt_apply y (h2 ▸ ⟨h, h3⟩)).le
          · rw [h3, hc₁]
          · exact (hJ'.lt_apply y (h1 ▸ ⟨h3, h'⟩)).le
        have hhyp : IsHyperbolic f := PSL2.isHyperbolic_of_two_fixed
          (fun h1' => hf1 (by
            have hk : f ∈ toPSL.ker := h1'
            rw [ker_toPSL, Subgroup.mem_zpowers_iff] at hk
            obtain ⟨j, rfl⟩ := hk
            rw [delta_zpow_apply] at hc
            have : (j : ℤ) = 0 := by exact_mod_cast (show (j : ℝ) = 0 by linarith)
            rw [this, zpow_zero]))
          (show toPSL f • RP1.proj c = RP1.proj c by rw [← proj_apply, hc])
          (show toPSL f • RP1.proj c₁ = RP1.proj c₁ by rw [← proj_apply, hc₁])
          (fun h => by
            obtain ⟨n, hn⟩ := RP1.proj_eq_proj_iff.1 h
            have hlo : (m' : ℝ) < -n := by linarith [hc₁K.1]
            have hhi : (-n : ℝ) < m' + 1 := by linarith [hc₁K.2]
            have : (m' : ℤ) < -n := by exact_mod_cast hlo
            have : -n < (m' + 1 : ℤ) := by exact_mod_cast hhi
            omega)
        exact hhyp.not_forall_le ⟨c, hc⟩ hle
      · rw [h1, ← h2, inter_self]; exact hJn.nonempty
    · push Not at hK
      have hKf : ∀ y ∈ Ioo (c + m') (c + m' + 1), f y ≠ y := hK
      have hK₁ := hJ'.subset isPreconnected_Ioo hKf ⟨x', hsub' hx', hx'⟩
      have hK₂ := hJn.subset isPreconnected_Ioo hKf ⟨_, hsubn hy, hy⟩
      exact ⟨x', hx', hK₂ (hsub' hx')⟩
  · push Not at hfix
    refine ⟨0, ?_⟩
    rw [(htr 0).eq_univ hfix, hJ'.eq_univ hfix, univ_inter]
    exact univ_nonempty


/-- A map `ℝ → ℝ` commuting with `t ↦ t + 1` commutes with every integer translation. -/
theorem map_add_int_of_add_one {Φ : ℝ → ℝ} (h : ∀ s, Φ (s + 1) = Φ s + 1) (s : ℝ) (n : ℤ) :
    Φ (s + n) = Φ s + n := by
  induction n using Int.induction_on generalizing s with
  | zero => simp
  | succ m ih =>
    have := h (s + m)
    push_cast at ih ⊢
    rw [← add_assoc, this, ih]; ring
  | pred m ih =>
    have h1 := h (s + (-(m : ℝ) - 1))
    have h2 := ih s
    push_cast at h1 h2 ⊢
    rw [show s + (-(m : ℝ) - 1) + 1 = s + -(m : ℝ) by ring, h2] at h1
    linarith

section Witness

variable {L : Type*} [TopologicalSpace L] [ChartedSpace RP1 L]
  [HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1)] {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}

/-- **The developed image of an `ℝP¹`-circle is a component** of `{x | x < f x}` bounded by fixed
points (l.713–719: `d` is a homeomorphism onto its image `I`, preserved by `ρ(1)`). -/
theorem IsLiftedDevPair.isComp (h : IsLiftedDevPair E D f) : GTilde.IsComp f (range D) := by
  obtain ⟨hE, hDc, hDm, hDd, hDf⟩ := h
  have hmaps : ∀ x ∈ range D, f x ∈ range D := by
    rintro _ ⟨s, rfl⟩; exact ⟨s + 1, hDf s⟩
  have hmaps' : ∀ x ∈ range D, f⁻¹ x ∈ range D := by
    rintro _ ⟨s, rfl⟩
    refine ⟨s - 1, ?_⟩
    have := hDf (s - 1)
    rw [sub_add_cancel] at this
    rw [this, GTilde.inv_apply_apply]
  refine ⟨(hDd.isLocalHomeomorph_lift hE.isCoveringMap.isLocalHomeomorph hDc).isOpenMap.isOpen_range,
    isPreconnected_range hDc, range_nonempty D, ?_, fun y hy hyJ => ?_⟩
  · rintro _ ⟨s, rfl⟩; rw [← hDf]; exact hDm (lt_add_one s)
  · have hJ := isPreconnected_range hDc
    by_cases hup : ∃ b ∈ range D, y < b
    · obtain ⟨b, hb, hyb⟩ := hup
      have hlow : range D ⊆ Ici y := fun a ha => by
        by_contra hay
        have hay' : a < y := not_le.1 hay
        exact hyJ (hJ.Icc_subset ha hb ⟨hay'.le, hyb.le⟩)
      have h1 : y ≤ f y := closure_minimal (fun x hx => show f x ∈ Ici y from hlow (hmaps x hx))
        (isClosed_Ici.preimage (GTilde.continuous f)) hy
      have h2 : y ≤ f⁻¹ y := closure_minimal
        (fun x hx => show f⁻¹ x ∈ Ici y from hlow (hmaps' x hx))
        (isClosed_Ici.preimage (GTilde.continuous f⁻¹)) hy
      have h3 := (GTilde.strictMono f).monotone h2
      rw [GTilde.apply_inv_apply] at h3
      exact le_antisymm h3 h1
    · push Not at hup
      have h1 : f y ≤ y := closure_minimal (fun x hx => (hup _ (hmaps x hx) : f x ≤ y))
        (isClosed_Iic.preimage (GTilde.continuous f)) hy
      have h2 : f⁻¹ y ≤ y := closure_minimal (fun x hx => (hup _ (hmaps' x hx) : f⁻¹ x ≤ y))
        (isClosed_Iic.preimage (GTilde.continuous f⁻¹)) hy
      have h3 := (GTilde.strictMono f).monotone h2
      rw [GTilde.apply_inv_apply] at h3
      exact le_antisymm h1 h3

/-- Translating a witness by `δⁿ` (central). -/
theorem IsLiftedDevPair.add_int (h : IsLiftedDevPair E D f) (n : ℤ) :
    IsLiftedDevPair E (fun s => D s + n) f := by
  obtain ⟨hE, hDc, hDm, hDd, hDf⟩ := h
  refine ⟨hE, hDc.add continuous_const, fun a b hab => by
    simp only; linarith [hDm hab], ?_, fun s => by simp only; rw [GTilde.map_add_int, hDf]⟩
  have : (RP1.proj ∘ fun s => D s + n) = RP1.proj ∘ D :=
    funext fun s => by simp only [Function.comp_apply, RP1.proj_add_int]
  rw [this]; exact hDd

/-- Conjugating a witness by `k ∈ G̃`. -/
theorem IsLiftedDevPair.conj (h : IsLiftedDevPair E D f) (k : GTilde) :
    IsLiftedDevPair E (fun s => k (D s)) (k * f * k⁻¹) := by
  obtain ⟨hE, hDc, hDm, hDd, hDf⟩ := h
  refine ⟨hE, (GTilde.continuous k).comp hDc, (GTilde.strictMono k).comp hDm, fun s => ?_,
    fun s => ?_⟩
  · obtain ⟨g, hg⟩ := hDd s
    refine ⟨GTilde.toPSL k * g, hg.mono fun s' hs' => ?_⟩
    simp only [Function.comp_apply] at hs' ⊢
    rw [GTilde.proj_apply, hs', mul_smul]
  · simp only
    rw [hDf, GTilde.coe_mul_apply, GTilde.coe_mul_apply, GTilde.inv_apply_apply]

end Witness

/-- The factor `g` with a fixed point is transported by the relation of two lifted developing
pairs: `f = δᵏ g`, `f' = κ f κ⁻¹ = δ^{k'} g'` give `g' = κ g κ⁻¹`. -/
theorem GTilde.conj_factor {f f' g g' κ : GTilde} {k k' : ℤ} (hg : ∃ x, g x = x)
    (hg' : ∃ x, g' x = x) (hfg : f = GTilde.delta ^ k * g) (hfg' : f' = GTilde.delta ^ k' * g')
    (hf' : f' = κ * f * κ⁻¹) : g' = κ * g * κ⁻¹ := by
  have hc : κ * GTilde.delta ^ k = GTilde.delta ^ k * κ :=
    (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ GTilde.delta_mem_center k)) κ
  have e : f' = GTilde.delta ^ k * (κ * g * κ⁻¹) := by
    rw [hf', hfg, ← mul_assoc, hc, mul_assoc, mul_assoc, mul_assoc]
  obtain ⟨x, hx⟩ := hg
  have hfix : (κ * g * κ⁻¹) (κ x) = κ x := by
    rw [GTilde.coe_mul_apply, GTilde.coe_mul_apply, GTilde.inv_apply_apply, hx]
  have hkk : k' = k := GTilde.delta_zpow_mul_unique hg' ⟨κ x, hfix⟩ (hfg'.symm.trans e)
  rw [hkk] at hfg'
  exact mul_left_cancel (hfg'.symm.trans e)

/-- A lifted holonomy `δᵏ g` with `k ≠ 0` and `g` having a fixed point has no fixed point. -/
theorem GTilde.apply_ne_of_degree_ne_zero {f g : GTilde} {k : ℤ} (hk : k ≠ 0)
    (hg : ∃ x, g x = x) (hfg : f = GTilde.delta ^ k * g) (x : ℝ) : f x ≠ x := fun hx => by
  have h1 := GTilde.angle_eq_zero_of_fixed hx
  rw [GTilde.angle_eq_of_delta_zpow_mul hg hfg] at h1
  have : (k : ℝ) = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h (by positivity)
    · exact h
  exact hk (by exact_mod_cast this)

/-- Without fixed point in `]a, b[`, an element of `G̃` moves all of `]a, b[` in one direction. -/
theorem GTilde.lt_apply_of_no_fixed {f : GTilde} {a b : ℝ} (h : ∀ y ∈ Ioo a b, f y ≠ y)
    {y₁ y₂ : ℝ} (h₁ : y₁ ∈ Ioo a b) (h₂ : y₂ ∈ Ioo a b) (hy₁ : y₁ < f y₁) : y₂ < f y₂ := by
  by_contra hy₂
  have hy₂' : f y₂ < y₂ := lt_of_le_of_ne (not_lt.1 hy₂) (h y₂ h₂)
  have hc : ContinuousOn (fun y => f y - y) (uIcc y₁ y₂) :=
    ((GTilde.continuous f).sub continuous_id).continuousOn
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc hc
    (show (0 : ℝ) ∈ uIcc (f y₁ - y₁) (f y₂ - y₂) from
      Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩))
  have hzI : z ∈ Ioo a b := by
    rcases Set.mem_uIcc.1 hz with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      exact ⟨by linarith [h₁.1, h₂.1], by linarith [h₁.2, h₂.2]⟩
  exact h z hzI (by simp only at hz0; linarith)

theorem GTilde.apply_le_of_Icc {f : GTilde} {a : ℝ} (h : ∀ y ∈ Icc a (a + 1), f y ≤ y) (x : ℝ) :
    f x ≤ x := by
  set n := ⌊x - a⌋
  have h1 : a ≤ x - n := by have := Int.floor_le (x - a); linarith
  have h2 : x - n ≤ a + 1 := by have := Int.lt_floor_add_one (x - a); linarith
  have := h (x - n) ⟨h1, h2⟩
  have e : f x = f (x - n) + n := by rw [← GTilde.map_add_int]; congr 1; ring
  linarith

/-- **The fixed points of a hyperbolic `g ∈ G̃` with a fixed point `c`**: exactly one more in
`]c, c + 1[`, `c₁`, and `g` moves `]c, c₁[` and `]c₁, c + 1[` in opposite directions. -/
theorem GTilde.IsHyperbolic.fixed_structure {f : GTilde} (hf : IsHyperbolic f) {c : ℝ}
    (hc : f c = c) : ∃ c₁ ∈ Ioo c (c + 1), f c₁ = c₁ ∧
      (∀ y ∈ Ioo c (c + 1), f y = y → y = c₁) ∧
      (((∀ y ∈ Ioo c c₁, y < f y) ∧ ∀ y ∈ Ioo c₁ (c + 1), f y < y) ∨
        ((∀ y ∈ Ioo c c₁, f y < y) ∧ ∀ y ∈ Ioo c₁ (c + 1), y < f y)) := by
  have hf1 : f ≠ 1 := fun h => hf.toPSL_ne_one (by rw [h, map_one])
  have hc1 : f (c + 1) = c + 1 := by
    have := GTilde.map_add_int f c 1; push_cast at this; rw [this, hc]
  -- a second fixed point
  obtain ⟨c₁, hc₁I, hc₁⟩ : ∃ c₁ ∈ Ioo c (c + 1), f c₁ = c₁ := by
    by_contra hno
    push Not at hno
    have hmid : c + 1 / 2 ∈ Ioo c (c + 1) := ⟨by linarith, by linarith⟩
    rcases lt_or_gt_of_ne (hno _ hmid) with hlt | hgt
    · exact hf.not_forall_ge ⟨c, hc⟩ (GTilde.apply_le_of_Icc (a := c) fun y hy => by
        rcases eq_or_lt_of_le hy.1 with h | h
        · rw [← h, hc]
        rcases eq_or_lt_of_le hy.2 with h' | h'
        · rw [h', hc1]
        by_contra hle
        exact (not_lt.2 (le_of_lt (not_le.1 hle)))
          (by
            have := GTilde.lt_apply_of_no_fixed hno ⟨h, h'⟩ hmid (lt_of_le_of_ne
              (le_of_lt (not_le.1 hle)) (hno y ⟨h, h'⟩).symm)
            linarith))
    · exact hf.not_forall_le ⟨c, hc⟩ (GTilde.le_apply_of_Icc (a := c) fun y hy => by
        rcases eq_or_lt_of_le hy.1 with h | h
        · rw [← h, hc]
        rcases eq_or_lt_of_le hy.2 with h' | h'
        · rw [h', hc1]
        exact (GTilde.lt_apply_of_no_fixed hno hmid ⟨h, h'⟩ hgt).le)
  have huniq : ∀ y ∈ Ioo c (c + 1), f y = y → y = c₁ := fun y hy hfy =>
    GTilde.eq_of_fixed_Ioo hf1 hc 0 (by simpa using hy) (by simpa using hc₁I) hfy hc₁
  have hno₀ : ∀ y ∈ Ioo c c₁, f y ≠ y := fun y hy hfy =>
    (huniq y ⟨hy.1, hy.2.trans hc₁I.2⟩ hfy ▸ hy).2.false
  have hno₁ : ∀ y ∈ Ioo c₁ (c + 1), f y ≠ y := fun y hy hfy =>
    (huniq y ⟨hc₁I.1.trans hy.1, hy.2⟩ hfy ▸ hy).1.false
  have hm₀ : (c + c₁) / 2 ∈ Ioo c c₁ := ⟨by linarith [hc₁I.1], by linarith [hc₁I.1]⟩
  have hm₁ : (c₁ + (c + 1)) / 2 ∈ Ioo c₁ (c + 1) := ⟨by linarith [hc₁I.2], by linarith [hc₁I.2]⟩
  have dir : ∀ {a b : ℝ} (hno : ∀ y ∈ Ioo a b, f y ≠ y) {m : ℝ}, m ∈ Ioo a b →
      (∀ y ∈ Ioo a b, y < f y) ∨ (∀ y ∈ Ioo a b, f y < y) := fun {a b} hno {m} hm => by
    rcases lt_or_gt_of_ne (hno m hm) with h | h
    · right
      intro y hy
      by_contra hle
      exact (not_lt.2 (le_of_lt (GTilde.lt_apply_of_no_fixed hno hy hm (lt_of_le_of_ne
        (not_lt.1 hle) (hno y hy).symm)))) h
    · left
      exact fun y hy => GTilde.lt_apply_of_no_fixed hno hm hy h
  refine ⟨c₁, hc₁I, hc₁, huniq, ?_⟩
  have hIcc : ∀ y ∈ Icc c (c + 1), y = c ∨ y = c₁ ∨ y = c + 1 ∨ y ∈ Ioo c c₁ ∨
      y ∈ Ioo c₁ (c + 1) := fun y hy => by
    rcases eq_or_lt_of_le hy.1 with h | h
    · exact Or.inl h.symm
    rcases eq_or_lt_of_le hy.2 with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    rcases lt_trichotomy y c₁ with h3 | h3 | h3
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, h3⟩)))
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, h'⟩)))
  rcases dir hno₀ hm₀ with d₀ | d₀ <;> rcases dir hno₁ hm₁ with d₁ | d₁
  · exfalso
    exact hf.not_forall_le ⟨c, hc⟩ (GTilde.le_apply_of_Icc (a := c) fun y hy => by
      rcases hIcc y hy with rfl | rfl | rfl | h | h
      · rw [hc]
      · rw [hc₁]
      · rw [hc1]
      · exact (d₀ y h).le
      · exact (d₁ y h).le)
  · exact Or.inl ⟨d₀, d₁⟩
  · exact Or.inr ⟨d₀, d₁⟩
  · exfalso
    exact hf.not_forall_ge ⟨c, hc⟩ (GTilde.apply_le_of_Icc (a := c) fun y hy => by
      rcases hIcc y hy with rfl | rfl | rfl | h | h
      · rw [hc]
      · rw [hc₁]
      · rw [hc1]
      · exact (d₀ y h).le
      · exact (d₁ y h).le)

section Iso2

variable {L L' : Type*} [TopologicalSpace L] [ChartedSpace RP1 L]
  [HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1)] [TopologicalSpace L'] [ChartedSpace RP1 L']
  [HasGroupoid L' (gxGroupoid PSL(2, ℝ) RP1)]

/-- **l.721–723, "if"** (oriented form, l.723–731): `ℝP¹`-circles with conjugate lifted holonomies are isomorphic. -/
theorem exists_rp1Iso_of_conj {f f' : GTilde} (hf : HasLiftedHolonomy L f)
    (hf' : HasLiftedHolonomy L' f') (hc : ∃ h : GTilde, f' = h * f * h⁻¹) :
    ∃ φ : L ≃ₜ L', IsRP1Iso φ := by
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨E, D₀, h₀⟩ := hf
  obtain ⟨E', D', h'⟩ := hf'
  have h₀ : IsLiftedDevPair E D₀ f := h₀
  have h' : IsLiftedDevPair E' D' (k * f * k⁻¹) := h'
  have h₁ := h₀.conj k
  obtain ⟨n, hn⟩ := h₁.isComp.exists_add_int h'.isComp
  have h₂ := h₁.add_int n
  set D₂ : ℝ → ℝ := fun s => k (D₀ s) + n with hD₂
  have hr : range D' = range D₂ := h'.isComp.eq h₂.isComp (by
    rwa [show range D₂ = (· + (n : ℝ)) '' range (fun s => k (D₀ s)) from
      (range_comp (· + (n : ℝ)) (fun s => k (D₀ s)))])
  have hex : ∀ s, D₂ s ∈ range D' := fun s => hr ▸ mem_range_self s
  have hex' : ∀ t, D' t ∈ range D₂ := fun t => hr ▸ mem_range_self t
  choose Φ hΦ using hex
  choose Ψ hΨ using hex'
  have hD'm := h'.2.2.1
  have hD₂m := h₂.2.2.1
  have hΦΨ : ∀ t, Φ (Ψ t) = t := fun t => hD'm.injective (by rw [hΦ, hΨ])
  have hΨΦ : ∀ s, Ψ (Φ s) = s := fun s => hD₂m.injective (by rw [hΨ, hΦ])
  have hΦm : StrictMono Φ := fun a b hab => by
    rw [← hD'm.lt_iff_lt, hΦ, hΦ]; exact hD₂m hab
  have hΨm : StrictMono Ψ := fun a b hab => by
    rw [← hD₂m.lt_iff_lt, hΨ, hΨ]; exact hD'm hab
  have hΦc : Continuous Φ := hΦm.monotone.continuous_of_surjective fun t => ⟨Ψ t, hΦΨ t⟩
  have hΨc : Continuous Ψ := hΨm.monotone.continuous_of_surjective fun s => ⟨Φ s, hΨΦ s⟩
  have hΦ1 : ∀ s, Φ (s + 1) = Φ s + 1 := fun s => hD'm.injective (by
    rw [hΦ, h'.2.2.2.2, hΦ, h₂.2.2.2.2])
  have hΨ1 : ∀ t, Ψ (t + 1) = Ψ t + 1 := fun t => hD₂m.injective (by
    rw [hΨ, h₂.2.2.2.2, hΨ, h'.2.2.2.2])
  have hE := h₀.1
  have hE' := h'.1
  -- descend `Φ` and `Ψ`
  let φ₀ : L → L' := fun x => E' (Φ (Classical.choose (hE.surjective x)))
  let ψ₀ : L' → L := fun y => E (Ψ (Classical.choose (hE'.surjective y)))
  have hφ₀ : ∀ s, φ₀ (E s) = E' (Φ s) := fun s => by
    have hs := Classical.choose_spec (hE.surjective (E s))
    show E' (Φ (Classical.choose (hE.surjective (E s)))) = E' (Φ s)
    generalize Classical.choose (hE.surjective (E s)) = s₀ at hs ⊢
    obtain ⟨m, hm⟩ := hE.fiber _ s hs
    rw [hm, map_add_int_of_add_one hΦ1, hE'.add_int]
  have hψ₀ : ∀ t, ψ₀ (E' t) = E (Ψ t) := fun t => by
    have ht := Classical.choose_spec (hE'.surjective (E' t))
    show E (Ψ (Classical.choose (hE'.surjective (E' t)))) = E (Ψ t)
    generalize Classical.choose (hE'.surjective (E' t)) = t₀ at ht ⊢
    obtain ⟨m, hm⟩ := hE'.fiber _ t ht
    rw [hm, map_add_int_of_add_one hΨ1, hE.add_int]
  have hqE := hE.isCoveringMap.isQuotientMap hE.surjective
  have hqE' := hE'.isCoveringMap.isQuotientMap hE'.surjective
  have hφc : Continuous φ₀ := hqE.continuous_iff.2 (by
    have : φ₀ ∘ E = E' ∘ Φ := funext hφ₀
    rw [this]; exact hE'.isCoveringMap.continuous.comp hΦc)
  have hψc : Continuous ψ₀ := hqE'.continuous_iff.2 (by
    have : ψ₀ ∘ E' = E ∘ Ψ := funext hψ₀
    rw [this]; exact hE.isCoveringMap.continuous.comp hΨc)
  let φ : L ≃ₜ L' :=
    { toFun := φ₀
      invFun := ψ₀
      left_inv := fun x => by
        obtain ⟨s, rfl⟩ := hE.surjective x
        rw [hφ₀, hψ₀, hΨΦ]
      right_inv := fun y => by
        obtain ⟨t, rfl⟩ := hE'.surjective y
        rw [hψ₀, hφ₀, hΦΨ]
      continuous_toFun := hφc
      continuous_invFun := hψc }
  refine ⟨φ, hφc, fun x => ?_⟩
  obtain ⟨s, rfl⟩ := hE.surjective x
  obtain ⟨g₁, hg₁⟩ := h₂.2.2.2.1 s
  obtain ⟨g₂, hg₂⟩ := h'.2.2.2.1 (Φ s)
  have hev : ∀ᶠ s' in 𝓝 s, chartAt RP1 (φ (E s)) (φ (E s')) =
      (g₂⁻¹ * g₁) • chartAt RP1 (E s) (E s') := by
    filter_upwards [hg₁, hΦc.continuousAt.eventually hg₂] with s' h1 h2
    simp only [Function.comp_apply] at h1 h2
    show chartAt RP1 (φ₀ (E s)) (φ₀ (E s')) = _
    rw [hφ₀, hφ₀, mul_smul, ← h1, ← hΦ, h2, inv_smul_smul]
  exact ⟨g₂⁻¹ * g₁, Filter.mem_of_superset (hE.isCoveringMap.isOpenMap.image_mem_nhds hev)
    (by rintro _ ⟨s', hs', rfl⟩; exact hs')⟩

/-- **l.721–723, in the oriented form of l.723–731**: two `ℝP¹`-circles are isomorphic iff their
lifted holonomies (the elements `ρ(γ₀)` of the canonical generator, l.733–737) are conjugate in
`G̃`. The printed "holonomy groups are conjugate" is the group form; it is proved here only for
equal hyperbolic groups (`GX.rp1Iso_of_zpowers_eq`). -/
theorem rp1Iso_iff_conj {f f' : GTilde} (hf : HasLiftedHolonomy L f)
    (hf' : HasLiftedHolonomy L' f') :
    (∃ φ : L ≃ₜ L', IsRP1Iso φ) ↔ ∃ h : GTilde, f' = h * f * h⁻¹ :=
  ⟨fun ⟨_, hφ⟩ => conj_of_rp1Iso hφ hf hf', exists_rp1Iso_of_conj hf hf'⟩

end Iso2

/-! ## 3. The developed image: "these examples exhaust the list" (l.688–719) -/

section Image

variable {L : Type*} [TopologicalSpace L] [ChartedSpace RP1 L]
  [HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1)]

/-- **The classification of `ℝP¹`-circles by their developed image** (l.688–719): for every
witness `(E, D)` of the lifted holonomy `f` of an `ℝP¹`-circle, exactly one of
* (elliptic circles, l.690–694) `f` is elliptic or central, and `D` is onto `ℝP̃¹`;
* (degree `k ≥ 1`, l.696–703) `f = δᵏ g`, `k ≥ 1`, `g` parabolic or hyperbolic with a fixed point,
  and `D` is onto;
* (degree `0`, l.705–710) `f` is parabolic or hyperbolic with a fixed point, and `D` is onto
  `]x₀, x₁[` for two successive fixed points `x₀ < x₁` of `f`: `x₁ = δ x₀` if `f` is parabolic,
  `x₁ < δ x₀` if `f` is hyperbolic. -/
theorem IsLiftedDevPair.exhaust {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}
    (h : IsLiftedDevPair E D f) :
    ((GTilde.IsElliptic f ∨ GTilde.toPSL f = 1) ∧ range D = univ) ∨
    (∃ k : ℤ, 1 ≤ k ∧ ∃ g : GTilde, (∃ x, g x = x) ∧
      (GTilde.IsParabolic g ∨ GTilde.IsHyperbolic g) ∧ f = GTilde.delta ^ k * g ∧
      range D = univ) ∨
    ((GTilde.IsParabolic f ∨ GTilde.IsHyperbolic f) ∧ ∃ x₀ x₁ : ℝ, x₀ < x₁ ∧ f x₀ = x₀ ∧
      f x₁ = x₁ ∧ range D = Ioo x₀ x₁ ∧ (GTilde.IsParabolic f → x₁ = GTilde.delta x₀) ∧
      (GTilde.IsHyperbolic f → x₁ < GTilde.delta x₀)) := by
  have hJ := h.isComp
  have hW : HasLiftedHolonomy L f := ⟨E, D, h⟩
  by_cases he : GTilde.IsElliptic f ∨ GTilde.toPSL f = 1
  · left
    refine ⟨he, hJ.eq_univ fun x hx => ?_⟩
    rcases he with he | he
    · exact he.apply_ne x hx
    · have hk : f ∈ GTilde.toPSL.ker := he
      rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hk
      obtain ⟨j, rfl⟩ := hk
      rw [GTilde.delta_zpow_apply] at hx
      obtain ⟨y, hy⟩ := hJ.nonempty
      have := hJ.lt_apply y hy
      rw [GTilde.delta_zpow_apply] at this
      linarith
  · right
    push Not at he
    obtain ⟨k, g, hg, hfg⟩ := GTilde.exists_delta_zpow_mul_of_not_isElliptic he.1
    have hk0 := hW.deg_nonneg hg hfg
    have hpsl : GTilde.toPSL g = GTilde.toPSL f := by
      rw [hfg, map_mul, map_zpow, GTilde.toPSL_delta, one_zpow, one_mul]
    have hpg : GTilde.IsParabolic f ∨ GTilde.IsHyperbolic f := by
      rcases PSL2.trichotomy (GTilde.toPSL f) with h1 | h1 | h1 | h1
      · exact absurd h1 he.2
      · exact absurd h1 he.1
      · exact Or.inl h1
      · exact Or.inr h1
    rcases hk0.lt_or_eq with hk | hk
    · left
      refine ⟨k, hk, g, hg, ?_, hfg, hJ.eq_univ
        (GTilde.apply_ne_of_degree_ne_zero (ne_of_gt hk) hg hfg)⟩
      unfold GTilde.IsParabolic GTilde.IsHyperbolic at hpg ⊢
      rwa [hpsl]
    · right
      rw [← hk, zpow_zero, one_mul] at hfg
      subst hfg
      obtain ⟨c, hc⟩ := hg
      obtain ⟨y₀, hy₀⟩ := hJ.nonempty
      have hsub := hJ.subset_Ioo hc hy₀
      set m := ⌊y₀ - c⌋
      have hbdd : BddAbove (range D) := ⟨c + m + 1, fun y hy => (hsub hy).2.le⟩
      have hbdd' : BddBelow (range D) := ⟨c + m, fun y hy => (hsub hy).1.le⟩
      set x₀ := sInf (range D)
      set x₁ := sSup (range D)
      have hJeq : range D = Ioo x₀ x₁ := by
        ext y
        constructor
        · intro hy
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJ.isOpen y hy
          have h1 : y + ε / 2 ∈ range D := hball (by
            rw [Metric.mem_ball, Real.dist_eq, show y + ε / 2 - y = ε / 2 by ring,
              abs_of_pos (by positivity)]; linarith)
          have h2 : y - ε / 2 ∈ range D := hball (by
            rw [Metric.mem_ball, Real.dist_eq, show y - ε / 2 - y = -(ε / 2) by ring, abs_neg,
              abs_of_pos (by positivity)]; linarith)
          exact ⟨lt_of_le_of_lt (csInf_le hbdd' h2) (by linarith),
            lt_of_lt_of_le (by linarith) (le_csSup hbdd h1)⟩
        · rintro ⟨h1, h2⟩
          obtain ⟨b, hb, hyb⟩ := exists_lt_of_lt_csSup hJ.nonempty h2
          obtain ⟨a, ha, hay⟩ := exists_lt_of_csInf_lt hJ.nonempty h1
          exact hJ.isPreconnected.Icc_subset ha hb ⟨hay.le, hyb.le⟩
      have hlt : x₀ < x₁ := by
        have := hJeq ▸ hy₀; exact this.1.trans this.2
      have hcl : closure (range D) = Icc x₀ x₁ := by rw [hJeq, closure_Ioo hlt.ne]
      have hx₀ : f x₀ = x₀ := hJ.fixed x₀ (hcl ▸ left_mem_Icc.2 hlt.le)
        (by rw [hJeq]; exact fun h => lt_irrefl _ h.1)
      have hx₁ : f x₁ = x₁ := hJ.fixed x₁ (hcl ▸ right_mem_Icc.2 hlt.le)
        (by rw [hJeq]; exact fun h => lt_irrefl _ h.2)
      have hx₀1 : f (x₀ + 1) = x₀ + 1 := by
        have := GTilde.map_add_int f x₀ 1; push_cast at this; rw [this, hx₀]
      have hle1 : x₁ ≤ x₀ + 1 := by
        by_contra h3
        push Not at h3
        have hin : x₀ + 1 ∈ range D := hJeq ▸ ⟨by linarith, h3⟩
        exact (hJ.lt_apply _ hin).ne' hx₀1
      refine ⟨hpg, x₀, x₁, hlt, hx₀, hx₁, hJeq, fun hpar => ?_, fun hhyp => ?_⟩
      · obtain ⟨n, hn⟩ := hpar.eq_add_int_of_fixed hx₀ hx₁
        rw [GTilde.delta_apply]
        have hn1 : (1 : ℝ) ≤ n := by
          have : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
          exact_mod_cast this
        linarith
      · rw [GTilde.delta_apply]
        rcases hle1.lt_or_eq with h3 | h3
        · exact h3
        · exfalso
          refine hhyp.not_forall_le ⟨x₀, hx₀⟩ (GTilde.le_apply_of_Icc (a := x₀) fun y hy => ?_)
          rcases eq_or_lt_of_le hy.1 with h4 | h4
          · rw [← h4, hx₀]
          rcases eq_or_lt_of_le hy.2 with h5 | h5
          · rw [h5, hx₀1]
          exact (hJ.lt_apply y (hJeq ▸ ⟨h4, h3 ▸ h5⟩)).le

end Image

/-! ## 4. The parametrisations (l.739–760) -/

namespace GTilde

/-- `x` is a **repelling** fixed point of `g`: `g x = x`, and near `x` the other points are moved
away from `x`. -/
def IsRepellingAt (g : GTilde) (x : ℝ) : Prop :=
  g x = x ∧ ∀ᶠ y in 𝓝[≠] x, |y - x| < |g y - x|

/-- `x` is an **attracting** fixed point of `g`. -/
def IsAttractingAt (g : GTilde) (x : ℝ) : Prop :=
  g x = x ∧ ∀ᶠ y in 𝓝[≠] x, |g y - x| < |y - x|

/-- **The two parabolic classes** (l.748–750): a parabolic `g ∈ G̃` with a fixed point is
positive (`g x ≥ x` everywhere) or negative (`g x ≤ x` everywhere), and not both. -/
theorem IsParabolic.le_or_ge {f : GTilde} (hf : IsParabolic f) (hfix : ∃ x, f x = x) :
    ((∀ x, x ≤ f x) ∨ (∀ x, f x ≤ x)) ∧ ¬ ((∀ x, x ≤ f x) ∧ (∀ x, f x ≤ x)) := by
  refine ⟨?_, fun ⟨h1, h2⟩ => hf.2 ?_⟩
  · by_cases hgt : ∃ x, x < f x
    · exact Or.inl (hf.le_apply hfix hgt)
    · push Not at hgt
      exact Or.inr hgt
  · have : f = 1 := ext' fun x => by rw [one_apply]; exact le_antisymm (h2 x) (h1 x)
    rw [this, map_one]

end GTilde

namespace PSL2

/-- `tr²` is a conjugacy invariant of `PSL(2,ℝ)`. -/
theorem trSq_conj (c g : PSL(2, ℝ)) : trSq (c * g * c⁻¹) = trSq g := by
  obtain ⟨C, rfl⟩ := pslMk_surjective c
  obtain ⟨A, rfl⟩ := pslMk_surjective g
  have e : pslMk C * pslMk A * (pslMk C)⁻¹ = pslMk (C * A * C⁻¹) := by
    simp only [pslMk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [e, trSq_mk, trSq_mk, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.trace_mul_cycle, Matrix.adjugate_mul, C.2,
    one_smul, Matrix.one_mul]

/-- **Hyperbolic conjugacy classes are parametrised by the absolute value of the trace**
(l.747–748): two hyperbolic elements of `PSL(2,ℝ)` are conjugate iff `tr² ` agree. -/
theorem IsHyperbolic.isConj_iff {g g' : PSL(2, ℝ)} (hg : IsHyperbolic g) (hg' : IsHyperbolic g') :
    (∃ c : PSL(2, ℝ), g' = c * g * c⁻¹) ↔ trSq g = trSq g' :=
  ⟨fun ⟨c, hc⟩ => by rw [hc, trSq_conj], exists_conj_of_trSq_eq hg hg'⟩

/-- **There are exactly two parabolic conjugacy classes** (l.748–750): two parabolic elements of
`PSL(2,ℝ)` are conjugate iff their lifts with a fixed point are both positive or both
negative. -/
theorem IsParabolic.isConj_iff {g g' : PSL(2, ℝ)} (hg : IsParabolic g) (hg' : IsParabolic g')
    {f f' : GTilde} (hf : GTilde.toPSL f = g) (hf' : GTilde.toPSL f' = g') (hfix : ∃ x, f x = x)
    (hfix' : ∃ x, f' x = x) :
    (∃ c : PSL(2, ℝ), g' = c * g * c⁻¹) ↔ ((∀ x, x ≤ f x) ↔ (∀ x, x ≤ f' x)) :=
  isConj_iff_forall_le hg hg' hf hf' hfix hfix'

end PSL2

section Param

variable {L L' : Type*} [TopologicalSpace L] [ChartedSpace RP1 L]
  [HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1)] [TopologicalSpace L'] [ChartedSpace RP1 L']
  [HasGroupoid L' (gxGroupoid PSL(2, ℝ) RP1)]

/-- **The elliptic case, injectivity** (l.742–744): elliptic `ℝP¹`-circles (central holonomy
included, OQ-113 (d)) with the same real angle are isomorphic. -/
theorem rp1Iso_of_angle_eq {f f' : GTilde} (hf : HasLiftedHolonomy L f)
    (hf' : HasLiftedHolonomy L' f') (he : GTilde.IsElliptic f ∨ GTilde.toPSL f = 1)
    (he' : GTilde.IsElliptic f' ∨ GTilde.toPSL f' = 1) (hθ : GTilde.angle f = GTilde.angle f') :
    ∃ φ : L ≃ₜ L', IsRP1Iso φ :=
  (rp1Iso_iff_conj hf hf').2 (GTilde.exists_conj_of_angle_eq he he' hθ)

/-- **The case `k ≥ 1`** (l.746–747): non-elliptic `ℝP¹`-circles of degree `k ≥ 1` are
parametrised by `(k, [g])`, `[g]` the conjugacy class of `g` in `G = PSL(2,ℝ)`. Proved for every
degree (`k ≥ 1` is not used; at `k = 0` it is the parametrisation of l.756–757 by `[g]`). -/
theorem rp1Iso_iff_of_degree_pos {f f' g g' : GTilde} {k k' : ℤ} (hf : HasLiftedHolonomy L f)
    (hf' : HasLiftedHolonomy L' f') (hg : ∃ x, g x = x)
    (hg' : ∃ x, g' x = x) (hfg : f = GTilde.delta ^ k * g) (hfg' : f' = GTilde.delta ^ k' * g') :
    (∃ φ : L ≃ₜ L', IsRP1Iso φ) ↔
      k = k' ∧ ∃ c : PSL(2, ℝ), GTilde.toPSL g' = c * GTilde.toPSL g * c⁻¹ := by
  rw [rp1Iso_iff_conj hf hf']
  constructor
  · rintro ⟨κ, hκ⟩
    have hgg := GTilde.conj_factor hg hg' hfg hfg' hκ
    obtain ⟨x, hx⟩ := hg
    have hfix : (κ * g * κ⁻¹) (κ x) = κ x := by
      rw [GTilde.coe_mul_apply, GTilde.coe_mul_apply, GTilde.inv_apply_apply, hx]
    have hc : κ * GTilde.delta ^ k = GTilde.delta ^ k * κ :=
      (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ GTilde.delta_mem_center k)) κ
    have e : f' = GTilde.delta ^ k * (κ * g * κ⁻¹) := by
      rw [hκ, hfg, ← mul_assoc, hc, mul_assoc, mul_assoc, mul_assoc]
    refine ⟨GTilde.delta_zpow_mul_unique ⟨κ x, hfix⟩ hg' (e.symm.trans hfg'), GTilde.toPSL κ, ?_⟩
    rw [hgg, map_mul, map_mul, map_inv]
  · rintro ⟨rfl, c, hc⟩
    obtain ⟨κ, rfl⟩ := GTilde.toPSL_surjective c
    obtain ⟨x, hx⟩ := hg
    have hfix : (κ * g * κ⁻¹) (κ x) = κ x := by
      rw [GTilde.coe_mul_apply, GTilde.coe_mul_apply, GTilde.inv_apply_apply, hx]
    have hker : g' * (κ * g * κ⁻¹)⁻¹ ∈ GTilde.toPSL.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hc, mul_inv_cancel]
    rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hker
    obtain ⟨n, hn⟩ := hker
    have hgn : g' = GTilde.delta ^ n * (κ * g * κ⁻¹) := by rw [hn, inv_mul_cancel_right]
    have hn0 : (0 : ℤ) = n := GTilde.delta_zpow_mul_unique hg' ⟨κ x, hfix⟩
      (by rw [zpow_zero, one_mul, ← hgn])
    rw [← hn0, zpow_zero, one_mul] at hgn
    have hc' : κ * GTilde.delta ^ k = GTilde.delta ^ k * κ :=
      (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ GTilde.delta_mem_center k)) κ
    refine ⟨κ, ?_⟩
    rw [hfg', hgn, hfg, ← mul_assoc κ (GTilde.delta ^ k) g, hc']
    group

/-- **The case `k = 0`, parabolic** (l.752–756): every parabolic `ℝP¹`-circle of degree `0` is
positive. -/
theorem HasLiftedHolonomy.le_apply_of_parabolic {f : GTilde} (hf : HasLiftedHolonomy L f)
    (hp : GTilde.IsParabolic f) (hfix : ∃ x, f x = x) : ∀ x, x ≤ f x :=
  hp.le_apply hfix hf.lt_apply

/-- **The case `k = 0`, hyperbolic** (l.756–757): hyperbolic `ℝP¹`-circles of degree `0` are
parametrised by `|tr|`. -/
theorem rp1Iso_iff_of_degree_zero_hyperbolic {f f' : GTilde} (hf : HasLiftedHolonomy L f)
    (hf' : HasLiftedHolonomy L' f') (hh : GTilde.IsHyperbolic f) (hh' : GTilde.IsHyperbolic f')
    (hfix : ∃ x, f x = x) (hfix' : ∃ x, f' x = x) :
    (∃ φ : L ≃ₜ L', IsRP1Iso φ) ↔ PSL2.trSq (GTilde.toPSL f) = PSL2.trSq (GTilde.toPSL f') := by
  rw [rp1Iso_iff_of_degree_pos hf hf' hfix hfix' (k := 0) (k' := 0) (by rw [zpow_zero, one_mul])
    (by rw [zpow_zero, one_mul]), ← PSL2.IsHyperbolic.isConj_iff hh hh']
  simp only [true_and]

/-- **l.758–759**: a hyperbolic `ℝP¹`-circle of degree `0` is the quotient of `]x₀, x₁[` with
`x₀` a repelling and `x₁` an attracting fixed point. -/
theorem IsLiftedDevPair.repelling_attracting {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}
    (h : IsLiftedDevPair E D f) (hh : GTilde.IsHyperbolic f) {x₀ x₁ : ℝ}
    (hD : range D = Ioo x₀ x₁) : GTilde.IsRepellingAt f x₀ ∧ GTilde.IsAttractingAt f x₁ := by
  have hJ := h.isComp
  have hne := hJ.nonempty
  rw [hD] at hne
  have hlt : x₀ < x₁ := nonempty_Ioo.1 hne
  have hcl : closure (range D) = Icc x₀ x₁ := by rw [hD, closure_Ioo hlt.ne]
  have hx₀ : f x₀ = x₀ := hJ.fixed x₀ (hcl ▸ left_mem_Icc.2 hlt.le)
    (by rw [hD]; exact fun h => lt_irrefl _ h.1)
  have hx₁ : f x₁ = x₁ := hJ.fixed x₁ (hcl ▸ right_mem_Icc.2 hlt.le)
    (by rw [hD]; exact fun h => lt_irrefl _ h.2)
  obtain ⟨c₁, hc₁I, hc₁, huniq, hdir⟩ := hh.fixed_structure hx₀
  have hx₁I : x₁ ∈ Ioo x₀ (x₀ + 1) := ⟨hlt, by
    by_contra hle
    have hin : c₁ ∈ range D := hD ▸ ⟨hc₁I.1, lt_of_lt_of_le hc₁I.2 (not_lt.1 hle)⟩
    exact (hJ.lt_apply _ hin).ne' hc₁⟩
  obtain rfl : x₁ = c₁ := huniq x₁ hx₁I hx₁
  have d : (∀ y ∈ Ioo x₀ x₁, y < f y) ∧ ∀ y ∈ Ioo x₁ (x₀ + 1), f y < y := by
    rcases hdir with h1 | h1
    · exact h1
    · exfalso
      have hm : (x₀ + x₁) / 2 ∈ Ioo x₀ x₁ := ⟨by linarith, by linarith⟩
      exact lt_asymm (h1.1 _ hm) (hJ.lt_apply _ (hD ▸ hm))
  have dl : ∀ y ∈ Ioo (x₁ - 1) x₀, f y < y := fun y hy => by
    have := d.2 (y + ((1 : ℤ) : ℝ)) ⟨by push_cast; linarith [hy.1], by push_cast; linarith [hy.2]⟩
    rw [GTilde.map_add_int] at this
    linarith
  constructor
  · refine ⟨hx₀, ?_⟩
    have hnhds : Ioo (x₁ - 1) x₁ ∈ 𝓝 x₀ := Ioo_mem_nhds (by linarith [hx₁I.2]) hlt
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with y hy hyne
    rcases lt_or_gt_of_ne (show y ≠ x₀ from hyne) with h1 | h1
    · have hfy := dl y ⟨hy.1, h1⟩
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
    · have hfy := d.1 y ⟨h1, hy.2⟩
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  · refine ⟨hx₁, ?_⟩
    have hnhds : Ioo x₀ (x₀ + 1) ∈ 𝓝 x₁ := Ioo_mem_nhds hlt hx₁I.2
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with y hy hyne
    rcases lt_or_gt_of_ne (show y ≠ x₁ from hyne) with h1 | h1
    · have hfy := d.1 y ⟨hy.1, h1⟩
      have hfy' : f y < x₁ := by have := GTilde.strictMono f h1; rwa [hx₁] at this
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
    · have hfy := d.2 y ⟨h1, hy.2⟩
      have hfy' : x₁ < f y := by have := GTilde.strictMono f h1; rwa [hx₁] at this
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith

end Param

/-- **l.721, and the surjectivity of the parametrisations**: every non-trivial cyclic
subgroup of `G̃` is the holonomy group of an `ℝP¹`-circle. -/
theorem exists_rp1Circle_of_ne_one {f : GTilde} (hf : f ≠ 1) :
    ∃ (L : Type) (_ : TopologicalSpace L) (_ : ChartedSpace RP1 L),
      HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1) ∧ IsCircle L ∧
        (HasLiftedHolonomy L f ∨ HasLiftedHolonomy L f⁻¹) :=
  exists_rp1Circle_quotient hf

/-! ## 5. `(Γ_p, ℓ(p))`-circles: the lifted developing map -/

section LinkCover

variable (p : HS 2)

/-- **The universal covering `ℝP̃¹ → ℓ(p)`**, read through `θ`: `t ↦` the ray of `θ⁻¹(e^{iπt})`.
Over `ℝP¹` it is `GX.RP1.proj` (`GX.linkToRP1_linkCover`); `δ` is the antipodal map of `ℓ(p)`
(`GX.linkCover_add_one`), so one turn of `ℓ(p)` is `δ²` (l.903–905). -/
def linkCover (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) : Link p :=
  (linkHomeomorph p θ).symm (Circle.exp (π * t))

theorem coe_linkCover (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) :
    ((linkCover p θ t : Link p) : TpHS p) =
      ‖θ.symm (Circle.exp (π * t))‖⁻¹ • θ.symm (Circle.exp (π * t)) := rfl

theorem linkToRP1_linkCover (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) :
    linkToRP1 p θ (linkCover p θ t) = RP1.proj t := by
  rw [linkToRP1_eq, Function.comp_apply, linkCover, Homeomorph.apply_symm_apply, RP1.proj,
    ← Circle.exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
  congr 1; ring

theorem linkCover_add_one (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) :
    linkCover p θ (t + 1) = -linkCover p θ t := by
  apply Subtype.ext
  rw [coe_neg_sphere, coe_linkCover, coe_linkCover]
  have he : ((Circle.exp (π * (t + 1)) : Circle) : ℂ) = -(Circle.exp (π * t) : ℂ) := by
    rw [mul_add, mul_one, Circle.exp_add, Circle.coe_mul, Circle.coe_exp π, Complex.exp_pi_mul_I]
    ring
  rw [he, map_neg, norm_neg, smul_neg]

theorem linkCover_eq_linkCover_iff (θ : TpHS p ≃ₗ[ℝ] ℂ) {s t : ℝ} :
    linkCover p θ s = linkCover p θ t ↔ ∃ n : ℤ, t = s + 2 * n := by
  rw [linkCover, linkCover, (linkHomeomorph p θ).symm.injective.eq_iff, Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, mul_left_cancel₀ Real.pi_ne_zero ?_⟩
    push_cast
    linarith
  · rintro ⟨n, rfl⟩
    exact ⟨-n, by push_cast; ring⟩

theorem linkCover_add_two_mul (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) (n : ℤ) :
    linkCover p θ (t + 2 * n) = linkCover p θ t :=
  ((linkCover_eq_linkCover_iff p θ).2 ⟨n, rfl⟩).symm

theorem isCoveringMap_linkCover (θ : TpHS p ≃ₗ[ℝ] ℂ) : IsCoveringMap (linkCover p θ) := by
  have := (Circle.isCoveringMap_exp.comp_homeomorph
    (Homeomorph.mulLeft₀ π Real.pi_ne_zero)).homeomorph_comp (linkHomeomorph p θ).symm
  exact this

theorem linkCover_surjective (θ : TpHS p ≃ₗ[ℝ] ℂ) : Function.Surjective (linkCover p θ) :=
  fun σ => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective (linkHomeomorph p θ σ)
    exact ⟨t / π, by rw [linkCover, mul_div_cancel₀ _ Real.pi_ne_zero, ht,
      Homeomorph.symm_apply_apply]⟩

/-- Two lifts through `linkCover` of the same map differ by a constant `2n`. -/
theorem linkCover_lift_eq {θ : TpHS p ≃ₗ[ℝ] ℂ} {g₁ g₂ : ℝ → ℝ} (h₁ : Continuous g₁)
    (h₂ : Continuous g₂) (h : ∀ s, linkCover p θ (g₁ s) = linkCover p θ (g₂ s)) :
    ∃ n : ℤ, ∀ s, g₁ s = g₂ s + 2 * n := by
  obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff p θ).1 (h 0)
  refine ⟨-n, fun s => congrFun ((isCoveringMap_linkCover p θ).eq_of_comp_eq (g₁ := g₁)
    (g₂ := fun s => g₂ s + 2 * ((-n : ℤ) : ℝ)) h₁ (h₂.add continuous_const)
    (funext fun s => ?_) 0 (by show g₁ 0 = g₂ 0 + 2 * ((-n : ℤ) : ℝ); rw [hn]; push_cast; ring)) s⟩
  simp only [Function.comp_apply]
  rw [linkCover_add_two_mul, h]

/-- **The lift of `A ∈ Γ_p` to `ℝP̃¹`** through `linkCover` (from `θ` to `θ'`, given that the two
maps `ℓ(p) → ℝP¹` differ by `g₀`): an element of `G̃`. -/
theorem exists_rayLift {θ θ' : TpHS p ≃ₗ[ℝ] ℂ} {g₀ : PSL(2, ℝ)}
    (hg₀ : ∀ σ, linkToRP1 p θ' σ = g₀ • linkToRP1 p θ σ) (A : GammaP p) :
    ∃ F : GTilde, ∀ t, linkCover p θ' (F t) = A • linkCover p θ t := by
  have hc : Continuous fun t => A • linkCover p θ t :=
    (continuous_const_smul A).comp (isCoveringMap_linkCover p θ).continuous
  obtain ⟨e₀, he₀⟩ := linkCover_surjective p θ' (A • linkCover p θ 0)
  obtain ⟨F₀, ⟨-, hF₀⟩, -⟩ := (isCoveringMap_linkCover p θ').existsUnique_continuousMap_lifts
    ⟨_, hc⟩ 0 e₀ he₀
  have hF : ∀ t, linkCover p θ' (F₀ t) = A • linkCover p θ t := fun t => congrFun hF₀ t
  obtain ⟨B, hB⟩ := pslMk_surjective (pslMk (gammaToSL p θ' A) * g₀)
  have hlift : IsSLLift B F₀ := ⟨F₀.continuous, fun t => by
    rw [← linkToRP1_linkCover p θ', hF, linkToRP1_smul, hg₀, linkToRP1_linkCover, ← mul_smul,
      ← hB, pslMk_smul]⟩
  exact ⟨GTilde.ofLift hlift, fun t => by rw [GTilde.ofLift_apply]; exact hF t⟩

end LinkCover

section GammaCircle

variable {L : Type*} [TopologicalSpace L]

/-- **A lifted developing pair of a `(Γ_p, ℓ(p))`-circle** (l.842–843, l.896–902): a periodic
covering `E : ℝ → L` (the universal covering `L̃`) and an increasing `D : ℝ → ℝP̃¹` lifting a
developing map `d = linkCover ∘ D : L̃ → ℓ(p)`, with lifted holonomy `f` (`D (s + 1) = f (D s)`).
`D` increasing is the canonical orientation of l.729–731, for `θ` oriented. -/
def GammaLinkCircle.IsLiftedDev (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L)
    (D : ℝ → ℝ) (f : GTilde) : Prop :=
  IsPeriodicCover E ∧ Continuous D ∧ StrictMono D ∧ C.IsDevAlong E (linkCover C.pt θ ∘ D) ∧
    ∀ s, D (s + 1) = f (D s)

variable {C : GammaLinkCircle L} {θ θ' : TpHS C.pt ≃ₗ[ℝ] ℂ} {E E' : ℝ → L} {D D' : ℝ → ℝ}
  {f f' : GTilde}

/-- Reading a developing map through a continuous reparametrisation. -/
theorem GammaLinkCircle.IsDevAlong.comp_reparam {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] {E₀ : M → L} {d : M → Link C.pt} (hd : C.IsDevAlong E₀ d) {ψ : N → M}
    (hψ : Continuous ψ) : C.IsDevAlong (E₀ ∘ ψ) (d ∘ ψ) := fun s => by
  obtain ⟨A, hA⟩ := hd (ψ s)
  exact ⟨A, hψ.continuousAt.eventually hA⟩

/-- The charts of the underlying `ℝP¹`-structure are the charts of `C` followed by `ℓ(p) → ℝP¹`. -/
theorem GammaLinkCircle.rp1_chartAt_apply (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ)
    (x y : L) : @chartAt RP1 _ L _ (C.rp1ChartedSpace θ) x y =
      linkToRP1 C.pt θ (@chartAt (Link C.pt) _ L _ C.atlas x y) := by
  letI := C.atlas
  show ((chartAt (Link C.pt) x).trans (@chartAt RP1 _ (Link C.pt) _ (linkRP1ChartedSpace C.pt θ)
    (chartAt (Link C.pt) x x))) y = _
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, linkRP1_chart_eq C.pt θ _
    (@chart_mem_atlas RP1 (Link C.pt) _ _ (linkRP1ChartedSpace C.pt θ) _)]

/-- The lifted developing map is a local homeomorphism of `ℝ`. -/
theorem GammaLinkCircle.IsLiftedDev.isLocalHomeomorph (h : C.IsLiftedDev θ E D f) :
    IsLocalHomeomorph D := by
  letI := C.atlas
  obtain ⟨hE, hDc, -, hd, -⟩ := h
  have hEl := hE.isCoveringMap.isLocalHomeomorph
  have hdl : IsLocalHomeomorph (linkCover C.pt θ ∘ D) := by
    letI := pullbackChartedSpace (X := Link C.pt) hEl
    exact ((C.isDevAlong_iff_isGXMorphism hEl).1 hd).isLocalHomeomorph
  exact IsLocalHomeomorph.of_comp hdl (isCoveringMap_linkCover C.pt θ).isLocalHomeomorph hDc

/-- A lifted developing pair of the `(Γ_p, ℓ(p))`-circle witnesses the lifted holonomy of its
underlying `ℝP¹`-circle (l.770–771): the degree, the trace class and the angle of l.739–760 are
those of `f`. -/
theorem GammaLinkCircle.IsLiftedDev.isLiftedDevPair (h : C.IsLiftedDev θ E D f) :
    letI := C.rp1ChartedSpace θ
    IsLiftedDevPair E D f := by
  letI := C.rp1ChartedSpace θ
  obtain ⟨hE, hDc, hDm, hd, hDf⟩ := h
  refine ⟨hE, hDc, hDm, fun s => ?_, hDf⟩
  obtain ⟨A, hA⟩ := hd s
  refine ⟨pslMk (gammaToSL C.pt θ A), hA.mono fun s' hs' => ?_⟩
  simp only [Function.comp_apply] at hs' ⊢
  rw [C.rp1_chartAt_apply θ, ← linkToRP1_smul, ← hs', linkToRP1_linkCover]

/-- Every `(Γ_p, ℓ(p))`-circle has a lifted developing pair. -/
theorem GammaLinkCircle.exists_isLiftedDev (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) :
    ∃ E D f, C.IsLiftedDev θ E D f := by
  letI := C.atlas
  obtain ⟨E, hE, d, hd, ρ, hρ⟩ := C.exists_isDevAlong
  have hEl := hE.isCoveringMap.isLocalHomeomorph
  have hdc := hd.continuous hE.isCoveringMap.continuous
  obtain ⟨e₀, he₀⟩ := linkCover_surjective C.pt θ (d 0)
  obtain ⟨D₀, ⟨-, hD₀⟩, -⟩ := (isCoveringMap_linkCover C.pt θ).existsUnique_continuousMap_lifts
    ⟨d, hdc⟩ 0 e₀ he₀
  have hD : ∀ s, linkCover C.pt θ (D₀ s) = d s := fun s => congrFun hD₀ s
  have hd' : C.IsDevAlong E (linkCover C.pt θ ∘ D₀) := by
    have : linkCover C.pt θ ∘ D₀ = d := funext hD
    rw [this]; exact hd
  have hdl : IsLocalHomeomorph (linkCover C.pt θ ∘ D₀) := by
    letI := pullbackChartedSpace (X := Link C.pt) hEl
    exact ((C.isDevAlong_iff_isGXMorphism hEl).1 hd').isLocalHomeomorph
  have hD₀l : IsLocalHomeomorph D₀ := IsLocalHomeomorph.of_comp hdl
    (isCoveringMap_linkCover C.pt θ).isLocalHomeomorph D₀.continuous
  have hinj := injective_of_isOpenMap_real D₀.continuous hD₀l.isOpenMap
  obtain ⟨F, hF⟩ := exists_rayLift C.pt (θ := θ) (θ' := θ) (g₀ := 1)
    (fun σ => (one_smul _ _).symm) ρ
  obtain ⟨n, hn⟩ := linkCover_lift_eq C.pt (D₀.continuous.comp (continuous_add_const 1))
    ((GTilde.continuous F).comp D₀.continuous) (fun s => by
      simp only [Function.comp_apply]; rw [hD, hρ, hF, hD])
  set f : GTilde := GTilde.delta ^ (2 * n) * F
  have hf : ∀ s, D₀ (s + 1) = f (D₀ s) := fun s => by
    have := hn s
    simp only [Function.comp_apply] at this
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply, this]; push_cast; ring
  rcases D₀.continuous.strictMono_of_inj hinj with hmono | hanti
  · exact ⟨E, D₀, f, hE, D₀.continuous, hmono, hd', hf⟩
  · refine ⟨E ∘ Neg.neg, D₀ ∘ Neg.neg, f⁻¹, ⟨hE.isCoveringMap.comp_homeomorph (Homeomorph.neg ℝ),
      hE.surjective.comp neg_surjective, fun s => ?_, fun s t hst => ?_⟩,
      D₀.continuous.comp continuous_neg, hanti.comp (fun _ _ h => neg_lt_neg h),
      hd'.comp_reparam continuous_neg, fun s => ?_⟩
    · simp only [Function.comp_apply]
      rw [← hE.add_one (-(s + 1)), show -(s + 1) + 1 = -s by ring]
    · obtain ⟨m, hm⟩ := hE.fiber _ _ hst
      exact ⟨-m, by push_cast; linarith⟩
    · simp only [Function.comp_apply]
      rw [show -s = -(s + 1) + 1 by ring, hf, GTilde.inv_apply_apply]

/-- `f` is the lift through `linkCover` of the holonomy `ρ ∈ Γ_p`. -/
theorem GammaLinkCircle.IsLiftedDev.exists_linkCover_apply (h : C.IsLiftedDev θ E D f) :
    ∃ ρ : GammaP C.pt, ∀ t, linkCover C.pt θ (f t) = ρ • linkCover C.pt θ t := by
  letI := C.atlas
  have hDl := h.isLocalHomeomorph
  obtain ⟨hE, hDc, hDm, hd, hDf⟩ := h
  have hEl := hE.isCoveringMap.isLocalHomeomorph
  have hd1 : C.IsDevAlong E ((linkCover C.pt θ ∘ D) ∘ fun s => s + 1) := by
    have := hd.comp_reparam (continuous_add_const (1 : ℝ))
    have hE1 : (E ∘ fun s : ℝ => s + 1) = E := funext fun s => hE.add_one s
    rwa [hE1] at this
  obtain ⟨ρ, hρ, -⟩ := hd.existsUnique_eq_smul hEl hd1
  obtain ⟨F, hF⟩ := exists_rayLift C.pt (θ := θ) (θ' := θ) (g₀ := 1)
    (fun σ => (one_smul _ _).symm) ρ
  obtain ⟨n, hn⟩ := linkCover_lift_eq C.pt ((GTilde.continuous f).comp hDc)
    ((GTilde.continuous F).comp hDc) (fun s => by
      have := hρ s
      simp only [Function.comp_apply] at this ⊢
      rw [← hDf, this, hF])
  have hfe : f = GTilde.delta ^ (2 * n) * F := GTilde.eq_of_eqOn hDl.isOpenMap.isOpen_range
    (range_nonempty D) (by
      rintro _ ⟨s, rfl⟩
      have := hn s
      simp only [Function.comp_apply] at this
      rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply, this]; push_cast; ring)
  refine ⟨ρ, fun t => ?_⟩
  rw [hfe, GTilde.coe_mul_apply, GTilde.delta_zpow_apply, show F t + ((2 * n : ℤ) : ℝ) =
    F t + 2 * n by push_cast; ring, linkCover_add_two_mul, hF]

/-- **Two lifted developing pairs are related** by a reparametrisation `ψ` of `L̃` and an element
`k ∈ G̃`: `E' = E ∘ ψ`, `D' = k ∘ D ∘ ψ`, `f' = k f k⁻¹`. -/
theorem GammaLinkCircle.IsLiftedDev.relate (hθ : IsOrientedTangent C.pt θ)
    (hθ' : IsOrientedTangent C.pt θ') (h : C.IsLiftedDev θ E D f)
    (h' : C.IsLiftedDev θ' E' D' f') :
    ∃ (ψ : ℝ → ℝ) (k : GTilde), (∀ s, E' s = E (ψ s)) ∧ (∀ s, D' s = k (D (ψ s))) ∧
      f' = k * f * k⁻¹ := by
  letI := C.atlas
  have hD₂l := h'.isLocalHomeomorph
  obtain ⟨hE₁, hD₁c, hD₁m, hD₁, hf₁⟩ := h
  obtain ⟨hE₂, hD₂c, hD₂m, hD₂, hf₂⟩ := h'
  have hE₂l := hE₂.isCoveringMap.isLocalHomeomorph
  -- 1. `E' = E ∘ ψ`
  obtain ⟨e₀, he₀⟩ := hE₁.surjective (E' 0)
  obtain ⟨ψ, ⟨-, hψ0⟩, -⟩ := hE₁.isCoveringMap.existsUnique_continuousMap_lifts
    ⟨E', hE₂.isCoveringMap.continuous⟩ 0 e₀ he₀
  have hψ : ∀ s, E (ψ s) = E' s := fun s => congrFun hψ0 s
  -- 2. `ψ (s + 1) = ψ s + ε`
  obtain ⟨ε, hε⟩ := hE₁.fiber (ψ 0) (ψ (0 + 1)) (by rw [hψ, hψ, hE₂.add_one])
  have hψ1 : ∀ s, ψ (s + 1) = ψ s + ε := fun s => congrFun
    (hE₁.isCoveringMap.eq_of_comp_eq (g₁ := fun s => ψ (s + 1)) (g₂ := fun s => ψ s + ε)
      (ψ.continuous.comp (continuous_add_const 1)) (ψ.continuous.add continuous_const)
      (funext fun s => by
        simp only [Function.comp_apply]
        rw [hψ, hE₁.add_int, hψ, hE₂.add_one]) 0 hε) s
  -- 3. `linkCover θ ∘ D ∘ ψ` is a developing map along `E'`
  have hD₁ψ : C.IsDevAlong E' (linkCover C.pt θ ∘ (D ∘ ψ)) := by
    have := hD₁.comp_reparam ψ.continuous
    have hE : E ∘ ψ = E' := funext hψ
    rw [hE] at this
    exact this
  -- 4. `d' = B • (d ∘ ψ)`
  obtain ⟨B, hB, -⟩ := hD₁ψ.existsUnique_eq_smul hE₂l hD₂
  -- 5. the lift of `B` from `θ` to `θ'`
  obtain ⟨g₀, hg₀⟩ := linkToRP1_eq_smul C.pt hθ hθ'
  obtain ⟨F, hF⟩ := exists_rayLift C.pt hg₀ B
  obtain ⟨n, hn⟩ := linkCover_lift_eq C.pt hD₂c ((GTilde.continuous F).comp
    (hD₁c.comp ψ.continuous)) (fun s => by
      have := hB s
      simp only [Function.comp_apply] at this ⊢
      rw [this, hF])
  set k : GTilde := GTilde.delta ^ (2 * n) * F with hk
  have hD₂k : ∀ s, D' s = k (D (ψ s)) := fun s => by
    rw [hn, hk, GTilde.coe_mul_apply, GTilde.delta_zpow_apply]
    simp only [Function.comp_apply]; push_cast; ring
  clear_value k
  -- 6. `ψ` is increasing
  have hψm : StrictMono ψ := by
    intro s t hst
    by_contra hle
    have hle' := not_lt.1 hle
    have h1 := hD₂m hst
    rw [hD₂k, hD₂k] at h1
    exact absurd h1 (not_lt.2 ((GTilde.strictMono k).monotone (hD₁m.monotone hle')))
  -- 7. `ε = 1`
  have hε1 : ε = 1 := by
    have h01 : ψ 1 = ψ 0 + ε := by simpa using hψ1 0
    have hpos : (0 : ℝ) < ε := by have := hψm zero_lt_one; linarith
    have hge : (1 : ℤ) ≤ ε := by exact_mod_cast hpos
    by_contra hne
    have h2 : (2 : ℝ) ≤ ε := by exact_mod_cast (show (2 : ℤ) ≤ ε by omega)
    obtain ⟨t, ht, hψt⟩ := intermediate_value_Icc zero_le_one ψ.continuous.continuousOn
      (show ψ 0 + 1 ∈ Icc (ψ 0) (ψ 1) from ⟨by linarith, by linarith⟩)
    have hEt : E' 0 = E' t := by
      rw [← hψ, ← hψ, hψt, show ψ 0 + 1 = ψ 0 + ((1 : ℤ) : ℝ) by simp, hE₁.add_int]
    obtain ⟨m, hm⟩ := hE₂.fiber 0 t hEt
    rw [zero_add] at hm
    have hm0 : (0 : ℝ) ≤ m := hm ▸ ht.1
    have hm1 : (m : ℝ) ≤ 1 := hm ▸ ht.2
    have hm0' : (0 : ℤ) ≤ m := by exact_mod_cast hm0
    have hm1' : m ≤ (1 : ℤ) := by exact_mod_cast hm1
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · rw [hm, Int.cast_zero] at hψt; linarith
    · rw [hm, Int.cast_one, h01] at hψt; linarith
  -- 8. `f' = k f k⁻¹` on the image of `D'`, an open interval
  refine ⟨ψ, k, fun s => (hψ s).symm, hD₂k,
    GTilde.eq_of_eqOn hD₂l.isOpenMap.isOpen_range (range_nonempty D') ?_⟩
  rintro _ ⟨s, rfl⟩
  show f' (D' s) = (k * f * k⁻¹) (D' s)
  have e2 : D' (s + 1) = k (f (D (ψ s))) := by rw [hD₂k, hψ1, hε1, Int.cast_one, hf₁]
  rw [← hf₂, e2, hD₂k s, GTilde.coe_mul_apply, GTilde.coe_mul_apply, GTilde.inv_apply_apply]

/-! ### The dynamics of `Γ_p` on `ℓ(p)` at a space-like `p` -/

section DeSitterDynamics

variable {p : HS 2}

/-- Two non-proportional lightlike directions at `p ∈ dS²`. -/
theorem exists_two_null (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ n₁ n₂ : Link p, Causal.Flat.minkQ (dsProj p n₁) = 0 ∧
      Causal.Flat.minkQ (dsProj p n₂) = 0 ∧ ∀ c : ℝ, (n₂ : TpHS p) ≠ c • (n₁ : TpHS p) := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have hp1 := norm_snd_of_deSitter hp
  have hx := sum_sq_of_norm hp1
  set k := Real.sqrt (Causal.Flat.minkQ (p : 𝕄))
  have hk : 0 < k := Real.sqrt_pos.2 hQ
  have hk2 : k ^ 2 = Causal.Flat.minkQ (p : 𝕄) := Real.sq_sqrt hQ.le
  have hQp := minkQ_two (p : 𝕄)
  set w₁ : 𝕄 := dsU p + k • jVec p
  set w₂ : 𝕄 := dsU p + (-k) • jVec p
  have hBp : ∀ c : ℝ, Causal.Flat.minkB (p : 𝕄) (dsU p + c • jVec p) = 0 := fun c => by
    rw [Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, Causal.Flat.minkB_comm,
      minkB_dsU_self hp1, Causal.Flat.minkB_comm, minkB_jVec, mul_zero, add_zero]
  have hBj : ∀ c : ℝ, Causal.Flat.minkB (jVec p) (dsU p + c • jVec p) = c := fun c => by
    rw [Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, Causal.Flat.minkB_comm,
      minkB_dsU_jVec, ← Causal.Flat.minkQ_eq_minkB, minkQ_jVec, hp1]; ring
  have hBu : ∀ c : ℝ, Causal.Flat.minkB (dsU p) (dsU p + c • jVec p) =
      -Causal.Flat.minkQ (p : 𝕄) := fun c => by
    rw [Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, minkB_dsU_jVec,
      ← Causal.Flat.minkQ_eq_minkB, minkQ_dsU hp1]; ring
  have hQw : ∀ c : ℝ, c ^ 2 = Causal.Flat.minkQ (p : 𝕄) →
      Causal.Flat.minkQ (dsU p + c • jVec p) = 0 := fun c hc => by
    rw [minkQ_two]
    simp only [dsU, jVec, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, jRot_zero, jRot_one]
    rw [hQp] at hc
    linear_combination (1 + (p : 𝕄).1 ^ 2 + c ^ 2) * hx + hc
  have htp : ∀ c : ℝ, c ≠ 0 → tpMk p (dsU p + c • jVec p) ≠ 0 := fun c hc h0 => by
    obtain ⟨m, hm⟩ := (tpMk_eq_zero_iff p).1 h0
    have := hBj c
    rw [hm, Causal.Flat.minkB_smul_right, minkB_jVec, mul_zero] at this
    exact hc this.symm
  have hnull : ∀ c : ℝ, c ≠ 0 → c ^ 2 = Causal.Flat.minkQ (p : 𝕄) →
      Causal.Flat.minkQ (dsProj p (dirOf p (dsU p + c • jVec p))) = 0 := fun c hc hc2 => by
    rw [dsProj_dirOf p (htp c hc), Causal.Flat.minkQ_smul, perpLin_apply, hBp,
      zero_smul, sub_zero, Causal.Flat.minkQ_smul, hQw c hc2, mul_zero, mul_zero]
  refine ⟨dirOf p w₁, dirOf p w₂, hnull k hk.ne' hk2, hnull (-k) (neg_ne_zero.2 hk.ne')
    (by rw [neg_sq, hk2]), fun c hc => ?_⟩
  rw [coe_dirOf p (htp k hk.ne'), coe_dirOf p (htp (-k) (neg_ne_zero.2 hk.ne'))] at hc
  set a := ‖tpMk p w₁‖
  set b := ‖tpMk p w₂‖
  have hb : b ≠ 0 := norm_ne_zero_iff.2 (htp (-k) (neg_ne_zero.2 hk.ne'))
  have h1 : tpMk p w₂ = tpMk p ((b * c * a⁻¹) • w₁) := by
    rw [show tpMk p ((b * c * a⁻¹) • w₁) = (b * c * a⁻¹) • tpMk p w₁ from
      Submodule.Quotient.mk_smul _ _ _]
    have := congrArg (b • ·) hc
    simp only [smul_smul, mul_inv_cancel₀ hb, one_smul] at this
    rw [this, ← mul_assoc]
  obtain ⟨m, hm⟩ := (tpMk_eq_tpMk_iff p).1 h1
  have e1 := congrArg (Causal.Flat.minkB (jVec p)) hm
  have e2 := congrArg (Causal.Flat.minkB (dsU p)) hm
  rw [hBj, Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, Causal.Flat.minkB_smul_right,
    hBj, minkB_jVec, mul_zero, add_zero] at e1
  rw [hBu, Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, Causal.Flat.minkB_smul_right,
    hBu, minkB_dsU_self hp1, mul_zero, add_zero] at e2
  have hr : b * c * a⁻¹ = -1 := by
    have : k * (b * c * a⁻¹ + 1) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hk.ne'
    linarith
  rw [hr] at e2
  linarith

/-- **At `p ∈ dS²`, an element `A ≠ 1` of `Γ_p` fixes only lightlike directions.** -/
theorem eq_one_of_smul_eq_of_deSitter (hp : p ∈ HS.piece 2 .deSitter) {A : GammaP p}
    {σ : Link p} (hσ : A • σ = σ) (hσ0 : Causal.Flat.minkQ (dsProj p σ) ≠ 0) : A = 1 := by
  obtain ⟨n₁, n₂, h₁, h₂, h12⟩ := exists_two_null hp
  set θ := tpHSEquiv p
  have hfix : ∀ {τ : Link p}, A • τ = τ →
      pslMk (gammaToSL p θ A) • linkToRP1 p θ τ = linkToRP1 p θ τ := fun hτ => by
    rw [← linkToRP1_smul, hτ]
  have hθne : ∀ τ : Link p, θ τ ≠ 0 := fun τ =>
    (LinearEquiv.map_ne_zero_iff θ).2 (raySphere_ne_zero τ)
  have hne : ∀ {τ τ' : Link p}, (∀ c : ℝ, (τ' : TpHS p) ≠ c • (τ : TpHS p)) →
      linkToRP1 p θ τ ≠ linkToRP1 p θ τ' := fun {τ τ'} h he => by
    obtain ⟨c, hc⟩ := (RP1.mk_eq_mk_iff (hθne τ) (hθne τ')).1 he
    exact h c (θ.injective (by rw [map_smul, hc, Complex.real_smul]))
  have hnp : ∀ {τ : Link p}, Causal.Flat.minkQ (dsProj p τ) = 0 →
      ∀ c : ℝ, (τ : TpHS p) ≠ c • (σ : TpHS p) := fun {τ} hτ c hc => by
    rw [hc, map_smul, Causal.Flat.minkQ_smul] at hτ
    rcases mul_eq_zero.1 hτ with h | h
    · have hc0 : c = 0 := pow_eq_zero_iff two_ne_zero |>.1 h
      rw [hc0, zero_smul] at hc
      exact raySphere_ne_zero τ hc
    · exact hσ0 h
  have hone := PSL2.eq_one_of_three_fixed (hfix hσ) (hfix (smul_eq_of_deSitter hp h₁ A))
    (hfix (smul_eq_of_deSitter hp h₂ A)) (hne (hnp h₁)) (hne (hnp h₂)) (hne h12)
  have hcen : gammaToSL p θ A ∈ Subgroup.center SL(2, ℝ) := (QuotientGroup.eq_one_iff _).1 hone
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
  have hT : ∀ z : TpHS p, GammaP.tangent A z = r • z := fun z => by
    apply θ.injective
    have := slLin_gammaToSL p θ A (θ z)
    rw [LinearEquiv.symm_apply_apply] at this
    rw [← this, map_smul, slLin_apply, ← hr]
    apply Complex.ext <;> simp [Matrix.scalar_apply]
  obtain ⟨c, hc0, hcT⟩ := (gammaP_smul_eq_iff A n₁).1 (smul_eq_of_deSitter hp h₁ A)
  rw [hT] at hcT
  have hrc : r = c := by
    have h0 : (r - c) • (n₁ : TpHS p) = 0 := by rw [sub_smul, hcT, sub_self]
    have := (smul_eq_zero.1 h0).resolve_right (raySphere_ne_zero n₁)
    linarith
  have hr1 : r = 1 := by
    have h2 : r ^ 2 = 1 := by simpa using hr2
    have : (r - 1) * (r + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  exact gammaP_eq_one_of_tangent p (fun z => by rw [hT, hr1, one_smul])

variable {θ : TpHS p ≃ₗ[ℝ] ℂ} {A : GammaP p} {g : GTilde}

/-- **The fixed points of the lift `g` of `A ≠ 1` are the lifts of the lightlike directions.** -/
theorem fixed_iff_null (hp : p ∈ HS.piece 2 .deSitter) (hA : A ≠ 1)
    (hg : ∀ t, linkCover p θ (g t) = A • linkCover p θ t) (hfix : ∃ x, g x = x) (t : ℝ) :
    g t = t ↔ Causal.Flat.minkQ (dsProj p (linkCover p θ t)) = 0 := by
  constructor
  · intro ht
    by_contra h0
    exact hA (eq_one_of_smul_eq_of_deSitter hp (by rw [← hg, ht]) h0)
  · intro h0
    have h1 : linkCover p θ t = linkCover p θ (g t) := by rw [hg, smul_eq_of_deSitter hp h0 A]
    obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff p θ).1 h1
    have ha := GTilde.apply_lt_delta_of_fixed hfix t
    have hb := GTilde.sub_one_lt_apply_of_fixed hfix t
    rw [GTilde.delta_apply] at ha
    rw [hn] at ha hb
    have h3 : (n : ℝ) < 1 / 2 := by linarith
    have h4 : (-1 / 2 : ℝ) < n := by linarith
    have : n = 0 := by
      have : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
      have : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
      omega
    rw [hn, this]; simp

/-- **The sign of `g − id` is constant on the lift of an open preconnected set of non-fixed
directions.** -/
theorem sign_const {S : Set (Link p)}
    (hSo : IsOpen S) (hSc : IsPreconnected S) (hSf : ∀ t, linkCover p θ t ∈ S → g t ≠ t) :
    (∀ t, linkCover p θ t ∈ S → t < g t) ∨ (∀ t, linkCover p θ t ∈ S → g t < t) := by
  have hlc := isCoveringMap_linkCover p θ
  have hshift : ∀ t (n : ℤ), g (t + 2 * n) = g t + 2 * n := fun t n => by
    have := GTilde.map_add_int g t (2 * n); push_cast at this; exact this
  have hfib : ∀ t t', linkCover p θ t = linkCover p θ t' →
      (t < g t ↔ t' < g t') ∧ (g t < t ↔ g t' < t') := fun t t' h => by
    obtain ⟨n, rfl⟩ := (linkCover_eq_linkCover_iff p θ).1 h
    rw [hshift]
    exact ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith,
      fun h => by linarith⟩⟩
  set P := linkCover p θ '' {t | linkCover p θ t ∈ S ∧ t < g t}
  set Q := linkCover p θ '' {t | linkCover p θ t ∈ S ∧ g t < t}
  have hPo : IsOpen P := hlc.isOpenMap _ ((hSo.preimage hlc.continuous).inter
    (isOpen_lt continuous_id (GTilde.continuous g)))
  have hQo : IsOpen Q := hlc.isOpenMap _ ((hSo.preimage hlc.continuous).inter
    (isOpen_lt (GTilde.continuous g) continuous_id))
  have hcover : S ⊆ P ∪ Q := fun σ hσ => by
    obtain ⟨t, rfl⟩ := linkCover_surjective p θ σ
    rcases lt_or_gt_of_ne (hSf t hσ) with h | h
    · exact Or.inr ⟨t, ⟨hσ, h⟩, rfl⟩
    · exact Or.inl ⟨t, ⟨hσ, h⟩, rfl⟩
  have hdisj : S ∩ (P ∩ Q) = ∅ := by
    refine eq_empty_of_forall_notMem fun σ ⟨_, ⟨t, ⟨_, ht⟩, he⟩, ⟨t', ⟨_, ht'⟩, he'⟩⟩ => ?_
    have := ((hfib t t' (he.trans he'.symm)).1).1 ht
    linarith
  rcases isPreconnected_iff_subset_of_disjoint.1 hSc P Q hPo hQo hcover hdisj with h | h
  · left; intro t ht
    obtain ⟨t', ⟨-, ht'⟩, he⟩ := h ht
    exact ((hfib t' t he).1).1 ht'
  · right; intro t ht
    obtain ⟨t', ⟨-, ht'⟩, he⟩ := h ht
    exact ((hfib t' t he).2).1 ht'

/-- `δⁿ` acts on `ℓ(p)` as `(−1)ⁿ`. -/
theorem linkCover_add_int (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) (n : ℤ) :
    linkCover p θ (t + n) = linkCover p θ t ∨ linkCover p θ (t + n) = -linkCover p θ t := by
  induction n using Int.induction_on generalizing t with
  | zero => left; simp
  | succ m ih =>
    have e : t + ((m + 1 : ℤ) : ℝ) = (t + (m : ℤ)) + 1 := by push_cast; ring
    rw [e, linkCover_add_one]
    rcases ih t with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h, neg_neg])
  | pred m ih =>
    have e : t + (-(m : ℤ) : ℝ) = (t + ((-(m : ℤ) - 1 : ℤ) : ℝ)) + 1 := by push_cast; ring
    have h1 := linkCover_add_one p θ (t + ((-(m : ℤ) - 1 : ℤ) : ℝ))
    rw [← e] at h1
    have h2 : linkCover p θ (t + ((-(m : ℤ) - 1 : ℤ) : ℝ)) =
        -linkCover p θ (t + (-(m : ℤ) : ℝ)) := by rw [h1, neg_neg]
    rcases ih t with h | h
    · push_cast at h h2 ⊢; exact Or.inr (by rw [h2, h])
    · push_cast at h h2 ⊢; exact Or.inl (by rw [h2, h, neg_neg])

theorem minkQ_dsProj_neg (σ : Link p) :
    Causal.Flat.minkQ (dsProj p ((-σ : Link p) : TpHS p)) = Causal.Flat.minkQ (dsProj p σ) := by
  rw [dsProj_neg, Causal.Flat.minkQ_neg]

theorem neg_mem_timelike_iff (σ : Link p) :
    -σ ∈ dsFutureDirs p ∪ dsPastDirs p ↔ σ ∈ dsFutureDirs p ∪ dsPastDirs p := by
  simp only [mem_union, dsFutureDirs, dsPastDirs, mem_setOf_eq, dsProj_neg, neg_neg]
  exact Or.comm

theorem minkQ_neg_of_timelike {σ : Link p} (h : σ ∈ dsFutureDirs p ∪ dsPastDirs p) :
    Causal.Flat.minkQ (dsProj p σ) < 0 := by
  rcases h with h | h
  · exact h.2
  · have := h.2; rwa [Causal.Flat.minkQ_neg] at this

theorem timelike_of_minkQ_neg {σ : Link p} (h : Causal.Flat.minkQ (dsProj p σ) < 0) :
    σ ∈ dsFutureDirs p ∪ dsPastDirs p :=
  Causal.Flat.isFutureTimelike_or_neg h

/-- An element of `G̃` lifting `A ∈ Γ_p` (`p ∈ dS²`), not in the centre, is hyperbolic. -/
theorem isHyperbolic_of_linkCover (hp : p ∈ HS.piece 2 .deSitter) {f : GTilde}
    (hf : ∀ t, linkCover p θ (f t) = A • linkCover p θ t) (h1 : GTilde.toPSL f ≠ 1) :
    GTilde.IsHyperbolic f := by
  obtain ⟨n₁, n₂, h₁, h₂, h12⟩ := exists_two_null hp
  obtain ⟨t₁, ht₁⟩ := linkCover_surjective p θ n₁
  obtain ⟨t₂, ht₂⟩ := linkCover_surjective p θ n₂
  have hfx : ∀ {t : ℝ}, Causal.Flat.minkQ (dsProj p (linkCover p θ t)) = 0 →
      GTilde.toPSL f • RP1.proj t = RP1.proj t := fun {t} h0 => by
    rw [← GTilde.proj_apply, ← linkToRP1_linkCover p θ, hf, smul_eq_of_deSitter hp h0,
      linkToRP1_linkCover]
  refine PSL2.isHyperbolic_of_two_fixed h1 (hfx (by rw [ht₁]; exact h₁))
    (hfx (by rw [ht₂]; exact h₂)) fun he => ?_
  rw [← linkToRP1_linkCover p θ, ← linkToRP1_linkCover p θ, ht₁, ht₂] at he
  have hθne : ∀ τ : Link p, θ τ ≠ 0 := fun τ =>
    (LinearEquiv.map_ne_zero_iff θ).2 (raySphere_ne_zero τ)
  obtain ⟨c, hc⟩ := (RP1.mk_eq_mk_iff (hθne n₁) (hθne n₂)).1 he
  exact h12 c (θ.injective (by rw [map_smul, hc, Complex.real_smul]))

/-- **At `p ∈ dS²`, the lift `g` of `A ∈ Γ_p ∖ {1}` with a fixed point moves the time-like
directions one way and the space-like directions the other way** (l.896–905). -/
theorem timelike_spacelike_dir (hp : p ∈ HS.piece 2 .deSitter) (hA : A ≠ 1)
    (hg : ∀ t, linkCover p θ (g t) = A • linkCover p θ t) (hfix : ∃ x, g x = x) :
    ((∀ t, linkCover p θ t ∈ dsFutureDirs p ∪ dsPastDirs p → t < g t) ∧
      ∀ t, 0 < Causal.Flat.minkQ (dsProj p (linkCover p θ t)) → g t < t) ∨
    ((∀ t, linkCover p θ t ∈ dsFutureDirs p ∪ dsPastDirs p → g t < t) ∧
      ∀ t, 0 < Causal.Flat.minkQ (dsProj p (linkCover p θ t)) → t < g t) := by
  -- the core: time-like directions moved to the right force space-like ones to the left
  have core : ∀ {A : GammaP p} {g : GTilde}, A ≠ 1 →
      (∀ t, linkCover p θ (g t) = A • linkCover p θ t) → (∃ x, g x = x) →
      (∀ t, linkCover p θ t ∈ dsFutureDirs p ∪ dsPastDirs p → t < g t) →
      ∀ t, 0 < Causal.Flat.minkQ (dsProj p (linkCover p θ t)) → g t < t := by
    intro A g hA hg hfix hT t ht
    have hfn := fixed_iff_null hp hA hg hfix
    have hg1 : GTilde.toPSL g ≠ 1 := fun h1 => by
      have hk : g ∈ GTilde.toPSL.ker := h1
      rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hk
      obtain ⟨j, rfl⟩ := hk
      obtain ⟨x, hx⟩ := hfix
      rw [GTilde.delta_zpow_apply] at hx
      have hj : j = 0 := by exact_mod_cast (show (j : ℝ) = 0 by linarith)
      obtain ⟨σ, hσ⟩ := (isConnected_dsFutureDirs hp).nonempty
      obtain ⟨t', ht'⟩ := linkCover_surjective p θ σ
      have := (hfn t').1 (by rw [hj, zpow_zero, GTilde.one_apply])
      rw [ht'] at this
      exact (minkQ_neg_of_timelike (Or.inl hσ)).ne this
    have hh := isHyperbolic_of_linkCover hp hg hg1
    obtain ⟨c, hc⟩ := hfix
    obtain ⟨c₁, hc₁I, hc₁, huniq, hdir⟩ := hh.fixed_structure hc
    -- `δⁿ` preserves time-like and space-like directions
    have hq : ∀ t (n : ℤ), Causal.Flat.minkQ (dsProj p (linkCover p θ (t + n))) =
        Causal.Flat.minkQ (dsProj p (linkCover p θ t)) := fun t n => by
      rcases linkCover_add_int θ t n with h | h <;> rw [h]
      exact minkQ_dsProj_neg _
    have hshift : ∀ y (n : ℤ), (g (y + n) < y + n ↔ g y < y) := fun y n => by
      rw [GTilde.map_add_int]; constructor <;> intro h <;> linarith
    -- reduce to `[c, c + 1)`
    set j := ⌊t - c⌋
    set y := t - j
    have hy1 : c ≤ y := by have := Int.floor_le (t - c); simp only [y]; linarith
    have hy2 : y < c + 1 := by have := Int.lt_floor_add_one (t - c); simp only [y]; linarith
    have hty : t = y + j := by simp only [y]; ring
    have hqy : 0 < Causal.Flat.minkQ (dsProj p (linkCover p θ y)) := by rw [← hq y j, ← hty]; exact ht
    have hyc : y ≠ c := fun h => by
      rw [h] at hqy; exact hqy.ne' ((hfn c).1 hc)
    have hyc₁ : y ≠ c₁ := fun h => by
      rw [h] at hqy; exact hqy.ne' ((hfn c₁).1 hc₁)
    rw [hty, hshift]
    -- each half maps into the time-like or the space-like directions
    have hTo : IsOpen (dsFutureDirs p ∪ dsPastDirs p) :=
      (isOpen_dsFutureDirs p).union (isOpen_dsPastDirs p)
    have hSo : IsOpen {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} :=
      isOpen_lt continuous_const (Causal.Flat.continuous_minkQ.comp (continuous_dsProj p))
    have hTS : Disjoint (dsFutureDirs p ∪ dsPastDirs p)
        {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} :=
      Set.disjoint_left.2 fun σ h1 h2 => (minkQ_neg_of_timelike h1).not_gt h2
    have half : ∀ {a b : ℝ}, (∀ z ∈ Ioo a b, g z ≠ z) →
        linkCover p θ '' Ioo a b ⊆ dsFutureDirs p ∪ dsPastDirs p ∨
          linkCover p θ '' Ioo a b ⊆ {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} :=
      fun {a b} hno => (isPreconnected_Ioo.image _
        (isCoveringMap_linkCover p θ).continuous.continuousOn).subset_or_subset hTo hSo hTS
        (by
          rintro _ ⟨z, hz, rfl⟩
          rcases lt_trichotomy (Causal.Flat.minkQ (dsProj p (linkCover p θ z))) 0 with h | h | h
          · exact Or.inl (timelike_of_minkQ_neg h)
          · exact absurd ((hfn z).2 h) (hno z hz)
          · exact Or.inr h)
    have hno₀ : ∀ z ∈ Ioo c c₁, g z ≠ z := fun z hz hgz =>
      (huniq z ⟨hz.1, hz.2.trans hc₁I.2⟩ hgz ▸ hz).2.false
    have hno₁ : ∀ z ∈ Ioo c₁ (c + 1), g z ≠ z := fun z hz hgz =>
      (huniq z ⟨hc₁I.1.trans hz.1, hz.2⟩ hgz ▸ hz).1.false
    -- some time-like point lies in one of the halves
    have htime : ∃ z, (z ∈ Ioo c c₁ ∨ z ∈ Ioo c₁ (c + 1)) ∧
        linkCover p θ z ∈ dsFutureDirs p ∪ dsPastDirs p := by
      obtain ⟨σ, hσ⟩ := (isConnected_dsFutureDirs hp).nonempty
      obtain ⟨t', ht'⟩ := linkCover_surjective p θ σ
      set j' := ⌊t' - c⌋
      set z := t' - j'
      have hz1 : c ≤ z := by have := Int.floor_le (t' - c); simp only [z]; linarith
      have hz2 : z < c + 1 := by have := Int.lt_floor_add_one (t' - c); simp only [z]; linarith
      have htz : t' = z + j' := by simp only [z]; ring
      have hqz : Causal.Flat.minkQ (dsProj p (linkCover p θ z)) < 0 := by
        rw [← hq z j', ← htz, ht']; exact minkQ_neg_of_timelike (Or.inl hσ)
      have hzc : z ≠ c := fun h => by rw [h] at hqz; exact hqz.ne ((hfn c).1 hc)
      have hzc₁ : z ≠ c₁ := fun h => by rw [h] at hqz; exact hqz.ne ((hfn c₁).1 hc₁)
      refine ⟨z, ?_, timelike_of_minkQ_neg hqz⟩
      rcases lt_trichotomy z c₁ with h | h | h
      · exact Or.inl ⟨lt_of_le_of_ne hz1 (Ne.symm hzc), h⟩
      · exact absurd h hzc₁
      · exact Or.inr ⟨h, hz2⟩
    have hyI : y ∈ Ioo c c₁ ∨ y ∈ Ioo c₁ (c + 1) := by
      rcases lt_trichotomy y c₁ with h | h | h
      · exact Or.inl ⟨lt_of_le_of_ne hy1 (Ne.symm hyc), h⟩
      · exact absurd h hyc₁
      · exact Or.inr ⟨h, hy2⟩
    have hmid₀ : (c + c₁) / 2 ∈ Ioo c c₁ := ⟨by linarith [hc₁I.1], by linarith [hc₁I.1]⟩
    have hmid₁ : (c₁ + (c + 1)) / 2 ∈ Ioo c₁ (c + 1) :=
      ⟨by linarith [hc₁I.2], by linarith [hc₁I.2]⟩
    have hnotboth : ¬ (linkCover p θ '' Ioo c c₁ ⊆
          {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} ∧
        linkCover p θ '' Ioo c₁ (c + 1) ⊆ {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)}) :=
      fun ⟨h0, h1⟩ => by
        obtain ⟨z, hzI, hzT⟩ := htime
        rcases hzI with hz | hz
        · exact Set.disjoint_left.1 hTS hzT (h0 ⟨z, hz, rfl⟩)
        · exact Set.disjoint_left.1 hTS hzT (h1 ⟨z, hz, rfl⟩)
    have hyS : linkCover p θ y ∈ {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} := hqy
    rcases hdir with ⟨d₀, d₁⟩ | ⟨d₀, d₁⟩
    · rcases hyI with hy | hy
      · exfalso
        have h1 : linkCover p θ '' Ioo c₁ (c + 1) ⊆
            {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} := by
          rcases half hno₁ with h | h
          · exact absurd (hT _ (h ⟨_, hmid₁, rfl⟩)) (lt_asymm (d₁ _ hmid₁))
          · exact h
        rcases half hno₀ with h0 | h0
        · exact Set.disjoint_left.1 hTS (h0 ⟨y, hy, rfl⟩) hyS
        · exact hnotboth ⟨h0, h1⟩
      · exact d₁ y hy
    · rcases hyI with hy | hy
      · exact d₀ y hy
      · exfalso
        have h0 : linkCover p θ '' Ioo c c₁ ⊆
            {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} := by
          rcases half hno₀ with h | h
          · exact absurd (hT _ (h ⟨_, hmid₀, rfl⟩)) (lt_asymm (d₀ _ hmid₀))
          · exact h
        rcases half hno₁ with h1 | h1
        · exact Set.disjoint_left.1 hTS (h1 ⟨y, hy, rfl⟩) hyS
        · exact hnotboth ⟨h0, h1⟩
  have hfn := fixed_iff_null hp hA hg hfix
  have hpast : ∀ t, linkCover p θ t ∈ dsPastDirs p →
      linkCover p θ (t + 1) ∈ dsFutureDirs p := fun t ht => by
    rw [linkCover_add_one]
    show Causal.Flat.IsFutureTimelike (dsProj p ((-linkCover p θ t : Link p) : TpHS p))
    rw [dsProj_neg]; exact ht
  have hsh : ∀ t, (t < g t ↔ t + 1 < g (t + 1)) ∧ (g t < t ↔ g (t + 1) < t + 1) := fun t => by
    have := GTilde.map_add_int g t 1
    push_cast at this
    rw [this]
    exact ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith,
      fun h => by linarith⟩⟩
  rcases sign_const (p := p) (θ := θ) (g := g) (isOpen_dsFutureDirs p)
      (isConnected_dsFutureDirs hp).isPreconnected
      (fun t ht hgt => (minkQ_neg_of_timelike (Or.inl ht)).ne ((hfn t).1 hgt)) with hr | hl
  · have hT : ∀ t, linkCover p θ t ∈ dsFutureDirs p ∪ dsPastDirs p → t < g t := fun t ht => by
      rcases ht with ht | ht
      · exact hr t ht
      · exact (hsh t).1.2 (hr _ (hpast t ht))
    exact Or.inl ⟨hT, core hA hg hfix hT⟩
  · have hT : ∀ t, linkCover p θ t ∈ dsFutureDirs p ∪ dsPastDirs p → g t < t := fun t ht => by
      rcases ht with ht | ht
      · exact hl t ht
      · exact (hsh t).2.2 (hl _ (hpast t ht))
    have hgi : ∀ t, linkCover p θ (g⁻¹ t) = A⁻¹ • linkCover p θ t := fun t => by
      rw [eq_inv_smul_iff, ← hg, GTilde.apply_inv_apply]
    obtain ⟨x, hx⟩ := hfix
    have hfixi : ∃ x, g⁻¹ x = x := ⟨x, by have := GTilde.inv_apply_apply g x; rwa [hx] at this⟩
    have hTi : ∀ t, linkCover p θ t ∈ dsFutureDirs p ∪ dsPastDirs p → t < g⁻¹ t :=
      fun t ht => by
        have := GTilde.strictMono g⁻¹ (hT t ht); rwa [GTilde.inv_apply_apply] at this
    have hS := core (inv_ne_one.2 hA) hgi hfixi hTi
    exact Or.inr ⟨hT, fun t ht => by
      have := GTilde.strictMono g (hS t ht); rwa [GTilde.apply_inv_apply] at this⟩

end DeSitterDynamics

/-! ### The types by the position of `p` (l.785–802) -/

/-- **Time-like** (l.788–791): at `p ∈ ℍ²±` the underlying `ℝP¹`-circle is elliptic (central
holonomy included, OQ-113 (d)). -/
theorem GammaLinkCircle.IsLiftedDev.isElliptic_of_timelike (h : C.IsLiftedDev θ E D f)
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) : GTilde.IsElliptic f ∨ GTilde.toPSL f = 1 := by
  sorry -- SORRY(bbsrem:previous_section_observed_only): needs that at a time-like `p` the tangent action of `ρ ∈ Γ_p` is a rotation of the Euclidean plane `p^⊥` (`dsProj` is an isometry onto it), so that it has an eigen-ray only when it is `±id`; then `pslMk (gammaToSL ρ)` has no fixed point on `ℝP¹` or is `1`. The Euclidean structure of `p^⊥` at a time-like `p` is not built in `GX.BBS.IPm`

/-- **Space-like** (l.794–795): at `p ∈ dS²` and with non-trivial holonomy, the underlying
`ℝP¹`-circle is hyperbolic. -/
theorem GammaLinkCircle.IsLiftedDev.isHyperbolic_of_deSitter (h : C.IsLiftedDev θ E D f)
    (hp : C.pt ∈ HS.piece 2 .deSitter) (hρ : GTilde.toPSL f ≠ 1) : GTilde.IsHyperbolic f := by
  obtain ⟨ρ, hρf⟩ := h.exists_linkCover_apply
  exact isHyperbolic_of_linkCover hp hρf hρ

/-- **Light-like** (l.797–800): at `p ∈ ∂ℍ²±` and with non-trivial holonomy, the underlying
`ℝP¹`-circle is parabolic. -/
theorem GammaLinkCircle.IsLiftedDev.isParabolic_of_null (h : C.IsLiftedDev θ E D f)
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) = 0) (hρ : GTilde.toPSL f ≠ 1) : GTilde.IsParabolic f := by
  sorry -- SORRY(bbsrem:previous_section_observed_only): needs the single-element form of `GX.fixedPoints_eq_of_null`: an element `≠ 1` of `Γ_p`, `p` lightlike, fixes no ray but the two tangent directions (its tangent action preserves `B(p, ·)` and the tangent line, so it is unipotent). With the argument of `GX.GammaLinkCircle.IsLiftedDev.even_of_nonneg` (no anti-fixed ray) the underlying element of `PSL(2,ℝ)` then has exactly one fixed point. Not built

/-- **l.794–795 and l.797–800 need non-trivial holonomy**: at every `p`, the link of a regular
point is a `(Γ_p, ℓ(p))`-circle whose underlying `ℝP¹`-circle has lifted holonomy `δ²`, which is not
hyperbolic (l.794–795, `p ∈ dS²`) nor parabolic (`GX.not_isParabolic_delta_sq`; l.797–800,
`p ∈ ∂ℍ²±`). This is a regular point;
the singular counterexample is the `n`-fold cyclic cover of `ℓ(p)`, `n ≥ 2` (trivial
`Γ_p`-holonomy, lifted holonomy `δ^{2n}`), argued, not built. -/
theorem regular_not_isHyperbolic {p : HS 2} (θ : TpHS p ≃ₗ[ℝ] ℂ) :
    ∃ E D, (GammaLinkCircle.regular p).IsLiftedDev θ E D (GTilde.delta ^ 2) ∧
      ¬ GTilde.IsHyperbolic (GTilde.delta ^ 2) := by
  refine ⟨fun s => linkCover p θ (2 * s), fun s => 2 * s, ⟨⟨?_, fun σ => ?_, fun s => ?_,
    fun s t hst => ?_⟩, continuous_const.mul continuous_id, fun a b hab => by simp only; linarith,
    fun s => ⟨1, Eventually.of_forall fun s' => ?_⟩, fun s => ?_⟩, ?_⟩
  · exact (isCoveringMap_linkCover p θ).comp_homeomorph (Homeomorph.mulLeft₀ (2 : ℝ) two_ne_zero)
  · obtain ⟨t, ht⟩ := linkCover_surjective p θ σ
    exact ⟨t / 2, by show linkCover p θ (2 * (t / 2)) = σ; rw [mul_div_cancel₀ _ two_ne_zero, ht]⟩
  · show linkCover p θ (2 * (s + 1)) = linkCover p θ (2 * s)
    rw [show 2 * (s + 1) = 2 * s + 2 * (((1 : ℤ)) : ℝ) by push_cast; ring, linkCover_add_two_mul]
  · obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff p θ).1 hst
    exact ⟨n, by linarith⟩
  · show linkCover p θ (2 * s') = (1 : GammaP p) • (chartAt (Link p) (linkCover p θ (2 * s)))
      (linkCover p θ (2 * s'))
    rw [one_smul, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
  · simp only
    rw [pow_two, GTilde.coe_mul_apply, GTilde.delta_apply, GTilde.delta_apply]; ring
  · intro hh
    have : (4 : ℝ) < PSL2.trSq (GTilde.toPSL (GTilde.delta ^ 2)) := hh
    rw [map_pow, GTilde.toPSL_delta, one_pow, PSL2.trSq_one] at this
    exact lt_irrefl _ this

/-- `δ²` is not parabolic: the light-like half of the finding on l.794–800. -/
theorem not_isParabolic_delta_sq : ¬ GTilde.IsParabolic (GTilde.delta ^ 2) := fun h =>
  h.2 (by rw [map_pow, GTilde.toPSL_delta, one_pow])

/-- **The degree is even** (l.905, l.918) at every non-timelike `p`. -/
theorem GammaLinkCircle.IsLiftedDev.even_of_nonneg (h : C.IsLiftedDev θ E D f)
    (hp : 0 ≤ Causal.Flat.minkQ (C.pt : 𝕄)) {k : ℤ} {g : GTilde} (hg : ∃ x, g x = x)
    (hfg : f = GTilde.delta ^ k * g) : Even k := by
  obtain ⟨ρ, hρ⟩ := h.exists_linkCover_apply
  -- a direction fixed by every element of `Γ_p`
  obtain ⟨n, hn⟩ : ∃ n : Link C.pt, ρ • n = n := by
    rcases hp.lt_or_eq with hq | hq
    · obtain ⟨n₁, -, h₁, -⟩ := exists_two_null (p := C.pt) hq
      exact ⟨n₁, smul_eq_of_deSitter hq h₁ ρ⟩
    · have hne : (tangentDirs C.pt).Nonempty := by
        by_contra h0
        rw [not_nonempty_iff_eq_empty] at h0
        have := ncard_tangentDirs (p := C.pt) hq.symm
        rw [h0, ncard_empty] at this
        exact absurd this (by norm_num)
      obtain ⟨n, hn⟩ := hne
      exact ⟨n, smul_eq_of_null hq.symm hn ρ⟩
  obtain ⟨x, hx⟩ := hg
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  obtain ⟨m, rfl⟩ := hodd
  -- `ρ` would map `σ = linkCover x` to `−σ`
  have hfx : f x = x + 1 + 2 * m := by
    rw [hfg, GTilde.coe_mul_apply, GTilde.delta_zpow_apply, hx]; push_cast; ring
  have hσ : ρ • linkCover C.pt θ x = -linkCover C.pt θ x := by
    rw [← hρ, hfx, linkCover_add_two_mul, linkCover_add_one]
  obtain ⟨c, hc, hcT⟩ := (gammaP_smul_eq_iff ρ n).1 hn
  rw [gammaP_smul_def, linRaySmul_eq_iff, coe_neg_sphere] at hσ
  obtain ⟨c', hc', hc'T⟩ := hσ
  set σ := linkCover C.pt θ x
  have harea := linkArea_tangent C.pt ρ (n : TpHS C.pt) (σ : TpHS C.pt)
  rw [hcT, hc'T, linkArea_smul_left, smul_neg, ← neg_smul, linkArea_smul_right] at harea
  have hL : linkArea C.pt (n : TpHS C.pt) (σ : TpHS C.pt) = 0 := by
    have : (1 + c * c') * linkArea C.pt (n : TpHS C.pt) (σ : TpHS C.pt) = 0 := by
      linear_combination -harea
    exact (mul_eq_zero.1 this).resolve_left (by positivity)
  obtain ⟨r, hr⟩ := eq_smul_of_linkArea_eq_zero C.pt (raySphere_ne_zero n) hL
  have : (c + c') • (σ : TpHS C.pt) = 0 := by
    have e : GammaP.tangent ρ (σ : TpHS C.pt) = c • (σ : TpHS C.pt) := by
      rw [hr, map_smul, hcT, smul_comm]
    rw [add_smul, ← e, hc'T, smul_neg, neg_add_cancel]
  exact raySphere_ne_zero σ ((smul_eq_zero.1 this).resolve_left (by positivity))

/-! ### Degree `0` (l.866–891) -/

/-- **Space-like singularities of degree `0`** (l.866–879): `L` is the quotient of an interval `I`
of `ℓ(p)` by `⟨g⟩` (`I` the image of `D`, read in `ℓ(p)`), and there are three possibilities:
`I = i⁺(ℓ(p))` (BTZ-like past; then `L = i⁺(L)`, `i⁻(L) = ∅`), `I = i⁻(ℓ(p))` (BTZ-like future),
or `I` a space-like arc (Misner; `i⁺(L) = i⁻(L) = ∅`). -/
theorem GammaLinkCircle.IsLiftedDev.spacelike_degree_zero (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : C.pt ∈ HS.piece 2 .deSitter) (hh : GTilde.IsHyperbolic f)
    (hfix : ∃ x, f x = x) :
    (linkCover C.pt θ '' range D = iPlus C.pt ∧ C.iPlusL = univ ∧ C.iMinusL = ∅) ∨
    (linkCover C.pt θ '' range D = iMinus C.pt ∧ C.iMinusL = univ ∧ C.iPlusL = ∅) ∨
    (linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)} ∧
      C.iPlusL = ∅ ∧ C.iMinusL = ∅) := by
  sorry -- SORRY(bbsrem:previous_section_observed_only): by `GX.IsLiftedDevPair.exhaust` the developed image is `]x₀, x₁[` between consecutive fixed points of `f`, which are the lifts of the lightlike directions (`GX.fixed_iff_null`), so `linkCover` maps it into one of `i⁺`, `i⁻`, the space-like set (`GX.timelike_spacelike_dir`'s `half` argument); the missing step is "onto": that `i⁺(ℓ(p))` is exactly one arc between two consecutive lightlike directions (its lift is a union of components of `ℝ ∖ Fix(g)`), not built

/-- **Light-like singularities of degree `0`** (l.880–891), at `p ∈ ∂ℍ²₊`: `L` is the quotient of
`i⁺(ℓ(p))` (future cuspidal) or of `i⁻(ℓ(p))` minus its tangent directions (extreme BTZ-like
future; the printed `i⁻(ℓ(p))` is a closed arc, OQ-116 (b)) by a parabolic element. -/
theorem GammaLinkCircle.IsLiftedDev.bdPlus_degree_zero (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : C.pt ∈ HS.piece 2 .bdPlus) (hpar : GTilde.IsParabolic f)
    (hfix : ∃ x, f x = x) :
    (linkCover C.pt θ '' range D = iPlus C.pt ∧ C.iPlusL = univ ∧ C.iMinusL = ∅) ∨
    (linkCover C.pt θ '' range D = iMinus C.pt \ tangentDirs C.pt ∧ C.iMinusL = univ ∧
      C.iPlusL = ∅) := by
  sorry -- SORRY(bbsrem:previous_section_observed_only): needs the parabolic analysis at a lightlike `p` (see `GX.GammaLinkCircle.IsLiftedDev.isParabolic_of_null`): the fixed points of `f` are the lifts of the two tangent directions, and the two open arcs `{B(p,·) < 0} = i⁺`, `{B(p,·) > 0} = i⁻ ∖ T` (`GX.components_compl_tangentDirs`) are the possible images; not built

/-! ### Degree `k ≥ 1` (l.893–922) -/

/-- **Space-like singularities of degree `k ≥ 1`, the components of `I^±`** (l.896–905): the fixed
points of `g` are `x₀ + i`, `x₁ + i` (`x_{2i} = δⁱ x₀`, `x_{2i+1} = δⁱ x₁`), the components of
`I⁺` are `δ^{2i} ]x₀, x₁[` and those of `I⁻` are `δ^{2i+1} ]x₀, x₁[`. -/
theorem GammaLinkCircle.IsLiftedDev.iPlus_components (h : C.IsLiftedDev θ E D f)
    (hp : C.pt ∈ HS.piece 2 .deSitter) {k : ℤ} (hk : 1 ≤ k) {g : GTilde} (hg : ∃ x, g x = x)
    (hh : GTilde.IsHyperbolic g) (hfg : f = GTilde.delta ^ k * g) :
    ∃ x₀ x₁ : ℝ, x₀ < x₁ ∧ x₁ < x₀ + 1 ∧ g x₀ = x₀ ∧ g x₁ = x₁ ∧
      (∀ y, g y = y → ∃ i : ℤ, y = x₀ + i ∨ y = x₁ + i) ∧
      linkCover C.pt θ ⁻¹' iPlus C.pt = ⋃ i : ℤ, Ioo (x₀ + 2 * i) (x₁ + 2 * i) ∧
      linkCover C.pt θ ⁻¹' iMinus C.pt = ⋃ i : ℤ, Ioo (x₀ + 2 * i + 1) (x₁ + 2 * i + 1) := by
  sorry -- SORRY(bbsrem:previous_section_observed_only): the dynamics are built (`GX.GTilde.IsHyperbolic.fixed_structure`: fixed points `x₀ + ℤ`, `x₁ + ℤ`; `GX.timelike_spacelike_dir`: time-like components moved one way, space-like the other); the missing step is the arc structure of `ℓ(p)`: that `linkCover` maps `]x₀, x₁[` onto `i⁺(ℓ(p))` exactly (not into a proper sub-arc), i.e. that `i⁺` is one arc between consecutive lightlike directions; not built

/-- **A positive space-like singularity of degree `k ≥ 1`** (l.908–910), in the form of l.915
(a reading, SCOPE (f)): `p ∈ dS²`, the underlying `ℝP¹`-circle is hyperbolic of degree `k ≥ 1`,
`f = δᵏ g`, and `g x ≥ x` for every `x ∈ I⁺` (`I⁺ = D(E⁻¹ i⁺(L))` in `L̃_p ≈ ℝP̃¹`). The primary
definition of l.908–910 (the left extremities of the components of `I⁺` are repelling) is
equivalent, not formalized. -/
def GammaLinkCircle.IsSpacelikePositive (C : GammaLinkCircle L) : Prop :=
  C.pt ∈ HS.piece 2 .deSitter ∧ ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde), C.IsLiftedDev θ E D f ∧ 1 ≤ k ∧
      (∃ x, g x = x) ∧ GTilde.IsHyperbolic g ∧ f = GTilde.delta ^ k * g ∧
      ∀ s, E s ∈ C.iPlusL → D s ≤ g (D s)

/-- **A negative space-like singularity of degree `k ≥ 1`** (l.911–913), in the form of l.915:
`g x ≤ x` on `I⁺`. -/
def GammaLinkCircle.IsSpacelikeNegative (C : GammaLinkCircle L) : Prop :=
  C.pt ∈ HS.piece 2 .deSitter ∧ ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde), C.IsLiftedDev θ E D f ∧ 1 ≤ k ∧
      (∃ x, g x = x) ∧ GTilde.IsHyperbolic g ∧ f = GTilde.delta ^ k * g ∧
      ∀ s, E s ∈ C.iPlusL → g (D s) ≤ D s

/-- **Positivity does not depend on the choices**: if `C` is positive, every lifted developing
pair (for every oriented `θ`) satisfies the inequality. -/
theorem GammaLinkCircle.IsSpacelikePositive.forall (hC : C.IsSpacelikePositive)
    (hθ : IsOrientedTangent C.pt θ) (h : C.IsLiftedDev θ E D f) {k : ℤ} {g : GTilde}
    (hg : ∃ x, g x = x) (hfg : f = GTilde.delta ^ k * g) :
    ∀ s, E s ∈ C.iPlusL → D s ≤ g (D s) := by
  obtain ⟨-, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, -, hfg₀, hpos⟩ := hC
  obtain ⟨ψ, κ, hE, hD, hf⟩ := h₀.relate hθ₀ hθ h
  have hgg := GTilde.conj_factor hg₀ hg hfg₀ hfg hf
  intro s hs
  rw [hE] at hs
  have := (GTilde.strictMono κ).monotone (hpos (ψ s) hs)
  rw [hD, hgg, GTilde.coe_mul_apply, GTilde.coe_mul_apply, GTilde.inv_apply_apply]
  exact this

theorem GammaLinkCircle.IsSpacelikeNegative.forall (hC : C.IsSpacelikeNegative)
    (hθ : IsOrientedTangent C.pt θ) (h : C.IsLiftedDev θ E D f) {k : ℤ} {g : GTilde}
    (hg : ∃ x, g x = x) (hfg : f = GTilde.delta ^ k * g) :
    ∀ s, E s ∈ C.iPlusL → g (D s) ≤ D s := by
  obtain ⟨-, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, -, hfg₀, hneg⟩ := hC
  obtain ⟨ψ, κ, hE, hD, hf⟩ := h₀.relate hθ₀ hθ h
  have hgg := GTilde.conj_factor hg₀ hg hfg₀ hfg hf
  intro s hs
  rw [hE] at hs
  have := (GTilde.strictMono κ).monotone (hneg (ψ s) hs)
  rw [hD, hgg, GTilde.coe_mul_apply, GTilde.coe_mul_apply, GTilde.inv_apply_apply]
  exact this

/-- **A positive light-like singularity of degree `k ≥ 1`** (l.917–922): `p ∈ ∂ℍ²±`, the
underlying `ℝP¹`-circle is parabolic of degree `k ≥ 1`, and `g x ≥ x` on `L̃_p`. -/
def GammaLinkCircle.IsLightlikePositive (C : GammaLinkCircle L) : Prop :=
  Causal.Flat.minkQ (C.pt : 𝕄) = 0 ∧ ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde), C.IsLiftedDev θ E D f ∧ 1 ≤ k ∧
      (∃ x, g x = x) ∧ GTilde.IsParabolic g ∧ f = GTilde.delta ^ k * g ∧ ∀ x, x ≤ g x

def GammaLinkCircle.IsLightlikeNegative (C : GammaLinkCircle L) : Prop :=
  Causal.Flat.minkQ (C.pt : 𝕄) = 0 ∧ ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde), C.IsLiftedDev θ E D f ∧ 1 ≤ k ∧
      (∃ x, g x = x) ∧ GTilde.IsParabolic g ∧ f = GTilde.delta ^ k * g ∧ ∀ x, g x ≤ x

/-- **The light-like dichotomy** (l.917–922). -/
theorem GammaLinkCircle.IsLiftedDev.lightlike_dichotomy (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : Causal.Flat.minkQ (C.pt : 𝕄) = 0) {k : ℤ} (hk : 1 ≤ k)
    {g : GTilde} (hg : ∃ x, g x = x) (hpar : GTilde.IsParabolic g)
    (hfg : f = GTilde.delta ^ k * g) :
    (C.IsLightlikePositive ∨ C.IsLightlikeNegative) ∧
      ¬ (C.IsLightlikePositive ∧ C.IsLightlikeNegative) := by
  refine ⟨?_, fun ⟨⟨_, θ₁, hθ₁, E₁, D₁, f₁, k₁, g₁, h₁, _, hg₁, hpar₁, hfg₁, hle₁⟩,
    ⟨_, θ₂, hθ₂, E₂, D₂, f₂, k₂, g₂, h₂, _, hg₂, hpar₂, hfg₂, hge₂⟩⟩ => ?_⟩
  · rcases (hpar.le_or_ge hg).1 with hle | hge
    · exact Or.inl ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hpar, hfg, hle⟩
    · exact Or.inr ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hpar, hfg, hge⟩
  · obtain ⟨ψ, κ, -, -, hf⟩ := h₁.relate hθ₁ hθ₂ h₂
    have hgg := GTilde.conj_factor hg₁ hg₂ hfg₁ hfg₂ hf
    exact (hpar₂.le_or_ge hg₂).2 ⟨fun x => by rw [hgg]; exact GTilde.le_conj_apply hle₁ κ x,
      hge₂⟩

end GammaCircle

/-! ## 6. Isomorphisms of `(Γ_p, ℓ(p))`-circles, and `bbsrem:previous_section_observed_only` -/

section Remark

variable {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']

/-- **An isomorphism of `(Γ_p, ℓ(p))`-circles** (same `p`): a homeomorphism which is a
`(Γ_p, ℓ(p))`-morphism. -/
def GammaLinkCircle.IsIso (C : GammaLinkCircle L) (C' : GammaLinkCircle L') (φ : L ≃ₜ L') :
    Prop :=
  ∃ h : C'.pt = C.pt,
    letI := C.atlas
    letI : ChartedSpace (Link C.pt) L' := h ▸ C'.atlas
    IsGXMorphism (GammaP C.pt) (Link C.pt) φ

/-- **Positivity is an isomorphism invariant.** -/
theorem GammaLinkCircle.IsIso.isSpacelikePositive {C : GammaLinkCircle L}
    {C' : GammaLinkCircle L'} {φ : L ≃ₜ L'} (hφ : C.IsIso C' φ) (hC : C.IsSpacelikePositive) :
    C'.IsSpacelikePositive := by
  obtain ⟨hpt, hmor⟩ := hφ
  obtain ⟨q, atl, hgr, hcirc⟩ := C'
  simp only at hpt
  subst hpt
  letI := C.atlas
  letI : ChartedSpace (Link C.pt) L' := atl
  have hmor' : IsGXMorphism (GammaP C.pt) (Link C.pt) φ := hmor
  obtain ⟨hp, θ, hθ, E, D, f, k, g, ⟨hE, hDc, hDm, hd, hDf⟩, hk, hg, hh, hfg, hpos⟩ := hC
  refine ⟨hp, θ, hθ, φ ∘ E, D, f, k, g, ⟨⟨hE.isCoveringMap.homeomorph_comp φ,
    φ.surjective.comp hE.surjective, fun s => by simp only [Function.comp_apply, hE.add_one],
    fun s t h => hE.fiber s t (φ.injective h)⟩, hDc, hDm, fun s => ?_, hDf⟩, hk, hg, hh, hfg,
    fun s hs => hpos s ?_⟩
  · obtain ⟨A₁, h₁⟩ := hd s
    obtain ⟨A₂, h₂⟩ := hmor'.exists_smul_eq (E s)
    refine ⟨A₁ * A₂⁻¹, ?_⟩
    filter_upwards [h₁, hE.isCoveringMap.continuous.continuousAt.eventually h₂] with s' hs1 hs2
    show (linkCover C.pt θ ∘ D) s' = (A₁ * A₂⁻¹) • chartAt (Link C.pt) (φ (E s)) (φ (E s'))
    rw [hs2, mul_smul, inv_smul_smul, hs1]
  · obtain ⟨A₂, h₂⟩ := hmor'.exists_smul_eq (E s)
    have e := h₂.self_of_nhds
    have hsI : chartAt (Link C.pt) (φ (E s)) (φ (E s)) ∈ iPlus C.pt := hs
    rw [e, smul_mem_iPlus_iff] at hsI
    exact hsI

/-- **`bbsrem:previous_section_observed_only` (i)** (l.927–928): there is only one hyperbolic
`ℝP¹`-circle of holonomy `⟨g⟩` up to `ℝP¹`-isomorphism. -/
theorem rp1Iso_of_zpowers_eq [ChartedSpace RP1 L] [HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1)]
    [ChartedSpace RP1 L'] [HasGroupoid L' (gxGroupoid PSL(2, ℝ) RP1)] {f f' : GTilde}
    (hf : HasLiftedHolonomy L f) (hf' : HasLiftedHolonomy L' f')
    (hz : Subgroup.zpowers f = Subgroup.zpowers f') (hh : GTilde.IsHyperbolic f) :
    ∃ φ : L ≃ₜ L', IsRP1Iso φ := by
  obtain ⟨E, D, hW⟩ := hf
  have hW : IsLiftedDevPair E D f := hW
  have hJ := hW.isComp
  -- `f` has infinite order: it moves the points of its developed image to the right
  obtain ⟨x, hx⟩ := hJ.nonempty
  have key : ∀ m : ℕ, x < (f ^ (m + 1)) x ∧ (f ^ (m + 1)) x ∈ range D := by
    intro m
    induction m with
    | zero =>
      rw [zero_add, pow_one]
      obtain ⟨s, rfl⟩ := hx
      exact ⟨hJ.lt_apply _ ⟨s, rfl⟩, ⟨s + 1, hW.2.2.2.2 s⟩⟩
    | succ m ih =>
      rw [pow_succ', GTilde.coe_mul_apply]
      obtain ⟨s, hs⟩ := ih.2
      refine ⟨ih.1.trans (hJ.lt_apply _ ih.2), ⟨s + 1, ?_⟩⟩
      rw [hW.2.2.2.2 s, hs]
  have hinf : ∀ a : ℤ, f ^ a = 1 → a = 0 := by
    intro a ha
    by_contra ha0
    have hna : f ^ a.natAbs = 1 := by
      rcases Int.natAbs_eq a with h | h
      · rw [← zpow_natCast, ← h, ha]
      · rw [← zpow_natCast, show ((a.natAbs : ℕ) : ℤ) = -a by omega, zpow_neg, ha, inv_one]
    obtain ⟨m, hm⟩ : ∃ m, a.natAbs = m + 1 := ⟨a.natAbs - 1, by omega⟩
    have := (key m).1
    rw [← hm, hna, GTilde.one_apply] at this
    exact lt_irrefl _ this
  -- `f' = f` or `f' = f⁻¹`
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hz ▸ Subgroup.mem_zpowers f')
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hz.symm ▸ Subgroup.mem_zpowers f)
  have hmj : m * j = 1 := by
    have h1 : f ^ (m * j - 1) = 1 := by
      rw [zpow_sub, zpow_mul, hm, hj, zpow_one, mul_inv_cancel]
    have := hinf _ h1
    omega
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmj with rfl | rfl
  · rw [zpow_one] at hm
    exact exists_rp1Iso_of_conj ⟨E, D, hW⟩ hf' ⟨1, by rw [← hm]; group⟩
  · rw [zpow_neg, zpow_one] at hm
    obtain ⟨k, g, hg, hfg⟩ := GTilde.exists_delta_zpow_mul_of_not_isElliptic
      (GTilde.IsHyperbolic.not_isElliptic hh)
    have hk0 : 0 ≤ k := HasLiftedHolonomy.deg_nonneg ⟨E, D, hW⟩ hg hfg
    have hc : GTilde.delta ^ (-k) * g⁻¹ = g⁻¹ * GTilde.delta ^ (-k) :=
      ((Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ GTilde.delta_mem_center (-k))) g⁻¹).symm
    have hfi : f' = GTilde.delta ^ (-k) * g⁻¹ := by
      rw [← hm, hfg, mul_inv_rev, hc, zpow_neg]
    obtain ⟨y, hy⟩ := hg
    have hgi : g⁻¹ y = y := by have := GTilde.inv_apply_apply g y; rwa [hy] at this
    have hk1 : 0 ≤ -k := HasLiftedHolonomy.deg_nonneg hf' ⟨y, hgi⟩ hfi
    have hk : k = 0 := by omega
    rw [hk, zpow_zero, one_mul] at hfg
    obtain ⟨h, hhf⟩ := hh.exists_conj_inv ⟨y, by rw [hfg]; exact hy⟩
    exact exists_rp1Iso_of_conj ⟨E, D, hW⟩ hf' ⟨h, by rw [hhf, hm]⟩

/-- **`bbsrem:previous_section_observed_only` (ii)** (l.928–930), on `ℓ(p)`, `p ∈ dS²`: for
`A ∈ Γ_p ∖ {1}` and its lift `g` with a fixed point, a real projective conjugacy `h ∈ G̃` (which
preserves the orientation) between `g` and `g⁻¹` maps the time-like directions to space-like
ones, and the space-like directions to time-like ones. -/
theorem conj_inv_swaps_timelike_spacelike {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter)
    (θ : TpHS p ≃ₗ[ℝ] ℂ) {A : GammaP p} (hA : A ≠ 1) {g : GTilde}
    (hg : ∀ t, linkCover p θ (g t) = A • linkCover p θ t) (hfix : ∃ x, g x = x) {h : GTilde}
    (hh : h * g * h⁻¹ = g⁻¹) (t : ℝ) :
    (linkCover p θ t ∈ iPlus p ∪ iMinus p →
        0 < Causal.Flat.minkQ (dsProj p (linkCover p θ (h t)))) ∧
      (0 < Causal.Flat.minkQ (dsProj p (linkCover p θ t)) →
        linkCover p θ (h t) ∈ iPlus p ∪ iMinus p) := by
  have hfn := fixed_iff_null hp hA hg hfix
  rw [iPlus_of_deSitter hp, iMinus_of_deSitter hp]
  have h1 := GTilde.lt_apply_iff_of_conj_inv hh
  have hh' : h * g⁻¹ * h⁻¹ = g⁻¹⁻¹ :=
    calc h * g⁻¹ * h⁻¹ = (h * g * h⁻¹)⁻¹ := by group
      _ = g⁻¹⁻¹ := by rw [hh]
  have h2 : ∀ x, g x < x ↔ h x < g (h x) := fun x => by
    have := GTilde.lt_apply_iff_of_conj_inv hh' x
    constructor
    · intro hx
      have h3 : x < g⁻¹ x := by
        have := GTilde.strictMono g⁻¹ hx; rwa [GTilde.inv_apply_apply] at this
      have h4 := this.1 h3
      have := GTilde.strictMono g h4; rwa [GTilde.apply_inv_apply] at this
    · intro hx
      have h3 : g⁻¹ (h x) < h x := by
        have := GTilde.strictMono g⁻¹ hx; rwa [GTilde.inv_apply_apply] at this
      have h4 := this.2 h3
      have := GTilde.strictMono g h4; rwa [GTilde.apply_inv_apply] at this
  rcases timelike_spacelike_dir hp hA hg hfix with ⟨hT, hS⟩ | ⟨hT, hS⟩
  · refine ⟨fun ht => ?_, fun ht => ?_⟩
    · have := (h1 t).1 (hT t ht)
      rcases lt_trichotomy (Causal.Flat.minkQ (dsProj p (linkCover p θ (h t)))) 0 with hq | hq | hq
      · exact absurd (hT _ (timelike_of_minkQ_neg hq)) (lt_asymm this)
      · exact absurd ((hfn (h t)).2 hq) this.ne
      · exact hq
    · have := (h2 t).1 (hS t ht)
      rcases lt_trichotomy (Causal.Flat.minkQ (dsProj p (linkCover p θ (h t)))) 0 with hq | hq | hq
      · exact timelike_of_minkQ_neg hq
      · exact absurd ((hfn (h t)).2 hq) this.ne'
      · exact absurd (hS _ hq) (lt_asymm this)
  · refine ⟨fun ht => ?_, fun ht => ?_⟩
    · have := (h2 t).1 (hT t ht)
      rcases lt_trichotomy (Causal.Flat.minkQ (dsProj p (linkCover p θ (h t)))) 0 with hq | hq | hq
      · exact absurd (hT _ (timelike_of_minkQ_neg hq)) (lt_asymm this)
      · exact absurd ((hfn (h t)).2 hq) this.ne'
      · exact hq
    · have := (h1 t).1 (hS t ht)
      rcases lt_trichotomy (Causal.Flat.minkQ (dsProj p (linkCover p θ (h t)))) 0 with hq | hq | hq
      · exact timelike_of_minkQ_neg hq
      · exact absurd ((hfn (h t)).2 hq) this.ne
      · exact absurd (hS _ hq) (lt_asymm this)

/-- **The quotient `ℝ/⟨δ² g⟩` along `linkCover`** (the examples of l.928): for `g ∈ G̃` with a fixed
point lifting `A ∈ Γ_p` through `linkCover p θ`, the quotient of `ℝP̃¹` by `δ² g` is a
`(Γ_p, ℓ(p))`-circle `⟨p, cs, hcs, hL⟩` (so its point is `p` by definition) with a lifted developing
pair of lifted holonomy `δ² g`. Through `GX.exists_gammaLinkCircle_quotient_of_forall_lt`. -/
theorem exists_isLiftedDev_delta_sq_mul (p : HS 2) (θ : TpHS p ≃ₗ[ℝ] ℂ) {A : GammaP p}
    {g : GTilde} (hg : ∀ t, linkCover p θ (g t) = A • linkCover p θ t) (hfix : ∃ x, g x = x) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link p) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))) (hL : IsCircle L) (E : ℝ → L)
      (D : ℝ → ℝ),
        (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ E D (GTilde.delta ^ (2 : ℤ) * g) := by
  have happ : ∀ x, (GTilde.delta ^ (2 : ℤ) * g) x = g x + 2 * ((1 : ℤ) : ℝ) := fun x => by
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; ring
  have hlt : ∀ x, x < (GTilde.delta ^ (2 : ℤ) * g) x := fun x => by
    rw [happ]
    have := GTilde.sub_one_lt_apply_of_fixed hfix x
    push_cast; linarith
  have hDf : ∀ x, linkCover p θ ((GTilde.delta ^ (2 : ℤ) * g) x) = A • linkCover p θ x :=
    fun x => by rw [happ, linkCover_add_two_mul, hg]
  obtain ⟨L, _, cs, hcs, hL, E, ψ, hE, hψc, hψm, hψf, hdev⟩ :=
    exists_gammaLinkCircle_quotient_of_forall_lt p
      (isCoveringMap_linkCover p θ).isLocalHomeomorph hlt hDf
  exact ⟨L, inferInstance, cs, hcs, hL, E, ψ, hE, hψc, hψm, hdev, hψf⟩

/-- A point of `i⁺(L)` develops to a future time-like direction, at `p ∈ dS²`. -/
theorem GammaLinkCircle.IsLiftedDev.mem_dsFutureDirs {C : GammaLinkCircle L}
    {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde} (h : C.IsLiftedDev θ E D f)
    (hp : C.pt ∈ HS.piece 2 .deSitter) {s : ℝ} (hs : E s ∈ C.iPlusL) :
    linkCover C.pt θ (D s) ∈ dsFutureDirs C.pt := by
  rw [← iPlus_of_deSitter hp]
  exact (Set.ext_iff.1 h.2.2.2.1.preimage_iPlus s).2 hs

/-- **At `p ∈ dS²`, a non-trivial element of `Γ_p` lifts to `G̃` with a fixed point** through
`linkCover p θ`: some `A ∈ Γ_p ∖ {1}` (`Γ_p` moves the time-like directions,
`GX.fixedPoints_subset_of_deSitter`) has a lift `g ∈ G̃` with a fixed point (`A` fixes the
lightlike directions, `GX.smul_eq_of_deSitter`, so a lift through `GX.exists_rayLift` fixes the
lift of one of them up to `δ^{2n}`), and `g` is hyperbolic (`GX.isHyperbolic_of_linkCover`). -/
theorem exists_gammaP_lift_fixed {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter)
    (θ : TpHS p ≃ₗ[ℝ] ℂ) :
    ∃ (A : GammaP p) (g : GTilde), A ≠ 1 ∧ (∀ t, linkCover p θ (g t) = A • linkCover p θ t) ∧
      (∃ x, g x = x) ∧ GTilde.IsHyperbolic g := by
  -- `Γ_p` moves a future time-like direction
  obtain ⟨σ, hσ⟩ := (isConnected_dsFutureDirs hp).nonempty
  obtain ⟨A, hA⟩ : ∃ A : GammaP p, A • σ ≠ σ := by
    by_contra h
    push Not at h
    exact (minkQ_neg_of_timelike (Or.inl hσ)).ne (fixedPoints_subset_of_deSitter hp h)
  have hA1 : A ≠ 1 := fun h => hA (by rw [h, one_smul])
  -- its lift, normalised by `δ^{2n}` to fix the lift of a lightlike direction
  obtain ⟨F, hF⟩ := exists_rayLift p (θ := θ) (θ' := θ) (g₀ := 1)
    (fun σ => (one_smul _ _).symm) A
  obtain ⟨n₁, -, h₁, -⟩ := exists_two_null hp
  obtain ⟨t₁, ht₁⟩ := linkCover_surjective p θ n₁
  obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff p θ).1
    (show linkCover p θ t₁ = linkCover p θ (F t₁) by rw [hF, ht₁, smul_eq_of_deSitter hp h₁ A])
  set g : GTilde := GTilde.delta ^ (-(2 * n)) * F
  have hgapp : ∀ t, g t = F t + 2 * ((-n : ℤ) : ℝ) := fun t => by
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; ring
  have hg : ∀ t, linkCover p θ (g t) = A • linkCover p θ t := fun t => by
    rw [hgapp, linkCover_add_two_mul, hF]
  have hfix : ∃ x, g x = x := ⟨t₁, by rw [hgapp, hn]; push_cast; ring⟩
  -- `g` is not central: it does not fix the lifts of `σ`
  have hg1 : GTilde.toPSL g ≠ 1 := fun h1 => by
    have hk : g ∈ GTilde.toPSL.ker := h1
    rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hk
    obtain ⟨j, hj⟩ := hk
    obtain ⟨x, hx⟩ := hfix
    rw [← hj, GTilde.delta_zpow_apply] at hx
    have hj0 : j = 0 := by exact_mod_cast (show (j : ℝ) = 0 by linarith)
    obtain ⟨t, ht⟩ := linkCover_surjective p θ σ
    apply hA
    rw [← ht, ← hg, ← hj, hj0, zpow_zero, GTilde.one_apply]
  exact ⟨A, g, hA1, hg, hfix, isHyperbolic_of_linkCover hp hg hg1⟩

/-- **`bbsrem:previous_section_observed_only`, "this remark does not extend"** (l.928): at
every `p ∈ dS²` there are a positive and a negative space-like `(Γ_p, ℓ(p))`-circle of degree `2`
whose lifted holonomies are conjugate in `G̃`, i.e. (`GX.rp1Iso_iff_conj`) whose underlying
`ℝP¹`-circles are isomorphic. They are `ℝ/⟨δ² g⟩` and `ℝ/⟨δ² g⁻¹⟩` (developed by `linkCover`),
`g` the lift with a fixed point of some `A ∈ Γ_p ∖ {1}` (`GX.exists_gammaP_lift_fixed`); `g` is
conjugate to `g⁻¹` in `G̃` (`GX.GTilde.IsHyperbolic.exists_conj_inv`), and the one of `g`, `g⁻¹`
moving the future time-like directions up gives the positive circle
(`GX.timelike_spacelike_dir`). -/
theorem exists_positive_negative {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L L' : Type) (_ : TopologicalSpace L) (_ : TopologicalSpace L') (C : GammaLinkCircle L)
      (C' : GammaLinkCircle L'), C.pt = p ∧ C'.pt = p ∧ C.IsSpacelikePositive ∧
      C'.IsSpacelikeNegative ∧ ∃ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (θ' : TpHS C'.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L)
        (E' : ℝ → L') (D D' : ℝ → ℝ) (f f' : GTilde), C.IsLiftedDev θ E D f ∧
        C'.IsLiftedDev θ' E' D' f' ∧ ∃ κ : GTilde, f' = κ * f * κ⁻¹ := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent p
  obtain ⟨A, g, hA1, hg, hfix, hh⟩ := exists_gammaP_lift_fixed hp θ
  -- `g⁻¹` lifts `A⁻¹`, with a fixed point, hyperbolic
  have hgi : ∀ t, linkCover p θ (g⁻¹ t) = A⁻¹ • linkCover p θ t := fun t => by
    rw [eq_inv_smul_iff, ← hg, GTilde.apply_inv_apply]
  have hfixi : ∃ x, g⁻¹ x = x := by
    obtain ⟨x, hx⟩ := hfix
    exact ⟨x, by have := GTilde.inv_apply_apply g x; rwa [hx] at this⟩
  have hhi : GTilde.IsHyperbolic g⁻¹ := isHyperbolic_of_linkCover hp hgi (by
    rw [map_inv]; exact inv_ne_one.2 hh.toPSL_ne_one)
  -- the conjugacy `κ g κ⁻¹ = g⁻¹`, and `κ (δ² g) κ⁻¹ = δ² g⁻¹`, `κ (δ² g⁻¹) κ⁻¹ = δ² g`
  obtain ⟨κ, hκ⟩ := hh.exists_conj_inv hfix
  have hc : κ * GTilde.delta ^ (2 : ℤ) = GTilde.delta ^ (2 : ℤ) * κ :=
    (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ GTilde.delta_mem_center 2)) κ
  have hκi : κ * g⁻¹ * κ⁻¹ = g := by
    calc κ * g⁻¹ * κ⁻¹ = (κ * g * κ⁻¹)⁻¹ := by group
      _ = g := by rw [hκ, inv_inv]
  have hconj : ∀ g₁ g₂ : GTilde, κ * g₁ * κ⁻¹ = g₂ →
      GTilde.delta ^ (2 : ℤ) * g₂ = κ * (GTilde.delta ^ (2 : ℤ) * g₁) * κ⁻¹ := fun g₁ g₂ e => by
    rw [← e, ← mul_assoc κ, hc]; group
  -- the two quotients `ℝ/⟨δ² g⟩` and `ℝ/⟨δ² g⁻¹⟩`
  obtain ⟨L₁, _, cs₁, hcs₁, hL₁, E₁, D₁, h₁⟩ := exists_isLiftedDev_delta_sq_mul p θ hg hfix
  obtain ⟨L₂, _, cs₂, hcs₂, hL₂, E₂, D₂, h₂⟩ := exists_isLiftedDev_delta_sq_mul p θ hgi hfixi
  set C₁ : GammaLinkCircle L₁ := GammaLinkCircle.mk p cs₁ hcs₁ hL₁
  set C₂ : GammaLinkCircle L₂ := GammaLinkCircle.mk p cs₂ hcs₂ hL₂
  have hT₁ : ∀ s, E₁ s ∈ C₁.iPlusL → linkCover p θ (D₁ s) ∈ dsFutureDirs p ∪ dsPastDirs p :=
    fun s hs => Or.inl (h₁.mem_dsFutureDirs hp hs)
  have hT₂ : ∀ s, E₂ s ∈ C₂.iPlusL → linkCover p θ (D₂ s) ∈ dsFutureDirs p ∪ dsPastDirs p :=
    fun s hs => Or.inl (h₂.mem_dsFutureDirs hp hs)
  have h2 : (1 : ℤ) ≤ 2 := by norm_num
  rcases timelike_spacelike_dir hp hA1 hg hfix with ⟨hT, -⟩ | ⟨hT, -⟩
  · -- `g` moves the time-like directions up: `ℝ/⟨δ² g⟩` is positive, `ℝ/⟨δ² g⁻¹⟩` negative
    refine ⟨L₁, L₂, inferInstance, inferInstance, C₁, C₂, rfl, rfl,
      ⟨hp, θ, hθ, E₁, D₁, _, 2, g, h₁, h2, hfix, hh, rfl, fun s hs => (hT _ (hT₁ s hs)).le⟩,
      ⟨hp, θ, hθ, E₂, D₂, _, 2, g⁻¹, h₂, h2, hfixi, hhi, rfl, fun s hs => ?_⟩,
      θ, θ, E₁, E₂, D₁, D₂, _, _, h₁, h₂, κ, hconj g g⁻¹ hκ⟩
    have := GTilde.strictMono g⁻¹ (hT _ (hT₂ s hs))
    rw [GTilde.inv_apply_apply] at this
    exact this.le
  · -- `g` moves the time-like directions down: `ℝ/⟨δ² g⁻¹⟩` is positive, `ℝ/⟨δ² g⟩` negative
    refine ⟨L₂, L₁, inferInstance, inferInstance, C₂, C₁, rfl, rfl,
      ⟨hp, θ, hθ, E₂, D₂, _, 2, g⁻¹, h₂, h2, hfixi, hhi, rfl, fun s hs => ?_⟩,
      ⟨hp, θ, hθ, E₁, D₁, _, 2, g, h₁, h2, hfix, hh, rfl, fun s hs => (hT _ (hT₁ s hs)).le⟩,
      θ, θ, E₂, E₁, D₂, D₁, _, _, h₂, h₁, κ, hconj g⁻¹ g hκi⟩
    have := GTilde.strictMono g⁻¹ (hT _ (hT₂ s hs))
    rw [GTilde.inv_apply_apply] at this
    exact this.le

/-- **`bbsrem:previous_section_observed_only` (iii)** (l.930–931): positive and negative
hyperbolic `(Γ_p, ℓ(p))`-circles are not isomorphic. -/
theorem not_isIso_of_positive_of_negative {C : GammaLinkCircle L} {C' : GammaLinkCircle L'}
    (hC : C.IsSpacelikePositive) (hC' : C'.IsSpacelikeNegative) (φ : L ≃ₜ L') :
    ¬ C.IsIso C' φ := by
  intro hφ
  have hpos' := hφ.isSpacelikePositive hC
  obtain ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hneg⟩ := hC'
  have hpos := hpos'.forall hθ h hg hfg
  have hDl := h.isLocalHomeomorph
  letI := C'.rp1ChartedSpace θ
  haveI := C'.rp1_hasGroupoid θ
  have hW : IsLiftedDevPair E D f := h.isLiftedDevPair
  have hrange : range D = univ := hW.isComp.eq_univ
    (GTilde.apply_ne_of_degree_ne_zero (by omega) hg hfg)
  -- the open set `E⁻¹ i⁺(L')`, nonempty
  set U := {s | E s ∈ C'.iPlusL}
  have hU : U = (linkCover C'.pt θ ∘ D) ⁻¹' iPlus C'.pt := by
    rw [h.2.2.2.1.preimage_iPlus]; rfl
  have hUo : IsOpen U := by
    rw [hU]
    exact (isOpen_iPlus (fun hb => by
      have := HS.region_eq_of_mem hp; rw [HS.region_eq_of_mem hb] at this; cases this)).preimage
      ((isCoveringMap_linkCover C'.pt θ).continuous.comp h.2.1)
  have hUn : U.Nonempty := by
    obtain ⟨σ, hσ⟩ := (isConnected_dsFutureDirs hp).nonempty
    obtain ⟨t, ht⟩ := linkCover_surjective C'.pt θ σ
    obtain ⟨s, hs⟩ : t ∈ range D := hrange ▸ mem_univ t
    refine ⟨s, ?_⟩
    rw [hU, mem_preimage, Function.comp_apply, hs, ht, iPlus_of_deSitter hp]
    exact hσ
  have hg1 : g = 1 := GTilde.eq_of_eqOn (hDl.isOpenMap U hUo) (hUn.image D) (by
    rintro _ ⟨s, hs, rfl⟩
    exact (le_antisymm (hneg s hs) (hpos s hs)))
  exact hh.toPSL_ne_one (by rw [hg1, map_one])

/-- **The dichotomy** (l.906–915): a space-like `(Γ_p, ℓ(p))`-circle of degree `k ≥ 1` is positive
or negative, and not both. -/
theorem GammaLinkCircle.IsLiftedDev.spacelike_dichotomy {C : GammaLinkCircle L}
    {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde} (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : C.pt ∈ HS.piece 2 .deSitter) {k : ℤ} (hk : 1 ≤ k)
    {g : GTilde} (hg : ∃ x, g x = x) (hh : GTilde.IsHyperbolic g)
    (hfg : f = GTilde.delta ^ k * g) :
    (C.IsSpacelikePositive ∨ C.IsSpacelikeNegative) ∧
      ¬ (C.IsSpacelikePositive ∧ C.IsSpacelikeNegative) := by
  have hq : 0 < Causal.Flat.minkQ (C.pt : 𝕄) := hp
  obtain ⟨ρ, hρ⟩ := h.exists_linkCover_apply
  obtain ⟨m, hm⟩ := h.even_of_nonneg hq.le hg hfg
  have hgl : ∀ t, linkCover C.pt θ (g t) = ρ • linkCover C.pt θ t := fun t => by
    have e : f t = g t + k := by rw [hfg, GTilde.coe_mul_apply, GTilde.delta_zpow_apply]
    rw [← hρ, e, hm, show g t + ((m + m : ℤ) : ℝ) = g t + 2 * (m : ℝ) by push_cast; ring,
      linkCover_add_two_mul]
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    apply hh.toPSL_ne_one
    have hg1 : g = 1 := GTilde.ext' fun t => by
      have h1 : linkCover C.pt θ t = linkCover C.pt θ (g t) := by rw [hgl, one_smul]
      obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff C.pt θ).1 h1
      have ha := GTilde.apply_lt_delta_of_fixed hg t
      have hb := GTilde.sub_one_lt_apply_of_fixed hg t
      rw [GTilde.delta_apply] at ha
      rw [hn] at ha hb
      have : n = 0 := by
        have : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
        have : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
        omega
      rw [hn, this, GTilde.one_apply]; simp
    rw [hg1, map_one]
  have hfn := fixed_iff_null hp hρ1 hgl hg
  have hiff : ∀ s, E s ∈ C.iPlusL ↔ linkCover C.pt θ (D s) ∈ dsFutureDirs C.pt := fun s => by
    rw [← iPlus_of_deSitter hp]
    exact (Set.ext_iff.1 h.2.2.2.1.preimage_iPlus s).symm
  have hnot : ¬ (C.IsSpacelikePositive ∧ C.IsSpacelikeNegative) := fun ⟨a, b⟩ =>
    not_isIso_of_positive_of_negative a b (Homeomorph.refl L)
      ⟨rfl, by letI := C.atlas; exact isGXMorphism_id⟩
  rcases sign_const (p := C.pt) (θ := θ) (g := g) (isOpen_dsFutureDirs C.pt)
      (isConnected_dsFutureDirs hp).isPreconnected
      (fun t ht hgt => (minkQ_neg_of_timelike (Or.inl ht)).ne ((hfn t).1 hgt)) with hr | hl
  · exact ⟨Or.inl ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
      fun s hs => (hr _ ((hiff s).1 hs)).le⟩, hnot⟩
  · exact ⟨Or.inr ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
      fun s hs => (hl _ ((hiff s).1 hs)).le⟩, hnot⟩

/-- **`bbsrem:previous_section_observed_only`, "this remark does not extend"** (l.927–931), with
both halves: at every `p ∈ dS²` there are two space-like `(Γ_p, ℓ(p))`-circles of degree `2`, one
positive and one negative, whose underlying `ℝP¹`-circles are `ℝP¹`-isomorphic (the analogue of
(i) holds for them) and which are not `(Γ_p, ℓ(p))`-isomorphic. The identifications `θ`, `θ'` of the
`ℝP¹`-structures carry no `IsOrientedTangent` condition here (nor in `GX.exists_positive_negative`),
so the isomorphism clause is stated for some identifications, not for oriented ones; the proof's
witnesses are oriented, so the oriented form holds as well, but it is not stated. -/
theorem exists_rp1Iso_not_isIso {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L L' : Type) (_ : TopologicalSpace L) (_ : TopologicalSpace L') (C : GammaLinkCircle L)
      (C' : GammaLinkCircle L'), C.pt = p ∧ C'.pt = p ∧ C.IsSpacelikePositive ∧
      C'.IsSpacelikeNegative ∧ (∀ φ : L ≃ₜ L', ¬ C.IsIso C' φ) ∧
      ∃ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (θ' : TpHS C'.pt ≃ₗ[ℝ] ℂ),
        letI := C.rp1ChartedSpace θ
        letI := C'.rp1ChartedSpace θ'
        haveI := C.rp1_hasGroupoid θ
        haveI := C'.rp1_hasGroupoid θ'
        ∃ φ : L ≃ₜ L', IsRP1Iso φ := by
  obtain ⟨L, L', _, _, C, C', hC, hC', hpos, hneg, θ, θ', E, E', D, D', f, f', h, h', κ, hκ⟩ :=
    exists_positive_negative hp
  refine ⟨L, L', inferInstance, inferInstance, C, C', hC, hC', hpos, hneg,
    fun φ => not_isIso_of_positive_of_negative hpos hneg φ, θ, θ', ?_⟩
  letI := C.rp1ChartedSpace θ
  letI := C'.rp1ChartedSpace θ'
  haveI := C.rp1_hasGroupoid θ
  haveI := C'.rp1_hasGroupoid θ'
  exact (rp1Iso_iff_conj ⟨E, D, h.isLiftedDevPair⟩ ⟨E', D', h'.isLiftedDevPair⟩).2 ⟨κ, hκ⟩

end Remark

end GX
