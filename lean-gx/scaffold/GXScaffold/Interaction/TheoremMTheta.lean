import GX.BBS.PhotonCircles

/-!
# Theorem M's real-angle half: `Θ₋ = Θ₊` across a regular de Sitter annulus

Research target `T-3p1-theorem-m-theta` (`roadmap/roadmap.toml`): `papers/bbs/NOTES-3+1.md` N4
(M3) (`N4 l.344–349`) and BBS's remark after Lemma `surgery-key`, whose proof is the lemma's
(`papers/bbs/legacy/labeled/colI_v1.tex`, `l.` below, l.2958–3016). Labels below, **none marked**
(a research target; the master records results). 0 `sorry`; standard axioms only.

* `N4:M3-theta` — `NOTES-3+1.md:344–349` — **`Θ₋ = Θ₊` as real numbers, with no named
  hypothesis**: `GX.DSAnnulus.theta_eq_of_regular`, for every regular de Sitter annulus of every
  HS-surface (`(SO₀(1,2), HS²)`-manifold). It rests on
  `GX.DSAnnulus.exists_isDevelopment` (the developing map of `Ā` into `d̃S² ∪ R±` and its holonomy,
  from gx's developing theorem) and `GX.DSAnnulus.IsDevelopment.theta_eq`: the holonomy acts on
  `R₋` and `R₊` by **one** `h ∈ G̃` (`GX.exists_gTilde_of_holonomy`, from the equivariance of
  `ι_ε`), so `Θ± = angle h^{±1}`, and real angles are `≥ 0`. « Degree included »: for `Θ > 0`
  the lifted holonomies coincide (`GX.DSAnnulus.hasLiftedHolonomy_iff_of_pos`); non-elliptic
  `C±` have the same degree (`GX.DSAnnulus.degree_eq_of_regular`). Under the named hypothesis,
  for every `Θ`: `GX.DSAnnulus.theta_eq`,
  `GX.DSAnnulus.hasLiftedHolonomy_iff`, `GX.DSAnnulus.exists_theta`.
* `bbsrem:causally_regular_hs_sphere_containing` — `colI_v1.tex:3013` — **as stated, under the
  named hypothesis** of l.2991–3004 (`GX.DSAnnulus.IsIotaPrime`: `ι'_L` and the diagram):
  `GX.DSAnnulus.IsIotaPrime.exists_projIso`, `ι'_L : C̃₋ → C̃₊` induces a projective isomorphism
  `ῑ : C₋ ≃ₜ C₊`; `GX.DSAnnulus.remark_projIso`. **Without it when `Θ₋ > 0`** (e.g. `C₋`
  elliptic): `GX.DSAnnulus.remark_projIso_of_pos`, through
  `GX.DSAnnulus.IsDevelopment.exists_projIso_of_pos`: the existence of `ῑ` only; that `ι'_L`
  induces it is stated under the hypothesis alone. The case `Θ = 0` without it is open here
  (SCOPE (d)).
* The model (l.2979–2990): `GX.DSTilde` (`d̃S² ∪ R±`, the strip `ℝ × [−1, 1]`, simply connected),
  `GX.dsCover` (onto `dS² ∪ ∂ℍ²±`, through the leaf chart `GX.iotaChart`), `GX.iotaTilde` (`ι̃_L`),
  `GX.dsCover_rMinus`, `GX.dsCover_rPlus` (`R± ≅ ℝP̃¹`), `GX.dsCover_iotaTilde` (`π ∘ ι̃ = ι ∘ π`),
  `GX.iotaTilde_rMinus` (`ι̃ : R₋ → R₊` is the identity in `ℝP̃¹`-coordinates: projective).
* General: `GX.hasRealAngle_iff_of_isGXMorphism` (projectively isomorphic `ℝP¹`-circles have the
  same real angle), `GX.exists_projIso_of_lift`, `GX.hasLiftedHolonomy_or_inv`,
  `GX.surjective_of_equivariant` (l.3006: for a fixed-point-free holonomy the developing map is
  onto `ℝP̃¹`), `GX.GTilde.angle_inv`, `GX.UniversalCover.exists_deck_apply_eq`.
* Non-vacuity: `GX.modelAnnulus` (`dS² ∪ ∂ℍ²±` in `HS²`) satisfies every hypothesis, the named
  one included (`GX.modelAnnulus_isIotaPrime`, `GX.modelAnnulus_theta_eq`), with
  `Θ₋ = Θ₊ = 2π` (`GX.modelAnnulus_hasRealAngle`).

> **(M3) Conservation.** Θ₋ = Θ₊, **as real numbers**, and hol(C₋) = hol(C₊). […] At the level
> of the **real** angle, it is BBS's remark after Lemma `surgery-key` (l.3013). There, the left
> isotropic foliation of A induces a projective isomorphism ῑ : C₋ → C₊, so the two
> ℝP¹-circles, degree included, are isomorphic. (N4 l.344–349)
>
> If $\Sigma$ is a causally regular HS-sphere containing only elliptic singularities, the map
> $\iota'_L:\tilde C_-\rightarrow\tilde C_+$ induces a projective isomorphism
> $\bar\iota:C_-\rightarrow C_+$. (l.3013–3016)
>
> Since $D$ does not contain singularities, we have an analogous proper submersion
> $\iota'_L:\tilde D\cup\tilde C_-\cup\tilde C_+\rightarrow\tilde C_+$ […] By the naturality
> of the construction, the following diagram commutes […] The map $d|_{\tilde C_+}$ is the
> developing map for the projective structure of $C_+$. (l.2991–3006)

## Hypothesis checklist

| BBS / N4 | here |
|---|---|
| `Σ` a causally regular HS-sphere (l.3014; N4 Setting) | ⚠ weakened: any `(SO₀(1,2), HS²)`-manifold `M` (`Reg Σ`) carrying N4's annulus (`GX.DSAnnulus`, SCOPE (a)) |
| only elliptic singularities (l.3014) | ⚠ weakened: not used |
| `A` regular, joining `C₋ = ∂D₋` to `C₊ = ∂D₊` (N4 l.326–328) | ⚠ weakened (Lean assumes less): the discs `D±` and `C± = ∂D±` do not enter; `M` non-singular; `C₋` past and `C₊` future photon circles; `Ā` covered by the strip, `R±` by periodic coverings of `C±` |
| `A` de Sitter | ✓ carried where used: the points of `Ā` are de Sitter points or photons (`hreg`) |
| the ℝP¹-structures of `C±` (l.1903–1905) | ⚠ read: from the hyperbolic side through the HS-charts (`GX.IsPhotonCircle.rp1ChartedSpace`, OQ-117 (c)) |
| « projective isomorphism » (l.3015–3016) | ✓ a homeomorphism that is a `(PSL(2,ℝ), ℝP¹)`-morphism, and its inverse too |
| the developing map `d` (l.2971–2974), on `C̃±` too (l.3000) | ✓ built (`exists_isDevelopment`, from gx's developing theorem; `M` is locally path-connected and semilocally simply connected because it is charted on `HS²`, `GX.semilocallySimplyConnected_of_chartedSpace_hs2`) |
| `ι'_L` and the diagram (l.2991–3004) | ⚠ named hypothesis `IsIotaPrime`, for « `ι'_L` induces `ῑ` » (every `Θ`) and for the existence of `ῑ` when `Θ = 0`; the existence of `ῑ` when `Θ₋ > 0`, and `Θ₋ = Θ₊`, need none |
| « left » (l.2983) | ⚠ weakened: every statement holds for both foliations `ε = ±1` (OQ-117 (d) immaterial) |
| the normalisation of the angle (OQ-113 (a)) | ⚠ weakened: `Θ₋ = Θ₊` holds in every normalisation (SCOPE (e)) |

## SCOPE (disclosed)

* **(a) N4's data** is `GX.DSAnnulus`: photon circles `C₋` (past) and `C₊` (future) in `M`, a
  continuous `cover : ℝ × [−1, 1] → M` of period `1` in `s`, restricting on `R±` to periodic
  coverings `E± : ℝ → C±`. That `cover` is a covering of an embedded annulus is not required.
* **(b)** `d̃S² ∪ R±` is the strip, mapped onto `dS² ∪ ∂ℍ²±` by `GX.dsCover`; it is simply
  connected and locally path-connected; that `dsCover` is a covering map is not stated (lifts are
  built through the `∂ℍ²₊`-coordinate). `d` is a lift of gx's developing map of `M̃` through it.
* **(c) The named hypothesis** `GX.DSAnnulus.IsIotaPrime`: a continuous `ι'`, lifting a map
  `Ā → C₊`, with `d ∘ ι' = ι̃_L ∘ d` and `d` a developing map (l.2991–3004). Properness and
  submersion are not used. It holds in the model (`GX.modelAnnulus_isIotaPrime`).
* **(d) Not formalized**: the construction of `ι'_L` from the left foliation of `Ā`; the remark
  for `Θ = 0` without the named hypothesis (there `h` has fixed points, `d|C̃₊` need not be onto
  `ℝP̃¹`, and the developed images of `C̃±` must be matched; the session's sketch [r], not
  formalized: they are components of `ℝ ∖ Fix h`, matched by a power of `δ`, or by a lift of a
  quarter turn when the orientations differ); Lemma `surgery-key` itself (`d` proper, the
  embedding in `𝒫_θ`); (M4).
* **(e) Normalisation.** `Θ±` are `GX.GTilde.angle = 2π τ`. The proof shows the lifted
  holonomies are `h^{±1}` for one `h`, with `h⁻¹` only when `τ(h) = 0`; so `τ₋ = τ₊`, every
  rescaling `c τ` of the angle (OQ-113 (a)) agrees on `C±`, and for `Θ > 0` the lifted
  holonomies themselves coincide. OQ-113 bears on the value of `Θ`, not on `Θ₋ = Θ₊`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.BBS.PhotonCircles`, `GX.BBS.RP1Circles`, `GX.Structure.Developing`,
`GX.Topology.UniversalCover`; no `Causal.*` import (DEC-33).
-/

noncomputable section

open Set Filter Topology Real
open scoped MatrixGroups

namespace GX

set_option linter.unusedSectionVars false

/-! ### Projective isomorphisms of `ℝP¹`-circles preserve the lifted holonomy -/

section ProjIso

variable {L₁ L₂ : Type*} [TopologicalSpace L₁] [TopologicalSpace L₂] [ChartedSpace RP1 L₁]
  [ChartedSpace RP1 L₂]

/-- The inverse of a projective homeomorphism is projective. -/
theorem isGXMorphism_homeomorph_symm {φ : L₁ ≃ₜ L₂} (hφ : IsGXMorphism PSL(2, ℝ) RP1 φ) :
    IsGXMorphism PSL(2, ℝ) RP1 φ.symm := by
  refine ⟨φ.symm.continuous, fun y => ?_⟩
  obtain ⟨g, hg⟩ := hφ.exists_smul_eq (φ.symm y)
  refine ⟨g⁻¹, ?_⟩
  filter_upwards [φ.symm.continuous.continuousAt.eventually hg] with y' hy'
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at hy'
  rw [hy', inv_smul_smul]

/-- **A projective isomorphism transports the lifted holonomy**: if `φ : L₁ ≃ₜ L₂` is a
`(PSL(2,ℝ), ℝP¹)`-morphism, every lifted holonomy of `L₁` is one of `L₂`. -/
theorem HasLiftedHolonomy.of_isGXMorphism {φ : L₁ ≃ₜ L₂} (hφ : IsGXMorphism PSL(2, ℝ) RP1 φ)
    {f : GTilde} (hf : HasLiftedHolonomy L₁ f) : HasLiftedHolonomy L₂ f := by
  obtain ⟨E, D, hE, hDc, hDm, hDev, hDf⟩ := hf
  refine ⟨φ ∘ E, D, ⟨hE.isCoveringMap.homeomorph_comp φ, φ.surjective.comp hE.surjective,
    fun s => by simp only [Function.comp_apply, hE.add_one],
    fun s t h => hE.fiber s t (φ.injective h)⟩, hDc, hDm, fun s => ?_, hDf⟩
  obtain ⟨g, hg⟩ := hDev s
  obtain ⟨h, hh⟩ := hφ.exists_smul_eq (E s)
  refine ⟨g * h⁻¹, ?_⟩
  filter_upwards [hg, hE.isCoveringMap.continuous.continuousAt.eventually hh] with s' h1 h2
  simp only [Function.comp_apply] at h1 h2 ⊢
  rw [h1, h2, mul_smul, inv_smul_smul]

theorem hasLiftedHolonomy_iff_of_isGXMorphism {φ : L₁ ≃ₜ L₂}
    (hφ : IsGXMorphism PSL(2, ℝ) RP1 φ) (f : GTilde) :
    HasLiftedHolonomy L₁ f ↔ HasLiftedHolonomy L₂ f :=
  ⟨HasLiftedHolonomy.of_isGXMorphism hφ,
    HasLiftedHolonomy.of_isGXMorphism (isGXMorphism_homeomorph_symm hφ)⟩

/-- **Projectively isomorphic `ℝP¹`-circles have the same real angle.** -/
theorem hasRealAngle_iff_of_isGXMorphism {φ : L₁ ≃ₜ L₂} (hφ : IsGXMorphism PSL(2, ℝ) RP1 φ)
    (θ : ℝ) : HasRealAngle L₁ θ ↔ HasRealAngle L₂ θ :=
  ⟨fun ⟨f, hf, h⟩ => ⟨f, (hasLiftedHolonomy_iff_of_isGXMorphism hφ f).1 hf, h⟩,
    fun ⟨f, hf, h⟩ => ⟨f, (hasLiftedHolonomy_iff_of_isGXMorphism hφ f).2 hf, h⟩⟩

variable [HasGroupoid L₁ (gxGroupoid PSL(2, ℝ) RP1)] [HasGroupoid L₂ (gxGroupoid PSL(2, ℝ) RP1)]

/-- **A map of universal covers intertwining developing maps descends to a projective
isomorphism** (the last step of l.3013–3016). -/
theorem exists_projIso_of_lift (hL₁ : IsCircle L₁) (hL₂ : IsCircle L₂) {E₁ : ℝ → L₁}
    {E₂ : ℝ → L₂} (hE₁ : IsPeriodicCover E₁) (hE₂ : IsPeriodicCover E₂) {D₁ D₂ : ℝ → ℝ}
    (hD₁c : Continuous D₁) (hD₁ : IsDevAlong E₁ (RP1.proj ∘ D₁))
    (hD₂ : IsDevAlong E₂ (RP1.proj ∘ D₂)) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ1 : ∀ s, φ (s + 1) = φ s + 1) (hφD : ∀ s, D₂ (φ s) = D₁ s) :
    ∃ ι : L₁ ≃ₜ L₂, (∀ s, ι (E₁ s) = E₂ (φ s)) ∧ IsGXMorphism PSL(2, ℝ) RP1 ι ∧
      IsGXMorphism PSL(2, ℝ) RP1 ι.symm := by
  have hE₁l := hE₁.isCoveringMap.isLocalHomeomorph
  have hD₁i : Function.Injective D₁ := injective_of_isOpenMap_real hD₁c
    (hD₁.isLocalHomeomorph_lift hE₁l hD₁c).isOpenMap
  have hφi : Function.Injective φ := fun s s' h => hD₁i (by rw [← hφD, ← hφD, h])
  have hφm : StrictMono φ := by
    rcases hφc.strictMono_of_inj hφi with h | h
    · exact h
    · exfalso
      have := h (lt_add_one (0 : ℝ))
      rw [hφ1] at this
      linarith
  let F : CircleDeg1Lift := ⟨⟨φ, hφm.monotone⟩, hφ1⟩
  have hφs : Function.Surjective φ := F.continuous_iff_surjective.1 hφc
  have hφn : ∀ (s : ℝ) (n : ℤ), φ (s + n) = φ s + n := fun s n => F.map_add_int s n
  -- the induced map `ῑ`
  let ιf : L₁ → L₂ := fun x => E₂ (φ (Function.surjInv hE₁.surjective x))
  have hι : ∀ s, ιf (E₁ s) = E₂ (φ s) := by
    intro s
    have h0 : E₁ (Function.surjInv hE₁.surjective (E₁ s)) = E₁ s := Function.surjInv_eq _ _
    obtain ⟨n, hn⟩ := hE₁.fiber _ _ h0
    show E₂ (φ (Function.surjInv hE₁.surjective (E₁ s))) = E₂ (φ s)
    conv_rhs => rw [hn]
    rw [hφn, hE₂.add_int]
  have hιc : Continuous ιf := by
    rw [(hE₁.isCoveringMap.isQuotientMap hE₁.surjective).continuous_iff]
    have : ιf ∘ E₁ = E₂ ∘ φ := funext hι
    rw [this]
    exact hE₂.isCoveringMap.continuous.comp hφc
  have hιi : Function.Injective ιf := by
    intro x x' h
    obtain ⟨s, rfl⟩ := hE₁.surjective x
    obtain ⟨s', rfl⟩ := hE₁.surjective x'
    rw [hι, hι] at h
    obtain ⟨n, hn⟩ := hE₂.fiber _ _ h
    rw [← hφn] at hn
    rw [hφi hn, hE₁.add_int]
  have hιs : Function.Surjective ιf := by
    intro y
    obtain ⟨u, rfl⟩ := hE₂.surjective y
    obtain ⟨s, rfl⟩ := hφs u
    exact ⟨E₁ s, hι s⟩
  obtain ⟨e₁⟩ := hL₁
  obtain ⟨e₂⟩ := hL₂
  haveI : CompactSpace L₁ := e₁.symm.compactSpace
  haveI : T2Space L₂ := e₂.isEmbedding.t2Space
  let ι : L₁ ≃ₜ L₂ := hιc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ιf ⟨hιi, hιs⟩)
  have hιapp : ∀ x, ι x = ιf x := fun _ => rfl
  have hGX : IsGXMorphism PSL(2, ℝ) RP1 ι := by
    refine ⟨ι.continuous, fun x => ?_⟩
    obtain ⟨s, rfl⟩ := hE₁.surjective x
    obtain ⟨g₁, hg₁⟩ := hD₁ s
    obtain ⟨g₂, hg₂⟩ := hD₂ (φ s)
    refine ⟨g₂⁻¹ * g₁, ?_⟩
    have hev : ∀ᶠ s' in 𝓝 s, chartAt RP1 (ι (E₁ s)) (ι (E₁ s')) =
        (g₂⁻¹ * g₁) • chartAt RP1 (E₁ s) (E₁ s') := by
      filter_upwards [hg₁, hφc.continuousAt.eventually hg₂] with s' h1 h2
      simp only [Function.comp_apply, hφD] at h1 h2
      rw [hιapp, hιapp, hι, hι, mul_smul, ← h1, h2, inv_smul_smul]
    exact Filter.mem_of_superset (hE₁.isCoveringMap.isOpenMap.image_mem_nhds hev)
      (by rintro _ ⟨s', hs', rfl⟩; exact hs')
  exact ⟨ι, fun s => hι s, hGX, isGXMorphism_homeomorph_symm hGX⟩

/-- **An equivariant lift of a developing map gives the lifted holonomy, up to orientation**: if
`D` lifts a developing map along a periodic covering and `D (s + 1) = h (D s)`, then `h` (if `D`
increases) or `h⁻¹` (if `D` decreases) is a lifted holonomy of `L₁`. -/
theorem hasLiftedHolonomy_or_inv {E : ℝ → L₁} (hE : IsPeriodicCover E) {D : ℝ → ℝ}
    (hDc : Continuous D) (hD : IsDevAlong E (RP1.proj ∘ D)) {h : GTilde}
    (hDh : ∀ s, D (s + 1) = h (D s)) :
    HasLiftedHolonomy L₁ h ∨ HasLiftedHolonomy L₁ h⁻¹ := by
  have hEl := hE.isCoveringMap.isLocalHomeomorph
  have hinj : Function.Injective D := injective_of_isOpenMap_real hDc
    (hD.isLocalHomeomorph_lift hEl hDc).isOpenMap
  rcases hDc.strictMono_of_inj hinj with hmono | hanti
  · exact Or.inl ⟨E, D, hE, hDc, hmono, hD, hDh⟩
  · refine Or.inr ⟨E ∘ Neg.neg, D ∘ Neg.neg, ⟨hE.isCoveringMap.comp_homeomorph (Homeomorph.neg ℝ),
      hE.surjective.comp neg_surjective, fun s => ?_, fun s t hst => ?_⟩,
      hDc.comp continuous_neg, hanti.comp (fun _ _ h => neg_lt_neg h),
      hD.comp_continuous continuous_neg, fun s => ?_⟩
    · simp only [Function.comp_apply]
      rw [← hE.add_one (-(s + 1)), show -(s + 1) + 1 = -s by ring]
    · obtain ⟨m, hm⟩ := hE.fiber _ _ hst
      exact ⟨-m, by push_cast; linarith⟩
    · simp only [Function.comp_apply]
      rw [show -s = -(s + 1) + 1 by ring, hDh, GTilde.inv_apply_apply]

/-- **An equivariant lift for a fixed-point-free `g` is onto**: if `D` lifts a developing map
along a periodic covering, `D (s + 1) = g (D s)` and `g` has no fixed point in `ℝP̃¹`, then
`D : ℝ → ℝP̃¹` is surjective (the developing map of an `ℝP¹`-circle without fixed point of its
holonomy is onto `ℝP̃¹`). -/
theorem surjective_of_equivariant {E : ℝ → L₁} (hE : IsPeriodicCover E) {D : ℝ → ℝ}
    (hDc : Continuous D) (hD : IsDevAlong E (RP1.proj ∘ D)) {g : GTilde}
    (hDg : ∀ s, D (s + 1) = g (D s)) (hfix : ∀ x, g x ≠ x) : Function.Surjective D := by
  have hEl := hE.isCoveringMap.isLocalHomeomorph
  have hinj : Function.Injective D := injective_of_isOpenMap_real hDc
    (hD.isLocalHomeomorph_lift hEl hDc).isOpenMap
  -- the iterates
  have hiter : ∀ (n : ℤ) (s : ℝ), D (s + n) = (g ^ n) (D s) := by
    intro n
    induction n using Int.induction_on with
    | zero => intro s; simp only [Int.cast_zero, add_zero, zpow_zero]; rfl
    | succ m ih =>
      intro s
      rw [zpow_add_one, GTilde.coe_mul_apply, ← hDg, ← ih]
      congr 1; push_cast; ring
    | pred m ih =>
      intro s
      have h1 : (g⁻¹ : GTilde) (D s) = D (s - 1) := by
        rw [show D s = g (D (s - 1)) by rw [← hDg, sub_add_cancel], GTilde.inv_apply_apply]
      rw [zpow_sub_one, GTilde.coe_mul_apply, h1, ← ih]
      congr 1; push_cast; ring
  -- a direction in which some power moves every point by at least `|n| c`
  obtain ⟨f, hf, hfr⟩ : ∃ f : GTilde, (f = g ∨ f = g⁻¹) ∧ ∀ x, x < f x := by
    rcases lt_or_gt_of_ne (hfix 0) with h0 | h0
    · refine ⟨g⁻¹, Or.inr rfl, GTilde.lt_apply_of_forall_ne (fun x hx => hfix x ?_)
        (x₀ := g 0) (by rw [GTilde.inv_apply_apply]; exact h0)⟩
      have := GTilde.apply_inv_apply g x
      rwa [hx] at this
    · exact ⟨g, Or.inl rfl, GTilde.lt_apply_of_forall_ne hfix h0⟩
  obtain ⟨c, hc, hfc⟩ := GTilde.exists_add_le_of_forall_lt hfr
  have hbound : ∀ (n : ℤ) (x : ℝ), ((|n| : ℤ) : ℝ) * c ≤ |(g ^ n) x - x| := by
    intro n x
    rcases hf with rfl | rfl
    · exact GTilde.abs_zpow_apply_sub_ge hfc n x
    · have := GTilde.abs_zpow_apply_sub_ge hfc (-n) x
      rwa [inv_zpow', neg_neg, abs_neg] at this
  -- `D` is unbounded on both sides
  intro y
  obtain ⟨N, hN⟩ := exists_nat_gt (|y - D 0| / c)
  have hNc : |y - D 0| < N * c := by rwa [div_lt_iff₀ hc] at hN
  have hN0 : (0 : ℝ) < N := by
    have := abs_nonneg (y - D 0)
    nlinarith
  have hp := hbound N (D 0)
  have hm := hbound (-N) (D 0)
  rw [← hiter, zero_add] at hp hm
  push_cast at hp hm
  rw [abs_neg, abs_of_pos hN0] at hm
  rw [abs_of_pos hN0] at hp
  have hmem : y ∈ uIcc (D (-(N : ℝ))) (D N) := by
    rw [Set.mem_uIcc]
    rcases hDc.strictMono_of_inj hinj with hmono | hanti
    · have h1 : D 0 < D N := hmono hN0
      have h2 : D (-(N : ℝ)) < D 0 := hmono (by linarith)
      rw [abs_of_pos (by linarith : 0 < D N - D 0)] at hp
      rw [abs_of_neg (by linarith : D (-(N : ℝ)) - D 0 < 0)] at hm
      have := le_abs_self (y - D 0)
      have := neg_abs_le (y - D 0)
      exact Or.inl ⟨by linarith, by linarith⟩
    · have h1 : D N < D 0 := hanti hN0
      have h2 : D 0 < D (-(N : ℝ)) := hanti (by linarith)
      rw [abs_of_neg (by linarith : D N - D 0 < 0)] at hp
      rw [abs_of_pos (by linarith : 0 < D (-(N : ℝ)) - D 0)] at hm
      have := le_abs_self (y - D 0)
      have := neg_abs_le (y - D 0)
      exact Or.inr ⟨by linarith, by linarith⟩
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hDc.continuousOn hmem
  exact ⟨s, hs⟩

end ProjIso

/-- **The real angle changes sign under inversion**: `angle f⁻¹ = −angle f`. -/
theorem GTilde.angle_inv (f : GTilde) : GTilde.angle f⁻¹ = -GTilde.angle f := by
  rw [GTilde.angle, GTilde.angle, ← mul_neg, ← CircleDeg1Lift.translationNumber_units_inv]
  rfl

/-! ### The model: `d̃S² ∪ R₋ ∪ R₊` (l.2979–2990) -/

/-- **`d̃S² ∪ R₋ ∪ R₊`** (l.2979–2981): the strip `ℝ × [−1, 1]`, mapped onto `dS² ∪ ∂ℍ²±` by
`GX.dsCover`; `R₋ = ℝ × {−1}`, `R₊ = ℝ × {1}`. -/
abbrev DSTilde : Type := ℝ × Icc (-1 : ℝ) 1

/-- The point `s` of `R₋`. -/
def rMinus (s : ℝ) : DSTilde := (s, ⟨-1, le_rfl, by norm_num⟩)

/-- The point `s` of `R₊`. -/
def rPlus (s : ℝ) : DSTilde := (s, ⟨1, by norm_num, le_rfl⟩)

theorem continuous_rMinus : Continuous rMinus := continuous_id.prodMk continuous_const

theorem continuous_rPlus : Continuous rPlus := continuous_id.prodMk continuous_const

/-- **The projection `π : d̃S² ∪ R± → dS² ∪ ∂ℍ²±`**: `(s, t)` is the point at height `t` of the
`ε`-leaf ending at `[proj s] ∈ ∂ℍ²₊` (through the leaf chart `GX.iotaChart`). -/
def dsCover (ε : ℝ) (hε : ε ^ 2 = 1) (z : DSTilde) : HS.closedDS :=
  (iotaChart ε hε).symm (rp1ToBdPlus (RP1.proj z.1), z.2)

/-- **`ι̃_ε : d̃S² ∪ R± → R₊`**, the lift of `ι_ε` (l.2987–2989): the projection along the
leaves `{s} × [−1, 1]`. -/
def iotaTilde (z : DSTilde) : DSTilde := rPlus z.1

section Model

variable {ε : ℝ} (hε : ε ^ 2 = 1)

theorem continuous_dsCover : Continuous (dsCover ε hε) :=
  (iotaChart ε hε).symm.continuous.comp
    ((rp1ToBdPlus.continuous.comp (RP1.continuous_proj.comp continuous_fst)).prodMk continuous_snd)

/-- The time coordinate of `dsCover z` is the height `z.2`. -/
theorem fst_dsCover (z : DSTilde) :
    (((dsCover ε hε z : HS.closedDS) : HS 2) : Causal.Minkowski 2).1 = z.2 := rfl

theorem dsCover_add_int (s : ℝ) (n : ℤ) (t : Icc (-1 : ℝ) 1) :
    dsCover ε hε (s + n, t) = dsCover ε hε (s, t) := by
  show (iotaChart ε hε).symm (rp1ToBdPlus (RP1.proj (s + n)), t) =
    (iotaChart ε hε).symm (rp1ToBdPlus (RP1.proj s), t)
  rw [RP1.proj_add_int]

theorem dsCover_add_one (s : ℝ) (t : Icc (-1 : ℝ) 1) :
    dsCover ε hε (s + 1, t) = dsCover ε hε (s, t) := by
  have := dsCover_add_int hε s 1 t
  rwa [Int.cast_one] at this

/-- `ι_ε ∘ π = π ∘ ι̃_ε` read in `∂ℍ²₊`: the leaf through `(s, t)` ends at `[proj s]`. -/
theorem iota_dsCover (z : DSTilde) : iota ε hε (dsCover ε hε z) = rp1ToBdPlus (RP1.proj z.1) := by
  rw [← iotaChart_apply_fst, dsCover, Homeomorph.apply_symm_apply]

/-- **`R₊ ≅ ℝP̃¹`** (l.2980–2981): `π (s, 1) = [proj s] ∈ ∂ℍ²₊`. -/
theorem dsCover_rPlus (s : ℝ) :
    (dsCover ε hε (rPlus s) : HS 2) = rp1ToBdPlus (RP1.proj s) :=
  leafPtHS_one hε _

/-- **`R₋ ≅ ℝP̃¹`** (l.2980–2981): `π (s, −1) = −[proj s] ∈ ∂ℍ²₋`. -/
theorem dsCover_rMinus (s : ℝ) :
    (dsCover ε hε (rMinus s) : HS 2) = rp1ToBdMinus (RP1.proj s) := by
  rw [coe_rp1ToBdMinus]
  exact leafPtHS_neg_one hε _

/-- **The diagram of the model** (l.2987–2989): `π ∘ ι̃_ε = ι_ε ∘ π`. -/
theorem dsCover_iotaTilde (z : DSTilde) :
    (dsCover ε hε (iotaTilde z) : HS 2) = iota ε hε (dsCover ε hε z) := by
  rw [iotaTilde, dsCover_rPlus, iota_dsCover]

/-- **`ι̃_ε : R₋ → R₊` is projective**: it is the identity in the `ℝP̃¹`-coordinates of
`GX.dsCover_rMinus`, `GX.dsCover_rPlus`. -/
theorem iotaTilde_rMinus (s : ℝ) : iotaTilde (rMinus s) = rPlus s := rfl

theorem iotaTilde_rPlus (s : ℝ) : iotaTilde (rPlus s) = rPlus s := rfl

/-- The points of the strip over `∂ℍ²₋` are those of `R₋`. -/
theorem eq_rMinus_of_mem_bdMinus {z : DSTilde}
    (hz : (dsCover ε hε z : HS 2) ∈ HS.piece 2 .bdMinus) : z = rMinus z.1 := by
  have h := (HS.mem_bdMinus_iff.1 hz).1
  rw [fst_dsCover] at h
  exact Prod.ext rfl (Subtype.ext h)

/-- The points of the strip over `∂ℍ²₊` are those of `R₊`. -/
theorem eq_rPlus_of_mem_bdPlus {z : DSTilde}
    (hz : (dsCover ε hε z : HS 2) ∈ HS.piece 2 .bdPlus) : z = rPlus z.1 := by
  have h := (HS.mem_bdPlus_iff.1 hz).1
  rw [fst_dsCover] at h
  exact Prod.ext rfl (Subtype.ext h)

end Model

/-- `d̃S² ∪ R±` is contractible. -/
instance contractibleSpace_dsTilde : ContractibleSpace DSTilde := by
  haveI : ContractibleSpace (Icc (-1 : ℝ) 1) :=
    (convex_Icc (-1 : ℝ) 1).contractibleSpace (nonempty_Icc.2 (by norm_num))
  infer_instance

/-- **`d̃S² ∪ R±` is simply connected.** -/
instance simplyConnectedSpace_dsTilde : SimplyConnectedSpace DSTilde := inferInstance

/-- `d̃S² ∪ R±` is locally path-connected (homeomorphic to a convex subset of `ℝ²`). -/
instance locPathConnectedSpace_dsTilde : LocPathConnectedSpace DSTilde := by
  have hS : Convex ℝ (univ ×ˢ Icc (-1 : ℝ) 1 : Set (ℝ × ℝ)) := convex_univ.prod (convex_Icc _ _)
  haveI := Convex.locPathConnectedSpace (ℝ × ℝ) hS
  let e : DSTilde ≃ₜ (univ ×ˢ Icc (-1 : ℝ) 1 : Set (ℝ × ℝ)) :=
    ((Homeomorph.Set.univ ℝ).symm.prodCongr (Homeomorph.refl _)).trans
      (Homeomorph.Set.prod _ _).symm
  exact e.isOpenEmbedding.locPathConnectedSpace

/-- The deck group of the universal cover is transitive on the fibres. -/
theorem UniversalCover.exists_deck_apply_eq {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    {c c' : UniversalCover Y y₀} (h : c.pt = c'.pt) :
    ∃ γ : Deck (UniversalCover.proj Y y₀), γ.1 c = c' := by
  obtain ⟨y, q⟩ := c
  obtain ⟨y', q'⟩ := c'
  obtain rfl : y = y' := h
  refine ⟨⟨UniversalCover.leftMulHomeomorph (q'.trans q.symm), rfl⟩, ?_⟩
  show UniversalCover.leftMul (q'.trans q.symm) ⟨y, q⟩ = ⟨y, q'⟩
  simp only [UniversalCover.leftMul, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]

/-! ### The photon structures read through `∂ℍ²±` -/

section PhotonCharts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (HS 2) M]
  [HasGroupoid M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2))]

theorem eq_false_of_bdPiece_eq {b : Bool} (h : bdPiece b = .bdMinus) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem eq_true_of_bdPiece_eq {b : Bool} (h : bdPiece b = .bdPlus) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

theorem coe_rp1ToBd_of_eq_false {b : Bool} (hb : b = false) (w : RP1) :
    (rp1ToBd b w : HS 2) = rp1ToBdMinus w := by
  subst hb; rfl

theorem coe_rp1ToBd_of_eq_true {b : Bool} (hb : b = true) (w : RP1) :
    (rp1ToBd b w : HS 2) = rp1ToBdPlus w := by
  subst hb; rfl

/-- **The chart of a circle of past photons**, read through `∂ℍ²₋ ≅ ℝP¹`, is the HS-chart. -/
theorem IsPhotonCircle.coe_rp1ToBdMinus_chartAt {C : Set M} (hC : IsPhotonCircle C)
    (hpast : ∀ x ∈ C, hsRegion x = .bdMinus) (x y : C)
    (hy : (y : M) ∈ (chartAt (HS 2) (x : M)).source) :
    (rp1ToBdMinus (@chartAt RP1 _ C _ hC.rp1ChartedSpace x y) : HS 2) =
      chartAt (HS 2) (x : M) y := by
  have h1 := rp1ToBd_photonChartOf hC.exists_bdPiece.choose C hC.exists_bdPiece.choose_spec.1
    hC.exists_bdPiece.choose_spec.2
    ((gxGroupoid (Causal.Flat.lorentz 2) (HS 2)).chart_mem_maximalAtlas (x : M)) x hy
  have hb : hC.exists_bdPiece.choose = false := eq_false_of_bdPiece_eq
    ((hC.exists_bdPiece.choose_spec.1 x x.2).symm.trans (hpast x x.2))
  rw [coe_rp1ToBd_of_eq_false hb] at h1
  exact h1

/-- **The chart of a circle of future photons**, read through `∂ℍ²₊ ≅ ℝP¹`, is the HS-chart. -/
theorem IsPhotonCircle.coe_rp1ToBdPlus_chartAt {C : Set M} (hC : IsPhotonCircle C)
    (hfut : ∀ x ∈ C, hsRegion x = .bdPlus) (x y : C)
    (hy : (y : M) ∈ (chartAt (HS 2) (x : M)).source) :
    (rp1ToBdPlus (@chartAt RP1 _ C _ hC.rp1ChartedSpace x y) : HS 2) =
      chartAt (HS 2) (x : M) y := by
  have h1 := rp1ToBd_photonChartOf hC.exists_bdPiece.choose C hC.exists_bdPiece.choose_spec.1
    hC.exists_bdPiece.choose_spec.2
    ((gxGroupoid (Causal.Flat.lorentz 2) (HS 2)).chart_mem_maximalAtlas (x : M)) x hy
  have hb : hC.exists_bdPiece.choose = true := eq_true_of_bdPiece_eq
    ((hC.exists_bdPiece.choose_spec.1 x x.2).symm.trans (hfut x x.2))
  rw [coe_rp1ToBd_of_eq_true hb] at h1
  exact h1

end PhotonCharts

/-- **`ι̃_ε` is `G̃`-equivariant, so the holonomy acts on `R₋` and `R₊` by one element of `G̃`**:
if a continuous `dev` of the strip satisfies `π (dev (s + 1, t)) = B • π (dev (s, t))` for some
`B ∈ SO₀(1,2)`, there is `h ∈ G̃` with `(dev (s + 1, t)).1 = h (dev (s, t)).1` for all `(s, t)`,
the same `h` at every height `t`. -/
theorem exists_gTilde_of_holonomy {ε : ℝ} (hε : ε ^ 2 = 1) {dev : DSTilde → DSTilde}
    (hdev : Continuous dev) {B : Causal.Flat.lorentz 2}
    (hB : ∀ z : DSTilde,
      (dsCover ε hε (dev (z.1 + 1, z.2)) : HS 2) = B • (dsCover ε hε (dev z) : HS 2)) :
    ∃ h : GTilde, ∀ z : DSTilde, (dev (z.1 + 1, z.2)).1 = h (dev z).1 := by
  obtain ⟨h₀, hh₀⟩ := GTilde.toPSL_surjective (pslEquivLorentz.symm B)
  have key : ∀ z : DSTilde, RP1.proj (dev (z.1 + 1, z.2)).1 = RP1.proj (h₀ (dev z).1) := by
    intro z
    have e1 : dsCover ε hε (dev (z.1 + 1, z.2)) = B • dsCover ε hε (dev z) := Subtype.ext (hB z)
    have e2 := congrArg (fun σ => ((iota ε hε σ : HS.piece 2 .bdPlus) : HS 2)) e1
    rw [iota_smul, coe_smul_piece, iota_dsCover, iota_dsCover, smul_rp1ToBdPlus] at e2
    rw [GTilde.proj_apply, hh₀]
    exact rp1ToBdPlus.injective (Subtype.ext e2)
  set k : DSTilde → ℝ := fun z => (dev (z.1 + 1, z.2)).1 - h₀ (dev z).1 with hk
  have hint : ∀ z, ∃ n : ℤ, k z = n := by
    intro z
    obtain ⟨n, hn⟩ := RP1.proj_eq_proj_iff.1 (key z)
    exact ⟨n, by simp only [hk]; linarith⟩
  have hc : Continuous k :=
    (continuous_fst.comp (hdev.comp ((continuous_fst.add continuous_const).prodMk
      continuous_snd))).sub ((GTilde.continuous h₀).comp (continuous_fst.comp hdev))
  set z₀ : DSTilde := rPlus 0
  obtain ⟨n, hn⟩ := hint z₀
  refine ⟨GTilde.delta ^ n * h₀, fun z => ?_⟩
  have hz := eq_of_continuous_intValued hc hint z z₀
  rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply]
  simp only [hk] at hz hn
  linarith

/-- **An HS-surface is semilocally simply connected**: it is charted on `HS²`, which is locally
unloopable (`GX.isLocallyUnloopable_hs2`). -/
theorem semilocallySimplyConnected_of_chartedSpace_hs2 (M : Type*) [TopologicalSpace M]
    [ChartedSpace (HS 2) M] : SemilocallySimplyConnected M :=
  (isLocallyUnloopable_hs2.semilocallySimplyConnected_of_charts (W := (univ : Set M))
    fun y _ => ⟨chartAt (HS 2) y, mem_chart_source _ y, subset_univ _⟩).of_homeomorph
    (Homeomorph.Set.univ M)

/-! ### N4's data: a regular de Sitter annulus between `C₋` and `C₊` -/

/-- **A regular de Sitter annulus** `Ā = C₋ ∪ A ∪ C₊` in an HS-surface `M` (N4 "Setting",
l.321–329; BBS l.2960: `D`, « the de Sitter part of `Σ` »): the photon circles `C₋` (past
photons, the boundary of the past disc) and `C₊` (future photons), and the covering of `Ā` by
the strip `ℝ × [−1, 1]`, of period `1`, restricting to periodic coverings `E± : ℝ → C±` on
the boundary lines. `M` stands for `Reg Σ`, so `Ā` is regular. -/
structure DSAnnulus (M : Type*) [TopologicalSpace M] [ChartedSpace (HS 2) M]
    [HasGroupoid M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2))] where
  /-- `C₋`, the circle of photons bounding the past hyperbolic region. -/
  cMinus : Set M
  /-- `C₊`, the circle of photons bounding the future hyperbolic region. -/
  cPlus : Set M
  isPhotonCircle_minus : IsPhotonCircle cMinus
  isPhotonCircle_plus : IsPhotonCircle cPlus
  past : ∀ x ∈ cMinus, hsRegion x = .bdMinus
  future : ∀ x ∈ cPlus, hsRegion x = .bdPlus
  /-- `Ã ∪ C̃₋ ∪ C̃₊ → Ā`. -/
  cover : DSTilde → M
  continuous_cover : Continuous cover
  cover_add_one : ∀ (s : ℝ) (t : Icc (-1 : ℝ) 1), cover (s + 1, t) = cover (s, t)
  /-- `C̃₋ → C₋`. -/
  eMinus : ℝ → cMinus
  /-- `C̃₊ → C₊`. -/
  ePlus : ℝ → cPlus
  isPeriodicCover_minus : IsPeriodicCover eMinus
  isPeriodicCover_plus : IsPeriodicCover ePlus
  cover_rMinus : ∀ s, cover (rMinus s) = eMinus s
  cover_rPlus : ∀ s, cover (rPlus s) = ePlus s

namespace DSAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (HS 2) M]
  [HasGroupoid M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2))] (A : DSAnnulus M)
  {ε : ℝ} (hε : ε ^ 2 = 1)

/-- **The developing map `d : D̃ ∪ C̃₋ ∪ C̃₊ → d̃S² ∪ R₋ ∪ R₊`** (l.2971–2974, extended to the
boundary as in the diagram of l.2997–3004): continuous, and near every point `π ∘ d` is an
`SO₀(1,2)`-translate of the HS-chart of `M`, read through the covering of `Ā`. -/
structure IsDevelopment (dev : DSTilde → DSTilde) : Prop where
  continuous : Continuous dev
  locally : ∀ z, ∃ g : Causal.Flat.lorentz 2, ∀ᶠ z' in 𝓝 z,
    (dsCover ε hε (dev z') : HS 2) = g • chartAt (HS 2) (A.cover z) (A.cover z')

/-- **The named hypothesis (l.2991–3004)**: « Since `D` does not contain singularities, we have
an analogous proper submersion `ι'_L : D̃ ∪ C̃₋ ∪ C̃₊ → C̃₊` » and « by the naturality of the
construction, the diagram commutes ». `ι'` is continuous, lifts a map `Ā → C₊` (the leaf
projection of `Ā`), and `d ∘ ι' = ι̃_ε ∘ d`. Only what the proof uses is carried. -/
structure IsIotaPrime (dev : DSTilde → DSTilde) (ι' : DSTilde → ℝ) : Prop where
  isDevelopment : A.IsDevelopment hε dev
  continuous : Continuous ι'
  descends : ∀ z z', A.cover z = A.cover z' → A.ePlus (ι' z) = A.ePlus (ι' z')
  comm : ∀ z, dev (rPlus (ι' z)) = iotaTilde (dev z)

/-- The named hypothesis, existentially. -/
def HasIotaPrime : Prop := ∃ dev ι', A.IsIotaPrime hε dev ι'

variable {A hε}

/-- The developing map sends `C̃₋` into `R₋`. -/
theorem IsDevelopment.eq_rMinus {dev : DSTilde → DSTilde} (h : A.IsDevelopment hε dev)
    (s : ℝ) : dev (rMinus s) = rMinus (dev (rMinus s)).1 := by
  obtain ⟨g, hg⟩ := h.locally (rMinus s)
  apply eq_rMinus_of_mem_bdMinus hε
  rw [hg.self_of_nhds, HS.mem_piece_iff_region, HS.region_smul, A.cover_rMinus]
  exact A.past _ (A.eMinus s).2

/-- The developing map sends `C̃₊` into `R₊`. -/
theorem IsDevelopment.eq_rPlus {dev : DSTilde → DSTilde} (h : A.IsDevelopment hε dev)
    (s : ℝ) : dev (rPlus s) = rPlus (dev (rPlus s)).1 := by
  obtain ⟨g, hg⟩ := h.locally (rPlus s)
  apply eq_rPlus_of_mem_bdPlus hε
  rw [hg.self_of_nhds, HS.mem_piece_iff_region, HS.region_smul, A.cover_rPlus]
  exact A.future _ (A.ePlus s).2

/-- **`d|C̃₋` is the developing map of `C₋`** (l.3005–3006, for `C₋`): its `ℝP̃¹`-coordinate
lifts a developing map along `E₋` of the structure from the hyperbolic side. -/
theorem IsDevelopment.isDevAlong_minus {dev : DSTilde → DSTilde} (h : A.IsDevelopment hε dev) :
    @IsDevAlong A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace A.eMinus
      (RP1.proj ∘ fun s => (dev (rMinus s)).1) := by
  letI := A.isPhotonCircle_minus.rp1ChartedSpace
  intro s
  obtain ⟨g, hg⟩ := h.locally (rMinus s)
  refine ⟨pslEquivLorentz.symm g, ?_⟩
  have hc : Continuous fun s' => ((A.eMinus s' : A.cMinus) : M) :=
    continuous_subtype_val.comp A.isPeriodicCover_minus.isCoveringMap.continuous
  have hsrc : ∀ᶠ s' in 𝓝 s,
      ((A.eMinus s' : A.cMinus) : M) ∈ (chartAt (HS 2) ((A.eMinus s : A.cMinus) : M)).source :=
    hc.continuousAt.eventually ((chartAt (HS 2) _).open_source.mem_nhds (mem_chart_source _ _))
  filter_upwards [continuous_rMinus.continuousAt.eventually hg, hsrc] with s' h1 h2
  rw [A.cover_rMinus, A.cover_rMinus, h.eq_rMinus s', dsCover_rMinus,
    ← A.isPhotonCircle_minus.coe_rp1ToBdMinus_chartAt A.past _ _ h2, smul_rp1ToBdMinus] at h1
  exact rp1ToBdMinus.injective (Subtype.ext h1)

/-- **`d|C̃₊` is the developing map of `C₊`** (l.3005–3006). -/
theorem IsDevelopment.isDevAlong_plus {dev : DSTilde → DSTilde} (h : A.IsDevelopment hε dev) :
    @IsDevAlong A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace A.ePlus
      (RP1.proj ∘ fun s => (dev (rPlus s)).1) := by
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  intro s
  obtain ⟨g, hg⟩ := h.locally (rPlus s)
  refine ⟨pslEquivLorentz.symm g, ?_⟩
  have hc : Continuous fun s' => ((A.ePlus s' : A.cPlus) : M) :=
    continuous_subtype_val.comp A.isPeriodicCover_plus.isCoveringMap.continuous
  have hsrc : ∀ᶠ s' in 𝓝 s,
      ((A.ePlus s' : A.cPlus) : M) ∈ (chartAt (HS 2) ((A.ePlus s : A.cPlus) : M)).source :=
    hc.continuousAt.eventually ((chartAt (HS 2) _).open_source.mem_nhds (mem_chart_source _ _))
  filter_upwards [continuous_rPlus.continuousAt.eventually hg, hsrc] with s' h1 h2
  rw [A.cover_rPlus, A.cover_rPlus, h.eq_rPlus s', dsCover_rPlus,
    ← A.isPhotonCircle_plus.coe_rp1ToBdPlus_chartAt A.future _ _ h2, smul_rp1ToBdPlus] at h1
  exact rp1ToBdPlus.injective (Subtype.ext h1)

/-- The `ℝP̃¹`-coordinate of `d|C̃₊` is injective. -/
theorem IsDevelopment.injective_plus {dev : DSTilde → DSTilde} (h : A.IsDevelopment hε dev) :
    Function.Injective fun u => (dev (rPlus u)).1 := by
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  haveI := A.isPhotonCircle_plus.rp1_hasGroupoid
  have hc : Continuous fun u => (dev (rPlus u)).1 :=
    continuous_fst.comp (h.continuous.comp continuous_rPlus)
  exact injective_of_isOpenMap_real hc (h.isDevAlong_plus.isLocalHomeomorph_lift
    A.isPeriodicCover_plus.isCoveringMap.isLocalHomeomorph hc).isOpenMap

/-- `ι'` is the identity on `C̃₊`. -/
theorem IsIotaPrime.apply_rPlus {dev : DSTilde → DSTilde} {ι' : DSTilde → ℝ}
    (h : A.IsIotaPrime hε dev ι') (s : ℝ) : ι' (rPlus s) = s := by
  have h1 := congrArg Prod.fst (h.comm (rPlus s))
  exact h.isDevelopment.injective_plus h1

/-- `ι'` commutes with the deck transformations: `ι' (s + 1, t) = ι' (s, t) + 1`. -/
theorem IsIotaPrime.apply_add_one {dev : DSTilde → DSTilde} {ι' : DSTilde → ℝ}
    (h : A.IsIotaPrime hε dev ι') (s : ℝ) (t : Icc (-1 : ℝ) 1) :
    ι' (s + 1, t) = ι' (s, t) + 1 := by
  set g : DSTilde → ℝ := fun z => ι' (z.1 + 1, z.2) - ι' z with hg
  have hgc : Continuous g := (h.continuous.comp
    ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub h.continuous
  have hint : ∀ z, ∃ n : ℤ, g z = n := by
    rintro ⟨u, τ⟩
    have he := h.descends (u + 1, τ) (u, τ) (A.cover_add_one u τ)
    obtain ⟨n, hn⟩ := A.isPeriodicCover_plus.fiber _ _ he.symm
    exact ⟨n, by simp only [hg]; linarith⟩
  have h1 : g (rPlus s) = 1 := by
    simp only [hg]
    rw [show ((rPlus s).1 + 1, (rPlus s).2) = rPlus (s + 1) from rfl, h.apply_rPlus,
      h.apply_rPlus]
    ring
  have hconst := eq_of_continuous_intValued hgc hint (s, t) (rPlus s)
  rw [h1] at hconst
  simp only [hg] at hconst
  linarith

/-- The diagram on `C̃₋`: `d₊ ∘ ι' = d₋` in `ℝP̃¹`-coordinates. -/
theorem IsIotaPrime.dev_comp {dev : DSTilde → DSTilde} {ι' : DSTilde → ℝ}
    (h : A.IsIotaPrime hε dev ι') (s : ℝ) :
    (dev (rPlus (ι' (rMinus s)))).1 = (dev (rMinus s)).1 := by
  have h1 := congrArg Prod.fst (h.comm (rMinus s))
  exact h1

/-- **BBS l.3013–3016 (`bbsrem:causally_regular_hs_sphere_containing`), under the named
hypothesis**: `ι'_L : C̃₋ → C̃₊` induces a projective isomorphism `ῑ : C₋ → C₊`. -/
theorem IsIotaPrime.exists_projIso {dev : DSTilde → DSTilde} {ι' : DSTilde → ℝ}
    (h : A.IsIotaPrime hε dev ι') :
    letI := A.isPhotonCircle_minus.rp1ChartedSpace
    letI := A.isPhotonCircle_plus.rp1ChartedSpace
    ∃ ι : A.cMinus ≃ₜ A.cPlus, (∀ s, ι (A.eMinus s) = A.ePlus (ι' (rMinus s))) ∧
      IsGXMorphism PSL(2, ℝ) RP1 ι ∧ IsGXMorphism PSL(2, ℝ) RP1 ι.symm := by
  letI := A.isPhotonCircle_minus.rp1ChartedSpace
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  haveI := A.isPhotonCircle_minus.rp1_hasGroupoid
  haveI := A.isPhotonCircle_plus.rp1_hasGroupoid
  exact exists_projIso_of_lift A.isPhotonCircle_minus.isCircle A.isPhotonCircle_plus.isCircle
    A.isPeriodicCover_minus A.isPeriodicCover_plus
    (continuous_fst.comp (h.isDevelopment.continuous.comp continuous_rMinus))
    h.isDevelopment.isDevAlong_minus h.isDevelopment.isDevAlong_plus
    (h.continuous.comp continuous_rMinus) (fun s => h.apply_add_one s _) h.dev_comp

/-- **The remark, existentially.** -/
theorem remark_projIso (h : A.HasIotaPrime hε) :
    letI := A.isPhotonCircle_minus.rp1ChartedSpace
    letI := A.isPhotonCircle_plus.rp1ChartedSpace
    ∃ ι : A.cMinus ≃ₜ A.cPlus, IsGXMorphism PSL(2, ℝ) RP1 ι ∧
      IsGXMorphism PSL(2, ℝ) RP1 ι.symm := by
  obtain ⟨dev, ι', h⟩ := h
  obtain ⟨ι, -, hι, hι'⟩ := h.exists_projIso
  exact ⟨ι, hι, hι'⟩

/-- **N4 (M3), the two `ℝP¹`-circles are isomorphic, degree included**: `C₋` and `C₊` have the
same lifted holonomies in `G̃`. -/
theorem hasLiftedHolonomy_iff (h : A.HasIotaPrime hε) (f : GTilde) :
    @HasLiftedHolonomy A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace f ↔
      @HasLiftedHolonomy A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace f := by
  letI := A.isPhotonCircle_minus.rp1ChartedSpace
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  obtain ⟨ι, hι, -⟩ := A.remark_projIso h
  exact hasLiftedHolonomy_iff_of_isGXMorphism hι f

/-- **N4 (M3), real-angle half: `Θ₋ = Θ₊` as real numbers.** -/
theorem theta_eq (h : A.HasIotaPrime hε) {θm θp : ℝ}
    (hm : @HasRealAngle A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace θm)
    (hp : @HasRealAngle A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace θp) : θm = θp := by
  letI := A.isPhotonCircle_minus.rp1ChartedSpace
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  haveI := A.isPhotonCircle_plus.rp1_hasGroupoid
  obtain ⟨ι, hι, -⟩ := A.remark_projIso h
  exact ((hasRealAngle_iff_of_isGXMorphism hι θm).1 hm).unique hp

/-- **`Θ₋ = Θ₊`, existentially**: there is one real number which is the real angle of both. -/
theorem exists_theta (h : A.HasIotaPrime hε) :
    ∃ θ : ℝ, @HasRealAngle A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace θ ∧
      @HasRealAngle A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace θ := by
  letI := A.isPhotonCircle_minus.rp1ChartedSpace
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  haveI := A.isPhotonCircle_minus.rp1_hasGroupoid
  obtain ⟨θ, hθ⟩ := GX.exists_hasRealAngle (L := A.cMinus) A.isPhotonCircle_minus.isCircle
  obtain ⟨ι, hι, -⟩ := A.remark_projIso h
  exact ⟨θ, hθ, (hasRealAngle_iff_of_isGXMorphism hι θ).1 hθ⟩

/-- **The holonomy of the annulus** (N4 (M3): « a loop parallel to `C₋` is homotopic across the
regular annulus `A` to a loop parallel to `C₊` »): the developing map is equivariant for the
deck transformation `(s, t) ↦ (s + 1, t)`, through some `B ∈ SO₀(1,2)`. -/
def IsEquivariant (hε' : ε ^ 2 = 1) (dev : DSTilde → DSTilde) : Prop :=
  ∃ B : Causal.Flat.lorentz 2, ∀ z : DSTilde,
    (dsCover ε hε' (dev (z.1 + 1, z.2)) : HS 2) = B • (dsCover ε hε' (dev z) : HS 2)

/-- **`C₋` and `C₊` have lifted holonomies `h^{±1}` for one `h ∈ G̃`**: for a developing map
with holonomy, the `ℝP̃¹`-coordinates of `d|C̃₋` and `d|C̃₊` are equivariant for the same `h`. -/
theorem IsDevelopment.exists_gTilde {dev : DSTilde → DSTilde} (h : A.IsDevelopment hε dev)
    (hhol : IsEquivariant hε dev) :
    ∃ g : GTilde,
      (@HasLiftedHolonomy A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace g ∨
        @HasLiftedHolonomy A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace g⁻¹) ∧
      (@HasLiftedHolonomy A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace g ∨
        @HasLiftedHolonomy A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace g⁻¹) := by
  obtain ⟨B, hB⟩ := hhol
  obtain ⟨g, hg⟩ := exists_gTilde_of_holonomy hε h.continuous hB
  refine ⟨g, ?_, ?_⟩
  · letI := A.isPhotonCircle_minus.rp1ChartedSpace
    haveI := A.isPhotonCircle_minus.rp1_hasGroupoid
    exact hasLiftedHolonomy_or_inv A.isPeriodicCover_minus
      (continuous_fst.comp (h.continuous.comp continuous_rMinus)) h.isDevAlong_minus
      (fun s => hg (rMinus s))
  · letI := A.isPhotonCircle_plus.rp1ChartedSpace
    haveI := A.isPhotonCircle_plus.rp1_hasGroupoid
    exact hasLiftedHolonomy_or_inv A.isPeriodicCover_plus
      (continuous_fst.comp (h.continuous.comp continuous_rPlus)) h.isDevAlong_plus
      (fun s => hg (rPlus s))

/-- **N4 (M3), real-angle half, from the developing map alone: `Θ₋ = Θ₊`.** No `ι'_L` is
needed: the holonomy of the annulus acts on `R₋` and `R₊` by one `h ∈ G̃`
(`GX.exists_gTilde_of_holonomy`), so `Θ±` are `angle h^{±1}`; and since real angles are
`≥ 0`, opposite signs force `angle h = 0`. -/
theorem IsDevelopment.theta_eq {dev : DSTilde → DSTilde} (h : A.IsDevelopment hε dev)
    (hhol : IsEquivariant hε dev) {θm θp : ℝ}
    (hm : @HasRealAngle A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace θm)
    (hp : @HasRealAngle A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace θp) : θm = θp := by
  letI := A.isPhotonCircle_minus.rp1ChartedSpace
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  haveI := A.isPhotonCircle_minus.rp1_hasGroupoid
  haveI := A.isPhotonCircle_plus.rp1_hasGroupoid
  obtain ⟨g, hgm, hgp⟩ := h.exists_gTilde hhol
  have hm0 := hm.nonneg
  have hp0 := hp.nonneg
  have hginv := GTilde.angle_inv g
  rcases hgm with hgm | hgm <;> rcases hgp with hgp | hgp
  · rw [hm.unique ⟨_, hgm, rfl⟩, hp.unique ⟨_, hgp, rfl⟩]
  · rw [hm.unique ⟨_, hgm, rfl⟩, hp.unique ⟨_, hgp, rfl⟩] at *
    linarith
  · rw [hm.unique ⟨_, hgm, rfl⟩, hp.unique ⟨_, hgp, rfl⟩] at *
    linarith
  · rw [hm.unique ⟨_, hgm, rfl⟩, hp.unique ⟨_, hgp, rfl⟩]

/-- **BBS l.3013–3016 when `Θ₋ > 0`, from the developing map alone** (no `ι'_L`): if the real
angle of `C₋` is positive (e.g. `C₋` elliptic, `GX.HasRealAngle.pos_of_isElliptic`), the holonomy
`h` of the annulus has no fixed point on `ℝP̃¹`, so `d|C̃₊` is onto `ℝP̃¹`, and
`φ = (d|C̃₊)⁻¹ ∘ d|C̃₋` induces a projective isomorphism `ῑ : C₋ → C₊`. Only the existence of `ῑ`
is stated: the inducing clause is dropped, and that `φ` is `ι'_L` read in developed coordinates is
not stated here. -/
theorem IsDevelopment.exists_projIso_of_pos {dev : DSTilde → DSTilde}
    (h : A.IsDevelopment hε dev) (hhol : IsEquivariant hε dev) {θ : ℝ}
    (hθ : @HasRealAngle A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace θ) (hpos : 0 < θ) :
    letI := A.isPhotonCircle_minus.rp1ChartedSpace
    letI := A.isPhotonCircle_plus.rp1ChartedSpace
    ∃ ι : A.cMinus ≃ₜ A.cPlus, IsGXMorphism PSL(2, ℝ) RP1 ι ∧
      IsGXMorphism PSL(2, ℝ) RP1 ι.symm := by
  letI := A.isPhotonCircle_minus.rp1ChartedSpace
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  haveI := A.isPhotonCircle_minus.rp1_hasGroupoid
  haveI := A.isPhotonCircle_plus.rp1_hasGroupoid
  obtain ⟨B, hB⟩ := hhol
  obtain ⟨g, hg⟩ := exists_gTilde_of_holonomy hε h.continuous hB
  set Dm : ℝ → ℝ := fun s => (dev (rMinus s)).1 with hDm
  set Dp : ℝ → ℝ := fun s => (dev (rPlus s)).1 with hDp
  have hDmc : Continuous Dm := continuous_fst.comp (h.continuous.comp continuous_rMinus)
  have hDpc : Continuous Dp := continuous_fst.comp (h.continuous.comp continuous_rPlus)
  have hDmg : ∀ s, Dm (s + 1) = g (Dm s) := fun s => hg (rMinus s)
  have hDpg : ∀ s, Dp (s + 1) = g (Dp s) := fun s => hg (rPlus s)
  -- `g` has no fixed point, since `Θ₋ = ± angle g > 0`
  have hfix : ∀ x, g x ≠ x := by
    intro x hx
    have h0 := GTilde.angle_eq_zero_of_fixed hx
    rcases hasLiftedHolonomy_or_inv A.isPeriodicCover_minus hDmc h.isDevAlong_minus hDmg
      with hm | hm
    · have := hθ.unique ⟨_, hm, rfl⟩
      linarith
    · have := hθ.unique ⟨_, hm, rfl⟩
      rw [GTilde.angle_inv, h0] at this
      linarith
  -- `d|C̃₊` is a homeomorphism `ℝ ≃ₜ ℝ`
  have hDploc := h.isDevAlong_plus.isLocalHomeomorph_lift
    A.isPeriodicCover_plus.isCoveringMap.isLocalHomeomorph hDpc
  have hDpi : Function.Injective Dp := injective_of_isOpenMap_real hDpc hDploc.isOpenMap
  have hDps : Function.Surjective Dp :=
    surjective_of_equivariant A.isPeriodicCover_plus hDpc h.isDevAlong_plus hDpg hfix
  let e : ℝ ≃ₜ ℝ :=
    (Equiv.ofBijective Dp ⟨hDpi, hDps⟩).toHomeomorphOfContinuousOpen hDpc hDploc.isOpenMap
  have hφD : ∀ s, Dp (e.symm (Dm s)) = Dm s := fun s => e.apply_symm_apply (Dm s)
  have hφ1 : ∀ s, e.symm (Dm (s + 1)) = e.symm (Dm s) + 1 := by
    intro s
    apply hDpi
    rw [hφD, hDpg, hφD, hDmg]
  obtain ⟨ι, -, hι, hι'⟩ := exists_projIso_of_lift A.isPhotonCircle_minus.isCircle
    A.isPhotonCircle_plus.isCircle A.isPeriodicCover_minus A.isPeriodicCover_plus hDmc
    h.isDevAlong_minus h.isDevAlong_plus (e.symm.continuous.comp hDmc) hφ1 hφD
  exact ⟨ι, hι, hι'⟩

/-- **The developing map of the annulus exists, with its holonomy** (l.2971–2974, extended to
`C̃±`): from gx's classical developing theorem (`GX.developing_theorem`) on the universal cover
of `M`, through the lifts of `Ā`'s covering to `M̃` and of the developed annulus to
`d̃S² ∪ R±`. `M` is locally path-connected and semilocally simply connected (gx's standing
hypotheses, as in `GX.theoremM_developing`), and the points of `Ā` are de Sitter points or
photons (`A` a de Sitter annulus). -/
theorem exists_isDevelopment [LocPathConnectedSpace M] (hM : SemilocallySimplyConnected M)
    (hreg : ∀ z, hsRegion (A.cover z) = .deSitter ∨ hsRegion (A.cover z) = .bdPlus ∨
      hsRegion (A.cover z) = .bdMinus) :
    ∃ dev : DSTilde → DSTilde, A.IsDevelopment hε dev ∧ IsEquivariant hε dev := by
  set z₀ : DSTilde := rPlus 0
  set x₀ : M := A.cover z₀
  letI := coverChartedSpace (HS 2) hM x₀
  obtain ⟨devM, hol, hdevM, -, hhol⟩ :=
    developing_theorem (G := Causal.Flat.lorentz 2) (X := HS 2) hM x₀
  have hp : IsCoveringMap (UniversalCover.proj M x₀) := UniversalCover.isCoveringMap_proj hM
  -- the lift of the covering of `Ā` to `M̃`
  obtain ⟨c, ⟨-, hc⟩, -⟩ := hp.existsUnique_continuousMap_lifts ⟨A.cover, A.continuous_cover⟩ z₀
    (UniversalCover.base x₀) rfl
  have hcp : ∀ z, (c z).pt = A.cover z := fun z => congrFun hc z
  -- the deck transformation over `(s, t) ↦ (s + 1, t)`
  let T : DSTilde → DSTilde := fun z => (z.1 + 1, z.2)
  have hT : Continuous T := (continuous_fst.add continuous_const).prodMk continuous_snd
  obtain ⟨γ, hγ⟩ := UniversalCover.exists_deck_apply_eq (c := c z₀) (c' := c (T z₀))
    (by rw [hcp, hcp]; exact (A.cover_add_one _ _).symm)
  have hγp : ∀ w, (γ.1 w).pt = w.pt := fun w => congrFun γ.2 w
  have hcT : ∀ z, c (T z) = γ.1 (c z) := by
    have := hp.eq_of_comp_eq (g₁ := fun z => c (T z)) (g₂ := fun z => γ.1 (c z))
      (c.continuous.comp hT) (γ.1.continuous.comp c.continuous) (funext fun z => by
        show (c (T z)).pt = (γ.1 (c z)).pt
        rw [hγp, hcp, hcp]
        exact A.cover_add_one _ _) z₀ hγ.symm
    exact fun z => congrFun this z
  -- the developed annulus in `HS²`
  let d₀ : DSTilde → HS 2 := fun z => devM (c z)
  have hd₀c : Continuous d₀ := hdevM.continuous.comp c.continuous
  have hloc : ∀ z, ∃ g : Causal.Flat.lorentz 2, ∀ᶠ z' in 𝓝 z,
      d₀ z' = g • chartAt (HS 2) (A.cover z) (A.cover z') := by
    intro z
    obtain ⟨g, hg⟩ := (isGXMorphism_iff_model.1 hdevM).2 (c z)
    refine ⟨g, ?_⟩
    filter_upwards [c.continuous.continuousAt.eventually hg] with z' hz'
    show devM (c z') = _
    rw [hz', pullback_chartAt_apply]
    show g • chartAt (HS 2) (c z).pt (c z').pt = _
    rw [hcp, hcp]
  have hmem : ∀ z, d₀ z ∈ HS.closedDS := by
    intro z
    obtain ⟨g, hg⟩ := hloc z
    rw [hg.self_of_nhds, HS.smul_mem_closedDS_iff, HS.mem_closedDS_iff, HS.mem_piece_iff_region,
      HS.mem_piece_iff_region, HS.mem_piece_iff_region]
    exact hreg z
  -- its lift to `d̃S² ∪ R±`
  let d₁ : DSTilde → HS.closedDS := fun z => ⟨d₀ z, hmem z⟩
  have hd₁c : Continuous d₁ := hd₀c.subtype_mk _
  have hq : IsCoveringMap (fun s : ℝ => rp1ToBdPlus (RP1.proj s)) :=
    RP1.isCoveringMap_proj.homeomorph_comp rp1ToBdPlus
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℝ, rp1ToBdPlus (RP1.proj e₀) = (iotaChart ε hε (d₁ z₀)).1 := by
    obtain ⟨w, hw⟩ := rp1ToBdPlus.surjective (iotaChart ε hε (d₁ z₀)).1
    obtain ⟨e, he⟩ := RP1.proj_surjective w
    exact ⟨e, by rw [he, hw]⟩
  obtain ⟨u, ⟨-, hu⟩, -⟩ := hq.existsUnique_continuousMap_lifts
    ⟨fun z => (iotaChart ε hε (d₁ z)).1,
      continuous_fst.comp ((iotaChart ε hε).continuous.comp hd₁c)⟩ z₀ e₀ he₀
  let dev : DSTilde → DSTilde := fun z => (u z, (iotaChart ε hε (d₁ z)).2)
  have hdev : ∀ z, (dsCover ε hε (dev z) : HS 2) = d₀ z := by
    intro z
    have h1 : rp1ToBdPlus (RP1.proj (u z)) = (iotaChart ε hε (d₁ z)).1 := congrFun hu z
    show (((iotaChart ε hε).symm (rp1ToBdPlus (RP1.proj (u z)), (iotaChart ε hε (d₁ z)).2) :
      HS.closedDS) : HS 2) = d₀ z
    rw [h1, Prod.mk.eta, Homeomorph.symm_apply_apply]
  refine ⟨dev, ⟨u.continuous.prodMk (continuous_snd.comp ((iotaChart ε hε).continuous.comp hd₁c)),
    fun z => ?_⟩, hol γ, fun z => ?_⟩
  · obtain ⟨g, hg⟩ := hloc z
    exact ⟨g, by filter_upwards [hg] with z' hz'; rw [hdev, hz']⟩
  · rw [hdev, hdev]
    show devM (c (T z)) = hol γ • devM (c z)
    rw [hcT, hhol]

/-- **N4 (M3), real-angle half, with no hypothesis beyond N4's data: `Θ₋ = Θ₊`.** For a regular
de Sitter annulus `Ā` in an HS-surface `M` (any `(SO₀(1,2), HS²)`-manifold: it is locally
path-connected and semilocally simply connected, being charted on `HS²`), the real angles of the
circles of photons `C₋` and `C₊` (from the hyperbolic side) are equal. -/
theorem theta_eq_of_regular
    (hreg : ∀ z, hsRegion (A.cover z) = .deSitter ∨ hsRegion (A.cover z) = .bdPlus ∨
      hsRegion (A.cover z) = .bdMinus) {θm θp : ℝ}
    (hm : @HasRealAngle A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace θm)
    (hp : @HasRealAngle A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace θp) : θm = θp := by
  haveI := ChartedSpace.locPathConnectedSpace (HS 2) M
  obtain ⟨dev, hdev, hhol⟩ := A.exists_isDevelopment (ε := 1) (hε := one_pow 2)
    (semilocallySimplyConnected_of_chartedSpace_hs2 M) hreg
  exact hdev.theta_eq hhol hm hp

/-- **N4 (M3), « degree included »**: if the lifted holonomies of `C₋` and `C₊` are `δ^{k±} g±`
with `g±` having a fixed point in `ℝP̃¹` (l.696–698: non-elliptic, of degree `k±`), then
`k₋ = k₊`. -/
theorem degree_eq_of_regular
    (hreg : ∀ z, hsRegion (A.cover z) = .deSitter ∨ hsRegion (A.cover z) = .bdPlus ∨
      hsRegion (A.cover z) = .bdMinus) {fm fp gm gp : GTilde} {km kp : ℤ}
    (hfm : @HasLiftedHolonomy A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace fm)
    (hfp : @HasLiftedHolonomy A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace fp)
    (hgm : ∃ x, gm x = x) (hgp : ∃ x, gp x = x) (hm : fm = GTilde.delta ^ km * gm)
    (hp : fp = GTilde.delta ^ kp * gp) : km = kp := by
  have h := A.theta_eq_of_regular hreg (θm := GTilde.angle fm) (θp := GTilde.angle fp)
    ⟨fm, hfm, rfl⟩ ⟨fp, hfp, rfl⟩
  rw [GTilde.angle_eq_of_delta_zpow_mul hgm hm, GTilde.angle_eq_of_delta_zpow_mul hgp hp] at h
  have h' : (km : ℝ) = kp := by
    have := Real.pi_pos
    nlinarith
  exact_mod_cast h'

/-- **BBS l.3013–3016 for `Θ > 0` (in particular elliptic `C₋`), with no hypothesis beyond
N4's data**: `C₋` and `C₊` are projectively isomorphic. -/
theorem remark_projIso_of_pos
    (hreg : ∀ z, hsRegion (A.cover z) = .deSitter ∨ hsRegion (A.cover z) = .bdPlus ∨
      hsRegion (A.cover z) = .bdMinus) {θ : ℝ}
    (hθ : @HasRealAngle A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace θ) (hpos : 0 < θ) :
    letI := A.isPhotonCircle_minus.rp1ChartedSpace
    letI := A.isPhotonCircle_plus.rp1ChartedSpace
    ∃ ι : A.cMinus ≃ₜ A.cPlus, IsGXMorphism PSL(2, ℝ) RP1 ι ∧
      IsGXMorphism PSL(2, ℝ) RP1 ι.symm := by
  haveI := ChartedSpace.locPathConnectedSpace (HS 2) M
  obtain ⟨dev, hdev, hhol⟩ := A.exists_isDevelopment (ε := 1) (hε := one_pow 2)
    (semilocallySimplyConnected_of_chartedSpace_hs2 M) hreg
  exact hdev.exists_projIso_of_pos hhol hθ hpos

/-- **N4 (M3), « the two `ℝP¹`-circles, degree included, are isomorphic », for `Θ > 0`**: `C₋`
and `C₊` have the same lifted holonomies in `G̃`. -/
theorem hasLiftedHolonomy_iff_of_pos
    (hreg : ∀ z, hsRegion (A.cover z) = .deSitter ∨ hsRegion (A.cover z) = .bdPlus ∨
      hsRegion (A.cover z) = .bdMinus) {θ : ℝ}
    (hθ : @HasRealAngle A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace θ) (hpos : 0 < θ)
    (f : GTilde) :
    @HasLiftedHolonomy A.cMinus _ A.isPhotonCircle_minus.rp1ChartedSpace f ↔
      @HasLiftedHolonomy A.cPlus _ A.isPhotonCircle_plus.rp1ChartedSpace f := by
  letI := A.isPhotonCircle_minus.rp1ChartedSpace
  letI := A.isPhotonCircle_plus.rp1ChartedSpace
  obtain ⟨ι, hι, -⟩ := A.remark_projIso_of_pos hreg hθ hpos
  exact hasLiftedHolonomy_iff_of_isGXMorphism hι f

end DSAnnulus

/-! ### The named hypothesis is satisfiable: the model annulus `dS² ∪ ∂ℍ²±` in `HS²` -/

section ModelAnnulus

variable {ε : ℝ} (hε : ε ^ 2 = 1)

theorem hsRegion_self (x : HS 2) : hsRegion x = HS.region x := rfl

theorem isPhotonCircle_bdMinus : IsPhotonCircle (HS.piece 2 .bdMinus) where
  isPhoton x hx := isPhoton_iff.2 (Or.inr (HS.region_eq_of_mem hx))
  relOpen x hx := by
    filter_upwards [eventually_hsRegion_bdMinus (M := HS 2) (HS.region_eq_of_mem hx)] with y hy hph
    exact HS.mem_piece_iff_region.2 (hy hph)
  isCircle := ⟨rp1ToBdMinus.symm⟩

theorem isPhotonCircle_bdPlus : IsPhotonCircle (HS.piece 2 .bdPlus) where
  isPhoton x hx := isPhoton_iff.2 (Or.inl (HS.region_eq_of_mem hx))
  relOpen x hx := by
    filter_upwards [eventually_hsRegion_bdPlus (M := HS 2) (HS.region_eq_of_mem hx)] with y hy hph
    exact HS.mem_piece_iff_region.2 (hy hph)
  isCircle := ⟨rp1ToBdPlus.symm⟩

/-- **The model annulus** `dS² ∪ ∂ℍ²±` of `HS²` (the de Sitter part of the link of a regular
point), covered by the strip through `GX.dsCover`. -/
def modelAnnulus : DSAnnulus (HS 2) where
  cMinus := HS.piece 2 .bdMinus
  cPlus := HS.piece 2 .bdPlus
  isPhotonCircle_minus := isPhotonCircle_bdMinus
  isPhotonCircle_plus := isPhotonCircle_bdPlus
  past := fun _ hx => HS.region_eq_of_mem hx
  future := fun _ hx => HS.region_eq_of_mem hx
  cover z := (dsCover ε hε z : HS 2)
  continuous_cover := continuous_subtype_val.comp (continuous_dsCover hε)
  cover_add_one s t := by rw [dsCover_add_one]
  eMinus := rp1ToBdMinus ∘ RP1.proj
  ePlus := rp1ToBdPlus ∘ RP1.proj
  isPeriodicCover_minus := by
    have := isPeriodicCover_of_homeomorph rp1ToBdMinus.symm
    rwa [Homeomorph.symm_symm] at this
  isPeriodicCover_plus := by
    have := isPeriodicCover_of_homeomorph rp1ToBdPlus.symm
    rwa [Homeomorph.symm_symm] at this
  cover_rMinus s := dsCover_rMinus hε s
  cover_rPlus s := dsCover_rPlus hε s

/-- **The named hypothesis holds in the model**, with `d = id` and `ι' (s, t) = s`. -/
theorem modelAnnulus_isIotaPrime : (modelAnnulus hε).IsIotaPrime hε id Prod.fst := by
  refine ⟨⟨continuous_id, fun z => ⟨1, Eventually.of_forall fun z' => ?_⟩⟩, continuous_fst,
    fun z z' hzz => ?_, fun z => rfl⟩
  · rw [one_smul, chartAt_self_eq]
    rfl
  · have h1 : dsCover ε hε z = dsCover ε hε z' := Subtype.ext hzz
    have h2 := congrArg (iota ε hε) h1
    rw [iota_dsCover, iota_dsCover] at h2
    exact h2

theorem modelAnnulus_hasIotaPrime : (modelAnnulus hε).HasIotaPrime hε :=
  ⟨id, Prod.fst, modelAnnulus_isIotaPrime hε⟩

/-- In the model the holonomy of the annulus is trivial. -/
theorem modelAnnulus_isEquivariant : DSAnnulus.IsEquivariant hε id :=
  ⟨1, fun z => by rw [one_smul, id, id, dsCover_add_one]⟩

/-- The points of the model annulus are de Sitter points or photons. -/
theorem modelAnnulus_region (z : DSTilde) :
    hsRegion ((modelAnnulus hε).cover z) = .deSitter ∨
      hsRegion ((modelAnnulus hε).cover z) = .bdPlus ∨
      hsRegion ((modelAnnulus hε).cover z) = .bdMinus := by
  rw [hsRegion_self, ← HS.mem_piece_iff_region, ← HS.mem_piece_iff_region,
    ← HS.mem_piece_iff_region, ← HS.mem_closedDS_iff]
  exact (dsCover ε hε z).2

/-- **Every hypothesis of `GX.DSAnnulus.theta_eq_of_regular` holds in the model.** -/
theorem modelAnnulus_theta_eq {θm θp : ℝ}
    (hm : @HasRealAngle (modelAnnulus hε).cMinus _
      (modelAnnulus hε).isPhotonCircle_minus.rp1ChartedSpace θm)
    (hp : @HasRealAngle (modelAnnulus hε).cPlus _
      (modelAnnulus hε).isPhotonCircle_plus.rp1ChartedSpace θp) : θm = θp :=
  (modelAnnulus hε).theta_eq_of_regular (modelAnnulus_region hε) hm hp

/-- In the model `∂ℍ²₊` has lifted holonomy `δ`: the regular case `Θ = 2π`. -/
theorem modelAnnulus_hasLiftedHolonomy_plus :
    @HasLiftedHolonomy (modelAnnulus hε).cPlus _
      (modelAnnulus hε).isPhotonCircle_plus.rp1ChartedSpace GTilde.delta := by
  letI := (modelAnnulus hε).isPhotonCircle_plus.rp1ChartedSpace
  refine ⟨(modelAnnulus hε).ePlus, id, (modelAnnulus hε).isPeriodicCover_plus, continuous_id,
    strictMono_id, fun s => ⟨1, Eventually.of_forall fun s' => ?_⟩,
    fun s => (GTilde.delta_apply s).symm⟩
  rw [one_smul]
  apply rp1ToBdPlus.injective
  apply Subtype.ext
  rw [IsPhotonCircle.coe_rp1ToBdPlus_chartAt _ (modelAnnulus hε).future _ _
    (by rw [chartAt_self_eq]; exact mem_univ _), chartAt_self_eq]
  rfl

/-- In the model `∂ℍ²₋` has lifted holonomy `δ` too (`GX.DSAnnulus.hasLiftedHolonomy_iff`). -/
theorem modelAnnulus_hasLiftedHolonomy_minus :
    @HasLiftedHolonomy (modelAnnulus hε).cMinus _
      (modelAnnulus hε).isPhotonCircle_minus.rp1ChartedSpace GTilde.delta :=
  ((modelAnnulus hε).hasLiftedHolonomy_iff (modelAnnulus_hasIotaPrime hε) _).2
    (modelAnnulus_hasLiftedHolonomy_plus hε)

/-- **In the model, `Θ₋ = Θ₊ = 2π`**: the regular point, of mass `1 − Θ/2π = 0` (in the
normalisation `angle δ = 2π` of `GX.GTilde.angle`, OQ-113 (a)). -/
theorem modelAnnulus_hasRealAngle :
    @HasRealAngle (modelAnnulus hε).cMinus _
        (modelAnnulus hε).isPhotonCircle_minus.rp1ChartedSpace (2 * π) ∧
      @HasRealAngle (modelAnnulus hε).cPlus _
        (modelAnnulus hε).isPhotonCircle_plus.rp1ChartedSpace (2 * π) :=
  ⟨⟨_, modelAnnulus_hasLiftedHolonomy_minus hε, GTilde.angle_delta.symm⟩,
    ⟨_, modelAnnulus_hasLiftedHolonomy_plus hε, GTilde.angle_delta.symm⟩⟩

end ModelAnnulus

end GX
