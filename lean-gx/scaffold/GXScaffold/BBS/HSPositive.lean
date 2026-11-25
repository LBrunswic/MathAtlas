import GX.BBS.HSSuspension
import GXScaffold.BBS.HSSingularities

/-!
# BBS § 3.8: positive HS-singularities, singular HS-surfaces, singular lines and interactions

Target `T-bbs-positive-hs-surface` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx, DEC-192).
`papers/bbs/legacy/labeled/colI_v1.tex`. 0 `sorry`. Imports the strict `GX.BBS.HSSuspension`
(`𝔢(L)`, singular HS-structures) and `GXScaffold.BBS.HSSingularities` (sorry-free: lifted
developing pairs, the positive/negative space-like and light-like circles).

* `bbsdef:hs_surface_interaction_singular_line` — `colI_v1.tex:1508` — partial (unmarked: the mark
  waits on OQ-113 (a)/(b), the cone angle as half the real angle of the link, and OQ-120 (c),
  positivity in l.915's form; and on the readings (b)–(f) of SCOPE, questions): an HS-singularity
  `p̄` of `𝔢(L)`, equivalently a singular line of type `L`, is positive:
  `GX.GammaLinkCircle.IsPositive`; a singular HS-surface, equivalently an interaction through its
  HS-sphere `Σ_x`, is positive: `GX.SingularHSStructure.IsPositive` (every point of `𝒮` has a
  positive link at `p̄`), « every link » reading `GX.SingularHSStructure.IsPositiveEvery`. Through
  `GX.GammaLinkCircle.coneAngle`, `GX.GammaLinkCircle.IsRegular` (« singularity »),
  `GX.SingularHSStructure.IsApexLink` (the link at `p̄`).

> Among singular lines, i.e. ``particles'', we can distinguish the ones having an attracting
> behavior on lightrays [...]
> A HS-surface, an interaction or a singular line is *positive* if all space-like and light-like
> singularities of degree $\geq 2$ therein are positive, and if all time-like singularities have a
> cone angle less that $2\pi$. (l.1505–1511)
>
> In other words, the singularity is positive if and only if for every $x$ in $I^+$ we have
> $gx \geq x$. (l.915)
>
> Here, the singularity corresponding to $p$ as a prefered status, as representation a
> $(\Gamma_p, \ell(p))$-singularity. (l.782–783)
>
> Therefore, we can define the type of the singular line: it is the type of the
> $(\Gamma_p, \ell(p))$-circle describing the singularity type of each of its elements. (l.983–984)

## Main declarations

* **The cone angle** `GX.GammaLinkCircle.coneAngle`: half the real angle of any lifted developing
  pair (`…coneAngle_eq`, `…coneAngle_eq_half`); `2π` at a regular point (`…coneAngle_regular`);
  `< 2π` iff `f < δ²` (`…coneAngle_lt_two_pi_iff`); positive at time-like `p`.
* **Regular links** `GX.GammaLinkCircle.IsRegular` (isomorphic to `ℓ(p)`): lifted holonomy `δ²`,
  factor `g = 1` (`…IsRegular.eq_delta_sq`, `…factor_eq`); positive (`…IsRegular.isPositive`).
* **Positive circles** `GX.GammaLinkCircle.IsPositive`: the three clauses, and
  `…isPositive_iff_of_timelike` (cone angle `< 2π`), `…isPositive_iff_of_deSitter`
  (`= IsSpacelikePositive` for hyperbolic `g`), `…isPositive_iff_of_null`
  (`= IsLightlikePositive` for parabolic `g`); an isomorphism invariant
  (`…IsIso.isPositive_iff`); non-vacuity `GX.exists_isPositive_and_not_isPositive` (the positive
  and negative tachyons of degree `2`); `GX.exists_isPositive_delta_four` (SCOPE (c)).
* **Positive singular HS-surfaces** `GX.SingularHSStructure.IsPositive`, `…IsPositiveEvery`,
  `…HasApexLinks` and the bridge `…IsPositiveEvery.isPositive`; regular HS-surfaces are positive
  (`…isPositive_ofHSSurface`); `𝔢(L)`: `GX.GammaLinkCircle.DevData.isPositiveAt_north`,
  `…isPositive_of_isPositiveEvery`; `GX.exists_not_isPositiveEvery`.
* **An inhabitant with a singular point**: `𝔢(L) ∖ {−p̄}` (`GX.BiSusp.offSouth`,
  `GX.SingularHSStructure.restrictTo`) is a singular HS-surface with `𝒮 = {p̄}`, positive when `L`
  is (`GX.GammaLinkCircle.DevData.isSingularHSSurface_offSouth`, `…isPositive_offSouth`);
  `GX.exists_isPositive_isSingularHSSurface`, with `L` a non-regular positive tachyon.

## Hypothesis checklist

| BBS | here |
|---|---|
| « A HS-surface » (l.1509) | ✓ any `GX.SingularHSStructure` (no `IsSingularHSSurface` needed); regular ones are positive |
| « an interaction » (l.1509) | ⚠ read: through its HS-sphere `Σ_x` (SCOPE (f)) |
| « a singular line » (l.1509) | ⚠ read: through its type `L` (l.983–984); `𝔢(L)` at `p̄` (SCOPE (f)) |
| « singularities therein » | ⚠ read: points of `𝒮` through a link at `p̄` (SCOPE (d), (e)), regular ones not counted (SCOPE (b)) |
| space-like / light-like / time-like | ✓ `p ∈ dS²` / `minkQ p = 0` (`∂ℍ²±`) / `minkQ p < 0` (`ℍ²±`) |
| « of degree `≥ 2` » | ✓ `f = δᵏ g`, `g` with a fixed point, `k ≥ 2` (`k ≥ 1` alike: `k` is even) |
| « positive », space-like (l.906–915) | ⚠ l.915's form (OQ-120 (c)), every lifted pair; `IsSpacelikePositive` for hyperbolic `g` |
| « positive », light-like (l.917–922) | ✓ `g x ≥ x` on `ℝP̃¹`; `IsLightlikePositive` for parabolic `g` |
| « cone angle less than `2π` » | ⚠ `coneAngle` (OQ-113 (a)/(b), SCOPE (a)); `= 2π` at regular points |

## SCOPE (disclosed)

* **(a) Cone angle.** Not defined by the paper for a `(Γ_p, ℓ(p))`-circle (l.804–806: time-like
  singularities are the cone points of hyperbolic surfaces). `coneAngle = angle f / 2`, `f` the
  lifted holonomy of any lifted developing pair: `ℓ(p)` is developed through the double cover
  `linkCover` (one turn is `δ²`), so the link's real angle is twice the cone angle (OQ-113 (a)/(b),
  `…coneAngle_eq_half`) and a regular point has `2π`. The geometric angle (`2π` times the turns of
  `ℓ(p)` per period) does not depend on the normalisation; `< 2π` is `f < δ²`, i.e. N9's
  `P̃ y < δ y` in the visual lift (`GX.SingKind.IsPositive`, `GXScaffold.Interaction.FunnelGTilde`).
* **(b) « Singularity ».** l.948–953 does not ask the points of `𝒮` to be singular, and
  `𝔢(ℓ(p)) = HS²` (`regular_susp`) models a regular point, of cone angle exactly `2π` at a
  time-like `p`. The time-like clause is read for non-regular links (`IsRegular`); regular links
  satisfy the two others (`IsRegular.isPositive`). A finding (the literal clause would make every
  `𝒮` containing a regular time-like point non-positive).
* **(c) Trivial holonomy.** With l.915's form for every decomposition, a space-like or light-like
  circle with `g = 1` and degree `2k ≥ 4` (the cyclic covers of `ℓ(p)`; built for `δ⁴`,
  `GX.exists_isPositive_delta_four`) is positive, while l.906–913 (repelling ends, `g` hyperbolic)
  calls it neither positive nor negative. A question; causality (l.1114) excludes degree `≥ 4`.
* **(d) The link at `p̄`.** A point `x ∈ 𝒮` is read at the apex `p̄` (l.782–783): `IsApexLink`,
  an HS-isomorphism (`SingularHSStructure.IsIso`, OQ-126 (b)) of a neighbourhood of `x` into `𝔢(L)`
  sending `x` to height `0`. The strict `IsSingularHSSurface` allows either apex; the link at `−p̄`
  is `bbsrem:p_p`'s (T-bbs-p-p).
* **(e) Some link or every link.** `IsPositive`: some positive link at `p̄`; `IsPositiveEvery`:
  every link at `p̄` positive. They agree if the type of an HS-singularity is well defined (l.785
  « mutually non isomorphic », l.850–853), not formalized; `IsPositiveEvery ∧ HasApexLinks →
  IsPositive` is proved. Positivity is invariant under isomorphisms of circles with the same `p`.
* **(f) Lines and interactions.** No AdS spacetime here. A singular line of type `L` is positive
  when `L` is. Through `𝔢(L)` (as l.1117 reads causality): `L` positive gives a positive `p̄`, and
  `𝔢(L)` positive (every link) gives `L` positive. « `𝔢(L)` positive iff `L` is » also needs the
  link at `−p̄` (`bbsrem:p_p`) and (e): not formalized. An interaction is positive when `Σ_x` is.
* **(g) Not formalized:** invariance under HS-isomorphisms moving `p` (OQ-120 (a)); the form of
  l.908–913.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.HSSuspension`.
-/

noncomputable section

open Set Filter Topology Real

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. The cone angle, and the regular link -/

section Circle

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L} {θ : TpHS C.pt ≃ₗ[ℝ] ℂ}
  {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}

/-- **The cone angle** of the HS-singularity `p̄` of `𝔢(L)` (l.804–806, l.863–864; « cone angle »,
l.1510–1511): half the real angle (`GX.GTilde.angle`, `angle δ = 2π`) of the lifted holonomy of a
lifted developing pair, `θ` oriented. Independent of the choices (`coneAngle_eq`); half, because
`ℓ(p)` is developed through the double cover `GX.linkCover`, one turn being `δ²` (OQ-113 (a)/(b)),
so that a regular point has cone angle `2π` (`coneAngle_regular`). -/
def GammaLinkCircle.coneAngle (C : GammaLinkCircle L) : ℝ :=
  GTilde.angle (C.exists_isLiftedDev
    (exists_isOrientedTangent C.pt).choose).choose_spec.choose_spec.choose / 2

/-- The cone angle is half the real angle of **every** lifted developing pair (`θ` oriented). -/
theorem GammaLinkCircle.coneAngle_eq (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) : C.coneAngle = GTilde.angle f / 2 := by
  have h₀ := (C.exists_isLiftedDev
    (exists_isOrientedTangent C.pt).choose).choose_spec.choose_spec.choose_spec
  obtain ⟨-, -, hf⟩ :=
    (h₀.relate (exists_isOrientedTangent C.pt).choose_spec hθ h).choose_spec.choose_spec
  rw [GammaLinkCircle.coneAngle, hf, GTilde.angle_conj]

/-- **« A link's angle is twice the cone angle »** (OQ-113 (a)): `Θ` the real angle of the
underlying `ℝP¹`-circle (`GX.HasRealAngle`, `θ` oriented), the cone angle is `Θ / 2`. -/
theorem GammaLinkCircle.coneAngle_eq_half (hθ : IsOrientedTangent C.pt θ) {Θ : ℝ}
    (hΘ : letI := C.rp1ChartedSpace θ; HasRealAngle L Θ) : C.coneAngle = Θ / 2 := by
  letI := C.rp1ChartedSpace θ
  haveI := C.rp1_hasGroupoid θ
  obtain ⟨E, D, f, h⟩ := C.exists_isLiftedDev θ
  have h1 : HasRealAngle L (GTilde.angle f) := ⟨f, ⟨E, D, h.isLiftedDevPair⟩, rfl⟩
  rw [GammaLinkCircle.coneAngle_eq hθ h, hΘ.unique h1]

/-- **Cone angle `< 2π` is `f < δ²`** (normalisation-free): `f t < t + 2` for every `t ∈ ℝP̃¹`,
`f` the lifted holonomy of any lifted developing pair. -/
theorem GammaLinkCircle.coneAngle_lt_two_pi_iff (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) : C.coneAngle < 2 * π ↔ ∀ t, f t < t + 2 := by
  rw [GammaLinkCircle.coneAngle_eq hθ h, GTilde.angle]
  constructor
  · intro hlt t
    have hτ : CircleDeg1Lift.translationNumber ((f : CircleDeg1Liftˣ) : CircleDeg1Lift) <
        ((2 : ℤ) : ℝ) := by
      push_cast
      nlinarith [Real.pi_pos]
    have := CircleDeg1Lift.map_lt_of_translationNumber_lt_int
      ((f : CircleDeg1Liftˣ) : CircleDeg1Lift) hτ t
    push_cast at this
    exact this
  · intro hlt
    have := CircleDeg1Lift.translationNumber_lt_of_forall_lt_add
      ((f : CircleDeg1Liftˣ) : CircleDeg1Lift) (GTilde.continuous f) (z := 2) hlt
    nlinarith [Real.pi_pos]

/-- The cone angle of a time-like singularity is positive (its holonomy is elliptic or central,
`GX.GammaLinkCircle.IsLiftedDev.isElliptic_of_timelike`). -/
theorem GammaLinkCircle.coneAngle_pos_of_timelike (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) :
    0 < C.coneAngle := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent C.pt
  obtain ⟨E, D, f, h⟩ := C.exists_isLiftedDev θ
  rw [GammaLinkCircle.coneAngle_eq hθ h]
  have hfix : ∀ x, f x ≠ x := fun x hx => by
    rcases h.isElliptic_of_timelike hp with he | he
    · exact he.apply_ne x hx
    · have hk : f ∈ GTilde.toPSL.ker := he
      rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hk
      obtain ⟨n, rfl⟩ := hk
      have h0 := h.lt_apply 0
      rw [GTilde.delta_zpow_apply] at hx h0
      have hn : (n : ℝ) = 0 := by linarith
      rw [hn] at h0
      linarith
  have := GTilde.angle_pos_of_forall_ne hfix (h.lt_apply 0)
  positivity

/-- **`C` is the link of a regular point**: `(Γ_p, ℓ(p))`-isomorphic (`GX.GammaLinkCircle.IsIso`)
to `ℓ(p)` itself (`GX.GammaLinkCircle.regular`, `𝔢(ℓ(p)) = HS²` by
`GX.GammaLinkCircle.DevData.regular_susp`). A point of `𝒮` whose link is not regular is a
**singularity** (SCOPE (b)). -/
def GammaLinkCircle.IsRegular (C : GammaLinkCircle L) : Prop :=
  ∃ φ : L ≃ₜ Link C.pt, C.IsIso (GammaLinkCircle.regular C.pt) φ

/-- `angle δ² = 4π`. -/
private theorem angle_delta_sq' : GTilde.angle (GTilde.delta ^ 2) = 4 * π := by
  have := GTilde.angle_delta_zpow 2
  rw [zpow_ofNat] at this
  rw [this]
  push_cast
  ring

/-- `ℓ(p)` is regular. -/
theorem GammaLinkCircle.isRegular_regular (p : HS 2) : (GammaLinkCircle.regular p).IsRegular := by
  letI := (GammaLinkCircle.regular p).atlas
  exact ⟨Homeomorph.refl _, rfl, isGXMorphism_id⟩

/-- An isomorphism onto `ℓ(p)` carries lifted developing pairs. -/
theorem GammaLinkCircle.IsIso.isLiftedDev_regular {φ : L ≃ₜ Link C.pt}
    (hφ : C.IsIso (GammaLinkCircle.regular C.pt) φ) (h : C.IsLiftedDev θ E D f) :
    (GammaLinkCircle.regular C.pt).IsLiftedDev θ (φ ∘ E) D f := by
  obtain ⟨_, hmor⟩ := hφ
  letI := C.atlas
  have hmor' : IsGXMorphism (GammaP C.pt) (Link C.pt) φ := hmor
  obtain ⟨hE, hDc, hDm, hd, hDf⟩ := h
  refine ⟨⟨hE.isCoveringMap.homeomorph_comp φ, φ.surjective.comp hE.surjective,
    fun s => by simp only [Function.comp_apply, hE.add_one],
    fun s t h => hE.fiber s t (φ.injective h)⟩, hDc, hDm, fun s => ?_, hDf⟩
  obtain ⟨A₁, h₁⟩ := hd s
  obtain ⟨A₂, h₂⟩ := hmor'.exists_smul_eq (E s)
  refine ⟨A₁ * A₂⁻¹, ?_⟩
  filter_upwards [h₁, hE.isCoveringMap.continuous.continuousAt.eventually h₂] with s' hs1 hs2
  show (linkCover C.pt θ ∘ D) s' = (A₁ * A₂⁻¹) • chartAt (Link C.pt) (φ (E s)) (φ (E s'))
  rw [hs2, mul_smul, inv_smul_smul, hs1]

/-- **A regular link has lifted holonomy `δ²`** (for every lifted developing pair, `θ` oriented). -/
theorem GammaLinkCircle.IsRegular.eq_delta_sq (hC : C.IsRegular) (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) : f = GTilde.delta ^ 2 := by
  obtain ⟨φ, hφ⟩ := hC
  have h' := hφ.isLiftedDev_regular h
  obtain ⟨E₀, D₀, h₀, -⟩ := regular_not_isHyperbolic θ
  obtain ⟨-, κ, -, -, hf⟩ :=
    GammaLinkCircle.IsLiftedDev.relate (C := GammaLinkCircle.regular C.pt) hθ hθ h₀ h'
  have hc : κ * GTilde.delta ^ 2 = GTilde.delta ^ 2 * κ :=
    (Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ GTilde.delta_mem_center 2)) κ
  rw [hf, hc, mul_inv_cancel_right]

/-- A regular link has degree `2` and trivial factor: `f = δ² · 1`. -/
theorem GammaLinkCircle.IsRegular.factor_eq (hC : C.IsRegular) (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) {k : ℤ} {g : GTilde} (hg : ∃ x, g x = x)
    (hfg : f = GTilde.delta ^ k * g) : k = 2 ∧ g = 1 := by
  have e : GTilde.delta ^ k * g = GTilde.delta ^ (2 : ℤ) * 1 := by
    rw [← hfg, hC.eq_delta_sq hθ h, mul_one, zpow_ofNat]
  have hk := GTilde.delta_zpow_mul_unique hg ⟨0, GTilde.one_apply 0⟩ e
  subst hk
  exact ⟨rfl, mul_left_cancel e⟩

/-- **A regular point has cone angle `2π`** (the normalisation of `coneAngle`). -/
theorem GammaLinkCircle.coneAngle_regular (p : HS 2) :
    (GammaLinkCircle.regular p).coneAngle = 2 * π := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent p
  obtain ⟨E, D, h, -⟩ := regular_not_isHyperbolic θ
  rw [GammaLinkCircle.coneAngle_eq (C := GammaLinkCircle.regular p) hθ h, angle_delta_sq']
  ring

/-- Every regular link has cone angle `2π`. -/
theorem GammaLinkCircle.IsRegular.coneAngle_eq (hC : C.IsRegular) : C.coneAngle = 2 * π := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent C.pt
  obtain ⟨E, D, f, h⟩ := C.exists_isLiftedDev θ
  rw [GammaLinkCircle.coneAngle_eq hθ h, hC.eq_delta_sq hθ h, angle_delta_sq']
  ring

/-! ## 2. Positive `(Γ_p, ℓ(p))`-circles: positive HS-singularities and singular lines -/

/-- **A positive HS-singularity** (`bbsdef:hs_surface_interaction_singular_line`, l.1508–1512,
for the singularity `p̄` of `𝔢(L)`), equivalently **a positive singular line** of type `L` (the type
of a singular line is its circle, l.983–985; SCOPE (f)):
* a time-like singularity (`p ∈ ℍ²±`, not regular) has cone angle `< 2π`;
* a space-like singularity (`p ∈ dS²`) of degree `k ≥ 2` is positive in the form of l.915:
  `g x ≥ x` on `I⁺ = D(E⁻¹ i⁺(L))`, `f = δᵏ g`, `g` with a fixed point (OQ-120 (c));
* a light-like singularity (`p ∈ ∂ℍ²±`) of degree `k ≥ 2` is positive (l.919–920): `g x ≥ x` on
  `ℝP̃¹`.
The last two are read for **every** lifted developing pair (`θ` oriented) and every decomposition;
for `g` hyperbolic, resp. parabolic, they are `GX.GammaLinkCircle.IsSpacelikePositive`,
resp. `…IsLightlikePositive` (`isPositive_iff_of_deSitter`, `isPositive_iff_of_null`). -/
structure GammaLinkCircle.IsPositive (C : GammaLinkCircle L) : Prop where
  /-- time-like singularities have cone angle `< 2π` -/
  timelike : Causal.Flat.minkQ (C.pt : 𝕄) < 0 → ¬ C.IsRegular → C.coneAngle < 2 * π
  /-- space-like singularities of degree `≥ 2` are positive (l.915) -/
  spacelike : C.pt ∈ HS.piece 2 .deSitter → ∀ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ →
    ∀ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde), C.IsLiftedDev θ E D f → ∀ (k : ℤ) (g : GTilde),
      (∃ x, g x = x) → f = GTilde.delta ^ k * g → 2 ≤ k → ∀ s, E s ∈ C.iPlusL → D s ≤ g (D s)
  /-- light-like singularities of degree `≥ 2` are positive (l.919–920) -/
  lightlike : Causal.Flat.minkQ (C.pt : 𝕄) = 0 → ∀ θ : TpHS C.pt ≃ₗ[ℝ] ℂ,
    IsOrientedTangent C.pt θ → ∀ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde), C.IsLiftedDev θ E D f →
      ∀ (k : ℤ) (g : GTilde), (∃ x, g x = x) → f = GTilde.delta ^ k * g → 2 ≤ k → ∀ x, x ≤ g x

/-- **A regular link is positive** (it is no singularity; it satisfies the space-like and
light-like clauses with `g = 1`). -/
theorem GammaLinkCircle.IsRegular.isPositive (hC : C.IsRegular) : C.IsPositive := by
  refine ⟨fun _ hreg => absurd hC hreg, fun _ θ hθ E D f h k g hg hfg _ s _ => ?_,
    fun _ θ hθ E D f h k g hg hfg _ x => ?_⟩
  · obtain ⟨-, rfl⟩ := hC.factor_eq hθ h hg hfg
    rw [GTilde.one_apply]
  · obtain ⟨-, rfl⟩ := hC.factor_eq hθ h hg hfg
    rw [GTilde.one_apply]

/-- `ℓ(p)` is positive. -/
theorem GammaLinkCircle.isPositive_regular (p : HS 2) : (GammaLinkCircle.regular p).IsPositive :=
  (GammaLinkCircle.isRegular_regular p).isPositive

/-- A positive space-like circle of degree `k ≥ 1` with `g` hyperbolic is positive in the sense of
`GX.GammaLinkCircle.IsSpacelikePositive` (`k` is even, `…even_of_nonneg`, so `k ≥ 2`). -/
theorem GammaLinkCircle.IsPositive.isSpacelikePositive (hC : C.IsPositive)
    (hp : C.pt ∈ HS.piece 2 .deSitter) (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) {k : ℤ} (hk : 1 ≤ k) {g : GTilde} (hg : ∃ x, g x = x)
    (hh : GTilde.IsHyperbolic g) (hfg : f = GTilde.delta ^ k * g) : C.IsSpacelikePositive := by
  have hq : 0 < Causal.Flat.minkQ (C.pt : 𝕄) := hp
  obtain ⟨m, hm⟩ := h.even_of_nonneg hq.le hg hfg
  exact ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
    hC.spacelike hp θ hθ E D f h k g hg hfg (by omega)⟩

/-- A positive space-like circle (`GX.GammaLinkCircle.IsSpacelikePositive`) is positive. -/
theorem GammaLinkCircle.IsSpacelikePositive.isPositive (hC : C.IsSpacelikePositive) :
    C.IsPositive := by
  have hq : 0 < Causal.Flat.minkQ (C.pt : 𝕄) := hC.1
  exact ⟨fun h => absurd h (not_lt.2 hq.le),
    fun _ θ hθ E D f h k g hg hfg _ => hC.forall hθ h hg hfg, fun h => absurd h hq.ne'⟩

/-- **Light-like positivity does not depend on the choices**: if `C` is positive, every lifted
developing pair (`θ` oriented) and every decomposition `f = δᵏ g` satisfy `g x ≥ x`. -/
theorem GammaLinkCircle.IsLightlikePositive.le_apply_of_isLiftedDev (hC : C.IsLightlikePositive)
    (hθ : IsOrientedTangent C.pt θ) (h : C.IsLiftedDev θ E D f) {k : ℤ} {g : GTilde}
    (hg : ∃ x, g x = x) (hfg : f = GTilde.delta ^ k * g) (x : ℝ) : x ≤ g x := by
  obtain ⟨-, θ₁, hθ₁, E₁, D₁, f₁, k₁, g₁, h₁, -, hg₁, -, hfg₁, hle₁⟩ := hC
  obtain ⟨-, κ, -, -, hf⟩ := h₁.relate hθ₁ hθ h
  rw [GTilde.conj_factor hg₁ hg hfg₁ hfg hf]
  exact GTilde.le_conj_apply hle₁ κ x

/-- A positive light-like circle of degree `k ≥ 1` with `g` parabolic is positive in the sense of
`GX.GammaLinkCircle.IsLightlikePositive`. -/
theorem GammaLinkCircle.IsPositive.isLightlikePositive (hC : C.IsPositive)
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) = 0) (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) {k : ℤ} (hk : 1 ≤ k) {g : GTilde} (hg : ∃ x, g x = x)
    (hpar : GTilde.IsParabolic g) (hfg : f = GTilde.delta ^ k * g) : C.IsLightlikePositive := by
  obtain ⟨m, hm⟩ := h.even_of_nonneg hp.ge hg hfg
  exact ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hpar, hfg,
    hC.lightlike hp θ hθ E D f h k g hg hfg (by omega)⟩

/-- A positive light-like circle (`GX.GammaLinkCircle.IsLightlikePositive`) is positive. -/
theorem GammaLinkCircle.IsLightlikePositive.isPositive (hC : C.IsLightlikePositive) :
    C.IsPositive := by
  have hp : Causal.Flat.minkQ (C.pt : 𝕄) = 0 := hC.1
  exact ⟨fun h => absurd hp h.ne,
    fun h => absurd hp (show (0 : ℝ) < Causal.Flat.minkQ (C.pt : 𝕄) from h).ne',
    fun _ θ hθ E D f h k g hg hfg _ x => hC.le_apply_of_isLiftedDev hθ h hg hfg x⟩

/-- **Time-like**: a time-like singularity is positive iff its cone angle is `< 2π`. -/
theorem GammaLinkCircle.isPositive_iff_of_timelike (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0)
    (hreg : ¬ C.IsRegular) : C.IsPositive ↔ C.coneAngle < 2 * π := by
  refine ⟨fun hC => hC.timelike hp hreg, fun h => ⟨fun _ _ => h, fun hd => ?_, fun h0 => ?_⟩⟩
  · exact absurd (show (0 : ℝ) < Causal.Flat.minkQ (C.pt : 𝕄) from hd) (not_lt.2 hp.le)
  · exact absurd h0 hp.ne

/-- **Space-like** (a tachyon, l.1484–1487): a space-like circle of degree `≥ 1` with hyperbolic
`g` is positive iff it is a positive space-like singularity in the sense of l.906–915. -/
theorem GammaLinkCircle.isPositive_iff_of_deSitter (hp : C.pt ∈ HS.piece 2 .deSitter)
    (hθ : IsOrientedTangent C.pt θ) (h : C.IsLiftedDev θ E D f) {k : ℤ} (hk : 1 ≤ k)
    {g : GTilde} (hg : ∃ x, g x = x) (hh : GTilde.IsHyperbolic g)
    (hfg : f = GTilde.delta ^ k * g) : C.IsPositive ↔ C.IsSpacelikePositive := by
  exact ⟨fun hC => hC.isSpacelikePositive hp hθ h hk hg hh hfg, fun hC => hC.isPositive⟩

/-- **Light-like** (a photon, l.1457–1461): a light-like circle of degree `≥ 1` with parabolic `g`
is positive iff it is a positive light-like singularity (l.917–922). -/
theorem GammaLinkCircle.isPositive_iff_of_null (hp : Causal.Flat.minkQ (C.pt : 𝕄) = 0)
    (hθ : IsOrientedTangent C.pt θ) (h : C.IsLiftedDev θ E D f) {k : ℤ} (hk : 1 ≤ k)
    {g : GTilde} (hg : ∃ x, g x = x) (hpar : GTilde.IsParabolic g)
    (hfg : f = GTilde.delta ^ k * g) : C.IsPositive ↔ C.IsLightlikePositive := by
  exact ⟨fun hC => hC.isLightlikePositive hp hθ h hk hg hpar hfg, fun hC => hC.isPositive⟩

/-- A positive tachyon is a singularity (not regular). -/
theorem GammaLinkCircle.IsSpacelikePositive.not_isRegular (hC : C.IsSpacelikePositive) :
    ¬ C.IsRegular := by
  intro hreg
  obtain ⟨-, θ, hθ, E, D, f, k, g, h, -, hg, hh, hfg, -⟩ := hC
  obtain ⟨-, rfl⟩ := hreg.factor_eq hθ h hg hfg
  exact hh.toPSL_ne_one (map_one _)

/-- **A negative tachyon is not positive** (through the dichotomy,
`GX.not_isIso_of_positive_of_negative`). -/
theorem GammaLinkCircle.IsSpacelikeNegative.not_isPositive (hC : C.IsSpacelikeNegative) :
    ¬ C.IsPositive := by
  intro hpos
  have hpos' : C.IsSpacelikePositive := by
    obtain ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, -⟩ := hC
    exact hpos.isSpacelikePositive hp hθ h hk hg hh hfg
  exact not_isIso_of_positive_of_negative hpos' hC (Homeomorph.refl L)
    ⟨rfl, by letI := C.atlas; exact isGXMorphism_id⟩

/-- **Non-vacuity**: at every `p ∈ dS²`, a positive non-regular circle and a non-positive one
(the degree-`2` tachyons of `GX.exists_positive_negative`). -/
theorem exists_isPositive_and_not_isPositive {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L L' : Type) (_ : TopologicalSpace L) (_ : TopologicalSpace L') (C : GammaLinkCircle L)
      (C' : GammaLinkCircle L'), C.pt = p ∧ C'.pt = p ∧ C.IsPositive ∧ ¬ C.IsRegular ∧
        ¬ C'.IsPositive := by
  obtain ⟨L, L', _, _, C, C', hC, hC', hpos, hneg, -⟩ := exists_positive_negative hp
  exact ⟨L, L', inferInstance, inferInstance, C, C', hC, hC', hpos.isPositive, hpos.not_isRegular,
    hneg.not_isPositive⟩

/-- **Positivity beyond the dichotomy of l.906–915**: at every `p ∈ dS²` there is a non-regular
space-like `(Γ_p, ℓ(p))`-circle of degree `4` with trivial `Γ_p`-holonomy (the 2-fold cyclic cover
of `ℓ(p)`, lifted holonomy `δ⁴`, so `g = 1`). It is positive in l.915's form (`g x ≥ x` with
equality), and it is neither positive nor negative in the hyperbolic sense of l.906–913
(`GX.GammaLinkCircle.IsSpacelikePositive`, `…Negative`), which needs `g` hyperbolic. Its
underlying `ℝP¹`-circle is not hyperbolic (`δ⁴` is central): a *singular* space-like point for which
l.794–795 (« `L` is a hyperbolic `ℝP¹`-circle ») fails. -/
theorem exists_isPositive_delta_four {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), C.pt = p ∧ C.IsPositive ∧
      ¬ C.IsRegular ∧ ¬ C.IsSpacelikePositive ∧ ¬ C.IsSpacelikeNegative ∧
      ¬ GTilde.IsHyperbolic (GTilde.delta ^ (4 : ℤ)) ∧
      ∃ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L) (D : ℝ → ℝ), IsOrientedTangent C.pt θ ∧
        C.IsLiftedDev θ E D (GTilde.delta ^ (4 : ℤ)) := by
  have hq : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent p
  have hlt : ∀ x, x < (GTilde.delta ^ (4 : ℤ)) x := fun x => by
    rw [GTilde.delta_zpow_apply]; push_cast; linarith
  have hDf : ∀ x, linkCover p θ ((GTilde.delta ^ (4 : ℤ)) x) = (1 : GammaP p) • linkCover p θ x :=
    fun x => by
      rw [GTilde.delta_zpow_apply, one_smul,
        show x + ((4 : ℤ) : ℝ) = x + 2 * ((2 : ℤ) : ℝ) by push_cast; ring, linkCover_add_two_mul]
  obtain ⟨L, _, cs, hcs, hL, E, ψ, hE, hψc, hψm, hψf, hdev⟩ :=
    exists_gammaLinkCircle_quotient_of_forall_lt p
      (isCoveringMap_linkCover p θ).isLocalHomeomorph hlt hDf
  let C : GammaLinkCircle L := GammaLinkCircle.mk p cs hcs hL
  have hθC : IsOrientedTangent C.pt θ := hθ
  have h : C.IsLiftedDev θ E ψ (GTilde.delta ^ (4 : ℤ)) := ⟨hE, hψc, hψm, hdev, hψf⟩
  -- every decomposition `f = δᵏ g` of every lifted holonomy has `k = 4`, `g = 1`
  have hfac : ∀ (θ' : TpHS C.pt ≃ₗ[ℝ] ℂ), IsOrientedTangent C.pt θ' → ∀ (E' : ℝ → L)
      (D' : ℝ → ℝ) (f' : GTilde), C.IsLiftedDev θ' E' D' f' → ∀ (k : ℤ) (g : GTilde),
      (∃ x, g x = x) → f' = GTilde.delta ^ k * g → k = 4 ∧ g = 1 := by
    intro θ' hθ' E' D' f' h' k g hg hfg
    obtain ⟨-, κ, -, -, hf⟩ := GammaLinkCircle.IsLiftedDev.relate (C := C) hθC hθ' h h'
    have hc : κ * GTilde.delta ^ (4 : ℤ) = GTilde.delta ^ (4 : ℤ) * κ :=
      (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ GTilde.delta_mem_center 4)) κ
    rw [hc, mul_inv_cancel_right] at hf
    have e : GTilde.delta ^ k * g = GTilde.delta ^ (4 : ℤ) * 1 := by rw [← hfg, hf, mul_one]
    have hk := GTilde.delta_zpow_mul_unique hg ⟨0, GTilde.one_apply 0⟩ e
    subst hk
    exact ⟨rfl, mul_left_cancel e⟩
  refine ⟨L, inferInstance, C, rfl, ⟨fun hneg => absurd hq (not_lt.2 hneg.le),
    fun _ θ' hθ' E' D' f' h' k g hg hfg _ s _ => ?_, fun h0 => absurd h0 hq.ne'⟩, fun hreg => ?_,
    fun ⟨_, θ', hθ', E', D', f', k, g, h', _, hg, hh, hfg, _⟩ => ?_,
    fun ⟨_, θ', hθ', E', D', f', k, g, h', _, hg, hh, hfg, _⟩ => ?_, fun hh => ?_, θ, E, ψ, hθC,
    h⟩
  · obtain ⟨-, rfl⟩ := hfac θ' hθ' E' D' f' h' k g hg hfg
    rw [GTilde.one_apply]
  · have e := congrArg (fun F : GTilde => F 0) (hreg.eq_delta_sq hθC h)
    have e2 := GTilde.delta_zpow_apply 2 0
    rw [zpow_ofNat] at e2
    simp only [GTilde.delta_zpow_apply] at e
    rw [e2] at e
    push_cast at e
    linarith
  · obtain ⟨-, rfl⟩ := hfac θ' hθ' E' D' f' h' k g hg hfg
    exact hh.toPSL_ne_one (map_one _)
  · obtain ⟨-, rfl⟩ := hfac θ' hθ' E' D' f' h' k g hg hfg
    exact hh.toPSL_ne_one (map_one _)
  · have : (4 : ℝ) < PSL2.trSq (GTilde.toPSL (GTilde.delta ^ (4 : ℤ))) := hh
    rw [map_zpow, GTilde.toPSL_delta, one_zpow, PSL2.trSq_one] at this
    exact lt_irrefl _ this

/-! ### Positivity is an isomorphism invariant -/

section Iso

variable {L' : Type*} [TopologicalSpace L']

/-- The inverse of a `(Γ_p, ℓ(p))`-homeomorphism is one. -/
private theorem isGXMorphism_homeomorph_symm_link {p : HS 2} [ChartedSpace (Link p) L]
    [ChartedSpace (Link p) L'] {φ : L ≃ₜ L'} (hφ : IsGXMorphism (GammaP p) (Link p) φ) :
    IsGXMorphism (GammaP p) (Link p) φ.symm := by
  refine ⟨φ.symm.continuous, fun y => ?_⟩
  obtain ⟨g, hg⟩ := hφ.exists_smul_eq (φ.symm y)
  refine ⟨g⁻¹, ?_⟩
  filter_upwards [φ.symm.continuous.continuousAt.eventually hg] with y' hy'
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at hy'
  rw [hy', inv_smul_smul]

/-- **Positivity is an isomorphism invariant** of `(Γ_p, ℓ(p))`-circles (`GX.GammaLinkCircle.IsIso`,
the same `p`, OQ-120 (a)). -/
theorem GammaLinkCircle.IsIso.isPositive {C' : GammaLinkCircle L'} {φ : L ≃ₜ L'}
    (hφ : C.IsIso C' φ) (hC : C.IsPositive) : C'.IsPositive := by
  obtain ⟨hpt, hmor⟩ := hφ
  obtain ⟨q, atl, hgr, hcirc⟩ := C'
  simp only at hpt
  subst hpt
  letI := C.atlas
  letI : ChartedSpace (Link C.pt) L' := atl
  have hmor' : IsGXMorphism (GammaP C.pt) (Link C.pt) φ := hmor
  have hinv := isGXMorphism_homeomorph_symm_link hmor'
  set C' : GammaLinkCircle L' := ⟨C.pt, atl, hgr, hcirc⟩ with hC'
  -- lifted developing pairs of `C'` are carried to `C` by `φ⁻¹`
  have htr : ∀ {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L'} {D : ℝ → ℝ} {f : GTilde},
      C'.IsLiftedDev θ E D f → C.IsLiftedDev θ (φ.symm ∘ E) D f := by
    intro θ E D f h
    obtain ⟨hE, hDc, hDm, hd, hDf⟩ := h
    refine ⟨⟨hE.isCoveringMap.homeomorph_comp φ.symm, φ.symm.surjective.comp hE.surjective,
      fun s => by simp only [Function.comp_apply, hE.add_one],
      fun s t h => hE.fiber s t (φ.symm.injective h)⟩, hDc, hDm, fun s => ?_, hDf⟩
    obtain ⟨A₁, h₁⟩ := hd s
    obtain ⟨A₂, h₂⟩ := hinv.exists_smul_eq (E s)
    refine ⟨A₁ * A₂⁻¹, ?_⟩
    filter_upwards [h₁, hE.isCoveringMap.continuous.continuousAt.eventually h₂] with s' hs1 hs2
    show (linkCover C.pt θ ∘ D) s' =
      (A₁ * A₂⁻¹) • chartAt (Link C.pt) (φ.symm (E s)) (φ.symm (E s'))
    rw [hs2, mul_smul, inv_smul_smul, hs1]
  -- and `i⁺(L')` to `i⁺(L)`
  have hiP : ∀ y : L', y ∈ C'.iPlusL → φ.symm y ∈ C.iPlusL := fun y hy => by
    obtain ⟨A, hA⟩ := hinv.exists_smul_eq y
    have e := hA.self_of_nhds
    show chartAt (Link C.pt) (φ.symm y) (φ.symm y) ∈ iPlus C.pt
    rw [e, smul_mem_iPlus_iff]
    exact hy
  refine ⟨fun hp hreg => ?_, fun hp θ hθ E D f h k g hg hfg hk s hs =>
    hC.spacelike hp θ hθ _ D f (htr h) k g hg hfg hk s (hiP _ hs),
    fun hp θ hθ E D f h k g hg hfg hk => hC.lightlike hp θ hθ _ D f (htr h) k g hg hfg hk⟩
  -- time-like: the same cone angle, and `C` is not regular either
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent C.pt
  obtain ⟨E, D, f, h⟩ := C'.exists_isLiftedDev θ
  have hcone : C'.coneAngle = C.coneAngle := by
    rw [GammaLinkCircle.coneAngle_eq (C := C') hθ h, GammaLinkCircle.coneAngle_eq hθ (htr h)]
  rw [hcone]
  refine hC.timelike hp fun ⟨ψ, hψ⟩ => hreg ⟨φ.symm.trans ψ, rfl, ?_⟩
  obtain ⟨_, hψm⟩ := hψ
  have hψm' : IsGXMorphism (GammaP C.pt) (Link C.pt) ψ := hψm
  exact hψm'.comp hinv

/-- Positivity is a property of the isomorphism class. -/
theorem GammaLinkCircle.IsIso.isPositive_iff {C' : GammaLinkCircle L'} {φ : L ≃ₜ L'}
    (hφ : C.IsIso C' φ) : C.IsPositive ↔ C'.IsPositive := by
  refine ⟨hφ.isPositive, fun hC' => ?_⟩
  have hsymm : C'.IsIso C φ.symm := by
    obtain ⟨hpt, hmor⟩ := hφ
    obtain ⟨q, atl, hgr, hcirc⟩ := C'
    simp only at hpt
    subst hpt
    letI := C.atlas
    letI : ChartedSpace (Link C.pt) L' := atl
    have hmor' : IsGXMorphism (GammaP C.pt) (Link C.pt) φ := hmor
    exact ⟨rfl, isGXMorphism_homeomorph_symm_link hmor'⟩
  exact hsymm.isPositive hC'

/-- A circle isomorphic to the regular link is positive. -/
theorem GammaLinkCircle.IsIso.isPositive_of_regular {p : HS 2}
    {φ : Link p ≃ₜ L} {C' : GammaLinkCircle L} (hφ : (GammaLinkCircle.regular p).IsIso C' φ) :
    C'.IsPositive :=
  hφ.isPositive (GammaLinkCircle.isPositive_regular p)

end Iso

end Circle

/-! ## 3. Positive singular HS-surfaces, and interactions -/

section Surface

variable {M : Type*} [TopologicalSpace M]

/-- `C` is **a link of `x` at the apex `p̄`** (l.951–952 read with l.782–783: « the singularity
corresponding to `p` has a preferred status, as representing a `(Γ_p, ℓ(p))`-singularity »): an
HS-isomorphism (`GX.SingularHSStructure.IsIso`) from a neighbourhood of `x` onto an open set of
`𝔢(L)` (for some developing data) sending `x` to `p̄` (height `0`). SCOPE (d). -/
def SingularHSStructure.IsApexLink (A : SingularHSStructure M) (x : M) {L : Type}
    [TopologicalSpace L] (C : GammaLinkCircle L) : Prop :=
  ∃ (Δ : C.DevData) (φ : OpenPartialHomeomorph M (BiSusp L)), x ∈ φ.source ∧
    A.IsIso Δ.suspStructure φ ∧ BiSusp.ht (φ x) = 0

/-- **The singular point `x` is positive**: it has a positive link at `p̄`. -/
def SingularHSStructure.IsPositiveAt (A : SingularHSStructure M) (x : M) : Prop :=
  ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), A.IsApexLink x C ∧ C.IsPositive

/-- **`bbsdef:hs_surface_interaction_singular_line`: a positive singular HS-surface**
(l.1508–1512), and **a positive interaction** through its HS-sphere `Σ_x` (SCOPE (f)): every point
of `𝒮` has a positive link at `p̄` (`GX.GammaLinkCircle.IsPositive`). The « every link » reading is
`IsPositiveEvery` (SCOPE (e)). -/
def SingularHSStructure.IsPositive (A : SingularHSStructure M) : Prop :=
  ∀ x ∈ A.sing, A.IsPositiveAt x

/-- **The « every link » reading**: every link at `p̄` of every point of `𝒮` is positive. It is
vacuous at a point with no link at `p̄`; with `HasApexLinks` it implies `IsPositive`
(`IsPositiveEvery.isPositive`). SCOPE (e). -/
def SingularHSStructure.IsPositiveEvery (A : SingularHSStructure M) : Prop :=
  ∀ x ∈ A.sing, ∀ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L),
    A.IsApexLink x C → C.IsPositive

/-- Every point of `𝒮` has a link at `p̄` (the reading of l.951–952 with l.782–783; the strict
`GX.IsSingularHSSurface` allows either apex). -/
def SingularHSStructure.HasApexLinks (A : SingularHSStructure M) : Prop :=
  ∀ x ∈ A.sing, ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), A.IsApexLink x C

/-- A positive structure has links at `p̄`. -/
theorem SingularHSStructure.IsPositive.hasApexLinks {A : SingularHSStructure M}
    (hA : A.IsPositive) : A.HasApexLinks := by
  intro x hx
  obtain ⟨L, _, C, hL, -⟩ := hA x hx
  exact ⟨L, inferInstance, C, hL⟩

/-- **The two readings**: « every link » and the existence of links give « some link ». -/
theorem SingularHSStructure.IsPositiveEvery.isPositive {A : SingularHSStructure M}
    (hA : A.IsPositiveEvery) (hL : A.HasApexLinks) : A.IsPositive := by
  intro x hx
  obtain ⟨L, _, C, hC⟩ := hL x hx
  exact ⟨L, inferInstance, C, hC, hA x hx L inferInstance C hC⟩

/-- **A (regular) HS-surface is positive** (no singular point). -/
theorem SingularHSStructure.isPositive_ofHSSurface (M : Type*) [TopologicalSpace M]
    [ChartedSpace (HS 2) M] [IsHSSurface M] : (SingularHSStructure.ofHSSurface M).IsPositive := by
  exact fun x hx => absurd hx (notMem_empty x)

/-- A (regular) HS-surface is positive in the « every link » reading. -/
theorem SingularHSStructure.isPositiveEvery_ofHSSurface (M : Type*) [TopologicalSpace M]
    [ChartedSpace (HS 2) M] [IsHSSurface M] :
    (SingularHSStructure.ofHSSurface M).IsPositiveEvery := by
  exact fun x hx => absurd hx (notMem_empty x)

/-- `L` is a link of `p̄` in `𝔢(L)` (the identity). -/
theorem GammaLinkCircle.DevData.isApexLink_north {L : Type} [TopologicalSpace L]
    {C : GammaLinkCircle L} (Δ : C.DevData) :
    haveI := C.nonempty
    Δ.suspStructure.IsApexLink (BiSusp.north L) C := by
  haveI := C.nonempty
  exact ⟨Δ, OpenPartialHomeomorph.refl _, trivial, Δ.suspStructure.isIso_refl, rfl⟩

/-- **A positive singular line has a positive apex**: if `L` is positive, `p̄` is a positive
singular point of `𝔢(L)`. -/
theorem GammaLinkCircle.DevData.isPositiveAt_north {L : Type} [TopologicalSpace L]
    {C : GammaLinkCircle L} (Δ : C.DevData) (hC : C.IsPositive) :
    haveI := C.nonempty
    Δ.suspStructure.IsPositiveAt (BiSusp.north L) := by
  haveI := C.nonempty
  exact ⟨L, inferInstance, C, Δ.isApexLink_north, hC⟩

/-- **Positivity of `𝔢(L)` gives positivity of `L`** (« every link » reading, at `p̄`). -/
theorem GammaLinkCircle.DevData.isPositive_of_isPositiveEvery {L : Type} [TopologicalSpace L]
    {C : GammaLinkCircle L} (Δ : C.DevData) (h : Δ.suspStructure.IsPositiveEvery) :
    C.IsPositive := by
  haveI := C.nonempty
  have hN : BiSusp.north L ∈ Δ.suspStructure.sing := Or.inl rfl
  exact h _ hN L inferInstance C Δ.isApexLink_north

/-- **Non-vacuity**: at every `p ∈ dS²`, a singular HS-sphere `𝔢(L)` which is not positive (`L` the
negative tachyon of `GX.exists_positive_negative`). -/
theorem exists_not_isPositiveEvery {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L) (Δ : C.DevData),
      C.pt = p ∧ ¬ Δ.suspStructure.IsPositiveEvery := by
  obtain ⟨L, L', _, _, C, C', hC, hC', hpos, hneg, -⟩ := exists_positive_negative hp
  obtain ⟨Δ⟩ := C'.nonempty_devData
  exact ⟨L', inferInstance, C', Δ, hC',
    fun h => hneg.not_isPositive (Δ.isPositive_of_isPositiveEvery h)⟩

/-! ## 4. An inhabitant: `𝔢(L) ∖ {−p̄}`, a singular HS-surface with the one singularity `p̄` -/

/-- An open subset of a topological surface is a topological surface. -/
theorem IsTopologicalSurface.ofOpens (hM : IsTopologicalSurface M)
    (U : TopologicalSpace.Opens M) : IsTopologicalSurface U := by
  haveI := hM.t2Space
  refine ⟨inferInstance, fun x => ?_⟩
  obtain ⟨e, he⟩ := hM.exists_chart x
  exact ⟨e.subtypeRestr ⟨x⟩, by rw [OpenPartialHomeomorph.subtypeRestr_source]; exact he⟩

/-- **The restriction of a singular HS-structure to an open set `U`**: singular set `𝒮 ∩ U`,
charts the restrictions of the charts of `Σ`. -/
def SingularHSStructure.restrictTo (A : SingularHSStructure M) (U : TopologicalSpace.Opens M) :
    SingularHSStructure U where
  sing := Subtype.val ⁻¹' A.sing
  atlas := {f | ∃ e ∈ A.atlas, ∃ h : Nonempty U, f = e.subtypeRestr h}
  compatible := by
    rintro _ ⟨e, he, h, rfl⟩ _ ⟨e', he', h', rfl⟩
    refine symm_trans_mem_gxGroupoid fun x hx => ?_
    have hx1 : (x : M) ∈ e.source := by
      have := hx.1
      rwa [OpenPartialHomeomorph.subtypeRestr_source] at this
    have hx2 : (x : M) ∈ e'.source := by
      have := hx.2
      rwa [OpenPartialHomeomorph.subtypeRestr_source] at this
    obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid (A.compatible e he e' he') hx1 hx2
    exact ⟨g, continuous_subtype_val.continuousAt.eventually hg⟩
  support_eq := by
    ext x
    rw [mem_support]
    constructor
    · rintro ⟨_, ⟨e, he, h, rfl⟩, hx⟩
      rw [OpenPartialHomeomorph.subtypeRestr_source] at hx
      have : (x : M) ∈ support A.atlas := mem_support.2 ⟨e, he, hx⟩
      rw [A.support_eq] at this
      exact this
    · intro hx
      obtain ⟨e, he, hxe⟩ := A.exists_chart hx
      exact ⟨e.subtypeRestr ⟨x⟩, ⟨e, he, ⟨x⟩, rfl⟩,
        by rw [OpenPartialHomeomorph.subtypeRestr_source]; exact hxe⟩

/-- **The inclusion `U → Σ` is an HS-isomorphism** of the restricted structure onto its image. -/
theorem SingularHSStructure.isIso_restrictTo (A : SingularHSStructure M)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (A.restrictTo U).IsIso A (U.openPartialHomeomorphSubtypeCoe hU) := by
  refine ⟨fun x _ => Iff.rfl, fun x _ _ e he hxe e' he' hxe' => ?_⟩
  obtain ⟨e₀, he₀, h, rfl⟩ := he
  rw [OpenPartialHomeomorph.subtypeRestr_source] at hxe
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid (A.compatible e₀ he₀ e' he') hxe hxe'
  exact ⟨g, continuous_subtype_val.continuousAt.eventually hg⟩

/-- `𝔢(L) ∖ {−p̄}`: the points of height `≠ π`. -/
def BiSusp.offSouth (S : Type*) [TopologicalSpace S] : TopologicalSpace.Opens (BiSusp S) :=
  ⟨{x | BiSusp.ht x ≠ π}, isOpen_ne_fun BiSusp.continuous_ht continuous_const⟩

/-- In `𝔢(L) ∖ {−p̄}`, every singular point is linked at `p̄` by `L` itself. -/
theorem GammaLinkCircle.DevData.isApexLink_offSouth {L : Type} [TopologicalSpace L]
    {C : GammaLinkCircle L} (Δ : C.DevData) {x : BiSusp.offSouth L}
    (hx : x ∈ (Δ.suspStructure.restrictTo (BiSusp.offSouth L)).sing) :
    (Δ.suspStructure.restrictTo (BiSusp.offSouth L)).IsApexLink x C := by
  have hU : Nonempty (BiSusp.offSouth L) := ⟨x⟩
  refine ⟨Δ, (BiSusp.offSouth L).openPartialHomeomorphSubtypeCoe hU, trivial,
    Δ.suspStructure.isIso_restrictTo _ hU, ?_⟩
  show BiSusp.ht (x : BiSusp L) = 0
  rcases hx with h | h
  · exact h
  · exact absurd h x.2

/-- **`𝔢(L) ∖ {−p̄}` is a singular HS-surface**, whose singular set is `{p̄}`. -/
theorem GammaLinkCircle.DevData.isSingularHSSurface_offSouth {L : Type} [TopologicalSpace L]
    {C : GammaLinkCircle L} (Δ : C.DevData) :
    IsSingularHSSurface (BiSusp.offSouth L) (Δ.suspStructure.restrictTo (BiSusp.offSouth L)) := by
  haveI : Nonempty L := C.nonempty
  haveI := C.t2Space_susp
  refine ⟨C.isTopologicalSurface_susp.ofOpens _, ?_, fun x hx => ?_⟩
  · have hfin : (BiSusp.poles L).Finite := by
      rw [BiSusp.poles_eq]
      exact Set.toFinite _
    have hfin' : (Subtype.val ⁻¹' BiSusp.poles L : Set (BiSusp.offSouth L)).Finite :=
      hfin.preimage Subtype.val_injective.injOn
    haveI := hfin'.to_subtype
    show DiscreteTopology (Subtype.val ⁻¹' BiSusp.poles L : Set (BiSusp.offSouth L))
    infer_instance
  · obtain ⟨Δ', φ, hxφ, hiso, -⟩ := Δ.isApexLink_offSouth hx
    exact ⟨L, inferInstance, C, Δ', φ, hxφ, hiso⟩

/-- The apex `p̄` is a point of `𝔢(L) ∖ {−p̄}`, and it is singular there. -/
theorem GammaLinkCircle.DevData.north_mem_sing_offSouth {L : Type} [TopologicalSpace L]
    {C : GammaLinkCircle L} (Δ : C.DevData) :
    haveI : Nonempty L := C.nonempty
    ∃ hN : BiSusp.north L ∈ BiSusp.offSouth L,
      (⟨BiSusp.north L, hN⟩ : BiSusp.offSouth L) ∈
        (Δ.suspStructure.restrictTo (BiSusp.offSouth L)).sing := by
  haveI : Nonempty L := C.nonempty
  exact ⟨show BiSusp.ht (BiSusp.north L) ≠ π from fun h =>
    Real.pi_pos.ne ((rfl : (0 : ℝ) = BiSusp.ht (BiSusp.north L)).trans h),
    Or.inl rfl⟩

/-- **`𝔢(L) ∖ {−p̄}` is positive when `L` is.** -/
theorem GammaLinkCircle.DevData.isPositive_offSouth {L : Type} [TopologicalSpace L]
    {C : GammaLinkCircle L} (Δ : C.DevData) (hC : C.IsPositive) :
    (Δ.suspStructure.restrictTo (BiSusp.offSouth L)).IsPositive :=
  fun _ hx => ⟨L, inferInstance, C, Δ.isApexLink_offSouth hx, hC⟩

/-- **Non-vacuity**: at every `p ∈ dS²` there is a positive singular HS-surface whose one
singular point is linked by a positive, non-regular space-like circle at `p` (`𝔢(L) ∖ {−p̄}`, `L`
the positive circle of `GX.exists_positive_negative`, which has degree `2`; the statement does not
record the degree). -/
theorem exists_isPositive_isSingularHSSurface {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (M : Type) (_ : TopologicalSpace M) (A : SingularHSStructure M), IsSingularHSSurface M A ∧
      A.IsPositive ∧ ∃ x ∈ A.sing, ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L),
        C.pt = p ∧ A.IsApexLink x C ∧ C.IsPositive ∧ ¬ C.IsRegular := by
  obtain ⟨L, L', _, _, C, C', hC, -, hpos, -, -⟩ := exists_positive_negative hp
  obtain ⟨Δ⟩ := C.nonempty_devData
  haveI : Nonempty L := C.nonempty
  obtain ⟨hN, hNs⟩ := Δ.north_mem_sing_offSouth
  exact ⟨BiSusp.offSouth L, inferInstance, _, Δ.isSingularHSSurface_offSouth,
    Δ.isPositive_offSouth hpos.isPositive, _, hNs, L, inferInstance, C, hC,
    Δ.isApexLink_offSouth hNs, hpos.isPositive, hpos.not_isRegular⟩

end Surface

end GX
