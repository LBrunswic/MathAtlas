import GXScaffold.BBS.HSLinkRemarks

/-!
# BBS § 3, two link remarks: the mass of an elliptic singularity (`bbsrem:masspositive`) and the wedge deformation from elliptic through light-like to space-like singularities (`bbsrem:cheminsing`)

Targets `T-bbs-cheminsing` and its tidy-up `T-bbs-cheminsing-tidy` (`roadmap/roadmap.toml`; BBS
layer L2 in lean-gx, DEC-192).
`papers/bbs/legacy/labeled/colI_v1.tex`. 0 `sorry`. Imports `GXScaffold.BBS.HSLinkRemarks` (and
through it the sorry-free scaffold `HSSingularities`, `HSPositive`, `HSDegree`, `HSAntipodal`,
`HSClassification`, `HSRemarkReadings`).

* `bbsrem:masspositive` — `colI_v1.tex:1166` — partial (unmarked: the singular line is read
  through its HS link and `θ` is `GX.GammaLinkCircle.coneAngle`, OQ-113 (a)/(b); the physics
  sentences are informal): the mass `GX.GammaLinkCircle.mass` (`m = 1 − θ/2π`), negative iff
  `θ > 2π` `GX.GammaLinkCircle.mass_neg_iff`, positive iff `θ < 2π` `…mass_pos_iff`, a non-regular
  time-like singularity is positive iff its mass is `GX.GammaLinkCircle.isPositive_iff_mass_pos`,
  a negative mass `GX.HSCheminsing.exists_mass_neg` (`θ = 3π`), regular points have mass `0`.
* `bbsrem:cheminsing` — `colI_v1.tex:1493` — partial (unmarked: the light-like and space-like
  clauses are **false in the library's holonomy convention and true in the gluing-map
  convention**, OQ-144; « positive mass » of a space-like singularity and « continuous
  deformation » are readings; the surgery is read on its link): the wedge link
  `GX.GammaLinkCircle.IsWedgeLink`, `GX.HSCheminsing.exists_isWedgeLink`; time-like: cone angle `< 2π`, mass in
  `]0, 1[`, positive `…IsWedgeLink.timelike`; light-like: negative, positive in the gluing-map
  convention `…IsWedgeLink.lightlike`; space-like: negative, positive in the gluing-map convention
  `…IsWedgeLink.spacelike`; the isometry `GX.Cheminsing.wedgeIsom` (unique, `…wedgeIsom_unique`),
  continuous in `x` `GX.Cheminsing.continuousOn_wedgeLin`, the deformation through `x_∞`
  `GX.Cheminsing.exists_deformation`; the assembly `GX.bbsrem_cheminsing_reading`; an explicit
  elliptic member at the pole `[(1, 0, 0)]` (the time-like branch is not vacuous)
  `GX.Cheminsing.cheminsing_timelike_pole`, every `x ∈ ℍ²₊` `GX.Cheminsing.arc_wedge_timelike`;
  explicit members refuting the printed signs in the library's convention
  `GX.not_cheminsing_lightlike_positive`, `GX.not_cheminsing_spacelike_positive` (each states the
  family's membership: ends, `h = γ_x^{±1}`, `b < a + 2`, `x` in the region).

> [...] where they are called wordlines, or cosmic strings, describing a massive particle in
> motion, with mass $m := 1 - \theta/2\pi$. Hence $\theta > 2\pi$ corresponds to particles with
> negative mass - but they are usually not considered in physics. (l.1168–1171)
>
> Let $[p_1, p_2]$ be an oriented arc in $\partial\HH^2_+$, and for every $x$ in $\HH^2_+$
> consider the elliptic singularity (with positive mass) obtained by removing the wedge comprising
> geodesic rays issued from $x$ and with extremity in $[p_1, p_2]$ and glueing back by an elliptic
> isometry. Move $x$ until it reaches a point $x_\infty$ in $\partial\HH^2 \setminus [p_1, p_2]$.
> It provides a continuous deformation of an elliptic singularity to a light-like singularity,
> which can be continued further into $\dS^2$ by a continuous sequence of space-like
> singularities. Observe that the light-like (resp. space-like) singularities appearing in this
> continuous family are positive (resp. have positive mass). (l.1495–1500)

## Hypothesis checklist

| BBS | here |
|---|---|
| a singular line of angle `θ`, mass `1 − θ/2π` (l.1170) | ⚠ read through its HS link: `θ = coneAngle` of the `(Γ_p, ℓ(p))`-circle (OQ-113 (a)/(b)) |
| `[p₁, p₂]` an oriented arc of `∂ℍ²₊` | ⚠ read: `q₁, q₂ ∈ ∂ℍ²₊`, a set `P ⊆ ∂ℍ²₊` with `B(x, q) ≠ 0` on `P` (`x` off the arc); the orientation is immaterial (both labelings, `hends`) |
| the wedge of rays from `x` with extremity in `[p₁, p₂]` | ⚠ read on the link: an interval `[a, b]` of `ℝP̃¹` all of whose directions point to `P` (`hW`), ends the directions of `q₁, q₂` |
| « glueing back by an elliptic isometry » | ✓ the unique `γ_x ∈ Γ_x` with `γ_x q₁ ∈ ℝ₊ q₂` (`wedgeIsom`, `wedgeIsom_unique`); `γ` and `γ⁻¹` give the same gluing |
| `x ∈ ℍ²₊` | ✓ (`hypPlus_subset_region`); every time-like `x` of the region is covered; over the arc `arcP`, every `x ∈ ℍ²₊` is a member (`arc_wedge_timelike`), e.g. the pole (`cheminsing_timelike_pole`) |
| `x_∞ ∈ ∂ℍ² ∖ [p₁, p₂]` | ✓ read in `∂ℍ²₊` (`bdPlus_mem_region`) |
| « continuous deformation [...] continued further into `dS²` » | ⚠ read: `x ↦ γ_x` continuous on the open region, the path `[x_∞ − s e_t]` (SCOPE (b)) |
| « elliptic singularity (with positive mass) » | ✓ cone angle `< 2π`, `0 < m < 1`, positive (`IsWedgeLink.timelike`) |
| « light-like [...] are positive » | ✗ in the library's convention (negative, `not_cheminsing_lightlike_positive`); ✓ in the gluing-map convention (`IsLightlikePositiveGlue`) |
| « space-like [...] have positive mass » | ⚠ read as positive (l.906–915); ✗ library convention, ✓ gluing-map convention |

## SCOPE (disclosed)

* **(a) The sign finding (OQ-144).** The wedge link is convention-free: removing `[a, b]` and
  gluing gives the lifted holonomy `f` with `f b = a + 2 < b + 2`. At time-like `x` this is cone
  angle `< 2π`. At light-like and space-like `x` (no fixed direction in the wedge) `f = δ² g`,
  `g` the lift with a fixed point and `g b = a < b`, so `g ≤ id` (on `I⁺` at `dS²`): **negative**
  in the library's reading of l.906–922 (`IsLiftedDev`, `D (s + 1) = f (D s)`), positive when the
  inequalities are read with the gluing-map holonomy `g⁻¹` (`IsLightlikePositiveGlue`,
  `IsSpacelikePositiveGlue`, equivalent to the library's negative ones). In the library's
  convention the time-like clause of `IsPositive` (`f < δ²`) and its light-like clause (`f ≥ δ²`)
  point opposite ways along this deformation; in the gluing-map convention positivity is `f ≤ δ²`
  throughout. Evidence for OQ-144, not a ruling.
* **(b) Readings.** « Continuous deformation »: continuity of `x ↦ γ_x` (coefficients), not of
  the lifted holonomy in `G̃` nor of the circles. « Positive mass » of a tachyon: positive in the
  sense of l.906–915 (l.1291 says « positive mass » of a tachyon; the tachyon mass of l.1328 is
  commented out). The surgered surface is identified with a neighbourhood of the apex of `𝔢(L)`
  on its link only, as in `GXScaffold.BBS.HSLinkRemarks` (argued, not formalized).
* **(c) Not formalized:** the physics sentences of `bbsrem:masspositive` (Gott, Carlip); cone
  angles other than `3π` beyond `2π`; `γ_x` elliptic / parabolic / hyperbolic by region (only its
  link's type is used).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal
`51cbb00` through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology Real

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. The mass of a time-like singularity (`bbsrem:masspositive`) -/

section Mass

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

/-- **The mass** `m := 1 − θ/2π` of the singularity `p̄` of `𝔢(L)` (l.1170), `θ` its cone angle
(`GX.GammaLinkCircle.coneAngle`). -/
def GammaLinkCircle.mass (C : GammaLinkCircle L) : ℝ := 1 - C.coneAngle / (2 * π)

/-- **l.1170–1171: `θ > 2π` is negative mass.** -/
theorem GammaLinkCircle.mass_neg_iff : C.mass < 0 ↔ 2 * π < C.coneAngle := by
  rw [GammaLinkCircle.mass, sub_neg, one_lt_div (by positivity)]

theorem GammaLinkCircle.mass_pos_iff : 0 < C.mass ↔ C.coneAngle < 2 * π := by
  rw [GammaLinkCircle.mass, sub_pos, div_lt_one (by positivity)]

theorem GammaLinkCircle.mass_eq_zero_iff : C.mass = 0 ↔ C.coneAngle = 2 * π := by
  rw [GammaLinkCircle.mass, sub_eq_zero, eq_comm, div_eq_one_iff_eq (by positivity)]

theorem GammaLinkCircle.IsRegular.mass_eq_zero (hC : C.IsRegular) : C.mass = 0 := by
  rw [GammaLinkCircle.mass_eq_zero_iff]; exact hC.coneAngle_eq

theorem GammaLinkCircle.mass_lt_one_of_timelike (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) :
    C.mass < 1 := by
  have := C.coneAngle_pos_of_timelike hp
  rw [GammaLinkCircle.mass]
  have : 0 < C.coneAngle / (2 * π) := by positivity
  linarith

/-- **Positive mass is positivity** (l.1510–1511 against l.1170): a non-regular time-like
singularity is positive iff its mass is positive. -/
theorem GammaLinkCircle.isPositive_iff_mass_pos (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0)
    (hreg : ¬ C.IsRegular) : C.IsPositive ↔ 0 < C.mass := by
  rw [GammaLinkCircle.isPositive_iff_of_timelike hp hreg, GammaLinkCircle.mass_pos_iff]

namespace HSCheminsing

/-- **Negative masses occur** (l.1158–1159, a domain wrapping around `c`): at every time-like `p`,
the circle `ℝ/⟨δ³⟩` (lifted holonomy `δ³`, a lift of the half-turn) has cone angle `3π`, negative
mass, and is not positive. -/
theorem exists_mass_neg {p : HS 2} (hp : Causal.Flat.minkQ (p : 𝕄) < 0) :
    ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), C.pt = p ∧
      C.coneAngle = 3 * π ∧ C.mass < 0 ∧ ¬ C.IsRegular ∧ ¬ C.IsPositive := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent p
  have hlt : ∀ x, x < (GTilde.delta ^ (3 : ℤ)) x := fun x => by
    rw [GTilde.delta_zpow_apply]; push_cast; linarith
  have hDf : ∀ x, linkCover p θ ((GTilde.delta ^ (3 : ℤ)) x) =
      gammaHalfTurn hp • linkCover p θ x := fun x => by
    rw [GTilde.delta_zpow_apply]
    have e : x + ((3 : ℤ) : ℝ) = (x + 1) + 2 * ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [e, linkCover_add_two_mul, linkCover_add_one]
    apply Subtype.ext
    rw [gammaP_smul_def, coe_linRaySmul, GammaP.tangent_gammaHalfTurn hp, norm_neg,
      norm_raySphere, inv_one, one_smul, coe_neg_sphere]
  obtain ⟨L, _, cs, hcs, hL, E, ψ, hE, hψc, hψm, hψf, hdev⟩ :=
    exists_gammaLinkCircle_quotient_of_forall_lt p
      (isCoveringMap_linkCover p θ).isLocalHomeomorph hlt hDf
  have hD : (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ E ψ (GTilde.delta ^ (3 : ℤ)) :=
    ⟨hE, hψc, hψm, hdev, hψf⟩
  have hca : (GammaLinkCircle.mk p cs hcs hL).coneAngle = 3 * π := by
    rw [GammaLinkCircle.coneAngle_eq (C := GammaLinkCircle.mk p cs hcs hL) hθ hD,
      GTilde.angle_delta_zpow]
    push_cast; ring
  have hreg : ¬ (GammaLinkCircle.mk p cs hcs hL).IsRegular := fun h => by
    have := h.coneAngle_eq; rw [hca] at this; nlinarith [Real.pi_pos]
  refine ⟨L, inferInstance, GammaLinkCircle.mk p cs hcs hL, rfl, hca, ?_, hreg, ?_⟩
  · rw [GammaLinkCircle.mass_neg_iff, hca]; nlinarith [Real.pi_pos]
  · rw [GammaLinkCircle.isPositive_iff_of_timelike hp hreg, hca]; nlinarith [Real.pi_pos]

end HSCheminsing

end Mass

/-! ## 2. Wedge links -/

section Wedge

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

/-- **`C` is the link at `p` of the wedge `[a, b]` removed and glued back by `h`** (l.1495): in
the coordinates `linkCover p θ` of `ℓ(p)` (`θ` oriented), the wedge is the arc `[a, b]`
(`a < b < a + 2`), the arc `[b, a + 2]` is kept and its ends are glued by `h ∈ Γ_p`, which sends
the direction of `b` to that of `a`; `C` has a lifted developing pair whose lifted holonomy `f`
lifts `h` and sends `b` to `a + 2` (a fundamental domain `[b, f b]`). Convention-free: the gluing by
`h` and by `h⁻¹` is the same identification, and `f` is fixed by the increasing `D`. -/
def GammaLinkCircle.IsWedgeLink (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (a b : ℝ)
    (h : GammaP C.pt) : Prop :=
  IsOrientedTangent C.pt θ ∧ ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde), C.IsLiftedDev θ E D f ∧
    (∀ t, linkCover C.pt θ (f t) = h • linkCover C.pt θ t) ∧ f b = a + 2

/-- **Light-like positivity in the gluing-map convention** (OQ-144): l.919–920 read with the
holonomy taken as the gluing map, i.e. with `g⁻¹` for the factor `g` of the library's lifted
holonomy `f = δᵏ g` (`D (s + 1) = f (D s)`). Equivalent to the library's
`GX.GammaLinkCircle.IsLightlikeNegative` (`isLightlikePositiveGlue_iff`). -/
def GammaLinkCircle.IsLightlikePositiveGlue (C : GammaLinkCircle L) : Prop :=
  Causal.Flat.minkQ (C.pt : 𝕄) = 0 ∧ ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde), C.IsLiftedDev θ E D f ∧ 1 ≤ k ∧
      (∃ x, g x = x) ∧ GTilde.IsParabolic g ∧ f = GTilde.delta ^ k * g ∧ ∀ x, x ≤ g⁻¹ x

/-- **Space-like positivity in the gluing-map convention** (OQ-144): l.915 read with `g⁻¹`.
Equivalent to the library's `GX.GammaLinkCircle.IsSpacelikeNegative`
(`isSpacelikePositiveGlue_iff`). -/
def GammaLinkCircle.IsSpacelikePositiveGlue (C : GammaLinkCircle L) : Prop :=
  C.pt ∈ HS.piece 2 .deSitter ∧ ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde), C.IsLiftedDev θ E D f ∧ 1 ≤ k ∧
      (∃ x, g x = x) ∧ GTilde.IsHyperbolic g ∧ f = GTilde.delta ^ k * g ∧
      ∀ s, E s ∈ C.iPlusL → D s ≤ g⁻¹ (D s)

theorem GammaLinkCircle.isLightlikePositiveGlue_iff :
    C.IsLightlikePositiveGlue ↔ C.IsLightlikeNegative := by
  have key : ∀ g : GTilde, ((∀ x, x ≤ g⁻¹ x) ↔ ∀ x, g x ≤ x) := fun g =>
    ⟨fun h x => by
      have := (GTilde.strictMono g).monotone (h x); rwa [GTilde.apply_inv_apply] at this,
    fun h x => by
      have := (GTilde.strictMono g⁻¹).monotone (h x); rwa [GTilde.inv_apply_apply] at this⟩
  constructor
  · rintro ⟨hp, θ, hθ, E, D, f, k, g, hD, hk, hfix, hpar, hfg, hle⟩
    exact ⟨hp, θ, hθ, E, D, f, k, g, hD, hk, hfix, hpar, hfg, (key g).1 hle⟩
  · rintro ⟨hp, θ, hθ, E, D, f, k, g, hD, hk, hfix, hpar, hfg, hle⟩
    exact ⟨hp, θ, hθ, E, D, f, k, g, hD, hk, hfix, hpar, hfg, (key g).2 hle⟩

theorem GammaLinkCircle.isSpacelikePositiveGlue_iff :
    C.IsSpacelikePositiveGlue ↔ C.IsSpacelikeNegative := by
  have key : ∀ (g : GTilde) (x : ℝ), x ≤ g⁻¹ x ↔ g x ≤ x := fun g x =>
    ⟨fun h => by
      have := (GTilde.strictMono g).monotone h; rwa [GTilde.apply_inv_apply] at this,
    fun h => by
      have := (GTilde.strictMono g⁻¹).monotone h; rwa [GTilde.inv_apply_apply] at this⟩
  constructor
  · rintro ⟨hp, θ, hθ, E, D, f, k, g, hD, hk, hfix, hh, hfg, hle⟩
    exact ⟨hp, θ, hθ, E, D, f, k, g, hD, hk, hfix, hh, hfg, fun s hs => (key g _).1 (hle s hs)⟩
  · rintro ⟨hp, θ, hθ, E, D, f, k, g, hD, hk, hfix, hh, hfg, hle⟩
    exact ⟨hp, θ, hθ, E, D, f, k, g, hD, hk, hfix, hh, hfg, fun s hs => (key g _).2 (hle s hs)⟩

namespace HSCheminsing

/-- A lift of `A ∈ Γ_p` through `linkCover` with a prescribed value. -/
theorem exists_linkLift_through (p : HS 2) (θ : TpHS p ≃ₗ[ℝ] ℂ) (A : GammaP p) {s t : ℝ}
    (h : A • linkCover p θ s = linkCover p θ t) :
    ∃ F : GTilde, (∀ u, linkCover p θ (F u) = A • linkCover p θ u) ∧ F s = t := by
  obtain ⟨F₀, hF₀⟩ := exists_rayLift p (θ := θ) (θ' := θ) (g₀ := 1)
    (fun σ => (one_smul _ _).symm) A
  obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff p θ).1
    (show linkCover p θ (F₀ s) = linkCover p θ t by rw [hF₀, h])
  refine ⟨GTilde.delta ^ (2 * n) * F₀, fun u => ?_, ?_⟩
  · rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply,
      show ((2 * n : ℤ) : ℝ) = 2 * (n : ℝ) by push_cast; ring, linkCover_add_two_mul, hF₀]
  · rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply, hn]; push_cast; ring

/-- Two lifts of the same element differ by `δ^{2n}`. -/
theorem linkLift_eq_add {p : HS 2} {θ : TpHS p ≃ₗ[ℝ] ℂ} {A : GammaP p} {F F' : GTilde}
    (hF : ∀ u, linkCover p θ (F u) = A • linkCover p θ u)
    (hF' : ∀ u, linkCover p θ (F' u) = A • linkCover p θ u) :
    ∃ n : ℤ, ∀ u, F u = F' u + 2 * n := by
  exact linkCover_lift_eq p (GTilde.continuous F) (GTilde.continuous F')
    fun u => by rw [hF, hF']

/-- Time-like wedges: the lift moves every point by less than a turn. -/
theorem wedge_bounds_of_timelike {p : HS 2} (hp : Causal.Flat.minkQ (p : 𝕄) < 0)
    {θ : TpHS p ≃ₗ[ℝ] ℂ} {h : GammaP p} {f : GTilde}
    (hf : ∀ t, linkCover p θ (f t) = h • linkCover p θ t) {a b : ℝ} (hab : a < b)
    (hba : b < a + 2) (hfb : f b = a + 2) : ∀ t, t < f t ∧ f t < t + 2 := by
  have hh1 : h ≠ 1 := by
    rintro rfl
    obtain ⟨n, hn⟩ := linkLift_eq_add hf (F' := 1) (fun u => by rw [one_smul, GTilde.one_apply])
    have hnb := hn b
    rw [hfb, GTilde.one_apply] at hnb
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have : (0 : ℤ) < n := by exact_mod_cast h1
    have : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hne : ∀ t (n : ℤ), f t ≠ t + 2 * n := fun t n he =>
    GammaP.smul_ne_of_timelike hp hh1 (linkCover p θ t) (by rw [← hf, he, linkCover_add_two_mul])
  have hc : Continuous fun u => f u - u := (GTilde.continuous f).sub continuous_id
  intro t
  by_contra hcon
  rw [not_and_or, not_lt, not_lt] at hcon
  rcases hcon with h0 | h2
  · have hmem : (0 : ℝ) ∈ uIcc (f t - t) (f b - b) := by
      rw [hfb]; exact Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
    obtain ⟨c, -, hc0⟩ := intermediate_value_uIcc (a := t) (b := b) hc.continuousOn hmem
    exact hne c 0 (by push_cast; simp only at hc0; linarith)
  · have hmem : (2 : ℝ) ∈ uIcc (f t - t) (f b - b) := by
      rw [hfb]; exact Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
    obtain ⟨c, -, hc0⟩ := intermediate_value_uIcc (a := t) (b := b) hc.continuousOn hmem
    exact hne c 1 (by push_cast; simp only at hc0; linarith)

/-- **A wedge with no fixed direction is shorter than half a turn**, at a non-time-like `p`:
the fixed directions of `h` lift to a set invariant under `t ↦ t + 1`. -/
theorem wedge_short {p : HS 2} (hp : 0 ≤ Causal.Flat.minkQ (p : 𝕄)) {θ : TpHS p ≃ₗ[ℝ] ℂ}
    {h : GammaP p} {a b : ℝ} (hnf : ∀ t ∈ Icc a b, h • linkCover p θ t ≠ linkCover p θ t) :
    b < a + 1 := by
  obtain ⟨g₀, hg₀, c₀, hc₀⟩ := exists_lift_fixed hp θ h
  have hfixadd : ∀ m : ℤ, g₀ (c₀ + m) = c₀ + m := fun m => by rw [GTilde.map_add_int, hc₀]
  have hnfix : ∀ t ∈ Icc a b, g₀ t ≠ t := fun t ht he => hnf t ht (by rw [← hg₀, he])
  have hm1 : c₀ + ⌊a - c₀⌋ ≤ a := by have := Int.floor_le (a - c₀); linarith
  have hm2 : a < c₀ + ⌊a - c₀⌋ + 1 := by have := Int.lt_floor_add_one (a - c₀); linarith
  by_contra hcon
  push Not at hcon
  exact hnfix (c₀ + ((⌊a - c₀⌋ + 1 : ℤ) : ℝ)) ⟨by push_cast; linarith, by push_cast; linarith⟩
    (hfixadd _)

/-- Non-time-like wedges with no fixed direction: half a turn at most, glued by the fixed-point
lift. -/
theorem wedge_factor {p : HS 2} (hp : 0 ≤ Causal.Flat.minkQ (p : 𝕄))
    {θ : TpHS p ≃ₗ[ℝ] ℂ} {h : GammaP p} {f : GTilde}
    (hf : ∀ t, linkCover p θ (f t) = h • linkCover p θ t) {a b : ℝ} (hab : a < b)
    (hfb : f b = a + 2) (hnf : ∀ t ∈ Icc a b, h • linkCover p θ t ≠ linkCover p θ t) :
    b < a + 1 ∧ ∃ g : GTilde, f = GTilde.delta ^ (2 : ℤ) * g ∧ (∃ x, g x = x) ∧ g b = a ∧
      (∀ t, linkCover p θ (g t) = h • linkCover p θ t) ∧ g ≠ 1 := by
  obtain ⟨g₀, hg₀, c₀, hc₀⟩ := exists_lift_fixed hp θ h
  have hba : b < a + 1 := wedge_short hp hnf
  have hgapp : ∀ t, (GTilde.delta ^ (-2 : ℤ) * f) t = f t - 2 := fun t => by
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; ring
  have hg : ∀ t, linkCover p θ ((GTilde.delta ^ (-2 : ℤ) * f) t) = h • linkCover p θ t :=
    fun t => by
      rw [hgapp, show f t - 2 = f t + 2 * ((-1 : ℤ) : ℝ) by push_cast; ring,
        linkCover_add_two_mul, hf]
  obtain ⟨n, hn⟩ := linkLift_eq_add hg hg₀
  have hgb : (GTilde.delta ^ (-2 : ℤ) * f) b = a := by rw [hgapp, hfb]; ring
  have h1 := GTilde.sub_one_lt_apply_of_fixed ⟨c₀, hc₀⟩ b
  have h2 := GTilde.apply_lt_delta_of_fixed ⟨c₀, hc₀⟩ b
  rw [GTilde.delta_apply] at h2
  have hn0 : n = 0 := by
    have hnb := hn b
    rw [hgb] at hnb
    have e1 : (-1 : ℝ) < n := by linarith
    have e2 : (n : ℝ) < 1 := by linarith
    have : (-1 : ℤ) < n := by exact_mod_cast e1
    have : n < (1 : ℤ) := by exact_mod_cast e2
    omega
  have hgg₀ : GTilde.delta ^ (-2 : ℤ) * f = g₀ := GTilde.ext' fun u => by
    rw [hn u, hn0]; simp
  refine ⟨hba, GTilde.delta ^ (-2 : ℤ) * f, ?_, ⟨c₀, by rw [hgg₀]; exact hc₀⟩, hgb, hg, ?_⟩
  · refine GTilde.ext' fun u => ?_
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply, hgapp]; push_cast; ring
  · intro h1'
    rw [h1', GTilde.one_apply] at hgb
    linarith

/-- **Existence of the wedge link.** -/
theorem exists_isWedgeLink (p : HS 2) {θ : TpHS p ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent p θ)
    {a b : ℝ} (hab : a < b) (hba : b < a + 2) (h : GammaP p)
    (hh : h • linkCover p θ b = linkCover p θ a)
    (hreg : Causal.Flat.minkQ (p : 𝕄) < 0 ∨
      ∀ t ∈ Icc a b, h • linkCover p θ t ≠ linkCover p θ t) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link p) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))) (hL : IsCircle L),
      (GammaLinkCircle.mk p cs hcs hL).IsWedgeLink θ a b h := by
  obtain ⟨f, hf, hfb⟩ := exists_linkLift_through p θ h (s := b) (t := a + 2) (by
    rw [hh, show a + 2 = a + 2 * ((1 : ℤ) : ℝ) by push_cast; ring, linkCover_add_two_mul])
  have hlt : ∀ x, x < f x := by
    by_cases hp : Causal.Flat.minkQ (p : 𝕄) < 0
    · exact fun x => (wedge_bounds_of_timelike hp hf hab hba hfb x).1
    · obtain ⟨-, g, hfg, hfix, -, -, -⟩ :=
        wedge_factor (not_lt.1 hp) hf hab hfb (hreg.resolve_left hp)
      intro x
      have := GTilde.sub_one_lt_apply_of_fixed hfix x
      rw [hfg, GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; linarith
  obtain ⟨L, _, cs, hcs, hL, E, ψ, hE, hψc, hψm, hψf, hdev⟩ :=
    exists_gammaLinkCircle_quotient_of_forall_lt p
      (isCoveringMap_linkCover p θ).isLocalHomeomorph hlt hf
  exact ⟨L, inferInstance, cs, hcs, hL, hθ, E, ψ, f, ⟨hE, hψc, hψm, hdev, hψf⟩, hf, hfb⟩

end HSCheminsing

open HSCheminsing

/-- **The elliptic members** (l.1495, « the elliptic singularity (with positive mass) »): at a
time-like `p` the wedge link has cone angle `< 2π`, is not regular, is positive, and its mass is
in `]0, 1[`. Convention-free. -/
theorem GammaLinkCircle.IsWedgeLink.timelike {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {a b : ℝ}
    {h : GammaP C.pt} (hC : C.IsWedgeLink θ a b h) (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0)
    (hab : a < b) (hba : b < a + 2) :
    C.coneAngle < 2 * π ∧ ¬ C.IsRegular ∧ C.IsPositive ∧ 0 < C.mass ∧ C.mass < 1 := by
  obtain ⟨hθ, E, D, f, hD, hf, hfb⟩ := hC
  have hb := wedge_bounds_of_timelike hp hf hab hba hfb
  have hca : C.coneAngle < 2 * π := (C.coneAngle_lt_two_pi_iff hθ hD).2 fun t => (hb t).2
  have hreg : ¬ C.IsRegular := fun hr => by
    have e := hr.eq_delta_sq hθ hD
    rw [e] at hfb
    have : (GTilde.delta ^ (2 : ℕ) : GTilde) b = b + 2 := by
      rw [show (GTilde.delta ^ (2 : ℕ) : GTilde) = GTilde.delta ^ ((2 : ℕ) : ℤ) from
        (zpow_natCast _ _).symm, GTilde.delta_zpow_apply]
      push_cast; ring
    linarith
  exact ⟨hca, hreg, (GammaLinkCircle.isPositive_iff_of_timelike hp hreg).2 hca,
    GammaLinkCircle.mass_pos_iff.2 hca, GammaLinkCircle.mass_lt_one_of_timelike hp⟩

/-- **The light-like members** (l.1497–1499): at a light-like `p`, a wedge with no direction
fixed by `h` gives a light-like singularity of degree `2` which is **negative** in the library's
convention (`g ≤ id`), not positive, and positive in the gluing-map convention. -/
theorem GammaLinkCircle.IsWedgeLink.lightlike {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {a b : ℝ}
    {h : GammaP C.pt} (hC : C.IsWedgeLink θ a b h) (hp : Causal.Flat.minkQ (C.pt : 𝕄) = 0)
    (hab : a < b) (hnf : ∀ t ∈ Icc a b, h • linkCover C.pt θ t ≠ linkCover C.pt θ t) :
    C.IsLightlikeNegative ∧ C.IsLightlikePositiveGlue ∧ ¬ C.IsLightlikePositive ∧
      ¬ C.IsPositive ∧ ¬ C.IsRegular := by
  obtain ⟨hθ, E, D, f, hD, hf, hfb⟩ := hC
  obtain ⟨-, g, hfg, hfix, hgb, hg, hg1⟩ := wedge_factor hp.ge hf hab hfb hnf
  have hpar : GTilde.IsParabolic g := (isParabolic_iff_ne_one_of_lift hp hg hfix).2 hg1
  have hle : ∀ x, g x ≤ x := by
    rcases (hpar.le_or_ge hfix).1 with h1 | h1
    · exfalso; have := h1 b; linarith
    · exact h1
  have hneg : C.IsLightlikeNegative :=
    ⟨hp, θ, hθ, E, D, f, 2, g, hD, by norm_num, hfix, hpar, hfg, hle⟩
  have hnpos : ¬ C.IsLightlikePositive := fun hpos =>
    (GammaLinkCircle.IsLiftedDev.lightlike_dichotomy hθ hD hp (by norm_num : (1 : ℤ) ≤ 2) hfix
      hpar hfg).2 ⟨hpos, hneg⟩
  have hnP : ¬ C.IsPositive := fun hP =>
    hnpos (hP.isLightlikePositive hp hθ hD (by norm_num) hfix hpar hfg)
  exact ⟨hneg, GammaLinkCircle.isLightlikePositiveGlue_iff.2 hneg, hnpos, hnP,
    fun hr => hnP hr.isPositive⟩

/-- **The space-like members** (l.1498–1500): at `p ∈ dS²`, a wedge with no direction fixed by
`h` and a time-like end gives a space-like singularity of degree `2` which is **negative** in the
library's convention (`g < id` on the time-like directions), not positive, and positive in the
gluing-map convention. -/
theorem GammaLinkCircle.IsWedgeLink.spacelike {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {a b : ℝ}
    {h : GammaP C.pt} (hC : C.IsWedgeLink θ a b h) (hp : C.pt ∈ HS.piece 2 .deSitter)
    (hab : a < b) (hnf : ∀ t ∈ Icc a b, h • linkCover C.pt θ t ≠ linkCover C.pt θ t)
    (hbt : linkCover C.pt θ b ∈ dsFutureDirs C.pt ∪ dsPastDirs C.pt) :
    C.IsSpacelikeNegative ∧ C.IsSpacelikePositiveGlue ∧ ¬ C.IsSpacelikePositive ∧
      ¬ C.IsPositive ∧ ¬ C.IsRegular := by
  obtain ⟨hθ, E, D, f, hD, hf, hfb⟩ := hC
  have hq : 0 < Causal.Flat.minkQ (C.pt : 𝕄) := hp
  obtain ⟨-, g, hfg, hfix, hgb, hg, hg1⟩ := wedge_factor hq.le hf hab hfb hnf
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hnf b ⟨hab.le, le_rfl⟩ (one_smul _ _)
  have hhyp : GTilde.IsHyperbolic g := (isHyperbolic_iff_ne_one_of_lift hp hg hfix).2 hg1
  have hdown : ∀ t, linkCover C.pt θ t ∈ dsFutureDirs C.pt ∪ dsPastDirs C.pt → g t < t := by
    rcases timelike_spacelike_dir hp hh1 hg hfix with ⟨h1, -⟩ | ⟨h1, -⟩
    · exfalso; have := h1 b hbt; linarith
    · exact h1
  have hneg : C.IsSpacelikeNegative :=
    ⟨hp, θ, hθ, E, D, f, 2, g, hD, by norm_num, hfix, hhyp, hfg,
      fun s hs => (hdown _ (Or.inl (hD.mem_dsFutureDirs hp hs))).le⟩
  exact ⟨hneg, GammaLinkCircle.isSpacelikePositiveGlue_iff.2 hneg,
    fun hpos => hneg.not_isPositive hpos.isPositive, hneg.not_isPositive,
    fun hr => hneg.not_isPositive hr.isPositive⟩

end Wedge

open HSCheminsing

open Causal.Flat (minkB_comm minkQ_eq_minkB minkB_sub_left minkB_add_left minkB_smul_left)

/-- The Minkowski form `B` of `ℝ^{1,2}`. -/
local notation "𝐁" => Causal.Flat.minkB

/-- The Minkowski quadratic form `Q` of `ℝ^{1,2}`. -/
local notation "𝐐" => Causal.Flat.minkQ

/-! ## 3. The wedge isometry `γ_x` and the deformation through `x_∞` -/

namespace Cheminsing

theorem cramer (a b c z : 𝕄) : vol3 a b c • z = 𝐁 z a • lcross b c +
    𝐁 z b • lcross c a + 𝐁 z c • lcross a b := by
  apply mink3_ext <;>
  simp only [Prod.smul_fst, Prod.fst_add, Prod.snd_add, Prod.smul_snd, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, lcross, mink3_fst, mink3_snd_zero, mink3_snd_one,
    minkB_coords, vol3_eq] <;> ring

theorem eq_zero_of_perp {a b c z : 𝕄} (h : vol3 a b c ≠ 0) (ha : 𝐁 z a = 0)
    (hb : 𝐁 z b = 0) (hc : 𝐁 z c = 0) : z = 0 := by
  have := cramer a b c z
  rw [ha, hb, hc] at this
  simp only [zero_smul, add_zero] at this
  exact (smul_eq_zero.1 this).resolve_left h

theorem minkQ_comb (x p n : 𝕄) (α β κ : ℝ) :
    𝐐 (α • x + β • p + κ • n) = α ^ 2 * 𝐐 x +
      2 * α * β * 𝐁 x p + 2 * α * κ * 𝐁 x n +
      β ^ 2 * 𝐐 p + 2 * β * κ * 𝐁 p n +
      κ ^ 2 * 𝐐 n := by
  simp only [minkQ_coords, minkB_coords, Prod.smul_fst, Prod.fst_add, Prod.snd_add, Prod.smul_snd,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem vol3_x_x (x p : 𝕄) : vol3 x p x = 0 := by rw [vol3_eq]; ring
theorem vol3_x_x' (x p : 𝕄) : vol3 x x p = 0 := by rw [vol3_eq]; ring

def bf (w : 𝕄) : 𝕄 →ₗ[ℝ] ℝ := (Causal.Flat.minkForm 2).flip w
theorem bf_apply (w v : 𝕄) : bf w v = 𝐁 v w := rfl

def lcrossL (w : 𝕄) : 𝕄 →ₗ[ℝ] 𝕄 where
  toFun u := lcross u w
  map_add' u v := by
    apply mink3_ext <;> simp only [lcross, mink3_fst, mink3_snd_zero, mink3_snd_one,
      Prod.fst_add, Prod.snd_add, PiLp.add_apply] <;> ring
  map_smul' c u := by
    apply mink3_ext <;> simp only [lcross, mink3_fst, mink3_snd_zero, mink3_snd_one,
      Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

theorem continuous_lcross_left (w : 𝕄) : Continuous fun u : 𝕄 => lcross u w :=
  LinearMap.continuous_of_finiteDimensional (lcrossL w)
theorem continuous_minkB_left (w : 𝕄) : Continuous fun u : 𝕄 => 𝐁 u w :=
  LinearMap.continuous_of_finiteDimensional (bf w)
theorem continuous_minkQ : Continuous fun u : 𝕄 => 𝐐 u := by
  unfold Causal.Flat.minkQ; fun_prop

/-- the wedge map -/
def wedgeLin (x p₁ p₂ : 𝕄) : 𝕄 →ₗ[ℝ] 𝕄 :=
  (bf p₁).smulRight ((𝐁 x p₁)⁻¹ • x - (𝐐 x / (𝐁 x p₁ * 𝐁 x p₂)) • p₂) +
    (bf x).smulRight ((𝐁 x p₂)⁻¹ • p₂) +
    (bf (lcross x p₁)).smulRight ((𝐁 x p₁ * 𝐁 x p₂)⁻¹ • lcross x p₂)

theorem wedgeLin_apply (x p₁ p₂ v : 𝕄) : wedgeLin x p₁ p₂ v =
    𝐁 v p₁ • ((𝐁 x p₁)⁻¹ • x - (𝐐 x / (𝐁 x p₁ * 𝐁 x p₂)) • p₂) +
      𝐁 v x • ((𝐁 x p₂)⁻¹ • p₂) +
      𝐁 v (lcross x p₁) • ((𝐁 x p₁ * 𝐁 x p₂)⁻¹ • lcross x p₂) := rfl

section
variable {x p₁ p₂ : 𝕄}

theorem lcrossB_left (x p : 𝕄) : 𝐁 (lcross x p) x = 0 := by
  rw [minkB_lcross, vol3_x_x]
theorem lcrossB_right (x p : 𝕄) : 𝐁 (lcross x p) p = 0 := by
  rw [minkB_lcross, CutGlue.vol3_self]
theorem lcrossQ_null (x p : 𝕄) (hp : 𝐐 p = 0) : 𝐐 (lcross x p) = 𝐁 x p ^ 2 := by
  rw [minkQ_lcross, hp, mul_zero, sub_zero]
theorem vol3_lcross (x p : 𝕄) (hp : 𝐐 p = 0) : vol3 x p (lcross x p) = 𝐁 x p ^ 2 := by
  rw [← minkB_lcross, ← minkQ_eq_minkB, lcrossQ_null x p hp]

theorem wedgeLin_self (hc₁ : 𝐁 x p₁ ≠ 0) (hc₂ : 𝐁 x p₂ ≠ 0) : wedgeLin x p₁ p₂ x = x := by
  rw [wedgeLin_apply, ← minkQ_eq_minkB, minkB_comm x (lcross x p₁), lcrossB_left,
    zero_smul, add_zero, smul_sub, smul_smul, smul_smul, smul_smul, mul_inv_cancel₀ hc₁, one_smul]
  have : 𝐁 x p₁ * (𝐐 x / (𝐁 x p₁ * 𝐁 x p₂)) = 𝐐 x * (𝐁 x p₂)⁻¹ := by
    field_simp
  rw [this]; abel

theorem wedgeLin_p₁ (hq₁ : 𝐐 p₁ = 0) :
    wedgeLin x p₁ p₂ p₁ = (𝐁 x p₁ / 𝐁 x p₂) • p₂ := by
  rw [wedgeLin_apply, ← minkQ_eq_minkB, hq₁, minkB_comm p₁ (lcross x p₁), lcrossB_right,
    zero_smul, zero_smul, zero_add, add_zero, smul_smul, minkB_comm p₁ x, div_eq_mul_inv]

theorem wedgeLin_lcross (hc₁ : 𝐁 x p₁ ≠ 0) (hc₂ : 𝐁 x p₂ ≠ 0) (hq₁ : 𝐐 p₁ = 0) :
    wedgeLin x p₁ p₂ (lcross x p₁) = (𝐁 x p₁ / 𝐁 x p₂) • lcross x p₂ := by
  rw [wedgeLin_apply, lcrossB_right, lcrossB_left, ← minkQ_eq_minkB,
    lcrossQ_null x p₁ hq₁, zero_smul, zero_smul, zero_add, zero_add, smul_smul]
  congr 1
  field_simp

theorem decomp (hc₁ : 𝐁 x p₁ ≠ 0) (hq₁ : 𝐐 p₁ = 0) (v : 𝕄) :
    v = (𝐁 v p₁ / 𝐁 x p₁) • x +
      ((𝐁 v x - 𝐁 v p₁ / 𝐁 x p₁ * 𝐐 x) / 𝐁 x p₁) • p₁ +
      (𝐁 v (lcross x p₁) / 𝐁 x p₁ ^ 2) • lcross x p₁ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_perp (a := x) (b := p₁) (c := lcross x p₁) ?_ ?_ ?_ ?_
  · rw [vol3_lcross x p₁ hq₁]; exact pow_ne_zero 2 hc₁
  · simp only [minkB_sub_left, minkB_add_left, minkB_smul_left, ← minkQ_eq_minkB,
      minkB_comm p₁ x, lcrossB_left]
    field_simp; ring
  · simp only [minkB_sub_left, minkB_add_left, minkB_smul_left, ← minkQ_eq_minkB, hq₁,
      lcrossB_right]
    field_simp; ring
  · simp only [minkB_sub_left, minkB_add_left, minkB_smul_left, ← minkQ_eq_minkB,
      lcrossQ_null x p₁ hq₁, minkB_comm x (lcross x p₁), minkB_comm p₁ (lcross x p₁),
      lcrossB_left, lcrossB_right]
    field_simp; ring

theorem minkQ_wedgeLin (hc₁ : 𝐁 x p₁ ≠ 0) (hc₂ : 𝐁 x p₂ ≠ 0) (hq₁ : 𝐐 p₁ = 0)
    (hq₂ : 𝐐 p₂ = 0) (v : 𝕄) : 𝐐 (wedgeLin x p₁ p₂ v) = 𝐐 v := by
  have hv := decomp hc₁ hq₁ v
  have hT : wedgeLin x p₁ p₂ v = (𝐁 v p₁ / 𝐁 x p₁) • x +
      ((𝐁 v x - 𝐁 v p₁ / 𝐁 x p₁ *
        𝐐 x) / 𝐁 x p₁ *
          (𝐁 x p₁ / 𝐁 x p₂)) • p₂ +
      (𝐁 v (lcross x p₁) / 𝐁 x p₁ ^ 2 *
        (𝐁 x p₁ / 𝐁 x p₂)) • lcross x p₂ := by
    conv_lhs => rw [hv]
    rw [map_add, map_add, map_smul, map_smul, map_smul, wedgeLin_self hc₁ hc₂,
      wedgeLin_p₁ hq₁, wedgeLin_lcross hc₁ hc₂ hq₁, smul_smul, smul_smul]
  rw [hT, minkQ_comb]
  conv_rhs => rw [hv, minkQ_comb]
  rw [hq₁, hq₂, lcrossQ_null x p₁ hq₁, lcrossQ_null x p₂ hq₂, minkB_comm x (lcross x p₁),
    minkB_comm x (lcross x p₂), minkB_comm p₁ (lcross x p₁), minkB_comm p₂ (lcross x p₂),
    lcrossB_left, lcrossB_left, lcrossB_right,
    lcrossB_right]
  field_simp
  ring

theorem minkB_wedgeLin (hc₁ : 𝐁 x p₁ ≠ 0) (hc₂ : 𝐁 x p₂ ≠ 0) (hq₁ : 𝐐 p₁ = 0)
    (hq₂ : 𝐐 p₂ = 0) (v w : 𝕄) :
    𝐁 (wedgeLin x p₁ p₂ v) (wedgeLin x p₁ p₂ w) = 𝐁 v w :=
  Causal.Flat.minkB_map_of_minkQ (minkQ_wedgeLin hc₁ hc₂ hq₁ hq₂) v w

theorem wedgeLin_injective (hc₁ : 𝐁 x p₁ ≠ 0) (hc₂ : 𝐁 x p₂ ≠ 0) (hq₁ : 𝐐 p₁ = 0)
    (hq₂ : 𝐐 p₂ = 0) : Function.Injective (wedgeLin x p₁ p₂) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h : ∀ w, 𝐁 v w = 0 := fun w => by
    rw [← minkB_wedgeLin hc₁ hc₂ hq₁ hq₂ v w, hv]; simp [Causal.Flat.minkB]
  refine eq_zero_of_perp (a := x) (b := p₁) (c := lcross x p₁) ?_ (h x) (h p₁) (h _)
  rw [vol3_lcross x p₁ hq₁]; exact pow_ne_zero 2 hc₁

theorem det_wedgeLin (hc₁ : 𝐁 x p₁ ≠ 0) (hc₂ : 𝐁 x p₂ ≠ 0) (hq₁ : 𝐐 p₁ = 0)
    (hq₂ : 𝐐 p₂ = 0) : LinearMap.det (wedgeLin x p₁ p₂) = 1 := by
  have h := vol3_map (wedgeLin x p₁ p₂) x p₁ (lcross x p₁)
  rw [wedgeLin_self hc₁ hc₂, wedgeLin_p₁ hq₁, wedgeLin_lcross hc₁ hc₂ hq₁,
    vol3_smul_mid, CutGlue.vol3_smul_right, vol3_lcross x p₂ hq₂, vol3_lcross x p₁ hq₁] at h
  have h2 : (𝐁 x p₁ ^ 2) ≠ 0 := pow_ne_zero 2 hc₁
  have h3 : (𝐁 x p₁ / 𝐁 x p₂) *
      ((𝐁 x p₁ / 𝐁 x p₂) * 𝐁 x p₂ ^ 2) =
      𝐁 x p₁ ^ 2 := by field_simp
  rw [h3] at h
  have : LinearMap.det (wedgeLin x p₁ p₂) * 𝐁 x p₁ ^ 2 =
      1 * 𝐁 x p₁ ^ 2 := by rw [one_mul]; exact h.symm
  exact mul_right_cancel₀ h2 this
end

/-- **The region where the wedge isometry is defined**: `B(x, q₁) B(x, q₂) > 0`. -/
def region (q₁ q₂ : HS 2) : Set (HS 2) :=
  {x | 0 < 𝐁 (x : 𝕄) q₁ * 𝐁 (x : 𝕄) q₂}

variable {q₁ q₂ x : HS 2}

theorem region_ne (hx : x ∈ region q₁ q₂) :
    𝐁 (x : 𝕄) q₁ ≠ 0 ∧ 𝐁 (x : 𝕄) q₂ ≠ 0 := by
  have h : 0 < 𝐁 (x : 𝕄) q₁ * 𝐁 (x : 𝕄) q₂ := hx
  exact ⟨fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h,
    fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h⟩

theorem region_ratio_pos (hx : x ∈ region q₁ q₂) :
    0 < 𝐁 (x : 𝕄) q₁ / 𝐁 (x : 𝕄) q₂ := by
  have h : 0 < 𝐁 (x : 𝕄) q₁ * 𝐁 (x : 𝕄) q₂ := hx
  have h2 := (region_ne hx).2
  have : 𝐁 (x : 𝕄) q₁ / 𝐁 (x : 𝕄) q₂ =
      𝐁 (x : 𝕄) q₁ * 𝐁 (x : 𝕄) q₂ /
        𝐁 (x : 𝕄) q₂ ^ 2 := by field_simp
  rw [this]; exact div_pos h (by positivity)

theorem bdPlus_null (h : q₁ ∈ HS.piece 2 .bdPlus) : 𝐐 (q₁ : 𝕄) = 0 := h.1

theorem bdPlus_future (h : q₁ ∈ HS.piece 2 .bdPlus) : Causal.Flat.IsFutureCausal (q₁ : 𝕄) :=
  ⟨h.2.le, h.1.le⟩

/-- The wedge isometry as a linear automorphism. -/
def wedgeEquiv (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ region q₁ q₂) : 𝕄 ≃ₗ[ℝ] 𝕄 :=
  LinearEquiv.ofInjectiveEndo (wedgeLin (x : 𝕄) q₁ q₂)
    (wedgeLin_injective (region_ne hx).1 (region_ne hx).2 (bdPlus_null h₁) (bdPlus_null h₂))

theorem wedgeEquiv_apply (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ region q₁ q₂) (v : 𝕄) : wedgeEquiv h₁ h₂ hx v = wedgeLin (x : 𝕄) q₁ q₂ v := rfl

theorem wedgeEquiv_mem (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ region q₁ q₂) : wedgeEquiv h₁ h₂ hx ∈ Causal.Flat.lorentz 2 := by
  obtain ⟨hc₁, hc₂⟩ := region_ne hx
  have hQ : ∀ v, 𝐐 (wedgeEquiv h₁ h₂ hx v) = 𝐐 v := fun v =>
    minkQ_wedgeLin hc₁ hc₂ (bdPlus_null h₁) (bdPlus_null h₂) v
  have he : Causal.Flat.IsFutureTimelike (Causal.Flat.timeUnit 2) := isFutureTimelike_timeUnit
  have hq₁0 : (q₁ : 𝕄) ≠ 0 := raySphere_ne_zero q₁
  have hq₂0 : (q₂ : 𝕄) ≠ 0 := raySphere_ne_zero q₂
  refine Causal.Flat.mem_lorentz_of_future hQ he ?_
    (det_wedgeLin hc₁ hc₂ (bdPlus_null h₁) (bdPlus_null h₂))
  have hlam := region_ratio_pos hx
  refine isFutureTimelike_of_minkB_neg (u := (𝐁 (x : 𝕄) q₁ /
      𝐁 (x : 𝕄) q₂) • (q₂ : 𝕄))
    (by rw [hQ]; exact he.2) ?_ (smul_ne_zero hlam.ne' hq₂0) ?_
  · exact ⟨by rw [Prod.smul_fst, smul_eq_mul]; exact mul_nonneg hlam.le h₂.2.le,
      by rw [Causal.Flat.minkQ_smul, bdPlus_null h₂, mul_zero]⟩
  · rw [← wedgeLin_p₁ (bdPlus_null h₁), wedgeEquiv_apply,
      minkB_wedgeLin hc₁ hc₂ (bdPlus_null h₁) (bdPlus_null h₂)]
    exact Causal.Flat.minkB_neg_of_future (bdPlus_future h₁) hq₁0 he

/-- **The wedge isometry** `γ_x ∈ Γ_x`: the element of `SO₀(1,2)` fixing `x` and sending `q₁` to
a positive multiple of `q₂` (it is the one, `wedgeIsom_unique`). -/
def wedgeIsom (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ region q₁ q₂) : GammaP x :=
  ⟨⟨wedgeEquiv h₁ h₂ hx, wedgeEquiv_mem h₁ h₂ hx⟩,
    wedgeLin_self (region_ne hx).1 (region_ne hx).2⟩

theorem wedgeIsom_apply (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ region q₁ q₂) (v : 𝕄) :
    (((wedgeIsom h₁ h₂ hx : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) v =
      wedgeLin (x : 𝕄) q₁ q₂ v := rfl

theorem wedgeIsom_q₁ (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ region q₁ q₂) :
    (((wedgeIsom h₁ h₂ hx : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) q₁ =
      (𝐁 (x : 𝕄) q₁ / 𝐁 (x : 𝕄) q₂) • (q₂ : 𝕄) :=
  wedgeLin_p₁ (bdPlus_null h₁)

/-- A null vector with `B(x, w) ≠ 0` is not on the line of `x`. -/
theorem tpMk_ne_zero_of_null {w : 𝕄} (hw : 𝐐 w = 0)
    (hB : 𝐁 (x : 𝕄) w ≠ 0) : tpMk x w ≠ 0 := by
  intro h
  obtain ⟨c, rfl⟩ := (tpMk_eq_zero_iff x).1 h
  rw [Causal.Flat.minkQ_smul] at hw
  rw [Causal.Flat.minkB_smul_right, ← minkQ_eq_minkB] at hB
  rcases mul_eq_zero.1 hw with h1 | h1
  · exact hB (by rw [pow_eq_zero_iff (by norm_num)] at h1; rw [h1, zero_mul])
  · exact hB (by rw [h1, mul_zero])

/-- **`γ_x` sends the direction of `q₁` to the direction of `q₂`.** -/
theorem wedgeIsom_smul_dirOf (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ region q₁ q₂) : wedgeIsom h₁ h₂ hx • dirOf x q₁ = dirOf x q₂ := by
  obtain ⟨hc₁, hc₂⟩ := region_ne hx
  have hn₁ := tpMk_ne_zero_of_null (bdPlus_null h₁) hc₁
  have hn₂ := tpMk_ne_zero_of_null (bdPlus_null h₂) hc₂
  rw [gammaP_smul_def, linRaySmul_eq_iff]
  refine ⟨‖tpMk x (q₁ : 𝕄)‖⁻¹ * (𝐁 (x : 𝕄) q₁ / 𝐁 (x : 𝕄) q₂) *
    ‖tpMk x (q₂ : 𝕄)‖, by
      have := region_ratio_pos hx
      have := norm_pos_iff.2 hn₁
      have := norm_pos_iff.2 hn₂
      positivity, ?_⟩
  rw [coe_dirOf x hn₁, coe_dirOf x hn₂, map_smul, tpMk, GammaP.tangent_mk]
  show _ • tpMk x _ = _
  rw [wedgeIsom_q₁ h₁ h₂ hx, tpMk, Submodule.Quotient.mk_smul, smul_smul, smul_smul]
  congr 1
  field_simp


theorem lcross_smul_right (u v : 𝕄) (c : ℝ) : lcross u (c • v) = c • lcross u v := by
  apply mink3_ext <;> simp only [lcross, mink3_fst, mink3_snd_zero, mink3_snd_one,
    Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul] <;> ring

/-- `SO₀(1,2)` commutes with the Lorentzian cross product. -/
theorem lcross_lorentz (A : Causal.Flat.lorentz 2) (u v : 𝕄) :
    (A : 𝕄 ≃ₗ[ℝ] 𝕄) (lcross u v) = lcross ((A : 𝕄 ≃ₗ[ℝ] 𝕄) u) ((A : 𝕄 ≃ₗ[ℝ] 𝕄) v) := by
  have hB : ∀ a b : 𝕄, 𝐁 ((A : 𝕄 ≃ₗ[ℝ] 𝕄) a) ((A : 𝕄 ≃ₗ[ℝ] 𝕄) b) =
      𝐁 a b :=
    Causal.Flat.minkB_map_of_minkQ (A := ((A : 𝕄 ≃ₗ[ℝ] 𝕄) : 𝕄 →ₗ[ℝ] 𝕄)) A.2.1
  have key : ∀ w : 𝕄, 𝐁 ((A : 𝕄 ≃ₗ[ℝ] 𝕄) (lcross u v) -
      lcross ((A : 𝕄 ≃ₗ[ℝ] 𝕄) u) ((A : 𝕄 ≃ₗ[ℝ] 𝕄) v)) w = 0 := fun w => by
    rw [minkB_sub_left, minkB_lcross]
    conv_lhs => rw [← (A : 𝕄 ≃ₗ[ℝ] 𝕄).apply_symm_apply w]
    rw [hB, minkB_lcross, ← vol3_lorentz A u v, LinearEquiv.apply_symm_apply, sub_self]
  have h0 := eq_zero_of_perp (a := mink3 1 0 0) (b := mink3 0 1 0) (c := mink3 0 0 1)
    (by rw [vol3_basis]; exact one_ne_zero) (key _) (key _) (key _)
  exact sub_eq_zero.1 h0

/-- **`γ_x` is the only element of `Γ_x` sending `q₁` into the line of `q₂`** (« the » elliptic
isometry of l.1495). -/
theorem wedgeIsom_unique (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ region q₁ q₂) {A : GammaP x} {c : ℝ}
    (hA : ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) q₁ = c • (q₂ : 𝕄)) :
    A = wedgeIsom h₁ h₂ hx := by
  obtain ⟨hc₁, hc₂⟩ := region_ne hx
  set A' : 𝕄 ≃ₗ[ℝ] 𝕄 := ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) with hA'
  have hAx : A' x = x := A.2
  have hB : ∀ a b : 𝕄, 𝐁 (A' a) (A' b) = 𝐁 a b :=
    Causal.Flat.minkB_map_of_minkQ (A := (A' : 𝕄 →ₗ[ℝ] 𝕄)) (A : Causal.Flat.lorentz 2).2.1
  have hc : c = 𝐁 (x : 𝕄) q₁ / 𝐁 (x : 𝕄) q₂ := by
    have := hB x q₁
    rw [hAx, hA, Causal.Flat.minkB_smul_right] at this
    field_simp
    linarith
  have hAn : A' (lcross x q₁) = c • lcross x q₂ := by
    rw [hA', lcross_lorentz, ← hA', hAx, hA, lcross_smul_right]
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))
  show A' v = wedgeLin (x : 𝕄) q₁ q₂ v
  rw [decomp hc₁ (bdPlus_null h₁) v]
  simp only [map_add, map_smul]
  rw [hAx, hA, hAn, wedgeLin_self hc₁ hc₂, wedgeLin_p₁ (bdPlus_null h₁),
    wedgeLin_lcross hc₁ hc₂ (bdPlus_null h₁), hc]

/-! ### The deformation: continuity in `x`, the region, the path through `x_∞` -/

theorem continuous_coe_hs : Continuous fun x : HS 2 => (x : 𝕄) := continuous_subtype_val

/-- **The wedge isometry depends continuously on `x`** (on its region), read on the matrix
coefficients: `x ↦ γ_x v` is continuous for every `v`. -/
theorem continuousOn_wedgeLin (q₁ q₂ : HS 2) (v : 𝕄) :
    ContinuousOn (fun x : HS 2 => wedgeLin (x : 𝕄) q₁ q₂ v) (region q₁ q₂) := by
  have hB : ∀ w : 𝕄, Continuous fun x : HS 2 => 𝐁 (x : 𝕄) w := fun w =>
    (continuous_minkB_left w).comp continuous_coe_hs
  have hBv : Continuous fun x : HS 2 => 𝐁 v (lcross (x : 𝕄) q₁) := by
    have : (fun x : HS 2 => 𝐁 v (lcross (x : 𝕄) q₁)) =
        fun x : HS 2 => 𝐁 (lcross (x : 𝕄) q₁) v :=
      funext fun (x : HS 2) => minkB_comm _ _
    rw [this]
    exact (continuous_minkB_left v).comp ((continuous_lcross_left _).comp continuous_coe_hs)
  have hBx : Continuous fun x : HS 2 => 𝐁 v (x : 𝕄) := by
    have : (fun x : HS 2 => 𝐁 v (x : 𝕄)) =
        fun x : HS 2 => 𝐁 (x : 𝕄) v :=
      funext fun (x : HS 2) => minkB_comm _ _
    rw [this]; exact hB v
  have hQ : Continuous fun x : HS 2 => 𝐐 (x : 𝕄) :=
    continuous_minkQ.comp continuous_coe_hs
  have hc₁ : ∀ x ∈ region q₁ q₂, 𝐁 (x : 𝕄) q₁ ≠ 0 := fun x hx => (region_ne hx).1
  have hc₂ : ∀ x ∈ region q₁ q₂, 𝐁 (x : 𝕄) q₂ ≠ 0 := fun x hx => (region_ne hx).2
  have hc₁₂ : ∀ x ∈ region q₁ q₂,
      𝐁 (x : 𝕄) q₁ * 𝐁 (x : 𝕄) q₂ ≠ 0 :=
    fun x hx => mul_ne_zero (hc₁ x hx) (hc₂ x hx)
  simp only [wedgeLin_apply]
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · refine continuous_const.continuousOn.smul (ContinuousOn.sub ?_ ?_)
    · exact ((hB _).continuousOn.inv₀ hc₁).smul continuous_coe_hs.continuousOn
    · exact (hQ.continuousOn.div ((hB _).mul (hB _)).continuousOn hc₁₂).smul
        continuous_const.continuousOn
  · exact hBx.continuousOn.smul
      (((hB _).continuousOn.inv₀ hc₂).smul continuous_const.continuousOn)
  · exact hBv.continuousOn.smul ((((hB _).mul (hB _)).continuousOn.inv₀ hc₁₂).smul
      ((continuous_lcross_left _).comp continuous_coe_hs).continuousOn)

theorem isOpen_region (q₁ q₂ : HS 2) : IsOpen (region q₁ q₂) :=
  isOpen_lt continuous_const
    (((continuous_minkB_left _).comp continuous_coe_hs).mul
      ((continuous_minkB_left _).comp continuous_coe_hs))

/-- `ℍ²₊ ⊆` the region (the paper's `x ∈ ℍ²₊`). -/
theorem hypPlus_subset_region (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus) :
    HS.piece 2 .hypPlus ⊆ region q₁ q₂ := fun x hx => by
  have hx' : Causal.Flat.IsFutureTimelike (x : 𝕄) := hx
  have e₁ := Causal.Flat.minkB_neg_of_future (bdPlus_future h₁) (raySphere_ne_zero q₁) hx'
  have e₂ := Causal.Flat.minkB_neg_of_future (bdPlus_future h₂) (raySphere_ne_zero q₂) hx'
  rw [minkB_comm] at e₁ e₂
  exact mul_pos_of_neg_of_neg e₁ e₂

/-- Two distinct points of `∂ℍ²₊` pair negatively. -/
theorem minkB_neg_of_bdPlus {y q : HS 2} (hy : y ∈ HS.piece 2 .bdPlus)
    (hq : q ∈ HS.piece 2 .bdPlus) (hne : y ≠ q) : 𝐁 (y : 𝕄) q < 0 := by
  obtain ⟨hy1, hy2⟩ := HS.mem_bdPlus_iff.1 hy
  obtain ⟨hq1, hq2⟩ := HS.mem_bdPlus_iff.1 hq
  have hle : 𝐁 (y : 𝕄) q ≤ 0 := by
    have := real_inner_le_norm (y : 𝕄).2 (q : 𝕄).2
    rw [Causal.Flat.minkB, hy1, hq1, hy2, hq2] at *
    linarith
  refine lt_of_le_of_ne hle fun h0 => hne ?_
  obtain ⟨c, hc⟩ := Causal.Flat.eq_smul_of_null_orth (bdPlus_null hy) (raySphere_ne_zero y)
    (bdPlus_null hq) h0
  have hc1 : c = 1 := by
    have := congrArg Prod.fst hc
    rw [Prod.smul_fst, smul_eq_mul, hy1, hq1, mul_one] at this
    exact this.symm
  rw [hc1, one_smul] at hc
  exact Subtype.ext hc.symm

/-- `∂ℍ²₊ ∖ {q₁, q₂} ⊆` the region (the paper's `x_∞ ∉ [p₁, p₂]`). -/
theorem bdPlus_mem_region (h₁ : q₁ ∈ HS.piece 2 .bdPlus) (h₂ : q₂ ∈ HS.piece 2 .bdPlus)
    (hx : x ∈ HS.piece 2 .bdPlus) (hx₁ : x ≠ q₁) (hx₂ : x ≠ q₂) : x ∈ region q₁ q₂ :=
  mul_pos_of_neg_of_neg (minkB_neg_of_bdPlus hx h₁ hx₁) (minkB_neg_of_bdPlus hx h₂ hx₂)

/-- The path `s ↦ [x_∞ − s e_t]` through `x_∞ ∈ ∂ℍ²₊`. -/
def defPath (x₀ : HS 2) (s : ℝ) : HS 2 :=
  rayNormalize x₀ ((x₀ : 𝕄) - s • Causal.Flat.timeUnit 2)

theorem defPath_vec_ne {x₀ : HS 2} (hx₀ : x₀ ∈ HS.piece 2 .bdPlus) (s : ℝ) :
    (x₀ : 𝕄) - s • Causal.Flat.timeUnit 2 ≠ 0 := by
  intro h
  have h2 := congrArg Prod.snd h
  simp only [Prod.snd_sub, Prod.smul_snd, Causal.Flat.timeUnit, smul_zero, sub_zero,
    Prod.snd_zero] at h2
  have := (HS.mem_bdPlus_iff.1 hx₀).2
  rw [h2, norm_zero] at this
  exact zero_ne_one this

theorem continuous_defPath {x₀ : HS 2} (hx₀ : x₀ ∈ HS.piece 2 .bdPlus) :
    Continuous (defPath x₀) :=
  continuous_iff_continuousAt.2 fun s =>
    ContinuousAt.comp (f := fun s : ℝ => (x₀ : 𝕄) - s • Causal.Flat.timeUnit 2)
      (continuousAt_rayNormalize x₀ (defPath_vec_ne hx₀ s))
      ((continuous_const.sub (continuous_id.smul continuous_const) :
        Continuous fun s : ℝ => (x₀ : 𝕄) - s • Causal.Flat.timeUnit 2).continuousAt)

theorem defPath_zero (x₀ : HS 2) : defPath x₀ 0 = x₀ := by
  rw [defPath, zero_smul, sub_zero, rayNormalize_raySphere]

theorem minkQ_defPath_vec {x₀ : HS 2} (hx₀ : x₀ ∈ HS.piece 2 .bdPlus) (s : ℝ) :
    𝐐 ((x₀ : 𝕄) - s • Causal.Flat.timeUnit 2) = 2 * s - s ^ 2 := by
  obtain ⟨h1, h2⟩ := HS.mem_bdPlus_iff.1 hx₀
  simp only [Causal.Flat.minkQ, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    Causal.Flat.timeUnit, smul_zero, sub_zero, smul_eq_mul, mul_one, h1, h2]
  ring

/-- **The deformation of the remark**: moving `x` through `x_∞ ∈ ∂ℍ²₊ ∖ {q₁, q₂}` along
`s ↦ [x_∞ − s e_t]`, the point lies in `ℍ²₊` for `s < 0`, at `x_∞` for `s = 0`, in `dS²` for
`0 < s < 2`, and, for `|s|` small, in the region of the wedge isometry, which varies
continuously along the path. -/
theorem exists_deformation {x₀ : HS 2} (hx₀ : x₀ ∈ HS.piece 2 .bdPlus)
    (hR : x₀ ∈ region q₁ q₂) :
    Continuous (defPath x₀) ∧ defPath x₀ 0 = x₀ ∧
      (∀ s < 0, defPath x₀ s ∈ HS.piece 2 .hypPlus) ∧
      (∀ s, 0 < s → s < 2 → defPath x₀ s ∈ HS.piece 2 .deSitter) ∧
      ∃ ε > 0, (∀ s ∈ Ioo (-ε) ε, defPath x₀ s ∈ region q₁ q₂) ∧
        ∀ v : 𝕄, ContinuousOn (fun s => wedgeLin (defPath x₀ s : 𝕄) q₁ q₂ v) (Ioo (-ε) ε) := by
  have hc := continuous_defPath hx₀
  have hcoe : ∀ s, (defPath x₀ s : 𝕄) =
      ‖(x₀ : 𝕄) - s • Causal.Flat.timeUnit 2‖⁻¹ • ((x₀ : 𝕄) - s • Causal.Flat.timeUnit 2) :=
    fun s => coe_rayNormalize x₀ (defPath_vec_ne hx₀ s)
  have hpos : ∀ s, 0 < ‖(x₀ : 𝕄) - s • Causal.Flat.timeUnit 2‖⁻¹ := fun s =>
    inv_pos.2 (norm_pos_iff.2 (defPath_vec_ne hx₀ s))
  obtain ⟨h1, -⟩ := HS.mem_bdPlus_iff.1 hx₀
  have hopen : defPath x₀ ⁻¹' region q₁ q₂ ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds ((isOpen_region q₁ q₂).mem_nhds (by rwa [defPath_zero]))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hopen
  have hsub : Ioo (-ε) ε ⊆ defPath x₀ ⁻¹' region q₁ q₂ := fun s hs =>
    hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact hs)
  refine ⟨hc, defPath_zero x₀, fun s hs => ?_, fun s hs hs2 => ?_, ε, hε, hsub,
    fun v => (continuousOn_wedgeLin q₁ q₂ v).comp hc.continuousOn hsub⟩
  · show Causal.Flat.IsFutureTimelike (defPath x₀ s : 𝕄)
    rw [hcoe, HS.isFutureTimelike_smul_iff (hpos s)]
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_sub, Prod.smul_fst, Causal.Flat.timeUnit, smul_eq_mul, mul_one, h1]
      linarith
    · rw [minkQ_defPath_vec hx₀]; nlinarith
  · show 0 < 𝐐 (defPath x₀ s : 𝕄)
    rw [hcoe, HS.minkQ_smul_pos_iff (hpos s), minkQ_defPath_vec hx₀]
    nlinarith


/-! ### Directions toward the points of `∂ℍ²₊` -/

theorem minkQ_perpLin_null {w : 𝕄} (hw : 𝐐 w = 0) :
    𝐐 (perpLin x w) =
      -(𝐐 (x : 𝕄) * 𝐁 (x : 𝕄) w ^ 2) := by
  have e : perpLin x w = 𝐐 (x : 𝕄) • w +
      (-𝐁 (x : 𝕄) w) • (x : 𝕄) + (0 : ℝ) • (0 : 𝕄) := by
    rw [perpLin_apply, zero_smul, add_zero, neg_smul, ← sub_eq_add_neg]
  rw [e, minkQ_comb, hw, minkB_comm w (x : 𝕄)]
  ring

/-- **At `x ∈ dS²`, the direction of a null `w` with `B(x, w) ≠ 0` is time-like** (future or
past). -/
theorem dirOf_timelike (hx : x ∈ HS.piece 2 .deSitter) {w : 𝕄} (hw : 𝐐 w = 0)
    (hB : 𝐁 (x : 𝕄) w ≠ 0) :
    dirOf x w ∈ dsFutureDirs x ∪ dsPastDirs x ∧
      𝐐 (dsProj x (dirOf x w : TpHS x)) < 0 := by
  have hn := tpMk_ne_zero_of_null hw hB
  have hd : dsProj x (dirOf x w : TpHS x) = ‖tpMk x w‖⁻¹ • perpLin x w := by
    rw [coe_dirOf x hn, map_smul, dsProj_mk]
  have hq : 0 < 𝐐 (x : 𝕄) := hx
  have hQ : 𝐐 (dsProj x (dirOf x w : TpHS x)) < 0 := by
    rw [hd, Causal.Flat.minkQ_smul, minkQ_perpLin_null hw]
    have h1 : 0 < (‖tpMk x w‖⁻¹) ^ 2 := pow_pos (inv_pos.2 (norm_pos_iff.2 hn)) 2
    have h2 : 0 < 𝐐 (x : 𝕄) * 𝐁 (x : 𝕄) w ^ 2 :=
      mul_pos hq (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hB)))
    nlinarith
  rcases Causal.Flat.isFutureTimelike_or_neg hQ with h | h
  · exact ⟨Or.inl h, hQ⟩
  · exact ⟨Or.inr h, hQ⟩

/-- **At a non-time-like `x`, no element `≠ 1` of `Γ_x` fixes the direction of a null `w` with
`B(x, w) ≠ 0`**: the fixed directions are the null ones at `x ∈ dS²`, the two tangent ones at
`x ∈ ∂ℍ²±`. -/
theorem smul_dirOf_ne (hx : 0 ≤ 𝐐 (x : 𝕄)) {w : 𝕄}
    (hw : 𝐐 w = 0) (hB : 𝐁 (x : 𝕄) w ≠ 0) {A : GammaP x}
    (hA : A ≠ 1) : A • dirOf x w ≠ dirOf x w := by
  intro heq
  rcases hx.lt_or_eq with hpos | hzero
  · exact hA (eq_one_of_smul_eq_of_deSitter hpos heq (dirOf_timelike hpos hw hB).2.ne)
  · have hz : 𝐐 (x : 𝕄) = 0 := hzero.symm
    have hn := tpMk_ne_zero_of_null hw hB
    have hmem : dirOf x w ∈ {σ : Link x | A • σ = σ} := heq
    rw [GammaP.fixedPoints_eq_of_null hz hA] at hmem
    have h0 : nullPairing x (dirOf x w : TpHS x) = 0 := hmem
    rw [nullPairing_dirOf x hz hn] at h0
    exact hB ((mul_eq_zero.1 h0).resolve_left (inv_pos.2 (norm_pos_iff.2 hn)).ne')

end Cheminsing

open Cheminsing in
/-- **`bbsrem:cheminsing`, the assembly.** For `q₁, q₂ ∈ ∂ℍ²₊`, the arc read as a set
`P ⊆ ∂ℍ²₊` and `x` in the region of `γ_x` with `B(x, q) ≠ 0` on `P`: the wedge `[a, b]` of
`ℓ(x)` pointing to `P`, ends at the directions of `q₁, q₂`, glued back by `γ_x^{±1}`, has a
link; at time-like `x` it is an elliptic singularity of positive mass; at light-like `x` it is
negative in the library's convention and positive in the gluing-map convention; at `x ∈ dS²`
likewise. -/
theorem bbsrem_cheminsing_reading {q₁ q₂ : HS 2} (h₁ : q₁ ∈ HS.piece 2 .bdPlus)
    (h₂ : q₂ ∈ HS.piece 2 .bdPlus) {P : Set (HS 2)} (hP : P ⊆ HS.piece 2 .bdPlus) {x : HS 2}
    (hx : x ∈ region q₁ q₂) (hPx : ∀ q ∈ P, 𝐁 (x : 𝕄) q ≠ 0)
    {θ : TpHS x ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent x θ) {a b : ℝ} (hab : a < b) (hba : b < a + 2)
    (hW : ∀ t ∈ Icc a b, ∃ q ∈ P, linkCover x θ t = dirOf x q) {h : GammaP x}
    (hends : (linkCover x θ a = dirOf x q₁ ∧ linkCover x θ b = dirOf x q₂ ∧
        h = (wedgeIsom h₁ h₂ hx)⁻¹) ∨
      (linkCover x θ a = dirOf x q₂ ∧ linkCover x θ b = dirOf x q₁ ∧ h = wedgeIsom h₁ h₂ hx)) :
    (∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link x) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP x) (Link x))) (hL : IsCircle L),
        (GammaLinkCircle.mk x cs hcs hL).IsWedgeLink θ a b h) ∧
    ∀ {L : Type} [TopologicalSpace L] (cs : ChartedSpace (Link x) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP x) (Link x))) (hL : IsCircle L),
      (GammaLinkCircle.mk x cs hcs hL).IsWedgeLink θ a b h →
      (𝐐 (x : 𝕄) < 0 →
        (GammaLinkCircle.mk x cs hcs hL).coneAngle < 2 * π ∧
        0 < (GammaLinkCircle.mk x cs hcs hL).mass ∧
        (GammaLinkCircle.mk x cs hcs hL).IsPositive ∧
        ¬ (GammaLinkCircle.mk x cs hcs hL).IsRegular) ∧
      (𝐐 (x : 𝕄) = 0 →
        (GammaLinkCircle.mk x cs hcs hL).IsLightlikeNegative ∧
        (GammaLinkCircle.mk x cs hcs hL).IsLightlikePositiveGlue ∧
        ¬ (GammaLinkCircle.mk x cs hcs hL).IsPositive) ∧
      (x ∈ HS.piece 2 .deSitter →
        (GammaLinkCircle.mk x cs hcs hL).IsSpacelikeNegative ∧
        (GammaLinkCircle.mk x cs hcs hL).IsSpacelikePositiveGlue ∧
        ¬ (GammaLinkCircle.mk x cs hcs hL).IsPositive) := by
  have hγ := wedgeIsom_smul_dirOf h₁ h₂ hx
  have hh : h • linkCover x θ b = linkCover x θ a := by
    rcases hends with ⟨ha, hb, rfl⟩ | ⟨ha, hb, rfl⟩
    · rw [hb, ha, inv_smul_eq_iff, hγ]
    · rw [hb, ha, hγ]
  have hne : linkCover x θ a ≠ linkCover x θ b := fun he => by
    obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff x θ).1 he
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have : (0 : ℤ) < n := by exact_mod_cast h1
    have : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hh1 : h ≠ 1 := by
    rintro rfl
    rw [one_smul] at hh
    exact hne hh.symm
  have hnf : 0 ≤ 𝐐 (x : 𝕄) →
      ∀ t ∈ Icc a b, h • linkCover x θ t ≠ linkCover x θ t := fun hq0 t ht => by
    obtain ⟨q, hq, hqt⟩ := hW t ht
    rw [hqt]
    exact smul_dirOf_ne hq0 (bdPlus_null (hP hq)) (hPx q hq) hh1
  refine ⟨exists_isWedgeLink x hθ hab hba h hh ?_, fun cs hcs hL hC => ⟨fun hp => ?_,
    fun hp => ?_, fun hp => ?_⟩⟩
  · by_cases hp : 𝐐 (x : 𝕄) < 0
    · exact Or.inl hp
    · exact Or.inr (hnf (not_lt.1 hp))
  · obtain ⟨h1, h2, h3, h4, -⟩ := hC.timelike hp hab hba
    exact ⟨h1, h4, h3, h2⟩
  · obtain ⟨h1, h2, -, h3, -⟩ := hC.lightlike hp hab (hnf hp.ge)
    exact ⟨h1, h2, h3⟩
  · have hq : 0 < 𝐐 (x : 𝕄) := hp
    obtain ⟨q, hq', hqb⟩ := hW b ⟨hab.le, le_rfl⟩
    have hbt : linkCover x θ b ∈ dsFutureDirs x ∪ dsPastDirs x := by
      rw [hqb]; exact (dirOf_timelike hp (bdPlus_null (hP hq')) (hPx q hq')).1
    obtain ⟨h1, h2, -, h3, -⟩ := hC.spacelike hp hab (hnf hq.le) hbt
    exact ⟨h1, h2, h3⟩

/-! ## 4. A light-like member of the family, not positive in the library's convention -/

namespace Cheminsing

/-- The point `(1, cos s, sin s)` of `∂ℍ²₊`. -/
def qPt (s : ℝ) : HS 2 := (rp1ToBdPlus (Circle.exp s) : HS 2)

theorem qPt_mem (s : ℝ) : qPt s ∈ HS.piece 2 .bdPlus := (rp1ToBdPlus (Circle.exp s)).2

theorem coe_qPt (s : ℝ) : (qPt s : 𝕄) = mink3 1 (Real.cos s) (Real.sin s) := by
  rw [qPt, coe_rp1ToBdPlus, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

theorem continuous_qPt : Continuous qPt :=
  continuous_subtype_val.comp (rp1ToBdPlus.continuous.comp Circle.exp.continuous)

theorem minkB_qPt (u s : ℝ) :
    𝐁 (qPt u : 𝕄) (qPt s) = -1 + Real.cos (u - s) := by
  rw [coe_qPt, coe_qPt, minkB_coords, Real.cos_sub]
  simp only [mink3_fst, mink3_snd_zero, mink3_snd_one]
  ring

end Cheminsing

namespace Cheminsing

/-- The arc `{(1, cos s, sin s) : π/2 ≤ s ≤ π}` of `∂ℍ²₊`, from `(1, 0, 1)` to `(1, −1, 0)`. -/
def arcP : Set (HS 2) := qPt '' Icc (π / 2) π

theorem arcP_subset : arcP ⊆ HS.piece 2 .bdPlus := by rintro _ ⟨s, -, rfl⟩; exact qPt_mem s

/-- If `x` has vanishing last coordinate, the two ends of the arc are seen from `x` in different
directions. -/
theorem dirOf_arc_ne {x : HS 2} (hx2 : (x : 𝕄).2 1 = 0)
    (hB₁ : 𝐁 (x : 𝕄) (qPt (π / 2)) ≠ 0)
    (hB₂ : 𝐁 (x : 𝕄) (qPt π) ≠ 0) :
    dirOf x (qPt (π / 2)) ≠ dirOf x (qPt π) := by
  intro he
  have hn₁ := tpMk_ne_zero_of_null (bdPlus_null (qPt_mem _)) hB₁
  have hn₂ := tpMk_ne_zero_of_null (bdPlus_null (qPt_mem _)) hB₂
  have he' := congrArg (fun σ : Link x => (σ : TpHS x)) he
  rw [coe_dirOf x hn₁, coe_dirOf x hn₂, tpMk, tpMk, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub] at he'
  obtain ⟨k, hk⟩ := (tpMk_eq_zero_iff x).1 he'
  have h3 := congrArg (fun v : 𝕄 => v.2 1) hk
  simp only [Prod.snd_sub, Prod.smul_snd, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hx2,
    coe_qPt, mink3_snd_one, Real.sin_pi_div_two, Real.sin_pi, mul_zero, sub_zero, mul_one] at h3
  rw [inv_eq_zero, norm_eq_zero] at h3
  rw [coe_qPt, Real.sin_pi_div_two] at hn₁
  exact hn₁ h3

/-- `qPt 0 = (1, 1, 0)` is off the arc `arcP`. -/
theorem qPt_zero_not_mem_arcP : qPt 0 ∉ arcP := by
  rintro ⟨s, hs, he⟩
  have h := minkB_qPt 0 s
  rw [he, ← minkQ_eq_minkB, bdPlus_null (qPt_mem 0), zero_sub, Real.cos_neg] at h
  have := Real.cos_nonpos_of_pi_div_two_le_of_le hs.1 (by linarith [hs.2, Real.pi_pos])
  linarith

/-- At `x ∈ ℍ²₊`, every point of `∂ℍ²₊` pairs negatively with `x`. -/
theorem minkB_neg_of_hypPlus {x q : HS 2} (hx : x ∈ HS.piece 2 .hypPlus)
    (hq : q ∈ HS.piece 2 .bdPlus) : 𝐁 (x : 𝕄) q < 0 := by
  rw [minkB_comm]
  exact Causal.Flat.minkB_neg_of_future (bdPlus_future hq) (raySphere_ne_zero q) hx

/-- **Two points of `∂ℍ²₊` pairing with `x` with the same sign are seen from `x` in different
directions, unless they coincide.** -/
theorem eq_of_dirOf_eq {x q q' : HS 2} (hq : q ∈ HS.piece 2 .bdPlus)
    (hq' : q' ∈ HS.piece 2 .bdPlus) (hB : 0 < 𝐁 (x : 𝕄) q * 𝐁 (x : 𝕄) q')
    (he : dirOf x q = dirOf x q') : q = q' := by
  by_contra hne
  have hqq' := minkB_neg_of_bdPlus hq hq' hne
  have hB1 : 𝐁 (x : 𝕄) q ≠ 0 := fun h0 => by rw [h0, zero_mul] at hB; exact lt_irrefl _ hB
  have hB2 : 𝐁 (x : 𝕄) q' ≠ 0 := fun h0 => by rw [h0, mul_zero] at hB; exact lt_irrefl _ hB
  have hn₁ := tpMk_ne_zero_of_null (bdPlus_null hq) hB1
  have hn₂ := tpMk_ne_zero_of_null (bdPlus_null hq') hB2
  have hc₁ : 0 < ‖tpMk x (q : 𝕄)‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hn₁)
  have hc₂ : 0 < ‖tpMk x (q' : 𝕄)‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hn₂)
  have key : tpMk x (‖tpMk x (q : 𝕄)‖⁻¹ • (q : 𝕄) - ‖tpMk x (q' : 𝕄)‖⁻¹ • (q' : 𝕄)) = 0 := by
    have h := congrArg (fun σ : Link x => (σ : TpHS x)) he
    rw [coe_dirOf x hn₁, coe_dirOf x hn₂] at h
    rw [tpMk, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_smul, sub_eq_zero]
    exact h
  generalize ‖tpMk x (q : 𝕄)‖⁻¹ = c₁ at key hc₁
  generalize ‖tpMk x (q' : 𝕄)‖⁻¹ = c₂ at key hc₂
  obtain ⟨k, hk⟩ := (tpMk_eq_zero_iff x).1 key
  have e1 := congrArg (fun v : 𝕄 => 𝐁 v q) hk
  have e2 := congrArg (fun v : 𝕄 => 𝐁 v q') hk
  simp only [minkB_sub_left, minkB_smul_left] at e1 e2
  rw [← minkQ_eq_minkB, bdPlus_null hq, minkB_comm (q' : 𝕄) q] at e1
  rw [← minkQ_eq_minkB (q' : 𝕄), bdPlus_null hq'] at e2
  have hprod : (k * 𝐁 (x : 𝕄) q) * (k * 𝐁 (x : 𝕄) q') =
      -(c₁ * c₂ * (𝐁 (q : 𝕄) q' * 𝐁 (q : 𝕄) q')) := by
    rw [← e1, ← e2]; ring
  have h1 : 0 ≤ (k * 𝐁 (x : 𝕄) q) * (k * 𝐁 (x : 𝕄) q') := by
    have := mul_nonneg (sq_nonneg k) hB.le
    linarith [show (k * 𝐁 (x : 𝕄) q) * (k * 𝐁 (x : 𝕄) q') =
      k ^ 2 * (𝐁 (x : 𝕄) q * 𝐁 (x : 𝕄) q') by ring]
  have h2 : 0 < c₁ * c₂ * (𝐁 (q : 𝕄) q' * 𝐁 (q : 𝕄) q') :=
    mul_pos (mul_pos hc₁ hc₂) (mul_pos_of_neg_of_neg hqq' hqq')
  linarith

/-- **The lifted wedge over the arc `arcP`**, given that a wedge of `ℓ(x)` pointing to `arcP` and
glued by an element sending its right end to its left one is shorter than a turn (`hshort`): an
interval `[a, b]` of `ℝP̃¹`, `a < b < a + 2`, all of whose directions point to `arcP`, with ends
the directions of `p₁ = (1, 0, 1)` and `p₂ = (1, −1, 0)` and `h = γ_x^{±1}` (the hypotheses `hW`
and `hends` of `GX.bbsrem_cheminsing_reading`). -/
theorem arc_wedge_ends {x : HS 2}
    (hBs : ∀ s ∈ Icc (π / 2) π, 𝐁 (x : 𝕄) (qPt s) ≠ 0)
    (hx : x ∈ region (qPt (π / 2)) (qPt π))
    (hdir : dirOf x (qPt (π / 2)) ≠ dirOf x (qPt π))
    (hshort : ∀ (θ : TpHS x ≃ₗ[ℝ] ℂ) {a b : ℝ} {h : GammaP x},
      (∀ t ∈ Icc a b, ∃ q ∈ arcP, linkCover x θ t = dirOf x q) →
      h • linkCover x θ b = linkCover x θ a → linkCover x θ a ≠ linkCover x θ b → b < a + 2) :
    ∃ (θ : TpHS x ≃ₗ[ℝ] ℂ) (a b : ℝ) (h : GammaP x), IsOrientedTangent x θ ∧ a < b ∧
      b < a + 2 ∧ (∀ t ∈ Icc a b, ∃ q ∈ arcP, linkCover x θ t = dirOf x q) ∧
      ((linkCover x θ a = dirOf x (qPt (π / 2)) ∧ linkCover x θ b = dirOf x (qPt π) ∧
          h = (wedgeIsom (qPt_mem _) (qPt_mem _) hx)⁻¹) ∨
        (linkCover x θ a = dirOf x (qPt π) ∧ linkCover x θ b = dirOf x (qPt (π / 2)) ∧
          h = wedgeIsom (qPt_mem _) (qPt_mem _) hx)) := by
  have hle : π / 2 ≤ π := by linarith [Real.pi_pos]
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent x
  -- the directions of the arc, lifted to `ℝP̃¹`
  set c : ℝ → Link x := fun s => dirOf x (qPt (projIcc (π / 2) π hle s) : 𝕄) with hcdef
  have hcc : Continuous c := by
    refine (continuousOn_dirOf x).comp_continuous
      (continuous_subtype_val.comp (continuous_qPt.comp
        (continuous_subtype_val.comp continuous_projIcc))) fun s => ?_
    exact tpMk_ne_zero_of_null (bdPlus_null (qPt_mem _)) (hBs _ (projIcc (π / 2) π hle s).2)
  obtain ⟨e₀, he₀⟩ := linkCover_surjective x θ (c 0)
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    (isCoveringMap_linkCover x θ).existsUnique_continuousMap_lifts ⟨c, hcc⟩ 0 e₀ he₀
  have hFc : ∀ s, linkCover x θ (F s) = c s := fun s => congrFun hF s
  have hF₁ : linkCover x θ (F (π / 2)) = dirOf x (qPt (π / 2)) := by
    rw [hFc, hcdef]; simp only; rw [projIcc_left]
  have hF₂ : linkCover x θ (F π) = dirOf x (qPt π) := by
    rw [hFc, hcdef]; simp only; rw [projIcc_right]
  have hne : F (π / 2) ≠ F π := fun he => hdir (by rw [← hF₁, ← hF₂, he])
  have hγ := wedgeIsom_smul_dirOf (qPt_mem (π / 2)) (qPt_mem π) hx
  have hIVT : ∀ t ∈ uIcc (F (π / 2)) (F π), ∃ q ∈ arcP, linkCover x θ t = dirOf x q := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := intermediate_value_uIcc (F.continuous.continuousOn) ht
    rw [uIcc_of_le hle] at hs
    refine ⟨qPt s, ⟨s, hs, rfl⟩, ?_⟩
    rw [← hst, hFc, hcdef]; simp only; rw [projIcc_of_mem hle hs]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hW : ∀ t ∈ Icc (F (π / 2)) (F π), ∃ q ∈ arcP, linkCover x θ t = dirOf x q :=
      fun t ht => hIVT t (by rw [uIcc_of_le hlt.le]; exact ht)
    have hh : (wedgeIsom (qPt_mem (π / 2)) (qPt_mem π) hx)⁻¹ • linkCover x θ (F π) =
        linkCover x θ (F (π / 2)) := by rw [hF₁, hF₂, inv_smul_eq_iff, hγ]
    have hba := hshort θ hW hh (by rw [hF₁, hF₂]; exact hdir)
    exact ⟨θ, _, _, _, hθ, hlt, hba, hW, Or.inl ⟨hF₁, hF₂, rfl⟩⟩
  · have hW : ∀ t ∈ Icc (F π) (F (π / 2)), ∃ q ∈ arcP, linkCover x θ t = dirOf x q :=
      fun t ht => hIVT t (by rw [uIcc_of_ge hgt.le]; exact ht)
    have hh : wedgeIsom (qPt_mem (π / 2)) (qPt_mem π) hx • linkCover x θ (F (π / 2)) =
        linkCover x θ (F π) := by rw [hF₁, hF₂, hγ]
    have hba := hshort θ hW hh (by rw [hF₁, hF₂]; exact Ne.symm hdir)
    exact ⟨θ, _, _, _, hθ, hgt, hba, hW, Or.inr ⟨hF₂, hF₁, rfl⟩⟩

/-- **The wedge over the arc `arcP`, at a non-time-like `x` off the arc**: every hypothesis of
`GX.bbsrem_cheminsing_reading` holds (the wedge `[a, b]` is the lift of the directions of the
arc, by lifting the path `s ↦ dir_x (1, cos s, sin s)` through `linkCover` and the intermediate
value theorem), so the wedge link exists and has the signs of the assembly. -/
theorem arc_wedge {x : HS 2} (hx0 : 0 ≤ 𝐐 (x : 𝕄))
    (hBs : ∀ s ∈ Icc (π / 2) π, 𝐁 (x : 𝕄) (qPt s) ≠ 0)
    (hx : x ∈ region (qPt (π / 2)) (qPt π))
    (hdir : dirOf x (qPt (π / 2)) ≠ dirOf x (qPt π)) :
    ∃ (θ : TpHS x ≃ₗ[ℝ] ℂ) (a b : ℝ) (h : GammaP x), IsOrientedTangent x θ ∧ a < b ∧
      b < a + 2 ∧ (∀ t ∈ Icc a b, ∃ q ∈ arcP, linkCover x θ t = dirOf x q) ∧
      ((linkCover x θ a = dirOf x (qPt (π / 2)) ∧ linkCover x θ b = dirOf x (qPt π) ∧
          h = (wedgeIsom (qPt_mem _) (qPt_mem _) hx)⁻¹) ∨
        (linkCover x θ a = dirOf x (qPt π) ∧ linkCover x θ b = dirOf x (qPt (π / 2)) ∧
          h = wedgeIsom (qPt_mem _) (qPt_mem _) hx)) ∧
      ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link x) L)
        (hcs : HasGroupoid L (gxGroupoid (GammaP x) (Link x))) (hL : IsCircle L),
        (GammaLinkCircle.mk x cs hcs hL).IsWedgeLink θ a b h ∧
        (𝐐 (x : 𝕄) = 0 →
          (GammaLinkCircle.mk x cs hcs hL).IsLightlikeNegative ∧
          (GammaLinkCircle.mk x cs hcs hL).IsLightlikePositiveGlue ∧
          ¬ (GammaLinkCircle.mk x cs hcs hL).IsPositive) ∧
        (x ∈ HS.piece 2 .deSitter →
          (GammaLinkCircle.mk x cs hcs hL).IsSpacelikeNegative ∧
          (GammaLinkCircle.mk x cs hcs hL).IsSpacelikePositiveGlue ∧
          ¬ (GammaLinkCircle.mk x cs hcs hL).IsPositive) := by
  have hP := arcP_subset
  have hPx : ∀ q ∈ arcP, 𝐁 (x : 𝕄) q ≠ 0 := by
    rintro _ ⟨s, hs, rfl⟩; exact hBs s hs
  obtain ⟨θ, a, b, h, hθ, hab, hba, hW, hends⟩ := arc_wedge_ends hBs hx hdir
    fun θ {a b h} hW hh hab' => by
      have hh1 : h ≠ 1 := by rintro rfl; rw [one_smul] at hh; exact hab' hh.symm
      have hnf : ∀ t ∈ Icc a b, h • linkCover x θ t ≠ linkCover x θ t := fun t ht => by
        obtain ⟨q, hq, hqt⟩ := hW t ht
        rw [hqt]
        exact smul_dirOf_ne hx0 (bdPlus_null (hP hq)) (hPx q hq) hh1
      have := wedge_short hx0 hnf
      linarith
  obtain ⟨⟨L, _, cs, hcs, hL, hC⟩, hall⟩ := bbsrem_cheminsing_reading (qPt_mem (π / 2))
    (qPt_mem π) hP hx hPx hθ hab hba hW hends
  obtain ⟨-, hnull, hds⟩ := hall cs hcs hL hC
  exact ⟨θ, a, b, h, hθ, hab, hba, hW, hends, L, inferInstance, cs, hcs, hL, hC, hnull, hds⟩

/-- **The wedge over the arc `arcP`, at a time-like `x ∈ ℍ²₊`** (the elliptic branch): every
hypothesis of `GX.bbsrem_cheminsing_reading` holds, and the wedge link is an elliptic singularity
of positive mass. The wedge is shorter than a turn because `q ↦ dir_x q` is injective on `∂ℍ²₊`
(`eq_of_dirOf_eq`) and `qPt 0 ∉ arcP`. -/
theorem arc_wedge_timelike {x : HS 2} (hxt : x ∈ HS.piece 2 .hypPlus) :
    ∃ (θ : TpHS x ≃ₗ[ℝ] ℂ) (a b : ℝ) (h : GammaP x), IsOrientedTangent x θ ∧ a < b ∧
      b < a + 2 ∧ (∀ t ∈ Icc a b, ∃ q ∈ arcP, linkCover x θ t = dirOf x q) ∧
      ((linkCover x θ a = dirOf x (qPt (π / 2)) ∧ linkCover x θ b = dirOf x (qPt π) ∧
          h = (wedgeIsom (qPt_mem (π / 2)) (qPt_mem π)
            (hypPlus_subset_region (qPt_mem (π / 2)) (qPt_mem π) hxt))⁻¹) ∨
        (linkCover x θ a = dirOf x (qPt π) ∧ linkCover x θ b = dirOf x (qPt (π / 2)) ∧
          h = wedgeIsom (qPt_mem (π / 2)) (qPt_mem π)
            (hypPlus_subset_region (qPt_mem (π / 2)) (qPt_mem π) hxt))) ∧
      ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link x) L)
        (hcs : HasGroupoid L (gxGroupoid (GammaP x) (Link x))) (hL : IsCircle L),
        (GammaLinkCircle.mk x cs hcs hL).IsWedgeLink θ a b h ∧
        (GammaLinkCircle.mk x cs hcs hL).coneAngle < 2 * π ∧
        0 < (GammaLinkCircle.mk x cs hcs hL).mass ∧
        (GammaLinkCircle.mk x cs hcs hL).IsPositive ∧
        ¬ (GammaLinkCircle.mk x cs hcs hL).IsRegular := by
  have hP := arcP_subset
  have hx := hypPlus_subset_region (qPt_mem (π / 2)) (qPt_mem π) hxt
  have hneg : ∀ q ∈ HS.piece 2 .bdPlus, 𝐁 (x : 𝕄) q < 0 := fun q hq =>
    minkB_neg_of_hypPlus hxt hq
  have hPx : ∀ q ∈ arcP, 𝐁 (x : 𝕄) q ≠ 0 := fun q hq => (hneg q (hP hq)).ne
  have hBs : ∀ s ∈ Icc (π / 2) π, 𝐁 (x : 𝕄) (qPt s) ≠ 0 := fun s _ => (hneg _ (qPt_mem s)).ne
  have hdir : dirOf x (qPt (π / 2)) ≠ dirOf x (qPt π) := fun he => by
    have e := eq_of_dirOf_eq (qPt_mem _) (qPt_mem _)
      (mul_pos_of_neg_of_neg (hneg _ (qPt_mem _)) (hneg _ (qPt_mem _))) he
    have h := minkB_qPt (π / 2) π
    rw [e, ← minkQ_eq_minkB, bdPlus_null (qPt_mem _),
      show π / 2 - π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two] at h
    norm_num at h
  obtain ⟨θ, a, b, h, hθ, hab, hba, hW, hends⟩ := arc_wedge_ends hBs hx hdir
    fun θ {a b h} hW _ _ => by
      by_contra hcon
      push Not at hcon
      obtain ⟨t₀, ht₀⟩ := linkCover_surjective x θ (dirOf x (qPt 0))
      have h1 : a ≤ t₀ + 2 * (⌈(a - t₀) / 2⌉ : ℤ) := by
        have := Int.le_ceil ((a - t₀) / 2); linarith
      have h2 : t₀ + 2 * (⌈(a - t₀) / 2⌉ : ℤ) < a + 2 := by
        have := Int.ceil_lt_add_one ((a - t₀) / 2); linarith
      obtain ⟨q, hq, hqt⟩ := hW _ ⟨h1, by linarith⟩
      rw [linkCover_add_two_mul, ht₀] at hqt
      have e := eq_of_dirOf_eq (qPt_mem 0) (hP hq)
        (mul_pos_of_neg_of_neg (hneg _ (qPt_mem 0)) (hneg _ (hP hq))) hqt
      exact qPt_zero_not_mem_arcP (by rw [e]; exact hq)
  obtain ⟨⟨L, _, cs, hcs, hL, hC⟩, hall⟩ := bbsrem_cheminsing_reading (qPt_mem (π / 2))
    (qPt_mem π) hP hx hPx hθ hab hba hW hends
  obtain ⟨hell, -, -⟩ := hall cs hcs hL hC
  obtain ⟨h1, h2, h3, h4⟩ := hell hxt.2
  exact ⟨θ, a, b, h, hθ, hab, hba, hW, hends, L, inferInstance, cs, hcs, hL, hC, h1, h2, h3, h4⟩

/-- **The elliptic clause of `bbsrem:cheminsing` on an explicit instance**: at the pole
`x = [(1, 0, 0)] ∈ ℍ²₊`, the wedge over the arc `arcP` from `p₁ = (1, 0, 1)` to `p₂ = (1, −1, 0)`,
glued back by `γ_x^{±1}`, satisfies every hypothesis of `GX.bbsrem_cheminsing_reading`, and its
link is an elliptic singularity (cone angle `< 2π`) of positive mass, positive and not regular:
the elliptic branch of the assembly is not vacuous. -/
theorem cheminsing_timelike_pole :
    ∃ (hx : HS.pole 2 ∈ region (qPt (π / 2)) (qPt π)) (θ : TpHS (HS.pole 2) ≃ₗ[ℝ] ℂ) (a b : ℝ)
      (h : GammaP (HS.pole 2)),
      HS.pole 2 ∈ HS.piece 2 .hypPlus ∧ (∀ q ∈ arcP, 𝐁 (HS.pole 2 : 𝕄) q ≠ 0) ∧
      IsOrientedTangent (HS.pole 2) θ ∧ a < b ∧ b < a + 2 ∧
      (∀ t ∈ Icc a b, ∃ q ∈ arcP, linkCover (HS.pole 2) θ t = dirOf (HS.pole 2) q) ∧
      ((linkCover (HS.pole 2) θ a = dirOf (HS.pole 2) (qPt (π / 2)) ∧
          linkCover (HS.pole 2) θ b = dirOf (HS.pole 2) (qPt π) ∧
          h = (wedgeIsom (qPt_mem _) (qPt_mem _) hx)⁻¹) ∨
        (linkCover (HS.pole 2) θ a = dirOf (HS.pole 2) (qPt π) ∧
          linkCover (HS.pole 2) θ b = dirOf (HS.pole 2) (qPt (π / 2)) ∧
          h = wedgeIsom (qPt_mem _) (qPt_mem _) hx)) ∧
      ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link (HS.pole 2)) L)
        (hcs : HasGroupoid L (gxGroupoid (GammaP (HS.pole 2)) (Link (HS.pole 2))))
        (hL : IsCircle L),
        (GammaLinkCircle.mk (HS.pole 2) cs hcs hL).IsWedgeLink θ a b h ∧
        (GammaLinkCircle.mk (HS.pole 2) cs hcs hL).coneAngle < 2 * π ∧
        0 < (GammaLinkCircle.mk (HS.pole 2) cs hcs hL).mass ∧
        (GammaLinkCircle.mk (HS.pole 2) cs hcs hL).IsPositive ∧
        ¬ (GammaLinkCircle.mk (HS.pole 2) cs hcs hL).IsRegular := by
  have hxt := HS.pole_mem_hypPlus (d := 2)
  obtain ⟨θ, a, b, h, hθ, hab, hba, hW, hends, L, _, cs, hcs, hL, hC, h1, h2, h3, h4⟩ :=
    arc_wedge_timelike hxt
  exact ⟨hypPlus_subset_region (qPt_mem _) (qPt_mem _) hxt, θ, a, b, h, hxt,
    fun q hq => (minkB_neg_of_hypPlus hxt (arcP_subset hq)).ne, hθ, hab, hba, hW, hends, L,
    inferInstance, cs, hcs, hL, hC, h1, h2, h3, h4⟩

end Cheminsing

open Cheminsing in
/-- **The light-like clause of `bbsrem:cheminsing` fails in the library's holonomy convention**,
on an explicit instance: `x_∞ = (1, 1, 0) ∈ ∂ℍ²₊`, off the arc `arcP` from `p₁ = (1, 0, 1)` to
`p₂ = (1, −1, 0)`, in the region of `γ_{x_∞}`; the wedge `[a, b]` (`a < b < a + 2`) at `x_∞`, all
of whose directions point to the arc, with ends the directions of `p₁, p₂`, glued back by the
paper's `γ_{x_∞}^{±1}` (`wedgeIsom`, `hends`) — a member of the family of
`GX.bbsrem_cheminsing_reading` — is a light-like singularity which is **negative**
(`IsLightlikeNegative`), not positive (`IsPositive`), and positive in the gluing-map convention
(`IsLightlikePositiveGlue`). -/
theorem not_cheminsing_lightlike_positive :
    ∃ (hx : qPt 0 ∈ region (qPt (π / 2)) (qPt π)) (θ : TpHS (qPt 0) ≃ₗ[ℝ] ℂ) (a b : ℝ)
      (h : GammaP (qPt 0)),
      qPt 0 ∈ HS.piece 2 .bdPlus ∧ qPt 0 ∉ arcP ∧ (∀ q ∈ arcP, 𝐁 (qPt 0 : 𝕄) q ≠ 0) ∧
      IsOrientedTangent (qPt 0) θ ∧ a < b ∧ b < a + 2 ∧
      (∀ t ∈ Icc a b, ∃ q ∈ arcP, linkCover (qPt 0) θ t = dirOf (qPt 0) q) ∧
      ((linkCover (qPt 0) θ a = dirOf (qPt 0) (qPt (π / 2)) ∧
          linkCover (qPt 0) θ b = dirOf (qPt 0) (qPt π) ∧
          h = (wedgeIsom (qPt_mem _) (qPt_mem _) hx)⁻¹) ∨
        (linkCover (qPt 0) θ a = dirOf (qPt 0) (qPt π) ∧
          linkCover (qPt 0) θ b = dirOf (qPt 0) (qPt (π / 2)) ∧
          h = wedgeIsom (qPt_mem _) (qPt_mem _) hx)) ∧
      ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link (qPt 0)) L)
        (hcs : HasGroupoid L (gxGroupoid (GammaP (qPt 0)) (Link (qPt 0)))) (hL : IsCircle L),
        (GammaLinkCircle.mk (qPt 0) cs hcs hL).IsWedgeLink θ a b h ∧
        (GammaLinkCircle.mk (qPt 0) cs hcs hL).IsLightlikeNegative ∧
        (GammaLinkCircle.mk (qPt 0) cs hcs hL).IsLightlikePositiveGlue ∧
        ¬ (GammaLinkCircle.mk (qPt 0) cs hcs hL).IsPositive := by
  have hle : π / 2 ≤ π := by linarith [Real.pi_pos]
  have hBs : ∀ s ∈ Icc (π / 2) π, 𝐁 (qPt 0 : 𝕄) (qPt s) ≠ 0 := fun s hs => by
    rw [minkB_qPt, zero_sub, Real.cos_neg]
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hs.1 (by linarith [hs.2, Real.pi_pos])
    linarith
  have hm₁ : π / 2 ∈ Icc (π / 2) π := ⟨le_rfl, hle⟩
  have hm₂ : π ∈ Icc (π / 2) π := ⟨hle, le_rfl⟩
  have hxq : ∀ s ∈ Icc (π / 2) π, qPt 0 ≠ qPt s := fun s hs he => hBs s hs (by
    rw [← he, ← minkQ_eq_minkB]; exact bdPlus_null (qPt_mem 0))
  have hx : qPt 0 ∈ region (qPt (π / 2)) (qPt π) :=
    bdPlus_mem_region (qPt_mem _) (qPt_mem _) (qPt_mem 0) (hxq _ hm₁) (hxq _ hm₂)
  have hnull : 𝐐 (qPt 0 : 𝕄) = 0 := bdPlus_null (qPt_mem 0)
  have hx2 : (qPt 0 : 𝕄).2 1 = 0 := by rw [coe_qPt, mink3_snd_one, Real.sin_zero]
  obtain ⟨θ, a, b, h, hθ, hab, hba, hW, hends, L, _, cs, hcs, hL, hC, hN, -⟩ :=
    arc_wedge hnull.ge hBs hx (dirOf_arc_ne hx2 (hBs _ hm₁) (hBs _ hm₂))
  obtain ⟨h1, h2, h3⟩ := hN hnull
  exact ⟨hx, θ, a, b, h, qPt_mem 0, qPt_zero_not_mem_arcP,
    by rintro _ ⟨s, hs, rfl⟩; exact hBs s hs, hθ, hab, hba, hW, hends, L,
    inferInstance, cs, hcs, hL, hC, h1, h2, h3⟩

open Cheminsing in
/-- **The space-like clause of `bbsrem:cheminsing` (« positive mass », read as positive in the
sense of l.906–915) fails in the library's holonomy convention**, on an explicit instance:
`x = [x_∞ − e_t/2] = [(1/2, 1, 0)] ∈ dS²`, a point of the deformation `defPath` past `x_∞`, in
the region of `γ_x`; the wedge `[a, b]` (`a < b < a + 2`) at `x`, all of whose directions point
to the arc `arcP`, with ends the directions of `p₁, p₂`, glued back by the paper's `γ_x^{±1}`
(`wedgeIsom`, `hends`) — a member of the family of `GX.bbsrem_cheminsing_reading` — is a
space-like singularity which is **negative** (`IsSpacelikeNegative`), not positive, and positive
in the gluing-map convention (`IsSpacelikePositiveGlue`). -/
theorem not_cheminsing_spacelike_positive :
    ∃ (hx : defPath (qPt 0) (1 / 2) ∈ region (qPt (π / 2)) (qPt π))
      (θ : TpHS (defPath (qPt 0) (1 / 2)) ≃ₗ[ℝ] ℂ) (a b : ℝ)
      (h : GammaP (defPath (qPt 0) (1 / 2))),
      defPath (qPt 0) (1 / 2) ∈ HS.piece 2 .deSitter ∧
      (∀ q ∈ arcP, 𝐁 (defPath (qPt 0) (1 / 2) : 𝕄) q ≠ 0) ∧
      IsOrientedTangent (defPath (qPt 0) (1 / 2)) θ ∧ a < b ∧ b < a + 2 ∧
      (∀ t ∈ Icc a b, ∃ q ∈ arcP, linkCover (defPath (qPt 0) (1 / 2)) θ t =
        dirOf (defPath (qPt 0) (1 / 2)) q) ∧
      ((linkCover (defPath (qPt 0) (1 / 2)) θ a = dirOf (defPath (qPt 0) (1 / 2)) (qPt (π / 2)) ∧
          linkCover (defPath (qPt 0) (1 / 2)) θ b = dirOf (defPath (qPt 0) (1 / 2)) (qPt π) ∧
          h = (wedgeIsom (qPt_mem _) (qPt_mem _) hx)⁻¹) ∨
        (linkCover (defPath (qPt 0) (1 / 2)) θ a = dirOf (defPath (qPt 0) (1 / 2)) (qPt π) ∧
          linkCover (defPath (qPt 0) (1 / 2)) θ b =
            dirOf (defPath (qPt 0) (1 / 2)) (qPt (π / 2)) ∧
          h = wedgeIsom (qPt_mem _) (qPt_mem _) hx)) ∧
      ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link (defPath (qPt 0) (1 / 2))) L)
        (hcs : HasGroupoid L (gxGroupoid (GammaP (defPath (qPt 0) (1 / 2)))
          (Link (defPath (qPt 0) (1 / 2))))) (hL : IsCircle L),
        (GammaLinkCircle.mk (defPath (qPt 0) (1 / 2)) cs hcs hL).IsWedgeLink θ a b h ∧
        (GammaLinkCircle.mk (defPath (qPt 0) (1 / 2)) cs hcs hL).IsSpacelikeNegative ∧
        (GammaLinkCircle.mk (defPath (qPt 0) (1 / 2)) cs hcs hL).IsSpacelikePositiveGlue ∧
        ¬ (GammaLinkCircle.mk (defPath (qPt 0) (1 / 2)) cs hcs hL).IsPositive := by
  have hle : π / 2 ≤ π := by linarith [Real.pi_pos]
  have h0 := qPt_mem 0
  set v : 𝕄 := (qPt 0 : 𝕄) - (1 / 2 : ℝ) • Causal.Flat.timeUnit 2 with hv
  have hv0 : v ≠ 0 := defPath_vec_ne h0 (1 / 2)
  have hcoe : (defPath (qPt 0) (1 / 2) : 𝕄) = ‖v‖⁻¹ • v := coe_rayNormalize _ hv0
  have hk : 0 < ‖v‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hv0)
  have hBv : ∀ s, 𝐁 v (qPt s) = -(1 / 2) + Real.cos s := fun s => by
    rw [hv, minkB_sub_left, minkB_smul_left, minkB_qPt, zero_sub,
      Real.cos_neg, coe_qPt, minkB_coords]
    simp only [Causal.Flat.timeUnit, mink3_fst, mink3_snd_zero, mink3_snd_one]
    simp
    ring
  have hB : ∀ s, 𝐁 (defPath (qPt 0) (1 / 2) : 𝕄) (qPt s) =
      ‖v‖⁻¹ * (-(1 / 2) + Real.cos s) := fun s => by
    rw [hcoe, minkB_smul_left, hBv]
  have hneg : ∀ s ∈ Icc (π / 2) π,
      𝐁 (defPath (qPt 0) (1 / 2) : 𝕄) (qPt s) < 0 := fun s hs => by
    rw [hB]
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hs.1 (by linarith [hs.2, Real.pi_pos])
    exact mul_neg_of_pos_of_neg hk (by linarith)
  have hBs : ∀ s ∈ Icc (π / 2) π,
      𝐁 (defPath (qPt 0) (1 / 2) : 𝕄) (qPt s) ≠ 0 := fun s hs => (hneg s hs).ne
  have hm₁ : π / 2 ∈ Icc (π / 2) π := ⟨le_rfl, hle⟩
  have hm₂ : π ∈ Icc (π / 2) π := ⟨hle, le_rfl⟩
  have hx : defPath (qPt 0) (1 / 2) ∈ region (qPt (π / 2)) (qPt π) :=
    mul_pos_of_neg_of_neg (hneg _ hm₁) (hneg _ hm₂)
  have hds : defPath (qPt 0) (1 / 2) ∈ HS.piece 2 .deSitter := by
    show 0 < 𝐐 (defPath (qPt 0) (1 / 2) : 𝕄)
    rw [hcoe, HS.minkQ_smul_pos_iff hk, hv, minkQ_defPath_vec h0]
    norm_num
  have hx2 : (defPath (qPt 0) (1 / 2) : 𝕄).2 1 = 0 := by
    rw [hcoe, hv]
    simp only [Prod.smul_snd, Prod.snd_sub, PiLp.smul_apply, coe_qPt, mink3_snd_one,
      Real.sin_zero, Causal.Flat.timeUnit, smul_zero, sub_zero, smul_eq_mul, mul_zero]
  obtain ⟨θ, a, b, h, hθ, hab, hba, hW, hends, L, _, cs, hcs, hL, hC, -, hS⟩ :=
    arc_wedge (le_of_lt hds) hBs hx (dirOf_arc_ne hx2 (hBs _ hm₁) (hBs _ hm₂))
  obtain ⟨h1, h2, h3⟩ := hS hds
  exact ⟨hx, θ, a, b, h, hds, by rintro _ ⟨s, hs, rfl⟩; exact hBs s hs, hθ, hab, hba, hW, hends,
    L, inferInstance, cs, hcs, hL, hC, h1, h2, h3⟩

end GX
