import GX.BBS.HSSuspension
import GXScaffold.BBS.HSCheminsing
import GXScaffold.Interaction.FunnelGTilde

/-!
# BBS § 4.1: space-like geodesics of the de Sitter part, positive mass, and the link of a massive particle

Target `T-bbs-positive-mass` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx, wave W4).
`papers/bbs/legacy/labeled/colI_v1.tex`. 0 `sorry`, standard axioms only. Imports the strict
`GX.BBS.HSSuspension` (`𝔢(L)`, singular HS-structures) and the sorry-free scaffold
`GXScaffold.BBS.HSCheminsing` (cone angle, mass, positivity) and `GXScaffold.Interaction.FunnelGTilde`
(the rotation lifts `R̃(φ)`).

* `bbsdef:has_positive_mass_simple` — `colI_v1.tex:1821` — partial (unmarked: readings (a)–(d) of
  SCOPE, a question): `GX.SingularHSStructure.HasPositiveMass`, through
  `GX.SingularHSStructure.IsSpacelikeGeodesic` (a curve of regular points which is, in a chart, a
  unit-speed great circle `GX.dsGeo` of `dS²`; chart-free, `…IsSpacelikeGeodesic.forall_chart`; in
  the de Sitter part, `…IsSpacelikeGeodesic.mem_deSitter`) and
  `GX.SingularHSStructure.IsSimpleClosedSpacelikeGeodesic` (period `ℓ` = length, injective on one
  period). The sentence after it (l.1826–1827) is `GX.GammaLinkCircle.DevData.hasPositiveMass_iff`,
  `…hasPositiveMass_iff_mass_pos`, `…hasPositiveMass_iff_isPositive`.
* `bbsrem:singular_ads_manifold_cone` — `colI_v1.tex:1797` — partial (unmarked: the link form
  only; « an explicit description of `L_x` follows from the construction of the AdS metric » is the
  AdS background, T-bbs-q8): for a time-like singularity, the link `𝔢(L)`.
  `GX.GammaLinkCircle.DevData.link_simpleClosed_geodesic` (cone angle `θ < 2π`: a simple closed
  space-like geodesic exists, it is unique, of length `θ < 2π`), from the three statements valid
  for every time-like `p`: `…exists_simpleClosed_equator` (the equator, of length `θ`),
  `…length_eq_coneAngle` (every one has length `θ`), `…range_eq_equator` (`θ ∉ 2πℤ`: every one is
  the equator).

> Let $M$ be a singular AdS manifold, $c$ be a cone singularity along a time-like
> curve, with positive mass (angle less than $2\pi$). Let $x\in c$ and let $L_x$ be
> the link of $M$ at $x$, and let $\gamma$ be a simple closed space-like geodesic in
> the de Sitter part of $L_x$. Then the length of $\gamma$ is less than $2\pi$. (l.1797–1802)
>
> An explicit description of $L_x$ follows from the construction of the AdS metric
> in the neighborhood of a time-like singularity, as seen in Section 2. The
> de Sitter part of this link contains a unique simple closed geodesic, and its
> length is equal to the angle at the singularity. So it is less than $2\pi$. (l.1805–1808)
>
> $\sigma$ has {\bf positive mass} if any simple closed space-like geodesic in the de
> Sitter part of $(S^2,\sigma)$ has length less than $2\pi$. (l.1822–1823)
>
> This notion of positivity of mass for an interaction generalizes the natural notion
> of positivity for time-like singularities. (l.1826–1827)

## Hypothesis checklist

| BBS | here |
|---|---|
| « $\sigma$ » on $S^2$, link of an interaction with massive particles and tachyons, positive, causal, two hyperbolic components (l.1812–1819) | ⚠ weakened: any `GX.SingularHSStructure` on any space |
| « simple closed space-like geodesic in the de Sitter part » | ⚠ read: unit-speed, in the charts (SCOPE (a), (b)); avoids `𝒮` (SCOPE (c)) |
| « length » | ✓ the period of the arc-length parametrisation (the de Sitter length) |
| « $c$ a cone singularity along a time-like curve » (l.1798) | ✓ for its link: a `(Γ_p, ℓ(p))`-circle at a time-like `p` (`minkQ p < 0`), future or past |
| « positive mass (angle less than $2\pi$) » | ✓ `C.coneAngle < 2π` (`GX.GammaLinkCircle.mass_pos_iff`) |
| « $L_x$ the link of $M$ at $x$ » | ⚠ read: `𝔢(L)` for the type `L` of `c` (SCOPE (e)) |

## SCOPE (disclosed)

* **(a) Arc length.** A geodesic is parametrised by arc length: `γ` is, in a chart near each
  parameter, `s ↦ [cos s · x + sin s · v]` with `Q x = Q v = 1`, `B(x, v) = 0` (the hyperboloid
  model of `dS²` inside `HS²`). Its length over one period is the period `ℓ`; « simple closed » is
  `ℓ`-periodic and injective on `[0, ℓ)`. Every space-like geodesic of `dS²` is such an arc of a
  space-like plane (argued: time-like and degenerate planes give time-like and light-like ones).
* **(b) In the charts.** « Read through the developing map » is read chart by chart, which is the
  same: the chart changes lie in `SO₀(1,2)` (`…forall_chart`).
* **(c) Singular points.** A geodesic avoids `𝒮`. For an interaction the de Sitter part contains
  tachyons (space-like singularities); whether a geodesic may pass through one is not settled by
  l.1822: a question. It is immaterial for `𝔢(L)` at a time-like `p`, whose apices are hyperbolic.
* **(d) Generality.** The definition is stated for every singular HS-structure, not only under the
  standing hypotheses of l.1812–1819.
* **(e) The AdS side.** No AdS spacetime here (T-bbs-q8): the link `L_x` of a point of a time-like
  cone singularity of angle `θ` is read as `𝔢(L)` for the elliptic `(Γ_p, ℓ(p))`-circle `L` of cone
  angle `θ` (`GX.GammaLinkCircle.coneAngle`, half the real angle of the link, OQ-113), for every
  choice of developing data `Δ`.
* **(f) The proof.** In a frame `A ∈ SO₀(1,2)` with `A e₀ ∈ ℝp` (`GX.TFrame`), `Γ_p` acts by
  rotations; the developing data has an angle `Φ` with `Φ(s+1) = Φ(s) + c`, `|c| = θ`
  (`…exists_angle`). A space-like geodesic lifts to the covering `ℝ × ]0, π[` of the regular part
  and develops onto one great circle (`…geodesic_lift`, `GX.exists_dsGeo_of_local`). The
  great-circle lemma `GX.TFrame.great_circle`: the equator `p^⊥` closes after `|m| θ` and is simple
  iff `|m| = 1`; any other great circle is periodic of period `2πk` only, winds once around `p`,
  and an intermediate value argument (`GX.exists_shift_eq`) finds a self-intersection unless
  `θ = 2πk`. So `ℓ = θ` always, and the geodesic is the equator unless `θ ∈ 2πℤ`.
* **(g) Not formalized:** for `θ ∈ 2πℤ` (e.g. a regular point, `θ = 2π`) the equator is not the
  only simple closed geodesic (every great circle of `dS²` is one when `θ = 2π`; argued); the
  remark excludes it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal
`51cbb00` through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology Real

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. Space-like geodesics of the de Sitter part, their length, positive mass -/

/-- `(x, v)` spans a space-like plane, orthonormally: `Q x = Q v = 1`, `B(x, v) = 0`. -/
def IsDSFrame (x v : 𝕄) : Prop :=
  Causal.Flat.minkQ x = 1 ∧ Causal.Flat.minkQ v = 1 ∧ Causal.Flat.minkB x v = 0

/-- The unit-speed space-like geodesic of `dS² ⊂ HS²` through `[x]` with velocity `v`, read in
the hyperboloid model `Q = 1`: `s ↦ [cos s · x + sin s · v]`. -/
def dsGeo (x v : 𝕄) (s : ℝ) : HS 2 :=
  rayNormalize (HS.pole 2) (Real.cos s • x + Real.sin s • v)

/-! ### Great circles of `dS²` -/

/-- The vector `cos s · x + sin s · v`. -/
def dsVec (x v : 𝕄) (s : ℝ) : 𝕄 := Real.cos s • x + Real.sin s • v

theorem dsGeo_eq (x v : 𝕄) (s : ℝ) : dsGeo x v s = rayNormalize (HS.pole 2) (dsVec x v s) := rfl

theorem minkQ_dsVec {x v : 𝕄} (h : IsDSFrame x v) (s : ℝ) :
    Causal.Flat.minkQ (dsVec x v s) = 1 := by
  obtain ⟨hx, hv, hxv⟩ := h
  rw [minkQ_two] at hx hv ⊢
  rw [minkB_two] at hxv
  simp only [dsVec, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  have := Real.sin_sq_add_cos_sq s
  linear_combination Real.cos s ^ 2 * hx + Real.sin s ^ 2 * hv + 2 * Real.cos s * Real.sin s * hxv +
    this

theorem dsVec_ne_zero {x v : 𝕄} (h : IsDSFrame x v) (s : ℝ) : dsVec x v s ≠ 0 := by
  intro h0
  have := minkQ_dsVec h s
  rw [h0] at this
  simp [Causal.Flat.minkQ] at this

theorem continuous_dsVec (x v : 𝕄) : Continuous (dsVec x v) :=
  (Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)

theorem continuous_dsGeo {x v : 𝕄} (h : IsDSFrame x v) : Continuous (dsGeo x v) :=
  continuous_iff_continuousAt.2 fun s =>
    (continuousAt_rayNormalize _ (dsVec_ne_zero h s)).comp (continuous_dsVec x v).continuousAt

/-- Two vectors of the same ray. -/
theorem rayNormalize_eq_rayNormalize_iff {u w : 𝕄} (hu : u ≠ 0) (hw : w ≠ 0) :
    rayNormalize (HS.pole 2) u = rayNormalize (HS.pole 2) w ↔ ∃ c : ℝ, 0 < c ∧ u = c • w := by
  constructor
  · intro h
    have h' := congrArg (fun σ : HS 2 => (σ : 𝕄)) h
    simp only [coe_rayNormalize _ hu, coe_rayNormalize _ hw] at h'
    have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw
    refine ⟨‖u‖ / ‖w‖, div_pos hnu hnw, ?_⟩
    calc u = ‖u‖ • (‖u‖⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hnu.ne', one_smul]
      _ = ‖u‖ • (‖w‖⁻¹ • w) := by rw [h']
      _ = _ := by rw [smul_smul, div_eq_mul_inv]
  · rintro ⟨c, hc, rfl⟩
    exact rayNormalize_smul_of_pos _ hw hc

/-- Two vectors of the same ray with the same `Q = 1` are equal. -/
theorem eq_of_rayNormalize_eq_of_minkQ {u w : 𝕄} (hu : Causal.Flat.minkQ u = 1)
    (hw : Causal.Flat.minkQ w = 1)
    (h : rayNormalize (HS.pole 2) u = rayNormalize (HS.pole 2) w) : u = w := by
  have hu0 : u ≠ 0 := by rintro rfl; simp [Causal.Flat.minkQ] at hu
  have hw0 : w ≠ 0 := by rintro rfl; simp [Causal.Flat.minkQ] at hw
  obtain ⟨c, hc, rfl⟩ := (rayNormalize_eq_rayNormalize_iff hu0 hw0).1 h
  have : Causal.Flat.minkQ (c • w) = c ^ 2 * Causal.Flat.minkQ w := by
    rw [minkQ_two, minkQ_two]
    simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [this, hw, mul_one] at hu
  have hc1 : c = 1 := by nlinarith
  rw [hc1, one_smul]

theorem dsGeo_eq_dsGeo_iff {x v x' v' : 𝕄} (h : IsDSFrame x v) (h' : IsDSFrame x' v') (s : ℝ) :
    dsGeo x v s = dsGeo x' v' s ↔ dsVec x v s = dsVec x' v' s := by
  refine ⟨fun e => eq_of_rayNormalize_eq_of_minkQ (minkQ_dsVec h s) (minkQ_dsVec h' s) e,
    fun e => by rw [dsGeo_eq, dsGeo_eq, e]⟩

/-- Two great circles agreeing near a point are equal. -/
theorem dsFrame_eq_of_eventuallyEq {x v x' v' : 𝕄} (h : IsDSFrame x v) (h' : IsDSFrame x' v')
    {s₀ : ℝ} (he : ∀ᶠ s in 𝓝 s₀, dsGeo x v s = dsGeo x' v' s) : x = x' ∧ v = v' := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 he
  set s₁ := s₀ + min (ε / 2) 1
  have hd : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
  have hd1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
  have h0 := (dsGeo_eq_dsGeo_iff h h' s₀).1 (hball (by simp [hε]))
  have h1 := (dsGeo_eq_dsGeo_iff h h' s₁).1 (hball (by
    rw [Real.dist_eq, show s₁ - s₀ = min (ε / 2) 1 by ring, abs_of_pos hd]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)))
  have hsin : Real.sin (s₁ - s₀) ≠ 0 := by
    rw [show s₁ - s₀ = min (ε / 2) 1 by ring]
    exact (Real.sin_pos_of_pos_of_lt_pi hd (by linarith [Real.pi_gt_three])).ne'
  simp only [dsVec] at h0 h1
  -- `sin (s₁ - s₀) • (x - x') = 0`
  have ex : Real.sin (s₁ - s₀) • (x - x') = 0 := by
    rw [Real.sin_sub]
    have : (Real.sin s₁ * Real.cos s₀ - Real.cos s₁ * Real.sin s₀) • (x - x') =
        Real.sin s₁ • (Real.cos s₀ • x + Real.sin s₀ • v - (Real.cos s₀ • x' + Real.sin s₀ • v'))
          - Real.sin s₀ • (Real.cos s₁ • x + Real.sin s₁ • v -
            (Real.cos s₁ • x' + Real.sin s₁ • v')) := by
      simp only [smul_sub, smul_add, smul_smul, sub_smul]
      module
    rw [this, h0, h1, sub_self, sub_self, smul_zero, smul_zero, sub_zero]
  have ev : Real.sin (s₁ - s₀) • (v - v') = 0 := by
    rw [Real.sin_sub]
    have : (Real.sin s₁ * Real.cos s₀ - Real.cos s₁ * Real.sin s₀) • (v - v') =
        Real.cos s₀ • (Real.cos s₁ • x + Real.sin s₁ • v - (Real.cos s₁ • x' + Real.sin s₁ • v'))
          - Real.cos s₁ • (Real.cos s₀ • x + Real.sin s₀ • v -
            (Real.cos s₀ • x' + Real.sin s₀ • v')) := by
      simp only [smul_sub, smul_add, smul_smul, sub_smul]
      module
    rw [this, h0, h1, sub_self, sub_self, smul_zero, smul_zero, sub_zero]
  exact ⟨sub_eq_zero.1 ((smul_eq_zero.1 ex).resolve_left hsin),
    sub_eq_zero.1 ((smul_eq_zero.1 ev).resolve_left hsin)⟩

/-- **Local to global**: a curve of `HS²` which is near every parameter a unit-speed great circle
of `dS²` is one great circle. -/
theorem exists_dsGeo_of_local {δ : ℝ → HS 2}
    (hloc : ∀ s, ∃ x v : 𝕄, IsDSFrame x v ∧ ∀ᶠ s' in 𝓝 s, δ s' = dsGeo x v s') :
    ∃ x v : 𝕄, IsDSFrame x v ∧ ∀ s, δ s = dsGeo x v s := by
  obtain ⟨x₀, v₀, h₀, he₀⟩ := hloc 0
  set S := {s | ∀ᶠ s' in 𝓝 s, δ s' = dsGeo x₀ v₀ s'} with hS_def
  have hS0 : (0 : ℝ) ∈ S := he₀
  have hSo : IsOpen S := isOpen_iff_mem_nhds.2 fun s hs => hs.eventually_nhds
  have hSc : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨x, v, h, he⟩ := hloc s
    obtain ⟨U, hU, hUo, hsU⟩ := eventually_nhds_iff.1 he
    refine Filter.mem_of_superset (hUo.mem_nhds hsU) fun s' hs' hs'S => hs ?_
    have hboth : ∀ᶠ s'' in 𝓝 s', dsGeo x v s'' = dsGeo x₀ v₀ s'' := by
      filter_upwards [hUo.mem_nhds hs', hs'S] with s'' h1 h2
      rw [← hU s'' h1, h2]
    obtain ⟨rfl, rfl⟩ := dsFrame_eq_of_eventuallyEq h h₀ hboth
    exact he
  have hSu : S = univ := (IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨0, hS0⟩)
  refine ⟨x₀, v₀, h₀, fun s => ?_⟩
  have : s ∈ S := hSu ▸ mem_univ s
  exact this.self_of_nhds


namespace SingularHSStructure

variable {M : Type*} [TopologicalSpace M] (A : SingularHSStructure M)

/-- **A space-like geodesic of the de Sitter part**, parametrised by arc length: a curve of
regular points which, read in a chart of the HS-structure near each parameter, is a unit-speed
space-like geodesic `s ↦ [cos s · x + sin s · v]` of `dS²` (a great-circle arc of a space-like
plane). -/
def IsSpacelikeGeodesic (γ : ℝ → M) : Prop :=
  Continuous γ ∧ ∀ s, γ s ∉ A.sing ∧ ∃ e ∈ A.atlas, γ s ∈ e.source ∧
    ∃ x v : 𝕄, IsDSFrame x v ∧ ∀ᶠ s' in 𝓝 s, e (γ s') = dsGeo x v s'

/-- **A simple closed space-like geodesic of length `ℓ`**: an arc-length parametrised space-like
geodesic of period `ℓ > 0`, injective on one period. -/
structure IsSimpleClosedSpacelikeGeodesic (γ : ℝ → M) (ℓ : ℝ) : Prop where
  geodesic : A.IsSpacelikeGeodesic γ
  pos : 0 < ℓ
  periodic : Function.Periodic γ ℓ
  injOn : InjOn γ (Ico 0 ℓ)

/-- **Positive mass** (`bbsdef:has_positive_mass_simple`, l.1821–1824): every simple closed
space-like geodesic of the de Sitter part has length `< 2π`. -/
def HasPositiveMass : Prop :=
  ∀ γ ℓ, A.IsSimpleClosedSpacelikeGeodesic γ ℓ → ℓ < 2 * π

end SingularHSStructure

/-! ## 2. Angle lifts and an intermediate value argument -/

/-- Iterating `f (s + T) = f s + d`. -/
theorem add_int_mul_of_add {f : ℝ → ℝ} {T d : ℝ} (h : ∀ s, f (s + T) = f s + d) (n : ℤ) (s : ℝ) :
    f (s + n * T) = f s + n * d := by
  induction n using Int.induction_on generalizing s with
  | zero => simp
  | succ k ih =>
    have := h (s + k * T)
    push_cast
    have ih' := ih s
    push_cast at ih'
    rw [show s + (k + 1) * T = s + k * T + T by ring, this, ih']
    ring
  | pred k ih =>
    have h1 := h (s + (-(k : ℝ) - 1) * T)
    have h2 := ih s
    push_cast at h2 ⊢
    rw [show s + (-(k : ℝ) - 1) * T + T = s + -(k : ℝ) * T by ring, h2] at h1
    linarith

/-- Two continuous angle lifts of the same map differ by a constant multiple of `2π`. -/
theorem exists_int_of_exp_eq {φ₁ φ₂ : ℝ → ℝ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (h : ∀ s, Circle.exp (φ₁ s) = Circle.exp (φ₂ s)) :
    ∃ n : ℤ, ∀ s, φ₁ s = φ₂ s + n * (2 * π) := by
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.1 (h 0)
  refine ⟨n, fun s => congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq (g₁ := φ₁)
    (g₂ := fun s => φ₂ s + n * (2 * π)) h₁ (h₂.add continuous_const) (funext fun s => ?_) 0 hn) s⟩
  simp only [Function.comp_apply]
  rw [h s, Circle.exp_add, mul_comm (n : ℝ)]
  rw [show Circle.exp (2 * π * n) = 1 from Circle.exp_two_pi_mul_int n, mul_one]

/-- **An intermediate value argument on a covering**: `φ` continuous injective with
`φ (s + T) = φ s + ε T` (`ε = ±1`), `lam` continuous `T`-periodic: for every `c` there are
`s₁, s₂` with `φ s₁ = φ s₂ + c` and `lam s₁ = lam s₂`. -/
theorem exists_shift_eq {φ lam : ℝ → ℝ} {T ε : ℝ} (hT : 0 < T) (hε : ε = 1 ∨ ε = -1)
    (hφc : Continuous φ) (hφi : Function.Injective φ) (hφT : ∀ s, φ (s + T) = φ s + ε * T)
    (hlc : Continuous lam) (hlT : Function.Periodic lam T) (c : ℝ) :
    ∃ s₁ s₂, φ s₁ = φ s₂ + c ∧ lam s₁ = lam s₂ := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  set φ' := fun s => ε * φ s with hφ'_def
  have hφ'c : Continuous φ' := continuous_const.mul hφc
  have hφ'i : Function.Injective φ' := fun a b h => hφi (by
    have := congrArg (ε * ·) h
    simp only [φ', ← mul_assoc, hε2, one_mul] at this
    exact this)
  have hφ'T : ∀ s, φ' (s + T) = φ' s + T := fun s => by
    simp only [φ', hφT]; rw [mul_add, ← mul_assoc, hε2, one_mul]
  have hmono : StrictMono φ' := by
    rcases hφ'c.strictMono_of_inj hφ'i with h | h
    · exact h
    · exfalso
      have h1 := h (show (0 : ℝ) < T from hT)
      rw [show T = 0 + T by ring, hφ'T] at h1
      linarith
  have hnT : ∀ n : ℤ, φ' (n * T) = φ' 0 + n * T := fun n => by
    have := add_int_mul_of_add hφ'T n 0
    rw [zero_add] at this
    exact this
  have hsurj : Function.Surjective φ' := by
    intro y
    obtain ⟨n₁, hn₁⟩ := Archimedean.arch (φ' 0 - y) hT
    obtain ⟨n₂, hn₂⟩ := Archimedean.arch (y - φ' 0) hT
    have ha := hnT (-(n₁ : ℤ))
    have hb := hnT (n₂ : ℤ)
    simp only [nsmul_eq_mul] at hn₁ hn₂
    push_cast at ha hb
    have hab : (-(n₁ : ℝ)) * T ≤ (n₂ : ℝ) * T := by
      apply mul_le_mul_of_nonneg_right _ hT.le
      have : (0 : ℝ) ≤ n₁ := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ n₂ := Nat.cast_nonneg _
      linarith
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc hab hφ'c.continuousOn
      (show y ∈ Icc (φ' (-(n₁ : ℝ) * T)) (φ' ((n₂ : ℝ) * T)) from
        ⟨by rw [ha]; linarith, by rw [hb]; linarith⟩)
    exact ⟨s, hs⟩
  set e := StrictMono.orderIsoOfSurjective φ' hmono hsurj
  set ψ : ℝ → ℝ := ⇑e.symm
  have hψc : Continuous ψ := e.symm.continuous
  have hφψ : ∀ u, φ' (ψ u) = u := fun u =>
    StrictMono.orderIsoOfSurjective_self_symm_apply φ' hmono hsurj u
  have hψT : ∀ u, ψ (u + T) = ψ u + T := fun u => by
    apply hφ'i
    rw [hφψ, hφ'T, hφψ]
  set H := fun u => lam (ψ u)
  have hHc : Continuous H := hlc.comp hψc
  have hHT : Function.Periodic H T := fun u => by simp only [H, hψT, hlT (ψ u)]
  have hK := hHT.compact_of_continuous hT.ne' hHc
  obtain ⟨M, ⟨uM, rfl⟩, hM⟩ := hK.exists_isGreatest (range_nonempty H)
  obtain ⟨m, ⟨um, rfl⟩, hm⟩ := hK.exists_isLeast (range_nonempty H)
  set c' := ε * c
  set F := fun u => H (u + c') - H u
  have hFc : Continuous F := (hHc.comp (continuous_id.add continuous_const)).sub hHc
  have hF1 : 0 ≤ F (uM - c') := by
    simp only [F, sub_add_cancel]
    linarith [hM ⟨uM - c', rfl⟩]
  have hF2 : F (um - c') ≤ 0 := by
    simp only [F, sub_add_cancel]
    linarith [hm ⟨um - c', rfl⟩]
  obtain ⟨u, -, hu⟩ := intermediate_value_uIcc (a := um - c') (b := uM - c') hFc.continuousOn
    (show (0 : ℝ) ∈ uIcc (F (um - c')) (F (uM - c')) from
      mem_uIcc.2 (Or.inl ⟨hF2, hF1⟩))
  refine ⟨ψ (u + c'), ψ u, ?_, ?_⟩
  · have h1 := hφψ (u + c')
    have h2 := hφψ u
    simp only [φ'] at h1 h2
    have key : ε * (φ (ψ (u + c')) - (φ (ψ u) + c)) = 0 := by
      simp only [c'] at h1; linarith
    have := congrArg (ε * ·) key
    simp only [← mul_assoc, hε2, one_mul, mul_zero] at this
    linarith
  · have : F u = 0 := hu
    simp only [F, H] at this
    linarith

/-! ## 3. A frame at a time-like point -/

/-- **A time-like frame at `p`**: `A ∈ SO₀(1,2)` sending the time axis onto the line of `p`,
`p = κ · A e₀`. Coordinates are read through `A⁻¹`. -/
structure TFrame (p : HS 2) where
  A : Causal.Flat.lorentz 2
  κ : ℝ
  hκ : κ ≠ 0
  hp : (p : 𝕄) = κ • ((A : 𝕄 ≃ₗ[ℝ] 𝕄) (Causal.Flat.timeUnit 2))

theorem exists_tFrame {p : HS 2} (hp : Causal.Flat.minkQ (p : 𝕄) < 0) : Nonempty (TFrame p) := by
  have h1 := HS.fst_ne_zero_of_minkQ_nonpos p hp.le
  rcases lt_or_gt_of_ne h1 with h | h
  · have hm : -p ∈ HS.piece 2 .hypPlus := by
      show Causal.Flat.IsFutureTimelike ((-p : HS 2) : 𝕄)
      rw [coe_neg_sphere]
      refine ⟨by simp; linarith, ?_⟩
      rw [minkQ_two] at hp ⊢
      simpa using hp
    obtain ⟨A, -, hA⟩ := HS.exists_smul_pole (by norm_num) hm
    obtain ⟨c, hc, hAc⟩ := linRaySmul_eq_iff.1 hA
    refine ⟨⟨A, -c⁻¹, by simp [hc.ne'], ?_⟩⟩
    have : ((A : 𝕄 ≃ₗ[ℝ] 𝕄) (Causal.Flat.timeUnit 2)) = c • ((-p : HS 2) : 𝕄) := hAc
    rw [this, coe_neg_sphere, smul_neg, smul_neg, neg_smul, neg_neg, smul_smul,
      inv_mul_cancel₀ hc.ne', one_smul]
  · have hm : p ∈ HS.piece 2 .hypPlus := ⟨h, hp⟩
    obtain ⟨A, -, hA⟩ := HS.exists_smul_pole (by norm_num) hm
    obtain ⟨c, hc, hAc⟩ := linRaySmul_eq_iff.1 hA
    refine ⟨⟨A, c⁻¹, by simp [hc.ne'], ?_⟩⟩
    have : ((A : 𝕄 ≃ₗ[ℝ] 𝕄) (Causal.Flat.timeUnit 2)) = c • (p : 𝕄) := hAc
    rw [this, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

namespace TFrame

variable {p : HS 2} (F : TFrame p)

/-- The coordinates `A⁻¹ y`. -/
def co (y : 𝕄) : 𝕄 := ((F.A⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) y

/-- The time coordinate. -/
def ta (y : 𝕄) : ℝ := (F.co y).1

/-- The space coordinate, as a complex number. -/
def cz (y : 𝕄) : ℂ := ⟨(F.co y).2 0, (F.co y).2 1⟩

theorem co_add (y y' : 𝕄) : F.co (y + y') = F.co y + F.co y' := map_add _ _ _
theorem co_smul (a : ℝ) (y : 𝕄) : F.co (a • y) = a • F.co y := map_smul _ _ _

theorem ta_add (y y' : 𝕄) : F.ta (y + y') = F.ta y + F.ta y' := by
  simp [ta, co_add]
theorem ta_smul (a : ℝ) (y : 𝕄) : F.ta (a • y) = a * F.ta y := by
  simp [ta, co_smul]
theorem cz_add (y y' : 𝕄) : F.cz (y + y') = F.cz y + F.cz y' := by
  apply Complex.ext <;> simp [cz, co_add]
theorem cz_smul (a : ℝ) (y : 𝕄) : F.cz (a • y) = a * F.cz y := by
  apply Complex.ext <;> simp [cz, co_smul]

theorem continuous_co : Continuous F.co :=
  LinearMap.continuous_of_finiteDimensional
    (((F.A⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) : 𝕄 →ₗ[ℝ] 𝕄)
theorem continuous_ta : Continuous F.ta := continuous_fst.comp F.continuous_co
theorem continuous_cz : Continuous F.cz := by
  have h0 : Continuous fun y : 𝕄 => (F.co y).2 0 :=
    ((PiLp.continuous_apply 2 _ 0).comp continuous_snd).comp F.continuous_co
  have h1 : Continuous fun y : 𝕄 => (F.co y).2 1 :=
    ((PiLp.continuous_apply 2 _ 1).comp continuous_snd).comp F.continuous_co
  have : F.cz = fun y => ((F.co y).2 0 : ℂ) + ((F.co y).2 1 : ℂ) * Complex.I :=
    funext fun y => by apply Complex.ext <;> simp [cz]
  rw [this]
  exact (Complex.continuous_ofReal.comp h0).add
    ((Complex.continuous_ofReal.comp h1).mul continuous_const)

theorem minkQ_eq (y : 𝕄) : Causal.Flat.minkQ y = -F.ta y ^ 2 + ‖F.cz y‖ ^ 2 := by
  have := Causal.Flat.lorentz.minkQ_apply (F.A⁻¹).2 y
  change Causal.Flat.minkQ (F.co y) = _ at this
  rw [← this, minkQ_two, Complex.sq_norm, Complex.normSq_apply]
  simp [ta, cz]
  ring

theorem minkB_eq (y y' : 𝕄) : Causal.Flat.minkB y y' =
    -(F.ta y * F.ta y') + ((F.cz y).re * (F.cz y').re + (F.cz y).im * (F.cz y').im) := by
  have := Causal.Flat.lorentz.minkB_apply (F.A⁻¹).2 y y'
  change Causal.Flat.minkB (F.co y) (F.co y') = _ at this
  rw [← this, minkB_two]
  simp [ta, cz]
  ring

theorem co_p : F.co (p : 𝕄) = F.κ • Causal.Flat.timeUnit 2 := by
  rw [F.hp, co_smul]
  congr 1
  show ((F.A⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((F.A : 𝕄 ≃ₗ[ℝ] 𝕄) _) = _
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
  rfl

theorem ta_p : F.ta (p : 𝕄) = F.κ := by
  simp [ta, co_p, Causal.Flat.timeUnit]
theorem cz_p : F.cz (p : 𝕄) = 0 := by
  apply Complex.ext <;> simp [cz, co_p, Causal.Flat.timeUnit]

theorem eq_of_co (y : 𝕄) : y = ((F.A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (F.co y) := by
  show y = ((F.A : 𝕄 ≃ₗ[ℝ] 𝕄) * ((F.A⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)) y
  rw [← Subgroup.coe_mul, mul_inv_cancel]
  rfl

theorem cz_eq_zero_iff {y : 𝕄} : F.cz y = 0 ↔ ∃ c : ℝ, y = c • (p : 𝕄) := by
  constructor
  · intro h
    have h0 : (F.co y).2 0 = 0 := by simpa [cz] using congrArg Complex.re h
    have h1 : (F.co y).2 1 = 0 := by simpa [cz] using congrArg Complex.im h
    refine ⟨F.ta y / F.κ, ?_⟩
    have hco : F.co y = F.ta y • Causal.Flat.timeUnit 2 := by
      refine mink3_ext ?_ ?_ ?_ <;> simp [ta, Causal.Flat.timeUnit, h0, h1]
    conv_lhs => rw [F.eq_of_co y]
    rw [hco, map_smul, F.hp, smul_smul, div_mul_cancel₀ _ F.hκ]
  · rintro ⟨c, rfl⟩
    rw [cz_smul, cz_p, mul_zero]

theorem tpMk_ne_zero_iff {y : 𝕄} : tpMk p y ≠ 0 ↔ F.cz y ≠ 0 := by
  rw [ne_eq, ne_eq, tpMk_eq_zero_iff, F.cz_eq_zero_iff]

theorem minkQ_nonpos_of_cz_eq_zero {y : 𝕄} (h : F.cz y = 0) : Causal.Flat.minkQ y ≤ 0 := by
  rw [F.minkQ_eq, h, norm_zero]
  nlinarith

/-- **`Γ_p` acts by rotations** in the frame: it fixes the time coordinate and multiplies the
space coordinate by a unit complex number. -/
theorem exists_rot (g : GammaP p) : ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ y : 𝕄,
    F.ta (((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) y) = F.ta y ∧
    F.cz (((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) y) = u * F.cz y := by
  set C : Causal.Flat.lorentz 2 := F.A⁻¹ * (g : Causal.Flat.lorentz 2) * F.A
  have hgp : ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (p : 𝕄) = p := g.2
  have hC : (C : 𝕄 ≃ₗ[ℝ] 𝕄) (Causal.Flat.timeUnit 2) = Causal.Flat.timeUnit 2 := by
    have hAe : (F.A : 𝕄 ≃ₗ[ℝ] 𝕄) (Causal.Flat.timeUnit 2) = F.κ⁻¹ • (p : 𝕄) := by
      rw [F.hp, smul_smul, inv_mul_cancel₀ F.hκ, one_smul]
    show ((F.A⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((F.A : 𝕄 ≃ₗ[ℝ] 𝕄)
        (Causal.Flat.timeUnit 2))) = _
    rw [hAe, map_smul, hgp, ← hAe]
    show ((F.A⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((F.A : 𝕄 ≃ₗ[ℝ] 𝕄) _) = _
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  obtain ⟨R, hR⟩ := HS.exists_rot_eq_of_fix hC
  obtain ⟨a, ha⟩ := exists_circle_of_specialOrth R
  have hco : ∀ y, F.co (((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) y) =
      ((C : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (F.co y) := fun y => by
    conv_lhs => rw [F.eq_of_co y]
    rfl
  refine ⟨(a : ℂ), by simp, fun y => ?_⟩
  have hcy := hco y
  rw [hR, HS.rot_apply] at hcy
  simp only [ta, cz, hcy]
  refine ⟨trivial, ?_⟩
  have h := ha (F.co y).2
  apply Complex.ext
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    simp only [Complex.orthonormalBasisOneI_repr_apply,
      Complex.orthonormalBasisOneI_repr_symm_apply] at this
    rw [this]
    simp [Complex.mul_re]
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    simp only [Complex.orthonormalBasisOneI_repr_apply,
      Complex.orthonormalBasisOneI_repr_symm_apply] at this
    rw [this]
    simp [Complex.mul_im]

end TFrame

/-! ## 4. The great-circle lemma -/

namespace TFrame

variable {p : HS 2} (F : TFrame p)

/-- The height `ta / ‖cz‖` of a vector over the plane `p^⊥` (invariant under positive scaling and
under `Γ_p`). -/
def mu (y : 𝕄) : ℝ := F.ta y / ‖F.cz y‖

theorem minkQ_comb {X V : 𝕄} (h : IsDSFrame X V) (α β : ℝ) :
    Causal.Flat.minkQ (α • X + β • V) = α ^ 2 + β ^ 2 := by
  obtain ⟨hx, hv, hxv⟩ := h
  rw [minkQ_two] at hx hv ⊢
  rw [minkB_two] at hxv
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  linear_combination α ^ 2 * hx + β ^ 2 * hv + 2 * α * β * hxv

theorem ta_dsVec (X V : 𝕄) (s : ℝ) :
    F.ta (dsVec X V s) = Real.cos s * F.ta X + Real.sin s * F.ta V := by
  rw [dsVec, F.ta_add, F.ta_smul, F.ta_smul]

theorem cz_dsVec (X V : 𝕄) (s : ℝ) :
    F.cz (dsVec X V s) = Real.cos s * F.cz X + Real.sin s * F.cz V := by
  rw [dsVec, F.cz_add, F.cz_smul, F.cz_smul]

theorem norm_cz_sq_of_minkQ {y : 𝕄} (hy : Causal.Flat.minkQ y = 1) :
    ‖F.cz y‖ ^ 2 = 1 + F.ta y ^ 2 := by
  have := F.minkQ_eq y
  rw [hy] at this
  linarith

theorem norm_cz_pos_of_minkQ {y : 𝕄} (hy : Causal.Flat.minkQ y = 1) : 0 < ‖F.cz y‖ := by
  have h := F.norm_cz_sq_of_minkQ hy
  have : (0 : ℝ) < ‖F.cz y‖ ^ 2 := by rw [h]; positivity
  refine lt_of_le_of_ne (norm_nonneg _) fun h0 => ?_
  rw [← h0] at this
  simp at this

theorem ta_eq_of_mu_eq {y y' : 𝕄} (hy : Causal.Flat.minkQ y = 1)
    (hy' : Causal.Flat.minkQ y' = 1) (h : F.mu y = F.mu y') : F.ta y = F.ta y' := by
  have hr := F.norm_cz_pos_of_minkQ hy
  have hr' := F.norm_cz_pos_of_minkQ hy'
  have h2 := F.norm_cz_sq_of_minkQ hy
  have h2' := F.norm_cz_sq_of_minkQ hy'
  simp only [mu] at h
  rw [div_eq_div_iff hr.ne' hr'.ne'] at h
  set a := F.ta y
  set b := F.ta y'
  set r := ‖F.cz y‖
  set r' := ‖F.cz y'‖
  have hsq : a ^ 2 = b ^ 2 := by
    have : a ^ 2 * r' ^ 2 = b ^ 2 * r ^ 2 := by
      have : (a * r') ^ 2 = (b * r) ^ 2 := by rw [h]
      linear_combination this
    rw [h2, h2'] at this
    nlinarith
  have : (a - b) * (a + b) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · have hb : b = -a := by linarith
    rw [hb] at h
    have : a * (r' + r) = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · rw [h3] at hb ⊢; rw [hb]; ring
    · linarith

theorem continuous_mu_dsVec {X V : 𝕄} (h : IsDSFrame X V) :
    Continuous fun s => F.mu (dsVec X V s) := by
  refine (F.continuous_ta.comp (continuous_dsVec X V)).div
    (continuous_norm.comp (F.continuous_cz.comp (continuous_dsVec X V))) fun s => ?_
  exact (F.norm_cz_pos_of_minkQ (minkQ_dsVec h s)).ne'

theorem dsVec_add_two_pi (X V : 𝕄) (s : ℝ) : dsVec X V (s + 2 * π) = dsVec X V s := by
  simp only [dsVec, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem dsVec_add_int_mul_two_pi (X V : 𝕄) (s : ℝ) (n : ℤ) :
    dsVec X V (s + n * (2 * π)) = dsVec X V s := by
  simp only [dsVec, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- The angle of `cz ∘ dsVec` determines the parameter modulo `2π`. -/
theorem eq_add_of_exp_eq {X V : 𝕄} (hXV : IsDSFrame X V) {s₁ s₂ : ℝ}
    (h : F.cz (dsVec X V s₁) / ‖F.cz (dsVec X V s₁)‖ =
      F.cz (dsVec X V s₂) / ‖F.cz (dsVec X V s₂)‖) : ∃ j : ℤ, s₁ = s₂ + j * (2 * π) := by
  have hr₁ := F.norm_cz_pos_of_minkQ (minkQ_dsVec hXV s₁)
  have hr₂ := F.norm_cz_pos_of_minkQ (minkQ_dsVec hXV s₂)
  set k := ‖F.cz (dsVec X V s₁)‖ / ‖F.cz (dsVec X V s₂)‖
  have hk : 0 < k := div_pos hr₁ hr₂
  have hcz : F.cz (dsVec X V s₁) = (k : ℂ) * F.cz (dsVec X V s₂) := by
    have h1 : (‖F.cz (dsVec X V s₁)‖ : ℂ) ≠ 0 := by exact_mod_cast hr₁.ne'
    have h2 : (‖F.cz (dsVec X V s₂)‖ : ℂ) ≠ 0 := by exact_mod_cast hr₂.ne'
    calc F.cz (dsVec X V s₁) = (‖F.cz (dsVec X V s₁)‖ : ℂ) *
          (F.cz (dsVec X V s₁) / ‖F.cz (dsVec X V s₁)‖) := by field_simp
      _ = (‖F.cz (dsVec X V s₁)‖ : ℂ) * (F.cz (dsVec X V s₂) / ‖F.cz (dsVec X V s₂)‖) := by
          rw [h]
      _ = _ := by simp only [k]; push_cast; field_simp
  have hz :
      F.cz ((Real.cos s₁ - k * Real.cos s₂) • X + (Real.sin s₁ - k * Real.sin s₂) • V) = 0 := by
    have e : (Real.cos s₁ - k * Real.cos s₂) • X + (Real.sin s₁ - k * Real.sin s₂) • V =
        dsVec X V s₁ + (-k) • dsVec X V s₂ := by
      simp only [dsVec, smul_add, smul_smul, sub_smul]; module
    rw [e, cz_add, cz_smul, hcz]
    push_cast; ring
  have hQ := F.minkQ_nonpos_of_cz_eq_zero hz
  rw [minkQ_comb hXV] at hQ
  have hc : Real.cos s₁ = k * Real.cos s₂ := by
    nlinarith [sq_nonneg (Real.cos s₁ - k * Real.cos s₂), sq_nonneg (Real.sin s₁ - k * Real.sin s₂)]
  have hs : Real.sin s₁ = k * Real.sin s₂ := by
    nlinarith [sq_nonneg (Real.cos s₁ - k * Real.cos s₂), sq_nonneg (Real.sin s₁ - k * Real.sin s₂)]
  have hk1 : k = 1 := by
    have h1 := Real.sin_sq_add_cos_sq s₁
    have h2 := Real.sin_sq_add_cos_sq s₂
    rw [hc, hs] at h1
    have : k ^ 2 = 1 := by nlinarith
    nlinarith
  rw [hk1, one_mul] at hc hs
  have : Circle.exp s₁ = Circle.exp s₂ := by
    apply Circle.ext
    rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc,
      hs]
  exact Circle.exp_eq_exp.1 this

/-- **On the equator `p^⊥` the angle runs at unit speed**: `φ s = φ 0 ± s`. -/
theorem angle_of_equator {X V : 𝕄} (hXV : IsDSFrame X V) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ : ∀ s, (Circle.exp (φ s) : ℂ) = F.cz (dsVec X V s) / ‖F.cz (dsVec X V s)‖)
    (ha : F.ta X = 0) (hb : F.ta V = 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ s, φ s = φ 0 + ε * s := by
  obtain ⟨hX, hV, hXV0⟩ := hXV
  have hqX := F.minkQ_eq X
  have hqV := F.minkQ_eq V
  have hBXV := F.minkB_eq X V
  rw [hX, ha] at hqX
  rw [hV, hb] at hqV
  rw [hXV0, ha, hb] at hBXV
  rw [Complex.sq_norm, Complex.normSq_apply] at hqX hqV
  set x₁ := (F.cz X).re
  set x₂ := (F.cz X).im
  set v₁ := (F.cz V).re
  set v₂ := (F.cz V).im
  have hx : x₁ ^ 2 + x₂ ^ 2 = 1 := by nlinarith
  have hv : v₁ ^ 2 + v₂ ^ 2 = 1 := by nlinarith
  have hB : x₁ * v₁ + x₂ * v₂ = 0 := by linarith
  set ε := x₁ * v₂ - x₂ * v₁ with hε_def
  have hε2 : ε ^ 2 = 1 := by
    have : ε ^ 2 = (x₁ ^ 2 + x₂ ^ 2) * (v₁ ^ 2 + v₂ ^ 2) - (x₁ * v₁ + x₂ * v₂) ^ 2 := by
      rw [hε_def]; ring
    rw [this, hx, hv, hB]; norm_num
  have hε : ε = 1 ∨ ε = -1 := by
    have : (ε - 1) * (ε + 1) = 0 := by linear_combination hε2
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  have hczV : F.cz V = ε * Complex.I * F.cz X := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      show v₁ = _
      linear_combination (-v₁) * hx + x₁ * hB
    · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      show v₂ = _
      linear_combination (-v₂) * hx + x₂ * hB
  have hcos : ∀ s, Real.cos (ε * s) = Real.cos s := fun s => by
    rcases hε with h | h <;> rw [h] <;> simp
  have hsin : ∀ s, Real.sin (ε * s) = ε * Real.sin s := fun s => by
    rcases hε with h | h <;> rw [h] <;> simp
  have hnX : ‖F.cz X‖ = 1 := by
    have : ‖F.cz X‖ ^ 2 = 1 := by rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
    nlinarith [norm_nonneg (F.cz X)]
  have hcz : ∀ s, F.cz (dsVec X V s) = F.cz X * (Circle.exp (ε * s) : ℂ) := fun s => by
    rw [F.cz_dsVec, hczV, Circle.coe_exp, Complex.exp_mul_I]
    push_cast
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cos (ε * s), ← Complex.ofReal_sin (ε * s), hcos,
      hsin]
    push_cast
    ring
  have hnorm : ∀ s, ‖F.cz (dsVec X V s)‖ = 1 := fun s => by
    rw [hcz, norm_mul, hnX, Circle.norm_coe, one_mul]
  have hφ0 : (Circle.exp (φ 0) : ℂ) = F.cz X := by
    rw [hφ, hnorm, hcz]; simp
  have hlift : ∀ s, Circle.exp (φ s) = Circle.exp (φ 0 + ε * s) := fun s => by
    apply Circle.ext
    rw [hφ, hnorm, Circle.exp_add, Circle.coe_mul, hφ0, hcz]
    simp
  obtain ⟨n, hn⟩ := exists_int_of_exp_eq (φ₂ := fun s => φ 0 + ε * s) hφc
    (continuous_const.add (continuous_const.mul continuous_id)) hlift
  have hn0 : (n : ℝ) * (2 * π) = 0 := by
    have := hn 0
    simp only [mul_zero, add_zero] at this
    linarith
  have hφlin : ∀ s, φ s = φ 0 + ε * s := fun s => by rw [hn s, hn0, add_zero]
  exact ⟨ε, hε, hφlin⟩

/-- **The great-circle lemma.** A unit-speed great circle `G = dsVec X V` of `dS²`, with a
continuous angle `φ` of its space coordinate, which closes up after `ℓ` in the quotient by the
translation `(φ, μ) ↦ (φ + c, μ)` (`m` turns) and is simple there, has `ℓ = |c|`; unless `c` is a
multiple of `2π` it is the equator `p^⊥`. -/
theorem great_circle {X V : 𝕄} (hXV : IsDSFrame X V) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ : ∀ s, (Circle.exp (φ s) : ℂ) = F.cz (dsVec X V s) / ‖F.cz (dsVec X V s)‖)
    {c ℓ : ℝ} (hc : c ≠ 0) (hℓ : 0 < ℓ) {m : ℤ}
    (hφℓ : ∀ s, φ (s + ℓ) = φ s + m * c)
    (hμℓ : ∀ s, F.mu (dsVec X V (s + ℓ)) = F.mu (dsVec X V s))
    (hsimple : ∀ s₁ ∈ Ico 0 ℓ, ∀ s₂ ∈ Ico 0 ℓ, ∀ n : ℤ, φ s₁ = φ s₂ + n * c →
      F.mu (dsVec X V s₁) = F.mu (dsVec X V s₂) → s₁ = s₂) :
    ℓ = |c| ∧ ((∀ k : ℤ, c ≠ 2 * π * k) → F.ta X = 0 ∧ F.ta V = 0) := by
  obtain ⟨hX, hV, hXV0⟩ := hXV
  by_cases h0 : F.ta X = 0 ∧ F.ta V = 0
  · -- the equator
    obtain ⟨ha, hb⟩ := h0
    refine ⟨?_, fun _ => ⟨ha, hb⟩⟩
    obtain ⟨ε, hε, hφlin⟩ := F.angle_of_equator ⟨hX, hV, hXV0⟩ hφc hφ ha hb
    have hεℓ : ε * ℓ = m * c := by
      have := hφℓ 0
      rw [zero_add, hφlin ℓ] at this
      linarith
    have habsε : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> simp
    have hlm : ℓ = |(m : ℝ)| * |c| := by
      have := congrArg abs hεℓ
      rw [abs_mul, abs_mul, habsε, one_mul, abs_of_pos hℓ] at this
      exact this
    have hmu0 : ∀ s, F.mu (dsVec X V s) = 0 := fun s => by
      simp only [mu, F.ta_dsVec, ha, hb, mul_zero, add_zero, zero_div]
    have hm1 : |(m : ℝ)| = 1 := by
      by_contra hne
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hlm
        linarith
      have hm2 : 2 ≤ |(m : ℝ)| := by
        have : 2 ≤ |m| := by
          rcases lt_trichotomy m 0 with h | h | h
          · have : m ≠ -1 := fun h' => hne (by rw [h']; simp)
            rw [abs_of_neg h]; omega
          · exact absurd h hm0
          · have : m ≠ 1 := fun h' => hne (by rw [h']; simp)
            rw [abs_of_pos h]; omega
        have : (2 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
        rwa [Int.cast_abs] at this
      have hcpos : 0 < |c| := abs_pos.2 hc
      have hcℓ : |c| < ℓ := by rw [hlm]; nlinarith
      have hn : ∃ n : ℤ, ε * |c| = n * c := by
        rcases hε with h | h <;> rcases abs_choice c with h' | h' <;> rw [h, h']
        · exact ⟨1, by ring⟩
        · exact ⟨-1, by push_cast; ring⟩
        · exact ⟨-1, by push_cast; ring⟩
        · exact ⟨1, by push_cast; ring⟩
      obtain ⟨n, hn⟩ := hn
      have := hsimple |c| ⟨hcpos.le, hcℓ⟩ 0 ⟨le_rfl, hℓ⟩ n (by rw [hφlin |c|, hn]) (by
        rw [hmu0, hmu0])
      linarith
    rw [hlm, hm1, one_mul]
  · have hXV : IsDSFrame X V := ⟨hX, hV, hXV0⟩
    -- (a) the height is `ℓ`-periodic
    have hta : ∀ s, F.ta (dsVec X V (s + ℓ)) = F.ta (dsVec X V s) := fun s =>
      F.ta_eq_of_mu_eq (minkQ_dsVec hXV _) (minkQ_dsVec hXV _) (hμℓ s)
    -- (b) `ℓ ∈ 2πℤ`
    have hcosℓ : Real.cos ℓ = 1 := by
      have e0 := hta 0
      have e1 := hta (π / 2)
      rw [F.ta_dsVec, F.ta_dsVec] at e0 e1
      rw [zero_add, Real.cos_zero, Real.sin_zero] at e0
      rw [Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two] at e1
      have hsc := Real.sin_sq_add_cos_sq ℓ
      by_contra hne
      have h2 : (1 - Real.cos ℓ) ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
      have ha : (2 - 2 * Real.cos ℓ) * F.ta X = 0 := by
        linear_combination (Real.cos ℓ - 1) * e0 - Real.sin ℓ * e1 - F.ta X * hsc
      have hb : (2 - 2 * Real.cos ℓ) * F.ta V = 0 := by
        linear_combination Real.sin ℓ * e0 + (Real.cos ℓ - 1) * e1 - F.ta V * hsc
      have h3 : (2 - 2 * Real.cos ℓ) ≠ 0 := by
        intro h; apply h2; linarith
      exact h0 ⟨(mul_eq_zero.1 ha).resolve_left h3, (mul_eq_zero.1 hb).resolve_left h3⟩
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff ℓ).1 hcosℓ
    have hkpos : (0 : ℝ) < k := by
      by_contra h; push Not at h
      nlinarith [Real.pi_pos]
    -- (c) the winding number of the angle
    have hexp2π : ∀ s, Circle.exp (φ (s + 2 * π)) = Circle.exp (φ s) := fun s => by
      apply Circle.ext; rw [hφ, hφ, dsVec_add_two_pi]
    obtain ⟨w, hw⟩ := exists_int_of_exp_eq (φ₁ := fun s => φ (s + 2 * π)) (φ₂ := φ)
      (hφc.comp (continuous_id.add continuous_const)) hφc hexp2π
    -- (d) the angle determines the parameter modulo `2π`
    have hmod : ∀ s₁ s₂, Circle.exp (φ s₁) = Circle.exp (φ s₂) → ∃ j : ℤ, s₁ = s₂ + j * (2 * π) :=
      fun s₁ s₂ h => F.eq_add_of_exp_eq hXV (by rw [← hφ, ← hφ, h])
    have hexpj : ∀ (x : ℝ) (j : ℤ), Circle.exp (x + j * (2 * π)) = Circle.exp x := fun x j => by
      rw [Circle.exp_add, show (j : ℝ) * (2 * π) = 2 * π * j by ring, Circle.exp_two_pi_mul_int,
        mul_one]
    have hno : ∀ s₁ s₂ (j : ℤ), s₁ < s₂ → s₂ < s₁ + 2 * π → φ s₂ ≠ φ s₁ + j * (2 * π) := by
      intro s₁ s₂ j h1 h2 he
      obtain ⟨j', hj'⟩ := hmod s₂ s₁ (by rw [he, hexpj])
      have hj1 : (0 : ℝ) < j' * (2 * π) := by linarith
      have hj2 : (j' : ℝ) * (2 * π) < 1 * (2 * π) := by linarith
      have hj1' : (0 : ℝ) < j' := by
        by_contra h; push Not at h; nlinarith [Real.pi_pos]
      have hj2' : (j' : ℝ) < 1 := lt_of_mul_lt_mul_right hj2 (by positivity)
      have : (0 : ℤ) < j' := by exact_mod_cast hj1'
      have : j' < (1 : ℤ) := by exact_mod_cast hj2'
      omega
    -- (e) `w = ±1`
    have hφ2π : φ (2 * π) = φ 0 + w * (2 * π) := by have := hw 0; rwa [zero_add] at this
    have hπ := Real.pi_pos
    have hw1 : w = 1 ∨ w = -1 := by
      rcases lt_trichotomy w 0 with hlt | heq | hgt
      · by_cases hm1 : w = -1
        · exact Or.inr hm1
        exfalso
        have hw2 : (w : ℝ) ≤ -2 := by exact_mod_cast (show w ≤ -2 by omega)
        obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 2 * π by positivity)
          hφc.continuousOn (show φ 0 - 2 * π ∈ Icc (φ (2 * π)) (φ 0) from
            ⟨by rw [hφ2π]; nlinarith, by linarith⟩)
        have hs0 : s ≠ 0 := by rintro rfl; linarith
        have hs2 : s ≠ 2 * π := by rintro rfl; rw [hφ2π] at hφs; nlinarith
        exact hno 0 s (-1) (lt_of_le_of_ne hs.1 (Ne.symm hs0)) (by
          rw [zero_add]; exact lt_of_le_of_ne hs.2 hs2) (by rw [hφs]; push_cast; ring)
      · exfalso
        rw [heq, Int.cast_zero, zero_mul, add_zero] at hφ2π
        have hAB : φ π ≠ φ 0 := by
          have := hno 0 π 0 hπ (by linarith)
          simpa using this
        obtain ⟨s₁, hs₁, h₁⟩ := intermediate_value_uIcc (a := 0) (b := π) hφc.continuousOn
          (show (φ 0 + φ π) / 2 ∈ uIcc (φ 0) (φ π) from by
            rcases lt_or_gt_of_ne hAB with h | h
            · rw [uIcc_of_ge h.le]; constructor <;> linarith
            · rw [uIcc_of_le h.le]; constructor <;> linarith)
        obtain ⟨s₂, hs₂, h₂⟩ := intermediate_value_uIcc (a := π) (b := 2 * π) hφc.continuousOn
          (show (φ 0 + φ π) / 2 ∈ uIcc (φ π) (φ (2 * π)) from by
            rw [hφ2π]
            rcases lt_or_gt_of_ne hAB with h | h
            · rw [uIcc_of_le h.le]; constructor <;> linarith
            · rw [uIcc_of_ge h.le]; constructor <;> linarith)
        rw [uIcc_of_le hπ.le] at hs₁
        rw [uIcc_of_le (by linarith)] at hs₂
        have h1π : s₁ ≠ π := by rintro rfl; apply hAB; linarith
        have h2π : s₂ ≠ π := by rintro rfl; apply hAB; linarith
        have h10 : s₁ ≠ 0 := by rintro rfl; apply hAB; linarith
        have h22 : s₂ ≠ 2 * π := by rintro rfl; apply hAB; rw [hφ2π] at h₂; linarith
        have l1 : s₁ < s₂ := lt_of_lt_of_le (lt_of_le_of_ne hs₁.2 h1π) hs₂.1
        have l2 : s₂ < s₁ + 2 * π := by
          have := lt_of_le_of_ne hs₂.2 h22
          have := lt_of_le_of_ne hs₁.1 (Ne.symm h10)
          linarith
        exact hno s₁ s₂ 0 l1 l2 (by rw [h₁, h₂]; simp)
      · by_cases hm1 : w = 1
        · exact Or.inl hm1
        exfalso
        have hw2 : (2 : ℝ) ≤ w := by exact_mod_cast (show 2 ≤ w by omega)
        obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 2 * π by positivity)
          hφc.continuousOn (show φ 0 + 2 * π ∈ Icc (φ 0) (φ (2 * π)) from
            ⟨by linarith, by rw [hφ2π]; nlinarith⟩)
        have hs0 : s ≠ 0 := by rintro rfl; linarith
        have hs2 : s ≠ 2 * π := by rintro rfl; rw [hφ2π] at hφs; nlinarith
        exact hno 0 s 1 (lt_of_le_of_ne hs.1 (Ne.symm hs0)) (by
          rw [zero_add]; exact lt_of_le_of_ne hs.2 hs2) (by rw [hφs]; push_cast; ring)
    have hw0 : (w : ℝ) ≠ 0 := by rcases hw1 with h | h <;> rw [h] <;> norm_num
    -- (f) the angle is injective
    have hφi : Function.Injective φ := by
      intro s₁ s₂ he
      obtain ⟨j, hj⟩ := hmod s₁ s₂ (by rw [he])
      have := add_int_mul_of_add (T := 2 * π) (d := w * (2 * π)) hw j s₂
      rw [← hj, he] at this
      have hj0 : (j : ℝ) * (w * (2 * π)) = 0 := by linarith
      have : (j : ℝ) = 0 := by
        rcases mul_eq_zero.1 hj0 with h | h
        · exact h
        · exfalso; rcases mul_eq_zero.1 h with h' | h'
          · exact hw0 h'
          · linarith
      rw [hj, this, zero_mul, add_zero]
    -- (g) an intermediate value: two parameters identified by the translation
    have hper : Function.Periodic (fun s => F.mu (dsVec X V s)) (2 * π) := fun s => by
      simp only [dsVec_add_two_pi]
    have hwε : (w : ℝ) = 1 ∨ (w : ℝ) = -1 := by
      rcases hw1 with h | h <;> rw [h] <;> norm_num
    obtain ⟨s₁, s₂, h12, hmu12⟩ := exists_shift_eq (T := 2 * π) (ε := w) (by positivity) hwε hφc
      hφi hw (F.continuous_mu_dsVec hXV) hper c
    -- (h) reduce modulo `ℓ`
    have hperℓ : Function.Periodic (fun s => F.mu (dsVec X V s)) ℓ := hμℓ
    set r₁ := toIcoMod hℓ 0 s₁
    set r₂ := toIcoMod hℓ 0 s₂
    set n₁ := toIcoDiv hℓ 0 s₁
    set n₂ := toIcoDiv hℓ 0 s₂
    have e₁ : s₁ = r₁ + n₁ * ℓ := by
      have := toIcoMod_add_toIcoDiv_zsmul hℓ 0 s₁; rw [zsmul_eq_mul] at this; linarith
    have e₂ : s₂ = r₂ + n₂ * ℓ := by
      have := toIcoMod_add_toIcoDiv_zsmul hℓ 0 s₂; rw [zsmul_eq_mul] at this; linarith
    have hr₁ : r₁ ∈ Ico 0 ℓ := by simpa using toIcoMod_mem_Ico hℓ 0 s₁
    have hr₂ : r₂ ∈ Ico 0 ℓ := by simpa using toIcoMod_mem_Ico hℓ 0 s₂
    have hφ₁ := add_int_mul_of_add hφℓ n₁ r₁
    have hφ₂ := add_int_mul_of_add hφℓ n₂ r₂
    have hμ₁ := hperℓ.int_mul n₁ r₁
    have hμ₂ := hperℓ.int_mul n₂ r₂
    rw [← e₁] at hφ₁ hμ₁
    rw [← e₂] at hφ₂ hμ₂
    have hrr := hsimple r₁ hr₁ r₂ hr₂ (1 + n₂ * m - n₁ * m) (by push_cast; linarith)
      (by rw [← hμ₁, ← hμ₂, hmu12])
    have hN : ((n₁ - n₂ : ℤ) : ℝ) * m = 1 := by
      have := add_int_mul_of_add hφℓ (n₁ - n₂) s₂
      rw [show s₂ + ((n₁ - n₂ : ℤ) : ℝ) * ℓ = s₁ by rw [e₁, e₂, hrr]; push_cast; ring] at this
      have h' : (((n₁ - n₂ : ℤ) : ℝ) * m - 1) * c = 0 := by linarith
      have := (mul_eq_zero.1 h').resolve_right hc
      linarith
    have hm1 : m = 1 ∨ m = -1 := by
      have : (n₁ - n₂) * m = 1 := by exact_mod_cast hN
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
    -- (i) the length
    have hmc : (m : ℝ) * c = k * (w * (2 * π)) := by
      have h1 := hφℓ 0
      have h2 := add_int_mul_of_add hw k 0
      rw [zero_add] at h1 h2
      rw [hk] at h2
      linarith
    have hmε : (m : ℝ) = 1 ∨ (m : ℝ) = -1 := by
      rcases hm1 with h | h <;> rw [h] <;> norm_num
    refine ⟨?_, fun hnot => ?_⟩
    · have := congrArg abs hmc
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hkpos, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
        at this
      rcases hmε with h | h <;> rcases hwε with h' | h' <;> rw [h, h'] at this <;>
        simp at this <;> linarith
    · exfalso
      refine hnot (m * k * w) ?_
      push_cast
      rcases hmε with h | h <;> rw [h] at hmc ⊢ <;> linarith

end TFrame

/-! ## 5. The angle of the developing data, and the cone angle -/

/-- A continuous map into `ℂ ∖ 0` has a continuous angle. -/
theorem exists_angle_lift {ζ : ℝ → ℂ} (hc : Continuous ζ) (h0 : ∀ s, ζ s ≠ 0) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ ∀ s, (Circle.exp (φ s) : ℂ) = ζ s / ‖ζ s‖ := by
  have hmem : ∀ s, ζ s / ‖ζ s‖ ∈ Submonoid.unitSphere ℂ := fun s => by
    show ζ s / ‖ζ s‖ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.2 (h0 s))]
  let u : C(ℝ, Circle) := ⟨fun s => ⟨ζ s / ‖ζ s‖, hmem s⟩, by
    refine Continuous.subtype_mk ?_ _
    exact hc.div (Complex.continuous_ofReal.comp (continuous_norm.comp hc)) fun s => by
      exact_mod_cast norm_ne_zero_iff.2 (h0 s)⟩
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (u 0)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts u 0 e₀ he₀
  exact ⟨F, F.continuous, fun s => by
    have := congrFun hF s
    simp only [Function.comp_apply] at this
    rw [this]; rfl⟩

namespace TFrame

variable {p : HS 2} (F : TFrame p)

/-- The space coordinate, as a linear map. -/
def czL : 𝕄 →ₗ[ℝ] ℂ where
  toFun := F.cz
  map_add' := F.cz_add
  map_smul' a y := by rw [F.cz_smul, RingHom.id_apply, Complex.real_smul]

/-- The space coordinate on `T_p HS² = ℝ^{1,2}/ℝp`. -/
def theta₀ : TpHS p →ₗ[ℝ] ℂ :=
  (ℝ ∙ (p : 𝕄)).liftQ F.czL (by
    rw [Submodule.span_le]
    rintro _ rfl
    show F.cz (p : 𝕄) = 0
    exact F.cz_p)

theorem theta₀_mk (y : 𝕄) : F.theta₀ (tpMk p y) = F.cz y := rfl

theorem theta₀_bijective : Function.Bijective F.theta₀ := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      have : F.cz y = 0 := hx
      obtain ⟨c, rfl⟩ := F.cz_eq_zero_iff.1 this
      exact (tpMk_eq_zero_iff p).2 ⟨c, rfl⟩
  · intro z
    refine ⟨tpMk p (((F.A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (mink3 0 z.re z.im)), ?_⟩
    rw [theta₀_mk]
    have : F.co (((F.A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (mink3 0 z.re z.im)) =
        mink3 0 z.re z.im := by
      show ((F.A⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((F.A : 𝕄 ≃ₗ[ℝ] 𝕄) _) = _
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    apply Complex.ext <;> simp [cz, this]

/-- The space coordinate on `T_p HS²`, a linear isomorphism onto `ℂ`. -/
def theta : TpHS p ≃ₗ[ℝ] ℂ := LinearEquiv.ofBijective F.theta₀ F.theta₀_bijective

theorem theta_mk (y : 𝕄) : F.theta (tpMk p y) = F.cz y := rfl

theorem vol3_p_eq (w₁ w₂ : 𝕄) : vol3 (p : 𝕄) w₁ w₂ =
    F.κ * ((F.cz w₁).re * (F.cz w₂).im - (F.cz w₁).im * (F.cz w₂).re) := by
  have h := vol3_lorentz (F.A⁻¹) (p : 𝕄) w₁ w₂
  change vol3 (F.co p) (F.co w₁) (F.co w₂) = _ at h
  rw [← h, F.co_p, vol3_eq]
  simp [cz, Causal.Flat.timeUnit]

/-- **An oriented space coordinate on `T_p HS²`**, and the sign `σ` relating its angle to the
frame's: a vector with space coordinate `r e^{iφ}` has direction `linkCover (σ φ / π)`. -/
theorem exists_theta : ∃ θ : TpHS p ≃ₗ[ℝ] ℂ, IsOrientedTangent p θ ∧ ∃ σ : ℝ,
    (σ = 1 ∨ σ = -1) ∧ ∀ (y : 𝕄) (φ r : ℝ), 0 < r → F.cz y = r * (Circle.exp φ : ℂ) →
      dirOf p y = linkCover p θ (σ * φ / π) := by
  have key : ∀ (θ : TpHS p ≃ₗ[ℝ] ℂ) (y : 𝕄) (r t : ℝ), 0 < r →
      θ (tpMk p y) = r * (Circle.exp (π * t) : ℂ) → dirOf p y = linkCover p θ t := by
    intro θ y r t hr h
    have hy : tpMk p y = r • θ.symm (Circle.exp (π * t)) := by
      rw [← θ.symm_apply_apply (tpMk p y), h, ← Complex.real_smul, map_smul]
    have hne : θ.symm (Circle.exp (π * t)) ≠ 0 := by
      rw [ne_eq, LinearEquiv.map_eq_zero_iff]
      exact Circle.coe_ne_zero _
    have hy0 : tpMk p y ≠ 0 := by rw [hy]; exact smul_ne_zero hr.ne' hne
    apply Subtype.ext
    rw [coe_dirOf p hy0, coe_linkCover, hy, norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul,
      mul_inv_rev, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
  rcases lt_or_gt_of_ne F.hκ with hκ | hκ
  · -- `κ < 0`: the conjugate coordinate is oriented
    refine ⟨F.theta.trans Complex.conjLIE.toLinearEquiv, ?_, -1, Or.inr rfl, ?_⟩
    · intro w₁ w₂ h₁ h₂
      have e₁ : F.cz w₁ = 1 := by
        have := congrArg (F.theta.trans Complex.conjLIE.toLinearEquiv) h₁
        rw [LinearEquiv.apply_symm_apply] at this
        have h' : (starRingEnd ℂ) (F.cz w₁) = 1 := this
        rw [← Complex.conj_conj (F.cz w₁), h', map_one]
      have e₂ : F.cz w₂ = -Complex.I := by
        have := congrArg (F.theta.trans Complex.conjLIE.toLinearEquiv) h₂
        rw [LinearEquiv.apply_symm_apply] at this
        have h' : (starRingEnd ℂ) (F.cz w₂) = Complex.I := this
        rw [← Complex.conj_conj (F.cz w₂), h', Complex.conj_I]
      rw [F.vol3_p_eq, e₁, e₂]
      simp
      linarith
    · intro y φ r hr h
      refine key _ y r _ hr ?_
      simp only [LinearEquiv.trans_apply, theta_mk, h]
      rw [show π * (-1 * φ / π) = -φ by field_simp]
      simp [Circle.coe_exp, ← Complex.exp_conj, Complex.exp_neg]
  · refine ⟨F.theta, ?_, 1, Or.inl rfl, ?_⟩
    · intro w₁ w₂ h₁ h₂
      have e₁ : F.cz w₁ = 1 := by
        have := congrArg F.theta h₁
        rwa [LinearEquiv.apply_symm_apply, theta_mk] at this
      have e₂ : F.cz w₂ = Complex.I := by
        have := congrArg F.theta h₂
        rwa [LinearEquiv.apply_symm_apply, theta_mk] at this
      rw [F.vol3_p_eq, e₁, e₂]
      simp
      linarith
    · intro y φ r hr h
      refine key _ y r _ hr ?_
      rw [theta_mk, h, show π * (1 * φ / π) = φ by field_simp]

end TFrame

/-! ### The angle of the developing data -/

section DevAngle

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

theorem GammaLinkCircle.DevData.cz_vlift_ne (Δ : C.DevData) (F : TFrame C.pt) (s : ℝ) :
    F.cz (Δ.vlift s) ≠ 0 :=
  F.tpMk_ne_zero_iff.1 (Δ.tpMk_vlift_ne s)

theorem GammaLinkCircle.DevData.continuous_cz_vlift (Δ : C.DevData) (F : TFrame C.pt) :
    Continuous fun s => F.cz (Δ.vlift s) :=
  F.continuous_cz.comp Δ.continuous_vlift

/-- **The angle of the developing data**: a continuous `Φ` with `cz (vlift s) ∈ ℝ₊ e^{iΦ(s)}`,
`Φ (s + 1) = Φ s + c` (the holonomy is a rotation), `Φ` injective, `c ≠ 0`, and the cone angle is
`|c|`. -/
theorem GammaLinkCircle.DevData.exists_angle (Δ : C.DevData) (F : TFrame C.pt) :
    ∃ (Φ : ℝ → ℝ) (c : ℝ), Continuous Φ ∧
      (∀ s, (Circle.exp (Φ s) : ℂ) = F.cz (Δ.vlift s) / ‖F.cz (Δ.vlift s)‖) ∧
      (∀ s, Φ (s + 1) = Φ s + c) ∧ Function.Injective Φ ∧ c ≠ 0 ∧ C.coneAngle = |c| := by
  obtain ⟨Φ, hΦc, hΦ⟩ := exists_angle_lift (Δ.continuous_cz_vlift F) (Δ.cz_vlift_ne F)
  obtain ⟨u, hu, hrot⟩ := F.exists_rot Δ.hol
  have hu' : u ∈ Submonoid.unitSphere ℂ := by
    show u ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, hu]
  obtain ⟨β, hβ⟩ := Circle.exp_surjective ⟨u, hu'⟩
  have hβ' : (Circle.exp β : ℂ) = u := by rw [hβ]
  have hcz1 : ∀ s, F.cz (Δ.vlift (s + 1)) = u * F.cz (Δ.vlift s) := fun s => by
    rw [Δ.vlift_add_one]; exact (hrot _).2
  have hn1 : ∀ s, ‖F.cz (Δ.vlift (s + 1))‖ = ‖F.cz (Δ.vlift s)‖ := fun s => by
    rw [hcz1, norm_mul, hu, one_mul]
  have hexp : ∀ s, Circle.exp (Φ (s + 1)) = Circle.exp (Φ s + β) := fun s => by
    apply Circle.ext
    rw [hΦ, Circle.exp_add, Circle.coe_mul, hΦ, hβ', hn1, hcz1]
    ring
  obtain ⟨n, hn⟩ := exists_int_of_exp_eq (φ₁ := fun s => Φ (s + 1)) (φ₂ := fun s => Φ s + β)
    (hΦc.comp (continuous_id.add continuous_const)) (hΦc.add continuous_const) hexp
  set c := β + n * (2 * π)
  have hΦ1 : ∀ s, Φ (s + 1) = Φ s + c := fun s => by rw [hn s]; ring
  obtain ⟨θ, hθ, σ, hσ, hdir⟩ := F.exists_theta
  set D : ℝ → ℝ := fun s => σ * Φ s / π
  have hDc : Continuous D := (continuous_const.mul hΦc).div_const _
  have hdD : ∀ s, linkCover C.pt θ (D s) = Δ.d s := fun s => by
    rw [← Δ.dirOf_vlift s]
    refine (hdir (Δ.vlift s) (Φ s) ‖F.cz (Δ.vlift s)‖
      (norm_pos_iff.2 (Δ.cz_vlift_ne F s)) ?_).symm
    rw [hΦ]
    have : (‖F.cz (Δ.vlift s)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (Δ.cz_vlift_ne F s)
    field_simp
  have hdev : C.IsDevAlong Δ.E (linkCover C.pt θ ∘ D) := by
    have : linkCover C.pt θ ∘ D = Δ.d := funext hdD
    rw [this]; exact Δ.dev
  have hDl : IsLocalHomeomorph D := by
    letI := C.atlas
    have hEl := Δ.periodic.isCoveringMap.isLocalHomeomorph
    have hdl : IsLocalHomeomorph (linkCover C.pt θ ∘ D) := by
      letI := pullbackChartedSpace (X := Link C.pt) hEl
      exact ((C.isDevAlong_iff_isGXMorphism hEl).1 hdev).isLocalHomeomorph
    exact IsLocalHomeomorph.of_comp hdl (isCoveringMap_linkCover C.pt θ).isLocalHomeomorph hDc
  have hDi : Function.Injective D := injective_of_isOpenMap_real hDc hDl.isOpenMap
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hΦi : Function.Injective Φ := fun a b h => hDi (by simp only [D, h])
  have hc : c ≠ 0 := by
    intro h0
    have := hΦ1 0
    rw [h0, add_zero, zero_add] at this
    exact one_ne_zero (hΦi this)
  have hD1 : ∀ s, D (s + 1) = D s + σ * c / π := fun s => by
    simp only [D, hΦ1]; ring
  have hσc : σ * c ≠ 0 := mul_ne_zero hσ0 hc
  have habs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  refine ⟨Φ, c, hΦc, hΦ, hΦ1, hΦi, hc, ?_⟩
  rcases lt_or_gt_of_ne hσc with hneg | hpos
  · -- reverse the parameter
    have hanti : StrictAnti D := by
      rcases hDc.strictMono_of_inj hDi with h | h
      · exfalso
        have := h (show (0 : ℝ) < 1 by norm_num)
        rw [show (1 : ℝ) = 0 + 1 by ring, hD1] at this
        have : σ * c / π < 0 := div_neg_of_neg_of_pos hneg Real.pi_pos
        linarith
      · exact h
    have hlift : C.IsLiftedDev θ (Δ.E ∘ Neg.neg) (D ∘ Neg.neg) (GTilde.rot (-(2 * (σ * c)))) := by
      refine ⟨Δ.periodic.comp_neg, hDc.comp continuous_neg, fun a b hab => hanti (neg_lt_neg hab),
        hdev.comp_reparam continuous_neg, fun s => ?_⟩
      simp only [Function.comp_apply, GTilde.rot_apply]
      have := hD1 (-(s + 1))
      rw [show -(s + 1) + 1 = -s by ring] at this
      rw [this]
      field_simp
      ring
    rw [GammaLinkCircle.coneAngle_eq hθ hlift, GTilde.angle_rot]
    rw [show |c| = |σ| * |c| by rw [habs, one_mul], ← abs_mul, abs_of_neg hneg]
    ring
  · have hmono : StrictMono D := by
      rcases hDc.strictMono_of_inj hDi with h | h
      · exact h
      · exfalso
        have := h (show (0 : ℝ) < 1 by norm_num)
        rw [show (1 : ℝ) = 0 + 1 by ring, hD1] at this
        have : 0 < σ * c / π := div_pos hpos Real.pi_pos
        linarith
    have hlift : C.IsLiftedDev θ Δ.E D (GTilde.rot (2 * (σ * c))) := by
      refine ⟨Δ.periodic, hDc, hmono, hdev, fun s => ?_⟩
      rw [GTilde.rot_apply, hD1]
      field_simp
    rw [GammaLinkCircle.coneAngle_eq hθ hlift, GTilde.angle_rot]
    rw [show |c| = |σ| * |c| by rw [habs, one_mul], ← abs_mul, abs_of_pos hpos]
    ring

end DevAngle

/-! ## 6. The regular part of `𝔢(L)`, read on its covering -/

namespace BiSusp

variable {S : Type*} [TopologicalSpace S]

/-- The base point `σ` of a point `[σ, t]` (a choice; meaningful off the apices). -/
def base (x : BiSusp S) : S := (mk_surjective x).choose

theorem base_mk {σ : S} {t : Icc (0 : ℝ) Real.pi} (h0 : 0 < (t : ℝ)) (hπ : (t : ℝ) < Real.pi) :
    base (mk σ t) = σ := by
  have h := (mk_surjective (mk σ t)).choose_spec.choose_spec
  rcases mk_eq_mk.1 h with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
  · exact h1
  · exact absurd h2 h0.ne'
  · exact absurd h2 hπ.ne

theorem eq_mk_base {x : BiSusp S} (hx : x ∉ poles S) :
    x = mk (base x) ⟨ht x, ht_mem x⟩ := by
  obtain ⟨σ, t, rfl⟩ := mk_surjective x
  obtain ⟨h0, hπ⟩ := notMem_poles_iff.1 hx
  rw [ht_mk] at h0 hπ
  rw [base_mk h0 hπ]
  rfl

theorem continuousAt_base {x : BiSusp S} (hx : x ∉ poles S) : ContinuousAt base x := by
  obtain ⟨σ, t, rfl⟩ := mk_surjective x
  obtain ⟨h0, hπ⟩ := notMem_poles_iff.1 hx
  rw [ht_mk] at h0 hπ
  have hq : (σ, t) ∈ regSet (univ : Set S) := ⟨trivial, h0, hπ⟩
  have hb : base (mk' (σ, t)) = σ := base_mk h0 hπ
  show Tendsto base (𝓝 (mk' (σ, t))) (𝓝 (base (mk' (σ, t))))
  rw [nhds_mk hq, tendsto_map'_iff, hb]
  refine (continuous_fst.tendsto (σ, t)).congr' ?_
  filter_upwards [(isOpen_regSet isOpen_univ).mem_nhds hq] with q hq'
  exact (base_mk hq'.2.1 hq'.2.2).symm

end BiSusp

/-- A Lorentz transformation moves a great circle of `dS²` onto a great circle. -/
theorem IsDSFrame.lorentz {x v : 𝕄} (h : IsDSFrame x v) (g : Causal.Flat.lorentz 2) :
    IsDSFrame ((g : 𝕄 ≃ₗ[ℝ] 𝕄) x) ((g : 𝕄 ≃ₗ[ℝ] 𝕄) v) :=
  ⟨by rw [Causal.Flat.lorentz.minkQ_apply g.2]; exact h.1,
    by rw [Causal.Flat.lorentz.minkQ_apply g.2]; exact h.2.1,
    by rw [Causal.Flat.lorentz.minkB_apply g.2]; exact h.2.2⟩

theorem smul_rayNormalize (g : Causal.Flat.lorentz 2) {u : 𝕄} (hu : u ≠ 0) (σ₀ : HS 2) :
    g • rayNormalize σ₀ u = rayNormalize σ₀ ((g : 𝕄 ≃ₗ[ℝ] 𝕄) u) := by
  have hgu : (g : 𝕄 ≃ₗ[ℝ] 𝕄) u ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hu
  rw [hs_smul_def, linRaySmul_eq_iff]
  refine ⟨‖u‖⁻¹ * ‖(g : 𝕄 ≃ₗ[ℝ] 𝕄) u‖, mul_pos (inv_pos.2 (norm_pos_iff.2 hu))
    (norm_pos_iff.2 hgu), ?_⟩
  rw [coe_rayNormalize _ hu, coe_rayNormalize _ hgu, map_smul, smul_smul, mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 hgu), mul_one]

theorem smul_dsGeo {x v : 𝕄} (h : IsDSFrame x v) (g : Causal.Flat.lorentz 2) (s : ℝ) :
    g • dsGeo x v s = dsGeo ((g : 𝕄 ≃ₗ[ℝ] 𝕄) x) ((g : 𝕄 ≃ₗ[ℝ] 𝕄) v) s := by
  rw [dsGeo_eq, smul_rayNormalize g (dsVec_ne_zero h s), dsGeo_eq]
  simp only [dsVec, map_add, map_smul]

theorem rayNormalize_eq_of_ne {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (σ₀ σ₁ : RaySphere V) {u : V} (hu : u ≠ 0) : rayNormalize σ₀ u = rayNormalize σ₁ u :=
  Subtype.ext (by rw [coe_rayNormalize _ hu, coe_rayNormalize _ hu])

section Cover

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

/-- **The charts of `𝔢(L)` read on the covering** `ℝ × [0, π] → 𝔢(L)`, `(σ, t) ↦ [E σ, t]`:
near a regular point, a chart of the atlas is an element of `Γ_p` times the developing map
`(σ, t) ↦ [cos t · p + sin t · w(σ)]`. -/
theorem GammaLinkCircle.DevData.chart_eq (Δ : C.DevData)
    {χ : OpenPartialHomeomorph (BiSusp L) (HS 2)} (hχ : χ ∈ Δ.suspAtlas) {σ₀ : ℝ}
    {t₀ : Icc (0 : ℝ) Real.pi} (h0 : 0 < (t₀ : ℝ)) (hπ : (t₀ : ℝ) < Real.pi)
    (hx : BiSusp.mk (Δ.E σ₀) t₀ ∈ χ.source) :
    ∃ g : GammaP C.pt, ∀ᶠ σ in 𝓝 σ₀, ∀ t : Icc (0 : ℝ) Real.pi,
      χ (BiSusp.mk (Δ.E σ) t) =
        (g : Causal.Flat.lorentz 2) • arcPt C.pt (Δ.vlift σ) t := by
  obtain ⟨c, W, hW, hl, rfl⟩ := hχ
  obtain ⟨q, hq, hqx⟩ := hx
  have hq' : q = (Δ.E σ₀, t₀) := BiSusp.mk'_injOn_regSet ⟨trivial, hq.2⟩ ⟨trivial, h0, hπ⟩ hqx
  have hσc : Δ.E σ₀ ∈ c.source := by have := hq.1; rw [hq'] at this; exact this
  obtain ⟨s₁, hs₁, A, hA⟩ := hl _ hσc
  obtain ⟨n, hn⟩ := Δ.periodic.fiber s₁ σ₀ hs₁
  refine ⟨A * Δ.hol ^ (-n), ?_⟩
  have hcont : Tendsto (fun σ : ℝ => σ + (-n : ℤ)) (𝓝 σ₀) (𝓝 s₁) := by
    have : Tendsto (fun σ : ℝ => σ + ((-n : ℤ) : ℝ)) (𝓝 σ₀) (𝓝 (σ₀ + ((-n : ℤ) : ℝ))) :=
      (continuous_add_const _).tendsto σ₀
    rwa [show σ₀ + ((-n : ℤ) : ℝ) = s₁ by rw [hn]; push_cast; ring] at this
  filter_upwards [hcont.eventually hA] with σ hσ t
  rw [suspChart_apply, suspMap_mk]
  have hE : Δ.E (σ + ((-n : ℤ) : ℝ)) = Δ.E σ := Δ.periodic.add_int σ (-n)
  rw [hE] at hσ
  rw [hσ, Δ.vlift_add_int, ← LinearEquiv.mul_apply]
  exact (smul_arcPt C.pt (A * Δ.hol ^ (-n)) (Δ.tpMk_vlift_ne σ) t).symm

/-- **The lift of a space-like geodesic of `𝔢(L)`** to the covering: a continuous base
`σ̃ : ℝ → ℝ` and height `h : ℝ → ]0, π[`, developed onto one great circle `dsVec X V`. -/
theorem GammaLinkCircle.DevData.geodesic_lift (Δ : C.DevData) {γ : ℝ → BiSusp L}
    (hγ : Δ.suspStructure.IsSpacelikeGeodesic γ) :
    ∃ (σ' h : ℝ → ℝ) (X V : 𝕄), Continuous σ' ∧ Continuous h ∧ IsDSFrame X V ∧
      (∀ s, 0 < h s ∧ h s < Real.pi) ∧
      (∀ s, γ s = BiSusp.mk (Δ.E (σ' s)) (projIcc 0 Real.pi Real.pi_pos.le (h s))) ∧
      (∀ s, ∃ k : ℝ, 0 < k ∧ arcVec C.pt (Δ.vlift (σ' s)) (h s) = k • dsVec X V s) := by
  obtain ⟨hγc, hγs⟩ := hγ
  have hreg : ∀ s, γ s ∉ BiSusp.poles L := fun s => (hγs s).1
  -- the base and the height
  have hbc : Continuous fun s => BiSusp.base (γ s) :=
    continuous_iff_continuousAt.2 fun s =>
      (BiSusp.continuousAt_base (hreg s)).comp hγc.continuousAt
  obtain ⟨e₀, he₀⟩ := Δ.periodic.surjective (BiSusp.base (γ 0))
  obtain ⟨σ', ⟨-, hσ'⟩, -⟩ := Δ.periodic.isCoveringMap.existsUnique_continuousMap_lifts
    ⟨fun s => BiSusp.base (γ s), hbc⟩ 0 e₀ he₀
  have hσ's : ∀ s, Δ.E (σ' s) = BiSusp.base (γ s) := fun s => congrFun hσ' s
  set h : ℝ → ℝ := fun s => BiSusp.ht (γ s)
  have hhc : Continuous h := BiSusp.continuous_ht.comp hγc
  have hh : ∀ s, 0 < h s ∧ h s < Real.pi := fun s => BiSusp.notMem_poles_iff.1 (hreg s)
  have hγeq : ∀ s, γ s = BiSusp.mk (Δ.E (σ' s)) (projIcc 0 Real.pi Real.pi_pos.le (h s)) := by
    intro s
    rw [hσ's, projIcc_of_mem _ (BiSusp.ht_mem (γ s))]
    exact BiSusp.eq_mk_base (hreg s)
  -- the developed curve is locally a great circle
  set δ : ℝ → HS 2 := fun s => arcPt C.pt (Δ.vlift (σ' s)) (h s)
  have hloc : ∀ s, ∃ x v : 𝕄, IsDSFrame x v ∧ ∀ᶠ s' in 𝓝 s, δ s' = dsGeo x v s' := by
    intro s
    obtain ⟨-, e, he, hes, x, v, hxv, hev⟩ := hγs s
    have hx := hγeq s ▸ hes
    have hh0 := hh s
    obtain ⟨g, hg⟩ := Δ.chart_eq he (t₀ := projIcc 0 Real.pi Real.pi_pos.le (h s))
      (by rw [projIcc_of_mem _ ⟨hh0.1.le, hh0.2.le⟩]; exact hh0.1)
      (by rw [projIcc_of_mem _ ⟨hh0.1.le, hh0.2.le⟩]; exact hh0.2) hx
    refine ⟨_, _, hxv.lorentz ((g : Causal.Flat.lorentz 2)⁻¹), ?_⟩
    filter_upwards [σ'.continuous.continuousAt.eventually hg, hev] with s' h1 h2
    have h3 := h1 (projIcc 0 Real.pi Real.pi_pos.le (h s'))
    rw [← hγeq s', h2, projIcc_of_mem _ ⟨(hh s').1.le, (hh s').2.le⟩] at h3
    show arcPt C.pt (Δ.vlift (σ' s')) (h s') = _
    rw [← smul_dsGeo hxv, h3, inv_smul_smul]
  obtain ⟨X, V, hXV, hδ⟩ := exists_dsGeo_of_local hloc
  refine ⟨σ', h, X, V, σ'.continuous, hhc, hXV, hh, hγeq, fun s => ?_⟩
  have h1 := hδ s
  simp only [δ, arcPt, dsGeo_eq] at h1
  have hne := arcVec_ne_zero C.pt (Δ.tpMk_vlift_ne (σ' s)) (h s)
  rw [rayNormalize_eq_of_ne C.pt (HS.pole 2) hne] at h1
  exact (rayNormalize_eq_rayNormalize_iff hne (dsVec_ne_zero hXV s)).1 h1

end Cover

/-! ## 7. Heights over `p^⊥`, and the analysis of a simple closed geodesic of `𝔢(L)` -/

namespace TFrame

variable {p : HS 2} (F : TFrame p)

theorem ta_arcVec (w : 𝕄) (t : ℝ) :
    F.ta (arcVec p w t) = Real.cos t * F.κ + Real.sin t * F.ta w := by
  rw [arcVec, F.ta_add, F.ta_smul, F.ta_smul, F.ta_p]

theorem cz_arcVec (w : 𝕄) (t : ℝ) : F.cz (arcVec p w t) = Real.sin t * F.cz w := by
  rw [arcVec, F.cz_add, F.cz_smul, F.cz_smul, F.cz_p, mul_zero, zero_add]

theorem mu_smul {k : ℝ} (hk : 0 < k) (y : 𝕄) : F.mu (k • y) = F.mu y := by
  simp only [mu, F.ta_smul, F.cz_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hk]
  by_cases h : ‖F.cz y‖ = 0
  · simp [h]
  · field_simp

theorem cz_div_norm_smul {k : ℝ} (hk : 0 < k) (y : 𝕄) :
    F.cz (k • y) / ‖F.cz (k • y)‖ = F.cz y / ‖F.cz y‖ := by
  rw [F.cz_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  by_cases h : ‖F.cz y‖ = 0
  · rw [norm_eq_zero.1 h]; simp
  · push_cast
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp

theorem cz_div_norm_arcVec {w : 𝕄} {t : ℝ} (ht : 0 < Real.sin t) :
    F.cz (arcVec p w t) / ‖F.cz (arcVec p w t)‖ = F.cz w / ‖F.cz w‖ := by
  rw [F.cz_arcVec, ← F.cz_smul, F.cz_div_norm_smul ht]

theorem mu_arcVec_inj {w : 𝕄} (hw : F.cz w ≠ 0) {t₁ t₂ : ℝ} (h₁ : 0 < t₁ ∧ t₁ < Real.pi)
    (h₂ : 0 < t₂ ∧ t₂ < Real.pi) (h : F.mu (arcVec p w t₁) = F.mu (arcVec p w t₂)) :
    t₁ = t₂ := by
  have hs₁ := Real.sin_pos_of_pos_of_lt_pi h₁.1 h₁.2
  have hs₂ := Real.sin_pos_of_pos_of_lt_pi h₂.1 h₂.2
  have hr := norm_pos_iff.2 hw
  simp only [mu, F.ta_arcVec, F.cz_arcVec, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs₁, abs_of_pos hs₂] at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have key : F.κ * ‖F.cz w‖ * Real.sin (t₂ - t₁) = 0 := by
    rw [Real.sin_sub]; linear_combination h
  have hsin : Real.sin (t₂ - t₁) = 0 :=
    (mul_eq_zero.1 key).resolve_left (mul_ne_zero F.hκ hr.ne')
  have := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).1 hsin
  linarith

theorem ta_gammaP (g : GammaP p) (y : 𝕄) :
    F.ta (((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) y) = F.ta y := by
  obtain ⟨u, -, h⟩ := F.exists_rot g
  exact (h y).1

theorem mu_gammaP (g : GammaP p) (y : 𝕄) :
    F.mu (((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) y) = F.mu y := by
  obtain ⟨u, hu, h⟩ := F.exists_rot g
  simp only [mu, (h y).1, (h y).2, norm_mul, hu, one_mul]

theorem arcVec_gammaP (g : GammaP p) (w : 𝕄) (t : ℝ) :
    arcVec p (((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w) t =
      ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (arcVec p w t) := by
  have hgp : ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (p : 𝕄) = p := g.2
  simp only [arcVec, map_add, map_smul, hgp]

theorem minkB_p (y : 𝕄) : Causal.Flat.minkB y (p : 𝕄) = -(F.ta y * F.κ) := by
  rw [F.minkB_eq, F.ta_p, F.cz_p]; simp

theorem minkB_smul_left (c : ℝ) (y z : 𝕄) :
    Causal.Flat.minkB (c • y) z = c * Causal.Flat.minkB y z := by
  rw [minkB_two, minkB_two]
  simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  ring

theorem minkB_gammaP_smul_eq_zero_iff (g : GammaP p) (y : HS 2) :
    Causal.Flat.minkB (((g : Causal.Flat.lorentz 2) • y : HS 2) : 𝕄) (p : 𝕄) = 0 ↔
      Causal.Flat.minkB (y : 𝕄) (p : 𝕄) = 0 := by
  have hgp : ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (p : 𝕄) = p := g.2
  have hne : ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (y : 𝕄) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero y)
  rw [coe_hs_smul, minkB_smul_left]
  conv_lhs => rw [← hgp]
  rw [Causal.Flat.lorentz.minkB_apply (g : Causal.Flat.lorentz 2).2]
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hne))
  · intro h; rw [h, mul_zero]

theorem minkB_arcPt_eq_zero_iff {w : 𝕄} (hw : tpMk p w ≠ 0) (t : ℝ) :
    Causal.Flat.minkB (arcPt p w t : 𝕄) (p : 𝕄) = 0 ↔ F.ta (arcVec p w t) = 0 := by
  have hne := arcVec_ne_zero p hw t
  rw [arcPt, coe_rayNormalize _ hne, minkB_smul_left, F.minkB_p]
  constructor
  · intro h
    have h1 := (mul_eq_zero.1 h).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hne))
    have h2 : F.ta (arcVec p w t) * F.κ = 0 := by linarith
    exact (mul_eq_zero.1 h2).resolve_right F.hκ
  · intro h; rw [h]; ring

end TFrame

section Analysis

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

theorem GammaLinkCircle.DevData.mu_arcVec_add_int (Δ : C.DevData) (F : TFrame C.pt) (n : ℤ)
    (σ t : ℝ) :
    F.mu (arcVec C.pt (Δ.vlift (σ + n)) t) = F.mu (arcVec C.pt (Δ.vlift σ) t) := by
  rw [Δ.vlift_add_int, TFrame.arcVec_gammaP, F.mu_gammaP]

theorem GammaLinkCircle.DevData.ta_vlift_add_int (Δ : C.DevData) (F : TFrame C.pt) (n : ℤ)
    (σ : ℝ) : F.ta (Δ.vlift (σ + n)) = F.ta (Δ.vlift σ) := by
  rw [Δ.vlift_add_int, F.ta_gammaP]

/-- **The equator of `𝔢(L)`**: the regular points developed onto the great circle `p^⊥`. -/
def GammaLinkCircle.DevData.equator (Δ : C.DevData) : Set (BiSusp L) :=
  {x | x ∉ BiSusp.poles L ∧ ∃ e ∈ Δ.suspAtlas, x ∈ e.source ∧
    Causal.Flat.minkB (e x : 𝕄) (C.pt : 𝕄) = 0}

/-- The equator in the coordinates of the covering. -/
theorem GammaLinkCircle.DevData.mem_equator_iff (Δ : C.DevData) (F : TFrame C.pt) {σ t : ℝ}
    (ht : 0 < t ∧ t < Real.pi) :
    BiSusp.mk (Δ.E σ) (projIcc 0 Real.pi Real.pi_pos.le t) ∈ Δ.equator ↔
      F.ta (arcVec C.pt (Δ.vlift σ) t) = 0 := by
  have htI : t ∈ Icc (0 : ℝ) Real.pi := ⟨ht.1.le, ht.2.le⟩
  have h0 : 0 < ((projIcc 0 Real.pi Real.pi_pos.le t : Icc (0 : ℝ) Real.pi) : ℝ) := by
    rw [projIcc_of_mem _ htI]; exact ht.1
  have hπ : ((projIcc 0 Real.pi Real.pi_pos.le t : Icc (0 : ℝ) Real.pi) : ℝ) < Real.pi := by
    rw [projIcc_of_mem _ htI]; exact ht.2
  have hreg : BiSusp.mk (Δ.E σ) (projIcc 0 Real.pi Real.pi_pos.le t) ∉ BiSusp.poles L := by
    rw [BiSusp.notMem_poles_iff, BiSusp.ht_mk]; exact ⟨h0, hπ⟩
  have hval : ∀ e ∈ Δ.suspAtlas, BiSusp.mk (Δ.E σ) (projIcc 0 Real.pi Real.pi_pos.le t) ∈ e.source →
      (Causal.Flat.minkB (e (BiSusp.mk (Δ.E σ) (projIcc 0 Real.pi Real.pi_pos.le t)) : 𝕄)
        (C.pt : 𝕄) = 0 ↔ F.ta (arcVec C.pt (Δ.vlift σ) t) = 0) := by
    intro e he hxe
    obtain ⟨g, hg⟩ := Δ.chart_eq he h0 hπ hxe
    rw [hg.self_of_nhds, TFrame.minkB_gammaP_smul_eq_zero_iff, projIcc_of_mem _ htI,
      F.minkB_arcPt_eq_zero_iff (Δ.tpMk_vlift_ne σ)]
  constructor
  · rintro ⟨-, e, he, hxe, hB⟩
    exact (hval e he hxe).1 hB
  · intro h
    obtain ⟨e, he, hxe⟩ := Δ.suspStructure.exists_chart hreg
    exact ⟨hreg, e, he, hxe, (hval e he hxe).2 h⟩

/-- **The analysis of a simple closed space-like geodesic of `𝔢(L)`**, in a time-like frame and
for an angle `Φ` of the developing data with `Φ (s + 1) = Φ s + c`: its length is `|c|`, and
unless `c ∈ 2πℤ` it develops onto the equator `p^⊥`. -/
theorem GammaLinkCircle.DevData.simpleClosed_analysis (Δ : C.DevData) (F : TFrame C.pt)
    {Φ : ℝ → ℝ} {c : ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ s, (Circle.exp (Φ s) : ℂ) = F.cz (Δ.vlift s) / ‖F.cz (Δ.vlift s)‖)
    (hΦ1 : ∀ s, Φ (s + 1) = Φ s + c) (hΦi : Function.Injective Φ) (hc : c ≠ 0)
    {γ : ℝ → BiSusp L} {ℓ : ℝ} (h : Δ.suspStructure.IsSimpleClosedSpacelikeGeodesic γ ℓ) :
    ∃ (σ' hgt : ℝ → ℝ) (X V : 𝕄), Continuous σ' ∧ IsDSFrame X V ∧
      (∀ s, 0 < hgt s ∧ hgt s < Real.pi) ∧
      (∀ s, γ s = BiSusp.mk (Δ.E (σ' s)) (projIcc 0 Real.pi Real.pi_pos.le (hgt s))) ∧
      (∀ s, ∃ k : ℝ, 0 < k ∧ arcVec C.pt (Δ.vlift (σ' s)) (hgt s) = k • dsVec X V s) ∧
      (∀ s, (Circle.exp (Φ (σ' s)) : ℂ) = F.cz (dsVec X V s) / ‖F.cz (dsVec X V s)‖) ∧
      ℓ = |c| ∧ ((∀ k : ℤ, c ≠ 2 * π * k) → F.ta X = 0 ∧ F.ta V = 0) := by
  obtain ⟨σ', hgt, X, V, hσc, -, hXV, hh, hγeq, hk⟩ := Δ.geodesic_lift h.geodesic
  have hIcc : ∀ s, hgt s ∈ Icc (0 : ℝ) Real.pi := fun s => ⟨(hh s).1.le, (hh s).2.le⟩
  have hsin : ∀ s, 0 < Real.sin (hgt s) := fun s =>
    Real.sin_pos_of_pos_of_lt_pi (hh s).1 (hh s).2
  -- the angle along the curve
  have hφ : ∀ s, (Circle.exp (Φ (σ' s)) : ℂ) = F.cz (dsVec X V s) / ‖F.cz (dsVec X V s)‖ := by
    intro s
    obtain ⟨k, hk0, hks⟩ := hk s
    rw [hΦ, ← F.cz_div_norm_arcVec (w := Δ.vlift (σ' s)) (hsin s), hks, F.cz_div_norm_smul hk0]
  have hmu : ∀ s, F.mu (dsVec X V s) = F.mu (arcVec C.pt (Δ.vlift (σ' s)) (hgt s)) := by
    intro s
    obtain ⟨k, hk0, hks⟩ := hk s
    rw [hks, F.mu_smul hk0]
  -- base points and heights read off `γ`
  have hbase : ∀ s, BiSusp.base (γ s) = Δ.E (σ' s) := fun s => by
    rw [hγeq s, BiSusp.base_mk]
    · rw [projIcc_of_mem _ (hIcc s)]; exact (hh s).1
    · rw [projIcc_of_mem _ (hIcc s)]; exact (hh s).2
  have hht : ∀ s, BiSusp.ht (γ s) = hgt s := fun s => by
    rw [hγeq s, BiSusp.ht_mk, projIcc_of_mem _ (hIcc s)]
  -- closing up after `ℓ`: `m` turns
  have hEℓ : ∀ s, Δ.E (σ' (s + ℓ)) = Δ.E (σ' s) := fun s => by
    rw [← hbase, ← hbase, h.periodic s]
  have hhℓ : ∀ s, hgt (s + ℓ) = hgt s := fun s => by rw [← hht, ← hht, h.periodic s]
  obtain ⟨m, hm⟩ := Δ.periodic.fiber (σ' 0) (σ' ℓ) (by rw [← hEℓ 0, zero_add])
  have hσℓ : ∀ s, σ' (s + ℓ) = σ' s + m := by
    have := Δ.periodic.isCoveringMap.eq_of_comp_eq (g₁ := fun s => σ' (s + ℓ))
      (g₂ := fun s => σ' s + m) (hσc.comp (continuous_add_const ℓ))
      (hσc.add continuous_const) (funext fun s => by
        simp only [Function.comp_apply]; rw [hEℓ, Δ.periodic.add_int]) 0
      (by simp only [zero_add]; exact hm)
    exact fun s => congrFun this s
  have hΦn : ∀ (n : ℤ) (x : ℝ), Φ (x + n) = Φ x + n * c := fun n x => by
    have := add_int_mul_of_add (T := 1) hΦ1 n x
    rwa [mul_one] at this
  have hφℓ : ∀ s, Φ (σ' (s + ℓ)) = Φ (σ' s) + m * c := fun s => by rw [hσℓ, hΦn]
  have hμℓ : ∀ s, F.mu (dsVec X V (s + ℓ)) = F.mu (dsVec X V s) := fun s => by
    rw [hmu, hmu, hσℓ, hhℓ, Δ.mu_arcVec_add_int]
  -- simplicity, read on the covering
  have hsimple : ∀ s₁ ∈ Ico 0 ℓ, ∀ s₂ ∈ Ico 0 ℓ, ∀ n : ℤ, Φ (σ' s₁) = Φ (σ' s₂) + n * c →
      F.mu (dsVec X V s₁) = F.mu (dsVec X V s₂) → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ n hφn hμn
    have hσ : σ' s₁ = σ' s₂ + n := hΦi (by rw [hφn, hΦn])
    have hh12 : hgt s₁ = hgt s₂ := by
      refine F.mu_arcVec_inj (Δ.cz_vlift_ne F (σ' s₂)) (hh s₁) (hh s₂) ?_
      rw [← Δ.mu_arcVec_add_int F n, ← hσ, ← hmu, hμn, hmu]
    refine h.injOn hs₁ hs₂ ?_
    rw [hγeq, hγeq, hσ, Δ.periodic.add_int, hh12]
  obtain ⟨hℓc, hX⟩ := F.great_circle hXV (hΦc.comp hσc) hφ hc h.pos hφℓ hμℓ hsimple
  exact ⟨σ', hgt, X, V, hσc, hXV, hh, hγeq, hk, hφ, hℓc, hX⟩

end Analysis

/-- A continuous injective `φ` with `φ (s + T) = φ s + d` (`T, d > 0`) is an increasing
bijection. -/
theorem strictMono_surjective_of_add {φ : ℝ → ℝ} {T d : ℝ} (hT : 0 < T) (hd : 0 < d)
    (hφc : Continuous φ) (hφi : Function.Injective φ) (hφT : ∀ s, φ (s + T) = φ s + d) :
    StrictMono φ ∧ Function.Surjective φ := by
  have hmono : StrictMono φ := by
    rcases hφc.strictMono_of_inj hφi with h | h
    · exact h
    · exfalso
      have h1 := h (show (0 : ℝ) < T from hT)
      rw [show T = 0 + T by ring, hφT] at h1
      linarith
  refine ⟨hmono, fun y => ?_⟩
  have hnT : ∀ n : ℤ, φ (n * T) = φ 0 + n * d := fun n => by
    have := add_int_mul_of_add hφT n 0
    rw [zero_add] at this
    exact this
  obtain ⟨n₁, hn₁⟩ := Archimedean.arch (φ 0 - y) hd
  obtain ⟨n₂, hn₂⟩ := Archimedean.arch (y - φ 0) hd
  have ha := hnT (-(n₁ : ℤ))
  have hb := hnT (n₂ : ℤ)
  simp only [nsmul_eq_mul] at hn₁ hn₂
  push_cast at ha hb
  have hab : (-(n₁ : ℝ)) * T ≤ (n₂ : ℝ) * T := by
    apply mul_le_mul_of_nonneg_right _ hT.le
    have : (0 : ℝ) ≤ n₁ := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ n₂ := Nat.cast_nonneg _
    linarith
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc hab hφc.continuousOn
    (show y ∈ Icc (φ (-(n₁ : ℝ) * T)) (φ ((n₂ : ℝ) * T)) from
      ⟨by rw [ha]; linarith, by rw [hb]; linarith⟩)
  exact ⟨s, hs⟩

/-! ## 8. The link computation -/

section Link

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

/-- **The equator is a simple closed space-like geodesic of length the cone angle**: at every
time-like `p`, the de Sitter part of `𝔢(L)` contains a simple closed space-like geodesic of length
`θ = C.coneAngle`, whose image is the equator. -/
theorem GammaLinkCircle.DevData.exists_simpleClosed_equator
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) (Δ : C.DevData) :
    ∃ γ : ℝ → BiSusp L, Δ.suspStructure.IsSimpleClosedSpacelikeGeodesic γ C.coneAngle ∧
      range γ = Δ.equator := by
  obtain ⟨F⟩ := exists_tFrame hp
  obtain ⟨Φ, c, hΦc, hΦ, hΦ1, hΦi, hc, hcone⟩ := Δ.exists_angle F
  rw [hcone]
  have hcpos : 0 < |c| := abs_pos.2 hc
  -- the angle, oriented
  set ε₀ : ℝ := if 0 < c then 1 else -1 with hε₀_def
  have hε₀ : ε₀ = 1 ∨ ε₀ = -1 := by
    by_cases h : 0 < c
    · left; simp [ε₀, h]
    · right; simp [ε₀, h]
  have hε₀c : ε₀ * c = |c| := by
    by_cases h : 0 < c
    · simp [ε₀, h, abs_of_pos h]
    · simp [ε₀, h, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hc)]
  have hε₀2 : ε₀ * ε₀ = 1 := by rcases hε₀ with h | h <;> rw [h] <;> norm_num
  set Φ' : ℝ → ℝ := fun s => ε₀ * Φ s
  have hΦ'c : Continuous Φ' := continuous_const.mul hΦc
  have hΦ'i : Function.Injective Φ' := fun a b h => hΦi (by
    have := congrArg (ε₀ * ·) h
    simp only [Φ', ← mul_assoc, hε₀2, one_mul] at this
    exact this)
  have hΦ'1 : ∀ s, Φ' (s + 1) = Φ' s + |c| := fun s => by
    simp only [Φ', hΦ1, mul_add, hε₀c]
  obtain ⟨hmono, hsurj⟩ := strictMono_surjective_of_add one_pos hcpos hΦ'c hΦ'i hΦ'1
  set e := StrictMono.orderIsoOfSurjective Φ' hmono hsurj
  set ψ : ℝ → ℝ := ⇑e.symm
  have hψc : Continuous ψ := e.symm.continuous
  have hΦψ : ∀ u, Φ' (ψ u) = u := fun u =>
    StrictMono.orderIsoOfSurjective_self_symm_apply Φ' hmono hsurj u
  have hψΦ : ∀ σ, ψ (Φ' σ) = σ := fun σ =>
    StrictMono.orderIsoOfSurjective_symm_apply_self Φ' hmono hsurj σ
  have hψ1 : ∀ u, ψ (u + |c|) = ψ u + 1 := fun u => by
    apply hΦ'i; rw [hΦψ, hΦ'1, hΦψ]
  have hΦψ' : ∀ u, Φ (ψ u) = ε₀ * u := fun u => by
    have := hΦψ u
    simp only [Φ'] at this
    calc Φ (ψ u) = ε₀ * (ε₀ * Φ (ψ u)) := by rw [← mul_assoc, hε₀2, one_mul]
      _ = ε₀ * u := by rw [this]
  -- the height of the equator over the base point `σ`
  set t₀ : ℝ → ℝ := fun σ => π / 2 + Real.arctan (F.ta (Δ.vlift σ) / F.κ)
  have ht₀ : ∀ σ, 0 < t₀ σ ∧ t₀ σ < Real.pi := fun σ => by
    have h1 := Real.arctan_lt_pi_div_two (F.ta (Δ.vlift σ) / F.κ)
    have h2 := Real.neg_pi_div_two_lt_arctan (F.ta (Δ.vlift σ) / F.κ)
    constructor <;> simp only [t₀] <;> linarith
  have ht₀c : Continuous t₀ :=
    continuous_const.add (Real.continuous_arctan.comp
      ((F.continuous_ta.comp Δ.continuous_vlift).div_const _))
  have ht₀1 : ∀ σ, t₀ (σ + 1) = t₀ σ := fun σ => by
    have := Δ.ta_vlift_add_int F 1 σ
    push_cast at this
    simp only [t₀, this]
  have hta₀ : ∀ σ, F.ta (arcVec C.pt (Δ.vlift σ) (t₀ σ)) = 0 := fun σ => by
    have hκ := F.hκ
    have hcu := Real.cos_arctan_pos (F.ta (Δ.vlift σ) / F.κ)
    have htu := Real.tan_arctan (F.ta (Δ.vlift σ) / F.κ)
    rw [F.ta_arcVec]
    simp only [t₀]
    generalize Real.arctan (F.ta (Δ.vlift σ) / F.κ) = u at hcu htu ⊢
    rw [add_comm (π / 2) u, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    rw [Real.tan_eq_sin_div_cos] at htu
    have hsu : Real.sin u = F.ta (Δ.vlift σ) / F.κ * Real.cos u := by
      rw [← htu]; field_simp
    rw [hsu]
    field_simp
    ring
  have hmu₀ : ∀ σ, F.mu (arcVec C.pt (Δ.vlift σ) (t₀ σ)) = 0 := fun σ => by
    simp [TFrame.mu, hta₀ σ]
  have hI : ∀ σ, t₀ σ ∈ Icc (0 : ℝ) Real.pi := fun σ => ⟨(ht₀ σ).1.le, (ht₀ σ).2.le⟩
  -- the curve
  set γ₀ : ℝ → BiSusp L := fun s =>
    BiSusp.mk (Δ.E (ψ s)) (projIcc 0 Real.pi Real.pi_pos.le (t₀ (ψ s)))
  have hγ₀c : Continuous γ₀ :=
    BiSusp.continuous_mk'.comp ((Δ.periodic.isCoveringMap.continuous.comp hψc).prodMk
      (continuous_projIcc.comp (ht₀c.comp hψc)))
  have hreg : ∀ s, γ₀ s ∉ BiSusp.poles L := fun s => by
    rw [BiSusp.notMem_poles_iff, BiSusp.ht_mk, projIcc_of_mem _ (hI _)]
    exact ht₀ _
  -- the curve, developed: the equator `p^⊥` at unit speed
  set U₁ : 𝕄 := ((F.A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (mink3 0 1 0)
  set U₂ : 𝕄 := ((F.A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (mink3 0 0 ε₀)
  have hU : IsDSFrame U₁ U₂ := by
    have h0 : IsDSFrame (mink3 0 1 0) (mink3 0 0 ε₀) := by
      refine ⟨by rw [minkQ_two]; simp, by rcases hε₀ with h | h <;> rw [h, minkQ_two] <;> simp, ?_⟩
      rw [minkB_two]; simp
    exact h0.lorentz F.A
  have hdev : ∀ s, arcPt C.pt (Δ.vlift (ψ s)) (t₀ (ψ s)) = dsGeo U₁ U₂ s := fun s => by
    have hsin := Real.sin_pos_of_pos_of_lt_pi (ht₀ (ψ s)).1 (ht₀ (ψ s)).2
    have hr := norm_pos_iff.2 (Δ.cz_vlift_ne F (ψ s))
    have hK : 0 < Real.sin (t₀ (ψ s)) * ‖F.cz (Δ.vlift (ψ s))‖ := mul_pos hsin hr
    have hcw : F.cz (Δ.vlift (ψ s)) =
        ‖F.cz (Δ.vlift (ψ s))‖ * (Circle.exp (ε₀ * s) : ℂ) := by
      rw [← hΦψ', hΦ]
      have : (‖F.cz (Δ.vlift (ψ s))‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
    have hcos : Real.cos (ε₀ * s) = Real.cos s := by rcases hε₀ with h | h <;> rw [h] <;> simp
    have hsin' : Real.sin (ε₀ * s) = ε₀ * Real.sin s := by
      rcases hε₀ with h | h <;> rw [h] <;> simp
    have hcz : F.cz (arcVec C.pt (Δ.vlift (ψ s)) (t₀ (ψ s))) =
        ((Real.sin (t₀ (ψ s)) * ‖F.cz (Δ.vlift (ψ s))‖ * Real.cos s : ℝ) : ℂ) +
          ((Real.sin (t₀ (ψ s)) * ‖F.cz (Δ.vlift (ψ s))‖ * (ε₀ * Real.sin s) : ℝ) : ℂ) *
            Complex.I := by
      have e := hcw
      rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos (ε₀ * s),
        ← Complex.ofReal_sin (ε₀ * s), hcos, hsin'] at e
      conv_lhs => rw [F.cz_arcVec, e]
      simp only [Complex.ofReal_mul]; ring
    have hco : F.co (arcVec C.pt (Δ.vlift (ψ s)) (t₀ (ψ s))) =
        (Real.sin (t₀ (ψ s)) * ‖F.cz (Δ.vlift (ψ s))‖) •
          mink3 0 (Real.cos s) (ε₀ * Real.sin s) := by
      apply mink3_ext
      · show F.ta _ = _
        rw [hta₀]; simp
      · show (F.cz (arcVec C.pt (Δ.vlift (ψ s)) (t₀ (ψ s)))).re = _
        rw [hcz]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero, Prod.smul_snd,
          PiLp.smul_apply, mink3_snd_zero, smul_eq_mul]
      · show (F.cz (arcVec C.pt (Δ.vlift (ψ s)) (t₀ (ψ s)))).im = _
        rw [hcz]
        simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add,
          Prod.smul_snd, PiLp.smul_apply, mink3_snd_one, smul_eq_mul]
    have hvec : arcVec C.pt (Δ.vlift (ψ s)) (t₀ (ψ s)) =
        (Real.sin (t₀ (ψ s)) * ‖F.cz (Δ.vlift (ψ s))‖) • dsVec U₁ U₂ s := by
      rw [F.eq_of_co (arcVec C.pt (Δ.vlift (ψ s)) (t₀ (ψ s))), hco, map_smul]
      congr 1
      simp only [dsVec, U₁, U₂, ← map_smul, ← map_add]
      congr 1
      apply mink3_ext <;> simp [mul_comm]
    rw [arcPt, rayNormalize_eq_of_ne C.pt (HS.pole 2)
      (arcVec_ne_zero C.pt (Δ.tpMk_vlift_ne _) _), hvec,
      rayNormalize_smul_of_pos _ (dsVec_ne_zero hU s) hK]
    rfl
  -- membership in the equator
  have hmem : ∀ s, γ₀ s ∈ Δ.equator := fun s =>
    (Δ.mem_equator_iff F (ht₀ (ψ s))).2 (hta₀ (ψ s))
  refine ⟨γ₀, ⟨⟨hγ₀c, fun s => ⟨hreg s, ?_⟩⟩, hcpos, fun s => ?_, fun s₁ hs₁ s₂ hs₂ h12 => ?_⟩, ?_⟩
  · -- a geodesic
    obtain ⟨χ, hχ, hsχ⟩ := Δ.suspStructure.exists_chart (hreg s)
    have h0 : 0 < ((projIcc 0 Real.pi Real.pi_pos.le (t₀ (ψ s)) : Icc (0 : ℝ) Real.pi) : ℝ) := by
      rw [projIcc_of_mem _ (hI _)]; exact (ht₀ _).1
    have hπ : ((projIcc 0 Real.pi Real.pi_pos.le (t₀ (ψ s)) : Icc (0 : ℝ) Real.pi) : ℝ) <
        Real.pi := by
      rw [projIcc_of_mem _ (hI _)]; exact (ht₀ _).2
    obtain ⟨g, hg⟩ := Δ.chart_eq hχ h0 hπ hsχ
    refine ⟨χ, hχ, hsχ, _, _, hU.lorentz (g : Causal.Flat.lorentz 2), ?_⟩
    filter_upwards [hψc.continuousAt.eventually hg] with s' hs'
    have := hs' (projIcc 0 Real.pi Real.pi_pos.le (t₀ (ψ s')))
    show χ (γ₀ s') = _
    simp only [γ₀]
    rw [this, projIcc_of_mem _ (hI _), hdev, smul_dsGeo hU]
  · -- closed, of length `|c|`
    simp only [γ₀]
    rw [hψ1, Δ.periodic.add_one, ht₀1]
  · -- simple
    have hb : ∀ s, BiSusp.base (γ₀ s) = Δ.E (ψ s) := fun s => by
      simp only [γ₀]
      rw [BiSusp.base_mk]
      · rw [projIcc_of_mem _ (hI _)]; exact (ht₀ _).1
      · rw [projIcc_of_mem _ (hI _)]; exact (ht₀ _).2
    have hE : Δ.E (ψ s₁) = Δ.E (ψ s₂) := by rw [← hb, ← hb, h12]
    obtain ⟨n, hn⟩ := Δ.periodic.fiber _ _ hE
    have hs : s₂ = s₁ + n * |c| := by
      have := add_int_mul_of_add hΦ'1 n (ψ s₁)
      rw [mul_one, ← hn, hΦψ, hΦψ] at this
      exact this
    have hn0 : n = 0 := by
      have h1 : (n : ℝ) * |c| < 1 * |c| := by linarith [hs₁.1, hs₂.2]
      have h2 : (-1 : ℝ) * |c| < n * |c| := by linarith [hs₁.2, hs₂.1]
      have h1' : (n : ℝ) < 1 := lt_of_mul_lt_mul_right h1 hcpos.le
      have h2' : (-1 : ℝ) < n := lt_of_mul_lt_mul_right h2 hcpos.le
      have : n < 1 := by exact_mod_cast h1'
      have : -1 < n := by exact_mod_cast h2'
      omega
    rw [hs, hn0]; simp
  · -- its range is the equator
    ext x
    refine ⟨fun ⟨s, hs⟩ => hs ▸ hmem s, fun hx => ?_⟩
    have hxp := hx.1
    obtain ⟨σ₁, hσ₁⟩ := Δ.periodic.surjective (BiSusp.base x)
    have hht := BiSusp.notMem_poles_iff.1 hxp
    have hxeq : x = BiSusp.mk (Δ.E σ₁) (projIcc 0 Real.pi Real.pi_pos.le (BiSusp.ht x)) := by
      rw [hσ₁, projIcc_of_mem _ (BiSusp.ht_mem x)]; exact BiSusp.eq_mk_base hxp
    have hta1 : F.ta (arcVec C.pt (Δ.vlift σ₁) (BiSusp.ht x)) = 0 :=
      (Δ.mem_equator_iff F hht).1 (hxeq ▸ hx)
    refine ⟨Φ' σ₁, ?_⟩
    simp only [γ₀]
    rw [hψΦ]
    have ht : t₀ σ₁ = BiSusp.ht x :=
      F.mu_arcVec_inj (Δ.cz_vlift_ne F σ₁) (ht₀ σ₁) hht (by
        rw [hmu₀]; simp [TFrame.mu, hta1])
    rw [ht, ← hxeq]

/-- **Every simple closed space-like geodesic of the de Sitter part of `𝔢(L)` has length the cone
angle** (every time-like `p`, every cone angle). -/
theorem GammaLinkCircle.DevData.length_eq_coneAngle
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) (Δ : C.DevData) {γ : ℝ → BiSusp L} {ℓ : ℝ}
    (h : Δ.suspStructure.IsSimpleClosedSpacelikeGeodesic γ ℓ) : ℓ = C.coneAngle := by
  obtain ⟨F⟩ := exists_tFrame hp
  obtain ⟨Φ, c, hΦc, hΦ, hΦ1, hΦi, hc, hcone⟩ := Δ.exists_angle F
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hℓ, -⟩ :=
    Δ.simpleClosed_analysis F hΦc hΦ hΦ1 hΦi hc h
  rw [hℓ, hcone]

/-- **Uniqueness**: unless the cone angle is a multiple of `2π`, every simple closed space-like
geodesic of the de Sitter part of `𝔢(L)` is the equator. -/
theorem GammaLinkCircle.DevData.range_eq_equator
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) (Δ : C.DevData)
    (hθ : ∀ k : ℤ, C.coneAngle ≠ 2 * π * k) {γ : ℝ → BiSusp L} {ℓ : ℝ}
    (h : Δ.suspStructure.IsSimpleClosedSpacelikeGeodesic γ ℓ) : range γ = Δ.equator := by
  obtain ⟨F⟩ := exists_tFrame hp
  obtain ⟨Φ, c, hΦc, hΦ, hΦ1, hΦi, hc, hcone⟩ := Δ.exists_angle F
  obtain ⟨σ', hgt, X, V, hσc, hXV, hh, hγeq, hk, hφ, -, hX⟩ :=
    Δ.simpleClosed_analysis F hΦc hΦ hΦ1 hΦi hc h
  have hc2 : ∀ k : ℤ, c ≠ 2 * π * k := by
    intro k hk'
    apply hθ |k|
    rw [hcone, hk', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), Int.cast_abs]
  obtain ⟨ha, hb⟩ := hX hc2
  have hta0 : ∀ s, F.ta (dsVec X V s) = 0 := fun s => by rw [F.ta_dsVec, ha, hb]; ring
  have htaγ : ∀ s, F.ta (arcVec C.pt (Δ.vlift (σ' s)) (hgt s)) = 0 := fun s => by
    obtain ⟨k, -, hks⟩ := hk s
    rw [hks, F.ta_smul, hta0, mul_zero]
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    rw [hγeq s]
    exact (Δ.mem_equator_iff F (hh s)).2 (htaγ s)
  · intro hx
    have hxp := hx.1
    obtain ⟨σ₁, hσ₁⟩ := Δ.periodic.surjective (BiSusp.base x)
    have hht := BiSusp.notMem_poles_iff.1 hxp
    have hxeq : x = BiSusp.mk (Δ.E σ₁) (projIcc 0 Real.pi Real.pi_pos.le (BiSusp.ht x)) := by
      rw [hσ₁, projIcc_of_mem _ (BiSusp.ht_mem x)]; exact BiSusp.eq_mk_base hxp
    have hta1 : F.ta (arcVec C.pt (Δ.vlift σ₁) (BiSusp.ht x)) = 0 :=
      (Δ.mem_equator_iff F hht).1 (hxeq ▸ hx)
    obtain ⟨ε, hε, hφlin⟩ := F.angle_of_equator hXV (hΦc.comp hσc) hφ ha hb
    have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    set s := ε * (Φ σ₁ - Φ (σ' 0))
    have hσs : σ' s = σ₁ := by
      apply hΦi
      have := hφlin s
      simp only [Function.comp_apply] at this
      rw [this]
      simp only [s, ← mul_assoc, hε2, one_mul]
      ring
    have hhs : hgt s = BiSusp.ht x := by
      have h1 := htaγ s
      rw [hσs] at h1
      exact F.mu_arcVec_inj (Δ.cz_vlift_ne F σ₁) (hh s) hht (by simp [TFrame.mu, h1, hta1])
    exact ⟨s, by rw [hγeq, hσs, hhs, ← hxeq]⟩

/-- **`𝔢(L)` has positive mass iff its cone angle is `< 2π`** (every time-like `p`). -/
theorem GammaLinkCircle.DevData.hasPositiveMass_iff
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) (Δ : C.DevData) :
    Δ.suspStructure.HasPositiveMass ↔ C.coneAngle < 2 * π := by
  constructor
  · intro h
    obtain ⟨γ, hγ, -⟩ := Δ.exists_simpleClosed_equator hp
    exact h γ _ hγ
  · intro h γ ℓ hγ
    rw [Δ.length_eq_coneAngle hp hγ]
    exact h

end Link


/-! ## 9. The definition is chart-free; the link form of the remark -/

/-- The points of a great circle `dsGeo` lie in `dS²`. -/
theorem dsGeo_mem_deSitter {x v : 𝕄} (h : IsDSFrame x v) (s : ℝ) :
    dsGeo x v s ∈ HS.piece 2 .deSitter := by
  show 0 < Causal.Flat.minkQ ((dsGeo x v s : HS 2) : 𝕄)
  have hne := dsVec_ne_zero h s
  rw [dsGeo_eq, coe_rayNormalize _ hne]
  have : Causal.Flat.minkQ (‖dsVec x v s‖⁻¹ • dsVec x v s) =
      (‖dsVec x v s‖⁻¹) ^ 2 * Causal.Flat.minkQ (dsVec x v s) := by
    rw [minkQ_two, minkQ_two]
    simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [this, minkQ_dsVec h, mul_one]
  have : 0 < ‖dsVec x v s‖ := norm_pos_iff.2 hne
  positivity

namespace SingularHSStructure

variable {M : Type*} [TopologicalSpace M] {A : SingularHSStructure M}

/-- **Chart independence**: a space-like geodesic is a unit-speed great circle of `dS²` in
**every** chart of the structure (the chart changes lie in `SO₀(1,2)`). -/
theorem IsSpacelikeGeodesic.forall_chart {γ : ℝ → M} (h : A.IsSpacelikeGeodesic γ) (s : ℝ)
    {e : OpenPartialHomeomorph M (HS 2)} (he : e ∈ A.atlas) (hs : γ s ∈ e.source) :
    ∃ x v : 𝕄, IsDSFrame x v ∧ ∀ᶠ s' in 𝓝 s, e (γ s') = dsGeo x v s' := by
  obtain ⟨-, e₀, he₀, hs₀, x, v, hxv, hev⟩ := h.2 s
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid (A.compatible e₀ he₀ e he) hs₀ hs
  refine ⟨_, _, hxv.lorentz g, ?_⟩
  filter_upwards [h.1.continuousAt.eventually hg, hev] with s' h1 h2
  rw [h1, h2, smul_dsGeo hxv]

/-- **A space-like geodesic lies in the de Sitter part**, read in any chart. -/
theorem IsSpacelikeGeodesic.mem_deSitter {γ : ℝ → M} (h : A.IsSpacelikeGeodesic γ) (s : ℝ)
    {e : OpenPartialHomeomorph M (HS 2)} (he : e ∈ A.atlas) (hs : γ s ∈ e.source) :
    e (γ s) ∈ HS.piece 2 .deSitter := by
  obtain ⟨x, v, hxv, hev⟩ := h.forall_chart s he hs
  rw [hev.self_of_nhds]
  exact dsGeo_mem_deSitter hxv s

end SingularHSStructure

section LinkForm

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

/-- **Positive mass of `𝔢(L)` is positive mass of the singularity** (l.1826–1827: the notion
« generalizes the natural notion of positivity for time-like singularities »): at a time-like
`p`, `𝔢(L)` has positive mass iff `m = 1 − θ/2π > 0`. -/
theorem GammaLinkCircle.DevData.hasPositiveMass_iff_mass_pos
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) (Δ : C.DevData) :
    Δ.suspStructure.HasPositiveMass ↔ 0 < C.mass := by
  rw [Δ.hasPositiveMass_iff hp, GammaLinkCircle.mass_pos_iff]

/-- …and, for a non-regular time-like link, iff the singularity is positive in the sense of
`bbsdef:hs_surface_interaction_singular_line`. -/
theorem GammaLinkCircle.DevData.hasPositiveMass_iff_isPositive
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) (hreg : ¬ C.IsRegular) (Δ : C.DevData) :
    Δ.suspStructure.HasPositiveMass ↔ C.IsPositive := by
  rw [Δ.hasPositiveMass_iff hp, GammaLinkCircle.isPositive_iff_of_timelike hp hreg]

/-- **The link computation of the remark** (`bbsrem:singular_ads_manifold_cone`, l.1797–1809):
for a time-like singularity of cone angle `θ < 2π` (positive mass), the de Sitter part of the
link `𝔢(L)` contains a simple closed space-like geodesic, it is unique (every one has the
equator as its image), its length is the cone angle `θ`; so every simple closed space-like geodesic of the
de Sitter part has length `< 2π`. -/
theorem GammaLinkCircle.DevData.link_simpleClosed_geodesic
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) (Δ : C.DevData) (hθ : C.coneAngle < 2 * π) :
    (∃ γ : ℝ → BiSusp L, Δ.suspStructure.IsSimpleClosedSpacelikeGeodesic γ C.coneAngle) ∧
    (∀ (γ γ' : ℝ → BiSusp L) (ℓ ℓ' : ℝ), Δ.suspStructure.IsSimpleClosedSpacelikeGeodesic γ ℓ →
      Δ.suspStructure.IsSimpleClosedSpacelikeGeodesic γ' ℓ' → range γ = range γ') ∧
    (∀ (γ : ℝ → BiSusp L) (ℓ : ℝ), Δ.suspStructure.IsSimpleClosedSpacelikeGeodesic γ ℓ →
      ℓ = C.coneAngle ∧ ℓ < 2 * π) := by
  have hpos := C.coneAngle_pos_of_timelike hp
  have hnot : ∀ k : ℤ, C.coneAngle ≠ 2 * π * k := by
    intro k hk
    have h1 : (0 : ℝ) < k := by
      by_contra h; push Not at h; nlinarith [Real.pi_pos]
    have h2 : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have : (0 : ℤ) < k := by exact_mod_cast h1
    have : k < (1 : ℤ) := by exact_mod_cast h2
    omega
  obtain ⟨γ₀, hγ₀, -⟩ := Δ.exists_simpleClosed_equator hp
  refine ⟨⟨γ₀, hγ₀⟩, fun γ γ' ℓ ℓ' h h' => ?_, fun γ ℓ h => ?_⟩
  · rw [Δ.range_eq_equator hp hnot h, Δ.range_eq_equator hp hnot h']
  · have := Δ.length_eq_coneAngle hp h
    exact ⟨this, this ▸ hθ⟩

end LinkForm

end GX
