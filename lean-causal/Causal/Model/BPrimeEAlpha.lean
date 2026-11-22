import Causal.Model.EAlphaGX
import Causal.Model.EAlphaContinuation

/-!
# (b′) at `E_κ`, `κ > 0`: BTZ_1's `prop:isom` for `α, β > 0`, in local form

`defi:causal_Ealpha` — `ETT.tex:1335`. **Not marked** (SCOPE): the label's `(G,X)` sentence is
about every `E_{≥0}`-manifold, `E₀` included (OQ-34/OQ-35), and the row waits on OQ-82 (the
group), OQ-64 ((b′)) and OQ-18 (uniqueness). This file proves a model fact of `E_κ`, `κ > 0`:
every a.e. isomorphism chart `ψ : E_κ ⇀ E_κ′` is a chart isomorphism of the causalities, the
singular line included; hence the `(G,X)` sentence for `E_{>0}`-manifolds. Target
`T-ett-bprime-ealpha`.

> The causal and chronological orders of $\mass{\alpha}$ give rise to a sheaf with values in
> $\mathbf{C}$: for $\U\subset \mass{\alpha}$ open and $x,y\in \U$, one sets $x\leq_\U y$ (resp.
> $x\ll_\U y$) if and only if there is a future causal (resp. chronological) curve from $x$ to $y$
> in $\U$. On any $\mass{\geq0}$-manifold $M$ there is then a unique causal structure inducing that
> of $\mass{\alpha}$ in every chart [...] (`ETT.tex:1336–1340`)

The step at the models is `prop:isom` of `brunswic2021cauchy`
(`papers/gx/sources/2108.12631/src/BTZ_1.tex:378–383`, proof l.445–465), for `α, β > 0`:

> Let $\alpha,\beta\in \R_+$ with $\alpha\neq 2\pi$, and let $\U$ be an open connected
> subset of $\E^{1,2}_\alpha$ containing a singular point and let
> $\phi:\U\rightarrow \E^{1,2}_\beta$ be an almost everywhere $\mass{}$-morphism. If $\phi$ is a
> local homeomorphism then $\alpha=\beta$ and $\phi$ is the restriction of an element of
> $\isom(\E^{1,2}_\alpha)$.

## What is proved (no `sorry`)

* **`prop:isom` for `α, β > 0`, local form** (`prop_isom_local`): for `κ ≠ 2π` and an a.e.
  isomorphism chart `ψ : E_κ ⇀ E_κ′` (`IsAEChart` for `EAlphaGX.singularGX`) whose source contains
  a point `p` of the singular line, `κ′ = κ`, and on a ball about `p`,
  `ψ (t, polar(r, θ)) = (t + s, polar(r, θ + c))`, `c ∈ ℝ/κℤ`: a rotation about the line after a
  translation along it. Type invariance alone: `eq_of_isAEChart`. Same model, as a map of
  BTZ_1's `Isom(E_κ)` (l.373): `exists_eqOn_rotShift`.
* **The converse** (`isAEChart_rotShift`): every rotation-translation `rotShift s c` is an a.e.
  isomorphism chart through the line, and a chart isomorphism (`chartIso_rotShift`): near the line
  the a.e. isomorphism charts are rotation-translations, and every rotation-translation is one.
* **(b′) at the models `E_κ`, `κ > 0`** (`chartIso_of_isAEChart`): every a.e. isomorphism chart
  `ψ : E_κ ⇀ E_κ′`, its source meeting the line or not, is a `ChartIso` of `massive κ` into
  `massive κ′`. As the hypothesis `hiso` of `existsUnique_causality_singularGX_dec25` for the
  family `{κ // 0 < κ}`: `hiso_family`.
* **`E_{>0}`-manifolds** (`existsUnique_causality_ealpha`): a singular `(Isom, E^{1,2})`-manifold
  whose singular points lie in a.e. isomorphism charts into models `E_κ`, `κ > 0`, carries an
  absolutely minimal causality making every chart an isomorphism, unique among absolutely minimal
  ones; no model hypothesis is left.
* **The reflection** `conjE` (`θ ↦ −θ`) is a chart isomorphism (`chartIso_conjE`) and, under
  `Flat.isom 2 = SO₀(1,2) ⋉ ℝ³`, not an a.e. isomorphism chart (`not_isAEChart_conjE`) (OQ-82).
* Non-vacuity: `nonvacuous` (at `κ = π`).

## The route (BPrimeE0's slit box, for a timelike axis)

Parameters `b = (t, r, θ)` of the slit box `|t − t_p| < ε`, `0 < r < ε`, `|θ| < κ/2` give the
point `pt b = (t, polar(r, θ))` and its development `devPt t r θ = (t, r e^{iθ})`. (1) `HolRel`:
near `b`, `ψ` reads from a sector chart normalized to the development into a sector chart of
`E_κ′` normalized by a real representative of its centre (`chart_dev`) as one isometry `g`, unique
modulo the holonomy `rotIsom κ′` (`HolRel.unique`); so one `g` on the box (`exists_holRel`).
(2) Along `r → 0` it sends the time axis into itself (`smul_timeAxis`). (3) Such an isometry is
`(t, x) ↦ (t + s, R_φ x)`: no boost, the determinant excludes the reflections
(`isom_of_timeAxis`). (4) The development fixes the angle of `ψ (pt b)` modulo `2π` only; the
angle read in the target charts is continuous, so one `c ∈ ℝ/κ′ℤ` serves on the box
(`exists_slitBox`, a second preconnectedness argument). (5) Continuity across `θ = ±κ/2` gives
`κ ∈ κ′ℤ`, injectivity at `θ = ±κ′/2` gives `κ′ ≥ κ` (`eq_of_isAEChart`). (6) One-sided limits
extend the formula to the ball (`prop_isom_local`). (7) Locality and the regular case: (b′).

## Hypothesis checklist

| paper / source | here |
|---|---|
| BTZ_1 prop:isom: `α, β ∈ ℝ₊`, `α ≠ 2π` | `α ≠ 2π` ✓ carried; ⚠ special case: `α, β > 0` (`E₀ → E₀` is `Causal.Port.BPrimeE0`, `E₀ ↔ E_κ` is `Causal.Remarks.MassAModelsInstance`) |
| prop:isom: `U` open connected containing a singular point; `φ` a local homeomorphism | ⚠ strengthened: `ψ` an open partial homeomorphism (injective on its source), as `IsAEChart` asks; ⚠ narrowed: local form, the conclusion on a ball about each singular point of the source (SCOPE) |
| prop:isom: `φ` an a.e. `𝔼`-morphism | ✓ carried, DEC-25's reading: `IsAEChart`, a.e. `(G,X)` both ways |
| `Isom(E^{1,2})` (ETT l.1333) | reading (OQ-82): `Flat.isom 2`; used once, through the determinant (`isom_of_timeAxis`) |
| « isomorphisms of the model spaces » (ETT l.631–632) | reading (OQ-64): `IsAEChart`; an isomorphism of topological spacetimes is `ChartIso` |
| « unique causal structure » (ETT l.1339) | reading (OQ-18): unique among absolutely minimal causalities |
| « On any `E_{≥0}`-manifold » (ETT l.1339) | ⚠ special case: `E_{>0}`-manifolds (`existsUnique_causality_ealpha`); every `E_{≥0}`-manifold is the assembly over `MassAModel` (`Causal.Remarks.EModelsBPrime`, `massA_singular_all`, `causal_Ealpha_manifolds`) |

## SCOPE (disclosed)

* **Why unmarked.** `E₀` and the pairs `E₀ ↔ E_κ` are not here (`Causal.Port.BPrimeE0`,
  `Causal.Remarks.MassAModelsInstance`; OQ-34/OQ-35); the readings
  OQ-82, OQ-64, OQ-18 are open; the `(G,X)` sentence is proved for `E_{>0}`-manifolds only.
* **Local form.** `prop:isom`'s global form on a connected `U` (by `lem:liouville`, l.361) is not
  proved, nor the case of a non-injective local homeomorphism; (b′) needs the local form only.
  The formula is stated for the polar representations `x.2 = polar(r, θ)` with `r ≥ 0`, which
  every point has (`exists_polar`).
* Under OQ-82's other reading `O↑(1,2) ⋉ ℝ³` the determinant step fails and the reflections
  `θ ↦ c − θ` become a.e. isomorphisms (by hand); they are chart isomorphisms (`chartIso_conjE`), but the
  theorem for that group is not stated (no such group in the library).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The template is
`Causal.Port.BPrimeE0` (T-ett-bprime-e0), read and not imported; gx's covering route
(`D_∞`, BTZ_1 l.445–465) is not followed: no cover is built.
-/

namespace Causal

open Set Real Metric Topology TopologicalSpace Filter

namespace BPrimeEAlpha

open EAlphaSector EAlphaContinuation EAlphaGX Complex

attribute [local instance] EAlphaGX.singularGX

/-! ### Generic lemmas -/

/-- Two maps continuous at `a`, equal along a non-trivial filter finer than `𝓝 a`, agree at `a`. -/
private theorem eq_of_eventuallyEq_of_continuousAt {X : Type*} [TopologicalSpace X] [T2Space X]
    {f g : ℝ → X} {a : ℝ} {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝 a) (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (h : f =ᶠ[l] g) : f a = g a :=
  tendsto_nhds_unique ((hf.tendsto.mono_left hl).congr' h) (hg.tendsto.mono_left hl)

/-- **A locally determined, pointwise unique choice on a preconnected set is global.** -/
theorem exists_forall_of_isPreconnected {X β : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {Q : β → X → Prop} (hloc : ∀ x ∈ S, ∃ c, ∀ᶠ y in 𝓝 x, Q c y)
    (huniq : ∀ x ∈ S, ∀ c c', Q c x → Q c' x → c = c') {x₀ : X} (hx₀ : x₀ ∈ S) :
    ∃ c, ∀ x ∈ S, Q c x := by
  obtain ⟨c₀, hc₀⟩ := hloc x₀ hx₀
  refine ⟨c₀, fun x hx => ?_⟩
  have key : ∀ c, (∀ᶠ y in 𝓝 x₀, Q c y) → ∀ᶠ y in 𝓝 x, Q c y := by
    refine hS.induction₂' (fun a b => ∀ c, (∀ᶠ y in 𝓝 a, Q c y) → ∀ᶠ y in 𝓝 b, Q c y) ?_ ?_
      hx₀ hx
    · intro a ha
      obtain ⟨ca, hca⟩ := hloc a ha
      filter_upwards [nhdsWithin_le_nhds hca.eventually_nhds, self_mem_nhdsWithin] with b hb hbS
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [huniq a ha c ca hc.self_of_nhds hca.self_of_nhds]
        exact hb
      · rw [huniq b hbS c ca hc.self_of_nhds hb.self_of_nhds]
        exact hca
    · intro a b d _ _ _ h1 h2 c hc
      exact h2 c (h1 c hc)
  exact (key c₀ hc₀).self_of_nhds

/-! ### Rotations of the cone, translations of time -/

namespace ConeRot

variable {α : ℝ}

/-- The rotation by `c` of polar coordinates. -/
def rotPt (c : AddCircle α) (p : ConePoint α) : ConePoint α := ⟨p.r, p.θ + c, p.r_nonneg⟩

theorem dist_rotPt (c : AddCircle α) (p q : ConePoint α) :
    dist (rotPt c p) (rotPt c q) = dist p q := by
  rw [ConePoint.dist_def, ConePoint.dist_def]
  simp only [rotPt, angDist, add_sub_add_right_eq_sub]

/-- **The rotation by `c ∈ ℝ/κℤ` of the cone `C_κ`** about its apex. -/
noncomputable def rot (c : AddCircle α) : Cone α → Cone α :=
  SeparationQuotient.lift (fun p => Cone.mk (rotPt c p)) fun p q h => by
    rw [Cone.mk_eq_mk_iff, dist_rotPt]
    exact Metric.inseparable_iff.1 h

theorem rot_mk (c : AddCircle α) (p : ConePoint α) : rot c (Cone.mk p) = Cone.mk (rotPt c p) :=
  rfl

theorem dist_rot (c : AddCircle α) (x y : Cone α) : dist (rot c x) (rot c y) = dist x y := by
  obtain ⟨p, rfl⟩ := Cone.mk_surjective x
  obtain ⟨q, rfl⟩ := Cone.mk_surjective y
  rw [rot_mk, rot_mk, Cone.dist_mk, Cone.dist_mk, dist_rotPt]

theorem rot_rot (c d : AddCircle α) (x : Cone α) : rot c (rot d x) = rot (d + c) x := by
  obtain ⟨p, rfl⟩ := Cone.mk_surjective x
  rw [rot_mk, rot_mk, rot_mk]
  congr 1
  ext
  · rfl
  · simp only [rotPt, add_assoc]

theorem rot_zero (x : Cone α) : rot 0 x = x := by
  obtain ⟨p, rfl⟩ := Cone.mk_surjective x
  rw [rot_mk]
  congr 1
  ext
  · rfl
  · simp only [rotPt, add_zero]

theorem rot_polar (c : AddCircle α) (r : ℝ) (θ : AddCircle α) :
    rot c (Cone.polar (r, θ)) = Cone.polar (r, θ + c) :=
  rfl

/-- The rotation as an isometry of `C_κ`. -/
noncomputable def rotIso (c : AddCircle α) : Cone α ≃ᵢ Cone α where
  toFun := rot c
  invFun := rot (-c)
  left_inv x := by rw [rot_rot, add_neg_cancel, rot_zero]
  right_inv x := by rw [rot_rot, neg_add_cancel, rot_zero]
  isometry_toFun := Isometry.of_dist_eq (dist_rot c)

theorem rotIso_apply (c : AddCircle α) (x : Cone α) : rotIso c x = rot c x := rfl

/-- The reflection `θ ↦ −θ` of polar coordinates. -/
def conjPt (p : ConePoint α) : ConePoint α := ⟨p.r, -p.θ, p.r_nonneg⟩

theorem dist_conjPt (p q : ConePoint α) : dist (conjPt p) (conjPt q) = dist p q := by
  rw [ConePoint.dist_def, ConePoint.dist_def]
  simp only [conjPt, angDist, neg_sub_neg, norm_sub_rev]

/-- **The reflection `θ ↦ −θ` of the cone `C_κ`.** -/
noncomputable def conj : Cone α → Cone α :=
  SeparationQuotient.lift (fun p => Cone.mk (conjPt p)) fun p q h => by
    rw [Cone.mk_eq_mk_iff, dist_conjPt]
    exact Metric.inseparable_iff.1 h

theorem conj_polar (r : ℝ) (θ : AddCircle α) : conj (Cone.polar (r, θ)) = Cone.polar (r, -θ) :=
  rfl

theorem dist_conj (x y : Cone α) : dist (conj x) (conj y) = dist x y := by
  obtain ⟨p, rfl⟩ := Cone.mk_surjective x
  obtain ⟨q, rfl⟩ := Cone.mk_surjective y
  exact dist_conjPt p q

theorem conj_conj (x : Cone α) : conj (conj x) = x := by
  obtain ⟨p, rfl⟩ := Cone.mk_surjective x
  show Cone.mk (conjPt (conjPt p)) = Cone.mk p
  congr 1
  ext
  · rfl
  · exact neg_neg _

/-- The reflection as an isometry of `C_κ`. -/
noncomputable def conjIso : Cone α ≃ᵢ Cone α where
  toFun := conj
  invFun := conj
  left_inv := conj_conj
  right_inv := conj_conj
  isometry_toFun := Isometry.of_dist_eq dist_conj

end ConeRot

section Shift

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A future causal curve is carried by a translation of time times a map of space preserving
distances. -/
theorem staticLe_map_shift {f : X → Y} (hf : ∀ x y, dist (f x) (f y) = dist x y) {s : ℝ}
    {g : ℝ × X → ℝ × Y} (hg : ∀ z, g z = (z.1 + s, f z.2)) {U : Set (ℝ × X)} {U' : Set (ℝ × Y)}
    (hU : MapsTo g U U') {p q : ℝ × X} (h : staticLe U p q) : staticLe U' (g p) (g q) := by
  obtain ⟨h1, γ, hp, hq, hγ⟩ := h
  rw [hg, hg]
  refine ⟨by simp only; linarith, fun τ => f (γ (τ - s)), by simp [hp], by simp [hq], ⟨?_, ?_⟩⟩
  · intro τ hτ τ' hτ'
    simp only at hτ hτ' ⊢
    rw [hf]
    have := hγ.lip (τ - s) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ (τ' - s)
      ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
    rwa [sub_sub_sub_cancel_right] at this
  · intro τ hτ
    simp only at hτ
    have h2 := hU (hγ.mem (τ - s) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
    rw [hg] at h2
    simpa using h2

theorem staticLt_map_shift {f : X → Y} (hf : ∀ x y, dist (f x) (f y) = dist x y) {s : ℝ}
    {g : ℝ × X → ℝ × Y} (hg : ∀ z, g z = (z.1 + s, f z.2)) {U : Set (ℝ × X)} {U' : Set (ℝ × Y)}
    (hU : MapsTo g U U') {p q : ℝ × X} (h : staticLt U p q) : staticLt U' (g p) (g q) := by
  obtain ⟨h1, L, hL, γ, hp, hq, hγ⟩ := h
  rw [hg, hg]
  refine ⟨by simp only; linarith, L, hL, fun τ => f (γ (τ - s)), by simp [hp], by simp [hq],
    ⟨?_, ?_⟩⟩
  · intro τ hτ τ' hτ'
    simp only at hτ hτ' ⊢
    rw [hf]
    have := hγ.lip (τ - s) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ (τ' - s)
      ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
    rwa [sub_sub_sub_cancel_right] at this
  · intro τ hτ
    simp only at hτ
    have h2 := hU (hγ.mem (τ - s) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
    rw [hg] at h2
    simpa using h2

/-- The translation of time by `s` times an isometry of space. -/
noncomputable def shiftIso (s : ℝ) (e : X ≃ᵢ Y) : ℝ × X ≃ₜ ℝ × Y :=
  (Homeomorph.addRight s).prodCongr e.toHomeomorph

theorem shiftIso_apply (s : ℝ) (e : X ≃ᵢ Y) (z : ℝ × X) : shiftIso s e z = (z.1 + s, e z.2) :=
  rfl

theorem shiftIso_symm_apply (s : ℝ) (e : X ≃ᵢ Y) (z : ℝ × Y) :
    (shiftIso s e).symm z = (z.1 + -s, e.symm z.2) :=
  rfl

variable [GeodesicSpace X] [GeodesicSpace Y]

/-- **A translation of time times an isometry of space is a chart isomorphism of the static
spacetimes.** -/
theorem chartIso_shiftIso (s : ℝ) (e : X ≃ᵢ Y) :
    ChartIso (staticCausality X) (staticCausality Y) (shiftIso s e).toOpenPartialHomeomorph := by
  set R := shiftIso s e with hR
  intro U hU x hx y hy
  have himg : ((chartImage R.toOpenPartialHomeomorph U : Opens (ℝ × Y)) : Set (ℝ × Y)) =
      R '' U := by
    rw [coe_chartImage_of_le hU]; rfl
  have hmaps : MapsTo R U (chartImage R.toOpenPartialHomeomorph U : Set (ℝ × Y)) :=
    fun z hz => by rw [himg]; exact mem_image_of_mem R hz
  have hmaps' : MapsTo R.symm (chartImage R.toOpenPartialHomeomorph U : Set (ℝ × Y)) U := by
    intro z hz
    rw [himg] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [Homeomorph.symm_apply_apply]
  have hg : ∀ z, R z = (z.1 + s, e z.2) := fun z => rfl
  have hg' : ∀ z, R.symm z = (z.1 + -s, e.symm z.2) := fun z => rfl
  show (staticLe (U : Set (ℝ × X)) x y ↔
      staticLe (chartImage R.toOpenPartialHomeomorph U : Set (ℝ × Y)) (R x) (R y)) ∧
    (staticLt (U : Set (ℝ × X)) x y ↔
      staticLt (chartImage R.toOpenPartialHomeomorph U : Set (ℝ × Y)) (R x) (R y))
  refine ⟨⟨fun h => staticLe_map_shift e.dist_eq hg hmaps h, fun h => ?_⟩,
    ⟨fun h => staticLt_map_shift e.dist_eq hg hmaps h, fun h => ?_⟩⟩
  · have := staticLe_map_shift e.symm.dist_eq hg' hmaps' h
    rwa [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at this
  · have := staticLt_map_shift e.symm.dist_eq hg' hmaps' h
    rwa [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at this

end Shift

/-! ### Polar points, developments and normalized sector charts -/

section Polar

variable {α : ℝ}

/-- The point `(t, polar(r, θ))` of `E_κ` of parameter `b = (t, r, θ)`, for a real angle `θ`. -/
noncomputable def pt (α : ℝ) (b : ℝ × ℝ × ℝ) : Massive α :=
  (b.1, Cone.polar (b.2.1, (b.2.2 : AddCircle α)))

theorem continuous_pt : Continuous (pt α) := by
  unfold pt
  exact continuous_fst.prodMk (Cone.continuous_polar.comp
    (continuous_snd.fst.prodMk ((AddCircle.continuous_mk' α).comp continuous_snd.snd)))

/-- At radius `0` the polar point is on the singular line. -/
theorem pt_zero (t θ : ℝ) : pt α (t, 0, θ) = (t, Cone.apex) :=
  Prod.ext rfl (Cone.mk_eq_apex (ConePoint.of_r le_rfl _))

/-- Every point of `C_κ` is a polar point with a real angle. -/
theorem exists_polar (y : Cone α) : ∃ r θ : ℝ, 0 ≤ r ∧ y = Cone.polar (r, (θ : AddCircle α)) := by
  obtain ⟨q, rfl⟩ := Cone.mk_surjective y
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective q.θ
  refine ⟨q.r, θ, q.r_nonneg, ?_⟩
  rw [← Cone.polar_rad_θ q, ← hθ]

/-- Near a point `p` of the line, the polar points of radius `< ε` at times `ε`-close to `p`'s
lie in the ball of radius `ε` about `p`. -/
theorem pt_mem_ball {p : Massive α} (hp : p.2 = Cone.apex) {ε t r : ℝ} (ht : t ∈ ball p.1 ε)
    (hr0 : 0 ≤ r) (hrε : r < ε) (θ : ℝ) : pt α (t, r, θ) ∈ ball p ε := by
  rw [mem_ball, Prod.dist_eq, hp]
  refine max_lt ht ?_
  rw [dist_comm]
  show Cone.rad (Cone.polar (r, (θ : AddCircle α))) < ε
  rw [rad_polar hr0]
  exact hrε

theorem continuous_devPt : Continuous fun b : ℝ × ℝ × ℝ => devPt b.1 b.2.1 b.2.2 := by
  unfold devPt
  exact continuous_fst.prodMk (Complex.orthonormalBasisOneI.repr.continuous.comp
    ((Complex.continuous_ofReal.comp continuous_snd.fst).mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd.snd).mul continuous_const))))

theorem rotIsom_smul_devPt (c t ρ θ : ℝ) : rotIsom c • devPt t ρ θ = devPt t ρ (θ + c) := by
  unfold devPt
  rw [rotIsom_smul_repr]
  congr 2
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem norm_devPt_snd (t ρ θ : ℝ) : ‖(devPt t ρ θ).2‖ = |ρ| := by
  unfold devPt
  simp only
  rw [LinearIsometryEquiv.norm_map, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

theorem devPt_zero (t θ : ℝ) : devPt t 0 θ = ((t, 0) : Minkowski 2) := by
  unfold devPt
  simp

/-- Two developments with nonnegative radii, the second positive, are equal only if their times
and radii are, and their angles agree modulo `2π`. -/
theorem devPt_eq_devPt {t t' ρ ρ' θ θ' : ℝ} (hρ : 0 ≤ ρ) (hρ' : 0 < ρ')
    (h : devPt t ρ θ = devPt t' ρ' θ') : t = t' ∧ ρ = ρ' ∧ cexp (θ * I) = cexp (θ' * I) := by
  have h1 : t = t' := congrArg Prod.fst h
  have h2 : ρ = ρ' := by
    have := congrArg (fun v : Minkowski 2 => ‖v.2‖) h
    simp only [norm_devPt_snd, abs_of_nonneg hρ, abs_of_pos hρ'] at this
    exact this
  refine ⟨h1, h2, ?_⟩
  subst h2
  have h3 := Complex.orthonormalBasisOneI.repr.injective (congrArg Prod.snd h)
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hρ'.ne') h3

/-- Two rotations about the time axis agreeing at a point off the axis are equal. -/
theorem rotIsom_eq_of_smul_eq {a b : ℝ} {v : Minkowski 2} (hv : v.2 ≠ 0)
    (h : rotIsom a • v = rotIsom b • v) : rotIsom a = rotIsom b := by
  apply rotIsom_eq_of_exp_eq
  rw [rotIsom_smul, rotIsom_smul] at h
  have h2 := congrArg Prod.snd h
  simp only at h2
  rw [planeRot_apply', planeRot_apply'] at h2
  have h3 := Complex.orthonormalBasisOneI.repr.injective h2
  have hu : Complex.orthonormalBasisOneI.repr.symm v.2 ≠ 0 := by
    rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  exact mul_right_cancel₀ hu h3

variable [Fact (0 < α)]

/-- The real angle of a point of a sector chart's disc, read with the representative `φ` of the
direction of the chart's centre. -/
noncomputable def chartAngle (k : Index α) (φ : ℝ) (y : Massive α) : ℝ :=
  φ + Complex.arg ((planeChart k).symm y.2)

/-- **A sector chart, normalized by a representative of its centre, is a development**: on its
source it is `devPt t r θ` with `y = (t, polar(r, θ))`, `θ` its angle `chartAngle`. -/
theorem chart_dev (k : Index α) (φ : ℝ) (hφ : (φ : AddCircle α) = k.1.θ) {y : Massive α}
    (hy : y ∈ (chart k).source) :
    y.2 = Cone.polar (Cone.rad y.2, (chartAngle k φ y : AddCircle α)) ∧
      rotIsom φ • chart k y = devPt y.1 (Cone.rad y.2) (chartAngle k φ y) := by
  have hy2 : y.2 ∈ (planeChart k).target := by
    rw [chart_source] at hy
    rw [planeChart_target]
    exact hy.2
  obtain ⟨z, hz⟩ : ∃ z, (planeChart k).symm y.2 = z := ⟨_, rfl⟩
  have hzs : z ∈ (planeChart k).source := hz ▸ (planeChart k).map_target hy2
  have hyz : y.2 = fromPlane k.1.θ z := by
    rw [← planeChart_apply, ← hz, (planeChart k).right_inv hy2]
  have hrad : Cone.rad y.2 = ‖z‖ := by rw [hyz, fromPlane, Cone.rad_mk]
  have hang : chartAngle k φ y = φ + Complex.arg z := by rw [chartAngle, hz]
  rw [hang, hrad]
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [hyz]
    unfold fromPlane Cone.polar
    congr 1
    ext
    · exact (ConePoint.of_r (norm_nonneg z) _).symm
    · show k.1.θ + ((Complex.arg z : ℝ) : AddCircle α) = ((φ + Complex.arg z : ℝ) : AddCircle α)
      rw [AddCircle.coe_add, hφ]
  · rw [chart_apply, coneChart_apply, hz, rotIsom_smul_repr]
    unfold devPt
    congr 2
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [show (((φ + Complex.arg z : ℝ)) : ℂ) * I = φ * I + Complex.arg z * I by push_cast; ring,
      Complex.exp_add]
    ring

theorem continuousOn_chartAngle (k : Index α) (φ : ℝ) :
    ContinuousOn (chartAngle k φ) (chart k).source := by
  intro y hy
  have hy2 : y.2 ∈ (planeChart k).target := by
    rw [chart_source] at hy
    rw [planeChart_target]
    exact hy.2
  have hzs : (planeChart k).symm y.2 ∈ planeDisc α k.1.r := (planeChart k).map_target hy2
  have harg := abs_arg_lt_of_mem_planeDisc k.2 (Fact.out : 0 < α) hzs
  have hslit : (planeChart k).symm y.2 ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]
    refine ⟨fun h => ?_, harg.1⟩
    have := halfAngle_le_pi_div_two (α := α)
    rw [h, abs_of_pos pi_pos] at harg
    linarith [pi_pos]
  have hc : ContinuousAt (fun y : Massive α => (planeChart k).symm y.2) y :=
    ((planeChart k).continuousAt_symm hy2).comp continuous_snd.continuousAt
  exact (continuousAt_const.add ((continuousAt_arg hslit).comp
    (f := fun y : Massive α => (planeChart k).symm y.2) hc)).continuousWithinAt

theorem rad_pos_of_mem_chart_source {k : Index α} {y : Massive α} (hy : y ∈ (chart k).source) :
    0 < Cone.rad y.2 := by
  have h := chart_source_subset_regPart k hy
  refine lt_of_le_of_ne (Cone.rad_nonneg _) fun h0 => h ?_
  exact Cone.rad_eq_zero.1 h0.symm

theorem chart_snd_ne_zero {k : Index α} {y : Massive α} (hy : y ∈ (chart k).source) :
    (chart k y).2 ≠ 0 := by
  have hy2 : y.2 ∈ (planeChart k).target := by
    rw [chart_source] at hy
    rw [planeChart_target]
    exact hy.2
  rw [chart_apply, coneChart_apply]
  simp only
  rw [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  exact (abs_arg_lt_of_mem_planeDisc k.2 (Fact.out : 0 < α)
    ((planeChart k).map_target hy2)).1

/-- **Two rotated sector charts agreeing at one point agree on their whole overlap**
(`exists_rotation`: they differ there by one rotation). -/
theorem rotIsom_smul_chart_eqOn {k₁ k₂ : Index α} {a₁ a₂ : ℝ} {y₀ : Massive α}
    (h₁ : y₀ ∈ (chart k₁).source) (h₂ : y₀ ∈ (chart k₂).source)
    (h : rotIsom a₁ • chart k₁ y₀ = rotIsom a₂ • chart k₂ y₀) :
    ∀ y ∈ (chart k₁).source ∩ (chart k₂).source,
      rotIsom a₁ • chart k₁ y = rotIsom a₂ • chart k₂ y := by
  obtain ⟨c, hc⟩ := exists_rotation k₁ k₂
  rw [hc y₀ ⟨h₁, h₂⟩, ← mul_smul, ← rotIsom_add] at h
  have he := rotIsom_eq_of_smul_eq (chart_snd_ne_zero h₁) h
  intro y hy
  rw [hc y hy, ← mul_smul, ← rotIsom_add, he]

/-- The sector chart centred at `(ρ, φ₀)`, at a polar point near its centre: normalized by `φ₀`,
it is the development. -/
theorem chart_ringIndex_pt {ρ : ℝ} (hρ : 0 < ρ) (φ₀ : ℝ) {b : ℝ × ℝ × ℝ} (hr : 0 < b.2.1)
    (hθ : |b.2.2 - φ₀| < π)
    (hz : (b.2.1 : ℂ) * cexp (((b.2.2 - φ₀ : ℝ) : ℂ) * I) ∈ planeDisc α ρ) :
    pt α b ∈ (chart (ringIndex hρ φ₀)).source ∧
      rotIsom φ₀ • chart (ringIndex hρ φ₀) (pt α b) = devPt b.1 b.2.1 b.2.2 := by
  set k : Index α := ringIndex hρ φ₀
  have hz' : (b.2.1 : ℂ) * cexp (((b.2.2 - φ₀ : ℝ) : ℂ) * I) ∈ (planeChart k).source := by
    rw [planeChart_source]; exact hz
  have hpol : Cone.polar (b.2.1, (b.2.2 : AddCircle α)) =
      planeChart k ((b.2.1 : ℂ) * cexp (((b.2.2 - φ₀ : ℝ) : ℂ) * I)) := by
    rw [planeChart_apply]
    have := polar_eq_fromPlane (α := α) hr φ₀ (b.2.2 - φ₀) hθ
    rw [show φ₀ + (b.2.2 - φ₀) = b.2.2 by ring] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [chart_source]
    refine ⟨trivial, ?_⟩
    show Cone.polar (b.2.1, (b.2.2 : AddCircle α)) ∈ coneDisc k.1
    rw [hpol, ← planeChart_target]
    exact (planeChart k).map_source hz'
  · rw [chart_apply]
    show rotIsom φ₀ • ((b.1, coneChart k (Cone.polar (b.2.1, (b.2.2 : AddCircle α)))) :
      Minkowski 2) = _
    rw [coneChart_apply, hpol, (planeChart k).left_inv hz', rotIsom_smul_repr]
    unfold devPt
    congr 2
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Near a parameter `b₀` of positive radius, the sector chart centred at `pt b₀`, normalized by
its angle, is the development. -/
theorem eventually_chart_ringIndex_pt {b₀ : ℝ × ℝ × ℝ} (hr : 0 < b₀.2.1) :
    ∀ᶠ b in 𝓝 b₀, pt α b ∈ (chart (ringIndex hr b₀.2.2)).source ∧
      rotIsom b₀.2.2 • chart (ringIndex hr b₀.2.2) (pt α b) = devPt b.1 b.2.1 b.2.2 := by
  have hw := sin_halfAngle_pos (α := α)
  have h1 : ∀ᶠ b in 𝓝 b₀, 0 < b.2.1 :=
    (continuous_snd.fst.tendsto b₀).eventually (lt_mem_nhds hr)
  have h2 : ∀ᶠ b in 𝓝 b₀, |b.2.2 - b₀.2.2| < π := by
    have hc : Continuous fun b : ℝ × ℝ × ℝ => |b.2.2 - b₀.2.2| := by fun_prop
    refine (hc.tendsto b₀).eventually (gt_mem_nhds ?_)
    simp [pi_pos]
  have h3 : ∀ᶠ b in 𝓝 b₀, (b.2.1 : ℂ) * cexp (((b.2.2 - b₀.2.2 : ℝ) : ℂ) * I) ∈
      planeDisc α b₀.2.1 := by
    have hc : Continuous fun b : ℝ × ℝ × ℝ =>
        (b.2.1 : ℂ) * cexp (((b.2.2 - b₀.2.2 : ℝ) : ℂ) * I) := by fun_prop
    refine (hc.tendsto b₀).eventually (isOpen_ball.mem_nhds ?_)
    simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    exact mem_ball_self (mul_pos hr hw)
  filter_upwards [h1, h2, h3] with b hb1 hb2 hb3
  exact chart_ringIndex_pt hr b₀.2.2 hb1 hb2 hb3

end Polar

/-! ### One isometry develops `ψ` on a slit box -/

section HolRel

variable {α α' : ℝ} [Fact (0 < α)] [Fact (0 < α')]

/-- `ψ` reads near `pt b`, from a sector chart of `E_κ` normalized to the development near `b`
into a sector chart of `E_κ′` normalized by a representative `φ′` of its centre, as `g`. -/
def HolRel (ψ : OpenPartialHomeomorph (Massive α) (Massive α')) (g : Flat.isom 2)
    (b : ℝ × ℝ × ℝ) : Prop :=
  ∃ (k : Index α) (φ : ℝ) (k' : Index α') (φ' : ℝ), (φ' : AddCircle α') = k'.1.θ ∧
    (∀ᶠ b₁ in 𝓝 b, pt α b₁ ∈ (chart k).source ∧
      rotIsom φ • chart k (pt α b₁) = devPt b₁.1 b₁.2.1 b₁.2.2) ∧
    ∀ᶠ y in 𝓝 (pt α b), y ∈ (chart k).source ∧ ψ y ∈ (chart k').source ∧
      rotIsom φ' • chart k' (ψ y) = g • (rotIsom φ • chart k y)

/-- Near a parameter of positive radius in the source, `ψ` reads as one isometry: the local
`(G,X)` condition of `IsAEChart`. -/
theorem eventually_holRel (hα' : α' ≠ 2 * π) {ψ : OpenPartialHomeomorph (Massive α) (Massive α')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {b : ℝ × ℝ × ℝ} (hr : 0 < b.2.1)
    (hb : pt α b ∈ ψ.source) : ∃ g : Flat.isom 2, ∀ᶠ b₁ in 𝓝 b, HolRel ψ g b₁ := by
  set k : Index α := ringIndex hr b.2.2
  have hsrc := eventually_chart_ringIndex_pt (α := α) hr
  have hxk : pt α b ∈ (chart k).source := hsrc.self_of_nhds.1
  have hxr : pt α b ∈ Reg (Flat.isom 2) (Minkowski 2) (Massive α) :=
    regPart_subset_reg (chart_source_subset_regPart k hxk)
  have hψx := (hψ.mem_reg_iff hb).1 hxr
  rw [reg_eq hα'] at hψx
  obtain ⟨k', hk'⟩ := exists_mem_chart_source hψx
  obtain ⟨h, hh⟩ := hψ.regularOn.exists_smul_eq (pt α b) ⟨hb, hxr⟩ (chart k)
    (sectorAtlas_subset_aeAtlas (chart_mem_sectorAtlas k)) (chart k')
    (sectorAtlas_subset_aeAtlas (chart_mem_sectorAtlas k')) hxk hk'
  obtain ⟨φ', hφ'⟩ := QuotientAddGroup.mk_surjective k'.1.θ
  refine ⟨rotIsom φ' * h * rotIsom (-b.2.2), ?_⟩
  have hev : ∀ᶠ y in 𝓝 (pt α b), y ∈ (chart k).source ∧ ψ y ∈ (chart k').source ∧
      rotIsom φ' • chart k' (ψ y) =
        (rotIsom φ' * h * rotIsom (-b.2.2)) • (rotIsom b.2.2 • chart k y) := by
    filter_upwards [(chart k).open_source.mem_nhds hxk,
      (ψ.continuousAt hb).preimage_mem_nhds ((chart k').open_source.mem_nhds hk'), hh]
      with y h1 h2 h3
    refine ⟨h1, h2, ?_⟩
    rw [h3, ← mul_smul, ← mul_smul, mul_assoc (rotIsom φ' * h), ← rotIsom_add, neg_add_cancel,
      rotIsom_zero, mul_one]
  have hev2 := (continuous_pt.tendsto b).eventually hev.eventually_nhds
  filter_upwards [hsrc.eventually_nhds, hev2] with b₁ hb₁ hy
  exact ⟨k, b.2.2, k', φ', hφ', hb₁, hy⟩

/-- The relation is invariant under the holonomy `rotIsom κ′`. -/
theorem HolRel.mul_left {ψ : OpenPartialHomeomorph (Massive α) (Massive α')} {g : Flat.isom 2}
    {b : ℝ × ℝ × ℝ} (h : HolRel ψ g b) (n : ℤ) : HolRel ψ (rotIsom (n * α') * g) b := by
  obtain ⟨k, φ, k', φ', hφ', hs, ht⟩ := h
  refine ⟨k, φ, k', n * α' + φ', ?_, hs, ?_⟩
  · have h0 : ((n * α' : ℝ) : AddCircle α') = 0 :=
      (AddCircle.coe_eq_zero_iff α').2 ⟨n, by rw [zsmul_eq_mul]⟩
    rw [AddCircle.coe_add, h0, zero_add, hφ']
  · filter_upwards [ht] with y ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [rotIsom_add, mul_smul, h3, mul_smul]

/-- **Two isometries reading `ψ` at `b` differ by a power of the holonomy `rotIsom κ′`.** -/
theorem HolRel.unique {ψ : OpenPartialHomeomorph (Massive α) (Massive α')} {g g' : Flat.isom 2}
    {b : ℝ × ℝ × ℝ} (h : HolRel ψ g b) (h' : HolRel ψ g' b) :
    ∃ n : ℤ, g' = rotIsom (n * α') * g := by
  obtain ⟨k₁, φ₁, k₁', φ₁', hφ₁', hs₁, ht₁⟩ := h
  obtain ⟨k₂, φ₂, k₂', φ₂', hφ₂', hs₂, ht₂⟩ := h'
  -- the source charts agree near `pt b`
  have hS : ∀ y ∈ (chart k₁).source ∩ (chart k₂).source,
      rotIsom φ₁ • chart k₁ y = rotIsom φ₂ • chart k₂ y :=
    rotIsom_smul_chart_eqOn hs₁.self_of_nhds.1 hs₂.self_of_nhds.1
      (hs₁.self_of_nhds.2.trans hs₂.self_of_nhds.2.symm)
  -- the target charts differ by a power of the holonomy
  have hz₁ := ht₁.self_of_nhds.2.1
  have hz₂ := ht₂.self_of_nhds.2.1
  obtain ⟨hp₁, hd₁⟩ := chart_dev k₁' φ₁' hφ₁' hz₁
  obtain ⟨hp₂, hd₂⟩ := chart_dev k₂' φ₂' hφ₂' hz₂
  have hρ := rad_pos_of_mem_chart_source hz₁
  have hang : ((chartAngle k₂' φ₂' (ψ (pt α b)) - chartAngle k₁' φ₁' (ψ (pt α b)) : ℝ) :
      AddCircle α') = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact polar_inj hρ (hp₂.symm.trans hp₁)
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff α').1 hang
  rw [zsmul_eq_mul] at hn
  have hT0 : rotIsom φ₂' • chart k₂' (ψ (pt α b)) =
      rotIsom (n * α' + φ₁') • chart k₁' (ψ (pt α b)) := by
    rw [hd₂, rotIsom_add, mul_smul, hd₁, rotIsom_smul_devPt]
    congr 1
    linarith
  have hT := rotIsom_smul_chart_eqOn hz₂ hz₁ hT0
  -- rigidity near `pt b`
  have hall : ∀ᶠ y in 𝓝 (pt α b), y ∈ (chart k₁).source ∧
      g' • (rotIsom φ₁ • chart k₁ y) = (rotIsom (n * α') * g) • (rotIsom φ₁ • chart k₁ y) := by
    filter_upwards [ht₁, ht₂] with y ⟨hy₁, hψ₁, e₁⟩ ⟨hy₂, hψ₂, e₂⟩
    refine ⟨hy₁, ?_⟩
    rw [hS y ⟨hy₁, hy₂⟩, ← e₂, hT (ψ y) ⟨hψ₂, hψ₁⟩, rotIsom_add, mul_smul, e₁,
      ← hS y ⟨hy₁, hy₂⟩, mul_smul]
  obtain ⟨t, ht, hto, hxt⟩ := _root_.mem_nhds_iff.1 hall
  have hopen : IsOpen ((fun v => rotIsom φ₁ • v) '' (chart k₁ '' t)) :=
    isOpenMap_smul _ _ ((chart k₁).isOpen_image_of_subset_source hto fun y hy => (ht hy).1)
  refine ⟨n, eq_of_eqOn hopen ⟨_, _, ⟨_, hxt, rfl⟩, rfl⟩ ?_⟩
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact (ht hy).2

/-- **An isometry reading `ψ` near `b` develops it with a continuous angle**: near `b`,
`ψ (pt b₁) = (τ, polar(ρ, Θ b₁))` with `devPt τ ρ (Θ b₁) = g • devPt b₁`, `Θ` continuous at
`b`. -/
theorem HolRel.eventually_dev {ψ : OpenPartialHomeomorph (Massive α) (Massive α')}
    {g : Flat.isom 2} {b : ℝ × ℝ × ℝ} (h : HolRel ψ g b) (hb : pt α b ∈ ψ.source) :
    ∃ Θ : ℝ × ℝ × ℝ → ℝ, ContinuousAt Θ b ∧ ∀ᶠ b₁ in 𝓝 b,
      (ψ (pt α b₁)).2 = Cone.polar (Cone.rad (ψ (pt α b₁)).2, (Θ b₁ : AddCircle α')) ∧
      devPt (ψ (pt α b₁)).1 (Cone.rad (ψ (pt α b₁)).2) (Θ b₁) = g • devPt b₁.1 b₁.2.1 b₁.2.2 := by
  obtain ⟨k, φ, k', φ', hφ', hs, ht⟩ := h
  have hz : ψ (pt α b) ∈ (chart k').source := ht.self_of_nhds.2.1
  refine ⟨fun b₁ => chartAngle k' φ' (ψ (pt α b₁)), ?_, ?_⟩
  · exact ((continuousOn_chartAngle k' φ').continuousAt ((chart k').open_source.mem_nhds hz)).comp
      (f := fun b₁ => ψ (pt α b₁)) ((ψ.continuousAt hb).comp continuous_pt.continuousAt)
  · have ht' := (continuous_pt.tendsto b).eventually ht
    filter_upwards [hs, ht'] with b₁ hs1 ht1
    obtain ⟨-, hs2⟩ := hs1
    obtain ⟨-, h2, h3⟩ := ht1
    obtain ⟨hp, hd⟩ := chart_dev k' φ' hφ' h2
    exact ⟨hp, by rw [← hd, h3, hs2]⟩

/-- **One isometry develops `ψ` on a preconnected set of parameters** of positive radius in the
source. -/
theorem exists_holRel (hα' : α' ≠ 2 * π) {ψ : OpenPartialHomeomorph (Massive α) (Massive α')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {B : Set (ℝ × ℝ × ℝ)} (hB : IsPreconnected B)
    (hBs : ∀ b ∈ B, pt α b ∈ ψ.source) (hBr : ∀ b ∈ B, 0 < b.2.1) {b₀ : ℝ × ℝ × ℝ}
    (hb₀ : b₀ ∈ B) : ∃ g : Flat.isom 2, ∀ b ∈ B, HolRel ψ g b := by
  obtain ⟨g, hg⟩ := eventually_holRel hα' hψ (hBr b₀ hb₀) (hBs b₀ hb₀)
  refine ⟨g, fun b hb => ?_⟩
  have key : ∀ g', HolRel ψ g' b₀ → HolRel ψ g' b := by
    refine hB.induction₂' (fun a c => ∀ g', HolRel ψ g' a → HolRel ψ g' c) ?_ ?_ hb₀ hb
    · intro a ha
      obtain ⟨g₀, hg₀⟩ := eventually_holRel hα' hψ (hBr a ha) (hBs a ha)
      have hg₀a := hg₀.self_of_nhds
      filter_upwards [nhdsWithin_le_nhds hg₀] with c hc
      refine ⟨fun g' hg' => ?_, fun g' hg' => ?_⟩
      · obtain ⟨n, rfl⟩ := HolRel.unique hg₀a hg'
        exact hc.mul_left n
      · obtain ⟨n, rfl⟩ := HolRel.unique hc hg'
        exact hg₀a.mul_left n
    · intro a c d _ _ _ h1 h2 g' hg'
      exact h2 g' (h1 g' hg')
  exact key g hg.self_of_nhds

end HolRel

/-! ### The isometries of `E^{1,2}` preserving the time axis -/

/-- **An isometry of `E^{1,2}` sending two points of the time axis into it** is a rotation about
the axis after a translation along it: `g • (t, x) = (t + s, R_φ x)`. The linear part fixes the
future unit vector of the axis (it is orthochronous), so preserves its orthogonal plane, on which
it is an isometry of determinant one: no boost, and the determinant excludes the reflections. -/
theorem isom_of_timeAxis (g : Flat.isom 2) {t₁ t₂ s₁ s₂ : ℝ} (hne : t₁ ≠ t₂)
    (h₁ : g • ((t₁, 0) : Minkowski 2) = (s₁, 0)) (h₂ : g • ((t₂, 0) : Minkowski 2) = (s₂, 0)) :
    ∃ s φ : ℝ, ∀ v : Minkowski 2, g • v = (v.1 + s, planeRot φ v.2) := by
  set A := (g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2).linear with hAdef
  have hA : A ∈ Flat.lorentz 2 := g.2
  have haff : ∀ v, g • v = A v + g • (0 : Minkowski 2) := fun v => by
    have h := Flat.isom_sub (g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2) 0 v
    rw [sub_zero] at h
    rw [Flat.isom_smul_def, Flat.isom_smul_def, ← h]
    abel
  -- the image of the time direction
  have hsub : t₂ - t₁ ≠ 0 := sub_ne_zero.2 hne.symm
  have hd : (t₂ - t₁) • A ((1, 0) : Minkowski 2) = ((s₂ - s₁, 0) : Minkowski 2) := by
    have h := Flat.isom_sub (g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2) (t₁, 0) (t₂, 0)
    rw [← Flat.isom_smul_def, ← Flat.isom_smul_def, h₁, h₂] at h
    have e1 : ((t₂, 0) : Minkowski 2) - (t₁, 0) = (t₂ - t₁) • ((1, 0) : Minkowski 2) := by
      ext <;> simp
    have e2 : ((s₂, 0) : Minkowski 2) - (s₁, 0) = ((s₂ - s₁, 0) : Minkowski 2) := by
      ext <;> simp
    rw [e1, map_smul, e2] at h
    exact h.symm
  have hfst : (A ((1, 0) : Minkowski 2)).1 = (s₂ - s₁) / (t₂ - t₁) := by
    have := congrArg Prod.fst hd
    simp only [Prod.smul_fst, smul_eq_mul] at this
    field_simp
    linarith
  have hsnd : (A ((1, 0) : Minkowski 2)).2 = 0 := by
    have := congrArg Prod.snd hd
    simp only [Prod.smul_snd] at this
    exact (smul_eq_zero.1 this).resolve_left hsub
  -- it is the future unit vector
  have hq := Flat.lorentz.minkQ_apply hA ((1, 0) : Minkowski 2)
  have hfc : Flat.IsFutureCausal ((1, 0) : Minkowski 2) := ⟨zero_le_one, by simp [Flat.minkQ]⟩
  have hfc' := Flat.lorentz.isFutureCausal_apply hA hfc
  have he : A ((1, 0) : Minkowski 2) = ((1, 0) : Minkowski 2) := by
    simp only [Flat.minkQ, hsnd, norm_zero] at hq
    have h1 : 0 ≤ (A ((1, 0) : Minkowski 2)).1 := hfc'.1
    have h2 : (A ((1, 0) : Minkowski 2)).1 = 1 := by
      norm_num at hq
      rcases hq with hq | hq
      · exact hq
      · linarith
    exact Prod.ext h2 hsnd
  -- the spatial plane is preserved, isometrically
  have hsp : ∀ x : EuclideanSpace ℝ (Fin 2),
      (A ((0, x) : Minkowski 2)).1 = 0 ∧ ‖(A ((0, x) : Minkowski 2)).2‖ = ‖x‖ := by
    intro x
    have q1 := Flat.lorentz.minkQ_apply hA ((0, x) : Minkowski 2)
    have q2 := Flat.lorentz.minkQ_apply hA ((1, x) : Minkowski 2)
    have e : ((1, x) : Minkowski 2) = ((1, 0) : Minkowski 2) + ((0, x) : Minkowski 2) := by
      ext <;> simp
    rw [e, map_add, he] at q2
    simp only [Flat.minkQ, Prod.fst_add, Prod.snd_add, zero_add] at q1 q2
    have ha : (A ((0, x) : Minkowski 2)).1 = 0 := by nlinarith
    refine ⟨ha, ?_⟩
    rw [ha] at q1
    have h3 : ‖(A ((0, x) : Minkowski 2)).2‖ ^ 2 = ‖x‖ ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
  -- the spatial part `L`
  set L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 2)) ∘ₗ (A : Minkowski 2 →ₗ[ℝ] Minkowski 2) ∘ₗ
      LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 2)) with hLdef
  have hL : ∀ x, L x = (A ((0, x) : Minkowski 2)).2 := fun x => rfl
  have hAv : ∀ v : Minkowski 2, A v = (v.1, L v.2) := by
    intro v
    have e : v = v.1 • ((1, 0) : Minkowski 2) + ((0, v.2) : Minkowski 2) := by ext <;> simp
    have hw : A ((0, v.2) : Minkowski 2) = ((0, L v.2) : Minkowski 2) :=
      Prod.ext (hsp v.2).1 (hL v.2).symm
    conv_lhs => rw [e]
    rw [map_add, map_smul, he, hw]
    ext <;> simp
  -- `det L = 1`
  have hAL : (A : Minkowski 2 →ₗ[ℝ] Minkowski 2) = LinearMap.prodMap LinearMap.id L := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.prodMap_apply, LinearMap.id_apply]
    exact hAv v
  have hdetL : LinearMap.det L = 1 := by
    have := Flat.lorentz.det_eq_one hA
    rw [hAL, LinearMap.det_prodMap, LinearMap.det_id, one_mul] at this
    exact this
  -- `L` is a rotation: through `ℂ`
  set repr := Complex.orthonormalBasisOneI.repr with hrepr
  let f : ℂ →ₗ[ℝ] ℂ := (repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℂ) ∘ₗ L ∘ₗ
    (repr.toLinearEquiv : ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
  have hfn : ∀ z, ‖f z‖ = ‖z‖ := fun z => by
    show ‖repr.symm (L (repr z))‖ = ‖z‖
    rw [LinearIsometryEquiv.norm_map, hL, (hsp _).2, LinearIsometryEquiv.norm_map]
  let fi : ℂ →ₗᵢ[ℝ] ℂ := ⟨f, hfn⟩
  let fe : ℂ ≃ₗᵢ[ℝ] ℂ := fi.toLinearIsometryEquiv rfl
  have hfe : ∀ z, fe z = repr.symm (L (repr z)) := fun z => rfl
  have hdetf : LinearMap.det (fe.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = 1 := by
    have e : (fe.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
        (repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℂ) ∘ₗ L ∘ₗ
          (repr.symm.toLinearEquiv.symm : ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) :=
      LinearMap.ext fun z => rfl
    rw [e, LinearMap.det_conj, hdetL]
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex fe
  · -- a rotation
    refine ⟨s₁ - t₁, Complex.arg a, fun v => ?_⟩
    have h0 : g • (0 : Minkowski 2) = ((s₁ - t₁, 0) : Minkowski 2) := by
      have h := haff ((t₁, 0) : Minkowski 2)
      rw [h₁, hAv, map_zero] at h
      rw [show ((s₁ - t₁, 0) : Minkowski 2) = ((s₁, 0) : Minkowski 2) - ((t₁, 0) : Minkowski 2) by
        ext <;> simp, h]
      abel
    have hLv : L v.2 = planeRot (Complex.arg a) v.2 := by
      rw [planeRot_apply']
      have h1 : repr.symm (L v.2) = a * repr.symm v.2 := by
        have := hfe (repr.symm v.2)
        rw [LinearIsometryEquiv.apply_symm_apply, ha, rotation_apply] at this
        exact this.symm
      have h2 : (a : ℂ) = Complex.exp (Complex.arg a * I) := by
        conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (a : ℂ)]
        rw [Circle.norm_coe, Complex.ofReal_one, one_mul]
      rw [← h2, ← h1, LinearIsometryEquiv.apply_symm_apply]
    rw [haff, hAv, h0, hLv]
    ext <;> simp
  · -- a reflection: excluded by the determinant
    exfalso
    rw [ha] at hdetf
    have e : ((conjLIE.trans (rotation a)).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
        ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ
          (conjAe.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) :=
      LinearMap.ext fun z => rfl
    rw [e, LinearMap.det_comp, det_rotation, Complex.det_conjAe] at hdetf
    norm_num at hdetf

theorem smul_devPt_of_isom {g : Flat.isom 2} {s φ : ℝ}
    (hg : ∀ v : Minkowski 2, g • v = (v.1 + s, planeRot φ v.2)) (t ρ θ : ℝ) :
    g • devPt t ρ θ = devPt (t + s) ρ (θ + φ) := by
  rw [hg]
  unfold devPt
  simp only
  rw [planeRot_repr]
  congr 2
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### The limit at the singular line, and the formula on the slit box -/

section Slit

variable {α α' : ℝ} [Fact (0 < α)] [Fact (0 < α')]

/-- **The developing isometry preserves the time axis**: if `g` develops `ψ` along the segment
`r ↦ (τ, r, 0)`, `0 < r < ε`, and `ψ` sends `(τ, apex)` to the line, then `g` sends `(τ, 0)` to
the time axis. -/
theorem smul_timeAxis {ψ : OpenPartialHomeomorph (Massive α) (Massive α')} {g : Flat.isom 2}
    {τ ε : ℝ} (hε : 0 < ε) (hq : ((τ, Cone.apex) : Massive α) ∈ ψ.source)
    (hsing : (ψ (τ, Cone.apex)).2 = Cone.apex)
    (hrel : ∀ r ∈ Ioo (0 : ℝ) ε, HolRel ψ g (τ, r, 0))
    (hsrc : ∀ r ∈ Ioo (0 : ℝ) ε, pt α (τ, r, 0) ∈ ψ.source) :
    g • ((τ, 0) : Minkowski 2) = ((ψ (τ, Cone.apex)).1, 0) := by
  have hval : ∀ r ∈ Ioo (0 : ℝ) ε, (ψ (pt α (τ, r, 0))).1 = (g • devPt τ r 0).1 ∧
      Cone.rad (ψ (pt α (τ, r, 0))).2 = ‖(g • devPt τ r 0).2‖ := by
    intro r hr
    obtain ⟨Θ, -, hΘ⟩ := (hrel r hr).eventually_dev (hsrc r hr)
    obtain ⟨-, hd⟩ := hΘ.self_of_nhds
    simp only at hd
    rw [← hd, norm_devPt_snd, abs_of_nonneg (Cone.rad_nonneg _)]
    exact ⟨rfl, rfl⟩
  have hseg : Continuous fun r : ℝ => ((τ, r, (0 : ℝ)) : ℝ × ℝ × ℝ) := by fun_prop
  have hFc : Continuous fun r : ℝ => g • devPt τ r 0 :=
    (continuous_const_smul g).comp (continuous_devPt.comp hseg)
  have hpt0 : pt α (τ, 0, 0) = (τ, Cone.apex) := pt_zero τ 0
  have hGc : ContinuousAt (fun r : ℝ => ψ (pt α (τ, r, 0))) 0 :=
    (ψ.continuousAt (hpt0 ▸ hq)).comp (f := fun r : ℝ => pt α (τ, r, 0))
      (continuous_pt.comp hseg).continuousAt
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 ε := Ioo_mem_nhdsGT hε
  have hrad : Continuous fun y : Cone α' => Cone.rad y := continuous_const.dist continuous_id
  have e1 := eq_of_eventuallyEq_of_continuousAt hl
    (f := fun r => (ψ (pt α (τ, r, 0))).1) (g := fun r => (g • devPt τ r 0).1)
    (continuous_fst.continuousAt.comp hGc) hFc.fst.continuousAt
    (hev.mono fun r hr => (hval r hr).1)
  have e2 := eq_of_eventuallyEq_of_continuousAt hl
    (f := fun r => Cone.rad (ψ (pt α (τ, r, 0))).2) (g := fun r => ‖(g • devPt τ r 0).2‖)
    (hrad.continuousAt.comp (continuous_snd.continuousAt.comp hGc))
    (continuous_norm.comp hFc.snd).continuousAt (hev.mono fun r hr => (hval r hr).2)
  simp only [hpt0, hsing, devPt_zero] at e1 e2
  have hr0 : Cone.rad (Cone.apex : Cone α') = 0 := Cone.rad_eq_zero.2 rfl
  rw [hr0] at e2
  exact Prod.ext e1.symm (norm_eq_zero.1 e2.symm)

/-- An a.e. isomorphism chart sends the singular line of `E_κ`, `κ ≠ 2π`, into the singular line
of `E_κ′`, and then `κ′ ≠ 2π` (`Sing(E_{2π}) = ∅`). -/
theorem mem_singLine_of_isAEChart (hα : α ≠ 2 * π)
    {ψ : OpenPartialHomeomorph (Massive α) (Massive α')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {q : Massive α} (hq : q ∈ ψ.source)
    (hqs : q ∈ singLine α) : α' ≠ 2 * π ∧ ψ q ∈ singLine α' := by
  have hqS : q ∉ Reg (Flat.isom 2) (Minkowski 2) (Massive α) := by
    rw [reg_eq hα]
    exact fun h => h hqs
  have hψq : ψ q ∉ Reg (Flat.isom 2) (Minkowski 2) (Massive α') :=
    fun h => hqS ((hψ.mem_reg_iff hq).2 h)
  have hα' : α' ≠ 2 * π := by
    intro h
    subst h
    exact hψq (by rw [reg_eq_univ_two_pi]; exact mem_univ _)
  refine ⟨hα', ?_⟩
  rw [reg_eq hα'] at hψq
  exact not_not.1 hψq

/-- The slit box of parameters about the time `t₀`: `|t − t₀| < ε`, `0 < r < ε`, `|θ| < κ/2`. -/
def slitBox (α t₀ ε : ℝ) : Set (ℝ × ℝ × ℝ) :=
  ball t₀ ε ×ˢ (Ioo 0 ε ×ˢ Ioo (-(α / 2)) (α / 2))

/-- **The formula on the slit box**: near a point `p` of the line, `ψ` is
`(t, polar(r, θ)) ↦ (t + s, polar(r, θ + c))` for `|θ| < κ/2`. -/
theorem exists_slitBox (hα : α ≠ 2 * π) {ψ : OpenPartialHomeomorph (Massive α) (Massive α')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {p : Massive α} (hp : p ∈ ψ.source)
    (hps : p ∈ singLine α) :
    ∃ ε > 0, ball p ε ⊆ ψ.source ∧ ∃ (s : ℝ) (c : AddCircle α'), ∀ b ∈ slitBox α p.1 ε,
      ψ (pt α b) = (b.1 + s, Cone.polar (b.2.1, (b.2.2 : AddCircle α') + c)) := by
  obtain ⟨hα', -⟩ := mem_singLine_of_isAEChart hα hψ hp hps
  have hp2 : p.2 = Cone.apex := hps
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ψ.open_source p hp
  refine ⟨ε, hε, hball, ?_⟩
  have hα0 : 0 < α := Fact.out
  have hBs : ∀ b ∈ slitBox α p.1 ε, pt α b ∈ ψ.source := fun b hb =>
    hball (pt_mem_ball hp2 hb.1 hb.2.1.1.le hb.2.1.2 b.2.2)
  have hBr : ∀ b ∈ slitBox α p.1 ε, 0 < b.2.1 := fun b hb => hb.2.1.1
  have hBc : IsPreconnected (slitBox α p.1 ε) :=
    ((convex_ball _ _).prod ((convex_Ioo _ _).prod (convex_Ioo _ _))).isPreconnected
  have hb₀ : ((p.1, ε / 2, 0) : ℝ × ℝ × ℝ) ∈ slitBox α p.1 ε :=
    ⟨mem_ball_self hε, ⟨by positivity, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨g, hg⟩ := exists_holRel hα' hψ hBc hBs hBr hb₀
  -- `g` preserves the time axis
  have haxis : ∀ τ ∈ ball p.1 ε, g • ((τ, 0) : Minkowski 2) = ((ψ (τ, Cone.apex)).1, 0) := by
    intro τ hτ
    have hq : ((τ, Cone.apex) : Massive α) ∈ ψ.source := by
      have := pt_mem_ball (α := α) hp2 hτ le_rfl hε 0
      rw [pt_zero] at this
      exact hball this
    have hqs := (mem_singLine_of_isAEChart hα hψ hq rfl).2
    exact smul_timeAxis hε hq hqs (fun r hr => hg _ ⟨hτ, hr, ⟨by linarith, by linarith⟩⟩)
      (fun r hr => hBs _ ⟨hτ, hr, ⟨by linarith, by linarith⟩⟩)
  have hτ₂ : p.1 + ε / 2 ∈ ball p.1 ε := by
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith
  obtain ⟨s, φ, hgf⟩ := isom_of_timeAxis g (show p.1 ≠ p.1 + ε / 2 by intro h; linarith)
    (haxis _ (mem_ball_self hε)) (haxis _ hτ₂)
  have hgd := smul_devPt_of_isom hgf
  refine ⟨s, ?_⟩
  -- the angle read in the target charts is continuous: one rotation `c` on the box
  set Q : AddCircle α' → ℝ × ℝ × ℝ → Prop := fun c b =>
    ψ (pt α b) = (b.1 + s, Cone.polar (b.2.1, (b.2.2 : AddCircle α') + c)) with hQ
  have hloc : ∀ b ∈ slitBox α p.1 ε, ∃ c, ∀ᶠ b₁ in 𝓝 b, Q c b₁ := by
    intro b hb
    obtain ⟨Θ, hΘc, hΘ⟩ := (hg b hb).eventually_dev (hBs b hb)
    have hr0 : ∀ᶠ b₁ in 𝓝 b, 0 < b₁.2.1 :=
      (continuous_snd.fst.tendsto b).eventually (lt_mem_nhds (hBr b hb))
    have hint : ∀ᶠ b₁ in 𝓝 b, ∃ m : ℤ, Θ b₁ - b₁.2.2 = φ + 2 * π * m ∧
        (ψ (pt α b₁)).1 = b₁.1 + s ∧ Cone.rad (ψ (pt α b₁)).2 = b₁.2.1 := by
      filter_upwards [hΘ, hr0] with b₁ hb₁ hr1
      obtain ⟨-, hd1⟩ := hb₁
      rw [hgd] at hd1
      obtain ⟨ht, hρ, hexp⟩ := devPt_eq_devPt (Cone.rad_nonneg _) hr1 hd1
      obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
      have him := congrArg Complex.im hm
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.add_im, Complex.intCast_re, Complex.intCast_im, mul_zero,
        zero_mul, add_zero, mul_one, zero_add, Complex.mul_re, sub_zero] at him
      refine ⟨m, ?_, ht, hρ⟩
      norm_num at him
      linarith
    obtain ⟨m₀, hm₀, -, -⟩ := hint.self_of_nhds
    have hcont : ∀ᶠ b₁ in 𝓝 b, dist (Θ b₁ - b₁.2.2) (Θ b - b.2.2) < 2 * π := by
      have hc : ContinuousAt (fun b₁ : ℝ × ℝ × ℝ => Θ b₁ - b₁.2.2) b :=
        hΘc.sub continuous_snd.snd.continuousAt
      exact (Metric.continuousAt_iff'.1 hc) (2 * π) (by positivity)
    refine ⟨((φ + 2 * π * m₀ : ℝ) : AddCircle α'), ?_⟩
    filter_upwards [hint, hcont, hΘ] with b₁ hb₁ hc hΘ₁
    obtain ⟨m, hm, ht, hρ⟩ := hb₁
    obtain ⟨hp1, -⟩ := hΘ₁
    have hmm : m = m₀ := by
      rw [hm, hm₀, Real.dist_eq, show φ + 2 * π * m - (φ + 2 * π * m₀) = 2 * π * (m - m₀) by
        ring, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hc
      have h1 : |(m : ℝ) - m₀| < 1 := by
        have := Real.pi_pos
        nlinarith [abs_nonneg ((m : ℝ) - m₀)]
      have h2 : |m - m₀| < 1 := by exact_mod_cast h1
      have := abs_lt.1 h2
      omega
    show ψ (pt α b₁) = _
    refine Prod.ext ht ?_
    rw [hp1, hρ, show Θ b₁ = b₁.2.2 + (φ + 2 * π * m₀) by rw [← hmm]; linarith,
      AddCircle.coe_add]
  have huniq : ∀ b ∈ slitBox α p.1 ε, ∀ c c', Q c b → Q c' b → c = c' := by
    intro b hb c c' h h'
    have h2 := congrArg Prod.snd (h.symm.trans h')
    exact add_left_cancel (polar_inj (hBr b hb) h2)
  obtain ⟨c, hc⟩ := exists_forall_of_isPreconnected hBc hloc huniq hb₀
  exact ⟨c, hc⟩

/-- **Type invariance** (BTZ_1 l.462): an a.e. isomorphism chart `E_κ ⇀ E_κ′`, `κ ≠ 2π`, whose
source meets the singular line has `κ′ = κ`. Continuity across the slit gives `κ ∈ κ′ℤ`,
injectivity `κ′ ≥ κ`. -/
theorem eq_of_isAEChart (hα : α ≠ 2 * π) {ψ : OpenPartialHomeomorph (Massive α) (Massive α')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {p : Massive α} (hp : p ∈ ψ.source)
    (hps : p ∈ singLine α) : α' = α := by
  obtain ⟨ε, hε, hball, s, c, hform⟩ := exists_slitBox hα hψ hp hps
  have hp2 : p.2 = Cone.apex := hps
  have hα0 : 0 < α := Fact.out
  have hα'0 : 0 < α' := Fact.out
  set r := ε / 2 with hrdef
  have hr0 : 0 < r := by positivity
  have hrε : r < ε := by linarith
  have hmem : ∀ θ : ℝ, pt α (p.1, r, θ) ∈ ψ.source := fun θ =>
    hball (pt_mem_ball hp2 (mem_ball_self hε) hr0.le hrε θ)
  have hval : ∀ θ ∈ Ioo (-(α / 2)) (α / 2),
      ψ (pt α (p.1, r, θ)) = (p.1 + s, Cone.polar (r, (θ : AddCircle α') + c)) := fun θ hθ =>
    hform _ ⟨mem_ball_self hε, ⟨hr0, hrε⟩, hθ⟩
  -- `κ ∈ κ′ℤ`: continuity across the slit
  have hle : α' ≤ α := by
    have hw : Continuous fun θ : ℝ => pt α (p.1, r, θ) := continuous_pt.comp (by fun_prop)
    have hco : ((α / 2 : ℝ) : AddCircle α) = ((-(α / 2) : ℝ) : AddCircle α) := by
      rw [← sub_eq_zero, ← AddCircle.coe_sub, show α / 2 - -(α / 2) = α by ring,
        AddCircle.coe_period]
    have hslit : pt α (p.1, r, α / 2) = pt α (p.1, r, -(α / 2)) := by
      unfold pt
      simp only
      rw [hco]
    have hG : Continuous fun θ : ℝ => ((p.1 + s, Cone.polar (r, (θ : AddCircle α') + c)) :
        Massive α') :=
      continuous_const.prodMk (Cone.continuous_polar.comp (continuous_const.prodMk
        ((AddCircle.continuous_mk' α').add continuous_const)))
    have hc1 : ContinuousAt (fun θ => ψ (pt α (p.1, r, θ))) (α / 2) :=
      (ψ.continuousAt (hmem _)).comp (f := fun θ : ℝ => pt α (p.1, r, θ)) hw.continuousAt
    have hc2 : ContinuousAt (fun θ => ψ (pt α (p.1, r, θ))) (-(α / 2)) :=
      (ψ.continuousAt (hmem _)).comp (f := fun θ : ℝ => pt α (p.1, r, θ)) hw.continuousAt
    have hev1 : ∀ᶠ θ in 𝓝[<] (α / 2), θ ∈ Ioo (-(α / 2)) (α / 2) :=
      Ioo_mem_nhdsLT (by linarith)
    have hev2 : ∀ᶠ θ in 𝓝[>] (-(α / 2)), θ ∈ Ioo (-(α / 2)) (α / 2) :=
      Ioo_mem_nhdsGT (by linarith)
    have hE1 := eq_of_eventuallyEq_of_continuousAt (l := 𝓝[<] (α / 2)) nhdsWithin_le_nhds hc1
      hG.continuousAt (hev1.mono fun θ hθ => hval θ hθ)
    have hE2 := eq_of_eventuallyEq_of_continuousAt (l := 𝓝[>] (-(α / 2))) nhdsWithin_le_nhds hc2
      hG.continuousAt (hev2.mono fun θ hθ => hval θ hθ)
    rw [hslit] at hE1
    have h := congrArg Prod.snd (hE1.symm.trans hE2)
    simp only at h
    have h' := add_right_cancel (polar_inj hr0 h)
    have h'' : ((α : ℝ) : AddCircle α') = 0 := by
      rw [show α = α / 2 - -(α / 2) by ring, AddCircle.coe_sub, h', sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff α').1 h''
    rw [zsmul_eq_mul] at hn
    have hn0 : (0 : ℝ) < n := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have hn1 : (1 : ℝ) ≤ n := by
      have : (0 : ℤ) < n := by exact_mod_cast hn0
      exact_mod_cast this
    nlinarith
  -- `κ′ ≥ κ`: injectivity
  have hge : α ≤ α' := by
    by_contra hlt
    push Not at hlt
    have hθ₁ : -(α' / 2) ∈ Ioo (-(α / 2)) (α / 2) := ⟨by linarith, by linarith⟩
    have hθ₂ : α' / 2 ∈ Ioo (-(α / 2)) (α / 2) := ⟨by linarith, by linarith⟩
    have heq : ψ (pt α (p.1, r, -(α' / 2))) = ψ (pt α (p.1, r, α' / 2)) := by
      have hco : ((α' / 2 : ℝ) : AddCircle α') = ((-(α' / 2) : ℝ) : AddCircle α') := by
        rw [← sub_eq_zero, ← AddCircle.coe_sub, show α' / 2 - -(α' / 2) = α' by ring,
          AddCircle.coe_period]
      rw [hval _ hθ₁, hval _ hθ₂, hco]
    have hinj := ψ.injOn (hmem _) (hmem _) heq
    have h := polar_inj hr0 (congrArg Prod.snd hinj)
    have h'' : ((α' : ℝ) : AddCircle α) = 0 := by
      rw [show α' = α' / 2 - -(α' / 2) by ring, AddCircle.coe_sub, h, sub_self]
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff α).1 h''
    rw [zsmul_eq_mul] at hm
    have hm0 : (0 : ℝ) < m := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have hm1 : (1 : ℝ) ≤ m := by
      have : (0 : ℤ) < m := by exact_mod_cast hm0
      exact_mod_cast this
    nlinarith
  linarith

/-- **BTZ_1's `prop:isom` for `α, β > 0`, local form.** An a.e. isomorphism chart
`ψ : E_κ ⇀ E_κ′`, `κ ≠ 2π`, whose source contains a point `p` of the singular line has
`κ′ = κ`, and on a ball about `p` it is `(t, polar(r, θ)) ↦ (t + s, polar(r, θ + c))`. -/
theorem prop_isom_local (hα : α ≠ 2 * π) {ψ : OpenPartialHomeomorph (Massive α) (Massive α')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {p : Massive α} (hp : p ∈ ψ.source)
    (hps : p ∈ singLine α) :
    α' = α ∧ ∃ ε > 0, ball p ε ⊆ ψ.source ∧ ∃ (s : ℝ) (c : AddCircle α'),
      ∀ x ∈ ball p ε, ∀ r θ : ℝ, 0 ≤ r → x.2 = Cone.polar (r, (θ : AddCircle α)) →
        ψ x = (x.1 + s, Cone.polar (r, (θ : AddCircle α') + c)) := by
  obtain ⟨ε, hε, hball, s, c, hform⟩ := exists_slitBox hα hψ hp hps
  have heq := eq_of_isAEChart hα hψ hp hps
  refine ⟨heq, ε, hε, hball, s, c, fun x hx r θ hr hxr => ?_⟩
  subst heq
  have hp2 : p.2 = Cone.apex := hps
  have hα0 : 0 < α' := Fact.out
  -- the representative of `θ` in `[-κ/2, κ/2)`
  obtain ⟨θ', hθ'mem, hθ'coe⟩ : ∃ θ' : ℝ, θ' ∈ Ico (-(α' / 2)) (-(α' / 2) + α') ∧
      (θ' : AddCircle α') = θ :=
    ⟨_, (AddCircle.equivIco α' (-(α' / 2)) (θ : AddCircle α')).2, AddCircle.coe_equivIco⟩
  -- the radius
  have hx' := hx
  rw [mem_ball, Prod.dist_eq, hp2] at hx'
  have hxt : x.1 ∈ ball p.1 ε := lt_of_le_of_lt (le_max_left _ _) hx'
  have hrε : r < ε := by
    have h := lt_of_le_of_lt (le_max_right _ _) hx'
    rw [dist_comm] at h
    change Cone.rad x.2 < ε at h
    rwa [hxr, rad_polar hr] at h
  -- a path into the slit box, ending at `x`
  set δ := min (ε - r) (α' / 2 - θ') with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith [hθ'mem.2])
  have hpath : ∀ u ∈ Ioo (0 : ℝ) δ, ((x.1, r + u, θ' + u) : ℝ × ℝ × ℝ) ∈ slitBox α' p.1 ε := by
    intro u hu
    have h1 := min_le_left (ε - r) (α' / 2 - θ')
    have h2 := min_le_right (ε - r) (α' / 2 - θ')
    exact ⟨hxt, ⟨by linarith [hu.1], by linarith [hu.2]⟩,
      ⟨by linarith [hθ'mem.1, hu.1], by linarith [hu.2]⟩⟩
  have hx0 : pt α' (x.1, r + 0, θ' + 0) = x := by
    unfold pt
    simp only [add_zero]
    rw [hθ'coe, ← hxr]
  have hpc : Continuous fun u : ℝ => pt α' (x.1, r + u, θ' + u) :=
    continuous_pt.comp (by fun_prop)
  have hc1 : ContinuousAt (fun u : ℝ => ψ (pt α' (x.1, r + u, θ' + u))) 0 :=
    (ψ.continuousAt (by rw [hx0]; exact hball hx)).comp
      (f := fun u : ℝ => pt α' (x.1, r + u, θ' + u)) hpc.continuousAt
  have hG : Continuous fun u : ℝ =>
      ((x.1 + s, Cone.polar (r + u, ((θ' + u : ℝ) : AddCircle α') + c)) : Massive α') :=
    continuous_const.prodMk (Cone.continuous_polar.comp ((continuous_const.add continuous_id).prodMk
      ((AddCircle.continuous_mk' α').comp (continuous_const.add continuous_id) |>.add
        continuous_const)))
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ0
  have hE := eq_of_eventuallyEq_of_continuousAt nhdsWithin_le_nhds hc1 hG.continuousAt
    (hev.mono fun u hu => hform _ (hpath u hu))
  rw [hx0] at hE
  rw [hE]
  simp only [add_zero]
  rw [hθ'coe]

end Slit

/-! ### `Isom(E_κ)` and (b′) -/

section BPrime

variable {α : ℝ} [Fact (0 < α)]

/-- **The rotation-translation** `(t, x) ↦ (t + s, R_c x)` of `E_κ`, an element of BTZ_1's
`Isom(E_κ)` (l.373). -/
noncomputable def rotShift (s : ℝ) (c : AddCircle α) : Massive α ≃ₜ Massive α :=
  shiftIso s (ConeRot.rotIso c)

omit [Fact (0 < α)] in
theorem rotShift_apply (s : ℝ) (c : AddCircle α) (x : Massive α) :
    rotShift s c x = (x.1 + s, ConeRot.rot c x.2) := rfl

/-- A rotation-translation is a chart isomorphism of `E_κ`. -/
theorem chartIso_rotShift (s : ℝ) (c : AddCircle α) :
    ChartIso (massive α) (massive α) (rotShift s c).toOpenPartialHomeomorph :=
  chartIso_shiftIso s (ConeRot.rotIso c)

/-- **BTZ_1's `prop:isom` for `α = β > 0`, local form, same model**: near a point of the line of
its source, an a.e. isomorphism chart `ψ : E_κ ⇀ E_κ`, `κ ≠ 2π`, is a rotation-translation. -/
theorem exists_eqOn_rotShift (hα : α ≠ 2 * π) {ψ : OpenPartialHomeomorph (Massive α) (Massive α)}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {p : Massive α} (hp : p ∈ ψ.source)
    (hps : p ∈ singLine α) :
    ∃ (s : ℝ) (c : AddCircle α) (O : Opens (Massive α)), p ∈ O ∧ (O : Set (Massive α)) ⊆ ψ.source ∧
      ∀ x ∈ O, ψ x = rotShift s c x := by
  obtain ⟨-, ε, hε, hball, s, c, hform⟩ := prop_isom_local hα hψ hp hps
  refine ⟨s, c, ⟨ball p ε, isOpen_ball⟩, mem_ball_self hε, hball, fun x hx => ?_⟩
  obtain ⟨r, θ, hr, hxr⟩ := exists_polar x.2
  rw [hform x hx r θ hr hxr, rotShift_apply, hxr, ConeRot.rot_polar]

/-- (b′) at `E_κ → E_κ`, `κ ≠ 2π`: every a.e. isomorphism chart is a chart isomorphism. -/
theorem chartIso_of_isAEChart_self (hα : α ≠ 2 * π)
    {ψ : OpenPartialHomeomorph (Massive α) (Massive α)}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) : ChartIso (massive α) (massive α) ψ := by
  have hT := (massive α).chartTransport_chartIso ψ
  have hmin : (massive α).AbsolutelyMinimalOn (chartSource ψ) :=
    massive_causallyArcConnected.absolutelyMinimalOn_all _
  have hTmin : ((massive α).chartTransport ψ).AbsolutelyMinimalOn (chartSource ψ) :=
    hT.absolutelyMinimalOn le_rfl (massive_causallyArcConnected.absolutelyMinimalOn_all _)
  have hloc : ∀ x ∈ chartSource ψ, ∃ O : Opens (Massive α), x ∈ O ∧
      AgreeOn (massive α) ((massive α).chartTransport ψ) O := by
    intro x hx
    by_cases hxs : x ∈ singLine α
    · obtain ⟨s, c, O, hxO, hOs, heq⟩ := exists_eqOn_rotShift hα hψ hx hxs
      exact ⟨O, hxO, (chartIso_refl (massive α)).agreeOn_of_localIso hT (chartIso_rotShift s c)
        (fun z hz => ⟨mem_univ z, hOs hz⟩) (fun z hz => ⟨mem_univ _, (heq z hz).symm⟩)⟩
    · obtain ⟨k, hk⟩ := exists_mem_chart_source hxs
      have hc := sectorAtlas_subset_aeAtlas (chart_mem_sectorAtlas k)
      exact (chartIso_of_mem_aeAtlas _ hc).agreeOn_of_isAEChart Flat.isom_strongMorphism
        chartIso_of_mem_aeAtlas hc hψ hT hk hx
  have hloc' : ∀ x ∈ chartSource ψ, ∃ O : Opens (Massive α), x ∈ O ∧
      AgreeOn ((massive α).chartTransport ψ) (massive α) O := fun x hx => by
    obtain ⟨O, hxO, hO⟩ := hloc x hx
    exact ⟨O, hxO, hO.symm⟩
  refine hT.congr fun V hV x y => ?_
  have h1 := imp_of_agree_locally hmin hloc hV (x := x) (y := y)
  have h2 := imp_of_agree_locally hTmin hloc' hV (x := x) (y := y)
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

/-! ### Conversely, the rotation-translations are a.e. isomorphism charts -/

/-- The index of the sector chart rotated by `c`. -/
def rotIndex (c : AddCircle α) (k : Index α) : Index α := ⟨⟨k.1.r, k.1.θ + c, k.1.r_nonneg⟩, k.2⟩

omit [Fact (0 < α)] in
theorem rot_fromPlane (c θ : AddCircle α) (z : ℂ) :
    ConeRot.rot c (fromPlane θ z) = fromPlane (θ + c) z := by
  unfold fromPlane
  rw [ConeRot.rot_mk]
  congr 1
  ext
  · rfl
  · simp only [ConeRot.rotPt]
    abel

/-- **A rotation-translation maps a sector chart onto the rotated one, translating time.** -/
theorem chart_rotShift (s : ℝ) (c : AddCircle α) (k : Index α) {y : Massive α}
    (hy : y ∈ (chart k).source) :
    rotShift s c y ∈ (chart (rotIndex c k)).source ∧
      chart (rotIndex c k) (rotShift s c y) = ((y.1 + s, (chart k y).2) : Minkowski 2) := by
  have hy2 : y.2 ∈ (planeChart k).target := by
    rw [chart_source] at hy
    rw [planeChart_target]
    exact hy.2
  obtain ⟨z, hz⟩ : ∃ z, (planeChart k).symm y.2 = z := ⟨_, rfl⟩
  have hzs : z ∈ (planeChart k).source := hz ▸ (planeChart k).map_target hy2
  have hyz : y.2 = fromPlane k.1.θ z := by
    rw [← planeChart_apply, ← hz, (planeChart k).right_inv hy2]
  have hzs' : z ∈ (planeChart (rotIndex c k)).source := hzs
  have hrot : ConeRot.rot c y.2 = planeChart (rotIndex c k) z := by
    rw [planeChart_apply, hyz, rot_fromPlane]
    rfl
  refine ⟨?_, ?_⟩
  · rw [chart_source]
    refine ⟨trivial, ?_⟩
    show ConeRot.rot c y.2 ∈ coneDisc (rotIndex c k).1
    rw [hrot, ← planeChart_target]
    exact (planeChart _).map_source hzs'
  · rw [chart_apply, chart_apply, rotShift_apply]
    show ((y.1 + s, coneChart (rotIndex c k) (ConeRot.rot c y.2)) : Minkowski 2) =
      (y.1 + s, coneChart k y.2)
    rw [coneChart_apply, coneChart_apply, hrot, (planeChart _).left_inv hzs', hz]

/-- A map equal to a rotation-translation induces a `(G,X)`-morphism on the regular part of every
open set: in sector charts it is a translation along the time axis. -/
theorem isRegularOn_rotShift (hα : α ≠ 2 * π) {f : Massive α → Massive α} {s : ℝ}
    {c : AddCircle α} (hf : ∀ y, f y = rotShift s c y) {S : Set (Massive α)} (hS : IsOpen S) :
    IsRegularOn (Flat.isom 2) (aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α))
      (aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α)) f
      (S ∩ Reg (Flat.isom 2) (Minkowski 2) (Massive α)) := by
  have hA := (isMaximalAEAtlas_aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α)).1.1
  have hcont : Continuous f := by
    rw [show f = rotShift s c from funext hf]
    exact (rotShift s c).continuous
  refine IsRegularOn.of_exists hA hA (hS.inter (isOpen_reg _ _ _)) (fun x hx => hx.2) ?_
    hcont.continuousOn ?_
  · intro x hx
    have hx' := hx.2
    rw [reg_eq hα] at hx'
    show f x ∈ Reg (Flat.isom 2) (Minkowski 2) (Massive α)
    rw [reg_eq hα]
    obtain ⟨k, hk⟩ := exists_mem_chart_source hx'
    rw [hf]
    exact chart_source_subset_regPart _ (chart_rotShift s c k hk).1
  · intro x hx
    have hx' := hx.2
    rw [reg_eq hα] at hx'
    obtain ⟨k, hk⟩ := exists_mem_chart_source hx'
    refine ⟨chart k, sectorAtlas_subset_aeAtlas (chart_mem_sectorAtlas k), chart (rotIndex c k),
      sectorAtlas_subset_aeAtlas (chart_mem_sectorAtlas _), hk,
      by rw [hf]; exact (chart_rotShift s c k hk).1,
      ⟨AffineEquiv.constVAdd ℝ (Minkowski 2) ((s, 0) : Minkowski 2), Flat.constVAdd_mem_isom _⟩,
      ?_⟩
    filter_upwards [(chart k).open_source.mem_nhds hk] with y hy
    rw [hf, (chart_rotShift s c k hy).2]
    show _ = ((s, 0) : Minkowski 2) +ᵥ chart k y
    rw [vadd_eq_add, chart_apply]
    exact Prod.ext (add_comm _ _) (zero_add _).symm

/-- **The rotation-translations of `E_κ`, `κ ≠ 2π`, are a.e. isomorphism charts**, with source
`E_κ`: the converse of `exists_eqOn_rotShift` (BTZ_1's `Isom(E_κ)`, l.373). -/
theorem isAEChart_rotShift (hα : α ≠ 2 * π) (s : ℝ) (c : AddCircle α) :
    IsAEChart (Flat.isom 2) (Minkowski 2) (rotShift s c).toOpenPartialHomeomorph :=
  ⟨isRegularOn_rotShift hα (fun _ => rfl) isOpen_univ,
    isRegularOn_rotShift hα (s := -s) (c := -c) (fun _ => rfl) isOpen_univ⟩

end BPrime

/-- **(b′) at the models `E_κ`, `κ > 0`**: every a.e. isomorphism chart `ψ : E_κ ⇀ E_κ′` is a
chart isomorphism `massive κ → massive κ′`, its source meeting the singular line or not. -/
theorem chartIso_of_isAEChart {κ κ' : ℝ} [Fact (0 < κ)] [Fact (0 < κ')]
    {ψ : OpenPartialHomeomorph (Massive κ) (Massive κ')}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) : ChartIso (massive κ) (massive κ') ψ := by
  by_cases h2π : κ = 2 * π
  · subst h2π
    exact chartIso_of_isAEChart_two_pi (κ' := ⟨κ', Fact.out⟩) hψ
  by_cases hline : ∃ p ∈ ψ.source, p ∈ singLine κ
  · obtain ⟨p, hp, hps⟩ := hline
    have he := eq_of_isAEChart h2π hψ hp hps
    subst he
    exact chartIso_of_isAEChart_self h2π hψ
  · push Not at hline
    exact chartIso_of_isAEChart_of_subset_regPart (κ := ⟨κ, Fact.out⟩) (κ' := ⟨κ', Fact.out⟩)
      h2π hψ fun x hx => hline x hx

attribute [local instance] singularGXFamily

/-- **The hypothesis (b′) (`hiso`) of `existsUnique_causality_singularGX_dec25` for the family of
the models `E_κ`, `κ > 0`.** -/
theorem hiso_family : ∀ (κ κ' : {κ : ℝ // 0 < κ})
    (ψ : OpenPartialHomeomorph (Massive κ.1) (Massive κ'.1)),
    IsAEChart (Flat.isom 2) (Minkowski 2) ψ → ChartIso (massiveOf κ) (massiveOf κ') ψ := by
  intro κ κ' ψ hψ
  haveI : Fact (0 < κ.1) := ⟨κ.2⟩
  haveI : Fact (0 < κ'.1) := ⟨κ'.2⟩
  exact chartIso_of_isAEChart hψ

universe u

/-- **`E_{>0}`-manifolds** (`prop:GX_sing_espace_temps_topo` at the models `E_κ`, `κ > 0`, DEC-25):
a singular `(Isom(E^{1,2}), E^{1,2})`-manifold whose singular points lie in a.e. isomorphism
charts into the models `E_κ` carries an absolutely minimal causality for which every chart of its
maximal a.e. atlas and every chart into a model is an isomorphism, unique among absolutely minimal
causalities with some such chart an isomorphism at each point. No model hypothesis is left. -/
theorem existsUnique_causality_ealpha {M : Type u} [TopologicalSpace M]
    [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ κ : {κ : ℝ // 0 < κ},
      ∃ e : OpenPartialHomeomorph M (Massive κ.1), IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
        x ∈ e.source) :
    ∃ C : Causality M, (∀ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, ChartIso C (minkowski 2) e) ∧
      (∀ (κ : {κ : ℝ // 0 < κ}) (e : OpenPartialHomeomorph M (Massive κ.1)),
        IsAEChart (Flat.isom 2) (Minkowski 2) e → ChartIso C (massiveOf κ) e) ∧
      C.AbsolutelyMinimal ∧
      ∀ C' : Causality M, C'.AbsolutelyMinimal →
        (∀ x : M, (∃ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, x ∈ e.source ∧
            ChartIso C' (minkowski 2) e) ∨
          ∃ κ : {κ : ℝ // 0 < κ}, ∃ e : OpenPartialHomeomorph M (Massive κ.1),
            IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source ∧ ChartIso C' (massiveOf κ) e) →
        C' = C :=
  existsUnique_causality_singularGX_dec25 (Xα := fun κ : {κ : ℝ // 0 < κ} => Massive κ.1)
    (minkowski 2) massiveOf minkowski_causallyArcConnected Flat.isom_strongMorphism
    (fun κ => @massive_causallyArcConnected κ.1 ⟨κ.2⟩) hreg_family hiso_family hcov

/-! ### The reflection `θ ↦ −θ` (OQ-82) -/

section Reflection

variable {α : ℝ} [Fact (0 < α)]

/-- **The reflection `θ ↦ −θ` of `E_κ`**, an isometry of `E_κ` reversing the orientation of the
cone: it develops to a reflection of `E^{1,2}` in a timelike plane through the time axis. -/
noncomputable def conjE (α : ℝ) : Massive α ≃ₜ Massive α := shiftIso 0 (ConeRot.conjIso (α := α))

/-- **The reflection is a chart isomorphism of `E_κ`**: an isometry of the cone, times the
identity of time. -/
theorem chartIso_conjE : ChartIso (massive α) (massive α) (conjE α).toOpenPartialHomeomorph :=
  chartIso_shiftIso 0 ConeRot.conjIso

/-- **Under `Isom(E^{1,2}) = SO₀(1,2) ⋉ ℝ³` the reflection is not an a.e. isomorphism chart** of
`E_κ`, `κ ≠ 2π`: near the singular point `(0, apex)` it would be a rotation-translation
(`exists_eqOn_rotShift`); fixing `polar(ρ, 0)` forces the identity, which does not send
`polar(ρ, κ/4)` to `polar(ρ, −κ/4)`. (The determinant is where the proof excludes it.) -/
theorem not_isAEChart_conjE (hα : α ≠ 2 * π) :
    ¬ IsAEChart (Flat.isom 2) (Minkowski 2) (conjE α).toOpenPartialHomeomorph := by
  intro h
  have hα0 : 0 < α := Fact.out
  set p : Massive α := ((0 : ℝ), Cone.apex) with hpdef
  obtain ⟨s, c, O, hpO, -, heq⟩ := exists_eqOn_rotShift hα h (p := p) (mem_univ _) rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 O.isOpen p hpO
  have hρ : 0 < δ / 2 := by positivity
  have hmem : ∀ θ : ℝ, pt α (0, δ / 2, θ) ∈ O := fun θ =>
    hball (pt_mem_ball rfl (mem_ball_self hδ) hρ.le (by linarith) θ)
  -- at the angle `0`: `s = 0` and `c = 0`
  have h1 := heq _ (hmem 0)
  rw [rotShift_apply] at h1
  change (((0 : ℝ) + 0, ConeRot.conj (Cone.polar (δ / 2, ((0 : ℝ) : AddCircle α)))) :
    Massive α) = ((0 : ℝ) + s, ConeRot.rot c (Cone.polar (δ / 2, ((0 : ℝ) : AddCircle α)))) at h1
  rw [ConeRot.conj_polar, ConeRot.rot_polar] at h1
  have hc : c = 0 := by
    have := polar_inj hρ (congrArg Prod.snd h1)
    rw [AddCircle.coe_zero, neg_zero, zero_add] at this
    exact this.symm
  -- at the angle `κ/4`
  have h2 := heq _ (hmem (α / 4))
  rw [rotShift_apply] at h2
  change (((0 : ℝ) + 0, ConeRot.conj (Cone.polar (δ / 2, ((α / 4 : ℝ) : AddCircle α)))) :
    Massive α) = ((0 : ℝ) + s, ConeRot.rot c (Cone.polar (δ / 2, ((α / 4 : ℝ) : AddCircle α))))
    at h2
  rw [ConeRot.conj_polar, ConeRot.rot_polar, hc, add_zero] at h2
  have h3 := polar_inj hρ (congrArg Prod.snd h2)
  rw [add_zero] at h3
  have h4 : ((α / 2 : ℝ) : AddCircle α) = 0 := by
    rw [show α / 2 = α / 4 + α / 4 by ring, AddCircle.coe_add]
    calc ((α / 4 : ℝ) : AddCircle α) + ((α / 4 : ℝ) : AddCircle α) =
        -((α / 4 : ℝ) : AddCircle α) + ((α / 4 : ℝ) : AddCircle α) := by rw [h3]
      _ = 0 := neg_add_cancel _
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff α).1 h4
  rw [zsmul_eq_mul] at hn
  have hn0 : (0 : ℝ) < n := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0 : ℤ) < n := by exact_mod_cast hn0
    exact_mod_cast this
  nlinarith

end Reflection

/-! ### Non-vacuity -/

attribute [local instance] EAlphaGX.fact_pi_pos

/-- **Non-vacuity** (kb/0011), at `κ = π`. (1) Every rotation-translation of `E_π` is an a.e.
isomorphism chart whose source meets the singular line, so `prop_isom_local` and
`chartIso_of_isAEChart` apply to it at a singular point, and it is a chart isomorphism. (2) `E_π`
itself satisfies the hypothesis of `existsUnique_causality_ealpha`: its singular locus is the
line, nonempty, covered by the identity, an a.e. isomorphism chart into the model
`E_π`. -/
theorem nonvacuous (s : ℝ) (c : AddCircle π) :
    IsAEChart (Flat.isom 2) (Minkowski 2) (rotShift (α := π) s c).toOpenPartialHomeomorph ∧
      ((rotShift (α := π) s c).toOpenPartialHomeomorph.source ∩ singLine π).Nonempty ∧
      ChartIso (massive π) (massive π) (rotShift (α := π) s c).toOpenPartialHomeomorph ∧
      (Sing (Flat.isom 2) (Minkowski 2) (Massive π)).Nonempty ∧
      ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) (Massive π), ∃ κ : {κ : ℝ // 0 < κ},
        ∃ e : OpenPartialHomeomorph (Massive π) (Massive κ.1),
          IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source := by
  have hπ : π ≠ 2 * π := by linarith [pi_pos]
  refine ⟨isAEChart_rotShift hπ s c, ⟨((0 : ℝ), Cone.apex), mem_univ _, rfl⟩,
    chartIso_rotShift s c, sing_nonempty hπ, fun x _ => ⟨⟨π, pi_pos⟩,
      OpenPartialHomeomorph.refl (Massive π), isAEChart_refl, mem_univ x⟩⟩

end BPrimeEAlpha

end Causal
