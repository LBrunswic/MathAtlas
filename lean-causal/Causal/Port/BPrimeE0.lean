import Causal.Port.E0GXStructure
import Causal.Remarks.MassADEC25

/-!
# (b′) at `E₀`: every a.e. isomorphism between open subsets of `E₀` is a causal isomorphism

`cor:massA_causalite` — `ETT.tex:1396`. **Not marked** (SCOPE): this file discharges, at the model
`E₀` and under the readings OQ-34, OQ-35, OQ-64, OQ-82, the hypothesis (b′) (`hiso`) that the
existence half of the corollary takes in `Causal.massA_singular_dec25_models`, at `o = o′ = E₀`.
Target `T-ett-bprime-e0`.

> Every $\mass{\geq 0}$-manifold carries a natural absolutely minimal causality. (`ETT.tex:1396`)

> […] hypothesis $(B)$ from the fact that transition maps are restrictions of elements of $G$ and
> of isomorphisms of the model spaces […] (`ETT.tex:631–632`)

The step at `E₀` is `prop:isom` of `brunswic2021cauchy` at `α = β = 0`
(`papers/gx/sources/2108.12631/src/BTZ_1.tex:378–383`, proof l.444–465, « mutatis mutandis »
for `α = 0`, l.447):

> Let $\alpha,\beta\in \R_+$ with $\alpha\neq 2\pi$, and let $\U$ be an open connected
> subset of $\E^{1,2}_\alpha$ containing a singular point and let
> $\phi:\U\rightarrow \E^{1,2}_\beta$ be an almost everywhere $\mass{}$-morphism. If $\phi$ is a
> local homeomorphism then $\alpha=\beta$ and $\phi$ is the restriction of an element of
> $\isom(\E^{1,2}_\alpha)$.

## What is proved (no `sorry` in this file)

* **`prop:isom` at `α = β = 0`, local form** (`exists_eqOn_rotE0_tauShift`): near an axis point of
  its source, an a.e. isomorphism chart `ψ : E₀ ⇀ E₀` (`IsAEChart` for `E0GX.singularGX`) is
  `rotE0 φ ∘ tauShift t`, a rotation about the axis after a translation along it. Conversely every
  such map is an a.e. isomorphism chart (`isAEChart_rotE0_tauShift`): near the axis the a.e.
  isomorphisms are exactly BTZ_1's `Isom(𝔼^{1,2}_0)` (l.372–373).
* **(b′) at `E₀`** (`chartIso_of_isAEChart`): every a.e. isomorphism chart `ψ : E₀ ⇀ E₀`, its source
  meeting the axis or not, is a chart isomorphism of `E0.causality`. Assembled:
  `hiso_massAModel_none`, the hypothesis `hiso` of `massA_singular_dec25_models` at
  `o = o′ = none`, for any family of model structures equal to `E0GX.singularGX` at `E₀`.
* **`E₀`-manifolds** (`existsUnique_causality_e0`): `existsUnique_causality_singularGX_dec25` at the
  single model `E₀`, every model hypothesis discharged: a singular `(Isom(𝐌³), 𝐌³)`-manifold whose
  singular points lie in a.e. charts into `E₀` carries a unique natural absolutely minimal causality.
* **The reflection** `conjE0` (`θ ↦ −θ`) is a chart isomorphism (`chartIso_conjE0`) and, under
  `Flat.isom 2 = SO₀(1,2) ⋉ ℝ³`, not an a.e. isomorphism chart (`not_isAEChart_conjE0`).
* **Non-vacuity** (`nonvacuous`): each `rotE0 φ ∘ tauShift t` is an a.e. isomorphism chart through
  the axis; `E₀` itself is an `E₀`-manifold with `Sing ≠ ∅`, and `E0.causality` is its natural one.

## The route (restated over `E0GX`'s sector charts; gx's `GX.e0_localUnique_sing` is not used)

On a slit box `T = {|τ − τ_p| < ε, |z| < ε, z ∉ ℝ≤0}` the reference chart `c₀ = sectorChart (0,1)`
develops `x` with the angle `arg`. (1) `HolRel`: near each `x ∈ T`, `ψ` reads from `c₀` into a
sector chart as `hol(2π)^k * g`; the class of `g` modulo the holonomy is locally constant, so
one `g ∈ Isom(𝐌³)` sends the development of every `x ∈ T` to a development of `ψ x`
(`exists_isom_dev`, by `IsPreconnected.induction₂'`). (2) Along `ρ ↦ (τ, ρ)`, `ρ → 0`, the
image development has `b = r → 0` and `c² − ab = r² − 2τr → 0`: `g` maps the developed axis, the
null line `ℝ(1,0,0)`, into itself (`smul_null_line`). (3) Such an isometry is
`y ↦ B_μ(H_u y) + (s, 0, 0)`, `μ > 0`; the determinant excludes the reflection `c ↦ −c`
(`linear_of_null_fixed`, `isom_of_null_line`). (4) Hence on `T`,
`ψ(τ, re^{iθ}) = (μτ + (r/μ − μr)/2 + s/2, (r/μ)e^{iμ(θ+u)})`, BTZ_1's `h_ℓ` (l.369), `ℓ = μ`
(`eq_of_dev`). (5) `μ > 1` contradicts injectivity on `T`, `μ < 1` continuity across the slit
(`e^{2πiμ} ≠ 1`), so `μ = 1` (`mu_eq_one`); by density `ψ = rotE0 u ∘ tauShift (s/2)` on the
ball (`ball_subset_closure_slitBox`). (6) Locality (`E0.absolutelyMinimalOn`,
`imp_of_agree_locally`) and the regular case (`ChartIso.agreeOn_of_isAEChart`) give (b′).

## Hypothesis checklist

| paper / roadmap | here |
|---|---|
| `E₀` the extreme BTZ model (l.1330) | ⚠ read: `Causal.E0`, gx's metric through `D` (OQ-34, OQ-35) |
| « isomorphisms of the model spaces » (l.631–632) | ⚠ read (OQ-64): `IsAEChart` between open subsets of `E₀` (an open partial homeomorphism, a.e. `(G,X)` both ways); an isomorphism « of topological spacetimes » is `ChartIso` |
| `Isom(𝔼^{1,2})` (l.1331, l.1401) | ⚠ read (OQ-82): `Flat.isom 2 = SO₀(1,2) ⋉ ℝ³`; used once, through the determinant, to exclude the reflection |
| prop:isom: `U` open connected containing a singular point, `φ` a local homeomorphism | ⚠ strengthened (read through `IsAEChart`), local form: conclusion on a ball about each axis point of the source; `φ` an open partial homeomorphism (injective), as `IsAEChart` asks |
| prop:isom: `α = β` | ⚠ strengthened: `α = β = 0` (the only model here) |
| `cor:massA_causalite`: every `E_{≥0}`-manifold | ⚠ strengthened: the models `E₀` only: (b′) at `o = o′ = E₀`; the `E_κ` pairs need `E_κ`'s singular structure |

## SCOPE (disclosed)

* **Why unmarked.** The row's mark waits on OQ-18 (« natural »), OQ-64 ((b′) as a hypothesis of
  the model spaces), OQ-82 (the group) and OQ-34/OQ-35 (`E₀`), and the row itself on
  T-ett-singular-instance (no `E_{≥0}`-manifold with all its models packaged). This file proves
  (b′) at `E₀ → E₀` only; `E₀ ↔ E_κ` and `E_κ ↔ E_κ′` are not addressed.
* **Under OQ-82's other reading** `O↑(1,2) ⋉ ℝ³` the determinant step fails and the reflection
  after a rotation and a translation becomes an a.e. isomorphism; it is a chart isomorphism
  (`chartIso_conjE0`), but the theorem for that group is not stated (no such group in the library).
* **Not proved**: `prop:isom`'s global form (on a connected `U`, by `lem:liouville`); the local form
  is all (b′) needs.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Restated over the strict
`Causal.Port.E0GXStructure` (lean-causal never imports gx, DEC-33); gx's route
(`lean-gx/GX/BTZ/Rigid.lean` l.581–1720, a lift through the covering and the deck relation) was read
and not followed.
-/

namespace Causal

open Set Filter Topology TopologicalSpace Function

universe u

namespace BPrimeE0

open E0 E0GX Complex
open scoped Real

attribute [local instance] E0GX.singularGX

/-! ### The reference sector chart -/

/-- The base point `(0, 1)` of the reference sector, slit along `ℝ≤0`. -/
def y₀ : E0 := ((0 : ℝ), (1 : ℂ))

theorem y₀_ne : y₀.2 ≠ 0 := one_ne_zero

/-- **The reference chart** `c₀ = sectorChart (0, 1)`: the development with the angle `arg`. -/
noncomputable abbrev c₀ : OpenPartialHomeomorph E0 (Minkowski 2) := sectorChart y₀ y₀_ne

theorem mem_sector_y₀ {x : E0} : x ∈ sector y₀ ↔ x.2 ∈ slitPlane := by
  show x.2 / 1 ∈ slitPlane ↔ _
  rw [div_one]

theorem c₀_apply (x : E0) : c₀ x = nullToMink (lift x (arg x.2)) := by
  show nullToMink (lift x (arg (1 : ℂ) + arg (x.2 / 1))) = _
  rw [arg_one, div_one, zero_add]

theorem c₀_mem_aeAtlas : c₀ ∈ aeAtlas (Flat.isom 2) (Minkowski 2) E0 :=
  sectorAtlas_subset_aeAtlas (sectorChart_mem_sectorAtlas y₀_ne)

/-! ### The developments of `ψ` on a slit set, up to the holonomy -/

/-- `ψ` reads near `x`, from `c₀` into some sector chart, as `hol(2π)^k * g`. -/
def HolRel (ψ : OpenPartialHomeomorph E0 E0) (g : Flat.isom 2) (x : E0) : Prop :=
  ∃ (y : E0) (hy : y.2 ≠ 0) (k : ℤ), ψ x ∈ sector y ∧
    ∀ᶠ w in 𝓝 x, sectorChart y hy (ψ w) = (hol (2 * π) ^ k * g) • c₀ w

/-- At a point of the source off the slit, `ψ` reads from `c₀` as one isometry near it: the local
`(G,X)` condition of `IsAEChart`, into the sector chart at `ψ x`. -/
theorem eventually_holRel {ψ : OpenPartialHomeomorph E0 E0}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {x : E0} (hx : x ∈ ψ.source)
    (hxs : x.2 ∈ slitPlane) : ∃ g : Flat.isom 2, ∀ᶠ w in 𝓝 x, HolRel ψ g w := by
  have hx0 : x.2 ≠ 0 := slitPlane_ne_zero hxs
  have hxr : x ∈ Reg (Flat.isom 2) (Minkowski 2) E0 := by rw [reg_eq]; exact hx0
  have hψx : ψ x ∈ Reg (Flat.isom 2) (Minkowski 2) E0 := (hψ.mem_reg_iff hx).1 hxr
  have hψx0 : (ψ x).2 ≠ 0 := by rw [reg_eq] at hψx; exact hψx
  obtain ⟨g, hg⟩ := hψ.regularOn.exists_smul_eq x ⟨hx, hxr⟩ c₀ c₀_mem_aeAtlas
    (sectorChart (ψ x) hψx0) (sectorAtlas_subset_aeAtlas (sectorChart_mem_sectorAtlas hψx0))
    (mem_sector_y₀.2 hxs) (mem_sector_self hψx0)
  refine ⟨g, ?_⟩
  have hc : ∀ᶠ w in 𝓝 x, ψ w ∈ sector (ψ x) :=
    (ψ.continuousAt hx).preimage_mem_nhds ((isOpen_sector _).mem_nhds (mem_sector_self hψx0))
  filter_upwards [hg.eventually_nhds, hc] with w hw hws
  exact ⟨ψ x, hψx0, 0, hws, by simpa using hw⟩

/-- The relation is invariant under the holonomy `hol(2π)`. -/
theorem HolRel.mul_left {ψ : OpenPartialHomeomorph E0 E0} {g : Flat.isom 2} {x : E0}
    (h : HolRel ψ g x) (j : ℤ) : HolRel ψ (hol (2 * π) ^ j * g) x := by
  obtain ⟨y, hy, k, hxy, hev⟩ := h
  refine ⟨y, hy, k - j, hxy, ?_⟩
  have e : hol (2 * π) ^ (k - j) * (hol (2 * π) ^ j * g) = hol (2 * π) ^ k * g := by
    rw [← mul_assoc, ← zpow_add, sub_add_cancel]
  rwa [e]

/-- **Two isometries reading `ψ` at `x` differ by a power of the holonomy**: two sector charts at
`ψ x` differ by one (`sectorChart_eventually_eq_zpow_smul`), and `Isom(𝐌³)` acts rigidly. -/
theorem HolRel.unique {ψ : OpenPartialHomeomorph E0 E0} {g g' : Flat.isom 2} {x : E0}
    (hx : x ∈ ψ.source) (hxs : x.2 ∈ slitPlane) (h : HolRel ψ g x) (h' : HolRel ψ g' x) :
    ∃ j : ℤ, g' = hol (2 * π) ^ j * g := by
  obtain ⟨y, hy, k, hxy, hev⟩ := h
  obtain ⟨y', hy', k', hxy', hev'⟩ := h'
  obtain ⟨m, hm⟩ := sectorChart_eventually_eq_zpow_smul hy hy' hxy hxy'
  have hm' : ∀ᶠ w in 𝓝 x,
      sectorChart y' hy' (ψ w) = hol (2 * π) ^ m • sectorChart y hy (ψ w) :=
    (ψ.continuousAt hx).eventually hm
  have hall : ∀ᶠ w in 𝓝 x, (hol (2 * π) ^ k' * g') • c₀ w =
      (hol (2 * π) ^ m * (hol (2 * π) ^ k * g)) • c₀ w := by
    filter_upwards [hev, hev', hm'] with w h1 h2 h3
    rw [← h2, h3, h1, mul_smul, mul_smul, mul_smul]
  obtain ⟨t, ht, hto, hxt⟩ :=
    mem_nhds_iff.1 (hall.and ((isOpen_sector y₀).mem_nhds (mem_sector_y₀.2 hxs)))
  have hts : t ⊆ c₀.source := fun w hw => (ht hw).2
  have hr := IsRigidAction.smul_eq_of_eqOn (c₀.isOpen_image_of_subset_source hto hts)
    ⟨_, x, hxt, rfl⟩ (by rintro _ ⟨w, hw, rfl⟩; exact (ht hw).1)
  have hgg : hol (2 * π) ^ k' * g' = hol (2 * π) ^ m * (hol (2 * π) ^ k * g) :=
    Subtype.ext (AffineEquiv.ext fun v => hr v)
  refine ⟨m + k - k', ?_⟩
  calc g' = (hol (2 * π) ^ k')⁻¹ * (hol (2 * π) ^ k' * g') := by group
    _ = hol (2 * π) ^ (m + k - k') * g := by rw [hgg]; group

/-- An isometry reading `ψ` at `x` sends the development of `x` to a development of `ψ x`. -/
theorem HolRel.dev {ψ : OpenPartialHomeomorph E0 E0} {g : Flat.isom 2} {x : E0}
    (h : HolRel ψ g x) : ∃ θ, Polar (ψ x) θ ∧ nullToMink (lift (ψ x) θ) = g • c₀ x := by
  obtain ⟨y, hy, k, hxy, hev⟩ := h
  have h0 := hev.self_of_nhds
  refine ⟨angle y (ψ x) + 2 * π * ((-k : ℤ) : ℝ), (polar_angle hy _).add_int (-k), ?_⟩
  rw [lift_add_angle, ← hol_smul_nullToMink, hol_two_pi_mul_int]
  have e : nullToMink (lift (ψ x) (angle y (ψ x))) = sectorChart y hy (ψ x) := rfl
  rw [e, h0, ← mul_smul, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

/-- **One isometry develops `ψ` on a preconnected slit set**: on a preconnected `T` in the
source, off the slit `ℝ≤0`, some `g ∈ Isom(𝐌³)` sends the development of every `x ∈ T` (with
the angle `arg`) to a development of `ψ x`. -/
theorem exists_isom_dev {ψ : OpenPartialHomeomorph E0 E0}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {T : Set E0} (hT : IsPreconnected T)
    (hTs : T ⊆ ψ.source) (hTsl : ∀ x ∈ T, x.2 ∈ slitPlane) {x₀ : E0} (hx₀ : x₀ ∈ T) :
    ∃ g : Flat.isom 2, ∀ x ∈ T, ∃ θ, Polar (ψ x) θ ∧
      nullToMink (lift (ψ x) θ) = g • nullToMink (lift x (arg x.2)) := by
  obtain ⟨g, hg⟩ := eventually_holRel hψ (hTs hx₀) (hTsl x₀ hx₀)
  refine ⟨g, fun x hx => ?_⟩
  have key : ∀ g', HolRel ψ g' x₀ → HolRel ψ g' x := by
    refine hT.induction₂' (fun a b => ∀ g', HolRel ψ g' a → HolRel ψ g' b) ?_ ?_ hx₀ hx
    · intro a ha
      obtain ⟨g₀, hg₀⟩ := eventually_holRel hψ (hTs ha) (hTsl a ha)
      have hg₀a := hg₀.self_of_nhds
      filter_upwards [nhdsWithin_le_nhds hg₀, self_mem_nhdsWithin] with b hb hbT
      refine ⟨fun g' hg' => ?_, fun g' hg' => ?_⟩
      · obtain ⟨j, rfl⟩ := HolRel.unique (hTs ha) (hTsl a ha) hg₀a hg'
        exact hb.mul_left j
      · obtain ⟨j, rfl⟩ := HolRel.unique (hTs hbT) (hTsl b hbT) hb hg'
        exact hg₀a.mul_left j
    · intro a b c _ _ _ h1 h2 g' hg'
      exact h2 g' (h1 g' hg')
  obtain ⟨θ, h1, h2⟩ := (key g hg.self_of_nhds).dev
  exact ⟨θ, h1, by rw [h2, c₀_apply]⟩

/-! ### The isometries of `𝐌³` preserving the developed axis -/

/-- The null form `c² − ab` of `(a, b, c)`. -/
def nullQ (y : ℝ × ℝ × ℝ) : ℝ := y.2.2 ^ 2 - y.1 * y.2.1

/-- `lift` written out (`btzPaperNull`). -/
theorem lift_eq (x : E0) (θ : ℝ) :
    lift x θ = (2 * x.1 + rad x * θ ^ 2 - rad x, rad x, -(rad x * θ)) := by
  unfold E0.lift E0.btzPaperNull; rfl

/-- The null form of a development: `r² − 2τr`, independent of the angle. -/
theorem nullQ_lift (x : E0) (θ : ℝ) : nullQ (lift x θ) = rad x ^ 2 - 2 * x.1 * rad x := by
  rw [lift_eq, nullQ]; ring

/-- Coordinates `ℝ × ℝ × ℝ ≃ ℝ³`, to compute a determinant. -/
noncomputable def coordsNull : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun y := ![y.1, y.2.1, y.2.2]
  invFun v := (v 0, v 1, v 2)
  map_add' y y' := by funext i; fin_cases i <;> simp
  map_smul' c y := by funext i; fin_cases i <;> simp
  left_inv y := by simp
  right_inv v := by funext i; fin_cases i <;> simp

/-- **A linear map of `ℝ³` preserving `c² − ab`, of determinant one, and fixing the direction of
`(1, 0, 0)`** is `(a, b, c) ↦ (μa + μγ'²b + 2μγ'c, b/μ, γ'b + c)`. -/
theorem linear_of_null_fixed (N : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ))
    (hQ : ∀ y, nullQ (N y) = nullQ y) {μ : ℝ} (hμne : μ ≠ 0) (hN1 : N (1, 0, 0) = (μ, 0, 0))
    (hdet : LinearMap.det (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) = 1) :
    ∃ γ' : ℝ, ∀ y : ℝ × ℝ × ℝ,
      N y = (μ * y.1 + μ * γ' ^ 2 * y.2.1 + 2 * μ * γ' * y.2.2, y.2.1 / μ, γ' * y.2.1 + y.2.2) := by
  obtain ⟨⟨α', β', γ'⟩, h2⟩ : ∃ v, N (0, 1, 0) = v := ⟨_, rfl⟩
  obtain ⟨⟨α, β, γ⟩, h3⟩ : ∃ v, N (0, 0, 1) = v := ⟨_, rfl⟩
  have hNy : ∀ a b c : ℝ, N (a, b, c) =
      (a * μ + b * α' + c * α, b * β' + c * β, b * γ' + c * γ) := by
    intro a b c
    have e : ((a, b, c) : ℝ × ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
        b • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rw [e, map_add, map_add, map_smul, map_smul, map_smul, hN1, h2, h3]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  have q001 := hQ (0, 0, 1)
  have q010 := hQ (0, 1, 0)
  have q101 := hQ (1, 0, 1)
  have q110 := hQ (1, 1, 0)
  have q011 := hQ (0, 1, 1)
  simp only [hNy, nullQ] at q001 q010 q101 q110 q011
  norm_num at q001 q010 q101 q110 q011
  have hβ : β = 0 := by
    have h : μ * β = 0 := by linear_combination q001 - q101
    exact (mul_eq_zero.1 h).resolve_left hμne
  subst hβ
  have hβ' : μ * β' = 1 := by linear_combination q010 - q110
  have hγ2 : γ ^ 2 = 1 := by linear_combination q001
  have hα' : α' = μ * γ' ^ 2 := by linear_combination (-μ) * q010 - α' * hβ'
  have hα : α = 2 * μ * γ * γ' := by
    linear_combination (-μ) * (q011 - q010 - hγ2) - α * hβ'
  have hb' : β' = 1 / μ := by field_simp; linarith
  have hdetγ : LinearMap.det (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) = γ := by
    rw [← LinearMap.det_conj (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) coordsNull,
      ← LinearMap.det_toMatrix', Matrix.det_fin_three]
    simp [LinearMap.toMatrix'_apply, coordsNull, hNy, hα', hα, hb']
    field_simp
  have hγ1 : γ = 1 := by rw [← hdetγ, hdet]
  subst hγ1
  refine ⟨γ', fun y => ?_⟩
  rw [show y = (y.1, y.2.1, y.2.2) from rfl, hNy, hα', hα, hb']
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- **An isometry of `𝐌³` sending two points of the null line `ℝ(1, 0, 0)` into it** is, in null
coordinates, `y ↦ B_μ(H_u y) + (s, 0, 0)`: a boost `B_μ (a, b, c) = (μa, b/μ, c)`, `μ > 0`,
after the parabolic `H_u = angleShift u`, then a translation along the line. (The determinant
excludes the reflection `c ↦ −c`.) -/
theorem isom_of_null_line (g : Flat.isom 2) {a₁ a₂ b₁ b₂ : ℝ} (hne : a₁ ≠ a₂)
    (h₁ : g • nullToMink (a₁, 0, 0) = nullToMink (b₁, 0, 0))
    (h₂ : g • nullToMink (a₂, 0, 0) = nullToMink (b₂, 0, 0)) :
    ∃ μ u s : ℝ, 0 < μ ∧ ∀ y : ℝ × ℝ × ℝ, g • nullToMink y =
      nullToMink (μ * (y.1 - 2 * u * y.2.2 + u ^ 2 * y.2.1) + s, y.2.1 / μ, y.2.2 - u * y.2.1) := by
  have hA : (g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2).linear ∈ Flat.lorentz 2 := g.2
  have haff : ∀ v, g • v = (g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2).linear v + g • (0 : Minkowski 2) :=
    fun v => by
      have h := Flat.isom_sub (g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2) 0 v
      rw [sub_zero] at h
      rw [Flat.isom_smul_def, Flat.isom_smul_def, ← h]
      abel
  let N : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ) :=
    nullToMink.trans ((g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2).linear.trans nullToMink.symm)
  have hN : ∀ y, (g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2).linear (nullToMink y) = nullToMink (N y) :=
    fun y => by
      show _ = nullToMink (nullToMink.symm _)
      rw [LinearEquiv.apply_symm_apply]
      rfl
  have hQ : ∀ y, nullQ (N y) = nullQ y := fun y => by
    rw [nullQ, nullQ, ← minkQ_nullToMink, ← minkQ_nullToMink, ← hN, Flat.lorentz.minkQ_apply hA]
  -- the image of the null direction
  have hsub : a₂ - a₁ ≠ 0 := sub_ne_zero.2 hne.symm
  have e2 : N (a₂ - a₁, 0, 0) = (b₂ - b₁, 0, 0) := by
    have e : (g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2).linear
        (nullToMink (a₂, 0, 0) - nullToMink (a₁, 0, 0)) =
        nullToMink (b₂, 0, 0) - nullToMink (b₁, 0, 0) := by
      rw [← h₁, ← h₂, Flat.isom_smul_def, Flat.isom_smul_def, Flat.isom_sub]
    rw [← map_sub, ← map_sub, hN] at e
    have e' := nullToMink.injective e
    have ha : ((a₂, 0, 0) - (a₁, 0, 0) : ℝ × ℝ × ℝ) = (a₂ - a₁, 0, 0) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    have hb : ((b₂, 0, 0) - (b₁, 0, 0) : ℝ × ℝ × ℝ) = (b₂ - b₁, 0, 0) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rwa [ha, hb] at e'
  have he2 : N (a₂ - a₁, 0, 0) = (a₂ - a₁) • N (1, 0, 0) := by
    rw [← map_smul]; congr 1; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  rw [he2] at e2
  have c2 : (a₂ - a₁) * (N (1, 0, 0)).2.1 = 0 := congrArg (fun v => v.2.1) e2
  have c3 : (a₂ - a₁) * (N (1, 0, 0)).2.2 = 0 := congrArg (fun v => v.2.2) e2
  have hN1 : N (1, 0, 0) = ((N (1, 0, 0)).1, 0, 0) :=
    Prod.ext rfl (Prod.ext ((mul_eq_zero.1 c2).resolve_left hsub)
      ((mul_eq_zero.1 c3).resolve_left hsub))
  set μ := (N (1, 0, 0)).1 with hμ
  -- `μ > 0`
  have hμ0 : 0 ≤ μ := by
    have hf : Flat.IsFutureCausal (nullToMink ((1 : ℝ), (0 : ℝ), (0 : ℝ))) :=
      (nullCone_iff_isFutureCausal _).1 ⟨zero_le_one, le_rfl, by norm_num⟩
    have hf' := Flat.lorentz.isFutureCausal_apply hA hf
    rw [hN, hN1, ← nullCone_iff_isFutureCausal] at hf'
    exact hf'.1
  have hμne : μ ≠ 0 := fun h0 => by
    have h : N (1, 0, 0) = N 0 := by rw [hN1, h0, map_zero]; rfl
    have := congrArg Prod.fst (N.injective h)
    simp at this
  have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμne)
  -- the determinant
  have hdetN : LinearMap.det (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) = 1 := by
    have e : ((g : Minkowski 2 ≃ᵃ[ℝ] Minkowski 2).linear : Minkowski 2 →ₗ[ℝ] Minkowski 2) =
        (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Minkowski 2) ∘ₗ
        (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ (nullToMink.symm : Minkowski 2 →ₗ[ℝ] _) := by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [← hN, LinearEquiv.apply_symm_apply]
    rw [← LinearMap.det_conj (N : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) nullToMink, ← e]
    exact Flat.lorentz.det_eq_one hA
  obtain ⟨γ', hNf⟩ := linear_of_null_fixed N hQ hμne hN1 hdetN
  -- the translation part
  have h0 : g • (0 : Minkowski 2) = nullToMink (b₁ - a₁ * μ, 0, 0) := by
    have h := haff (nullToMink (a₁, 0, 0))
    rw [h₁, hN, hNf] at h
    have e : nullToMink (b₁ - a₁ * μ, 0, 0) = nullToMink (b₁, 0, 0) -
        nullToMink (μ * (a₁, (0 : ℝ), (0 : ℝ)).1 + μ * γ' ^ 2 * (a₁, (0 : ℝ), (0 : ℝ)).2.1 +
          2 * μ * γ' * (a₁, (0 : ℝ), (0 : ℝ)).2.2, (a₁, (0 : ℝ), (0 : ℝ)).2.1 / μ,
          γ' * (a₁, (0 : ℝ), (0 : ℝ)).2.1 + (a₁, (0 : ℝ), (0 : ℝ)).2.2) := by
      rw [← map_sub]; congr 1
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
    rw [e, h]; abel
  refine ⟨μ, -γ', b₁ - a₁ * μ, hμpos, fun y => ?_⟩
  rw [haff, hN, h0, ← map_add, hNf]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-! ### Limits at the axis -/

/-- Two maps continuous at `a`, equal along a non-trivial filter finer than `𝓝 a`, agree at `a`. -/
theorem eq_of_eventuallyEq_of_continuousAt {α : Type*} [TopologicalSpace α] [T2Space α]
    {f g : ℝ → α} {a : ℝ} {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝 a) (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (h : f =ᶠ[l] g) : f a = g a :=
  tendsto_nhds_unique ((hf.tendsto.mono_left hl).congr' h) (hg.tendsto.mono_left hl)

/-- **The developing isometry preserves the developed axis**: if `g` develops `ψ` along the
segment `ρ ↦ (τ, ρ)`, `0 < ρ < ε`, and `(τ, 0)` is in the source, `g` sends `D(τ, 0, ·)` into the
null line `ℝ(1, 0, 0)`: `r → 0` and `c² − ab = r² − 2τr → 0` along it. -/
theorem smul_null_line {ψ : OpenPartialHomeomorph E0 E0}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {g : Flat.isom 2} {τ ε : ℝ} (hε : 0 < ε)
    (hq : ((τ, (0 : ℂ)) : E0) ∈ ψ.source)
    (hdev : ∀ ρ ∈ Ioo (0 : ℝ) ε, ∃ θ, Polar (ψ (τ, (ρ : ℂ))) θ ∧
      nullToMink (lift (ψ (τ, (ρ : ℂ))) θ) = g • nullToMink (2 * τ - ρ, ρ, 0)) :
    ∃ b, g • nullToMink (2 * τ, 0, 0) = nullToMink (b, 0, 0) := by
  set q : E0 := (τ, (0 : ℂ)) with hqdef
  have hqa : q ∈ axis := show q.2 = 0 from rfl
  have hψq : ψ q ∈ axis := by
    by_contra h
    have h' : ψ q ∈ Reg (Flat.isom 2) (Minkowski 2) E0 := by rw [reg_eq]; exact h
    have h'' := (hψ.mem_reg_iff hq).2 h'
    rw [reg_eq] at h''
    exact h'' hqa
  let xρ : ℝ → E0 := fun ρ => (τ, (ρ : ℂ))
  have hxc : Continuous xρ := continuous_const.prodMk Complex.continuous_ofReal
  have hx0 : xρ 0 = q := by simp [xρ, hqdef]
  let F : ℝ → ℝ × ℝ × ℝ := fun ρ => nullToMink.symm (g • nullToMink (2 * τ - ρ, ρ, 0))
  have hFc : Continuous F := by
    have h1 : Continuous fun ρ : ℝ => ((2 * τ - ρ, ρ, (0 : ℝ)) : ℝ × ℝ × ℝ) := by fun_prop
    exact nullToMinkHomeomorph.symm.continuous.comp
      ((continuous_const_smul g).comp (nullToMinkHomeomorph.continuous.comp h1))
  have hψc : ContinuousAt (fun ρ => ψ (xρ ρ)) 0 :=
    (ψ.continuousAt hq).comp_of_eq hxc.continuousAt hx0
  have heq : ∀ ρ ∈ Ioo (0 : ℝ) ε, (F ρ).2.1 = rad (ψ (xρ ρ)) ∧
      nullQ (F ρ) = rad (ψ (xρ ρ)) ^ 2 - 2 * (ψ (xρ ρ)).1 * rad (ψ (xρ ρ)) := by
    intro ρ hρ
    obtain ⟨θ, -, h⟩ := hdev ρ hρ
    have hF : F ρ = lift (ψ (xρ ρ)) θ := by
      show nullToMink.symm _ = _
      rw [← h, LinearEquiv.symm_apply_apply]
    rw [hF]
    exact ⟨rfl, nullQ_lift _ _⟩
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 ε := Ioo_mem_nhdsGT hε
  have hr : ContinuousAt (fun ρ => rad (ψ (xρ ρ))) 0 := continuous_rad.continuousAt.comp hψc
  have ht : ContinuousAt (fun ρ => (ψ (xρ ρ)).1) 0 := continuous_fst.continuousAt.comp hψc
  have h1 := eq_of_eventuallyEq_of_continuousAt hl hFc.snd.fst.continuousAt hr
    (hev.mono fun ρ hρ => (heq ρ hρ).1)
  have h2 := eq_of_eventuallyEq_of_continuousAt hl
    (f := fun ρ => nullQ (F ρ))
    (g := fun ρ => rad (ψ (xρ ρ)) ^ 2 - 2 * (ψ (xρ ρ)).1 * rad (ψ (xρ ρ)))
    ((hFc.snd.snd.pow 2).sub (hFc.fst.mul hFc.snd.fst)).continuousAt
    ((hr.pow 2).sub ((continuousAt_const.mul ht).mul hr)) (hev.mono fun ρ hρ => (heq ρ hρ).2)
  simp only [hx0, rad_eq_zero.2 hψq] at h1 h2
  have hc : (F 0).2.2 = 0 := by
    simp only [nullQ, h1, mul_zero, sub_zero] at h2
    norm_num at h2
    exact h2
  refine ⟨(F 0).1, ?_⟩
  have e : g • nullToMink (2 * τ, 0, 0) = nullToMink (F 0) := by
    show _ = nullToMink (nullToMink.symm _)
    rw [LinearEquiv.apply_symm_apply, sub_zero]
  rw [e]
  exact congrArg nullToMink (Prod.ext rfl (Prod.ext h1 hc))

/-! ### The developed map on the slit box, and `μ = 1` -/

/-- **Reading off `ψ` from its development** through `y ↦ B_μ(H_u y) + (s, 0, 0)`:
`ψ(τ, re^{iθ}) = (μτ + (r/μ − μr)/2 + s/2, (r/μ) e^{iμ(θ + u)})` (BTZ_1's `h_ℓ`, l.369, composed
with a rotation and a translation). -/
theorem eq_of_dev {g : Flat.isom 2} {μ u s : ℝ} (hμ : 0 < μ)
    (hgf : ∀ y : ℝ × ℝ × ℝ, g • nullToMink y =
      nullToMink (μ * (y.1 - 2 * u * y.2.2 + u ^ 2 * y.2.1) + s, y.2.1 / μ, y.2.2 - u * y.2.1))
    {x z : E0} (hx : x.2 ≠ 0) {θ : ℝ} (hθ : Polar z θ)
    (h : nullToMink (lift z θ) = g • nullToMink (lift x (arg x.2))) :
    z = (μ * x.1 + (rad x / μ - μ * rad x) / 2 + s / 2,
      ((rad x / μ : ℝ) : ℂ) * cexp (((μ * (arg x.2 + u) : ℝ) : ℂ) * I)) := by
  rw [hgf] at h
  have h' := nullToMink.injective h
  rw [lift_eq, lift_eq] at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨e1, e2, e3⟩ := h'
  have hr : 0 < rad x := rad_pos.2 hx
  have e3' : rad z * θ = rad x * (arg x.2 + u) := by linarith
  have hθ' : θ = μ * (arg x.2 + u) := by
    refine mul_left_cancel₀ hr.ne' ?_
    calc rad x * θ = (rad x / μ * θ) * μ := by field_simp
      _ = (rad z * θ) * μ := by rw [e2]
      _ = rad x * (μ * (arg x.2 + u)) := by rw [e3']; ring
  have k : rad x / μ * (μ * (arg x.2 + u)) ^ 2 = μ * rad x * (arg x.2 + u) ^ 2 := by
    field_simp
  rw [e2, hθ', k] at e1
  refine Prod.ext ?_ ?_
  · show z.1 = _
    linear_combination e1 / 2
  · show z.2 = _
    rw [hθ, e2, hθ']

theorem norm_polarC {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) : ‖(ρ : ℂ) * cexp ((θ : ℂ) * I)‖ = ρ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ]

theorem arg_polarC {ρ : ℝ} (hρ : 0 < ρ) {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) :
    arg ((ρ : ℂ) * cexp ((θ : ℂ) * I)) = θ := by
  rw [Complex.exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I hρ hθ

theorem polarC_mem_slitPlane {ρ : ℝ} (hρ : 0 < ρ) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    (ρ : ℂ) * cexp ((θ : ℂ) * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg, arg_polarC hρ ⟨hθ.1, hθ.2.le⟩]
  exact ⟨hθ.2.ne, mul_ne_zero (ofReal_ne_zero.2 hρ.ne') (Complex.exp_ne_zero _)⟩

theorem mem_ball_of_axis' {p : E0} (hp0 : p.2 = 0) {ε τ : ℝ} (hτ : τ ∈ Metric.ball p.1 ε)
    {w : ℂ} (hw : ‖w‖ < ε) : ((τ, w) : E0) ∈ Metric.ball p ε := by
  rw [Metric.mem_ball, Prod.dist_eq, hp0, dist_zero_right]
  exact max_lt hτ hw

theorem mem_ball_of_axis {p : E0} (hp0 : p.2 = 0) {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : ‖w‖ < ε) :
    ((p.1, w) : E0) ∈ Metric.ball p ε :=
  mem_ball_of_axis' hp0 (Metric.mem_ball_self hε) hw

/-- **`μ = 1`**: for `μ > 1` the map is not injective on the slit box, for `μ < 1` it does not
extend continuously across the slit (`e^{2πiμ} ≠ 1`). -/
theorem mu_eq_one {ψ : OpenPartialHomeomorph E0 E0} {p : E0} {ε : ℝ} (hε : 0 < ε)
    (hball : Metric.ball p ε ⊆ ψ.source) {μ u s : ℝ} (hμ : 0 < μ)
    (hform : ∀ x : E0, x.1 ∈ Metric.ball p.1 ε → x.2 ∈ Metric.ball (0 : ℂ) ε →
      x.2 ∈ slitPlane → ψ x = (μ * x.1 + (rad x / μ - μ * rad x) / 2 + s / 2,
        ((rad x / μ : ℝ) : ℂ) * cexp (((μ * (arg x.2 + u) : ℝ) : ℂ) * I)))
    (hp0 : p.2 = 0) : μ = 1 := by
  have hρ : 0 < ε / 2 := by positivity
  set ρ := ε / 2 with hρdef
  have hρε : ρ < ε := by linarith
  have hval : ∀ θ ∈ Ioo (-π) π, ψ (p.1, (ρ : ℂ) * cexp ((θ : ℂ) * I)) =
      (μ * p.1 + (ρ / μ - μ * ρ) / 2 + s / 2,
        ((ρ / μ : ℝ) : ℂ) * cexp (((μ * (θ + u) : ℝ) : ℂ) * I)) := by
    intro θ hθ
    rw [hform (p.1, (ρ : ℂ) * cexp ((θ : ℂ) * I)) (Metric.mem_ball_self hε)
      (by rw [mem_ball_zero_iff, norm_polarC hρ.le]; exact hρε) (polarC_mem_slitPlane hρ hθ)]
    have hr : rad ((p.1, (ρ : ℂ) * cexp ((θ : ℂ) * I)) : E0) = ρ := norm_polarC hρ.le θ
    have ha : arg ((p.1, (ρ : ℂ) * cexp ((θ : ℂ) * I)) : E0).2 = θ :=
      arg_polarC hρ ⟨hθ.1, hθ.2.le⟩
    rw [hr, ha]
  have hpi := Real.pi_pos
  rcases lt_trichotomy μ 1 with hlt | heq | hgt
  · -- `μ < 1`: no continuous extension across the slit
    exfalso
    let z₀ : E0 := (p.1, -(ρ : ℂ))
    have hz₀ : z₀ ∈ ψ.source := hball (mem_ball_of_axis hp0 hε (by
      rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hρ.le]; exact hρε))
    let w : ℝ → E0 := fun θ => (p.1, (ρ : ℂ) * cexp ((θ : ℂ) * I))
    have hw : Continuous w := by fun_prop
    have hwπ : w π = z₀ := by
      show ((p.1, (ρ : ℂ) * cexp ((π : ℂ) * I)) : E0) = (p.1, -(ρ : ℂ))
      rw [Complex.exp_pi_mul_I, mul_neg_one]
    have hwπ' : w (-π) = z₀ := by
      show ((p.1, (ρ : ℂ) * cexp (((-π : ℝ) : ℂ) * I)) : E0) = (p.1, -(ρ : ℂ))
      rw [show (((-π : ℝ) : ℂ) * I) = -((π : ℂ) * I) by push_cast; ring, Complex.exp_neg,
        Complex.exp_pi_mul_I]
      norm_num
    let G : ℝ → E0 := fun θ => (μ * p.1 + (ρ / μ - μ * ρ) / 2 + s / 2,
      ((ρ / μ : ℝ) : ℂ) * cexp (((μ * (θ + u) : ℝ) : ℂ) * I))
    have hG : Continuous G := by fun_prop
    have hc1 : ContinuousAt (fun θ => ψ (w θ)) π :=
      (ψ.continuousAt hz₀).comp_of_eq hw.continuousAt hwπ
    have hc2 : ContinuousAt (fun θ => ψ (w θ)) (-π) :=
      (ψ.continuousAt hz₀).comp_of_eq hw.continuousAt hwπ'
    have hev1 : ∀ᶠ θ in 𝓝[<] π, θ ∈ Ioo (-π) π := Ioo_mem_nhdsLT (by linarith)
    have hev2 : ∀ᶠ θ in 𝓝[>] (-π), θ ∈ Ioo (-π) π := Ioo_mem_nhdsGT (by linarith)
    have hE1 := eq_of_eventuallyEq_of_continuousAt (l := 𝓝[<] π) nhdsWithin_le_nhds hc1
      hG.continuousAt (hev1.mono fun θ hθ => hval θ hθ)
    have hE2 := eq_of_eventuallyEq_of_continuousAt (l := 𝓝[>] (-π)) nhdsWithin_le_nhds hc2
      hG.continuousAt (hev2.mono fun θ hθ => hval θ hθ)
    simp only [hwπ, hwπ'] at hE1 hE2
    have h := congrArg Prod.snd (hE1.symm.trans hE2)
    simp only [G] at h
    have hne : ((ρ / μ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (mul_left_cancel₀ hne h)
    have him := congrArg Complex.im hn
    simp [Complex.mul_im] at him
    have h2 : (μ - n) * (2 * π) = 0 := by linear_combination him
    have hμn : μ = n := by
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · linarith
    have h0 : (0 : ℤ) < n := by exact_mod_cast (hμn ▸ hμ : (0 : ℝ) < n)
    have h1 : n < (1 : ℤ) := by exact_mod_cast (hμn ▸ hlt : (n : ℝ) < 1)
    omega
  · exact heq
  · -- `μ > 1`: two points of the slit box with one image
    exfalso
    have hlt : π / μ < π := div_lt_self hpi hgt
    have hpos : 0 < π / μ := by positivity
    have hθ₁ : -π / μ ∈ Ioo (-π) π := by
      rw [neg_div]; exact ⟨by linarith, by linarith⟩
    have hθ₂ : π / μ ∈ Ioo (-π) π := ⟨by linarith, hlt⟩
    have heq' : ψ (p.1, (ρ : ℂ) * cexp (((-π / μ : ℝ) : ℂ) * I)) =
        ψ (p.1, (ρ : ℂ) * cexp (((π / μ : ℝ) : ℂ) * I)) := by
      rw [hval _ hθ₁, hval _ hθ₂]
      refine Prod.ext rfl ?_
      show ((ρ / μ : ℝ) : ℂ) * cexp (((μ * (-π / μ + u) : ℝ) : ℂ) * I) =
        ((ρ / μ : ℝ) : ℂ) * cexp (((μ * (π / μ + u) : ℝ) : ℂ) * I)
      have hμ' : μ ≠ 0 := hμ.ne'
      rw [show μ * (π / μ + u) = μ * (-π / μ + u) + 2 * π by field_simp; ring]
      congr 1
      exact Complex.exp_eq_exp_iff_exists_int.2 ⟨-1, by push_cast; ring⟩
    have hmem : ∀ θ : ℝ, ((p.1, (ρ : ℂ) * cexp ((θ : ℂ) * I)) : E0) ∈ ψ.source := fun θ =>
      hball (mem_ball_of_axis hp0 hε (by rw [norm_polarC hρ.le]; exact hρε))
    have hinj := ψ.injOn (hmem _) (hmem _) heq'
    have harg := congrArg (fun x : E0 => arg x.2) hinj
    simp only at harg
    rw [arg_polarC hρ ⟨hθ₁.1, hθ₁.2.le⟩, arg_polarC hρ ⟨hθ₂.1, hθ₂.2.le⟩, neg_div] at harg
    linarith

/-- The slit box is dense in the ball about an axis point. -/
theorem ball_subset_closure_slitBox {p : E0} (hp0 : p.2 = 0) {ε : ℝ} :
    Metric.ball p ε ⊆ closure (Metric.ball p.1 ε ×ˢ (Metric.ball (0 : ℂ) ε ∩ slitPlane)) := by
  intro z hz
  rw [Metric.mem_ball, Prod.dist_eq, hp0] at hz
  have hz1 : dist z.1 p.1 < ε := lt_of_le_of_lt (le_max_left _ _) hz
  have hz2 : ‖z.2‖ < ε := by
    have h := lt_of_le_of_lt (le_max_right _ _) hz
    rwa [dist_zero_right] at h
  rw [Metric.mem_closure_iff]
  intro δ hδ
  by_cases hzs : z.2 ∈ slitPlane
  · exact ⟨z, ⟨hz1, mem_ball_zero_iff.2 hz2, hzs⟩, by rw [dist_self]; exact hδ⟩
  · have him : z.2.im = 0 := by
      rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hzs
      exact hzs.2
    set η := min (δ / 2) ((ε - ‖z.2‖) / 2) with hη
    have hη0 : 0 < η := lt_min (by positivity) (by linarith)
    have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηε : η < ε - ‖z.2‖ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hnη : ‖(η : ℂ) * I‖ = η := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hη0.le]
    refine ⟨(z.1, z.2 + (η : ℂ) * I), ⟨hz1, ?_, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff]
      calc ‖z.2 + (η : ℂ) * I‖ ≤ ‖z.2‖ + ‖(η : ℂ) * I‖ := norm_add_le _ _
        _ < ε := by rw [hnη]; linarith
    · rw [mem_slitPlane_iff]
      right
      simp [him, hη0.ne']
    · rw [Prod.dist_eq, dist_self, Complex.dist_eq, sub_add_cancel_left, norm_neg, hnη]
      exact max_lt hδ hηδ

/-! ### `prop:isom` at `α = β = 0`, locally, and (b′) at `E₀` -/

/-- **BTZ_1's `prop:isom` at `α = β = 0`, local form**: near an axis point of its source, an a.e.
isomorphism chart `ψ : E₀ ⇀ E₀` is a rotation about the axis after a translation along it. -/
theorem exists_eqOn_rotE0_tauShift {ψ : OpenPartialHomeomorph E0 E0}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {p : E0} (hp : p ∈ ψ.source)
    (hpa : p ∈ axis) :
    ∃ φ t : ℝ, ∃ O : Opens E0, p ∈ O ∧ (O : Set E0) ⊆ ψ.source ∧
      ∀ x ∈ O, ψ x = rotE0 φ (tauShift t x) := by
  have hp0 : p.2 = 0 := hpa
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ψ.open_source p hp
  set T : Set E0 := Metric.ball p.1 ε ×ˢ (Metric.ball (0 : ℂ) ε ∩ slitPlane) with hTdef
  have hTball : T ⊆ Metric.ball p ε := fun x hx =>
    mem_ball_of_axis' hp0 hx.1 (mem_ball_zero_iff.1 hx.2.1)
  have hTs : T ⊆ ψ.source := hTball.trans hball
  have hTsl : ∀ x ∈ T, x.2 ∈ slitPlane := fun x hx => hx.2.2
  have hmid : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε ∩ slitPlane := by
    refine ⟨?_, Complex.ofReal_mem_slitPlane.2 (by positivity)⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hT : IsPreconnected T := by
    have hD : IsPreconnected (Metric.ball (0 : ℂ) ε ∩ slitPlane) :=
      ((((convex_ball (0 : ℂ) ε).starConvex hmid.1).inter
        (Complex.starConvex_ofReal_slitPlane (by positivity))).isPathConnected
        hmid).isConnected.isPreconnected
    exact (convex_ball p.1 ε).isPreconnected.prod hD
  have hx₀ : ((p.1, ((ε / 2 : ℝ) : ℂ)) : E0) ∈ T := ⟨Metric.mem_ball_self hε, hmid⟩
  obtain ⟨g, hg⟩ := exists_isom_dev hψ hT hTs hTsl hx₀
  -- `g` preserves the developed axis
  have hline : ∀ τ ∈ Metric.ball p.1 ε,
      ∃ b, g • nullToMink (2 * τ, 0, 0) = nullToMink (b, 0, 0) := by
    intro τ hτ
    refine smul_null_line hψ hε (hball (mem_ball_of_axis' hp0 hτ (by simpa using hε))) ?_
    intro ρ hρ
    have hxT : ((τ, (ρ : ℂ)) : E0) ∈ T := ⟨hτ, by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hρ.1.le]; exact hρ.2,
      Complex.ofReal_mem_slitPlane.2 hρ.1⟩
    obtain ⟨θ, h1, h2⟩ := hg _ hxT
    refine ⟨θ, h1, ?_⟩
    rw [h2]
    congr 2
    have hrad : rad ((τ, (ρ : ℂ)) : E0) = ρ := by
      show ‖(ρ : ℂ)‖ = ρ
      rw [Complex.norm_real, Real.norm_of_nonneg hρ.1.le]
    rw [lift_eq, hrad, show arg ((τ, (ρ : ℂ)) : E0).2 = 0 from
      Complex.arg_ofReal_of_nonneg hρ.1.le]
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;> simp
  -- the structure of `g`
  obtain ⟨b₁, hb₁⟩ := hline p.1 (Metric.mem_ball_self hε)
  obtain ⟨b₂, hb₂⟩ := hline (p.1 + ε / 2) (by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith)
  obtain ⟨μ, u, s, hμ, hgf⟩ := isom_of_null_line g
    (show 2 * p.1 ≠ 2 * (p.1 + ε / 2) by intro h; linarith) hb₁ hb₂
  -- `ψ` on the slit box
  have hform : ∀ x : E0, x.1 ∈ Metric.ball p.1 ε → x.2 ∈ Metric.ball (0 : ℂ) ε →
      x.2 ∈ slitPlane → ψ x = (μ * x.1 + (rad x / μ - μ * rad x) / 2 + s / 2,
        ((rad x / μ : ℝ) : ℂ) * cexp (((μ * (arg x.2 + u) : ℝ) : ℂ) * I)) := by
    intro x h1 h2 h3
    obtain ⟨θ, hθ, h⟩ := hg x ⟨h1, h2, h3⟩
    exact eq_of_dev hμ hgf (slitPlane_ne_zero h3) hθ h
  have hμ1 : μ = 1 := mu_eq_one hε hball hμ hform hp0
  subst hμ1
  refine ⟨u, s / 2, ⟨Metric.ball p ε, Metric.isOpen_ball⟩, Metric.mem_ball_self hε, hball, ?_⟩
  have hR : Continuous fun x : E0 => rotE0 u (tauShift (s / 2) x) :=
    (rotE0 u).continuous.comp (tauShift _).continuous
  have hEqT : EqOn ψ (fun x => rotE0 u (tauShift (s / 2) x)) T := by
    intro x hx
    rw [hform x hx.1 hx.2.1 hx.2.2]
    show _ = ((x.1 + s / 2, cexp ((u : ℂ) * I) * x.2) : E0)
    refine Prod.ext (by simp only [one_mul, div_one, sub_self, zero_div, add_zero]) ?_
    simp only [div_one, one_mul]
    rw [show rad x = ‖x.2‖ from rfl]
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I x.2]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  exact fun x hx => hEqT.of_subset_closure (ψ.continuousOn.mono hball) hR.continuousOn hTball
    (ball_subset_closure_slitBox hp0) hx

/-- A rotation after a translation is a chart isomorphism of `E₀`. -/
theorem chartIso_rotE0_tauShift (φ t : ℝ) :
    ChartIso E0.causality E0.causality ((tauShift t).trans (rotE0 φ)).toOpenPartialHomeomorph :=
  chartIso_of_homeo _
    (fun x y => by
      show Le (rotE0 φ (tauShift t x)) (rotE0 φ (tauShift t y)) ↔ Le x y
      rw [le_rotE0_iff, le_tauShift_iff])
    (fun x y => by
      show Lt (rotE0 φ (tauShift t x)) (rotE0 φ (tauShift t y)) ↔ Lt x y
      rw [lt_rotE0_iff, lt_tauShift_iff])

/-- Near an axis point of its source, the causality transported by `ψ` is that of `E₀`. -/
theorem agreeOn_of_mem_axis {ψ : OpenPartialHomeomorph E0 E0}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) {p : E0} (hp : p ∈ ψ.source)
    (hpa : p ∈ axis) :
    ∃ O : Opens E0, p ∈ O ∧ AgreeOn E0.causality (E0.causality.chartTransport ψ) O := by
  obtain ⟨φ, t, O, hpO, hOs, heq⟩ := exists_eqOn_rotE0_tauShift hψ hp hpa
  exact ⟨O, hpO, (chartIso_refl E0.causality).agreeOn_of_localIso
    (E0.causality.chartTransport_chartIso ψ) (chartIso_rotE0_tauShift φ t)
    (fun z hz => ⟨mem_univ z, hOs hz⟩) (fun z hz => ⟨mem_univ _, (heq z hz).symm⟩)⟩

/-- **(b′) at `E₀`** (OQ-64): every a.e. isomorphism chart `ψ : E₀ ⇀ E₀` of `E0GX.singularGX`,
its source meeting the axis or not, is a chart isomorphism of `E0.causality`. -/
theorem chartIso_of_isAEChart {ψ : OpenPartialHomeomorph E0 E0}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) : ChartIso E0.causality E0.causality ψ := by
  have hT := E0.causality.chartTransport_chartIso ψ
  have hTmin : (E0.causality.chartTransport ψ).AbsolutelyMinimalOn (chartSource ψ) :=
    hT.absolutelyMinimalOn le_rfl (E0.absolutelyMinimalOn _)
  have hloc : ∀ x ∈ chartSource ψ,
      ∃ O : Opens E0, x ∈ O ∧ AgreeOn E0.causality (E0.causality.chartTransport ψ) O := by
    intro x hx
    by_cases hxa : x ∈ axis
    · exact agreeOn_of_mem_axis hψ hx hxa
    · have hx0 : x.2 ≠ 0 := hxa
      have hc := sectorAtlas_subset_aeAtlas (sectorChart_mem_sectorAtlas hx0)
      exact (chartIso_of_mem_aeAtlas _ hc).agreeOn_of_isAEChart Flat.isom_strongMorphism
        chartIso_of_mem_aeAtlas hc hψ hT (mem_sector_self hx0) hx
  have hloc' : ∀ x ∈ chartSource ψ,
      ∃ O : Opens E0, x ∈ O ∧ AgreeOn (E0.causality.chartTransport ψ) E0.causality O :=
    fun x hx => by
      obtain ⟨O, hxO, hO⟩ := hloc x hx
      exact ⟨O, hxO, hO.symm⟩
  refine hT.congr fun V hV x y => ?_
  have h1 := imp_of_agree_locally (E0.absolutelyMinimalOn (chartSource ψ)) hloc hV (x := x) (y := y)
  have h2 := imp_of_agree_locally hTmin hloc' hV (x := x) (y := y)
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

/-! ### Consequences: `E₀`-manifolds, and the hypothesis `hiso` at `o = o′ = E₀` -/

/-- **`prop:GX_sing_espace_temps_topo` at the single model `E₀`** (DEC-25): a singular
`(Isom(𝐌³), 𝐌³)`-manifold whose singular points lie in a.e. isomorphism charts into `E₀` carries
an absolutely minimal causality for which every chart of its maximal a.e. atlas and every chart
into `E₀` is an isomorphism, unique among absolutely minimal causalities with some such chart an
isomorphism at each point. No hypothesis on the model is left. -/
theorem existsUnique_causality_e0 {M : Type u} [TopologicalSpace M]
    [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
    (hcov : ∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) M, ∃ e : OpenPartialHomeomorph M E0,
      IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source) :
    ∃ C : Causality M, (∀ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, ChartIso C (minkowski 2) e) ∧
      (∀ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e →
        ChartIso C E0.causality e) ∧
      C.AbsolutelyMinimal ∧
      ∀ C' : Causality M, C'.AbsolutelyMinimal →
        (∀ x : M, (∃ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) M, x ∈ e.source ∧
            ChartIso C' (minkowski 2) e) ∨
          ∃ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
            x ∈ e.source ∧ ChartIso C' E0.causality e) →
        C' = C := by
  obtain ⟨C, hCX, hCY, hmin, huniq⟩ := existsUnique_causality_singularGX_dec25
    (Xα := fun _ : Unit => E0) (minkowski 2) (fun _ => E0.causality)
    minkowski_causallyArcConnected Flat.isom_strongMorphism (fun _ => E0.causallyArcConnected)
    (fun _ => chartIso_of_mem_aeAtlas) (fun _ _ _ hψ => chartIso_of_isAEChart hψ)
    (fun x hx => by
      obtain ⟨e, he, hxe⟩ := hcov x hx
      exact ⟨(), e, he, hxe⟩)
  refine ⟨C, hCX, fun e he => hCY () e he, hmin, fun C' hmin' hloc => huniq C' hmin' fun x => ?_⟩
  rcases hloc x with h | ⟨e, he, hxe, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨(), e, he, hxe, h'⟩

/-- **The hypothesis `hiso` of `massA_singular_dec25_models` at `o = o′ = none` (`E₀ → E₀`)**,
for any family of singular structures on the models whose value at `E₀` is `E0GX.singularGX`. -/
theorem hiso_massAModel_none
    [inst : ∀ o, SingularGXStructure (Flat.isom 2) (Minkowski 2) (MassAModel o)]
    (h0 : inst none = E0GX.singularGX)
    (ψ : OpenPartialHomeomorph (MassAModel none) (MassAModel none))
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ChartIso (massAModelCausality none) (massAModelCausality none) ψ := by
  have hψ' : @IsAEChart (Flat.isom 2) (Minkowski 2) _ _ _ E0 _ E0GX.singularGX E0 _
      E0GX.singularGX ψ := h0 ▸ hψ
  exact chartIso_of_isAEChart hψ'

/-! ### Non-vacuity: the rotations are a.e. isomorphism charts through the axis -/

/-- A map `w ↦ (w.1, ζ w.2)`, `‖ζ‖ = 1`, induces a `(G,X)`-morphism on every open set of regular
points: it reads in sector charts as one holonomy `hol s`. -/
theorem isRegularOn_mulLeft {f : E0 → E0} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hf : ∀ w, f w = (w.1, ζ * w.2)) {S : Set E0} (hS : IsOpen S) :
    IsRegularOn (Flat.isom 2) (aeAtlas (Flat.isom 2) (Minkowski 2) E0)
      (aeAtlas (Flat.isom 2) (Minkowski 2) E0) f (S ∩ Reg (Flat.isom 2) (Minkowski 2) E0) := by
  have hA := (isMaximalAEAtlas_aeAtlas (Flat.isom 2) (Minkowski 2) E0).1.1
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ
    exact zero_ne_one hζ
  have hcont : Continuous f := by
    have e : f = fun w => (w.1, ζ * w.2) := funext hf
    rw [e]
    fun_prop
  have hreg : ∀ w, f w ∈ Reg (Flat.isom 2) (Minkowski 2) E0 ↔
      w ∈ Reg (Flat.isom 2) (Minkowski 2) E0 := fun w => by
    rw [reg_eq, mem_compl_iff, mem_compl_iff, hf]
    show ¬ ζ * w.2 = 0 ↔ ¬ w.2 = 0
    rw [mul_eq_zero, not_or]
    exact ⟨fun h => h.2, fun h => ⟨hζ0, h⟩⟩
  refine IsRegularOn.of_exists hA hA (hS.inter (isOpen_reg _ _ _)) (fun x hx => hx.2)
    (fun x hx => (hreg x).2 hx.2) hcont.continuousOn fun x hx => ?_
  have hx0 : x.2 ≠ 0 := by
    have h := hx.2
    rw [reg_eq] at h
    exact h
  have hfx0 : (f x).2 ≠ 0 := by rw [hf]; exact mul_ne_zero hζ0 hx0
  refine ⟨sectorChart x hx0, sectorAtlas_subset_aeAtlas (sectorChart_mem_sectorAtlas hx0),
    sectorChart (f x) hfx0, sectorAtlas_subset_aeAtlas (sectorChart_mem_sectorAtlas hfx0),
    mem_sector_self hx0, mem_sector_self hfx0, hol (arg (f x).2 - arg x.2),
    Eventually.of_forall fun w => ?_⟩
  have hlift : ∀ θ, lift (f w) θ = lift w θ := fun θ => by
    have hr : rad (f w) = rad w := by
      show ‖(f w).2‖ = ‖w.2‖
      rw [hf, norm_mul, hζ, one_mul]
    rw [lift_eq, lift_eq, hr, hf]
  have hdiv : (f w).2 / (f x).2 = w.2 / x.2 := by
    rw [hf, hf]
    exact mul_div_mul_left _ _ hζ0
  show nullToMink (lift (f w) (arg (f x).2 + arg ((f w).2 / (f x).2))) =
    hol _ • nullToMink (lift w (arg x.2 + arg (w.2 / x.2)))
  rw [hlift, hdiv, hol_smul_nullToMink, ← lift_add_angle]
  congr 2
  ring

/-- **The rotations of `E₀` about its axis are a.e. isomorphism charts**, with source `E₀`. -/
theorem isAEChart_rotE0 (φ : ℝ) :
    IsAEChart (Flat.isom 2) (Minkowski 2) (rotE0 φ).toOpenPartialHomeomorph := by
  have h1 := isRegularOn_mulLeft (f := rotE0 φ) (Complex.norm_exp_ofReal_mul_I φ)
    (fun w => rfl) isOpen_univ
  have hζ : ‖cexp (-(φ : ℂ) * I)‖ = 1 := by
    rw [show -(φ : ℂ) * I = ((-φ : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 := isRegularOn_mulLeft (f := (rotE0 φ).symm) hζ (fun w => rfl) isOpen_univ
  exact ⟨h1, h2⟩

/-- A map `w ↦ (w.1 + t, w.2)` induces a `(G,X)`-morphism on every open set of regular points: it
reads in sector charts as the translation by `D(t, 0, ·) = nullToMink (2t, 0, 0)`. -/
theorem isRegularOn_addFst {f : E0 → E0} {t : ℝ} (hf : ∀ w, f w = (w.1 + t, w.2)) {S : Set E0}
    (hS : IsOpen S) :
    IsRegularOn (Flat.isom 2) (aeAtlas (Flat.isom 2) (Minkowski 2) E0)
      (aeAtlas (Flat.isom 2) (Minkowski 2) E0) f (S ∩ Reg (Flat.isom 2) (Minkowski 2) E0) := by
  have hA := (isMaximalAEAtlas_aeAtlas (Flat.isom 2) (Minkowski 2) E0).1.1
  have hcont : Continuous f := by
    have e : f = fun w => (w.1 + t, w.2) := funext hf
    rw [e]
    fun_prop
  have hreg : ∀ w, f w ∈ Reg (Flat.isom 2) (Minkowski 2) E0 ↔
      w ∈ Reg (Flat.isom 2) (Minkowski 2) E0 := fun w => by
    rw [reg_eq, mem_compl_iff, mem_compl_iff, hf]
    rfl
  refine IsRegularOn.of_exists hA hA (hS.inter (isOpen_reg _ _ _)) (fun x hx => hx.2)
    (fun x hx => (hreg x).2 hx.2) hcont.continuousOn fun x hx => ?_
  have hx0 : x.2 ≠ 0 := by
    have h := hx.2
    rw [reg_eq] at h
    exact h
  have hfx0 : (f x).2 ≠ 0 := by rw [hf]; exact hx0
  let v : Minkowski 2 := nullToMink (2 * t, 0, 0)
  refine ⟨sectorChart x hx0, sectorAtlas_subset_aeAtlas (sectorChart_mem_sectorAtlas hx0),
    sectorChart (f x) hfx0, sectorAtlas_subset_aeAtlas (sectorChart_mem_sectorAtlas hfx0),
    mem_sector_self hx0, mem_sector_self hfx0,
    ⟨AffineEquiv.constVAdd ℝ (Minkowski 2) v, Flat.constVAdd_mem_isom v⟩,
    Eventually.of_forall fun w => ?_⟩
  show nullToMink (lift (f w) (arg (f x).2 + arg ((f w).2 / (f x).2))) =
    v +ᵥ nullToMink (lift w (arg x.2 + arg (w.2 / x.2)))
  rw [hf, hf, vadd_eq_add, ← map_add, lift_eq, lift_eq]
  congr 1
  have hr : rad ((w.1 + t, w.2) : E0) = rad w := rfl
  rw [hr]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- **The translations of `E₀` along its axis are a.e. isomorphism charts**, with source `E₀`. -/
theorem isAEChart_tauShift (t : ℝ) :
    IsAEChart (Flat.isom 2) (Minkowski 2) (tauShift t).toOpenPartialHomeomorph := by
  have h1 := isRegularOn_addFst (f := tauShift t) (fun w => rfl) isOpen_univ
  have h2 := isRegularOn_addFst (f := (tauShift t).symm) (t := -t)
    (fun w => by
      show ((w.1 - t, w.2) : E0) = (w.1 + -t, w.2)
      rw [sub_eq_add_neg]) isOpen_univ
  exact ⟨h1, h2⟩

/-- **A rotation after a translation is an a.e. isomorphism chart** of `E₀`: the converse of
`exists_eqOn_rotE0_tauShift`, so near an axis point the a.e. isomorphism charts are exactly the
restrictions of `Isom(E₀)` (BTZ_1's `Isom(𝔼^{1,2}_0)`, l.372–373). -/
theorem isAEChart_rotE0_tauShift (φ t : ℝ) :
    IsAEChart (Flat.isom 2) (Minkowski 2)
      ((tauShift t).trans (rotE0 φ)).toOpenPartialHomeomorph := by
  rw [Homeomorph.trans_toOpenPartialHomeomorph]
  exact (isAEChart_tauShift t).trans (isAEChart_rotE0 φ)

/-- **Non-vacuity** (kb/0011). (1) Every rotation after a translation `rotE0 φ ∘ tauShift t` is
an a.e. isomorphism chart whose source meets the axis, so `chartIso_of_isAEChart` applies to it
at a singular point. (2) `E₀` itself is an `E₀`-manifold with a singular point, its singular
locus covered by the chart `refl`; its causality is the natural one of
`existsUnique_causality_e0` (every chart of the maximal a.e. atlas and every chart into `E₀` an
isomorphism, absolutely minimal). -/
theorem nonvacuous (φ t : ℝ) :
    IsAEChart (Flat.isom 2) (Minkowski 2)
        ((tauShift t).trans (rotE0 φ)).toOpenPartialHomeomorph ∧
      (((tauShift t).trans (rotE0 φ)).toOpenPartialHomeomorph.source ∩ axis).Nonempty ∧
      ChartIso E0.causality E0.causality
        ((tauShift t).trans (rotE0 φ)).toOpenPartialHomeomorph ∧
      (Sing (Flat.isom 2) (Minkowski 2) E0).Nonempty ∧
      (∀ x ∈ Sing (Flat.isom 2) (Minkowski 2) E0, ∃ e : OpenPartialHomeomorph E0 E0,
        IsAEChart (Flat.isom 2) (Minkowski 2) e ∧ x ∈ e.source) ∧
      (∀ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) E0, ChartIso E0.causality (minkowski 2) e) ∧
      (∀ e : OpenPartialHomeomorph E0 E0, IsAEChart (Flat.isom 2) (Minkowski 2) e →
        ChartIso E0.causality E0.causality e) ∧
      E0.causality.AbsolutelyMinimal :=
  ⟨isAEChart_rotE0_tauShift φ t, ⟨((0 : ℝ), (0 : ℂ)), mem_univ _, rfl⟩,
    chartIso_of_isAEChart (isAEChart_rotE0_tauShift φ t), sing_nonempty,
    fun x _ => ⟨OpenPartialHomeomorph.refl E0, isAEChart_refl, mem_univ x⟩,
    chartIso_of_mem_aeAtlas, fun _ he => chartIso_of_isAEChart he,
    E0.causallyArcConnected.absolutelyMinimal⟩

/-! ### The reflection `θ ↦ −θ` (OQ-82) -/

/-- **The reflection `z ↦ z̄` of `E₀`** (`θ ↦ −θ`): an isometry of `E₀` that is not an a.e.
isomorphism chart for `Isom(𝐌³) = SO₀(1,2) ⋉ ℝ³` (it develops to a reflection), but would be one
for `O↑(1,2) ⋉ ℝ³` (OQ-82). -/
noncomputable def conjE0 : E0 ≃ₜ E0 where
  toFun x := (x.1, (starRingEnd ℂ) x.2)
  invFun x := (x.1, (starRingEnd ℂ) x.2)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_fst.prodMk (Complex.continuous_conj.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (Complex.continuous_conj.comp continuous_snd)

theorem rad_conjE0 (x : E0) : rad (conjE0 x) = rad x := by
  show ‖(starRingEnd ℂ) x.2‖ = ‖x.2‖
  exact Complex.norm_conj _

theorem polar_conjE0 (x : E0) (θ : ℝ) : Polar (conjE0 x) θ ↔ Polar x (-θ) := by
  unfold Polar
  rw [rad_conjE0]
  show (starRingEnd ℂ) x.2 = _ ↔ _
  have e : (starRingEnd ℂ) ((rad x : ℂ) * cexp (((-θ : ℝ) : ℂ) * I)) =
      (rad x : ℂ) * cexp ((θ : ℂ) * I) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring_nf
  rw [← e]
  exact (starRingEnd ℂ).injective.eq_iff

theorem le_conjE0_iff (x y : E0) : Le (conjE0 x) (conjE0 y) ↔ Le x y := by
  rw [le_iff_closed, le_iff_closed, rad_conjE0, rad_conjE0]
  constructor
  · rintro ⟨θ₁, θ₂, h₁, h₂, h⟩
    refine ⟨-θ₁, -θ₂, (polar_conjE0 x θ₁).1 h₁, (polar_conjE0 y θ₂).1 h₂, ?_⟩
    have e : (-θ₂ - -θ₁) ^ 2 = (θ₂ - θ₁) ^ 2 := by ring
    unfold ClosedLe at h ⊢
    rw [e]
    exact h
  · rintro ⟨θ₁, θ₂, h₁, h₂, h⟩
    refine ⟨-θ₁, -θ₂, (polar_conjE0 x _).2 (by rwa [neg_neg]),
      (polar_conjE0 y _).2 (by rwa [neg_neg]), ?_⟩
    have e : (-θ₂ - -θ₁) ^ 2 = (θ₂ - θ₁) ^ 2 := by ring
    unfold ClosedLe at h ⊢
    rw [e]
    exact h

theorem lt_conjE0_iff (x y : E0) : Lt (conjE0 x) (conjE0 y) ↔ Lt x y := by
  rw [lt_iff_closed, lt_iff_closed, rad_conjE0, rad_conjE0]
  constructor
  · rintro ⟨θ₁, θ₂, h₁, h₂, h⟩
    refine ⟨-θ₁, -θ₂, (polar_conjE0 x θ₁).1 h₁, (polar_conjE0 y θ₂).1 h₂, ?_⟩
    have e : (-θ₂ - -θ₁) ^ 2 = (θ₂ - θ₁) ^ 2 := by ring
    unfold ClosedLt at h ⊢
    rw [e]
    exact h
  · rintro ⟨θ₁, θ₂, h₁, h₂, h⟩
    refine ⟨-θ₁, -θ₂, (polar_conjE0 x _).2 (by rwa [neg_neg]),
      (polar_conjE0 y _).2 (by rwa [neg_neg]), ?_⟩
    have e : (-θ₂ - -θ₁) ^ 2 = (θ₂ - θ₁) ^ 2 := by ring
    unfold ClosedLt at h ⊢
    rw [e]
    exact h

/-- **The reflection is a chart isomorphism of `E₀`**: the a.e. isomorphisms that the reading
`O↑(1,2) ⋉ ℝ³` of OQ-82 would add (a reflection after a rotation and a translation) are causal
isomorphisms too. -/
theorem chartIso_conjE0 :
    ChartIso E0.causality E0.causality conjE0.toOpenPartialHomeomorph :=
  chartIso_of_homeo _ le_conjE0_iff lt_conjE0_iff

/-- **Under `Isom(𝐌³) = SO₀(1,2) ⋉ ℝ³` the reflection is not an a.e. isomorphism chart** of `E₀`:
near the axis point `(0, 0)` it would be a rotation after a translation
(`exists_eqOn_rotE0_tauShift`), which fixes `(0, ρ)` only if it is the identity, while the
reflection moves `(0, iρ)`. (The determinant is where the proof excludes it.) -/
theorem not_isAEChart_conjE0 :
    ¬ IsAEChart (Flat.isom 2) (Minkowski 2) conjE0.toOpenPartialHomeomorph := by
  intro h
  obtain ⟨φ, t, O, hpO, -, heq⟩ :=
    exists_eqOn_rotE0_tauShift h (p := ((0 : ℝ), (0 : ℂ))) (mem_univ _) rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 O.isOpen _ hpO
  have hmem : ∀ w : ℂ, ‖w‖ < δ → (((0 : ℝ), w) : E0) ∈ O := fun w hw =>
    hball (mem_ball_of_axis rfl hδ hw)
  have hρ : 0 < δ / 2 := by positivity
  have h1 := heq _ (hmem ((δ / 2 : ℝ) : ℂ) (by
    rw [Complex.norm_real, Real.norm_of_nonneg hρ.le]; linarith))
  have h2 := heq _ (hmem (((δ / 2 : ℝ) : ℂ) * I) (by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    linarith))
  have e1 := congrArg Prod.snd h1
  have e2 := congrArg Prod.snd h2
  change (starRingEnd ℂ) ((δ / 2 : ℝ) : ℂ) = cexp ((φ : ℂ) * I) * ((δ / 2 : ℝ) : ℂ) at e1
  change (starRingEnd ℂ) (((δ / 2 : ℝ) : ℂ) * I) =
    cexp ((φ : ℂ) * I) * (((δ / 2 : ℝ) : ℂ) * I) at e2
  rw [Complex.conj_ofReal] at e1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I] at e2
  have hρ0 : ((δ / 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hρ.ne'
  have hc : cexp ((φ : ℂ) * I) = 1 :=
    mul_right_cancel₀ hρ0 (by rw [one_mul]; exact e1.symm)
  rw [hc, one_mul] at e2
  have him := congrArg Complex.im e2
  simp at him
  linarith

end BPrimeE0

end Causal
