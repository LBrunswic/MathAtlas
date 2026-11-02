import Causal.Flat.FlatSpacetime
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# `Causal.Flat.Quotient` — quotients `Γ\Ω` of open subsets of Minkowski space

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), the form
of every model of §3–§4 and of every target of §11. No b-label is certified: the quotient
construction is prose in the paper, used without an environment (l.210, l.611–612, l.1204–1209,
l.1279, and as a hypothesis of `blem:suspendre`, l.1836–1838, which this file does not attempt).
Line numbers are those of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`.

> Let $B$ be a flat spacetime, quotient of an open subset $\Omega$ of \mink by a group of
> isometries acting freely and properly discontinuously. (l.1836–1838)

> The quotient space $\Gamma\backslash\Omega$ is then a spacetime, admitting the cosmological
> time function induced by $T$ expressing it as a GH spacetime. The level sets of this time
> function are Cauchy hypersurfaces which are quotients $\Gamma\backslash S_{t}$ (l.1204–1208)

> The most obvious examples of Cauchy-complete MGH spacetimes are simply quotients of \mink
> itself by discrete groups of spacelike translations. (l.209–211)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's `n` is `d + 1`.

## What is proved (no `sorry`)

* **The action and the quotient.** `FlatQuotient.Invariant Γ Ω` (a class: `Γ ≤ isom d` maps the
  open `Ω` into itself; `invariant_iff` is BARBOT-THEOREMS' `(γ • ·) '' Ω = Ω`), the induced
  `MulAction Γ Ω`, and `FlatQuotient Γ Ω := MulAction.orbitRel.Quotient Γ Ω` with the quotient
  topology; `proj`, `proj_eq_proj_iff(')` (fibres are orbits), `proj_surjective`,
  `continuous_proj`, `isOpenMap_proj`.
* **Free and properly discontinuous** are mathlib's `IsCancelSMul Γ Ω` and
  `ProperlyDiscontinuousSMul Γ Ω` **on the subtype `Ω`** (compact sets of `Ω`, not of `𝐌ⁿ`): the
  paper's "acting freely and properly discontinuously" on `Ω` (l.1838). Under them:
  `isQuotientCoveringMap_proj`, `isCoveringMap_proj`, `t2Space` (mathlib's
  `t2Space_of_properlyDiscontinuousSMul_of_t2Space`).
* **`Γ\Ω` is an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold.** The charts are mathlib's
  `MulAction.instChartedSpaceQuotient` (local inverses of `proj` composed with the charts of `Ω`;
  `symm_apply_of_mem_target`, `apply_of_mem_source` read them pointwise), and
  `instHasGroupoid : HasGroupoid (FlatQuotient Γ Ω) (gxGroupoid (isom d) _)`: a transition sends
  each point into its own orbit, so by `eventually_eq_smul` (local constancy, from the
  disjoint-translates neighbourhood `exists_nhds_smul_eq_one`) it is locally one `γ ∈ Γ`.
  `connectedSpace` (when `Ω` is connected) and `toFlatSpacetime` (the bundled `FlatSpacetime`).
* **The projection is a local isometry** (`isLocalIsometry_proj`), hence `isEMorphism_proj`,
  `strongMorphism_proj`, `localIsomorphism_proj` of the flat causalities.
* **`IsQuotientOf M Γ Ω`** (BARBOT-THEOREMS §1), `IsQuotientOf.invariant`, `isQuotientOf` and
  `isQuotientOf_toFlatSpacetime` (the construction satisfies it), and
  `IsQuotientOf.exists_homeomorph` (it determines `M` up to a homeomorphism `Φ`, `Φ ∘ proj = π`).
* **Causal curves lift** (`liftsCausalCurves`): every causal curve of `Γ\Ω` over an interval `I`
  is `proj ∘ c'` for a causal curve `c'` of `Ω` over `I` — mathlib's
  `IsCoveringMap.existsUnique_continuousMap_lifts` on the subtype `I` (contractible, locally
  path-connected: `locPathConnectedSpace_of_ordConnected`), then causality read through the
  local isomorphism.
* **Cauchy surfaces descend** (l.1207–1208): `isCauchySurfaceOn_iff` relates the two readings
  (`(minkowski d).IsCauchySurfaceOn Ω S` and `(flatCausality d Ω).IsCauchySurface`, through
  `isIsometricEmbedding_subtype_val`); `inextensible_of_lift` (a lift of an inextensible curve is
  inextensible when `Γ` acts acausally, `ActsAcausally`), `liftsInextensible`,
  `isCauchySurface_image_of_liftsInextensible`, and **`isCauchySurface_image`**,
  `isCauchySurface_image_of_isCauchySurfaceOn`: under an acausal action, the image of a
  `Γ`-invariant Cauchy surface of `Ω` is a Cauchy surface of `Γ\Ω`; `barbotGH_toFlatSpacetime`.
* **A quotient need not be causal** (`not_isCausal_timeGroup`): `ℤ e₀` (a timelike translation)
  acts freely and properly discontinuously on `𝐌ⁿ` (instances proved), and `ℤ e₀\𝐌ⁿ` is not
  causal; it does not act acausally (`not_actsAcausally_timeGroup`).
* **A witness for the descent** (kb/0011; l.209–211): `ℤ e₁` (a spacelike translation of
  `Minkowski (d + 1)`, `spaceGroup`) acts freely and properly discontinuously (instances proved)
  and acausally (`actsAcausally_spaceGroup`), its generator is not `1`
  (`spaceTranslation_one_ne_one`), the slice `t = 0` is an invariant Cauchy surface
  (`isCauchySurface_slice_top`), so `ℤ e₁\𝐌ⁿ` is GH in Barbot's sense (`barbotGH_spaceGroup`).

## Hypothesis checklist

| paper | here |
|---|---|
| `Ω` an open subset of `𝐌ⁿ` (l.1837) | ✓ carried: `Ω : Opens (Minkowski d)` (BARBOT-THEOREMS' `isOpen` field is the type) |
| `Γ` a group of isometries preserving `Ω` | ✓ carried: `Γ : Subgroup (isom d)`, `[Invariant Γ Ω]` |
| acting freely and properly discontinuously (l.1838) | ✓ carried: `[IsCancelSMul Γ Ω]`, `[ProperlyDiscontinuousSMul Γ Ω]` on the subtype `Ω`; only the statements needing them ask them (T2, covering, charts, groupoid) |
| the quotient is a flat spacetime | ✓ T2, charted, `HasGroupoid`; connected `⇐ Ω` connected; second countability not asked (as in `FlatSpacetime`) |
| level sets descend to Cauchy hypersurfaces (l.1207–1208) | ⚠ strengthened: `ActsAcausally Γ Ω` (no `γ ≠ 1` with `x ≤_Ω γ x`) is added; the paper's setting (a `Γ`-invariant time function) implies it when the time function is strictly increasing along `≤` (true of Barbot's regular cosmological time, l.1184–1187; not given by the library's `IsTimeFunction`, strict on `≪` only), and that implication is not proved here (SCOPE); hypotheses inhabited by `spaceGroup` |

## SCOPE (disclosed)

* **Acausal action.** `isCauchySurface_image` asks `ActsAcausally Γ Ω`. It is used once: two
  points of one orbit on one causal curve of `Ω` would let an extension of the lift project to a
  curve with no new image point (`inextensible_of_lift`). In Barbot's uses `Γ` preserves a time
  function (the cosmological time, l.1184–1187) or a Cauchy surface: then `x ≤ γ x` with
  `γ ≠ 1` is impossible. For a time function `T` this needs `T` strictly increasing on `≤`
  (true of Barbot's regular cosmological time, l.1184–1187; not given by the library's
  `IsTimeFunction`, DEC-10, a strong morphism to the timeline, strict on `≪` only: along a null
  relation `x ≤ γ x` with `T (γ x) = T x` contradicts nothing). Deriving `ActsAcausally` from a
  `Γ`-invariant Cauchy surface needs inextensible extensions of causal curves (`CurvesExtend`),
  not proved for open subsets of `𝐌ⁿ` here. The freeness and proper discontinuity alone do **not** suffice: `ℤ e₀\𝐌ⁿ` is not
  causal (`not_isCausal_timeGroup`). An achronal action (no `x ≪ γ x`) would not suffice either
  for the argument: a null translation sends points to their causal, not chronological, future.
  The hypotheses are inhabited by a nontrivial group: `spaceGroup` (`barbotGH_spaceGroup`).
* **Causality of `Γ\Ω`** under `ActsAcausally` is **not proved**: it needs the lifting of the
  `≤` relation on `⊤` of the quotient (through chains of local relations), not only of causal
  curves; `not_isCausal_timeGroup` shows some hypothesis on the action is needed.
* **GH of `Γ\Ω`.** Proved: Barbot's GH (a Cauchy surface) under an acausal action with an
  invariant Cauchy surface (`barbotGH_toFlatSpacetime`). Not proved: ETT's `GH` (causal + compact
  diamonds) of the quotient; it would follow from Barbot's GH through `theo:geroch` (iii)⇒(i),
  the cited `sorry` of `CausalScaffold.GerochEquiv`, or directly from causality and properness of
  the projection on diamonds, not attempted.
* **The charts are mathlib's**, chosen by `Classical.choose`; nothing here depends on the choice
  (only `symm_apply_of_mem_target`/`apply_of_mem_source`, true for every chart of the atlas).
  `HasGroupoid` is for the atlas, so `flatCausality` and `IsLocalIsometry` of `Γ\Ω` are those of
  this atlas; `IsQuotientOf.exists_homeomorph` identifies another `IsQuotientOf M` with `Γ\Ω`
  topologically only (that `Φ` is an isometry for `M`'s charts is not stated).
* `IsQuotientOf` follows BARBOT-THEOREMS §1 but takes `Ω : Opens` (its `isOpen` field is the
  type) and `M` any charted space (a `FlatSpacetime` coerces). It asks neither freeness nor
  proper discontinuity, which BARBOT-THEOREMS' sketch does not ask either.
* Generic helpers (charts of an open subset, continuity on an interval, local path-connectedness
  of an interval, the causality of the subtype `⊤`) are `private`; `le_top_subtype_iff` re-derives
  the case `W = ⊤` of `isIsometricEmbedding_subtype_val` (graduation candidate).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 2, package WP-31b-Quotient.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Function

universe u

variable {d : ℕ}

/-! ### The action of `Γ` on an invariant open set -/

namespace FlatQuotient

/-- **`Ω` is `Γ`-invariant**: every element of `Γ` maps `Ω` into itself. -/
class Invariant (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) : Prop where
  smul_mem : ∀ γ : Γ, ∀ p ∈ Ω, (γ : isom d) • p ∈ Ω

variable (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d))

/-- Invariance in the form of BARBOT-THEOREMS §1 (`(γ • ·) '' Ω = Ω` for `γ ∈ Γ`). -/
theorem invariant_iff :
    Invariant Γ Ω ↔ ∀ γ ∈ Γ, (fun p : Minkowski d => γ • p) '' (Ω : Set (Minkowski d)) = Ω := by
  constructor
  · intro h γ hγ
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact h.smul_mem ⟨γ, hγ⟩ p hp
    · intro p hp
      refine ⟨γ⁻¹ • p, h.smul_mem ⟨γ⁻¹, Γ.inv_mem hγ⟩ p hp, ?_⟩
      simp only [smul_inv_smul]
  · intro h
    exact ⟨fun γ p hp => (h _ γ.2).subset ⟨p, hp, rfl⟩⟩

variable [Invariant Γ Ω]

/-- The chart of the open subset `Ω` at any point has target `Ω`. -/
private theorem chartAt_opens_target' (x : Ω) : (chartAt (Minkowski d) x).target = Ω := by
  rw [TopologicalSpace.Opens.chartAt_eq]
  simp [OpenPartialHomeomorph.subtypeRestr]

/-- The chart of the open subset `Ω` is `Subtype.val`, so its inverse on `Ω` is `⟨p, hp⟩`. -/
private theorem chartAt_opens_symm' {x : Ω} {p : Minkowski d} (hp : p ∈ Ω) :
    (chartAt (Minkowski d) x).symm p = ⟨p, hp⟩ :=
  Subtype.ext ((chartAt (Minkowski d) x).right_inv (by rw [chartAt_opens_target']; exact hp))

/-- The action of `Γ` on the subtype `Ω`. -/
noncomputable instance instMulAction : MulAction Γ Ω where
  smul γ p := ⟨(γ : isom d) • (p : Minkowski d), Invariant.smul_mem γ p.1 p.2⟩
  one_smul p := Subtype.ext (one_smul (isom d) (p : Minkowski d))
  mul_smul γ γ' p := Subtype.ext (mul_smul (γ : isom d) (γ' : isom d) (p : Minkowski d))

@[simp] theorem coe_smul (γ : Γ) (p : Ω) :
    ((γ • p : Ω) : Minkowski d) = (γ : isom d) • (p : Minkowski d) := rfl

instance instContinuousConstSMul : ContinuousConstSMul Γ Ω :=
  ⟨fun γ => ((continuous_const_smul (γ : isom d)).comp continuous_subtype_val).subtype_mk _⟩

instance instLocallyCompactSpace : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace

end FlatQuotient

open FlatQuotient

/-- **The quotient `Γ\Ω`** (l.1836–1838): the orbit space of the action of `Γ` on the invariant
open set `Ω`, with the quotient topology. -/
abbrev FlatQuotient (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) [Invariant Γ Ω] :=
  MulAction.orbitRel.Quotient Γ Ω

namespace FlatQuotient

variable (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) [Invariant Γ Ω]

/-- The projection `Ω → Γ\Ω`. -/
noncomputable def proj : Ω → FlatQuotient Γ Ω := Quotient.mk _

variable {Γ Ω}

theorem proj_eq_proj_iff {a b : Ω} : proj Γ Ω a = proj Γ Ω b ↔ ∃ γ : Γ, γ • b = a := by
  show Quotient.mk _ a = Quotient.mk _ b ↔ _
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

theorem proj_eq_proj_iff' {a b : Ω} :
    proj Γ Ω a = proj Γ Ω b ↔ ∃ γ ∈ Γ, γ • (a : Minkowski d) = b := by
  rw [eq_comm, proj_eq_proj_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, γ.2, congrArg Subtype.val hγ⟩
  · rintro ⟨γ, hγ, h⟩
    exact ⟨⟨γ, hγ⟩, Subtype.ext h⟩

variable (Γ Ω)

theorem proj_surjective : Surjective (proj Γ Ω) := Quotient.mk_surjective

theorem continuous_proj : Continuous (proj Γ Ω) := continuous_quot_mk

theorem isOpenMap_proj : IsOpenMap (proj Γ Ω) :=
  MulAction.isOpenQuotientMap_quotientMk.isOpenMap

variable [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω]

/-- **The projection is a quotient covering map** (mathlib). -/
theorem isQuotientCoveringMap_proj : IsQuotientCoveringMap (proj Γ Ω) Γ :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- **The projection is a covering map.** -/
theorem isCoveringMap_proj : IsCoveringMap (proj Γ Ω) :=
  (isQuotientCoveringMap_proj Γ Ω).isCoveringMap

omit [IsCancelSMul Γ Ω] in
/-- **`Γ\Ω` is Hausdorff** (mathlib's `t2Space_of_properlyDiscontinuousSMul_of_t2Space`). -/
theorem t2Space : T2Space (FlatQuotient Γ Ω) := inferInstance

/-- **The charts of `Γ\Ω`**, read pointwise: on the target of a chart `e`, `e.symm p` is the class
of `p ∈ Ω`. -/
theorem symm_apply_of_mem_target {e : OpenPartialHomeomorph (FlatQuotient Γ Ω) (Minkowski d)}
    (he : e ∈ atlas (Minkowski d) (FlatQuotient Γ Ω)) {p : Minkowski d} (hp : p ∈ e.target) :
    ∃ hpΩ : p ∈ Ω, e.symm p = proj Γ Ω ⟨p, hpΩ⟩ := by
  obtain ⟨q, rfl⟩ := he
  rw [OpenPartialHomeomorph.trans_target, chartAt_opens_target'] at hp
  refine ⟨hp.1, ?_⟩
  simp only [OpenPartialHomeomorph.coe_trans_symm, comp_apply,
    IsLocalHomeomorph.localInverseAt_symm, chartAt_opens_symm' Ω hp.1]
  rfl

/-- On the source of a chart `e`, `e r ∈ Ω` and its class is `r`. -/
theorem apply_of_mem_source {e : OpenPartialHomeomorph (FlatQuotient Γ Ω) (Minkowski d)}
    (he : e ∈ atlas (Minkowski d) (FlatQuotient Γ Ω)) {r : FlatQuotient Γ Ω} (hr : r ∈ e.source) :
    ∃ h : e r ∈ Ω, proj Γ Ω ⟨e r, h⟩ = r := by
  obtain ⟨q, rfl⟩ := he
  rw [OpenPartialHomeomorph.trans_source] at hr
  have key : ∀ (σ : OpenPartialHomeomorph (FlatQuotient Γ Ω) Ω), ⇑σ.symm = proj Γ Ω →
      ∀ (x : Ω) {r : FlatQuotient Γ Ω}, r ∈ σ.source →
      ∃ h : (σ.trans (chartAt (Minkowski d) x)) r ∈ Ω,
        proj Γ Ω ⟨(σ.trans (chartAt (Minkowski d) x)) r, h⟩ = r := by
    intro σ hσ x r hr
    refine ⟨(σ r).2, ?_⟩
    have : (⟨(σ.trans (chartAt (Minkowski d) x)) r, (σ r).2⟩ : Ω) = σ r := Subtype.ext rfl
    rw [this, ← hσ]
    exact σ.left_inv hr
  exact key _ (IsLocalHomeomorph.localInverseAt_symm _ _) _ hr.1

/-- Every point of `Ω` has a neighbourhood in `𝐌ⁿ` no point of which in `Ω` is moved into it by
a nontrivial element of `Γ`. -/
theorem exists_nhds_smul_eq_one (x : Minkowski d) (hx : x ∈ Ω) :
    ∃ U ∈ 𝓝 x, ∀ γ : Γ, ∀ y ∈ Ω, y ∈ U → (γ : isom d) • y ∈ U → γ = 1 := by
  obtain ⟨U, hU, hUγ⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Γ (⟨x, hx⟩ : Ω)
  obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ _ _).1 hU
  refine ⟨u, hu, fun γ y hy hyu hγy => ?_⟩
  have hfix : γ • (⟨x, hx⟩ : Ω) = ⟨x, hx⟩ :=
    hUγ γ ⟨γ • ⟨y, hy⟩, ⟨⟨y, hy⟩, hsub hyu, rfl⟩, hsub hγy⟩
  exact IsCancelSMul.right_cancel γ 1 (⟨x, hx⟩ : Ω) (by rw [one_smul]; exact hfix)

/-- **Local constancy**: a map `F` continuous at `p₀ ∈ Ω`, which near `p₀` sends each point of
`Ω` into its own `Γ`-orbit in `Ω`, is near `p₀` the action of one element of `Γ`. -/
theorem eventually_eq_smul {F : Minkowski d → Minkowski d} {p₀ : Minkowski d}
    (hF : ContinuousAt F p₀)
    (horb : ∀ᶠ p in 𝓝 p₀, p ∈ Ω ∧ F p ∈ Ω ∧ ∃ γ : Γ, (γ : isom d) • p = F p) :
    ∃ γ : Γ, ∀ᶠ p in 𝓝 p₀, F p = (γ : isom d) • p := by
  obtain ⟨-, hFp₀, γ, hγ⟩ := horb.self_of_nhds
  obtain ⟨U, hU, hUγ⟩ := exists_nhds_smul_eq_one Γ Ω (F p₀) hFp₀
  refine ⟨γ, ?_⟩
  have h1 : ∀ᶠ p in 𝓝 p₀, F p ∈ U := hF.eventually_mem hU
  have h2 : ∀ᶠ p in 𝓝 p₀, (γ : isom d) • p ∈ U :=
    (continuous_const_smul (γ : isom d)).continuousAt.eventually_mem (by rw [hγ]; exact hU)
  filter_upwards [horb, h1, h2] with p hp hFU hγU
  obtain ⟨hpΩ, -, δ, hδ⟩ := hp
  have h3 := hUγ (δ * γ⁻¹) ((γ : isom d) • p) (Invariant.smul_mem γ p hpΩ) hγU (by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul, hδ]; exact hFU)
  rw [mul_inv_eq_one] at h3
  subst h3
  exact hδ.symm

/-- **`Γ\Ω` is an `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold**: the transition between two charts is, near each
point, an element of `Γ ⊆ isom d`. -/
instance instHasGroupoid :
    HasGroupoid (FlatQuotient Γ Ω) (gxGroupoid (isom d) (Minkowski d)) := by
  have key : ∀ {e e' : OpenPartialHomeomorph (FlatQuotient Γ Ω) (Minkowski d)},
      e ∈ atlas (Minkowski d) (FlatQuotient Γ Ω) → e' ∈ atlas (Minkowski d) (FlatQuotient Γ Ω) →
      (gxPregroupoid (isom d) (Minkowski d)).property (e.symm.trans e') (e.symm.trans e').source := by
    intro e e' he he' p hp
    obtain ⟨γ, hγ⟩ := eventually_eq_smul (Γ := Γ) (Ω := Ω) (F := e.symm.trans e')
      ((e.symm.trans e').continuousAt hp) (by
        filter_upwards [(e.symm.trans e').open_source.mem_nhds hp] with p' hp'
        rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hp'
        obtain ⟨hp'Ω, hsymm⟩ := symm_apply_of_mem_target Γ Ω he hp'.1
        obtain ⟨hF, hFproj⟩ := apply_of_mem_source Γ Ω he' (r := e.symm p') hp'.2
        obtain ⟨γ, hγ, h⟩ := proj_eq_proj_iff'.1 (hFproj.trans hsymm).symm
        exact ⟨hp'Ω, hF, ⟨γ, hγ⟩, h⟩)
    exact ⟨(γ : isom d), hγ⟩
  refine ⟨fun {e e'} he he' => ?_⟩
  rw [gxGroupoid, mem_groupoid_of_pregroupoid]
  refine ⟨key he he', ?_⟩
  have := key he' he
  rwa [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

omit [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω] in
/-- **`Γ\Ω` is connected when `Ω` is.** -/
theorem connectedSpace (hΩ : IsConnected (Ω : Set (Minkowski d))) :
    ConnectedSpace (FlatQuotient Γ Ω) := by
  haveI : ConnectedSpace Ω := isConnected_iff_connectedSpace.1 hΩ
  infer_instance

/-- **`Γ\Ω` as a flat spacetime**, for `Ω` connected. -/
noncomputable def toFlatSpacetime (hΩ : IsConnected (Ω : Set (Minkowski d))) :
    FlatSpacetime.{0} d :=
  haveI := connectedSpace Γ Ω hΩ
  FlatSpacetime.of (FlatQuotient Γ Ω)

/-! ### The projection is a local isometry -/

/-- **The projection is a local isometry.** -/
theorem isLocalIsometry_proj : IsLocalIsometry d (proj Γ Ω) := by
  refine ⟨continuous_proj Γ Ω, fun x => ?_⟩
  set e := chartAt (Minkowski d) (proj Γ Ω x)
  have hsx : (chartAt (Minkowski d) x).symm (x : Minkowski d) = x := by
    rw [chartAt_opens_symm' Ω x.2]
  have hxt : (x : Minkowski d) ∈ (chartAt (Minkowski d) x).target := by
    rw [chartAt_opens_target']; exact x.2
  have hG : ContinuousAt (proj Γ Ω ∘ (chartAt (Minkowski d) x).symm) (x : Minkowski d) :=
    (continuous_proj Γ Ω).continuousAt.comp ((chartAt (Minkowski d) x).continuousAt_symm hxt)
  have hGx : (proj Γ Ω ∘ (chartAt (Minkowski d) x).symm) (x : Minkowski d) = proj Γ Ω x := by
    simp only [comp_apply, hsx]
  have hF : ContinuousAt (e ∘ proj Γ Ω ∘ (chartAt (Minkowski d) x).symm) (x : Minkowski d) := by
    refine ContinuousAt.comp (f := proj Γ Ω ∘ (chartAt (Minkowski d) x).symm) ?_ hG
    rw [hGx]
    exact e.continuousAt (mem_chart_source _ _)
  obtain ⟨γ, hγ⟩ := eventually_eq_smul (Γ := Γ) (Ω := Ω) hF (by
    have hsrc : ∀ᶠ p in 𝓝 (x : Minkowski d),
        (proj Γ Ω ∘ (chartAt (Minkowski d) x).symm) p ∈ e.source :=
      hG.eventually_mem (by rw [hGx]; exact e.open_source.mem_nhds (mem_chart_source _ _))
    filter_upwards [Ω.isOpen.mem_nhds x.2, hsrc] with p hp hpe
    simp only [comp_apply, chartAt_opens_symm' Ω hp] at hpe ⊢
    obtain ⟨hF, hFproj⟩ := apply_of_mem_source Γ Ω (chart_mem_atlas _ _) hpe
    obtain ⟨γ, hγ, h⟩ := proj_eq_proj_iff'.1 hFproj.symm
    exact ⟨hp, hF, ⟨γ, hγ⟩, h⟩)
  exact ⟨(γ : isom d), hγ⟩

/-- **The projection is an `IsEMorphism` of the flat causalities.** -/
theorem isEMorphism_proj :
    IsEMorphism (flatCausality d Ω) (flatCausality d (FlatQuotient Γ Ω)) (proj Γ Ω) :=
  (isLocalIsometry_proj Γ Ω).isEMorphism

/-- **The projection is a strong morphism of the flat causalities.** -/
theorem strongMorphism_proj :
    StrongMorphism (flatCausality d Ω) (flatCausality d (FlatQuotient Γ Ω)) (proj Γ Ω) :=
  (isLocalIsometry_proj Γ Ω).strongMorphism

/-- **The projection is a local isomorphism of the flat causalities.** -/
theorem localIsomorphism_proj :
    LocalIsomorphism (flatCausality d Ω) (flatCausality d (FlatQuotient Γ Ω)) (proj Γ Ω) :=
  (isLocalIsometry_proj Γ Ω).localIsomorphism

end FlatQuotient

/-! ### `IsQuotientOf` -/

/-- **`M` is the quotient `Γ\Ω`** (BARBOT-THEOREMS §1): `Ω` is `Γ`-invariant, and some covering
map `π : Ω → M`, surjective and a local isometry, has the `Γ`-orbits for fibres. `Ω` is an open
set by its type (`Opens`), which replaces BARBOT-THEOREMS' `isOpen` field. -/
structure IsQuotientOf (M : Type u) [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) : Prop where
  inv : ∀ γ ∈ Γ, (fun p : Minkowski d => γ • p) '' (Ω : Set (Minkowski d)) = Ω
  quot : ∃ π : Ω → M, IsCoveringMap π ∧ IsLocalIsometry d π ∧ Surjective π ∧
    ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q

/-- The invariance of `IsQuotientOf`, as the class `FlatQuotient.Invariant`. -/
theorem IsQuotientOf.invariant {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} (h : IsQuotientOf M Γ Ω) :
    FlatQuotient.Invariant Γ Ω :=
  (FlatQuotient.invariant_iff Γ Ω).2 h.inv

namespace FlatQuotient

variable (Γ : Subgroup (isom d)) (Ω : Opens (Minkowski d)) [Invariant Γ Ω]
  [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω]

/-- **The constructed quotient is a quotient**: `IsQuotientOf (Γ\Ω) Γ Ω`. -/
theorem isQuotientOf : IsQuotientOf (FlatQuotient Γ Ω) Γ Ω :=
  ⟨(invariant_iff Γ Ω).1 inferInstance, proj Γ Ω, isCoveringMap_proj Γ Ω, isLocalIsometry_proj Γ Ω,
    proj_surjective Γ Ω, fun _ _ => proj_eq_proj_iff'⟩

/-- The same, for the bundled flat spacetime `toFlatSpacetime`. -/
theorem isQuotientOf_toFlatSpacetime (hΩ : IsConnected (Ω : Set (Minkowski d))) :
    IsQuotientOf (toFlatSpacetime Γ Ω hΩ) Γ Ω :=
  isQuotientOf Γ Ω

omit [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω] in
/-- **`IsQuotientOf` determines `M` up to homeomorphism**: the projection `π` of an
`IsQuotientOf M Γ Ω` factors through `Γ\Ω` by a homeomorphism `Φ` with `Φ ∘ proj = π`. -/
theorem _root_.Causal.Flat.IsQuotientOf.exists_homeomorph {M : Type u} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] (h : IsQuotientOf M Γ Ω) :
    ∃ π : Ω → M, IsCoveringMap π ∧ IsLocalIsometry d π ∧
      ∃ Φ : FlatQuotient Γ Ω ≃ₜ M, ∀ x, Φ (proj Γ Ω x) = π x := by
  obtain ⟨π, hcov, hloc, hsurj, hfib⟩ := h.quot
  have hrel : ∀ a b : Ω, (MulAction.orbitRel Γ Ω) a b → π a = π b := by
    intro a b hab
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    exact ((hfib b a).2 ⟨γ, γ.2, congrArg Subtype.val hγ⟩).symm
  let Φ : FlatQuotient Γ Ω → M := Quotient.lift π hrel
  have hΦ : ∀ x, Φ (proj Γ Ω x) = π x := fun _ => rfl
  have hcont : Continuous Φ := hcov.continuous.quotient_lift hrel
  have hopen : IsOpenMap Φ := by
    intro U hU
    have himg : Φ '' U = π '' (proj Γ Ω ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨x, rfl⟩ := proj_surjective Γ Ω q
        exact ⟨x, hq, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨proj Γ Ω x, hx, rfl⟩
    rw [himg]
    exact hcov.isOpenMap _ (hU.preimage (continuous_proj Γ Ω))
  have hbij : Bijective Φ := by
    refine ⟨fun q q' hqq' => ?_, fun y => ?_⟩
    · obtain ⟨x, rfl⟩ := proj_surjective Γ Ω q
      obtain ⟨x', rfl⟩ := proj_surjective Γ Ω q'
      rw [hΦ, hΦ] at hqq'
      exact proj_eq_proj_iff'.2 ((hfib x x').1 hqq')
    · obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨proj Γ Ω x, rfl⟩
  exact ⟨π, hcov, hloc, (IsHomeomorph.mk hcont hopen hbij).homeomorph Φ, hΦ⟩

/-! ### Cauchy surfaces descend -/

omit [Invariant Γ Ω] [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω] in
/-- **The two readings of "Cauchy surface of `Ω`" agree**: `S ⊆ Ω` is a Cauchy surface of the
open set `Ω` of `𝐌ⁿ` (`IsCauchySurfaceOn`) iff its trace on the subtype is a Cauchy surface of
`Ω` as a flat spacetime (through `isIsometricEmbedding_subtype_val`, FlatSpacetime's open-subset
lemma). -/
theorem isCauchySurfaceOn_iff {S : Set (Minkowski d)} (hS : S ⊆ Ω) :
    (minkowski d).IsCauchySurfaceOn Ω S ↔
      (flatCausality d Ω).IsCauchySurface (Subtype.val ⁻¹' S : Set Ω) := by
  have hU : ((Ω : Opens (Minkowski d)) : Set (Minkowski d)) =
      Subtype.val '' ((⊤ : Opens Ω) : Set Ω) := by
    rw [Opens.coe_top, image_univ, Subtype.range_coe]
  have h := ((isIsometricEmbedding_subtype_val (d := d) Ω).isEMorphism).isCauchySurfaceOn_image_iff
    (Subtype.val_injective.injOn) le_rfl hU (S := (Subtype.val ⁻¹' S : Set Ω)) (subset_univ _)
  have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set Ω) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hS hx⟩, hx, rfl⟩
  rw [flatCausality_self (d := d), himg] at h
  exact h.symm

/-- **Causal curves lift** through `Γ\Ω`: every causal curve of the quotient over an interval is
the projection of a causal curve of `Ω` over the same interval. -/
def LiftsCausalCurves : Prop :=
  ∀ (I : Set ℝ) (c : ℝ → FlatQuotient Γ Ω),
    (flatCausality d (FlatQuotient Γ Ω)).CausalCurveIn ⊤ I c →
      ∃ c' : ℝ → Ω, (flatCausality d Ω).CausalCurveIn ⊤ I c' ∧ ∀ t ∈ I, proj Γ Ω (c' t) = c t

/-- **Inextensible causal curves lift** to inextensible causal curves. -/
def LiftsInextensible : Prop :=
  ∀ (I : Set ℝ) (c : ℝ → FlatQuotient Γ Ω),
    (flatCausality d (FlatQuotient Γ Ω)).Inextensible ⊤ I c →
      ∃ c' : ℝ → Ω, (flatCausality d Ω).Inextensible ⊤ I c' ∧ ∀ t ∈ I, proj Γ Ω (c' t) = c t

/-- **Γ acts acausally** on `Ω`: no nontrivial element sends a point of `Ω` into its causal
future in `Ω`. -/
def ActsAcausally : Prop :=
  ∀ γ : Γ, γ ≠ 1 → ∀ x : Ω, ¬ (flatCausality d Ω).le ⊤ x (γ • x)


/-- A map continuous on every segment of an interval is continuous on the interval. -/
private theorem continuousOn_of_Icc {X : Type*} [TopologicalSpace X] {I : Set ℝ} {f : ℝ → X}
    (h : ∀ a ∈ I, ∀ b ∈ I, ContinuousOn f (Icc a b)) : ContinuousOn f I := by
  intro t ht
  have hL : ContinuousWithinAt f (I ∩ Iic t) t := by
    by_cases hex : ∃ a ∈ I, a < t
    · obtain ⟨a, ha, hat⟩ := hex
      refine ((h a ha t ht) t ⟨hat.le, le_rfl⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Ioi a, isOpen_Ioi, hat, fun s hs => ⟨le_of_lt hs.1, hs.2.2⟩⟩
    · simp only [not_exists, not_and, not_lt] at hex
      exact continuousWithinAt_singleton.mono fun s hs => le_antisymm hs.2 (hex s hs.1)
  have hR : ContinuousWithinAt f (I ∩ Ici t) t := by
    by_cases hex : ∃ b ∈ I, t < b
    · obtain ⟨b, hb, htb⟩ := hex
      refine ((h t ht b hb) t ⟨le_rfl, htb.le⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, htb, fun s hs => ⟨hs.2.2, le_of_lt hs.1⟩⟩
    · simp only [not_exists, not_and, not_lt] at hex
      exact continuousWithinAt_singleton.mono fun s hs => le_antisymm (hex s hs.1) hs.2
  have := hL.union hR
  rwa [← inter_union_distrib_left, Iic_union_Ici, inter_univ] at this

/-- An interval of `ℝ` is locally path-connected. -/
private theorem locPathConnectedSpace_of_ordConnected {I : Set ℝ} (hI : I.OrdConnected) :
    LocPathConnectedSpace I := by
  refine LocPathConnectedSpace.of_bases (p := fun _ (ε : ℝ) => 0 < ε)
    (s := fun x ε => (Subtype.val : I → ℝ) ⁻¹' (I ∩ Metric.ball (x : ℝ) ε)) (fun x => ?_)
    (fun x ε hε => ?_)
  · rw [nhds_subtype]
    refine ((Metric.nhds_basis_ball (x := (x : ℝ))).comap (Subtype.val : I → ℝ)).congr
      (fun _ => Iff.rfl) (fun ε _ => ?_)
    ext y
    simp
  · exact ((hI.convex.inter (convex_ball _ _)).isPathConnected
      ⟨x, x.2, Metric.mem_ball_self hε⟩).preimage_coe inter_subset_left

/-- **Causal curves of `Γ\Ω` lift to `Ω`.** -/
theorem liftsCausalCurves : LiftsCausalCurves Γ Ω := by
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.nonempty
  have hcont : ContinuousOn c I := continuousOn_of_Icc fun a ha b hb => hc.continuousOn_Icc ha hb
  haveI : ContractibleSpace I := hc.ordConnected.convex.contractibleSpace hc.nonempty
  haveI : LocPathConnectedSpace I := locPathConnectedSpace_of_ordConnected hc.ordConnected
  obtain ⟨x₀, hx₀⟩ := proj_surjective Γ Ω (c t₀)
  obtain ⟨F, ⟨-, hFl⟩, -⟩ := (isCoveringMap_proj Γ Ω).existsUnique_continuousMap_lifts
    ⟨I.restrict c, hcont.restrict⟩ ⟨t₀, ht₀⟩ x₀ hx₀
  classical
  let c' : ℝ → Ω := fun t => if h : t ∈ I then F ⟨t, h⟩ else x₀
  have hc'I : ∀ t (h : t ∈ I), c' t = F ⟨t, h⟩ := fun t h => dif_pos h
  have hlift : ∀ t ∈ I, proj Γ Ω (c' t) = c t := fun t h => by
    rw [hc'I t h]; exact congrFun hFl ⟨t, h⟩
  have hc'cont : ContinuousOn c' I := by
    rw [continuousOn_iff_continuous_restrict]
    have : I.restrict c' = F := funext fun ⟨t, h⟩ => hc'I t h
    rw [this]
    exact F.continuous
  refine ⟨c', ⟨hc.nonempty, hc.ordConnected, fun a ha b hb => ?_⟩, hlift⟩
  refine ⟨fun _ _ => trivial, fun t ht N _ htN => ?_⟩
  have hIcc : Icc a b ⊆ I := hc.ordConnected.out ha hb
  obtain ⟨V, hxV, -, hV⟩ := (localIsomorphism_proj Γ Ω).2 (c' t)
  let V' : Opens Ω := V ⊓ N
  let U : Opens (FlatQuotient Γ Ω) := ⟨proj Γ Ω '' V', isOpenMap_proj Γ Ω _ V'.isOpen⟩
  have hcU : c t ∈ U := ⟨c' t, ⟨hxV, htN⟩, hlift t (hIcc ht)⟩
  obtain ⟨l₁, u₁, hl₁, hu₁, hrel⟩ := (hc.curve a ha b hb).rel t ht U le_top hcU
  have hev : ∀ᶠ s in 𝓝[Icc a b] t, c' s ∈ V' :=
    (hc'cont.mono hIcc) t ht (V'.isOpen.mem_nhds ⟨hxV, htN⟩)
  obtain ⟨O, hO, htO, hOsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO t htO
  refine ⟨max l₁ (t - ε), min u₁ (t + ε), max_lt hl₁ (by linarith), lt_min hu₁ (by linarith),
    fun s hs s' hs' h1 h2 h3 => ?_⟩
  have hmem : ∀ r ∈ Icc a b, max l₁ (t - ε) < r → r < min u₁ (t + ε) → c' r ∈ V' := by
    intro r hr hr1 hr2
    refine hOsub ⟨hball ?_, hr⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor
    · linarith [min_le_right u₁ (t + ε)]
    · linarith [le_max_right l₁ (t - ε)]
  have hsV := hmem s hs h1 (h2.trans h3)
  have hs'V := hmem s' hs' (h1.trans h2) h3
  have hcs := hrel s hs s' hs' ((le_max_left _ _).trans_lt h1) h2 (h3.trans_le (min_le_left _ _))
  rw [← hlift s (hIcc hs), ← hlift s' (hIcc hs')] at hcs
  exact (flatCausality d Ω).le_mono inf_le_right
    (((hV V' inf_le_left U rfl (c' s) hsV (c' s') hs'V).1).2 hcs)

/-- **A lift of an inextensible curve is inextensible** when `Γ` acts acausally: an extension
of the lift projects to an extension of the curve, and its new point projects to a new point
because two points of one orbit are never on one causal curve. -/
theorem inextensible_of_lift (hac : ActsAcausally Γ Ω) {I : Set ℝ}
    {c : ℝ → FlatQuotient Γ Ω} {c' : ℝ → Ω}
    (hc : (flatCausality d (FlatQuotient Γ Ω)).Inextensible ⊤ I c)
    (hc' : (flatCausality d Ω).CausalCurveIn ⊤ I c') (hlift : ∀ t ∈ I, proj Γ Ω (c' t) = c t) :
    (flatCausality d Ω).Inextensible ⊤ I c' := by
  refine ⟨hc', ?_⟩
  rintro ⟨I'', c'', hcurve, ⟨φ, h1, h2, h3, h4⟩, ⟨t', ht', h5⟩⟩
  apply hc.2
  refine ⟨I'', proj Γ Ω ∘ c'',
    (isEMorphism_proj Γ Ω).causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hcurve,
    ⟨φ, h1, h2, h3, fun t ht => ?_⟩, ⟨t', ht', fun t ht heq => ?_⟩⟩
  · simp only [comp_apply]
    rw [h4 t ht, hlift t ht]
  · rw [comp_apply, ← hlift t ht, proj_eq_proj_iff] at heq
    obtain ⟨γ, hγ⟩ := heq
    have hne : γ ≠ 1 := by
      rintro rfl
      rw [one_smul] at hγ
      exact h5 t ht hγ.symm
    rcases le_total (φ t) t' with hle | hle
    · have hrel := hcurve.le_of_le (h2 ht) ht' hle
      rw [h4 t ht, ← hγ] at hrel
      exact hac γ hne _ hrel
    · have hrel := hcurve.le_of_le ht' (h2 ht) hle
      rw [h4 t ht, ← hγ] at hrel
      apply hac γ⁻¹ (inv_ne_one.2 hne) (γ • c' t)
      rwa [inv_smul_smul]

/-- Under an acausal action, inextensible curves lift. -/
theorem liftsInextensible (hac : ActsAcausally Γ Ω) : LiftsInextensible Γ Ω := by
  intro I c hc
  obtain ⟨c', hc', hlift⟩ := liftsCausalCurves Γ Ω I c hc.1
  exact ⟨c', inextensible_of_lift Γ Ω hac hc hc' hlift, hlift⟩

/-- **Cauchy surfaces descend, given the lifting of inextensible curves**: the image of a
`Γ`-invariant Cauchy surface of `Ω` is a Cauchy surface of `Γ\Ω`. -/
theorem isCauchySurface_image_of_liftsInextensible (hL : LiftsInextensible Γ Ω) {S : Set Ω}
    (hinv : ∀ γ : Γ, ∀ p ∈ S, γ • p ∈ S) (hS : (flatCausality d Ω).IsCauchySurface S) :
    (flatCausality d (FlatQuotient Γ Ω)).IsCauchySurface (proj Γ Ω '' S) := by
  intro I c hc
  obtain ⟨c', hc', hlift⟩ := hL I c hc
  obtain ⟨x, ⟨⟨t, ht, rfl⟩, hxS⟩, huniq⟩ := hS I c' hc'
  refine ⟨proj Γ Ω (c' t), ⟨⟨t, ht, (hlift t ht).symm⟩, ⟨_, hxS, rfl⟩⟩, ?_⟩
  rintro y ⟨⟨s, hs, rfl⟩, ⟨z, hz, hzy⟩⟩
  rw [← hlift s hs, proj_eq_proj_iff] at hzy
  obtain ⟨γ, hγ⟩ := hzy
  have hmem : c' s ∈ S := by
    have := hinv γ⁻¹ z hz
    rwa [← hγ, inv_smul_smul] at this
  rw [← hlift s hs, huniq (c' s) ⟨⟨s, hs, rfl⟩, hmem⟩]

/-- **Cauchy surfaces descend** (l.1204–1209), for an acausal action. -/
theorem isCauchySurface_image (hac : ActsAcausally Γ Ω) {S : Set Ω}
    (hinv : ∀ γ : Γ, ∀ p ∈ S, γ • p ∈ S) (hS : (flatCausality d Ω).IsCauchySurface S) :
    (flatCausality d (FlatQuotient Γ Ω)).IsCauchySurface (proj Γ Ω '' S) :=
  isCauchySurface_image_of_liftsInextensible Γ Ω (liftsInextensible Γ Ω hac) hinv hS

/-- **Cauchy surfaces descend**, read in `𝐌ⁿ`: a `Γ`-invariant Cauchy surface `S ⊆ Ω` of the open
set `Ω` projects to a Cauchy surface of `Γ\Ω`. -/
theorem isCauchySurface_image_of_isCauchySurfaceOn (hac : ActsAcausally Γ Ω)
    {S : Set (Minkowski d)} (hSΩ : S ⊆ Ω) (hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S)
    (hS : (minkowski d).IsCauchySurfaceOn Ω S) :
    (flatCausality d (FlatQuotient Γ Ω)).IsCauchySurface
      (proj Γ Ω '' (Subtype.val ⁻¹' S : Set Ω)) :=
  isCauchySurface_image Γ Ω hac (fun γ p hp => hinv γ γ.2 p hp)
    ((isCauchySurfaceOn_iff Ω hSΩ).1 hS)

/-- **`Γ\Ω` is GH in Barbot's sense** (it has a Cauchy surface, l.500–509) when `Ω` has a
`Γ`-invariant Cauchy surface and `Γ` acts acausally. -/
theorem barbotGH_toFlatSpacetime (hΩ : IsConnected (Ω : Set (Minkowski d)))
    (hac : ActsAcausally Γ Ω) {S : Set Ω} (hinv : ∀ γ : Γ, ∀ p ∈ S, γ • p ∈ S)
    (hS : (flatCausality d Ω).IsCauchySurface S) : BarbotGH (toFlatSpacetime Γ Ω hΩ) :=
  ⟨_, isCauchySurface_image Γ Ω hac hinv hS⟩

end FlatQuotient


/-! ### A quotient need not be causal: a timelike translation -/

namespace FlatQuotient

variable (d) in
/-- The unit time vector `e₀ = (1, 0)`. -/
noncomputable def timeVec : Minkowski d := (1, 0)

variable (d) in
/-- `n ↦` the translation by `n e₀`. -/
noncomputable def timeTranslation : Multiplicative ℤ →* isom d where
  toFun n := ⟨AffineEquiv.constVAdd ℝ (Minkowski d) (((Multiplicative.toAdd n : ℤ) : ℝ) • timeVec d),
    constVAdd_mem_isom _⟩
  map_one' := by
    apply Subtype.ext
    ext p
    · simp [timeVec]
    · simp [timeVec]
  map_mul' a b := by
    apply Subtype.ext
    ext p
    · simp [timeVec]
      ring
    · simp [timeVec]

theorem timeTranslation_smul (n : Multiplicative ℤ) (p : Minkowski d) :
    timeTranslation d n • p = (((Multiplicative.toAdd n : ℤ) : ℝ) • timeVec d) + p := rfl

variable (d) in
/-- **The group generated by a timelike translation**, `ℤ e₀`. -/
noncomputable def timeGroup : Subgroup (isom d) := (timeTranslation d).range

instance instInvariantTimeGroup : Invariant (timeGroup d) ⊤ := ⟨fun _ _ _ => trivial⟩

theorem fst_timeTranslation_smul (n : Multiplicative ℤ) (p : Minkowski d) :
    (timeTranslation d n • p).1 = ((Multiplicative.toAdd n : ℤ) : ℝ) + p.1 := by
  rw [timeTranslation_smul]
  simp [timeVec]

/-- The time translations act freely. -/
instance instIsCancelSMulTimeGroup : IsCancelSMul (timeGroup d) (⊤ : Opens (Minkowski d)) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨_, n, rfl⟩ x hx
  have h := congrArg (fun q : (⊤ : Opens (Minkowski d)) => (q : Minkowski d).1) hx
  simp only [coe_smul, fst_timeTranslation_smul] at h
  have hn : ((Multiplicative.toAdd n : ℤ) : ℝ) = 0 := by linarith
  have hn' : Multiplicative.toAdd n = 0 := by exact_mod_cast hn
  apply Subtype.ext
  show timeTranslation d n = 1
  rw [show n = 1 from hn', map_one]

/-- The time translations act properly discontinuously. -/
instance instProperlyDiscontinuousSMulTimeGroup :
    ProperlyDiscontinuousSMul (timeGroup d) (⊤ : Opens (Minkowski d)) := by
  refine ⟨fun {K L} hK hL => ?_⟩
  have hf : Continuous fun q : (⊤ : Opens (Minkowski d)) => (q : Minkowski d).1 :=
    continuous_fst.comp continuous_subtype_val
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨R', hR'⟩ := hL.exists_bound_of_continuousOn hf.continuousOn
  set N : ℤ := ⌈R + R'⌉
  refine ((Set.finite_Icc (-N) N).image fun m : ℤ =>
    (⟨timeTranslation d (Multiplicative.ofAdd m), m, rfl⟩ : timeGroup d)).subset ?_
  rintro ⟨_, n, rfl⟩ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  have h1 := hR k hk
  have h2 := hR' _ hl
  simp only [coe_smul, fst_timeTranslation_smul, Real.norm_eq_abs] at h1 h2
  refine ⟨Multiplicative.toAdd n, ?_, rfl⟩
  have hN : R + R' ≤ (N : ℝ) := Int.le_ceil _
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  have habs : |((Multiplicative.toAdd n : ℤ) : ℝ)| ≤ (N : ℝ) :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have habs' : |Multiplicative.toAdd n| ≤ N := by exact_mod_cast habs
  exact ⟨by linarith [neg_abs_le (Multiplicative.toAdd n)], (le_abs_self _).trans habs'⟩

/-- On `Ω = ⊤`, the flat causality of the subtype is `minkowski d`. -/
private theorem le_top_subtype_iff (x y : (⊤ : Opens (Minkowski d))) :
    (flatCausality d (⊤ : Opens (Minkowski d))).le ⊤ x y ↔
      (minkowski d).le ⊤ (x : Minkowski d) y := by
  have h := ((isIsometricEmbedding_subtype_val (d := d) (⊤ : Opens (Minkowski d))).rel_iff ⊤ ⊤
    (by ext z; simp) x y).1
  rw [h, flatCausality_self (d := d)]

/-- **Finding: `Γ\Ω` need not be causal.** The group `ℤ e₀` of time translations acts freely and
properly discontinuously on `𝐌ⁿ`, so `ℤ e₀ \ 𝐌ⁿ` is a flat spacetime (Hausdorff, connected,
`(Isom(𝐌ⁿ), 𝐌ⁿ)`-charted), and it is not causal: the classes of `0` and `e₀/2` precede each other.
So "a quotient of a GH open set is GH" needs a hypothesis on the action. -/
theorem not_isCausal_timeGroup :
    ¬ (flatCausality d (FlatQuotient (timeGroup d) ⊤)).IsCausal := by
  intro hcaus
  let a : (⊤ : Opens (Minkowski d)) := ⟨0, trivial⟩
  let b : (⊤ : Opens (Minkowski d)) := ⟨((1 : ℝ) / 2, 0), trivial⟩
  let γ : timeGroup d := ⟨timeTranslation d (Multiplicative.ofAdd 1), _, rfl⟩
  have hab : (flatCausality d (⊤ : Opens (Minkowski d))).le ⊤ a b := by
    rw [le_top_subtype_iff, minkowski_le_top_iff]
    norm_num [a, b]
  have hba : (flatCausality d (⊤ : Opens (Minkowski d))).le ⊤ b (γ • a) := by
    rw [le_top_subtype_iff, minkowski_le_top_iff]
    simp only [coe_smul, γ, a, b, timeTranslation_smul, timeVec, add_zero]
    norm_num
  have h1 := (strongMorphism_proj (timeGroup d) ⊤).le_of_mapsTo (U := ⊤) (V := ⊤)
    (fun _ _ => trivial) hab
  have h2 := (strongMorphism_proj (timeGroup d) ⊤).le_of_mapsTo (U := ⊤) (V := ⊤)
    (fun _ _ => trivial) hba
  have hγa : proj (timeGroup d) ⊤ (γ • a) = proj (timeGroup d) ⊤ a :=
    proj_eq_proj_iff.2 ⟨γ, rfl⟩
  rw [hγa] at h2
  obtain ⟨δ, hδ⟩ := proj_eq_proj_iff.1 (hcaus h1 h2)
  obtain ⟨_, n, rfl⟩ := δ
  have h := congrArg (fun q : (⊤ : Opens (Minkowski d)) => (q : Minkowski d).1) hδ
  simp only [coe_smul, fst_timeTranslation_smul, b, a] at h
  have h' : ((Multiplicative.toAdd n : ℤ) : ℝ) * 2 = -1 := by
    simp only [Prod.fst_zero] at h
    linarith
  have h'' : Multiplicative.toAdd n * 2 = -1 := by exact_mod_cast h'
  omega

/-- The time translations do not act acausally: `0 ≤ e₀`. -/
theorem not_actsAcausally_timeGroup : ¬ ActsAcausally (timeGroup d) ⊤ := by
  intro hac
  let γ : timeGroup d := ⟨timeTranslation d (Multiplicative.ofAdd 1), _, rfl⟩
  have hγ : γ ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : timeGroup d =>
      ((g : isom d) • (0 : Minkowski d)).1) h
    simp only [γ, fst_timeTranslation_smul, OneMemClass.coe_one, one_smul, Prod.fst_zero,
      toAdd_ofAdd] at h1
    norm_num at h1
  apply hac γ hγ ⟨0, trivial⟩
  rw [le_top_subtype_iff, minkowski_le_top_iff]
  simp only [coe_smul, γ, timeTranslation_smul, timeVec]
  norm_num

/-! ### A witness for the descent: a spacelike translation (kb/0011)

Barbot's "quotients of `𝐌ⁿ` itself by discrete groups of spacelike translations" (l.209–211),
for one generator: `ℤ e₁` with `e₁ = (0, single 0 1)`, which needs one spatial dimension
(`Minkowski (d + 1)`, Barbot's `n ≥ 2`). It acts freely, properly discontinuously and acausally
on `𝐌ⁿ`, and preserves the slice `t = 0`, so every hypothesis of `isCauchySurface_image` and of
`barbotGH_toFlatSpacetime` is met by a nontrivial group. -/

variable (d) in
/-- The unit spacelike vector `e₁ = (0, single 0 1)` of `Minkowski (d + 1)`. -/
noncomputable def spaceVec : Minkowski (d + 1) := (0, EuclideanSpace.single 0 1)

variable (d) in
/-- `n ↦` the translation by `n e₁`. -/
noncomputable def spaceTranslation : Multiplicative ℤ →* isom (d + 1) where
  toFun n := ⟨AffineEquiv.constVAdd ℝ (Minkowski (d + 1))
    (((Multiplicative.toAdd n : ℤ) : ℝ) • spaceVec d), constVAdd_mem_isom _⟩
  map_one' := by
    apply Subtype.ext
    ext p
    · simp [spaceVec]
    · simp [spaceVec]
  map_mul' a b := by
    apply Subtype.ext
    ext p
    · simp [spaceVec]
    · simp [spaceVec, add_smul, add_assoc]

theorem spaceTranslation_smul (n : Multiplicative ℤ) (p : Minkowski (d + 1)) :
    spaceTranslation d n • p = (((Multiplicative.toAdd n : ℤ) : ℝ) • spaceVec d) + p := rfl

theorem fst_spaceTranslation_smul (n : Multiplicative ℤ) (p : Minkowski (d + 1)) :
    (spaceTranslation d n • p).1 = p.1 := by
  rw [spaceTranslation_smul]
  simp [spaceVec]

theorem coord_spaceTranslation_smul (n : Multiplicative ℤ) (p : Minkowski (d + 1)) :
    (spaceTranslation d n • p).2 0 = ((Multiplicative.toAdd n : ℤ) : ℝ) + p.2 0 := by
  rw [spaceTranslation_smul]
  simp [spaceVec]

variable (d) in
/-- **The group generated by a spacelike translation**, `ℤ e₁`. -/
noncomputable def spaceGroup : Subgroup (isom (d + 1)) := (spaceTranslation d).range

instance instInvariantSpaceGroup : Invariant (spaceGroup d) ⊤ := ⟨fun _ _ _ => trivial⟩

/-- The spacelike translations act freely. -/
instance instIsCancelSMulSpaceGroup :
    IsCancelSMul (spaceGroup d) (⊤ : Opens (Minkowski (d + 1))) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨_, n, rfl⟩ x hx
  have h := congrArg (fun q : (⊤ : Opens (Minkowski (d + 1))) => (q : Minkowski (d + 1)).2 0) hx
  simp only [coe_smul, coord_spaceTranslation_smul] at h
  have hn : ((Multiplicative.toAdd n : ℤ) : ℝ) = 0 := by linarith
  have hn' : Multiplicative.toAdd n = 0 := by exact_mod_cast hn
  apply Subtype.ext
  show spaceTranslation d n = 1
  rw [show n = 1 from hn', map_one]

/-- The spacelike translations act properly discontinuously. -/
instance instProperlyDiscontinuousSMulSpaceGroup :
    ProperlyDiscontinuousSMul (spaceGroup d) (⊤ : Opens (Minkowski (d + 1))) := by
  refine ⟨fun {K L} hK hL => ?_⟩
  have hf : Continuous fun q : (⊤ : Opens (Minkowski (d + 1))) => (q : Minkowski (d + 1)).2 0 :=
    ((EuclideanSpace.proj (0 : Fin (d + 1))).continuous.comp continuous_snd).comp
      continuous_subtype_val
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨R', hR'⟩ := hL.exists_bound_of_continuousOn hf.continuousOn
  set N : ℤ := ⌈R + R'⌉
  refine ((Set.finite_Icc (-N) N).image fun m : ℤ =>
    (⟨spaceTranslation d (Multiplicative.ofAdd m), m, rfl⟩ : spaceGroup d)).subset ?_
  rintro ⟨_, n, rfl⟩ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  have h1 := hR k hk
  have h2 := hR' _ hl
  simp only [coe_smul, coord_spaceTranslation_smul, Real.norm_eq_abs] at h1 h2
  refine ⟨Multiplicative.toAdd n, ?_, rfl⟩
  have hN : R + R' ≤ (N : ℝ) := Int.le_ceil _
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  have habs : |((Multiplicative.toAdd n : ℤ) : ℝ)| ≤ (N : ℝ) :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have habs' : |Multiplicative.toAdd n| ≤ N := by exact_mod_cast habs
  exact ⟨by linarith [neg_abs_le (Multiplicative.toAdd n)], (le_abs_self _).trans habs'⟩

/-- The group `ℤ e₁` is nontrivial: its generator is not `1`. -/
theorem spaceTranslation_one_ne_one : spaceTranslation d (Multiplicative.ofAdd 1) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : isom (d + 1) => (g • (0 : Minkowski (d + 1))).2 0) h
  simp only [coord_spaceTranslation_smul, one_smul, toAdd_ofAdd] at h1
  norm_num at h1

/-- **The spacelike translations act acausally**: `x ≤ x + n e₁` forces `|n| ≤ 0`. -/
theorem actsAcausally_spaceGroup : ActsAcausally (spaceGroup d) ⊤ := by
  rintro ⟨_, n, rfl⟩ hne x hle
  apply hne
  rw [le_top_subtype_iff, minkowski_le_top_iff] at hle
  simp only [coe_smul, spaceTranslation_smul] at hle
  simp [spaceVec] at hle
  subst hle
  exact Subtype.ext (map_one _)

/-- The slice `t = 0` of `𝐌ⁿ`, on the subtype `⊤`. -/
theorem isCauchySurface_slice_top :
    (flatCausality (d + 1) (⊤ : Opens (Minkowski (d + 1)))).IsCauchySurface
      (Subtype.val ⁻¹' graph (fun _ : EuclideanSpace ℝ (Fin (d + 1)) => (0 : ℝ))) :=
  (isCauchySurfaceOn_iff ⊤ (fun _ _ => trivial)).1
    ((minkowski (d + 1)).isCauchySurfaceOn_top.2 isCauchySurface_graph_zero)

/-- `𝐌ⁿ` (the open set `⊤`) is connected. -/
theorem isConnected_top : IsConnected ((⊤ : Opens (Minkowski d)) : Set (Minkowski d)) := by
  rw [Opens.coe_top]; exact isConnected_univ

/-- **Witness for the descent** (l.209–211): `ℤ e₁\𝐌ⁿ` is GH in Barbot's sense, through
`barbotGH_toFlatSpacetime`, the slice `t = 0` being `ℤ e₁`-invariant. -/
theorem barbotGH_spaceGroup :
    BarbotGH (toFlatSpacetime (spaceGroup d) ⊤ isConnected_top) :=
  barbotGH_toFlatSpacetime (spaceGroup d) ⊤ isConnected_top actsAcausally_spaceGroup
    (fun ⟨_, n, rfl⟩ p hp => by
      simp only [mem_preimage, mem_graph, coe_smul, fst_spaceTranslation_smul] at hp ⊢
      exact hp)
    isCauchySurface_slice_top


end FlatQuotient

end Causal.Flat
