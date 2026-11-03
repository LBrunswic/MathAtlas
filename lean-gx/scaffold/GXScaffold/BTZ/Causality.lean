import GXScaffold.BTZ.Model
import GXScaffold.BTZ.Rigid
import Causal.ArcConnected
import Causal.SingularFlat
import Causal.Static
import Causal.Minkowski
import Causal.CauchyExtension
import Causal.Flat.Form
import Causal.Flat.CBGSlice
import Causal.CurvesExtend
import Causal.Flat.Cosmological
import Causal.GXSingular
import Causal.Flat.IsomCausal

/-!
# `GXScaffold.BTZ.Causality` — the causality of `𝔼₀` and of `Y = 𝕄 ⊕ 𝔼₀`, from causal curves

Package WP-41e (WAVE5-PLAN.md, WP-39e; round 2 after `AUDIT-2.json`: `chartIso_mem` closed). `papers/gx`,
§4.2–4.3 (`RamcovGX.tex:2193–2246`, the orders of `𝐄^{1,2}` and "future causal or chronological
curves are curves that are locally increasing") extended to `𝔼₀` as l.2313 asks ("Causal notions
introduced in the section `sec:mess` above extend naturally to `BTZ̃`-manifolds and
`BTZ`-manifolds"), read by DEC-33 (ETT's causality from curves, `defi:causal_Ealpha`).

**No ledger label is marked.** This is infrastructure for Section 4. One row is touched,
unmarked: `lem:manifolds_manifolds_causally_connected` (l.2329) for the model `𝔼₀` alone
(`GX.E0.causallyArcConnected`; the lemma is about every `BTZ`-manifold, so the row is not closed;
`def:singular_manifold_endowed_causal`, l.2319, is read as `Causal.Causality.CausallyArcConnected`).

## What is built (0 `sorry`)

* `𝔼₀ = ℝ × ℂ` in the paper's `(τ, z = r e^{iθ})` (`GX.E0`), `f = τ − r/2` (`GX.E0.fcoord`),
  `h = τ + r` (`GX.E0.hcoord`), the BTZ line (`GX.E0.axis`). Local relations `GX.E0.Le`, `GX.E0.Lt`
  (developments `btzPaperNull (τ, r, θ)` differing by a future causal / timelike vector, winding
  free), closed form `GX.E0.nullCone_lift_iff`; transitive, push-up for the local relations.
* **The causality** `GX.E0.causality` from curves (`GX.E0.CLe`, `GX.E0.CLt`), `I^±_U` open in every
  `U` at every point; globally `≤ = Le`, `≪ = Lt` (`GX.E0.le_top_iff`, `GX.E0.lt_top_iff`).
* **The calculus** `0 ≤ Δr ≤ 2Δτ`, `τ, r, f, h` monotone (`GX.E0.calculus_le`, strict
  `GX.E0.calculus_lt`); the metric control `dist x y ≤ 3(τ_y − τ_x)` along `≼` (`GX.E0.Le.dist_le`).
* **At a BTZ point `p`**: `J⁺(p) = {f ≥ τ_p}`, `I⁺(p) = {r > 0, f > τ_p}` globally and in every ball
  (`GX.E0.Jplus_axis`, `GX.E0.Iplus_axis`, `GX.E0.Iplus_ball_axis`), `J⁻(p)` the half-line below,
  `I⁻_U(p) = ∅` (`GX.E0.Iminus_axis`); **`Causal.Causality.BTZAxioms`** with DEC-64's `Iplus_of_lt`
  (`GX.E0.btzAxioms`); DEC-64's refutation of `Iplus_eq` witnessed (`GX.E0.Iplus_ne_Jplus_diff`).
* `Z⁺ = 𝔼₀`, `Z⁻ = 𝔼₀ ∖ sing₀`, tarentin; **`J^±(V)` open for every open `V`, BTZ points included**
  (`GX.E0.isOpen_Jplus`, `GX.E0.isOpen_Jminus`, lemma K's obligation); `J^±(x)` closed
  (`GX.E0.isClosed_Jplus`, `GX.E0.isClosed_Jminus`); **strongly causal** (`GX.E0.stronglyCausal`);
  causal, causally arc-connected, absolutely minimal; `h` a time function, curves extend.
* **Diamonds form a basis** (`GX.E0.diamonds_basis`: `p, q ∈ U` with `x ∈ Int J(p,q) ⊆ J(p,q) ⊆ U`,
  BTZ points included; `GX.E0.nhds_hasBasis_openDiamond`); the Alexandrov topology is the topology
  (`GX.E0.alexandrovTopology_eq`).
* Off the axis the sector charts are `Causal.ChartIso`/`Causal.IsEMorphismOn` onto `𝐌³`
  (`GX.E0.chartIso_sectorChart`); **the generators of `Isom(𝔼₀)` are chart isomorphisms**:
  `τ`-translations and rotations (`GX.E0.chartIso_tauShift`, `GX.E0.chartIso_rotE0`, both preserve
  the axis), through `GX.E0.chartIso_of_homeo`.
* `Y = 𝕄 ⊕ 𝔼₀` (`GX.E0.ModelY`, `GX.E0.causalityY`); **the `LocalModel` fields
  `absolutelyMinimalOn_Y`, `coneSliceFuture` (`GX.E0.coneSliceFuture_Y`) and `coneSlicePast` at
  every point (`GX.E0.coneSlicePast_Y`)**. At a BTZ point `w` (`GX.E0.sliceAt_past_of_mem_axis`):
  `K = J⁺(w) ∩ {h = c} = {f ≥ τ_w, h = c}`, `c = τ_w + δ/4`; an open `V ⊇ K` contains
  `{f > τ_w − η, h = c}` (compactness), the level `{h = c}` of
  `N = {f > a, h < b, r < 2(c − a)/3}` (`GX.E0.sliceDom`), a Cauchy surface of `N`
  (`GX.E0.isCauchySurfaceOn_sliceDom`: an inextensible curve of `N` has a limit at an end that
  stays below / above the level, which is in `N`, so it would extend —
  `GX.E0.futureExtensible_sliceDom`, `GX.E0.pastExtensible_sliceDom`).
* **`Causal.SingularFlatAxioms` for `𝔼₀` given push-up** (`GX.E0.singularFlatAxioms_of_pushUp`,
  `sing = GX.E0.singE0`): every other field proved.
* Model's `𝔼₀`: `GX.E0.toPaper : GX.BTZE0 ≃ₜ E0`, the transported `GX.E0.causalityYBTZ` on
  `𝕄 ⊕ BTZE0` (Rigid's `E0Y` carrier) with `absolutelyMinimalOn_YBTZ`, `coneSliceFuture_YBTZ`,
  `coneSlicePast_YBTZ` (every point).
* **`LocalModel.chartIso_mem` for `𝔐E₀`** (`GX.E0.chartIso_mem_e0Groupoid`: every element of
  Rigid's `GX.e0Groupoid` is a `Causal.ChartIso` of `causalityYBTZ`, BTZ points included). The
  charts of `BTZE0`'s maximal a.e. atlas are chart isomorphisms (`GX.E0.chartIso_aeAtlas`: locally
  `g •` a sector chart, `btz_chart_eq_smul_btzPaperDev`), hence Rigid's `e0Atlas`
  (`GX.E0.chartIso_e0Atlas`); at a regular point an element of `G` is `c'⁻¹ ∘ g ∘ c`
  (`GX.E0.isoNear_of_mem_e0Groupoid_reg`); at a BTZ point it is read in `𝔼₀`'s coordinates
  (`GX.E0.paperConj`) and **a partial homeomorphism of `𝔼₀` preserving the axis and a chart
  isomorphism near its regular points is one** (`GX.E0.chartIso_of_axis`: causal curves through
  the axis are mapped by the orientation along the axis, `GX.E0.orientation_axis`, and the
  closedness of `J^±`, `GX.E0.le_ends_of_leaves`); the local isomorphisms glue by absolute
  minimality (`GX.E0.chartIso_of_isoNear`, the argument of `Causal.chartIso_of_mem_maximalAtlas`).

## Hypothesis checklist

| paper / dispatch | here |
|---|---|
| `𝔼₀`, `−2dτdr + dr² + r²dθ²` (l.1944) | ✓ through Model's `btzPaperNull` |
| curves "locally increasing" (l.2217), DEC-33 | ✓ `Causal.CurveOn` for `Le` |
| `0 ≤ ṙ ≤ 2τ̇`, `f`, `h` monotone | ✓ integrated (`calculus_le`) |
| `I^±` open; `J^±(V)` open, BTZ points included | ✓ every `U`; `J^±(V)` for `U = ⊤` (lemma K's form) |
| diamonds a basis | ✓ (full diamonds; `I⁻ = ∅` on the axis) |
| `LocalModel`: `absolutelyMinimalOn_Y`, `coneSliceFuture`, `coneSlicePast` | ✓ verbatim |
| `LocalModel.chartIso_mem` | ✓ verbatim for Rigid's `e0Groupoid` (`chartIso_mem_e0Groupoid`) |

## SCOPE (disclosed)

* (a) The causality is built on `E0 = ℝ × ℂ` from the developing map alone and transported to
  `GX.BTZE0` by `toPaper`; `btzE0Structure` is not used; Rigid's `e0SingY 0 = toPaperY ⁻¹' singY0`
  and the identification with Model's structure are WP-39f's assembly lemmas.
* (b) `chartIso_mem` is proved for Rigid's `e0Groupoid` (this file imports
  `GXScaffold.BTZ.Rigid`, round 2); it uses no rigidity (`localUnique_sing`): continuity, the
  axis-to-axis property of `G` and its regular charts suffice. `LocalModel`'s (O1) is this theorem.
* (c) Massive cones `𝔼_α` (DEC-74) are not part of `Y` here.
* (d) **Push-up in every open set** (`SingularFlatAxioms.pushUp`) and **`CausallyOpenFuture`**
  (`J⁺_U(V)` open for `V ⊆ U`, `U ≠ ⊤`) are not proved: both need a chain argument along a causal
  curve of `U` (local push-up off the axis through the sector charts, `Iplus_of_lt` read in `U` at
  the axis). Push-up holds globally (`Lt.trans_le`, `Le.trans_lt`); `CausallyOpenFuture` follows
  from local push-up and local `Iplus_of_lt`. Local push-up is proved in `GXScaffold.BTZ.LocalModel`
  (`GX.E0LM.e0_pushUp`), which imports this file.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `731ed99`.
-/

namespace GX

open Set Filter Topology Function Complex
open scoped Real

/-! ### `𝔼₀` in the paper's coordinates -/

/-- **The BTZ model space `𝔼₀` in the paper's cylindrical coordinates** (`RamcovGX.tex:1944`): a
point is `(τ, z)` with `z = r e^{iθ}`, `ℝ × ℂ` with its product (natural) topology. -/
abbrev E0 : Type := ℝ × ℂ

namespace E0

/-- The radial coordinate `r = |z|`. -/
noncomputable def rad (x : E0) : ℝ := ‖x.2‖

/-- `f = τ − r/2`, non-decreasing along future causal curves (constant on the future light cones
of the BTZ points). -/
noncomputable def fcoord (x : E0) : ℝ := x.1 - rad x / 2

/-- `h = τ + r`, non-decreasing along future causal curves, a time function. -/
noncomputable def hcoord (x : E0) : ℝ := x.1 + rad x

/-- **The singular (BTZ) line** `{r = 0}` (`RamcovGX.tex:1944`). -/
def axis : Set E0 := {x | x.2 = 0}

theorem rad_nonneg (x : E0) : 0 ≤ rad x := norm_nonneg _

theorem rad_eq_zero {x : E0} : rad x = 0 ↔ x ∈ axis := norm_eq_zero

theorem rad_pos {x : E0} : 0 < rad x ↔ x ∉ axis := norm_pos_iff

theorem continuous_rad : Continuous rad := continuous_norm.comp continuous_snd

theorem continuous_fcoord : Continuous fcoord :=
  continuous_fst.sub (continuous_rad.div_const 2)

theorem continuous_hcoord : Continuous hcoord := continuous_fst.add continuous_rad

theorem isClosed_axis : IsClosed axis := isClosed_eq continuous_snd continuous_const

/-! ### The null cone of `𝐌³` in null coordinates -/

/-- The closed future cone of `(ℝ³, nullQ)`, `nullQ (a, b, c) = −ab + c²`: `a, b ≥ 0`, `c² ≤ ab`
(`nullCone_iff_minkowski`: the causal future of `0` in `Causal.Minkowski 2` through `nullToMink`). -/
def NullCone (V : ℝ × ℝ × ℝ) : Prop := 0 ≤ V.1 ∧ 0 ≤ V.2.1 ∧ V.2.2 ^ 2 ≤ V.1 * V.2.1

/-- The open future cone: `b > 0`, `c² < ab` (then `a > 0`). -/
def NullConeLt (V : ℝ × ℝ × ℝ) : Prop := 0 < V.2.1 ∧ V.2.2 ^ 2 < V.1 * V.2.1

theorem NullConeLt.fst_pos {V : ℝ × ℝ × ℝ} (h : NullConeLt V) : 0 < V.1 := by
  obtain ⟨hb, hc⟩ := h
  by_contra ha
  have ha' : V.1 ≤ 0 := not_lt.1 ha
  nlinarith [sq_nonneg V.2.2]

theorem NullConeLt.nullCone {V : ℝ × ℝ × ℝ} (h : NullConeLt V) : NullCone V :=
  ⟨h.fst_pos.le, h.1.le, h.2.le⟩

theorem nullCone_zero : NullCone 0 := ⟨le_rfl, le_rfl, by simp⟩

/-- The cross term of two cone vectors: `2 c₁ c₂ ≤ a₁ b₂ + a₂ b₁`. -/
theorem cross_le {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ} (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (h₁ : c₁ ^ 2 ≤ a₁ * b₁)
    (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) (h₂ : c₂ ^ 2 ≤ a₂ * b₂) :
    2 * (c₁ * c₂) ≤ a₁ * b₂ + a₂ * b₁ := by
  have hprod : (c₁ * c₂) ^ 2 ≤ (a₁ * b₁) * (a₂ * b₂) := by
    rw [mul_pow]; exact mul_le_mul h₁ h₂ (sq_nonneg _) (mul_nonneg ha₁ hb₁)
  have hamgm : 4 * ((a₁ * b₁) * (a₂ * b₂)) ≤ (a₁ * b₂ + a₂ * b₁) ^ 2 := by
    nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]
  have hS : 0 ≤ a₁ * b₂ + a₂ * b₁ := by positivity
  have h4 : (2 * (c₁ * c₂)) ^ 2 ≤ (a₁ * b₂ + a₂ * b₁) ^ 2 := by nlinarith
  exact (abs_le_of_sq_le_sq' h4 hS).2

theorem NullCone.add {V W : ℝ × ℝ × ℝ} (hV : NullCone V) (hW : NullCone W) : NullCone (V + W) := by
  obtain ⟨ha₁, hb₁, h₁⟩ := hV
  obtain ⟨ha₂, hb₂, h₂⟩ := hW
  have hx := cross_le ha₁ hb₁ h₁ ha₂ hb₂ h₂
  refine ⟨add_nonneg ha₁ ha₂, add_nonneg hb₁ hb₂, ?_⟩
  simp only [Prod.fst_add, Prod.snd_add]
  nlinarith

theorem NullConeLt.add_nullCone {V W : ℝ × ℝ × ℝ} (hV : NullConeLt V) (hW : NullCone W) :
    NullConeLt (V + W) := by
  have hV' := hV.nullCone
  obtain ⟨ha₁, hb₁, h₁⟩ := hV'
  obtain ⟨hb₁', h₁'⟩ := hV
  obtain ⟨ha₂, hb₂, h₂⟩ := hW
  have hx := cross_le ha₁ hb₁ h₁ ha₂ hb₂ h₂
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Prod.snd_add]; linarith
  · simp only [Prod.fst_add, Prod.snd_add]
    nlinarith

theorem NullCone.add_nullConeLt {V W : ℝ × ℝ × ℝ} (hV : NullCone V) (hW : NullConeLt W) :
    NullConeLt (V + W) := by
  rw [add_comm]; exact hW.add_nullCone hV

theorem NullCone.smul {V : ℝ × ℝ × ℝ} (hV : NullCone V) {s : ℝ} (hs : 0 ≤ s) :
    NullCone (s • V) := by
  obtain ⟨ha, hb, h⟩ := hV
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul]; positivity
  · simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]; positivity
  · simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
    have : (s * V.2.2) ^ 2 = s ^ 2 * V.2.2 ^ 2 := by ring
    rw [this, show s * V.1 * (s * V.2.1) = s ^ 2 * (V.1 * V.2.1) by ring]
    exact mul_le_mul_of_nonneg_left h (sq_nonneg s)

theorem NullConeLt.smul {V : ℝ × ℝ × ℝ} (hV : NullConeLt V) {s : ℝ} (hs : 0 < s) :
    NullConeLt (s • V) := by
  obtain ⟨hb, h⟩ := hV
  refine ⟨?_, ?_⟩
  · simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]; positivity
  · simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
    have : (s * V.2.2) ^ 2 = s ^ 2 * V.2.2 ^ 2 := by ring
    rw [this, show s * V.1 * (s * V.2.1) = s ^ 2 * (V.1 * V.2.1) by ring]
    exact mul_lt_mul_of_pos_left h (by positivity)

theorem isOpen_nullConeLt : IsOpen {V : ℝ × ℝ × ℝ | NullConeLt V} := by
  have h1 : Continuous fun V : ℝ × ℝ × ℝ => V.2.1 := continuous_snd.fst
  have h2 : Continuous fun V : ℝ × ℝ × ℝ => V.2.2 ^ 2 := continuous_snd.snd.pow 2
  have h3 : Continuous fun V : ℝ × ℝ × ℝ => V.1 * V.2.1 := continuous_fst.mul continuous_snd.fst
  exact (isOpen_lt continuous_const h1).inter (isOpen_lt h2 h3)

/-! ### The developed lift and the two relations -/

/-- **The null coordinates of the development of `x` with angle `θ`**: `btzPaperNull (τ, r, θ) =
(2τ + rθ² − r, r, −rθ)`, i.e. `nullToMink.symm` of the paper's `D(τ, r, θ)` (`btzPaperDev`,
`GXScaffold.BTZ.Model`). -/
noncomputable def lift (x : E0) (θ : ℝ) : ℝ × ℝ × ℝ := btzPaperNull (x.1, rad x, θ)

/-- `θ` is an angle of `x`: `z = r e^{iθ}` (every `θ` on the axis). -/
def Polar (x : E0) (θ : ℝ) : Prop := x.2 = (rad x : ℂ) * cexp (θ * I)

variable {x y z : E0} {θ θ' θ₁ θ₂ θ₃ : ℝ}

theorem polar_arg (x : E0) : Polar x (arg x.2) := (norm_mul_exp_arg_mul_I x.2).symm

theorem Polar.of_axis (hx : x ∈ axis) (θ : ℝ) : Polar x θ := by
  have : rad x = 0 := rad_eq_zero.2 hx
  simp only [Polar, this, Complex.ofReal_zero, zero_mul]
  exact hx

theorem Polar.add_int (h : Polar x θ) (k : ℤ) : Polar x (θ + 2 * π * k) := by
  unfold Polar at h ⊢
  rw [h]
  congr 1
  rw [show ((θ + 2 * π * k : ℝ) : ℂ) * I = θ * I + k * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem Polar.eq_add_int (h : Polar x θ) (h' : Polar x θ') (hx : 0 < rad x) :
    ∃ k : ℤ, θ' = θ + 2 * π * k := by
  unfold Polar at h h'
  have hr : (rad x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  have he : cexp (θ' * I) = cexp (θ * I) := mul_left_cancel₀ hr (h'.symm.trans h)
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have : ((θ' : ℝ) : ℂ) * I = ((θ + 2 * π * n : ℝ) : ℂ) * I := by rw [hn]; push_cast; ring
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero this

theorem lift_sub (x y : E0) (θ₁ θ₂ : ℝ) :
    lift y θ₂ - lift x θ₁ = (2 * (y.1 - x.1) + rad y * θ₂ ^ 2 - rad x * θ₁ ^ 2 - (rad y - rad x),
      rad y - rad x, rad x * θ₁ - rad y * θ₂) := by
  simp only [lift, btzPaperNull]
  ext <;> simp <;> ring

/-- The causal relation of two developed points in the paper's coordinates. -/
def ClosedLe (τ₁ r₁ τ₂ r₂ δ : ℝ) : Prop :=
  τ₁ ≤ τ₂ ∧ r₁ ≤ r₂ ∧ r₁ * r₂ * δ ^ 2 ≤ (r₂ - r₁) * (2 * (τ₂ - τ₁) - (r₂ - r₁))

/-- The chronological relation of two developed points in the paper's coordinates. -/
def ClosedLt (τ₁ r₁ τ₂ r₂ δ : ℝ) : Prop :=
  r₁ < r₂ ∧ r₁ * r₂ * δ ^ 2 < (r₂ - r₁) * (2 * (τ₂ - τ₁) - (r₂ - r₁))

theorem closedLt_closedLe {τ₁ r₁ τ₂ r₂ δ : ℝ} (h₁ : 0 ≤ r₁) (h : ClosedLt τ₁ r₁ τ₂ r₂ δ) :
    ClosedLe τ₁ r₁ τ₂ r₂ δ := by
  obtain ⟨hr, hq⟩ := h
  have h0 : 0 ≤ r₁ * r₂ * δ ^ 2 := by have := h₁.trans hr.le; positivity
  refine ⟨?_, hr.le, hq.le⟩
  by_contra hτ
  have : 2 * (τ₂ - τ₁) - (r₂ - r₁) < 0 := by linarith [not_le.1 hτ]
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hr) this]

/-- The algebraic identity behind the closed forms: `ab − c² = Δr(2Δτ − Δr) − r₁r₂(θ₂−θ₁)²`. -/
theorem lift_sub_key (x y : E0) (θ₁ θ₂ : ℝ) :
    (lift y θ₂ - lift x θ₁).1 * (lift y θ₂ - lift x θ₁).2.1 - (lift y θ₂ - lift x θ₁).2.2 ^ 2 =
      (rad y - rad x) * (2 * (y.1 - x.1) - (rad y - rad x)) - rad x * rad y * (θ₂ - θ₁) ^ 2 := by
  rw [lift_sub]; ring

/-- **The causal cone in the paper's coordinates**: the developed vector from `x` (angle `θ₁`) to
`y` (angle `θ₂`) is future causal iff `τ₁ ≤ τ₂`, `r₁ ≤ r₂` and
`r₁ r₂ (θ₂−θ₁)² ≤ (r₂−r₁)(2(τ₂−τ₁) − (r₂−r₁))` — the integrated form of `0 ≤ ṙ ≤ 2τ̇`. -/
theorem nullCone_lift_iff (x y : E0) (θ₁ θ₂ : ℝ) :
    NullCone (lift y θ₂ - lift x θ₁) ↔ ClosedLe x.1 (rad x) y.1 (rad y) (θ₂ - θ₁) := by
  have key := lift_sub_key x y θ₁ θ₂
  have h1 := rad_nonneg x
  have h2 := rad_nonneg y
  have hA : (lift y θ₂ - lift x θ₁).1 =
      2 * (y.1 - x.1) - (rad x * θ₁ - rad y * θ₂) * (θ₁ + θ₂) - (rad y - rad x) * (1 + θ₁ * θ₂) := by
    rw [lift_sub]; ring
  have hB : (lift y θ₂ - lift x θ₁).2.1 = rad y - rad x := by rw [lift_sub]
  have hC : (lift y θ₂ - lift x θ₁).2.2 = rad x * θ₁ - rad y * θ₂ := by rw [lift_sub]
  unfold NullCone ClosedLe
  constructor
  · rintro ⟨ha, hb, hc⟩
    rw [hB] at hb
    refine ⟨?_, by linarith, by linarith⟩
    rcases hb.lt_or_eq with hb | hb
    · have h0 : 0 ≤ rad x * rad y * (θ₂ - θ₁) ^ 2 := by positivity
      have : 0 ≤ (rad y - rad x) * (2 * (y.1 - x.1) - (rad y - rad x)) := by linarith
      have h3 : 0 ≤ 2 * (y.1 - x.1) - (rad y - rad x) := nonneg_of_mul_nonneg_right
        (by linarith [mul_comm (rad y - rad x) (2 * (y.1 - x.1) - (rad y - rad x))]) hb
      linarith
    · have hc0 : (lift y θ₂ - lift x θ₁).2.2 = 0 := by
        rw [hB, ← hb, mul_zero] at hc
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm hc (sq_nonneg _))
      rw [hA, ← hC, hc0, ← hb] at ha
      linarith
  · rintro ⟨hτ, hr, hq⟩
    have hb : 0 ≤ (lift y θ₂ - lift x θ₁).2.1 := by rw [hB]; linarith
    refine ⟨?_, hb, by linarith⟩
    rcases hb.lt_or_eq with hb' | hb'
    · have : 0 ≤ (lift y θ₂ - lift x θ₁).1 * (lift y θ₂ - lift x θ₁).2.1 := by
        nlinarith [sq_nonneg (lift y θ₂ - lift x θ₁).2.2]
      exact nonneg_of_mul_nonneg_left this hb'
    · have hrr : rad y = rad x := by rw [hB] at hb'; linarith
      have hq' : (rad x * (θ₂ - θ₁)) ^ 2 ≤ 0 := by
        rw [hrr, sub_self, zero_mul] at hq
        nlinarith
      have hz : rad x * (θ₂ - θ₁) = 0 := pow_eq_zero_iff two_ne_zero |>.1
        (le_antisymm hq' (sq_nonneg _))
      rw [hA, hrr]
      have : (rad x * θ₁ - rad x * θ₂) = -(rad x * (θ₂ - θ₁)) := by ring
      rw [this, hz]
      simp only [neg_zero, zero_mul, sub_zero, sub_self, zero_mul]
      linarith

/-- **The chronological cone in the paper's coordinates.** -/
theorem nullConeLt_lift_iff (x y : E0) (θ₁ θ₂ : ℝ) :
    NullConeLt (lift y θ₂ - lift x θ₁) ↔ ClosedLt x.1 (rad x) y.1 (rad y) (θ₂ - θ₁) := by
  have key := lift_sub_key x y θ₁ θ₂
  have hB : (lift y θ₂ - lift x θ₁).2.1 = rad y - rad x := by rw [lift_sub]
  unfold NullConeLt ClosedLt
  rw [hB]
  constructor
  · rintro ⟨hb, hc⟩; exact ⟨by linarith, by rw [hB] at key; linarith⟩
  · rintro ⟨hr, hq⟩; exact ⟨by linarith, by rw [hB] at key; linarith⟩

/-- **`x ≼ y` in `𝔼₀`**: some developments of `x` and `y` (angles `θ₁`, `θ₂`) are causally related
in `𝐌³`; the winding `θ₂ − θ₁` is free (`𝔼₀ = ⟨P⟩\J⁺(Δ)`). -/
def Le (x y : E0) : Prop :=
  ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ NullCone (lift y θ₂ - lift x θ₁)

/-- **`x ≺ y` in `𝔼₀`**: some developments are chronologically related. -/
def Lt (x y : E0) : Prop :=
  ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ NullConeLt (lift y θ₂ - lift x θ₁)

theorem le_iff_closed : Le x y ↔
    ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ ClosedLe x.1 (rad x) y.1 (rad y) (θ₂ - θ₁) := by
  simp only [Le, nullCone_lift_iff]

theorem lt_iff_closed : Lt x y ↔
    ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ ClosedLt x.1 (rad x) y.1 (rad y) (θ₂ - θ₁) := by
  simp only [Lt, nullConeLt_lift_iff]

theorem Lt.le (h : Lt x y) : Le x y := by
  obtain ⟨θ₁, θ₂, h₁, h₂, h⟩ := h
  exact ⟨θ₁, θ₂, h₁, h₂, h.nullCone⟩

theorem le_refl' (x : E0) : Le x x :=
  ⟨arg x.2, arg x.2, polar_arg x, polar_arg x, by rw [sub_self]; exact nullCone_zero⟩

theorem Le.closed (h : Le x y) :
    x.1 ≤ y.1 ∧ rad x ≤ rad y ∧ 0 ≤ (rad y - rad x) * (2 * (y.1 - x.1) - (rad y - rad x)) := by
  obtain ⟨θ₁, θ₂, -, -, h⟩ := le_iff_closed.1 h
  have : 0 ≤ rad x * rad y * (θ₂ - θ₁) ^ 2 := by
    have := rad_nonneg x; have := rad_nonneg y; positivity
  exact ⟨h.1, h.2.1, this.trans h.2.2⟩

theorem Lt.closed (h : Lt x y) :
    rad x < rad y ∧ 0 < (rad y - rad x) * (2 * (y.1 - x.1) - (rad y - rad x)) := by
  obtain ⟨θ₁, θ₂, -, -, h⟩ := lt_iff_closed.1 h
  have : 0 ≤ rad x * rad y * (θ₂ - θ₁) ^ 2 := by
    have := rad_nonneg x; have := rad_nonneg y; positivity
  exact ⟨h.1, this.trans_lt h.2⟩

/-- Re-choosing the angle of the source: `Le y z` holds with any prescribed angle of `y` when `y`
is off the axis. -/
theorem Le.realign (h : Le y z) (hy : Polar y θ) (hr : 0 < rad y) :
    ∃ θ', Polar z θ' ∧ NullCone (lift z θ' - lift y θ) := by
  obtain ⟨θ₂, θ₃, h₂, h₃, h⟩ := h
  obtain ⟨k, hk⟩ := h₂.eq_add_int hy hr
  refine ⟨θ₃ + 2 * π * k, h₃.add_int k, ?_⟩
  rw [nullCone_lift_iff] at h ⊢
  rwa [hk, show θ₃ + 2 * π * k - (θ₂ + 2 * π * k) = θ₃ - θ₂ by ring]

theorem Lt.realign (h : Lt y z) (hy : Polar y θ) (hr : 0 < rad y) :
    ∃ θ', Polar z θ' ∧ NullConeLt (lift z θ' - lift y θ) := by
  obtain ⟨θ₂, θ₃, h₂, h₃, h⟩ := h
  obtain ⟨k, hk⟩ := h₂.eq_add_int hy hr
  refine ⟨θ₃ + 2 * π * k, h₃.add_int k, ?_⟩
  rw [nullConeLt_lift_iff] at h ⊢
  rwa [hk, show θ₃ + 2 * π * k - (θ₂ + 2 * π * k) = θ₃ - θ₂ by ring]

theorem lift_sub_add (x y z : E0) (θ₁ θ₂ θ₃ : ℝ) :
    lift z θ₃ - lift x θ₁ = (lift z θ₃ - lift y θ₂) + (lift y θ₂ - lift x θ₁) := by abel

theorem Le.trans (h₁ : Le x y) (h₂ : Le y z) : Le x z := by
  obtain ⟨θ₁, θ₂, hx, hy, h⟩ := h₁
  rcases (rad_nonneg y).lt_or_eq with hr | hr
  · obtain ⟨θ₃, hz, h'⟩ := h₂.realign hy hr
    exact ⟨θ₁, θ₃, hx, hz, lift_sub_add x y z θ₁ θ₂ θ₃ ▸ h'.add h⟩
  · have hc := Le.closed ⟨θ₁, θ₂, hx, hy, h⟩
    obtain ⟨θ₂', θ₃, -, hz, h''⟩ := le_iff_closed.1 h₂
    have hx0 : rad x = 0 := le_antisymm (hr ▸ hc.2.1) (rad_nonneg x)
    refine le_iff_closed.2 ⟨θ₁, θ₃, hx, hz, ?_⟩
    obtain ⟨hτ, hrz, hq⟩ := h''
    rw [← hr] at hq hrz
    rw [hx0]
    refine ⟨hc.1.trans hτ, rad_nonneg z, ?_⟩
    have := rad_nonneg z
    simp only [zero_mul, sub_zero] at hq ⊢
    nlinarith [hc.1]

theorem Lt.trans_le (h₁ : Lt x y) (h₂ : Le y z) : Lt x z := by
  obtain ⟨θ₁, θ₂, hx, hy, h⟩ := h₁
  have hr : 0 < rad y := (rad_nonneg x).trans_lt (Lt.closed ⟨θ₁, θ₂, hx, hy, h⟩).1
  obtain ⟨θ₃, hz, h'⟩ := h₂.realign hy hr
  exact ⟨θ₁, θ₃, hx, hz, lift_sub_add x y z θ₁ θ₂ θ₃ ▸ h'.add_nullConeLt h⟩

theorem Le.trans_lt (h₁ : Le x y) (h₂ : Lt y z) : Lt x z := by
  obtain ⟨θ₁, θ₂, hx, hy, h⟩ := h₁
  rcases (rad_nonneg y).lt_or_eq with hr | hr
  · obtain ⟨θ₃, hz, h'⟩ := h₂.realign hy hr
    exact ⟨θ₁, θ₃, hx, hz, lift_sub_add x y z θ₁ θ₂ θ₃ ▸ h'.add_nullCone h⟩
  · have hc := Le.closed ⟨θ₁, θ₂, hx, hy, h⟩
    obtain ⟨θ₂', θ₃, -, hz, h''⟩ := lt_iff_closed.1 h₂
    have hx0 : rad x = 0 := le_antisymm (hr ▸ hc.2.1) (rad_nonneg x)
    refine lt_iff_closed.2 ⟨θ₁, θ₃, hx, hz, ?_⟩
    obtain ⟨hrz, hq⟩ := h''
    rw [← hr] at hq hrz
    rw [hx0]
    refine ⟨hrz, ?_⟩
    simp only [zero_mul, sub_zero] at hq ⊢
    nlinarith [hc.1]

theorem Lt.trans (h₁ : Lt x y) (h₂ : Lt y z) : Lt x z := h₁.trans_le h₂.le

/-- `|x| ≤ |x + 2πk|` for `|x| ≤ π`: the principal angle is the shortest winding. -/
theorem abs_le_abs_add_two_pi_mul {x : ℝ} (hx : |x| ≤ π) (k : ℤ) : |x| ≤ |x + 2 * π * k| := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 hk
    have : x + 2 * π * k ≤ -π := by
      have := (abs_le.1 hx).2; nlinarith [Real.pi_pos]
    exact hx.trans (by rw [abs_of_nonpos (by linarith [Real.pi_pos] : x + 2 * π * k ≤ 0)]; linarith)
  · simp [hk]
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : π ≤ x + 2 * π * k := by
      have := (abs_le.1 hx).1; nlinarith [Real.pi_pos]
    exact hx.trans (by rw [abs_of_nonneg (by linarith [Real.pi_pos] : 0 ≤ x + 2 * π * k)]; linarith)

/-- With angles less than `π` apart, the relation `Lt` is read on those very angles. -/
theorem Lt.of_polar (h : Lt x y) (hx : Polar x θ₁) (hy : Polar y θ₂) (hθ : |θ₂ - θ₁| ≤ π) :
    NullConeLt (lift y θ₂ - lift x θ₁) := by
  obtain ⟨θ₁', θ₂', hx', hy', h⟩ := h
  rw [nullConeLt_lift_iff] at h ⊢
  obtain ⟨hr, hq⟩ := h
  refine ⟨hr, lt_of_le_of_lt ?_ hq⟩
  rcases (rad_nonneg x).lt_or_eq with hx0 | hx0
  · obtain ⟨k₁, hk₁⟩ := hx.eq_add_int hx' hx0
    obtain ⟨k₂, hk₂⟩ := hy.eq_add_int hy' (hx0.trans hr)
    have hd : θ₂' - θ₁' = (θ₂ - θ₁) + 2 * π * ((k₂ - k₁ : ℤ) : ℝ) := by
      rw [hk₁, hk₂]; push_cast; ring
    have habs := abs_le_abs_add_two_pi_mul hθ (k₂ - k₁)
    rw [← hd] at habs
    have : (θ₂ - θ₁) ^ 2 ≤ (θ₂' - θ₁') ^ 2 := sq_le_sq.2 habs
    have : 0 ≤ rad x * rad y := mul_nonneg (rad_nonneg x) (rad_nonneg y)
    exact mul_le_mul_of_nonneg_left (by assumption) this
  · rw [← hx0]; simp

theorem Le.of_polar (h : Le x y) (hx : Polar x θ₁) (hy : Polar y θ₂) (hθ : |θ₂ - θ₁| ≤ π) :
    NullCone (lift y θ₂ - lift x θ₁) := by
  obtain ⟨θ₁', θ₂', hx', hy', h⟩ := h
  rw [nullCone_lift_iff] at h ⊢
  obtain ⟨hτ, hr, hq⟩ := h
  refine ⟨hτ, hr, le_trans ?_ hq⟩
  rcases (rad_nonneg x).lt_or_eq with hx0 | hx0
  · obtain ⟨k₁, hk₁⟩ := hx.eq_add_int hx' hx0
    obtain ⟨k₂, hk₂⟩ := hy.eq_add_int hy' (hx0.trans_le hr)
    have hd : θ₂' - θ₁' = (θ₂ - θ₁) + 2 * π * ((k₂ - k₁ : ℤ) : ℝ) := by
      rw [hk₁, hk₂]; push_cast; ring
    have habs := abs_le_abs_add_two_pi_mul hθ (k₂ - k₁)
    rw [← hd] at habs
    have : (θ₂ - θ₁) ^ 2 ≤ (θ₂' - θ₁') ^ 2 := sq_le_sq.2 habs
    have : 0 ≤ rad x * rad y := mul_nonneg (rad_nonneg x) (rad_nonneg y)
    exact mul_le_mul_of_nonneg_left (by assumption) this
  · rw [← hx0]; simp

/-! ### Straight segments of `𝐌³`, read back in `𝔼₀` -/

/-- **The inverse of the development** on `{b > 0}` (and on the axis `{b = c = 0}`):
`(a, b, c) ↦ (τ, r e^{iθ})` with `r = b`, `θ = −c/b`, `τ = (a − c²/b + b)/2`. -/
noncomputable def unlift (R : ℝ × ℝ × ℝ) : E0 :=
  ((R.1 - R.2.2 ^ 2 / R.2.1 + R.2.1) / 2, (R.2.1 : ℂ) * cexp (↑(-(R.2.2 / R.2.1)) * I))

/-- The developed points `unlift` inverts: `b > 0`, or the axis `b = c = 0`. -/
def Adm (R : ℝ × ℝ × ℝ) : Prop := 0 < R.2.1 ∨ (R.2.1 = 0 ∧ R.2.2 = 0)

variable {P Q R : ℝ × ℝ × ℝ}

theorem Adm.nonneg (h : Adm R) : 0 ≤ R.2.1 := by
  rcases h with h | h
  · exact h.le
  · exact h.1.ge

theorem unlift_lift (hx : Polar x θ) : unlift (lift x θ) = x := by
  simp only [unlift, lift, btzPaperNull]
  rcases (rad_nonneg x).lt_or_eq with hr | hr
  · refine Prod.ext ?_ ?_
    · simp only
      field_simp
      ring
    · simp only
      rw [show -(-(rad x * θ) / rad x) = θ by field_simp]
      exact hx.symm
  · have hx0 : x.2 = 0 := rad_eq_zero.1 hr.symm
    rw [← hr]
    refine Prod.ext ?_ ?_
    · simp
    · simp [hx0]

theorem rad_unlift (hR : 0 ≤ R.2.1) : rad (unlift R) = R.2.1 := by
  simp only [rad, unlift, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR,
    norm_exp_ofReal_mul_I, mul_one]

theorem polar_unlift (hR : 0 ≤ R.2.1) : Polar (unlift R) (-(R.2.2 / R.2.1)) := by
  unfold Polar
  rw [rad_unlift hR]
  rfl

theorem lift_unlift (hR : Adm R) : lift (unlift R) (-(R.2.2 / R.2.1)) = R := by
  have hrad := rad_unlift hR.nonneg
  simp only [lift, btzPaperNull, hrad]
  rcases hR with hb | ⟨hb, hc⟩
  · refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only [unlift]; field_simp; ring
    · simp only; field_simp
  · obtain ⟨a, b, c⟩ := R
    simp only at hb hc
    subst hb hc
    simp [unlift]
    ring

/-- The straight segment `P + s(Q − P)` of `ℝ³`. -/
def seg (P Q : ℝ × ℝ × ℝ) (s : ℝ) : ℝ × ℝ × ℝ := P + s • (Q - P)

theorem seg_zero : seg P Q 0 = P := by simp [seg]

theorem seg_one : seg P Q 1 = Q := by simp [seg]

theorem seg_sub (P Q : ℝ × ℝ × ℝ) (s s' : ℝ) : seg P Q s' - seg P Q s = (s' - s) • (Q - P) := by
  simp only [seg, sub_smul]; abel

theorem seg_fst (P Q : ℝ × ℝ × ℝ) (s : ℝ) : (seg P Q s).1 = P.1 + s * (Q.1 - P.1) := rfl

theorem seg_snd_fst (P Q : ℝ × ℝ × ℝ) (s : ℝ) :
    (seg P Q s).2.1 = P.2.1 + s * (Q.2.1 - P.2.1) := rfl

theorem seg_snd_snd (P Q : ℝ × ℝ × ℝ) (s : ℝ) :
    (seg P Q s).2.2 = P.2.2 + s * (Q.2.2 - P.2.2) := rfl

theorem adm_seg (hP : Adm P) (hPQ : NullCone (Q - P)) {s : ℝ} (hs : 0 ≤ s) : Adm (seg P Q s) := by
  obtain ⟨-, hb, hc⟩ := hPQ
  simp only [Prod.snd_sub, Prod.fst_sub] at hb hc
  unfold Adm
  rw [seg_snd_fst, seg_snd_snd]
  rcases hP with hP | ⟨hP, hC⟩
  · left; nlinarith
  · rw [hP, hC] at hc ⊢
    rw [hP] at hb
    simp only [sub_zero, zero_add] at hb hc ⊢
    rcases (mul_nonneg hs hb).lt_or_eq with h | h
    · left; exact h
    · right
      refine ⟨h.symm, ?_⟩
      rcases hs.lt_or_eq with hs' | hs'
      · have hQ : Q.2.1 = 0 := (mul_eq_zero.1 h.symm).resolve_left hs'.ne'
        rw [hQ, mul_zero] at hc
        have : Q.2.2 = 0 := by nlinarith [sq_nonneg Q.2.2]
        simp [this]
      · simp [← hs']

theorem continuousAt_unlift (hR : R.2.1 ≠ 0) : ContinuousAt unlift R := by
  unfold unlift
  have h1 : ContinuousAt (fun R : ℝ × ℝ × ℝ => R.2.2 / R.2.1) R :=
    continuousAt_snd.snd.div continuousAt_snd.fst hR
  have h2 : ContinuousAt (fun R : ℝ × ℝ × ℝ => R.2.2 ^ 2 / R.2.1) R :=
    (continuousAt_snd.snd.pow 2).div continuousAt_snd.fst hR
  refine ContinuousAt.prodMk ?_ ?_
  · exact ((continuousAt_fst.sub h2).add continuousAt_snd.fst).div_const 2
  · refine (Complex.continuous_ofReal.continuousAt.comp continuousAt_snd.fst).mul ?_
    exact Complex.continuous_exp.continuousAt.comp
      ((Complex.continuous_ofReal.continuousAt.comp h1.neg).mul continuousAt_const)

theorem continuousOn_unlift_seg (hP : Adm P) (hPQ : NullCone (Q - P)) :
    ContinuousOn (fun s => unlift (seg P Q s)) (Icc 0 1) := by
  have hseg : Continuous (seg P Q) := by unfold seg; fun_prop
  rcases hP with hP | ⟨hP, hC⟩
  · intro s hs
    have hb : (seg P Q s).2.1 ≠ 0 := by
      rcases adm_seg (Or.inl hP) hPQ hs.1 with h | h
      · exact h.ne'
      · exfalso
        have := hPQ.2.1; simp only [Prod.snd_sub, Prod.fst_sub] at this
        have h' := h.1; rw [seg_snd_fst] at h'
        nlinarith [hs.1]
    exact ((continuousAt_unlift hb).comp hseg.continuousAt).continuousWithinAt
  · set g : ℝ → E0 := fun s => ((P.1 + s * (Q.1 - P.1) - s * (Q.2.2 ^ 2 / Q.2.1) + s * Q.2.1) / 2,
      ((s * Q.2.1 : ℝ) : ℂ) * cexp (↑(-(Q.2.2 / Q.2.1)) * I)) with hg
    have hgc : Continuous g := by rw [hg]; fun_prop
    refine hgc.continuousOn.congr fun s hs => ?_
    have hb := hPQ.2.1
    have hcq := hPQ.2.2
    simp only [Prod.snd_sub, Prod.fst_sub, hP, hC, sub_zero] at hb hcq
    simp only [hg, unlift, seg, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, hP, hC, smul_eq_mul, sub_zero, zero_add]
    rcases hs.1.lt_or_eq with hs0 | hs0
    · rcases hb.lt_or_eq with hb0 | hb0
      · refine Prod.ext ?_ ?_
        · simp only; field_simp
        · simp only
          rw [show s * Q.2.2 / (s * Q.2.1) = Q.2.2 / Q.2.1 by field_simp]
      · rw [← hb0] at hcq ⊢
        have : Q.2.2 = 0 := by nlinarith [sq_nonneg Q.2.2]
        simp [this]
    · simp [← hs0]

/-- The relation `R` restricted to the open set `N` (the family the curves of `Causal.Curves` are
taken for). -/
def relOn (R : E0 → E0 → Prop) (N : TopologicalSpace.Opens E0) (x y : E0) : Prop :=
  x ∈ N ∧ y ∈ N ∧ R x y

theorem isRelFamily_relOn {R : E0 → E0 → Prop} (hR : ∀ {x y z}, R x y → R y z → R x z) :
    Causal.IsRelFamily (relOn R) where
  mem_left h := h.1
  mem_right h := h.2.1
  trans h₁ h₂ := ⟨h₁.1, h₂.2.1, hR h₁.2.2 h₂.2.2⟩
  mono hN _ _ h := ⟨hN h.1, hN h.2.1, h.2.2⟩

/-- A continuous curve, `R`-increasing on `[a, b]`, is a curve of every open set containing it. -/
theorem curveOn_of_continuousOn {R : E0 → E0 → Prop} {W : TopologicalSpace.Opens E0}
    {c : ℝ → E0} {a b : ℝ} (hc : ContinuousOn c (Icc a b)) (hmem : ∀ t ∈ Icc a b, c t ∈ W)
    (hR : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s < s' → R (c s) (c s')) :
    Causal.CurveOn (relOn R) W c a b where
  mem := hmem
  rel t ht N _ htN := by
    have hN : c ⁻¹' N ∈ 𝓝[Icc a b] t := hc t ht (N.isOpen.mem_nhds htN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hN
    refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hsb : s ∈ Metric.ball t ε := by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    have hs'b : s' ∈ Metric.ball t ε := by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    exact ⟨hball ⟨hsb, hs⟩, hball ⟨hs'b, hs'⟩, hR s hs s' hs' h2⟩

theorem le_unlift_seg (hP : Adm P) (hPQ : NullCone (Q - P)) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') : Le (unlift (seg P Q s)) (unlift (seg P Q s')) := by
  have h₁ := adm_seg hP hPQ hs
  have h₂ := adm_seg hP hPQ (hs.trans hss')
  refine ⟨_, _, polar_unlift h₁.nonneg, polar_unlift h₂.nonneg, ?_⟩
  rw [lift_unlift h₁, lift_unlift h₂, seg_sub]
  exact hPQ.smul (sub_nonneg.2 hss')

theorem lt_unlift_seg (hP : Adm P) (hPQ : NullConeLt (Q - P)) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s < s') : Lt (unlift (seg P Q s)) (unlift (seg P Q s')) := by
  have h₁ := adm_seg hP hPQ.nullCone hs
  have h₂ := adm_seg hP hPQ.nullCone (hs.trans hss'.le)
  refine ⟨_, _, polar_unlift h₁.nonneg, polar_unlift h₂.nonneg, ?_⟩
  rw [lift_unlift h₁, lift_unlift h₂, seg_sub]
  exact hPQ.smul (sub_pos.2 hss')

/-- **A straight causal segment of `𝐌³` is a future causal curve of `𝔼₀`.** -/
theorem curveOn_unlift_seg (hP : Adm P) (hPQ : NullCone (Q - P)) {W : TopologicalSpace.Opens E0}
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P Q s) ∈ W) :
    Causal.CurveOn (relOn Le) W (fun s => unlift (seg P Q s)) 0 1 :=
  curveOn_of_continuousOn (continuousOn_unlift_seg hP hPQ) hW
    fun _ hs _ _ h => le_unlift_seg hP hPQ hs.1 h.le

/-- **A straight chronological segment of `𝐌³` is a future chronological curve of `𝔼₀`.** -/
theorem curveOn_unlift_seg_lt (hP : Adm P) (hPQ : NullConeLt (Q - P))
    {W : TopologicalSpace.Opens E0} (hW : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P Q s) ∈ W) :
    Causal.CurveOn (relOn Lt) W (fun s => unlift (seg P Q s)) 0 1 :=
  curveOn_of_continuousOn (continuousOn_unlift_seg hP hPQ.nullCone) hW
    fun _ hs _ _ h => lt_unlift_seg hP hPQ hs.1 h

theorem adm_lift (x : E0) (θ : ℝ) : Adm (lift x θ) := by
  simp only [Adm, lift, btzPaperNull]
  rcases (rad_nonneg x).lt_or_eq with h | h
  · exact Or.inl h
  · right; rw [← h]; simp

/-! ### Curves: constants, concatenation -/

section Curves

open TopologicalSpace

variable {r r' : Opens E0 → E0 → E0 → Prop} {U W : Opens E0} {c c' : ℝ → E0} {a b a' b' : ℝ}

theorem curveOn_const (hx : x ∈ U) : Causal.CurveOn r U (fun _ => x) 0 0 where
  mem _ _ := hx
  rel t _ _ _ _ := ⟨t - 1, t + 1, by linarith, by linarith, fun s hs s' hs' _ h _ => by
    have : s = s' := by rw [hs.1.antisymm' hs.2, hs'.1.antisymm' hs'.2]
    exact absurd this h.ne⟩

theorem curveOn_mono_rel (h : ∀ N x y, r N x y → r' N x y) (hc : Causal.CurveOn r W c a b) :
    Causal.CurveOn r' W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, h'⟩ := hc.rel t ht N hN htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => h _ _ _ (h' s hs s' hs' h1 h2 h3)⟩

/-- Concatenation of two curves, the second translated to start where the first ends. -/
theorem curve_append (hr : Causal.IsRelFamily r) (hc : Causal.CurveOn r U c a b) (hc' : Causal.CurveOn r U c' a' b')
    (hab : a ≤ b) (hab' : a' ≤ b') (h : c b = c' a') :
    ∃ d : ℝ → E0, Causal.CurveOn r U d a (b + (b' - a')) ∧ d a = c a ∧ d (b + (b' - a')) = c' b' := by
  have e1 : 1 * b + (a' - b) = a' := by ring
  have e2 : 1 * (b + (b' - a')) + (a' - b) = b' := by ring
  have hc'' : Causal.CurveOn r U (fun t => c' (1 * t + (a' - b))) b (b + (b' - a')) :=
    Causal.CurveOn.comp_affine (k := 1) (m := a' - b) one_pos (by rw [e1, e2]; exact hc')
  have hj : c b = (fun t => c' (1 * t + (a' - b))) b := by simp only; rw [e1]; exact h
  refine ⟨_, Causal.CurveOn.concat hr hc hc'' hab (by linarith) hj, by simp [hab], ?_⟩
  by_cases hb : b + (b' - a') ≤ b
  · have : b' = a' := le_antisymm (by linarith) hab'
    subst this
    simp only [sub_self, add_zero, le_refl, if_true]
    exact h
  · simp only [hb, if_false]; rw [e2]

end Curves

/-! ### The causality of `𝔼₀` -/

section Causal.Causality

open TopologicalSpace

/-- `x ≤_U y` (`defi:causal_Ealpha`, `RamcovGX.tex:2215`, DEC-33): a future causal curve of `U` from
`x` to `y` — a continuous curve along which the developed points are causally related, the
local relation being `Le` (some development of the two points is causally related in `𝐌³`). -/
def CLe (U : Opens E0) (x y : E0) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ ∃ c : ℝ → E0, Causal.CurveOn (relOn Le) U c a b ∧ c a = x ∧ c b = y

/-- `x ≪_U y`: a future chronological curve of `U` over a non-trivial segment. -/
def CLt (U : Opens E0) (x y : E0) : Prop :=
  ∃ a b : ℝ, a < b ∧ ∃ c : ℝ → E0, Causal.CurveOn (relOn Lt) U c a b ∧ c a = x ∧ c b = y

theorem isRelFamily_le : Causal.IsRelFamily (relOn Le) := isRelFamily_relOn Le.trans

theorem isRelFamily_lt : Causal.IsRelFamily (relOn Lt) := isRelFamily_relOn Lt.trans

variable {U V : Opens E0}

theorem CLe.le (h : CLe U x y) : Le x y := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
  rcases hab.lt_or_eq with hab | hab
  · exact (hc.rel_of_lt isRelFamily_le le_rfl hab le_rfl).2.2
  · rw [hab]; exact le_refl' _

theorem CLt.lt (h : CLt U x y) : Lt x y := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
  exact (hc.rel_of_lt isRelFamily_lt le_rfl hab le_rfl).2.2

theorem CLe.mem_left (h : CLe U x y) : x ∈ U := by
  obtain ⟨a, b, hab, c, hc, rfl, -⟩ := h; exact hc.mem a ⟨le_rfl, hab⟩

theorem CLe.mem_right (h : CLe U x y) : y ∈ U := by
  obtain ⟨a, b, hab, c, hc, -, rfl⟩ := h; exact hc.mem b ⟨hab, le_rfl⟩

theorem CLt.cle (h : CLt U x y) : CLe U x y := by
  obtain ⟨a, b, hab, c, hc, h1, h2⟩ := h
  exact ⟨a, b, hab.le, c, curveOn_mono_rel (fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.le⟩) hc, h1, h2⟩

theorem CLe.refl (hx : x ∈ U) : CLe U x x := ⟨0, 0, le_rfl, _, curveOn_const hx, rfl, rfl⟩

theorem CLe.trans (h₁ : CLe U x y) (h₂ : CLe U y z) : CLe U x z := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h₁
  obtain ⟨a', b', hab', c', hc', h1, rfl⟩ := h₂
  obtain ⟨d, hd, hda, hdb⟩ := curve_append isRelFamily_le hc hc' hab hab' h1.symm
  exact ⟨a, _, by linarith, d, hd, hda, hdb⟩

theorem CLt.trans (h₁ : CLt U x y) (h₂ : CLt U y z) : CLt U x z := by
  obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h₁
  obtain ⟨a', b', hab', c', hc', h1, rfl⟩ := h₂
  obtain ⟨d, hd, hda, hdb⟩ := curve_append isRelFamily_lt hc hc' hab.le hab'.le h1.symm
  exact ⟨a, _, by linarith, d, hd, hda, hdb⟩

theorem CLe.mono (hVU : V ≤ U) (h : CLe V x y) : CLe U x y := by
  obtain ⟨a, b, hab, c, hc, h1, h2⟩ := h
  exact ⟨a, b, hab, c, hc.mono_opens isRelFamily_le hVU, h1, h2⟩

theorem CLt.mono (hVU : V ≤ U) (h : CLt V x y) : CLt U x y := by
  obtain ⟨a, b, hab, c, hc, h1, h2⟩ := h
  exact ⟨a, b, hab, c, hc.mono_opens isRelFamily_lt hVU, h1, h2⟩

/-- The straight segment between two developments, as a causal curve from `x` to `y`. -/
theorem cle_of_seg (hx : Polar x θ₁) (hy : Polar y θ₂) (h : NullCone (lift y θ₂ - lift x θ₁))
    (hU : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg (lift x θ₁) (lift y θ₂) s) ∈ U) : CLe U x y :=
  ⟨0, 1, zero_le_one, _, curveOn_unlift_seg (adm_lift x θ₁) h hU,
    by simp only [seg_zero, unlift_lift hx], by simp only [seg_one, unlift_lift hy]⟩

theorem clt_of_seg (hx : Polar x θ₁) (hy : Polar y θ₂) (h : NullConeLt (lift y θ₂ - lift x θ₁))
    (hU : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg (lift x θ₁) (lift y θ₂) s) ∈ U) : CLt U x y :=
  ⟨0, 1, zero_lt_one, _, curveOn_unlift_seg_lt (adm_lift x θ₁) h hU,
    by simp only [seg_zero, unlift_lift hx], by simp only [seg_one, unlift_lift hy]⟩

/-- **Globally, `x ≤ y ⟺ Le x y`**: a causal relation of developments is realised by a straight
segment. -/
theorem cle_top_iff : CLe ⊤ x y ↔ Le x y := by
  refine ⟨CLe.le, fun ⟨θ₁, θ₂, hx, hy, h⟩ => cle_of_seg hx hy h fun _ _ => trivial⟩

theorem clt_top_iff : CLt ⊤ x y ↔ Lt x y := by
  refine ⟨CLt.lt, fun ⟨θ₁, θ₂, hx, hy, h⟩ => clt_of_seg hx hy h fun _ _ => trivial⟩

end Causal.Causality

/-! ### Openness of the chronological relation -/

section Open

open TopologicalSpace

theorem continuous_btzPaperNull : Continuous btzPaperNull := by unfold btzPaperNull; fun_prop

/-- Near `y` off the axis, `θ_y + arg (z / z_y)` is an angle of `z`. -/
theorem polar_add_arg_div (y w : E0) (hy : y.2 ≠ 0) : Polar w (arg y.2 + arg (w.2 / y.2)) := by
  unfold Polar rad
  have h1 := norm_mul_exp_arg_mul_I (w.2 / y.2)
  have h2 := norm_mul_exp_arg_mul_I y.2
  have hn : (‖y.2‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hy)
  calc w.2 = (w.2 / y.2) * y.2 := by field_simp
    _ = (‖w.2 / y.2‖ * cexp (arg (w.2 / y.2) * I)) * (‖y.2‖ * cexp (arg y.2 * I)) := by
        rw [h1, h2]
    _ = ↑‖w.2‖ * cexp (↑(arg y.2 + arg (w.2 / y.2)) * I) := by
        rw [norm_div, Complex.ofReal_div, Complex.ofReal_add, add_mul, Complex.exp_add]
        field_simp

/-- The local lift at `y` off the axis: the development with the angle continuing `arg z_y`. -/
noncomputable def locLift (y w : E0) : ℝ × ℝ × ℝ := lift w (arg y.2 + arg (w.2 / y.2))

theorem locLift_self (y : E0) (hy : y.2 ≠ 0) : locLift y y = lift y (arg y.2) := by
  simp [locLift, div_self hy]

theorem continuousAt_locLift (y : E0) (hy : y.2 ≠ 0) : ContinuousAt (locLift y) y := by
  have harg : ContinuousAt (fun w : E0 => arg (w.2 / y.2)) y := by
    have h1 : y.2 / y.2 ∈ Complex.slitPlane := by rw [div_self hy]; exact Complex.one_mem_slitPlane
    have hf : ContinuousAt (fun w : E0 => w.2 / y.2) y := continuousAt_snd.div_const _
    exact ContinuousAt.comp (f := fun w : E0 => w.2 / y.2) (Complex.continuousAt_arg h1) hf
  unfold locLift lift
  exact continuous_btzPaperNull.continuousAt.comp
    (continuousAt_fst.prodMk (continuous_rad.continuousAt.prodMk (continuousAt_const.add harg)))

/-- **Balls centred on the axis are order-convex**: `w₁ ≼ w ≼ w₂` with `w₁, w₂` in the ball puts
`w` in it (`τ` and `r` are monotone, and the ball is `{|τ − τ_x| < δ, r < δ}`). -/
theorem mem_ball_of_le_of_le {δ : ℝ} {w₁ w w₂ : E0} (hx : x ∈ axis) (h₁ : Le w₁ w) (h₂ : Le w w₂)
    (hw₁ : w₁ ∈ Metric.ball x δ) (hw₂ : w₂ ∈ Metric.ball x δ) : w ∈ Metric.ball x δ := by
  have hx0 : x.2 = 0 := hx
  have c₁ := h₁.closed
  have c₂ := h₂.closed
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hw₁ hw₂ ⊢
  rw [Real.dist_eq, abs_lt] at hw₁ hw₂ ⊢
  simp only [hx0, dist_zero_right] at hw₁ hw₂ ⊢
  have : ‖w.2‖ ≤ ‖w₂.2‖ := c₂.2.1
  exact ⟨⟨by linarith [c₁.1], by linarith [c₂.1]⟩, this.trans_lt hw₂.2⟩

/-- `seg` stays in a convex set containing its ends. -/
theorem seg_mem_of_convex {S : Set (ℝ × ℝ × ℝ)} (hS : Convex ℝ S) (hP : P ∈ S) (hQ : Q ∈ S)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : seg P Q s ∈ S :=
  hS.add_smul_sub_mem hP hQ hs

/-- A point of a segment, read in `𝔼₀`, lies between its ends. -/
theorem le_seg_ends (hP : Adm P) (hPQ : NullCone (Q - P)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Le (unlift P) (unlift (seg P Q s)) ∧ Le (unlift (seg P Q s)) (unlift Q) := by
  have h0 := le_unlift_seg hP hPQ le_rfl hs.1
  have h1 := le_unlift_seg hP hPQ hs.1 hs.2
  rw [seg_zero] at h0
  rw [seg_one] at h1
  exact ⟨h0, h1⟩

/-- **`I⁺_U(x)` is open.** -/
theorem isOpen_CLt_right (U : Opens E0) (x : E0) : IsOpen {y | CLt U x y} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨a, b, hab, c, hc, rfl, rfl⟩
  have hLt : Lt (c a) (c b) := (hc.rel_of_lt isRelFamily_lt le_rfl hab le_rfl).2.2
  have hry : 0 < rad (c b) := (rad_nonneg _).trans_lt hLt.closed.1
  have hy0 : (c b).2 ≠ 0 := norm_pos_iff.1 hry
  set Q := lift (c b) (arg (c b).2) with hQdef
  have hQy : unlift Q = c b := unlift_lift (polar_arg _)
  have hQb : 0 < Q.2.1 := hry
  -- a ball around `Q` read inside `U`, off the axis
  have hUQ : unlift ⁻¹' U ∩ {R | 0 < R.2.1} ∈ 𝓝 Q := by
    refine Filter.inter_mem ((continuousAt_unlift hQb.ne').preimage_mem_nhds ?_)
      ((isOpen_lt continuous_const continuous_snd.fst).mem_nhds hQb)
    rw [hQy]; exact U.isOpen.mem_nhds (hc.mem b ⟨hab.le, le_rfl⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hUQ
  -- a point `z = c s₀` of the curve just before `b`, with `locLift z` near `Q`
  have hφ := continuousAt_locLift (c b) hy0
  rw [ContinuousAt, locLift_self _ hy0] at hφ
  have hpre : c ⁻¹' (locLift (c b) ⁻¹' Metric.ball Q (ε / 2)) ∈ 𝓝[Icc a b] b :=
    (hc.continuousOn isRelFamily_lt) b ⟨hab.le, le_rfl⟩ (hφ (Metric.ball_mem_nhds Q (by linarith)))
  obtain ⟨δ₁, hδ₁, hδball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel b ⟨hab.le, le_rfl⟩ U le_rfl (hc.mem b ⟨hab.le, le_rfl⟩)
  set s₀ := (max (max a l) (b - δ₁) + b) / 2 with hs₀
  have hs₀b : s₀ < b := by
    have : max (max a l) (b - δ₁) < b := max_lt (max_lt hab hl) (by linarith)
    rw [hs₀]; linarith
  have hs₀a : a ≤ s₀ := by
    have : a ≤ max (max a l) (b - δ₁) := (le_max_left _ _).trans (le_max_left _ _)
    rw [hs₀]; linarith
  have hs₀l : l < s₀ := by
    have : l ≤ max (max a l) (b - δ₁) := (le_max_right _ _).trans (le_max_left _ _)
    rw [hs₀]; linarith
  have hs₀δ : b - δ₁ < s₀ := by
    have : b - δ₁ ≤ max (max a l) (b - δ₁) := le_max_right _ _
    rw [hs₀]; linarith
  have hs₀mem : s₀ ∈ Icc a b := ⟨hs₀a, hs₀b.le⟩
  have hzy : Lt (c s₀) (c b) := (hrel s₀ hs₀mem b ⟨hab.le, le_rfl⟩ hs₀l hs₀b hu).2.2
  set P := locLift (c b) (c s₀) with hPdef
  have hPball : P ∈ Metric.ball Q (ε / 2) := by
    refine hδball ⟨?_, hs₀mem⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  have hPz : unlift P = c s₀ := unlift_lift (polar_add_arg_div _ _ hy0)
  have hcone : NullConeLt (Q - P) := by
    refine hzy.of_polar (polar_add_arg_div _ _ hy0) (polar_arg _) ?_
    rw [show arg (c b).2 - (arg (c b).2 + arg ((c s₀).2 / (c b).2)) =
      -arg ((c s₀).2 / (c b).2) by ring, abs_neg]
    exact Complex.abs_arg_le_pi _
  -- the neighbourhood
  have hS : IsOpen (Metric.ball Q (ε / 2) ∩ {Q' | NullConeLt (Q' - P)}) :=
    Metric.isOpen_ball.inter (isOpen_nullConeLt.preimage (continuous_id.sub continuous_const))
  have hφ' := continuousAt_locLift (c b) hy0
  refine Filter.mem_of_superset (hφ'.preimage_mem_nhds (hS.mem_nhds ?_)) ?_
  · rw [locLift_self _ hy0]; exact ⟨Metric.mem_ball_self (by linarith), hcone⟩
  · rintro y' ⟨hy'b, hy'c⟩
    set Q' := locLift (c b) y'
    have hQ'y : unlift Q' = y' := unlift_lift (polar_add_arg_div _ _ hy0)
    have hsegU : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P Q' s) ∈ U := fun s hs => by
      have := seg_mem_of_convex (convex_ball Q (ε / 2)) hPball hy'b hs
      exact (hball (Metric.ball_subset_ball (by linarith) this)).1
    have hPadm : Adm P := Or.inl (hball (Metric.ball_subset_ball (by linarith) hPball)).2
    have hseg := curveOn_unlift_seg_lt hPadm hy'c hsegU
    have hres : Causal.CurveOn (relOn Lt) U c a s₀ :=
      hc.restrict le_rfl hs₀b.le le_rfl fun t ht => hc.mem t ⟨ht.1, ht.2.trans hs₀b.le⟩
    obtain ⟨d, hd, hda, hdb⟩ := curve_append isRelFamily_lt hres hseg hs₀a zero_le_one
      (by simp only [seg_zero, hPz])
    refine ⟨a, _, by linarith, d, hd, hda, ?_⟩
    rw [hdb, seg_one, hQ'y]

/-- `|arg z − arg w| ≤ 2π`. -/
theorem abs_arg_sub_arg_le (z w : ℂ) : |arg z - arg w| ≤ 2 * π := by
  rw [abs_le]
  constructor <;> linarith [Complex.arg_le_pi z, Complex.neg_pi_lt_arg z, Complex.arg_le_pi w,
    Complex.neg_pi_lt_arg w]

/-- **`I⁻_U(y)` is open**, BTZ points included. -/
theorem isOpen_CLt_left (U : Opens E0) (y : E0) : IsOpen {x | CLt U x y} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨a, b, hab, c, hc, rfl, hcb⟩
  have haU : c a ∈ U := hc.mem a ⟨le_rfl, hab.le⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel a ⟨le_rfl, hab.le⟩ U le_rfl haU
  -- the tail of the curve from `c s₀` to `y`
  have htail : ∀ s₀ ∈ Ioo a b, ∀ x' : E0, ∀ d : ℝ → E0, Causal.CurveOn (relOn Lt) U d 0 1 →
      d 0 = x' → d 1 = c s₀ → CLt U x' y := by
    intro s₀ hs₀ x' d hd hd0 hd1
    have hres : Causal.CurveOn (relOn Lt) U c s₀ b :=
      hc.restrict hs₀.1.le le_rfl le_rfl fun t ht => hc.mem t ⟨hs₀.1.le.trans ht.1, ht.2⟩
    obtain ⟨e, he, hea, heb⟩ := curve_append isRelFamily_lt hd hres zero_le_one hs₀.2.le hd1
    exact ⟨0, _, by linarith [hs₀.2], e, he, hea.trans hd0, heb.trans hcb⟩
  rcases (rad_nonneg (c a)).lt_or_eq with hrx | hrx
  · -- off the axis: the local lift at `x`
    have hx0 : (c a).2 ≠ 0 := norm_pos_iff.1 hrx
    set P := lift (c a) (arg (c a).2) with hPdef
    have hPx : unlift P = c a := unlift_lift (polar_arg _)
    have hPb : 0 < P.2.1 := hrx
    have hUP : unlift ⁻¹' U ∩ {R | 0 < R.2.1} ∈ 𝓝 P := by
      refine Filter.inter_mem ((continuousAt_unlift hPb.ne').preimage_mem_nhds ?_)
        ((isOpen_lt continuous_const continuous_snd.fst).mem_nhds hPb)
      rw [hPx]; exact U.isOpen.mem_nhds haU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hUP
    have hφ := continuousAt_locLift (c a) hx0
    rw [ContinuousAt, locLift_self _ hx0] at hφ
    have hpre : c ⁻¹' (locLift (c a) ⁻¹' Metric.ball P (ε / 2)) ∈ 𝓝[Icc a b] a :=
      (hc.continuousOn isRelFamily_lt) a ⟨le_rfl, hab.le⟩
        (hφ (Metric.ball_mem_nhds P (by linarith)))
    obtain ⟨δ₁, hδ₁, hδball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    set s₀ := (a + min (min b u) (a + δ₁)) / 2 with hs₀
    have hm : a < min (min b u) (a + δ₁) := lt_min (lt_min hab hu) (by linarith)
    have hs₀a : a < s₀ := by rw [hs₀]; linarith
    have hs₀b : s₀ < b := by
      have : min (min b u) (a + δ₁) ≤ b := (min_le_left _ _).trans (min_le_left _ _)
      rw [hs₀]; linarith
    have hs₀u : s₀ < u := by
      have : min (min b u) (a + δ₁) ≤ u := (min_le_left _ _).trans (min_le_right _ _)
      rw [hs₀]; linarith
    have hs₀δ : s₀ < a + δ₁ := by
      have : min (min b u) (a + δ₁) ≤ a + δ₁ := min_le_right _ _
      rw [hs₀]; linarith
    have hs₀mem : s₀ ∈ Icc a b := ⟨hs₀a.le, hs₀b.le⟩
    have hxz : Lt (c a) (c s₀) := (hrel a ⟨le_rfl, hab.le⟩ s₀ hs₀mem hl hs₀a hs₀u).2.2
    set Q := locLift (c a) (c s₀) with hQdef
    have hQball : Q ∈ Metric.ball P (ε / 2) := by
      refine hδball ⟨?_, hs₀mem⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    have hQz : unlift Q = c s₀ := unlift_lift (polar_add_arg_div _ _ hx0)
    have hcone : NullConeLt (Q - P) := by
      refine hxz.of_polar (polar_arg _) (polar_add_arg_div _ _ hx0) ?_
      rw [show arg (c a).2 + arg ((c s₀).2 / (c a).2) - arg (c a).2 =
        arg ((c s₀).2 / (c a).2) by ring]
      exact Complex.abs_arg_le_pi _
    have hS : IsOpen (Metric.ball P (ε / 2) ∩ {P' | NullConeLt (Q - P')}) :=
      Metric.isOpen_ball.inter (isOpen_nullConeLt.preimage (continuous_const.sub continuous_id))
    have hφ' := continuousAt_locLift (c a) hx0
    refine Filter.mem_of_superset (hφ'.preimage_mem_nhds (hS.mem_nhds ?_)) ?_
    · rw [locLift_self _ hx0]; exact ⟨Metric.mem_ball_self (by linarith), hcone⟩
    · rintro x' ⟨hx'b, hx'c⟩
      set P' := locLift (c a) x'
      have hP'x : unlift P' = x' := unlift_lift (polar_add_arg_div _ _ hx0)
      have hsegU : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P' Q s) ∈ U := fun s hs => by
        have := seg_mem_of_convex (convex_ball P (ε / 2)) hx'b hQball hs
        exact (hball (Metric.ball_subset_ball (by linarith) this)).1
      have hP'adm : Adm P' := Or.inl (hball (Metric.ball_subset_ball (by linarith) hx'b)).2
      exact htail s₀ ⟨hs₀a, hs₀b⟩ x' _ (curveOn_unlift_seg_lt hP'adm hx'c hsegU)
        (by simp only [seg_zero, hP'x]) (by simp only [seg_one, hQz])
  · -- on the axis: a ball, order-convex, and the cone condition uniform in the angles
    have hxax : c a ∈ axis := rad_eq_zero.1 hrx.symm
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 U.isOpen (c a) haU
    have hpre : c ⁻¹' Metric.ball (c a) δ ∈ 𝓝[Icc a b] a :=
      (hc.continuousOn isRelFamily_lt) a ⟨le_rfl, hab.le⟩ (Metric.ball_mem_nhds _ hδ)
    obtain ⟨δ₁, hδ₁, hδball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    set s₀ := (a + min (min b u) (a + δ₁)) / 2 with hs₀
    have hm : a < min (min b u) (a + δ₁) := lt_min (lt_min hab hu) (by linarith)
    have hs₀a : a < s₀ := by rw [hs₀]; linarith
    have hs₀b : s₀ < b := by
      have : min (min b u) (a + δ₁) ≤ b := (min_le_left _ _).trans (min_le_left _ _)
      rw [hs₀]; linarith
    have hs₀u : s₀ < u := by
      have : min (min b u) (a + δ₁) ≤ u := (min_le_left _ _).trans (min_le_right _ _)
      rw [hs₀]; linarith
    have hs₀δ : s₀ < a + δ₁ := by
      have : min (min b u) (a + δ₁) ≤ a + δ₁ := min_le_right _ _
      rw [hs₀]; linarith
    have hs₀mem : s₀ ∈ Icc a b := ⟨hs₀a.le, hs₀b.le⟩
    have hxz : Lt (c a) (c s₀) := (hrel a ⟨le_rfl, hab.le⟩ s₀ hs₀mem hl hs₀a hs₀u).2.2
    have hzball : c s₀ ∈ Metric.ball (c a) δ := by
      refine hδball ⟨?_, hs₀mem⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    set z := c s₀
    have hzc := hxz.closed
    rw [← hrx, sub_zero] at hzc
    set G : E0 → ℝ := fun x' => (rad z - rad x') * (2 * (z.1 - x'.1) - (rad z - rad x')) -
      4 * π ^ 2 * (rad x' * rad z) with hG
    have hGc : Continuous G := by
      have := continuous_rad
      rw [hG]; fun_prop
    have hV : IsOpen (Metric.ball (c a) δ ∩ {x' | rad x' < rad z} ∩ {x' | 0 < G x'}) :=
      (Metric.isOpen_ball.inter (isOpen_lt continuous_rad continuous_const)).inter
        (isOpen_lt continuous_const hGc)
    refine Filter.mem_of_superset (hV.mem_nhds ⟨⟨Metric.mem_ball_self hδ, ?_⟩, ?_⟩) ?_
    · show rad (c a) < rad z
      rw [← hrx]; exact hzc.1
    · show 0 < G (c a)
      simp only [hG, ← hrx, zero_mul, mul_zero, sub_zero]; exact hzc.2
    · rintro x' ⟨⟨hx'b, hx'r⟩, hx'G⟩
      have hcone : NullConeLt (lift z (arg z.2) - lift x' (arg x'.2)) := by
        rw [nullConeLt_lift_iff]
        refine ⟨hx'r, ?_⟩
        have h2π : (arg z.2 - arg x'.2) ^ 2 ≤ (2 * π) ^ 2 :=
          sq_le_sq' (abs_le.1 (abs_arg_sub_arg_le _ _)).1 (abs_le.1 (abs_arg_sub_arg_le _ _)).2
        have hrr : 0 ≤ rad x' * rad z := mul_nonneg (rad_nonneg _) (rad_nonneg _)
        have : rad x' * rad z * (arg z.2 - arg x'.2) ^ 2 ≤ 4 * π ^ 2 * (rad x' * rad z) := by
          nlinarith
        have hx'G' : 0 < G x' := hx'G
        simp only [hG] at hx'G'
        linarith
      have hsegU : ∀ s ∈ Icc (0 : ℝ) 1,
          unlift (seg (lift x' (arg x'.2)) (lift z (arg z.2)) s) ∈ U := fun s hs => by
        have hends := le_seg_ends (adm_lift x' _) hcone.nullCone hs
        rw [unlift_lift (polar_arg _), unlift_lift (polar_arg _)] at hends
        exact hδU (mem_ball_of_le_of_le hxax hends.1 hends.2 hx'b hzball)
      exact htail s₀ ⟨hs₀a, hs₀b⟩ x' _ (curveOn_unlift_seg_lt (adm_lift x' _) hcone hsegU)
        (by simp only [seg_zero, unlift_lift (polar_arg _)])
        (by simp only [seg_one, unlift_lift (polar_arg _)]; rfl)

end Open

/-! ### The causality of `𝔼₀`, and its calculus -/

section Calculus

open TopologicalSpace

/-- **The causality of `𝔼₀`** (`defi:causal_Ealpha` / `defi:causal_E0` read by DEC-33): `x ≤_U y`
(resp. `x ≪_U y`) iff a future causal (resp. chronological) curve joins them in `U`
(`CLe`, `CLe`); the relations are those of `Causal.Curves` for the local relations `Le`, `Lt` of
developments in `𝐌³`. -/
noncomputable def causality : Causal.Causality E0 where
  le := CLe
  lt := CLt
  le_mem_left h := h.mem_left
  le_mem_right h := h.mem_right
  lt_mem_left h := h.cle.mem_left
  lt_mem_right h := h.cle.mem_right
  le_refl hx := CLe.refl hx
  le_trans := CLe.trans
  lt_trans := CLt.trans
  le_mono hVU _ _ h := h.mono hVU
  lt_mono hVU _ _ h := h.mono hVU
  le_of_lt h := h.cle
  isOpen_lt_right := isOpen_CLt_right
  isOpen_lt_left := isOpen_CLt_left

variable {U : Opens E0} {p : E0}

@[simp] theorem causality_le : causality.le U x y ↔ CLe U x y := Iff.rfl

@[simp] theorem causality_lt : causality.lt U x y ↔ CLt U x y := Iff.rfl

/-- **Globally, `x ≤ y` iff some developments are causally related in `𝐌³`.** -/
theorem le_top_iff : causality.le ⊤ x y ↔ Le x y := cle_top_iff

theorem lt_top_iff : causality.lt ⊤ x y ↔ Lt x y := clt_top_iff

theorem le_of_le (h : causality.le U x y) : Le x y := CLe.le h

theorem nonneg_of_mul_nonneg' {B X : ℝ} (hB : 0 < B) (h : 0 ≤ B * X) : 0 ≤ X := by
  by_contra hX
  have : B * X < 0 := mul_neg_of_pos_of_neg hB (not_le.1 hX)
  linarith

theorem pos_of_mul_pos' {B X : ℝ} (hB : 0 ≤ B) (h : 0 < B * X) : 0 < X := by
  by_contra hX
  have : B * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB (not_lt.1 hX)
  linarith

theorem lt_of_lt (h : causality.lt U x y) : Lt x y := CLt.lt h

/-- **The calculus along future causal curves** (`B16 lem:BTZ_causal_curve` (i), `BTZ_HAL_1.tex:515`,
integrated): `0 ≤ Δr ≤ 2Δτ`, so `τ`, `r`, `f = τ − r/2` and `h = τ + r` are non-decreasing. -/
theorem calculus_le (h : causality.le U x y) :
    0 ≤ rad y - rad x ∧ rad y - rad x ≤ 2 * (y.1 - x.1) ∧ x.1 ≤ y.1 ∧ rad x ≤ rad y ∧
      fcoord x ≤ fcoord y ∧ hcoord x ≤ hcoord y := by
  obtain ⟨hτ, hr, hq⟩ := (le_of_le h).closed
  have hd : rad y - rad x ≤ 2 * (y.1 - x.1) := by
    rcases (sub_nonneg.2 hr).lt_or_eq with h' | h'
    · have := nonneg_of_mul_nonneg' h' hq
      linarith
    · rw [← h']; linarith
  refine ⟨by linarith, hd, hτ, hr, ?_, ?_⟩ <;> simp only [fcoord, hcoord] <;> linarith

/-- **Along future chronological curves `r`, `τ`, `f` and `h` increase strictly.** -/
theorem calculus_lt (h : causality.lt U x y) :
    rad x < rad y ∧ rad y - rad x < 2 * (y.1 - x.1) ∧ x.1 < y.1 ∧ fcoord x < fcoord y ∧
      hcoord x < hcoord y := by
  obtain ⟨hr, hq⟩ := (lt_of_lt h).closed
  have h2 : 0 < 2 * (y.1 - x.1) - (rad y - rad x) := by
    by_contra h'
    have : 2 * (y.1 - x.1) - (rad y - rad x) ≤ 0 := not_lt.1 h'
    nlinarith [sub_pos.2 hr]
  refine ⟨hr, by linarith, by linarith, ?_, ?_⟩ <;> simp only [fcoord, hcoord] <;> linarith

/-- Two points of the axis, `τ`-ordered, are causally related. -/
theorem le_axis (hx : x ∈ axis) (hy : y ∈ axis) (h : x.1 ≤ y.1) : Le x y := by
  refine le_iff_closed.2 ⟨0, 0, Polar.of_axis hx 0, Polar.of_axis hy 0, ?_⟩
  rw [rad_eq_zero.2 hx, rad_eq_zero.2 hy]
  exact ⟨h, le_rfl, by simp⟩

theorem fcoord_of_axis (hx : x ∈ axis) : fcoord x = x.1 := by
  simp [fcoord, rad_eq_zero.2 hx]

/-- **The causal future of a BTZ point is `{f ≥ τ_p}`**: below, the future light cone of `p` is
the level set `f = τ_p`. -/
theorem le_axis_iff (hp : p ∈ axis) : Le p y ↔ p.1 ≤ fcoord y := by
  rw [le_iff_closed]
  have hp0 := rad_eq_zero.2 hp
  constructor
  · rintro ⟨θ₁, θ₂, -, -, hτ, hr, hq⟩
    rw [hp0] at hq hr
    simp only [zero_mul, sub_zero] at hq
    simp only [fcoord]
    rcases (rad_nonneg y).lt_or_eq with h' | h'
    · have := nonneg_of_mul_nonneg' h' hq
      linarith
    · rw [← h']; linarith
  · intro h
    have hr := rad_nonneg y
    refine ⟨0, arg y.2, Polar.of_axis hp 0, polar_arg y, ?_, ?_, ?_⟩
    · simp only [fcoord] at h; linarith
    · rw [hp0]; exact hr
    · rw [hp0]; simp only [zero_mul, sub_zero]; simp only [fcoord] at h
      exact mul_nonneg hr (by linarith)

/-- **The chronological future of a BTZ point is `{r > 0, f > τ_p}`.** -/
theorem lt_axis_iff (hp : p ∈ axis) : Lt p y ↔ 0 < rad y ∧ p.1 < fcoord y := by
  rw [lt_iff_closed]
  have hp0 := rad_eq_zero.2 hp
  constructor
  · rintro ⟨θ₁, θ₂, -, -, hr, hq⟩
    rw [hp0] at hq hr
    simp only [zero_mul, sub_zero] at hq
    refine ⟨hr, ?_⟩
    simp only [fcoord]
    have := pos_of_mul_pos' hr.le hq
    linarith
  · rintro ⟨hr, h⟩
    refine ⟨0, arg y.2, Polar.of_axis hp 0, polar_arg y, ?_, ?_⟩
    · rw [hp0]; exact hr
    · rw [hp0]; simp only [zero_mul, sub_zero]; simp only [fcoord] at h
      exact mul_pos hr (by linarith)

/-- **The causal past of a BTZ point is the singular half-line below it**
(`defi:causal_E0`, `ETT.tex:1344`; B21 §1.2). -/
theorem le_axis_iff' (hp : p ∈ axis) : Le x p ↔ x ∈ axis ∧ x.1 ≤ p.1 := by
  constructor
  · intro h
    obtain ⟨hτ, hr, -⟩ := h.closed
    rw [rad_eq_zero.2 hp] at hr
    exact ⟨rad_eq_zero.1 (le_antisymm hr (rad_nonneg x)), hτ⟩
  · rintro ⟨hx, h⟩; exact le_axis hx hp h

theorem Jplus_axis (hp : p ∈ axis) : causality.Jplus ⊤ {p} = {y | p.1 ≤ fcoord y} := by
  ext y; rw [Causal.Precausality.mem_Jplus_singleton, le_top_iff, le_axis_iff hp]; rfl

theorem Iplus_axis (hp : p ∈ axis) :
    causality.Iplus ⊤ {p} = {y | 0 < rad y ∧ p.1 < fcoord y} := by
  ext y; rw [Causal.Precausality.mem_Iplus_singleton, lt_top_iff, lt_axis_iff hp]; rfl

theorem Jminus_axis (hp : p ∈ axis) :
    causality.Jminus ⊤ {p} = {x | x ∈ axis ∧ x.1 ≤ p.1} := by
  ext x; rw [Causal.Precausality.mem_Jminus_singleton, le_top_iff, le_axis_iff' hp]; rfl

/-- **`I⁻_U(p) = ∅` at a BTZ point**, in every open set. -/
theorem Iminus_axis (hp : p ∈ axis) (U : Opens E0) : causality.Iminus U {p} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have h := Causal.Precausality.mem_Iminus_singleton.1 hx
  have := (calculus_lt h).1
  rw [rad_eq_zero.2 hp] at this
  exact absurd this (not_lt.2 (rad_nonneg x))

/-- **`J⁻_U(p) ⊂ sing₀` at a BTZ point**, in every open set (`past_local`). -/
theorem Jminus_axis_subset (hp : p ∈ axis) (U : Opens E0) : causality.Jminus U {p} ⊆ axis :=
  fun _ hx => ((le_axis_iff' hp).1 (le_of_le (Causal.Precausality.mem_Jminus_singleton.1 hx))).1

/-- **Locally `I⁺(p) = {r > 0, f > τ_p}` at a BTZ point**: in every ball `B` centred at `p`,
`I⁺_B(p) = B ∩ {r > 0, f > τ_p}`. -/
theorem Iplus_ball_axis (hp : p ∈ axis) {δ : ℝ} :
    causality.Iplus ⟨Metric.ball p δ, Metric.isOpen_ball⟩ {p} =
      Metric.ball p δ ∩ {y | 0 < rad y ∧ p.1 < fcoord y} := by
  refine Set.ext fun y => ?_
  rw [Causal.Precausality.mem_Iplus_singleton]
  constructor
  · intro h
    exact ⟨causality.lt_mem_right h, (lt_axis_iff hp).1 (lt_of_lt h)⟩
  · rintro ⟨hy, hy'⟩
    have hlt := (lt_axis_iff hp).2 hy'
    obtain ⟨θ₁, θ₂, h₁, h₂, hc⟩ := hlt
    refine clt_of_seg h₁ h₂ hc fun s hs => ?_
    have hends := le_seg_ends (adm_lift p θ₁) hc.nullCone hs
    rw [unlift_lift h₁, unlift_lift h₂] at hends
    have hpb : p ∈ Metric.ball p δ := Metric.mem_ball_self ((Metric.pos_of_mem_ball hy))
    exact mem_ball_of_le_of_le hp hends.1 hends.2 hpb hy

/-- `I⁺_U(p) ⊂ U ∩ {r > 0, f > τ_p}` for every open `U`, and equality in every ball inside `U`. -/
theorem Iplus_axis_subset (hp : p ∈ axis) (U : Opens E0) :
    causality.Iplus U {p} ⊆ U ∩ {y | 0 < rad y ∧ p.1 < fcoord y} := fun _ hy =>
  ⟨causality.lt_mem_right (Causal.Precausality.mem_Iplus_singleton.1 hy),
    (lt_axis_iff hp).1 (lt_of_lt (Causal.Precausality.mem_Iplus_singleton.1 hy))⟩

end Calculus

/-! ### Causal arc-connectedness and absolute minimality -/

section ArcConnected

open TopologicalSpace

variable {W : Opens E0} {c : ℝ → E0} {a b : ℝ}

/-- A curve for the local relation `Le` is a future causal curve of `causality` in the sense of
`Causal.Curves` (locally `≤_N`-increasing for every open `N`). -/
theorem causalCurveOn_of_curveOn (hc : Causal.CurveOn (relOn Le) W c a b) :
    causality.CausalCurveOn W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    have hpre : c ⁻¹' N ∈ 𝓝[Icc a b] t :=
      (hc.continuousOn isRelFamily_le) t ht (N.isOpen.mem_nhds htN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hmem : ∀ τ ∈ Icc s s', c τ ∈ N := fun τ hτ => hball
      ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2],
        ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩⟩
    exact ⟨s, s', h2.le, c, hc.restrict hs.1 hs'.2 hN hmem, rfl, rfl⟩

theorem chronalCurveOn_of_curveOn (hc : Causal.CurveOn (relOn Lt) W c a b) :
    causality.ChronalCurveOn W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    have hpre : c ⁻¹' N ∈ 𝓝[Icc a b] t :=
      (hc.continuousOn isRelFamily_lt) t ht (N.isOpen.mem_nhds htN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hmem : ∀ τ ∈ Icc s s', c τ ∈ N := fun τ hτ => hball
      ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2],
        ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩⟩
    exact ⟨s, s', h2, c, hc.restrict hs.1 hs'.2 hN hmem, rfl, rfl⟩

/-- Reparametrisation of a curve over `[a, b]`, `a < b`, to `[0, 1]`. -/
theorem curveOn_reparam {r : Opens E0 → E0 → E0 → Prop} (hc : Causal.CurveOn r W c a b) (hab : a < b) :
    Causal.CurveOn r W (fun t => c ((b - a) * t + a)) 0 1 :=
  Causal.CurveOn.comp_affine (k := b - a) (m := a) (sub_pos.2 hab)
    (by rw [mul_zero, zero_add, mul_one, sub_add_cancel]; exact hc)

/-- **`𝔼₀` is causally arc-connected** (`def:causal_arc_connectedness`): `≤_U` and `≪_U` are
realised by causal and chronal curves of `U` in the sense of `Causal.Curves`. -/
theorem causallyArcConnected : causality.CausallyArcConnected := by
  rw [Causal.Causality.CausallyArcConnected, Causal.Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    rcases hab.lt_or_eq with hab | hab
    · refine ⟨_, causalCurveOn_of_curveOn (curveOn_reparam hc hab), by simp, by simp⟩
    · refine ⟨fun _ => c a, causalCurveOn_of_curveOn (curveOn_of_continuousOn
        continuousOn_const (fun _ _ => hc.mem a ⟨le_rfl, hab.le⟩) fun _ _ _ _ _ => le_refl' _),
        rfl, by rw [hab]⟩
  · obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    exact ⟨_, chronalCurveOn_of_curveOn (curveOn_reparam hc hab), by simp, by simp⟩

/-- **The causality of `𝔼₀` is absolutely minimal on every open set** (`cor:model_minimal`,
`ETT.tex:1380`, for `κ = 0`, through `cor:causalement_connexe_minimal`). -/
theorem absolutelyMinimalOn (W : Opens E0) : causality.AbsolutelyMinimalOn W :=
  Causal.Causality.CausallyArcConnectedOn.absolutelyMinimalOn (causallyArcConnected.mono le_top)

end ArcConnected

/-! ### Strong tarentinity: `Z⁺ = 𝔼₀`, `Z⁻ = 𝔼₀ ∖ sing₀` -/

section Tarentin

open TopologicalSpace

variable {p : E0}

/-- A fixed future timelike vector of `(ℝ³, nullQ)`. -/
def timelikeT (k : ℝ) : ℝ × ℝ × ℝ := (k, k, 0)

theorem nullConeLt_timelikeT {k : ℝ} (hk : 0 < k) : NullConeLt (timelikeT k) := by
  refine ⟨hk, ?_⟩; simp only [timelikeT]; nlinarith

/-- **Every point has chronological future in each of its neighbourhoods** (`rem:btz_pas_tarentin`:
`Z⁺ = 𝔼₀`). -/
theorem exists_lt_mem (p : E0) {V : Set E0} (hV : V ∈ 𝓝 p) : ∃ q ∈ V, Lt p q := by
  set P := lift p (arg p.2)
  set Q := P + timelikeT 1
  have hPQ : NullConeLt (Q - P) := by
    rw [show Q - P = timelikeT 1 by simp [Q]]; exact nullConeLt_timelikeT one_pos
  have hcont := continuousOn_unlift_seg (adm_lift p (arg p.2)) hPQ.nullCone
  have h0 : unlift (seg P Q 0) = p := by rw [seg_zero]; exact unlift_lift (polar_arg p)
  have hpre : (fun s => unlift (seg P Q s)) ⁻¹' V ∈ 𝓝[Icc 0 1] 0 :=
    hcont 0 ⟨le_rfl, zero_le_one⟩ (by beta_reduce; rw [h0]; exact hV)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  set s := min (ε / 2) 1
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, min_le_right _ _⟩
  refine ⟨unlift (seg P Q s), hball ⟨?_, hs⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact (min_le_left _ _).trans_lt (by linarith)
  · have := lt_unlift_seg (adm_lift p (arg p.2)) hPQ le_rfl hs0
    rwa [h0] at this

/-- **A point off the axis has chronological past in each of its neighbourhoods**
(`rem:btz_pas_tarentin`: `Z⁻ ⊇ 𝔼₀ ∖ sing₀`). -/
theorem exists_lt_mem' (hp : p ∉ axis) {V : Set E0} (hV : V ∈ 𝓝 p) : ∃ q ∈ V, Lt q p := by
  have hr := rad_pos.2 hp
  set Q := lift p (arg p.2)
  set P := Q - timelikeT (rad p / 2)
  have hPQ : NullConeLt (Q - P) := by
    rw [show Q - P = timelikeT (rad p / 2) by simp [P]]; exact nullConeLt_timelikeT (by linarith)
  have hP : Adm P := by
    left
    have : P.2.1 = rad p - rad p / 2 := rfl
    rw [this]; linarith
  have hcont := continuousOn_unlift_seg hP hPQ.nullCone
  have h1 : unlift (seg P Q 1) = p := by rw [seg_one]; exact unlift_lift (polar_arg p)
  have hpre : (fun s => unlift (seg P Q s)) ⁻¹' V ∈ 𝓝[Icc 0 1] 1 :=
    hcont 1 ⟨zero_le_one, le_rfl⟩ (by beta_reduce; rw [h1]; exact hV)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  set s := max (1 - ε / 2) 0
  have hs1 : s < 1 := max_lt (by linarith) one_pos
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨le_max_right _ _, hs1.le⟩
  refine ⟨unlift (seg P Q s), hball ⟨?_, hs⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have : 1 - ε / 2 ≤ s := le_max_left _ _
      linarith
    · linarith
  · have := lt_unlift_seg hP hPQ hs.1 hs1
    rwa [h1] at this

theorem mem_Zplus (p : E0) : p ∈ causality.Zplus := fun U hU => by
  obtain ⟨q, hq, h⟩ := exists_lt_mem p hU
  exact ⟨q, Causal.Precausality.mem_Iplus_singleton.2 (lt_top_iff.2 h), hq⟩

theorem mem_Zminus_iff (p : E0) : p ∈ causality.Zminus ↔ p ∉ axis := by
  constructor
  · intro h hp
    obtain ⟨q, hq, -⟩ := h univ univ_mem
    rw [Iminus_axis hp] at hq
    exact hq
  · intro hp U hU
    obtain ⟨q, hq, h⟩ := exists_lt_mem' hp hU
    exact ⟨q, Causal.Precausality.mem_Iminus_singleton.2 (lt_top_iff.2 h), hq⟩

theorem isOpen_fcoord_gt (c : ℝ) : IsOpen {y : E0 | c < fcoord y} :=
  isOpen_lt continuous_const continuous_fcoord

/-- Points of the axis just below `p` lie in every neighbourhood of `p`. -/
theorem exists_axis_below (hp : p ∈ axis) {V : Set E0} (hV : V ∈ 𝓝 p) :
    ∃ ε > 0, ((p.1 - ε, 0) : E0) ∈ V := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨δ / 2, by linarith, hball ?_⟩
  have hp0 : p.2 = 0 := hp
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, hp0, dist_self]
  refine ⟨?_, hδ⟩
  rw [show p.1 - δ / 2 - p.1 = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith)]
  linarith

/-- **`𝔼₀` is tarentin** (`rem:sing_tarentin`, `ETT.tex:1364`, for the model): every point lies in
the interior of a causal diamond with vertices in any prescribed neighbourhood. -/
theorem tarentin : causality.Tarentin := by
  intro x U hU
  obtain ⟨q, hqU, hxq⟩ := exists_lt_mem x hU
  have hIq : IsOpen (causality.Iminus ⊤ {q}) := causality.isOpen_Iminus
  have hxIq : x ∈ causality.Iminus ⊤ {q} :=
    Causal.Precausality.mem_Iminus_singleton.2 (lt_top_iff.2 hxq)
  by_cases hx : x ∈ axis
  · obtain ⟨ε, hε, hpU⟩ := exists_axis_below hx hU
    set p : E0 := (x.1 - ε, 0)
    have hpax : p ∈ axis := rfl
    refine ⟨p, hpU, q, hqU, ?_⟩
    have hsub : causality.Iminus ⊤ {q} ∩ {y | p.1 < fcoord y} ⊆ causality.diamond ⊤ p q := by
      rintro y ⟨hy1, hy2⟩
      refine (causality.mem_diamond).2 ⟨?_, causality.le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hy1)⟩
      exact le_top_iff.2 ((le_axis_iff hpax).2 hy2.le)
    refine interior_maximal hsub (hIq.inter (isOpen_fcoord_gt _)) ⟨hxIq, ?_⟩
    show x.1 - ε < fcoord x
    rw [fcoord_of_axis hx]; linarith
  · obtain ⟨p, hpU, hpx⟩ := exists_lt_mem' hx hU
    refine ⟨p, hpU, q, hqU, ?_⟩
    have hsub : causality.Iminus ⊤ {q} ∩ causality.Iplus ⊤ {p} ⊆ causality.diamond ⊤ p q := by
      rintro y ⟨hy1, hy2⟩
      exact (causality.mem_diamond).2 ⟨causality.le_of_lt (Causal.Precausality.mem_Iplus_singleton.1 hy2),
        causality.le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hy1)⟩
    exact interior_maximal hsub (hIq.inter causality.isOpen_Iplus)
      ⟨hxIq, Causal.Precausality.mem_Iplus_singleton.2 (lt_top_iff.2 hpx)⟩

end Tarentin

/-! ### The BTZ axioms of `𝔼₀` and the openness of `J^±(V)` -/

section BTZ

open TopologicalSpace

variable {p : E0}

theorem axis_eq_of_fst_eq (hx : x ∈ axis) (hy : y ∈ axis) (h : x.1 = y.1) : x = y :=
  Prod.ext h (hx.trans hy.symm)

/-- `t ↦ (τ_p + t, 0)`, the BTZ line through `p`. -/
def axisLine (p : E0) (t : ℝ) : E0 := (p.1 + t, 0)

theorem axisLine_mem (p : E0) (t : ℝ) : axisLine p t ∈ axis := rfl

theorem isometry_axisLine (p : E0) : Isometry (axisLine p) := by
  refine Isometry.of_dist_eq fun t t' => ?_
  simp only [axisLine, Prod.dist_eq, dist_self, Real.dist_eq]
  rw [max_eq_left (abs_nonneg _)]
  congr 1; ring

theorem range_axisLine (p : E0) : range (axisLine p) = axis := by
  ext y
  refine ⟨fun ⟨t, ht⟩ => ht ▸ axisLine_mem p t, fun hy => ⟨y.1 - p.1, ?_⟩⟩
  exact Prod.ext (by simp [axisLine]) (by simp only [axisLine]; exact hy.symm)

theorem curveOn_axisLine (p : E0) (W : Opens E0) (a b : ℝ) :
    Causal.CurveOn (relOn Le) W (axisLine p) a b ∨ ¬ ∀ t ∈ Icc a b, axisLine p t ∈ W := by
  by_cases h : ∀ t ∈ Icc a b, axisLine p t ∈ W
  · exact Or.inl (curveOn_of_continuousOn (isometry_axisLine p).continuous.continuousOn h
      fun s _ s' _ hss' => le_axis (axisLine_mem p s) (axisLine_mem p s')
        (by simp only [axisLine]; linarith))
  · exact Or.inr h

theorem causalCurveIn_axisLine (p : E0) : causality.CausalCurveIn ⊤ univ (axisLine p) where
  nonempty := univ_nonempty
  ordConnected := ordConnected_univ
  curve a _ b _ := by
    rcases curveOn_axisLine p ⊤ a b with h | h
    · exact causalCurveOn_of_curveOn h
    · exact absurd (fun _ _ => trivial) h

/-- **The BTZ axioms of the model `𝔼₀`** (`Causal.Causality.BTZAxioms`, DEC-64's corrected form
with `Iplus_of_lt`): the first instance in the library with a non-empty BTZ locus. -/
theorem btzAxioms : causality.BTZAxioms axis where
  singularPastAt p hp := by
    have hp0 : p.2 = 0 := hp
    refine ⟨⟨fun n => (p.1 - 1 / ((n : ℝ) + 1), 0), ?_, fun n => ⟨?_, ?_⟩⟩, ?_⟩
    · have h1 : Tendsto (fun n : ℕ => p.1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 p.1) := by
        have := (tendsto_const_nhds (x := p.1)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        rwa [sub_zero] at this
      have := h1.prodMk_nhds (tendsto_const_nhds (x := (0 : ℂ)))
      rwa [show ((p.1, (0 : ℂ)) : E0) = p from Prod.ext rfl hp0.symm] at this
    · have : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      exact le_top_iff.2 (le_axis rfl hp (by simp only; linarith))
    · intro h
      have := congrArg Prod.fst h
      simp only at this
      have : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      linarith
    · intro x hxp hne
      obtain ⟨hx, hτ⟩ := (le_axis_iff' hp).1 (le_top_iff.1 hxp)
      have hlt : x.1 < p.1 := lt_of_le_of_ne hτ fun h => hne (axis_eq_of_fst_eq hx hp h)
      set d := p.1 - x.1 with hd
      have hd0 : 0 < d := by rw [hd]; linarith
      set u : ℕ → E0 := fun n => (p.1 - d / (2 * ((n : ℝ) + 1)), 0) with hu
      have hpos : ∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) := fun n => by positivity
      refine ⟨u, ?_, ?_, ?_, ?_⟩
      · have h1 : Tendsto (fun n : ℕ => d / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
          have : Tendsto (fun n : ℕ => (d / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 ((d / 2) * 0)) :=
            tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
          rw [mul_zero] at this
          refine this.congr fun n => ?_
          field_simp
        have h2 := (tendsto_const_nhds (x := p.1)).sub h1
        rw [sub_zero] at h2
        have := h2.prodMk_nhds (tendsto_const_nhds (x := (0 : ℂ)))
        rwa [show ((p.1, (0 : ℂ)) : E0) = p from Prod.ext rfl hp0.symm] at this
      · intro m n hmn
        refine le_top_iff.2 (le_axis rfl rfl ?_)
        simp only [hu]
        have : d / (2 * ((n : ℝ) + 1)) ≤ d / (2 * ((m : ℝ) + 1)) := by
          apply div_le_div_of_nonneg_left hd0.le (hpos m)
          have : (m : ℝ) ≤ n := by exact_mod_cast hmn
          linarith
        linarith
      · intro n
        have hax : u n ∈ axis := rfl
        rw [Jplus_axis hax]
        refine interior_maximal (t := {y | (u n).1 < fcoord y})
          (fun y (hy : (u n).1 < fcoord y) => hy.le) (isOpen_fcoord_gt _) ?_
        show (u n).1 < fcoord p
        rw [fcoord_of_axis hp]
        simp only [hu]
        have : 0 < d / (2 * ((n : ℝ) + 1)) := div_pos hd0 (hpos n)
        linarith
      · rw [Jminus_axis hp, Jminus_axis rfl]
        refine ⟨⟨hx, hτ⟩, mem_nhdsWithin.2 ⟨{w | w.1 < p.1 - d / 2}, isOpen_lt continuous_fst
          continuous_const, ?_, fun w ⟨hw1, hw2, _⟩ => ⟨hw2, ?_⟩⟩⟩
        · show x.1 < p.1 - d / 2
          rw [hd]; linarith
        · simp only [hu]
          have : (2 * (((0 : ℕ) : ℝ) + 1)) = 2 := by norm_num
          rw [this]
          exact hw1.le
  Iminus_eq_empty p hp := Iminus_axis hp ⊤
  Iplus_of_lt p hp p' hp' hle hne y hy := by
    obtain ⟨hy1, hy2⟩ := hy
    have hτ := (calculus_le hle).2.2.1
    have hlt : p.1 < p'.1 := lt_of_le_of_ne hτ fun h => hne (axis_eq_of_fst_eq hp hp' h)
    have hfy := (le_axis_iff hp').1 (le_top_iff.1 (Causal.Precausality.mem_Jplus_singleton.1 hy1))
    exact Causal.Precausality.mem_Iplus_singleton.2 (lt_top_iff.2 ((lt_axis_iff hp).2
      ⟨rad_pos.2 hy2, by linarith⟩))
  past_local p hp := ⟨⊤, trivial, fun q hq => ((le_axis_iff' hp).1 (le_of_le hq)).1⟩
  line p hp := by
    refine ⟨fun t => axisLine p t, Prod.ext (add_zero _) (show (0 : ℂ) = p.2 from (hp : p.2 = 0).symm), fun _ =>
      (isometry_axisLine p).isClosedEmbedding, ?_, ?_⟩
    · exact Causal.Causality.inextensible_of_unbounded (f := Prod.fst)
        (fun x y h => (calculus_le h).2.2.1) (causalCurveIn_axisLine p)
        (fun b => ⟨b - p.1 + 1, by simp only [axisLine]; linarith⟩)
        (fun b => ⟨b - p.1 - 1, by simp only [axisLine]; linarith⟩)
    · have hconn : IsPreconnected axis := by
        rw [← range_axisLine p]; exact isPreconnected_range (isometry_axisLine p).continuous
      rw [show (fun t => axisLine p t) = axisLine p from rfl, range_axisLine p,
        hconn.connectedComponentIn hp]

/-- **DEC-64's finding, a witness in `𝔼₀`**: the former `BTZAxioms.Iplus_eq`
(`I⁺(p) = J⁺(p) ∖ sing₀`, ETT l.1351) fails at every BTZ point: the point `(τ_p + 1/2, 1)` of the
radial null ray (`f = τ_p`) is in `J⁺(p) ∖ sing₀` and not in `I⁺(p)`. -/
theorem Iplus_ne_Jplus_diff (hp : p ∈ axis) :
    causality.Iplus ⊤ {p} ≠ causality.Jplus ⊤ {p} \ axis := by
  intro h
  set q : E0 := (p.1 + 1 / 2, 1)
  have hrq : rad q = 1 := by simp [rad, q]
  have hfq : fcoord q = p.1 := by simp only [fcoord, hrq, q]; ring
  have hq : q ∈ causality.Jplus ⊤ {p} \ axis := by
    refine ⟨?_, fun h' => by simp [axis, q] at h'⟩
    rw [Jplus_axis hp]; exact hfq.ge
  rw [← h, Iplus_axis hp] at hq
  exact absurd hq.2 (by rw [hfq]; exact lt_irrefl _)

/-- **`J⁺(V)` is open for every open `V`, BTZ points included** (lemma K's future-side obligation,
`BARBOT-INTERFACE.md`): at a BTZ point `p ∈ V`, `J⁺(p) ⊂ {f > τ_p − ε} ⊂ J⁺(p − ε)` with
`p − ε ∈ V` on the line; off the axis, `J⁺(v) ⊂ I⁺(v′)` for some `v′ ≪ v` in `V` (`Z⁻`). -/
theorem isOpen_Jplus {V : Set E0} (hV : IsOpen V) : IsOpen (causality.Jplus ⊤ V) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨v, hv, hvy⟩
  have hvy' := le_top_iff.1 hvy
  by_cases hax : v ∈ axis
  · obtain ⟨ε, hε, hmem⟩ := exists_axis_below hax (hV.mem_nhds hv)
    have hfy := (le_axis_iff hax).1 hvy'
    refine Filter.mem_of_superset ((isOpen_fcoord_gt (v.1 - ε)).mem_nhds (by
      show v.1 - ε < fcoord y; linarith)) fun w hw => ⟨_, hmem, le_top_iff.2 ((le_axis_iff rfl).2 ?_)⟩
    exact (le_of_lt hw : v.1 - ε ≤ fcoord w)
  · obtain ⟨v', hv', hlt⟩ := exists_lt_mem' hax (hV.mem_nhds hv)
    have hy : causality.lt ⊤ v' y := lt_top_iff.2 (hlt.trans_le hvy')
    refine Filter.mem_of_superset ((isOpen_CLt_right ⊤ v').mem_nhds hy) fun w hw =>
      ⟨v', hv', causality.le_of_lt hw⟩

/-- **`J⁻(V)` is open for every open `V`** (every point is in `Z⁺`). -/
theorem isOpen_Jminus {V : Set E0} (hV : IsOpen V) : IsOpen (causality.Jminus ⊤ V) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨v, hv, hxv⟩
  obtain ⟨v', hv', hlt⟩ := exists_lt_mem v (hV.mem_nhds hv)
  have hx : causality.lt ⊤ x v' := lt_top_iff.2 ((le_top_iff.1 hxv).trans_lt hlt)
  exact Filter.mem_of_superset ((isOpen_CLt_left ⊤ v').mem_nhds hx) fun w hw =>
    ⟨v', hv', causality.le_of_lt hw⟩

end BTZ

/-! ### The model `Y = 𝕄 ⊕ 𝔼₀` -/

section Sum

open TopologicalSpace

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]

/-- The trace `U ∩ M₁` of an open set of `M₁ ⊕ M₂`. -/
def leftOpens (U : Opens (M₁ ⊕ M₂)) : Opens M₁ :=
  ⟨Sum.inl ⁻¹' (U : Set (M₁ ⊕ M₂)), U.isOpen.preimage continuous_inl⟩

/-- The trace `U ∩ M₂` of an open set of `M₁ ⊕ M₂`. -/
def rightOpens (U : Opens (M₁ ⊕ M₂)) : Opens M₂ :=
  ⟨Sum.inr ⁻¹' (U : Set (M₁ ⊕ M₂)), U.isOpen.preimage continuous_inr⟩

theorem leftOpens_mono {U V : Opens (M₁ ⊕ M₂)} (h : V ≤ U) : leftOpens V ≤ leftOpens U :=
  fun _ hx => h hx

theorem rightOpens_mono {U V : Opens (M₁ ⊕ M₂)} (h : V ≤ U) : rightOpens V ≤ rightOpens U :=
  fun _ hx => h hx

/-- A pair of relation families, on the disjoint union: no relation across the summands. -/
def sumRel (r₁ : Opens M₁ → M₁ → M₁ → Prop) (r₂ : Opens M₂ → M₂ → M₂ → Prop)
    (U : Opens (M₁ ⊕ M₂)) : M₁ ⊕ M₂ → M₁ ⊕ M₂ → Prop
  | .inl a, .inl b => r₁ (leftOpens U) a b
  | .inr a, .inr b => r₂ (rightOpens U) a b
  | _, _ => False

/-- **The causality of a disjoint union** `M₁ ⊕ M₂`: each summand with its own causality, no
relation across. -/
def sumCausality (C₁ : Causal.Causality M₁) (C₂ : Causal.Causality M₂) : Causal.Causality (M₁ ⊕ M₂) where
  le := sumRel C₁.le C₂.le
  lt := sumRel C₁.lt C₂.lt
  le_mem_left {U x y} h := by
    rcases x with a | a <;> rcases y with b | b <;> simp only [sumRel] at h
    · exact C₁.le_mem_left h
    · exact C₂.le_mem_left h
  le_mem_right {U x y} h := by
    rcases x with a | a <;> rcases y with b | b <;> simp only [sumRel] at h
    · exact C₁.le_mem_right h
    · exact C₂.le_mem_right h
  lt_mem_left {U x y} h := by
    rcases x with a | a <;> rcases y with b | b <;> simp only [sumRel] at h
    · exact C₁.lt_mem_left h
    · exact C₂.lt_mem_left h
  lt_mem_right {U x y} h := by
    rcases x with a | a <;> rcases y with b | b <;> simp only [sumRel] at h
    · exact C₁.lt_mem_right h
    · exact C₂.lt_mem_right h
  le_refl {U x} hx := by
    rcases x with a | a
    · exact C₁.le_refl (U := leftOpens U) hx
    · exact C₂.le_refl (U := rightOpens U) hx
  le_trans {U x y z} h₁ h₂ := by
    rcases x with a | a <;> rcases y with b | b <;> rcases z with c | c <;>
      simp only [sumRel] at h₁ h₂ ⊢
    · exact C₁.le_trans h₁ h₂
    · exact C₂.le_trans h₁ h₂
  lt_trans {U x y z} h₁ h₂ := by
    rcases x with a | a <;> rcases y with b | b <;> rcases z with c | c <;>
      simp only [sumRel] at h₁ h₂ ⊢
    · exact C₁.lt_trans h₁ h₂
    · exact C₂.lt_trans h₁ h₂
  le_mono {U V} hVU x y h := by
    rcases x with a | a <;> rcases y with b | b <;> simp only [sumRel] at h ⊢
    · exact C₁.le_mono (leftOpens_mono hVU) h
    · exact C₂.le_mono (rightOpens_mono hVU) h
  lt_mono {U V} hVU x y h := by
    rcases x with a | a <;> rcases y with b | b <;> simp only [sumRel] at h ⊢
    · exact C₁.lt_mono (leftOpens_mono hVU) h
    · exact C₂.lt_mono (rightOpens_mono hVU) h
  le_of_lt {U x y} h := by
    rcases x with a | a <;> rcases y with b | b <;> simp only [sumRel] at h ⊢
    · exact C₁.le_of_lt h
    · exact C₂.le_of_lt h
  isOpen_lt_right U x := by
    rcases x with a | a
    · have : {y | sumRel C₁.lt C₂.lt U (.inl a) y} = Sum.inl '' {b | C₁.lt (leftOpens U) a b} := by
        ext y; rcases y with b | b <;> simp [sumRel]
      rw [this]; exact isOpenMap_inl _ (C₁.isOpen_lt_right _ a)
    · have : {y | sumRel C₁.lt C₂.lt U (.inr a) y} = Sum.inr '' {b | C₂.lt (rightOpens U) a b} := by
        ext y; rcases y with b | b <;> simp [sumRel]
      rw [this]; exact isOpenMap_inr _ (C₂.isOpen_lt_right _ a)
  isOpen_lt_left U x := by
    rcases x with a | a
    · have : {y | sumRel C₁.lt C₂.lt U y (.inl a)} = Sum.inl '' {b | C₁.lt (leftOpens U) b a} := by
        ext y; rcases y with b | b <;> simp [sumRel]
      rw [this]; exact isOpenMap_inl _ (C₁.isOpen_lt_left _ a)
    · have : {y | sumRel C₁.lt C₂.lt U y (.inr a)} = Sum.inr '' {b | C₂.lt (rightOpens U) b a} := by
        ext y; rcases y with b | b <;> simp [sumRel]
      rw [this]; exact isOpenMap_inr _ (C₂.isOpen_lt_left _ a)

variable {C₁ : Causal.Causality M₁} {C₂ : Causal.Causality M₂}

theorem sumCausality_le_inl {U : Opens (M₁ ⊕ M₂)} {a b : M₁} :
    (sumCausality C₁ C₂).le U (.inl a) (.inl b) ↔ C₁.le (leftOpens U) a b := Iff.rfl

theorem sumCausality_le_inr {U : Opens (M₁ ⊕ M₂)} {a b : M₂} :
    (sumCausality C₁ C₂).le U (.inr a) (.inr b) ↔ C₂.le (rightOpens U) a b := Iff.rfl

theorem sumCausality_lt_inl {U : Opens (M₁ ⊕ M₂)} {a b : M₁} :
    (sumCausality C₁ C₂).lt U (.inl a) (.inl b) ↔ C₁.lt (leftOpens U) a b := Iff.rfl

theorem sumCausality_lt_inr {U : Opens (M₁ ⊕ M₂)} {a b : M₂} :
    (sumCausality C₁ C₂).lt U (.inr a) (.inr b) ↔ C₂.lt (rightOpens U) a b := Iff.rfl

/-- A curve of a summand is a curve of the disjoint union (`inl`). -/
theorem curveOn_inl {r₁ : Opens M₁ → M₁ → M₁ → Prop} {r₂ : Opens M₂ → M₂ → M₂ → Prop}
    {U : Opens (M₁ ⊕ M₂)} {c : ℝ → M₁} {a b : ℝ} (hc : Causal.CurveOn r₁ (leftOpens U) c a b) :
    Causal.CurveOn (sumRel r₁ r₂) U (fun t => Sum.inl (c t)) a b where
  mem t ht := hc.mem t ht
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, h⟩ := hc.rel t ht (leftOpens N) (leftOpens_mono hN) htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => h s hs s' hs' h1 h2 h3⟩

theorem curveOn_inr {r₁ : Opens M₁ → M₁ → M₁ → Prop} {r₂ : Opens M₂ → M₂ → M₂ → Prop}
    {U : Opens (M₁ ⊕ M₂)} {c : ℝ → M₂} {a b : ℝ} (hc : Causal.CurveOn r₂ (rightOpens U) c a b) :
    Causal.CurveOn (sumRel r₁ r₂) U (fun t => Sum.inr (c t)) a b where
  mem t ht := hc.mem t ht
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, h⟩ := hc.rel t ht (rightOpens N) (rightOpens_mono hN) htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => h s hs s' hs' h1 h2 h3⟩

/-- **A disjoint union of causally arc-connected spacetimes is causally arc-connected.** -/
theorem sumCausality_causallyArcConnected (h₁ : C₁.CausallyArcConnected)
    (h₂ : C₂.CausallyArcConnected) : (sumCausality C₁ C₂).CausallyArcConnected := by
  rw [Causal.Causality.CausallyArcConnected, Causal.Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  rcases p with a | a <;> rcases q with b | b
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨c, hc, h0, h1⟩ := ((h₁ (leftOpens U) le_top a b).1).1 h
      exact ⟨_, curveOn_inl hc, by rw [h0], by rw [h1]⟩
    · obtain ⟨c, hc, h0, h1⟩ := ((h₁ (leftOpens U) le_top a b).2).1 h
      exact ⟨_, curveOn_inl hc, by rw [h0], by rw [h1]⟩
  · exact ⟨fun h => h.elim, fun h => h.elim⟩
  · exact ⟨fun h => h.elim, fun h => h.elim⟩
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨c, hc, h0, h1⟩ := ((h₂ (rightOpens U) le_top a b).1).1 h
      exact ⟨_, curveOn_inr hc, by rw [h0], by rw [h1]⟩
    · obtain ⟨c, hc, h0, h1⟩ := ((h₂ (rightOpens U) le_top a b).2).1 h
      exact ⟨_, curveOn_inr hc, by rw [h0], by rw [h1]⟩

end Sum

section Y

open TopologicalSpace

/-- **The model space of `𝔼₀`-manifolds**, `Y = 𝕄 ⊕ 𝔼₀` (`Geometry.ofLocalModelOfBTZ`'s instance,
`BARBOT-INTERFACE.md`: « Instance: Y = 𝕄 ⊕ E₀ »). -/
abbrev ModelY : Type := Causal.Minkowski 2 ⊕ E0

/-- **The causality of `Y`**: Minkowski's on `𝕄`, `𝔼₀`'s on `𝔼₀`. -/
noncomputable def causalityY : Causal.Causality ModelY := sumCausality (Causal.minkowski 2) causality

theorem causalityY_causallyArcConnected : causalityY.CausallyArcConnected :=
  sumCausality_causallyArcConnected Causal.minkowski_causallyArcConnected causallyArcConnected

/-- **The `LocalModel` field `absolutelyMinimalOn_Y`** (B3, `cor:massA_causalite`): the causality of
`Y` is absolutely minimal on every open set. -/
theorem absolutelyMinimalOn_Y (W : Opens ModelY) : causalityY.AbsolutelyMinimalOn W :=
  Causal.Causality.CausallyArcConnectedOn.absolutelyMinimalOn
    (causalityY_causallyArcConnected.mono le_top)

end Y

/-! ### `Le` is Minkowski's causality of the developments (DEC-33) -/

section Bridge

open TopologicalSpace

theorem nullCone_iff_isFutureCausal (V : ℝ × ℝ × ℝ) :
    NullCone V ↔ Causal.Flat.IsFutureCausal (nullToMink V) := by
  rw [Causal.Flat.IsFutureCausal, fst_nullToMink, minkQ_nullToMink]
  simp only [nullτ_apply, nullQ, NullCone]
  constructor
  · rintro ⟨ha, hb, hc⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨hab, hc⟩
    have hprod : 0 ≤ V.1 * V.2.1 := by nlinarith [sq_nonneg V.2.2]
    have ha : 0 ≤ V.1 := by
      by_contra h
      have h' : V.1 < 0 := not_le.1 h
      have hb' : 0 < V.2.1 := by linarith
      nlinarith [mul_neg_of_neg_of_pos h' hb']
    have hb : 0 ≤ V.2.1 := by
      by_contra h
      have h' : V.2.1 < 0 := not_le.1 h
      have ha' : 0 < V.1 := by linarith
      nlinarith [mul_neg_of_pos_of_neg ha' h']
    exact ⟨ha, hb, by linarith⟩

theorem nullConeLt_iff_isFutureTimelike (V : ℝ × ℝ × ℝ) :
    NullConeLt V ↔ Causal.Flat.IsFutureTimelike (nullToMink V) := by
  rw [isFutureTimelike_nullToMink_iff]
  simp only [nullτ_apply, nullQ]
  constructor
  · intro h
    have ha := h.fst_pos
    obtain ⟨hb, hc⟩ := h
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hc, hab⟩
    refine ⟨?_, by linarith⟩
    by_contra h
    have h' : V.2.1 ≤ 0 := not_lt.1 h
    have ha : 0 < V.1 := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le h', sq_nonneg V.2.2]

theorem minkowski_le_nullToMink (P Q : ℝ × ℝ × ℝ) :
    (Causal.minkowski 2).le ⊤ (nullToMink P) (nullToMink Q) ↔ NullCone (Q - P) := by
  rw [Causal.Flat.le_top_iff_minkQ, ← map_sub, nullCone_iff_isFutureCausal]

theorem minkowski_lt_nullToMink (P Q : ℝ × ℝ × ℝ) :
    (Causal.minkowski 2).lt ⊤ (nullToMink P) (nullToMink Q) ↔ NullConeLt (Q - P) := by
  rw [Causal.Flat.lt_top_iff_minkQ, ← map_sub, nullConeLt_iff_isFutureTimelike]

/-- **DEC-33's reading, checked**: `x ≼ y` iff the paper's developing map `D` (`btzPaperDev`,
`RamcovGX.tex:2237`) sends some angles of `x` and `y` to causally related points of `𝐌³`. -/
theorem le_iff_btzPaperDev : Le x y ↔ ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧
    (Causal.minkowski 2).le ⊤ (btzPaperDev (x.1, rad x, θ₁)) (btzPaperDev (y.1, rad y, θ₂)) := by
  simp only [btzPaperDev_eq_nullToMink, minkowski_le_nullToMink]; rfl

theorem lt_iff_btzPaperDev : Lt x y ↔ ∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧
    (Causal.minkowski 2).lt ⊤ (btzPaperDev (x.1, rad x, θ₁)) (btzPaperDev (y.1, rad y, θ₂)) := by
  simp only [btzPaperDev_eq_nullToMink, minkowski_lt_nullToMink]; rfl

end Bridge

/-! ### Off the axis: the sector charts are causal isomorphisms onto open sets of `𝐌³` -/

section Sector

open TopologicalSpace

variable {y w : E0}

/-- **The slit sector around `y`**: `z / z_y ∉ ℝ≤0`; on it the angle `angle y` continues `arg z_y`. -/
def sector (y : E0) : Set E0 := {w | w.2 / y.2 ∈ Complex.slitPlane}

theorem isOpen_sector (y : E0) : IsOpen (sector y) :=
  Complex.isOpen_slitPlane.preimage (continuous_snd.div_const _)

/-- The sector as an open set. -/
def sectorOpens (y : E0) : Opens E0 := ⟨sector y, isOpen_sector y⟩

theorem mem_sector_self (hy : y.2 ≠ 0) : y ∈ sector y := by
  show y.2 / y.2 ∈ Complex.slitPlane; rw [div_self hy]; exact Complex.one_mem_slitPlane

theorem ne_zero_of_mem_sector (hw : w ∈ sector y) : w.2 ≠ 0 := fun h => by
  have := Complex.slitPlane_ne_zero hw; rw [h, zero_div] at this; exact this rfl

theorem not_mem_axis_of_mem_sector (hw : w ∈ sector y) : w ∉ axis := ne_zero_of_mem_sector hw

/-- The branch of the angle on the sector. -/
noncomputable def angle (y w : E0) : ℝ := arg y.2 + arg (w.2 / y.2)

/-- **The sector chart**: the development with the branch angle, in Minkowski coordinates
(`= btzPaperDev (τ, r, angle)`). -/
noncomputable def chartMap (y w : E0) : Causal.Minkowski 2 := nullToMink (locLift y w)

theorem chartMap_eq (y w : E0) : chartMap y w = btzPaperDev (w.1, rad w, angle y w) :=
  (btzPaperDev_eq_nullToMink _).symm

theorem polar_angle (hy : y.2 ≠ 0) (w : E0) : Polar w (angle y w) := polar_add_arg_div y w hy

theorem continuousOn_angle (y : E0) : ContinuousOn (angle y) (sector y) := fun _ hw =>
  (continuousAt_const.add (ContinuousAt.comp (f := fun w : E0 => w.2 / y.2)
    (Complex.continuousAt_arg hw) (continuousAt_snd.div_const _))).continuousWithinAt

theorem continuousOn_locLift (y : E0) : ContinuousOn (locLift y) (sector y) :=
  continuous_btzPaperNull.comp_continuousOn
    (continuous_fst.continuousOn.prodMk (continuous_rad.continuousOn.prodMk (continuousOn_angle y)))

theorem continuousOn_chartMap (y : E0) : ContinuousOn (chartMap y) (sector y) :=
  nullToMinkHomeomorph.continuous.comp_continuousOn (continuousOn_locLift y)

theorem unlift_symm_chartMap (hy : y.2 ≠ 0) (w : E0) :
    unlift (nullToMink.symm (chartMap y w)) = w := by
  rw [chartMap, LinearEquiv.symm_apply_apply]; exact unlift_lift (polar_angle hy w)

theorem injOn_chartMap (hy : y.2 ≠ 0) : InjOn (chartMap y) (sector y) := fun w _ w' _ h => by
  rw [← unlift_symm_chartMap hy w, ← unlift_symm_chartMap hy w', h]

/-- The image of the sector in null coordinates. -/
def Img (y : E0) : Set (ℝ × ℝ × ℝ) := {R | 0 < R.2.1 ∧ |-(R.2.2 / R.2.1) - arg y.2| < π}

theorem abs_arg_lt_pi_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) : |arg z| < π := by
  rw [abs_lt]
  exact ⟨Complex.neg_pi_lt_arg z, lt_of_le_of_ne (Complex.arg_le_pi z)
    (Complex.mem_slitPlane_iff_arg.1 hz).1⟩

theorem locLift_mem_Img (hw : w ∈ sector y) : locLift y w ∈ Img y := by
  have hr : 0 < rad w := norm_pos_iff.2 (ne_zero_of_mem_sector hw)
  refine ⟨hr, ?_⟩
  have : -((locLift y w).2.2 / (locLift y w).2.1) = angle y w := by
    simp only [locLift, lift, btzPaperNull]
    field_simp
    rfl
  rw [this, angle, add_sub_cancel_left]
  exact abs_arg_lt_pi_of_mem_slitPlane hw

theorem locLift_unlift (hy : y.2 ≠ 0) {R : ℝ × ℝ × ℝ} (hR : R ∈ Img y) :
    locLift y (unlift R) = R := by
  obtain ⟨hB, hθ⟩ := hR
  set θ := -(R.2.2 / R.2.1)
  have hry : 0 < rad y := norm_pos_iff.2 hy
  have hratio : (unlift R).2 / y.2 = ((R.2.1 / rad y : ℝ) : ℂ) * cexp (↑(θ - arg y.2) * I) := by
    have h1 : (unlift R).2 = (R.2.1 : ℂ) * cexp (↑θ * I) := rfl
    have h2 : y.2 = (rad y : ℂ) * cexp (↑(arg y.2) * I) := polar_arg y
    rw [h1]
    conv_lhs => rw [h2]
    have hne : (rad y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hry.ne'
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.ofReal_div]
    field_simp
  have key : ∀ φ : ℝ, φ ∈ Ioc (-π) π → arg (cexp (↑φ * I)) = φ := fun φ hφ => by
    rw [Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I hφ
  have harg : arg ((unlift R).2 / y.2) = θ - arg y.2 := by
    rw [hratio, Complex.arg_real_mul _ (div_pos hB hry)]
    rw [abs_lt] at hθ
    exact key _ ⟨hθ.1, hθ.2.le⟩
  show lift (unlift R) (arg y.2 + arg ((unlift R).2 / y.2)) = R
  rw [harg, add_sub_cancel]
  exact lift_unlift (Or.inl hB)

theorem image_chartMap (hy : y.2 ≠ 0) {V : Set E0} (hV : V ⊆ sector y) :
    chartMap y '' V = nullToMink.symm ⁻¹' (Img y ∩ unlift ⁻¹' V) := by
  ext m
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [chartMap, LinearEquiv.symm_apply_apply]; exact locLift_mem_Img (hV hw)
    · show unlift (nullToMink.symm (chartMap y w)) ∈ V
      rw [unlift_symm_chartMap hy]; exact hw
  · rintro ⟨h1, h2⟩
    refine ⟨_, h2, ?_⟩
    rw [chartMap, locLift_unlift hy h1, LinearEquiv.apply_symm_apply]

theorem isOpen_image_chartMap (hy : y.2 ≠ 0) {V : Set E0} (hV : V ⊆ sector y) (hVo : IsOpen V) :
    IsOpen (chartMap y '' V) := by
  rw [image_chartMap hy hV]
  refine IsOpen.preimage nullToMinkHomeomorph.symm.continuous ?_
  have hpos : IsOpen {R : ℝ × ℝ × ℝ | 0 < R.2.1} := isOpen_lt continuous_const continuous_snd.fst
  have hf : ContinuousOn (fun R : ℝ × ℝ × ℝ => (-(R.2.2 / R.2.1), unlift R))
      {R : ℝ × ℝ × ℝ | 0 < R.2.1} := fun R hR =>
    ((continuousAt_snd.snd.div continuousAt_snd.fst (ne_of_gt hR)).neg.prodMk
      (continuousAt_unlift (ne_of_gt hR))).continuousWithinAt
  have ht : IsOpen ({θ : ℝ | |θ - arg y.2| < π} ×ˢ V) :=
    (isOpen_lt ((continuous_id.sub continuous_const).abs) continuous_const).prod hVo
  have := hf.isOpen_inter_preimage hpos ht
  convert this using 1
  ext R
  simp only [Img, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_prod]
  tauto

/-- A curve of `𝔼₀` in the sector develops to a causal curve of `𝐌³` (`Causal.Curves`). -/
theorem curveOn_chartMap {W : Opens E0} (hW : (W : Set E0) ⊆ sector y)
    {c : ℝ → E0} {a b : ℝ} {U : Opens (Causal.Minkowski 2)}
    (hU : ∀ t ∈ Icc a b, chartMap y (c t) ∈ U) {Rel : E0 → E0 → Prop}
    {RelM : Opens (Causal.Minkowski 2) → Causal.Minkowski 2 → Causal.Minkowski 2 → Prop}
    (hRelTrans : ∀ {x y z}, Rel x y → Rel y z → Rel x z)
    (hstep : ∀ s s' : E0, Rel s s' → |angle y s' - angle y s| ≤ π →
      ∀ (B : Opens (Causal.Minkowski 2)), Convex ℝ (B : Set (Causal.Minkowski 2)) →
        chartMap y s ∈ B → chartMap y s' ∈ B → RelM B (chartMap y s) (chartMap y s'))
    (hmono : ∀ {B N : Opens (Causal.Minkowski 2)}, B ≤ N → ∀ {p q}, RelM B p q → RelM N p q)
    (hc : Causal.CurveOn (relOn Rel) W c a b) :
    Causal.CurveOn RelM U (fun t => chartMap y (c t)) a b where
  mem := hU
  rel t ht N hN htN := by
    have hcont := hc.continuousOn (isRelFamily_relOn (R := Rel) (fun h₁ h₂ => hRelTrans h₁ h₂))
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 N.isOpen _ htN
    have hct : c t ∈ sector y := hW (hc.mem t ht)
    have hsec : sector y ∈ 𝓝 (c t) := (isOpen_sector y).mem_nhds hct
    have h1 : (fun s => chartMap y (c s)) ⁻¹' Metric.ball (chartMap y (c t)) ρ ∈ 𝓝[Icc a b] t :=
      (((continuousOn_chartMap y).continuousAt hsec).comp_continuousWithinAt (hcont t ht))
        (Metric.ball_mem_nhds _ hρ)
    have h2 : (fun s => angle y (c s)) ⁻¹' Metric.ball (angle y (c t)) (π / 2) ∈ 𝓝[Icc a b] t :=
      (((continuousOn_angle y).continuousAt hsec).comp_continuousWithinAt (hcont t ht))
        (Metric.ball_mem_nhds _ (by positivity))
    obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhdsWithin_iff.1 (Filter.inter_mem h1 h2)
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht W le_rfl (hc.mem t ht)
    refine ⟨max l (t - ε), min u (t + ε), max_lt hl (by linarith), lt_min hu (by linarith),
      fun s hs s' hs' h1' h2' h3' => ?_⟩
    have hl' : l < s := (le_max_left _ _).trans_lt h1'
    have hu' : s' < u := h3'.trans_le (min_le_left _ _)
    have hsε : s ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right l (t - ε), min_le_right u (t + ε)]
    have hs'ε : s' ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right l (t - ε), min_le_right u (t + ε)]
    obtain ⟨hsB, hsA⟩ := hεb ⟨hsε, hs⟩
    obtain ⟨hs'B, hs'A⟩ := hεb ⟨hs'ε, hs'⟩
    have hR : Rel (c s) (c s') := (hrel s hs s' hs' hl' h2' hu').2.2
    have hang : |angle y (c s') - angle y (c s)| ≤ π := by
      simp only [mem_preimage, Metric.mem_ball, Real.dist_eq] at hsA hs'A
      have := abs_sub_le (angle y (c s')) (angle y (c t)) (angle y (c s))
      rw [abs_sub_comm (angle y (c t))] at this
      linarith
    let B : Opens (Causal.Minkowski 2) := ⟨Metric.ball (chartMap y (c t)) ρ, Metric.isOpen_ball⟩
    exact hmono (fun z hz => hball hz : B ≤ N) (hstep _ _ hR hang B (convex_ball _ _) hsB hs'B)

theorem curveOn_chartMap_le (hy : y.2 ≠ 0) {W : Opens E0} (hW : (W : Set E0) ⊆ sector y)
    {c : ℝ → E0} {a b : ℝ} {U : Opens (Causal.Minkowski 2)}
    (hU : ∀ t ∈ Icc a b, chartMap y (c t) ∈ U) (hc : Causal.CurveOn (relOn Le) W c a b) :
    Causal.CurveOn (Causal.minkowski 2).le U (fun t => chartMap y (c t)) a b :=
  curveOn_chartMap (Rel := Le) hW hU Le.trans (fun s s' h hang _ hB hs hs' =>
    (Causal.Flat.le_iff_of_convex hB).2 ⟨hs, hs', (minkowski_le_nullToMink _ _).2
      (h.of_polar (polar_angle hy s) (polar_angle hy s') hang)⟩)
    (fun hBN _ _ h => (Causal.minkowski 2).le_mono hBN h) hc

theorem curveOn_chartMap_lt (hy : y.2 ≠ 0) {W : Opens E0} (hW : (W : Set E0) ⊆ sector y)
    {c : ℝ → E0} {a b : ℝ} {U : Opens (Causal.Minkowski 2)}
    (hU : ∀ t ∈ Icc a b, chartMap y (c t) ∈ U) (hc : Causal.CurveOn (relOn Lt) W c a b) :
    Causal.CurveOn (Causal.minkowski 2).lt U (fun t => chartMap y (c t)) a b :=
  curveOn_chartMap (Rel := Lt) hW hU Lt.trans (fun s s' h hang _ hB hs hs' =>
    (Causal.Flat.lt_iff_of_convex hB).2 ⟨hs, hs', (minkowski_lt_nullToMink _ _).2
      (h.of_polar (polar_angle hy s) (polar_angle hy s') hang)⟩)
    (fun hBN _ _ h => (Causal.minkowski 2).lt_mono hBN h) hc

/-- A curve, continuous and locally `R`-increasing, is a curve for `relOn R`. -/
theorem curveOn_of_local {R : E0 → E0 → Prop} {W : Opens E0} {c : ℝ → E0} {a b : ℝ}
    (hc : ContinuousOn c (Icc a b)) (hmem : ∀ t ∈ Icc a b, c t ∈ W)
    (hR : ∀ t ∈ Icc a b, ∃ l u, l < t ∧ t < u ∧ ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, l < s → s < s' →
      s' < u → R (c s) (c s')) :
    Causal.CurveOn (relOn R) W c a b where
  mem := hmem
  rel t ht N _ htN := by
    have hN : c ⁻¹' N ∈ 𝓝[Icc a b] t := hc t ht (N.isOpen.mem_nhds htN)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hN
    obtain ⟨l, u, hl, hu, hRl⟩ := hR t ht
    refine ⟨max l (t - ε), min u (t + ε), max_lt hl (by linarith), lt_min hu (by linarith),
      fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hsb : s ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right l (t - ε), min_le_right u (t + ε)]
    have hs'b : s' ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right l (t - ε), min_le_right u (t + ε)]
    exact ⟨hball ⟨hsb, hs⟩, hball ⟨hs'b, hs'⟩, hRl s hs s' hs'
      ((le_max_left _ _).trans_lt h1) h2 (h3.trans_le (min_le_left _ _))⟩

/-- A causal (chronological) curve of `𝐌³` in the image of the sector pulls back to `𝔼₀`. -/
theorem curveOn_pullback (hy : y.2 ≠ 0) {V : Opens E0} (hV : (V : Set E0) ⊆ sector y)
    {U : Opens (Causal.Minkowski 2)} (hU : (U : Set (Causal.Minkowski 2)) = chartMap y '' V)
    {d : ℝ → Causal.Minkowski 2} {a b : ℝ} {RelM : Opens (Causal.Minkowski 2) →
      Causal.Minkowski 2 → Causal.Minkowski 2 → Prop} (hRelM : Causal.IsRelFamily RelM)
    {Rel : E0 → E0 → Prop} (hdRel : ∀ p q : E0, RelM U (chartMap y p) (chartMap y q) → Rel p q)
    (hd : Causal.CurveOn RelM U d a b) :
    Causal.CurveOn (relOn Rel) V (fun t => unlift (nullToMink.symm (d t))) a b := by
  have hpt : ∀ t ∈ Icc a b, ∃ w ∈ V, chartMap y w = d t := fun t ht => by
    have := hd.mem t ht; rw [← SetLike.mem_coe, hU] at this; exact this
  have heq : ∀ t ∈ Icc a b, chartMap y (unlift (nullToMink.symm (d t))) = d t := fun t ht => by
    obtain ⟨w, -, hw⟩ := hpt t ht; rw [← hw, unlift_symm_chartMap hy]
  have hdc := hd.continuousOn hRelM
  refine curveOn_of_local ?_ (fun t ht => ?_) (fun t ht => ?_)
  · intro t ht
    obtain ⟨w, hwV, hw⟩ := hpt t ht
    have hB : (nullToMink.symm (d t)).2.1 ≠ 0 := by
      rw [← hw, chartMap, LinearEquiv.symm_apply_apply]
      exact (norm_pos_iff.2 (ne_zero_of_mem_sector (hV hwV))).ne'
    exact ((continuousAt_unlift hB).comp nullToMinkHomeomorph.symm.continuous.continuousAt
      |>.comp_continuousWithinAt (hdc t ht))
  · obtain ⟨w, hwV, hw⟩ := hpt t ht; rw [← hw, unlift_symm_chartMap hy]; exact hwV
  · obtain ⟨l, u, hl, hu, hrel⟩ := hd.rel t ht U le_rfl (hd.mem t ht)
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => hdRel _ _ ?_⟩
    rw [heq s hs, heq s' hs']
    exact hrel s hs s' hs' h1 h2 h3

/-- **Off the axis the causality of `𝔼₀` is Minkowski's through the sector chart**: for every open
`V` in the sector, `≤_V` and `≪_V` are carried to `≤_{D(V)}` and `≪_{D(V)}`. -/
theorem chartIso_sector (hy : y.2 ≠ 0) {V : Opens E0} (hV : (V : Set E0) ⊆ sector y)
    {U : Opens (Causal.Minkowski 2)} (hU : (U : Set (Causal.Minkowski 2)) = chartMap y '' V)
    {p q : E0} (hp : p ∈ V) (hq : q ∈ V) :
    (causality.le V p q ↔ (Causal.minkowski 2).le U (chartMap y p) (chartMap y q)) ∧
      (causality.lt V p q ↔ (Causal.minkowski 2).lt U (chartMap y p) (chartMap y q)) := by
  have hmapsU : ∀ w ∈ V, chartMap y w ∈ U := fun w hw => by
    rw [← SetLike.mem_coe, hU]; exact mem_image_of_mem _ hw
  have hdLe : ∀ p q : E0, (Causal.minkowski 2).le U (chartMap y p) (chartMap y q) → Le p q :=
    fun p q h => by
      have := (minkowski_le_nullToMink _ _).1 ((Causal.minkowski 2).le_mono le_top h)
      exact ⟨_, _, polar_angle hy p, polar_angle hy q, this⟩
  have hdLt : ∀ p q : E0, (Causal.minkowski 2).lt U (chartMap y p) (chartMap y q) → Lt p q :=
    fun p q h => by
      have := (minkowski_lt_nullToMink _ _).1 ((Causal.minkowski 2).lt_mono le_top h)
      exact ⟨_, _, polar_angle hy p, polar_angle hy q, this⟩
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    have hcM := curveOn_chartMap_le hy hV (fun t ht => hmapsU _ (hc.mem t ht)) hc
    rcases hab.lt_or_eq with hab | hab
    · exact hcM.rel_of_lt (Causal.Precausality.isRelFamily_le _) le_rfl hab le_rfl
    · rw [hab]; exact (Causal.minkowski 2).le_refl (hmapsU _ (hc.mem b ⟨hab.le, le_rfl⟩))
  · obtain ⟨d, hd, hd0, hd1⟩ := ((Causal.minkowski_causallyArcConnected U le_top _ _).1).1 h
    refine ⟨0, 1, zero_le_one, _, curveOn_pullback hy hV hU
      (Causal.Precausality.isRelFamily_le _) hdLe hd, ?_, ?_⟩
    · simp only [hd0, unlift_symm_chartMap hy]
    · simp only [hd1, unlift_symm_chartMap hy]
  · obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    exact (curveOn_chartMap_lt hy hV (fun t ht => hmapsU _ (hc.mem t ht)) hc).rel_of_lt
      (Causal.Precausality.isRelFamily_lt _) le_rfl hab le_rfl
  · obtain ⟨d, hd, hd0, hd1⟩ := ((Causal.minkowski_causallyArcConnected U le_top _ _).2).1 h
    refine ⟨0, 1, zero_lt_one, _, curveOn_pullback hy hV hU
      (Causal.Precausality.isRelFamily_lt _) hdLt hd, ?_, ?_⟩
    · simp only [hd0, unlift_symm_chartMap hy]
    · simp only [hd1, unlift_symm_chartMap hy]

/-- **The sector chart is an abstract `𝕄≥0`-morphism** (`Causal.IsEMorphismOn`), injective:
`𝔼₀ ∖ sing₀` is locally Minkowski space as a topological spacetime. -/
theorem isEMorphismOn_chartMap (hy : y.2 ≠ 0) :
    Causal.IsEMorphismOn causality (Causal.minkowski 2) (sectorOpens y) (chartMap y) where
  continuousOn := continuousOn_chartMap y
  isOpen_image V hV := isOpen_image_chartMap hy hV V.isOpen
  map_le V U hV hmaps x z h := by
    obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    have hcM := curveOn_chartMap_le hy hV (fun t ht => hmaps (hc.mem t ht)) hc
    rcases hab.lt_or_eq with hab | hab
    · exact hcM.rel_of_lt (Causal.Precausality.isRelFamily_le _) le_rfl hab le_rfl
    · rw [hab]; exact (Causal.minkowski 2).le_refl (hmaps (hc.mem b ⟨hab.le, le_rfl⟩))
  map_lt V U hV hmaps x z h := by
    obtain ⟨a, b, hab, c, hc, rfl, rfl⟩ := h
    exact (curveOn_chartMap_lt hy hV (fun t ht => hmaps (hc.mem t ht)) hc).rel_of_lt
      (Causal.Precausality.isRelFamily_lt _) le_rfl hab le_rfl
  locally x hx := ⟨sectorOpens y, le_rfl, hx, injOn_chartMap hy, fun V' hV' U hU p hp q hq =>
    chartIso_sector hy hV' hU hp hq⟩

end Sector

/-! ### Cone slices (`LocalModel.coneSliceFuture`, `coneSlicePast`) -/

section Slices

open TopologicalSpace

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- **The cone-slice property at `y`** in the shape of `LocalModel.coneSliceFuture` /
`coneSlicePast`: in every open `O ∋ y`, a set `K ⊆ O` of points `z ≠ y` with `Q O z` such that every
open `V ⊇ K` contains a Cauchy surface `Γ` of some open `N ∋ y`, `N ⊆ O`. -/
def SliceAt (C : Causal.Causality M) (y : M) (Q : Opens M → M → Prop) : Prop :=
  ∀ O : Opens M, y ∈ O → ∃ K : Set M, K ⊆ O ∧ (∀ z ∈ K, z ≠ y ∧ Q O z) ∧
    ∀ V : Set M, IsOpen V → K ⊆ V → ∃ (N : Opens M) (Γ : Set M), y ∈ N ∧ N ≤ O ∧ Γ ⊆ N ∧
      Γ ⊆ V ∧ C.IsCauchySurfaceOn N Γ

/-- **Pull-back of cone slices** along an injective abstract `𝕄≥0`-morphism on `W ∋ y`. -/
theorem SliceAt.pullback {C : Causal.Causality M} {D : Causal.Causality N} {W : Opens M} {φ : M → N}
    (h : Causal.IsEMorphismOn C D W φ) (hinj : InjOn φ W) {y : M} (hy : y ∈ W)
    {QM : Opens M → M → Prop} {QN : Opens N → N → Prop}
    (hQmono : ∀ {O₁ O₂ : Opens M}, O₁ ≤ O₂ → ∀ z, QM O₁ z → QM O₂ z)
    (hQ : ∀ O' : Opens M, O' ≤ W → y ∈ O' → ∀ U : Opens N, (U : Set N) = φ '' O' →
      ∀ z ∈ O', QN U (φ z) → QM O' z)
    (hD : SliceAt D (φ y) QN) : SliceAt C y QM := by
  intro O hyO
  set O' : Opens M := O ⊓ W
  have hyO' : y ∈ O' := ⟨hyO, hy⟩
  set U' : Opens N := ⟨φ '' O', h.isOpen_image O' inf_le_right⟩
  obtain ⟨K', hK'U, hK'p, hK'V⟩ := hD U' (mem_image_of_mem φ hyO')
  have hcont : ContinuousOn φ W := h.continuousOn
  refine ⟨O' ∩ φ ⁻¹' K', fun z hz => hz.1.1, fun z hz => ?_, fun V hV hKV => ?_⟩
  · obtain ⟨hne, hq⟩ := hK'p _ hz.2
    exact ⟨fun hzy => hne (hzy ▸ rfl), hQmono inf_le_left z (hQ O' inf_le_right hyO' U' rfl z hz.1 hq)⟩
  · set OV : Opens M := O' ⊓ ⟨V, hV⟩
    set V' : Set N := φ '' OV
    have hV'o : IsOpen V' := h.isOpen_image OV (inf_le_left.trans inf_le_right)
    have hK'V' : K' ⊆ V' := fun k' hk' => by
      obtain ⟨k, hk, rfl⟩ := hK'U hk'
      exact ⟨k, ⟨hk, hKV ⟨hk, hk'⟩⟩, rfl⟩
    obtain ⟨N', Γ', hyN', hN'U, hΓN', hΓV', hC⟩ := hK'V V' hV'o hK'V'
    have hNo : IsOpen ((O' : Set M) ∩ φ ⁻¹' N') :=
      (hcont.mono inf_le_right).isOpen_inter_preimage O'.isOpen N'.isOpen
    set Nm : Opens M := ⟨(O' : Set M) ∩ φ ⁻¹' N', hNo⟩
    have himN : (N' : Set N) = φ '' Nm := by
      ext n'
      refine ⟨fun hn' => ?_, fun ⟨o, ho, hoe⟩ => hoe ▸ ho.2⟩
      obtain ⟨o, ho, rfl⟩ := hN'U hn'
      exact ⟨o, ⟨ho, hn'⟩, rfl⟩
    have himΓ : Γ' = φ '' ((O' : Set M) ∩ φ ⁻¹' Γ') := by
      ext n'
      refine ⟨fun hn' => ?_, fun ⟨o, ho, hoe⟩ => hoe ▸ ho.2⟩
      obtain ⟨o, ho, rfl⟩ := hN'U (hΓN' hn')
      exact ⟨o, ⟨ho, hn'⟩, rfl⟩
    refine ⟨Nm, (O' : Set M) ∩ φ ⁻¹' Γ', ⟨hyO', hyN'⟩, fun z hz => hz.1.1,
      fun z hz => ⟨hz.1, hΓN' hz.2⟩, fun z hz => ?_, ?_⟩
    · obtain ⟨v, hv, hve⟩ := hΓV' hz.2
      have : v = z := hinj (hv.1.2) (hz.1.2) hve
      exact this ▸ hv.2
    · have hNW : Nm ≤ W := fun z (hz : z ∈ (O' : Set M) ∩ φ ⁻¹' N') => hz.1.2
      have hΓN : (O' : Set M) ∩ φ ⁻¹' Γ' ⊆ Nm := fun z (hz : z ∈ (O' : Set M) ∩ φ ⁻¹' Γ') =>
        (⟨hz.1, hΓN' hz.2⟩ : z ∈ (O' : Set M) ∩ φ ⁻¹' N')
      rw [h.isCauchySurfaceOn_image_iff hinj hNW himN hΓN, ← himΓ]
      exact hC

/-- **Push-forward of cone slices** along an injective abstract `𝕄≥0`-morphism defined everywhere. -/
theorem SliceAt.pushforward {C : Causal.Causality M} {D : Causal.Causality N} {φ : M → N}
    (h : Causal.IsEMorphismOn C D ⊤ φ) (hinj : Injective φ) {y : M}
    {QM : Opens M → M → Prop} {QN : Opens N → N → Prop}
    (hQ : ∀ (O : Opens N) (hO : IsOpen (φ ⁻¹' (O : Set N))) (z : M),
      QM ⟨φ ⁻¹' (O : Set N), hO⟩ z → QN O (φ z))
    (hC : SliceAt C y QM) : SliceAt D (φ y) QN := by
  have hcont : Continuous φ := continuousOn_univ.1 (by simpa using h.continuousOn)
  intro O hyO
  have hOo : IsOpen (φ ⁻¹' (O : Set N)) := O.isOpen.preimage hcont
  obtain ⟨K, hKO, hKp, hKV⟩ := hC ⟨φ ⁻¹' O, hOo⟩ hyO
  refine ⟨φ '' K, fun _ ⟨z, hz, hze⟩ => hze ▸ hKO hz, ?_, fun V hV hKV' => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hne, hq⟩ := hKp z hz
    exact ⟨fun h' => hne (hinj h'), hQ O hOo z hq⟩
  · obtain ⟨Nm, Γ, hyN, hNO, hΓN, hΓV, hCa⟩ := hKV (φ ⁻¹' V) (hV.preimage hcont)
      fun z hz => hKV' ⟨z, hz, rfl⟩
    refine ⟨⟨φ '' Nm, h.isOpen_image Nm le_top⟩, φ '' Γ, ⟨y, hyN, rfl⟩,
      fun _ ⟨z, hz, hze⟩ => hze ▸ hNO hz, image_mono hΓN, fun _ ⟨z, hz, hze⟩ => hze ▸ hΓV hz, ?_⟩
    exact (h.isCauchySurfaceOn_image_iff hinj.injOn le_top rfl hΓN).1 hCa

/-- Minkowski's cone slices (`Causal.CBG.minkowski_coneSlice`) in the shape of `SliceAt`. -/
theorem minkowski_sliceAt_future (m : Causal.Minkowski 2) :
    SliceAt (Causal.minkowski 2) m fun O z => (Causal.minkowski 2).le O z m := by
  intro O hO
  obtain ⟨K, hK, hKp, hV⟩ := Causal.CBG.minkowski_coneSlice (Or.inl rfl) m O hO
  exact ⟨K, hK, fun z hz => ⟨(hKp z hz).1, (hKp z hz).2.1 rfl⟩, hV⟩

theorem minkowski_sliceAt_past (m : Causal.Minkowski 2) :
    SliceAt (Causal.minkowski 2) m fun O z => (Causal.minkowski 2).le O m z := by
  intro O hO
  obtain ⟨K, hK, hKp, hV⟩ := Causal.CBG.minkowski_coneSlice (Or.inr rfl) m O hO
  exact ⟨K, hK, fun z hz => ⟨(hKp z hz).1, (hKp z hz).2.2 rfl⟩, hV⟩

/-- **Cone slices of `𝔼₀` off the axis, future side** (transported from Minkowski space through the
sector chart). -/
theorem sliceAt_future_of_not_mem_axis {y : E0} (hy : y ∉ axis) :
    SliceAt causality y fun O z => z ∉ axis ∧ causality.le O z y := by
  have hy0 : y.2 ≠ 0 := hy
  refine SliceAt.pullback (isEMorphismOn_chartMap hy0) (injOn_chartMap hy0)
    (mem_sector_self hy0) (fun hO _ h => ⟨h.1, causality.le_mono hO h.2⟩) ?_
    (minkowski_sliceAt_future (chartMap y y))
  intro O' hO' hyO' U hU z hz hq
  exact ⟨not_mem_axis_of_mem_sector (hO' hz), (chartIso_sector hy0 hO' hU hz hyO').1.2 hq⟩

/-- **Cone slices of `𝔼₀` off the axis, past side.** -/
theorem sliceAt_past_of_not_mem_axis {y : E0} (hy : y ∉ axis) :
    SliceAt causality y fun O z => causality.le O y z := by
  have hy0 : y.2 ≠ 0 := hy
  refine SliceAt.pullback (isEMorphismOn_chartMap hy0) (injOn_chartMap hy0)
    (mem_sector_self hy0) (fun hO _ h => causality.le_mono hO h) ?_
    (minkowski_sliceAt_past (chartMap y y))
  intro O' hO' hyO' U hU z hz hq
  exact (chartIso_sector hy0 hO' hU hyO' hz).1.2 hq

end Slices

/-! ### The summands of `Y` as abstract `𝕄≥0`-morphisms; the cone-slice fields of `Y` -/

section YSlices

open TopologicalSpace

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  {C₁ : Causal.Causality M₁} {C₂ : Causal.Causality M₂}

theorem leftOpens_image_inl {U : Opens (M₁ ⊕ M₂)} {V : Opens M₁}
    (hU : (U : Set (M₁ ⊕ M₂)) = Sum.inl '' V) : leftOpens U = V := by
  ext a
  show Sum.inl a ∈ (U : Set (M₁ ⊕ M₂)) ↔ a ∈ V
  rw [hU]; exact ⟨fun ⟨b, hb, he⟩ => Sum.inl_injective he ▸ hb, fun h => ⟨a, h, rfl⟩⟩

theorem rightOpens_image_inr {U : Opens (M₁ ⊕ M₂)} {V : Opens M₂}
    (hU : (U : Set (M₁ ⊕ M₂)) = Sum.inr '' V) : rightOpens U = V := by
  ext a
  show Sum.inr a ∈ (U : Set (M₁ ⊕ M₂)) ↔ a ∈ V
  rw [hU]; exact ⟨fun ⟨b, hb, he⟩ => Sum.inr_injective he ▸ hb, fun h => ⟨a, h, rfl⟩⟩

theorem isEMorphismOn_inl : Causal.IsEMorphismOn C₁ (sumCausality C₁ C₂) ⊤ Sum.inl where
  continuousOn := continuous_inl.continuousOn
  isOpen_image V _ := isOpenMap_inl _ V.isOpen
  map_le V U _ hmaps _ _ h := C₁.le_mono (fun a ha => hmaps ha) h
  map_lt V U _ hmaps _ _ h := C₁.lt_mono (fun a ha => hmaps ha) h
  locally _ _ := ⟨⊤, le_rfl, trivial, Sum.inl_injective.injOn, fun V' _ U hU _ _ _ _ => by
    show (_ ↔ C₁.le (leftOpens U) _ _) ∧ (_ ↔ C₁.lt (leftOpens U) _ _)
    rw [leftOpens_image_inl hU]; exact ⟨Iff.rfl, Iff.rfl⟩⟩

theorem isEMorphismOn_inr : Causal.IsEMorphismOn C₂ (sumCausality C₁ C₂) ⊤ Sum.inr where
  continuousOn := continuous_inr.continuousOn
  isOpen_image V _ := isOpenMap_inr _ V.isOpen
  map_le V U _ hmaps _ _ h := C₂.le_mono (fun a ha => hmaps ha) h
  map_lt V U _ hmaps _ _ h := C₂.lt_mono (fun a ha => hmaps ha) h
  locally _ _ := ⟨⊤, le_rfl, trivial, Sum.inr_injective.injOn, fun V' _ U hU _ _ _ _ => by
    show (_ ↔ C₂.le (rightOpens U) _ _) ∧ (_ ↔ C₂.lt (rightOpens U) _ _)
    rw [rightOpens_image_inr hU]; exact ⟨Iff.rfl, Iff.rfl⟩⟩

/-- The BTZ locus of `Y`: the axis of the `𝔼₀` summand. -/
def singY0 : Set ModelY := Sum.inr '' axis

/-- **The `LocalModel` field `coneSliceFuture` for `Y = 𝕄 ⊕ 𝔼₀`** (statement verbatim, with
`singY 0 = singY0`): Minkowski's cone slices on `𝕄` and, off the axis, on `𝔼₀` through the sector
charts. -/
theorem coneSliceFuture_Y : ∀ y : ModelY, y ∉ singY0 → ∀ O : Opens ModelY, y ∈ O →
    ∃ K : Set ModelY, K ⊆ O ∧ (∀ z ∈ K, z ∉ singY0 ∧ z ≠ y ∧ causalityY.le O z y) ∧
      ∀ V : Set ModelY, IsOpen V → K ⊆ V → ∃ (N : Opens ModelY) (Γ : Set ModelY), y ∈ N ∧
        N ≤ O ∧ Γ ⊆ N ∧ Γ ⊆ V ∧ causalityY.IsCauchySurfaceOn N Γ := by
  intro y hy
  have key : SliceAt causalityY y fun O z => z ∉ singY0 ∧ causalityY.le O z y := by
    rcases y with m | w
    · refine SliceAt.pushforward (QM := fun O z => (Causal.minkowski 2).le O z m)
        isEMorphismOn_inl Sum.inl_injective ?_ (minkowski_sliceAt_future m)
      intro O hO z hq
      exact ⟨fun ⟨_, _, h⟩ => Sum.inr_ne_inl h, hq⟩
    · have hw : w ∉ axis := fun h => hy ⟨w, h, rfl⟩
      refine SliceAt.pushforward isEMorphismOn_inr Sum.inr_injective ?_
        (sliceAt_future_of_not_mem_axis hw)
      intro O hO z ⟨hz, hq⟩
      exact ⟨fun ⟨_, h, he⟩ => hz (Sum.inr_injective he ▸ h), hq⟩
  intro O hyO
  obtain ⟨K, hK, hKp, hV⟩ := key O hyO
  exact ⟨K, hK, fun z hz => ⟨(hKp z hz).2.1, (hKp z hz).1, (hKp z hz).2.2⟩, hV⟩

/-- **The `LocalModel` field `coneSlicePast` for `Y`, reduced to the BTZ points**: given the cone
slices of `𝔼₀` at its axis, the field holds at every point (Minkowski's on `𝕄`, the sector charts
off the axis). -/
theorem coneSlicePast_Y_of_axis
    (hax : ∀ w ∈ axis, SliceAt causality w fun O z => causality.le O w z) :
    ∀ y : ModelY, ∀ O : Opens ModelY, y ∈ O → ∃ K : Set ModelY, K ⊆ O ∧
      (∀ z ∈ K, z ≠ y ∧ causalityY.le O y z) ∧
      ∀ V : Set ModelY, IsOpen V → K ⊆ V → ∃ (N : Opens ModelY) (Γ : Set ModelY), y ∈ N ∧
        N ≤ O ∧ Γ ⊆ N ∧ Γ ⊆ V ∧ causalityY.IsCauchySurfaceOn N Γ := by
  intro y
  have key : SliceAt causalityY y fun O z => causalityY.le O y z := by
    rcases y with m | w
    · exact SliceAt.pushforward (QM := fun O z => (Causal.minkowski 2).le O m z)
        isEMorphismOn_inl Sum.inl_injective (fun _ _ _ hq => hq) (minkowski_sliceAt_past m)
    · refine SliceAt.pushforward (QM := fun O z => causality.le O w z) isEMorphismOn_inr
        Sum.inr_injective (fun _ _ _ hq => hq) ?_
      by_cases hw : w ∈ axis
      · exact hax w hw
      · exact sliceAt_past_of_not_mem_axis hw
  exact key

end YSlices

/-! ### `h = τ + r` is a time function; curves extend; the sector charts as charts -/

section TimeChart

open TopologicalSpace

/-- **`h = τ + r` is strictly increasing along `≤`**: a continuous time function of `𝔼₀`. -/
theorem hcoord_lt_of_le (h : causality.le ⊤ x y) (hne : x ≠ y) : hcoord x < hcoord y := by
  obtain ⟨θ₁, θ₂, hx, hy, hc⟩ := le_iff_closed.1 (le_top_iff.1 h)
  obtain ⟨hτ, hr, hq⟩ := hc
  rcases (show hcoord x ≤ hcoord y by simp only [hcoord]; linarith).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    simp only [hcoord] at h'
    have hτ' : x.1 = y.1 := by linarith
    have hr' : rad x = rad y := by linarith
    rw [hr', sub_self, zero_mul] at hq
    apply hne
    rcases (rad_nonneg y).lt_or_eq with hpos | hzero
    · have hθ : θ₂ - θ₁ = 0 := by
        have : rad y * rad y * (θ₂ - θ₁) ^ 2 = 0 :=
          le_antisymm hq (by positivity)
        have hyy : rad y * rad y ≠ 0 := by positivity
        exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this).resolve_left hyy)
      have : θ₂ = θ₁ := by linarith
      refine Prod.ext hτ' ?_
      rw [hx, hy, hr', this]
    · exact Prod.ext hτ' ((rad_eq_zero.1 (hr' ▸ hzero.symm)).trans
        (rad_eq_zero.1 hzero.symm).symm)

/-- **Causal curves of `𝔼₀` extend to inextensible ones** (`Causal.Causality.CurvesExtend`), by the
time function `h`. -/
theorem curvesExtend : causality.CurvesExtend :=
  Causal.Causality.curvesExtend_of_timeFunction continuous_hcoord fun _ _ h hne =>
    hcoord_lt_of_le h hne

/-- **`𝔼₀` is causal**: `≤` is antisymmetric. -/
theorem isCausal : causality.IsCausal := fun x y h₁ h₂ => by
  by_contra hne
  exact absurd (hcoord_lt_of_le h₁ hne) (not_lt.2 (hcoord_lt_of_le h₂ (Ne.symm hne)).le)

variable {y : E0}

/-- **The sector chart** as an open partial homeomorphism `sector y → 𝐌³`. -/
noncomputable def sectorChart (y : E0) (hy : y.2 ≠ 0) :
    OpenPartialHomeomorph E0 (Causal.Minkowski 2) where
  toFun := chartMap y
  invFun m := unlift (nullToMink.symm m)
  source := sector y
  target := chartMap y '' sector y
  map_source' _ hw := mem_image_of_mem _ hw
  map_target' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [unlift_symm_chartMap hy]; exact hw
  left_inv' w _ := unlift_symm_chartMap hy w
  right_inv' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [unlift_symm_chartMap hy]
  open_source := isOpen_sector y
  open_target := isOpen_image_chartMap hy subset_rfl (isOpen_sector y)
  continuousOn_toFun := continuousOn_chartMap y
  continuousOn_invFun := by
    rintro _ ⟨w, hw, rfl⟩
    have hB : (nullToMink.symm (chartMap y w)).2.1 ≠ 0 := by
      rw [chartMap, LinearEquiv.symm_apply_apply]
      exact (norm_pos_iff.2 (ne_zero_of_mem_sector hw)).ne'
    exact ((continuousAt_unlift hB).comp
      nullToMinkHomeomorph.symm.continuous.continuousAt).continuousWithinAt

/-- **Off the axis the sector chart is a chart isomorphism** (`Causal.ChartIso`, the `LocalModel`
field `chartIso_mem`'s content on the regular part of `𝔼₀`): for every open `U` of its source,
`≤_U` and `≪_U` are Minkowski's `≤` and `≪` on the image. -/
theorem chartIso_sectorChart (hy : y.2 ≠ 0) :
    Causal.ChartIso causality (Causal.minkowski 2) (sectorChart y hy) := by
  intro U hU p hp q hq
  have hsub : (U : Set E0) ⊆ sector y := hU
  have himg : ((Causal.chartImage (sectorChart y hy) U : Opens _) : Set (Causal.Minkowski 2)) =
      chartMap y '' U := by
    rw [Causal.coe_chartImage]
    congr 1
    exact inter_eq_right.2 hsub
  exact chartIso_sector hy hsub himg hp hq

end TimeChart

/-! ### The metric control of `≼`; closed causal cones; strong causality -/

section Closed

open TopologicalSpace

/-- `‖e^{iθ₂} − e^{iθ₁}‖ ≤ |θ₂ − θ₁|`. -/
theorem norm_cexp_sub_cexp_le (θ₁ θ₂ : ℝ) :
    ‖cexp (θ₂ * I) - cexp (θ₁ * I)‖ ≤ |θ₂ - θ₁| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ₂ - θ₁)
  have e : cexp (θ₂ * I) - cexp (θ₁ * I) = cexp (θ₁ * I) * (cexp (I * ↑(θ₂ - θ₁)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [Real.norm_eq_abs] using h

/-- **Along `≼` the displacement is controlled by the elapsed time**: `‖z_y − z_x‖ ≤ 3(τ_y − τ_x)`
(`r₁|δ| ≤ Δτ` from the closed form, and `Δr ≤ 2Δτ`). -/
theorem Le.norm_sub_le (h : Le x y) : ‖y.2 - x.2‖ ≤ 3 * (y.1 - x.1) := by
  obtain ⟨θ₁, θ₂, hx, hy, hτ, hr, hq⟩ := le_iff_closed.1 h
  have h1 := rad_nonneg x
  have h2 := rad_nonneg y
  have hτ' : 0 ≤ y.1 - x.1 := sub_nonneg.2 hτ
  have hsq : (rad x * |θ₂ - θ₁|) ^ 2 ≤ (y.1 - x.1) ^ 2 := by
    have : (rad x * |θ₂ - θ₁|) ^ 2 ≤ rad x * rad y * (θ₂ - θ₁) ^ 2 := by
      rw [mul_pow, sq_abs]
      have : rad x ^ 2 ≤ rad x * rad y := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    nlinarith [sq_nonneg ((y.1 - x.1) - (rad y - rad x))]
  have hδ : rad x * |θ₂ - θ₁| ≤ y.1 - x.1 :=
    (sq_le_sq₀ (mul_nonneg h1 (abs_nonneg _)) hτ').1 hsq
  have hd : rad y - rad x ≤ 2 * (y.1 - x.1) := (calculus_le (U := ⊤) (le_top_iff.2 h)).2.1
  have hnorm : ‖y.2 - x.2‖ ≤ (rad y - rad x) + rad x * |θ₂ - θ₁| := by
    have e : y.2 - x.2 = ((rad y - rad x : ℝ) : ℂ) * cexp (θ₂ * I) +
        (rad x : ℂ) * (cexp (θ₂ * I) - cexp (θ₁ * I)) := by
      conv_lhs => rw [hx, hy]
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 hr)]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
      exact mul_le_mul_of_nonneg_left (norm_cexp_sub_cexp_le θ₁ θ₂) h1
  linarith

/-- **`dist x y ≤ 3(τ_y − τ_x)` along `≼`.** -/
theorem Le.dist_le (h : Le x y) : dist x y ≤ 3 * (y.1 - x.1) := by
  have hτ := h.closed.1
  rw [Prod.dist_eq, Real.dist_eq, dist_comm, dist_eq_norm]
  exact max_le (by rw [abs_le]; constructor <;> linarith) h.norm_sub_le

theorem abs_fst_sub_le_dist (x y : E0) : |x.1 - y.1| ≤ dist x y := by
  rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _

/-- The distance to a point of the axis. -/
theorem dist_axis {w : E0} (hw : w ∈ axis) (z : E0) : dist z w = max |z.1 - w.1| (rad z) := by
  have hw0 : w.2 = 0 := hw
  rw [Prod.dist_eq, Real.dist_eq, hw0, dist_zero_right]; rfl

/-- **The winding can be read within `π` of the principal angle of the source.** -/
theorem le_iff_bounded : Le x y ↔ ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ ∧
    NullCone (lift y θ - lift x (arg x.2)) := by
  constructor
  · intro h
    obtain ⟨θ, hθ, hpol⟩ : ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ := by
      by_cases hx : x.2 = 0
      · refine ⟨arg y.2, ?_, polar_arg y⟩
        rw [hx, Complex.arg_zero]
        exact ⟨by linarith [Complex.neg_pi_lt_arg y.2], by linarith [Complex.arg_le_pi y.2]⟩
      · exact ⟨arg x.2 + arg (y.2 / x.2), ⟨by linarith [Complex.neg_pi_lt_arg (y.2 / x.2)],
          by linarith [Complex.arg_le_pi (y.2 / x.2)]⟩, polar_add_arg_div x y hx⟩
    refine ⟨θ, hθ, hpol, h.of_polar (polar_arg x) hpol ?_⟩
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  · rintro ⟨θ, -, hpol, h⟩
    exact ⟨_, _, polar_arg x, hpol, h⟩

/-- The same, with `x` the target. -/
theorem le_iff_bounded' : Le y x ↔ ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ ∧
    NullCone (lift x (arg x.2) - lift y θ) := by
  constructor
  · intro h
    obtain ⟨θ, hθ, hpol⟩ : ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ := by
      by_cases hx : x.2 = 0
      · refine ⟨arg y.2, ?_, polar_arg y⟩
        rw [hx, Complex.arg_zero]
        exact ⟨by linarith [Complex.neg_pi_lt_arg y.2], by linarith [Complex.arg_le_pi y.2]⟩
      · exact ⟨arg x.2 + arg (y.2 / x.2), ⟨by linarith [Complex.neg_pi_lt_arg (y.2 / x.2)],
          by linarith [Complex.arg_le_pi (y.2 / x.2)]⟩, polar_add_arg_div x y hx⟩
    refine ⟨θ, hθ, hpol, h.of_polar hpol (polar_arg x) ?_⟩
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  · rintro ⟨θ, -, hpol, h⟩
    exact ⟨_, _, hpol, polar_arg x, h⟩

theorem isClosed_nullCone : IsClosed {V : ℝ × ℝ × ℝ | NullCone V} :=
  (isClosed_le continuous_const continuous_fst).inter ((isClosed_le continuous_const
    continuous_snd.fst).inter (isClosed_le (continuous_snd.snd.pow 2)
      (continuous_fst.mul continuous_snd.fst)))

theorem continuous_lift : Continuous fun p : E0 × ℝ => lift p.1 p.2 :=
  continuous_btzPaperNull.comp ((continuous_fst.comp continuous_fst).prodMk
    ((continuous_rad.comp continuous_fst).prodMk continuous_snd))

theorem isClosed_polar : IsClosed {p : E0 × ℝ | Polar p.1 p.2} := by
  refine isClosed_eq (continuous_snd.comp continuous_fst) ?_
  exact (Complex.continuous_ofReal.comp (continuous_rad.comp continuous_fst)).mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      continuous_const))

/-- A set of the shape `{y | ∃ θ ∈ [α, β], Polar y θ ∧ NullCone (g (y, θ))}` is closed. -/
theorem isClosed_exists_polar_nullCone {g : E0 × ℝ → ℝ × ℝ × ℝ} (hg : Continuous g) (α β : ℝ) :
    IsClosed {y : E0 | ∃ θ ∈ Icc α β, Polar y θ ∧ NullCone (g (y, θ))} := by
  haveI : CompactSpace (Icc α β) := isCompact_iff_compactSpace.1 isCompact_Icc
  set F : E0 × Icc α β → E0 × ℝ := fun p => (p.1, (p.2 : ℝ))
  have hF : Continuous F := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hS : IsClosed (F ⁻¹' ({p : E0 × ℝ | Polar p.1 p.2} ∩ g ⁻¹' {V | NullCone V})) :=
    (isClosed_polar.inter (isClosed_nullCone.preimage hg)).preimage hF
  convert isClosedMap_fst_of_compactSpace _ hS using 1
  ext y
  constructor
  · rintro ⟨θ, hθ, hp, hn⟩
    exact ⟨(y, ⟨θ, hθ⟩), ⟨hp, hn⟩, rfl⟩
  · rintro ⟨⟨y', θ⟩, ⟨hp, hn⟩, rfl⟩
    exact ⟨θ, θ.2, hp, hn⟩

/-- **`J⁺(x)` is closed.** -/
theorem isClosed_Jplus (x : E0) : IsClosed (causality.Jplus ⊤ {x}) := by
  have : causality.Jplus ⊤ {x} = {y : E0 | ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ ∧
      NullCone ((fun p : E0 × ℝ => lift p.1 p.2 - lift x (arg x.2)) (y, θ))} := by
    ext y; rw [Causal.Precausality.mem_Jplus_singleton, le_top_iff, le_iff_bounded]; rfl
  rw [this]
  exact isClosed_exists_polar_nullCone (continuous_lift.sub continuous_const) _ _

/-- **`J⁻(x)` is closed.** -/
theorem isClosed_Jminus (x : E0) : IsClosed (causality.Jminus ⊤ {x}) := by
  have : causality.Jminus ⊤ {x} = {y : E0 | ∃ θ ∈ Icc (arg x.2 - π) (arg x.2 + π), Polar y θ ∧
      NullCone ((fun p : E0 × ℝ => lift x (arg x.2) - lift p.1 p.2) (y, θ))} := by
    ext y; rw [Causal.Precausality.mem_Jminus_singleton, le_top_iff, le_iff_bounded']; rfl
  rw [this]
  exact isClosed_exists_polar_nullCone (continuous_const.sub continuous_lift) _ _

/-- **`𝔼₀` is strongly causal** (`def:strongly_causal_spacetime`): `J⁺(B) ∩ J⁻(B)` for a small ball
`B` is causally convex and lies in the ball of `7` times the radius (`Le.dist_le`). -/
theorem stronglyCausal : causality.StronglyCausal := by
  intro p U hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  set B := Metric.ball p (δ / 10)
  have hBo : IsOpen B := Metric.isOpen_ball
  refine ⟨causality.Jplus ⊤ B ∩ causality.Jminus ⊤ B, ?_, ?_, ?_⟩
  · exact Filter.mem_of_superset (hBo.mem_nhds (Metric.mem_ball_self (by positivity)))
      fun z hz => ⟨⟨z, hz, causality.le_refl trivial⟩, ⟨z, hz, causality.le_refl trivial⟩⟩
  · rintro z ⟨⟨u, hu, huz⟩, ⟨v, hv, hzv⟩⟩
    apply hball
    have h1 := (le_top_iff.1 huz).dist_le
    have h2 := (le_top_iff.1 hzv).closed.1
    have hu' : dist u p < δ / 10 := hu
    have hv' : dist v p < δ / 10 := hv
    have hτu := abs_lt.1 ((abs_fst_sub_le_dist u p).trans_lt hu')
    have hτv := abs_lt.1 ((abs_fst_sub_le_dist v p).trans_lt hv')
    rw [Metric.mem_ball]
    calc dist z p ≤ dist z u + dist u p := dist_triangle _ _ _
      _ = dist u z + dist u p := by rw [dist_comm z u]
      _ < δ := by linarith [hτu.1, hτu.2, hτv.1, hτv.2]
  · refine ⟨fun _ _ => trivial, fun a ha b hb w hw => ?_⟩
    obtain ⟨⟨u, hu, hua⟩, -⟩ := ha
    obtain ⟨-, ⟨v, hv, hbv⟩⟩ := hb
    have hwb : causality.le ⊤ w b := Causal.Precausality.mem_Jminus_singleton.1 hw.1
    have haw : causality.le ⊤ a w := Causal.Precausality.mem_Jplus_singleton.1 hw.2
    exact ⟨⟨u, hu, causality.le_trans hua haw⟩, ⟨v, hv, causality.le_trans hwb hbv⟩⟩

end Closed

/-! ### Limits of causal curves; non-trivial local cones -/

section Limits

open TopologicalSpace

/-- **A causal curve of `𝔼₀` whose time is bounded above converges at its upper end**
(`𝔼₀ = ℝ × ℂ` is complete, and `dist ≤ 3Δτ` along `≼`, `Le.dist_le`). -/
theorem exists_tendsto_of_bddAbove {J : Set ℝ} {γ : ℝ → E0} {β : ℝ}
    (hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → Le (γ u) (γ u'))
    (hJ : J.Nonempty) (hJc : J.OrdConnected) (hβ : IsLUB J β) (hβJ : β ∉ J)
    (hbdd : BddAbove ((fun u => (γ u).1) '' J)) : ∃ p, Tendsto γ (𝓝[<] β) (𝓝 p) := by
  have hlt : ∀ u ∈ J, u < β := fun u hu =>
    lt_of_le_of_ne (hβ.1 hu) fun he => hβJ (he ▸ hu)
  set τ := sSup ((fun u => (γ u).1) '' J)
  have hcauchy : Cauchy (map γ (𝓝[<] β)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hτ⟩ :=
      exists_lt_of_lt_csSup (hJ.image _) (sub_lt_self τ (by positivity : 0 < ε / 3))
    have hsub := Causal.Flat.Ioo_subset_of_isLUB hJc hβ hu₁
    refine ⟨γ '' Ioo u₁ β, mem_map.2 (mem_of_superset (Ioo_mem_nhdsLT (hlt u₁ hu₁))
      (subset_preimage_image _ _)), ?_⟩
    have key : ∀ u ∈ Ioo u₁ β, ∀ u' ∈ Ioo u₁ β, u ≤ u' → dist (γ u) (γ u') < ε :=
      fun u hu u' hu' huu' => by
        have h1 := (hle u (hsub hu) u' (hsub hu') huu').dist_le
        have h2 := (hle u₁ hu₁ u (hsub hu) hu.1.le).closed.1
        have h3 : (γ u').1 ≤ τ := le_csSup hbdd ⟨u', hsub hu', rfl⟩
        linarith
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rcases le_total u u' with huu' | huu'
    · exact key u hu u' hu' huu'
    · rw [dist_comm]; exact key u' hu' u hu huu'
  obtain ⟨p, hp⟩ := CompleteSpace.complete hcauchy
  exact ⟨p, hp⟩

/-- **A causal curve of `𝔼₀` whose time is bounded below converges at its lower end.** -/
theorem exists_tendsto_of_bddBelow {J : Set ℝ} {γ : ℝ → E0} {α : ℝ}
    (hle : ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → Le (γ u) (γ u'))
    (hJ : J.Nonempty) (hJc : J.OrdConnected) (hα : IsGLB J α) (hαJ : α ∉ J)
    (hbdd : BddBelow ((fun u => (γ u).1) '' J)) : ∃ p, Tendsto γ (𝓝[>] α) (𝓝 p) := by
  have hgt : ∀ u ∈ J, α < u := fun u hu =>
    lt_of_le_of_ne (hα.1 hu) fun he => hαJ (he ▸ hu)
  set σ := sInf ((fun u => (γ u).1) '' J)
  have hcauchy : Cauchy (map γ (𝓝[>] α)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hσ⟩ :=
      exists_lt_of_csInf_lt (hJ.image _) (lt_add_of_pos_right σ (by positivity : 0 < ε / 3))
    have hsub := Causal.Flat.Ioo_subset_of_isGLB hJc hα hu₁
    refine ⟨γ '' Ioo α u₁, mem_map.2 (mem_of_superset (Ioo_mem_nhdsGT (hgt u₁ hu₁))
      (subset_preimage_image _ _)), ?_⟩
    have key : ∀ u ∈ Ioo α u₁, ∀ u' ∈ Ioo α u₁, u ≤ u' → dist (γ u) (γ u') < ε :=
      fun u hu u' hu' huu' => by
        have h1 := (hle u (hsub hu) u' (hsub hu') huu').dist_le
        have h2 := (hle u' (hsub hu') u₁ hu₁ hu'.2.le).closed.1
        have h3 : σ ≤ (γ u).1 := csInf_le hbdd ⟨u, hsub hu, rfl⟩
        linarith
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rcases le_total u u' with huu' | huu'
    · exact key u hu u' hu' huu'
    · rw [dist_comm]; exact key u' hu' u hu huu'
  obtain ⟨p, hp⟩ := CompleteSpace.complete hcauchy
  exact ⟨p, hp⟩

/-- A short initial piece of a straight causal segment stays in an open set containing its start. -/
theorem exists_seg_mem_start (hP : Adm P) (hPQ : NullCone (Q - P)) {W : Opens E0}
    (hW : unlift P ∈ W) : ∃ s₀ ∈ Ioc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) s₀, unlift (seg P Q s) ∈ W := by
  have hcont := continuousOn_unlift_seg hP hPQ
  have hpre : (fun s => unlift (seg P Q s)) ⁻¹' W ∈ 𝓝[Icc 0 1] 0 :=
    hcont 0 ⟨le_rfl, zero_le_one⟩ (by beta_reduce; rw [seg_zero]; exact W.isOpen.mem_nhds hW)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨min (ε / 2) 1, ⟨lt_min (by linarith) one_pos, min_le_right _ _⟩, fun s hs => ?_⟩
  refine hball ⟨?_, hs.1, hs.2.trans (min_le_right _ _)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
  exact hs.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))

/-- A short final piece of a straight causal segment stays in an open set containing its end. -/
theorem exists_seg_mem_end (hP : Adm P) (hPQ : NullCone (Q - P)) {W : Opens E0}
    (hW : unlift Q ∈ W) : ∃ s₀ ∈ Ico (0 : ℝ) 1, ∀ s ∈ Icc s₀ 1, unlift (seg P Q s) ∈ W := by
  have hcont := continuousOn_unlift_seg hP hPQ
  have hpre : (fun s => unlift (seg P Q s)) ⁻¹' W ∈ 𝓝[Icc 0 1] 1 :=
    hcont 1 ⟨zero_le_one, le_rfl⟩ (by beta_reduce; rw [seg_one]; exact W.isOpen.mem_nhds hW)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨max (1 - ε / 2) 0, ⟨le_max_right _ _, max_lt (by linarith) one_pos⟩, fun s hs => ?_⟩
  refine hball ⟨?_, (le_max_right _ _).trans hs.1, hs.2⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  have := (le_max_left (1 - ε / 2) 0).trans hs.1
  constructor <;> linarith [hs.2]

/-- The piece `[s, s']` of a straight causal segment is a causal curve of every open set holding
it. -/
theorem cle_of_seg_piece (hP : Adm P) (hPQ : NullCone (Q - P)) {W : Opens E0} {s s' : ℝ}
    (hs : 0 ≤ s) (hss' : s ≤ s') (hs' : s' ≤ 1)
    (hW : ∀ σ ∈ Icc s s', unlift (seg P Q σ) ∈ W) :
    CLe W (unlift (seg P Q s)) (unlift (seg P Q s')) :=
  ⟨s, s', hss', _, curveOn_of_continuousOn ((continuousOn_unlift_seg hP hPQ).mono
    (Icc_subset_Icc hs hs')) hW fun _ hσ _ _ h => le_unlift_seg hP hPQ (hs.trans hσ.1) h.le,
    rfl, rfl⟩

theorem Lt.ne (h : Lt x y) : x ≠ y := fun he => by
  have := h.closed.1; rw [he] at this; exact lt_irrefl _ this

variable {p : E0}

/-- **Every point has a causal future point in each open set containing it.** -/
theorem exists_le_ne (W : Opens E0) (hp : p ∈ W) : ∃ q, causality.le W p q ∧ q ≠ p := by
  set P := lift p (arg p.2)
  set Q := P + timelikeT 1
  have hPQ : NullConeLt (Q - P) := by
    rw [show Q - P = timelikeT 1 by simp [Q]]; exact nullConeLt_timelikeT one_pos
  have hP : Adm P := adm_lift p _
  have hPp : unlift P = p := unlift_lift (polar_arg p)
  obtain ⟨s₀, hs₀, hmem⟩ := exists_seg_mem_start hP hPQ.nullCone (W := W) (by rw [hPp]; exact hp)
  refine ⟨unlift (seg P Q s₀), ?_, ?_⟩
  · have := cle_of_seg_piece hP hPQ.nullCone le_rfl hs₀.1.le hs₀.2 (W := W)
      fun σ hσ => hmem σ ⟨hσ.1, hσ.2⟩
    rwa [seg_zero, hPp] at this
  · have := lt_unlift_seg hP hPQ le_rfl hs₀.1
    rw [seg_zero, hPp] at this
    exact this.ne.symm

/-- **Every point has a causal past point in each open set containing it** (off the axis by a
timelike segment, on the axis along the line). -/
theorem exists_ge_ne (W : Opens E0) (hp : p ∈ W) : ∃ q, causality.le W q p ∧ q ≠ p := by
  by_cases hax : p ∈ axis
  · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 W.isOpen p hp
    have hp0 : p.2 = 0 := hax
    have hmem : ∀ t ∈ Icc (-(δ / 2)) 0, axisLine p t ∈ W := fun t ht => hball (by
      rw [Metric.mem_ball, dist_axis hax, max_lt_iff]
      refine ⟨?_, ?_⟩
      · simp only [axisLine]; rw [add_sub_cancel_left, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      · rw [rad_eq_zero.2 (axisLine_mem p t)]; exact hδ)
    rcases curveOn_axisLine p W (-(δ / 2)) 0 with hc | hc
    · refine ⟨axisLine p (-(δ / 2)), ⟨-(δ / 2), 0, by linarith, _, hc, rfl, ?_⟩, ?_⟩
      · exact Prod.ext (add_zero _) (show (0 : ℂ) = p.2 from hp0.symm)
      · intro h
        have := congrArg Prod.fst h
        simp only [axisLine] at this
        linarith
    · exact absurd hmem hc
  · have hr := rad_pos.2 hax
    set Q := lift p (arg p.2)
    set P := Q - timelikeT (rad p / 2)
    have hPQ : NullConeLt (Q - P) := by
      rw [show Q - P = timelikeT (rad p / 2) by simp [P]]
      exact nullConeLt_timelikeT (by linarith)
    have hP : Adm P := by
      left
      have : P.2.1 = rad p - rad p / 2 := rfl
      rw [this]; linarith
    have hQp : unlift Q = p := unlift_lift (polar_arg p)
    obtain ⟨s₀, hs₀, hmem⟩ := exists_seg_mem_end hP hPQ.nullCone (W := W) (by rw [hQp]; exact hp)
    refine ⟨unlift (seg P Q s₀), ?_, ?_⟩
    · have := cle_of_seg_piece hP hPQ.nullCone hs₀.1 hs₀.2.le le_rfl (W := W)
        fun σ hσ => hmem σ hσ
      rwa [seg_one, hQp] at this
    · have := lt_unlift_seg hP hPQ hs₀.1 hs₀.2
      rw [seg_one, hQp] at this
      exact this.ne

theorem Jplus_ne_singleton {W : Opens E0} (hp : p ∈ W) : causality.Jplus W {p} ≠ {p} := by
  obtain ⟨q, hq, hne⟩ := exists_le_ne W hp
  intro h
  have : q ∈ causality.Jplus W {p} := Causal.Precausality.mem_Jplus_singleton.2 hq
  rw [h] at this; exact hne this

theorem Jminus_ne_singleton {W : Opens E0} (hp : p ∈ W) : causality.Jminus W {p} ≠ {p} := by
  obtain ⟨q, hq, hne⟩ := exists_ge_ne W hp
  intro h
  have : q ∈ causality.Jminus W {p} := Causal.Precausality.mem_Jminus_singleton.2 hq
  rw [h] at this; exact hne this

end Limits

/-! ### The cone slice at a BTZ point (`LocalModel.coneSlicePast` on the axis) -/

section AxisSlice

open TopologicalSpace

theorem fcoord_eq_hcoord (z : E0) : fcoord z = hcoord z - 3 / 2 * rad z := by
  simp only [fcoord, hcoord]; ring

theorem isOpen_sliceDom (a b c : ℝ) :
    IsOpen {z : E0 | a < fcoord z ∧ hcoord z < b ∧ rad z < 2 * (c - a) / 3} := by
  simp only [setOf_and]
  exact (isOpen_lt continuous_const continuous_fcoord).inter
    ((isOpen_lt continuous_hcoord continuous_const).inter (isOpen_lt continuous_rad continuous_const))

/-- **The development domain of the level `{h = c}` near a BTZ point**:
`N = {f > a, h < b, r < 2(c − a)/3}`. Its three walls are placed so that no inextensible causal
curve of `N` can leave it without crossing `{h = c}`: below the level the wall `r = 2(c−a)/3` is
out of reach (there `r = 2(h − f)/3 < 2(c − a)/3`), above it the wall `f = a` is (there
`f = h − 3r/2 > c − (c − a)`); the wall `h = b` is above the level. -/
def sliceDom (a b c : ℝ) : Opens E0 :=
  ⟨{z | a < fcoord z ∧ hcoord z < b ∧ rad z < 2 * (c - a) / 3}, isOpen_sliceDom a b c⟩

theorem mem_sliceDom {a b c : ℝ} {z : E0} :
    z ∈ sliceDom a b c ↔ a < fcoord z ∧ hcoord z < b ∧ rad z < 2 * (c - a) / 3 := Iff.rfl

theorem le_of_le_top_curve {W : Opens E0} {J : Set ℝ} {γ : ℝ → E0}
    (hγ : causality.CausalCurveIn W J γ) :
    ∀ u ∈ J, ∀ u' ∈ J, u ≤ u' → causality.le ⊤ (γ u) (γ u') :=
  fun _ hu _ hu' huu' => causality.le_mono le_top (hγ.le_of_le hu hu' huu')

/-- **Past end**: a causal curve of `N` above the level `{h = c}`, over a parameter interval
bounded below, is extensible in `N` at its past end (its limit there is in `N`). -/
theorem pastExtensible_sliceDom {a b c : ℝ} {J : Set ℝ} {γ : ℝ → E0}
    (hγ : causality.CausalCurveIn (sliceDom a b c) J γ) (hJ : BddBelow J)
    (hT : ∀ u ∈ J, c < hcoord (γ u)) : causality.PastExtensible (sliceDom a b c) J γ := by
  by_cases hmin : ∃ a', IsLeast J a'
  · obtain ⟨a', ha⟩ := hmin
    exact Causal.Causality.pastExtensible_of_isLeast causallyArcConnected isCausal hγ ha
      (Jminus_ne_singleton (hγ.mem ha.1))
  have hglb : IsGLB J (sInf J) := isGLB_csInf hγ.nonempty hJ
  have hαJ : sInf J ∉ J := fun hα => hmin ⟨_, hα, hglb.1⟩
  have hgt : ∀ u ∈ J, sInf J < u := fun u hu =>
    lt_of_le_of_ne (hglb.1 hu) fun he => hαJ (he ▸ hu)
  have hle := le_of_le_top_curve hγ
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  have hbdd : BddBelow ((fun u => (γ u).1) '' J) := by
    refine ⟨a, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h1 := (hγ.mem hu).1
    have h2 := rad_nonneg (γ u)
    simp only [fcoord] at h1
    linarith
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddBelow (fun u hu u' hu' h => le_top_iff.1 (hle u hu u' hu' h))
    hγ.nonempty hγ.ordConnected hglb hαJ hbdd
  have hsub := Causal.Flat.Ioo_subset_of_isGLB hγ.ordConnected hglb hu₀
  have hev : ∀ᶠ u in 𝓝[>] (sInf J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsGT (hgt u₀ hu₀)) hsub
  have hpz : causality.le ⊤ p (γ u₀) := by
    refine Causal.Precausality.mem_Jminus_singleton.1 ((isClosed_Jminus (γ u₀)).mem_of_tendsto hp ?_)
    filter_upwards [Ioo_mem_nhdsGT (hgt u₀ hu₀)] with u hu
    exact Causal.Precausality.mem_Jminus_singleton.2 (hle u (hsub hu) u₀ hu₀ hu.2.le)
  have hhp : c ≤ hcoord p := (isClosed_le continuous_const continuous_hcoord).mem_of_tendsto hp
    (hev.mono fun u hu => (hT u hu).le)
  have hcal := calculus_le hpz
  obtain ⟨-, hz2, hz3⟩ := hγ.mem hu₀
  have hpN : p ∈ sliceDom a b c := by
    refine ⟨?_, by linarith [hcal.2.2.2.2.2], by linarith [hcal.2.2.2.1]⟩
    rw [fcoord_eq_hcoord]; linarith [hcal.2.2.2.1]
  exact Causal.Causality.pastExtensible_of_tendsto_opens isClosed_Jminus stronglyCausal
    causallyArcConnected isCausal hγ hpN hgt
    (Causal.Flat.ordConnected_insert_of_isGLB hγ.ordConnected hglb) hp (Jminus_ne_singleton hpN)

/-- **Future end**: a causal curve of `N` below the level `{h = c}` (`c < b`), over a parameter
interval bounded above, is extensible in `N` at its future end. -/
theorem futureExtensible_sliceDom {a b c : ℝ} (hcb : c < b) {J : Set ℝ} {γ : ℝ → E0}
    (hγ : causality.CausalCurveIn (sliceDom a b c) J γ) (hJ : BddAbove J)
    (hT : ∀ u ∈ J, hcoord (γ u) < c) : causality.FutureExtensible (sliceDom a b c) J γ := by
  by_cases hmax : ∃ b', IsGreatest J b'
  · obtain ⟨b', hb⟩ := hmax
    exact Causal.Causality.futureExtensible_of_isGreatest causallyArcConnected isCausal hγ hb
      (Jplus_ne_singleton (hγ.mem hb.1))
  have hlub : IsLUB J (sSup J) := isLUB_csSup hγ.nonempty hJ
  have hβJ : sSup J ∉ J := fun hβ => hmax ⟨_, hβ, hlub.1⟩
  have hlt : ∀ u ∈ J, u < sSup J := fun u hu =>
    lt_of_le_of_ne (hlub.1 hu) fun he => hβJ (he ▸ hu)
  have hle := le_of_le_top_curve hγ
  obtain ⟨u₀, hu₀⟩ := hγ.nonempty
  have hbdd : BddAbove ((fun u => (γ u).1) '' J) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h1 := hT u hu
    have h2 := rad_nonneg (γ u)
    simp only [hcoord] at h1
    simp only
    linarith
  obtain ⟨p, hp⟩ := exists_tendsto_of_bddAbove (fun u hu u' hu' h => le_top_iff.1 (hle u hu u' hu' h))
    hγ.nonempty hγ.ordConnected hlub hβJ hbdd
  have hsub := Causal.Flat.Ioo_subset_of_isLUB hγ.ordConnected hlub hu₀
  have hev : ∀ᶠ u in 𝓝[<] (sSup J), u ∈ J :=
    mem_of_superset (Ioo_mem_nhdsLT (hlt u₀ hu₀)) hsub
  have hzp : causality.le ⊤ (γ u₀) p := by
    refine Causal.Precausality.mem_Jplus_singleton.1 ((isClosed_Jplus (γ u₀)).mem_of_tendsto hp ?_)
    filter_upwards [Ioo_mem_nhdsLT (hlt u₀ hu₀)] with u hu
    exact Causal.Precausality.mem_Jplus_singleton.2 (hle u₀ hu₀ u (hsub hu) hu.1.le)
  have hhp : hcoord p ≤ c := (isClosed_le continuous_hcoord continuous_const).mem_of_tendsto hp
    (hev.mono fun u hu => (hT u hu).le)
  have hcal := calculus_le hzp
  obtain ⟨hz1, -, -⟩ := hγ.mem hu₀
  have hfp : a < fcoord p := by linarith [hcal.2.2.2.2.1]
  have hpN : p ∈ sliceDom a b c := by
    refine ⟨hfp, by linarith, ?_⟩
    have := fcoord_eq_hcoord p
    linarith
  exact Causal.Causality.futureExtensible_of_tendsto_opens isClosed_Jplus stronglyCausal
    causallyArcConnected isCausal hγ hpN hlt
    (Causal.Flat.ordConnected_insert_of_isLUB hγ.ordConnected hlub) hp (Jplus_ne_singleton hpN)

/-- **The level `{h = c}` is a Cauchy surface of `N = sliceDom a b c`** (`c < b`): every
inextensible causal curve of `N` reaches both sides of the level (`pastExtensible_sliceDom`,
`futureExtensible_sliceDom`, after an `arctan` reparametrisation), hence meets it (intermediate
values of the continuous `h`), and meets it once (`h` strictly increasing along `≤`). -/
theorem isCauchySurfaceOn_sliceDom {a b c : ℝ} (hcb : c < b) :
    causality.IsCauchySurfaceOn (sliceDom a b c) ({z | hcoord z = c} ∩ sliceDom a b c) := by
  intro I γ hγ
  have hle := le_of_le_top_curve hγ.1
  obtain ⟨hpi, hfi⟩ := Causal.Causality.inextensible_iff.1 hγ
  obtain ⟨hd, hsub, htan, hpast, hfut⟩ := hγ.1.arctanReparam
  have hbb : BddBelow (Real.arctan '' I) := ⟨-(π / 2), fun u hu => (hsub hu).1.le⟩
  have hba : BddAbove (Real.arctan '' I) := ⟨π / 2, fun u hu => (hsub hu).2.le⟩
  obtain ⟨s₁, hs₁, h₁⟩ : ∃ s ∈ I, hcoord (γ s) ≤ c := by
    by_contra hcon
    push Not at hcon
    exact hpi.2 (hpast (pastExtensible_sliceDom hd hbb fun u hu => hcon _ (htan u hu)))
  obtain ⟨s₂, hs₂, h₂⟩ : ∃ s ∈ I, c ≤ hcoord (γ s) := by
    by_contra hcon
    push Not at hcon
    exact hfi.2 (hfut (futureExtensible_sliceDom hcb hd hba fun u hu => hcon _ (htan u hu)))
  have hex : ∃ s ∈ I, hcoord (γ s) = c := by
    rcases le_total s₁ s₂ with h12 | h21
    · have hIcc : Icc s₁ s₂ ⊆ I := hγ.1.ordConnected.out hs₁ hs₂
      have hcont : ContinuousOn (fun s => hcoord (γ s)) (Icc s₁ s₂) :=
        continuous_hcoord.comp_continuousOn (hγ.1.continuousOn_Icc hs₁ hs₂)
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc h12 hcont ⟨h₁, h₂⟩
      exact ⟨s, hIcc hs, hs0⟩
    · have := (calculus_le (hle s₂ hs₂ s₁ hs₁ h21)).2.2.2.2.2
      exact ⟨s₂, hs₂, le_antisymm (this.trans h₁) h₂⟩
  obtain ⟨s, hs, hsc⟩ := hex
  refine ⟨γ s, ⟨⟨s, hs, rfl⟩, hsc, hγ.1.mem hs⟩, ?_⟩
  rintro _ ⟨⟨s', hs', rfl⟩, hs'c, -⟩
  have hs'c' : hcoord (γ s') = c := hs'c
  by_contra hne
  rcases le_total s s' with h | h
  · have := hcoord_lt_of_le (hle s hs s' hs' h) (Ne.symm hne)
    rw [hsc, hs'c'] at this; exact lt_irrefl _ this
  · have := hcoord_lt_of_le (hle s' hs' s hs h) hne
    rw [hsc, hs'c'] at this; exact lt_irrefl _ this

/-- Points of `J⁺(w) ∩ ball(w, δ)` at a BTZ point `w` are reached inside the ball. -/
theorem cle_ball_of_le_axis {w z : E0} (hw : w ∈ axis) {δ : ℝ} (hz : z ∈ Metric.ball w δ)
    (h : Le w z) {O : Opens E0} (hO : Metric.ball w δ ⊆ O) : causality.le O w z := by
  obtain ⟨θ₁, θ₂, h₁, h₂, hc⟩ := h
  refine cle_of_seg h₁ h₂ hc fun s hs => hO ?_
  have hends := le_seg_ends (adm_lift w θ₁) hc hs
  rw [unlift_lift h₁, unlift_lift h₂] at hends
  exact mem_ball_of_le_of_le hw hends.1 hends.2 (Metric.mem_ball_self (Metric.pos_of_mem_ball hz)) hz

/-- **`LocalModel.coneSlicePast` at a BTZ point of `𝔼₀`** (the dispatch's
`K = J⁺_O(w) ∩ {τ + r = c}`, `c` slightly above `τ(w)`): `K = {f ≥ τ_w, h = c}` (the part of the
level in `J⁺(w)`, a compact disc of radius `2(c − τ_w)/3`); an open `V ⊇ K` contains the thickened
disc `{f > τ_w − η, h = c}` (compactness), which is the level `{h = c}` of the domain
`N = sliceDom (τ_w − η) b c`, a Cauchy surface of it (`isCauchySurfaceOn_sliceDom`). -/
theorem sliceAt_past_of_mem_axis {w : E0} (hw : w ∈ axis) :
    SliceAt causality w fun O z => causality.le O w z := by
  intro O hwO
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 O.isOpen w hwO
  have hw0 : rad w = 0 := rad_eq_zero.2 hw
  set ε := δ / 4 with hε
  have hε0 : 0 < ε := by positivity
  set c := w.1 + ε with hc
  set K : Set E0 := {z | w.1 ≤ fcoord z ∧ hcoord z = c} with hK
  have hKball : ∀ z ∈ K, z ∈ Metric.ball w δ := by
    rintro z ⟨hf, hh⟩
    have hr := rad_nonneg z
    have h1 := fcoord_eq_hcoord z
    rw [hh] at h1
    have h2 : z.1 = c - rad z := by
      have : hcoord z = z.1 + rad z := rfl
      linarith
    rw [Metric.mem_ball, dist_axis hw, max_lt_iff, abs_lt]
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  refine ⟨K, fun z hz => hδO (hKball z hz), fun z hz => ⟨?_, ?_⟩, fun V hV hKV => ?_⟩
  · rintro rfl
    have h := hz.2
    simp only [hcoord, hw0, add_zero, hc] at h
    linarith
  · exact cle_ball_of_le_axis hw (hKball z hz) ((le_axis_iff hw).2 hz.1) hδO
  · -- compactness: a thickening of `K` in `V`
    have hKc : IsCompact K := by
      refine Metric.isCompact_of_isClosed_isBounded
        ((isClosed_le continuous_const continuous_fcoord).inter
          (isClosed_eq continuous_hcoord continuous_const))
        (Metric.isBounded_ball.subset fun z hz => hKball z hz)
    obtain ⟨η', hη', hthick⟩ := hKc.exists_thickening_subset_open hV hKV
    set η := min ε η' with hη
    have hη0 : 0 < η := lt_min hε0 hη'
    have hηε : η ≤ ε := min_le_left _ _
    have hηη' : η ≤ η' := min_le_right _ _
    set a := w.1 - η with ha
    set b := w.1 + 2 * ε with hb
    have hcb : c < b := by rw [hc, hb]; linarith
    refine ⟨sliceDom a b c, {z | hcoord z = c} ∩ sliceDom a b c, ?_, ?_, inter_subset_right,
      ?_, isCauchySurfaceOn_sliceDom hcb⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [fcoord_of_axis hw, ha]; linarith
      · simp only [hcoord, hw0, add_zero, hb]; linarith
      · rw [hw0, hc, ha]; linarith
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := hz
      have hr := rad_nonneg z
      simp only [fcoord] at h1
      simp only [hcoord] at h2
      refine hδO ?_
      rw [Metric.mem_ball, dist_axis hw, max_lt_iff, abs_lt]
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      have : rad z < 2 * (c - a) / 3 := h3
      rw [hc, ha] at this
      linarith
    · rintro z ⟨hzc, hzN⟩
      have hzc' : hcoord z = c := hzc
      refine hthick (Metric.mem_thickening_iff.2 ?_)
      by_cases hfz : w.1 ≤ fcoord z
      · exact ⟨z, ⟨hfz, hzc'⟩, by rw [dist_self]; exact hη'⟩
      · push Not at hfz
        have hf1 : a < fcoord z := hzN.1
        have hfeq := fcoord_eq_hcoord z
        rw [hzc'] at hfeq
        set r := rad z with hr
        have hrpos : 2 * ε / 3 < r := by linarith
        have hrlt : r < 2 * (ε + η) / 3 := by linarith
        have hr0 : 0 < r := by linarith
        set r' := 2 * ε / 3 with hr'
        set z' : E0 := (c - r', ((r' / r : ℝ) : ℂ) * z.2) with hz'
        have hrz' : rad z' = r' := by
          simp only [rad, hz', norm_mul, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_pos (by positivity), show ‖z.2‖ = r from rfl]
          field_simp
        have hz1 : z.1 = c - r := by
          have : hcoord z = z.1 + rad z := rfl
          rw [hzc'] at this; linarith
        refine ⟨z', ⟨?_, ?_⟩, ?_⟩
        · show w.1 ≤ (c - r') - rad z' / 2
          rw [hrz', hc, hr']; linarith
        · show (c - r') + rad z' = c
          rw [hrz']; ring
        · rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm, max_lt_iff]
          have hnorm : ‖z.2 - ((r' / r : ℝ) : ℂ) * z.2‖ = r - r' := by
            rw [show z.2 - ((r' / r : ℝ) : ℂ) * z.2 = ((1 - r' / r : ℝ) : ℂ) * z.2 by push_cast; ring,
              norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have : r' / r ≤ 1 := (div_le_one hr0).2 (by linarith)
            rw [abs_of_nonneg (by linarith)]
            show (1 - r' / r) * r = r - r'
            field_simp
          refine ⟨?_, ?_⟩
          · simp only [hz']; rw [hz1, abs_lt]; constructor <;> linarith
          · simp only [hz']; rw [hnorm]; linarith

end AxisSlice

/-- **The `LocalModel` field `coneSlicePast` for `Y = 𝕄 ⊕ 𝔼₀`, at every point** (statement
verbatim): Minkowski's cone slices on `𝕄`, the sector charts off the axis
(`sliceAt_past_of_not_mem_axis`), and at the BTZ points the level `{τ + r = c}` of the domain
`sliceDom` (`sliceAt_past_of_mem_axis`). -/
theorem coneSlicePast_Y : ∀ y : ModelY, ∀ O : TopologicalSpace.Opens ModelY, y ∈ O →
    ∃ K : Set ModelY, K ⊆ O ∧ (∀ z ∈ K, z ≠ y ∧ causalityY.le O y z) ∧
      ∀ V : Set ModelY, IsOpen V → K ⊆ V → ∃ (N : TopologicalSpace.Opens ModelY)
        (Γ : Set ModelY), y ∈ N ∧ N ≤ O ∧ Γ ⊆ N ∧ Γ ⊆ V ∧ causalityY.IsCauchySurfaceOn N Γ :=
  coneSlicePast_Y_of_axis fun _ hw => sliceAt_past_of_mem_axis hw

/-! ### Diamonds form a basis of the topology -/

section Diamonds

open TopologicalSpace

/-- A full diamond with vertices `δ`-close to `x` lies in the ball of radius `7δ` (`Le.dist_le`). -/
theorem diamond_subset_ball {x p q : E0} {δ : ℝ} (hp : dist p x < δ) (hq : dist q x < δ) :
    causality.diamond ⊤ p q ⊆ Metric.ball x (7 * δ) := by
  rintro w ⟨hwq, hpw⟩
  have h1 := (le_top_iff.1 (Causal.Precausality.mem_Jplus_singleton.1 hpw)).dist_le
  have h2 := (le_top_iff.1 (Causal.Precausality.mem_Jminus_singleton.1 hwq)).closed.1
  have hτp := abs_lt.1 ((abs_fst_sub_le_dist p x).trans_lt hp)
  have hτq := abs_lt.1 ((abs_fst_sub_le_dist q x).trans_lt hq)
  rw [Metric.mem_ball]
  calc dist w x ≤ dist w p + dist p x := dist_triangle _ _ _
    _ = dist p w + dist p x := by rw [dist_comm w p]
    _ < 7 * δ := by linarith [hτp.1, hτp.2, hτq.1, hτq.2]

/-- **Diamonds form a basis** (`rem:sing_tarentin` with the localisation the topology asks): for
every `x` and every neighbourhood `U` of `x` there are `p, q ∈ U` with
`x ∈ Int J(p, q) ⊆ J(p, q) ⊆ U`, BTZ points included (there `I⁻(x) = ∅`, so the basis uses the
interiors of the full diamonds `J⁺(p) ∩ J⁻(q)`, not chronological diamonds). -/
theorem diamonds_basis (x : E0) {U : Set E0} (hU : U ∈ 𝓝 x) :
    ∃ p ∈ U, ∃ q ∈ U, x ∈ causality.openDiamond ⊤ p q ∧ causality.diamond ⊤ p q ⊆ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨p, hp, q, hq, hx⟩ := tarentin x (Metric.ball x (δ / 7)) (Metric.ball_mem_nhds x (by positivity))
  have hsub : causality.diamond ⊤ p q ⊆ U := fun w hw => hball (by
    have := diamond_subset_ball hp hq hw
    rwa [show 7 * (δ / 7) = δ by ring] at this)
  exact ⟨p, hball (Metric.ball_subset_ball (by linarith) hp), q,
    hball (Metric.ball_subset_ball (by linarith) hq), hx, hsub⟩

/-- **The open diamonds form a neighbourhood basis at every point.** -/
theorem nhds_hasBasis_openDiamond (x : E0) :
    (𝓝 x).HasBasis (fun pq : E0 × E0 => x ∈ causality.openDiamond ⊤ pq.1 pq.2)
      fun pq => causality.openDiamond ⊤ pq.1 pq.2 := by
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨pq, hx, hsub⟩ => ?_⟩⟩
  · obtain ⟨p, -, q, -, hx, hsub⟩ := diamonds_basis x hU
    exact ⟨(p, q), hx, interior_subset.trans hsub⟩
  · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hx) hsub

/-- **The Alexandrov topology of `𝔼₀` is its topology** (`def:alexandrov_topology`). -/
theorem alexandrovTopology_eq :
    causality.alexandrovTopology = (inferInstance : TopologicalSpace E0) := by
  refine le_antisymm ?_ (le_generateFrom fun s ⟨p, q, hs⟩ => hs ▸ isOpen_interior)
  refine le_of_nhds_le_nhds fun x U hU => ?_
  obtain ⟨p, -, q, -, hx, hsub⟩ := diamonds_basis x hU
  exact @Filter.mem_of_superset _ _ _ _
    (@IsOpen.mem_nhds _ causality.alexandrovTopology _ _
      (TopologicalSpace.isOpen_generateFrom_of_mem ⟨p, q, rfl⟩) hx) (interior_subset.trans hsub)

end Diamonds

/-! ### Isometries of `𝔼₀` as chart isomorphisms; the singular-flat axioms but push-up -/

section Isom

open TopologicalSpace

/-- A homeomorphism carrying the relation `R` forward carries `R`-curves of `W` to `R`-curves of
`e(W)`. -/
theorem curveOn_homeo (e : E0 ≃ₜ E0) {R : E0 → E0 → Prop} (hR : ∀ x y, R x y → R (e x) (e y))
    {W W' : Opens E0} (hW : (W' : Set E0) = e '' W) {c : ℝ → E0} {a b : ℝ}
    (hc : Causal.CurveOn (relOn R) W c a b) :
    Causal.CurveOn (relOn R) W' (fun t => e (c t)) a b where
  mem t ht := by
    show e (c t) ∈ (W' : Set E0)
    rw [hW]; exact mem_image_of_mem e (hc.mem t ht)
  rel t ht N hN htN := by
    let N' : Opens E0 := ⟨e ⁻¹' N, N.isOpen.preimage e.continuous⟩
    have hN' : N' ≤ W := fun z hz => by
      have h1 : e z ∈ (W' : Set E0) := hN hz
      rw [hW] at h1
      obtain ⟨z', hz', he⟩ := h1
      exact e.injective he ▸ hz'
    obtain ⟨l, u, hl, hu, h⟩ := hc.rel t ht N' hN' htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => by
      obtain ⟨m1, m2, hr⟩ := h s hs s' hs' h1 h2 h3
      exact ⟨m1, m2, hR _ _ hr⟩⟩

/-- **A homeomorphism of `𝔼₀` preserving `≼` and `≺` both ways is a chart isomorphism**
(`Causal.ChartIso`) of the causality of `𝔼₀` onto itself. -/
theorem chartIso_of_homeo (e : E0 ≃ₜ E0) (hle : ∀ x y, Le (e x) (e y) ↔ Le x y)
    (hlt : ∀ x y, Lt (e x) (e y) ↔ Lt x y) :
    Causal.ChartIso causality causality e.toOpenPartialHomeomorph := by
  intro U hU x _ y _
  have himg : ((Causal.chartImage e.toOpenPartialHomeomorph U : Opens E0) : Set E0) = e '' U := by
    rw [Causal.coe_chartImage_of_le hU]; rfl
  have himg' : (U : Set E0) =
      e.symm '' (Causal.chartImage e.toOpenPartialHomeomorph U : Opens E0) := by
    rw [himg, ← image_comp, Homeomorph.symm_comp_self, image_id]
  have hle' : ∀ a b, Le a b → Le (e.symm a) (e.symm b) := fun a b h => by
    rw [← hle, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]; exact h
  have hlt' : ∀ a b, Lt a b → Lt (e.symm a) (e.symm b) := fun a b h => by
    rw [← hlt, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]; exact h
  show (CLe U x y ↔ CLe _ (e x) (e y)) ∧ (CLt U x y ↔ CLt _ (e x) (e y))
  refine ⟨⟨fun ⟨a, b, hab, c, hc, h0, h1⟩ => ⟨a, b, hab, _,
      curveOn_homeo e (fun x y => (hle x y).2) himg hc, by simp only [h0], by simp only [h1]⟩,
    fun ⟨a, b, hab, c, hc, h0, h1⟩ => ⟨a, b, hab, _, curveOn_homeo e.symm hle' himg' hc,
      by simp only [h0, Homeomorph.symm_apply_apply], by simp only [h1, Homeomorph.symm_apply_apply]⟩⟩,
    ⟨fun ⟨a, b, hab, c, hc, h0, h1⟩ => ⟨a, b, hab, _,
      curveOn_homeo e (fun x y => (hlt x y).2) himg hc, by simp only [h0], by simp only [h1]⟩,
    fun ⟨a, b, hab, c, hc, h0, h1⟩ => ⟨a, b, hab, _, curveOn_homeo e.symm hlt' himg' hc,
      by simp only [h0, Homeomorph.symm_apply_apply], by simp only [h1, Homeomorph.symm_apply_apply]⟩⟩⟩

/-- **The translation `τ ↦ τ + t` along the BTZ line**, an isometry of `𝔼₀`. -/
noncomputable def tauShift (t : ℝ) : E0 ≃ₜ E0 where
  toFun x := (x.1 + t, x.2)
  invFun x := (x.1 - t, x.2)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The rotation `z ↦ e^{iφ} z` about the BTZ line**, an isometry of `𝔼₀`. -/
noncomputable def rotE0 (φ : ℝ) : E0 ≃ₜ E0 where
  toFun x := (x.1, cexp (φ * I) * x.2)
  invFun x := (x.1, cexp (-φ * I) * x.2)
  left_inv x := by
    refine Prod.ext rfl ?_
    show cexp (-φ * I) * (cexp (φ * I) * x.2) = x.2
    rw [← mul_assoc, ← Complex.exp_add, show (-φ * I : ℂ) + φ * I = 0 by ring, Complex.exp_zero,
      one_mul]
  right_inv x := by
    refine Prod.ext rfl ?_
    show cexp (φ * I) * (cexp (-φ * I) * x.2) = x.2
    rw [← mul_assoc, ← Complex.exp_add, show (φ * I : ℂ) + -φ * I = 0 by ring, Complex.exp_zero,
      one_mul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem rad_tauShift (t : ℝ) (x : E0) : rad (tauShift t x) = rad x := rfl

theorem polar_tauShift (t : ℝ) (x : E0) (θ : ℝ) : Polar (tauShift t x) θ ↔ Polar x θ := Iff.rfl

theorem rad_rotE0 (φ : ℝ) (x : E0) : rad (rotE0 φ x) = rad x := by
  show ‖cexp (φ * I) * x.2‖ = ‖x.2‖
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem polar_rotE0 (φ : ℝ) (x : E0) (θ : ℝ) : Polar (rotE0 φ x) θ ↔ Polar x (θ - φ) := by
  unfold Polar
  rw [rad_rotE0]
  show cexp (φ * I) * x.2 = _ ↔ _
  have hne : cexp (φ * I) ≠ 0 := Complex.exp_ne_zero _
  have e : (rad x : ℂ) * cexp (θ * I) = cexp (φ * I) * ((rad x : ℂ) * cexp (↑(θ - φ) * I)) := by
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e]
  exact ⟨fun h => mul_left_cancel₀ hne h, fun h => by rw [h]⟩

theorem le_tauShift_iff (t : ℝ) (x y : E0) : Le (tauShift t x) (tauShift t y) ↔ Le x y := by
  rw [le_iff_closed, le_iff_closed]
  show (∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ ClosedLe (x.1 + t) (rad x) (y.1 + t) (rad y) _) ↔ _
  simp only [ClosedLe, add_le_add_iff_right, show ∀ a b : ℝ, b + t - (a + t) = b - a from
    fun a b => by ring]

theorem lt_tauShift_iff (t : ℝ) (x y : E0) : Lt (tauShift t x) (tauShift t y) ↔ Lt x y := by
  rw [lt_iff_closed, lt_iff_closed]
  show (∃ θ₁ θ₂, Polar x θ₁ ∧ Polar y θ₂ ∧ ClosedLt (x.1 + t) (rad x) (y.1 + t) (rad y) _) ↔ _
  simp only [ClosedLt, show ∀ a b : ℝ, b + t - (a + t) = b - a from fun a b => by ring]

theorem le_rotE0_iff (φ : ℝ) (x y : E0) : Le (rotE0 φ x) (rotE0 φ y) ↔ Le x y := by
  rw [le_iff_closed, le_iff_closed, rad_rotE0, rad_rotE0]
  show (∃ θ₁ θ₂, _ ∧ _ ∧ ClosedLe x.1 (rad x) y.1 (rad y) _) ↔ _
  constructor
  · rintro ⟨θ₁, θ₂, h₁, h₂, h⟩
    refine ⟨θ₁ - φ, θ₂ - φ, (polar_rotE0 φ x θ₁).1 h₁, (polar_rotE0 φ y θ₂).1 h₂, ?_⟩
    rwa [show θ₂ - φ - (θ₁ - φ) = θ₂ - θ₁ by ring]
  · rintro ⟨θ₁, θ₂, h₁, h₂, h⟩
    refine ⟨θ₁ + φ, θ₂ + φ, (polar_rotE0 φ x _).2 (by rwa [add_sub_cancel_right]),
      (polar_rotE0 φ y _).2 (by rwa [add_sub_cancel_right]), ?_⟩
    rwa [show θ₂ + φ - (θ₁ + φ) = θ₂ - θ₁ by ring]

theorem lt_rotE0_iff (φ : ℝ) (x y : E0) : Lt (rotE0 φ x) (rotE0 φ y) ↔ Lt x y := by
  rw [lt_iff_closed, lt_iff_closed, rad_rotE0, rad_rotE0]
  show (∃ θ₁ θ₂, _ ∧ _ ∧ ClosedLt x.1 (rad x) y.1 (rad y) _) ↔ _
  constructor
  · rintro ⟨θ₁, θ₂, h₁, h₂, h⟩
    refine ⟨θ₁ - φ, θ₂ - φ, (polar_rotE0 φ x θ₁).1 h₁, (polar_rotE0 φ y θ₂).1 h₂, ?_⟩
    rwa [show θ₂ - φ - (θ₁ - φ) = θ₂ - θ₁ by ring]
  · rintro ⟨θ₁, θ₂, h₁, h₂, h⟩
    refine ⟨θ₁ + φ, θ₂ + φ, (polar_rotE0 φ x _).2 (by rwa [add_sub_cancel_right]),
      (polar_rotE0 φ y _).2 (by rwa [add_sub_cancel_right]), ?_⟩
    rwa [show θ₂ + φ - (θ₁ + φ) = θ₂ - θ₁ by ring]

/-- **The translations along the BTZ line are chart isomorphisms** (`chartIso_mem` for the
`τ`-translation generators of `Isom(𝔼₀)`). -/
theorem chartIso_tauShift (t : ℝ) :
    Causal.ChartIso causality causality (tauShift t).toOpenPartialHomeomorph :=
  chartIso_of_homeo _ (le_tauShift_iff t) (lt_tauShift_iff t)

/-- **The rotations about the BTZ line are chart isomorphisms** (`chartIso_mem` for the rotation
generators of `Isom(𝔼₀)`). -/
theorem chartIso_rotE0 (φ : ℝ) :
    Causal.ChartIso causality causality (rotE0 φ).toOpenPartialHomeomorph :=
  chartIso_of_homeo _ (le_rotE0_iff φ) (lt_rotE0_iff φ)

theorem tauShift_axis {t : ℝ} {x : E0} : tauShift t x ∈ axis ↔ x ∈ axis := Iff.rfl

theorem rotE0_axis {φ : ℝ} {x : E0} : rotE0 φ x ∈ axis ↔ x ∈ axis := by
  rw [← rad_eq_zero, ← rad_eq_zero, rad_rotE0]

/-- The singular loci of `𝔼₀`: `sing₀ = axis`, `sing_α = ∅` for `α ≠ 0`. -/
def singE0 (α : ℝ) : Set E0 := if α = 0 then axis else ∅

theorem singE0_zero : singE0 0 = axis := if_pos rfl

theorem singE0_of_ne {α : ℝ} (h : α ≠ 0) : singE0 α = ∅ := if_neg h

/-- The BTZ line has empty interior. -/
theorem interior_axis : interior axis = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hx0 : x.2 = 0 := (interior_subset hx : x ∈ axis)
  have hmem : ((x.1, ((δ / 2 : ℝ) : ℂ)) : E0) ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_self, hx0, dist_zero_right,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact ⟨hδ, by linarith⟩
  have h1 : ((δ / 2 : ℝ) : ℂ) = 0 := (interior_subset (hball hmem) : _ ∈ axis)
  have := Complex.ofReal_eq_zero.1 h1
  linarith

/-- **`Causal.SingularFlatAxioms` for `𝔼₀`, push-up given**: every field but `pushUp` is proved
(the BTZ axioms, absolute minimality, causal arc-connectedness, tarentinity, `Z⁺ = 𝔼₀`,
`Z⁻ = 𝔼₀ ∖ sing₀`, the topology, the singular loci). The local push-up `J^±_U(I^±_U(x)) ⊂
I^±_U(x)` in every open `U` is the one input left (it holds globally, `Lt.trans_le`). -/
theorem singularFlatAxioms_of_pushUp (hP : causality.PushUp) :
    causality.SingularFlatAxioms singE0 where
  toBTZAxioms := by rw [singE0_zero]; exact btzAxioms
  pushUp := hP
  absolutelyMinimal := causallyArcConnected.absolutelyMinimal
  causallyArcConnected := causallyArcConnected
  tarentin := tarentin
  mem_Zplus := mem_Zplus
  mem_Zminus_iff p := by rw [singE0_zero]; exact mem_Zminus_iff p
  t2 := inferInstance
  secondCountable := inferInstance
  metrizable := inferInstance
  locallyCompact := inferInstance
  noIsolated p := inferInstance
  isClosed_sing α _ := by
    by_cases h : α = 0
    · rw [h, singE0_zero]; exact isClosed_axis
    · rw [singE0_of_ne h]; exact isClosed_empty
  interior_sing α _ := by
    by_cases h : α = 0
    · rw [h, singE0_zero]; exact interior_axis
    · rw [singE0_of_ne h]; exact interior_empty
  massive_line α hα p hp := by
    rw [singE0_of_ne hα.ne'] at hp; exact absurd hp (notMem_empty p)

end Isom

/-! ### Transport to Model's `𝔼₀ = Γ_{2π}\(𝔻_∞ × ℝ)` and to `𝕄 ⊕ BTZE0` -/

section Transport

open TopologicalSpace

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]

/-- The image of an open set by a homeomorphism. -/
def opensImage (e : X ≃ₜ Z) (U : Opens X) : Opens Z := ⟨e '' U, e.isOpenMap U U.isOpen⟩

theorem opensImage_mono (e : X ≃ₜ Z) {U V : Opens X} (h : V ≤ U) : opensImage e V ≤ opensImage e U :=
  image_mono h

theorem mem_of_mem_opensImage (e : X ≃ₜ Z) {U : Opens X} {x : X} (h : e x ∈ opensImage e U) :
    x ∈ U := by
  obtain ⟨x', hx', he⟩ := h; exact e.injective he ▸ hx'

/-- **The causality pulled back along a homeomorphism** `e : X ≃ₜ Z`. -/
def transportCausality (e : X ≃ₜ Z) (C : Causal.Causality Z) : Causal.Causality X where
  le U x y := C.le (opensImage e U) (e x) (e y)
  lt U x y := C.lt (opensImage e U) (e x) (e y)
  le_mem_left h := mem_of_mem_opensImage e (C.le_mem_left h)
  le_mem_right h := mem_of_mem_opensImage e (C.le_mem_right h)
  lt_mem_left h := mem_of_mem_opensImage e (C.lt_mem_left h)
  lt_mem_right h := mem_of_mem_opensImage e (C.lt_mem_right h)
  le_refl hx := C.le_refl ⟨_, hx, rfl⟩
  le_trans h₁ h₂ := C.le_trans h₁ h₂
  lt_trans h₁ h₂ := C.lt_trans h₁ h₂
  le_mono hVU _ _ h := C.le_mono (opensImage_mono e hVU) h
  lt_mono hVU _ _ h := C.lt_mono (opensImage_mono e hVU) h
  le_of_lt h := C.le_of_lt h
  isOpen_lt_right U x := (C.isOpen_lt_right (opensImage e U) (e x)).preimage e.continuous
  isOpen_lt_left U x := (C.isOpen_lt_left (opensImage e U) (e x)).preimage e.continuous

variable {e : X ≃ₜ Z} {C : Causal.Causality Z}

theorem curveOn_transport {r : Opens Z → Z → Z → Prop} {U : Opens X} {c : ℝ → Z} {a b : ℝ}
    (hc : Causal.CurveOn r (opensImage e U) c a b) :
    Causal.CurveOn (fun N p q => r (opensImage e N) (e p) (e q)) U (fun t => e.symm (c t)) a b where
  mem t ht := by
    have := hc.mem t ht
    obtain ⟨u, hu, he⟩ := this
    rw [← he, Homeomorph.symm_apply_apply]; exact hu
  rel t ht N hN htN := by
    have htN' : c t ∈ opensImage e N := ⟨_, htN, e.apply_symm_apply _⟩
    obtain ⟨l, u, hl, hu, h⟩ := hc.rel t ht (opensImage e N) (opensImage_mono e hN) htN'
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
    simp only [Homeomorph.apply_symm_apply]
    exact h s hs s' hs' h1 h2 h3

/-- Causal arc-connectedness is transported along homeomorphisms. -/
theorem transport_causallyArcConnected (h : C.CausallyArcConnected) :
    (transportCausality e C).CausallyArcConnected := by
  rw [Causal.Causality.CausallyArcConnected, Causal.Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun hpq => ?_, fun hpq => ?_⟩
  · obtain ⟨c, hc, h0, h1⟩ := ((h (opensImage e U) le_top (e p) (e q)).1).1 hpq
    exact ⟨_, curveOn_transport hc, by simp [h0], by simp [h1]⟩
  · obtain ⟨c, hc, h0, h1⟩ := ((h (opensImage e U) le_top (e p) (e q)).2).1 hpq
    exact ⟨_, curveOn_transport hc, by simp [h0], by simp [h1]⟩

theorem opensImage_eq {U : Opens X} {V : Opens Z} (hU : (U : Set X) = e.symm '' V) :
    opensImage e U = V := by
  ext z
  show z ∈ e '' (U : Set X) ↔ z ∈ V
  rw [hU, ← image_comp, Homeomorph.self_comp_symm, image_id]
  exact Iff.rfl

/-- The inverse of the transporting homeomorphism is an abstract `𝕄≥0`-morphism. -/
theorem isEMorphismOn_transport_symm :
    Causal.IsEMorphismOn C (transportCausality e C) ⊤ e.symm where
  continuousOn := e.symm.continuous.continuousOn
  isOpen_image V _ := e.symm.isOpenMap V V.isOpen
  map_le V U _ hmaps x y h := by
    show C.le (opensImage e U) (e (e.symm x)) (e (e.symm y))
    simp only [Homeomorph.apply_symm_apply]
    exact C.le_mono (show V ≤ opensImage e U from
      fun z hz => ⟨e.symm z, hmaps hz, e.apply_symm_apply z⟩) h
  map_lt V U _ hmaps x y h := by
    show C.lt (opensImage e U) (e (e.symm x)) (e (e.symm y))
    simp only [Homeomorph.apply_symm_apply]
    exact C.lt_mono (show V ≤ opensImage e U from
      fun z hz => ⟨e.symm z, hmaps hz, e.apply_symm_apply z⟩) h
  locally _ _ := ⟨⊤, le_rfl, trivial, e.symm.injective.injOn, fun V' _ U hU p _ q _ => by
    show (_ ↔ C.le (opensImage e U) (e (e.symm p)) (e (e.symm q))) ∧
      (_ ↔ C.lt (opensImage e U) (e (e.symm p)) (e (e.symm q)))
    simp only [opensImage_eq hU, Homeomorph.apply_symm_apply, iff_self, and_self]⟩

/-- Cone slices are transported along the homeomorphism. -/
theorem SliceAt.transport {z : Z} {Q : TopologicalSpace.Opens Z → Z → Prop}
    (h : SliceAt C z Q) : SliceAt (transportCausality e C) (e.symm z)
      (fun O x => Q (opensImage e O) (e x)) := by
  refine SliceAt.pushforward isEMorphismOn_transport_symm e.symm.injective (fun O hO z hq => ?_) h
  have : (⟨e.symm ⁻¹' (O : Set X), hO⟩ : Opens Z) = opensImage e O := by
    ext w
    show w ∈ e.symm ⁻¹' (O : Set X) ↔ w ∈ e '' (O : Set X)
    rw [e.image_eq_preimage_symm]
  rw [this] at hq
  simpa using hq

end Transport

section BTZE0

open TopologicalSpace

/-- `(w, t) ↦ (t/2, w̄)`: the cylinder's `ℂ × ℝ` to the paper's `(τ, z)` (`t = 2τ`, `θ_cyl = −θ`,
`btzPaperDev_eq_btzDevM`). -/
noncomputable def paperCoords : ℂ × ℝ ≃ₜ E0 where
  toFun p := (p.2 / 2, (starRingEnd ℂ) p.1)
  invFun q := ((starRingEnd ℂ) q.2, 2 * q.1)
  left_inv p := Prod.ext (Complex.conj_conj _) (by simp only; ring)
  right_inv q := Prod.ext (by simp only; ring) (Complex.conj_conj _)
  continuous_toFun := by
    exact (continuous_snd.div_const 2).prodMk (Complex.continuous_conj.comp continuous_fst)
  continuous_invFun := by
    exact (Complex.continuous_conj.comp continuous_snd).prodMk (continuous_const.mul continuous_fst)

/-- **Model's `𝔼₀` in the paper's coordinates**: `GX.BTZE0 = Γ_{2π}\(𝔻_∞ × ℝ) ≃ₜ ℝ × ℂ`. -/
noncomputable def toPaper : BTZE0 ≃ₜ E0 := (cylHomeomorph btz_two_pi_ne_zero ℝ).trans paperCoords

/-- `toPaper` reads the cylinder point `(r, −θ, 2τ)` as `(τ, r e^{iθ})`: the developments of this
file are Model's (`btzPaperDev_eq_btzDevM`). -/
theorem toPaper_posEmb {r : ℝ} (hr : 0 < r) (θ τ : ℝ) :
    toPaper (orbitMk (GammaA (2 * π)) (DInfty.posEmb ⟨(r, -θ), hr⟩, 2 * τ)) =
      (τ, (r : ℂ) * cexp (θ * I)) := by
  show paperCoords (cylHomeomorph btz_two_pi_ne_zero ℝ _) = _
  rw [cylHomeomorph_apply]
  refine Prod.ext (by show 2 * τ / 2 = τ; ring) ?_
  show (starRingEnd ℂ) (DInfty.cplx (2 * π) (DInfty.posEmb ⟨(r, -θ), hr⟩)) = _
  simp only [DInfty.cplx, DInfty.posEmb_r, DInfty.posEmb_θ]
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  rw [show 2 * π / (2 * π) * -θ = -θ by field_simp]
  push_cast; ring

theorem toPaper_apex (τ : ℝ) : toPaper (orbitMk (GammaA (2 * π)) (DInfty.apex, 2 * τ)) = (τ, 0) := by
  show paperCoords (cylHomeomorph btz_two_pi_ne_zero ℝ _) = _
  rw [cylHomeomorph_apply]
  refine Prod.ext (by show 2 * τ / 2 = τ; ring) ?_
  show (starRingEnd ℂ) (DInfty.cplx (2 * π) DInfty.apex) = 0
  rw [DInfty.cplx_apex, map_zero]

/-- **The causality of Model's `𝔼₀`** (`GX.BTZE0`), through `toPaper`. -/
noncomputable def causalityBTZE0 : Causal.Causality BTZE0 := transportCausality toPaper causality

/-- **`Y = 𝕄 ⊕ BTZE0`** (the carrier of `GXScaffold.BTZ.Rigid`'s `E0Y`) and its homeomorphism
with `ModelY`. -/
noncomputable def toPaperY : (Causal.Minkowski 2 ⊕ BTZE0) ≃ₜ ModelY :=
  Homeomorph.sumCongr (Homeomorph.refl _) toPaper

/-- **The causality of `𝕄 ⊕ BTZE0`**: Minkowski's on `𝕄`, `causalityBTZE0` on `BTZE0`. -/
noncomputable def causalityYBTZ : Causal.Causality (Causal.Minkowski 2 ⊕ BTZE0) :=
  transportCausality toPaperY causalityY

theorem causalityYBTZ_causallyArcConnected : causalityYBTZ.CausallyArcConnected :=
  transport_causallyArcConnected causalityY_causallyArcConnected

/-- **`absolutelyMinimalOn_Y` for `𝕄 ⊕ BTZE0`.** -/
theorem absolutelyMinimalOn_YBTZ (W : Opens (Causal.Minkowski 2 ⊕ BTZE0)) :
    causalityYBTZ.AbsolutelyMinimalOn W :=
  Causal.Causality.CausallyArcConnectedOn.absolutelyMinimalOn
    (causalityYBTZ_causallyArcConnected.mono le_top)

/-- **`coneSliceFuture` for `𝕄 ⊕ BTZE0`**, the BTZ locus read through `toPaperY` (its axis). -/
theorem coneSliceFuture_YBTZ : ∀ y : Causal.Minkowski 2 ⊕ BTZE0, y ∉ toPaperY ⁻¹' singY0 →
    ∀ O : Opens (Causal.Minkowski 2 ⊕ BTZE0), y ∈ O →
    ∃ K : Set (Causal.Minkowski 2 ⊕ BTZE0), K ⊆ O ∧
      (∀ z ∈ K, z ∉ toPaperY ⁻¹' singY0 ∧ z ≠ y ∧ causalityYBTZ.le O z y) ∧
      ∀ V : Set (Causal.Minkowski 2 ⊕ BTZE0), IsOpen V → K ⊆ V →
        ∃ (N : Opens (Causal.Minkowski 2 ⊕ BTZE0)) (Γ : Set (Causal.Minkowski 2 ⊕ BTZE0)),
          y ∈ N ∧ N ≤ O ∧ Γ ⊆ N ∧ Γ ⊆ V ∧ causalityYBTZ.IsCauchySurfaceOn N Γ := by
  intro y hy
  have hY : SliceAt causalityY (toPaperY y) fun O z => z ∉ singY0 ∧ causalityY.le O z (toPaperY y) := by
    intro O hO
    obtain ⟨K, hK, hKp, hV⟩ := coneSliceFuture_Y (toPaperY y) hy O hO
    exact ⟨K, hK, fun z hz => ⟨(hKp z hz).2.1, (hKp z hz).1, (hKp z hz).2.2⟩, hV⟩
  have key := hY.transport (e := toPaperY)
  rw [Homeomorph.symm_apply_apply] at key
  intro O hyO
  obtain ⟨K, hK, hKp, hV⟩ := key O hyO
  exact ⟨K, hK, fun z hz => ⟨(hKp z hz).2.1, (hKp z hz).1, (hKp z hz).2.2⟩, hV⟩


/-- **`coneSlicePast` for `𝕄 ⊕ BTZE0`**, at every point (Rigid's `E0Y` carrier). -/
theorem coneSlicePast_YBTZ : ∀ y : Causal.Minkowski 2 ⊕ BTZE0,
    ∀ O : Opens (Causal.Minkowski 2 ⊕ BTZE0), y ∈ O →
    ∃ K : Set (Causal.Minkowski 2 ⊕ BTZE0), K ⊆ O ∧ (∀ z ∈ K, z ≠ y ∧ causalityYBTZ.le O y z) ∧
      ∀ V : Set (Causal.Minkowski 2 ⊕ BTZE0), IsOpen V → K ⊆ V →
        ∃ (N : Opens (Causal.Minkowski 2 ⊕ BTZE0)) (Γ : Set (Causal.Minkowski 2 ⊕ BTZE0)),
          y ∈ N ∧ N ≤ O ∧ Γ ⊆ N ∧ Γ ⊆ V ∧ causalityYBTZ.IsCauchySurfaceOn N Γ := by
  intro y
  have hY : SliceAt causalityY (toPaperY y) fun O z => causalityY.le O (toPaperY y) z :=
    coneSlicePast_Y (toPaperY y)
  have key := hY.transport (e := toPaperY)
  rw [Homeomorph.symm_apply_apply] at key
  exact key

end BTZE0


/-! ### Chart isomorphisms, locally -/

section IsoNear

open TopologicalSpace

variable {M X Z : Type*} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Z]
  {C : Causal.Causality M} {D : Causal.Causality X} {E : Causal.Causality Z}
  {e : OpenPartialHomeomorph M X} {f : OpenPartialHomeomorph X Z} {O O' : Opens M}

/-- `e` carries the relations of every open subset of `O` to those of its image: `Causal.ChartIso`
restricted to the open subsets of `O`. -/
def IsoNear (C : Causal.Causality M) (D : Causal.Causality X) (e : OpenPartialHomeomorph M X)
    (O : Opens M) : Prop :=
  ∀ V : Opens M, V ≤ O → ∀ a ∈ V, ∀ b ∈ V,
    (C.le V a b ↔ D.le (Causal.chartImage e V) (e a) (e b)) ∧
      (C.lt V a b ↔ D.lt (Causal.chartImage e V) (e a) (e b))

theorem isoNear_of_chartIso (h : Causal.ChartIso C D e) (hO : O ≤ Causal.chartSource e) :
    IsoNear C D e O := fun V hV => h V (hV.trans hO)

theorem IsoNear.mono (h : IsoNear C D e O) (hO : O' ≤ O) : IsoNear C D e O' :=
  fun V hV => h V (hV.trans hO)

theorem chartImage_congr {e e' : OpenPartialHomeomorph M X} {V : Opens M}
    (hV : V ≤ Causal.chartSource e) (hV' : V ≤ Causal.chartSource e')
    (heq : ∀ z ∈ V, e z = e' z) : Causal.chartImage e V = Causal.chartImage e' V := by
  apply SetLike.coe_injective
  rw [Causal.coe_chartImage_of_le hV, Causal.coe_chartImage_of_le hV']
  exact image_congr heq

/-- Two charts which agree on `O` are isomorphisms near `O` together. -/
theorem IsoNear.congr {e e' : OpenPartialHomeomorph M X} (h : IsoNear C D e O)
    (hO : O ≤ Causal.chartSource e) (hO' : O ≤ Causal.chartSource e')
    (heq : ∀ z ∈ O, e z = e' z) : IsoNear C D e' O := by
  intro V hV a ha b hb
  rw [← chartImage_congr (hV.trans hO) (hV.trans hO') fun z hz => heq z (hV hz),
    ← heq a (hV ha), ← heq b (hV hb)]
  exact h V hV a ha b hb

theorem chartImage_trans {V : Opens M} (hV : V ≤ Causal.chartSource (e.trans f)) :
    Causal.chartImage (e.trans f) V = Causal.chartImage f (Causal.chartImage e V) := by
  have hVe : V ≤ Causal.chartSource e := fun z hz => (hV hz).1
  have hVf : Causal.chartImage e V ≤ Causal.chartSource f := by
    intro p hp
    obtain ⟨z, -, hzV, rfl, -⟩ := Causal.exists_of_mem_chartImage hp
    exact (hV hzV).2
  apply SetLike.coe_injective
  rw [Causal.coe_chartImage_of_le hV, Causal.coe_chartImage_of_le hVf,
    Causal.coe_chartImage_of_le hVe, OpenPartialHomeomorph.coe_trans, image_comp]

/-- **Composition.** -/
theorem IsoNear.trans {O'' : Opens X} (h : IsoNear C D e O) (h' : IsoNear D E f O'')
    (hO : O ≤ Causal.chartSource (e.trans f)) (hO'' : Causal.chartImage e O ≤ O'') :
    IsoNear C E (e.trans f) O := by
  intro V hV a ha b hb
  have hVt := hV.trans hO
  have hVe : V ≤ Causal.chartSource e := fun z hz => (hVt hz).1
  have h1 := h V hV a ha b hb
  have h2 := h' (Causal.chartImage e V) ((Causal.chartImage_mono hV).trans hO'') (e a)
    (Causal.mem_chartImage_of_mem (hVe ha) ha) (e b) (Causal.mem_chartImage_of_mem (hVe hb) hb)
  rw [chartImage_trans hVt, OpenPartialHomeomorph.coe_trans, comp_apply, comp_apply, ← h2.1,
    ← h2.2]
  exact h1

theorem chartIso_trans (h : Causal.ChartIso C D e) (h' : Causal.ChartIso D E f) :
    Causal.ChartIso C E (e.trans f) :=
  IsoNear.trans (isoNear_of_chartIso h (fun z hz => hz.1)) h' le_rfl (by
    intro p hp
    obtain ⟨z, -, hzV, rfl, -⟩ := Causal.exists_of_mem_chartImage hp
    exact hzV.2)

/-- **Inverse.** -/
theorem IsoNear.symm (h : IsoNear C D e O) (hO : O ≤ Causal.chartSource e) :
    IsoNear D C e.symm (Causal.chartImage e O) := by
  intro V' hV' a' ha' b' hb'
  have hVt : (V' : Set X) ⊆ e.target := fun p hp => by
    obtain ⟨z, hz, -, rfl, -⟩ := Causal.exists_of_mem_chartImage (hV' hp)
    exact e.map_source hz
  set V := Causal.chartImage e.symm V'
  have hVO : V ≤ O := by
    intro z hz
    obtain ⟨p, -, hpV, rfl, -⟩ := Causal.exists_of_mem_chartImage hz
    obtain ⟨w, hw, hwO, rfl, -⟩ := Causal.exists_of_mem_chartImage (hV' hpV)
    rw [e.left_inv hw]; exact hwO
  have hVs : V ≤ Causal.chartSource e := hVO.trans hO
  have himg : Causal.chartImage e V = V' := by
    apply SetLike.coe_injective
    rw [Causal.coe_chartImage_of_le hVs]
    show e '' (e.symm '' (e.target ∩ V')) = V'
    rw [inter_eq_right.2 hVt, image_image]
    conv_rhs => rw [← image_id (V' : Set X)]
    exact image_congr fun p hp => e.right_inv (hVt hp)
  have ha : e.symm a' ∈ V := Causal.mem_chartImage_of_mem (e.symm.map_source' (hVt ha') |> fun _ =>
    (show a' ∈ e.symm.source from hVt ha')) ha'
  have hb : e.symm b' ∈ V := Causal.mem_chartImage_of_mem (show b' ∈ e.symm.source from hVt hb') hb'
  have := h V hVO _ ha _ hb
  rw [himg, e.right_inv (hVt ha'), e.right_inv (hVt hb')] at this
  exact ⟨this.1.symm, this.2.symm⟩

theorem isoNear_of_agreeOn (h : Causal.AgreeOn C (D.chartTransport e) O)
    (hO : O ≤ Causal.chartSource e) : IsoNear C D e O := by
  intro V hV a ha b hb
  have hVs := hV.trans hO
  have h1 := h V hV a b
  rw [Causal.Causality.chartTransport, Causal.LocalCausality.extend_le_iff hVs,
    Causal.LocalCausality.extend_lt_iff hVs] at h1
  exact ⟨h1.1.trans ⟨fun h => h.2.2, fun h' => ⟨ha, hb, h'⟩⟩,
    h1.2.trans ⟨fun h => h.2.2, fun h' => ⟨ha, hb, h'⟩⟩⟩

theorem agreeOn_of_isoNear (h : IsoNear C D e O) (hO : O ≤ Causal.chartSource e) :
    Causal.AgreeOn C (D.chartTransport e) O := by
  intro V hV a b
  have hVs := hV.trans hO
  rw [Causal.Causality.chartTransport, Causal.LocalCausality.extend_le_iff hVs,
    Causal.LocalCausality.extend_lt_iff hVs]
  refine ⟨⟨fun hab => ?_, fun hab => ?_⟩, ⟨fun hab => ?_, fun hab => ?_⟩⟩
  · have ha := C.le_mem_left hab; have hb := C.le_mem_right hab
    exact ⟨ha, hb, ((h V hV a ha b hb).1).1 hab⟩
  · exact ((h V hV a hab.1 b hab.2.1).1).2 hab.2.2
  · have ha := C.lt_mem_left hab; have hb := C.lt_mem_right hab
    exact ⟨ha, hb, ((h V hV a ha b hb).2).1 hab⟩
  · exact ((h V hV a hab.1 b hab.2.1).2).2 hab.2.2

/-- **A chart which is near every point of its source an isomorphism is one**, for causalities
absolutely minimal on every open set (the argument of `Causal.chartIso_of_mem_maximalAtlas`). -/
theorem chartIso_of_isoNear (hC : ∀ W : Opens M, C.AbsolutelyMinimalOn W)
    (hD : ∀ W : Opens X, D.AbsolutelyMinimalOn W)
    (h : ∀ x ∈ e.source, ∃ O : Opens M, x ∈ O ∧ O ≤ Causal.chartSource e ∧ IsoNear C D e O) :
    Causal.ChartIso C D e := by
  have hCe := D.chartTransport_chartIso e
  have hloc : ∀ x ∈ Causal.chartSource e, ∃ O : Opens M, x ∈ O ∧
      Causal.AgreeOn C (D.chartTransport e) O := fun x hx => by
    obtain ⟨O, hxO, hO, hiso⟩ := h x hx
    exact ⟨O, hxO, agreeOn_of_isoNear hiso hO⟩
  have hACe : (D.chartTransport e).AbsolutelyMinimalOn (Causal.chartSource e) :=
    hCe.absolutelyMinimalOn le_rfl (hD _)
  refine hCe.congr fun V hV x y => ?_
  have h₁ := Causal.imp_of_agree_locally (hC _) hloc hV (x := x) (y := y)
  have h₂ := Causal.imp_of_agree_locally hACe (fun z hz => by
    obtain ⟨O, hzO, hO⟩ := hloc z hz
    exact ⟨O, hzO, hO.symm⟩) hV (x := x) (y := y)
  exact ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩

end IsoNear


/-! ### The charts of `𝕄 ⊕ BTZE0` -/

section ChartsY

open TopologicalSpace

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]

/-- A homeomorphism is a chart isomorphism from the causality it transports. -/
theorem chartIso_transport (e : X ≃ₜ Z) (C : Causal.Causality Z) :
    Causal.ChartIso (transportCausality e C) C e.toOpenPartialHomeomorph := by
  intro U hU x _ y _
  have : Causal.chartImage e.toOpenPartialHomeomorph U = opensImage e U := by
    apply SetLike.coe_injective; rw [Causal.coe_chartImage_of_le hU]; rfl
  rw [this]; exact ⟨Iff.rfl, Iff.rfl⟩

theorem chartIso_transport_symm (e : X ≃ₜ Z) (C : Causal.Causality Z) :
    Causal.ChartIso C (transportCausality e C) e.symm.toOpenPartialHomeomorph := by
  intro U hU x _ y _
  have : opensImage e (Causal.chartImage e.symm.toOpenPartialHomeomorph U) = U := by
    apply opensImage_eq; rw [Causal.coe_chartImage_of_le hU]; rfl
  show (C.le U x y ↔ C.le (opensImage e _) (e (e.symm x)) (e (e.symm y))) ∧
    (C.lt U x y ↔ C.lt (opensImage e _) (e (e.symm x)) (e (e.symm y)))
  rw [this, e.apply_symm_apply, e.apply_symm_apply]
  exact ⟨Iff.rfl, Iff.rfl⟩

@[simp] theorem toPaperY_inl (m : Causal.Minkowski 2) : toPaperY (Sum.inl m) = Sum.inl m := rfl

@[simp] theorem toPaperY_inr (x : BTZE0) : toPaperY (Sum.inr x) = Sum.inr (toPaper x) := rfl

theorem rightOpens_opensImage_toPaperY (U : Opens (Causal.Minkowski 2 ⊕ BTZE0)) :
    rightOpens (opensImage toPaperY U) = opensImage toPaper (rightOpens U) := by
  ext w
  show Sum.inr w ∈ toPaperY '' (U : Set (Causal.Minkowski 2 ⊕ BTZE0)) ↔ w ∈ toPaper '' (Sum.inr ⁻¹' (U : Set (Causal.Minkowski 2 ⊕ BTZE0)))
  constructor
  · rintro ⟨u | u, hu, he⟩
    · simp at he
    · simp only [toPaperY_inr, Sum.inr.injEq] at he
      exact ⟨u, hu, he⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Sum.inr u, hu, rfl⟩

theorem leftOpens_opensImage_toPaperY (U : Opens (Causal.Minkowski 2 ⊕ BTZE0)) :
    leftOpens (opensImage toPaperY U) = leftOpens U := by
  ext w
  show Sum.inl w ∈ toPaperY '' (U : Set (Causal.Minkowski 2 ⊕ BTZE0)) ↔ Sum.inl w ∈ (U : Set (Causal.Minkowski 2 ⊕ BTZE0))
  constructor
  · rintro ⟨u | u, hu, he⟩
    · simp only [toPaperY_inl, Sum.inl.injEq] at he
      exact he ▸ hu
    · simp at he
  · intro hu
    exact ⟨Sum.inl w, hu, rfl⟩

variable {U : Opens (Causal.Minkowski 2 ⊕ BTZE0)}

theorem le_inr_iff {a b : BTZE0} :
    causalityYBTZ.le U (.inr a) (.inr b) ↔ causalityBTZE0.le (rightOpens U) a b := by
  show causality.le (rightOpens (opensImage toPaperY U)) (toPaper a) (toPaper b) ↔ _
  rw [rightOpens_opensImage_toPaperY]; rfl

theorem lt_inr_iff {a b : BTZE0} :
    causalityYBTZ.lt U (.inr a) (.inr b) ↔ causalityBTZE0.lt (rightOpens U) a b := by
  show causality.lt (rightOpens (opensImage toPaperY U)) (toPaper a) (toPaper b) ↔ _
  rw [rightOpens_opensImage_toPaperY]; rfl

theorem le_inl_iff {a b : Causal.Minkowski 2} :
    causalityYBTZ.le U (.inl a) (.inl b) ↔ (Causal.minkowski 2).le (leftOpens U) a b := by
  show (Causal.minkowski 2).le (leftOpens (opensImage toPaperY U)) a b ↔ _
  rw [leftOpens_opensImage_toPaperY]

theorem lt_inl_iff {a b : Causal.Minkowski 2} :
    causalityYBTZ.lt U (.inl a) (.inl b) ↔ (Causal.minkowski 2).lt (leftOpens U) a b := by
  show (Causal.minkowski 2).lt (leftOpens (opensImage toPaperY U)) a b ↔ _
  rw [leftOpens_opensImage_toPaperY]

/-- The `𝕄`-chart of `Y` is a chart isomorphism. -/
theorem chartIso_e0Inl_symm : Causal.ChartIso causalityYBTZ (Causal.minkowski 2) e0Inl.symm := by
  intro V hV x hx y hy
  have hVs : (V : Set (Causal.Minkowski 2 ⊕ BTZE0)) ⊆ range Sum.inl := fun z hz => by
    have := hV hz; rwa [Causal.mem_chartSource, e0Inl_symm_source] at this
  obtain ⟨a, rfl⟩ := hVs hx
  obtain ⟨b, rfl⟩ := hVs hy
  have himg : Causal.chartImage e0Inl.symm V = leftOpens V := by
    ext m
    rw [Causal.coe_chartImage_of_le hV]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m', rfl⟩ := hVs hu
      rw [e0Inl_symm_inl]; exact hu
    · intro hm
      exact ⟨Sum.inl m, hm, e0Inl_symm_inl m⟩
  rw [himg, e0Inl_symm_inl, e0Inl_symm_inl, le_inl_iff, lt_inl_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem rightOpens_chartImage_e0Inr (V : Opens BTZE0) :
    rightOpens (Causal.chartImage e0Inr V) = V := by
  ext x
  show Sum.inr x ∈ e0Inr '' (e0Inr.source ∩ V) ↔ x ∈ V
  rw [e0Inr_source, univ_inter]
  constructor
  · rintro ⟨u, hu, he⟩
    rw [e0Inr_apply, Sum.inr.injEq] at he
    exact he ▸ hu
  · intro hx; exact ⟨x, hx, rfl⟩

theorem chartIso_e0Inr : Causal.ChartIso causalityBTZE0 causalityYBTZ e0Inr := by
  intro V _ x _ y _
  rw [e0Inr_apply, e0Inr_apply, le_inr_iff, lt_inr_iff, rightOpens_chartImage_e0Inr]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem chartIso_e0Inr_symm : Causal.ChartIso causalityYBTZ causalityBTZE0 e0Inr.symm := by
  intro V hV x hx y hy
  have hVs : (V : Set (Causal.Minkowski 2 ⊕ BTZE0)) ⊆ range Sum.inr := fun z hz => by
    have := hV hz; rwa [Causal.mem_chartSource, e0Inr_symm_source] at this
  obtain ⟨a, rfl⟩ := hVs hx
  obtain ⟨b, rfl⟩ := hVs hy
  have himg : Causal.chartImage e0Inr.symm V = rightOpens V := by
    ext m
    rw [Causal.coe_chartImage_of_le hV]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m', rfl⟩ := hVs hu
      rw [e0Inr_symm_inr]; exact hu
    · intro hm
      exact ⟨Sum.inr m, hm, e0Inr_symm_inr m⟩
  rw [himg, e0Inr_symm_inr, e0Inr_symm_inr, le_inr_iff, lt_inr_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- `𝔼₀` (paper coordinates) into `Y = 𝕄 ⊕ BTZE0`. -/
noncomputable def paperInY : OpenPartialHomeomorph E0 (Causal.Minkowski 2 ⊕ BTZE0) :=
  toPaper.symm.toOpenPartialHomeomorph.trans e0Inr

/-- `Y ⊇ BTZE0` to `𝔼₀` (paper coordinates). -/
noncomputable def paperOfY : OpenPartialHomeomorph (Causal.Minkowski 2 ⊕ BTZE0) E0 :=
  e0Inr.symm.trans toPaper.toOpenPartialHomeomorph

theorem chartIso_paperInY : Causal.ChartIso causality causalityYBTZ paperInY :=
  chartIso_trans (chartIso_transport_symm toPaper causality) chartIso_e0Inr

theorem chartIso_paperOfY : Causal.ChartIso causalityYBTZ causality paperOfY :=
  chartIso_trans chartIso_e0Inr_symm (chartIso_transport toPaper causality)

@[simp] theorem paperInY_apply (w : E0) : paperInY w = Sum.inr (toPaper.symm w) := rfl

@[simp] theorem paperOfY_inr (x : BTZE0) : paperOfY (Sum.inr x) = toPaper x := by
  simp [paperOfY]

@[simp] theorem paperInY_source : paperInY.source = univ := by
  simp [paperInY]

theorem paperOfY_source : paperOfY.source = range Sum.inr := by
  simp [paperOfY]

end ChartsY

/-! ### The charts of the maximal a.e. atlas of `BTZE0` are chart isomorphisms -/

section AeCharts

open TopologicalSpace

attribute [local instance] btzE0Structure

theorem toPaper_orbitMk_snd' (y : DInfty × ℝ) :
    (toPaper (orbitMk (GammaA (2 * π)) y)).2 = (starRingEnd ℂ) (DInfty.cplx (2 * π) y.1) := by
  show (paperCoords (cylHomeomorph btz_two_pi_ne_zero ℝ _)).2 = _
  rw [cylHomeomorph_apply]; rfl

/-- A point of Model's `𝔼₀` is regular iff it is off the axis in the paper's coordinates. -/
theorem mem_reg_iff_toPaper (x : BTZE0) :
    x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 ↔ toPaper x ∉ axis := by
  have key : ∀ y : DInfty × ℝ, (toPaper (orbitMk (GammaA (2 * π)) y)).2 ≠ 0 ↔ 0 < y.1.r := by
    intro y
    rw [toPaper_orbitMk_snd', Ne, map_eq_zero, ← norm_eq_zero, DInfty.norm_cplx]
    exact ⟨fun h => lt_of_le_of_ne y.1.r_nonneg (Ne.symm h), fun h => h.ne'⟩
  rw [btzE0_reg_eq]
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective x
  show _ ↔ (toPaper (Quotient.mk _ y)).2 ≠ 0
  constructor
  · rintro ⟨y', hy', he⟩
    have := (key y').2 hy'
    rwa [show orbitMk (GammaA (2 * π)) y' = Quotient.mk _ y from he] at this
  · intro h
    exact ⟨y, (key y).1 h, rfl⟩

/-- A point of `𝔼₀` off the axis, in the polar form `(τ, r e^{iθ})`, is the class of the cylinder
point `btzPaperCyl (τ, r, θ)`. -/
theorem toPaper_symm_eq_orbitMk {w : E0} (hw : w ∉ axis) {θ : ℝ} (hθ : Polar w θ) :
    toPaper.symm w = orbitMk (GammaA (2 * π)) (btzPaperCyl (w.1, rad w, θ)) := by
  have hr : 0 < rad w := rad_pos.2 hw
  apply toPaper.injective
  rw [Homeomorph.apply_symm_apply, btzPaperCyl_of_pos (p := (w.1, rad w, θ)) hr]
  have h2 : ((w.1, (rad w : ℂ) * cexp (θ * I)) : E0) = w := Prod.ext rfl hθ.symm
  exact ((toPaper_posEmb hr θ w.1).trans h2).symm

/-- The sector chart read on Model's `𝔼₀`. -/
noncomputable def sectorChartBTZ (y : E0) (hy : y.2 ≠ 0) :
    OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2) :=
  toPaper.toOpenPartialHomeomorph.trans (sectorChart y hy)

theorem chartIso_sectorChartBTZ {y : E0} (hy : y.2 ≠ 0) :
    Causal.ChartIso causalityBTZE0 (Causal.minkowski 2) (sectorChartBTZ y hy) :=
  chartIso_trans (chartIso_transport toPaper causality) (chartIso_sectorChart hy)

theorem causalityBTZE0_causallyArcConnected : causalityBTZE0.CausallyArcConnected :=
  transport_causallyArcConnected causallyArcConnected

/-- **The charts of `BTZE0`'s maximal a.e. atlas are chart isomorphisms** onto `𝕄`: near each
point such a chart is `g •` a sector chart (`btz_chart_eq_smul_btzPaperDev`). -/
theorem chartIso_aeAtlas {c : OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2)}
    (hc : c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) :
    Causal.ChartIso causalityBTZE0 (Causal.minkowski 2) c := by
  refine chartIso_of_isoNear (causalityBTZE0_causallyArcConnected.absolutelyMinimalOn_all)
    (Causal.minkowski_causallyArcConnected.absolutelyMinimalOn_all) fun x hx => ?_
  set y := toPaper x
  have hxr : x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
    mem_support.2 ⟨c, hc, hx⟩
  have hyax : y ∉ axis := (mem_reg_iff_toPaper x).1 hxr
  have hy : y.2 ≠ 0 := hyax
  set p : ℝ × ℝ × ℝ := (y.1, rad y, angle y y)
  have hpx : orbitMk (GammaA (2 * π)) (btzPaperCyl p) = x := by
    rw [← toPaper_symm_eq_orbitMk hyax (polar_angle hy y), Homeomorph.symm_apply_apply]
  obtain ⟨g, hg⟩ := btz_chart_eq_smul_btzPaperDev isBTZStructure_btzE0 hc
    (p := p) (rad_pos.2 hyax) (by rw [hpx]; exact hx)
  set φ : BTZE0 → ℝ × ℝ × ℝ := fun z => ((toPaper z).1, rad (toPaper z), angle y (toPaper z))
  have hφ : ContinuousAt φ x := by
    have hang : ContinuousAt (angle y) y :=
      (continuousOn_angle y).continuousAt ((isOpen_sector y).mem_nhds (mem_sector_self hy))
    have h3 : ContinuousAt (fun z => angle y (toPaper z)) x :=
      ContinuousAt.comp (g := angle y) (f := toPaper) hang toPaper.continuous.continuousAt
    exact (continuous_fst.comp toPaper.continuous).continuousAt.prodMk
      ((continuous_rad.comp toPaper.continuous).continuousAt.prodMk h3)
  have hev : ∀ᶠ z in 𝓝 x, z ∈ c.source ∧ toPaper z ∈ sector y ∧
      c z = g • sectorChartBTZ y hy z := by
    have h1 : ∀ᶠ z in 𝓝 x, c (orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z))) =
        g • btzPaperDev (φ z) := hφ.eventually hg
    have h2 : ∀ᶠ z in 𝓝 x, toPaper z ∈ sector y :=
      toPaper.continuous.continuousAt.preimage_mem_nhds
        ((isOpen_sector y).mem_nhds (mem_sector_self hy))
    filter_upwards [h1, h2, c.open_source.mem_nhds hx] with z hz1 hz2 hz3
    refine ⟨hz3, hz2, ?_⟩
    have hzax : toPaper z ∉ axis := not_mem_axis_of_mem_sector hz2
    have hz : orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z)) = z := by
      rw [← toPaper_symm_eq_orbitMk hzax (polar_angle hy (toPaper z)),
        Homeomorph.symm_apply_apply]
    rw [hz] at hz1
    rw [hz1]
    show g • btzPaperDev (φ z) = g • chartMap y (toPaper z)
    rw [chartMap_eq]
  set O : Opens BTZE0 := ⟨interior {z | z ∈ c.source ∧ toPaper z ∈ sector y ∧
      c z = g • sectorChartBTZ y hy z}, isOpen_interior⟩
  have hO : O ≤ Causal.chartSource (sectorChartBTZ y hy) ⊓ Causal.chartSource c := by
    intro z hz
    obtain ⟨h1, h2, -⟩ := interior_subset hz
    refine ⟨?_, h1⟩
    show z ∈ (toPaper.toOpenPartialHomeomorph.trans (sectorChart y hy)).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨trivial, h2⟩
  have hagree := Causal.ChartIso.agreeOn_of_smul Causal.Flat.isom_strongMorphism
    (chartIso_sectorChartBTZ hy) ((Causal.minkowski 2).chartTransport_chartIso c) hO
    (fun z hz => (interior_subset hz).2.2)
  exact ⟨O, mem_interior_iff_mem_nhds.2 hev, hO.trans inf_le_right,
    isoNear_of_agreeOn hagree (hO.trans inf_le_right)⟩

/-- **The regular charts of `Y = 𝕄 ⊕ BTZE0`** (Rigid's `e0Atlas`) are chart isomorphisms. -/
theorem chartIso_e0Atlas {c : OpenPartialHomeomorph (Causal.Minkowski 2 ⊕ BTZE0)
    (Causal.Minkowski 2)} (hc : c ∈ e0Atlas) :
    Causal.ChartIso causalityYBTZ (Causal.minkowski 2) c := by
  rcases mem_e0Atlas.1 hc with rfl | ⟨c', hc', rfl⟩
  · exact chartIso_e0Inl_symm
  · exact chartIso_trans chartIso_e0Inr_symm (chartIso_aeAtlas hc')

end AeCharts

/-! ### Curves through the BTZ line under a homeomorphism regular off it -/

section AxisCurves

open TopologicalSpace

variable {F : OpenPartialHomeomorph E0 E0}

theorem Lt.not_mem_axis {x y : E0} (h : Lt x y) : y ∉ axis := fun hy => by
  obtain ⟨hx, -⟩ := (le_axis_iff' hy).1 h.le
  have := ((lt_axis_iff hx).1 h).1
  rw [rad_eq_zero.2 hy] at this
  exact lt_irrefl _ this

theorem chartImage_symm_chartImage {e : OpenPartialHomeomorph E0 E0} {V : Opens E0}
    (hV : V ≤ Causal.chartSource e) :
    Causal.chartImage e.symm (Causal.chartImage e V) = V := by
  have hV' : Causal.chartImage e V ≤ Causal.chartSource e.symm := by
    intro p hp
    obtain ⟨z, hz, -, rfl, -⟩ := Causal.exists_of_mem_chartImage hp
    exact e.map_source hz
  apply SetLike.coe_injective
  rw [Causal.coe_chartImage_of_le hV', Causal.coe_chartImage_of_le hV, image_image]
  conv_rhs => rw [← image_id (V : Set E0)]
  exact image_congr fun z hz => e.left_inv (hV hz)

variable (hreg : ∀ x ∈ F.source, x ∉ axis → ∃ O : Opens E0, x ∈ O ∧
  O ≤ Causal.chartSource F ∧ IsoNear causality causality F O)
include hreg

/-- Near a parameter where a causal curve is off the axis, its image is `≼`-increasing. -/
theorem regular_window_le {V : Opens E0} (hV : V ≤ Causal.chartSource F) {γ : ℝ → E0} {a b : ℝ}
    (hc : Causal.CurveOn (relOn Le) V γ a b) {t : ℝ} (ht : t ∈ Icc a b) (hγt : γ t ∉ axis) :
    ∃ l u, l < t ∧ t < u ∧ ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, l < s → s < s' → s' < u →
      Le (F (γ s)) (F (γ s')) := by
  obtain ⟨O, hxO, -, hiso⟩ := hreg (γ t) (hV (hc.mem t ht)) hγt
  set W : Opens E0 := O ⊓ V
  have hpre : γ ⁻¹' W ∈ 𝓝[Icc a b] t :=
    (hc.continuousOn isRelFamily_le) t ht (W.isOpen.mem_nhds ⟨hxO, hc.mem t ht⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
  have hmem : ∀ τ ∈ Icc s s', γ τ ∈ W := fun τ hτ => hball
    ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2],
      ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩⟩
  have hW : causality.le W (γ s) (γ s') :=
    ⟨s, s', h2.le, γ, hc.restrict hs.1 hs'.2 inf_le_right hmem, rfl, rfl⟩
  exact le_of_le (((hiso W inf_le_left (γ s) (hmem s ⟨le_rfl, h2.le⟩) (γ s')
    (hmem s' ⟨h2.le, le_rfl⟩)).1).1 hW)

/-- Near a parameter where a chronological curve is off the axis, its image is `≺`-increasing. -/
theorem regular_window_lt {V : Opens E0} (hV : V ≤ Causal.chartSource F) {γ : ℝ → E0} {a b : ℝ}
    (hc : Causal.CurveOn (relOn Lt) V γ a b) {t : ℝ} (ht : t ∈ Icc a b) (hγt : γ t ∉ axis) :
    ∃ l u, l < t ∧ t < u ∧ ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, l < s → s < s' → s' < u →
      Lt (F (γ s)) (F (γ s')) := by
  obtain ⟨O, hxO, -, hiso⟩ := hreg (γ t) (hV (hc.mem t ht)) hγt
  set W : Opens E0 := O ⊓ V
  have hpre : γ ⁻¹' W ∈ 𝓝[Icc a b] t :=
    (hc.continuousOn isRelFamily_lt) t ht (W.isOpen.mem_nhds ⟨hxO, hc.mem t ht⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
  have hmem : ∀ τ ∈ Icc s s', γ τ ∈ W := fun τ hτ => hball
    ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2],
      ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩⟩
  have hW : causality.lt W (γ s) (γ s') :=
    ⟨s, s', h2, γ, hc.restrict hs.1 hs'.2 inf_le_right hmem, rfl, rfl⟩
  exact lt_of_lt (((hiso W inf_le_left (γ s) (hmem s ⟨le_rfl, h2.le⟩) (γ s')
    (hmem s' ⟨h2.le, le_rfl⟩)).2).1 hW)

/-- A causal curve off the axis has a `≼`-increasing image. -/
theorem regular_curve_le {V : Opens E0} (hV : V ≤ Causal.chartSource F) {γ : ℝ → E0} {a b : ℝ}
    (hc : Causal.CurveOn (relOn Le) V γ a b) (hoff : ∀ s ∈ Icc a b, γ s ∉ axis) {s s' : ℝ}
    (hs : a ≤ s) (hss' : s < s') (hs' : s' ≤ b) : Le (F (γ s)) (F (γ s')) := by
  have hcont : ContinuousOn (fun t => F (γ t)) (Icc a b) :=
    F.continuousOn.comp (hc.continuousOn isRelFamily_le) fun t ht => hV (hc.mem t ht)
  have himg : Causal.CurveOn (relOn Le) ⊤ (fun t => F (γ t)) a b :=
    curveOn_of_local hcont (fun _ _ => trivial)
      fun t ht => regular_window_le hreg hV hc ht (hoff t ht)
  exact (himg.rel_of_lt isRelFamily_le hs hss' hs').2.2

/-- A chronological curve off the axis has a `≺`-increasing image. -/
theorem regular_curve_lt {V : Opens E0} (hV : V ≤ Causal.chartSource F) {γ : ℝ → E0} {a b : ℝ}
    (hc : Causal.CurveOn (relOn Lt) V γ a b) (hoff : ∀ s ∈ Icc a b, γ s ∉ axis) {s s' : ℝ}
    (hs : a ≤ s) (hss' : s < s') (hs' : s' ≤ b) : Lt (F (γ s)) (F (γ s')) := by
  have hcont : ContinuousOn (fun t => F (γ t)) (Icc a b) :=
    F.continuousOn.comp (hc.continuousOn isRelFamily_lt) fun t ht => hV (hc.mem t ht)
  have himg : Causal.CurveOn (relOn Lt) ⊤ (fun t => F (γ t)) a b :=
    curveOn_of_local hcont (fun _ _ => trivial)
      fun t ht => regular_window_lt hreg hV hc ht (hoff t ht)
  exact (himg.rel_of_lt isRelFamily_lt hs hss' hs').2.2

/-- **The limit at the axis**: a causal curve leaving the axis at its start has a causally related
image of its ends (`J⁻` is closed). -/
theorem le_ends_of_leaves {V : Opens E0} (hV : V ≤ Causal.chartSource F) {γ : ℝ → E0} {a b : ℝ}
    (hc : Causal.CurveOn (relOn Le) V γ a b) (hab : a < b) (hoff : ∀ s ∈ Ioc a b, γ s ∉ axis) :
    Le (F (γ a)) (F (γ b)) := by
  have hcont : ContinuousOn (fun t => F (γ t)) (Icc a b) :=
    F.continuousOn.comp (hc.continuousOn isRelFamily_le) fun t ht => hV (hc.mem t ht)
  have hS := isClosed_Jminus (F (γ b))
  have hsub : (fun t => F (γ t)) '' Ioo a b ⊆ causality.Jminus ⊤ {F (γ b)} := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [Causal.Precausality.mem_Jminus_singleton, le_top_iff]
    exact regular_curve_le hreg hV (hc.restrict hσ.1.le le_rfl le_rfl
      fun t ht => hc.mem t ⟨hσ.1.le.trans ht.1, ht.2⟩)
      (fun t ht => hoff t ⟨hσ.1.trans_le ht.1, ht.2⟩) le_rfl hσ.2 le_rfl
  have hcl : F (γ a) ∈ closure ((fun t => F (γ t)) '' Ioo a b) :=
    ((hcont a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self).mem_closure_image
      (by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩)
  have := hS.closure_subset_iff.2 hsub hcl
  rwa [Causal.Precausality.mem_Jminus_singleton, le_top_iff] at this

variable (hax : ∀ x ∈ F.source, F x ∈ axis ↔ x ∈ axis)
include hax

/-- **Orientation along the axis**: near a BTZ point, `F` preserves the order of `τ` on the axis
(a chronological ray leaving `p₂` and the closedness of `J^±` force `F p₁ ≼ F p₂`). -/
theorem orientation_axis {p₀ : E0} (hp₀ : p₀ ∈ F.source) :
    ∃ δ > 0, Metric.ball p₀ δ ⊆ F.source ∧ ∀ p₁ ∈ Metric.ball p₀ δ, ∀ p₂ ∈ Metric.ball p₀ δ,
      p₁ ∈ axis → p₂ ∈ axis → p₁.1 ≤ p₂.1 → (F p₁).1 ≤ (F p₂).1 := by
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 F.open_source p₀ hp₀
  refine ⟨δ₀ / 10, by positivity, (Metric.ball_subset_ball (by linarith)).trans hball,
    fun p₁ hp₁ p₂ hp₂ hax₁ hax₂ h12 => ?_⟩
  set B₀ : Opens E0 := ⟨Metric.ball p₀ δ₀, Metric.isOpen_ball⟩
  have hB₀ : B₀ ≤ Causal.chartSource F := hball
  -- the image of a chronological future point of `p₂`
  have key : ∀ q, Lt p₂ q → dist q p₂ < δ₀ / 10 → Le (F p₁) (F q) := by
    intro q hq hqd
    have h1q : Le p₁ q := (le_axis hax₁ hax₂ h12).trans hq.le
    obtain ⟨θ₁, θ₂, hp₁θ, hqθ, hN⟩ := h1q
    set P := lift p₁ θ₁
    set Q := lift q θ₂
    have hqax : q ∉ axis := hq.not_mem_axis
    have hP0 : P.2.1 = 0 := rad_eq_zero.2 hax₁
    have hQ : Q.2.1 = rad q := rfl
    have hmem : ∀ s ∈ Icc (0 : ℝ) 1, unlift (seg P Q s) ∈ B₀ := by
      intro s hs
      obtain ⟨hl, hr⟩ := le_seg_ends (adm_lift p₁ θ₁) hN hs
      rw [unlift_lift hp₁θ] at hl
      rw [unlift_lift hqθ] at hr
      have d1 := hl.dist_le
      have d2 := hr.closed.1
      have d3 := (le_abs_self _).trans (abs_fst_sub_le_dist q p₂)
      have d4 := (le_abs_self _).trans (abs_fst_sub_le_dist p₂ p₀)
      have d5 := (neg_le_abs _).trans (abs_fst_sub_le_dist p₁ p₀)
      rw [Metric.mem_ball] at hp₁ hp₂
      show dist (unlift (seg P Q s)) p₀ < δ₀
      have := dist_triangle (unlift (seg P Q s)) p₁ p₀
      rw [dist_comm] at d1
      linarith
    have hc := curveOn_unlift_seg (adm_lift p₁ θ₁) hN hmem
    have hoff : ∀ s ∈ Ioc (0 : ℝ) 1, unlift (seg P Q s) ∉ axis := by
      intro s hs
      rw [← rad_pos, rad_unlift (adm_seg (adm_lift p₁ θ₁) hN hs.1.le).nonneg, seg_snd_fst, hP0,
        hQ]
      have := rad_pos.2 hqax
      nlinarith [hs.1]
    have := le_ends_of_leaves hreg hB₀ hc zero_lt_one hoff
    simp only [seg_zero, seg_one, unlift_lift hp₁θ] at this
    rwa [show unlift Q = q from unlift_lift hqθ] at this
  -- `p₂` is a limit of such points
  have hp₂s : p₂ ∈ F.source := hball (Metric.ball_subset_ball (by linarith) hp₂)
  set T : Set E0 := {q | Lt p₂ q ∧ dist q p₂ < δ₀ / 10}
  have hT : p₂ ∈ closure T := by
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨q, hq, hlt⟩ := exists_lt_mem p₂ (inter_mem hN (Metric.ball_mem_nhds p₂
      (show (0 : ℝ) < δ₀ / 10 by positivity)))
    exact ⟨q, hq.1, hlt, hq.2⟩
  have hcl := (F.continuousAt hp₂s).continuousWithinAt.mem_closure_image hT
  have hsub : F '' T ⊆ causality.Jplus ⊤ {F p₁} := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Causal.Precausality.mem_Jplus_singleton, le_top_iff]
    exact key q hq.1 hq.2
  have hle := (isClosed_Jplus (F p₁)).closure_subset_iff.2 hsub hcl
  rw [Causal.Precausality.mem_Jplus_singleton, le_top_iff] at hle
  exact ((le_axis_iff' ((hax p₂ hp₂s).2 hax₂)).1 hle).2

/-- **The image of a causal curve is a causal curve**, also through the axis. -/
theorem cle_image {V : Opens E0} (hV : V ≤ Causal.chartSource F) {x y : E0} (h : CLe V x y) :
    CLe (Causal.chartImage F V) (F x) (F y) := by
  obtain ⟨a, b, hab, γ, hc, rfl, rfl⟩ := h
  have hcont : ContinuousOn (fun t => F (γ t)) (Icc a b) :=
    F.continuousOn.comp (hc.continuousOn isRelFamily_le) fun t ht => hV (hc.mem t ht)
  refine ⟨a, b, hab, fun t => F (γ t), curveOn_of_local hcont
    (fun t ht => Causal.mem_chartImage_of_mem (hV (hc.mem t ht)) (hc.mem t ht))
    (fun t ht => ?_), rfl, rfl⟩
  by_cases hγt : γ t ∈ axis
  swap
  · exact regular_window_le hreg hV hc ht hγt
  obtain ⟨δ, hδ, hδs, hor⟩ := orientation_axis hreg hax (hV (hc.mem t ht))
  have hpre : γ ⁻¹' Metric.ball (γ t) δ ∈ 𝓝[Icc a b] t :=
    (hc.continuousOn isRelFamily_le) t ht (Metric.ball_mem_nhds _ hδ)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨t - ε, t + ε, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
  have hB : ∀ τ ∈ Icc s s', γ τ ∈ Metric.ball (γ t) δ := fun τ hτ => hball
    ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2],
      ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩⟩
  have hsrc : ∀ τ ∈ Icc a b, γ τ ∈ F.source := fun τ hτ => hV (hc.mem τ hτ)
  -- along the axis part, the orientation
  have haxis : ∀ σ ∈ Icc s s', ∀ σ' ∈ Icc s s', σ ≤ σ' → γ σ' ∈ axis →
      Le (F (γ σ)) (F (γ σ')) := by
    intro σ hσ σ' hσ' hle hσ'ax
    have hσab : σ ∈ Icc a b := ⟨hs.1.trans hσ.1, hσ.2.trans hs'.2⟩
    have hσ'ab : σ' ∈ Icc a b := ⟨hs.1.trans hσ'.1, hσ'.2.trans hs'.2⟩
    have hLe : Le (γ σ) (γ σ') := by
      rcases hle.lt_or_eq with hlt | heq
      · exact (hc.rel_of_lt isRelFamily_le hσab.1 hlt hσ'ab.2).2.2
      · rw [heq]; exact le_refl' _
    obtain ⟨hσax, hτ⟩ := (le_axis_iff' hσ'ax).1 hLe
    exact le_axis ((hax _ (hsrc σ hσab)).2 hσax) ((hax _ (hsrc σ' hσ'ab)).2 hσ'ax)
      (hor _ (hB σ hσ) _ (hB σ' hσ') hσax hσ'ax hτ)
  have hss : s ∈ Icc s s' := ⟨le_rfl, h2.le⟩
  have hss' : s' ∈ Icc s s' := ⟨h2.le, le_rfl⟩
  by_cases hs'ax : γ s' ∈ axis
  · exact haxis s hss s' hss' h2.le hs'ax
  set A : Set ℝ := Icc s s' ∩ γ ⁻¹' axis
  by_cases hA : A.Nonempty
  swap
  · have hoff : ∀ τ ∈ Icc s s', γ τ ∉ axis := fun τ hτ hτax => hA ⟨τ, hτ, hτax⟩
    exact regular_curve_le hreg hV (hc.restrict hs.1 hs'.2 le_rfl
      fun τ hτ => hc.mem τ ⟨hs.1.trans hτ.1, hτ.2.trans hs'.2⟩) hoff le_rfl h2 le_rfl
  have hAc : IsClosed A :=
    ((hc.continuousOn isRelFamily_le).mono (Icc_subset_Icc hs.1 hs'.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_axis
  have hAb : BddAbove A := ⟨s', fun τ hτ => hτ.1.2⟩
  set t₁ := sSup A
  have ht₁ : t₁ ∈ A := hAc.csSup_mem hA hAb
  have ht₁s' : t₁ < s' := lt_of_le_of_ne ht₁.1.2 fun h => hs'ax (h ▸ ht₁.2)
  have hoff : ∀ τ ∈ Ioc t₁ s', γ τ ∉ axis := fun τ hτ hτax =>
    absurd (le_csSup hAb ⟨⟨ht₁.1.1.trans hτ.1.le, hτ.2⟩, hτax⟩) (not_le.2 hτ.1)
  have h1' := haxis s hss t₁ ht₁.1 ht₁.1.1 ht₁.2
  have h2' := le_ends_of_leaves hreg hV (hc.restrict (hs.1.trans ht₁.1.1) hs'.2 le_rfl
    fun τ hτ => hc.mem τ ⟨(hs.1.trans ht₁.1.1).trans hτ.1, hτ.2.trans hs'.2⟩) ht₁s' hoff
  exact h1'.trans h2'

omit hax in
/-- **The image of a chronological curve is a chronological curve**, also from the axis. -/
theorem clt_image {V : Opens E0} (hV : V ≤ Causal.chartSource F) {x y : E0} (h : CLt V x y) :
    CLt (Causal.chartImage F V) (F x) (F y) := by
  obtain ⟨a, b, hab, γ, hc, rfl, rfl⟩ := h
  have hcont : ContinuousOn (fun t => F (γ t)) (Icc a b) :=
    F.continuousOn.comp (hc.continuousOn isRelFamily_lt) fun t ht => hV (hc.mem t ht)
  have hcle : Causal.CurveOn (relOn Le) V γ a b :=
    curveOn_mono_rel (fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.le⟩) hc
  have hoff : ∀ s ∈ Ioc a b, γ s ∉ axis := fun s hs =>
    (hc.rel_of_lt isRelFamily_lt le_rfl hs.1 hs.2).2.2.not_mem_axis
  have hglob : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s < s' → Lt (F (γ s)) (F (γ s')) := by
    intro s hs s' hs' hss'
    have hrest : ∀ {σ σ' : ℝ}, a < σ → σ < σ' → σ' ≤ b → Lt (F (γ σ)) (F (γ σ')) :=
      fun {σ σ'} hσ hσσ' hσ' => regular_curve_lt hreg hV (hc.restrict hσ.le hσ' le_rfl
        fun τ hτ => hc.mem τ ⟨hσ.le.trans hτ.1, hτ.2.trans hσ'⟩)
        (fun τ hτ => hoff τ ⟨hσ.trans_le hτ.1, hτ.2.trans hσ'⟩) le_rfl hσσ' le_rfl
    rcases hs.1.lt_or_eq with has | has
    · exact hrest has hss' hs'.2
    · subst has
      set σ := (a + s') / 2
      have h1 : a < σ := by simp only [σ]; linarith
      have h2 : σ < s' := by simp only [σ]; linarith
      have hle := le_ends_of_leaves hreg hV (hcle.restrict le_rfl (h2.le.trans hs'.2) le_rfl
        fun τ hτ => hcle.mem τ ⟨hτ.1, hτ.2.trans (h2.le.trans hs'.2)⟩) h1
        (fun τ hτ => hoff τ ⟨hτ.1, hτ.2.trans (h2.le.trans hs'.2)⟩)
      exact hle.trans_lt (hrest h1 h2 hs'.2)
  refine ⟨a, b, hab, fun t => F (γ t), curveOn_of_local hcont
    (fun t ht => Causal.mem_chartImage_of_mem (hV (hc.mem t ht)) (hc.mem t ht))
    (fun t _ => ⟨a - 1, b + 1, by linarith [‹t ∈ Icc a b›.1], by linarith [‹t ∈ Icc a b›.2],
      fun s hs s' hs' _ h _ => hglob s hs s' hs' h⟩), rfl, rfl⟩

/-- **A partial homeomorphism of `𝔼₀` preserving the axis and a chart isomorphism near every
regular point is a chart isomorphism**, BTZ points included. -/
theorem chartIso_of_axis : Causal.ChartIso causality causality F := by
  have hax' : ∀ x ∈ F.symm.source, F.symm x ∈ axis ↔ x ∈ axis := fun x hx => by
    have h := hax (F.symm x) (F.map_target hx)
    rw [F.right_inv hx] at h
    exact h.symm
  have hreg' : ∀ x ∈ F.symm.source, x ∉ axis → ∃ O : Opens E0, x ∈ O ∧
      O ≤ Causal.chartSource F.symm ∧ IsoNear causality causality F.symm O := by
    intro x hx hxax
    have hz : F.symm x ∈ F.source := F.map_target hx
    obtain ⟨O, hzO, hOs, hiso⟩ := hreg (F.symm x) hz fun h => hxax ((hax' x hx).1 h)
    refine ⟨Causal.chartImage F O, ?_, ?_, hiso.symm hOs⟩
    · have := Causal.mem_chartImage_of_mem hz hzO
      rwa [F.right_inv hx] at this
    · intro p hp
      obtain ⟨z, hz', -, rfl, -⟩ := Causal.exists_of_mem_chartImage hp
      exact F.map_source hz'
  intro V hV x hx y hy
  have hV' : Causal.chartImage F V ≤ Causal.chartSource F.symm := by
    intro p hp
    obtain ⟨z, hz', -, rfl, -⟩ := Causal.exists_of_mem_chartImage hp
    exact F.map_source hz'
  have hback : ∀ {p q : E0}, p ∈ V → q ∈ V →
      (CLe (Causal.chartImage F V) (F p) (F q) → CLe V p q) ∧
        (CLt (Causal.chartImage F V) (F p) (F q) → CLt V p q) := by
    intro p q hp hq
    have e1 := chartImage_symm_chartImage hV
    have ep := F.left_inv (hV hp)
    have eq := F.left_inv (hV hq)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := cle_image (F := F.symm) hreg' hax' hV' h
      rwa [e1, ep, eq] at this
    · have := clt_image (F := F.symm) hreg' hV' h
      rwa [e1, ep, eq] at this
  exact ⟨⟨cle_image hreg hax hV, (hback hx hy).1⟩, ⟨clt_image hreg hV, (hback hx hy).2⟩⟩

end AxisCurves

/-! ### `chartIso_mem`: the elements of `G` are chart isomorphisms of `𝕄 ⊕ BTZE0` -/

section ChartIsoMem

open TopologicalSpace

attribute [local instance] btzE0Structure

/-- At a regular point an element of `G` is, near the point, `c'⁻¹ ∘ g ∘ c` for regular charts
`c`, `c'` and `g ∈ Isom(𝐌³)`: a chart isomorphism near the point. -/
theorem isoNear_of_mem_e0Groupoid_reg {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid)
    {x : E0Y} (hx : x ∈ e.source) (hxr : x ∈ e0Reg) :
    ∃ O : Opens E0Y, x ∈ O ∧ O ≤ Causal.chartSource e ∧
      IsoNear causalityYBTZ causalityYBTZ e O := by
  obtain ⟨hcont, hreg⟩ := (mem_e0Groupoid_iff.1 he).1 x hx
  obtain ⟨hex, hch⟩ := hreg hxr
  obtain ⟨c, hc, hxc⟩ := mem_support.1 hxr
  obtain ⟨c', hc', hexc⟩ := mem_support.1 hex
  obtain ⟨g, hg⟩ := hch c hc c' hc' hxc hexc
  have hev : ∀ᶠ z in 𝓝 x, z ∈ c.source ∧ z ∈ e.source ∧ e z ∈ c'.source ∧
      c' (e z) = g • c z := by
    filter_upwards [c.open_source.mem_nhds hxc, e.open_source.mem_nhds hx,
      hcont.preimage_mem_nhds (c'.open_source.mem_nhds hexc), hg] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  set O : Opens E0Y := ⟨interior {z | z ∈ c.source ∧ z ∈ e.source ∧ e z ∈ c'.source ∧
      c' (e z) = g • c z}, isOpen_interior⟩
  have hO : O ≤ Causal.chartSource c ⊓ Causal.chartSource e := fun z hz =>
    ⟨(interior_subset hz).1, (interior_subset hz).2.1⟩
  have hagree := Causal.ChartIso.agreeOn_of_regular Causal.Flat.isom_strongMorphism
    (chartIso_e0Atlas hc) (causalityYBTZ.chartTransport_chartIso e) (chartIso_e0Atlas hc') hO
    fun z hz => ⟨(interior_subset hz).2.2.1, (interior_subset hz).2.2.2⟩
  exact ⟨O, mem_interior_iff_mem_nhds.2 hev, hO.trans inf_le_right,
    isoNear_of_agreeOn hagree (hO.trans inf_le_right)⟩

/-- An element of `G` read in the paper's coordinates of `𝔼₀`. -/
noncomputable def paperConj (e : OpenPartialHomeomorph E0Y E0Y) : OpenPartialHomeomorph E0 E0 :=
  paperInY.trans (e.trans paperOfY)

theorem paperConj_apply (e : OpenPartialHomeomorph E0Y E0Y) (w : E0) :
    paperConj e w = paperOfY (e (paperInY w)) := rfl

theorem mem_paperConj_source {e : OpenPartialHomeomorph E0Y E0Y} {w : E0} :
    w ∈ (paperConj e).source ↔ paperInY w ∈ e.source ∧ e (paperInY w) ∈ range Sum.inr := by
  simp only [paperConj, OpenPartialHomeomorph.trans_source, paperInY_source, univ_inter,
    mem_preimage, mem_inter_iff, paperOfY_source]

theorem paperInY_paperOfY {z : E0Y} (hz : z ∈ range Sum.inr) : paperInY (paperOfY z) = z := by
  obtain ⟨u, rfl⟩ := hz
  rw [paperOfY_inr, paperInY_apply, Homeomorph.symm_apply_apply]

theorem inr_mem_e0Reg_iff_toPaper {u : BTZE0} : (Sum.inr u : E0Y) ∈ e0Reg ↔ toPaper u ∉ axis := by
  rw [inr_mem_e0Reg_iff, mem_reg_iff_toPaper]

theorem paperInY_mem_e0Reg_iff {w : E0} : paperInY w ∈ e0Reg ↔ w ∉ axis := by
  rw [paperInY_apply, inr_mem_e0Reg_iff_toPaper, Homeomorph.apply_symm_apply]

/-- **An element of `G`, read in `𝔼₀`'s coordinates, is a chart isomorphism**, BTZ points
included. -/
theorem chartIso_paperConj {e : OpenPartialHomeomorph E0Y E0Y} (he : e ∈ e0Groupoid) :
    Causal.ChartIso causality causality (paperConj e) := by
  have hreg : ∀ x ∈ (paperConj e).source, x ∉ axis → ∃ O : Opens E0, x ∈ O ∧
      O ≤ Causal.chartSource (paperConj e) ∧ IsoNear causality causality (paperConj e) O := by
    intro w hw hwax
    obtain ⟨hw1, hw2⟩ := mem_paperConj_source.1 hw
    obtain ⟨O, hxO, hOs, hiso⟩ :=
      isoNear_of_mem_e0Groupoid_reg he hw1 (paperInY_mem_e0Reg_iff.2 hwax)
    set O₁ : Opens E0Y := O ⊓ Causal.chartSource (e.trans paperOfY)
    have hiso₁ : IsoNear causalityYBTZ causality (e.trans paperOfY) O₁ := by
      refine IsoNear.trans (hiso.mono inf_le_left) (isoNear_of_chartIso chartIso_paperOfY le_rfl)
        inf_le_right ?_
      intro p hp
      obtain ⟨z, -, hz, rfl, -⟩ := Causal.exists_of_mem_chartImage hp
      exact hz.2.2
    have hcont : Continuous paperInY := continuous_inr.comp toPaper.symm.continuous
    set O₂ : Opens E0 := Causal.chartSource (paperConj e) ⊓ ⟨paperInY ⁻¹' O₁, O₁.isOpen.preimage hcont⟩
    refine ⟨O₂, ⟨hw, hxO, ?_⟩, inf_le_left, ?_⟩
    · show paperInY w ∈ (e.trans paperOfY).source
      rw [OpenPartialHomeomorph.trans_source, paperOfY_source]; exact ⟨hw1, hw2⟩
    · refine IsoNear.trans (isoNear_of_chartIso chartIso_paperInY fun z _ => by
        show z ∈ paperInY.source; rw [paperInY_source]; trivial) hiso₁ inf_le_left ?_
      intro p hp
      obtain ⟨z, -, hz, rfl, -⟩ := Causal.exists_of_mem_chartImage hp
      exact hz.2
  have hax : ∀ x ∈ (paperConj e).source, paperConj e x ∈ axis ↔ x ∈ axis := by
    intro w hw
    obtain ⟨hw1, ⟨u, hu⟩⟩ := mem_paperConj_source.1 hw
    have h := mem_e0Reg_iff_of_mem he hw1
    rw [paperInY_mem_e0Reg_iff, ← hu, inr_mem_e0Reg_iff_toPaper] at h
    rw [paperConj_apply, ← hu, paperOfY_inr]
    exact not_iff_not.1 h.symm
  exact chartIso_of_axis hreg hax

/-- **`LocalModel.chartIso_mem` for `𝔐E₀`** (`Y = 𝕄 ⊕ BTZE0`, `G = GX.e0Groupoid`, the causality
`GX.E0.causalityYBTZ`): every element of `G` is a chart isomorphism, at the BTZ points included.
At a regular point it is `c'⁻¹ ∘ g ∘ c` (`isoNear_of_mem_e0Groupoid_reg`); at a BTZ point it is
read in `𝔼₀`'s coordinates (`chartIso_paperConj`); the two are glued by absolute minimality
(`chartIso_of_isoNear`). -/
theorem chartIso_mem_e0Groupoid :
    ∀ e ∈ e0Groupoid, Causal.ChartIso causalityYBTZ causalityYBTZ e := by
  intro e he
  refine chartIso_of_isoNear absolutelyMinimalOn_YBTZ absolutelyMinimalOn_YBTZ fun x hx => ?_
  by_cases hxr : x ∈ e0Reg
  · exact isoNear_of_mem_e0Groupoid_reg he hx hxr
  have hexr : e x ∉ e0Reg := fun h => hxr ((mem_e0Reg_iff_of_mem he hx).2 h)
  have hinr : ∀ {z : E0Y}, z ∉ e0Reg → z ∈ range Sum.inr := fun {z} hz => by
    rcases z with m | u
    · exact absurd (inl_mem_e0Reg m) hz
    · exact ⟨u, rfl⟩
  set e' := paperOfY.trans ((paperConj e).trans paperInY)
  have hiso : Causal.ChartIso causalityYBTZ causalityYBTZ e' :=
    chartIso_trans chartIso_paperOfY (chartIso_trans (chartIso_paperConj he) chartIso_paperInY)
  set O : Opens E0Y := Causal.chartSource (e.trans paperOfY) ⊓ Causal.chartSource paperOfY
  have hOe : O ≤ Causal.chartSource e := fun z hz => hz.1.1
  have hsrc : ∀ {z : E0Y}, z ∈ Causal.chartSource paperOfY → z ∈ range Sum.inr := fun {z} h => by
    have h' : z ∈ paperOfY.source := h
    rwa [paperOfY_source] at h'
  have hsrc' : ∀ {z : E0Y}, z ∈ paperOfY.source → z ∈ range Sum.inr := fun {z} h => by
    rwa [paperOfY_source] at h
  have hOe' : O ≤ Causal.chartSource e' := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
    have hz3' := hsrc hz3
    have hz2' : e z ∈ range Sum.inr := hsrc' hz2
    show z ∈ (paperOfY.trans ((paperConj e).trans paperInY)).source
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source, paperInY_source]
    refine ⟨hz3, ?_, trivial⟩
    rw [mem_paperConj_source, paperInY_paperOfY hz3']
    exact ⟨hz1, hz2'⟩
  have heq : ∀ z ∈ O, e' z = e z := by
    intro z hz
    obtain ⟨⟨-, hz2⟩, hz3⟩ := hz
    have hz3' := hsrc hz3
    have hz2' : e z ∈ range Sum.inr := hsrc' hz2
    show paperInY (paperConj e (paperOfY z)) = e z
    rw [paperConj_apply, paperInY_paperOfY hz3', paperInY_paperOfY hz2']
  refine ⟨O, ⟨⟨hx, ?_⟩, ?_⟩, hOe, ?_⟩
  · show e x ∈ paperOfY.source
    rw [paperOfY_source]; exact hinr hexr
  · show x ∈ paperOfY.source
    rw [paperOfY_source]; exact hinr hxr
  · exact (isoNear_of_chartIso hiso hOe').congr hOe' hOe heq

end ChartIsoMem

end E0

end GX
