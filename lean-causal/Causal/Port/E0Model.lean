import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Basic
import Causal.Flat.Form

/-!
# The BTZ model space `E₀ = ℝ × ℂ` in the paper's coordinates, and its null structure

Target `T-ett-port-e0` (DEC-134), the first of three modules (`Causal.Port.E0Model`,
`Causal.Port.E0Causality`, `Causal.Port.E0Axioms`). **No label is marked here.**
Cited, unmarked: `defi:causal_E0` — `ETT.tex:1344` (assembled and scoped in
`Causal.Port.E0Axioms`).

> For $\alpha>0$, $\mass{\alpha}$ is Minkowski space $\mass{}=\E^{1,2}$ with a cone singularity of
> angle $\alpha$ along a timelike line [...] The space $\mass{0}$ is the extreme BTZ model, with
> metric $-\d \tau^2+\d \r^2+\r^2\d \theta^2$ in coordinates $(\tau,\r,\theta)$; its singular locus
> $\{\r=0\}$ is a lightlike line. We write $\sing(\mass{\alpha})$ for the singular line and
> $\reg(\mass{\alpha})$ for its complement, which is an $(\isom(\mass{}),\mass{})$-manifold.
> (`ETT.tex:1327–1333`)

**Ported from `lean-gx/GX/BTZ/Causality.lean` at commit `c48aa45`** (gx package WP-41e), the
part of l.116–1647 that involves no causal relation; the rest is in `E0Causality` and `E0Axioms`.
`lean-causal` never imports `lean-gx` (gx imports `Causal`, DEC-33), so the code is copied.
Every declaration `GX.E0.x` of that range is `Causal.E0.x` here, with gx's statement and proof
character for character, except:

1. **Restated from `lean-gx/GX/BTZ/Model.lean` at `c48aa45`**: `GX.btzPaperNull` (l.1413) is
   `Causal.E0.btzPaperNull`, and `GX.btzPaperDev` (l.1408), the paper's developing map `D`
   verbatim, is `Causal.E0.btzPaperDev`; `GX.btzPaperDev_eq_nullToMink` (l.1416) is
   `Causal.E0.btzPaperDev_eq_nullToMink`.
2. **Restated from `lean-gx/GX/Lorentz/Bridge.lean` at `c48aa45`**: `GX.nullToMink` (l.88) is
   `Causal.E0.nullToMink`, with `nullToMink_apply` (l.113) and `minkQ_nullToMink` (l.123, gx's
   `nullQ y` written out as `y.2.2 ^ 2 - y.1 * y.2.1`).
3. **New** (gx's docstring of `NullCone` cites a `nullCone_iff_minkowski` that gx does not
   contain): `nullCone_iff_isFutureCausal`, `nullConeLt_iff_isFutureTimelike`,
   `nullCone_sub_iff_le`, `nullConeLt_sub_iff_lt` — the cones of this file are those of
   Minkowski space `Causal.minkowski 2` through `nullToMink`, so the local relations of
   `E0Causality` say "some developments are causally (chronologically) related in `𝐌³`".
4. gx's docstrings are kept verbatim. Where they name a gx declaration, its port here has the
   same name in `Causal.E0` (`btzPaperDev`, `nullToMink`, …); gx's `GX.BTZ.Model` is this
   file; the `nullCone_iff_minkowski` that `NullCone`'s docstring cites does not exist in gx, its
   content is `nullCone_iff_isFutureCausal` here.

The gx line of each declaration: coordinates l.116–150, null cones l.152–233, the developed lift
and its closed forms l.235–357, `abs_le_abs_add_two_pi_mul` l.460, straight segments and `unlift`
l.509–646, `adm_lift` l.704, `continuous_btzPaperNull`, `polar_add_arg_div`, `locLift` l.841–869,
`seg_mem_of_convex` l.885, `abs_arg_sub_arg_le` l.968.

## Contents

* `Causal.E0` `= ℝ × ℂ`, with the product topology: a point is `(τ, z)`, `z = r e^{iθ}`;
  `rad` (`r`), `fcoord` (`f = τ − r/2`), `hcoord` (`h = τ + r`), the singular line `axis`
  (`{r = 0}`).
* The closed and open future cones `NullCone`, `NullConeLt` of `(ℝ³, c² − ab)`, their algebra,
  and the bridge to `Causal.minkowski 2`.
* The development `lift x θ = btzPaperNull (τ, r, θ)` of a point with angle `θ` (`Polar x θ`), the
  closed forms `nullCone_lift_iff`, `nullConeLt_lift_iff`; the inverse `unlift` and the straight
  segments `seg`, continuous when read back in `E₀` (`continuousOn_unlift_seg`).

## Hypothesis checklist

| paper | here |
|---|---|
| `E₀`, coordinates `(τ, r, θ)` (l.1330–1331) | ✓ `ℝ × ℂ`, `z = r e^{iθ}`, the product topology |
| metric `−dτ² + dr² + r²dθ²` (l.1330) | ⚠ read as `−2dτdr + dr² + r²dθ²` through the paper's `D` (SCOPE) |
| `{r = 0}` a lightlike line (l.1331) | ✓ `axis`; lightlike in the causal sense in `E0Axioms` |

## SCOPE (disclosed)

* **(a) The metric.** ETT prints `−dτ² + dr² + r²dθ²` (l.1330), for which `{r = 0}` is timelike;
  this is a recorded finding of `defi:causal_E0` (curation, `findings_triage`). The model here is
  gx's, the flat extreme-BTZ metric `−2dτdr + dr² + r²dθ²` (gx's source paper,
  `RamcovGX.tex:1944`), entered through its developing map `D = btzPaperDev` and gx's proof that
  `D` pulls the Minkowski form back to that metric (gx's `GX.btzPaperDev_pullback`, not ported:
  no derivative is used anywhere in the causal theory). What is used is `D` itself, in null
  coordinates (`btzPaperDev_eq_nullToMink`).
* **(b) The topology** is the product topology of `ℝ × ℂ`, the natural one; gx's
  `GX.E0.toPaper : GX.BTZE0 ≃ₜ E0` (gx's l.3467, not ported) identifies it with the topology of
  gx's `(G,X)`-manifold `BTZE0`, so gx's `GX.BTZ.Topology` is not needed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Ported from
`lean-gx/GX/BTZ/Causality.lean`, `GX/BTZ/Model.lean`, `GX/Lorentz/Bridge.lean` at `c48aa45`
(target `T-ett-port-e0`, DEC-134).
-/

namespace Causal

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

/-! ### The null structure: the paper's developing map, and `𝐌³` in null coordinates

Restated from gx (`GX.btzPaperNull`, `GX.btzPaperDev`, `GX.btzPaperDev_eq_nullToMink`,
`GX.BTZ.Model` l.1405–1424; `GX.nullToMink`, `GX.nullToMink_apply`, `GX.minkQ_nullToMink`,
`GX.Lorentz.Bridge` l.88–127, at `c48aa45`). -/

/-- **The paper's developing map in its own cylindrical coordinates** `p = (τ, r, θ)`
(gx's `GX.btzPaperDev`, `RamcovGX.tex:1947`, `2237`, with `θ ∈ ℝ`):
`(t, (x, y)) = (τ + ½rθ², (τ + ½rθ² − r, −rθ))`, a polynomial map `ℝ³ → 𝐌³`. -/
noncomputable def btzPaperDev (p : ℝ × ℝ × ℝ) : Minkowski 2 :=
  (p.1 + 1 / 2 * p.2.1 * p.2.2 ^ 2,
    WithLp.toLp 2 ![p.1 + 1 / 2 * p.2.1 * p.2.2 ^ 2 - p.2.1, -(p.2.1 * p.2.2)])

/-- `btzPaperDev` in null coordinates (gx's `GX.btzPaperNull`; `btzPaperDev_eq_nullToMink`). -/
def btzPaperNull (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (2 * p.1 + p.2.1 * p.2.2 ^ 2 - p.2.1, p.2.1, -(p.2.1 * p.2.2))

/-- **Null coordinates to Minkowski coordinates** (gx's `GX.nullToMink`): `(a, b, x) ↦ (t, (y, x))`
with `t = (a + b)/2`, `y = (a − b)/2`. -/
noncomputable def nullToMink : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] Minkowski 2 where
  toFun y := ((y.1 + y.2.1) / 2, WithLp.toLp 2 ![(y.1 - y.2.1) / 2, y.2.2])
  invFun v := (v.1 + v.2 0, v.1 - v.2 0, v.2 1)
  map_add' y y' := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add]; ring
    · ext i
      fin_cases i
      · simp; ring
      · simp
  map_smul' c y := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring
    · ext i
      fin_cases i
      · simp; ring
      · simp
  left_inv y := by
    show ((y.1 + y.2.1) / 2 + (y.1 - y.2.1) / 2, (y.1 + y.2.1) / 2 - (y.1 - y.2.1) / 2, y.2.2) = y
    ext <;> simp <;> ring
  right_inv v := by
    refine Prod.ext ?_ ?_
    · simp
    · ext i; fin_cases i <;> simp

theorem nullToMink_apply (y : ℝ × ℝ × ℝ) :
    nullToMink y = ((y.1 + y.2.1) / 2, WithLp.toLp 2 ![(y.1 - y.2.1) / 2, y.2.2]) := rfl

/-- **`nullToMink` is an isometry** (gx's `GX.minkQ_nullToMink`): `minkQ ∘ nullToMink` is the
null form `c² − ab`. -/
theorem minkQ_nullToMink (y : ℝ × ℝ × ℝ) :
    Flat.minkQ (nullToMink y) = y.2.2 ^ 2 - y.1 * y.2.1 := by
  simp only [Flat.minkQ, nullToMink_apply, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]
  ring

/-- **`D` is `btzPaperNull` read in Minkowski coordinates** (gx's
`GX.btzPaperDev_eq_nullToMink`). -/
theorem btzPaperDev_eq_nullToMink (p : ℝ × ℝ × ℝ) :
    btzPaperDev p = nullToMink (btzPaperNull p) := by
  rw [nullToMink_apply, btzPaperDev, btzPaperNull]
  refine Prod.ext (by simp only; ring) ?_
  ext i; fin_cases i
  · simp; ring
  · simp

/-- **`NullCone` is the closed future cone of `𝐌³`** read through `nullToMink` (new; gx's
docstring of `NullCone` cites it as `nullCone_iff_minkowski`). -/
theorem nullCone_iff_isFutureCausal (V : ℝ × ℝ × ℝ) :
    NullCone V ↔ Flat.IsFutureCausal (nullToMink V) := by
  rw [Flat.IsFutureCausal, minkQ_nullToMink]
  have h1 : (nullToMink V).1 = (V.1 + V.2.1) / 2 := rfl
  rw [h1]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨by positivity, by linarith⟩
  · rintro ⟨hab, hc⟩
    have hprod : 0 ≤ V.1 * V.2.1 := by nlinarith [sq_nonneg V.2.2]
    have ha : 0 ≤ V.1 := by
      by_contra ha
      have ha' : V.1 < 0 := not_le.1 ha
      have hb' : 0 < V.2.1 := by linarith
      nlinarith
    have hb : 0 ≤ V.2.1 := by
      by_contra hb
      have hb' : V.2.1 < 0 := not_le.1 hb
      have ha' : 0 < V.1 := by linarith
      nlinarith
    exact ⟨ha, hb, by linarith⟩

/-- **`NullConeLt` is the open future timelike cone of `𝐌³`** through `nullToMink` (new). -/
theorem nullConeLt_iff_isFutureTimelike (V : ℝ × ℝ × ℝ) :
    NullConeLt V ↔ Flat.IsFutureTimelike (nullToMink V) := by
  rw [Flat.IsFutureTimelike, minkQ_nullToMink]
  have h1 : (nullToMink V).1 = (V.1 + V.2.1) / 2 := rfl
  rw [h1]
  constructor
  · intro h
    have ha := h.fst_pos
    obtain ⟨hb, hc⟩ := h
    exact ⟨by positivity, by linarith⟩
  · rintro ⟨hab, hc⟩
    have hprod : 0 < V.1 * V.2.1 := by nlinarith [sq_nonneg V.2.2]
    have hb : 0 < V.2.1 := by
      by_contra hb
      have hb' : V.2.1 ≤ 0 := not_lt.1 hb
      have ha' : 0 < V.1 := by linarith
      nlinarith
    exact ⟨hb, by linarith⟩

/-- **Two points of `ℝ³` differ by a `NullCone` vector iff their images are causally related in
`𝐌³`** (`Causal.minkowski 2`, globally; new). -/
theorem nullCone_sub_iff_le (P Q : ℝ × ℝ × ℝ) :
    NullCone (Q - P) ↔ (minkowski 2).le ⊤ (nullToMink P) (nullToMink Q) := by
  rw [Flat.le_top_iff_minkQ, ← map_sub, nullCone_iff_isFutureCausal]

/-- **The same for `NullConeLt` and the chronology of `𝐌³`** (new). -/
theorem nullConeLt_sub_iff_lt (P Q : ℝ × ℝ × ℝ) :
    NullConeLt (Q - P) ↔ (minkowski 2).lt ⊤ (nullToMink P) (nullToMink Q) := by
  rw [Flat.lt_top_iff_minkQ, ← map_sub, nullConeLt_iff_isFutureTimelike]

/-! ### The developed lift and the two relations -/

/-- **The null coordinates of the development of `x` with angle `θ`**: `btzPaperNull (τ, r, θ) =
(2τ + rθ² − r, r, −rθ)`, i.e. `nullToMink.symm` of the paper's `D(τ, r, θ)` (`btzPaperDev`,
`GX.BTZ.Model`). -/
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

theorem adm_lift (x : E0) (θ : ℝ) : Adm (lift x θ) := by
  simp only [Adm, lift, btzPaperNull]
  rcases (rad_nonneg x).lt_or_eq with h | h
  · exact Or.inl h
  · right; rw [← h]; simp

/-! ### Local lifts off the axis -/

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

/-- `seg` stays in a convex set containing its ends. -/
theorem seg_mem_of_convex {S : Set (ℝ × ℝ × ℝ)} (hS : Convex ℝ S) (hP : P ∈ S) (hQ : Q ∈ S)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : seg P Q s ∈ S :=
  hS.add_smul_sub_mem hP hQ hs

/-- `|arg z − arg w| ≤ 2π`. -/
theorem abs_arg_sub_arg_le (z w : ℂ) : |arg z - arg w| ≤ 2 * π := by
  rw [abs_le]
  constructor <;> linarith [Complex.arg_le_pi z, Complex.neg_pi_lt_arg z, Complex.arg_le_pi w,
    Complex.neg_pi_lt_arg w]

end E0

end Causal
