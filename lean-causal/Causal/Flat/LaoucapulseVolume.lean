import Causal.Flat.Laoucapulse
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# `Causal.Flat.LaoucapulseVolume` — Barbot's Prop 4.2, two-case form (DEC-102, DEC-104)

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §4.1.
Line numbers are those of `papers/barbot/legacy/labeled/GHFspace.tex`. Label certified:

* **`bprop:laoucapulse`** — `GHFspace.tex:855` (Prop 4.2, l.854–866;
  `bprop_laoucapulse_two_case`), MARKED under DEC-104 (ruling K) in a two-case form, for every
  dimension `n = d + 1` (`n = 1` vacuous, `𝒮 = ∅`): for `n ≥ 3` (`d ≥ 2`) "expanding" is **volume**-expanding (DEC-102: the
  volume Jacobian exceeds `1`), for the round measure on `𝒮⁺` and the round measure times
  Lebesgue on `𝒥⁺ ≅ 𝒮⁺ × ℝ` (`laoucapulse_volume`, `laoucapulseVolumeReading`): for a linear
  isometry `g`, `{w | g expands volume at w} = δ⁺⁻¹ {u | L(g) expands volume at u}`; for `n = 2`
  (`d = 1`, `𝒮 = S⁰`) it is the **conformal** reading (`a(g, ·) > 1` on `𝒮`, metric expansion
  for the sup product with any `lam·|·|` on `ℝ`), where the printed equality holds exactly
  (`Laoucapulse.laoucapulse_one`). Both Jacobians are computed exactly, not bounded: `a(g, u)^d`
  at `(u, s) ∈ 𝒥⁺`, for every isometry and every `s` (`hasVolumeJacobianAt_isomPenrose`), and
  `a(g, u)^{d−1}` at `u ∈ 𝒮` for `[L(g)]` (`hasVolumeJacobianAt_lorentzSphere`),
  `a = 1/N(L(g)v)` (l.841); so for every `d` the volume-expanding domain on `𝒥⁺` is `δ⁺⁻¹(U)`,
  `U = {a(g, ·) > 1}` (`laoucapulse_volume_domain`).
  **Findings kept**: the volume reading is false for `n = 2` (`not_laoucapulseVolumeReading_one`:
  `S⁰` has no volume to expand), hence the two cases; the metric reading is refuted for `n = 3`
  and every euclidean metric on `ℝ` (`Penrose.not_laoucapulseMetricReading_two`,
  `Laoucapulse.not_laoucapulseScaledReading_two`, `_one`); at the very point `(u₀, 4)` of that
  refutation `g` expands volume (`boostIsom_expandsVolumeAt_laoBase`).

> Observe also that the factor $\frac{1}{N(L(g)v)}$ is common to the $v$ and $s$ components.
> Hence: (l.849–851)

> Equip ${\mathcal J}^{+} \approx {\mathcal S}^{+} \times {\mathbb R}$ with the product metric
> of the round metric on the sphere ${\mathcal S}^{+}$ and any euclidean metric on $\mathbb R$.
> Let $g$ be a linear isometry of \mink, i.e., admitting a trivial translation part $\tau$. Then,
> the domain in ${\mathcal J}^{+}$ where the action of $g$ is expanding is precisely the preimage
> under $\delta^{+}$ of the domain of ${\mathcal S}^{+}$ where the action of $L(g)$ is expanding.
> (l.857–865)

**Dimension (kb/0024).** Barbot's `n` is `d + 1`; `𝒮 ≅ S^{d−1}`. Chart and normalisation are
`Penrose`'s: `𝒮` the unit sphere of `ℝ^d`, `nullVec u = (1, u)`, `g.(u, s) = ([L(g)]u, a s + b)`
(`isomPenrose`), `a(g, u) = penroseFactor (linearPart g) u`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `g` linear (`τ = 0`) | ✓ carried in `bprop_laoucapulse_two_case` and `laoucapulse_volume`; ⚠ weakened: not used (`laoucapulse_volume_domain`, `laoucapulse_one`) |
| round metric on `𝒮⁺`, any euclidean metric on `ℝ` | ✓ carried as their volumes for `n ≥ 3`: `roundMeasure d` (`toSphere`), `penroseVolume d` (product with Lebesgue); every normalisation gives the same Jacobian (`HasVolumeJacobianAt.smul_measure`, `.conj`); for `n = 2` as `Laoucapulse`'s sup product `penroseDist lam`, every `lam > 0` |
| "expanding" (undefined) | expanding: volume reading for n ≥ 3 (DEC-102), conformal for n = 2 (ruling K). Volume: `ExpandsVolumeAt μ f x := ∃ J > 1, HasVolumeJacobianAt μ f J x`, i.e. `\|det Df(x)\| > 1`; `J ≥ 0` is unique (`HasVolumeJacobianAt.unique`). Conformal (DEC-104): `IsConformallyExpandingAt` (`a > 1`) on `𝒮 = S⁰`, `IsExpandingAtWrt (penroseDist lam)` on `𝒥⁺`. Findings kept: the volume reading fails at `n = 2` (`not_laoucapulseVolumeReading_one`), the metric reading is refuted at `n = 3` (`not_laoucapulseMetricReading_two`) |
| dimension `n` | ✓ carried: every `d`; `d = 0` vacuous (`𝒮 = ∅`, `isEmpty_penroseSphere_zero`), `d = 1` conformal, `d ≥ 2` volume (DEC-104) |

## SCOPE (disclosed)

* **The Jacobian.** `HasVolumeJacobianAt μ f J x`: for every `ε > 0`, `(J − ε) μ(B) ≤ μ(f B) ≤
  (J + ε) μ(B)` for measurable `B` near `x` — the measure-theoretic form of `J = |det Df(x)|`.
  Here it is computed from a determinant. On `𝒮` (`LaouVol.roundMeasure_image_bounds`): the cone
  over `[A]C` is the image of `{r u | u ∈ C, 0 < r < a(u)}` under the cone map
  `F_A(x) = (A(‖x‖, x))₂` of `ℝ^d ∖ 0`, whose derivative `h ↦ (A(⟪u, h⟫, h))₂` has determinant
  `c(A, u) = 1/a(u)` (`LaouVol.det_coneDeriv`: `A ψ_u = ψ_{[A]u} S (c⁻¹ ⊕ DF_A)` with `ψ`, `S`
  transvections and `det A = 1`); Mathlib's change of variables
  (`lintegral_abs_det_fderiv_eq_addHaar_image`) and polar coordinates give
  `σ([A]C) ∈ [α^d/β, β^d/α] σ(C)` when `α ≤ a ≤ β` on `C`, hence the Jacobian `a^{d−1}`: `[L(g)]`
  is conformal of factor `a` on `S^{d−1}`. On `𝒥⁺` (`LaouVol.penroseVolume_image_bounds`): the
  action is the fibrewise affine `(u, s) ↦ (u, a(u)s + b(u))` (factor `a`) followed by
  `[L(g)] × id`; Fubini both ways gives the Jacobian `a^{d−1} · a = a^d` — the common factor of
  l.849–851 read for volumes. The shear `s·da + db` is below the diagonal and does not enter it.
* **Normalisation.** That `toSphere` is the Riemannian volume of the round metric is the polar
  formula, not proved here; it is rotation invariant and any constant multiple has the same
  Jacobians (`smul_measure`). Barbot's chart `(u, s) ↦ ((1, u)/√2, s/√2)` (radius `1/√2`,
  `Penrose`'s normalisation note) carries `penroseVolume d` to a constant multiple of his volume,
  so the Jacobian is unchanged by `.conj`; that chart map is not formalized.
* The consumer l.1660–1661 (Sullivan's property (i)) uses metric expansion on `𝒮` along
  `Λ̂ × {0}`; it is `laoucapulse_cover` (`Laoucapulse`), unaffected.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-102, DEC-104 (ruling K).
-/

open MeasureTheory Set Metric Topology Filter
open scoped Pointwise ENNReal

namespace Causal.Flat

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ### The measures -/

/-- **The round measure of `𝒮`**: Mathlib's `Measure.toSphere` of Lebesgue measure on
`EuclideanSpace ℝ (Fin d)`, `σ(T) = d · Leb{r u | u ∈ T, 0 < r < 1}` — the polar-coordinates
factor of Lebesgue measure (`Measure.measurePreserving_homeomorphUnitSphereProd`). -/
noncomputable def roundMeasure (d : ℕ) : Measure (PenroseSphere d) :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

instance : IsFiniteMeasure (roundMeasure d) := by unfold roundMeasure; infer_instance

instance : (roundMeasure d).IsOpenPosMeasure := by unfold roundMeasure; infer_instance

instance : IsLocallyFiniteMeasure (roundMeasure d) := by unfold roundMeasure; infer_instance

/-- The volume of `𝒥⁺ ≅ 𝒮 × ℝ`: the round measure of `𝒮` times Lebesgue measure on `ℝ`. -/
noncomputable def penroseVolume (d : ℕ) : Measure (PenroseSphere d × ℝ) :=
  (roundMeasure d).prod volume

/-- The translation term `b(g, u) = ⟨(1, [L(g)]u) | g 0⟩` of the action (l.842). -/
noncomputable def penroseShift (g : isom d) (u : PenroseSphere d) : ℝ :=
  minkB (nullVec (lorentzSphere (linearPart g) u)) (g • (0 : Minkowski d))

theorem continuous_penroseShift (g : isom d) : Continuous (penroseShift g) := by
  have h : ∀ u, penroseShift g u = -(g • (0 : Minkowski d)).1 +
      inner ℝ (lorentzSphere (linearPart g) u : E) (g • (0 : Minkowski d)).2 := fun u => by
    rw [penroseShift, minkB_nullVec]
  simp_rw [funext h]
  exact continuous_const.add
    ((continuous_subtype_val.comp (continuous_lorentzSphere _)).inner continuous_const)

instance : (penroseVolume d).IsOpenPosMeasure := by unfold penroseVolume; infer_instance

instance : IsLocallyFiniteMeasure (penroseVolume d) := by unfold penroseVolume; infer_instance


namespace LaouVol

/-- `A (1, u) = c(A, u) • (1, [A]u)`. -/
theorem lorentz_nullVec (A : lorentz d) (u : PenroseSphere d) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) =
      lorentzScale A u • nullVec (lorentzSphere A u) := by
  rw [nullVec_lorentzSphere, smul_smul, mul_inv_cancel₀ (lorentzScale_pos A u).ne', one_smul]

/-- The derivative of the cone map at a point of direction `u`: `h ↦ (A(⟪u, h⟫, h))₂`. -/
noncomputable def coneDeriv (A : lorentz d) (u : E) : E →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ ℝ E).comp
    ((linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)).comp
      ((innerSL ℝ u).prod (ContinuousLinearMap.id ℝ E)))

theorem coneDeriv_apply (A : lorentz d) (u h : E) :
    coneDeriv A u h = ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (inner ℝ u h, h)).2 := rfl

/-- The tangent hyperplane `T_u = (1,u)^⊥` of the null cone is carried to `T_{[A]u}`: the time
component of `A(⟪u,h⟫, h)` is `⟪[A]u, (A(⟪u,h⟫, h))₂⟫`. -/
theorem coneDeriv_fst (A : lorentz d) (u : PenroseSphere d) (h : E) :
    ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (inner ℝ (u : E) h, h)).1 =
      inner ℝ (lorentzSphere A u : E) (coneDeriv A u h) := by
  have h1 := minkB_nullVec_lorentzSphere A u (inner ℝ (u : E) h, h)
  rw [minkB_nullVec, minkB_nullVec] at h1
  simp only [neg_add_cancel, mul_zero] at h1
  rw [coneDeriv_apply]; linarith

/-- `(A e₀)₀ = c⁻¹ + ⟪[A]u, (A e₀)₂⟫`, `e₀ = (1, 0)`. -/
theorem lorentz_e0_fst (A : lorentz d) (u : PenroseSphere d) :
    ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) ((1 : ℝ), (0 : E))).1 =
      (lorentzScale A u)⁻¹ +
        inner ℝ (lorentzSphere A u : E) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) ((1 : ℝ), (0 : E))).2 := by
  have h1 := minkB_nullVec_lorentzSphere A u ((1 : ℝ), (0 : E))
  rw [minkB_nullVec, minkB_nullVec] at h1
  simp only [inner_zero_right, add_zero] at h1
  linarith

/-- `ψ_v (t, y) = (t + ⟪v, y⟫, y)`, a transvection. -/
noncomputable def psi (v : E) : Minkowski d →ₗ[ℝ] Minkowski d :=
  LinearMap.transvection ((innerₛₗ ℝ v).comp (LinearMap.snd ℝ ℝ E)) ((1 : ℝ), (0 : E))

theorem psi_apply (v : E) (p : Minkowski d) : psi v p = (p.1 + inner ℝ v p.2, p.2) := by
  refine Prod.ext ?_ ?_ <;> simp [psi, LinearMap.transvection.apply]

theorem det_psi (v : E) : LinearMap.det (psi v) = 1 := by
  simp [psi]

/-- **The Jacobian of the cone map**: `det (coneDeriv A u) = c(A, u)` (`det A = 1`). -/
theorem det_coneDeriv (A : lorentz d) (u : PenroseSphere d) :
    LinearMap.det (coneDeriv A (u : E) : E →ₗ[ℝ] E) = lorentzScale A u := by
  set c := lorentzScale A u with hc
  have hc0 : c ≠ 0 := (lorentzScale_pos A u).ne'
  set Aₗ := (A : Minkowski d ≃ₗ[ℝ] Minkowski d)
  set z : E := (Aₗ ((1 : ℝ), (0 : E))).2
  set L : E →ₗ[ℝ] E := (coneDeriv A (u : E) : E →ₗ[ℝ] E)
  set S : Minkowski d →ₗ[ℝ] Minkowski d :=
    LinearMap.transvection (c • LinearMap.fst ℝ ℝ E) ((0 : ℝ), z)
  set P : Minkowski d →ₗ[ℝ] Minkowski d := LinearMap.prodMap (c⁻¹ • LinearMap.id) L
  have key : (Aₗ : Minkowski d →ₗ[ℝ] Minkowski d) ∘ₗ psi (u : E) =
      psi (lorentzSphere A u : E) ∘ₗ S ∘ₗ P := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨t, h⟩ := p
    have hsplit : ((t + inner ℝ (u : E) h, h) : Minkowski d) =
        t • ((1 : ℝ), (0 : E)) + (inner ℝ (u : E) h, h) := by
      ext <;> simp [add_comm]
    simp only [LinearMap.comp_apply, psi_apply, LinearEquiv.coe_coe]
    rw [hsplit, map_add, map_smul]
    simp only [S, P, LinearMap.transvection.apply, LinearMap.prodMap_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.fst_apply]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_add, Prod.smul_snd]
      rw [lorentz_e0_fst A u, coneDeriv_fst A u h, ← hc]
      simp only [L, z, Aₗ, inner_add_right, inner_smul_right, ContinuousLinearMap.coe_coe]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      simp only [L, z, Aₗ, ContinuousLinearMap.coe_coe, coneDeriv_apply]
      rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul, add_comm]
  have hdet := congrArg LinearMap.det key
  rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_comp, det_psi, det_psi,
    lorentz.det_eq_one A.2] at hdet
  simp only [S, P, LinearMap.transvection.det, LinearMap.det_prodMap, LinearMap.det_smul,
    LinearMap.det_id, Module.finrank_self, LinearMap.smul_apply, LinearMap.fst_apply,
    smul_eq_mul, mul_zero, add_zero, one_mul, pow_one, mul_one] at hdet
  field_simp at hdet
  linarith


/-! ### The cone map and its derivative -/

/-- **The cone map** `F_A(x) = (A(‖x‖, x))₂`: the action of `A` on the future null cone
`{(‖x‖, x)}`, read in its spatial coordinate. -/
noncomputable def coneMap (A : lorentz d) (x : E) : E :=
  ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (‖x‖, x)).2

theorem coneMap_smul (A : lorentz d) (u : PenroseSphere d) {r : ℝ} (hr : 0 ≤ r) :
    coneMap A (r • (u : E)) = (r * lorentzScale A u) • (lorentzSphere A u : E) := by
  have hn : ‖r • (u : E)‖ = r := by
    rw [norm_smul, norm_penroseSphere, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]
  have hp : ((‖r • (u : E)‖, r • (u : E)) : Minkowski d) = r • nullVec u := by
    rw [hn]; exact Prod.ext (by simp [nullVec]) (by simp [nullVec])
  unfold coneMap
  rw [hp, map_smul, lorentz_nullVec, smul_smul]
  rfl

theorem hasFDerivAt_norm' {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (innerSL ℝ (‖x‖⁻¹ • x)) x := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt hx2
  have hf : (fun y : E => √(‖y‖ ^ 2)) = fun y => ‖y‖ := funext fun y => Real.sqrt_sq (norm_nonneg y)
  rw [hf] at h
  refine h.congr_fderiv (ContinuousLinearMap.ext fun h' => ?_)
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  simp only [innerSL_apply_apply, inner_smul_left, smul_apply,
    Real.sqrt_sq (norm_nonneg x), smul_eq_mul, conj_trivial]
  simp only [two_smul]
  field_simp
  ring

theorem hasFDerivAt_coneMap (A : lorentz d) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (coneMap A) (coneDeriv A (‖x‖⁻¹ • x)) x := by
  have hp : HasFDerivAt (fun y : E => ((‖y‖, y) : Minkowski d))
      ((innerSL ℝ (‖x‖⁻¹ • x)).prod (ContinuousLinearMap.id ℝ E)) x :=
    (hasFDerivAt_norm' hx).prodMk (hasFDerivAt_id x)
  exact (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp x
    ((linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)).hasFDerivAt.comp x hp)

/-! ### Polar coordinates -/

/-- Polar coordinates `(u, r) ↦ r u`. -/
def polar (p : PenroseSphere d × ℝ) : E := p.2 • (p.1 : E)

theorem continuous_polar : Continuous (polar (d := d)) := by
  unfold polar; fun_prop

theorem norm_polar {p : PenroseSphere d × ℝ} (hp : 0 ≤ p.2) : ‖polar p‖ = p.2 := by
  rw [polar, norm_smul, norm_penroseSphere, mul_one, Real.norm_eq_abs, abs_of_nonneg hp]

theorem polar_injOn : InjOn (polar (d := d)) {p | 0 < p.2} := by
  rintro ⟨u, r⟩ hr ⟨u', r'⟩ hr' h
  simp only [mem_setOf_eq] at hr hr'
  have hrr : r = r' := by
    have := congrArg norm h
    rwa [norm_polar hr.le, norm_polar hr'.le] at this
  subst hrr
  refine Prod.ext (Subtype.ext ?_) rfl
  exact smul_right_injective E hr.ne' h

theorem Ioo_smul_eq_polar (T : Set (PenroseSphere d)) (a b : ℝ) :
    Ioo a b • ((↑) '' T : Set E) = polar '' (T ×ˢ Ioo a b) := by
  ext x
  simp only [Set.mem_smul, mem_image, mem_prod, polar, Prod.exists]
  constructor
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, r, ⟨hu, hr⟩, rfl⟩
  · rintro ⟨u, r, ⟨hu, hr⟩, rfl⟩
    exact ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩

theorem polar_smul_Ioo (T : Set (PenroseSphere d)) {r : ℝ} (hr : 0 < r) :
    polar '' (T ×ˢ Ioo 0 r) = r • (polar '' (T ×ˢ Ioo (0 : ℝ) 1)) := by
  ext x
  simp only [mem_image, mem_prod, mem_Ioo, Prod.exists, polar, Set.mem_smul_set]
  constructor
  · rintro ⟨u, ρ, ⟨hu, h0, h1⟩, rfl⟩
    refine ⟨(ρ / r) • (u : E), ⟨u, ρ / r, ⟨hu, div_pos h0 hr, (div_lt_one hr).2 h1⟩, rfl⟩, ?_⟩
    rw [smul_smul, mul_div_cancel₀ _ hr.ne']
  · rintro ⟨_, ⟨u, ρ, ⟨hu, h0, h1⟩, rfl⟩, rfl⟩
    exact ⟨u, r * ρ, ⟨hu, mul_pos hr h0, by nlinarith⟩, by rw [smul_smul]⟩

theorem roundMeasure_apply {T : Set (PenroseSphere d)} (hT : MeasurableSet T) :
    roundMeasure d T = d * volume (polar '' (T ×ˢ Ioo (0 : ℝ) 1)) := by
  rw [roundMeasure, Measure.toSphere_apply' _ hT, Ioo_smul_eq_polar, finrank_euclideanSpace_fin]

theorem volume_polar_Ioo (T : Set (PenroseSphere d)) {r : ℝ} (hr : 0 < r) :
    volume (polar '' (T ×ˢ Ioo 0 r)) =
      ENNReal.ofReal (r ^ d) * volume (polar '' (T ×ˢ Ioo (0 : ℝ) 1)) := by
  rw [polar_smul_Ioo T hr, Measure.addHaar_smul_of_nonneg _ hr.le, finrank_euclideanSpace_fin]

theorem lorentzSphere_injective (A : lorentz d) : Function.Injective (lorentzSphere A) := by
  intro u u' h
  apply nullVec_injective_smul (c := lorentzScale A u / lorentzScale A u')
  apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d).injective
  rw [map_smul, lorentz_nullVec, lorentz_nullVec, h, smul_smul,
    div_mul_cancel₀ _ (lorentzScale_pos A u').ne']

theorem measurableEmbedding_lorentzSphere (A : lorentz d) : MeasurableEmbedding (lorentzSphere A) :=
  (continuous_lorentzSphere A).measurableEmbedding (lorentzSphere_injective A)

/-! ### The sphere Jacobian of `[L(g)]`: bounds -/

/-- **The change of variables on `𝒮`.** If `α ≤ a(A, ·) ≤ β` on a measurable `C ⊆ 𝒮`
(`α > 0`), then `(α^d/β) σ(C) ≤ σ([A] C) ≤ (β^d/α) σ(C)` for the round measure `σ`. Proof: the
cone over `[A]C` of radius `1` is the image under the cone map `F_A` of the region
`D = {r u | u ∈ C, 0 < r < a(u)}`, `F_A` has Jacobian determinant `c = 1/a` (`det_coneDeriv`), and
`D` is squeezed between the cones over `C` of radii `α` and `β`. -/
theorem roundMeasure_image_bounds (A : lorentz d) {C : Set (PenroseSphere d)}
    (hC : MeasurableSet C) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hab : ∀ u ∈ C, α ≤ penroseFactor A u ∧ penroseFactor A u ≤ β) :
    ENNReal.ofReal (α ^ d / β) * roundMeasure d C ≤ roundMeasure d (lorentzSphere A '' C) ∧
      roundMeasure d (lorentzSphere A '' C) ≤ ENNReal.ofReal (β ^ d / α) * roundMeasure d C := by
  have hβ : 0 < β := hα.trans_le hαβ
  set a := penroseFactor A
  set D : Set E := polar '' {p : PenroseSphere d × ℝ | p.1 ∈ C ∧ 0 < p.2 ∧ p.2 < a p.1} with hD_def
  have hS : MeasurableSet {p : PenroseSphere d × ℝ | p.1 ∈ C ∧ 0 < p.2 ∧ p.2 < a p.1} :=
    (measurable_fst hC).inter ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd ((continuous_penroseFactor A).measurable.comp measurable_fst)))
  have hD : MeasurableSet D :=
    hS.image_of_continuousOn_injOn continuous_polar.continuousOn
      (polar_injOn.mono fun p hp => hp.2.1)
  -- the polar description of `D` and of the cone map on it
  have hFpolar : ∀ (u : PenroseSphere d) (r : ℝ), 0 ≤ r →
      coneMap A (polar (u, r)) = polar (lorentzSphere A u, r * lorentzScale A u) := fun u r hr =>
    coneMap_smul A u hr
  have hcz : ∀ u, lorentzScale A u = (a u)⁻¹ := fun u => by
    simp only [a, penroseFactor, inv_inv]
  have himage : coneMap A '' D = polar '' ((lorentzSphere A '' C) ×ˢ Ioo (0 : ℝ) 1) := by
    ext y
    simp only [hD_def, mem_image, mem_setOf_eq, mem_prod, mem_Ioo, Prod.exists]
    constructor
    · rintro ⟨_, ⟨u, r, ⟨hu, hr0, hra⟩, rfl⟩, rfl⟩
      refine ⟨lorentzSphere A u, r * lorentzScale A u, ⟨⟨u, hu, rfl⟩,
        mul_pos hr0 (lorentzScale_pos A u), ?_⟩, (hFpolar u r hr0.le).symm⟩
      rw [hcz, ← div_eq_mul_inv, div_lt_one (penroseFactor_pos A u)]; exact hra
    · rintro ⟨_, ρ, ⟨⟨u, hu, rfl⟩, hρ0, hρ1⟩, rfl⟩
      refine ⟨polar (u, ρ * a u), ⟨u, ρ * a u, ⟨hu, mul_pos hρ0 (penroseFactor_pos A u), ?_⟩, rfl⟩,
        ?_⟩
      · have := penroseFactor_pos A u; nlinarith
      · rw [hFpolar u _ (mul_pos hρ0 (penroseFactor_pos A u)).le, hcz, mul_assoc,
          mul_inv_cancel₀ (penroseFactor_pos A u).ne', mul_one]
  have hDnz : ∀ x ∈ D, x ≠ 0 := by
    rintro _ ⟨⟨u, r⟩, ⟨_, hr, _⟩, rfl⟩ h0
    have := congrArg norm h0
    rw [norm_polar hr.le, norm_zero] at this
    exact hr.ne' this
  have hdir : ∀ (u : PenroseSphere d) (r : ℝ), 0 < r → ‖polar (u, r)‖⁻¹ • polar (u, r) = (u : E) :=
    fun u r hr => by
      rw [norm_polar hr.le]; simp only [polar, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hinj : InjOn (coneMap A) D := by
    rintro _ ⟨⟨u, r⟩, ⟨_, hr, _⟩, rfl⟩ _ ⟨⟨u', r'⟩, ⟨_, hr', _⟩, rfl⟩ h
    rw [hFpolar u r hr.le, hFpolar u' r' hr'.le] at h
    have h' := polar_injOn (mul_pos hr (lorentzScale_pos A u))
      (show (0 : ℝ) < (lorentzSphere A u', r' * lorentzScale A u').2 from
        mul_pos hr' (lorentzScale_pos A u')) h
    have huu : u = u' := lorentzSphere_injective A (congrArg Prod.fst h')
    subst huu
    have : r = r' := mul_right_cancel₀ (lorentzScale_pos A u).ne' (congrArg Prod.snd h')
    rw [this]
  have hderiv : ∀ x ∈ D, HasFDerivWithinAt (coneMap A) (coneDeriv A (‖x‖⁻¹ • x)) D x :=
    fun x hx => (hasFDerivAt_coneMap A (hDnz x hx)).hasFDerivWithinAt
  have hcov := lintegral_abs_det_fderiv_eq_addHaar_image volume hD hderiv hinj
  rw [himage] at hcov
  -- the Jacobian `c = 1/a` is pinched on `D`
  have hdetb : ∀ x ∈ D, ENNReal.ofReal β⁻¹ ≤ ENNReal.ofReal |(coneDeriv A (‖x‖⁻¹ • x)).det| ∧
      ENNReal.ofReal |(coneDeriv A (‖x‖⁻¹ • x)).det| ≤ ENNReal.ofReal α⁻¹ := by
    rintro _ ⟨⟨u, r⟩, ⟨hu, hr, _⟩, rfl⟩
    rw [hdir u r hr, ContinuousLinearMap.det, det_coneDeriv, abs_of_pos (lorentzScale_pos A u),
      hcz]
    have hau := penroseFactor_pos A u
    exact ⟨ENNReal.ofReal_le_ofReal (inv_anti₀ hau (hab u hu).2),
      ENNReal.ofReal_le_ofReal (inv_anti₀ hα (hab u hu).1)⟩
  have hDsub : D ⊆ polar '' (C ×ˢ Ioo 0 β) := by
    rintro _ ⟨⟨u, r⟩, ⟨hu, hr, hra⟩, rfl⟩
    exact ⟨(u, r), ⟨hu, hr, hra.trans_le (hab u hu).2⟩, rfl⟩
  have hsubD : polar '' (C ×ˢ Ioo 0 α) ⊆ D := by
    rintro _ ⟨⟨u, r⟩, ⟨hu, hr, hrα⟩, rfl⟩
    exact ⟨(u, r), ⟨hu, hr, hrα.trans_le (hab u hu).1⟩, rfl⟩
  have hlo : ENNReal.ofReal β⁻¹ * volume D ≤
      volume (polar '' ((lorentzSphere A '' C) ×ˢ Ioo (0 : ℝ) 1)) := by
    rw [← hcov, ← setLIntegral_const]
    exact setLIntegral_mono' hD fun x hx => (hdetb x hx).1
  have hhi : volume (polar '' ((lorentzSphere A '' C) ×ˢ Ioo (0 : ℝ) 1)) ≤
      ENNReal.ofReal α⁻¹ * volume D := by
    rw [← hcov, ← setLIntegral_const]
    exact setLIntegral_mono' hD fun x hx => (hdetb x hx).2
  have hDlo : ENNReal.ofReal (α ^ d) * volume (polar '' (C ×ˢ Ioo (0 : ℝ) 1)) ≤ volume D := by
    rw [← volume_polar_Ioo C hα]; exact measure_mono hsubD
  have hDhi : volume D ≤ ENNReal.ofReal (β ^ d) * volume (polar '' (C ×ˢ Ioo (0 : ℝ) 1)) := by
    rw [← volume_polar_Ioo C hβ]; exact measure_mono hDsub
  have hφC : MeasurableSet (lorentzSphere A '' C) :=
    (measurableEmbedding_lorentzSphere A).measurableSet_image.2 hC
  rw [roundMeasure_apply hC, roundMeasure_apply hφC]
  have e1 : ENNReal.ofReal (α ^ d / β) = ENNReal.ofReal β⁻¹ * ENNReal.ofReal (α ^ d) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hβ.le), div_eq_inv_mul]
  have e2 : ENNReal.ofReal (β ^ d / α) = ENNReal.ofReal α⁻¹ * ENNReal.ofReal (β ^ d) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hα.le), div_eq_inv_mul]
  constructor
  · rw [e1, mul_left_comm, mul_assoc]
    gcongr
    exact (mul_le_mul_right hDlo _).trans hlo
  · rw [e2, mul_left_comm, mul_assoc]
    gcongr
    exact hhi.trans (mul_le_mul_right hDhi _)

/-! ### The bounds for the action of `Isom(𝐌ⁿ)` on `𝒥⁺` -/

/-- Lebesgue measure of an affine image of a subset of `ℝ`. -/
theorem volume_image_affine {a : ℝ} (ha : 0 < a) (b : ℝ) (S : Set ℝ) :
    volume ((fun s => a * s + b) '' S) = ENNReal.ofReal a * volume S := by
  have h : (fun s => a * s + b) '' S = (fun s => s + -b) ⁻¹' (a • S) := by
    ext x
    simp only [mem_image, mem_preimage, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, by ring⟩
    · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by linarith⟩
  rw [h, measure_preimage_add_right, Measure.addHaar_smul, Module.finrank_self, pow_one,
    abs_of_pos ha]

/-- **The change of variables on `𝒥⁺`.** If `α ≤ a(g, ·) ≤ β` on the `𝒮`-projection of a measurable
`B ⊆ 𝒮 × ℝ` (`α > 0`), then `(α^{d+1}/β) ν(B) ≤ ν(g B) ≤ (β^{d+1}/α) ν(B)`. The action
factors as `(u, s) ↦ (u, a(u)s + b(u))` (fibrewise affine: factor `a` on each fibre) followed by
`[L(g)] × id` (factor in `[α^d/β, β^d/α]` on each slice, `roundMeasure_image_bounds`). -/
theorem penroseVolume_image_bounds (g : isom d) {B : Set (PenroseSphere d × ℝ)}
    (hB : MeasurableSet B) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hab : ∀ w ∈ B, α ≤ penroseFactor (linearPart g) w.1 ∧ penroseFactor (linearPart g) w.1 ≤ β) :
    ENNReal.ofReal (α ^ (d + 1) / β) * penroseVolume d B ≤ penroseVolume d (isomPenrose g '' B) ∧
      penroseVolume d (isomPenrose g '' B) ≤ ENNReal.ofReal (β ^ (d + 1) / α) * penroseVolume d B := by
  have hβ : 0 < β := hα.trans_le hαβ
  set A := linearPart g
  set a := penroseFactor A
  set b := penroseShift g
  set C : Set (PenroseSphere d) := {u | α ≤ a u ∧ a u ≤ β}
  have hC : MeasurableSet C := (measurableSet_le measurable_const
    (continuous_penroseFactor A).measurable).inter
    (measurableSet_le (continuous_penroseFactor A).measurable measurable_const)
  set T : PenroseSphere d × ℝ → PenroseSphere d × ℝ := fun w => (w.1, a w.1 * w.2 + b w.1)
  set Φ : PenroseSphere d × ℝ → PenroseSphere d × ℝ := fun w => (lorentzSphere A w.1, w.2)
  have hG : isomPenrose g = Φ ∘ T := rfl
  have hTc : Continuous T := continuous_fst.prodMk
    ((((continuous_penroseFactor A).comp continuous_fst).mul continuous_snd).add
      ((continuous_penroseShift g).comp continuous_fst))
  have hTi : Function.Injective T := by
    rintro ⟨u, s⟩ ⟨u', s'⟩ h
    simp only [T, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have := penroseFactor_pos A u
    refine Prod.ext rfl ?_
    have : a u * s = a u * s' := by linarith
    exact mul_left_cancel₀ (penroseFactor_pos A u).ne' this
  have hΦc : Continuous Φ := ((continuous_lorentzSphere A).comp continuous_fst).prodMk continuous_snd
  have hΦi : Function.Injective Φ := by
    rintro ⟨u, s⟩ ⟨u', s'⟩ h
    simp only [Φ, Prod.mk.injEq] at h
    exact Prod.ext (lorentzSphere_injective A h.1) h.2
  have hTe := hTc.measurableEmbedding hTi
  have hΦe := hΦc.measurableEmbedding hΦi
  have hTB : MeasurableSet (T '' B) := hTe.measurableSet_image.2 hB
  have hBC : ∀ u, u ∉ C → Prod.mk u ⁻¹' B = ∅ := fun u hu => by
    ext s; simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact fun hs => hu (hab _ hs)
  -- the fibrewise affine step
  have hslice : ∀ u, Prod.mk u ⁻¹' (T '' B) = (fun s => a u * s + b u) '' (Prod.mk u ⁻¹' B) :=
    fun u => by
      ext s'
      simp only [mem_preimage, mem_image, T, Prod.exists, Prod.mk.injEq]
      constructor
      · rintro ⟨u', s, hB', rfl, rfl⟩; exact ⟨s, hB', rfl⟩
      · rintro ⟨s, hB', rfl⟩; exact ⟨u, s, hB', rfl, rfl⟩
  have hT : ENNReal.ofReal α * penroseVolume d B ≤ penroseVolume d (T '' B) ∧
      penroseVolume d (T '' B) ≤ ENNReal.ofReal β * penroseVolume d B := by
    have ha : ∀ u, 0 < a u := penroseFactor_pos A
    simp only [penroseVolume, Measure.prod_apply hB, Measure.prod_apply hTB, hslice,
      volume_image_affine (ha _)]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    constructor
    · refine lintegral_mono fun u => ?_
      by_cases hu : u ∈ C
      · gcongr; exact hu.1
      · simp [hBC u hu]
    · refine lintegral_mono fun u => ?_
      by_cases hu : u ∈ C
      · gcongr; exact hu.2
      · simp [hBC u hu]
  -- the sphere step, slice by slice
  have hTBC : ∀ w ∈ T '' B, w.1 ∈ C := by
    rintro _ ⟨w, hw, rfl⟩; exact hab w hw
  have hΦ : ∀ {B' : Set (PenroseSphere d × ℝ)}, MeasurableSet B' → (∀ w ∈ B', w.1 ∈ C) →
      ENNReal.ofReal (α ^ d / β) * penroseVolume d B' ≤ penroseVolume d (Φ '' B') ∧
        penroseVolume d (Φ '' B') ≤ ENNReal.ofReal (β ^ d / α) * penroseVolume d B' := by
    intro B' hB' hB'C
    have hΦB' : MeasurableSet (Φ '' B') := hΦe.measurableSet_image.2 hB'
    have hsl : ∀ s, (fun u => (u, s)) ⁻¹' (Φ '' B') =
        lorentzSphere A '' ((fun u => (u, s)) ⁻¹' B') := fun s => by
      ext u'
      simp only [mem_preimage, mem_image, Φ, Prod.exists, Prod.mk.injEq]
      constructor
      · rintro ⟨u, s₁, hB'', rfl, rfl⟩; exact ⟨u, hB'', rfl⟩
      · rintro ⟨u, hB'', rfl⟩; exact ⟨u, s, hB'', rfl, rfl⟩
    have hb := fun s => roundMeasure_image_bounds A (C := (fun u => (u, s)) ⁻¹' B')
      (measurable_prodMk_right hB') hα hαβ (fun u hu => hB'C _ hu)
    simp only [penroseVolume, Measure.prod_apply_symm hB', Measure.prod_apply_symm hΦB', hsl]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ⟨lintegral_mono fun s => (hb s).1, lintegral_mono fun s => (hb s).2⟩
  have hΦT := hΦ hTB hTBC
  rw [hG, image_comp]
  have e1 : ENNReal.ofReal (α ^ (d + 1) / β) = ENNReal.ofReal (α ^ d / β) * ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; rw [pow_succ]; ring
  have e2 : ENNReal.ofReal (β ^ (d + 1) / α) = ENNReal.ofReal (β ^ d / α) * ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; rw [pow_succ]; ring
  constructor
  · rw [e1, mul_assoc]
    exact (mul_le_mul_right hT.1 _).trans hΦT.1
  · rw [e2, mul_assoc]
    exact hΦT.2.trans (mul_le_mul_right hT.2 _)

end LaouVol

/-! ### The volume Jacobian of a map, and volume expansion -/

section Jacobian

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- `f` has **volume Jacobian `J` at `x`** for the measure `μ`: for every `ε > 0`, on every
measurable set `B` in some neighbourhood of `x`, `(J − ε) μ(B) ≤ μ(f B) ≤ (J + ε) μ(B)`. For a
`C¹` diffeomorphism of a Riemannian manifold and its Riemannian volume this is `J = |det Df(x)|`,
the determinant taken in orthonormal frames; the number `J ≥ 0` is unique
(`HasVolumeJacobianAt.unique`). -/
def HasVolumeJacobianAt (μ : Measure X) (f : X → X) (J : ℝ) (x : X) : Prop :=
  ∀ ε > 0, ∃ V ∈ 𝓝 x, ∀ B ⊆ V, MeasurableSet B →
    ENNReal.ofReal (J - ε) * μ B ≤ μ (f '' B) ∧ μ (f '' B) ≤ ENNReal.ofReal (J + ε) * μ B

/-- `f` **expands volume at `x`** (the volume reading of "expanding", DEC-102): its volume
Jacobian at `x` exists and exceeds `1`, i.e. `|det Df(x)| > 1`. -/
def ExpandsVolumeAt (μ : Measure X) (f : X → X) (x : X) : Prop :=
  ∃ J > (1 : ℝ), HasVolumeJacobianAt μ f J x

/-- **The volume Jacobian is unique** among nonnegative numbers, for a measure charging every
nonempty open set and finite near `x`. -/
theorem HasVolumeJacobianAt.unique [OpensMeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]
    [IsLocallyFiniteMeasure μ] {f : X → X} {x : X} {J J' : ℝ} (h : HasVolumeJacobianAt μ f J x)
    (h' : HasVolumeJacobianAt μ f J' x) (hJ : 0 ≤ J) (hJ' : 0 ≤ J') : J = J' := by
  have key : ∀ {J J' : ℝ}, 0 ≤ J → HasVolumeJacobianAt μ f J x → HasVolumeJacobianAt μ f J' x →
      ¬ J < J' := by
    intro J J' hJ h h' hlt
    set ε := (J' - J) / 3 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    obtain ⟨V, hV, hVB⟩ := h ε hε
    obtain ⟨V', hV', hV'B⟩ := h' ε hε
    obtain ⟨W, hW, hWfin⟩ := μ.finiteAt_nhds x
    have hN : V ∩ V' ∩ W ∈ 𝓝 x := inter_mem (inter_mem hV hV') hW
    have hxU : x ∈ interior (V ∩ V' ∩ W) := mem_interior_iff_mem_nhds.2 hN
    have hUN : interior (V ∩ V' ∩ W) ⊆ V ∩ V' ∩ W := interior_subset
    have hpos : μ (interior (V ∩ V' ∩ W)) ≠ 0 :=
      (isOpen_interior.measure_pos μ ⟨x, hxU⟩).ne'
    have hfin : μ (interior (V ∩ V' ∩ W)) ≠ ∞ :=
      ((measure_mono (hUN.trans inter_subset_right)).trans_lt hWfin).ne
    have h1 := (hV'B _ (hUN.trans (inter_subset_left.trans inter_subset_right))
      isOpen_interior.measurableSet).1
    have h2 := (hVB _ (hUN.trans (inter_subset_left.trans inter_subset_left))
      isOpen_interior.measurableSet).2
    have h3 := (ENNReal.mul_le_mul_iff_left hpos hfin).1 (h1.trans h2)
    rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at h3
    linarith
  rcases lt_trichotomy J J' with hlt | heq | hgt
  · exact absurd hlt (key hJ h h')
  · exact heq
  · exact absurd hgt (key hJ' h' h)

/-- Under a volume Jacobian `J ≥ 0` at `x`, `f` expands volume at `x` iff `J > 1`. -/
theorem HasVolumeJacobianAt.expandsVolumeAt_iff [OpensMeasurableSpace X] {μ : Measure X}
    [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ] {f : X → X} {x : X} {J : ℝ}
    (h : HasVolumeJacobianAt μ f J x) (hJ : 0 ≤ J) : ExpandsVolumeAt μ f x ↔ 1 < J :=
  ⟨fun ⟨J', hJ', h'⟩ => h'.unique h (by linarith) hJ ▸ hJ', fun hJ1 => ⟨J, hJ1, h⟩⟩

/-- The volume Jacobian does not depend on the normalisation of the measure. -/
theorem HasVolumeJacobianAt.smul_measure {μ : Measure X} {f : X → X} {J : ℝ} {x : X}
    (h : HasVolumeJacobianAt μ f J x) (c : ℝ≥0∞) : HasVolumeJacobianAt (c • μ) f J x := by
  intro ε hε
  obtain ⟨V, hV, hVB⟩ := h ε hε
  refine ⟨V, hV, fun B hBV hB => ?_⟩
  simp only [Measure.smul_apply, smul_eq_mul]
  obtain ⟨h1, h2⟩ := hVB B hBV hB
  rw [mul_left_comm, mul_left_comm _ c]
  exact ⟨mul_le_mul_right h1 c, mul_le_mul_right h2 c⟩

/-- The volume Jacobian is invariant under a change of chart carrying one measure to the other:
if `e : X ≃ₜ Y` is measurable both ways and `e_* μ = μ'`, then `e ∘ f ∘ e⁻¹` has, at `e x`, the
Jacobian `f` has at `x`. -/
theorem HasVolumeJacobianAt.conj {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    {μ : Measure X} {μ' : Measure Y} {f : X → X} {J : ℝ} {x : X} (h : HasVolumeJacobianAt μ f J x)
    (e : X ≃ₜ Y) (he : MeasurableEmbedding e) (hμ : μ.map e = μ') :
    HasVolumeJacobianAt μ' (e ∘ f ∘ e.symm) J (e x) := by
  intro ε hε
  obtain ⟨V, hV, hVB⟩ := h ε hε
  refine ⟨e.symm ⁻¹' V, e.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hV),
    fun B hBV hB => ?_⟩
  have hB0 : e ⁻¹' B ⊆ V := fun y hy => by simpa using hBV hy
  have hB0m : MeasurableSet (e ⁻¹' B) := he.measurable hB
  have hμB : μ' B = μ (e ⁻¹' B) := by rw [← hμ, he.map_apply]
  have himg : (e ∘ f ∘ e.symm) '' B = e '' (f '' (e ⁻¹' B)) := by
    rw [image_comp, image_comp, e.image_symm]
  have hμf : μ' ((e ∘ f ∘ e.symm) '' B) = μ (f '' (e ⁻¹' B)) := by
    rw [himg, ← hμ, he.map_apply, e.injective.preimage_image]
  rw [hμB, hμf]
  exact hVB _ hB0 hB0m

/-- Bounds pinched by a continuous function give a volume Jacobian. -/
theorem hasVolumeJacobianAt_of_bounds {μ : Measure X} {f : X → X} {x : X} {a : X → ℝ}
    (ha : ContinuousAt a x) (ha0 : 0 < a x) {J : ℝ} {lo hi : ℝ → ℝ → ℝ}
    (hlo : Tendsto (fun δ => lo (a x - δ) (a x + δ)) (𝓝 0) (𝓝 J))
    (hhi : Tendsto (fun δ => hi (a x - δ) (a x + δ)) (𝓝 0) (𝓝 J))
    (hb : ∀ α β : ℝ, 0 < α → α ≤ β → ∀ B, MeasurableSet B → (∀ y ∈ B, α ≤ a y ∧ a y ≤ β) →
      ENNReal.ofReal (lo α β) * μ B ≤ μ (f '' B) ∧ μ (f '' B) ≤ ENNReal.ofReal (hi α β) * μ B) :
    HasVolumeJacobianAt μ f J x := by
  intro ε hε
  have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), J - ε < lo (a x - δ) (a x + δ) :=
    hlo.eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), hi (a x - δ) (a x + δ) < J + ε :=
    hhi.eventually (gt_mem_nhds (by linarith))
  have h3 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < a x := gt_mem_nhds ha0
  obtain ⟨δ, ⟨⟨hδ1, hδ2⟩, hδ3⟩, hδ0⟩ :=
    ((((h1.and h2).and h3).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  refine ⟨a ⁻¹' Ioo (a x - δ) (a x + δ),
    ha.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), fun B hBV hB => ?_⟩
  have hbd := hb (a x - δ) (a x + δ) (by linarith) (by linarith) B hB
    fun y hy => ⟨(hBV hy).1.le, (hBV hy).2.le⟩
  refine ⟨le_trans ?_ hbd.1, hbd.2.trans ?_⟩
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hδ1.le) _
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hδ2.le) _

end Jacobian

/-! ### `bprop:laoucapulse` in the volume reading -/

namespace LaouVol

/-- A point of `𝒮` forces `d ≥ 1`. -/
theorem one_le_of_penroseSphere (u : PenroseSphere d) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | h
  · have h1 := norm_penroseSphere u
    rw [Subsingleton.elim (u : EuclideanSpace ℝ (Fin 0)) 0, norm_zero] at h1
    exact absurd h1 zero_ne_one
  · exact h

theorem tendsto_bound (a₀ : ℝ) (ha₀ : 0 < a₀) (m : ℕ) :
    Tendsto (fun δ : ℝ => (a₀ - δ) ^ (m + 1) / (a₀ + δ)) (𝓝 0) (𝓝 (a₀ ^ m)) ∧
      Tendsto (fun δ : ℝ => (a₀ + δ) ^ (m + 1) / (a₀ - δ)) (𝓝 0) (𝓝 (a₀ ^ m)) := by
  have e : a₀ ^ m = a₀ ^ (m + 1) / a₀ := by rw [pow_succ, mul_div_cancel_right₀ _ ha₀.ne']
  constructor
  · have hc : ContinuousAt (fun δ : ℝ => (a₀ - δ) ^ (m + 1) / (a₀ + δ)) 0 :=
      ((continuous_const.sub continuous_id).pow _).continuousAt.div
        (continuous_const.add continuous_id).continuousAt (by simp [ha₀.ne'])
    simpa [← e] using hc.tendsto
  · have hc : ContinuousAt (fun δ : ℝ => (a₀ + δ) ^ (m + 1) / (a₀ - δ)) 0 :=
      ((continuous_const.add continuous_id).pow _).continuousAt.div
        (continuous_const.sub continuous_id).continuousAt (by simp [ha₀.ne'])
    simpa [← e] using hc.tendsto

end LaouVol

open LaouVol

/-- **The sphere Jacobian of `[L(g)]`** for the round measure: `a(g, u)^{d−1}`, Barbot's `n − 2`
power of the conformal factor `a = 1/N(L(g)v)` (l.841): `[L(g)]` is conformal with factor `a`
on the `(d−1)`-sphere. -/
theorem hasVolumeJacobianAt_lorentzSphere (A : lorentz d) (u : PenroseSphere d) :
    HasVolumeJacobianAt (roundMeasure d) (lorentzSphere A) (penroseFactor A u ^ (d - 1)) u := by
  obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, (Nat.sub_add_cancel (one_le_of_penroseSphere u)).symm⟩
  have hm' : d - 1 = m := by omega
  rw [hm']
  obtain ⟨hlo, hhi⟩ := tendsto_bound (penroseFactor A u) (penroseFactor_pos A u) m
  rw [← hm] at hlo hhi
  refine hasVolumeJacobianAt_of_bounds (a := penroseFactor A) (lo := fun α β => α ^ d / β)
    (hi := fun α β => β ^ d / α) (continuous_penroseFactor A).continuousAt (penroseFactor_pos A u)
    hlo hhi
    fun α β hα hαβ B hB hab => roundMeasure_image_bounds A hB hα hαβ hab

/-- **The Jacobian of the action of an isometry on `𝒥⁺ ≅ 𝒮 × ℝ`** for the round measure times
Lebesgue measure: `a(g, u)^d` at `(u, s)` — the sphere factor `a^{d−1}` times the fibre factor
`a`; independent of `s` and of the translation part (the shear `s·da + db` is below the
diagonal). -/
theorem hasVolumeJacobianAt_isomPenrose (g : isom d) (w : PenroseSphere d × ℝ) :
    HasVolumeJacobianAt (penroseVolume d) (isomPenrose g) (penroseFactor (linearPart g) w.1 ^ d)
      w := by
  obtain ⟨hlo, hhi⟩ := tendsto_bound (penroseFactor (linearPart g) w.1)
    (penroseFactor_pos (linearPart g) w.1) d
  exact hasVolumeJacobianAt_of_bounds (a := fun w => penroseFactor (linearPart g) w.1)
    (lo := fun α β => α ^ (d + 1) / β) (hi := fun α β => β ^ (d + 1) / α)
    ((continuous_penroseFactor _).comp continuous_fst).continuousAt
    (penroseFactor_pos (linearPart g) w.1) hlo hhi
    fun α β hα hαβ B hB hab => penroseVolume_image_bounds g hB hα hαβ hab

/-- **`g` expands volume at `(u, s) ∈ 𝒥⁺` iff `a(g, u) > 1`**, every isometry, every `s`. -/
theorem expandsVolumeAt_isomPenrose_iff (g : isom d) (w : PenroseSphere d × ℝ) :
    ExpandsVolumeAt (penroseVolume d) (isomPenrose g) w ↔
      IsConformallyExpandingAt (linearPart g) w.1 := by
  have ha := penroseFactor_pos (linearPart g) w.1
  rw [(hasVolumeJacobianAt_isomPenrose g w).expandsVolumeAt_iff (pow_nonneg ha.le _),
    IsConformallyExpandingAt,
    one_lt_pow_iff_of_nonneg ha.le (by have := one_le_of_penroseSphere w.1; omega)]

/-- **`L(g)` expands volume at `u ∈ 𝒮` iff `a(g, u) > 1`**, for `d ≥ 2` (Barbot's `n ≥ 3`). -/
theorem expandsVolumeAt_lorentzSphere_iff (hd : 2 ≤ d) (A : lorentz d) (u : PenroseSphere d) :
    ExpandsVolumeAt (roundMeasure d) (lorentzSphere A) u ↔ IsConformallyExpandingAt A u := by
  have ha := penroseFactor_pos A u
  rw [(hasVolumeJacobianAt_lorentzSphere A u).expandsVolumeAt_iff (pow_nonneg ha.le _),
    IsConformallyExpandingAt, one_lt_pow_iff_of_nonneg ha.le (by omega)]

/-- For `d = 1` (`n = 2`, `𝒮 = S⁰`) no `L(g)` expands volume: its sphere Jacobian is `a⁰ = 1`. -/
theorem not_expandsVolumeAt_lorentzSphere_one (A : lorentz 1) (u : PenroseSphere 1) :
    ¬ ExpandsVolumeAt (roundMeasure 1) (lorentzSphere A) u := by
  rw [(hasVolumeJacobianAt_lorentzSphere A u).expandsVolumeAt_iff (pow_nonneg
    (penroseFactor_pos A u).le _)]
  simp

/-- **`bprop:laoucapulse` (Prop 4.2, l.855) in the volume reading (DEC-102)**, the printed
equality under the unprinted `d ≥ 2` (Barbot's `n ≥ 3`; ⚠ strengthened, false for `d = 1`): for
a linear isometry `g`, the domain of `𝒥⁺ ≅ 𝒮 × ℝ` where the action of `g` expands volume (round measure × Lebesgue) is the preimage under `δ⁺` of the
domain of `𝒮` where the action of `L(g)` expands volume (round measure). The linearity of `g`
is not used. -/
theorem laoucapulse_volume (hd : 2 ≤ d) {g : isom d} (_hg : g • (0 : Minkowski d) = 0) :
    {w | ExpandsVolumeAt (penroseVolume d) (isomPenrose g) w} =
      Prod.fst ⁻¹' {u | ExpandsVolumeAt (roundMeasure d) (lorentzSphere (linearPart g)) u} := by
  ext w
  simp only [mem_setOf_eq, mem_preimage, expandsVolumeAt_isomPenrose_iff,
    expandsVolumeAt_lorentzSphere_iff hd]

/-- The volume-expanding domain of any isometry, in every dimension: `δ⁺⁻¹(U)`,
`U = {a(g, ·) > 1}`. -/
theorem laoucapulse_volume_domain (g : isom d) :
    {w | ExpandsVolumeAt (penroseVolume d) (isomPenrose g) w} =
      Prod.fst ⁻¹' {u | IsConformallyExpandingAt (linearPart g) u} := by
  ext w
  simp only [mem_setOf_eq, mem_preimage, expandsVolumeAt_isomPenrose_iff]

/-- `bprop:laoucapulse` **as printed, in the volume reading** (DEC-102), kept as a `Prop`: for a
linear isometry `g`, the domain of `𝒥⁺` where `g` expands volume is the `δ⁺`-preimage of the
domain of `𝒮` where `L(g)` expands volume. True for `d ≥ 2` (`laoucapulseVolumeReading`), false
for `d = 1` (`not_laoucapulseVolumeReading_one`). -/
def LaoucapulseVolumeReading (d : ℕ) : Prop :=
  ∀ g : isom d, g • (0 : Minkowski d) = 0 →
    {w | ExpandsVolumeAt (penroseVolume d) (isomPenrose g) w} =
      Prod.fst ⁻¹' {u | ExpandsVolumeAt (roundMeasure d) (lorentzSphere (linearPart g)) u}

/-- **`bprop:laoucapulse` holds in the volume reading for `n ≥ 3`.** -/
theorem laoucapulseVolumeReading (hd : 2 ≤ d) : LaoucapulseVolumeReading d :=
  fun _ hg => laoucapulse_volume hd hg

/-- `c(A⁻¹, [A]u) = c(A, u)⁻¹`. -/
theorem lorentzScale_inv_lorentzSphere (A : lorentz d) (u : PenroseSphere d) :
    lorentzScale A⁻¹ (lorentzSphere A u) = (lorentzScale A u)⁻¹ := by
  have h : ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)
      ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)) = nullVec u := by
    rw [Subgroup.coe_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  unfold lorentzScale
  rw [nullVec_lorentzSphere, map_smul, h]
  simp [nullVec, lorentzScale]

/-- **For `n = 2` the printed equality fails in the volume reading**: `S⁰` carries no volume to
expand (`not_expandsVolumeAt_lorentzSphere_one`), while the inverse of the boost
`Laou.boostIsom1` has `a = 2` at `[L]u₊` and so expands volume on `𝒥⁺` there. -/
theorem not_laoucapulseVolumeReading_one : ¬ LaoucapulseVolumeReading 1 := by
  intro h
  set g := Laou.boostIsom1⁻¹
  have hg : g • (0 : Minkowski 1) = 0 := by
    rw [inv_smul_eq_iff, Laou.boostIsom1_smul, map_zero]
  set w : PenroseSphere 1 × ℝ := (lorentzSphere (linearPart Laou.boostIsom1) Laou.uPlus, 0)
  have hw : w ∈ {w | ExpandsVolumeAt (penroseVolume 1) (isomPenrose g) w} := by
    rw [mem_setOf_eq, expandsVolumeAt_isomPenrose_iff, IsConformallyExpandingAt, penroseFactor,
      map_inv, lorentzScale_inv_lorentzSphere, inv_inv, Laou.lorentzScale_boost1_uPlus]
    norm_num
  rw [h g hg] at hw
  exact not_expandsVolumeAt_lorentzSphere_one _ _ hw

/-- **Non-vacuity**, `d = 2`: the boost `Laoucapulse.boostIsom` (`cosh = 5/4`, `sinh = 3/4`)
expands volume at every point `(u₀, s)` of the fibre over `u₀ = (−3/5, 4/5)`, where
`a = 5/4`, including `(u₀, 4)`, where it is not metrically expanding
(`not_laoucapulseMetricReading_two`). -/
theorem boostIsom_expandsVolumeAt_laoBase (s : ℝ) :
    ExpandsVolumeAt (penroseVolume 2) (isomPenrose Laoucapulse.boostIsom)
      (Laoucapulse.laoBase, s) := by
  rw [expandsVolumeAt_isomPenrose_iff, IsConformallyExpandingAt, penroseFactor,
    Laoucapulse.lorentzScale_boost]
  simp [Laoucapulse.laoBase]
  norm_num

/-- **`bprop:laoucapulse` (Prop 4.2, l.855), the two-case form of DEC-104 (ruling K)**, for every
dimension `d` (Barbot's `n = d + 1`) and every linear isometry `g`:

* `d ≥ 2` (`n ≥ 3`), **volume reading** (DEC-102): the domain of `𝒥⁺ ≅ 𝒮 × ℝ` where `g` expands
  volume (round measure × Lebesgue) is the `δ⁺`-preimage of the domain of `𝒮` where `L(g)`
  expands volume (round measure) — `laoucapulse_volume`;
* `d = 1` (`n = 2`, `𝒮 = S⁰`), **conformal reading**: for every euclidean metric `lam·|·|` on `ℝ`,
  the domain where `g` is metrically expanding for the sup product metric is the `δ⁺`-preimage of
  the domain where `L(g)` is conformally expanding (`a(g, ·) > 1`) — `laoucapulse_one`.

The two cases are exhaustive. At `d = 0` (`n = 1`) both hold vacuously: `𝒮 = ∅`
(`isEmpty_penroseSphere_zero`), so both sides of the `d < 2` equality are empty. The volume reading's failure at `d = 1`
(`not_laoucapulseVolumeReading_one`) and the metric reading's refutation at `d = 2`
(`not_laoucapulseMetricReading_two`) are findings, not covered here. -/
theorem bprop_laoucapulse_two_case {g : isom d} (hg : g • (0 : Minkowski d) = 0) :
    (2 ≤ d →
      {w | ExpandsVolumeAt (penroseVolume d) (isomPenrose g) w} =
        Prod.fst ⁻¹' {u | ExpandsVolumeAt (roundMeasure d) (lorentzSphere (linearPart g)) u}) ∧
    (d < 2 → ∀ lam : ℝ, 0 < lam →
      {w | IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w} =
        Prod.fst ⁻¹' {u | IsConformallyExpandingAt (linearPart g) u}) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨fun h => by omega, fun _ lam _ => ?_⟩
    haveI := isEmpty_penroseSphere_zero
    ext w
    exact isEmptyElim w.1
  refine ⟨fun h2 => laoucapulse_volume h2 hg, fun h2 lam hlam => ?_⟩
  obtain rfl : d = 1 := by omega
  exact laoucapulse_one g hlam

end Causal.Flat
