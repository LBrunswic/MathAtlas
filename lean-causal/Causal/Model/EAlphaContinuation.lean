import Causal.Model.EAlphaSectors
import Causal.Port.SingularAtlas

/-!
# Continuing a chart of `E_κ` once around the singular line

`defi:causal_Ealpha` — `ETT.tex:1335`. Not marked: this file proves a model fact about `E_κ`,
`κ > 0`, which the singular `(Isom(E^{1,2}), E^{1,2})`-structure of `E_κ` needs
(`Causal.Model.EAlphaGX`); the row is about every `E_{≥0}`-manifold. Target
`T-ett-ealpha-gx-structure` (the continuation lemma the block asks to state on its own, for
T-ett-bprime-ealpha and T-ett-e-models-bprime).

> For $\alpha>0$, $\mass{\alpha}$ is Minkowski space $\mass{}=\E^{1,2}$ with a cone singularity of
> angle $\alpha$ along a timelike line --- a massive particle --- and $\mass{2\pi}=\mass{}$
> [...] We write $\sing(\mass{\alpha})$ for the singular line and $\reg(\mass{\alpha})$ for its
> complement, which is an $(\isom(\mass{}),\mass{})$-manifold. (`ETT.tex:1327–1333`)

## What is proved (no `sorry`)

* **The continuation lemma** (`exists_smul_devPt_of_ringBox`). Fix a time `t₀`, `ε > 0` and a
  radius `ρ > 0`, and let `F : E_κ → E^{1,2}` be, on each box `ringBox t₀ ε ρ φ` (the times
  `|t − t₀| < ε` times the sector disc of `Causal.Model.EAlphaSectors` centred at `(ρ, φ)`), one
  isometry after the sector chart of that box. Then one `g ∈ Isom(E^{1,2})` gives
  `F (t, polar(ρ, φ)) = g • (t, ρ e^{iφ})` for every `|t − t₀| < ε` and **every real `φ ≥ 0`**:
  `F`, continued along the circle of radius `ρ` about the line, is one isometry after the
  developing map `(t, r, φ) ↦ (t, r e^{iφ})`. Nothing is asked of `F` off the boxes, nor a point
  of the line. The proof chains the boxes at the angles `jδ`, `δ = sin(w)/2`: consecutive sector
  charts differ by the rotation `rotIsom (−δ)` (`exists_rotation`, evaluated at a midpoint), and
  rigidity carries the isometry from one box to the next.
* **Two obstructions**: the holonomy `rotIsom κ` is trivial, `e^{iκ} = 1`
  (`exp_mul_I_eq_one_of_ringBox`: the angles `0` and `κ` are one point of `E_κ`); and if `F` is
  injective on the circle, `2π ∈ κℤ` (`coe_two_pi_eq_zero_of_ringBox`: the angles `0` and `2π`
  have one image). Together: **`κ = 2π`** (`eq_two_pi_of_ringBox`). For `κ ∉ 2πℤ` the first fails;
  for `κ ∈ 2πℤ`, `κ ≥ 4π`, the second.
* **For a chart through the singular line** (`exists_ringBox_of_mem_source`): a chart `e`
  compatible with every sector chart (`(chart k).symm ≫ e` in the `(Isom(E^{1,2}), E^{1,2})`-
  groupoid, as every chart of an `(Isom, E)`-atlas containing them is) whose source contains
  `(t₀, apex)` satisfies these hypotheses on every small circle. Hence `exists_smul_devPt`,
  `exp_mul_I_eq_one_of_mem_source`, `coe_two_pi_eq_zero_of_mem_source`, and
  **`eq_two_pi_of_mem_source`**: such a chart exists only if `κ = 2π`.
* Tools: `devPt`, `ringIndex`, `ringBox`, `chart_ringIndex_polar` (the sector chart at polar
  points), `isPreconnected_coneDisc`, `rotIsom_add`, `rotIsom_zero`, `rotIsom_eq_of_exp_eq`,
  `polar_inj`, `rad_polar`.

## Hypothesis checklist

| paper / roadmap | here |
|---|---|
| `κ > 0` | ✓ carried (`[Fact (0 < α)]`); `κ > 2π` included |
| the charts: of the maximal a.e. atlas (roadmap) | ⚠ weakened: any chart compatible with the sector charts (`he`); the core lemma asks only a map which is a translate of the sector chart on each box |
| `Isom(E^{1,2})` (l.1331) | `Flat.isom 2` (OQ-82); the proof uses only the rotations about the time axis and the rigidity and faithfulness of the action |
| roadmap [r] (b): wide polar sector charts are needed | ⚠ not needed: the disc charts of `EAlphaSectors` chained around a circle of radius `ρ`, `ρ` small |

## SCOPE (disclosed)

* The continuation is stated on one circle of radius `ρ` (any small `ρ`, each with its own `g`),
  not on the whole punctured box; the two obstructions need only one circle. One `g` for all
  radii (rigidity on the overlaps of the boxes at angle `0`) is not stated.
* Nothing here says that a chart through the line exists; at `κ = 2π` one does
  (`Causal.EAlphaGX.twoPiChart`, module `Causal.Model.EAlphaGX`, with
  `Causal.EAlphaGX.continuation_nonvacuous`), so the lemma is not vacuous.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Real Metric Topology TopologicalSpace Filter

namespace EAlphaContinuation

open EAlphaSector

/-- **The developing map** at time `t`, radius `ρ` and real angle `φ`: the point `(t, ρ e^{iφ})`
of `E^{1,2}`. -/
noncomputable def devPt (t ρ φ : ℝ) : Minkowski 2 :=
  (t, Complex.orthonormalBasisOneI.repr ((ρ : ℂ) * Complex.exp (φ * Complex.I)))

/-! ### Rotations about the time axis -/

theorem planeRot_apply' (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    planeRot c v = Complex.orthonormalBasisOneI.repr
      (Complex.exp (c * Complex.I) * Complex.orthonormalBasisOneI.repr.symm v) := by
  conv_lhs => rw [← Complex.orthonormalBasisOneI.repr.apply_symm_apply v]
  exact planeRot_repr c _

theorem rotIsom_smul_repr (c t : ℝ) (u : ℂ) :
    rotIsom c • ((t, Complex.orthonormalBasisOneI.repr u) : Minkowski 2) =
      (t, Complex.orthonormalBasisOneI.repr (Complex.exp (c * Complex.I) * u)) := by
  rw [rotIsom_smul, planeRot_repr]

theorem rotIsom_eq_of_exp_eq {a b : ℝ}
    (h : Complex.exp (a * Complex.I) = Complex.exp (b * Complex.I)) : rotIsom a = rotIsom b := by
  refine eq_of_smul_eq_smul (α := Minkowski 2) fun v => ?_
  rw [rotIsom_smul, rotIsom_smul, planeRot_apply', planeRot_apply', h]

theorem rotIsom_add (a b : ℝ) : rotIsom (a + b) = rotIsom a * rotIsom b := by
  refine eq_of_smul_eq_smul (α := Minkowski 2) fun v => ?_
  rw [mul_smul, rotIsom_smul, rotIsom_smul, rotIsom_smul, planeRot_apply', planeRot_apply',
    planeRot_apply', LinearIsometryEquiv.symm_apply_apply, ← mul_assoc, ← Complex.exp_add]
  congr 4
  push_cast; ring

theorem rotIsom_zero : rotIsom 0 = 1 := by
  refine eq_of_smul_eq_smul (α := Minkowski 2) fun v => ?_
  rw [one_smul, rotIsom_smul, planeRot_apply', Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, LinearIsometryEquiv.apply_symm_apply]

/-! ### Polar points and the sector discs centred on a circle -/

variable {α : ℝ}

/-- Two polar points at one radius `ρ > 0` are equal only if their directions are. -/
theorem polar_inj {ρ : ℝ} (hρ : 0 < ρ) {θ θ' : AddCircle α}
    (h : Cone.polar (ρ, θ) = Cone.polar (ρ, θ')) : θ = θ' := by
  have hd := Cone.mk_eq_mk_iff.1 h
  rw [ConePoint.dist_def, ConePoint.of_r hρ.le, ConePoint.of_r hρ.le] at hd
  have ha : angDist (ConePoint.of ρ θ).θ (ConePoint.of ρ θ').θ = 0 := by
    by_contra hne
    have := Cone.coneE_self_pos hρ (lt_of_le_of_ne (angDist_nonneg _ _) (Ne.symm hne))
      (angDist_le_pi _ _)
    linarith
  have hn : ‖θ - θ'‖ = 0 := by
    by_contra hne
    have := lt_min (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) pi_pos
    unfold angDist at ha
    exact absurd ha (ne_of_gt this)
  exact sub_eq_zero.1 (norm_eq_zero.1 hn)

/-- The sector disc centred at radius `ρ` in the direction `φ`. -/
def ringIndex {ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) : Index α := ⟨⟨ρ, (φ : AddCircle α), hρ.le⟩, hρ⟩

/-- **The box at angle `φ`** about the circle of radius `ρ`: the times `t ∈ (t₀ − ε, t₀ + ε)`
times the sector disc centred at `(ρ, φ)`. -/
def ringBox (t₀ ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) : Set (Massive α) :=
  ball t₀ ε ×ˢ coneDisc (ringIndex (α := α) hρ φ).1

theorem isOpen_ringBox {t₀ ε ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) : IsOpen (ringBox (α := α) t₀ ε hρ φ) :=
  isOpen_ball.prod isOpen_ball

/-- A polar point of radius `ρ ≥ 0` is at distance `ρ` from the apex. -/
theorem rad_polar {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : AddCircle α) : Cone.rad (Cone.polar (ρ, θ)) = ρ := by
  unfold Cone.polar
  rw [Cone.rad_mk, ConePoint.of_r hρ]

/-- The polar point of radius `ρ` and angle `φ₀ + ψ`, `|ψ| < π`, is the polar position
`ρ e^{iψ}` around the direction `φ₀`. -/
theorem polar_eq_fromPlane {ρ : ℝ} (hρ : 0 < ρ) (φ₀ ψ : ℝ) (hψ : |ψ| < π) :
    Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α)) =
      fromPlane (φ₀ : AddCircle α) ((ρ : ℂ) * Complex.exp (ψ * Complex.I)) := by
  have hn : ‖(ρ : ℂ) * Complex.exp (ψ * Complex.I)‖ = ρ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ]
  have ha : Complex.arg ((ρ : ℂ) * Complex.exp (ψ * Complex.I)) = ψ := by
    rw [Complex.arg_real_mul _ hρ, Complex.exp_mul_I]
    rw [abs_lt] at hψ
    exact Complex.arg_cos_add_sin_mul_I ⟨hψ.1, hψ.2.le⟩
  unfold Cone.polar fromPlane
  congr 1
  ext
  · rw [ConePoint.of_r hρ.le]; exact hn.symm
  · show ((φ₀ + ψ : ℝ) : AddCircle α) = (φ₀ : AddCircle α) + _
    rw [ha, AddCircle.coe_add]

variable [hα : Fact (0 < α)]

omit hα in
/-- `ρ e^{iψ}` lies in the planar disc of radius `ρ sin w` about `ρ` when `|ψ| < sin w`. -/
theorem mem_planeDisc {ρ : ℝ} (hρ : 0 < ρ) {ψ : ℝ} (hψ : |ψ| < sin (halfAngle α)) :
    (ρ : ℂ) * Complex.exp (ψ * Complex.I) ∈ planeDisc α ρ := by
  show dist ((ρ : ℂ) * Complex.exp (ψ * Complex.I)) ρ < ρ * sin (halfAngle α)
  rw [dist_eq_norm, show (ρ : ℂ) * Complex.exp (ψ * Complex.I) - ρ =
      ρ * (Complex.exp (Complex.I * ψ) - 1) by rw [mul_comm (ψ : ℂ)]; ring, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have h1 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := ψ)
  rw [Real.norm_eq_abs] at h1
  calc ρ * ‖Complex.exp (Complex.I * ψ) - 1‖ ≤ ρ * |ψ| := mul_le_mul_of_nonneg_left h1 hρ.le
    _ < ρ * sin (halfAngle α) := mul_lt_mul_of_pos_left hψ hρ

/-- **The sector chart centred at `(ρ, φ₀)` at a polar point of radius `ρ`**: the point of angle
`φ₀ + ψ`, `|ψ| < sin w`, is in its source, with value `(t, ρ e^{iψ})`. -/
theorem chart_ringIndex_polar {ρ : ℝ} (hρ : 0 < ρ) (φ₀ ψ : ℝ) (hψ : |ψ| < sin (halfAngle α))
    (t : ℝ) :
    ((t, Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α))) : Massive α) ∈
        (chart (ringIndex hρ φ₀)).source ∧
      chart (ringIndex hρ φ₀) (t, Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α))) =
        ((t, Complex.orthonormalBasisOneI.repr ((ρ : ℂ) * Complex.exp (ψ * Complex.I))) :
          Minkowski 2) := by
  set k : Index α := ringIndex hρ φ₀
  have hψπ : |ψ| < π := hψ.trans_le ((sin_le_one _).trans (by linarith [pi_gt_three]))
  have hz : (ρ : ℂ) * Complex.exp (ψ * Complex.I) ∈ (planeChart k).source := by
    rw [planeChart_source]; exact mem_planeDisc hρ hψ
  have hpol : Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α)) =
      planeChart k ((ρ : ℂ) * Complex.exp (ψ * Complex.I)) := by
    rw [planeChart_apply]; exact polar_eq_fromPlane hρ φ₀ ψ hψπ
  refine ⟨?_, ?_⟩
  · rw [chart_source]
    refine ⟨trivial, ?_⟩
    show Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α)) ∈ coneDisc k.1
    rw [hpol, ← planeChart_target]
    exact (planeChart k).map_source hz
  · rw [chart_apply]
    refine Prod.ext rfl ?_
    show coneChart k (Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α))) = _
    rw [coneChart_apply, hpol, (planeChart k).left_inv hz]

/-- The disc of a sector chart is preconnected (the image of a planar disc). -/
theorem isPreconnected_coneDisc (k : Index α) : IsPreconnected (coneDisc k.1) := by
  rw [← planeChart_target, ← (planeChart k).image_source_eq_target, planeChart_source]
  exact (convex_ball (k.1.r : ℂ) (k.1.r * sin (halfAngle α))).isPreconnected.image _
    (planeChart k).continuousOn

omit hα in
/-- The disc of a sector chart centred at radius `r` lies within `2r` of the apex. -/
theorem coneDisc_subset_ball_apex (p : ConePoint α) :
    coneDisc p ⊆ ball (Cone.apex : Cone α) (2 * p.r) := by
  intro y hy
  have h1 : dist y (Cone.mk p) < p.r * sin (halfAngle α) := hy
  have h2 : dist (Cone.mk p) (Cone.apex : Cone α) = p.r := by
    rw [dist_comm]; exact Cone.rad_mk p
  have h3 := sin_le_one (halfAngle α)
  have h4 := p.r_nonneg
  rw [mem_ball]
  calc dist y Cone.apex ≤ dist y (Cone.mk p) + dist (Cone.mk p) Cone.apex := dist_triangle _ _ _
    _ < 2 * p.r := by rw [h2]; nlinarith

theorem ringBox_subset_source {t₀ ε ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) :
    ringBox t₀ ε hρ φ ⊆ (chart (ringIndex (α := α) hρ φ)).source := by
  rintro ⟨t, y⟩ ⟨-, hy⟩
  rw [chart_source]
  exact ⟨trivial, hy⟩

theorem isPreconnected_ringBox {t₀ ε ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) :
    IsPreconnected (ringBox (α := α) t₀ ε hρ φ) :=
  (convex_ball t₀ ε).isPreconnected.prod (isPreconnected_coneDisc _)

/-- The polar point of radius `ρ` and angle `φ₀ + ψ`, `|ψ| < sin w`, is in the box at `φ₀`. -/
theorem polar_mem_ringBox {t₀ ε ρ : ℝ} (hρ : 0 < ρ) (φ₀ ψ : ℝ) (hψ : |ψ| < sin (halfAngle α))
    {t : ℝ} (ht : t ∈ ball t₀ ε) :
    ((t, Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α))) : Massive α) ∈ ringBox t₀ ε hρ φ₀ := by
  have h1 := (chart_ringIndex_polar hρ φ₀ ψ hψ t).1
  rw [chart_source] at h1
  exact ⟨ht, h1.2⟩

/-! ### The continuation lemma -/

/-- **The continuation lemma.** Let `F : E_κ → E^{1,2}` be, on each box about the circle of radius
`ρ` (`ringBox`), one isometry after the sector chart of the box. Then on that circle, at the times
of the boxes, `F` is one isometry after the developing map, for every real angle `φ ≥ 0`:
`F (t, polar(ρ, φ)) = g • (t, ρ e^{iφ})`. Nothing is asked of `F` off the boxes, nor its continuity,
nor a point of the singular line. -/
theorem exists_smul_devPt_of_ringBox {F : Massive α → Minkowski 2} {t₀ ε ρ : ℝ} (hε : 0 < ε)
    (hρ0 : 0 < ρ)
    (hF : ∀ φ : ℝ, ∃ h : Flat.isom 2, ∀ y ∈ ringBox t₀ ε hρ0 φ,
      chart (ringIndex (α := α) hρ0 φ) y = h • F y) :
    ∃ g : Flat.isom 2, ∀ t ∈ ball t₀ ε, ∀ φ : ℝ, 0 ≤ φ →
      F (t, Cone.polar (ρ, (φ : AddCircle α))) = g • devPt t ρ φ := by
  have hsw : 0 < sin (halfAngle α) := sin_halfAngle_pos
  set δ : ℝ := sin (halfAngle α) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  set S : ℝ → Set (Massive α) := ringBox t₀ ε hρ0 with hSdef
  have hSc : ∀ φ, S φ ⊆ (chart (ringIndex (α := α) hρ0 φ)).source := ringBox_subset_source hρ0
  have hSo : ∀ φ, IsOpen (S φ) := fun φ => isOpen_ringBox hρ0 φ
  -- the polar points of radius `ρ` in the boxes, and their chart values
  have hpt : ∀ φ₀ ψ : ℝ, |ψ| < sin (halfAngle α) → ∀ t ∈ ball t₀ ε,
      ((t, Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α))) : Massive α) ∈ S φ₀ ∧
        chart (ringIndex (α := α) hρ0 φ₀) (t, Cone.polar (ρ, ((φ₀ + ψ : ℝ) : AddCircle α))) =
          ((t, Complex.orthonormalBasisOneI.repr ((ρ : ℂ) * Complex.exp (ψ * Complex.I))) :
            Minkowski 2) := fun φ₀ ψ hψ t ht =>
    ⟨polar_mem_ringBox hρ0 φ₀ ψ hψ ht, (chart_ringIndex_polar hρ0 φ₀ ψ hψ t).2⟩
  have ht₀ : t₀ ∈ ball t₀ ε := mem_ball_self hε
  have hδw : |δ / 2| < sin (halfAngle α) := by
    rw [abs_of_pos (by positivity)]; linarith
  have hδw' : |-(δ / 2)| < sin (halfAngle α) := by rw [abs_neg]; exact hδw
  -- the chain: on the box at angle `jδ`, `F` is `g * rotIsom (jδ)` after the sector chart
  have hchain : ∃ g : Flat.isom 2, ∀ j : ℕ, ∀ y ∈ S (j * δ),
      F y = (g * rotIsom (j * δ)) • chart (ringIndex (α := α) hρ0 (j * δ)) y := by
    obtain ⟨h₀, hh₀⟩ := hF 0
    refine ⟨h₀⁻¹, fun j => ?_⟩
    induction j with
    | zero =>
      intro y hy
      rw [Nat.cast_zero, zero_mul] at hy ⊢
      rw [rotIsom_zero, mul_one, hh₀ y hy, inv_smul_smul]
    | succ j ih =>
      obtain ⟨h, hh⟩ := hF (((j + 1 : ℕ) : ℝ) * δ)
      obtain ⟨c, hc⟩ := exists_rotation (ringIndex (α := α) hρ0 (j * δ))
        (ringIndex (α := α) hρ0 (((j + 1 : ℕ) : ℝ) * δ))
      -- the midpoint of the two discs
      have hm₁ := hpt (j * δ) (δ / 2) hδw t₀ ht₀
      have hm₂ := hpt (((j + 1 : ℕ) : ℝ) * δ) (-(δ / 2)) hδw' t₀ ht₀
      have hmid : (((j + 1 : ℕ) : ℝ) * δ + -(δ / 2) : ℝ) = j * δ + δ / 2 := by push_cast; ring
      rw [hmid] at hm₂
      -- the rotation from one disc to the next is `rotIsom (-δ)`
      have hcδ : rotIsom c = rotIsom (-δ) := by
        apply rotIsom_eq_of_exp_eq
        have h1 := hc _ ⟨hSc _ hm₁.1, hSc _ hm₂.1⟩
        rw [hm₁.2, hm₂.2, rotIsom_smul_repr] at h1
        have h2 := Complex.orthonormalBasisOneI.repr.injective (congrArg Prod.snd h1)
        have hne : (ρ : ℂ) * Complex.exp (((δ / 2 : ℝ) : ℂ) * Complex.I) ≠ 0 :=
          mul_ne_zero (Complex.ofReal_ne_zero.2 hρ0.ne') (Complex.exp_ne_zero _)
        have h3 : Complex.exp (c * Complex.I) * ((ρ : ℂ) * Complex.exp (((δ / 2 : ℝ) : ℂ) * Complex.I))
            = Complex.exp (((-δ : ℝ) : ℂ) * Complex.I) *
              ((ρ : ℂ) * Complex.exp (((δ / 2 : ℝ) : ℂ) * Complex.I)) := by
          rw [← h2, mul_left_comm, ← Complex.exp_add]
          congr 3
          push_cast; ring
        exact mul_right_cancel₀ hne h3
      -- rigidity on the image of the overlap under the sector chart
      have hOo : IsOpen (S (j * δ) ∩ S (((j + 1 : ℕ) : ℝ) * δ)) := (hSo _).inter (hSo _)
      have hOs : S (j * δ) ∩ S (((j + 1 : ℕ) : ℝ) * δ) ⊆
          (chart (ringIndex (α := α) hρ0 (j * δ))).source := fun y hy => hSc _ hy.1
      have hgrp : h * (h₀⁻¹ * rotIsom (j * δ)) = rotIsom (-δ) := by
        refine eq_of_smul_eq_smul (α := Minkowski 2) fun m => ?_
        refine IsRigidAction.smul_eq_of_eqOn
          ((chart _).isOpen_image_of_subset_source hOo hOs) ⟨_, _, ⟨hm₁.1, hm₂.1⟩, rfl⟩ ?_ m
        rintro _ ⟨y, hy, rfl⟩
        show (h * (h₀⁻¹ * rotIsom (j * δ))) • chart _ y = rotIsom (-δ) • chart _ y
        rw [mul_smul, ← ih y hy.1, ← hh y hy.2, ← hcδ, hc y ⟨hSc _ hy.1, hSc _ hy.2⟩]
      have hinv : h₀⁻¹ * rotIsom (((j + 1 : ℕ) : ℝ) * δ) = h⁻¹ := by
        symm
        refine inv_eq_of_mul_eq_one_right ?_
        rw [show (((j + 1 : ℕ) : ℝ) * δ) = j * δ + δ by push_cast; ring, rotIsom_add,
          ← mul_assoc, ← mul_assoc, mul_assoc h, hgrp, ← rotIsom_add, neg_add_cancel,
          rotIsom_zero]
      intro y hy
      rw [hinv, hh y hy, inv_smul_smul]
  obtain ⟨g, hg⟩ := hchain
  refine ⟨g, fun t ht φ hφ => ?_⟩
  set j : ℕ := ⌊φ / δ⌋₊ with hjdef
  have hj1 : (j : ℝ) * δ ≤ φ := by
    have := Nat.floor_le (div_nonneg hφ hδ0.le)
    rwa [← hjdef, le_div_iff₀ hδ0] at this
  have hj2 : φ < (j : ℝ) * δ + δ := by
    have := Nat.lt_floor_add_one (φ / δ)
    rw [← hjdef, div_lt_iff₀ hδ0] at this
    linarith
  have hψ : |φ - j * δ| < sin (halfAngle α) := by
    rw [abs_of_nonneg (by linarith)]; linarith
  obtain ⟨hmem, hval⟩ := hpt (j * δ) (φ - j * δ) hψ t ht
  rw [show (j : ℝ) * δ + (φ - j * δ) = φ by ring] at hmem hval
  rw [hg j _ hmem, hval, mul_smul, rotIsom_smul_repr]
  unfold devPt
  congr 3
  rw [mul_left_comm, ← Complex.exp_add]
  congr 3
  push_cast; ring

/-- **First obstruction: the holonomy about the line is trivial.** Under the hypotheses of the
continuation lemma, the angles `0` and `κ` give one point of `E_κ`, so `e^{iκ} = 1`. -/
theorem exp_mul_I_eq_one_of_ringBox {F : Massive α → Minkowski 2} {t₀ ε ρ : ℝ} (hε : 0 < ε)
    (hρ0 : 0 < ρ)
    (hF : ∀ φ : ℝ, ∃ h : Flat.isom 2, ∀ y ∈ ringBox t₀ ε hρ0 φ,
      chart (ringIndex (α := α) hρ0 φ) y = h • F y) :
    Complex.exp (α * Complex.I) = 1 := by
  obtain ⟨g, hg⟩ := exists_smul_devPt_of_ringBox hε hρ0 hF
  have ht : t₀ ∈ ball t₀ ε := mem_ball_self hε
  have h0 := hg t₀ ht 0 le_rfl
  have hk := hg t₀ ht α hα.out.le
  rw [AddCircle.coe_period] at hk
  rw [show ((0 : ℝ) : AddCircle α) = 0 by simp] at h0
  have h1 : devPt t₀ ρ 0 = devPt t₀ ρ α := MulAction.injective g (h0.symm.trans hk)
  have h2 := Complex.orthonormalBasisOneI.repr.injective (congrArg Prod.snd h1)
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h2
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hρ0.ne') h2).symm

/-- **Second obstruction: injectivity.** Under the hypotheses of the continuation lemma, if `F` is
injective on the circle of radius `ρ` at the time `t₀`, the points of angles `0` and `2π` of that
circle have one image, so they are one point: `2π ∈ κℤ`. -/
theorem coe_two_pi_eq_zero_of_ringBox {F : Massive α → Minkowski 2} {t₀ ε ρ : ℝ} (hε : 0 < ε)
    (hρ0 : 0 < ρ)
    (hF : ∀ φ : ℝ, ∃ h : Flat.isom 2, ∀ y ∈ ringBox t₀ ε hρ0 φ,
      chart (ringIndex (α := α) hρ0 φ) y = h • F y)
    (hinj : InjOn F {y : Massive α | y.1 = t₀ ∧ Cone.rad y.2 = ρ}) :
    ((2 * π : ℝ) : AddCircle α) = 0 := by
  obtain ⟨g, hg⟩ := exists_smul_devPt_of_ringBox hε hρ0 hF
  have ht : t₀ ∈ ball t₀ ε := mem_ball_self hε
  have h0 := hg t₀ ht 0 le_rfl
  have h2 := hg t₀ ht (2 * π) (by positivity)
  have hdev : devPt t₀ ρ (2 * π) = devPt t₀ ρ 0 := by
    unfold devPt
    rw [show (((2 * π : ℝ) : ℂ) * Complex.I) = 2 * π * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  have heq : F (t₀, Cone.polar (ρ, ((2 * π : ℝ) : AddCircle α))) =
      F (t₀, Cone.polar (ρ, ((0 : ℝ) : AddCircle α))) := by
    rw [h2, h0, hdev]
  have hpt := hinj ⟨rfl, rad_polar hρ0.le _⟩ ⟨rfl, rad_polar hρ0.le _⟩ heq
  have hpol := polar_inj hρ0 (congrArg Prod.snd hpt)
  rw [hpol]
  simp

/-- **Both obstructions together: `κ = 2π`.** A map which, about a circle of radius `ρ`, is one
isometry after each sector chart and is injective on that circle exists only for `κ = 2π`. -/
theorem eq_two_pi_of_ringBox {F : Massive α → Minkowski 2} {t₀ ε ρ : ℝ} (hε : 0 < ε)
    (hρ0 : 0 < ρ)
    (hF : ∀ φ : ℝ, ∃ h : Flat.isom 2, ∀ y ∈ ringBox t₀ ε hρ0 φ,
      chart (ringIndex (α := α) hρ0 φ) y = h • F y)
    (hinj : InjOn F {y : Massive α | y.1 = t₀ ∧ Cone.rad y.2 = ρ}) : α = 2 * π := by
  have hpos := hα.out
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 (exp_mul_I_eq_one_of_ringBox hε hρ0 hF)
  have hαn : α = n * (2 * π) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    push Not at h
    nlinarith [pi_pos]
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0 : ℤ) < n := by exact_mod_cast hn0
    exact_mod_cast this
  have h2π : 2 * π ≤ α := by rw [hαn]; nlinarith [pi_pos]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff α).1 (coe_two_pi_eq_zero_of_ringBox hε hρ0 hF hinj)
  rw [zsmul_eq_mul] at hm
  have hm0 : (0 : ℝ) < m := by
    by_contra h
    push Not at h
    nlinarith [pi_pos]
  have hm1 : (1 : ℝ) ≤ m := by
    have : (0 : ℤ) < m := by exact_mod_cast hm0
    exact_mod_cast this
  exact le_antisymm (by nlinarith) h2π

/-! ### For a chart through the singular line -/

/-- **A chart through the singular line satisfies the hypotheses of the continuation lemma on
every small circle**: if `e` is compatible with every sector chart and `(t₀, apex) ∈ e.source`,
there is `ε > 0` such that for every `ρ ∈ (0, ε)` the boxes about the circle of radius `ρ` and the
points at distance `< 2ε` from `(t₀, apex)` lie in the source, and on each box the sector chart is
one isometry after `e`. -/
theorem exists_ringBox_of_mem_source {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : ∀ k : Index α, e.symm.trans (chart k) ∈ gxGroupoid (Flat.isom 2) (Minkowski 2))
    {t₀ : ℝ} (hp : ((t₀, Cone.apex) : Massive α) ∈ e.source) :
    ∃ ε > 0, ball ((t₀, Cone.apex) : Massive α) (2 * ε) ⊆ e.source ∧
      ∀ ρ (hρ0 : 0 < ρ), ρ < ε → ∀ φ : ℝ, ringBox t₀ ε hρ0 φ ⊆ e.source ∧
        ∃ h : Flat.isom 2, ∀ y ∈ ringBox t₀ ε hρ0 φ, chart (ringIndex (α := α) hρ0 φ) y = h • e y := by
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 e.open_source _ hp
  refine ⟨ε₀ / 2, by positivity, by rw [show 2 * (ε₀ / 2) = ε₀ by ring]; exact hball,
    fun ρ hρ0 hρε φ => ?_⟩
  have hSe : ringBox t₀ (ε₀ / 2) hρ0 φ ⊆ e.source := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    apply hball
    rw [← ball_prod_same]
    refine ⟨ball_subset_ball (by linarith) ht, ?_⟩
    exact ball_subset_ball (by show 2 * ρ ≤ ε₀; linarith) (coneDisc_subset_ball_apex _ hy)
  exact ⟨hSe, exists_smul_eq_on_of_isPreconnected (isPreconnected_ringBox hρ0 φ) hSe
    fun x hx => eventually_smul_eq_of_mem_gxGroupoid (he _) (hSe hx)
      (ringBox_subset_source hρ0 φ hx)⟩

/-- **A chart through the singular line, continued once around it, is one isometry after the
developing map.** Let `e : E_κ ⇀ E^{1,2}` be compatible with every sector chart and contain a
point `(t₀, apex)` of the singular line in its source. There is `ε > 0` such that for every
`ρ ∈ (0, ε)` some `g ∈ Isom(E^{1,2})` has `e (t, polar(ρ, φ)) = g • (t, ρ e^{iφ})` for all
`t ∈ (t₀ − ε, t₀ + ε)` and all real `φ ≥ 0`, these points lying in the source of `e`. -/
theorem exists_smul_devPt {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : ∀ k : Index α, e.symm.trans (chart k) ∈ gxGroupoid (Flat.isom 2) (Minkowski 2))
    {t₀ : ℝ} (hp : ((t₀, Cone.apex) : Massive α) ∈ e.source) :
    ∃ ε > 0, ∀ ρ ∈ Ioo 0 ε, ∃ g : Flat.isom 2, ∀ t ∈ ball t₀ ε, ∀ φ : ℝ, 0 ≤ φ →
      ((t, Cone.polar (ρ, (φ : AddCircle α))) : Massive α) ∈ e.source ∧
        e (t, Cone.polar (ρ, (φ : AddCircle α))) = g • devPt t ρ φ := by
  obtain ⟨ε, hε, hball, hbox⟩ := exists_ringBox_of_mem_source he hp
  refine ⟨ε, hε, fun ρ hρ => ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_devPt_of_ringBox hε hρ.1 fun φ => (hbox ρ hρ.1 hρ.2 φ).2
  refine ⟨g, fun t ht φ hφ => ⟨hball ?_, hg t ht φ hφ⟩⟩
  rw [← ball_prod_same]
  refine ⟨ball_subset_ball (by linarith) ht, ?_⟩
  rw [mem_ball, dist_comm]
  show Cone.rad _ < 2 * ε
  rw [rad_polar hρ.1.le]
  linarith [hρ.2]

omit hα in
/-- The circle of radius `ρ < 2ε` at the time `t₀` lies in the ball of radius `2ε` about
`(t₀, apex)`. -/
theorem circle_subset_ball {t₀ ρ ε : ℝ} (hρ : ρ < 2 * ε) :
    {y : Massive α | y.1 = t₀ ∧ Cone.rad y.2 = ρ} ⊆ ball ((t₀, Cone.apex) : Massive α) (2 * ε) := by
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  rw [← ball_prod_same]
  refine ⟨?_, ?_⟩
  · rw [show t = t₀ from ht]
    exact mem_ball_self (by have := Cone.rad_nonneg y; simp only at hy; linarith)
  · rw [mem_ball, dist_comm]
    show Cone.rad y < 2 * ε
    simp only at hy
    rw [hy]
    exact hρ

/-- **First obstruction, for a chart through the line**: `e^{iκ} = 1`. -/
theorem exp_mul_I_eq_one_of_mem_source {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : ∀ k : Index α, e.symm.trans (chart k) ∈ gxGroupoid (Flat.isom 2) (Minkowski 2))
    {t₀ : ℝ} (hp : ((t₀, Cone.apex) : Massive α) ∈ e.source) :
    Complex.exp (α * Complex.I) = 1 := by
  obtain ⟨ε, hε, -, hbox⟩ := exists_ringBox_of_mem_source he hp
  have hρ : (0 : ℝ) < ε / 2 := by positivity
  exact exp_mul_I_eq_one_of_ringBox hε hρ fun φ => (hbox (ε / 2) hρ (by linarith) φ).2

/-- **Second obstruction, for a chart through the line**: `2π ∈ κℤ`. -/
theorem coe_two_pi_eq_zero_of_mem_source {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : ∀ k : Index α, e.symm.trans (chart k) ∈ gxGroupoid (Flat.isom 2) (Minkowski 2))
    {t₀ : ℝ} (hp : ((t₀, Cone.apex) : Massive α) ∈ e.source) :
    ((2 * π : ℝ) : AddCircle α) = 0 := by
  obtain ⟨ε, hε, hball, hbox⟩ := exists_ringBox_of_mem_source he hp
  have hρ : (0 : ℝ) < ε / 2 := by positivity
  exact coe_two_pi_eq_zero_of_ringBox hε hρ (fun φ => (hbox (ε / 2) hρ (by linarith) φ).2)
    (e.injOn.mono ((circle_subset_ball (by linarith)).trans hball))

/-- **A chart compatible with the sector charts reaches the singular line only if `κ = 2π`.** -/
theorem eq_two_pi_of_mem_source {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : ∀ k : Index α, e.symm.trans (chart k) ∈ gxGroupoid (Flat.isom 2) (Minkowski 2))
    {t₀ : ℝ} (hp : ((t₀, Cone.apex) : Massive α) ∈ e.source) : α = 2 * π := by
  obtain ⟨ε, hε, hball, hbox⟩ := exists_ringBox_of_mem_source he hp
  have hρ : (0 : ℝ) < ε / 2 := by positivity
  exact eq_two_pi_of_ringBox hε hρ (fun φ => (hbox (ε / 2) hρ (by linarith) φ).2)
    (e.injOn.mono ((circle_subset_ball (by linarith)).trans hball))

/-- The same, for a point of `singLine κ`. -/
theorem eq_two_pi_of_mem_source_singLine {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : ∀ k : Index α, e.symm.trans (chart k) ∈ gxGroupoid (Flat.isom 2) (Minkowski 2))
    {x : Massive α} (hx : x ∈ e.source) (hxs : x ∈ singLine α) : α = 2 * π := by
  have hxe : x = (x.1, Cone.apex) := Prod.ext rfl hxs
  exact eq_two_pi_of_mem_source he (t₀ := x.1) (hxe ▸ hx)

end EAlphaContinuation

end Causal
