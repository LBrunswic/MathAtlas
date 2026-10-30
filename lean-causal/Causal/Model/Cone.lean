import Causal.Static
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The flat cone `C_α` of angle `α` as a proper geodesic metric space

No label of the paper is certified by this file: it builds the space part `C_α` of the
massive-particle model spaces `E_α = ℝ × C_α` (`Causal.Model.Massive`), from the
unlabelled paragraph `ETT.tex:1327`:

> For $\alpha>0$, $\mass{\alpha}$ is Minkowski space $\mass{}=\E^{1,2}$ with a cone singularity of
> angle $\alpha$ along a timelike line --- a massive particle --- and $\mass{2\pi}=\mass{}$; in
> cylindrical coordinates $(t,r,\theta)$ its metric is $-\d t^2+\d r^2+r^2\d \theta^2$.

## The construction

Mathlib has no cone, glued or quotient length metric at this pin (`Metric.Gluing` glues two
spaces along isometric subsets, which a sector glued to itself is not), so the cone is built from
its distance formula. A point is `(r, θ)`, `r ≥ 0`, `θ ∈ ℝ/αℤ` (`AddCircle α`, `ConePoint`); with
`δ = ‖θ₁ − θ₂‖` the distance of the directions on the circle of length `α`,

  `d((r₁,θ₁),(r₂,θ₂)) = √(r₁² + r₂² − 2 r₁ r₂ cos(min(δ, π)))`

(`coneE`, `angDist`): the law of cosines when the directions are less than `π` apart, `r₁ + r₂`
(through the apex) otherwise. It is a pseudometric (`ConePoint.instPseudoMetricSpace`): the
triangle inequality is the planar one after unfolding two angles `a`, `b'` with `a + b' ≤ π` side
by side (`coneE_add_le`, in `ℂ`), plus the monotonicity of the law of cosines in the angle on
`[0, π]` (`coneE_mono`). The directions of `r = 0` are at distance `0`, and `C_α` (`Cone`) is the
separation quotient, which identifies exactly them: the apex (`Cone.apex`).

## What is proved, for `α > 0`

* `Cone α` is a metric space, **proper** (closed balls are images of `[0, R] × ℝ/αℤ`), hence
  complete, and **geodesic** (`GeodesicSpace`, `Causal.Static`): through the apex when
  the directions are `≥ π` apart or one end is the apex (`exists_geodesic_through_apex`), along
  the planar segment of the flat sector they span otherwise (`exists_geodesic_straight`, in polar
  coordinates through `arctan`). Nothing about `α` beyond `α > 0` is used: `α > 2π` included.
* **`C_{2π}` is the Euclidean plane** (`coneTwoPiIsoComplex : Cone (2π) ≃ᵢ ℂ`,
  `coneTwoPiIsoEuclidean : Cone (2π) ≃ᵢ EuclideanSpace ℝ (Fin 2)`), by `(r, θ) ↦ r e^{iθ}`; the
  apex goes to `0`.
* **For `α ≠ 2π` the apex has no neighbourhood isometric to an open subset of the plane**
  (`apex_not_euclidean`): for `α < 2π` it is the midpoint of no two points, for `α > 2π` a point
  has a whole arc of antipodes through it.
* Sanity: `dist(apex, x) = rad x`; on one ray the distance is `|r₁ − r₂|`
  (`ConePoint.dist_same_dir`), across `≥ π` it is `r₁ + r₂` (`ConePoint.dist_of_pi_le`).

## Hypothesis checklist

| paper | here |
|---|---|
| `α > 0` | ✓ carried (`[Fact (0 < α)]`); the metric space itself is defined for every `α` |

## SCOPE (disclosed)

* **The definition is the distance formula, not the length metric of `dr² + r² dθ²`.** The two
  agree: the formula is the Euclidean cone over the circle of length `α` (Bridson–Haefliger,
  *Metric spaces of non-positive curvature*, Def. I.5.6, cited from memory, not checked against a
  copy); off the apex, directions `< π` apart span a flat sector isometric to a planar one
  (`coneE_eq_norm`: the distance is `|r₁ − r₂ e^{iδ}|`), so the metric is locally the flat one; a
  path between directions `≥ π` apart must sweep an angle `≥ π` and is no shorter than
  `r₁ + r₂`. The identification with the Riemannian length metric is argued here in prose, not
  formalized (the library has no Riemannian metric).
* That every point **other than** the apex has a neighbourhood isometric to a Euclidean disc is
  not formalized (only the apex half of "the apex is the unique singular point").

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Real Metric Topology

/-! ### The law of cosines -/

/-- The law of cosines: the distance between two points of the plane at distances `r`, `s` from
the origin and seen from it under the angle `a`. -/
noncomputable def coneE (r s a : ℝ) : ℝ := √(r ^ 2 + s ^ 2 - 2 * r * s * cos a)

theorem coneE_radicand (r s a : ℝ) :
    r ^ 2 + s ^ 2 - 2 * r * s * cos a = (r - s * cos a) ^ 2 + (s * sin a) ^ 2 := by
  have := sin_sq_add_cos_sq a
  linear_combination (-s ^ 2) * this

theorem coneE_radicand_nonneg (r s a : ℝ) : 0 ≤ r ^ 2 + s ^ 2 - 2 * r * s * cos a := by
  rw [coneE_radicand]; positivity

theorem coneE_nonneg (r s a : ℝ) : 0 ≤ coneE r s a := sqrt_nonneg _

theorem coneE_sq (r s a : ℝ) : coneE r s a ^ 2 = r ^ 2 + s ^ 2 - 2 * r * s * cos a :=
  sq_sqrt (coneE_radicand_nonneg r s a)

/-- The law of cosines is the modulus of `r − s e^{ia}`. -/
theorem coneE_eq_norm (r s a : ℝ) :
    coneE r s a = ‖(r : ℂ) - s * Complex.exp (a * Complex.I)‖ := by
  rw [Complex.norm_def, Complex.normSq_apply, coneE, coneE_radicand]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, Complex.sub_im,
    Complex.mul_im, zero_sub]
  ring

theorem coneE_comm (r s a : ℝ) : coneE r s a = coneE s r a := by
  unfold coneE; ring_nf

theorem coneE_neg (r s a : ℝ) : coneE r s (-a) = coneE r s a := by
  unfold coneE; rw [cos_neg]

theorem coneE_abs (r s a : ℝ) : coneE r s |a| = coneE r s a := by
  rcases abs_choice a with h | h <;> rw [h]; exact coneE_neg r s a

theorem coneE_zero (r s : ℝ) : coneE r s 0 = |r - s| := by
  unfold coneE; rw [cos_zero, ← sqrt_sq_eq_abs]; ring_nf

theorem coneE_pi (r s : ℝ) : coneE r s π = |r + s| := by
  unfold coneE; rw [cos_pi, ← sqrt_sq_eq_abs]; ring_nf

theorem coneE_zero_left (s a : ℝ) : coneE 0 s a = |s| := by
  unfold coneE; rw [← sqrt_sq_eq_abs]; ring_nf

theorem coneE_zero_right (r a : ℝ) : coneE r 0 a = |r| := by
  rw [coneE_comm, coneE_zero_left]

/-- **The planar triangle inequality**, written with angles: `a`, `b` are the angles at the
origin of the triangles `(P₁, P₂)` and `(P₂, P₃)`. -/
theorem coneE_add_le (r₁ r₂ r₃ a b : ℝ) :
    coneE r₁ r₃ (a + b) ≤ coneE r₁ r₂ a + coneE r₂ r₃ b := by
  simp only [coneE_eq_norm]
  have h : (r₂ : ℂ) * Complex.exp (a * Complex.I) - r₃ * Complex.exp ((a + b : ℝ) * Complex.I) =
      Complex.exp (a * Complex.I) * ((r₂ : ℂ) - r₃ * Complex.exp (b * Complex.I)) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]; ring
  calc ‖(r₁ : ℂ) - r₃ * Complex.exp ((a + b : ℝ) * Complex.I)‖
      ≤ ‖(r₁ : ℂ) - r₂ * Complex.exp (a * Complex.I)‖ +
        ‖(r₂ : ℂ) * Complex.exp (a * Complex.I) - r₃ * Complex.exp ((a + b : ℝ) * Complex.I)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = _ := by rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The law of cosines is non-decreasing in the angle over `[0, π]`. -/
theorem coneE_mono {r s a b : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π) : coneE r s a ≤ coneE r s b := by
  unfold coneE
  refine sqrt_le_sqrt ?_
  have := cos_le_cos_of_nonneg_of_le_pi ha hb hab
  nlinarith [mul_nonneg hr hs]

theorem abs_sub_le_coneE {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (a : ℝ) : |r - s| ≤ coneE r s a := by
  rw [← coneE_zero]
  unfold coneE
  refine sqrt_le_sqrt ?_
  rw [cos_zero]
  nlinarith [mul_nonneg hr hs, cos_le_one a]

theorem coneE_le_add {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (a : ℝ) : coneE r s a ≤ r + s := by
  have h := coneE_pi r s
  rw [abs_of_nonneg (add_nonneg hr hs)] at h
  rw [← h]
  unfold coneE
  refine sqrt_le_sqrt ?_
  rw [cos_pi]
  nlinarith [mul_nonneg hr hs, neg_one_le_cos a]

/-- Along a circle of radius `s`, the chord is at most the arc. -/
theorem coneE_self_le {s : ℝ} (hs : 0 ≤ s) (a : ℝ) : coneE s s a ≤ s * |a| := by
  rw [← sqrt_sq (mul_nonneg hs (abs_nonneg a))]
  unfold coneE
  refine sqrt_le_sqrt ?_
  have := one_sub_sq_div_two_le_cos (x := a)
  rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg s]

/-- Moving radially, then along a circle. -/
theorem coneE_le_abs_sub_add {r s : ℝ} (hs : 0 ≤ s) (a : ℝ) :
    coneE r s a ≤ |r - s| + s * |a| := by
  have h := coneE_add_le r s s 0 a
  rw [zero_add, coneE_zero] at h
  linarith [coneE_self_le hs a]

/-! ### Angles on the circle of length `α` -/

/-- The angle under which two directions are seen from the apex, capped at `π`: past `π` the
shortest path runs through the apex. -/
noncomputable def angDist {α : ℝ} (θ₁ θ₂ : AddCircle α) : ℝ := min ‖θ₁ - θ₂‖ π

theorem angDist_nonneg {α : ℝ} (θ₁ θ₂ : AddCircle α) : 0 ≤ angDist θ₁ θ₂ :=
  le_min (norm_nonneg _) pi_pos.le

theorem angDist_le_pi {α : ℝ} (θ₁ θ₂ : AddCircle α) : angDist θ₁ θ₂ ≤ π := min_le_right _ _

theorem angDist_comm {α : ℝ} (θ₁ θ₂ : AddCircle α) : angDist θ₁ θ₂ = angDist θ₂ θ₁ := by
  unfold angDist; rw [norm_sub_rev]

theorem angDist_self {α : ℝ} (θ : AddCircle α) : angDist θ θ = 0 := by
  unfold angDist; rw [sub_self, norm_zero]; exact min_eq_left pi_pos.le

theorem angDist_triangle {α : ℝ} (θ₁ θ₂ θ₃ : AddCircle α) :
    angDist θ₁ θ₃ ≤ min (angDist θ₁ θ₂ + angDist θ₂ θ₃) π := by
  have h : ‖θ₁ - θ₃‖ ≤ ‖θ₁ - θ₂‖ + ‖θ₂ - θ₃‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h1 := norm_nonneg (θ₁ - θ₂)
  have h2 := norm_nonneg (θ₂ - θ₃)
  have h3 := pi_pos
  unfold angDist
  simp only [min_def]
  split_ifs <;> linarith

/-! ### The pre-cone: polar coordinates -/

/-- A point of the cone in polar coordinates: a radius `r ≥ 0` and a direction `θ` on the circle
of length `α`. The directions of the apex `r = 0` are identified by the separation quotient
(`Cone`). -/
@[ext]
structure ConePoint (α : ℝ) where
  /-- The distance to the apex. -/
  r : ℝ
  /-- The direction. -/
  θ : AddCircle α
  r_nonneg : 0 ≤ r

namespace ConePoint

variable {α : ℝ}

/-- The point of radius `max u 0` in the direction `θ`. -/
noncomputable def of (u : ℝ) (θ : AddCircle α) : ConePoint α := ⟨max u 0, θ, le_max_right _ _⟩

theorem of_r {u : ℝ} (hu : 0 ≤ u) (θ : AddCircle α) : (of u θ).r = u := max_eq_left hu

/-- **The cone distance**: the law of cosines with the angle `min(δ, π)`, `δ` the distance of the
directions on the circle of length `α`. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (ConePoint α) where
  dist p q := coneE p.r q.r (angDist p.θ q.θ)
  dist_self p := by
    show coneE p.r p.r (angDist p.θ p.θ) = 0
    rw [angDist_self, coneE_zero, sub_self, abs_zero]
  dist_comm p q := by
    show coneE p.r q.r (angDist p.θ q.θ) = coneE q.r p.r (angDist q.θ p.θ)
    rw [angDist_comm, coneE_comm]
  dist_triangle p q w := by
    show coneE p.r w.r (angDist p.θ w.θ) ≤
      coneE p.r q.r (angDist p.θ q.θ) + coneE q.r w.r (angDist q.θ w.θ)
    set a := angDist p.θ q.θ
    set b := angDist q.θ w.θ
    have ha := angDist_nonneg p.θ q.θ
    have hb := angDist_nonneg q.θ w.θ
    have ha' := angDist_le_pi p.θ q.θ
    have hb' := angDist_le_pi q.θ w.θ
    have hc := angDist_nonneg p.θ w.θ
    have htri := angDist_triangle p.θ q.θ w.θ
    set b' := min b (π - a) with hb'def
    have hb'0 : 0 ≤ b' := le_min hb (by linarith)
    have hb'b : b' ≤ b := min_le_left _ _
    have hsum : a + b' = min (a + b) π := by
      rw [hb'def]; simp only [min_def]; split_ifs <;> linarith
    calc coneE p.r w.r (angDist p.θ w.θ) ≤ coneE p.r w.r (a + b') :=
          coneE_mono p.r_nonneg w.r_nonneg hc (hsum ▸ htri) (by rw [hsum]; exact min_le_right _ _)
      _ ≤ coneE p.r q.r a + coneE q.r w.r b' := coneE_add_le _ _ _ _ _
      _ ≤ coneE p.r q.r a + coneE q.r w.r b := by
          linarith [coneE_mono q.r_nonneg w.r_nonneg hb'0 hb'b hb']

theorem dist_def (p q : ConePoint α) : dist p q = coneE p.r q.r (angDist p.θ q.θ) := rfl

theorem abs_r_sub_le_dist (p q : ConePoint α) : |p.r - q.r| ≤ dist p q :=
  abs_sub_le_coneE p.r_nonneg q.r_nonneg _

theorem dist_of_r_eq_zero {p q : ConePoint α} (hp : p.r = 0) : dist p q = q.r := by
  rw [dist_def, hp, coneE_zero_left, abs_of_nonneg q.r_nonneg]

theorem dist_le_add (p q : ConePoint α) : dist p q ≤ p.r + q.r :=
  coneE_le_add p.r_nonneg q.r_nonneg _

/-- Two points on one ray. -/
theorem dist_same_dir {p q : ConePoint α} (h : p.θ = q.θ) : dist p q = |p.r - q.r| := by
  rw [dist_def, h, angDist_self, coneE_zero]

/-- Two points whose directions are at least `π` apart: the distance runs through the apex. -/
theorem dist_of_pi_le {p q : ConePoint α} (h : π ≤ ‖p.θ - q.θ‖) : dist p q = p.r + q.r := by
  rw [dist_def, angDist, min_eq_right h, coneE_pi, abs_of_nonneg (add_nonneg p.r_nonneg q.r_nonneg)]

/-- The polar coordinates depend continuously on `(u, θ)`, with the product topology. -/
theorem dist_of_le (u u' : ℝ) (θ θ' : AddCircle α) :
    dist (of u θ) (of u' θ') ≤ |u - u'| + max u' 0 * ‖θ - θ'‖ := by
  rw [dist_def]
  refine (coneE_le_abs_sub_add (of u' θ').r_nonneg _).trans (add_le_add ?_ ?_)
  · exact abs_max_sub_max_le_abs u u' 0
  · refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    rw [abs_of_nonneg (angDist_nonneg _ _)]
    exact min_le_left _ _

end ConePoint

/-! ### Geodesics -/

/-- A real representative of a direction, of absolute value its norm. -/
theorem exists_addCircle_rep {α : ℝ} (θ : AddCircle α) : ∃ σ : ℝ, (σ : AddCircle α) = θ ∧ |σ| = ‖θ‖ := by
  induction θ using QuotientAddGroup.induction_on with
  | H x =>
    refine ⟨x - round (α⁻¹ * x) * α, ?_, (AddCircle.norm_eq (p := α)).symm⟩
    rw [AddCircle.coe_sub, sub_eq_self, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero]

/-- The polar radius of a point of the plane with positive abscissa, times the cosine of its
polar angle, is the abscissa. -/
theorem sqrt_mul_cos_arctan {A B : ℝ} (hA : 0 < A) : √(A ^ 2 + B ^ 2) * cos (arctan (B / A)) = A := by
  rw [cos_arctan]
  have h : √(A ^ 2 + B ^ 2) = A * √(1 + (B / A) ^ 2) := by
    rw [show A ^ 2 + B ^ 2 = A ^ 2 * (1 + (B / A) ^ 2) by field_simp, sqrt_mul (sq_nonneg A),
      sqrt_sq hA.le]
  have h1 : 0 < √(1 + (B / A) ^ 2) := sqrt_pos.2 (by positivity)
  rw [h]; field_simp

theorem sqrt_mul_sin_arctan {A B : ℝ} (hA : 0 < A) : √(A ^ 2 + B ^ 2) * sin (arctan (B / A)) = B := by
  rw [sin_arctan]
  have h : √(A ^ 2 + B ^ 2) = A * √(1 + (B / A) ^ 2) := by
    rw [show A ^ 2 + B ^ 2 = A ^ 2 * (1 + (B / A) ^ 2) by field_simp, sqrt_mul (sq_nonneg A),
      sqrt_sq hA.le]
  have h1 : 0 < √(1 + (B / A) ^ 2) := sqrt_pos.2 (by positivity)
  rw [h]; field_simp

/-- In polar coordinates the law of cosines is the Euclidean distance. -/
theorem coneE_polar_sq {A B A' B' : ℝ} (hA : 0 < A) (hA' : 0 < A') :
    coneE (√(A ^ 2 + B ^ 2)) (√(A' ^ 2 + B' ^ 2)) (arctan (B / A) - arctan (B' / A')) ^ 2 =
      (A - A') ^ 2 + (B - B') ^ 2 := by
  have h1 := sqrt_mul_cos_arctan (B := B) hA
  have h2 := sqrt_mul_sin_arctan (B := B) hA
  have h3 := sqrt_mul_cos_arctan (B := B') hA'
  have h4 := sqrt_mul_sin_arctan (B := B') hA'
  have hρ := sq_sqrt (add_nonneg (sq_nonneg A) (sq_nonneg B))
  have hρ' := sq_sqrt (add_nonneg (sq_nonneg A') (sq_nonneg B'))
  rw [coneE_sq, cos_sub]
  set ρ := √(A ^ 2 + B ^ 2)
  set ρ' := √(A' ^ 2 + B' ^ 2)
  set ψ := arctan (B / A)
  set ψ' := arctan (B' / A')
  linear_combination hρ + hρ' - 2 * (ρ' * cos ψ') * h1 - 2 * A * h3 - 2 * (ρ' * sin ψ') * h2 -
    2 * B * h4

/-- The abscissa of the segment from `(r₁, −c)` to `(r₂, c)` (polar), rotated by `−c`... in
cartesian coordinates: `((1 − s) r₁ + s r₂) cos c`. -/
noncomputable def segA (r₁ r₂ c s : ℝ) : ℝ := (r₁ + s * (r₂ - r₁)) * cos c

/-- Its ordinate, `(s r₂ − (1 − s) r₁) sin c`. -/
noncomputable def segB (r₁ r₂ c s : ℝ) : ℝ := (s * (r₁ + r₂) - r₁) * sin c

theorem segA_pos {r₁ r₂ c s : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hc : |c| < π / 2)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 < segA r₁ r₂ c s := by
  have hcos : 0 < cos c := cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le c], by linarith [le_abs_self c]⟩
  refine mul_pos ?_ hcos
  rcases le_or_gt s (1 / 2) with h | h
  · nlinarith [hs.1, hs.2, mul_nonneg hs.1 h₂.le]
  · nlinarith [hs.1, hs.2, mul_nonneg (sub_nonneg.2 hs.2) h₁.le]

/-- The segment is straight: its chords are proportional to the parameter. -/
theorem seg_sq (r₁ r₂ c s s' : ℝ) :
    (segA r₁ r₂ c s - segA r₁ r₂ c s') ^ 2 + (segB r₁ r₂ c s - segB r₁ r₂ c s') ^ 2 =
      ((s - s') * coneE r₁ r₂ (2 * c)) ^ 2 := by
  rw [mul_pow, coneE_sq, cos_two_mul']
  unfold segA segB
  linear_combination (s - s') ^ 2 * (r₁ ^ 2 + r₂ ^ 2) * sin_sq_add_cos_sq c

/-- The polar angle of the segment stays within `[−|c|, |c|]`. -/
theorem abs_arctan_seg_le {r₁ r₂ c s : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hc : |c| < π / 2)
    (hs : s ∈ Icc (0 : ℝ) 1) : |arctan (segB r₁ r₂ c s / segA r₁ r₂ c s)| ≤ |c| := by
  have hA := segA_pos h₁ h₂ hc hs
  set A := segA r₁ r₂ c s
  set B := segB r₁ r₂ c s
  set ψ := arctan (B / A)
  have hcos : 0 < cos c := cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le c], by linarith [le_abs_self c]⟩
  have h1 := sqrt_mul_cos_arctan (B := B) hA
  have hρ := sq_sqrt (add_nonneg (sq_nonneg A) (sq_nonneg B))
  have hρpos : 0 < √(A ^ 2 + B ^ 2) := sqrt_pos.2 (by positivity)
  -- `A sin c ≥ |B| cos c`, i.e. `cos ψ ≥ cos c`
  have hL : |s * (r₁ + r₂) - r₁| ≤ r₁ + s * (r₂ - r₁) := by
    rw [abs_le]; constructor <;> nlinarith [hs.1, hs.2]
  have hAB : B ^ 2 * cos c ^ 2 ≤ A ^ 2 * sin c ^ 2 := by
    have e1 : B ^ 2 * cos c ^ 2 = (s * (r₁ + r₂) - r₁) ^ 2 * (sin c ^ 2 * cos c ^ 2) := by
      simp only [B, segB]; ring
    have e2 : A ^ 2 * sin c ^ 2 = (r₁ + s * (r₂ - r₁)) ^ 2 * (sin c ^ 2 * cos c ^ 2) := by
      simp only [A, segA]; ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← sq_abs (s * (r₁ + r₂) - r₁)]
    exact pow_le_pow_left₀ (abs_nonneg _) hL 2
  have hcosψ : cos c ≤ cos ψ := by
    have : √(A ^ 2 + B ^ 2) * cos c ≤ √(A ^ 2 + B ^ 2) * cos ψ := by
      rw [h1]
      refine (pow_le_pow_iff_left₀ (mul_nonneg hρpos.le hcos.le) hA.le two_ne_zero).1 ?_
      rw [mul_pow, hρ]
      nlinarith [sin_sq_add_cos_sq c]
    exact le_of_mul_le_mul_left this hρpos
  by_contra hlt
  push Not at hlt
  have hψ : |ψ| ≤ π := by
    have := neg_pi_div_two_lt_arctan (B / A)
    have := arctan_lt_pi_div_two (B / A)
    rw [abs_le]; constructor <;> linarith [pi_pos]
  have := cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg c) hψ hlt
  rw [cos_abs, cos_abs] at this
  linarith


/-! ### The cone -/

/-- **The flat cone `C_α` of angle `α`**: the polar coordinates with the cone distance, the
directions of the apex identified (the separation quotient: two points are identified iff their
distance is `0`, iff they are equal or both of radius `0`). -/
def Cone (α : ℝ) : Type := SeparationQuotient (ConePoint α)

namespace Cone

variable {α : ℝ}

noncomputable instance instMetricSpace : MetricSpace (Cone α) :=
  inferInstanceAs (MetricSpace (SeparationQuotient (ConePoint α)))

/-- The point of polar coordinates `p`. -/
noncomputable def mk (p : ConePoint α) : Cone α := SeparationQuotient.mk p

theorem dist_mk (p q : ConePoint α) : dist (mk p) (mk q) = dist p q := rfl

theorem mk_surjective : Function.Surjective (mk : ConePoint α → Cone α) :=
  SeparationQuotient.surjective_mk

theorem mk_eq_mk_iff {p q : ConePoint α} : mk p = mk q ↔ dist p q = 0 :=
  SeparationQuotient.mk_eq_mk.trans Metric.inseparable_iff

/-- Two points of radius `0` are the apex. -/
theorem mk_eq_mk_of_r_eq_zero {p q : ConePoint α} (hp : p.r = 0) (hq : q.r = 0) : mk p = mk q :=
  mk_eq_mk_iff.2 (by rw [ConePoint.dist_of_r_eq_zero hp, hq])

/-- **The apex**, the singular point of `C_α`. -/
noncomputable def apex : Cone α := mk ⟨0, 0, le_rfl⟩

/-- The distance to the apex. -/
noncomputable def rad (x : Cone α) : ℝ := dist apex x

theorem rad_mk (p : ConePoint α) : rad (mk p) = p.r :=
  ConePoint.dist_of_r_eq_zero rfl

theorem rad_nonneg (x : Cone α) : 0 ≤ rad x := dist_nonneg

theorem rad_eq_zero {x : Cone α} : rad x = 0 ↔ x = apex := by
  rw [rad, dist_eq_zero, eq_comm]

theorem mk_eq_apex {p : ConePoint α} (hp : p.r = 0) : mk p = apex :=
  mk_eq_mk_of_r_eq_zero hp rfl

/-- The map of polar coordinates `(u, θ) ↦ (max u 0, θ)`, continuous for the product topology. -/
noncomputable def polar (x : ℝ × AddCircle α) : Cone α := mk (ConePoint.of x.1 x.2)

theorem continuous_polar : Continuous (polar (α := α)) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hf : Continuous fun x : ℝ × AddCircle α => |x.1 - y.1| + max y.1 0 * ‖x.2 - y.2‖ := by
    fun_prop
  have h0 : |y.1 - y.1| + max y.1 0 * ‖y.2 - y.2‖ = 0 := by simp
  refine squeeze_zero (fun _ => dist_nonneg) (fun x => ConePoint.dist_of_le _ _ _ _) ?_
  have := hf.tendsto y
  rwa [h0] at this

theorem polar_rad_θ (p : ConePoint α) : polar (p.r, p.θ) = mk p := by
  unfold polar; congr 1; ext
  · exact ConePoint.of_r p.r_nonneg _
  · rfl

/-- **`C_α` is proper**: a closed ball lies in the image of the compact `[0, R] × (ℝ/αℤ)`. -/
instance instProperSpace [Fact (0 < α)] : ProperSpace (Cone α) := by
  refine ⟨fun x R => ?_⟩
  obtain ⟨p, rfl⟩ := mk_surjective x
  refine (((isCompact_Icc (a := (0 : ℝ)) (b := p.r + R)).prod isCompact_univ).image
    continuous_polar).of_isClosed_subset isClosed_closedBall fun z hz => ?_
  obtain ⟨q, rfl⟩ := mk_surjective z
  refine ⟨(q.r, q.θ), ⟨⟨q.r_nonneg, ?_⟩, trivial⟩, polar_rad_θ q⟩
  have h1 := ConePoint.abs_r_sub_le_dist q p
  rw [mem_closedBall, dist_mk] at hz
  have := le_abs_self (q.r - p.r)
  linarith

/-- `C_α` is complete. -/
example [Fact (0 < α)] : CompleteSpace (Cone α) := inferInstance

/-- Two points on rays seen under an angle `≥ π` (or one of them the apex): the distance runs
through the apex. -/
theorem dist_of_of {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {θ₁ θ₂ : AddCircle α}
    (h : u = 0 ∨ v = 0 ∨ π ≤ ‖θ₁ - θ₂‖) :
    dist (ConePoint.of u θ₁) (ConePoint.of v θ₂) = u + v := by
  rcases h with h | h | h
  · rw [ConePoint.dist_of_r_eq_zero (by rw [ConePoint.of_r hu]; exact h), ConePoint.of_r hv, h,
      zero_add]
  · rw [dist_comm, ConePoint.dist_of_r_eq_zero (by rw [ConePoint.of_r hv]; exact h),
      ConePoint.of_r hu, h, add_zero]
  · rw [ConePoint.dist_of_pi_le (p := ConePoint.of u θ₁) (q := ConePoint.of v θ₂) h,
      ConePoint.of_r hu, ConePoint.of_r hv]

theorem dist_of_same_dir {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (θ : AddCircle α) :
    dist (ConePoint.of u θ) (ConePoint.of v θ) = |u - v| := by
  rw [ConePoint.dist_same_dir (p := ConePoint.of u θ) (q := ConePoint.of v θ) rfl,
    ConePoint.of_r hu, ConePoint.of_r hv]

theorem of_r_self (p : ConePoint α) : ConePoint.of p.r p.θ = p := by
  ext
  · exact ConePoint.of_r p.r_nonneg _
  · rfl

/-- **The geodesic through the apex**: when one end is the apex, or the directions are at least
`π` apart, go straight to the apex and out again. -/
theorem exists_geodesic_through_apex (p q : ConePoint α) (h : p.r = 0 ∨ q.r = 0 ∨ π ≤ ‖p.θ - q.θ‖) :
    ∃ g : ℝ → Cone α, g 0 = mk p ∧ g 1 = mk q ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      dist (g s) (g s') = |s - s'| * dist (mk p) (mk q) := by
  set T := p.r + q.r with hTdef
  have hT : 0 ≤ T := add_nonneg p.r_nonneg q.r_nonneg
  have hpq : dist (mk p) (mk q) = T := by
    rw [dist_mk, ← of_r_self p, ← of_r_self q]
    exact dist_of_of p.r_nonneg q.r_nonneg h
  let P : ℝ → ConePoint α := fun s =>
    if s * T ≤ p.r then ConePoint.of (p.r - s * T) p.θ else ConePoint.of (s * T - p.r) q.θ
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' →
      dist (P s) (P s') = (s' - s) * T := by
    intro s hs s' hs' hss
    have hsT : s * T ≤ s' * T := mul_le_mul_of_nonneg_right hss hT
    have hs'T : s' * T ≤ T := by nlinarith [hs'.2]
    have hs0 : 0 ≤ s * T := mul_nonneg hs.1 hT
    by_cases h1 : s' * T ≤ p.r
    · simp only [P, if_pos h1, if_pos (hsT.trans h1)]
      rw [dist_of_same_dir (by linarith) (by linarith), abs_of_nonneg (by linarith)]
      ring
    by_cases h2 : s * T ≤ p.r
    · simp only [P, if_pos h2, if_neg h1]
      push Not at h1
      rw [dist_of_of (by linarith) (by linarith)]
      · ring
      rcases h with h | h | h
      · left; linarith
      · exfalso; linarith
      · exact Or.inr (Or.inr h)
    · simp only [P, if_neg h1, if_neg h2]
      push Not at h1 h2
      rw [dist_of_same_dir (by linarith) (by linarith), abs_of_nonpos (by linarith)]
      ring
  refine ⟨fun s => mk (P s), ?_, ?_, fun s hs s' hs' => ?_⟩
  · simp only [P, zero_mul, if_pos p.r_nonneg, sub_zero, of_r_self]
  · simp only [P, one_mul]
    split_ifs with h1
    · exact mk_eq_mk_of_r_eq_zero (by rw [ConePoint.of]; simp only; rw [max_eq_right (by linarith [q.r_nonneg])])
        (by linarith [q.r_nonneg])
    · push Not at h1
      rw [show T - p.r = q.r by rw [hTdef]; ring, of_r_self]
  · rw [dist_mk, hpq]
    rcases le_total s s' with hss | hss
    · rw [key s hs s' hs' hss, abs_of_nonpos (by linarith)]; ring
    · rw [dist_comm, key s' hs' s hs hss, abs_of_nonneg (by linarith)]

/-- **The straight geodesic**: two points off the apex whose directions are less than `π` apart
span a flat sector, and the geodesic is the segment of the plane, in polar coordinates. -/
theorem exists_geodesic_straight [hα : Fact (0 < α)] (p q : ConePoint α) (hp : 0 < p.r)
    (hq : 0 < q.r) (h : ‖p.θ - q.θ‖ < π) :
    ∃ g : ℝ → Cone α, g 0 = mk p ∧ g 1 = mk q ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      dist (g s) (g s') = |s - s'| * dist (mk p) (mk q) := by
  obtain ⟨σ, hσ, hσn⟩ := exists_addCircle_rep (q.θ - p.θ)
  rw [norm_sub_rev] at hσn
  set c := σ / 2 with hcdef
  have hc : |c| < π / 2 := by rw [hcdef, abs_div, abs_two]; linarith
  have hσα : |σ| ≤ α / 2 := by
    rw [hσn]
    have := AddCircle.norm_le_half_period α (x := p.θ - q.θ) hα.out.ne'
    rwa [abs_of_pos hα.out] at this
  set A := segA p.r q.r c
  set B := segB p.r q.r c
  let ψ : ℝ → ℝ := fun s => arctan (B s / A s)
  let P : ℝ → ConePoint α := fun s =>
    ⟨√(A s ^ 2 + B s ^ 2), p.θ + ((c + ψ s : ℝ) : AddCircle α), sqrt_nonneg _⟩
  have hψ : ∀ s ∈ Icc (0 : ℝ) 1, |ψ s| ≤ |c| := fun s hs => abs_arctan_seg_le hp hq hc hs
  have hcos : 0 < cos c :=
    cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le c], by linarith [le_abs_self c]⟩
  have hD : dist (mk p) (mk q) = coneE p.r q.r (2 * c) := by
    rw [dist_mk, ConePoint.dist_def, angDist, min_eq_left h.le, ← hσn, coneE_abs, hcdef]
    ring_nf
  refine ⟨fun s => mk (P s), ?_, ?_, fun s hs s' hs' => ?_⟩
  · have hA0 : A 0 = p.r * cos c := by simp [A, segA]
    have hB0 : B 0 = -(p.r * sin c) := by simp [B, segB]
    have hψ0 : ψ 0 = -c := by
      refine arctan_eq_of_tan_eq ?_ ⟨by linarith [le_abs_self c], by linarith [neg_abs_le c]⟩
      rw [hA0, hB0, tan_neg, tan_eq_sin_div_cos]
      field_simp
    refine congrArg mk ?_
    ext
    · show √(A 0 ^ 2 + B 0 ^ 2) = p.r
      rw [hA0, hB0, show (p.r * cos c) ^ 2 + (-(p.r * sin c)) ^ 2 = p.r ^ 2 * (sin c ^ 2 + cos c ^ 2)
        by ring, sin_sq_add_cos_sq, mul_one, sqrt_sq hp.le]
    · show p.θ + ((c + ψ 0 : ℝ) : AddCircle α) = p.θ
      rw [hψ0, add_neg_cancel, AddCircle.coe_zero, add_zero]
  · have hA1 : A 1 = q.r * cos c := by simp [A, segA]
    have hB1 : B 1 = q.r * sin c := by simp [B, segB]
    have hψ1 : ψ 1 = c := by
      refine arctan_eq_of_tan_eq ?_ ⟨by linarith [neg_abs_le c], by linarith [le_abs_self c]⟩
      rw [hA1, hB1, tan_eq_sin_div_cos]
      field_simp
    refine congrArg mk ?_
    ext
    · show √(A 1 ^ 2 + B 1 ^ 2) = q.r
      rw [hA1, hB1, show (q.r * cos c) ^ 2 + (q.r * sin c) ^ 2 = q.r ^ 2 * (sin c ^ 2 + cos c ^ 2)
        by ring, sin_sq_add_cos_sq, mul_one, sqrt_sq hq.le]
    · show p.θ + ((c + ψ 1 : ℝ) : AddCircle α) = q.θ
      rw [hψ1, show c + c = σ by rw [hcdef]; ring, hσ, add_sub_cancel]
  · have hb : |ψ s - ψ s'| ≤ |σ| := by
      have := abs_sub (ψ s) (ψ s')
      have h2 : |σ| = 2 * |c| := by rw [hcdef, abs_div, abs_two]; ring
      linarith [hψ s hs, hψ s' hs']
    have hang : angDist (P s).θ (P s').θ = |ψ s - ψ s'| := by
      show min ‖(p.θ + ((c + ψ s : ℝ) : AddCircle α)) - (p.θ + ((c + ψ s' : ℝ) : AddCircle α))‖ π = _
      rw [add_sub_add_left_eq_sub, ← AddCircle.coe_sub, show c + ψ s - (c + ψ s') = ψ s - ψ s' by ring,
        (AddCircle.norm_coe_eq_abs_iff α hα.out.ne').2 (by rw [abs_of_pos hα.out]; linarith)]
      exact min_eq_left (by linarith)
    have hsq : dist (mk (P s)) (mk (P s')) ^ 2 = ((s - s') * coneE p.r q.r (2 * c)) ^ 2 := by
      rw [dist_mk, ConePoint.dist_def, hang, coneE_abs]
      rw [← seg_sq]
      exact coneE_polar_sq (segA_pos hp hq hc hs) (segA_pos hp hq hc hs')
    have := congrArg Real.sqrt hsq
    rwa [sqrt_sq dist_nonneg, sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (coneE_nonneg _ _ _), ← hD]
      at this

/-- **`C_α` is geodesic**: through the apex when the directions are at least `π` apart (or one
end is the apex), along the planar segment of the flat sector they span otherwise. -/
instance instGeodesicSpace [Fact (0 < α)] : GeodesicSpace (Cone α) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨p, rfl⟩ := mk_surjective x
  obtain ⟨q, rfl⟩ := mk_surjective y
  by_cases h : p.r = 0 ∨ q.r = 0 ∨ π ≤ ‖p.θ - q.θ‖
  · exact exists_geodesic_through_apex p q h
  · push Not at h
    exact exists_geodesic_straight p q (lt_of_le_of_ne p.r_nonneg (Ne.symm h.1))
      (lt_of_le_of_ne q.r_nonneg (Ne.symm h.2.1)) h.2.2

/-! ### `C_{2π}` is the Euclidean plane -/

theorem toCircle_coe_two_pi (x : ℝ) :
    (AddCircle.toCircle (x : AddCircle (2 * π)) : ℂ) = Complex.exp (x * Complex.I) := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 2
  field_simp

/-- Polar coordinates of the plane `ℂ`. -/
noncomputable def toPlane (p : ConePoint (2 * π)) : ℂ := p.r * (AddCircle.toCircle p.θ : ℂ)

theorem dist_toPlane (p q : ConePoint (2 * π)) : dist (toPlane p) (toPlane q) = dist p q := by
  obtain ⟨σ, hσ, hσn⟩ := exists_addCircle_rep (q.θ - p.θ)
  have hq : q.θ = p.θ + (σ : AddCircle (2 * π)) := by rw [hσ]; abel
  have hπ : ‖p.θ - q.θ‖ ≤ π := by
    have := AddCircle.norm_le_half_period (2 * π) (x := p.θ - q.θ) (by positivity)
    rwa [abs_of_pos (by positivity), mul_div_cancel_left₀ _ two_ne_zero] at this
  rw [ConePoint.dist_def, angDist, min_eq_left hπ, norm_sub_rev, ← hσn, coneE_abs, coneE_eq_norm,
    dist_eq_norm, toPlane, toPlane, hq, AddCircle.toCircle_add, Circle.coe_mul, toCircle_coe_two_pi]
  set u : ℂ := (AddCircle.toCircle p.θ : ℂ)
  rw [show (p.r : ℂ) * u - q.r * (u * Complex.exp (σ * Complex.I)) =
      u * (p.r - q.r * Complex.exp (σ * Complex.I)) by ring, norm_mul, Circle.norm_coe, one_mul]

/-- The cone of angle `2π` mapped to the plane. -/
noncomputable def planeMap : Cone (2 * π) → ℂ :=
  SeparationQuotient.lift toPlane fun x y h => by
    rw [← dist_eq_zero, dist_toPlane]; exact Metric.inseparable_iff.1 h

theorem planeMap_mk (p : ConePoint (2 * π)) : planeMap (mk p) = toPlane p := rfl

theorem isometry_planeMap : Isometry planeMap := by
  refine Isometry.of_dist_eq fun x y => ?_
  obtain ⟨p, rfl⟩ := mk_surjective x
  obtain ⟨q, rfl⟩ := mk_surjective y
  rw [planeMap_mk, planeMap_mk, dist_toPlane, dist_mk]

/-- Polar coordinates of a complex number. -/
noncomputable def ofPlane (z : ℂ) : Cone (2 * π) := mk ⟨‖z‖, (Complex.arg z : ℝ), norm_nonneg z⟩

theorem planeMap_ofPlane (z : ℂ) : planeMap (ofPlane z) = z := by
  rw [ofPlane, planeMap_mk, toPlane]
  simp only
  rw [toCircle_coe_two_pi, Complex.norm_mul_exp_arg_mul_I]

/-- **`C_{2π}` is the Euclidean plane** `ℂ`. -/
noncomputable def coneTwoPiIsoComplex : Cone (2 * π) ≃ᵢ ℂ :=
  IsometryEquiv.mk' planeMap ofPlane planeMap_ofPlane isometry_planeMap

/-- **`C_{2π}` is the Euclidean plane** `ℝ²` (`ETT.tex:1328`, `\mass{2\pi}=\mass{}`, in space). -/
noncomputable def coneTwoPiIsoEuclidean : Cone (2 * π) ≃ᵢ EuclideanSpace ℝ (Fin 2) :=
  coneTwoPiIsoComplex.trans Complex.orthonormalBasisOneI.repr.toIsometryEquiv

/-- The apex of `C_{2π}` is the origin. -/
theorem coneTwoPiIsoComplex_apex : coneTwoPiIsoComplex apex = 0 := by
  show toPlane _ = 0
  simp [toPlane]

/-! ### The apex is singular when `α ≠ 2π` -/

theorem coneE_self_lt_two_mul {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (haπ : a < π) :
    coneE s s a < 2 * s := by
  have hcos : cos π < cos a := cos_lt_cos_of_nonneg_of_le_pi ha le_rfl haπ
  rw [cos_pi] at hcos
  rw [← sqrt_sq (by linarith : 0 ≤ 2 * s)]
  unfold coneE
  refine sqrt_lt_sqrt (coneE_radicand_nonneg s s a) ?_
  nlinarith [sq_pos_of_pos hs]

theorem coneE_self_pos {s a : ℝ} (hs : 0 < s) (ha : 0 < a) (haπ : a ≤ π) : 0 < coneE s s a := by
  have hcos : cos a < cos 0 := cos_lt_cos_of_nonneg_of_le_pi le_rfl haπ ha
  rw [cos_zero] at hcos
  unfold coneE
  refine sqrt_pos.2 ?_
  nlinarith [sq_pos_of_pos hs]

/-- In the plane, the antipode of `w + δ` on the circle of radius `δ` about `w` is unique. -/
theorem complex_antipode_unique {w c : ℂ} {δ : ℝ} (hδ : 0 < δ) (h1 : dist c w = δ)
    (h2 : dist (w + δ) c = 2 * δ) : c = w - δ := by
  rw [Complex.dist_eq] at h1 h2
  have e1 : (c - w).re ^ 2 + (c - w).im ^ 2 = δ ^ 2 := by
    rw [← h1, Complex.sq_norm, Complex.normSq_apply]; ring
  have e2 : (δ - (c - w).re) ^ 2 + (c - w).im ^ 2 = (2 * δ) ^ 2 := by
    rw [← h2, Complex.sq_norm, Complex.normSq_apply,
      show w + (δ : ℂ) - c = (δ : ℂ) - (c - w) by ring]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]; ring
  have hre : (c - w).re = -δ := by nlinarith
  have him : (c - w).im = 0 := by nlinarith
  have : c - w = -(δ : ℂ) := Complex.ext (by simp [hre]) (by simp [him])
  linear_combination this

variable [hα : Fact (0 < α)]

/-- **For `α ≠ 2π` the apex has no neighbourhood isometric to an open subset of the plane.** For
`α < 2π` the apex is the midpoint of no two points at equal distance from it; for `α > 2π` a
point at distance `δ` from the apex has a whole arc of points at distance `2δ` from it on the
circle of radius `δ`, where the plane has a single antipode. -/
theorem apex_not_euclidean (h2π : α ≠ 2 * π) :
    ¬ ∃ U ∈ 𝓝 (apex : Cone α), ∃ f : Cone α → ℂ,
      (∀ x ∈ U, ∀ y ∈ U, dist (f x) (f y) = dist x y) ∧ f '' U ∈ 𝓝 (f apex) := by
  rintro ⟨U, hU, f, hf, hfU⟩
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.mem_nhds_iff.1 hfU
  set δ := min ε₁ ε₂ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ₁ : δ < ε₁ := by have := min_le_left ε₁ ε₂; linarith
  have hδ₂ : δ < ε₂ := by have := min_le_right ε₁ ε₂; linarith
  have hapex : (apex : Cone α) ∈ U := mem_of_mem_nhds hU
  set w := f apex
  -- a preimage of `w + δ`
  obtain ⟨y, hyU, hy⟩ := hball₂ (show w + (δ : ℂ) ∈ ball w ε₂ by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]; exact hδ₂)
  have hyr : rad y = δ := by
    rw [rad, ← hf apex hapex y hyU, hy, dist_eq_norm, show w - (w + (δ : ℂ)) = -(δ : ℂ) by ring,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  obtain ⟨p, rfl⟩ := mk_surjective y
  rw [rad_mk] at hyr
  rcases lt_or_gt_of_ne h2π with hlt | hgt
  · -- `α < 2π`: a preimage of `w − δ` would be seen from `p` under the angle `π`
    obtain ⟨z, hzU, hz⟩ := hball₂ (show w - (δ : ℂ) ∈ ball w ε₂ by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hδ]; exact hδ₂)
    have hzr : rad z = δ := by
      rw [rad, ← hf apex hapex z hzU, hz, dist_eq_norm, sub_sub_cancel, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hδ]
    obtain ⟨q, rfl⟩ := mk_surjective z
    rw [rad_mk] at hzr
    have hd : dist (mk p) (mk q) = 2 * δ := by
      rw [← hf _ hyU _ hzU, hy, hz, dist_eq_norm, show w + (δ : ℂ) - (w - δ) = ((2 * δ : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hang : angDist p.θ q.θ < π := by
      have := AddCircle.norm_le_half_period α (x := p.θ - q.θ) hα.out.ne'
      rw [abs_of_pos hα.out] at this
      exact (min_le_left _ _).trans_lt (by linarith)
    rw [dist_mk, ConePoint.dist_def, hyr, hzr] at hd
    linarith [coneE_self_lt_two_mul hδ (angDist_nonneg _ _) hang]
  · -- `α > 2π`: two distinct points of `U` would both map to the antipode `w − δ`
    set η := (α / 2 - π) / 2 with hηdef
    have hη : 0 < η := by rw [hηdef]; linarith
    let q₁ : ConePoint α := ⟨δ, p.θ + ((π : ℝ) : AddCircle α), hδ.le⟩
    let q₂ : ConePoint α := ⟨δ, p.θ + ((π + η : ℝ) : AddCircle α), hδ.le⟩
    have hnorm : ∀ x : ℝ, 0 ≤ x → x ≤ α / 2 → ‖(x : AddCircle α)‖ = x := fun x hx hxα => by
      rw [(AddCircle.norm_coe_eq_abs_iff α hα.out.ne').2 (by
        rw [abs_of_nonneg hx, abs_of_pos hα.out]; exact hxα), abs_of_nonneg hx]
    have hmemU : ∀ q : ConePoint α, q.r = δ → mk q ∈ U := fun q hq => hball₁ (by
      rw [mem_ball, dist_comm]; show rad (mk q) < ε₁; rw [rad_mk, hq]; exact hδ₁)
    have hfar : ∀ x : ℝ, π ≤ x → x ≤ α / 2 →
        dist (mk p) (mk ⟨δ, p.θ + (x : AddCircle α), hδ.le⟩) = 2 * δ := fun x hx hxα => by
      rw [dist_mk, ConePoint.dist_of_pi_le]
      · simp only; rw [hyr]; ring
      · simp only
        rw [sub_add_cancel_left, norm_neg, hnorm x (by linarith [pi_pos]) hxα]; exact hx
    have hant : ∀ q : ConePoint α, q.r = δ → dist (mk p) (mk q) = 2 * δ → f (mk q) = w - δ :=
      fun q hq hd => by
        refine complex_antipode_unique hδ ?_ ?_
        · rw [hf _ (hmemU q hq) _ hapex, dist_comm]; show rad (mk q) = δ; rw [rad_mk, hq]
        · rw [← hy, hf _ hyU _ (hmemU q hq), hd]
    have h1 := hant q₁ rfl (hfar π le_rfl (by linarith))
    have h2 := hant q₂ rfl (hfar (π + η) (by linarith) (by linarith))
    have h12 : dist (mk q₁) (mk q₂) = 0 := by
      rw [← hf _ (hmemU q₁ rfl) _ (hmemU q₂ rfl), h1, h2, dist_self]
    rw [dist_mk, ConePoint.dist_def] at h12
    have hθ : ‖q₁.θ - q₂.θ‖ = η := by
      simp only [q₁, q₂]
      rw [add_sub_add_left_eq_sub, ← AddCircle.coe_sub, show π - (π + η) = -η by ring,
        AddCircle.coe_neg, norm_neg, hnorm η hη.le (by linarith [pi_pos])]
    have hpos : 0 < coneE δ δ (angDist q₁.θ q₂.θ) := by
      refine coneE_self_pos hδ ?_ (angDist_le_pi _ _)
      rw [angDist, hθ]; exact lt_min hη pi_pos
    exact hpos.ne' h12

end Cone

end Causal
