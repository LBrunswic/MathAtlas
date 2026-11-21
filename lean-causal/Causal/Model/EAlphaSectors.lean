import Causal.Remarks.MassiveManifold
import Causal.Port.GXBasic
import Causal.Flat.Nonlox.NullFrame
import Mathlib.Analysis.Complex.Isometry

/-!
# The regular charts of `E_κ`, `κ > 0`: chart isomorphisms onto open subsets of `E^{1,2}`

Target `T-ett-ealpha-sectors` (wave of 2026-11-21). No label is marked. The row this file serves,
`defi:causal_Ealpha` — `ETT.tex:1335`, stays partial: its `(G,X)` sentence is about every
`E_{≥0}`-manifold and `κ = 0`, which this file does not build. What it builds is the regular
`(Isom(E^{1,2}), E^{1,2})`-atlas of `E_κ` the row presupposes, in the sentence before it
(`ETT.tex:1331–1333`), and the model fact `hreg` of `Causal.GXSingular`.

> We write $\sing(\mass{\alpha})$ for the singular line and $\reg(\mass{\alpha})$ for its
> complement, which is an $(\isom(\mass{}),\mass{})$-manifold. (`ETT.tex:1331–1333`)

> The causal and chronological orders of $\mass{\alpha}$ give rise to a sheaf with values in
> $\mathbf{C}$: for $\U\subset \mass{\alpha}$ open and $x,y\in \U$, one sets $x\leq_\U y$ (resp.
> $x\ll_\U y$) if and only if there is a future causal (resp. chronological) curve from $x$ to $y$
> in $\U$. On any $\mass{\geq0}$-manifold $M$ there is then a unique causal structure inducing that
> of $\mass{\alpha}$ in every chart [...] (`defi:causal_Ealpha`, `ETT.tex:1335–1342`)

## What is proved

* **Static spacetimes** (model-free in the space): a chart of space which is distance-preserving
  on its source, times the identity of time, is a `ChartIso` of the static causalities
  (`staticCausality.chartIso_prod_isometricOn`), because the causal and chronological curves of
  `defi:causal_Ealpha` are graphs of Lipschitz maps and only distances along them are read.
* **The sector charts of `E_κ`** (`EAlphaSector.chart`). For a regular point `p = (R, θ₁)` of
  `C_κ`, `R > 0`, the ball `B(p, R sin w)`, `w = min(π/2, κ/4)`, lies in the flat sector of
  directions `‖θ − θ₁‖ < w` (`EAlphaSector.angle_lt_of_coneE_lt`), where the law of cosines is the
  planar distance since `min(δ, π) = δ` there; `(r, θ₁ + φ) ↦ r e^{iφ}` maps it isometrically onto
  the planar disc `B(R, R sin w)`. Times the time coordinate this is an open partial homeomorphism
  `E_κ → E^{1,2}` with source `ℝ × B(p, R sin w)` (`chart_source`), and a **`ChartIso`**
  (`chartIso_chart`).
* **An atlas of `reg(E_κ)`**: the sources lie in `reg(E_κ)` (`chart_source_subset_regPart`) and
  cover it (`exists_mem_chart_source`); two charts differ on their whole overlap by **one
  rotation** of the plane (`exists_rotation`), an element of `Isom(E^{1,2})`
  (`rotIsom`, through `Flat.Nonlox.nfSpatial`), so every transition lies in
  `gxGroupoid (Flat.isom 2) (Minkowski 2)` (`symm_trans_chart_mem_gxGroupoid`). **Every chart
  compatible with them is a `ChartIso`** (`chartIso_of_compatible`: a chart of the maximal atlas
  they generate, whole sectors included, by the argument of `chartIso_of_mem_maximalAtlas`).
  Assembled: `regPart_isomAtlas`.
* **Why the opening is at most `κ/2`** (`fromPlane_wide_not_isometric`): in `C_{π/2}` the polar
  map of a sector of opening `9π/20 < min(π, κ)` (containing the directions `0` and `2π/5`) does not
  preserve the cone distance.
* **`hreg` in `Causal.GXSingular`'s form** for the family `massiveSectorChart κ k`, `κ > 0`
  (`hreg_sectorChart`), and `massA_positive` with it discharged (`massA_positive_sectorCharts`).
* **The first `massA_positive` witness with a chart into an `E_κ`** (`massA_positive_massive`):
  `M = E_κ`, the sector charts into `E^{1,2}`, the identity into `E_κ`; the causality of the atlas
  is `massive κ`, causally arc-connected with push-up. Instances at `κ = π` and `κ = 4π`.

## Hypothesis checklist

| paper | here |
|---|---|
| `α > 0` | ✓ carried (`[Fact (0 < α)]`, `κ : {κ // 0 < κ}`); `α > 2π` included |
| `reg(E_α)` an `(Isom(E), E)`-manifold (l.1332) | ⚠ a reading (the structure is not named): an atlas; every compatible chart a `ChartIso` |
| `hreg` of `massA_positive` (regular charts isomorphisms) | ✓ discharged for the sector charts |
| `κ = 0`, `E_{≥0}`-manifolds | not addressed (no label marked) |

## SCOPE (disclosed)

* **The charts are discs, not whole sectors.** Each chart is the flat sector of opening `2w`
  around a direction, cut down to the ball `B(p, R sin w)`: balls are open for free, the sector's
  openness in `C_κ` is not proved. The family covers `reg(E_κ)`, so it is an atlas. A whole
  sector, once built as an open partial homeomorphism compatible with the discs, is a `ChartIso` by
  `chartIso_of_compatible`; it is not built here.
* **No `ChartedSpace` on the subtype `reg(E_κ)`** (kb/0001): "`reg(E_α)` is an
  `(Isom(E), E)`-manifold" is read as an atlas of charts of `E_κ` with sources in `reg(E_κ)`,
  covering it, with transitions in the groupoid (`regPart_isomAtlas`); the maximal atlas is the
  set of charts compatible with it, each a `ChartIso` (`chartIso_of_compatible`).
* "Isomorphism" is `ChartIso`, the relational form of `Causal.GXStructure` (equivalent to DEC-10's
  by `chartIso_iff_strongMorphism`).
* The rotation of `E^{1,2}` is `(t, x) ↦ (t, R_c x)`, `R_c` the rotation of angle `c` of
  `EuclideanSpace ℝ (Fin 2) ≅ ℂ`, in `SO₀(1,2)` by `Flat.Nonlox.nfSpatial_mem_lorentz`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Real Metric Topology TopologicalSpace Filter

/-! ### A chart of space which preserves distances on its source -/

section IsometricOn

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A static curve is carried by a map of space which preserves the distances of a set containing
the curve. -/
theorem StaticCurve.map_isometricOn {f : X → Y} {S : Set X}
    (hf : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) = dist x y) {L : ℝ}
    {U : Set (ℝ × X)} {U' : Set (ℝ × Y)} (hUS : ∀ z ∈ U, z.2 ∈ S)
    (hU : MapsTo (Prod.map id f) U U') {γ : ℝ → X} {a b : ℝ}
    (h : StaticCurve L U γ a b) : StaticCurve L U' (f ∘ γ) a b :=
  ⟨fun τ hτ τ' hτ' => by
    simp only [Function.comp, hf _ (hUS _ (h.mem τ hτ)) _ (hUS _ (h.mem τ' hτ'))]
    exact h.lip τ hτ τ' hτ', fun τ hτ => hU (h.mem τ hτ)⟩

theorem staticLe.map_isometricOn {f : X → Y} {S : Set X}
    (hf : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) = dist x y)
    {U : Set (ℝ × X)} {U' : Set (ℝ × Y)} (hUS : ∀ z ∈ U, z.2 ∈ S)
    (hU : MapsTo (Prod.map id f) U U') {p q : ℝ × X}
    (h : staticLe U p q) : staticLe U' (Prod.map id f p) (Prod.map id f q) := by
  obtain ⟨h1, γ, hp, hq, hγ⟩ := h
  exact ⟨h1, f ∘ γ, by simp [hp], by simp [hq], hγ.map_isometricOn hf hUS hU⟩

theorem staticLt.map_isometricOn {f : X → Y} {S : Set X}
    (hf : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) = dist x y)
    {U : Set (ℝ × X)} {U' : Set (ℝ × Y)} (hUS : ∀ z ∈ U, z.2 ∈ S)
    (hU : MapsTo (Prod.map id f) U U') {p q : ℝ × X}
    (h : staticLt U p q) : staticLt U' (Prod.map id f p) (Prod.map id f q) := by
  obtain ⟨h1, L, hL, γ, hp, hq, hγ⟩ := h
  exact ⟨h1, L, hL, f ∘ γ, by simp [hp], by simp [hq], hγ.map_isometricOn hf hUS hU⟩

variable [GeodesicSpace X] [GeodesicSpace Y]

/-- **A chart of space which preserves distances on its source is, times the identity of time, a
chart isomorphism of the static spacetimes.** -/
theorem staticCausality.chartIso_prod_isometricOn (e : OpenPartialHomeomorph X Y)
    (he : ∀ x ∈ e.source, ∀ y ∈ e.source, dist (e x) (e y) = dist x y) :
    ChartIso (staticCausality X) (staticCausality Y)
      ((OpenPartialHomeomorph.refl ℝ).prod e) := by
  set E := (OpenPartialHomeomorph.refl ℝ).prod e with hE
  have hEapp : ∀ z : ℝ × X, E z = Prod.map id e z := fun z => rfl
  have hsymm : ∀ x ∈ e.target, ∀ x' ∈ e.target, dist (e.symm x) (e.symm x') = dist x x' := by
    intro x hx x' hx'
    rw [← he _ (e.map_target hx) _ (e.map_target hx'), e.right_inv hx, e.right_inv hx']
  intro U hU x hx y hy
  have hUS : ∀ z ∈ (U : Set (ℝ × X)), z.2 ∈ e.source := fun z hz => (hU hz).2
  have hmaps : MapsTo (Prod.map id e) (U : Set (ℝ × X)) (chartImage E U : Set (ℝ × Y)) :=
    fun z hz => ⟨z, ⟨hU hz, hz⟩, rfl⟩
  have hUS' : ∀ z ∈ (chartImage E U : Set (ℝ × Y)), z.2 ∈ e.target := by
    rintro _ ⟨w, ⟨hw, -⟩, rfl⟩
    exact e.map_source hw.2
  have hmaps' : MapsTo (Prod.map id e.symm) (chartImage E U : Set (ℝ × Y)) (U : Set (ℝ × X)) := by
    rintro _ ⟨w, ⟨hw, hwU⟩, rfl⟩
    have : Prod.map id e.symm (E w) = w := Prod.ext rfl (e.left_inv hw.2)
    rw [this]; exact hwU
  have hback : ∀ z ∈ (U : Set (ℝ × X)), Prod.map id e.symm (E z) = z := fun z hz =>
    Prod.ext rfl (e.left_inv (hUS z hz))
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hEapp, hEapp]; exact staticLe.map_isometricOn he hUS hmaps h
  · have := staticLe.map_isometricOn hsymm hUS' hmaps' h
    rwa [hback x hx, hback y hy] at this
  · rw [hEapp, hEapp]; exact staticLt.map_isometricOn he hUS hmaps h
  · have := staticLt.map_isometricOn hsymm hUS' hmaps' h
    rwa [hback x hx, hback y hy] at this

end IsometricOn

namespace EAlphaSector

/-! ### Open partial homeomorphisms from maps preserving distances -/

section OfIsometricOn

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A map preserving distances on a set is injective there. -/
theorem injOn_of_isometricOn {f : Y → X} {D : Set Y}
    (hf : ∀ y ∈ D, ∀ y' ∈ D, dist (f y) (f y') = dist y y') : InjOn f D := fun y hy y' hy' h => by
  rw [← dist_eq_zero, ← hf y hy y' hy', h, dist_self]

/-- A map preserving distances on a set is continuous there. -/
theorem continuousOn_of_isometricOn {f : Y → X} {D : Set Y}
    (hf : ∀ y ∈ D, ∀ y' ∈ D, dist (f y) (f y') = dist y y') : ContinuousOn f D := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  exact ⟨ε, hε, fun a ha h => by rwa [hf a ha b hb]⟩

/-- A map preserving the distances of an open set `D` and mapping it onto an open set `T`, as an
open partial homeomorphism (the inverse is `Function.invFunOn`). -/
noncomputable def ofIsometricOn [Nonempty Y] (f : Y → X) {D : Set Y} {T : Set X}
    (hD : IsOpen D) (hT : IsOpen T) (hf : ∀ y ∈ D, ∀ y' ∈ D, dist (f y) (f y') = dist y y')
    (hmaps : MapsTo f D T) (hsurj : SurjOn f D T) : OpenPartialHomeomorph Y X where
  toFun := f
  invFun := Function.invFunOn f D
  source := D
  target := T
  map_source' := hmaps
  map_target' := hsurj.mapsTo_invFunOn
  left_inv' := (injOn_of_isometricOn hf).leftInvOn_invFunOn
  right_inv' := hsurj.rightInvOn_invFunOn
  open_source := hD
  open_target := hT
  continuousOn_toFun := continuousOn_of_isometricOn hf
  continuousOn_invFun := continuousOn_of_isometricOn fun x hx x' hx' => by
    rw [← hf _ (hsurj.mapsTo_invFunOn hx) _ (hsurj.mapsTo_invFunOn hx'),
      hsurj.rightInvOn_invFunOn hx, hsurj.rightInvOn_invFunOn hx']

/-- The inverse of a chart preserving distances on its source preserves them on its target. -/
theorem symm_isometricOn (e : OpenPartialHomeomorph Y X)
    (he : ∀ y ∈ e.source, ∀ y' ∈ e.source, dist (e y) (e y') = dist y y') :
    ∀ x ∈ e.target, ∀ x' ∈ e.target, dist (e.symm x) (e.symm x') = dist x x' := by
  intro x hx x' hx'
  rw [← he _ (e.map_target hx) _ (e.map_target hx'), e.right_inv hx, e.right_inv hx']

end OfIsometricOn

/-! ### The flat sector of a direction, cut down to a disc -/

variable {α : ℝ}

/-- The half-opening of the sector charts, `min(π/2, α/4)`: two directions of one sector are less
than `min(π, α/2)` apart, so seen from the apex under their real angle. -/
noncomputable def halfAngle (α : ℝ) : ℝ := min (π / 2) (α / 4)

theorem halfAngle_pos (hα : 0 < α) : 0 < halfAngle α := lt_min (by positivity) (by positivity)

theorem halfAngle_le_pi_div_two : halfAngle α ≤ π / 2 := min_le_left _ _

theorem halfAngle_le_quarter : halfAngle α ≤ α / 4 := min_le_right _ _

/-- Polar coordinates centred on the direction `θ₁`: the point of `C_α` at distance `‖z‖` from the
apex in the direction `θ₁ + arg z`. -/
noncomputable def fromPlane (θ₁ : AddCircle α) (z : ℂ) : Cone α :=
  Cone.mk ⟨‖z‖, θ₁ + ((Complex.arg z : ℝ) : AddCircle α), norm_nonneg z⟩

/-- The regular points of `C_α` in polar coordinates: the indices of the sector charts. -/
abbrev Index (α : ℝ) : Type := {p : ConePoint α // 0 < p.r}

/-- The disc of the plane around `R`, of radius `R sin w`. -/
def planeDisc (α R : ℝ) : Set ℂ := ball (R : ℂ) (R * sin (halfAngle α))

/-- The ball of `C_α` around `p`, of radius `r_p sin w`: the source of the sector chart at `p`. -/
def coneDisc (p : ConePoint α) : Set (Cone α) := ball (Cone.mk p) (p.r * sin (halfAngle α))

/-- **Seen from the apex, a point near `(R, θ₁)` is in the sector**: if the law of cosines at the
angle `a ∈ [0, π]` is below `R sin w`, `w ≤ π/2`, then `a < w`. -/
theorem angle_lt_of_coneE_lt {R s a w : ℝ} (hR : 0 < R) (hs : 0 ≤ s) (ha : 0 ≤ a) (haπ : a ≤ π)
    (hw : 0 < w) (hwπ : w ≤ π / 2) (h : coneE R s a < R * sin w) : a < w := by
  by_contra hwa
  push Not at hwa
  have hsinw : sin w ≤ 1 := sin_le_one w
  have hE : 0 ≤ coneE R s a := coneE_nonneg _ _ _
  have hsq := coneE_sq R s a
  rcases le_or_gt a (π / 2) with ha2 | ha2
  · -- `R sin w ≤ R sin a ≤ coneE`
    have h1 : sin w ≤ sin a := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) ha2 hwa
    have h2 : (R * sin a) ^ 2 ≤ coneE R s a ^ 2 := by
      rw [hsq, show R ^ 2 + s ^ 2 - 2 * R * s * cos a = (s - R * cos a) ^ 2 + (R * sin a) ^ 2 by
        have := sin_sq_add_cos_sq a; linear_combination (-R ^ 2) * this]
      nlinarith [sq_nonneg (s - R * cos a)]
    have h3 : 0 ≤ R * sin a := mul_nonneg hR.le (sin_nonneg_of_nonneg_of_le_pi ha haπ)
    have h4 : R * sin a ≤ coneE R s a := (pow_le_pow_iff_left₀ h3 hE two_ne_zero).1 h2
    nlinarith
  · -- `cos a ≤ 0`, so `coneE ≥ R ≥ R sin w`
    have hcos : cos a ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le ha2.le (by linarith [pi_pos])
    have h2 : R ^ 2 ≤ coneE R s a ^ 2 := by
      rw [hsq]; nlinarith [mul_nonneg hR.le hs, sq_nonneg s]
    have h4 : R ≤ coneE R s a := (pow_le_pow_iff_left₀ hR.le hE two_ne_zero).1 h2
    nlinarith

/-- The law of cosines from the origin to a point of the plane. -/
theorem coneE_arg (R : ℝ) (z : ℂ) : coneE R ‖z‖ (Complex.arg z) = dist z R := by
  rw [coneE_eq_norm, Complex.norm_mul_exp_arg_mul_I, dist_comm, dist_eq_norm]

/-- A point of the planar disc is off the origin, in the sector `|arg z| < w`. -/
theorem abs_arg_lt_of_mem_planeDisc {R : ℝ} (hR : 0 < R) (hα : 0 < α) {z : ℂ}
    (hz : z ∈ planeDisc α R) : z ≠ 0 ∧ |Complex.arg z| < halfAngle α := by
  have hz' : dist z R < R * sin (halfAngle α) := hz
  have hsin : sin (halfAngle α) ≤ 1 := sin_le_one _
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, dist_comm, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hz'
    nlinarith
  · refine angle_lt_of_coneE_lt hR (norm_nonneg z) (abs_nonneg _) (Complex.abs_arg_le_pi z)
      (halfAngle_pos hα) halfAngle_le_pi_div_two ?_
    rwa [coneE_abs, coneE_arg]

/-- The centre of the disc is the point `(R, θ₁)`. -/
theorem fromPlane_ofReal (θ₁ : AddCircle α) {R : ℝ} (hR : 0 ≤ R) :
    fromPlane θ₁ (R : ℂ) = Cone.mk ⟨R, θ₁, hR⟩ := by
  unfold fromPlane
  congr 1
  ext
  · simp [abs_of_nonneg hR]
  · simp [Complex.arg_ofReal_of_nonneg hR]

variable [hα : Fact (0 < α)]

/-- **In the sector the cone distance is the planar distance**: `min(δ, π) = δ` there. -/
theorem dist_fromPlane (θ₁ : AddCircle α) {z z' : ℂ} (hz : |Complex.arg z| < halfAngle α)
    (hz' : |Complex.arg z'| < halfAngle α) :
    dist (fromPlane θ₁ z) (fromPlane θ₁ z') = dist z z' := by
  set a := Complex.arg z
  set a' := Complex.arg z'
  have hw := halfAngle_le_pi_div_two (α := α)
  have hw' := halfAngle_le_quarter (α := α)
  have hd : |a - a'| < 2 * halfAngle α := by
    have := abs_sub a a'; linarith
  have hnorm : ‖((a - a' : ℝ) : AddCircle α)‖ = |a - a'| :=
    (AddCircle.norm_coe_eq_abs_iff α hα.out.ne').2 (by rw [abs_of_pos hα.out]; linarith)
  have hang : angDist (θ₁ + (a : AddCircle α)) (θ₁ + (a' : AddCircle α)) = |a - a'| := by
    unfold angDist
    rw [add_sub_add_left_eq_sub, ← AddCircle.coe_sub, hnorm]
    exact min_eq_left (by linarith)
  have hfac : z - z' = Complex.exp (a * Complex.I) *
      ((‖z‖ : ℂ) - ‖z'‖ * Complex.exp ((a' - a : ℝ) * Complex.I)) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z, ← Complex.norm_mul_exp_arg_mul_I z']
    have : Complex.exp ((a' : ℂ) * Complex.I) =
        Complex.exp (a * Complex.I) * Complex.exp ((a' - a : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [fromPlane, fromPlane, Cone.dist_mk, ConePoint.dist_def]
  simp only
  rw [hang, coneE_abs, ← coneE_neg, neg_sub, coneE_eq_norm, dist_eq_norm, hfac, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The planar disc goes into the ball of the cone. -/
theorem mapsTo_fromPlane (k : Index α) :
    MapsTo (fromPlane k.1.θ) (planeDisc α k.1.r) (coneDisc k.1) := by
  intro z hz
  have h0 : |Complex.arg (k.1.r : ℂ)| < halfAngle α := by
    rw [Complex.arg_ofReal_of_nonneg k.1.r_nonneg, abs_zero]; exact halfAngle_pos hα.out
  show dist (fromPlane k.1.θ z) (Cone.mk k.1) < _
  rw [← fromPlane_ofReal k.1.θ k.1.r_nonneg, dist_fromPlane _
    (abs_arg_lt_of_mem_planeDisc k.2 hα.out hz).2 h0]
  exact hz

/-- **Onto**: every point of the ball of the cone is in the sector, at a planar position of the
disc. -/
theorem surjOn_fromPlane (k : Index α) :
    SurjOn (fromPlane k.1.θ) (planeDisc α k.1.r) (coneDisc k.1) := by
  intro y hy
  obtain ⟨q, rfl⟩ := Cone.mk_surjective y
  obtain ⟨p, hp⟩ := k
  have hy' : coneE p.r q.r (angDist p.θ q.θ) < p.r * sin (halfAngle α) := by
    have : dist (Cone.mk q) (Cone.mk p) < p.r * sin (halfAngle α) := hy
    rwa [Cone.dist_mk, dist_comm, ConePoint.dist_def] at this
  have hw := halfAngle_le_pi_div_two (α := α)
  have hw0 := halfAngle_pos hα.out
  have ha := angle_lt_of_coneE_lt hp q.r_nonneg (angDist_nonneg _ _) (angDist_le_pi _ _) hw0 hw hy'
  have hθ : ‖q.θ - p.θ‖ < halfAngle α := by
    rw [norm_sub_rev]
    rcases min_lt_iff.1 ha with h | h
    · exact h
    · linarith [pi_pos]
  have hsin : sin (halfAngle α) ≤ 1 := sin_le_one _
  have hq : 0 < q.r := by
    have h1 : |p.r - q.r| ≤ dist p q := ConePoint.abs_r_sub_le_dist p q
    rw [ConePoint.dist_def] at h1
    have := le_abs_self (p.r - q.r)
    nlinarith
  obtain ⟨σ, hσ, hσn⟩ := exists_addCircle_rep (q.θ - p.θ)
  have hσw : |σ| < halfAngle α := hσn ▸ hθ
  set z : ℂ := (q.r : ℂ) * Complex.exp (σ * Complex.I) with hzdef
  have hzn : ‖z‖ = q.r := by
    rw [hzdef, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hq]
  have hza : Complex.arg z = σ := by
    rw [hzdef, Complex.arg_real_mul _ hq, Complex.exp_mul_I]
    rw [abs_lt] at hσw
    exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hfz : fromPlane p.θ z = Cone.mk q := by
    unfold fromPlane
    congr 1
    ext
    · exact hzn
    · show p.θ + ((Complex.arg z : ℝ) : AddCircle α) = q.θ
      rw [hza, hσ]; abel
  refine ⟨z, ?_, hfz⟩
  have h0 : |Complex.arg (p.r : ℂ)| < halfAngle α := by
    rw [Complex.arg_ofReal_of_nonneg p.r_nonneg, abs_zero]; exact hw0
  show dist z p.r < p.r * sin (halfAngle α)
  rw [← dist_fromPlane p.θ (by rw [hza]; exact hσw) h0, hfz, fromPlane_ofReal p.θ p.r_nonneg]
  exact hy

/-- The polar chart of the disc, from the plane. -/
noncomputable def planeChart (k : Index α) : OpenPartialHomeomorph ℂ (Cone α) :=
  ofIsometricOn (fromPlane k.1.θ) isOpen_ball isOpen_ball
    (fun _ hz _ hz' => dist_fromPlane k.1.θ (abs_arg_lt_of_mem_planeDisc k.2 hα.out hz).2
      (abs_arg_lt_of_mem_planeDisc k.2 hα.out hz').2)
    (mapsTo_fromPlane k) (surjOn_fromPlane k)

/-- **The sector chart of `C_α` at `p`**, into the Euclidean plane `ℝ²`. -/
noncomputable def coneChart (k : Index α) :
    OpenPartialHomeomorph (Cone α) (EuclideanSpace ℝ (Fin 2)) :=
  (planeChart k).symm.trans
    Complex.orthonormalBasisOneI.repr.toHomeomorph.toOpenPartialHomeomorph

/-- **The sector chart of `E_α` at `p`**: the time coordinate times the sector chart of `C_α`. -/
noncomputable def chart (k : Index α) : OpenPartialHomeomorph (Massive α) (Minkowski 2) :=
  (OpenPartialHomeomorph.refl ℝ).prod (coneChart k)

theorem planeChart_apply (k : Index α) (z : ℂ) : planeChart k z = fromPlane k.1.θ z := rfl

theorem planeChart_source (k : Index α) : (planeChart k).source = planeDisc α k.1.r := rfl

theorem planeChart_target (k : Index α) : (planeChart k).target = coneDisc k.1 := rfl

/-- The polar chart preserves distances on its source. -/
theorem planeChart_isometricOn (k : Index α) :
    ∀ z ∈ (planeChart k).source, ∀ z' ∈ (planeChart k).source,
      dist (planeChart k z) (planeChart k z') = dist z z' := fun _ hz _ hz' =>
  dist_fromPlane k.1.θ (abs_arg_lt_of_mem_planeDisc k.2 hα.out hz).2
    (abs_arg_lt_of_mem_planeDisc k.2 hα.out hz').2

theorem coneChart_source (k : Index α) : (coneChart k).source = coneDisc k.1 := by
  simp [coneChart, planeChart_target]

theorem coneChart_apply (k : Index α) (x : Cone α) :
    coneChart k x = Complex.orthonormalBasisOneI.repr ((planeChart k).symm x) := rfl

theorem chart_source (k : Index α) : (chart k).source = univ ×ˢ coneDisc k.1 := by
  simp [chart, coneChart_source]

theorem chart_apply (k : Index α) (x : Massive α) : chart k x = (x.1, coneChart k x.2) := rfl

/-- The sector chart of `C_α` preserves distances on its source. -/
theorem coneChart_isometricOn (k : Index α) :
    ∀ x ∈ (coneChart k).source, ∀ y ∈ (coneChart k).source,
      dist (coneChart k x) (coneChart k y) = dist x y := by
  intro x hx y hy
  rw [coneChart_source] at hx hy
  rw [coneChart_apply, coneChart_apply, LinearIsometryEquiv.dist_map]
  exact symm_isometricOn (planeChart k) (planeChart_isometricOn k) x hx y hy

/-- **The sector chart is an isomorphism of topological spacetimes** onto an open subset of
`E^{1,2}`. -/
theorem chartIso_chart (k : Index α) : ChartIso (massive α) (minkowski 2) (chart k) :=
  staticCausality.chartIso_prod_isometricOn (coneChart k) (coneChart_isometricOn k)

theorem sin_halfAngle_pos : 0 < sin (halfAngle α) :=
  sin_pos_of_pos_of_lt_pi (halfAngle_pos hα.out)
    (by linarith [halfAngle_le_pi_div_two (α := α), pi_pos])

/-- The sources lie in the regular part. -/
theorem chart_source_subset_regPart (k : Index α) : (chart k).source ⊆ regPart α := by
  intro x hx h
  rw [chart_source] at hx
  have h1 : dist x.2 (Cone.mk k.1) < k.1.r * sin (halfAngle α) := hx.2
  have h2 : x.2 = Cone.apex := h
  rw [h2, ← Cone.rad, Cone.rad_mk] at h1
  have := sin_le_one (halfAngle α)
  nlinarith [k.2]

/-- The sources cover the regular part. -/
theorem exists_mem_chart_source {x : Massive α} (hx : x ∈ regPart α) :
    ∃ k : Index α, x ∈ (chart k).source := by
  obtain ⟨q, hq⟩ := Cone.mk_surjective x.2
  have hr : 0 < q.r := by
    refine lt_of_le_of_ne q.r_nonneg fun h0 => hx ?_
    show x.2 = Cone.apex
    rw [← hq]; exact Cone.mk_eq_apex h0.symm
  refine ⟨⟨q, hr⟩, ?_⟩
  rw [chart_source]
  refine ⟨trivial, ?_⟩
  show dist x.2 (Cone.mk q) < q.r * sin (halfAngle α)
  rw [← hq, dist_self]
  exact mul_pos hr sin_halfAngle_pos

/-! ### Transitions: rotations -/

/-- The rotation of angle `c` of the plane `ℝ² ≅ ℂ`. -/
noncomputable def planeRot (c : ℝ) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.symm.trans
    ((rotation (Circle.exp c)).trans Complex.orthonormalBasisOneI.repr)

theorem det_planeRot (c : ℝ) :
    LinearMap.det ((planeRot c).toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) = 1 := by
  have e : ((planeRot c).toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) =
      (Complex.orthonormalBasisOneI.repr.toLinearEquiv : ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ∘ₗ
        ((rotation (Circle.exp c)).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ
          (Complex.orthonormalBasisOneI.repr.toLinearEquiv.symm :
            EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℂ) :=
    LinearMap.ext fun _ => rfl
  rw [e, LinearMap.det_conj, det_rotation]

theorem planeRot_repr (c : ℝ) (u : ℂ) :
    planeRot c (Complex.orthonormalBasisOneI.repr u) =
      Complex.orthonormalBasisOneI.repr (Complex.exp (c * Complex.I) * u) := by
  simp [planeRot, rotation_apply, Circle.coe_exp]

/-- **The rotation of angle `c` of `E^{1,2}` about the time axis**, an element of
`Isom(E^{1,2})`. -/
noncomputable def rotIsom (c : ℝ) : Flat.isom 2 :=
  Flat.Nonlox.nfIsom (Flat.Nonlox.nfSpatial (planeRot c))
    (Flat.Nonlox.nfSpatial_mem_lorentz (planeRot c) (det_planeRot c))

theorem rotIsom_smul (c : ℝ) (v : Minkowski 2) : rotIsom c • v = (v.1, planeRot c v.2) := rfl

omit hα in
/-- Two polar positions of one regular point have the same modulus, and directions which agree. -/
theorem fromPlane_eq_fromPlane {θ θ' : AddCircle α} {z z' : ℂ} (hz : z ≠ 0)
    (h : fromPlane θ z = fromPlane θ' z') :
    ‖z‖ = ‖z'‖ ∧ θ + ((Complex.arg z : ℝ) : AddCircle α) =
      θ' + ((Complex.arg z' : ℝ) : AddCircle α) := by
  unfold fromPlane at h
  have hd := Cone.mk_eq_mk_iff.1 h
  have hr : ‖z‖ = ‖z'‖ := by
    have := ConePoint.abs_r_sub_le_dist
      ⟨‖z‖, θ + ((Complex.arg z : ℝ) : AddCircle α), norm_nonneg z⟩
      ⟨‖z'‖, θ' + ((Complex.arg z' : ℝ) : AddCircle α), norm_nonneg z'⟩
    rw [hd] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  refine ⟨hr, ?_⟩
  rw [ConePoint.dist_def] at hd
  simp only at hd
  rw [← hr] at hd
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have ha : angDist (θ + ((Complex.arg z : ℝ) : AddCircle α))
      (θ' + ((Complex.arg z' : ℝ) : AddCircle α)) = 0 := by
    by_contra hne
    have := Cone.coneE_self_pos hpos (lt_of_le_of_ne (angDist_nonneg _ _) (Ne.symm hne))
      (angDist_le_pi _ _)
    linarith
  have hn : ‖(θ + ((Complex.arg z : ℝ) : AddCircle α)) -
      (θ' + ((Complex.arg z' : ℝ) : AddCircle α))‖ = 0 := by
    by_contra hne
    have := lt_min (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) pi_pos
    unfold angDist at ha
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hn)

/-- **Two sector charts differ by one rotation on their whole overlap**: the two polar angles of a
common point differ by a representative of `θ₁ − θ₂` of absolute value `< 2w ≤ α/2`, which is
unique. -/
theorem exists_rotation (k k' : Index α) :
    ∃ c : ℝ, ∀ x ∈ (chart k).source ∩ (chart k').source, chart k' x = rotIsom c • chart k x := by
  have hw := halfAngle_le_quarter (α := α)
  have key : ∀ {y : Cone α}, y ∈ coneDisc k.1 → y ∈ coneDisc k'.1 →
      ‖(planeChart k').symm y‖ = ‖(planeChart k).symm y‖ ∧
      (((Complex.arg ((planeChart k').symm y) - Complex.arg ((planeChart k).symm y) : ℝ)) :
        AddCircle α) = k.1.θ - k'.1.θ ∧
      |Complex.arg ((planeChart k').symm y) - Complex.arg ((planeChart k).symm y)| <
        2 * halfAngle α := by
    intro y hy hy'
    have hu := (planeChart k).map_target hy
    have hu' := (planeChart k').map_target hy'
    have he : fromPlane k.1.θ ((planeChart k).symm y) =
        fromPlane k'.1.θ ((planeChart k').symm y) := by
      rw [← planeChart_apply, ← planeChart_apply, (planeChart k).right_inv hy,
        (planeChart k').right_inv hy']
    have h1 := abs_arg_lt_of_mem_planeDisc k.2 hα.out hu
    have h2 := abs_arg_lt_of_mem_planeDisc k'.2 hα.out hu'
    obtain ⟨hr, hθ⟩ := fromPlane_eq_fromPlane h1.1 he
    refine ⟨hr.symm, ?_, ?_⟩
    · rw [AddCircle.coe_sub, sub_eq_sub_iff_add_eq_add, hθ, add_comm]
    · have := abs_sub (Complex.arg ((planeChart k').symm y)) (Complex.arg ((planeChart k).symm y))
      linarith [h1.2, h2.2]
  by_cases hne : ∃ x, x ∈ (chart k).source ∩ (chart k').source
  · obtain ⟨x₀, hx₀⟩ := hne
    rw [chart_source, chart_source] at hx₀
    obtain ⟨-, h0, h0c⟩ := key (mem_prod.1 hx₀.1).2 (mem_prod.1 hx₀.2).2
    refine ⟨Complex.arg ((planeChart k').symm x₀.2) - Complex.arg ((planeChart k).symm x₀.2),
      fun x hx => ?_⟩
    rw [chart_source, chart_source] at hx
    obtain ⟨hr, hc, hcc⟩ := key (mem_prod.1 hx.1).2 (mem_prod.1 hx.2).2
    set c := Complex.arg ((planeChart k').symm x₀.2) - Complex.arg ((planeChart k).symm x₀.2)
    set u := (planeChart k).symm x.2
    set u' := (planeChart k').symm x.2
    have hmem : ∀ d : ℝ, |d| < 2 * halfAngle α → d ∈ Ico (-(α / 2)) (-(α / 2) + α) := fun d hd => by
      rw [abs_lt] at hd; constructor <;> linarith
    have hdc : Complex.arg u' - Complex.arg u = c :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem _ hcc) (hmem _ h0c)).1 (hc.trans h0.symm)
    have hu' : u' = Complex.exp (c * Complex.I) * u := by
      rw [← Complex.norm_mul_exp_arg_mul_I u', ← Complex.norm_mul_exp_arg_mul_I u, hr,
        show Complex.arg u' = c + Complex.arg u by linarith]
      rw [show ((c + Complex.arg u : ℝ) : ℂ) * Complex.I = c * Complex.I + Complex.arg u * Complex.I
        by push_cast; ring, Complex.exp_add]
      ring
    rw [chart_apply, chart_apply, rotIsom_smul, coneChart_apply, coneChart_apply, planeRot_repr]
    refine Prod.ext rfl ?_
    show Complex.orthonormalBasisOneI.repr u' =
      Complex.orthonormalBasisOneI.repr (Complex.exp (c * Complex.I) * u)
    rw [hu']
  · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- **The transitions of the sector charts lie in the `(Isom(E^{1,2}), E^{1,2})`-groupoid.** -/
theorem symm_trans_chart_mem_gxGroupoid (k k' : Index α) :
    (chart k).symm.trans (chart k') ∈ gxGroupoid (Flat.isom 2) (Minkowski 2) := by
  obtain ⟨c, hc⟩ := exists_rotation k k'
  refine symm_trans_mem_gxGroupoid fun x hx => ⟨rotIsom c, ?_⟩
  filter_upwards [((chart k).open_source.inter (chart k').open_source).mem_nhds hx] with z hz
  exact hc z hz

/-- **Every chart compatible with the sector charts is an isomorphism**: a chart of `E_α` into
`E^{1,2}` with source in `reg(E_α)` whose transitions from the sector charts lie in the
`(Isom(E^{1,2}), E^{1,2})`-groupoid (a chart of the maximal atlas the sector charts generate, the
whole sectors among them) is a `ChartIso`. The argument of `chartIso_of_mem_maximalAtlas`, with the
sector charts in place of `chartAt`. -/
theorem chartIso_of_compatible {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (hsrc : e.source ⊆ regPart α)
    (he : ∀ k : Index α, (chart k).symm.trans e ∈ gxGroupoid (Flat.isom 2) (Minkowski 2)) :
    ChartIso (massive α) (minkowski 2) e := by
  have hCe := (minkowski 2).chartTransport_chartIso e
  have hloc : ∀ x ∈ chartSource e, ∃ O : Opens (Massive α), x ∈ O ∧
      AgreeOn (massive α) ((minkowski 2).chartTransport e) O := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_mem_chart_source (hsrc hx)
    obtain ⟨g, O, hxO, hO, heq⟩ := exists_smul_eq_of_mem_gxGroupoid (he k) hk hx
    exact ⟨O, hxO, (chartIso_chart k).agreeOn_of_smul Flat.isom_strongMorphism hCe hO heq⟩
  have hAC : (massive α).AbsolutelyMinimalOn (chartSource e) :=
    massive_causallyArcConnected.absolutelyMinimalOn_all _
  have hACe : ((minkowski 2).chartTransport e).AbsolutelyMinimalOn (chartSource e) :=
    hCe.absolutelyMinimalOn le_rfl (minkowski_causallyArcConnected.absolutelyMinimalOn_all _)
  refine hCe.congr fun V hV x y => ?_
  have h₁ := imp_of_agree_locally hAC hloc hV (x := x) (y := y)
  have h₂ := imp_of_agree_locally hACe (fun z hz => by
    obtain ⟨O, hzO, hO⟩ := hloc z hz
    exact ⟨O, hzO, hO.symm⟩) hV (x := x) (y := y)
  exact ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩

/-- **`reg(E_α)` is an `(Isom(E^{1,2}), E^{1,2})`-manifold whose charts are isomorphisms**
(`ETT.tex:1331–1333`, for `α > 0`): the sector charts have their sources in `reg(E_α)` and cover
it, their transitions lie in the groupoid, each is a `ChartIso`, and so is every chart compatible
with them. -/
theorem regPart_isomAtlas :
    (∀ k : Index α, (chart k).source ⊆ regPart α) ∧
      (∀ x ∈ regPart α, ∃ k : Index α, x ∈ (chart k).source) ∧
      (∀ k k' : Index α, (chart k).symm.trans (chart k') ∈ gxGroupoid (Flat.isom 2) (Minkowski 2)) ∧
      (∀ k : Index α, ChartIso (massive α) (minkowski 2) (chart k)) ∧
      ∀ e : OpenPartialHomeomorph (Massive α) (Minkowski 2), e.source ⊆ regPart α →
        (∀ k : Index α, (chart k).symm.trans e ∈ gxGroupoid (Flat.isom 2) (Minkowski 2)) →
        ChartIso (massive α) (minkowski 2) e :=
  ⟨chart_source_subset_regPart, fun _ hx => exists_mem_chart_source hx,
    symm_trans_chart_mem_gxGroupoid, chartIso_chart,
    fun _ hsrc he => chartIso_of_compatible hsrc he⟩

/-- **Why the sectors have opening at most `α/2`**: a sector of opening `< π` and `< α` is not
enough for the polar map to preserve the cone distance. In `C_{π/2}` the directions `0` and
`2π/5` (both in a sector of opening `9π/20 < π/2`) are `π/10` apart the other way round, so the points at
radius `1` are closer in the cone than their planar images `1`, `e^{2πi/5}`. (The roadmap note's
`[r]` reason for its sector charts fails here. Its conclusion does not need it: a ChartIso reads
distances along curves only, and `chartIso_of_compatible` gives it for every chart compatible with
the discs; the wide sector chart itself is not built here.) -/
theorem fromPlane_wide_not_isometric :
    dist (fromPlane (α := π / 2) 0 1) (fromPlane 0 (Complex.exp ((2 * π / 5 : ℝ) * Complex.I))) <
      dist (1 : ℂ) (Complex.exp ((2 * π / 5 : ℝ) * Complex.I)) := by
  have hpi := pi_pos
  set e := Complex.exp ((2 * π / 5 : ℝ) * Complex.I) with he
  have harg : Complex.arg e = 2 * π / 5 := by
    rw [he, Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩
  have hcirc : ‖((0 : AddCircle (π / 2)) + ((Complex.arg 1 : ℝ) : AddCircle (π / 2))) -
      ((0 : AddCircle (π / 2)) + ((Complex.arg e : ℝ) : AddCircle (π / 2)))‖ = π / 10 := by
    rw [Complex.arg_one, harg, zero_add, zero_add, ← AddCircle.coe_sub,
      show (0 : ℝ) - 2 * π / 5 = π / 10 - π / 2 by ring, AddCircle.coe_sub, AddCircle.coe_period,
      sub_zero, (AddCircle.norm_coe_eq_abs_iff (π / 2) (by positivity)).2
        (by rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]; linarith),
      abs_of_pos (by positivity)]
  have hd : dist (fromPlane (α := π / 2) 0 1) (fromPlane 0 e) = coneE 1 1 (π / 10) := by
    rw [fromPlane, fromPlane, Cone.dist_mk, ConePoint.dist_def]
    simp only
    rw [angDist, hcirc, min_eq_left (by linarith), norm_one, Complex.norm_exp_ofReal_mul_I]
  have hp : dist (1 : ℂ) e = coneE 1 1 (2 * π / 5) := by
    rw [coneE_eq_norm, dist_eq_norm, he, Complex.ofReal_one, one_mul]
  rw [hd, hp]
  unfold coneE
  refine sqrt_lt_sqrt (coneE_radicand_nonneg _ _ _) ?_
  have := cos_lt_cos_of_nonneg_of_le_pi (by positivity : (0 : ℝ) ≤ π / 10)
    (by linarith : 2 * π / 5 ≤ π) (by linarith : π / 10 < 2 * π / 5)
  linarith

end EAlphaSector

/-! ### `hreg`, and `massA_positive` with a chart into `E_κ` -/

open EAlphaSector

/-- **The sector charts of the models `E_κ`, `κ > 0`**, the family `r` of `massA_positive`. -/
noncomputable def massiveSectorChart (κ : {κ : ℝ // 0 < κ}) (k : Index κ.1) :
    OpenPartialHomeomorph (Massive κ.1) (Minkowski 2) :=
  @EAlphaSector.chart κ.1 ⟨κ.2⟩ k

/-- **`hreg` in `Causal.GXSingular`'s form**: every sector chart of every `E_κ` is an isomorphism
onto an open subset of `E^{1,2}`. -/
theorem hreg_sectorChart : ∀ κ k, ChartIso (massiveOf κ) (minkowski 2) (massiveSectorChart κ k) :=
  fun κ k => @EAlphaSector.chartIso_chart κ.1 ⟨κ.2⟩ k

/-- The transitions of the sector charts of `E_κ` lie in
`gxGroupoid (Flat.isom 2) (Minkowski 2)`. -/
theorem sectorChart_symm_trans_mem (κ : {κ : ℝ // 0 < κ}) (k k' : Index κ.1) :
    (massiveSectorChart κ k).symm.trans (massiveSectorChart κ k') ∈ gxGroupoid (Flat.isom 2) (Minkowski 2) :=
  @EAlphaSector.symm_trans_chart_mem_gxGroupoid κ.1 ⟨κ.2⟩ k k'

universe u

/-- **`massA_positive` with `hreg` discharged** for the sector charts: only the atlas remains. -/
theorem massA_positive_sectorCharts {M : Type u} [TopologicalSpace M]
    {I J : Type} (eX : I → OpenPartialHomeomorph M (Minkowski 2)) (β : J → {κ : ℝ // 0 < κ})
    (eY : ∀ j, OpenPartialHomeomorph M (Massive (β j).1))
    (hcover : ∀ x : M, (∃ i, x ∈ (eX i).source) ∨ ∃ j, x ∈ (eY j).source)
    (hXX : ∀ i i', (eX i).symm.trans (eX i') ∈ gxGroupoid (Flat.isom 2) (Minkowski 2))
    (hXY : ∀ i j, ∀ x ∈ (eX i).source, x ∈ (eY j).source → ∃ k : Index (β j).1,
      ∃ g : Flat.isom 2, ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eX i) ⊓ chartSource (eY j) ∧
        ∀ z ∈ O, eY j z ∈ (massiveSectorChart (β j) k).source ∧
          massiveSectorChart (β j) k (eY j z) = g • eX i z)
    (hYY : ∀ j j', ∀ x ∈ (eY j).source, x ∈ (eY j').source →
      ∃ ψ : OpenPartialHomeomorph (Massive (β j).1) (Massive (β j').1),
        ChartIso (massiveOf (β j)) (massiveOf (β j')) ψ ∧
        ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eY j) ⊓ chartSource (eY j') ∧
          ∀ z ∈ O, eY j z ∈ ψ.source ∧ ψ (eY j z) = eY j' z) :
    ∃ C : Causality M, IsAtlasCausality C eX β eY (minkowski 2) massiveOf ∧
      (∀ C' : Causality M, IsAtlasCausality C' eX β eY (minkowski 2) massiveOf → C' = C) ∧
      C.CausallyArcConnected ∧ C.PushUp :=
  massA_positive (K := fun κ => Index κ.1) massiveSectorChart eX β eY hreg_sectorChart hcover hXX hXY hYY

/-- **The first `massA_positive` witness with a chart into an `E_κ`**: `M = E_κ` with its sector
charts into `E^{1,2}` and the identity into `E_κ`. The atlas satisfies every hypothesis of
`massA_positive`, `massive κ` is a causality of the atlas, and it is the only one. -/
theorem massA_positive_massive (κ : {κ : ℝ // 0 < κ}) :
    IsAtlasCausality (massiveOf κ) (massiveSectorChart κ) (fun _ : Unit => κ)
        (fun _ => OpenPartialHomeomorph.refl (Massive κ.1)) (minkowski 2) massiveOf ∧
      ∀ C : Causality (Massive κ.1),
        IsAtlasCausality C (massiveSectorChart κ) (fun _ : Unit => κ)
          (fun _ => OpenPartialHomeomorph.refl (Massive κ.1)) (minkowski 2) massiveOf →
        C = massiveOf κ ∧ C.CausallyArcConnected ∧ C.PushUp := by
  haveI : Fact (0 < κ.1) := ⟨κ.2⟩
  have hmk : IsAtlasCausality (massiveOf κ) (massiveSectorChart κ) (fun _ : Unit => κ)
      (fun _ => OpenPartialHomeomorph.refl (Massive κ.1)) (minkowski 2) massiveOf :=
    ⟨hreg_sectorChart κ, fun _ => chartIso_refl _, massive_absolutelyMinimal⟩
  obtain ⟨C₀, -, huniq, hcac, hpush⟩ := massA_positive_sectorCharts (massiveSectorChart κ)
    (fun _ : Unit => κ) (fun _ => OpenPartialHomeomorph.refl (Massive κ.1))
    (fun x => Or.inr ⟨(), mem_univ x⟩) (sectorChart_symm_trans_mem κ)
    (fun i _ _ hx _ => ⟨i, 1, chartSource (massiveSectorChart κ i), hx,
      le_inf le_rfl fun z _ => mem_univ z, fun _ hz => ⟨hz, (one_smul _ _).symm⟩⟩)
    (fun _ _ _ _ _ => ⟨OpenPartialHomeomorph.refl _, chartIso_refl _, ⊤, trivial,
      fun z _ => ⟨mem_univ z, mem_univ z⟩, fun _ _ => ⟨mem_univ _, rfl⟩⟩)
  have h₀ : massiveOf κ = C₀ := huniq _ hmk
  refine ⟨hmk, fun C hC => ?_⟩
  have h₁ : C = C₀ := huniq C hC
  subst h₁
  exact ⟨h₀.symm, hcac, hpush⟩

/-- The witness at `κ = π`, a cone of deficit angle `π`. -/
theorem massA_positive_massive_pi :
    IsAtlasCausality (massiveOf ⟨π, pi_pos⟩) (massiveSectorChart ⟨π, pi_pos⟩) (fun _ : Unit => ⟨π, pi_pos⟩)
        (fun _ => OpenPartialHomeomorph.refl (Massive π)) (minkowski 2) massiveOf ∧
      ∀ C : Causality (Massive π),
        IsAtlasCausality C (massiveSectorChart ⟨π, pi_pos⟩) (fun _ : Unit => ⟨π, pi_pos⟩)
          (fun _ => OpenPartialHomeomorph.refl (Massive π)) (minkowski 2) massiveOf →
        C = massiveOf ⟨π, pi_pos⟩ ∧ C.CausallyArcConnected ∧ C.PushUp :=
  massA_positive_massive ⟨π, pi_pos⟩

/-- The witness at `κ = 4π`, a cone of excess angle `2π`. -/
theorem massA_positive_massive_four_pi :
    IsAtlasCausality (massiveOf ⟨4 * π, by positivity⟩) (massiveSectorChart ⟨4 * π, by positivity⟩)
        (fun _ : Unit => ⟨4 * π, by positivity⟩)
        (fun _ => OpenPartialHomeomorph.refl (Massive (4 * π))) (minkowski 2) massiveOf ∧
      ∀ C : Causality (Massive (4 * π)),
        IsAtlasCausality C (massiveSectorChart ⟨4 * π, by positivity⟩)
          (fun _ : Unit => ⟨4 * π, by positivity⟩)
          (fun _ => OpenPartialHomeomorph.refl (Massive (4 * π))) (minkowski 2) massiveOf →
        C = massiveOf ⟨4 * π, by positivity⟩ ∧ C.CausallyArcConnected ∧ C.PushUp :=
  massA_positive_massive ⟨4 * π, by positivity⟩

end Causal
