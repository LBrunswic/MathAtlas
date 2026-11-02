import GX.SingularII.Tame
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The hyperbolic plane, cusped hyperbolic surfaces, and `ex:take_closed_unit_disc`

Package WP-35i (DEC-71: "build ℍ²"), extended by WP-40b (DEC-81: the **metric reading**).
`papers/gx`, `RamcovGX.tex:1877–1886`, on WP-27i's `GX.SingularII.Tame` (whose
`GX.not_isOpen_horodisc_insert` is reused for the last sentence).

* `ex:take_closed_unit_disc` — `RamcovGX.tex:1877` — partial: every assertion of the example is
  proved for `M ∖ S` carrying a **complete hyperbolic metric** with a cusp at each point of `S`
  (`GX.take_closed_unit_disc_metric`, hypothesis `GX.IsCuspedHyperbolicMetric`; the
  `(G, X)` form `GX.take_closed_unit_disc`, hypothesis `GX.IsCuspedHyperbolic`); the two readings
  agree (`GX.IsCuspedHyperbolicMetric.isCuspedHyperbolic`,
  `GX.IsCuspedHyperbolic.exists_unique_metric`). Missing for `closed` (SCOPE (b)): the
  thick–thin step "finite volume ⇒ a cusp at each puncture" (the cusps are assumed; that they
  have finite area is proved, `GX.CuspChart.cusp_finite_area`), and the Riemannian tensor.
  The metric content (DEC-81): the hyperbolic metric `GX.IsHyperbolicMetric` (a length metric
  giving the topology, locally the metric of `ℍ` in the charts), **unique**
  (`GX.IsHyperbolicMetric.unique`); for complete `(G, X)`-surfaces it exists and is complete
  (`GX.IsCompleteHyperbolic.exists_isHyperbolicMetric`, the quotient metric
  `GX.IsHypQuotient.metricSpace`); **metric completeness ⇔ Thurston–Goldman completeness**
  (`GX.IsHyperbolicMetric.completeSpace_iff`; Hopf–Rinow,
  `GX.IsHyperbolicMetric.isCompleteHyperbolic`, `GX.IsDevLocalIsometry.exists_homeomorph`);
  `ℍ` is a geodesic space (`GX.exists_hypGeodesic`, `GX.hypGeod`); the area `dx dy / y²` of a
  cusp strip is `1/c` (`GX.volume_cuspStrip`).
  `X = ClosedDisc`, the open disc `ℍ = PoincareDisc` with the Poincaré distance `GX.hypDist`
  (mathlib's `UpperHalfPlane` distance through the Cayley transform), `G = Isom(ℍ) = GX.HypIsom`
  (all isometries, `GX.HypIsom.exists_mobF`), acting on `X` by homeomorphisms
  (`GX.HypIsom.extFun`; `(G,X)` analytical, `GX.analyticStructure_closedDisc`; `X` locally
  unloopable, `GX.isLocallyUnloopable_closedDisc`); `M` a singular `(G,X)`-manifold
  (`GX.IsCuspedHyperbolic.singularStructure`) with `sing(M) = S` (`…sing_eq`, the parabolic
  holonomy `…notMem_support_of_cusp`); `M` tamely singular; every developing map
  `\widetilde M → X` injective (`GX.injective_of_isCuspDev`); the singular points of
  `\widetilde M` are the points over `S`, each with arbitrarily small open neighbourhoods `U`
  homeomorphic to `{r < r₀} ⊆ 𝔻_∞` (`GX.exists_homeomorph_basicSet`) with `D(U)` a horodisc
  centred at `D(x) ∈ ∂ℍ` (`GX.image_basicSet`), not open in `X` (`GX.not_isOpen_horoSet`).
  The infrastructure: `GX.IsCompleteHyperbolic.exists_homeomorph` (the developing map of a
  complete hyperbolic surface is a homeomorphism onto `ℍ`), horodiscs `GX.horodisc` and their
  images `GX.HypIsom.mob_mem_horodisc_iff`, cusps `GX.CuspChart`, `GX.CuspChart.IsHyperbolicCusp`,
  their lifts `GX.exists_end_lift`.

> Take $X$ the closed unit disc in $\RR^2$ and identify the open disc with the pointcaré disc
> $\H$. Take $G$ the group of isometries of the pointcaré disc. Note that $G$ acts by
> homeomorphisms on $X$. Consider $M$ a genus $g$ surface and $S\subset M$ a finite subset such
> that $2g-2+s>0$. Endow $M\setminus S$ with a finite volume complete hyperbolic metric. On the
> one hand, $M$ is a tamely singular $(G,X)$-manifold with injective developing map
> $\widetilde M \xrightarrow{\D} X$. On the other hand, an open neighborhood $\U$ of a singular
> point $x$ of $\widetilde M$ is homeomorphic to a domain $\{r<r_0\}$ in the ``infinite angle
> disc'' $\DD_\infty$ introduced in Example \ref{ex:quotient_base}. We may choose $\U$ so that
> $\D(U)$ is a horodisc centered at $\D(x)$. Such a domain is not open for the topology of $X$.
> (l.1877)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `X` the closed unit disc, the open disc the Poincaré disc | ✓ carried: `ClosedDisc`, `PoincareDisc`, `hypDist` (`cosh d = 1 + 2|z-w|²/((1-|z|²)(1-|w|²))`, `GX.cosh_hypDist`) |
| `G` the isometry group of the Poincaré disc | ✓ carried: `HypIsom`, all `hypDist`-isometries; each is a Möbius map `mobF` (proved) |
| `M` a genus `g` surface | ⚠ weakened: `M` Hausdorff, locally path-connected, first countable, connected (what is used); the genus is not used |
| `S` finite, `2g-2+s>0` | ✓ `S` finite carried; ⚠ weakened: `2g-2+s>0` not used (it is the existence condition) |
| `M ∖ S` a hyperbolic metric | ✓ read metrically (DEC-81, SCOPE (b)): a `(G, ℍ)`-structure with a metric `m`, `IsHyperbolicMetric` (length metric, topology, locally `d_ℍ` in the charts); unique; the Riemannian tensor is not formalized |
| complete | ✓ carried (DEC-81): `m` complete as a metric space (`IsCuspedHyperbolicMetric.complete`), equivalent to Thurston–Goldman completeness (`IsHyperbolicMetric.completeSpace_iff`) |
| finite volume | ⚠ read (SCOPE (b)): a cusp at every point of `S` (`CuspChart`, `IsHyperbolicCusp`), whose area is proved finite (`CuspChart.cusp_finite_area`); finite volume ⇒ cusps (thick–thin) not built |
| singular manifolds second countable | ⚠ weakened: not used |

## SCOPE (disclosed)

* **(a)** "Tamely singular": `GX.IsTame` for the structure `IsCuspedHyperbolic.singularStructure`,
  the maximal a.e. atlas generated by the charts of `M ∖ S` read in `ℍ ⊆ X` (`cuspedAtlas`).
  `\widetilde M` is
  `MaxBranchedCover (sing M) y₀` with the structure `p^*B`; "singular point" is a point outside
  the support of `p^*B`, proved to be exactly the points over `sing(M) = S`. "With injective
  developing map" is proved for **every** developing map. "An open neighbourhood `U` … is
  homeomorphic to `{r < r₀}`" is read: such neighbourhoods exist in every neighbourhood of `x`
  (`x` ↦ apex); "`D(U)` is a horodisc centred at `D(x)`" is read: `D(U)` is a horodisc together
  with its centre `D(x) ∈ ∂ℍ` (`x ∈ U`).
* **(b)** "A finite volume complete hyperbolic metric" on `M ∖ S` is read **metrically**
  (DEC-81): a `(G, ℍ)`-structure carrying a metric `m` which gives its topology, is a length
  metric (paths of length — variation — arbitrarily close to the distance) and is locally the
  Poincaré metric read in the charts (`GX.IsHyperbolicMetric`; this is what the distance of a
  Riemannian metric of curvature `-1` is; the tensor itself is not formalized, no Riemannian
  surfaces at this pin). Such a metric is unique (`GX.IsHyperbolicMetric.unique`: lengths are
  local, `GX.eVariationOn_eq_of_locally`). "Complete" is metric completeness of `m`; it is
  proved equivalent to Thurston's and Goldman's completeness (developing maps are covering
  maps): ⇐ by the quotient metric of `ℍ` (`GX.IsHypQuotient`), ⇒ by Hopf–Rinow (geodesic arcs
  lift through the developing map, `GX.IsDevLocalIsometry.exists_lift_hypGeod`, by completeness;
  the lifts depend continuously on the end, mathlib's `IsLocalHomeomorph.continuous_lift`).
  "Finite volume" is read as a cusp at each `s ∈ S`: a neighbourhood `V ≅ ball(0, e^{-2πc})`,
  `s ↦ 0`, on which `w ↦ φ⁻¹(e^{2πiw})`, `Im w > c`, is a `(G, ℍ)`-morphism; the cusp is proved
  to have finite area — `W_c ∖ {s}` is the injective, locally isometric image of the strip
  `{c < Im w, 0 ≤ Re w < 1}`, of area `1/c` for the invariant area `dx dy / y²`
  (`GX.CuspChart.cusp_finite_area`). Not built: the thick–thin decomposition (finite volume ⇒
  each end is a cusp), and the area measure of the whole surface. From this the file builds:
  the developing map onto `ℍ`, the lifts of the cusps to horodiscs, the Fox ends over `S`, the
  extension of the developing map to the parabolic fixed points.
* **(c)** No inhabitant with a cusp is constructed (e.g. `Γ(2)\ℍ`, the thrice-punctured sphere);
  the hypotheses are those of the standard description of cusped hyperbolic surfaces.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.SingularII.Tame`, `GX.SingularII.Developing`, `GX.Structure.Developing`,
`GX.Branched.Universality`, `GX.Spread.Completion`, `GX.Singular.Quotient` (`𝔻_∞`).
-/
noncomputable section
open Set Filter Topology Function Complex
open scoped ComplexConjugate UpperHalfPlane Real
namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ### Algebra of the Poincaré disc -/

/-- The *hyperbolic ratio* `2|z - w|² / ((1 - |z|²)(1 - |w|²))` of the Poincaré disc:
`cosh d(z, w) = 1 + hypRatio z w` (`GX.cosh_hypDist`). -/
def hypRatio (z w : ℂ) : ℝ := 2 * normSq (z - w) / ((1 - normSq z) * (1 - normSq w))

/-- The reflection `σ_b`: complex conjugation if `b`, the identity otherwise. -/
def sigmaB (b : Bool) (z : ℂ) : ℂ := if b then conj z else z

@[simp] theorem normSq_sigmaB (b : Bool) (z : ℂ) : normSq (sigmaB b z) = normSq z := by
  cases b <;> simp [sigmaB]

theorem sigmaB_sub (b : Bool) (z w : ℂ) : sigmaB b z - sigmaB b w = sigmaB b (z - w) := by
  cases b <;> simp [sigmaB]

theorem continuous_sigmaB (b : Bool) : Continuous (sigmaB b) := by
  cases b
  · exact continuous_id
  · exact Complex.continuous_conj

/-- The disc automorphism `z ↦ (u σ_b(z) + a) / (1 + ā u σ_b(z))` (`|u| = 1`, `|a| < 1`):
every isometry of the Poincaré disc is one of them (`GX.HypIsom.exists_mobF`). -/
def mobF (u a : ℂ) (b : Bool) (z : ℂ) : ℂ :=
  (u * sigmaB b z + a) / (1 + conj a * u * sigmaB b z)

/-- The denominator of `mobF`. -/
def mobDen (u a : ℂ) (b : Bool) (z : ℂ) : ℂ := 1 + conj a * u * sigmaB b z

theorem normSq_den_sub_num (u a z : ℂ) (hu : normSq u = 1) :
    normSq (1 + conj a * u * z) - normSq (u * z + a) = (1 - normSq a) * (1 - normSq z) := by
  have hu' : u.re * u.re + u.im * u.im = 1 := by rw [normSq_apply] at hu; exact hu
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  linear_combination ((a.re * a.re + a.im * a.im) * (z.re * z.re + z.im * z.im) -
    (z.re * z.re + z.im * z.im)) * hu'

theorem num_sub_num (u a z w : ℂ) :
    (u * z + a) * (1 + conj a * u * w) - (u * w + a) * (1 + conj a * u * z) =
      u * (1 - normSq a) * (z - w) := by
  have : conj a * a = (normSq a : ℂ) := by rw [mul_comm]; exact mul_conj a
  linear_combination (u * (w - z)) * this

section Mob

variable {u a : ℂ} (b : Bool)

theorem normSq_mul_le_lt (hu : normSq u = 1) (ha : normSq a < 1) {z : ℂ} (hz : normSq z ≤ 1) :
    normSq (conj a * u * sigmaB b z) < 1 := by
  rw [map_mul, map_mul, normSq_conj, hu, mul_one, normSq_sigmaB]
  calc normSq a * normSq z ≤ normSq a * 1 :=
        mul_le_mul_of_nonneg_left hz (normSq_nonneg a)
    _ < 1 := by rw [mul_one]; exact ha

theorem mobDen_ne_zero (hu : normSq u = 1) (ha : normSq a < 1) {z : ℂ} (hz : normSq z ≤ 1) :
    mobDen u a b z ≠ 0 := by
  intro h
  have h' : conj a * u * sigmaB b z = -1 := by
    rw [mobDen] at h; linear_combination h
  have := normSq_mul_le_lt b hu ha hz
  rw [h'] at this
  simp at this

theorem normSq_mobDen_pos (hu : normSq u = 1) (ha : normSq a < 1) {z : ℂ} (hz : normSq z ≤ 1) :
    0 < normSq (mobDen u a b z) :=
  normSq_pos.2 (mobDen_ne_zero b hu ha hz)

/-- `1 - |f z|² = (1 - |a|²)(1 - |z|²)/|den z|²`. -/
theorem one_sub_normSq_mobF (hu : normSq u = 1) (ha : normSq a < 1) {z : ℂ}
    (hz : normSq z ≤ 1) :
    1 - normSq (mobF u a b z) = (1 - normSq a) * (1 - normSq z) / normSq (mobDen u a b z) := by
  have hd := normSq_mobDen_pos b hu ha hz
  have key := normSq_den_sub_num u a (sigmaB b z) hu
  rw [normSq_sigmaB] at key
  simp only [mobDen] at hd ⊢
  rw [mobF, map_div₀, eq_div_iff hd.ne', sub_mul, div_mul_cancel₀ _ hd.ne']
  linarith

/-- `f z - f w = u (1 - |a|²)(σz - σw)/(den z · den w)`. -/
theorem mobF_sub_mobF (hu : normSq u = 1) (ha : normSq a < 1) {z w : ℂ} (hz : normSq z ≤ 1)
    (hw : normSq w ≤ 1) :
    mobF u a b z - mobF u a b w =
      u * (1 - normSq a) * (sigmaB b z - sigmaB b w) / (mobDen u a b z * mobDen u a b w) := by
  have hdz := mobDen_ne_zero b hu ha hz
  have hdw := mobDen_ne_zero b hu ha hw
  simp only [mobDen] at hdz hdw ⊢
  rw [mobF, mobF, div_sub_div _ _ hdz hdw, ← num_sub_num]
  congr 1; ring

theorem normSq_mobF_le (hu : normSq u = 1) (ha : normSq a < 1) {z : ℂ} (hz : normSq z ≤ 1) :
    normSq (mobF u a b z) ≤ 1 := by
  have h := one_sub_normSq_mobF b hu ha hz
  have hd := normSq_mobDen_pos b hu ha hz
  have : 0 ≤ (1 - normSq a) * (1 - normSq z) / normSq (mobDen u a b z) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hd.le
  linarith

theorem normSq_mobF_lt (hu : normSq u = 1) (ha : normSq a < 1) {z : ℂ} (hz : normSq z < 1) :
    normSq (mobF u a b z) < 1 := by
  have h := one_sub_normSq_mobF b hu ha hz.le
  have hd := normSq_mobDen_pos b hu ha hz.le
  have : 0 < (1 - normSq a) * (1 - normSq z) / normSq (mobDen u a b z) :=
    div_pos (mul_pos (by linarith) (by linarith)) hd
  linarith

theorem normSq_mobF_eq_one (hu : normSq u = 1) (ha : normSq a < 1) {z : ℂ}
    (hz : normSq z = 1) : normSq (mobF u a b z) = 1 := by
  have h := one_sub_normSq_mobF b hu ha hz.le
  rw [hz, sub_self, mul_zero, zero_div] at h
  linarith

/-- The Möbius maps preserve the hyperbolic ratio. -/
theorem hypRatio_mobF (hu : normSq u = 1) (ha : normSq a < 1) {z w : ℂ} (hz : normSq z < 1)
    (hw : normSq w < 1) : hypRatio (mobF u a b z) (mobF u a b w) = hypRatio z w := by
  have hz' := one_sub_normSq_mobF b hu ha hz.le
  have hw' := one_sub_normSq_mobF b hu ha hw.le
  have hdz := normSq_mobDen_pos b hu ha hz.le
  have hdw := normSq_mobDen_pos b hu ha hw.le
  have hsub := mobF_sub_mobF b hu ha hz.le hw.le
  have ha' : 0 < 1 - normSq a := by linarith
  have hz0 : 0 < 1 - normSq z := by linarith
  have hw0 : 0 < 1 - normSq w := by linarith
  unfold hypRatio
  rw [hz', hw', hsub, map_div₀, map_mul, map_mul, map_mul, sigmaB_sub, normSq_sigmaB, hu]
  have h1 : normSq ((1 : ℂ) - (normSq a : ℂ)) = (1 - normSq a) ^ 2 := by
    rw [← ofReal_one, ← ofReal_sub, normSq_ofReal]; ring
  rw [h1]
  field_simp

end Mob

/-- The inverse of `z ↦ (z - a)/(1 - ā z)` is `y ↦ (y + a)/(1 + ā y)`. -/
theorem mobF_one_mobF_neg (ha : normSq a < 1) {y : ℂ} (hy : normSq y ≤ 1) :
    mobF 1 a false (mobF 1 (-a) false y) = y := by
  have hu : normSq (1 : ℂ) = 1 := map_one _
  have ha' : normSq (-a) < 1 := by rwa [normSq_neg]
  have hd := mobDen_ne_zero false hu ha' hy
  simp only [mobF, mobDen, sigmaB, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
    map_neg] at hd ⊢
  have hna : (1 : ℂ) - conj a * a ≠ 0 := by
    rw [mul_comm, mul_conj]
    intro h
    have : (normSq a : ℂ) = 1 := by linear_combination -h
    norm_cast at this
    linarith
  have hd' : 1 + -conj a * y ≠ 0 := hd
  rw [div_add' _ _ _ hd', mul_div_assoc', one_add_div hd', div_div_div_cancel_right₀ hd']
  rw [div_eq_iff]
  · ring
  · intro h
    apply hna
    linear_combination h


/-! ### Isometries fixing the centre -/

theorem normSq_lt_one_iff {z : ℂ} : normSq z < 1 ↔ z ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, normSq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg z]
  · intro h; nlinarith [norm_nonneg z]

theorem normSq_le_one_iff {z : ℂ} : normSq z ≤ 1 ↔ z ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall_zero_iff, normSq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg z]
  · intro h; nlinarith [norm_nonneg z]

/-- **Isometries of the Poincaré disc fixing `0` are rotations or reflections**: a map of the
open disc into itself preserving the hyperbolic ratio and fixing `0` is `z ↦ u z` or
`z ↦ u z̄`, `|u| = 1`. -/
theorem eq_mul_sigmaB_of_hypRatio {k : ℂ → ℂ} (hk : ∀ z, normSq z < 1 → normSq (k z) < 1)
    (hδ : ∀ z w, normSq z < 1 → normSq w < 1 → hypRatio (k z) (k w) = hypRatio z w)
    (h0 : k 0 = 0) :
    ∃ u : ℂ, ∃ b : Bool, normSq u = 1 ∧ ∀ z, normSq z < 1 → k z = u * sigmaB b z := by
  -- the norms are preserved
  have hn : ∀ z, normSq z < 1 → normSq (k z) = normSq z := by
    intro z hz
    have h := hδ 0 z (by simp) hz
    have hkz := hk z hz
    rw [h0] at h
    simp only [hypRatio, zero_sub, normSq_neg, map_zero, sub_zero, one_mul] at h
    rw [div_eq_div_iff (by linarith) (by linarith)] at h
    nlinarith
  -- the Euclidean distances are preserved
  have hd : ∀ z w, normSq z < 1 → normSq w < 1 → normSq (k z - k w) = normSq (z - w) := by
    intro z w hz hw
    have h := hδ z w hz hw
    simp only [hypRatio] at h
    rw [hn z hz, hn w hw] at h
    have hpos : 0 < (1 - normSq z) * (1 - normSq w) := mul_pos (by linarith) (by linarith)
    rw [div_left_inj' hpos.ne'] at h
    linarith
  -- the real inner products are preserved
  have hre : ∀ z w, normSq z < 1 → normSq w < 1 → (k z * conj (k w)).re = (z * conj w).re := by
    intro z w hz hw
    have h := hd z w hz hw
    rw [normSq_sub, normSq_sub, hn z hz, hn w hw] at h
    linarith
  have hh : normSq ((1 : ℂ) / 2) < 1 := by
    rw [normSq_apply]; norm_num
  have hi : normSq (I / 2) < 1 := by
    rw [normSq_apply]; norm_num
  set p := k (1 / 2) with hp
  set q := k (I / 2) with hq
  have hpn : p.re * p.re + p.im * p.im = 1 / 4 := by
    have := hn _ hh; rw [← hp, normSq_apply, normSq_apply] at this; rw [this]; norm_num
  have hqn : q.re * q.re + q.im * q.im = 1 / 4 := by
    have := hn _ hi; rw [← hq, normSq_apply, normSq_apply] at this; rw [this]; norm_num
  have hpq : p.re * q.re + p.im * q.im = 0 := by
    have := hre _ _ hh hi
    rw [← hp, ← hq] at this
    simp only [mul_re, conj_re, conj_im, div_re, div_im, one_re, one_im, I_re, I_im] at this
    norm_num at this
    linarith
  -- `q = ± i p`
  have hsign : (q.re = -p.im ∧ q.im = p.re) ∨ (q.re = p.im ∧ q.im = -p.re) := by
    have h1 : (q.re + p.im) * (q.re - p.im) = 0 ∨ True := Or.inr trivial
    clear h1
    by_cases hp1 : p.re = 0
    · have hp2 : p.im * p.im = 1 / 4 := by rw [hp1] at hpn; linarith
      have hq2 : q.im = 0 := by
        rw [hp1, zero_mul, zero_add] at hpq
        rcases mul_eq_zero.1 hpq with h | h
        · rw [h] at hp2; norm_num at hp2
        · exact h
      have hq1 : q.re * q.re = 1 / 4 := by rw [hq2] at hqn; linarith
      have : (q.re + p.im) * (q.re - p.im) = 0 := by ring_nf; nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; exact ⟨by linarith, by rw [hq2, hp1]⟩
      · right; exact ⟨by linarith, by rw [hq2, hp1]; ring⟩
    · -- `q.re = - q.im p.im / p.re`
      have hq1 : q.re = -(q.im * p.im) / p.re := by
        field_simp; linarith
      have hq2 : q.im * q.im = p.re * p.re := by
        rw [hq1] at hqn
        field_simp at hqn
        nlinarith
      have : (q.im - p.re) * (q.im + p.re) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.1 this with h | h
      · left
        have hqi : q.im = p.re := by linarith
        refine ⟨?_, hqi⟩
        rw [hq1, hqi]; field_simp
      · right
        have hqi : q.im = -p.re := by linarith
        refine ⟨?_, hqi⟩
        rw [hq1, hqi]; field_simp
  rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨2 * p, false, ?_, fun z hz => ?_⟩
    · rw [normSq_apply]; simp only [mul_re, mul_im, re_ofNat, im_ofNat]; nlinarith
    · have e1 := hre z _ hz hh
      have e2 := hre z _ hz hi
      rw [← hp] at e1; rw [← hq] at e2
      simp only [mul_re, conj_re, conj_im, div_re, div_im, one_re, one_im, I_re, I_im,
        h1, h2] at e1 e2
      norm_num at e1 e2
      apply Complex.ext
      · simp only [sigmaB, Bool.false_eq_true, ↓reduceIte, mul_re, mul_im, re_ofNat, im_ofNat]
        linear_combination (4 * p.re) * e1 - (4 * p.im) * e2 - 4 * (k z).re * hpn
      · simp only [sigmaB, Bool.false_eq_true, ↓reduceIte, mul_re, mul_im, re_ofNat, im_ofNat]
        linear_combination (4 * p.im) * e1 + (4 * p.re) * e2 - 4 * (k z).im * hpn
  · refine ⟨2 * p, true, ?_, fun z hz => ?_⟩
    · rw [normSq_apply]; simp only [mul_re, mul_im, re_ofNat, im_ofNat]; nlinarith
    · have e1 := hre z _ hz hh
      have e2 := hre z _ hz hi
      rw [← hp] at e1; rw [← hq] at e2
      simp only [mul_re, conj_re, conj_im, div_re, div_im, one_re, one_im, I_re, I_im,
        h1, h2] at e1 e2
      norm_num at e1 e2
      apply Complex.ext
      · simp only [sigmaB, ↓reduceIte, mul_re, mul_im, re_ofNat, im_ofNat, conj_re, conj_im]
        linear_combination (4 * p.re) * e1 + (4 * p.im) * e2 - 4 * (k z).re * hpn
      · simp only [sigmaB, ↓reduceIte, mul_re, mul_im, re_ofNat, im_ofNat, conj_re, conj_im]
        linear_combination (4 * p.im) * e1 - (4 * p.re) * e2 - 4 * (k z).im * hpn


/-- A map of the disc into itself preserving the hyperbolic ratio is a Möbius map `mobF u a b`. -/
theorem exists_mobF_of_hypRatio {f : ℂ → ℂ} (hf : ∀ z, normSq z < 1 → normSq (f z) < 1)
    (hδ : ∀ z w, normSq z < 1 → normSq w < 1 → hypRatio (f z) (f w) = hypRatio z w) :
    ∃ u a : ℂ, ∃ b : Bool, normSq u = 1 ∧ normSq a < 1 ∧
      ∀ z, normSq z < 1 → f z = mobF u a b z := by
  set a := f 0 with ha_def
  have ha : normSq a < 1 := hf 0 (by simp)
  have hu1 : normSq (1 : ℂ) = 1 := map_one _
  have ha' : normSq (-a) < 1 := by rwa [normSq_neg]
  set k : ℂ → ℂ := fun z => mobF 1 (-a) false (f z) with hk_def
  have hk : ∀ z, normSq z < 1 → normSq (k z) < 1 := fun z hz =>
    normSq_mobF_lt false hu1 ha' (hf z hz)
  have hkδ : ∀ z w, normSq z < 1 → normSq w < 1 → hypRatio (k z) (k w) = hypRatio z w :=
    fun z w hz hw => by
      rw [hk_def, hypRatio_mobF false hu1 ha' (hf z hz) (hf w hw), hδ z w hz hw]
  have hk0 : k 0 = 0 := by
    simp only [hk_def, mobF, sigmaB, Bool.false_eq_true, ↓reduceIte, one_mul, ← ha_def]
    simp
  obtain ⟨u, b, hu, hkz⟩ := eq_mul_sigmaB_of_hypRatio hk hkδ hk0
  refine ⟨u, a, b, hu, ha, fun z hz => ?_⟩
  have h1 := mobF_one_mobF_neg ha (hf z hz).le
  rw [← h1]
  change mobF 1 a false (k z) = _
  rw [hkz z hz]
  simp only [mobF, sigmaB, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
  ring_nf

/-! ### The Poincaré disc and its isometry group -/

/-- **The Poincaré disc** `ℍ` of `ex:take_closed_unit_disc`: the open unit disc. -/
abbrev PoincareDisc : Type := Metric.ball (0 : ℂ) 1

/-- **The model space `X` of `ex:take_closed_unit_disc`**: the closed unit disc (of `ℂ = ℝ²`). -/
abbrev ClosedDisc : Type := Metric.closedBall (0 : ℂ) 1

theorem PoincareDisc.normSq_lt (z : PoincareDisc) : normSq (z : ℂ) < 1 :=
  normSq_lt_one_iff.2 z.2

theorem ClosedDisc.normSq_le (z : ClosedDisc) : normSq (z : ℂ) ≤ 1 :=
  normSq_le_one_iff.2 z.2

/-- The inverse Cayley transform `z ↦ i(1 + z)/(1 - z)`, from the disc to the upper half-plane. -/
def cayInv (z : ℂ) : ℂ := I * (1 + z) / (1 - z)

theorem cayInv_im (z : ℂ) : (cayInv z).im = (1 - normSq z) / normSq (1 - z) := by
  rw [cayInv, div_im]
  simp only [mul_re, mul_im, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im,
    normSq_apply]
  ring

theorem one_sub_ne_zero_of_normSq_lt {z : ℂ} (hz : normSq z < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, map_one] at hz
  exact lt_irrefl _ hz

theorem cayInv_im_pos {z : ℂ} (hz : normSq z < 1) : 0 < (cayInv z).im := by
  rw [cayInv_im]
  exact div_pos (by linarith) (normSq_pos.2 (one_sub_ne_zero_of_normSq_lt hz))

theorem cayInv_sub {z w : ℂ} (hz : 1 - z ≠ 0) (hw : 1 - w ≠ 0) :
    cayInv z - cayInv w = 2 * I * (z - w) / ((1 - z) * (1 - w)) := by
  rw [cayInv, cayInv, div_sub_div _ _ hz hw]
  congr 1; ring

/-- The disc to the upper half-plane. -/
def toUHP (z : PoincareDisc) : ℍ := ⟨cayInv z, cayInv_im_pos z.normSq_lt⟩

/-- **The Poincaré distance** of the disc: the distance of the upper half-plane `ℍ` (mathlib's
`UpperHalfPlane.dist`) transported by the Cayley transform. -/
def hypDist (z w : PoincareDisc) : ℝ := dist (toUHP z) (toUHP w)

/-- `cosh d(z, w) = 1 + 2|z - w|²/((1 - |z|²)(1 - |w|²))`. -/
theorem cosh_hypDist (z w : PoincareDisc) : Real.cosh (hypDist z w) = 1 + hypRatio z w := by
  have hz := z.normSq_lt
  have hw := w.normSq_lt
  have hz1 := one_sub_ne_zero_of_normSq_lt hz
  have hw1 := one_sub_ne_zero_of_normSq_lt hw
  rw [hypDist, UpperHalfPlane.cosh_dist]
  congr 1
  have h1 : dist ((toUHP z : ℍ) : ℂ) (toUHP w) ^ 2 = normSq (cayInv z - cayInv w) := by
    rw [dist_eq_norm, normSq_eq_norm_sq]; rfl
  rw [h1, cayInv_sub hz1 hw1]
  have him : ∀ y : PoincareDisc, (toUHP y).im = (1 - normSq (y : ℂ)) / normSq (1 - (y : ℂ)) :=
    fun y => cayInv_im y
  rw [him, him, hypRatio]
  have hn1 : 0 < normSq (1 - (z : ℂ)) := normSq_pos.2 hz1
  have hn2 : 0 < normSq (1 - (w : ℂ)) := normSq_pos.2 hw1
  have hz0 : 0 < 1 - normSq (z : ℂ) := by linarith
  have hw0 : 0 < 1 - normSq (w : ℂ) := by linarith
  rw [map_div₀, map_mul, map_mul, map_mul, normSq_I]
  have h2 : normSq (2 : ℂ) = 4 := by rw [normSq_apply]; norm_num
  rw [h2]
  field_simp
  ring

theorem hypRatio_nonneg {z w : ℂ} (hz : normSq z < 1) (hw : normSq w < 1) :
    0 ≤ hypRatio z w :=
  div_nonneg (mul_nonneg zero_le_two (normSq_nonneg _))
    (mul_nonneg (by linarith) (by linarith))

theorem hypDist_eq_iff {z w z' w' : PoincareDisc} :
    hypDist z w = hypDist z' w' ↔ hypRatio z w = hypRatio z' w' := by
  constructor
  · intro h
    have := cosh_hypDist z w
    rw [h, cosh_hypDist] at this
    linarith
  · intro h
    apply Real.cosh_injOn (mem_Ici.2 dist_nonneg) (mem_Ici.2 dist_nonneg)
    show Real.cosh (hypDist z w) = Real.cosh (hypDist z' w')
    rw [cosh_hypDist, cosh_hypDist, h]

/-- **The isometry group `G = Isom(ℍ)` of the Poincaré disc**, as a subgroup (`ex:take_closed_unit_disc`): the
permutations of the open disc preserving the Poincaré distance `GX.hypDist`. -/
def hypIsomSubgroup : Subgroup (Equiv.Perm PoincareDisc) where
  carrier := {f | ∀ z w, hypDist (f z) (f w) = hypDist z w}
  mul_mem' {f g} hf hg z w := by
    show hypDist (f (g z)) (f (g w)) = hypDist z w
    rw [hf, hg]
  one_mem' z w := rfl
  inv_mem' {f} hf z w := by
    have := hf (f⁻¹ z) (f⁻¹ w)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at this
    exact this.symm

/-- **`G = Isom(ℍ)`**, as a type: the isometries of the Poincaré disc. -/
abbrev HypIsom : Type := ↥hypIsomSubgroup


namespace HypIsom

/-- Every isometry of the Poincaré disc is a Möbius map `mobF u a b` (`|u| = 1`, `|a| < 1`;
`b` records whether it reverses the orientation). -/
theorem exists_mobF (g : HypIsom) : ∃ p : ℂ × ℂ × Bool, normSq p.1 = 1 ∧ normSq p.2.1 < 1 ∧
    ∀ z : PoincareDisc, (((g : Equiv.Perm PoincareDisc) z : PoincareDisc) : ℂ) =
      mobF p.1 p.2.1 p.2.2 z := by
  set f : ℂ → ℂ := fun z => if h : z ∈ Metric.ball (0 : ℂ) 1 then
    (((g : Equiv.Perm PoincareDisc) ⟨z, h⟩ : PoincareDisc) : ℂ) else 0 with hf
  have hf' : ∀ z : PoincareDisc, f z = (((g : Equiv.Perm PoincareDisc) z : PoincareDisc) : ℂ) :=
    fun z => by rw [hf]; simp only [dif_pos z.2]
  have h1 : ∀ z, normSq z < 1 → normSq (f z) < 1 := fun z hz => by
    have := hf' ⟨z, normSq_lt_one_iff.1 hz⟩
    simp only at this; rw [this]; exact PoincareDisc.normSq_lt _
  have h2 : ∀ z w, normSq z < 1 → normSq w < 1 → hypRatio (f z) (f w) = hypRatio z w :=
    fun z w hz hw => by
      have hz' := hf' ⟨z, normSq_lt_one_iff.1 hz⟩
      have hw' := hf' ⟨w, normSq_lt_one_iff.1 hw⟩
      simp only at hz' hw'
      rw [hz', hw']
      exact hypDist_eq_iff.1 (g.2 ⟨z, normSq_lt_one_iff.1 hz⟩ ⟨w, normSq_lt_one_iff.1 hw⟩)
  obtain ⟨u, a, b, hu, ha, h⟩ := exists_mobF_of_hypRatio h1 h2
  exact ⟨(u, a, b), hu, ha, fun z => by rw [← hf', h z z.normSq_lt]⟩

/-- The Möbius coefficients of an isometry (a choice). -/
def coef (g : HypIsom) : ℂ × ℂ × Bool := (exists_mobF g).choose

theorem normSq_coef_one (g : HypIsom) : normSq g.coef.1 = 1 := (exists_mobF g).choose_spec.1

theorem normSq_coef_two (g : HypIsom) : normSq g.coef.2.1 < 1 :=
  (exists_mobF g).choose_spec.2.1

theorem apply_eq_mobF (g : HypIsom) (z : PoincareDisc) :
    (((g : Equiv.Perm PoincareDisc) z : PoincareDisc) : ℂ) = mobF g.coef.1 g.coef.2.1 g.coef.2.2 z :=
  (exists_mobF g).choose_spec.2.2 z

/-- The Möbius formula of an isometry, as a map of `ℂ`. -/
def mob (g : HypIsom) : ℂ → ℂ := mobF g.coef.1 g.coef.2.1 g.coef.2.2

theorem continuousOn_mob (g : HypIsom) : ContinuousOn g.mob (Metric.closedBall 0 1) := by
  intro z hz
  have hd := mobDen_ne_zero g.coef.2.2 g.normSq_coef_one g.normSq_coef_two
    (normSq_le_one_iff.2 hz)
  refine ContinuousAt.continuousWithinAt ?_
  unfold mob mobF
  refine ContinuousAt.div ?_ ?_ hd
  · exact ((continuous_const.mul (continuous_sigmaB _)).add continuous_const).continuousAt
  · exact (continuous_const.add (continuous_const.mul (continuous_sigmaB _))).continuousAt

theorem mapsTo_mob_closedBall (g : HypIsom) :
    MapsTo g.mob (Metric.closedBall 0 1) (Metric.closedBall 0 1) := fun _ hz =>
  normSq_le_one_iff.1 (normSq_mobF_le _ g.normSq_coef_one g.normSq_coef_two
    (normSq_le_one_iff.2 hz))

theorem mapsTo_mob_ball (g : HypIsom) :
    MapsTo g.mob (Metric.ball 0 1) (Metric.ball 0 1) := fun _ hz =>
  normSq_lt_one_iff.1 (normSq_mobF_lt _ g.normSq_coef_one g.normSq_coef_two
    (normSq_lt_one_iff.2 hz))

theorem mapsTo_mob_sphere (g : HypIsom) :
    MapsTo g.mob (Metric.sphere 0 1) (Metric.sphere 0 1) := fun z hz => by
  have h1 : normSq z = 1 := by
    rw [mem_sphere_zero_iff_norm] at hz; rw [normSq_eq_norm_sq, hz]; norm_num
  have := normSq_mobF_eq_one g.coef.2.2 g.normSq_coef_one g.normSq_coef_two h1
  rw [mem_sphere_zero_iff_norm]
  unfold mob
  rw [normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (mobF g.coef.1 g.coef.2.1 g.coef.2.2 z)]

/-- **The action of `G = Isom(ℍ)` on the closed disc `X`**: the continuous extension of an
isometry (`ex:take_closed_unit_disc`, "`G` acts by homeomorphisms on `X`"). -/
def extFun (g : HypIsom) (x : ClosedDisc) : ClosedDisc := ⟨g.mob x, g.mapsTo_mob_closedBall x.2⟩

theorem continuous_extFun (g : HypIsom) : Continuous g.extFun :=
  (g.continuousOn_mob.comp_continuous continuous_subtype_val fun x => x.2).subtype_mk _

end HypIsom

/-- The open disc inside the closed disc. -/
def ClosedDisc.ofPD (z : PoincareDisc) : ClosedDisc := ⟨z, Metric.ball_subset_closedBall z.2⟩

@[simp] theorem ClosedDisc.coe_ofPD (z : PoincareDisc) : ((ClosedDisc.ofPD z : ClosedDisc) : ℂ) = z :=
  rfl

/-- The open disc is dense in the closed disc. -/
theorem ClosedDisc.dense_ball : Dense {x : ClosedDisc | (x : ℂ) ∈ Metric.ball (0 : ℂ) 1} := by
  rw [Subtype.dense_iff]
  intro x hx
  have : (Subtype.val '' {x : ClosedDisc | (x : ℂ) ∈ Metric.ball (0 : ℂ) 1}) =
      Metric.ball (0 : ℂ) 1 := by
    ext z
    refine ⟨fun ⟨y, hy, hyz⟩ => hyz ▸ hy, fun hz => ⟨⟨z, Metric.ball_subset_closedBall hz⟩, hz, rfl⟩⟩
  rw [this, closure_ball _ one_ne_zero]
  exact hx

theorem ClosedDisc.eq_of_eqOn_ball {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f f' : ClosedDisc → Y} (hf : Continuous f) (hf' : Continuous f')
    (h : ∀ z : PoincareDisc, f (ClosedDisc.ofPD z) = f' (ClosedDisc.ofPD z)) : f = f' :=
  Continuous.ext_on ClosedDisc.dense_ball hf hf' fun y hy => h ⟨y, hy⟩

namespace HypIsom

theorem extFun_ofPD (g : HypIsom) (z : PoincareDisc) :
    g.extFun (ClosedDisc.ofPD z) = ClosedDisc.ofPD ((g : Equiv.Perm PoincareDisc) z) := by
  apply Subtype.ext
  show g.mob z = _
  rw [mob, ← apply_eq_mobF]
  rfl

end HypIsom

instance : MulAction HypIsom ClosedDisc where
  smul g x := g.extFun x
  one_smul x := by
    have : HypIsom.extFun 1 = id := ClosedDisc.eq_of_eqOn_ball (HypIsom.continuous_extFun 1)
      continuous_id fun z => by rw [HypIsom.extFun_ofPD]; rfl
    exact congrFun this x
  mul_smul g h x := by
    have : HypIsom.extFun (g * h) = g.extFun ∘ h.extFun :=
      ClosedDisc.eq_of_eqOn_ball (HypIsom.continuous_extFun _)
        (g.continuous_extFun.comp h.continuous_extFun) fun z => by
          rw [comp_apply, HypIsom.extFun_ofPD, HypIsom.extFun_ofPD, HypIsom.extFun_ofPD]; rfl
    exact congrFun this x

theorem HypIsom.smul_closedDisc (g : HypIsom) (x : ClosedDisc) : g • x = g.extFun x := rfl

theorem HypIsom.coe_smul_closedDisc (g : HypIsom) (x : ClosedDisc) :
    ((g • x : ClosedDisc) : ℂ) = g.mob x := rfl

theorem HypIsom.smul_ofPD (g : HypIsom) (z : PoincareDisc) :
    g • ClosedDisc.ofPD z = ClosedDisc.ofPD (g • z) := g.extFun_ofPD z

instance : ContinuousConstSMul HypIsom ClosedDisc := ⟨fun g => g.continuous_extFun⟩

theorem HypIsom.coe_smul_poincareDisc (g : HypIsom) (z : PoincareDisc) :
    ((g • z : PoincareDisc) : ℂ) = g.mob z := by
  rw [HypIsom.mob, ← HypIsom.apply_eq_mobF]; rfl

instance : ContinuousConstSMul HypIsom PoincareDisc := ⟨fun g => by
  have : (fun z : PoincareDisc => g • z) =
      fun z : PoincareDisc => (⟨g.mob z, g.mapsTo_mob_ball z.prop⟩ : PoincareDisc) :=
    funext fun z =>
    Subtype.ext (g.coe_smul_poincareDisc z)
  rw [this]
  exact (g.continuousOn_mob.comp_continuous continuous_subtype_val
    fun x => Metric.ball_subset_closedBall x.prop).subtype_mk _⟩


instance : Nonempty PoincareDisc := ⟨⟨0, Metric.mem_ball_self one_pos⟩⟩

instance : Nonempty ClosedDisc := ⟨⟨0, Metric.mem_closedBall_self zero_le_one⟩⟩

theorem mobF_one_zero (a : ℂ) : mobF 1 a false 0 = a := by
  simp [mobF, sigmaB]

theorem mobF_one_neg_self (a : ℂ) : mobF 1 (-a) false a = 0 := by
  simp [mobF, sigmaB]

/-- **Rigidity**: an isometry of the Poincaré disc fixing a non-empty open set is the identity. -/
theorem HypIsom.eq_one_of_fix {k : HypIsom} {U : Set PoincareDisc} (hU : IsOpen U)
    (hne : U.Nonempty) (hfix : ∀ z ∈ U, k • z = z) : k = 1 := by
  obtain ⟨p, hp⟩ := hne
  set P : ℂ := p.1 with hPdef
  have hP : normSq P < 1 := p.normSq_lt
  have hu1 : normSq (1 : ℂ) = 1 := map_one _
  have hP' : normSq (-P) < 1 := by rwa [normSq_neg]
  have hku := k.normSq_coef_one
  have hka := k.normSq_coef_two
  have hkp : k.mob P = P := by
    rw [← k.coe_smul_poincareDisc, hfix p hp]
  set q : ℂ → ℂ := fun y => mobF 1 (-P) false (k.mob (mobF 1 P false y)) with hq
  have hqb : ∀ y, normSq y < 1 → normSq (q y) < 1 := fun y hy =>
    normSq_mobF_lt _ hu1 hP' (normSq_mobF_lt _ hku hka (normSq_mobF_lt _ hu1 hP hy))
  have hqδ : ∀ y w, normSq y < 1 → normSq w < 1 → hypRatio (q y) (q w) = hypRatio y w :=
    fun y w hy hw => by
      have h1 := normSq_mobF_lt false hu1 hP hy
      have h2 := normSq_mobF_lt false hu1 hP hw
      rw [hq]
      simp only
      rw [hypRatio_mobF (z := k.mob (mobF 1 P false y)) (w := k.mob (mobF 1 P false w)) _ hu1 hP'
        (normSq_mobF_lt _ hku hka h1) (normSq_mobF_lt _ hku hka h2)]
      unfold mob
      rw [hypRatio_mobF _ hku hka h1 h2, hypRatio_mobF _ hu1 hP hy hw]
  have hq0 : q 0 = 0 := by
    simp only [hq, mobF_one_zero, hkp, mobF_one_neg_self]
  obtain ⟨u, b, hu, hqf⟩ := eq_mul_sigmaB_of_hypRatio hqb hqδ hq0
  -- `q` fixes a neighbourhood of `0`
  obtain ⟨O, hO, hUO⟩ := isOpen_induced_iff.1 hU
  have hPO : P ∈ O := by
    have : p ∈ Subtype.val ⁻¹' O := by rw [hUO]; exact hp
    exact this
  have hcont : ContinuousAt (mobF 1 P false) 0 := by
    have hd := mobDen_ne_zero false hu1 hP (z := 0) (by simp)
    unfold mobF
    refine ContinuousAt.div ?_ ?_ hd
    · exact ((continuous_const.mul (continuous_sigmaB _)).add continuous_const).continuousAt
    · exact (continuous_const.add (continuous_const.mul (continuous_sigmaB _))).continuousAt
  have hev : ∀ᶠ y in 𝓝 (0 : ℂ), mobF 1 P false y ∈ O := by
    have := hcont.preimage_mem_nhds (hO.mem_nhds (by rw [mobF_one_zero]; exact hPO))
    exact this
  obtain ⟨ε, hε, hεO⟩ := Metric.eventually_nhds_iff.1 (hev.and (Metric.ball_mem_nhds 0 one_pos))
  have hfixq : ∀ y : ℂ, ‖y‖ < ε → ‖y‖ < 1 → q y = y := by
    intro y hyε hy1
    have hyb : normSq y < 1 := normSq_lt_one_iff.2 (mem_ball_zero_iff.2 hy1)
    have hmb := normSq_mobF_lt false hu1 hP hyb
    set z : PoincareDisc := ⟨mobF 1 P false y, normSq_lt_one_iff.1 hmb⟩
    have hzU : z ∈ U := by
      rw [← hUO]
      exact (hεO (by rw [dist_zero_right]; exact hyε)).1
    have hkz : k.mob (mobF 1 P false y) = mobF 1 P false y := by
      have := congrArg Subtype.val (hfix z hzU)
      rw [k.coe_smul_poincareDisc] at this
      exact this
    simp only [hq, hkz]
    have := mobF_one_mobF_neg (a := -P) hP' hyb.le
    rwa [neg_neg] at this
  have hε2 : ‖((ε / 2 : ℝ) : ℂ)‖ < ε := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
  set δ : ℝ := min (ε / 2) (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hn1 : ‖((δ : ℝ) : ℂ)‖ = δ := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
  have hn2 : ‖I * ((δ : ℝ) : ℂ)‖ = δ := by
    rw [norm_mul, norm_I, one_mul, hn1]
  have e1 := hfixq _ (by rw [hn1]; exact hδε) (by rw [hn1]; exact hδ1)
  have e2 := hfixq _ (by rw [hn2]; exact hδε) (by rw [hn2]; exact hδ1)
  rw [hqf _ (normSq_lt_one_iff.2 (mem_ball_zero_iff.2 (by rw [hn1]; exact hδ1)))] at e1
  rw [hqf _ (normSq_lt_one_iff.2 (mem_ball_zero_iff.2 (by rw [hn2]; exact hδ1)))] at e2
  have hδ0 : ((δ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hδpos.ne'
  have hu' : u = 1 := by
    have : sigmaB b ((δ : ℝ) : ℂ) = (δ : ℂ) := by cases b <;> simp [sigmaB, conj_ofReal]
    rw [this] at e1
    exact mul_right_cancel₀ hδ0 (by rw [one_mul]; exact e1)
  have hb : b = false := by
    cases b
    · rfl
    · exfalso
      simp only [sigmaB, ↓reduceIte, map_mul, conj_I, conj_ofReal, hu', one_mul] at e2
      have : (2 : ℂ) * (I * (δ : ℂ)) = 0 := by linear_combination -e2
      simp [hδ0] at this
  -- hence `q = id`, and `k = 1`
  have hqid : ∀ y, normSq y < 1 → q y = y := fun y hy => by
    rw [hqf y hy, hu', hb]; simp [sigmaB]
  apply Subtype.ext
  apply Equiv.ext
  intro z
  apply Subtype.ext
  have hZ := z.normSq_lt
  have hy : normSq (mobF 1 (-P) false z) < 1 := normSq_mobF_lt false hu1 hP' hZ
  have hinv : mobF 1 P false (mobF 1 (-P) false z) = z := mobF_one_mobF_neg hP hZ.le
  have e' : mobF 1 (-P) false (k.mob (mobF 1 P false (mobF 1 (-P) false z))) =
      mobF 1 (-P) false z := hqid _ hy
  rw [hinv] at e'
  have h2 : k.mob z = z := calc
    k.mob z = mobF 1 P false (mobF 1 (-P) false (k.mob z)) :=
        (mobF_one_mobF_neg (y := k.mob z) hP (normSq_mobF_le _ hku hka hZ.le)).symm
    _ = mobF 1 P false (mobF 1 (-P) false z) := by rw [e']
    _ = z := hinv
  exact (k.apply_eq_mobF z).trans h2

theorem HypIsom.eq_of_eqOn {g h : HypIsom} {U : Set PoincareDisc} (hU : IsOpen U)
    (hne : U.Nonempty) (heq : ∀ z ∈ U, g • z = h • z) : g = h := by
  have := HypIsom.eq_one_of_fix (k := h⁻¹ * g) hU hne fun z hz => by
    rw [mul_smul, heq z hz, inv_smul_smul]
  exact (inv_mul_eq_one.1 this).symm

/-- `(Isom(ℍ), ℍ)` is analytical. -/
instance : IsAnalyticAction HypIsom PoincareDisc :=
  IsAnalyticAction.of_eq_of_eqOn fun hU hne heq => HypIsom.eq_of_eqOn hU hne heq

theorem ClosedDisc.isOpenEmbedding_ofPD : Topology.IsOpenEmbedding ClosedDisc.ofPD := by
  have hemb : Topology.IsEmbedding ClosedDisc.ofPD :=
    Topology.IsEmbedding.inclusion Metric.ball_subset_closedBall
  refine ⟨hemb, ?_⟩
  have : range ClosedDisc.ofPD = {x : ClosedDisc | (x : ℂ) ∈ Metric.ball (0 : ℂ) 1} := by
    ext x
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

/-- **`(Isom(ℍ), X)` is analytical** (`X` the closed disc): the action on `X` is faithful and
rigid. -/
instance : IsAnalyticAction HypIsom ClosedDisc :=
  IsAnalyticAction.of_eq_of_eqOn fun {g h U} hU hne heq => by
    refine HypIsom.eq_of_eqOn (U := ClosedDisc.ofPD ⁻¹' U)
      (hU.preimage ClosedDisc.isOpenEmbedding_ofPD.continuous) ?_ fun z hz => ?_
    · obtain ⟨x, hx⟩ := (ClosedDisc.dense_ball.inter_open_nonempty U hU hne)
      exact ⟨⟨x, hx.2⟩, hx.1⟩
    · have := heq hz
      simp only [HypIsom.smul_ofPD] at this
      exact ClosedDisc.isOpenEmbedding_ofPD.injective this

/-! ### The topology of the closed disc -/

theorem ClosedDisc.image_ball (x : ClosedDisc) (ε : ℝ) :
    Subtype.val '' (Metric.ball x ε : Set ClosedDisc) =
      Metric.ball (x : ℂ) ε ∩ Metric.closedBall 0 1 := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨z, h2⟩, h1, rfl⟩

theorem ClosedDisc.convex_image_ball (x : ClosedDisc) (ε : ℝ) :
    Convex ℝ (Metric.ball (x : ℂ) ε ∩ Metric.closedBall 0 1) :=
  (convex_ball _ _).inter (convex_closedBall _ _)

theorem ClosedDisc.isPathConnected_ball (x : ClosedDisc) {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (Metric.ball x ε : Set ClosedDisc) := by
  rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, ClosedDisc.image_ball]
  exact (ClosedDisc.convex_image_ball x ε).isPathConnected ⟨x, Metric.mem_ball_self hε, x.2⟩

instance : LocPathConnectedSpace ClosedDisc :=
  LocPathConnectedSpace.of_bases (fun _ => Metric.nhds_basis_ball)
    fun x _ hε => ClosedDisc.isPathConnected_ball x hε

instance : ConnectedSpace ClosedDisc :=
  isConnected_iff_connectedSpace.1 ((convex_closedBall (0 : ℂ) 1).isConnected
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩)

/-- **The closed disc is locally unloopable** (`def:topological_space_locally_unloopable`, the
standing hypothesis of §2.5, l.1660): its small balls are convex, hence contractible. -/
theorem isLocallyUnloopable_closedDisc : IsLocallyUnloopable ClosedDisc := by
  refine ⟨inferInstance, fun x U hU => ?_⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨Metric.ball x ε, hεU, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  set C : Set ℂ := Metric.ball (x : ℂ) ε ∩ Metric.closedBall 0 1
  have hC : Convex ℝ C := ClosedDisc.convex_image_ball x ε
  haveI : ContractibleSpace C := hC.contractibleSpace ⟨x, Metric.mem_ball_self hε, x.2⟩
  haveI : SimplyConnectedSpace C := SimplyConnectedSpace.ofContractible C
  have hemb : Topology.IsEmbedding (fun v : (Metric.ball x ε : Set ClosedDisc) => ((v : ClosedDisc) : ℂ)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hrange : range (fun v : (Metric.ball x ε : Set ClosedDisc) => ((v : ClosedDisc) : ℂ)) = C := by
    show _ = Metric.ball (x : ℂ) ε ∩ Metric.closedBall 0 1
    rw [← ClosedDisc.image_ball]
    ext z
    constructor
    · rintro ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  exact (SemilocallySimplyConnected.of_simplyConnectedSpace C).of_homeomorph
    ((hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm)

/-- **`(Isom(ℍ), X)` is an analytical structure** (`RamcovGX.tex:341`), `X` the closed disc. -/
theorem analyticStructure_closedDisc : AnalyticStructure HypIsom ClosedDisc where
  connectedSpace := inferInstance
  locallyConnectedSpace := inferInstance
  t2Space := inferInstance
  continuousConstSMul := inferInstance
  isAnalyticAction := inferInstance


/-! ### Horodiscs -/

/-- **The horodisc** of the Poincaré disc centred at `ξ ∈ ∂ℍ` (`|ξ| = 1`) with parameter `t > 0`:
the super-level set `{z : (1 - |z|²)/|ξ - z|² > 1/t}` of the Poisson kernel at `ξ`, i.e. the
Euclidean disc of radius `t/(1 + t)` internally tangent to the unit circle at `ξ`
(`GX.horodisc_eq_ball`). -/
def horodisc (ξ : ℂ) (t : ℝ) : Set ℂ := {z | normSq (ξ - z) < t * (1 - normSq z)}

theorem norm_lt_iff_normSq_lt {x : ℂ} {r : ℝ} (hr : 0 ≤ r) : ‖x‖ < r ↔ normSq x < r ^ 2 := by
  rw [normSq_eq_norm_sq]
  constructor
  · intro h; exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
  · intro h; exact lt_of_pow_lt_pow_left₀ 2 hr h

theorem horodisc_eq_ball {ξ : ℂ} (hξ : ‖ξ‖ = 1) {t : ℝ} (ht : 0 < t) :
    horodisc ξ t = Metric.ball (((1 - t / (1 + t) : ℝ) : ℂ) * ξ) (t / (1 + t)) := by
  have hξ' : ξ.re * ξ.re + ξ.im * ξ.im = 1 := by
    rw [← normSq_apply, normSq_eq_norm_sq, hξ]; norm_num
  have h1t : 0 < 1 + t := by linarith
  ext z
  rw [Metric.mem_ball, dist_eq_norm, norm_lt_iff_normSq_lt (by positivity), horodisc,
    mem_setOf_eq]
  have key : (1 + t) * (normSq (z - ((1 - t / (1 + t) : ℝ) : ℂ) * ξ) - (t / (1 + t)) ^ 2) =
      normSq (ξ - z) - t * (1 - normSq z) := by
    simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul,
      sub_zero, add_zero]
    field_simp
    linear_combination (-t) * hξ'
  constructor
  · intro h
    have : (1 + t) * (normSq (z - ((1 - t / (1 + t) : ℝ) : ℂ) * ξ) - (t / (1 + t)) ^ 2) < 0 := by
      rw [key]; linarith
    have := (mul_neg_iff.1 this).resolve_right (fun h' => by linarith [h'.1])
    linarith [this.2]
  · intro h
    have : normSq (ξ - z) - t * (1 - normSq z) < 0 := by
      rw [← key]; exact mul_neg_of_pos_of_neg h1t (by linarith)
    linarith

theorem horodisc_subset_ball {ξ : ℂ} {t : ℝ} (ht : 0 < t) :
    horodisc ξ t ⊆ Metric.ball 0 1 := fun z hz => by
  rw [← normSq_lt_one_iff]
  have : 0 ≤ normSq (ξ - z) := normSq_nonneg _
  have h : 0 < t * (1 - normSq z) := lt_of_le_of_lt this hz
  have := (pos_iff_pos_of_mul_pos h).1 ht
  linarith

theorem horodisc_mono {ξ : ℂ} {t t' : ℝ} (ht : 0 < t) (htt' : t ≤ t') :
    horodisc ξ t ⊆ horodisc ξ t' := fun z hz => by
  have hz1 : normSq z < 1 := normSq_lt_one_iff.2 (horodisc_subset_ball ht hz)
  show normSq (ξ - z) < t' * (1 - normSq z)
  calc normSq (ξ - z) < t * (1 - normSq z) := hz
    _ ≤ t' * (1 - normSq z) := mul_le_mul_of_nonneg_right htt' (by linarith)

theorem center_mem_horodisc {ξ : ℂ} (hξ : ‖ξ‖ = 1) {t : ℝ} (ht : 0 < t) :
    ((1 - t / (1 + t) : ℝ) : ℂ) * ξ ∈ horodisc ξ t := by
  rw [horodisc_eq_ball hξ ht]
  exact Metric.mem_ball_self (by positivity)

theorem horodisc_nonempty {ξ : ℂ} (hξ : ‖ξ‖ = 1) {t : ℝ} (ht : 0 < t) : (horodisc ξ t).Nonempty :=
  ⟨_, center_mem_horodisc hξ ht⟩

/-- Two horodiscs with the same centre meet (they are nested). -/
theorem horodisc_inter_nonempty {ξ : ℂ} (hξ : ‖ξ‖ = 1) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') :
    (horodisc ξ t ∩ horodisc ξ t').Nonempty := by
  rcases le_total t t' with h | h
  · obtain ⟨z, hz⟩ := horodisc_nonempty hξ ht
    exact ⟨z, hz, horodisc_mono ht h hz⟩
  · obtain ⟨z, hz⟩ := horodisc_nonempty hξ ht'
    exact ⟨z, horodisc_mono ht' h hz, hz⟩

/-- Small horodiscs are close to their centre. -/
theorem horodisc_subset_ball_center {ξ : ℂ} (hξ : ‖ξ‖ = 1) {t : ℝ} (ht : 0 < t) :
    horodisc ξ t ⊆ Metric.ball ξ (2 * t) := by
  rw [horodisc_eq_ball hξ ht]
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  have h1t : 0 < 1 + t := by linarith
  have hc : dist (((1 - t / (1 + t) : ℝ) : ℂ) * ξ) ξ = t / (1 + t) := by
    rw [dist_eq_norm]
    have : ((1 - t / (1 + t) : ℝ) : ℂ) * ξ - ξ = ((- (t / (1 + t)) : ℝ) : ℂ) * ξ := by
      push_cast; ring
    rw [this, norm_mul, hξ, mul_one, norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)]
  calc dist z ξ ≤ dist z (((1 - t / (1 + t) : ℝ) : ℂ) * ξ) + dist (((1 - t / (1 + t) : ℝ) : ℂ) * ξ) ξ :=
        dist_triangle _ _ _
    _ < t / (1 + t) + t / (1 + t) := by rw [hc]; linarith
    _ ≤ 2 * t := by
        rw [← two_mul]
        exact mul_le_mul_of_nonneg_left (div_le_self ht.le (by linarith)) zero_le_two

/-- A point in the closure of every horodisc centred at `ξ` is `ξ`. -/
theorem eq_of_forall_mem_closure_horodisc {ξ z : ℂ} (hξ : ‖ξ‖ = 1)
    (h : ∀ t > 0, z ∈ closure (horodisc ξ t)) : z = ξ := by
  by_contra hne
  have hd : 0 < dist z ξ := dist_pos.2 hne
  have := h (dist z ξ / 4) (by positivity)
  have h2 := closure_mono (horodisc_subset_ball_center hξ (t := dist z ξ / 4) (by positivity)) this
  rw [closure_ball _ (by positivity : 2 * (dist z ξ / 4) ≠ 0), Metric.mem_closedBall] at h2
  linarith

/-! ### The Cayley transform -/

/-- **The Cayley transform** `w ↦ (w - i)/(w + i)` from the upper half-plane to the disc. -/
def cay (w : ℂ) : ℂ := (w - I) / (w + I)

theorem add_I_ne_zero {w : ℂ} (hw : 0 < w.im) : w + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem normSq_add_I_sub {w : ℂ} : normSq (w + I) - normSq (w - I) = 4 * w.im := by
  simp only [normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
  ring

theorem one_sub_cay {w : ℂ} (hw : 0 < w.im) : 1 - cay w = 2 * I / (w + I) := by
  rw [cay, one_sub_div (add_I_ne_zero hw)]
  congr 1; ring

theorem one_sub_normSq_cay {w : ℂ} (hw : 0 < w.im) :
    1 - normSq (cay w) = 4 * w.im / normSq (w + I) := by
  have hd := normSq_pos.2 (add_I_ne_zero hw)
  rw [cay, map_div₀, eq_div_iff hd.ne', sub_mul, div_mul_cancel₀ _ hd.ne', one_mul]
  linarith [normSq_add_I_sub (w := w)]

theorem normSq_cay_lt {w : ℂ} (hw : 0 < w.im) : normSq (cay w) < 1 := by
  have h := one_sub_normSq_cay hw
  have : 0 < 4 * w.im / normSq (w + I) := div_pos (by linarith) (normSq_pos.2 (add_I_ne_zero hw))
  linarith

theorem cay_mem_horodisc_iff {w : ℂ} (hw : 0 < w.im) {c : ℝ} (hc : 0 < c) :
    cay w ∈ horodisc 1 c⁻¹ ↔ c < w.im := by
  have hd := normSq_pos.2 (add_I_ne_zero hw)
  rw [horodisc, mem_setOf_eq, one_sub_normSq_cay hw, one_sub_cay hw, map_div₀, map_mul]
  have h2 : normSq (2 : ℂ) = 4 := by rw [normSq_apply]; norm_num
  rw [h2, normSq_I, mul_one, div_lt_iff₀ hd, mul_div_assoc', div_mul_cancel₀ _ hd.ne']
  rw [inv_mul_eq_div, lt_div_iff₀ hc]
  constructor <;> intro h <;> linarith

theorem cayInv_cay {w : ℂ} (hw : 0 < w.im) : cayInv (cay w) = w := by
  have hd := add_I_ne_zero hw
  rw [cayInv, one_sub_cay hw, cay]
  field_simp
  ring_nf

theorem cay_cayInv {z : ℂ} (hz : 1 - z ≠ 0) : cay (cayInv z) = z := by
  rw [cay, cayInv]
  have h2 : I * (1 + z) / (1 - z) + I = 2 * I / (1 - z) := by
    field_simp; ring
  have h3 : I * (1 + z) / (1 - z) - I = 2 * I * z / (1 - z) := by
    field_simp; ring
  rw [h2, h3, div_div_div_cancel_right₀ hz]
  field_simp

/-- The standard horodisc centred at `1` is the image of the horoball `{Im w > c}`. -/
theorem image_cay_horoball {c : ℝ} (hc : 0 < c) :
    cay '' {w : ℂ | c < w.im} = horodisc 1 c⁻¹ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (cay_mem_horodisc_iff (hc.trans hw) hc).2 hw
  · intro hz
    have hz1 : normSq z < 1 := normSq_lt_one_iff.2 (horodisc_subset_ball (inv_pos.2 hc) hz)
    have him := cayInv_im_pos hz1
    have hcz := cay_cayInv (one_sub_ne_zero_of_normSq_lt hz1)
    refine ⟨cayInv z, ?_, hcz⟩
    rw [← hcz] at hz
    exact (cay_mem_horodisc_iff him hc).1 hz

/-- The Cayley transform is periodic-free: `cay (w + 1) ≠ cay w`. -/
theorem cay_add_one_ne {w : ℂ} (hw : 0 < w.im) : cay (w + 1) ≠ cay w := by
  intro h
  have h1 : cayInv (cay (w + 1)) = cayInv (cay w) := by rw [h]
  rw [cayInv_cay hw, cayInv_cay (by simpa using hw)] at h1
  simp at h1


/-! ### Möbius maps and horodiscs -/

namespace HypIsom

/-- The horodisc scaling factor of an isometry at a boundary point. -/
def lam (g : HypIsom) (ξ : ℂ) : ℝ :=
  (1 - normSq g.coef.2.1) / normSq (mobDen g.coef.1 g.coef.2.1 g.coef.2.2 ξ)

theorem lam_pos (g : HypIsom) {ξ : ℂ} (hξ : normSq ξ ≤ 1) : 0 < g.lam ξ :=
  div_pos (by linarith [g.normSq_coef_two])
    (normSq_mobDen_pos _ g.normSq_coef_one g.normSq_coef_two hξ)

/-- An isometry maps the horodisc `B(ξ, t)` onto the horodisc `B(g ξ, t λ_g(ξ))`. -/
theorem mob_mem_horodisc_iff (g : HypIsom) {ξ : ℂ} (hξ : normSq ξ = 1) (t : ℝ) {z : ℂ}
    (hz : normSq z < 1) :
    g.mob z ∈ horodisc (g.mob ξ) (t * g.lam ξ) ↔ z ∈ horodisc ξ t := by
  have hu := g.normSq_coef_one
  have ha := g.normSq_coef_two
  set u := g.coef.1; set a := g.coef.2.1; set b := g.coef.2.2
  have hdξ := normSq_mobDen_pos b hu ha hξ.le
  have hdz := normSq_mobDen_pos b hu ha hz.le
  have hsub := mobF_sub_mobF b hu ha hξ.le hz.le
  have h1 := one_sub_normSq_mobF b hu ha hz.le
  have ha' : 0 < 1 - normSq a := by linarith
  set K : ℝ := (1 - normSq a) ^ 2 / (normSq (mobDen u a b ξ) * normSq (mobDen u a b z)) with hK
  have hKpos : 0 < K := by positivity
  have e1 : normSq (g.mob ξ - g.mob z) = K * normSq (ξ - z) := by
    show normSq (mobF u a b ξ - mobF u a b z) = _
    rw [hsub, map_div₀, map_mul, map_mul, map_mul, sigmaB_sub, normSq_sigmaB, hu]
    have h1' : normSq ((1 : ℂ) - (normSq a : ℂ)) = (1 - normSq a) ^ 2 := by
      rw [← ofReal_one, ← ofReal_sub, normSq_ofReal]; ring
    rw [h1', hK]; field_simp
  have e2 : t * g.lam ξ * (1 - normSq (g.mob z)) = K * (t * (1 - normSq z)) := by
    show t * ((1 - normSq a) / normSq (mobDen u a b ξ)) * (1 - normSq (mobF u a b z)) = _
    rw [h1, hK]; field_simp
  simp only [horodisc, mem_setOf_eq]
  rw [e1, e2]
  exact mul_lt_mul_iff_of_pos_left hKpos

theorem mob_ball (g : HypIsom) {z : ℂ} (hz : normSq z < 1) : normSq (g.mob z) < 1 :=
  normSq_mobF_lt _ g.normSq_coef_one g.normSq_coef_two hz

theorem mob_sphere (g : HypIsom) {z : ℂ} (hz : normSq z = 1) : normSq (g.mob z) = 1 :=
  normSq_mobF_eq_one _ g.normSq_coef_one g.normSq_coef_two hz

/-- The image of a horodisc in the Poincaré disc. -/
theorem smul_mem_horodisc_iff (g : HypIsom) {ξ : ℂ} (hξ : normSq ξ = 1) (t : ℝ)
    (z : PoincareDisc) :
    ((g • z : PoincareDisc) : ℂ) ∈ horodisc (g.mob ξ) (t * g.lam ξ) ↔ (z : ℂ) ∈ horodisc ξ t := by
  rw [coe_smul_poincareDisc]
  exact g.mob_mem_horodisc_iff hξ t z.normSq_lt

end HypIsom

theorem normSq_eq_one_iff {ξ : ℂ} : normSq ξ = 1 ↔ ‖ξ‖ = 1 := by
  rw [normSq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg ξ]
  · intro h; rw [h]; norm_num


/-! ### Complete hyperbolic surfaces: the developing map onto `ℍ` -/

instance : SimplyConnectedSpace PoincareDisc := by
  haveI : ContractibleSpace PoincareDisc :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, Metric.mem_ball_self one_pos⟩
  exact SimplyConnectedSpace.ofContractible _

instance : LocPathConnectedSpace PoincareDisc := Metric.isOpen_ball.locPathConnectedSpace

section Complete

variable (Y : Type*) [TopologicalSpace Y] [ChartedSpace PoincareDisc Y]

/-- **A complete hyperbolic surface** (the reading of "complete hyperbolic metric", SCOPE (b)):
a `(G, ℍ)`-manifold, `G = Isom(ℍ)`, whose developing maps (of its universal cover, with the
pulled-back structure) are covering maps — Thurston's and Goldman's completeness of a
`(G,X)`-structure. -/
def IsCompleteHyperbolic : Prop :=
  ∀ [LocPathConnectedSpace Y] (hY : SemilocallySimplyConnected Y) (y₀ : Y) (dev : UniversalCover Y y₀ → PoincareDisc),
    (letI := coverChartedSpace PoincareDisc hY y₀; IsGXMorphism HypIsom PoincareDisc dev) →
      IsCoveringMap dev

variable {Y}

/-- **The developing map of a complete hyperbolic surface is a homeomorphism onto `ℍ`**
(`ex:take_closed_unit_disc`, the infrastructure DEC-71 asks for): a covering map onto the simply
connected disc from the connected universal cover is bijective, and open. -/
theorem IsCompleteHyperbolic.exists_homeomorph [LocPathConnectedSpace Y] (hc : IsCompleteHyperbolic Y)
    (hY : SemilocallySimplyConnected Y) (y₀ : Y) (dev : UniversalCover Y y₀ → PoincareDisc)
    (hdev : letI := coverChartedSpace PoincareDisc hY y₀; IsGXMorphism HypIsom PoincareDisc dev) :
    ∃ Θ : UniversalCover Y y₀ ≃ₜ PoincareDisc, ⇑Θ = dev := by
  have hcov := hc hY y₀ dev hdev
  set x₀ : UniversalCover Y y₀ := UniversalCover.base y₀
  obtain ⟨sec, ⟨hsec0, hsec⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id PoincareDisc) (dev x₀) x₀ rfl
  have hsec' : ∀ z, dev (sec z) = z := fun z => congrFun hsec z
  have hid : (fun x => sec (dev x)) = id :=
    hcov.eq_of_comp_eq (sec.continuous.comp hcov.continuous) continuous_id
      (funext fun x => by simp only [comp_apply, hsec', id]) x₀ (by simp only [hsec0, id])
  have hinj : Injective dev := fun a b hab => by
    have h1 := congrFun hid a
    have h2 := congrFun hid b
    simp only [id] at h1 h2
    rw [← h1, ← h2, hab]
  have hsurj : Surjective dev := fun z => ⟨sec z, hsec' z⟩
  exact ⟨(Equiv.ofBijective dev ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcov.continuous
    hcov.isOpenMap, rfl⟩

end Complete


/-! ### Cusps -/

/-- The Cayley transform as a point of the disc. -/
def cayP (w : ℂ) (hw : 0 < w.im) : PoincareDisc :=
  ⟨cay w, normSq_lt_one_iff.1 (normSq_cay_lt hw)⟩

/-- The horoball `{Im w > t}` of the upper half-plane, as a space. -/
abbrev Horoball (t : ℝ) : Type := {w : ℂ // t < w.im}

/-- The Cayley transform on a horoball (`0 ≤ t`). -/
def cayHB {t : ℝ} (ht : 0 ≤ t) (w : Horoball t) : PoincareDisc := cayP w (lt_of_le_of_lt ht w.2)

theorem continuous_cay_on : ContinuousOn cay {w : ℂ | 0 < w.im} := fun _ hw =>
  ((continuous_id.sub continuous_const).continuousAt.div
    (continuous_id.add continuous_const).continuousAt (add_I_ne_zero hw)).continuousWithinAt

theorem isOpenEmbedding_cayHB {t : ℝ} (ht : 0 ≤ t) : Topology.IsOpenEmbedding (cayHB ht) := by
  have hc : Continuous (cayHB ht) := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_cay_on.comp_continuous continuous_subtype_val
      fun w => lt_of_le_of_lt ht w.2
  have hinj : Injective (cayHB ht) := fun a b hab => by
    have h := congrArg (fun z : PoincareDisc => cayInv (z : ℂ)) hab
    simp only [cayHB, cayP] at h
    rw [cayInv_cay (lt_of_le_of_lt ht a.2), cayInv_cay (lt_of_le_of_lt ht b.2)] at h
    exact Subtype.ext h
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hc hinj ?_
  -- the inverse is continuous on the image: `cayInv`
  intro O hO
  obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
  -- the image is `{z ∈ 𝔻 | cayInv z ∈ O' ∧ t < (cayInv z).im}`
  have : cayHB ht '' (Subtype.val ⁻¹' O') =
      {z : PoincareDisc | cayInv z ∈ O' ∧ t < (cayInv z).im} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [cayHB, cayP, mem_setOf_eq]
      rw [cayInv_cay (lt_of_le_of_lt ht w.2)]
      exact ⟨hw, w.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨cayInv z, h2⟩, h1, Subtype.ext ?_⟩
      simp only [cayHB, cayP]
      exact cay_cayInv (one_sub_ne_zero_of_normSq_lt z.normSq_lt)
  rw [this]
  have hci : ContinuousOn cayInv (Metric.ball (0 : ℂ) 1) := fun z hz =>
    ((continuous_const.mul (continuous_const.add continuous_id)).continuousAt.div
      (continuous_const.sub continuous_id).continuousAt
      (one_sub_ne_zero_of_normSq_lt (normSq_lt_one_iff.2 hz))).continuousWithinAt
  have hcc : Continuous fun z : PoincareDisc => cayInv z :=
    hci.comp_continuous continuous_subtype_val fun z => z.2
  exact (hO'.preimage hcc).inter (isOpen_lt continuous_const (Complex.continuous_im.comp hcc))

theorem norm_cexp_two_pi (w : ℂ) : ‖Complex.exp (2 * π * I * w)‖ = Real.exp (-(2 * π * w.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [mul_re, mul_im]

theorem cexp_two_pi_add_int (w : ℂ) (n : ℤ) :
    Complex.exp (2 * π * I * (w + n)) = Complex.exp (2 * π * I * w) := by
  rw [mul_add, Complex.exp_add]
  have : Complex.exp (2 * π * I * n) = 1 := by
    rw [Complex.exp_eq_one_iff]; exact ⟨n, by ring⟩
  rw [this, mul_one]

section CuspChartSec

variable {M : Type*} [TopologicalSpace M]

/-- **A cusp chart** at `s ∈ S`: an open neighbourhood `V` of `s` meeting `S` only at `s`, with a
homeomorphism `φ : V ≃ ball(0, e^{-2πc})`, `φ(s) = 0`. Through it, `M ∖ S` near `s` is the image
of the horoball `{Im w > c}` under the cusp map `w ↦ φ⁻¹(e^{2πiw})` (`GX.CuspChart.E`). -/
structure CuspChart (S : Set M) (s : M) where
  /-- The neighbourhood. -/
  V : Set M
  isOpen_V : IsOpen V
  mem_V : s ∈ V
  inter_eq : V ∩ S = {s}
  /-- The height of the horoball. -/
  c : ℝ
  c_pos : 0 < c
  /-- The chart. -/
  φ : V ≃ₜ Metric.ball (0 : ℂ) (Real.exp (-(2 * π * c)))
  φ_s : (φ ⟨s, mem_V⟩ : ℂ) = 0

namespace CuspChart

variable {S : Set M} {s : M} (C : CuspChart S s)

/-- The radius `e^{-2πt}`. -/
def ρ (t : ℝ) : ℝ := Real.exp (-(2 * π * t))

theorem ρ_pos (t : ℝ) : 0 < ρ t := Real.exp_pos _

theorem ρ_lt_ρ {t t' : ℝ} : ρ t < ρ t' ↔ t' < t := by
  rw [ρ, ρ, Real.exp_lt_exp]
  constructor
  · intro h; nlinarith [Real.pi_pos]
  · intro h; nlinarith [Real.pi_pos]

theorem norm_cexp_lt (w : Horoball C.c) :
    ‖Complex.exp (2 * π * I * (w : ℂ))‖ < Real.exp (-(2 * π * C.c)) := by
  rw [norm_cexp_two_pi]
  exact ρ_lt_ρ.2 w.2

/-- `w ↦ e^{2πiw}` into the ball. -/
def expH (w : Horoball C.c) : Metric.ball (0 : ℂ) (Real.exp (-(2 * π * C.c))) :=
  ⟨Complex.exp (2 * π * I * (w : ℂ)), mem_ball_zero_iff.2 (C.norm_cexp_lt w)⟩

theorem continuous_expH : Continuous C.expH :=
  ((Complex.continuous_exp.comp (continuous_const.mul continuous_subtype_val))).subtype_mk _

/-- The cusp map into `V`. -/
def EV (w : Horoball C.c) : C.V := C.φ.symm (C.expH w)

theorem φ_EV (w : Horoball C.c) : C.φ (C.EV w) = C.expH w := C.φ.apply_symm_apply _

theorem EV_ne (w : Horoball C.c) : (C.EV w : M) ≠ s := by
  intro h
  have h' : C.EV w = ⟨s, C.mem_V⟩ := Subtype.ext h
  have := congrArg (fun x => (C.φ x : ℂ)) h'
  simp only [φ_EV, C.φ_s, expH] at this
  exact Complex.exp_ne_zero _ this

theorem EV_notMem (w : Horoball C.c) : (C.EV w : M) ∉ S := fun h => by
  have : (C.EV w : M) ∈ C.V ∩ S := ⟨(C.EV w).2, h⟩
  rw [C.inter_eq] at this
  exact C.EV_ne w this

/-- **The cusp map** `w ↦ φ⁻¹(e^{2πiw})`, from the horoball `{Im w > c}` onto `V ∖ {s}`. -/
def E (w : Horoball C.c) : (Sᶜ : Set M) := ⟨C.EV w, C.EV_notMem w⟩

theorem continuous_E : Continuous C.E :=
  ((continuous_subtype_val.comp (C.φ.symm.continuous.comp C.continuous_expH))).subtype_mk _

theorem E_add_int (w : Horoball C.c) (n : ℤ) :
    C.E ⟨w + n, by simpa using w.2⟩ = C.E w := by
  apply Subtype.ext
  simp only [E, EV]
  congr 2
  apply Subtype.ext
  simp only [expH]
  exact cexp_two_pi_add_int w n

theorem E_add_one (w : Horoball C.c) :
    C.E ⟨w + 1, by simpa using w.2⟩ = C.E w := by
  have := C.E_add_int w 1
  simpa using this

theorem exists_int_of_E_eq {w w' : Horoball C.c} (h : C.E w = C.E w') :
    ∃ n : ℤ, (w' : ℂ) = w + n := by
  have h0 : ((C.E w : (Sᶜ : Set M)) : M) = C.E w' := congrArg Subtype.val h
  have h1 : C.EV w = C.EV w' := Subtype.ext h0
  have h2 := congrArg (fun x => (C.φ x : ℂ)) h1
  simp only [φ_EV, expH] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h2.symm
  refine ⟨n, ?_⟩
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  apply mul_left_cancel₀ hπ
  linear_combination hn

/-- The sub-neighbourhoods `W_t = φ⁻¹(ball(0, e^{-2πt}))` of `s`. -/
def W (t : ℝ) : Set M := Subtype.val '' {x : C.V | ‖(C.φ x : ℂ)‖ < ρ t}

theorem W_subset_V (t : ℝ) : C.W t ⊆ C.V := by
  rintro _ ⟨x, -, rfl⟩; exact x.2

theorem mem_W (t : ℝ) : s ∈ C.W t :=
  ⟨⟨s, C.mem_V⟩, by show ‖(C.φ ⟨s, C.mem_V⟩ : ℂ)‖ < ρ t; rw [C.φ_s, norm_zero]; exact ρ_pos t,
    rfl⟩

theorem isOpen_W (t : ℝ) : IsOpen (C.W t) := by
  refine C.isOpen_V.isOpenMap_subtype_val _ ?_
  exact isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp C.φ.continuous))
    continuous_const

theorem isPreconnected_W (t : ℝ) : IsPreconnected (C.W t) := by
  have hB : IsPreconnected {y : Metric.ball (0 : ℂ) (Real.exp (-(2 * π * C.c))) |
      ‖(y : ℂ)‖ < ρ t} := by
    rw [Topology.IsInducing.subtypeVal.isPreconnected_image.symm]
    have : Subtype.val '' {y : Metric.ball (0 : ℂ) (Real.exp (-(2 * π * C.c))) | ‖(y : ℂ)‖ < ρ t} =
        Metric.ball 0 (Real.exp (-(2 * π * C.c))) ∩ Metric.ball 0 (ρ t) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, mem_ball_zero_iff.2 hy⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨z, h1⟩, mem_ball_zero_iff.1 h2, rfl⟩
    rw [this]
    exact ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have : C.W t = (Subtype.val ∘ C.φ.symm) '' {y | ‖(y : ℂ)‖ < ρ t} := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨C.φ x', hx', by simp⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨C.φ.symm y, by simpa using hy, rfl⟩
  rw [this]
  exact hB.image _ (continuous_subtype_val.comp C.φ.symm.continuous).continuousOn

theorem isCNbhd_W (t : ℝ) : IsCNbhd s (C.W t) := ⟨C.isOpen_W t, C.isPreconnected_W t, C.mem_W t⟩

theorem W_inter (t : ℝ) : C.W t ∩ S = {s} := by
  refine Subset.antisymm ?_ (singleton_subset_iff.2 ⟨C.mem_W t, ?_⟩)
  · rw [← C.inter_eq]; exact inter_subset_inter_left _ (C.W_subset_V t)
  · have : s ∈ C.V ∩ S := by rw [C.inter_eq]; rfl
    exact this.2

theorem W_anti {t t' : ℝ} (h : t ≤ t') : C.W t' ⊆ C.W t := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ‖(C.φ x : ℂ)‖ < ρ t' := hx
  refine ⟨x, show ‖(C.φ x : ℂ)‖ < ρ t from lt_of_lt_of_le hx' ?_, rfl⟩
  rcases h.lt_or_eq with h | h
  · exact (ρ_lt_ρ.2 h).le
  · rw [h]

theorem E_mem_W_iff (t : ℝ) (w : Horoball C.c) : (C.E w : M) ∈ C.W t ↔ t < (w : ℂ).im := by
  constructor
  · rintro ⟨x, hx, hxw⟩
    have : x = C.EV w := Subtype.ext hxw
    have hx' : ‖(C.φ x : ℂ)‖ < ρ t := hx
    rw [this, φ_EV] at hx'
    simp only [expH] at hx'
    rw [norm_cexp_two_pi] at hx'
    exact ρ_lt_ρ.1 hx'
  · intro h
    refine ⟨C.EV w, ?_, rfl⟩
    show ‖(C.φ (C.EV w) : ℂ)‖ < ρ t
    simp only [φ_EV, expH]
    rw [norm_cexp_two_pi]
    exact ρ_lt_ρ.2 h

theorem exists_E_eq {t : ℝ} (ht : C.c ≤ t) {x : M} (hx : x ∈ C.W t) (hxs : x ≠ s) :
    ∃ w : Horoball C.c, t < (w : ℂ).im ∧ (C.E w : M) = x := by
  obtain ⟨x', hx', rfl⟩ := hx
  set y : ℂ := (C.φ x' : ℂ)
  have hy0 : y ≠ 0 := by
    intro h
    apply hxs
    have : x' = ⟨s, C.mem_V⟩ := C.φ.injective (Subtype.ext (by rw [C.φ_s]; exact h))
    rw [this]
  set w : ℂ := Complex.log y / (2 * π * I)
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hexp : Complex.exp (2 * π * I * w) = y := by
    rw [mul_div_cancel₀ _ hπ, Complex.exp_log hy0]
  have hwim : w.im = -(Real.log ‖y‖) / (2 * π) := by
    simp only [w, div_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, normSq_apply,
      Complex.log_re, re_ofNat, im_ofNat]
    field_simp
    ring
  have hyt : ‖y‖ < ρ t := hx'
  have hlog : Real.log ‖y‖ < -(2 * π * t) := by
    rw [ρ] at hyt
    exact (Real.log_lt_iff_lt_exp (norm_pos_iff.2 hy0)).2 hyt
  have htw : t < w.im := by
    rw [hwim, lt_div_iff₀ (by positivity)]
    linarith
  refine ⟨⟨w, lt_of_le_of_lt ht htw⟩, htw, ?_⟩
  show ((C.φ.symm (C.expH _) : C.V) : M) = x'
  congr 1
  apply C.φ.injective
  rw [C.φ.apply_symm_apply]
  exact Subtype.ext hexp

theorem exists_W_subset {N : Set M} (hN : N ∈ 𝓝 s) : ∃ t, C.c ≤ t ∧ C.W t ⊆ N := by
  have h1 : (Subtype.val ⁻¹' N : Set C.V) ∈ 𝓝 (⟨s, C.mem_V⟩ : C.V) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  have h2 : C.φ.symm ⁻¹' (Subtype.val ⁻¹' N) ∈ 𝓝 (C.φ ⟨s, C.mem_V⟩) := by
    apply C.φ.symm.continuous.continuousAt.preimage_mem_nhds
    rw [C.φ.symm_apply_apply]; exact h1
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 h2
  set t := max C.c (-(Real.log r) / (2 * π) + 1)
  refine ⟨t, le_max_left _ _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hρ : ρ t < r := by
    rw [ρ, ← Real.lt_log_iff_exp_lt hr]
    have : -(Real.log r) / (2 * π) + 1 ≤ t := le_max_right _ _
    have h' : -(Real.log r) / (2 * π) < t := by linarith
    rw [div_lt_iff₀ (by positivity)] at h'
    linarith
  have : C.φ x ∈ Metric.ball (C.φ ⟨s, C.mem_V⟩) r := by
    rw [Metric.mem_ball, Subtype.dist_eq, C.φ_s, dist_zero_right]
    exact lt_trans hx hρ
  have := hrN this
  simpa using this

variable [ChartedSpace PoincareDisc (Sᶜ : Set M)]

/-- The Cayley transform of the horoball of the cusp chart. -/
def cayH (w : Horoball C.c) : PoincareDisc := cayHB C.c_pos.le w

/-- **A hyperbolic cusp**: the cusp map is a `(G, ℍ)`-morphism from the horoball `{Im w > c}`
(with the structure of an open subset of `ℍ`): read in the charts of `M ∖ S`, it is near every
point a translate of the Cayley transform. -/
def IsHyperbolicCusp : Prop :=
  ∀ w : Horoball C.c, ∃ g : HypIsom, ∀ᶠ w' in 𝓝 w,
    chartAt PoincareDisc (C.E w) (C.E w') = g • C.cayH w'

end CuspChart

end CuspChartSec


/-! ### The singular `(G,X)`-structure of `M` -/

section Lift

variable {M : Type*} [TopologicalSpace M] {S : Set M}

/-- The open disc into the closed disc, as an open partial homeomorphism. -/
def ofPDChart : OpenPartialHomeomorph PoincareDisc ClosedDisc :=
  ClosedDisc.isOpenEmbedding_ofPD.toOpenPartialHomeomorph ClosedDisc.ofPD

/-- A chart of `M ∖ S` into `ℍ`, as a chart of `M` into `X ⊇ ℍ`. -/
def liftChart (hS : IsClosed S) (e : OpenPartialHomeomorph (Sᶜ : Set M) PoincareDisc) :
    OpenPartialHomeomorph M ClosedDisc :=
  (e.trans ofPDChart).lift_openEmbedding hS.isOpen_compl.isOpenEmbedding_subtypeVal

theorem liftChart_apply (hS : IsClosed S) (e : OpenPartialHomeomorph (Sᶜ : Set M) PoincareDisc)
    (y : (Sᶜ : Set M)) : liftChart hS e y = ClosedDisc.ofPD (e y) := by
  rw [liftChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

theorem liftChart_source (hS : IsClosed S) (e : OpenPartialHomeomorph (Sᶜ : Set M) PoincareDisc) :
    (liftChart hS e).source = Subtype.val '' e.source := by
  rw [liftChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  congr 1
  rw [OpenPartialHomeomorph.trans_source]
  simp [ofPDChart]

theorem liftChart_source_subset (hS : IsClosed S)
    (e : OpenPartialHomeomorph (Sᶜ : Set M) PoincareDisc) : (liftChart hS e).source ⊆ Sᶜ := by
  rw [liftChart_source]; rintro _ ⟨y, -, rfl⟩; exact y.2

variable [ChartedSpace PoincareDisc (Sᶜ : Set M)]

/-- The atlas of `M` given by the hyperbolic structure of `M ∖ S`. -/
def cuspedAtlas (hS : IsClosed S) : Set (OpenPartialHomeomorph M ClosedDisc) :=
  range fun y : (Sᶜ : Set M) => liftChart hS (chartAt PoincareDisc y)

theorem mem_liftChart_source (hS : IsClosed S) (y : (Sᶜ : Set M)) :
    (y : M) ∈ (liftChart hS (chartAt PoincareDisc y)).source := by
  rw [liftChart_source]; exact ⟨y, mem_chart_source _ y, rfl⟩

theorem support_cuspedAtlas (hS : IsClosed S) : support (cuspedAtlas hS) = Sᶜ := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨e, ⟨y, rfl⟩, hxe⟩ := mem_support.1 hx
    exact liftChart_source_subset hS _ hxe
  · intro x hx
    exact mem_support.2 ⟨_, ⟨⟨x, hx⟩, rfl⟩, mem_liftChart_source hS ⟨x, hx⟩⟩

/-- Near a point of `M ∖ S`, a statement about the points of `M` follows from the statement
about the points of `M ∖ S`. -/
theorem eventually_of_compl (hS : IsClosed S) {y : (Sᶜ : Set M)} {P : M → Prop}
    (h : ∀ᶠ z : (Sᶜ : Set M) in 𝓝 y, P z) : ∀ᶠ x in 𝓝 (y : M), P x := by
  rw [← (hS.isOpen_compl.isOpenEmbedding_subtypeVal).map_nhds_eq y]
  exact h

variable [HasGroupoid (Sᶜ : Set M) (gxGroupoid HypIsom PoincareDisc)]

/-- Two lifted charts differ near every common point by an element of `G`. -/
theorem liftChart_eventually_smul (hS : IsClosed S) {e e' : OpenPartialHomeomorph (Sᶜ : Set M) PoincareDisc}
    (he : e ∈ (gxGroupoid HypIsom PoincareDisc).maximalAtlas (Sᶜ : Set M))
    (he' : e' ∈ (gxGroupoid HypIsom PoincareDisc).maximalAtlas (Sᶜ : Set M))
    {y : (Sᶜ : Set M)} (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    ∃ g : HypIsom, ∀ᶠ x in 𝓝 (y : M), liftChart hS e' x = g • liftChart hS e x := by
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas he he' hy hy'
  exact ⟨g, eventually_of_compl hS (P := fun x => liftChart hS e' x = g • liftChart hS e x)
    (hg.mono fun z hz => by
      show liftChart hS e' z = g • liftChart hS e z
      rw [liftChart_apply, liftChart_apply, hz, HypIsom.smul_ofPD])⟩

/-- The lifted charts form a `(G,X)`-atlas. -/
theorem isGXAtlas_cuspedAtlas (hS : IsClosed S) : IsGXAtlas HypIsom (cuspedAtlas (M := M) hS) := by
  refine isGXAtlas_of_eventually fun e he e' he' x hx => ?_
  obtain ⟨y, rfl⟩ := he
  obtain ⟨y', rfl⟩ := he'
  have hxS : x ∈ Sᶜ := liftChart_source_subset hS _ hx.1
  have h1 : (⟨x, hxS⟩ : (Sᶜ : Set M)) ∈ (chartAt PoincareDisc y).source := by
    have := hx.1; rw [liftChart_source] at this
    obtain ⟨z, hz, hzx⟩ := this
    rwa [show (⟨x, hxS⟩ : (Sᶜ : Set M)) = z from Subtype.ext hzx.symm]
  have h2 : (⟨x, hxS⟩ : (Sᶜ : Set M)) ∈ (chartAt PoincareDisc y').source := by
    have := hx.2; rw [liftChart_source] at this
    obtain ⟨z, hz, hzx⟩ := this
    rwa [show (⟨x, hxS⟩ : (Sᶜ : Set M)) = z from Subtype.ext hzx.symm]
  exact liftChart_eventually_smul hS ((gxGroupoid HypIsom PoincareDisc).chart_mem_maximalAtlas y)
    ((gxGroupoid HypIsom PoincareDisc).chart_mem_maximalAtlas y') h1 h2

end Lift


theorem convex_horoball (t : ℝ) : Convex ℝ {w : ℂ | t < w.im} := by
  have := convex_halfSpace_gt (Complex.imLm.isLinear) t
  simpa [Complex.imLm_coe] using this

instance (t : ℝ) : PreconnectedSpace (Horoball t) :=
  isPreconnected_iff_preconnectedSpace.1 (convex_horoball t).isPreconnected

instance (t : ℝ) : Nonempty (Horoball t) :=
  ⟨⟨(|t| + 1 : ℝ) * I, by simp; linarith [le_abs_self t]⟩⟩

theorem isOpen_horoball (t : ℝ) : IsOpen {w : ℂ | t < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

instance (t : ℝ) : LocPathConnectedSpace (Horoball t) := (isOpen_horoball t).locPathConnectedSpace

instance (t : ℝ) : SimplyConnectedSpace (Horoball t) := by
  haveI : ContractibleSpace (Horoball t) := (convex_horoball t).contractibleSpace
    ⟨(|t| + 1 : ℝ) * I, by simp; linarith [le_abs_self t]⟩
  exact SimplyConnectedSpace.ofContractible _

/-- The inclusion of horoballs. -/
def horoInc {t t' : ℝ} (h : t ≤ t') (w : Horoball t') : Horoball t := ⟨w, lt_of_le_of_lt h w.2⟩

theorem continuous_horoInc {t t' : ℝ} (h : t ≤ t') : Continuous (horoInc h) :=
  continuous_subtype_val.subtype_mk _

/-- The translation `w ↦ w + n` of a horoball. -/
def horoAdd {t : ℝ} (n : ℤ) (w : Horoball t) : Horoball t := ⟨w + n, by simpa using w.2⟩

theorem continuous_horoAdd {t : ℝ} (n : ℤ) : Continuous (horoAdd (t := t) n) :=
  (continuous_subtype_val.add continuous_const).subtype_mk _

/-- The Cayley transform into the closed disc, as a chart of a horoball. -/
def cayChart {t : ℝ} (ht : 0 ≤ t) : OpenPartialHomeomorph (Horoball t) ClosedDisc :=
  (ClosedDisc.isOpenEmbedding_ofPD.comp (isOpenEmbedding_cayHB ht)).toOpenPartialHomeomorph _

theorem cayChart_apply {t : ℝ} (ht : 0 ≤ t) (w : Horoball t) :
    cayChart ht w = ClosedDisc.ofPD (cayHB ht w) := rfl

theorem cayChart_source {t : ℝ} (ht : 0 ≤ t) : (cayChart ht).source = univ := rfl

section Cusped

variable {M : Type*} [TopologicalSpace M] {S : Set M} [ChartedSpace PoincareDisc (Sᶜ : Set M)]

variable (M S) in
/-- **The data of `ex:take_closed_unit_disc`** (SCOPE (b)): `S ⊆ M` finite and `M ∖ S` a complete
hyperbolic surface — a `(G, ℍ)`-manifold, `G = Isom(ℍ)`, whose developing maps are covering maps
— with a cusp at every point of `S`. -/
structure IsCuspedHyperbolic : Prop where
  finite : S.Finite
  hasGroupoid : HasGroupoid (Sᶜ : Set M) (gxGroupoid HypIsom PoincareDisc)
  complete : IsCompleteHyperbolic (Sᶜ : Set M)
  cusp : ∀ s ∈ S, ∃ C : CuspChart S s, C.IsHyperbolicCusp

namespace IsCuspedHyperbolic

variable [T1Space M] (H : IsCuspedHyperbolic M S)
include H

theorem isClosed : IsClosed S := H.finite.isClosed

/-- A chart into `ℂ` at a cusp. -/
theorem exists_chart (s : M) (hs : s ∈ S) :
    ∃ e : OpenPartialHomeomorph M ℂ, s ∈ e.source := by
  obtain ⟨C, -⟩ := H.cusp s hs
  haveI : Nonempty (Metric.ball (0 : ℂ) (Real.exp (-(2 * π * C.c)))) :=
    ⟨⟨0, Metric.mem_ball_self (Real.exp_pos _)⟩⟩
  have hball : Topology.IsOpenEmbedding (Subtype.val :
      Metric.ball (0 : ℂ) (Real.exp (-(2 * π * C.c))) → ℂ) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  set e₀ : OpenPartialHomeomorph C.V ℂ :=
    C.φ.toOpenPartialHomeomorph.trans (hball.toOpenPartialHomeomorph _)
  refine ⟨e₀.lift_openEmbedding C.isOpen_V.isOpenEmbedding_subtypeVal, ?_⟩
  rw [OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨⟨s, C.mem_V⟩, ?_, rfl⟩
  simp [e₀]

/-- `M ∖ S` is portly (`S` is skeletal). -/
theorem isPortly_compl [LocallyConnectedSpace M] : IsPortly (Sᶜ : Set M) := by
  haveI := H.finite.to_subtype
  have h : (Sᶜ : Set M) = ⋂ s : S, ({(s : M)}ᶜ : Set M) := by
    ext x
    simp only [mem_compl_iff, mem_iInter, mem_singleton_iff]
    exact ⟨fun h i hxi => h (hxi ▸ i.2), fun h hx => h ⟨x, hx⟩ rfl⟩
  rw [h]
  refine isPortly_iInter fun s => ?_
  obtain ⟨e, he⟩ := H.exists_chart s s.2
  exact isPortly_compl_singleton_of_chart (by rw [Complex.rank_real_complex]; norm_num) e he

theorem isAEAtlas [LocallyConnectedSpace M] : IsAEAtlas HypIsom (cuspedAtlas (M := M) H.isClosed) := by
  haveI := H.hasGroupoid
  refine ⟨isGXAtlas_cuspedAtlas H.isClosed, ?_⟩
  rw [support_cuspedAtlas]; exact H.isPortly_compl

/-- **The singular `(G,X)`-structure of `M`** (`ex:take_closed_unit_disc`, "`M` is a singular
`(G,X)`-manifold"): the maximal a.e. atlas generated by the charts of the hyperbolic surface
`M ∖ S`, read in `ℍ ⊆ X`. -/
@[reducible] def singularStructure [LocallyConnectedSpace M] : SingularGXStructure HypIsom ClosedDisc M :=
  ⟨maximalAEAtlas HypIsom (cuspedAtlas H.isClosed), H.isAEAtlas.isMaximalAEAtlas_maximalAEAtlas⟩

theorem cuspedAtlas_subset [LocallyConnectedSpace M] :
    letI := H.singularStructure
    cuspedAtlas H.isClosed ⊆ aeAtlas HypIsom ClosedDisc M :=
  H.isAEAtlas.subset_maximalAEAtlas

/-- **The parabolic holonomy**: a cusp is not in the support of any `(G,X)`-atlas containing the
charts of `M ∖ S` — its cusp map would develop injectively, while it is `1`-periodic. -/
theorem notMem_support_of_cusp {B : Set (OpenPartialHomeomorph M ClosedDisc)}
    (hB : IsGXAtlas HypIsom B) (hAB : cuspedAtlas H.isClosed ⊆ B) {s : M} (hs : s ∈ S) :
    s ∉ support B := by
  intro hsB
  obtain ⟨C, hC⟩ := H.cusp s hs
  obtain ⟨e, he, hse⟩ := mem_support.1 hsB
  obtain ⟨t, hct, htW⟩ := C.exists_W_subset (e.open_source.mem_nhds hse)
  have ht0 : 0 ≤ t := (C.c_pos.trans_le hct).le
  set f : Horoball t → ClosedDisc := fun w => e (C.E (horoInc hct w) : M) with hf
  have hloc : ∀ w ∈ (univ : Set (Horoball t)), ∃ g : HypIsom,
      ∀ᶠ w' in 𝓝 w, f w' = g • cayChart ht0 w' := by
    intro w _
    set y : (Sᶜ : Set M) := C.E (horoInc hct w)
    have hyW : (y : M) ∈ C.W t := (C.E_mem_W_iff t _).2 w.2
    have hℓ : liftChart H.isClosed (chartAt PoincareDisc y) ∈ B := hAB ⟨y, rfl⟩
    obtain ⟨g₁, hg₁⟩ := hB.eventually_smul_eq hℓ he (mem_liftChart_source H.isClosed y)
      (htW hyW)
    obtain ⟨g₂, hg₂⟩ := hC (horoInc hct w)
    have hcE : Continuous fun w' : Horoball t => (C.E (horoInc hct w') : M) :=
      continuous_subtype_val.comp (C.continuous_E.comp (continuous_horoInc hct))
    have h1 := hcE.continuousAt.eventually hg₁
    have h2 := (continuous_horoInc hct).continuousAt.eventually hg₂
    refine ⟨g₁ * g₂, ?_⟩
    filter_upwards [h1, h2] with w' hw1 hw2
    simp only [hf]
    rw [hw1, liftChart_apply, hw2, cayChart_apply, mul_smul, ← HypIsom.smul_ofPD]
    rfl
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected (e := cayChart ht0)
    isPreconnected_univ (by rw [cayChart_source]) hloc
  -- periodicity
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (Horoball t))
  have hper : f (horoAdd 1 w₀) = f w₀ := by
    simp only [hf]
    congr 2
    have := C.E_add_one (horoInc hct w₀)
    convert this using 2
    simp [horoAdd, horoInc]
  rw [hg _ (mem_univ _), hg _ (mem_univ _), smul_left_cancel_iff] at hper
  have := congrArg (fun x : ClosedDisc => (x : ℂ)) hper
  simp only [cayChart_apply, ClosedDisc.coe_ofPD, cayHB, cayP, horoAdd] at this
  exact cay_add_one_ne (lt_of_le_of_lt ht0 w₀.2) (by exact_mod_cast this)

/-- **`sing(M) = S`** (`ex:take_closed_unit_disc`). -/
theorem sing_eq [LocallyConnectedSpace M] :
    letI := H.singularStructure
    Sing HypIsom ClosedDisc M = S := by
  letI := H.singularStructure
  haveI := H.hasGroupoid
  apply Subset.antisymm
  · intro x hx
    by_contra hxS
    apply hx
    exact support_mono H.cuspedAtlas_subset (by rw [support_cuspedAtlas]; exact hxS)
  · intro s hs
    exact H.notMem_support_of_cusp (isMaximalAEAtlas_aeAtlas HypIsom ClosedDisc M).1.1
      H.cuspedAtlas_subset hs

end IsCuspedHyperbolic

end Cusped


/-! ### The universal cover of `M ∖ S` near a cusp -/

theorem isOpenEmbedding_smul_cayHB (g : HypIsom) {t : ℝ} (ht : 0 ≤ t) :
    Topology.IsOpenEmbedding fun w : Horoball t => g • cayHB ht w :=
  (Homeomorph.smul g).isOpenEmbedding.comp (isOpenEmbedding_cayHB ht)

theorem isPreconnected_horoball_sub {c t : ℝ} (hct : c ≤ t) :
    IsPreconnected {w : Horoball c | t < (w : ℂ).im} := by
  have : {w : Horoball c | t < (w : ℂ).im} = range (horoInc hct) := by
    ext w
    exact ⟨fun hw => ⟨⟨w, hw⟩, rfl⟩, fun ⟨w', h⟩ => h ▸ w'.2⟩
  rw [this]
  exact isPreconnected_range (continuous_horoInc hct)

section Develop

variable {M : Type*} [TopologicalSpace M] {S : Set M} [ChartedSpace PoincareDisc (Sᶜ : Set M)]
  [LocPathConnectedSpace (Sᶜ : Set M)] {y₀ : (Sᶜ : Set M)}


variable (hY : SemilocallySimplyConnected (Sᶜ : Set M)) (dv : UniversalCover (Sᶜ : Set M) y₀ ≃ₜ PoincareDisc)
  (hdv : ∀ c : UniversalCover (Sᶜ : Set M) y₀, ∃ g : HypIsom, ∀ᶠ c' in 𝓝 c, dv c' = g • chartAt PoincareDisc (UniversalCover.proj (Sᶜ : Set M) y₀ c) (UniversalCover.proj (Sᶜ : Set M) y₀ c'))

include hY hdv in
/-- **The lift of a cusp** to the universal cover develops onto a horodisc: a lift `L` of the
cusp map through `π : \widetilde{M ∖ S} → M ∖ S` satisfies `dv ∘ L = g • cay`. -/
theorem exists_cusp_lift {s : M} (C : CuspChart S s) (hC : C.IsHyperbolicCusp) (k : UniversalCover (Sᶜ : Set M) y₀)
    (w₀ : Horoball C.c) (hk : UniversalCover.proj (Sᶜ : Set M) y₀ k = C.E w₀) :
    ∃ L : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀, Continuous L ∧ L w₀ = k ∧ (∀ w, UniversalCover.proj (Sᶜ : Set M) y₀ (L w) = C.E w) ∧
      ∃ g : HypIsom, ∀ w, dv (L w) = g • C.cayH w := by
  have hπ := UniversalCover.isCoveringMap_proj (y₀ := y₀) hY
  obtain ⟨L, ⟨hL0, hL⟩, -⟩ := hπ.existsUnique_continuousMap_lifts ⟨C.E, C.continuous_E⟩ w₀ k hk
  have hLp : ∀ w, UniversalCover.proj (Sᶜ : Set M) y₀ (L w) = C.E w := fun w => congrFun hL w
  set ref : OpenPartialHomeomorph (Horoball C.c) PoincareDisc :=
    (isOpenEmbedding_cayHB C.c_pos.le).toOpenPartialHomeomorph _
  have hloc : ∀ w ∈ (univ : Set (Horoball C.c)), ∃ g : HypIsom,
      ∀ᶠ w' in 𝓝 w, dv (L w') = g • ref w' := by
    intro w _
    obtain ⟨g₁, hg₁⟩ := hdv (L w)
    obtain ⟨g₂, hg₂⟩ := hC w
    refine ⟨g₁ * g₂, ?_⟩
    filter_upwards [L.continuous.continuousAt.eventually hg₁, hg₂] with w' h1 h2
    rw [h1, hLp, hLp, h2, mul_smul]
    rfl
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected (e := ref) isPreconnected_univ
    (by intro w _; exact mem_univ _) hloc
  exact ⟨L, L.continuous, hL0, hLp, g, fun w => hg w (mem_univ _)⟩

include hY in
/-- Lifts of the cusp map are determined by one value. -/
theorem cusp_lift_unique {s : M} (C : CuspChart S s) {L L' : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀} (hL : Continuous L)
    (hL' : Continuous L') (hLp : ∀ w, UniversalCover.proj (Sᶜ : Set M) y₀ (L w) = C.E w) (hL'p : ∀ w, UniversalCover.proj (Sᶜ : Set M) y₀ (L' w) = C.E w)
    {w : Horoball C.c} (h : L w = L' w) : L = L' :=
  (UniversalCover.isCoveringMap_proj (y₀ := y₀) hY).eq_of_comp_eq hL hL'
    (funext fun w => by simp only [comp_apply, hLp, hL'p]) w h

theorem range_cusp_lift_eq {s : M} (C : CuspChart S s) {L : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀} {g : HypIsom}
    (hg : ∀ w, dv (L w) = g • C.cayH w) : L = fun w => dv.symm (g • C.cayH w) :=
  funext fun w => by rw [← hg, dv.symm_apply_apply]

theorem isOpenEmbedding_cusp_lift {s : M} (C : CuspChart S s) {L : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀}
    {g : HypIsom} (hg : ∀ w, dv (L w) = g • C.cayH w) : Topology.IsOpenEmbedding L := by
  rw [range_cusp_lift_eq dv C hg]
  exact dv.symm.isOpenEmbedding.comp (isOpenEmbedding_smul_cayHB g C.c_pos.le)

include hY hdv in
/-- **The components over a cusp neighbourhood are horoballs**: for an end `e` of the Fox
completion over a cusp `s`, the components `e(W_t)` (`t ≥ c`) are the images `L({Im w > t})` of
one lift of the cusp map. -/
theorem exists_end_lift {s : M} (hs : s ∈ S) (C : CuspChart S s) (hC : C.IsHyperbolicCusp)
    (e : SpreadEnd (univCoverProj S y₀)) (he : e.base = s) :
    ∃ L : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀, Continuous L ∧ (∀ w, UniversalCover.proj (Sᶜ : Set M) y₀ (L w) = C.E w) ∧
      (∃ g : HypIsom, ∀ w, dv (L w) = g • C.cayH w) ∧
      ∀ t, C.c ≤ t → e (C.W t) = L '' {w | t < (w : ℂ).im} := by
  have hW : ∀ t, IsCNbhd e.base (C.W t) := fun t => he ▸ C.isCNbhd_W t
  have hpre : ∀ (t : ℝ) (k : UniversalCover (Sᶜ : Set M) y₀), k ∈ univCoverProj S y₀ ⁻¹' C.W t ↔ ((UniversalCover.proj (Sᶜ : Set M) y₀ k : (Sᶜ : Set M)) : M) ∈ C.W t :=
    fun _ _ => Iff.rfl
  have hne : ∀ k : UniversalCover (Sᶜ : Set M) y₀, ((UniversalCover.proj (Sᶜ : Set M) y₀ k : (Sᶜ : Set M)) : M) ≠ s := fun k h => (UniversalCover.proj (Sᶜ : Set M) y₀ k).2 (h ▸ hs)
  -- a point of `e(W_c)` and a lift through it
  obtain ⟨k, hk⟩ := e.nonempty (hW C.c)
  obtain ⟨w₀, -, hw₀⟩ := C.exists_E_eq le_rfl (e.subset_preimage (hW C.c) hk) (hne k)
  obtain ⟨L, hLc, hL0, hLp, g, hg⟩ := exists_cusp_lift hY dv hdv C hC k w₀ (Subtype.ext hw₀.symm)
  have hLo := isOpenEmbedding_cusp_lift dv C hg
  have hEW : ∀ t (w : Horoball C.c), L w ∈ univCoverProj S y₀ ⁻¹' C.W t ↔ t < (w : ℂ).im :=
    fun t w => by rw [hpre, hLp]; exact C.E_mem_W_iff t w
  -- step A: `e(W_c) = L(H_c)`
  have hA : e (C.W C.c) = range L := by
    apply Subset.antisymm
    · refine (e.isPreconnected (hW C.c)).subset_of_closure_inter_subset hLo.isOpen_range
        ⟨k, hk, w₀, hL0⟩ ?_
      rintro z ⟨hzc, hze⟩
      obtain ⟨w', -, hw'⟩ := C.exists_E_eq le_rfl (e.subset_preimage (hW C.c) hze) (hne z)
      obtain ⟨L', hL'c, hL'0, hL'p, g', hg'⟩ := exists_cusp_lift hY dv hdv C hC z w' (Subtype.ext hw'.symm)
      have hL'o := isOpenEmbedding_cusp_lift dv C hg'
      obtain ⟨y, ⟨a, rfl⟩, ⟨b, hb⟩⟩ := mem_closure_iff.1 hzc _ hL'o.isOpen_range ⟨w', hL'0⟩
      have hab : C.E b = C.E a := by rw [← hLp, ← hL'p, hb]
      obtain ⟨n, hn⟩ := C.exists_int_of_E_eq hab
      have hshift : (fun w => L' (horoAdd n w)) = L := by
        refine cusp_lift_unique hY C (hL'c.comp (continuous_horoAdd n)) hLc
          (fun w => by rw [hL'p]; exact C.E_add_int w n) hLp (w := b) ?_
        rw [hb]; congr 1; exact Subtype.ext hn.symm
      refine ⟨horoAdd (-n) w', ?_⟩
      rw [← hshift]
      simp only
      rw [← hL'0]; congr 1
      apply Subtype.ext; simp [horoAdd]
    · rintro _ ⟨w, rfl⟩
      refine (e.isCompOf _ (hW C.c)).subset_of_meets (isPreconnected_range hLc) ?_ ⟨k, ⟨w₀, hL0⟩, hk⟩
        ⟨w, rfl⟩
      rintro _ ⟨w', rfl⟩
      exact (hEW C.c w').2 w'.2
  refine ⟨L, hLc, hLp, ⟨g, hg⟩, fun t ht => ?_⟩
  apply Subset.antisymm
  · intro z hz
    have hz' : z ∈ e (C.W C.c) := e.mono _ _ (hW t) (hW C.c) (C.W_anti ht) hz
    rw [hA] at hz'
    obtain ⟨w, rfl⟩ := hz'
    exact ⟨w, (hEW t w).1 (e.subset_preimage (hW t) hz), rfl⟩
  · obtain ⟨z, hz⟩ := e.nonempty (hW t)
    have hz' : z ∈ e (C.W C.c) := e.mono _ _ (hW t) (hW C.c) (C.W_anti ht) hz
    rw [hA] at hz'
    obtain ⟨w, rfl⟩ := hz'
    refine (e.isCompOf _ (hW t)).subset_of_meets ((isPreconnected_horoball_sub ht).image _
      hLc.continuousOn) ?_ ⟨L w, ⟨w, (hEW t w).1 (e.subset_preimage (hW t) hz), rfl⟩, hz⟩
    rintro _ ⟨w', hw', rfl⟩
    exact (hEW t w').2 hw'


include hY hdv in
/-- Over a cusp, `e(W_{t'}) = e(W_t) ∩ p⁻¹(W_{t'})` for `c ≤ t ≤ t'`. -/
theorem end_W_eq_inter {s : M} (hs : s ∈ S) (C : CuspChart S s) (hC : C.IsHyperbolicCusp)
    (e : SpreadEnd (univCoverProj S y₀)) (he : e.base = s) {t t' : ℝ} (ht : C.c ≤ t)
    (htt' : t ≤ t') : e (C.W t') = e (C.W t) ∩ univCoverProj S y₀ ⁻¹' C.W t' := by
  obtain ⟨L, -, hLp, -, hLW⟩ := exists_end_lift hY dv hdv hs C hC e he
  rw [hLW t ht, hLW t' (ht.trans htt')]
  ext k
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, lt_of_le_of_lt htt' hw, rfl⟩, ?_⟩
    show ((UniversalCover.proj (Sᶜ : Set M) y₀ (L w) : (Sᶜ : Set M)) : M) ∈ C.W t'
    rw [hLp]; exact (C.E_mem_W_iff t' w).2 hw
  · rintro ⟨⟨w, -, rfl⟩, hk⟩
    refine ⟨w, ?_, rfl⟩
    have : ((UniversalCover.proj (Sᶜ : Set M) y₀ (L w) : (Sᶜ : Set M)) : M) ∈ C.W t' := hk
    rw [hLp] at this
    exact (C.E_mem_W_iff t' w).1 this

include hY hdv in
/-- **An end over a cusp is determined by one component.** -/
theorem end_eq_of_comp_eq {s : M} (hs : s ∈ S) (C : CuspChart S s) (hC : C.IsHyperbolicCusp)
    {e e' : SpreadEnd (univCoverProj S y₀)} (he : e.base = s) (he' : e'.base = s) {t : ℝ}
    (ht : C.c ≤ t) (h : e (C.W t) = e' (C.W t)) : e = e' := by
  refine SpreadEnd.ext_of_isCNbhd (he.trans he'.symm) fun U hU => ?_
  have hU' : IsCNbhd e'.base U := by rw [he', ← he]; exact hU
  obtain ⟨t₁, ht₁, hW⟩ := C.exists_W_subset (hU.isOpen.mem_nhds (he ▸ hU.mem))
  set t' := max t t₁
  have h1 : e (C.W t') = e' (C.W t') := by
    rw [end_W_eq_inter hY dv hdv hs C hC e he ht (le_max_left _ _),
      end_W_eq_inter hY dv hdv hs C hC e' he' ht (le_max_left _ _), h]
  have hWU : C.W t' ⊆ U := (C.W_anti (le_max_right _ _)).trans hW
  have hWe : IsCNbhd e.base (C.W t') := he ▸ C.isCNbhd_W t'
  have hWe' : IsCNbhd e'.base (C.W t') := he' ▸ C.isCNbhd_W t'
  obtain ⟨k, hk⟩ := e.nonempty hWe
  have hk' : k ∈ e' (C.W t') := h1 ▸ hk
  have hU'' : IsCNbhd e'.base U := hU'
  have := (e.isCompOf U hU).eq_of_meets (e'.isCompOf U (he'.trans he.symm ▸ hU))
    ⟨k, e.mono _ _ hWe hU hWU hk, e'.mono _ _ hWe' hU'' hWU hk'⟩
  rw [this]

include hY hdv in
/-- **The basic neighbourhoods of an end over a cusp**: `{e} ∪ ι(e(W_t))`. -/
theorem basicSet_eq_insert {s : M} (hs : s ∈ S) (C : CuspChart S s) (hC : C.IsHyperbolicCusp)
    (hord : SpreadEnd.base ⁻¹' (Sᶜ : Set M) ⊆ range (SpreadEnd.ofPoint (univCoverProj S y₀)))
    (e : SpreadEnd (univCoverProj S y₀)) (he : e.base = s) {t : ℝ} (ht : C.c ≤ t) :
    SpreadEnd.basicSet (univCoverProj S y₀) (C.W t) (e (C.W t)) =
      insert e (SpreadEnd.ofPoint (univCoverProj S y₀) '' e (C.W t)) := by
  have hWe : IsCNbhd e.base (C.W t) := he ▸ C.isCNbhd_W t
  apply Subset.antisymm
  · intro e' he'
    have hb := SpreadEnd.base_mem_of_mem_basicSet he'
    by_cases hbS : e'.base ∈ S
    · have hbs : e'.base = s := by
        have : e'.base ∈ C.W t ∩ S := ⟨hb, hbS⟩
        rw [C.W_inter] at this; exact this
      left
      have hWe' : IsCNbhd e'.base (C.W t) := hbs ▸ C.isCNbhd_W t
      have := SpreadEnd.eq_of_mem_basicSet (e.isCompOf _ hWe) hWe' he'
      exact (end_eq_of_comp_eq hY dv hdv hs C hC he hbs ht this.symm).symm
    · right
      obtain ⟨k, rfl⟩ := hord hbS
      exact ⟨k, (SpreadEnd.ofPoint_mem_basicSet_iff hWe).1 he', rfl⟩
  · rintro e' (rfl | ⟨k, hk, rfl⟩)
    · exact SpreadEnd.mem_basicSet_self e' hWe
    · exact (SpreadEnd.ofPoint_mem_basicSet_iff hWe).2 hk

end Develop

/-- The point `1 ∈ ∂ℍ` of the closed disc. -/
def ClosedDisc.one : ClosedDisc := ⟨1, by simp⟩

@[simp] theorem ClosedDisc.coe_one : ((ClosedDisc.one : ClosedDisc) : ℂ) = 1 := rfl

theorem HypIsom.coe_smul_one (g : HypIsom) : ((g • ClosedDisc.one : ClosedDisc) : ℂ) = g.mob 1 :=
  rfl

theorem HypIsom.norm_smul_one (g : HypIsom) : ‖((g • ClosedDisc.one : ClosedDisc) : ℂ)‖ = 1 := by
  rw [coe_smul_one, ← normSq_eq_one_iff]
  exact g.mob_sphere (by simp)

/-- **The horodisc `g • B(1, 1/t)`**: a point of the disc is in it iff it is `g • cay(w)` with
`Im w > t`. -/
theorem HypIsom.mem_horodisc_iff (g : HypIsom) {t : ℝ} (ht : 0 < t) (y : PoincareDisc) :
    (y : ℂ) ∈ horodisc (g.mob 1) (t⁻¹ * g.lam 1) ↔
      ∃ w : ℂ, ∃ hw : t < w.im, y = g • cayP w (ht.trans hw) := by
  have hy : y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
  conv_lhs => rw [hy]
  rw [g.smul_mem_horodisc_iff (by simp) t⁻¹, ← image_cay_horoball ht]
  constructor
  · rintro ⟨w, hw, hwz⟩
    refine ⟨w, hw, ?_⟩
    rw [hy]; congr 1
    exact Subtype.ext hwz.symm
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [inv_smul_smul]; rfl

/-! ### One-point extensions of open embeddings, and the infinite angle disc -/

/-- Two open embeddings `i : P → X`, `j : P → Y`, extended by points `a ∉ i(P)`, `b ∉ j(P)` whose
neighbourhood filters have matching bases `{a} ∪ i(s_k)`, `{b} ∪ j(s_k)`: the extension
`a ↦ b`, `i(q) ↦ j(q)` is a homeomorphism `{a} ∪ i(P) ≃ {b} ∪ j(P)`. -/
theorem exists_homeomorph_insert {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] {i : P → X} {j : P → Y} (hi : Topology.IsOpenEmbedding i)
    (hj : Topology.IsOpenEmbedding j) {a : X} {b : Y} (ha : a ∉ range i) (hb : b ∉ range j)
    {ι : Type*} {pk : ι → Prop} {sk : ι → Set P}
    (hA : (𝓝 a).HasBasis pk fun k => insert a (i '' sk k))
    (hB : (𝓝 b).HasBasis pk fun k => insert b (j '' sk k)) :
    ∃ h : (insert a (range i) : Set X) ≃ₜ (insert b (range j) : Set Y),
      (h ⟨a, mem_insert _ _⟩ : Y) = b ∧ ∀ q, (h ⟨i q, mem_insert_of_mem _ ⟨q, rfl⟩⟩ : Y) = j q := by
  set A : Set X := insert a (range i)
  set F : A → Y := fun x => if h : (x : X) ∈ range i then j h.choose else b with hF
  have hFi : ∀ (q : P) (hq : i q ∈ A), F ⟨i q, hq⟩ = j q := fun q hq => by
    simp only [hF, dif_pos (mem_range_self q)]
    congr 1
    exact hi.injective (mem_range_self q).choose_spec
  have hFa : F ⟨a, mem_insert _ _⟩ = b := by simp only [hF, dif_neg ha]
  have hcases : ∀ x : A, (x : X) = a ∨ ∃ q, (x : X) = i q := fun x => by
    rcases x.2 with h | ⟨q, hq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, hq.symm⟩
  have hFeq : ∀ (x : A) (q : P), (x : X) = i q → F x = j q := fun x q hxq => by
    have : x = ⟨i q, hxq ▸ x.2⟩ := Subtype.ext hxq
    rw [this, hFi]
  have hFeqa : ∀ x : A, (x : X) = a → F x = b := fun x hxa => by
    have : x = ⟨a, mem_insert _ _⟩ := Subtype.ext hxa
    rw [this, hFa]
  have hAo : IsOpen A := by
    obtain ⟨k, hk, hks⟩ := hA.mem_iff.1 (Filter.univ_mem)
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    rcases hx with rfl | ⟨q, rfl⟩
    · exact Filter.mem_of_superset (hA.mem_of_mem hk)
        (insert_subset_insert (image_subset_range _ _))
    · exact Filter.mem_of_superset (hi.isOpen_range.mem_nhds (mem_range_self q))
        (subset_insert _ _)
  have hcont : Continuous F := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    rw [ContinuousAt, (hAo.isOpenEmbedding_subtypeVal.isInducing.nhds_eq_comap x)]
    intro N hN
    rcases hcases x with hx | ⟨q, hq⟩
    · rw [hFeqa x hx] at hN
      obtain ⟨k, hk, hkN⟩ := hB.mem_iff.1 hN
      refine ⟨insert a (i '' sk k), by rw [hx]; exact hA.mem_of_mem hk, fun x' hx' => hkN ?_⟩
      rcases hx' with h | ⟨q', hq', h⟩
      · rw [hFeqa x' h]; exact mem_insert _ _
      · rw [hFeq x' q' h.symm]; exact mem_insert_of_mem _ ⟨q', hq', rfl⟩
    · rw [hFeq x q hq] at hN
      refine ⟨i '' (j ⁻¹' N), hq ▸ hi.isOpenMap.image_mem_nhds
        (hj.continuous.continuousAt.preimage_mem_nhds hN), fun x' hx' => ?_⟩
      obtain ⟨q', hq', h⟩ := hx'
      show F x' ∈ N
      rw [hFeq x' q' h.symm]; exact hq'
  have hinj : Injective F := by
    intro x x' hxx'
    apply Subtype.ext
    rcases hcases x with hx | ⟨q, hq⟩ <;> rcases hcases x' with hx' | ⟨q', hq'⟩
    · rw [hx, hx']
    · rw [hFeqa x hx, hFeq x' q' hq'] at hxx'
      exact absurd ⟨q', hxx'.symm⟩ hb
    · rw [hFeq x q hq, hFeqa x' hx'] at hxx'
      exact absurd ⟨q, hxx'⟩ hb
    · rw [hFeq x q hq, hFeq x' q' hq'] at hxx'
      rw [hq, hq', hj.injective hxx']
  have hopen : IsOpenMap F := by
    intro O hO
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨x, hxO, rfl⟩
    have hO' : IsOpen ((Subtype.val : A → X) '' O) := hAo.isOpenMap_subtype_val O hO
    rcases hcases x with hx | ⟨q, hq⟩
    · rw [hFeqa x hx]
      obtain ⟨k, hk, hkO⟩ := hA.mem_iff.1 (hO'.mem_nhds ⟨x, hxO, hx⟩)
      refine Filter.mem_of_superset (hB.mem_of_mem hk) ?_
      rintro y (rfl | ⟨q', hq', rfl⟩)
      · exact ⟨x, hxO, hFeqa x hx⟩
      · obtain ⟨x', hx'O, hx'⟩ := hkO (mem_insert_of_mem _ ⟨q', hq', rfl⟩)
        exact ⟨x', hx'O, hFeq x' q' hx'⟩
    · rw [hFeq x q hq]
      have : i ⁻¹' ((Subtype.val : A → X) '' O) ∈ 𝓝 q :=
        hi.continuous.continuousAt.preimage_mem_nhds (hO'.mem_nhds ⟨x, hxO, hq⟩)
      refine Filter.mem_of_superset (hj.isOpenMap.image_mem_nhds this) ?_
      rintro _ ⟨q', hq', rfl⟩
      obtain ⟨x', hx'O, hx'⟩ := hq'
      exact ⟨x', hx'O, hFeq x' q' hx'⟩
  have hemb : Topology.IsOpenEmbedding F :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
  have hrange : range F = insert b (range j) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rcases hcases x with hx | ⟨q, hq⟩
      · rw [hFeqa x hx]; exact mem_insert _ _
      · rw [hFeq x q hq]; exact mem_insert_of_mem _ ⟨q, rfl⟩
    · rintro (rfl | ⟨q, rfl⟩)
      · exact ⟨_, hFa⟩
      · exact ⟨_, hFi q (mem_insert_of_mem _ ⟨q, rfl⟩)⟩
  refine ⟨hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange), ?_, fun q => ?_⟩
  · show F _ = b; exact hFa
  · show F _ = j q; exact hFi q _

/-- The horoball in the infinite angle disc: `w ↦ (r, θ) = (e^{-2π Im w}, Re w)`. -/
def horoD (w : ℂ) : DInfty := DInfty.posEmb ⟨(Real.exp (-(2 * π * w.im)), w.re), Real.exp_pos _⟩

theorem horoD_eq_logChart (w : ℂ) : horoD w = DInfty.logChart (2 * π * I * w) := by
  simp only [horoD, DInfty.logChart]
  congr 1
  apply Subtype.ext
  simp only [logHomeo, Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk]
  apply Prod.ext
  · simp [mul_re, mul_im]
  · simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
    field_simp
    ring

theorem isOpenEmbedding_horoD : Topology.IsOpenEmbedding horoD := by
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have : horoD = DInfty.logChart ∘ (Homeomorph.mulLeft₀ (2 * π * I) hπ) :=
    funext fun w => horoD_eq_logChart w
  rw [this]
  exact DInfty.isOpenEmbedding_logChart.comp (Homeomorph.mulLeft₀ _ hπ).isOpenEmbedding

theorem horoD_r (w : ℂ) : (horoD w).r = CuspChart.ρ w.im := rfl

theorem horoD_ne_apex (w : ℂ) : horoD w ≠ DInfty.apex := by
  intro h
  have := congrArg DInfty.r h
  rw [horoD_r, DInfty.apex_r] at this
  exact (CuspChart.ρ_pos _).ne' this

theorem exists_horoD_eq {p : DInfty} (hp : 0 < p.r) :
    ∃ w : ℂ, horoD w = p ∧ w.im = -(Real.log p.r) / (2 * π) := by
  set y : ℝ := -(Real.log p.r) / (2 * π) with hy
  have him : ((p.θ : ℂ) + (y : ℂ) * I).im = y := by simp
  refine ⟨(p.θ : ℂ) + (y : ℂ) * I, ?_, him⟩
  ext
  · rw [horoD_r, him, CuspChart.ρ]
    rw [show -(2 * π * y) = Real.log p.r by rw [hy]; field_simp]
    exact Real.exp_log hp
  · show ((p.θ : ℂ) + (y : ℂ) * I).re = p.θ
    simp

/-- `{r < ρ(t)} = {apex} ∪ horoD({Im w > t})`. -/
theorem r_lt_eq_insert (t : ℝ) {c : ℝ} (hct : c ≤ t) :
    {p : DInfty | p.r < CuspChart.ρ t} =
      insert DInfty.apex ((fun w : Horoball c => horoD w) '' {w | t < (w : ℂ).im}) := by
  ext p
  constructor
  · intro hp
    rcases p.pos_or_eq_apex with h | rfl
    · right
      obtain ⟨w, rfl, hw⟩ := exists_horoD_eq h
      have hwt : t < w.im := by
        have hp' : (horoD w).r < CuspChart.ρ t := hp
        rw [horoD_r] at hp'
        exact CuspChart.ρ_lt_ρ.1 hp'
      exact ⟨⟨w, lt_of_le_of_lt hct hwt⟩, hwt, rfl⟩
    · left; rfl
  · rintro (rfl | ⟨w, hw, rfl⟩)
    · show DInfty.apex.r < _; rw [DInfty.apex_r]; exact CuspChart.ρ_pos t
    · show (horoD w).r < _; rw [horoD_r]; exact CuspChart.ρ_lt_ρ.2 hw

theorem hasBasis_nhds_apex_ρ (t : ℝ) :
    (𝓝 DInfty.apex).HasBasis (fun t' => t ≤ t') fun t' => {p : DInfty | p.r < CuspChart.ρ t'} := by
  refine DInfty.hasBasis_nhds_apex.to_hasBasis (fun ε hε => ?_) fun t' _ =>
    ⟨_, CuspChart.ρ_pos t', subset_rfl⟩
  set t' := max t (-(Real.log ε) / (2 * π) + 1)
  refine ⟨t', le_max_left _ _, fun p (hp : p.r < CuspChart.ρ t') => show p.r < ε from lt_trans hp ?_⟩
  show Real.exp _ < ε
  rw [← Real.lt_log_iff_exp_lt hε]
  have : -(Real.log ε) / (2 * π) + 1 ≤ t' := le_max_right _ _
  have h' : -(Real.log ε) / (2 * π) < t' := by linarith
  rw [div_lt_iff₀ (by positivity)] at h'
  linarith

/-! ### The developing map of `\widetilde M` -/

section DevelopD

variable {M : Type*} [TopologicalSpace M] {S : Set M} [ChartedSpace PoincareDisc (Sᶜ : Set M)]
  [LocPathConnectedSpace (Sᶜ : Set M)] {y₀ : (Sᶜ : Set M)}
  (hY : SemilocallySimplyConnected (Sᶜ : Set M)) (dv : UniversalCover (Sᶜ : Set M) y₀ ≃ₜ PoincareDisc)
  (hdv : ∀ c : UniversalCover (Sᶜ : Set M) y₀, ∃ g : HypIsom, ∀ᶠ c' in 𝓝 c,
    dv c' = g • chartAt PoincareDisc (UniversalCover.proj (Sᶜ : Set M) y₀ c)
      (UniversalCover.proj (Sᶜ : Set M) y₀ c'))
  (hord : SpreadEnd.base ⁻¹' (Sᶜ : Set M) ⊆ range (SpreadEnd.ofPoint (univCoverProj S y₀)))
  {D : SpreadEnd (univCoverProj S y₀) → ClosedDisc}
  (hDreg : ∀ k, D (SpreadEnd.ofPoint (univCoverProj S y₀) k) = ClosedDisc.ofPD (dv k))

include hY hdv hord hDreg in
/-- The image by `D` of a basic neighbourhood of an end over a cusp: the horodisc `g • B(1, 1/t)`
together with its centre `D(e)`. -/
theorem image_basicSet {s : M} (hs : s ∈ S) (C : CuspChart S s) (hC : C.IsHyperbolicCusp)
    (e : SpreadEnd (univCoverProj S y₀)) (he : e.base = s)
    {L : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀} {g : HypIsom}
    (hLg : ∀ w, dv (L w) = g • C.cayH w) (hLW : ∀ t, C.c ≤ t → e (C.W t) = L '' {w | t < (w : ℂ).im})
    (hDe : D e = g • ClosedDisc.one) {t : ℝ} (ht : C.c ≤ t) :
    D '' SpreadEnd.basicSet (univCoverProj S y₀) (C.W t) (e (C.W t)) =
      {x : ClosedDisc | (x : ℂ) = D e ∨ (x : ℂ) ∈ horodisc (D e) (t⁻¹ * g.lam 1)} := by
  have ht0 : 0 < t := C.c_pos.trans_le ht
  rw [basicSet_eq_insert hY dv hdv hs C hC hord e he ht, image_insert_eq, hLW t ht, hDe,
    HypIsom.coe_smul_one]
  ext x
  constructor
  · intro hx
    rcases hx with rfl | ⟨_, ⟨k, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    · left; rfl
    · right
      show ((D (SpreadEnd.ofPoint _ (L w)) : ClosedDisc) : ℂ) ∈ _
      rw [hDreg, hLg, ClosedDisc.coe_ofPD, (g.mem_horodisc_iff ht0 _)]
      exact ⟨w, hw, rfl⟩
  · rintro (hx | hx)
    · left; exact Subtype.ext (by rw [hx]; rfl)
    · right
      have hxb : (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 :=
        horodisc_subset_ball (mul_pos (inv_pos.2 ht0) (g.lam_pos (by simp))) hx
      have hx' : ((⟨x, hxb⟩ : PoincareDisc) : ℂ) ∈ horodisc (g.mob 1) (t⁻¹ * g.lam 1) := hx
      obtain ⟨w, hw, hwy⟩ := (g.mem_horodisc_iff ht0 _).1 hx'
      refine ⟨SpreadEnd.ofPoint _ (L ⟨w, lt_of_le_of_lt ht hw⟩),
        ⟨L ⟨w, lt_of_le_of_lt ht hw⟩, ⟨⟨w, lt_of_le_of_lt ht hw⟩, hw, rfl⟩, rfl⟩, ?_⟩
      rw [hDreg, hLg]
      apply Subtype.ext
      rw [ClosedDisc.coe_ofPD]
      have := congrArg Subtype.val hwy
      exact this.symm

include hY hdv hord hDreg in
/-- `D` is continuous at an end over a cusp: the horodiscs shrink to their centre. -/
theorem continuousAt_of_cusp {s : M} (hs : s ∈ S) (C : CuspChart S s) (hC : C.IsHyperbolicCusp)
    (e : SpreadEnd (univCoverProj S y₀)) (he : e.base = s)
    {L : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀} {g : HypIsom}
    (hLg : ∀ w, dv (L w) = g • C.cayH w) (hLW : ∀ t, C.c ≤ t → e (C.W t) = L '' {w | t < (w : ℂ).im})
    (hDe : D e = g • ClosedDisc.one) [LocallyConnectedSpace M] : ContinuousAt D e := by
  intro N hN
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.1 hN
  have hlam := g.lam_pos (ξ := 1) (by simp)
  set t := max C.c (2 * g.lam 1 / δ + 1)
  have ht : C.c ≤ t := le_max_left _ _
  have ht0 : 0 < t := C.c_pos.trans_le ht
  have hτ : 2 * (t⁻¹ * g.lam 1) < δ := by
    have h1 : 2 * g.lam 1 / δ < t := by
      have := le_max_right C.c (2 * g.lam 1 / δ + 1); linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [← mul_assoc, mul_comm 2, mul_assoc, inv_mul_lt_iff₀ ht0]
    linarith
  have hWe : IsCNbhd e.base (C.W t) := he ▸ C.isCNbhd_W t
  refine Filter.mem_map.2 (Filter.mem_of_superset ((SpreadEnd.isOpen_basicSet hWe.isOpen _).mem_nhds
    (SpreadEnd.mem_basicSet_self e hWe)) fun e' he' => ?_)
  have hmem : D e' ∈ D '' SpreadEnd.basicSet (univCoverProj S y₀) (C.W t) (e (C.W t)) :=
    mem_image_of_mem D he'
  rw [image_basicSet hY dv hdv hord hDreg hs C hC e he hLg hLW hDe ht] at hmem
  apply hδN
  rw [Metric.mem_ball, Subtype.dist_eq]
  rcases hmem with h | h
  · rw [h, dist_self]; exact hδ
  · have hDe1 : ‖(D e : ℂ)‖ = 1 := by rw [hDe]; exact g.norm_smul_one
    have := horodisc_subset_ball_center hDe1 (mul_pos (inv_pos.2 ht0) hlam) h
    rw [Metric.mem_ball] at this
    linarith


include hY hdv in
/-- Two distinct ends over cusps have disjoint components over small cusp neighbourhoods. -/
theorem exists_disjoint_comp [T2Space M] [LocallyConnectedSpace M] {s s' : M} (hs : s ∈ S)
    (hs' : s' ∈ S) (C : CuspChart S s) (C' : CuspChart S s')
    {e e' : SpreadEnd (univCoverProj S y₀)} (he : e.base = s) (he' : e'.base = s') (hne : e ≠ e') :
    ∃ t t', C.c ≤ t ∧ C'.c ≤ t' ∧ Disjoint (e (C.W t)) (e' (C'.W t')) := by
  by_cases hss : s = s'
  · subst hss
    have : ∃ U, IsCNbhd e.base U ∧ e U ≠ e' U := by
      by_contra h
      push Not at h
      exact hne (SpreadEnd.ext_of_isCNbhd (he.trans he'.symm) h)
    obtain ⟨U, hU, hUne⟩ := this
    have hU' : IsCNbhd e'.base U := by rw [he', ← he]; exact hU
    obtain ⟨t, ht, htU⟩ := C.exists_W_subset (hU.isOpen.mem_nhds (he ▸ hU.mem))
    obtain ⟨t', ht', ht'U⟩ := C'.exists_W_subset (hU.isOpen.mem_nhds (he ▸ hU.mem))
    refine ⟨t, t', ht, ht', ?_⟩
    have hd : Disjoint (e U) (e' U) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      by_contra hne'
      exact hUne ((e.isCompOf U hU).eq_of_meets (e'.isCompOf U hU')
        (nonempty_iff_ne_empty.2 hne'))
    exact hd.mono (e.mono _ _ (he ▸ C.isCNbhd_W t) hU htU)
      (e'.mono _ _ (he' ▸ C'.isCNbhd_W t') hU' ht'U)
  · obtain ⟨U, U', hU, hU', hsU, hsU', hUU'⟩ := t2_separation hss
    obtain ⟨t, ht, htU⟩ := C.exists_W_subset (hU.mem_nhds hsU)
    obtain ⟨t', ht', ht'U⟩ := C'.exists_W_subset (hU'.mem_nhds hsU')
    refine ⟨t, t', ht, ht', ?_⟩
    have h1 : e (C.W t) ⊆ univCoverProj S y₀ ⁻¹' U :=
      (e.subset_preimage (he ▸ C.isCNbhd_W t)).trans (preimage_mono htU)
    have h2 : e' (C'.W t') ⊆ univCoverProj S y₀ ⁻¹' U' :=
      (e'.subset_preimage (he' ▸ C'.isCNbhd_W t')).trans (preimage_mono ht'U)
    exact (hUU'.preimage _).mono h1 h2

/-- The specification of the developing map at the ends over the cusps. -/
def IsCuspDev (dv : UniversalCover (Sᶜ : Set M) y₀ ≃ₜ PoincareDisc)
    (D : SpreadEnd (univCoverProj S y₀) → ClosedDisc) (e : SpreadEnd (univCoverProj S y₀)) : Prop :=
  ∃ C : CuspChart S e.base, C.IsHyperbolicCusp ∧ ∃ L : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀,
    ∃ g : HypIsom, (∀ w, dv (L w) = g • C.cayH w) ∧
      (∀ t, C.c ≤ t → e (C.W t) = L '' {w | t < (w : ℂ).im}) ∧ D e = g • ClosedDisc.one

include hY hdv hord hDreg in
/-- **The developing map of `\widetilde M` is injective.** -/
theorem injective_of_isCuspDev [T2Space M] [LocallyConnectedSpace M]
    (hcusp : ∀ e : SpreadEnd (univCoverProj S y₀), e.base ∈ S → IsCuspDev dv D e) : Injective D := by
  have hofP : Injective (SpreadEnd.ofPoint (univCoverProj S y₀)) := fun a b hab => by
    have h := congrArg D hab
    rw [hDreg, hDreg] at h
    exact dv.injective (ClosedDisc.isOpenEmbedding_ofPD.injective h)
  have hnorm : ∀ e, e.base ∈ S → ‖(D e : ℂ)‖ = 1 := fun e he => by
    obtain ⟨C, -, L, g, -, -, hDe⟩ := hcusp e he
    rw [hDe]; exact g.norm_smul_one
  have hnorm' : ∀ k, ‖(D (SpreadEnd.ofPoint (univCoverProj S y₀) k) : ℂ)‖ < 1 := fun k => by
    rw [hDreg, ClosedDisc.coe_ofPD]; exact mem_ball_zero_iff.1 (dv k).2
  intro e e' hee'
  by_cases he : e.base ∈ S
  · by_cases he' : e'.base ∈ S
    · by_contra hne
      obtain ⟨C, hC, L, g, hLg, hLW, hDe⟩ := hcusp e he
      obtain ⟨C', hC', L', g', hL'g, hL'W, hDe'⟩ := hcusp e' he'
      obtain ⟨t, t', ht, ht', hdisj⟩ := exists_disjoint_comp hY dv hdv he he' C C' rfl rfl hne
      have ht0 : 0 < t := C.c_pos.trans_le ht
      have ht0' : 0 < t' := C'.c_pos.trans_le ht'
      have hξ : g.mob 1 = g'.mob 1 := by
        rw [← HypIsom.coe_smul_one, ← HypIsom.coe_smul_one, ← hDe, ← hDe', hee']
      have hξ1 : ‖g.mob 1‖ = 1 := by rw [← HypIsom.coe_smul_one]; exact g.norm_smul_one
      obtain ⟨z, hz1, hz2⟩ := horodisc_inter_nonempty hξ1
        (mul_pos (inv_pos.2 ht0) (g.lam_pos (ξ := 1) (by simp)))
        (mul_pos (inv_pos.2 ht0') (g'.lam_pos (ξ := 1) (by simp)))
      have hzb : z ∈ Metric.ball (0 : ℂ) 1 :=
        horodisc_subset_ball (mul_pos (inv_pos.2 ht0) (g.lam_pos (ξ := 1) (by simp))) hz1
      set y : PoincareDisc := ⟨z, hzb⟩
      have hz2' : (y : ℂ) ∈ horodisc (g'.mob 1) (t'⁻¹ * g'.lam 1) := by
        rw [← hξ]; exact hz2
      obtain ⟨w, hw, hwy⟩ := (g.mem_horodisc_iff ht0 y).1 hz1
      obtain ⟨w', hw', hw'y⟩ := (g'.mem_horodisc_iff ht0' y).1 hz2'
      have h1 : L ⟨w, lt_of_le_of_lt ht hw⟩ ∈ e (C.W t) := by
        rw [hLW t ht]; exact ⟨_, hw, rfl⟩
      have h2 : L' ⟨w', lt_of_le_of_lt ht' hw'⟩ ∈ e' (C'.W t') := by
        rw [hL'W t' ht']; exact ⟨_, hw', rfl⟩
      have heq : L ⟨w, lt_of_le_of_lt ht hw⟩ = L' ⟨w', lt_of_le_of_lt ht' hw'⟩ := by
        apply dv.injective
        rw [hLg, hL'g]
        exact hwy.symm.trans hw'y
      exact Set.disjoint_left.1 hdisj h1 (heq ▸ h2)
    · obtain ⟨k, rfl⟩ := hord he'
      have := hnorm e he
      rw [hee'] at this
      exact absurd this (hnorm' k).ne
  · obtain ⟨k, rfl⟩ := hord he
    by_cases he' : e'.base ∈ S
    · have := hnorm e' he'
      rw [← hee'] at this
      exact absurd this (hnorm' k).ne
    · obtain ⟨k', rfl⟩ := hord he'
      rw [hDreg, hDreg] at hee'
      rw [dv.injective (ClosedDisc.isOpenEmbedding_ofPD.injective hee')]


/-- The sub-horoball `{Im w > t'}` of `{Im w > t}`. -/
def horoSub (t t' : ℝ) : Set (Horoball t) := {w | t' < (w : ℂ).im}

theorem isOpenEmbedding_horoInc {c t : ℝ} (h : c ≤ t) : Topology.IsOpenEmbedding (horoInc h) := by
  refine ⟨(Topology.IsEmbedding.of_comp_iff
    (Topology.IsEmbedding.subtypeVal (p := fun w : ℂ => c < w.im))).1
    (Topology.IsEmbedding.subtypeVal (p := fun w : ℂ => t < w.im)), ?_⟩
  have : range (horoInc h) = {w : Horoball c | t < (w : ℂ).im} := by
    ext w
    exact ⟨fun ⟨w', hw'⟩ => hw' ▸ w'.2, fun hw => ⟨⟨w, hw⟩, rfl⟩⟩
  rw [this]
  exact isOpen_lt continuous_const (Complex.continuous_im.comp continuous_subtype_val)

include hY hdv hord in
/-- **The basic neighbourhood of an end over a cusp is homeomorphic to `{r < r₀} ⊆ 𝔻_∞`**, the
end going to the apex (`ex:take_closed_unit_disc`, `𝔻_∞` the infinite angle disc of
`ex:quotient_base`). -/
theorem exists_homeomorph_basicSet [LocallyConnectedSpace M]
    (hemb : Topology.IsOpenEmbedding (SpreadEnd.ofPoint (univCoverProj S y₀)))
    {s : M} (hs : s ∈ S) (C : CuspChart S s) (hC : C.IsHyperbolicCusp)
    (e : SpreadEnd (univCoverProj S y₀)) (he : e.base = s)
    {L : Horoball C.c → UniversalCover (Sᶜ : Set M) y₀} {g : HypIsom}
    (hLg : ∀ w, dv (L w) = g • C.cayH w) (hLW : ∀ t, C.c ≤ t → e (C.W t) = L '' {w | t < (w : ℂ).im})
    {t : ℝ} (ht : C.c ≤ t) :
    ∃ h : (SpreadEnd.basicSet (univCoverProj S y₀) (C.W t) (e (C.W t)) :
        Set (SpreadEnd (univCoverProj S y₀))) ≃ₜ {p : DInfty | p.r < CuspChart.ρ t},
      (h ⟨e, SpreadEnd.mem_basicSet_self e (he ▸ C.isCNbhd_W t)⟩ : DInfty) = DInfty.apex := by
  set i : Horoball t → DInfty := fun w => horoD w
  set j : Horoball t → SpreadEnd (univCoverProj S y₀) :=
    fun w => SpreadEnd.ofPoint (univCoverProj S y₀) (L (horoInc ht w))
  have hi : Topology.IsOpenEmbedding i :=
    isOpenEmbedding_horoD.comp (isOpen_horoball t).isOpenEmbedding_subtypeVal
  have hj : Topology.IsOpenEmbedding j :=
    hemb.comp ((isOpenEmbedding_cusp_lift dv C hLg).comp (isOpenEmbedding_horoInc ht))
  have ha : DInfty.apex ∉ range i := by
    rintro ⟨w, hw⟩; exact horoD_ne_apex w hw
  have hb : e ∉ range j := by
    rintro ⟨w, hw⟩
    have h1 : ((UniversalCover.proj (Sᶜ : Set M) y₀ (L (horoInc ht w)) : (Sᶜ : Set M)) : M) = s :=
      (congrArg SpreadEnd.base hw).trans he
    exact (UniversalCover.proj (Sᶜ : Set M) y₀ (L (horoInc ht w))).2 (by rw [h1]; exact hs)
  have hiS : ∀ t', t ≤ t' → {p : DInfty | p.r < CuspChart.ρ t'} = insert DInfty.apex (i '' horoSub t t') :=
    fun t' ht' => r_lt_eq_insert t' ht'
  have hjS : ∀ t', t ≤ t' →
      SpreadEnd.basicSet (univCoverProj S y₀) (C.W t') (e (C.W t')) = insert e (j '' horoSub t t') := by
    intro t' ht'
    rw [basicSet_eq_insert hY dv hdv hs C hC hord e he (ht.trans ht'), hLW t' (ht.trans ht')]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨⟨w, lt_of_le_of_lt ht' hw⟩, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, ⟨horoInc ht w, hw, rfl⟩, rfl⟩
  have hA : (𝓝 DInfty.apex).HasBasis (fun t' => t ≤ t') fun t' => insert DInfty.apex (i '' horoSub t t') :=
    (hasBasis_nhds_apex_ρ t).congr (fun _ => Iff.rfl) fun t' ht' => hiS t' ht'
  have hB : (𝓝 e).HasBasis (fun t' => t ≤ t') fun t' => insert e (j '' horoSub t t') := by
    refine ((SpreadEnd.hasBasis_nhds e).to_hasBasis (fun W' hW' => ?_) fun t' ht' =>
      ⟨C.W t', he ▸ C.isCNbhd_W t', subset_rfl⟩).congr (fun _ => Iff.rfl) fun t' ht' => hjS t' ht'
    obtain ⟨t₁, ht₁, htW⟩ := C.exists_W_subset (hW'.isOpen.mem_nhds (he ▸ hW'.mem))
    refine ⟨max t t₁, le_max_left _ _, SpreadEnd.basicSet_mono e (he ▸ C.isCNbhd_W _) hW'
      ((C.W_anti (le_max_right _ _)).trans htW)⟩
  obtain ⟨h, hha, -⟩ := exists_homeomorph_insert hi hj ha hb hA hB
  have hU : SpreadEnd.basicSet (univCoverProj S y₀) (C.W t) (e (C.W t)) = insert e (range j) := by
    rw [hjS t le_rfl, ← image_univ]
    congr 2
    ext w; exact ⟨fun _ => trivial, fun _ => w.2⟩
  have hV : insert DInfty.apex (range i) = {p : DInfty | p.r < CuspChart.ρ t} := by
    rw [hiS t le_rfl, ← image_univ]
    congr 2
    ext w; exact ⟨fun _ => w.2, fun _ => trivial⟩
  refine ⟨(Homeomorph.setCongr hU).trans (h.symm.trans (Homeomorph.setCongr hV)), ?_⟩
  have : (Homeomorph.setCongr hU) ⟨e, SpreadEnd.mem_basicSet_self e (he ▸ C.isCNbhd_W t)⟩ =
      ⟨e, mem_insert _ _⟩ := rfl
  rw [Homeomorph.trans_apply, this, Homeomorph.trans_apply]
  have h2 : h.symm ⟨e, mem_insert _ _⟩ = ⟨DInfty.apex, mem_insert _ _⟩ := by
    rw [Homeomorph.symm_apply_eq]; exact Subtype.ext hha.symm
  rw [h2]
  rfl

end DevelopD

/-! ### `ex:take_closed_unit_disc`: the developing map of `\widetilde M` -/

section Main

variable {M : Type*} [TopologicalSpace M] {S : Set M} [ChartedSpace PoincareDisc (Sᶜ : Set M)]
  [T2Space M] [LocPathConnectedSpace M] [FirstCountableTopology M] [ConnectedSpace M]

/-- **The developing map of `\widetilde M^S`** (the maximal covering of `M` possibly branched
over the cusps): it exists, is injective, sends the ends over the cusps to `∂ℍ`, and maps small
neighbourhoods of such an end onto a horodisc together with its centre. -/
theorem IsCuspedHyperbolic.exists_developing (H : IsCuspedHyperbolic M S) (y₀ : (Sᶜ : Set M)) :
    letI := H.singularStructure
    ∃ D : MaxBranchedCover S y₀ → ClosedDisc,
      IsDevelopingMapOf HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base D ∧ Injective D ∧
      ∀ e : MaxBranchedCover S y₀, e.base ∈ S → ‖(D e : ℂ)‖ = 1 ∧
        ∀ N ∈ 𝓝 e, ∃ U : Set (MaxBranchedCover S y₀), IsOpen U ∧ ∃ heU : e ∈ U, U ⊆ N ∧
          (∃ r₀ > 0, ∃ h : U ≃ₜ {p : DInfty | p.r < r₀}, (h ⟨e, heU⟩ : DInfty) = DInfty.apex) ∧
          ∃ τ > 0, D '' U = {x : ClosedDisc | (x : ℂ) = D e ∨ (x : ℂ) ∈ horodisc (D e) τ} := by
  letI := H.singularStructure
  haveI := H.hasGroupoid
  have hS : IsSkeletal S := H.isPortly_compl
  have hSing := H.sing_eq
  have hY : SemilocallySimplyConnected (Sᶜ : Set M) :=
    semilocallySimplyConnected_compl_of_sing_subset isLocallyUnloopable_closedDisc H.isClosed
      hSing.le
  haveI : LocPathConnectedSpace (Sᶜ : Set M) := H.isClosed.isOpen_compl.locPathConnectedSpace
  obtain ⟨hcomp, hbc, hpb, hpre, hl, hsp⟩ := maxBranched_basic hS hY y₀
  haveI := hl
  haveI : T2Space (UniversalCover (Sᶜ : Set M) y₀) :=
    t2Space_of_isCoveringMap (UniversalCover.isCoveringMap_proj (y₀ := y₀) hY)
  have hemb : Topology.IsOpenEmbedding (SpreadEnd.ofPoint (univCoverProj S y₀)) :=
    ⟨SpreadEnd.isEmbedding_ofPoint hsp, hcomp.isPortly.isOpen⟩
  have hord : SpreadEnd.base ⁻¹' (Sᶜ : Set M) ⊆ range (SpreadEnd.ofPoint (univCoverProj S y₀)) :=
    hpre.le
  -- the developing map of the complete surface
  obtain ⟨dev, -, hdev, -, -⟩ := developing_theorem (G := HypIsom) (X := PoincareDisc) hY y₀
  obtain ⟨dv, hdvdev⟩ := IsCompleteHyperbolic.exists_homeomorph H.complete hY y₀ dev hdev
  have hdv : ∀ c : UniversalCover (Sᶜ : Set M) y₀, ∃ g : HypIsom, ∀ᶠ c' in 𝓝 c,
      dv c' = g • chartAt PoincareDisc (UniversalCover.proj (Sᶜ : Set M) y₀ c)
        (UniversalCover.proj (Sᶜ : Set M) y₀ c') := by
    intro c
    letI := coverChartedSpace PoincareDisc hY y₀
    obtain ⟨g, hg⟩ := (isGXMorphism_iff_model.1 hdev).2 c
    refine ⟨g, hg.mono fun c' h => ?_⟩
    rw [hdvdev, h, pullback_chartAt_apply]
  -- the data at the cusps
  choose Cs hCs using H.cusp
  have hdata : ∀ (e : SpreadEnd (univCoverProj S y₀)) (h : e.base ∈ S), ∃ g : HypIsom,
      ∃ L : Horoball (Cs e.base h).c → UniversalCover (Sᶜ : Set M) y₀,
        (∀ w, dv (L w) = g • (Cs e.base h).cayH w) ∧
        ∀ t, (Cs e.base h).c ≤ t → e ((Cs e.base h).W t) = L '' {w | t < (w : ℂ).im} := by
    intro e h
    obtain ⟨L, -, -, ⟨g, hg⟩, hLW⟩ := exists_end_lift hY dv hdv h (Cs e.base h) (hCs _ h) e rfl
    exact ⟨g, L, hg, hLW⟩
  choose gE LE hLg hLW using hdata
  have hreg : ∀ e : SpreadEnd (univCoverProj S y₀), e.base ∉ S →
      ∃ k, SpreadEnd.ofPoint (univCoverProj S y₀) k = e := fun e h => hord h
  choose kk hkk using hreg
  set D : SpreadEnd (univCoverProj S y₀) → ClosedDisc := fun e =>
    if h : e.base ∈ S then gE e h • ClosedDisc.one else ClosedDisc.ofPD (dv (kk e h)) with hD
  have hofP : Injective (SpreadEnd.ofPoint (univCoverProj S y₀)) := hemb.injective
  have hDreg : ∀ k, D (SpreadEnd.ofPoint (univCoverProj S y₀) k) = ClosedDisc.ofPD (dv k) := by
    intro k
    have hk : (SpreadEnd.ofPoint (univCoverProj S y₀) k).base ∉ S :=
      (UniversalCover.proj (Sᶜ : Set M) y₀ k).2
    simp only [hD, dif_neg hk]
    rw [hofP (hkk _ hk)]
  have hDe : ∀ e (h : e.base ∈ S), D e = gE e h • ClosedDisc.one := fun e h => by
    simp only [hD, dif_pos h]
  have hcusp : ∀ e : SpreadEnd (univCoverProj S y₀), e.base ∈ S → IsCuspDev dv D e :=
    fun e h => ⟨Cs e.base h, hCs _ h, LE e h, gE e h, hLg e h, hLW e h, hDe e h⟩
  -- continuity
  have hDc : Continuous D := by
    refine continuous_iff_continuousAt.2 fun e => ?_
    by_cases h : e.base ∈ S
    · exact continuousAt_of_cusp hY dv hdv hord hDreg h (Cs e.base h) (hCs _ h) e rfl
        (hLg e h) (hLW e h) (hDe e h)
    · obtain ⟨k, rfl⟩ := hord h
      have : D ∘ SpreadEnd.ofPoint (univCoverProj S y₀) = ClosedDisc.ofPD ∘ dv := funext hDreg
      rw [← hemb.continuousAt_iff, this]
      exact (ClosedDisc.isOpenEmbedding_ofPD.continuous.comp dv.continuous).continuousAt
  -- regularity on the regular part
  set B := aeAtlas HypIsom ClosedDisc M
  have hBm : IsMaximalAEAtlas HypIsom B := isMaximalAEAtlas_aeAtlas HypIsom ClosedDisc M
  set R : Set (MaxBranchedCover S y₀) := SpreadEnd.base ⁻¹' (Sᶜ : Set M) with hRdef
  have hRp : IsPortly R := hbc.isPortly_preimage hS
  have hAt := aePullback_spec_of_isAELocalHomeomorph hBm.1 hbc.isSpread.continuous
    (hbc.isAELocalHomeomorph hBm.1)
  have hRegB : (Sᶜ : Set M) = support B := by
    rw [← hSing, Sing, compl_compl]; rfl
  have hordβ : (Sᶜ : Set M) ⊆ ordY (SpreadEnd.base : MaxBranchedCover S y₀ → M) :=
    fun y hy => by by_contra hn; exact hy (hpb hn)
  have hRsupp : R ⊆ support (aePullback HypIsom B
      (SpreadEnd.base : MaxBranchedCover S y₀ → M)) := fun w hw =>
    hAt.2.mem_support_of_isLocalHomeomorphOn' hAt.1 hBm.1 (by rw [← hRegB]; exact hw)
      (hbc.ordX_subset_isLocalHomeomorphOn (hordβ hw))
  have hregβ := hAt.2.regLocusOf_eq hAt.1.1 hBm.1
  have hβR := (isRegularOn_regLocusOf (G := HypIsom) _ B
    (SpreadEnd.base : MaxBranchedCover S y₀ → M)).mono
    (fun w hw => by rw [hregβ]; exact ⟨hRsupp hw, by rw [← hRegB]; exact hw⟩) hRp.isOpen
  have hDR' : IsRegularOn HypIsom (aePullback HypIsom B
      (SpreadEnd.base : MaxBranchedCover S y₀ → M)) (gxModelAtlas HypIsom ClosedDisc) D R := by
    refine isRegularOn_model_of_eventually_comp hAt.1.1.1 hβR fun w hw => ?_
    obtain ⟨k, rfl⟩ := hord hw
    refine ⟨liftChart H.isClosed (chartAt PoincareDisc (UniversalCover.proj (Sᶜ : Set M) y₀ k)),
      H.cuspedAtlas_subset ⟨_, rfl⟩, mem_liftChart_source _ _, ?_⟩
    obtain ⟨g, hg⟩ := hdv k
    refine ⟨g, ?_⟩
    rw [← hemb.map_nhds_eq k]
    refine Filter.eventually_map.2 (hg.mono fun c' h => ?_)
    rw [hDreg, h]
    show _ = g • liftChart H.isClosed _ ((UniversalCover.proj (Sᶜ : Set M) y₀ c' : (Sᶜ : Set M)) : M)
    rw [liftChart_apply, HypIsom.smul_ofPD]
  have hDdev : IsDevelopingMapOf HypIsom B SpreadEnd.base D :=
    (isAEMorphismOf_iff (isMaximalAEAtlas_gxModelAtlas (G := HypIsom) (X := ClosedDisc)).1).2
      ⟨hDc, R, hRp, hDR'⟩
  refine ⟨D, hDdev, injective_of_isCuspDev hY dv hdv hord hDreg hcusp, fun e h => ⟨?_, ?_⟩⟩
  · rw [hDe e h]; exact (gE e h).norm_smul_one
  · intro N hN
    obtain ⟨W', hW', hW'N⟩ := (SpreadEnd.hasBasis_nhds e).mem_iff.1 hN
    obtain ⟨t, ht, htW⟩ := (Cs e.base h).exists_W_subset (hW'.isOpen.mem_nhds hW'.mem)
    have hWe : IsCNbhd e.base ((Cs e.base h).W t) := (Cs e.base h).isCNbhd_W t
    obtain ⟨hh, hhe⟩ := exists_homeomorph_basicSet hY dv hdv hord hemb h (Cs e.base h) (hCs _ h) e
      rfl (hLg e h) (hLW e h) ht
    refine ⟨_, SpreadEnd.isOpen_basicSet hWe.isOpen _, SpreadEnd.mem_basicSet_self e hWe,
      (SpreadEnd.basicSet_mono e hWe hW' htW).trans hW'N,
      ⟨CuspChart.ρ t, CuspChart.ρ_pos t, hh, hhe⟩, (t⁻¹ * (gE e h).lam 1),
      mul_pos (inv_pos.2 ((Cs e.base h).c_pos.trans_le ht)) ((gE e h).lam_pos (by simp)), ?_⟩
    exact image_basicSet hY dv hdv hord hDreg h (Cs e.base h) (hCs _ h) e rfl (hLg e h)
      (hLW e h) (hDe e h) ht


/-- The horodisc together with its centre, as a subset of the closed disc. -/
def horoSet (ξ : ℂ) (τ : ℝ) : Set ClosedDisc := {x | (x : ℂ) = ξ ∨ (x : ℂ) ∈ horodisc ξ τ}

/-- An isometry maps a horodisc with its centre onto a horodisc with its centre. -/
theorem HypIsom.image_horoSet (g : HypIsom) (ξ : ClosedDisc) (hξ : ‖(ξ : ℂ)‖ = 1) {τ : ℝ}
    (hτ : 0 < τ) :
    (fun x => g • x) '' horoSet ξ τ = horoSet (g • ξ : ClosedDisc) (τ * g.lam ξ) := by
  have hξ' : normSq (ξ : ℂ) = 1 := normSq_eq_one_iff.2 hξ
  have hball : ∀ x : ClosedDisc, (x : ℂ) ∈ horodisc (ξ : ℂ) τ → normSq (x : ℂ) < 1 :=
    fun x hx => normSq_lt_one_iff.2 (horodisc_subset_ball hτ hx)
  ext y
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · left; rw [Subtype.ext hx]
    · right
      rw [HypIsom.coe_smul_closedDisc, HypIsom.coe_smul_closedDisc]
      exact (g.mob_mem_horodisc_iff hξ' τ (hball x hx)).2 hx
  · rintro (hy | hy)
    · refine ⟨ξ, Or.inl rfl, Subtype.ext hy.symm⟩
    · have hlm := g.lam_pos hξ'.le
      have hyb : normSq (y : ℂ) < 1 :=
        normSq_lt_one_iff.2 (horodisc_subset_ball (mul_pos hτ hlm) hy)
      refine ⟨g⁻¹ • y, Or.inr ?_, smul_inv_smul g y⟩
      have hx1 : normSq ((g⁻¹ • y : ClosedDisc) : ℂ) < 1 := by
        rw [HypIsom.coe_smul_closedDisc]; exact (g⁻¹).mob_ball hyb
      refine (g.mob_mem_horodisc_iff hξ' τ hx1).1 ?_
      have : g.mob ((g⁻¹ • y : ClosedDisc) : ℂ) = (y : ℂ) := by
        rw [← HypIsom.coe_smul_closedDisc, smul_inv_smul]
      rw [this]; exact hy

/-- **The last sentence of `ex:take_closed_unit_disc`**: a horodisc together with its centre is not
open in the closed disc `X` (from `GX.not_isOpen_horodisc_insert`). -/
theorem not_isOpen_horoSet {ξ : ℂ} (hξ : ‖ξ‖ = 1) {τ : ℝ} (hτ : 0 < τ) :
    ¬ IsOpen (horoSet ξ τ) := by
  have h := not_isOpen_horodisc_insert hξ (r := τ / (1 + τ)) (by
    rw [div_lt_one (by linarith)]; linarith)
  unfold horoSet
  rw [horodisc_eq_ball hξ hτ]
  exact h

/-- **A point with horodisc neighbourhoods is singular**: if `x` has arbitrarily small open
neighbourhoods `U ≅ {r < r₀} ⊆ 𝔻_∞` (`x` to the apex) whose image by an a.e. morphism `D` into
the model is not open, no chart of the atlas contains `x` — near `x` a chart `φ` would be
`g • D`'s inverse partner, `D = g • φ` on the connected `U ∖ {x}` and, by density, on `U`, and
`φ` is open. -/
theorem notMem_support_of_horo_nbhd {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    {A : Set (OpenPartialHomeomorph Y ClosedDisc)} {D : Y → ClosedDisc}
    (hD : IsAEMorphismOf HypIsom A (gxModelAtlas HypIsom ClosedDisc) D) {x : Y}
    (hloc : ∀ N ∈ 𝓝 x, ∃ U : Set Y, IsOpen U ∧ ∃ hxU : x ∈ U, U ⊆ N ∧
      (∃ r₀ > 0, ∃ h : U ≃ₜ {p : DInfty | p.r < r₀}, (h ⟨x, hxU⟩ : DInfty) = DInfty.apex) ∧
      ¬ IsOpen (D '' U)) : x ∉ support A := by
  intro hxA
  obtain ⟨φ, hφ, hxφ⟩ := mem_support.1 hxA
  obtain ⟨Ur, -, hUr, -, -, -, hreg⟩ := hD.exists_isRegularOn
  -- a punctured neighbourhood has a point
  have hpunct : ∀ N ∈ 𝓝 x, ∃ U : Set Y, IsOpen U ∧ x ∈ U ∧ U ⊆ N ∧ (U \ {x}).Nonempty := by
    intro N hN
    obtain ⟨U, hU, hxU, hUN, ⟨r₀, hr₀, h, hhx⟩, -⟩ := hloc N hN
    refine ⟨U, hU, hxU, hUN, ?_⟩
    have hv : DInfty.posEmb ⟨(r₀ / 2, 0), by positivity⟩ ∈ {p : DInfty | p.r < r₀} := by
      show r₀ / 2 < r₀; linarith
    refine ⟨(h.symm ⟨_, hv⟩ : Y), (h.symm ⟨_, hv⟩).2, fun hx => ?_⟩
    have h1 : h.symm ⟨_, hv⟩ = ⟨x, hxU⟩ := Subtype.ext hx
    have h2 := congrArg (fun v => ((h v : {p : DInfty | p.r < r₀}) : DInfty).r) h1
    simp only [Homeomorph.apply_symm_apply, hhx, DInfty.apex_r, DInfty.posEmb_r] at h2
    linarith
  obtain ⟨U, hU, hxU, hUφ, ⟨r₀, hr₀, h, hhx⟩, hno⟩ := hloc _ (φ.open_source.mem_nhds hxφ)
  set P : Set Y := U \ {x} with hPdef
  have hPo : IsOpen P := hU.sdiff isClosed_singleton
  have hPeq : P = (fun v => (h.symm v : Y)) '' {v : {p : DInfty | p.r < r₀} | 0 < (v : DInfty).r} := by
    ext y
    constructor
    · rintro ⟨hyU, hyx⟩
      refine ⟨h ⟨y, hyU⟩, ?_, by simp only [Homeomorph.symm_apply_apply]⟩
      rcases ((h ⟨y, hyU⟩ : {p : DInfty | p.r < r₀}) : DInfty).pos_or_eq_apex with hp | hp
      · exact hp
      · exfalso
        apply hyx
        have : h ⟨y, hyU⟩ = h ⟨x, hxU⟩ := Subtype.ext (by rw [hhx]; exact hp)
        exact congrArg Subtype.val (h.injective this)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(h.symm v).2, fun hx => ?_⟩
      have h1 : h.symm v = ⟨x, hxU⟩ := Subtype.ext hx
      have h2 : h (h.symm v) = h ⟨x, hxU⟩ := by rw [h1]
      rw [Homeomorph.apply_symm_apply] at h2
      have h3 : (v : DInfty) = DInfty.apex := by rw [h2]; exact hhx
      have hv' : 0 < (v : DInfty).r := hv
      rw [h3, DInfty.apex_r] at hv'
      exact lt_irrefl _ hv'
  have hPc : IsPreconnected P := by
    rw [hPeq]
    have hS : IsPreconnected {v : {p : DInfty | p.r < r₀} | 0 < (v : DInfty).r} := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
      convert DInfty.isPreconnected_pos_r_lt r₀ using 1
      ext p
      constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨hv, v.2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨p, h2⟩, h1, rfl⟩
    exact hS.image _ (continuous_subtype_val.comp h.symm.continuous).continuousOn
  have hQc : IsPreconnected (P ∩ Ur) := hUr.isPreconnected_inter hPo hPc
  have hloc' : ∀ y ∈ P ∩ Ur, ∃ g : HypIsom, ∀ᶠ y' in 𝓝 y, D y' = g • φ y' :=
    fun y hy => hreg.eventually_eq_smul_model hy.2 hφ (hUφ hy.1.1)
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected hQc (fun y hy => hUφ hy.1.1) hloc'
  have hcl : U ⊆ closure (P ∩ Ur) := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      refine mem_closure_iff_nhds.2 fun N hN => ?_
      obtain ⟨U', hU', -, hU'N, ⟨z, hz⟩⟩ := hpunct (N ∩ U) (Filter.inter_mem hN (hU.mem_nhds hxU))
      obtain ⟨w, hw1, hw2⟩ := hUr.dense.inter_open_nonempty (U' \ {y}) (hU'.sdiff isClosed_singleton)
        ⟨z, hz⟩
      exact ⟨w, (hU'N hw1.1).1, ⟨(hU'N hw1.1).2, hw1.2⟩, hw2⟩
    · exact hUr.dense.open_subset_closure_inter hPo ⟨hy, hyx⟩
  have heq : EqOn D (fun y => g • φ y) U :=
    EqOn.of_subset_closure hg hD.continuous.continuousOn
      ((φ.continuousOn.mono hUφ).const_smul g) (inter_subset_left.trans sdiff_subset) hcl
  apply hno
  rw [heq.image_eq, show (fun y => g • φ y) = (fun z => g • z) ∘ φ from rfl, image_comp]
  exact (Homeomorph.smul g).isOpenMap _ (φ.isOpen_image_of_subset_source hU hUφ)

/-- The developing maps of `\widetilde M^S`, read for an arbitrary `T = S` (to state the example
with `sing(M)`, which is `S` only propositionally). -/
theorem IsCuspedHyperbolic.exists_developing' (H : IsCuspedHyperbolic M S) (T : Set M)
    (hT : T = S) (y₀ : (Tᶜ : Set M)) :
    letI := H.singularStructure
    ∃ D : MaxBranchedCover T y₀ → ClosedDisc,
      IsDevelopingMapOf HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base D ∧ Injective D ∧
      ∀ e : MaxBranchedCover T y₀, e.base ∈ T → ‖(D e : ℂ)‖ = 1 ∧
        ∀ N ∈ 𝓝 e, ∃ U : Set (MaxBranchedCover T y₀), IsOpen U ∧ ∃ heU : e ∈ U, U ⊆ N ∧
          (∃ r₀ > 0, ∃ h : U ≃ₜ {p : DInfty | p.r < r₀}, (h ⟨e, heU⟩ : DInfty) = DInfty.apex) ∧
          ∃ τ > 0, D '' U = horoSet (D e) τ := by
  subst hT
  exact H.exists_developing y₀

variable (M S) in
/-- **`ex:take_closed_unit_disc`** (`RamcovGX.tex:1877`, DEC-71). `X` the closed unit disc, the open
disc the Poincaré disc `ℍ`, `G = Isom(ℍ)` acting on `X` by homeomorphisms (`(G,X)` analytical,
`X` locally unloopable); `M` with `S ⊆ M` finite and `M ∖ S` a complete hyperbolic surface with
a cusp at every point of `S` (`GX.IsCuspedHyperbolic`, the reading of SCOPE (b)). Then: `M` is a
singular `(G,X)`-manifold with `sing(M) = S`; it is **tamely singular**; every developing map
`\widetilde M → X` (one exists) is **injective**; and every singular point `x` of
`\widetilde M` has arbitrarily small open neighbourhoods `U` **homeomorphic to `{r < r₀} ⊆ 𝔻_∞`**
(`x` to the apex) with `D(U)` **a horodisc centred at `D(x) ∈ ∂ℍ`** (with its centre), **not open
in `X`**. -/
theorem take_closed_unit_disc (H : IsCuspedHyperbolic M S) :
    letI := H.singularStructure
    Sing HypIsom ClosedDisc M = S ∧ IsTame HypIsom ClosedDisc M ∧
    ∀ y₀ : ((Sing HypIsom ClosedDisc M)ᶜ : Set M),
      (∃ D : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀ → ClosedDisc,
        IsDevelopingMapOf HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base D) ∧
      (∀ x : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀,
        x ∉ support (aePullback HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base) ↔
          x.base ∈ Sing HypIsom ClosedDisc M) ∧
      ∀ D : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀ → ClosedDisc,
        IsDevelopingMapOf HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base D →
        Injective D ∧ ∀ x : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀,
          x ∉ support (aePullback HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base) →
          ‖(D x : ℂ)‖ = 1 ∧
          ∀ N ∈ 𝓝 x, ∃ U : Set (MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀), IsOpen U ∧
            ∃ hxU : x ∈ U, U ⊆ N ∧
            (∃ r₀ > 0, ∃ h : U ≃ₜ {p : DInfty | p.r < r₀}, (h ⟨x, hxU⟩ : DInfty) = DInfty.apex) ∧
            ∃ τ > 0, D '' U = horoSet (D x) τ ∧ ¬ IsOpen (D '' U) := by
  letI := H.singularStructure
  have hSing := H.sing_eq
  refine ⟨hSing, ?_, fun y₀ => ?_⟩
  · -- tameness, from the developing map of `\widetilde M^S`
    have hS : IsSkeletal S := H.isPortly_compl
    obtain ⟨y₀⟩ := (nonempty_compl_of_isSkeletal hS).to_subtype
    have hY : SemilocallySimplyConnected (Sᶜ : Set M) :=
      semilocallySimplyConnected_compl_of_sing_subset isLocallyUnloopable_closedDisc H.isClosed
        hSing.le
    obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hY y₀
    haveI := hl
    obtain ⟨D, hD, -⟩ := H.exists_developing y₀
    exact isTame_of_isDevelopingMapOf isLocallyUnloopable_closedDisc hbc hD
  · obtain ⟨D₀, hD₀, hinj, hloc⟩ := H.exists_developing' _ hSing y₀
    have hS : IsSkeletal (Sing HypIsom ClosedDisc M) := isSkeletal_sing HypIsom ClosedDisc M
    have hY : SemilocallySimplyConnected ((Sing HypIsom ClosedDisc M)ᶜ : Set M) :=
      semilocallySimplyConnected_compl_of_sing_subset isLocallyUnloopable_closedDisc
        (isClosed_sing HypIsom ClosedDisc M) subset_rfl
    obtain ⟨-, hbc, hpb, -, hl, -⟩ := maxBranched_basic hS hY y₀
    haveI := hl
    -- the singular points of `\widetilde M` are the points over `sing(M)`
    have hsingM : ∀ x : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀,
        x ∉ support (aePullback HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base) ↔
          x.base ∈ Sing HypIsom ClosedDisc M := by
      intro x
      set B := aeAtlas HypIsom ClosedDisc M
      have hBm : IsMaximalAEAtlas HypIsom B := isMaximalAEAtlas_aeAtlas HypIsom ClosedDisc M
      have hAt := aePullback_spec_of_isAELocalHomeomorph hBm.1 hbc.isSpread.continuous
        (hbc.isAELocalHomeomorph hBm.1)
      constructor
      · intro hx
        by_contra hxS
        apply hx
        have hord : x.base ∈ ordY (SpreadEnd.base : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀ → M) := by
          by_contra hn; exact hxS (hpb hn)
        exact hAt.2.mem_support_of_isLocalHomeomorphOn' hAt.1 hBm.1
          (by by_contra h; exact hxS h)
          (hbc.ordX_subset_isLocalHomeomorphOn hord)
      · intro hx
        refine notMem_support_of_horo_nbhd hD₀ fun N hN => ?_
        obtain ⟨-, h2⟩ := hloc x hx
        obtain ⟨U, hU, hxU, hUN, hhom, τ, hτ, himg⟩ := h2 N hN
        refine ⟨U, hU, hxU, hUN, hhom, ?_⟩
        rw [himg]
        exact not_isOpen_horoSet (hloc x hx).1 hτ
    refine ⟨⟨D₀, hD₀⟩, hsingM, fun D hD => ?_⟩
    haveI := hbc.connectedSpace_source
    obtain ⟨g, hg, -⟩ := aeMorphism_model_unique hD hD₀
    have hDg : D = fun x => g • D₀ x := funext hg
    refine ⟨?_, fun x hx' => ?_⟩
    · rw [hDg]; exact (MulAction.injective g).comp hinj
    · have hx : x.base ∈ Sing HypIsom ClosedDisc M := (hsingM x).1 hx'
      obtain ⟨h1, h2⟩ := hloc x hx
      have hn : normSq ((D₀ x : ClosedDisc) : ℂ) = 1 := normSq_eq_one_iff.2 h1
      have hDx : ‖(D x : ℂ)‖ = 1 := by
        rw [hg, HypIsom.coe_smul_closedDisc, ← normSq_eq_one_iff]; exact g.mob_sphere hn
      refine ⟨hDx, fun N hN => ?_⟩
      obtain ⟨U, hU, hxU, hUN, hhom, τ, hτ, himg⟩ := h2 N hN
      have himg' : D '' U = horoSet (D x) (τ * g.lam (D₀ x)) := by
        rw [hDg, show (fun x => g • D₀ x) = (fun y => g • y) ∘ D₀ from rfl, image_comp, himg,
          g.image_horoSet _ h1 hτ]
        rfl
      refine ⟨U, hU, hxU, hUN, hhom, τ * g.lam (D₀ x), mul_pos hτ (g.lam_pos hn.le), himg', ?_⟩
      rw [himg']
      exact not_isOpen_horoSet hDx (mul_pos hτ (g.lam_pos hn.le))

end Main

/-! ### DEC-81: the metric geometry of `ℍ` -/

theorem continuous_toUHP : Continuous toUHP := by
  refine Continuous.upperHalfPlaneMk ?_ _
  refine Continuous.div (continuous_const.mul (continuous_const.add continuous_subtype_val))
    (continuous_const.sub continuous_subtype_val) fun z => ?_
  exact one_sub_ne_zero_of_normSq_lt z.normSq_lt

/-- The Cayley transform `ℍ → 𝔻`. -/
def ofUHP (w : ℍ) : PoincareDisc := cayP w w.im_pos

theorem continuous_ofUHP : Continuous ofUHP := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_cay_on.comp_continuous UpperHalfPlane.continuous_coe fun w => w.im_pos

theorem ofUHP_toUHP (z : PoincareDisc) : ofUHP (toUHP z) = z :=
  Subtype.ext (cay_cayInv (one_sub_ne_zero_of_normSq_lt z.normSq_lt))

theorem toUHP_ofUHP (w : ℍ) : toUHP (ofUHP w) = w :=
  UpperHalfPlane.ext (cayInv_cay w.im_pos)

/-- **The Cayley transform as a homeomorphism** `𝔻 ≃ₜ ℍ`. -/
def toUHPHomeomorph : PoincareDisc ≃ₜ ℍ where
  toFun := toUHP
  invFun := ofUHP
  left_inv := ofUHP_toUHP
  right_inv := toUHP_ofUHP
  continuous_toFun := continuous_toUHP
  continuous_invFun := continuous_ofUHP

theorem toUHP_injective : Injective toUHP := fun a b h => by
  rw [← ofUHP_toUHP a, h, ofUHP_toUHP]

theorem hypDist_self (z : PoincareDisc) : hypDist z z = 0 := dist_self _

theorem hypDist_comm (z w : PoincareDisc) : hypDist z w = hypDist w z := dist_comm _ _

theorem hypDist_triangle (z w v : PoincareDisc) : hypDist z v ≤ hypDist z w + hypDist w v :=
  dist_triangle _ _ _

theorem hypDist_nonneg (z w : PoincareDisc) : 0 ≤ hypDist z w := dist_nonneg

theorem eq_of_hypDist_eq_zero {z w : PoincareDisc} (h : hypDist z w = 0) : z = w :=
  toUHP_injective (dist_eq_zero.1 h)

/-- The isometries of `ℍ` preserve the Poincaré distance. -/
theorem HypIsom.hypDist_smul (g : HypIsom) (z w : PoincareDisc) :
    hypDist (g • z) (g • w) = hypDist z w := g.2 z w

/-- The topology of `𝔻` is the topology of the Poincaré distance. -/
theorem isOpen_iff_hypDist {U : Set PoincareDisc} :
    IsOpen U ↔ ∀ z ∈ U, ∃ ε > 0, ∀ w, hypDist z w < ε → w ∈ U := by
  rw [← toUHPHomeomorph.symm.isOpen_preimage, Metric.isOpen_iff]
  constructor
  · intro h z hz
    obtain ⟨ε, hε, hb⟩ := h (toUHP z) (by simpa [toUHPHomeomorph] using (ofUHP_toUHP z).symm ▸ hz)
    refine ⟨ε, hε, fun w hw => ?_⟩
    have := hb (show toUHP w ∈ Metric.ball (toUHP z) ε by rw [Metric.mem_ball, dist_comm]; exact hw)
    simpa [toUHPHomeomorph, ofUHP_toUHP] using this
  · intro h w hw
    obtain ⟨ε, hε, hb⟩ := h (ofUHP w) hw
    refine ⟨ε, hε, fun v hv => ?_⟩
    have := hb (ofUHP v) (by
      rw [hypDist, toUHP_ofUHP, toUHP_ofUHP, dist_comm]; exact hv)
    exact this


/-! #### Geodesic segments -/

/-- The hyperbolic coordinate of the diameter `(-1, 1)`: `L(x) = log((1 + x)/(1 - x))`, so that
`d(x, y) = |L x - L y|` (`GX.hypDist_ofReal`). -/
def diamCoord (x : ℝ) : ℝ := Real.log ((1 + x) / (1 - x))

theorem normSq_ofReal_lt {x : ℝ} (hx : |x| < 1) : normSq (x : ℂ) < 1 := by
  rw [normSq_ofReal]
  have := abs_lt.1 hx
  nlinarith

/-- A point of the diameter. -/
def diamPt (x : ℝ) (hx : |x| < 1) : PoincareDisc := ⟨x, normSq_lt_one_iff.1 (normSq_ofReal_lt hx)⟩

theorem toUHP_diamPt (x : ℝ) (hx : |x| < 1) :
    toUHP (diamPt x hx) = UpperHalfPlane.mk ⟨0, Real.exp (diamCoord x)⟩ (Real.exp_pos _) := by
  have h1 := abs_lt.1 hx
  have hpos : 0 < (1 + x) / (1 - x) := div_pos (by linarith) (by linarith)
  apply UpperHalfPlane.ext
  show cayInv (x : ℂ) = ⟨0, Real.exp (diamCoord x)⟩
  rw [diamCoord, Real.exp_log hpos]
  have hx1 : (1 : ℂ) - x ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.2 (by linarith)
  rw [cayInv]
  apply Complex.ext
  · simp only [div_re, mul_re, mul_im, I_re, I_im, add_re, add_im, one_re, one_im, ofReal_re,
      ofReal_im, sub_re, sub_im]
    ring
  · simp only [div_im, mul_re, mul_im, I_re, I_im, add_re, add_im, one_re, one_im, ofReal_re,
      ofReal_im, sub_re, sub_im, normSq_apply]
    have : (1 - x) ≠ 0 := by linarith
    field_simp
    ring

theorem hypDist_diamPt (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) :
    hypDist (diamPt x hx) (diamPt y hy) = dist (diamCoord x) (diamCoord y) := by
  rw [hypDist, toUHP_diamPt, toUHP_diamPt]
  exact (UpperHalfPlane.isometry_vertical_line 0).dist_eq _ _

theorem diamCoord_mono {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) (hxy : x ≤ y) :
    diamCoord x ≤ diamCoord y := by
  have h1 := abs_lt.1 hx
  have h2 := abs_lt.1 hy
  apply Real.log_le_log (div_pos (by linarith) (by linarith))
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem diamCoord_zero : diamCoord 0 = 0 := by simp [diamCoord]

/-- Two functions with the same pairwise distances on `s` have the same variation on `s`. -/
theorem eVariationOn_congr_edist_on {α E F : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    [PseudoEMetricSpace F] {f : α → E} {g : α → F} (s : Set α)
    (h : ∀ a ∈ s, ∀ b ∈ s, edist (f a) (f b) = edist (g a) (g b)) :
    eVariationOn f s = eVariationOn g s := by
  unfold eVariationOn
  congr 1
  ext p
  exact Finset.sum_congr rfl fun i _ => h _ (p.2.2.2 _) _ (p.2.2.2 _)

/-- Two functions with the same pairwise distances have the same variation. -/
theorem eVariationOn_congr_edist {α E F : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    [PseudoEMetricSpace F] {f : α → E} {g : α → F} (s : Set α)
    (h : ∀ a b, edist (f a) (f b) = edist (g a) (g b)) : eVariationOn f s = eVariationOn g s :=
  eVariationOn_congr_edist_on s fun a _ b _ => h a b

/-- **Length is local**: two paths whose pairwise distances agree near every time have the same
length (a Lebesgue number of the cover of `[0, 1]`, and the additivity of the variation). -/
theorem eVariationOn_eq_of_locally {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {f : unitInterval → E} {g : unitInterval → F}
    (h : ∀ t, ∃ N ∈ 𝓝 t, ∀ a ∈ N, ∀ b ∈ N, edist (f a) (f b) = edist (g a) (g b)) :
    eVariationOn f univ = eVariationOn g univ := by
  choose N hN hfg using h
  have hO : ∀ t, ∃ O, IsOpen O ∧ t ∈ O ∧ O ⊆ N t := fun t => by
    obtain ⟨O, hO1, hO2, hO3⟩ := mem_nhds_iff.1 (hN t)
    exact ⟨O, hO2, hO3, hO1⟩
  choose O hOo htO hON using hO
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hOo
    (fun t _ => mem_iUnion.2 ⟨t, htO t⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set P : ℕ → unitInterval := fun k => projIcc 0 1 zero_le_one ((k : ℝ) / (n + 1)) with hPdef
  have hP : Monotone P := fun i j hij => monotone_projIcc _
    (div_le_div_of_nonneg_right (Nat.cast_le.2 hij) (by positivity))
  have hP0 : P 0 = 0 := by
    simp only [hPdef, Nat.cast_zero, zero_div]
    exact projIcc_left _
  have hPn : P (n + 1) = 1 := by
    simp only [hPdef, Nat.cast_add, Nat.cast_one]
    rw [div_self (by positivity)]
    exact projIcc_right _
  have hpiece : ∀ k, eVariationOn f (Icc (P k) (P (k + 1))) =
      eVariationOn g (Icc (P k) (P (k + 1))) := by
    intro k
    obtain ⟨t, ht⟩ := hball (P k) (mem_univ _)
    have hmem : ∀ a ∈ Icc (P k) (P (k + 1)), a ∈ N t := by
      intro a ha
      refine hON t (ht ?_)
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.2 (show (P k : ℝ) ≤ a from ha.1))]
      have hl := (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul ((k + 1 : ℕ) / (n + 1) : ℝ)
        ((k : ℝ) / (n + 1))
      rw [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.2 (show (P k : ℝ) ≤ P (k + 1) from hP (Nat.le_succ k)))] at hl
      have hq : ((k + 1 : ℕ) : ℝ) / (n + 1) - (k : ℝ) / (n + 1) = 1 / ((n : ℝ) + 1) := by
        push_cast; ring
      rw [hq, abs_of_pos (by positivity)] at hl
      have ha2 : (a : ℝ) ≤ P (k + 1) := ha.2
      show (a : ℝ) - P k < δ
      linarith
    exact eVariationOn_congr_edist_on _ fun a ha b hb => hfg t a (hmem a ha) b (hmem b hb)
  have huniv : (univ : Set unitInterval) = Icc (P 0) (P (n + 1)) := by
    rw [hP0, hPn]
    refine (eq_univ_of_forall fun x => ?_).symm
    exact mem_Icc.2 ⟨(show (0 : unitInterval) ≤ x from x.2.1), (show x ≤ 1 from x.2.2)⟩
  rw [huniv, ← eVariationOn.sum' f hP, ← eVariationOn.sum' g hP]
  exact Finset.sum_congr rfl fun k _ => hpiece k

/-- A function whose pairwise distances are dominated by those of `g` has smaller variation. -/
theorem eVariationOn_mono_edist {α E F : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    [PseudoEMetricSpace F] {f : α → E} {g : α → F} (s : Set α)
    (h : ∀ a b, edist (f a) (f b) ≤ edist (g a) (g b)) : eVariationOn f s ≤ eVariationOn g s := by
  unfold eVariationOn
  exact iSup_mono fun p => Finset.sum_le_sum fun i _ => h _ _

theorem hypRatio_smul_eq (a b : ℝ) (w : ℂ) :
    hypRatio (a * w) (b * w) = hypRatio (a * ‖w‖) (b * ‖w‖) := by
  have hw : normSq ((‖w‖ : ℝ) : ℂ) = normSq w := by
    rw [normSq_ofReal, normSq_eq_norm_sq]; ring
  have e1 : (a : ℂ) * w - b * w = ((a - b : ℝ) : ℂ) * w := by push_cast; ring
  have e2 : (a : ℂ) * (‖w‖ : ℝ) - b * (‖w‖ : ℝ) = ((a - b : ℝ) : ℂ) * (‖w‖ : ℝ) := by
    push_cast; ring
  unfold hypRatio
  rw [e1, e2]
  simp only [normSq_mul, normSq_ofReal, hw]

/-- **Geodesic segments of `ℍ`**: any two points of the Poincaré disc are joined by a path whose
length (the variation of its image in `ℍ`) is their distance — `ℍ` is a geodesic space. -/
theorem exists_hypGeodesic (z w : PoincareDisc) :
    ∃ γ : Path z w, eVariationOn (fun t => toUHP (γ t)) univ = ENNReal.ofReal (hypDist z w) := by
  have hu1 : normSq (1 : ℂ) = 1 := map_one _
  have hz := z.normSq_lt
  have hz' : normSq (-(z : ℂ)) < 1 := by rwa [normSq_neg]
  set w' : ℂ := mobF 1 (-(z : ℂ)) false w with hw'
  have hw'1 : normSq w' < 1 := normSq_mobF_lt false hu1 hz' w.normSq_lt
  have hn : ‖w'‖ < 1 := by
    have := normSq_lt_one_iff.1 hw'1; simpa using this
  have hseg : ∀ t : unitInterval, normSq ((t : ℝ) * w') < 1 := by
    intro t
    rw [normSq_mul, normSq_ofReal]
    have h0 := t.2.1
    have h1 := t.2.2
    have : (t : ℝ) * t ≤ 1 := by nlinarith
    nlinarith [normSq_nonneg w']
  have hΦ : ∀ t : unitInterval, normSq (mobF 1 z false ((t : ℝ) * w')) < 1 :=
    fun t => normSq_mobF_lt false hu1 hz (hseg t)
  let γf : unitInterval → PoincareDisc := fun t =>
    ⟨mobF 1 z false ((t : ℝ) * w'), normSq_lt_one_iff.1 (hΦ t)⟩
  have hcont : Continuous γf := by
    refine Continuous.subtype_mk ?_ _
    have hc : ∀ t : unitInterval, mobDen 1 z false ((t : ℝ) * w') ≠ 0 := fun t =>
      mobDen_ne_zero false hu1 hz (hseg t).le
    unfold mobF
    refine Continuous.div ?_ ?_ hc
    · exact (continuous_const.mul ((continuous_sigmaB _).comp
        ((continuous_ofReal.comp continuous_subtype_val).mul continuous_const))).add
        continuous_const
    · exact continuous_const.add (continuous_const.mul ((continuous_sigmaB _).comp
        ((continuous_ofReal.comp continuous_subtype_val).mul continuous_const)))
  have h0 : γf 0 = z := by
    apply Subtype.ext
    show mobF 1 z false (((0 : unitInterval) : ℝ) * w') = z
    simp [mobF, sigmaB]
  have h1 : γf 1 = w := by
    apply Subtype.ext
    show mobF 1 z false (((1 : unitInterval) : ℝ) * w') = w
    simp only [Set.Icc.coe_one, ofReal_one, one_mul, hw']
    exact mobF_one_mobF_neg (a := (z : ℂ)) hz w.normSq_lt.le
  let γ : Path z w := ⟨⟨γf, hcont⟩, h0, h1⟩
  refine ⟨γ, ?_⟩
  -- the distances along `γ` are those of the diameter
  have hr : |‖w'‖| < 1 := by rw [abs_of_nonneg (norm_nonneg _)]; exact hn
  have hseg' : ∀ t : unitInterval, |(t : ℝ) * ‖w'‖| < 1 := by
    intro t
    rw [abs_mul, abs_of_nonneg t.2.1, abs_of_nonneg (norm_nonneg _)]
    calc (t : ℝ) * ‖w'‖ ≤ 1 * ‖w'‖ := mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hn
  let f : unitInterval → ℝ := fun t => diamCoord ((t : ℝ) * ‖w'‖)
  have hdist : ∀ s t : unitInterval, hypDist (γ s) (γ t) = dist (f s) (f t) := by
    intro s t
    have e1 : hypDist (γ s) (γ t) = hypDist (diamPt _ (hseg' s)) (diamPt _ (hseg' t)) := by
      rw [hypDist_eq_iff]
      show hypRatio (mobF 1 z false ((s : ℝ) * w')) (mobF 1 z false ((t : ℝ) * w')) =
        hypRatio (((s : ℝ) * ‖w'‖ : ℝ) : ℂ) (((t : ℝ) * ‖w'‖ : ℝ) : ℂ)
      rw [hypRatio_mobF false hu1 hz (hseg s) (hseg t), hypRatio_smul_eq]
      push_cast; rfl
    rw [e1, hypDist_diamPt]
  have hev : eVariationOn (fun t => toUHP (γ t)) univ = eVariationOn f univ := by
    refine eVariationOn_congr_edist _ fun a b => ?_
    rw [edist_dist, edist_dist]
    exact congrArg ENNReal.ofReal (hdist a b)
  have hmono : MonotoneOn f univ := fun a _ b _ hab =>
    diamCoord_mono (hseg' a) (hseg' b) (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
  have hf01 : f 0 ≤ f 1 := hmono (mem_univ _) (mem_univ _) zero_le_one
  have hzw : hypDist z w = f 1 - f 0 := by
    have := hdist 0 1
    rw [show γ 0 = z from h0, show γ 1 = w from h1] at this
    rw [this, Real.dist_eq, abs_of_nonpos (by linarith)]
    ring
  rw [hev, hzw]
  apply le_antisymm
  · have := hmono.eVariationOn_le (mem_univ (0 : unitInterval)) (mem_univ 1)
    rwa [show (univ : Set unitInterval) ∩ Icc 0 1 = univ from
      eq_univ_of_forall fun x => ⟨mem_univ x, x.2.1, x.2.2⟩] at this
  · have := eVariationOn.edist_le f (mem_univ (0 : unitInterval)) (mem_univ 1)
    rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)] at this
    exact this


theorem isOpen_hypBall (z : PoincareDisc) (r : ℝ) : IsOpen {w | hypDist z w < r} :=
  isOpen_lt (continuous_const.dist continuous_toUHP) continuous_const

/-! ### DEC-81: the hyperbolic metric of a quotient of `ℍ` -/

section HypQuot

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]

/-- **A quotient of `ℍ`**: `p : E → Y` continuous, open, onto, with closed fibres, and
`Θ : E ≃ₜ 𝔻` a homeomorphism for which any two points of a fibre are exchanged by a
transformation over `Y` read in `Θ` as an isometry of `ℍ` — the situation of the universal cover
of a complete hyperbolic surface (`GX.IsCompleteHyperbolic.isHypQuotient`). -/
structure IsHypQuotient (p : E → Y) (Θ : E ≃ₜ PoincareDisc) : Prop where
  continuous : Continuous p
  isOpenMap : IsOpenMap p
  surjective : Surjective p
  isClosed_fibre : ∀ y, IsClosed (p ⁻¹' {y})
  deck : ∀ e e', p e = p e' → ∃ φ : E → E, ∃ g : HypIsom,
    (∀ x, p (φ x) = p x) ∧ φ e = e' ∧ ∀ x, Θ (φ x) = g • Θ x

variable {p : E → Y} {Θ : E ≃ₜ PoincareDisc}

/-- **The quotient distance** `d(a, b) = inf {d_ℍ(Θ e, Θ e') : p e = a, p e' = b}`. -/
def quotDist (p : E → Y) (Θ : E ≃ₜ PoincareDisc) (a b : Y) : ℝ :=
  ⨅ e : {e : E // p e = a}, ⨅ e' : {e' : E // p e' = b}, hypDist (Θ e) (Θ e')

namespace IsHypQuotient

variable (H : IsHypQuotient p Θ)
include H

theorem nonempty_fibre (y : Y) : Nonempty {e : E // p e = y} :=
  let ⟨e, he⟩ := H.surjective y; ⟨⟨e, he⟩⟩

theorem bddBelow_fibre (z : PoincareDisc) (b : Y) :
    BddBelow (range fun e' : {e' : E // p e' = b} => hypDist z (Θ e')) :=
  ⟨0, by rintro _ ⟨e', rfl⟩; exact hypDist_nonneg _ _⟩

theorem iInf_le_iInf {e₁ e₂ : E} (h : p e₁ = p e₂) (b : Y) :
    ⨅ e' : {e' : E // p e' = b}, hypDist (Θ e₁) (Θ e') ≤
      ⨅ e' : {e' : E // p e' = b}, hypDist (Θ e₂) (Θ e') := by
  haveI := H.nonempty_fibre b
  obtain ⟨φ, g, hφp, hφe, hφΘ⟩ := H.deck e₂ e₁ h.symm
  refine le_ciInf fun e' => ?_
  refine (ciInf_le (H.bddBelow_fibre _ b) ⟨φ e', by rw [hφp]; exact e'.2⟩).trans_eq ?_
  show hypDist (Θ e₁) (Θ (φ e')) = hypDist (Θ e₂) (Θ e')
  rw [← hφe, hφΘ, hφΘ, HypIsom.hypDist_smul]

/-- The quotient distance computed from one lift of `a`. -/
theorem quotDist_eq {e : E} {a : Y} (he : p e = a) (b : Y) :
    quotDist p Θ a b = ⨅ e' : {e' : E // p e' = b}, hypDist (Θ e) (Θ e') := by
  haveI := H.nonempty_fibre a
  haveI := H.nonempty_fibre b
  apply le_antisymm
  · refine ciInf_le ⟨0, ?_⟩ (⟨e, he⟩ : {e : E // p e = a})
    rintro _ ⟨e₁, rfl⟩
    exact le_ciInf fun e' => hypDist_nonneg _ _
  · exact le_ciInf fun e₁ => H.iInf_le_iInf (he.trans e₁.2.symm) b

theorem quotDist_le {e e' : E} {a b : Y} (he : p e = a) (he' : p e' = b) :
    quotDist p Θ a b ≤ hypDist (Θ e) (Θ e') := by
  rw [H.quotDist_eq he]
  exact ciInf_le (H.bddBelow_fibre _ b) ⟨e', he'⟩

theorem exists_lt {e : E} {a : Y} (he : p e = a) (b : Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ e', p e' = b ∧ hypDist (Θ e) (Θ e') < quotDist p Θ a b + ε := by
  haveI := H.nonempty_fibre b
  rw [H.quotDist_eq he] at *
  obtain ⟨e', he'⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right
    (⨅ e' : {e' : E // p e' = b}, hypDist (Θ e) (Θ e')) hε)
  exact ⟨e', e'.2, he'⟩

theorem quotDist_nonneg (a b : Y) : 0 ≤ quotDist p Θ a b := by
  obtain ⟨e, he⟩ := H.surjective a
  haveI := H.nonempty_fibre b
  rw [H.quotDist_eq he]
  exact le_ciInf fun e' => hypDist_nonneg _ _

theorem quotDist_self (a : Y) : quotDist p Θ a a = 0 := by
  obtain ⟨e, he⟩ := H.surjective a
  exact le_antisymm ((H.quotDist_le he he).trans_eq (hypDist_self _)) (H.quotDist_nonneg a a)

theorem quotDist_comm (a b : Y) : quotDist p Θ a b = quotDist p Θ b a := by
  have key : ∀ a b, quotDist p Θ b a ≤ quotDist p Θ a b := by
    intro a b
    obtain ⟨e, he⟩ := H.surjective a
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨e', he', hlt⟩ := H.exists_lt he b hε
    exact lt_of_le_of_lt ((H.quotDist_le he' he).trans_eq (hypDist_comm _ _)) hlt
  exact le_antisymm (key b a) (key a b)

theorem quotDist_triangle (a b c : Y) :
    quotDist p Θ a c ≤ quotDist p Θ a b + quotDist p Θ b c := by
  obtain ⟨e, he⟩ := H.surjective a
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨e', he', h1⟩ := H.exists_lt he b (half_pos hε)
  obtain ⟨e'', he'', h2⟩ := H.exists_lt he' c (half_pos hε)
  calc quotDist p Θ a c ≤ hypDist (Θ e) (Θ e'') := H.quotDist_le he he''
    _ ≤ hypDist (Θ e) (Θ e') + hypDist (Θ e') (Θ e'') := hypDist_triangle _ _ _
    _ < quotDist p Θ a b + quotDist p Θ b c + ε := by linarith

theorem eq_of_quotDist_eq_zero {a b : Y} (h : quotDist p Θ a b = 0) : a = b := by
  obtain ⟨e, he⟩ := H.surjective a
  have hcl : IsClosed (Θ '' (p ⁻¹' {b})) := Θ.isClosedMap _ (H.isClosed_fibre b)
  by_contra hab
  have hnot : Θ e ∉ Θ '' (p ⁻¹' {b}) := by
    rintro ⟨e', he', hΘ⟩
    exact hab (he.symm.trans (by rw [Θ.injective hΘ.symm]; exact he'))
  obtain ⟨ε, hε, hball⟩ := isOpen_iff_hypDist.1 hcl.isOpen_compl _ hnot
  obtain ⟨e', he', hlt⟩ := H.exists_lt he b hε
  rw [h, zero_add] at hlt
  exact hball _ hlt ⟨e', he', rfl⟩

/-- The quotient distance gives the topology of `Y`. -/
theorem isOpen_iff (s : Set Y) :
    IsOpen s ↔ ∀ a ∈ s, ∃ ε > 0, ∀ b, quotDist p Θ a b < ε → b ∈ s := by
  constructor
  · intro hs a ha
    obtain ⟨e, he⟩ := H.surjective a
    have hO : IsOpen {z : PoincareDisc | p (Θ.symm z) ∈ s} :=
      hs.preimage (H.continuous.comp Θ.symm.continuous)
    obtain ⟨ε, hε, hb⟩ := isOpen_iff_hypDist.1 hO (Θ e) (by simpa [he] using ha)
    refine ⟨ε, hε, fun b hb' => ?_⟩
    obtain ⟨e', he', hlt⟩ := H.exists_lt he b (sub_pos.2 hb')
    have := hb (Θ e') (by linarith)
    simpa [he'] using this
  · intro h
    refine isOpen_iff_mem_nhds.2 fun a ha => ?_
    obtain ⟨ε, hε, hb⟩ := h a ha
    obtain ⟨e, he⟩ := H.surjective a
    have hopen : IsOpen (p '' (Θ ⁻¹' {z | hypDist (Θ e) z < ε})) :=
      H.isOpenMap _ ((isOpen_hypBall _ _).preimage Θ.continuous)
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨e, by simpa [hypDist_self] using hε, he⟩) ?_
    rintro _ ⟨e', he', rfl⟩
    exact hb _ (lt_of_le_of_lt (H.quotDist_le he rfl) he')

/-- **The hyperbolic metric of the quotient** — a metric space structure on `Y` whose topology is
(definitionally) the topology of `Y`. -/
@[implicit_reducible]
def metricSpace : MetricSpace Y :=
  MetricSpace.ofDistTopology (quotDist p Θ) H.quotDist_self H.quotDist_comm H.quotDist_triangle
    H.isOpen_iff fun _ _ => H.eq_of_quotDist_eq_zero

theorem dist_eq (a b : Y) : @dist Y H.metricSpace.toDist a b = quotDist p Θ a b := rfl

/-- **The hyperbolic metric of the quotient is complete.** -/
theorem completeSpace : @CompleteSpace Y H.metricSpace.toUniformSpace := by
  letI := H.metricSpace
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2 : ℝ) ^ n)
    (fun n => by positivity) fun u hu => ?_
  have key : ∀ (n : ℕ) (e : E), p e = u n →
      ∃ e', p e' = u (n + 1) ∧ hypDist (Θ e) (Θ e') < (1 / 2 : ℝ) ^ n := by
    intro n e he
    have h1 : quotDist p Θ (u n) (u (n + 1)) < (1 / 2 : ℝ) ^ n := hu n n (n + 1) le_rfl
      (Nat.le_succ n)
    obtain ⟨e', he', hlt⟩ := H.exists_lt he (u (n + 1)) (sub_pos.2 h1)
    exact ⟨e', he', by linarith⟩
  choose! f hf using key
  obtain ⟨e₀, he₀⟩ := H.surjective (u 0)
  let ee : ℕ → E := fun n => Nat.rec e₀ (fun n e => f n e) n
  have hee : ∀ n, p (ee n) = u n := by
    intro n
    induction n with
    | zero => exact he₀
    | succ n ih => exact (hf n (ee n) ih).1
  have hstep : ∀ n, dist (toUHP (Θ (ee n))) (toUHP (Θ (ee (n + 1)))) ≤ 2 / 2 / 2 ^ n := by
    intro n
    have := (hf n (ee n) (hee n)).2
    rw [show (2 : ℝ) / 2 / 2 ^ n = (1 / 2) ^ n by rw [div_self two_ne_zero, one_div_pow]]
    exact this.le
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hstep)
  refine ⟨p (Θ.symm (ofUHP w)), ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hw' : Tendsto (fun n => dist (toUHP (Θ (ee n))) w) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hw
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hw'
  show quotDist p Θ (u n) (p (Θ.symm (ofUHP w))) ≤ _
  refine (H.quotDist_le (hee n) rfl).trans_eq ?_
  rw [Homeomorph.apply_symm_apply, hypDist, toUHP_ofUHP]

/-- **The hyperbolic metric of the quotient is a length metric**: any two points are joined by
paths of length (variation) as close to their distance as wished, and no path is shorter. -/
theorem exists_path_variation_le (a b : Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : Path a b, @eVariationOn unitInterval _ Y H.metricSpace.toPseudoEMetricSpace γ univ ≤
      ENNReal.ofReal (quotDist p Θ a b + ε) := by
  letI := H.metricSpace
  obtain ⟨e, he⟩ := H.surjective a
  obtain ⟨e', he', hlt⟩ := H.exists_lt he b hε
  obtain ⟨γ₀, hγ₀⟩ := exists_hypGeodesic (Θ e) (Θ e')
  let γ : Path a b := ⟨⟨fun t => p (Θ.symm (γ₀ t)),
    H.continuous.comp (Θ.symm.continuous.comp γ₀.continuous)⟩,
    by simp [he], by simp [he']⟩
  refine ⟨γ, ?_⟩
  calc eVariationOn (fun t => γ t) univ ≤ eVariationOn (fun t => toUHP (γ₀ t)) univ := by
        refine eVariationOn_mono_edist _ fun s t => ?_
        rw [edist_dist, edist_dist]
        refine ENNReal.ofReal_le_ofReal ?_
        show quotDist p Θ (p (Θ.symm (γ₀ s))) (p (Θ.symm (γ₀ t))) ≤ hypDist (γ₀ s) (γ₀ t)
        refine (H.quotDist_le rfl rfl).trans_eq ?_
        simp
    _ = ENNReal.ofReal (hypDist (Θ e) (Θ e')) := hγ₀
    _ ≤ ENNReal.ofReal (quotDist p Θ a b + ε) := ENNReal.ofReal_le_ofReal hlt.le

theorem le_eVariationOn {a b : Y} (γ : Path a b) :
    ENNReal.ofReal (quotDist p Θ a b) ≤
      @eVariationOn unitInterval _ Y H.metricSpace.toPseudoEMetricSpace γ univ := by
  letI := H.metricSpace
  have := eVariationOn.edist_le (fun t => γ t) (mem_univ (0 : unitInterval)) (mem_univ 1)
  rw [edist_dist, γ.source, γ.target] at this
  exact this

/-- **The hyperbolic metric of the quotient is locally the metric of `ℍ` read in the charts**,
when `p` is a local homeomorphism and `Θ` is, near every point, an isometry of `ℍ` composed with
the chart of `Y` at its image. -/
theorem exists_nhds_quotDist_eq [ChartedSpace PoincareDisc Y] (hloc : IsLocalHomeomorph p)
    (hchart : ∀ e, ∃ g : HypIsom, ∀ᶠ e' in 𝓝 e, Θ e' = g • chartAt PoincareDisc (p e) (p e'))
    (y : Y) : ∃ V ∈ 𝓝 y, ∀ a ∈ V, ∀ b ∈ V,
      quotDist p Θ a b = hypDist (chartAt PoincareDisc y a) (chartAt PoincareDisc y b) := by
  obtain ⟨e, rfl⟩ := H.surjective y
  obtain ⟨g, hg⟩ := hchart e
  obtain ⟨h, heh, hph⟩ := hloc e
  obtain ⟨U₀, hU₀, hU₀o, heU₀⟩ := eventually_nhds_iff.1 hg
  set U : Set E := h.source ∩ U₀ with hUdef
  have hUo : IsOpen U := h.open_source.inter hU₀o
  obtain ⟨ε, hε, hball⟩ := isOpen_iff_hypDist.1 (Θ.isOpenMap U hUo) (Θ e) ⟨e, ⟨heh, heU₀⟩, rfl⟩
  set r := ε / 3 with hr
  have hrpos : 0 < r := by positivity
  have hpe : p e = h e := by rw [hph]
  have hhe : h.symm (p e) = e := by rw [hpe]; exact h.left_inv heh
  have htgt : p e ∈ h.target := by rw [hpe]; exact h.map_source heh
  set V : Set Y := h.target ∩ h.symm ⁻¹' (U ∩ {x | hypDist (Θ e) (Θ x) < r}) with hVdef
  have hV : V ∈ 𝓝 (p e) := by
    refine Filter.inter_mem (h.open_target.mem_nhds htgt) ?_
    refine (h.continuousAt_symm htgt).preimage_mem_nhds ?_
    rw [hhe]
    refine (hUo.inter ((isOpen_hypBall _ _).preimage Θ.continuous)).mem_nhds ⟨⟨heh, heU₀⟩, ?_⟩
    show hypDist (Θ e) (Θ e) < r
    rw [hypDist_self]; exact hrpos
  have hsec : ∀ a ∈ V, p (h.symm a) = a := fun a ha => by rw [hph]; exact h.right_inv ha.1
  have hΘ : ∀ a ∈ V, Θ (h.symm a) = g • chartAt PoincareDisc (p e) a := fun a ha => by
    have := hU₀ _ ha.2.1.2
    rwa [hsec a ha] at this
  refine ⟨V, hV, fun a ha b hb => ?_⟩
  apply le_antisymm
  · refine (H.quotDist_le (hsec a ha) (hsec b hb)).trans_eq ?_
    rw [hΘ a ha, hΘ b hb, HypIsom.hypDist_smul]
  · haveI := H.nonempty_fibre b
    rw [H.quotDist_eq (hsec a ha)]
    refine le_ciInf fun e'' => ?_
    rw [← HypIsom.hypDist_smul g, ← hΘ a ha, ← hΘ b hb]
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have h1 : hypDist (Θ e) (Θ (h.symm a)) < r := ha.2.2
    have h2 : hypDist (Θ e) (Θ (h.symm b)) < r := hb.2.2
    have h3 := hypDist_triangle (Θ (h.symm a)) (Θ e) (Θ (h.symm b))
    have h4 := hypDist_triangle (Θ e) (Θ (h.symm a)) (Θ e'')
    rw [hypDist_comm (Θ (h.symm a)) (Θ e)] at h3
    obtain ⟨x, hxU, hx⟩ := hball (Θ e'') (by linarith)
    have hxe : x = e'' := Θ.injective hx
    rw [hxe] at hxU
    have : (e'' : E) = h.symm b := h.injOn hxU.1 hb.2.1.1 (by rw [← hph, e''.2, hsec b hb])
    rw [this] at hlt
    exact lt_irrefl _ hlt

end IsHypQuotient

end HypQuot


/-! ### DEC-81: hyperbolic metrics on a `(G, ℍ)`-surface -/

section HypMetric

variable (Y : Type*) [TopologicalSpace Y] [ChartedSpace PoincareDisc Y]

/-- **A hyperbolic metric** on a `(G, ℍ)`-manifold `Y` (`G = Isom(ℍ)`), the metric reading of
"`M ∖ S` endowed with a hyperbolic metric" (DEC-81): a metric on `Y` giving its topology which is
a **length metric** (any two points are joined by paths whose length — the variation along the
path — is as close to their distance as wished) and **locally the metric of `ℍ`** read in the
charts. This is what the distance of a Riemannian metric of constant curvature `-1` is (its
small balls are isometric to balls of `ℍ`); the Riemannian tensor itself is not formalized (no
Riemannian surfaces at this pin). -/
structure IsHyperbolicMetric (m : MetricSpace Y) : Prop where
  topology_eq : m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace Y›
  length : ∀ (a b : Y) (ε : ℝ), 0 < ε → ∃ γ : Path a b,
    @eVariationOn unitInterval _ Y m.toPseudoEMetricSpace γ univ ≤
      ENNReal.ofReal (@dist Y m.toDist a b + ε)
  local_isometry : ∀ y : Y, ∃ V ∈ 𝓝 y, ∀ a ∈ V, ∀ b ∈ V,
    @dist Y m.toDist a b = hypDist (chartAt PoincareDisc y a) (chartAt PoincareDisc y b)

variable {Y}

/-- In a metric space no path is shorter than the distance of its ends. -/
theorem dist_le_eVariationOn {Z : Type*} [PseudoMetricSpace Z] {a b : Z} (γ : C(unitInterval, Z))
    (h0 : γ 0 = a) (h1 : γ 1 = b) : ENNReal.ofReal (dist a b) ≤ eVariationOn γ univ := by
  have := eVariationOn.edist_le (fun t => γ t) (mem_univ (0 : unitInterval)) (mem_univ 1)
  rwa [edist_dist, h0, h1] at this

/-- **The hyperbolic metric is unique**: a `(G, ℍ)`-structure carries at most one hyperbolic
metric (two of them agree near every point, so give every path the same length). -/
theorem IsHyperbolicMetric.unique {m m' : MetricSpace Y} (h : IsHyperbolicMetric Y m)
    (h' : IsHyperbolicMetric Y m') : m = m' := by
  have hloc : ∀ y : Y, ∃ W ∈ 𝓝 y, ∀ a ∈ W, ∀ b ∈ W,
      @dist Y m.toDist a b = @dist Y m'.toDist a b := by
    intro y
    obtain ⟨V, hV, hVd⟩ := h.local_isometry y
    obtain ⟨V', hV', hVd'⟩ := h'.local_isometry y
    exact ⟨V ∩ V', Filter.inter_mem hV hV', fun a ha b hb => by
      rw [hVd a ha.1 b hb.1, hVd' a ha.2 b hb.2]⟩
  have key : ∀ {m m' : MetricSpace Y}, IsHyperbolicMetric Y m → IsHyperbolicMetric Y m' →
      (∀ y : Y, ∃ W ∈ 𝓝 y, ∀ a ∈ W, ∀ b ∈ W, @dist Y m.toDist a b = @dist Y m'.toDist a b) →
      ∀ a b : Y, @dist Y m.toDist a b ≤ @dist Y m'.toDist a b := by
    intro m m' h h' hloc a b
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨γ, hγ⟩ := h'.length a b ε hε
    have hvar : @eVariationOn unitInterval _ Y m.toPseudoEMetricSpace γ univ =
        @eVariationOn unitInterval _ Y m'.toPseudoEMetricSpace γ univ := by
      refine @eVariationOn_eq_of_locally Y Y m.toPseudoEMetricSpace m'.toPseudoEMetricSpace
        γ γ fun t => ?_
      obtain ⟨W, hW, hWd⟩ := hloc (γ t)
      refine ⟨γ ⁻¹' W, γ.continuous.continuousAt.preimage_mem_nhds hW, fun s hs s' hs' => ?_⟩
      rw [@edist_dist Y m.toPseudoMetricSpace, @edist_dist Y m'.toPseudoMetricSpace]
      exact congrArg ENNReal.ofReal (hWd _ hs _ hs')
    have hle := @dist_le_eVariationOn Y m.toPseudoMetricSpace a b
      (@ContinuousMap.mk unitInterval Y _ m.toUniformSpace.toTopologicalSpace γ
        (by rw [h.topology_eq]; exact γ.continuous)) γ.source γ.target
    have := (hle.trans_eq hvar).trans hγ
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  apply MetricSpace.ext
  ext a b
  exact le_antisymm (key h h' hloc a b) (key h' h (fun y => let ⟨W, hW, hWd⟩ := hloc y
    ⟨W, hW, fun a ha b hb => (hWd a ha b hb).symm⟩) a b)

theorem IsCompleteHyperbolic.isHypQuotient [LocPathConnectedSpace Y] [ConnectedSpace Y]
    [T1Space Y] [HasGroupoid Y (gxGroupoid HypIsom PoincareDisc)] (hc : IsCompleteHyperbolic Y)
    (hY : SemilocallySimplyConnected Y) (y₀ : Y) :
    ∃ Θ : UniversalCover Y y₀ ≃ₜ PoincareDisc, IsHypQuotient (UniversalCover.proj Y y₀) Θ ∧
      ∀ e, ∃ g : HypIsom, ∀ᶠ e' in 𝓝 e,
        Θ e' = g • chartAt PoincareDisc (UniversalCover.proj Y y₀ e) (UniversalCover.proj Y y₀ e') := by
  obtain ⟨dev, hol, hdev, -, hhol⟩ := developing_theorem (G := HypIsom) (X := PoincareDisc) hY y₀
  obtain ⟨Θ, hΘ⟩ := IsCompleteHyperbolic.exists_homeomorph hc hY y₀ dev hdev
  haveI : PathConnectedSpace Y := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  refine ⟨Θ, ⟨UniversalCover.continuous_proj, UniversalCover.isOpenMap_proj,
    UniversalCover.proj_surjective, fun y => isClosed_singleton.preimage
      UniversalCover.continuous_proj, ?_⟩, fun e => ?_⟩
  · rintro ⟨y, a⟩ ⟨y', b⟩ h
    change y = y' at h
    subst h
    let γ : Deck (UniversalCover.proj Y y₀) := ⟨UniversalCover.leftMulHomeomorph (b.trans a.symm), rfl⟩
    refine ⟨γ.1, hol γ, fun x => congrFun γ.2 x, ?_, fun x => by rw [hΘ]; exact hhol γ x⟩
    show (⟨y, (b.trans a.symm).trans a⟩ : UniversalCover Y y₀) = ⟨y, b⟩
    rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
  · letI := coverChartedSpace PoincareDisc hY y₀
    obtain ⟨g, hg⟩ := (isGXMorphism_iff_model.1 hdev).2 e
    refine ⟨g, hg.mono fun e' he' => ?_⟩
    rw [hΘ, he', pullback_chartAt_apply]

/-- **A complete hyperbolic surface carries a complete hyperbolic metric** (DEC-81, metric
reading of `ex:take_closed_unit_disc`): the quotient metric of `ℍ` through the developing map,
a complete length metric locally isometric to `ℍ` in the charts. -/
theorem IsCompleteHyperbolic.exists_isHyperbolicMetric [LocPathConnectedSpace Y]
    [ConnectedSpace Y] [T1Space Y] [HasGroupoid Y (gxGroupoid HypIsom PoincareDisc)]
    (hc : IsCompleteHyperbolic Y) (hY : SemilocallySimplyConnected Y) :
    ∃ m : MetricSpace Y, IsHyperbolicMetric Y m ∧ @CompleteSpace Y m.toUniformSpace := by
  obtain ⟨y₀⟩ : Nonempty Y := ‹ConnectedSpace Y›.toNonempty
  obtain ⟨Θ, H, hch⟩ := hc.isHypQuotient hY y₀
  refine ⟨H.metricSpace, ⟨rfl, fun a b ε hε => H.exists_path_variation_le a b hε, ?_⟩,
    H.completeSpace⟩
  exact H.exists_nhds_quotDist_eq
    (UniversalCover.isCoveringMap_proj (y₀ := y₀) hY).isLocalHomeomorph hch

end HypMetric

/-! ### DEC-81: cusps have finite area -/

section CuspArea

open MeasureTheory
open scoped ENNReal


/-- The fundamental strip `{c < Im w, 0 ≤ Re w < 1}` of the horoball `{Im w > c}` modulo the
translation `w ↦ w + 1`. -/
def cuspStrip (c : ℝ) : Set ℍ := {w | c < w.im ∧ 0 ≤ w.re ∧ w.re < 1}

theorem lintegral_Ioi_inv_sq {c : ℝ} (hc : 0 < c) :
    ∫⁻ y in Ioi c, (((1 / ‖y‖₊) ^ 2 : NNReal) : ℝ≥0∞) = ENNReal.ofReal (1 / c) := by
  have h1 : ∀ y ∈ Ioi c, (((1 / ‖y‖₊) ^ 2 : NNReal) : ℝ≥0∞) = ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    intro y hy
    have hy0 : 0 < y := hc.trans hy
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos hy0, Real.rpow_neg hy0.le, one_div, inv_pow]
    norm_cast
  rw [setLIntegral_congr_fun measurableSet_Ioi h1,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) hc)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
        Real.rpow_nonneg (hc.trans hy).le _),
    integral_Ioi_rpow_of_lt (by norm_num) hc]
  congr 1
  norm_num
  rw [Real.rpow_neg_one, inv_eq_one_div]

/-- **The cusp has finite area**: for the invariant area `dx dy / y²` of `ℍ` (mathlib's
`volume` on `UpperHalfPlane`), the fundamental strip of a horoball `{Im w > c}` under
`w ↦ w + 1` has area `1/c`. -/
theorem volume_cuspStrip {c : ℝ} (hc : 0 < c) :
    volume (cuspStrip c) = ENNReal.ofReal (1 / c) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  have himg : ((↑) : ℍ → ℂ) '' cuspStrip c =
      Complex.measurableEquivRealProd ⁻¹' (Ico 0 1 ×ˢ Ioi c) := by
    ext z
    simp only [mem_image, cuspStrip, mem_setOf_eq, mem_preimage,
      Complex.measurableEquivRealProd_apply, mem_prod, mem_Ico, mem_Ioi]
    constructor
    · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨⟨h2, h3⟩, h1⟩
    · rintro ⟨⟨h2, h3⟩, h1⟩
      exact ⟨⟨z, hc.trans h1⟩, ⟨h1, h2, h3⟩, rfl⟩
  rw [himg]
  have := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : NNReal) : ℝ≥0∞)) (Ico 0 1 ×ˢ Ioi c)
  simp only [Complex.measurableEquivRealProd_apply] at this
  rw [this, Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_Ioi_inv_sq hc, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]

section CuspMetric

variable {M : Type*} [TopologicalSpace M] {S : Set M} {s : M}

namespace CuspChart

variable (C : CuspChart S s)

/-- The cusp map identifies the fundamental strip with the punctured cusp neighbourhood:
`E` is injective on `{0 ≤ Re w < 1}` and maps it onto `W_c ∖ {s}`. -/
theorem injOn_E_strip : InjOn C.E {w | 0 ≤ (w : ℂ).re ∧ (w : ℂ).re < 1} := by
  intro w hw w' hw' h
  obtain ⟨n, hn⟩ := C.exists_int_of_E_eq h
  have hre : (w' : ℂ).re = (w : ℂ).re + n := by rw [hn]; simp
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) < 1 := by linarith [hw.1, hw'.2]
    have h2 : (-1 : ℝ) < n := by linarith [hw.2, hw'.1]
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : -1 < n := by exact_mod_cast h2
    omega
  apply Subtype.ext
  rw [hn, hn0]; simp

theorem image_E_strip :
    Subtype.val '' (C.E '' {w | 0 ≤ (w : ℂ).re ∧ (w : ℂ).re < 1}) = C.W C.c \ {s} := by
  ext x
  constructor
  · rintro ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact ⟨(C.E_mem_W_iff C.c w).2 w.2, C.EV_ne w⟩
  · rintro ⟨hxW, hxs⟩
    obtain ⟨w, -, hw⟩ := C.exists_E_eq le_rfl hxW hxs
    set n : ℤ := -⌊(w : ℂ).re⌋
    refine ⟨C.E ⟨w + n, by simpa using w.2⟩, ⟨⟨w + n, by simpa using w.2⟩, ?_, rfl⟩, ?_⟩
    · show 0 ≤ ((w : ℂ) + n).re ∧ ((w : ℂ) + n).re < 1
      simp only [add_re, n, Int.cast_neg, neg_re, intCast_re]
      have := Int.floor_le (w : ℂ).re
      have := Int.lt_floor_add_one (w : ℂ).re
      constructor <;> linarith
    · rw [C.E_add_int]; exact hw

/-- The cusp map read in `ℍ`: the point `w` of the horoball. -/
theorem toUHP_cayH (w : Horoball C.c) :
    toUHP (C.cayH w) = UpperHalfPlane.mk w (C.c_pos.trans w.2) :=
  UpperHalfPlane.ext (cayInv_cay (C.c_pos.trans w.2))

variable [ChartedSpace PoincareDisc (Sᶜ : Set M)]

/-- **The cusp map is a local isometry** from the horoball `{Im w > c}` of `ℍ` to `M ∖ S` with
any hyperbolic metric (a hyperbolic cusp is a `(G, ℍ)`-morphism). -/
theorem exists_nhds_dist_E {m : MetricSpace (Sᶜ : Set M)} (hm : IsHyperbolicMetric (Sᶜ : Set M) m)
    (hC : C.IsHyperbolicCusp) (w : Horoball C.c) :
    ∃ N ∈ 𝓝 w, ∀ w₁ ∈ N, ∀ w₂ ∈ N, @dist _ m.toDist (C.E w₁) (C.E w₂) =
      dist (UpperHalfPlane.mk w₁ (C.c_pos.trans w₁.2)) (UpperHalfPlane.mk w₂ (C.c_pos.trans w₂.2)) := by
  obtain ⟨g, hg⟩ := hC w
  obtain ⟨V, hV, hVd⟩ := hm.local_isometry (C.E w)
  refine ⟨C.E ⁻¹' V ∩ {w' | chartAt PoincareDisc (C.E w) (C.E w') = g • C.cayH w'},
    Filter.inter_mem (C.continuous_E.continuousAt.preimage_mem_nhds hV) hg,
    fun w₁ h₁ w₂ h₂ => ?_⟩
  rw [hVd _ h₁.1 _ h₂.1, h₁.2, h₂.2, HypIsom.hypDist_smul, hypDist, toUHP_cayH, toUHP_cayH]

end CuspChart

/-- **Cusps have finite area** (`ex:take_closed_unit_disc`, DEC-81): at a hyperbolic cusp
`C` of `M ∖ S`, the punctured cusp neighbourhood `W_c ∖ {s}` is the injective image, under the
cusp map — a local isometry for the hyperbolic metric — of the fundamental strip
`{c < Im w, 0 ≤ Re w < 1}` of `ℍ`, whose hyperbolic area is `1/c < ∞`. -/
theorem CuspChart.cusp_finite_area [ChartedSpace PoincareDisc (Sᶜ : Set M)] (C : CuspChart S s)
    (hC : C.IsHyperbolicCusp) {m : MetricSpace (Sᶜ : Set M)}
    (hm : IsHyperbolicMetric (Sᶜ : Set M) m) :
    InjOn C.E {w | 0 ≤ (w : ℂ).re ∧ (w : ℂ).re < 1} ∧
    Subtype.val '' (C.E '' {w | 0 ≤ (w : ℂ).re ∧ (w : ℂ).re < 1}) = C.W C.c \ {s} ∧
    (∀ w, ∃ N ∈ 𝓝 w, ∀ w₁ ∈ N, ∀ w₂ ∈ N, @dist _ m.toDist (C.E w₁) (C.E w₂) =
      dist (UpperHalfPlane.mk w₁ (C.c_pos.trans w₁.2)) (UpperHalfPlane.mk w₂ (C.c_pos.trans w₂.2))) ∧
    volume (cuspStrip C.c) = ENNReal.ofReal (1 / C.c) :=
  ⟨C.injOn_E_strip, C.image_E_strip, C.exists_nhds_dist_E hm hC, volume_cuspStrip C.c_pos⟩

end CuspMetric

end CuspArea

/-! ### DEC-81: the geodesic segments of `ℍ`, as a family -/

theorem normSq_unitInterval_mul_lt (t : unitInterval) {w : ℂ} (hw : normSq w < 1) :
    normSq ((t : ℝ) * w) < 1 := by
  rw [normSq_mul, normSq_ofReal]
  have h0 := t.2.1
  have h1 := t.2.2
  have : (t : ℝ) * t ≤ 1 := by nlinarith
  nlinarith [normSq_nonneg w]

/-- The point `mobF 1 (-z) false w` (`w` moved by the isometry sending `z` to `0`). -/
theorem normSq_mobF_neg_lt (z w : PoincareDisc) : normSq (mobF 1 (-(z : ℂ)) false w) < 1 :=
  normSq_mobF_lt false (map_one _) (by rw [normSq_neg]; exact z.normSq_lt) w.normSq_lt

/-- **The geodesic segment from `z` to `w`** in the Poincaré disc: the diameter through `0`,
moved by the isometry `mobF 1 z` sending `0` to `z`. -/
def hypGeod (z w : PoincareDisc) (t : unitInterval) : PoincareDisc :=
  ⟨mobF 1 z false ((t : ℝ) * mobF 1 (-(z : ℂ)) false w), normSq_lt_one_iff.1
    (normSq_mobF_lt false (map_one _) z.normSq_lt
      (normSq_unitInterval_mul_lt t (normSq_mobF_neg_lt z w)))⟩

theorem hypGeod_zero (z w : PoincareDisc) : hypGeod z w 0 = z := by
  apply Subtype.ext
  show mobF 1 z false (((0 : unitInterval) : ℝ) * _) = z
  simp [mobF, sigmaB]

theorem hypGeod_one (z w : PoincareDisc) : hypGeod z w 1 = w := by
  apply Subtype.ext
  show mobF 1 z false (((1 : unitInterval) : ℝ) * _) = w
  simp only [Set.Icc.coe_one, ofReal_one, one_mul]
  exact mobF_one_mobF_neg (a := (z : ℂ)) z.normSq_lt w.normSq_lt.le

theorem hypGeod_self (z : PoincareDisc) (t : unitInterval) : hypGeod z z t = z := by
  apply Subtype.ext
  show mobF 1 z false ((t : ℝ) * mobF 1 (-(z : ℂ)) false z) = z
  rw [mobF_one_neg_self, mul_zero]
  simp [mobF, sigmaB]

theorem continuous_mobF_disc (u a : ℂ) (b : Bool) (hu : normSq u = 1) (ha : normSq a < 1)
    {X : Type*} [TopologicalSpace X] {f : X → ℂ} (hf : Continuous f) (hf1 : ∀ x, normSq (f x) ≤ 1) :
    Continuous fun x => mobF u a b (f x) := by
  unfold mobF
  refine Continuous.div ?_ ?_ fun x => mobDen_ne_zero b hu ha (hf1 x)
  · exact (continuous_const.mul ((continuous_sigmaB _).comp hf)).add continuous_const
  · exact continuous_const.add (continuous_const.mul ((continuous_sigmaB _).comp hf))

/-- The geodesic segments from `z` form a homotopy `I × 𝔻 → 𝔻`. -/
theorem continuous_hypGeod (z : PoincareDisc) :
    Continuous fun p : unitInterval × PoincareDisc => hypGeod z p.2 p.1 := by
  refine Continuous.subtype_mk ?_ _
  have hz' : normSq (-(z : ℂ)) < 1 := by rw [normSq_neg]; exact z.normSq_lt
  have h1 : Continuous fun p : unitInterval × PoincareDisc => mobF 1 (-(z : ℂ)) false p.2 :=
    continuous_mobF_disc 1 _ false (map_one _) hz' (continuous_subtype_val.comp continuous_snd)
      fun p => p.2.normSq_lt.le
  exact continuous_mobF_disc 1 z false (map_one _) z.normSq_lt
    ((continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul h1)
    fun p => (normSq_unitInterval_mul_lt p.1 (normSq_mobF_neg_lt z p.2)).le

theorem continuous_hypGeod' (z w : PoincareDisc) : Continuous (hypGeod z w) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_mobF_disc 1 z false (map_one _) z.normSq_lt
    ((continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
    fun t => (normSq_unitInterval_mul_lt t (normSq_mobF_neg_lt z w)).le

/-- The distances along a geodesic segment are those of a monotone real coordinate. -/
theorem exists_monotone_hypGeod (z w : PoincareDisc) :
    ∃ f : unitInterval → ℝ, Monotone f ∧
      ∀ s t, hypDist (hypGeod z w s) (hypGeod z w t) = dist (f s) (f t) := by
  have hu1 : normSq (1 : ℂ) = 1 := map_one _
  set w' : ℂ := mobF 1 (-(z : ℂ)) false w with hw'
  have hw'1 : normSq w' < 1 := normSq_mobF_neg_lt z w
  have hn : ‖w'‖ < 1 := by have := normSq_lt_one_iff.1 hw'1; simpa using this
  have hseg' : ∀ t : unitInterval, |(t : ℝ) * ‖w'‖| < 1 := by
    intro t
    rw [abs_mul, abs_of_nonneg t.2.1, abs_of_nonneg (norm_nonneg _)]
    calc (t : ℝ) * ‖w'‖ ≤ 1 * ‖w'‖ := mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hn
  refine ⟨fun t => diamCoord ((t : ℝ) * ‖w'‖), fun a b hab =>
    diamCoord_mono (hseg' a) (hseg' b) (mul_le_mul_of_nonneg_right hab (norm_nonneg _)),
    fun s t => ?_⟩
  have e1 : hypDist (hypGeod z w s) (hypGeod z w t) =
      hypDist (diamPt _ (hseg' s)) (diamPt _ (hseg' t)) := by
    rw [hypDist_eq_iff]
    show hypRatio (mobF 1 z false ((s : ℝ) * w')) (mobF 1 z false ((t : ℝ) * w')) =
      hypRatio (((s : ℝ) * ‖w'‖ : ℝ) : ℂ) (((t : ℝ) * ‖w'‖ : ℝ) : ℂ)
    rw [hypRatio_mobF false hu1 z.normSq_lt (normSq_unitInterval_mul_lt s hw'1)
      (normSq_unitInterval_mul_lt t hw'1), hypRatio_smul_eq]
    push_cast; rfl
  rw [e1, hypDist_diamPt]

/-- **The length of a geodesic arc is the distance of its ends.** -/
theorem eVariationOn_hypGeod_le (z w : PoincareDisc) {a b : unitInterval} (hab : a ≤ b) :
    eVariationOn (fun t => toUHP (hypGeod z w t)) (Icc a b) ≤
      ENNReal.ofReal (hypDist (hypGeod z w a) (hypGeod z w b)) := by
  obtain ⟨f, hf, hd⟩ := exists_monotone_hypGeod z w
  have hev : eVariationOn (fun t => toUHP (hypGeod z w t)) (Icc a b) = eVariationOn f (Icc a b) :=
    eVariationOn_congr_edist _ fun s t => by
      rw [edist_dist, edist_dist]; exact congrArg ENNReal.ofReal (hd s t)
  rw [hev, hd, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hf hab))]
  have := (hf.monotoneOn univ).eVariationOn_le (mem_univ a) (mem_univ b)
  rwa [univ_inter] at this


/-! ### DEC-81: metric completeness implies Thurston–Goldman completeness (Hopf–Rinow) -/

/-! #### Metric helpers -/

theorem exists_ball_subset_of_topology_eq {Z : Type*} [t : TopologicalSpace Z] (m : MetricSpace Z)
    (h : m.toUniformSpace.toTopologicalSpace = t) {V : Set Z} (hV : IsOpen V) {y : Z}
    (hy : y ∈ V) : ∃ ρ > 0, ∀ x, @dist Z m.toDist y x < ρ → x ∈ V := by
  subst h
  obtain ⟨ρ, hρ, hb⟩ := @Metric.isOpen_iff Z m.toPseudoMetricSpace V |>.1 hV y hy
  exact ⟨ρ, hρ, fun x hx => hb (by rw [@Metric.mem_ball Z m.toPseudoMetricSpace,
    @dist_comm Z m.toPseudoMetricSpace]; exact hx)⟩

theorem tendsto_of_dist_of_topology_eq {Z : Type*} [t : TopologicalSpace Z] (m : MetricSpace Z)
    (h : m.toUniformSpace.toTopologicalSpace = t) {u : ℕ → Z} {y : Z}
    (hu : Tendsto (fun n => @dist Z m.toDist (u n) y) atTop (𝓝 0)) : Tendsto u atTop (𝓝 y) := by
  subst h
  exact (@tendsto_iff_dist_tendsto_zero Z ℕ m.toPseudoMetricSpace _ _ _).2 hu

theorem exists_dist_tendsto_zero {Z : Type*} (m : MetricSpace Z)
    (hcomp : @CompleteSpace Z m.toUniformSpace) {u : ℕ → Z} {δ : ℕ → ℝ}
    (hu : ∀ n n', n ≤ n' → @dist Z m.toDist (u n) (u n') ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ y, Tendsto (fun n => @dist Z m.toDist (u n) y) atTop (𝓝 0) := by
  letI := m
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0' δ hu hδ)
  exact ⟨y, tendsto_iff_dist_tendsto_zero.1 hy⟩


section HopfRinow

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]

/-- The situation of the universal cover `q : E → Y` of a `(G, ℍ)`-surface with a hyperbolic
metric `m` and a developing map `dev : E → 𝔻`: `q` is a covering map, `dev` a local homeomorphism,
and `dev` is near every point an isometry for the metric of `Y` read through `q`. -/
structure IsDevLocalIsometry (m : MetricSpace Y) (q : E → Y) (dev : E → PoincareDisc) : Prop where
  topology_eq : m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace Y›
  covering : IsCoveringMap q
  local_homeo : IsLocalHomeomorph dev
  local_isometry : ∀ e, ∃ U ∈ 𝓝 e, ∀ e₁ ∈ U, ∀ e₂ ∈ U,
    @dist Y m.toDist (q e₁) (q e₂) = hypDist (dev e₁) (dev e₂)

variable {m : MetricSpace Y} {q : E → Y} {dev : E → PoincareDisc}

/-- The unit interval point of a real number. -/
abbrev projI (x : ℝ) : unitInterval := projIcc 0 1 zero_le_one x

theorem coe_toI {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : ((projI x : unitInterval) : ℝ) = x := by
  rw [coe_projIcc, min_eq_right h1, max_eq_right h0]

theorem continuous_toI : Continuous projI := continuous_projIcc

namespace IsDevLocalIsometry

variable (H : IsDevLocalIsometry m q dev)
include H

/-- **Along a lift of a geodesic arc, the projection is `1`-Lipschitz**: the metric of `Y`
between two points of the projected path is at most the hyperbolic distance of their
developments (the length of the projected arc is that of the geodesic). -/
theorem dist_le_of_lift {z w : PoincareDisc} {Λ : C(unitInterval, E)} {T : ℝ}
    (hΛ : ∀ t : unitInterval, (t : ℝ) ≤ T → dev (Λ t) = hypGeod z w t) {a b : unitInterval}
    (hab : a ≤ b) (hbT : (b : ℝ) ≤ T) :
    @dist Y m.toDist (q (Λ a)) (q (Λ b)) ≤ hypDist (hypGeod z w a) (hypGeod z w b) := by
  letI := m
  set φ : unitInterval → unitInterval := fun u => projI (a + u * (b - a)) with hφdef
  have hab' : (a : ℝ) ≤ b := hab
  have hφv : ∀ u : unitInterval, ((φ u : unitInterval) : ℝ) = a + u * (b - a) := fun u => by
    have h1 : (0 : ℝ) ≤ a + u * (b - a) := by
      have := a.2.1; have := u.2.1; nlinarith
    have h2 : (a : ℝ) + u * (b - a) ≤ 1 := by
      have := b.2.2; have := u.2.2; nlinarith
    exact coe_toI h1 h2
  have hφc : Continuous φ := continuous_toI.comp (continuous_const.add
    (continuous_subtype_val.mul continuous_const))
  have hφm : Monotone φ := fun u v huv => by
    show (φ u : ℝ) ≤ φ v
    rw [hφv, hφv]
    have : (u : ℝ) ≤ v := huv
    nlinarith
  have hφab : ∀ u, a ≤ φ u ∧ φ u ≤ b := fun u => by
    constructor
    · show (a : ℝ) ≤ φ u
      rw [hφv]; have := u.2.1; nlinarith
    · show (φ u : ℝ) ≤ b
      rw [hφv]; have := u.2.2; nlinarith
  have hφ0 : φ 0 = a := Subtype.ext (by rw [hφv]; simp)
  have hφ1 : φ 1 = b := Subtype.ext (by rw [hφv]; simp)
  set F : unitInterval → Y := fun u => q (Λ (φ u))
  set G : unitInterval → ℍ := fun u => toUHP (hypGeod z w (φ u))
  have hloc : ∀ u, ∃ N ∈ 𝓝 u, ∀ u₁ ∈ N, ∀ u₂ ∈ N, edist (F u₁) (F u₂) = edist (G u₁) (G u₂) := by
    intro u
    obtain ⟨U, hU, hUd⟩ := H.local_isometry (Λ (φ u))
    refine ⟨(fun v => Λ (φ v)) ⁻¹' U,
      (Λ.continuous.comp hφc).continuousAt.preimage_mem_nhds hU, fun u₁ h₁ u₂ h₂ => ?_⟩
    rw [edist_dist, edist_dist]
    congr 1
    have e1 := hUd _ h₁ _ h₂
    simp only [F, G]
    rw [e1, hΛ _ ((show ((φ u₁ : unitInterval) : ℝ) ≤ b from (hφab u₁).2).trans hbT),
      hΛ _ ((show ((φ u₂ : unitInterval) : ℝ) ≤ b from (hφab u₂).2).trans hbT)]
    rfl
  have hvar := eVariationOn_eq_of_locally hloc
  have h1 : edist (F 0) (F 1) ≤ eVariationOn F univ := eVariationOn.edist_le F (mem_univ _) (mem_univ _)
  have h2 : eVariationOn G univ ≤ eVariationOn (fun t => toUHP (hypGeod z w t)) (Icc a b) :=
    eVariationOn.comp_le_of_monotoneOn _ φ (hφm.monotoneOn _) fun u _ => hφab u
  have h3 := eVariationOn_hypGeod_le z w hab
  have := (h1.trans (hvar.trans_le h2)).trans h3
  simp only [F, hφ0, hφ1] at this
  rw [edist_dist] at this
  exact (ENNReal.ofReal_le_ofReal_iff (hypDist_nonneg _ _)).1 this

/-- Lifts of a geodesic arc from the same point agree where both are lifts. -/
theorem lift_unique [T2Space E] {c : unitInterval → PoincareDisc} {Λ Λ' : C(unitInterval, E)}
    {T T' : ℝ} (h0 : Λ 0 = Λ' 0) (hΛ : ∀ t : unitInterval, (t : ℝ) ≤ T → dev (Λ t) = c t)
    (hΛ' : ∀ t : unitInterval, (t : ℝ) ≤ T' → dev (Λ' t) = c t) {t : unitInterval}
    (ht : (t : ℝ) ≤ min T T') : Λ t = Λ' t := by
  set r := min T T'
  have hr : 0 ≤ r := (t.2.1).trans ht
  set s : Set unitInterval := {t | (t : ℝ) ≤ r}
  have hs : s = projI '' Icc 0 r := by
    ext x
    constructor
    · intro hx
      exact ⟨x, ⟨x.2.1, hx⟩, Subtype.ext (coe_toI x.2.1 x.2.2)⟩
    · rintro ⟨y, ⟨hy0, hyr⟩, rfl⟩
      show ((projI y : unitInterval) : ℝ) ≤ r
      rw [coe_projIcc]
      exact (max_le hr (min_le_right _ _ |>.trans hyr))
  have hsc : IsPreconnected s := hs ▸ isPreconnected_Icc.image _ continuous_toI.continuousOn
  refine (T2Space.isSeparatedMap dev).eqOn_of_comp_eqOn H.local_homeo.isLocallyInjective hsc
    Λ.continuous.continuousOn Λ'.continuous.continuousOn (fun x hx => ?_)
    (show (0 : unitInterval) ∈ s from show ((0 : unitInterval) : ℝ) ≤ r from hr) h0 ht
  show dev (Λ x) = dev (Λ' x)
  rw [hΛ x (hx.trans (min_le_left _ _)), hΛ' x (hx.trans (min_le_right _ _))]



end IsDevLocalIsometry

/-- `Λ` lifts the path `c` through `dev` from `e₀` up to time `T`. -/
def LiftsTo (dev : E → PoincareDisc) (e₀ : E) (c : unitInterval → PoincareDisc) (T : ℝ) : Prop :=
  ∃ Λ : C(unitInterval, E), Λ 0 = e₀ ∧ ∀ t : unitInterval, (t : ℝ) ≤ T → dev (Λ t) = c t

theorem LiftsTo.mono {e₀ : E} {c : unitInterval → PoincareDisc} {T T' : ℝ}
    (h : LiftsTo dev e₀ c T) (hT : T' ≤ T) : LiftsTo dev e₀ c T' :=
  let ⟨Λ, h0, hΛ⟩ := h; ⟨Λ, h0, fun t ht => hΛ t (ht.trans hT)⟩

theorem projI_clamp_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (t : unitInterval) :
    ((projI (max a (min t b)) : unitInterval) : ℝ) = max a (min t b) ∧ a ≤ max a (min t b) ∧
      max a (min t b) ≤ b :=
  ⟨coe_toI (ha.trans (le_max_left _ _)) ((max_le hab (min_le_right _ _)).trans hb),
    le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem projI_clamp_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {t : unitInterval}
    (h1 : a ≤ t) (h2 : (t : ℝ) ≤ b) : projI (max a (min t b)) = t := by
  apply Subtype.ext
  rw [(projI_clamp_bounds ha hab hb t).1, min_eq_left h2, max_eq_right h1]

/-- Gluing a lift up to time `a` with a lift through a chart of `dev` after `a`. -/
theorem liftsTo_glue {e₀ : E} {c : unitInterval → PoincareDisc} (hc : Continuous c)
    {Λ : C(unitInterval, E)} (hΛ0 : Λ 0 = e₀) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hΛ : ∀ t : unitInterval, (t : ℝ) ≤ a → dev (Λ t) = c t)
    (h : OpenPartialHomeomorph E PoincareDisc) (hdh : dev = h)
    (hsrc : Λ (projI a) ∈ h.source)
    (htgt : ∀ t : unitInterval, c (projI (max a (min t b))) ∈ h.target) :
    LiftsTo dev e₀ c b := by
  set clamp : unitInterval → unitInterval := fun t => projI (max a (min t b))
  have hclc : Continuous clamp :=
    continuous_toI.comp (continuous_const.max (continuous_subtype_val.min continuous_const))
  have hta : ((projI a : unitInterval) : ℝ) = a := coe_toI ha (hab.trans hb)
  have hagree : ∀ t : unitInterval, (t : ℝ) = a → Λ t = h.symm (c (clamp t)) := by
    intro t ht
    have htt : t = projI a := Subtype.ext (ht.trans hta.symm)
    have hcl : clamp t = t := projI_clamp_eq ha hab hb ht.ge (ht.le.trans hab)
    rw [hcl, htt, ← hΛ _ hta.le, hdh, h.left_inv hsrc]
  let Λ' : C(unitInterval, E) := ⟨fun t => if (t : ℝ) ≤ a then Λ t else h.symm (c (clamp t)),
    Continuous.if_le Λ.continuous (h.continuousOn_symm.comp_continuous (hc.comp hclc) htgt)
      continuous_subtype_val continuous_const hagree⟩
  refine ⟨Λ', ?_, fun t ht => ?_⟩
  · show (if ((0 : unitInterval) : ℝ) ≤ a then Λ 0 else _) = e₀
    rw [if_pos (by simpa using ha), hΛ0]
  · show dev (if (t : ℝ) ≤ a then Λ t else h.symm (c (clamp t))) = c t
    split_ifs with hta'
    · exact hΛ t hta'
    · have hcl : clamp t = t := projI_clamp_eq ha hab hb (not_le.1 hta').le ht
      have : c (clamp t) ∈ h.target := htgt t
      rw [hcl] at this ⊢
      rw [hdh]
      exact h.right_inv this

/-- **The extension step**: a lift up to a time `T < 1` extends past `T`. -/
theorem LiftsTo.extend (hdev : IsLocalHomeomorph dev) {e₀ : E} {c : unitInterval → PoincareDisc}
    (hc : Continuous c) {T : ℝ} (h : LiftsTo dev e₀ c T) (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ T' > T, LiftsTo dev e₀ c T' := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := h
  have htT : ((projI T : unitInterval) : ℝ) = T := coe_toI hT0 hT1.le
  obtain ⟨h, heh, hdh⟩ := hdev (Λ (projI T))
  have hcT : c (projI T) ∈ h.target := by
    rw [← hΛ _ htT.le, hdh]; exact h.map_source heh
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (h.open_target.preimage hc) (projI T) hcT
  set b := min (T + η / 2) 1
  have hTb : T < b := lt_min (by linarith) hT1
  refine ⟨b, hTb, liftsTo_glue hc hΛ0 hT0 hTb.le (min_le_right _ _) hΛ h hdh heh fun t => ?_⟩
  apply hball
  obtain ⟨e1, e2, e3⟩ := projI_clamp_bounds hT0 hTb.le (min_le_right _ _) t
  rw [Metric.mem_ball, Subtype.dist_eq, e1, htT, Real.dist_eq, abs_lt]
  have : b ≤ T + η / 2 := min_le_left _ _
  constructor <;> linarith



namespace IsDevLocalIsometry

variable (H : IsDevLocalIsometry m q dev)
include H

/-- **The limit step** (where completeness is used): a geodesic arc which lifts up to every time
before `s` lifts up to `s`. The projections of the lifts are Cauchy (they are `1`-Lipschitz
along the arc), converge in the complete `Y`, and the tail of the lifts lies in one sheet of `q`
over the limit, hence converges in `E`; a chart of `dev` at the limit continues the lift. -/
theorem liftsTo_of_forall_lt [T2Space E] (hcomp : @CompleteSpace Y m.toUniformSpace) {e₀ : E}
    {w : PoincareDisc} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hP : ∀ T, 0 ≤ T → T < s → LiftsTo dev e₀ (hypGeod (dev e₀) w) T) :
    LiftsTo dev e₀ (hypGeod (dev e₀) w) s := by
  set c := hypGeod (dev e₀) w with hcdef
  have hc : Continuous c := continuous_hypGeod' _ _
  obtain ⟨f, hfm, hfd⟩ := exists_monotone_hypGeod (dev e₀) w
  set Tn : ℕ → ℝ := fun n => s - s / (n + 2) with hTndef
  have hTn0 : ∀ n, 0 ≤ Tn n := fun n => by
    have : s / (n + 2) ≤ s := div_le_self hs0.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    simp only [hTndef]; linarith
  have hTns : ∀ n, Tn n < s := fun n => by
    have : 0 < s / (n + 2) := div_pos hs0 (by positivity)
    simp only [hTndef]; linarith
  have hTnm : Monotone Tn := fun n n' hnn' => by
    simp only [hTndef]
    have : s / ((n' : ℝ) + 2) ≤ s / (n + 2) :=
      div_le_div_of_nonneg_left hs0.le (by positivity) (by exact_mod_cast (by omega : n + 2 ≤ n' + 2))
    linarith
  have hTnlim : Tendsto Tn atTop (𝓝 s) := by
    have h1 : Tendsto (fun n : ℕ => s / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul s
      rw [mul_zero] at this
      refine (this.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      simp only [comp_apply, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    have := tendsto_const_nhds (x := s).sub h1
    rw [sub_zero] at this
    exact this
  choose Λ hΛ0 hΛ using fun n => hP (Tn n) (hTn0 n) (hTns n)
  set tn : ℕ → unitInterval := fun n => projI (Tn n) with htndef
  have htn : ∀ n, ((tn n : unitInterval) : ℝ) = Tn n := fun n => coe_toI (hTn0 n) ((hTns n).le.trans hs1)
  set ts : unitInterval := projI s
  have hts : (ts : ℝ) = s := coe_toI hs0.le hs1
  have htnlim : Tendsto tn atTop (𝓝 ts) := (continuous_toI.tendsto s).comp hTnlim
  have hcons : ∀ n n', n ≤ n' → ∀ t : unitInterval, (t : ℝ) ≤ Tn n → Λ n t = Λ n' t :=
    fun n n' hnn' t ht => H.lift_unique ((hΛ0 n).trans (hΛ0 n').symm) (hΛ n) (hΛ n')
      (le_min ht (ht.trans (hTnm hnn')))
  -- the hyperbolic distance from `c (tn n)` to the end `c ts`
  set δ : ℕ → ℝ := fun n => hypDist (c (tn n)) (c ts) with hδdef
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => toUHP (c (tn n))) atTop (𝓝 (toUHP (c ts))) :=
      ((continuous_toUHP.comp hc).tendsto ts).comp htnlim
    exact (tendsto_iff_dist_tendsto_zero.1 h1)
  have htn_le : ∀ n, tn n ≤ ts := fun n => show (tn n : ℝ) ≤ ts by rw [htn, hts]; exact (hTns n).le
  have hδt : ∀ n (t : unitInterval), tn n ≤ t → t ≤ ts → hypDist (c (tn n)) (c t) ≤ δ n := by
    intro n t h1 h2
    simp only [hδdef]
    rw [hfd, hfd, Real.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hfm h1)),
      abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hfm (h1.trans h2)))]
    linarith [hfm h2]
  -- the projections
  set y : ℕ → Y := fun n => q (Λ n (tn n)) with hydef
  have hyd : ∀ n n', n ≤ n' → @dist Y m.toDist (y n) (y n') ≤ δ n := by
    intro n n' hnn'
    have e1 : Λ n (tn n) = Λ n' (tn n) := hcons n n' hnn' _ (htn n).le
    simp only [hydef]
    rw [e1]
    refine (H.dist_le_of_lift (hΛ n') (show (tn n : ℝ) ≤ tn n' by rw [htn, htn]; exact hTnm hnn')
      (htn n').le).trans ?_
    exact hδt n (tn n') (show (tn n : ℝ) ≤ tn n' by rw [htn, htn]; exact hTnm hnn') (htn_le n')
  obtain ⟨y', hy'⟩ := exists_dist_tendsto_zero m hcomp hyd hδ
  have hyo : Tendsto y atTop (𝓝 y') := tendsto_of_dist_of_topology_eq m H.topology_eq hy'
  -- the sheets of `q` over `y'`
  obtain ⟨V, hVo, hy'V, S, hSo, hSinj, -, hSsurj, hSd, hScov⟩ := IsEvenlyCovered.exists_sheets (H.covering y')
  obtain ⟨ρ, hρ, hρV⟩ := exists_ball_subset_of_topology_eq m H.topology_eq hVo hy'V
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hy'.eventually (gt_mem_nhds (half_pos hρ))).and
    (hδ.eventually (gt_mem_nhds (half_pos hρ))))
  have htail : ∀ n, N ≤ n → ∀ t : unitInterval, tn N ≤ t → (t : ℝ) ≤ Tn n → q (Λ n t) ∈ V := by
    intro n hn t h1 h2
    apply hρV
    have e1 : q (Λ n (tn N)) = y N := by
      simp only [hydef]; rw [hcons N n hn _ (htn N).le]
    have hd1 : @dist Y m.toDist (y N) (q (Λ n t)) ≤ δ N := by
      rw [← e1]
      refine (H.dist_le_of_lift (hΛ n) h1 h2).trans (hδt N t h1 ?_)
      show (t : ℝ) ≤ ts; rw [hts]; exact h2.trans (hTns n).le
    have hd2 := (hN N le_rfl).1
    have := @dist_triangle Y m.toPseudoMetricSpace y' (y N) (q (Λ n t))
    rw [@dist_comm Y m.toPseudoMetricSpace y' (y N)] at this
    have := (hN N le_rfl).2
    linarith
  have hmemV : Λ N (tn N) ∈ q ⁻¹' V := htail N le_rfl (tn N) le_rfl (htn N).le
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hScov hmemV)
  have hsheet : ∀ n, N ≤ n → Λ n (tn n) ∈ S j := by
    intro n hn
    set seg := (fun t => Λ n t) '' (projI '' Icc (Tn N) (Tn n))
    have hseg : IsPreconnected seg :=
      (isPreconnected_Icc.image _ continuous_toI.continuousOn).image _ (Λ n).continuous.continuousOn
    have hsub : seg ⊆ ⋃ j, S j := by
      rintro _ ⟨t, ⟨x, ⟨hx1, hx2⟩, rfl⟩, rfl⟩
      have hx : ((projI x : unitInterval) : ℝ) = x :=
        coe_toI ((hTn0 N).trans hx1) (hx2.trans ((hTns n).le.trans hs1))
      refine hScov (htail n hn _ (show (tn N : ℝ) ≤ projI x by rw [hx, htn]; exact hx1) ?_)
      rw [hx]; exact hx2
    have hne : (seg ∩ S j).Nonempty := ⟨Λ n (tn N), ⟨tn N, ⟨Tn N, ⟨le_rfl, hTnm hn⟩, rfl⟩, rfl⟩,
      by rw [← hcons N n hn _ (htn N).le]; exact hj⟩
    exact GX.IsPreconnected.subset_of_pairwise_disjoint hSo hSd hseg hsub hne
      ⟨tn n, ⟨Tn n, ⟨hTnm hn, le_rfl⟩, rfl⟩, rfl⟩
  -- the limit point `e'` of the lifts, in the sheet `S j`
  obtain ⟨e', he'S, he'y⟩ := hSsurj j hy'V
  obtain ⟨k, hke', hqk⟩ := H.covering.isLocalHomeomorph e'
  have hk_y' : y' ∈ k.target := by rw [← he'y, hqk]; exact k.map_source hke'
  have hksymm : k.symm y' = e' := by rw [← he'y, hqk]; exact k.left_inv hke'
  have hcont : Tendsto (fun n => k.symm (y n)) atTop (𝓝 e') :=
    hksymm ▸ ((k.continuousAt_symm hk_y').tendsto.comp hyo)
  have hev2 : ∀ᶠ n in atTop, y n ∈ k.target ∧ k.symm (y n) ∈ S j ∧ N ≤ n :=
    ((hyo.eventually (k.open_target.mem_nhds hk_y')).and
      ((hcont.eventually ((hSo j).mem_nhds he'S)).and (eventually_ge_atTop N)))
  have hΛeq : ∀ᶠ n in atTop, Λ n (tn n) = k.symm (y n) := hev2.mono fun n ⟨h1, h2, h3⟩ =>
    hSinj j (hsheet n h3) h2 (by rw [hqk, k.right_inv h1]; exact (congrFun hqk _).symm)
  have hΛlim : Tendsto (fun n => Λ n (tn n)) atTop (𝓝 e') :=
    hcont.congr' (hΛeq.mono fun n h => h.symm)
  have hdev_e' : dev e' = c ts := by
    refine tendsto_nhds_unique ((H.local_homeo.continuous.tendsto e').comp hΛlim) ?_
    refine (((hc.tendsto ts).comp htnlim)).congr fun n => ?_
    exact (hΛ n (tn n) (htn n).le).symm
  -- a chart of `dev` at `e'` continues the lift
  obtain ⟨h, heh, hdh⟩ := H.local_homeo e'
  have hcs : c ts ∈ h.target := by rw [← hdev_e', hdh]; exact h.map_source heh
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (h.open_target.preimage hc) ts hcs
  obtain ⟨n₁, hn₁s, hn₁d⟩ := ((hΛlim.eventually (h.open_source.mem_nhds heh)).and
    (htnlim.eventually (Metric.ball_mem_nhds ts hη))).exists
  refine liftsTo_glue hc (hΛ0 n₁) (hTn0 n₁) (hTns n₁).le hs1 (hΛ n₁) h hdh hn₁s fun t => ?_
  apply hball
  obtain ⟨e1, e2, e3⟩ := projI_clamp_bounds (hTn0 n₁) (hTns n₁).le hs1 t
  have hd : dist (tn n₁) ts < η := hn₁d
  rw [Subtype.dist_eq, htn, hts, Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hTns n₁])] at hd
  rw [Metric.mem_ball, Subtype.dist_eq, e1, hts, Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (by linarith)]
  linarith


/-- **Geodesic lifting**: in a complete hyperbolic surface, every geodesic arc of `ℍ` from the
development of a point lifts through the developing map. -/
theorem exists_lift_hypGeod [T2Space E] (hcomp : @CompleteSpace Y m.toUniformSpace) (e₀ : E)
    (w : PoincareDisc) :
    ∃ Λ : C(unitInterval, E), Λ 0 = e₀ ∧ ∀ t, dev (Λ t) = hypGeod (dev e₀) w t := by
  set c := hypGeod (dev e₀) w
  have hc : Continuous c := continuous_hypGeod' _ _
  have h0 : LiftsTo dev e₀ c 0 := ⟨ContinuousMap.const _ e₀, rfl, fun t ht => by
    have : t = 0 := Subtype.ext (le_antisymm ht t.2.1)
    rw [this]
    exact (hypGeod_zero _ _).symm⟩
  set A : Set ℝ := {T | 0 ≤ T ∧ T ≤ 1 ∧ LiftsTo dev e₀ c T}
  have hA0 : (0 : ℝ) ∈ A := ⟨le_rfl, zero_le_one, h0⟩
  have hbdd : BddAbove A := ⟨1, fun T hT => hT.2.1⟩
  set s := sSup A
  have hs0 : 0 ≤ s := le_csSup hbdd hA0
  have hs1 : s ≤ 1 := csSup_le ⟨0, hA0⟩ fun T hT => hT.2.1
  have hPs : LiftsTo dev e₀ c s := by
    rcases hs0.lt_or_eq with hs | hs
    · refine H.liftsTo_of_forall_lt hcomp hs hs1 fun T _ hTs => ?_
      obtain ⟨T', hT'A, hTT'⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ hTs
      exact hT'A.2.2.mono hTT'.le
    · rw [← hs]; exact h0
  have hs_eq : s = 1 := by
    by_contra hne
    obtain ⟨T', hT', hP'⟩ := hPs.extend H.local_homeo hc hs0 (lt_of_le_of_ne hs1 hne)
    have hmem : min T' 1 ∈ A := ⟨hs0.trans (le_min hT'.le hs1), min_le_right _ _,
      hP'.mono (min_le_left _ _)⟩
    have := le_csSup hbdd hmem
    have : s < min T' 1 := lt_min hT' (lt_of_le_of_ne hs1 hne)
    linarith
  rw [hs_eq] at hPs
  obtain ⟨Λ, hΛ0, hΛ⟩ := hPs
  exact ⟨Λ, hΛ0, fun t => hΛ t t.2.2⟩

/-- **Hopf–Rinow for hyperbolic surfaces**: the developing map of a connected cover of a complete
hyperbolic surface (in the situation `GX.IsDevLocalIsometry`) is a homeomorphism onto `ℍ`. The
geodesic arcs from the development of a base point lift (`exists_lift_hypGeod`); the lifts
depend continuously on the end (mathlib's `IsLocalHomeomorph.continuous_lift`), giving a
continuous section, which is onto by connectedness. -/
theorem exists_homeomorph [T2Space E] [PreconnectedSpace E] [Nonempty E]
    (hcomp : @CompleteSpace Y m.toUniformSpace) : ∃ Θ : E ≃ₜ PoincareDisc, ⇑Θ = dev := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  set z₀ := dev e₀
  choose Λ hΛ0 hΛ using fun w => H.exists_lift_hypGeod hcomp e₀ w
  have sep := T2Space.isSeparatedMap dev
  have inj := H.local_homeo.isLocallyInjective
  set g : unitInterval × PoincareDisc → E := fun p => Λ p.2 p.1 with hgdef
  let F : C(unitInterval × PoincareDisc, PoincareDisc) :=
    ⟨fun p => hypGeod z₀ p.2 p.1, continuous_hypGeod z₀⟩
  have hg : Continuous g := H.local_homeo.continuous_lift sep F (funext fun p => hΛ p.2 p.1)
    (by simp only [hgdef, hΛ0]; exact continuous_const) fun w => (Λ w).continuous
  set σ : PoincareDisc → E := fun w => g (1, w) with hσdef
  have hσc : Continuous σ := hg.comp (continuous_const.prodMk continuous_id)
  have hσ : ∀ w, dev (σ w) = w := fun w => (hΛ w 1).trans (hypGeod_one _ _)
  have hσ0 : σ z₀ = e₀ := by
    have : (Λ z₀ : unitInterval → E) = fun _ => e₀ :=
      sep.eq_of_comp_eq inj (Λ z₀).continuous continuous_const
        (funext fun t => by simp only [comp_apply]; rw [hΛ, hypGeod_self]) 0 (hΛ0 z₀)
    exact congrFun this 1
  have hσdev : ∀ e, σ (dev e) = e := fun e => congrFun (sep.eq_of_comp_eq inj
    (hσc.comp H.local_homeo.continuous) continuous_id
    (funext fun e => by simp only [comp_apply, hσ, id]) e₀ (by simp only [comp_apply, id]; exact hσ0))
    e
  exact ⟨⟨⟨dev, σ, hσdev, hσ⟩, H.local_homeo.continuous, hσc⟩, rfl⟩

end IsDevLocalIsometry

end HopfRinow


section HopfRinowSurface

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace PoincareDisc Y]
  [HasGroupoid Y (gxGroupoid HypIsom PoincareDisc)]

theorem IsHyperbolicMetric.t2Space {m : MetricSpace Y} (hm : IsHyperbolicMetric Y m) :
    T2Space Y := by
  have h : @T2Space Y m.toUniformSpace.toTopologicalSpace := inferInstance
  rwa [hm.topology_eq] at h

/-- **Hopf–Rinow for hyperbolic surfaces** (DEC-81): a hyperbolic surface whose hyperbolic metric
is complete is complete in Thurston's and Goldman's sense — every developing map of its universal
cover is a covering map (indeed a homeomorphism onto `ℍ`). -/
theorem IsHyperbolicMetric.isCompleteHyperbolic {m : MetricSpace Y} (hm : IsHyperbolicMetric Y m)
    (hcomp : @CompleteSpace Y m.toUniformSpace) : IsCompleteHyperbolic Y := by
  intro _ hY y₀ dev hdev
  letI := coverChartedSpace PoincareDisc hY y₀
  haveI := hm.t2Space
  have hcov := UniversalCover.isCoveringMap_proj (y₀ := y₀) hY
  haveI : T2Space (UniversalCover Y y₀) := t2Space_of_isCoveringMap hcov
  have hLI : ∀ e, ∃ U ∈ 𝓝 e, ∀ e₁ ∈ U, ∀ e₂ ∈ U, @dist Y m.toDist (UniversalCover.proj Y y₀ e₁)
      (UniversalCover.proj Y y₀ e₂) = hypDist (dev e₁) (dev e₂) := by
    intro e
    obtain ⟨g, hg⟩ := (isGXMorphism_iff_model.1 hdev).2 e
    obtain ⟨V, hV, hVd⟩ := hm.local_isometry (UniversalCover.proj Y y₀ e)
    refine ⟨UniversalCover.proj Y y₀ ⁻¹' V ∩ {e' | dev e' = g • chartAt PoincareDisc e e'},
      Filter.inter_mem (UniversalCover.continuous_proj.continuousAt.preimage_mem_nhds hV) hg,
      fun e₁ h₁ e₂ h₂ => ?_⟩
    rw [hVd _ h₁.1 _ h₂.1, h₁.2, h₂.2, HypIsom.hypDist_smul, pullback_chartAt_apply,
      pullback_chartAt_apply]
  have H : IsDevLocalIsometry m (UniversalCover.proj Y y₀) dev :=
    ⟨hm.topology_eq, hcov, hdev.isLocalHomeomorph, hLI⟩
  obtain ⟨Θ, hΘ⟩ := H.exists_homeomorph hcomp
  rw [← hΘ]
  exact isCoveringMap_of_homeomorph Θ

/-- **Metric completeness is Thurston–Goldman completeness** (DEC-81): for a hyperbolic metric
on a connected, locally path-connected, semilocally simply connected `(Isom ℍ, ℍ)`-surface, the
metric is complete iff every developing map of the universal cover is a covering map. -/
theorem IsHyperbolicMetric.completeSpace_iff [LocPathConnectedSpace Y] [ConnectedSpace Y]
    {m : MetricSpace Y} (hm : IsHyperbolicMetric Y m) (hY : SemilocallySimplyConnected Y) :
    @CompleteSpace Y m.toUniformSpace ↔ IsCompleteHyperbolic Y := by
  refine ⟨hm.isCompleteHyperbolic, fun hc => ?_⟩
  haveI := hm.t2Space
  obtain ⟨m', hm', hc'⟩ := hc.exists_isHyperbolicMetric hY
  rwa [hm.unique hm']

end HopfRinowSurface

/-! ### DEC-81: `ex:take_closed_unit_disc` under the metric reading -/

section MetricExample

variable {M : Type*} [TopologicalSpace M] {S : Set M} [ChartedSpace PoincareDisc (Sᶜ : Set M)]

variable (M S) in
/-- **The data of `ex:take_closed_unit_disc` under the metric reading** (DEC-81): `S ⊆ M` finite
and `M ∖ S` a `(G, ℍ)`-surface (`G = Isom ℍ`) carrying a **complete hyperbolic metric** `m`
(`GX.IsHyperbolicMetric`: a length metric giving the topology, locally the metric of `ℍ` in the
charts; complete as a metric space), with a hyperbolic cusp at every point of `S` (the
finite-volume ends; the thick–thin step finite volume ⇒ cusps is not built). -/
structure IsCuspedHyperbolicMetric (m : MetricSpace (Sᶜ : Set M)) : Prop where
  finite : S.Finite
  hasGroupoid : HasGroupoid (Sᶜ : Set M) (gxGroupoid HypIsom PoincareDisc)
  metric : IsHyperbolicMetric (Sᶜ : Set M) m
  complete : @CompleteSpace (Sᶜ : Set M) m.toUniformSpace
  cusp : ∀ s ∈ S, ∃ C : CuspChart S s, C.IsHyperbolicCusp

/-- Metric completeness gives the `(G, X)` reading: by Hopf–Rinow
(`GX.IsHyperbolicMetric.isCompleteHyperbolic`), the surface is complete in Thurston's and
Goldman's sense. -/
theorem IsCuspedHyperbolicMetric.isCuspedHyperbolic {m : MetricSpace (Sᶜ : Set M)}
    (H : IsCuspedHyperbolicMetric M S m) : IsCuspedHyperbolic M S :=
  { finite := H.finite
    hasGroupoid := H.hasGroupoid
    complete := by
      haveI := H.hasGroupoid
      exact @IsHyperbolicMetric.isCompleteHyperbolic _ _ _ _ _ H.metric H.complete
    cusp := H.cusp }

/-- Conversely, the `(G, X)` reading carries **a unique hyperbolic metric, and it is complete**:
the two readings of the hypothesis of `ex:take_closed_unit_disc` agree. -/
theorem IsCuspedHyperbolic.exists_unique_metric [T2Space M] [LocPathConnectedSpace M]
    [ConnectedSpace M] (H : IsCuspedHyperbolic M S) :
    ∃ m : MetricSpace (Sᶜ : Set M), IsCuspedHyperbolicMetric M S m ∧
      ∀ m' : MetricSpace (Sᶜ : Set M), IsHyperbolicMetric (Sᶜ : Set M) m' → m' = m := by
  letI := H.singularStructure
  haveI := H.hasGroupoid
  have hSing := H.sing_eq
  have hY : SemilocallySimplyConnected (Sᶜ : Set M) :=
    semilocallySimplyConnected_compl_of_sing_subset isLocallyUnloopable_closedDisc H.isClosed
      hSing.le
  haveI : LocPathConnectedSpace (Sᶜ : Set M) := H.isClosed.isOpen_compl.locPathConnectedSpace
  haveI : ConnectedSpace (Sᶜ : Set M) := isConnected_iff_connectedSpace.1 H.isPortly_compl.isConnected
  obtain ⟨m, hm, hc⟩ := IsCompleteHyperbolic.exists_isHyperbolicMetric H.complete hY
  exact ⟨m, ⟨H.finite, H.hasGroupoid, hm, hc, H.cusp⟩, fun m' hm' => hm'.unique hm⟩

variable [T2Space M] [LocPathConnectedSpace M] [FirstCountableTopology M] [ConnectedSpace M]

variable (M S) in
/-- **`ex:take_closed_unit_disc` under the metric reading** (`RamcovGX.tex:1877`, DEC-81, DEC-71).
`M ∖ S` with a complete hyperbolic metric and a cusp at every point of the finite `S`
(`GX.IsCuspedHyperbolicMetric`). Then every assertion of the example holds: `M` is a singular
`(G, X)`-manifold with `sing(M) = S`, tamely singular, every developing map
`\widetilde M → X` is injective, every singular point of `\widetilde M` has arbitrarily small
neighbourhoods homeomorphic to `{r < r₀} ⊆ 𝔻_∞` mapped onto a horodisc with its centre, not
open in `X` (`GX.take_closed_unit_disc`, through Hopf–Rinow); and **the cusps have finite
area**: at each `s ∈ S` the punctured cusp neighbourhood is the injective image, under a local
isometry, of a strip of hyperbolic area `1/c`. -/
theorem take_closed_unit_disc_metric {m : MetricSpace (Sᶜ : Set M)}
    (H : IsCuspedHyperbolicMetric M S m) :
    (letI := H.isCuspedHyperbolic.singularStructure
    Sing HypIsom ClosedDisc M = S ∧ IsTame HypIsom ClosedDisc M ∧
    ∀ y₀ : ((Sing HypIsom ClosedDisc M)ᶜ : Set M),
      (∃ D : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀ → ClosedDisc,
        IsDevelopingMapOf HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base D) ∧
      (∀ x : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀,
        x ∉ support (aePullback HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base) ↔
          x.base ∈ Sing HypIsom ClosedDisc M) ∧
      ∀ D : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀ → ClosedDisc,
        IsDevelopingMapOf HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base D →
        Injective D ∧ ∀ x : MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀,
          x ∉ support (aePullback HypIsom (aeAtlas HypIsom ClosedDisc M) SpreadEnd.base) →
          ‖(D x : ℂ)‖ = 1 ∧
          ∀ N ∈ 𝓝 x, ∃ U : Set (MaxBranchedCover (Sing HypIsom ClosedDisc M) y₀), IsOpen U ∧
            ∃ hxU : x ∈ U, U ⊆ N ∧
            (∃ r₀ > 0, ∃ h : U ≃ₜ {p : DInfty | p.r < r₀}, (h ⟨x, hxU⟩ : DInfty) = DInfty.apex) ∧
            ∃ τ > 0, D '' U = horoSet (D x) τ ∧ ¬ IsOpen (D '' U)) ∧
    ∀ s ∈ S, ∃ C : CuspChart S s, C.IsHyperbolicCusp ∧
      InjOn C.E {w | 0 ≤ (w : ℂ).re ∧ (w : ℂ).re < 1} ∧
      Subtype.val '' (C.E '' {w | 0 ≤ (w : ℂ).re ∧ (w : ℂ).re < 1}) = C.W C.c \ {s} ∧
      (∀ w, ∃ N ∈ 𝓝 w, ∀ w₁ ∈ N, ∀ w₂ ∈ N, @dist _ m.toDist (C.E w₁) (C.E w₂) =
        dist (UpperHalfPlane.mk w₁ (C.c_pos.trans w₁.2))
          (UpperHalfPlane.mk w₂ (C.c_pos.trans w₂.2))) ∧
      MeasureTheory.volume (cuspStrip C.c) = ENNReal.ofReal (1 / C.c) :=
  ⟨take_closed_unit_disc M S H.isCuspedHyperbolic, fun s hs =>
    let ⟨C, hC⟩ := H.cusp s hs
    ⟨C, hC, C.cusp_finite_area hC H.metric⟩⟩

end MetricExample

end GX
