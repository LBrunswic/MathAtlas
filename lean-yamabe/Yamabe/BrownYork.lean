import Yamabe.Kobayashi

/-!
# Yamabe § 3, the mass of the excised regions: the Euclidean reference and the Brown–York mass

Labels (lines of `papers/yamabe/legacy/labeled/Yamabegap.tex`). NOT marked: both rows are
partial (the model's readings and the cited input, see SCOPE).

* `def:reference` — `Yamabegap.tex:378` (l.378–381): the Euclidean reference embedding of each
  `B_j` onto the boundary of a convex body `C_j ⊂ 𝔼^N`, its mean curvature `H_ref` w.r.t. the
  normal into `C_j`, and the round value `H_ref = −1/r_j`; eq:mass-def (l.383–387), the mass `M`.
* `prop:brown-york` — `Yamabegap.tex:390` (statement l.390–398, proof l.399–401): eq:mass-BY
  `M = Σ_j m_BY(B_j)/(N−1)`, the minimal-round value `m_BY = (N−1) ω_{N−1} r^{N−2}` (`8πr` at
  `N = 3`) and the Schwarzschild identification of the contribution of `B_j` with `m_j`.

> Let $N=3$ and assume that each boundary component $(B_j,\g|_{B_j})$ is a $2$-sphere of
> positive Gauss curvature. By the Weyl--Nirenberg embedding theorem \cite{MR58265} each
> $(B_j,\g|_{B_j})$ admits an isometric embedding into $\Eucl^3$ as the boundary of a convex body
> $C_j$, unique up to rigid motions. We write $\Href$ for the mean curvature of $\partial C_j$
> with respect to the normal pointing \emph{into} $C_j$; for a round sphere of radius $r_j$,
> $\Href=-1/r_j$. (l.380)

> The ``mass'' of the enclosed systems is read off as the deviation of the boundary mean
> curvature from its Euclidean reference value,
> $M := \int_{\partial\Sigma}\big(H_\g-\Href\big)\bvol$ ,
> i.e.\ $\int_{\partial \Sigma} H_\g \, \bvol = \int_{\partial \Sigma}\Href\, \bvol +  M$.
> (l.383–387)

> Let $\mBY(B_j):=\int_{B_j}(k_0-k)\,\bvol$ be the Brown--York quasi-local mass of $B_j$
> \cite{MR1188439,BrownYork1993} (in units $8\pi G=1$), where $k$ is the trace of the second
> fundamental form of $B_j\subset\Sigma$ with respect to the unit normal pointing out of the
> enclosed region, i.e.\ into the void, and $k_0$ the corresponding quantity for the isometric
> embedding of $B_j$ into $\Eucl^3$. Then $M=\frac{1}{N-1}\sum_{j=1}^n\mBY(B_j)$ .
> In particular, if $B_j$ is a minimal round sphere of radius $r_j$ (the horizon of a
> Schwarzschild-like end), then $\mBY(B_j)=(N-1)\omega_{N-1}r_j^{N-2}$, i.e.\ $8\pi r_j$ for
> $N=3$, and the contribution of $B_j$ to $M$ equals the mass parameter $m_j$ of the
> Schwarzschild solution with horizon radius $r_j$. (l.392–397)

> The outward normal $\nu$ of the void is the opposite of the normal pointing out of the enclosed
> region, so $(N-1)H_\g=\tr\mathrm{II}_\nu=-k$; likewise $(N-1)\Href=-k_0$. Hence
> $(N-1)(H_\g-\Href)=k_0-k$ and \eqref{eq:mass-BY} follows by integration. For a minimal round
> sphere $k=0$ and $k_0=(N-1)/r_j$. In units $8\pi G=1$ the Schwarzschild solution of mass
> parameter $m$ has horizon radius $r_s=2Gm=m/(4\pi)$, so that $\mBY=8\pi r_s=2m$ at the horizon
> and $\mBY/2=m$. (l.400)

## The model

The Euclidean half is genuine geometry in `𝔼^N = EuclideanSpace ℝ (Fin N)` (`Yamabe.Ref`):

* `Ref.divergence ν x = tr Dν(x)`; for a unit normal field `ν` of a hypersurface (extended with
  `|ν| = 1` near it) this is `tr II_ν`, and `Ref.meanCurv ν = div ν / (N − 1)` is the mean of the
  principal curvatures, the normalisation of l.299;
* `Ref.RefBody N` — a convex body `C` (convex, compact, with interior) with a differentiable
  unit normal field `ν` along `∂C`, orthogonal to the tangent cone of `∂C` and pointing into `C`;
  `RefBody.Href` (the mean curvature w.r.t. the normal into `C`), `RefBody.k₀` (`tr II` w.r.t.
  the normal out of `C`);
* `Ref.innerNormal c`, `Ref.ballBody c r` — the round ball with its radial inner normal, a
  `RefBody`.

The `Σ` half is the strict measured model (`Yamabe.Quotient`, `Yamabe.Kobayashi`):

* `MeasuredModel.RefEmbedding M g` — per component `j` a reference body and a measurable map
  `ι_j : X → 𝔼^N` carrying `B_j` (`bvol_j`-a.e.) into `∂C_j`, with `Vol(B_j, g) = Area(∂C_j)`,
  the area being the Minkowski content `Ref.HasBdryArea` (`lim (|C_t| − |C|)/t`);
* `RefEmbedding.Href`, `RefEmbedding.k₀` — the reference curvatures read on `B_j` through `ι_j`;
  `RefEmbedding.mass` — eq:mass-def; `RefEmbedding.mBY` — the Brown–York mass of `B_j` for a
  given `k`; `WeylNirenberg M g` — the cited input, `Nonempty (RefEmbedding M g)`.
* `schwarzschildLapse G m r = 1 − 2Gm/r`, `tangherliniLapse N G m r` (its `(N+1)`-dimensional
  form, for the finding).

## What is proved (no `sorry`)

def:reference: `Ref.divergence_neg` (`tr II_{−ν} = −tr II_ν`), `Ref.divergence_rigid`,
`Ref.meanCurv_rigid` (`H_ref` is invariant under rigid motions: the uniqueness clause's use),
`Ref.hasFDerivAt_innerNormal`, `Ref.divergence_innerNormal`, `Ref.ballBody` (the round ball is a reference body),
`Ref.ballBody_Href` (`H_ref = −1/r`), `Ref.ballBody_k₀` (`k₀ = (N−1)/r`),
`Ref.RefBody.sub_one_mul_Href` (`(N−1)H_ref = −k₀`), `Ref.hasBdryArea_closedBall` (the round
area as Minkowski content), `MeasuredModel.refEmbedding_of_area_pos` (the reading's strength), `MeasuredModel.exists_mass_brown_york` (under the cited
input at `N = 3`, `H_ref` and `M` exist and `M = Σ m_BY/2`), `RefEmbedding.integral_H_eq` (the « i.e. »
of eq:mass-def).
prop:brown-york: `RefEmbedding.prop_brown_york` (eq:mass-BY), `RefEmbedding.mBY_round`
(`m_BY = (N−1) ω_{N−1} r^{N−2}`), `RefEmbedding.mBY_round_three` (`8πr`),
`RefEmbedding.RoundMinimal.area` (the round area of `B_j`, derived), `RefEmbedding.mass_round` (`M = ω_{N−1} Σ r_j^{N−2}`, l.467), `schwarzschild_horizon_iff`,
`RefEmbedding.prop_brown_york_schwarzschild` (`m_BY = 8πr_s = 2m`, `m_BY/2 = m`, the contribution
of `B_j` to `M` is `m`). `tangherliniLapse_three` (the Tangherlini lapse at `N = 3` is Schwarzschild's). Finding:
`RefEmbedding.tangherlini_contribution` (`m_BY = 2m`, contribution `2m/(N−1)`),
`tangherlini_contribution_eq_iff` (`= m` iff `N = 3`), `tangherlini_contribution_four`
(`N = 4`: `2m/3 ≠ m`). Witness: `toyRef`, `toyRef_round` (every hypothesis of the round clause
holds on the two-point toy model with a round reference ball of area `1`), `toy_mass`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N = 3` (def:reference) | ⚠ read: the Euclidean layer is at every `N`; `WeylNirenberg` is stated at `N = 3` (the only dimension MR58265 covers); prop:brown-york is printed at general `N` and is proved at general `N ≥ 2` |
| `(B_j, g|B_j)` a 2-sphere of positive Gauss curvature | ⚠ not expressible on the model (no intrinsic curvature of `B_j`): it is the hypothesis of the cited theorem, whose conclusion is carried as data (`RefEmbedding`, `WeylNirenberg`), kb/0018 |
| Weyl–Nirenberg: an isometric embedding onto `∂C_j`, `C_j` convex | ⚠ carried (cited input, DEC-184): `RefEmbedding`; `C_j` convex compact with interior ✓; « isometric » read as `ι_j(B_j) ⊆ ∂C_j` and `Vol(B_j, g) = Area(∂C_j)` (Minkowski content); this carries the area of `B_j`, not its shape: `refEmbedding_of_area_pos` inhabits it on every model whose `B_j` have positive finite area (SCOPE) |
| « unique up to rigid motions » | ⚠ used only through `meanCurv_rigid`: `H_ref` at corresponding points is unchanged by a rigid motion of the field |
| `H_ref` w.r.t. the normal into `C_j` | ✓ `RefBody.Href = div ν/(N−1)`, `ν` unit, normal, pointing into `C`, differentiable on `∂C` |
| `H_ref = −1/r_j` for a round sphere | ✓ `ballBody_Href`, computed from the definition |
| eq:mass-def `M = ∫_{∂Σ}(H_g − H_ref)` | ✓ `RefEmbedding.mass = Σ_j ∫_{B_j}(H_g − H_ref ∘ ι_j)`; the « i.e. » needs `H_ref ∘ ι_j` integrable and `bvol_j` finite (carried in `integral_H_eq`) |
| `k` = `tr II` of `B_j ⊂ Σ` w.r.t. the normal into the void | ⚠ read: `Σ` carries `H_g` (w.r.t. `ν`, out of the void) but no second fundamental form, so `k` is a function characterised by the paper's own step `(N−1)H_g = −k` (`hk`), the sign rule proved where `II` exists (`divergence_neg`) |
| `k₀` the same for the embedding | ✓ `RefBody.k₀ = div(−ν)`, `(N−1)H_ref = −k₀` proved |
| `B_j` a minimal round sphere of radius `r_j` | ⚠ read: `H_g = 0` `bvol_j`-a.e.; `bvol_j(B_j) = ω_{N−1} r_j^{N−1}` derived from the area clause of `RefEmbedding` (`RoundMinimal.area`); its reference body is the round ball `closedBall c_j r_j` with the radial normal near `∂C_j` (Weyl uniqueness, carried) |
| Schwarzschild horizon radius `r_s = 2Gm`, `8πG = 1` | ✓ `r_s` is the zero of the lapse `1 − 2Gm/r` (`schwarzschild_horizon_iff`), `8πG = 1` carried |

## SCOPE (disclosed)

* The model's `Σ` has no second fundamental form: `H_g` is free data (`CurvedMetric`). The
  identity `(N−1)H_g = tr II_ν = −k` is therefore the characterisation of `k` (`hk`), not a
  theorem; its content, the oddness of `tr II` in the normal, is proved in `𝔼^N`
  (`divergence_neg`), where `II` is the differential of the normal field.
* `Ref.divergence` of a unit extension of the normal is `tr II` independently of the extension
  (classical); the file does not prove the independence, and in the round case carries the
  radial field near the sphere.
* The isometry of `ι_j` is not readable on the model (`B_j` has no intrinsic metric here, and
  Mathlib's Hausdorff measure is not the normalised surface measure): it is read as
  `ι_j(B_j) ⊆ ∂C_j` plus the area equality `Vol(B_j, g) = Area(∂C_j)`, the area of `∂C_j` being
  its Minkowski content (`hasBdryArea_closedBall`: `ω_{N−1} r^{N−1}` for a round sphere). This is
  **weak**: `refEmbedding_of_area_pos` proves that a reference embedding (a round ball of matching
  radius, a constant map) exists on every model whose `B_j` have positive finite area, so
  `WeylNirenberg` is a theorem there, and `H_ref`, `M` depend on the choice of `R` unless pinned by
  further hypotheses such as `RoundMinimal`. Every theorem consuming `R` quantifies over all `R`.
  (AUDIT-1, round 1, finding 1.)
* The Weyl–Nirenberg theorem itself (MR58265) is the cited input: never an axiom, carried as
  `RefEmbedding` data or the Prop `WeylNirenberg`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Metric
open scoped RealInnerProductSpace

noncomputable section

namespace Yamabe

namespace Ref

variable {N : ℕ}

/-- Euclidean space `𝔼^N`. -/
abbrev E (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- `div ν (x) = tr Dν(x)`. For a unit normal field `ν` of a hypersurface (extended with `|ν| = 1`
near it) this is the trace of the second fundamental form `tr II_ν`. -/
def divergence (ν : E N → E N) (x : E N) : ℝ :=
  LinearMap.trace ℝ (E N) (fderiv ℝ ν x : E N →ₗ[ℝ] E N)

/-- The mean curvature `H_ν = tr II_ν / (N − 1)`, the mean of the principal curvatures (l.299). -/
def meanCurv (ν : E N → E N) (x : E N) : ℝ := divergence ν x / ((N : ℝ) - 1)

/-- The radial unit field pointing to `c`: on the sphere `S(c, r)`, the normal into the ball. -/
def innerNormal (c : E N) (y : E N) : E N := -(‖y - c‖⁻¹ • (y - c))

/-- `tr II_{−ν} = −tr II_ν` (l.400). -/
theorem divergence_neg (ν : E N → E N) (x : E N) :
    divergence (fun y => -ν y) x = -divergence ν x := by
  unfold divergence
  rw [show (fun y => -ν y) = -ν from rfl, fderiv_neg]
  simp

/-- `div` is invariant under a rigid motion `y ↦ L y + a`, the field transported by `L`. -/
theorem divergence_rigid (L : E N ≃ₗᵢ[ℝ] E N) (a : E N) {ν : E N → E N} {x : E N}
    (hν : DifferentiableAt ℝ ν x) :
    divergence (fun y => L (ν (L.symm (y - a)))) (L x + a) = divergence ν x := by
  have hA : HasFDerivAt (fun y : E N => L.symm (y - a))
      ((L.symm.toContinuousLinearEquiv : E N →L[ℝ] E N).comp (ContinuousLinearMap.id ℝ (E N)))
      (L x + a) :=
    (L.symm.toContinuousLinearEquiv : E N →L[ℝ] E N).hasFDerivAt.comp (L x + a)
      ((hasFDerivAt_id _).sub_const a)
  have hx' : L.symm (L x + a - a) = x := by simp
  have hν' : HasFDerivAt ν (fderiv ℝ ν x) (L.symm (L x + a - a)) := by
    rw [hx']; exact hν.hasFDerivAt
  have h := (L.toContinuousLinearEquiv : E N →L[ℝ] E N).hasFDerivAt.comp (L x + a)
    (hν'.comp (L x + a) hA)
  have hfd : fderiv ℝ (fun y => L (ν (L.symm (y - a)))) (L x + a) = _ := h.fderiv
  unfold divergence
  rw [hfd, ← LinearMap.trace_conj' (fderiv ℝ ν x : E N →ₗ[ℝ] E N) L.toLinearEquiv]
  congr 1

/-- `H_ref` is unchanged by a rigid motion (the use of « unique up to rigid motions », l.380). -/
theorem meanCurv_rigid (L : E N ≃ₗᵢ[ℝ] E N) (a : E N) {ν : E N → E N} {x : E N}
    (hν : DifferentiableAt ℝ ν x) :
    meanCurv (fun y => L (ν (L.symm (y - a)))) (L x + a) = meanCurv ν x := by
  unfold meanCurv; rw [divergence_rigid L a hν]

/-- The differential of the radial inner normal away from its centre. -/
lemma hasFDerivAt_innerNormal {c x : E N} (hx : x ≠ c) :
    HasFDerivAt (innerNormal c) (-(‖x - c‖⁻¹ • ContinuousLinearMap.id ℝ (E N) +
      (-(‖x - c‖ ^ 2)⁻¹ • ‖x - c‖⁻¹ • innerSL ℝ (x - c)).smulRight (x - c))) x := by
  have hu : x - c ≠ 0 := sub_ne_zero.mpr hx
  have h0 := ((hasFDerivAt_id x).sub_const c).norm_sq
  have h1 := h0.sqrt (by simpa using hu)
  have hf : (fun y => √(‖id y - c‖ ^ 2)) = fun y => ‖y - c‖ := by
    funext y; simp
  rw [hf] at h1
  have h1' : HasFDerivAt (fun y => ‖y - c‖) (‖x - c‖⁻¹ • innerSL ℝ (x - c)) x := by
    refine h1.congr_fderiv ?_
    ext v
    simp
    field_simp
  have hρ : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have h2 := (hasDerivAt_inv hρ).comp_hasFDerivAt x h1'
  exact (h2.smul ((hasFDerivAt_id x).sub_const c)).neg

/-- `div` of the radial inner normal: `−(N − 1)/|x − c|`. -/
theorem divergence_innerNormal {c x : E N} (hx : x ≠ c) :
    divergence (innerNormal c) x = -(((N : ℝ) - 1) / ‖x - c‖) := by
  set u := x - c with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr hx
  have hρ : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  unfold divergence
  rw [(hasFDerivAt_innerNormal hx).fderiv,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
  simp only [ContinuousLinearMap.coe_coe, EuclideanSpace.basisFun_apply, ← hu_def]
  simp only [neg_apply, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  simp only [inner_neg_right, inner_add_right, inner_smul_right, smul_eq_mul,
    real_inner_self_eq_norm_sq, PiLp.norm_single, norm_one, one_pow, mul_one,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hs : ∑ i : Fin N, ⟪u, EuclideanSpace.single i (1:ℝ)⟫ * ⟪EuclideanSpace.single i (1:ℝ), u⟫ =
      ‖u‖ ^ 2 := by
    have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_inner_mul_inner u u
    simpa [real_inner_self_eq_norm_sq] using this
  have hs' : ∑ i : Fin N, -(‖u‖ ^ 2)⁻¹ * (‖u‖⁻¹ * ⟪u, EuclideanSpace.single i (1:ℝ)⟫) *
      ⟪EuclideanSpace.single i (1:ℝ), u⟫ = -(‖u‖ ^ 2)⁻¹ * ‖u‖⁻¹ * ‖u‖ ^ 2 := by
    rw [← hs, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- A convex body of `𝔼^N` with its unit normal field into it along `∂C` (def:reference). -/
structure RefBody (N : ℕ) where
  /-- the convex body `C_j` -/
  C : Set (E N)
  convex : Convex ℝ C
  compact : IsCompact C
  interior_nonempty : (interior C).Nonempty
  /-- the unit normal field of `∂C`, pointing into `C`, extended near `∂C` -/
  ν : E N → E N
  differentiable : ∀ x ∈ frontier C, DifferentiableAt ℝ ν x
  unit : ∀ x ∈ frontier C, ∀ᶠ y in 𝓝 x, ‖ν y‖ = 1
  normal : ∀ x ∈ frontier C, ∀ v ∈ tangentConeAt ℝ (frontier C) x, ⟪ν x, v⟫ = 0
  inward : ∀ x ∈ frontier C, ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ioo (0 : ℝ) ε, x + t • ν x ∈ interior C

namespace RefBody

variable (K : RefBody N)

/-- `H_ref`: the mean curvature of `∂C` w.r.t. the normal into `C` (l.380). -/
def Href (x : E N) : ℝ := meanCurv K.ν x

/-- `k₀`: `tr II` of `∂C` w.r.t. the normal out of `C` (l.395). -/
def k₀ (x : E N) : ℝ := divergence (fun y => -K.ν y) x

/-- `(N − 1) H_ref = −k₀` (l.400). -/
theorem sub_one_mul_Href (hN : 2 ≤ N) (x : E N) : ((N : ℝ) - 1) * K.Href x = -K.k₀ x := by
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold Href k₀ meanCurv
  rw [divergence_neg, neg_neg]
  field_simp

end RefBody

lemma ne_of_mem_frontier_closedBall {c x : E N} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ frontier (closedBall c r)) : x ≠ c := by
  rw [frontier_closedBall c hr.ne'] at hx
  exact ne_of_mem_sphere hx hr.ne'

/-- The round ball `closedBall c r` with its radial inner normal is a reference body. -/
def ballBody (c : E N) {r : ℝ} (hr : 0 < r) : RefBody N where
  C := closedBall c r
  convex := convex_closedBall c r
  compact := isCompact_closedBall c r
  interior_nonempty := ⟨c, by rw [interior_closedBall c hr.ne']; exact mem_ball_self hr⟩
  ν := innerNormal c
  differentiable := fun x hx =>
    (hasFDerivAt_innerNormal (ne_of_mem_frontier_closedBall hr hx)).differentiableAt
  unit := by
    intro x hx
    have hxc := ne_of_mem_frontier_closedBall hr hx
    filter_upwards [isOpen_ne.mem_nhds hxc] with y hy
    have : ‖y - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
    simp [innerNormal, norm_smul, this]
  normal := by
    intro x hx v hv
    rw [frontier_closedBall c hr.ne'] at hx hv
    have hf : HasFDerivWithinAt (fun y : E N => ‖y - c‖ ^ 2)
        (2 • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ (E N))) (sphere c r) x :=
      ((hasFDerivAt_id x).sub_const c).norm_sq.hasFDerivWithinAt
    have hg : HasFDerivWithinAt (fun y : E N => ‖y - c‖ ^ 2) (0 : E N →L[ℝ] ℝ)
        (sphere c r) x := by
      refine (hasFDerivWithinAt_const (r ^ 2) x (sphere c r)).congr (fun y hy => ?_) ?_
      · rw [mem_sphere_iff_norm.mp hy]
      · rw [mem_sphere_iff_norm.mp hx]
    have := hf.unique_on hg hv
    simp at this
    simp only [innerNormal, inner_neg_left, inner_smul_left]
    rw [inner_sub_left, this]; simp
  inward := by
    intro x hx
    rw [frontier_closedBall c hr.ne'] at hx
    have hxr : ‖x - c‖ = r := mem_sphere_iff_norm.mp hx
    refine ⟨r, hr, fun t ht => ?_⟩
    rw [interior_closedBall c hr.ne', mem_ball_iff_norm]
    have : x + t • innerNormal c x - c = (1 - t / r) • (x - c) := by
      simp only [innerNormal, hxr, smul_neg, smul_smul]
      rw [sub_smul, one_smul, div_eq_mul_inv, mul_comm]; abel
    rw [this, norm_smul, hxr, Real.norm_eq_abs,
      abs_of_pos (by have := ht.2; rw [sub_pos, div_lt_one hr]; exact this)]
    have := ht.1
    nlinarith [div_pos this hr]

/-- For a round sphere of radius `r`, `H_ref = −1/r` (l.380). -/
theorem ballBody_Href (hN : 2 ≤ N) (c : E N) {r : ℝ} (hr : 0 < r) {x : E N}
    (hx : x ∈ sphere c r) : (ballBody c hr).Href x = -1 / r := by
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  show meanCurv (innerNormal c) x = _
  unfold meanCurv
  rw [divergence_innerNormal (ne_of_mem_sphere hx hr.ne'), mem_sphere_iff_norm.mp hx]
  field_simp

/-- For a round sphere of radius `r`, `k₀ = (N − 1)/r` (l.400). -/
theorem ballBody_k₀ (c : E N) {r : ℝ} (hr : 0 < r) {x : E N}
    (hx : x ∈ sphere c r) : (ballBody c hr).k₀ x = ((N : ℝ) - 1) / r := by
  show divergence (fun y => -innerNormal c y) x = _
  rw [divergence_neg, divergence_innerNormal (ne_of_mem_sphere hx hr.ne'),
    mem_sphere_iff_norm.mp hx, neg_neg]

/-- `∂C` has area `A` in the sense of the (outer) Minkowski content:
`(|C_t| − |C|)/t → A` as `t → 0⁺`, `C_t` the closed `t`-thickening. For a convex body this is
the surface area of `∂C`, the quantity an isometry `B_j → ∂C_j` preserves. -/
def HasBdryArea (C : Set (E N)) (A : ℝ) : Prop :=
  Tendsto (fun t : ℝ => ((MeasureTheory.volume (cthickening t C)).toReal -
    (MeasureTheory.volume C).toReal) / t) (𝓝[>] 0) (𝓝 A)

lemma HasBdryArea.unique {C : Set (E N)} {A A' : ℝ} (h : HasBdryArea C A)
    (h' : HasBdryArea C A') : A = A' :=
  tendsto_nhds_unique h h'

/-- The round sphere of radius `r` has area `ω_{N−1} r^{N−1}` (Minkowski content). -/
theorem hasBdryArea_closedBall (c : E N) {r : ℝ} (hr : 0 < r) :
    HasBdryArea (closedBall c r) (sphereArea N * r ^ (N - 1)) := by
  set V := (MeasureTheory.volume (ball (0 : E N) 1)).toReal
  have hvol : ∀ s : ℝ, 0 ≤ s →
      (MeasureTheory.volume (closedBall c s)).toReal = s ^ N * V := by
    intro s hs
    rw [Measure.addHaar_closedBall _ c hs, ENNReal.toReal_mul, finrank_euclideanSpace_fin,
      ENNReal.toReal_ofReal (pow_nonneg hs _)]
  have hd : HasDerivAt (fun s : ℝ => s ^ N * V) ((N : ℝ) * r ^ (N - 1) * V) r :=
    (hasDerivAt_pow N r).mul_const V
  have ht := hd.tendsto_slope_zero_right
  have hlim : (N : ℝ) * r ^ (N - 1) * V = sphereArea N * r ^ (N - 1) := by
    rw [sphereArea_eq]; ring
  rw [hlim] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
  rw [cthickening_closedBall htp.le hr.le, hvol _ (by linarith), hvol _ hr.le, smul_eq_mul,
    add_comm t r]
  field_simp

end Ref

open Ref

/-- The Schwarzschild lapse `1 − 2Gm/r` (`N = 3`, `c = 1`). -/
def schwarzschildLapse (G m r : ℝ) : ℝ := 1 - 2 * G * m / r

/-- The horizon of the Schwarzschild solution of mass `m`: `r_s = 2Gm` (l.400). -/
theorem schwarzschild_horizon_iff {G m r : ℝ} (hr : r ≠ 0) :
    schwarzschildLapse G m r = 0 ↔ r = 2 * G * m := by
  unfold schwarzschildLapse
  rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hr, eq_comm]

/-- The Schwarzschild–Tangherlini lapse in `N + 1` dimensions,
`1 − 16πGm / ((N−1) ω_{N−1} r^{N−2})` (ADM normalisation); `N = 3` is `schwarzschildLapse`. -/
def tangherliniLapse (N : ℕ) (G m r : ℝ) : ℝ :=
  1 - 16 * Real.pi * G * m / (((N : ℝ) - 1) * sphereArea N * r ^ (N - 2))

theorem tangherliniLapse_three (G m r : ℝ) :
    tangherliniLapse 3 G m r = schwarzschildLapse G m r := by
  unfold tangherliniLapse schwarzschildLapse
  rw [sphereArea_three]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  congr 1
  norm_num
  rw [show 16 * Real.pi * G * m = (8 * Real.pi) * (2 * G * m) by ring,
    show 2 * (4 * Real.pi) * r = (8 * Real.pi) * r by ring,
    mul_div_mul_left _ _ (by positivity)]

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- def:reference on the model: per boundary component `B_j` a reference body `C_j` and a map
`ι_j` carrying `B_j` into `∂C_j`, with `Vol(B_j, g) = Area(∂C_j)` (the conclusion of
Weyl–Nirenberg, as far as the model reads it: an isometry preserves area). -/
structure RefEmbedding (g : FrameMetric X N) where
  body : Fin n → RefBody N
  ι : Fin n → X → E N
  measurable : ∀ j, Measurable (ι j)
  onto : ∀ j, ∀ᵐ x ∂(M.bvol g j), ι j x ∈ frontier (body j).C
  area : ∀ j, HasBdryArea (body j).C (M.bvol g j Set.univ).toReal

/-- **What the reading carries**: under the model's reading of « isometric » (into `∂C_j`, with the
area of `B_j`), a reference embedding exists as soon as every `B_j` has positive finite area:
a round ball of matching radius and a constant map. So `WeylNirenberg` below holds on every such
model; it carries the area of `B_j`, not its shape (SCOPE). -/
theorem refEmbedding_of_area_pos (hN : 2 ≤ N) (g : FrameMetric X N)
    (hA : ∀ j, 0 < (M.bvol g j Set.univ).toReal) : Nonempty (M.RefEmbedding g) := by
  have hω := sphereArea_pos (N := N) (by omega)
  have h1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  let rad : Fin n → ℝ := fun j =>
    ((M.bvol g j Set.univ).toReal / sphereArea N) ^ (1 / ((N : ℝ) - 1))
  have hrad : ∀ j, 0 < rad j := fun j => Real.rpow_pos_of_pos (div_pos (hA j) hω) _
  have harea : ∀ j, sphereArea N * rad j ^ (N - 1) = (M.bvol g j Set.univ).toReal := by
    intro j
    have hb := div_pos (hA j) hω
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le, Nat.cast_sub (by omega), Nat.cast_one,
      one_div_mul_cancel h1.ne', Real.rpow_one]
    field_simp
  let i0 : Fin N := ⟨0, by omega⟩
  refine ⟨{
    body := fun j => ballBody 0 (hrad j)
    ι := fun j _ => rad j • EuclideanSpace.single i0 1
    measurable := fun _ => measurable_const
    onto := fun j => ae_of_all _ fun _ => by
      show rad j • EuclideanSpace.single i0 (1 : ℝ) ∈ frontier (closedBall (0 : E N) (rad j))
      rw [frontier_closedBall _ (hrad j).ne', mem_sphere_zero_iff_norm, norm_smul,
        PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (hrad j)]
    area := fun j => by
      show HasBdryArea (closedBall (0 : E N) (rad j)) _
      rw [← harea j]
      exact hasBdryArea_closedBall 0 (hrad j) }⟩

/-- The cited input of def:reference (Weyl–Nirenberg, MR58265) on the model at `N = 3`. On the
model it carries only the area of each `B_j` (`refEmbedding_of_area_pos`). -/
def WeylNirenberg (M : MeasuredModel X D 3 n) (g : FrameMetric X 3) : Prop :=
  Nonempty (M.RefEmbedding g)

namespace RefEmbedding

variable {M} {g : CurvedMetric X N} (R : M.RefEmbedding g.toFrameMetric)

/-- `H_ref` on `B_j`. -/
def Href (j : Fin n) (x : X) : ℝ := (R.body j).Href (R.ι j x)

/-- `k₀` on `B_j`. -/
def k₀ (j : Fin n) (x : X) : ℝ := (R.body j).k₀ (R.ι j x)

/-- eq:mass-def: `M = ∫_{∂Σ} (H_g − H_ref) bvol = Σ_j ∫_{B_j} (H_g − H_ref) bvol`. -/
def mass : ℝ := ∑ j, ∫ x, (g.H x - R.Href j x) ∂(M.bvol g.toFrameMetric j)

/-- The Brown–York mass `m_BY(B_j) = ∫_{B_j} (k₀ − k) bvol` (units `8πG = 1`), for the function
`k` on `B_j`. -/
def mBY (j : Fin n) (k : X → ℝ) : ℝ := ∫ x, (R.k₀ j x - k x) ∂(M.bvol g.toFrameMetric j)

/-- The « i.e. » of eq:mass-def: `∫_{∂Σ} H_g = ∫_{∂Σ} H_ref + M`. -/
theorem integral_H_eq [∀ j, IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (hint : ∀ j, Integrable (R.Href j) (M.bvol g.toFrameMetric j)) :
    ∑ j, ∫ x, g.H x ∂(M.bvol g.toFrameMetric j) =
      ∑ j, ∫ x, R.Href j x ∂(M.bvol g.toFrameMetric j) + R.mass := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨C, hC⟩ := g.H_bdd
  have hH : Integrable g.H (M.bvol g.toFrameMetric j) :=
    Integrable.of_bound g.H_measurable.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)
  rw [integral_sub hH (hint j)]
  ring

/-- prop:brown-york, eq:mass-BY: if `(N−1) H_g = −k_j` on each `B_j`, then
`M = (1/(N−1)) Σ_j m_BY(B_j)`. -/
theorem prop_brown_york (hN : 2 ≤ N) (k : Fin n → X → ℝ)
    (hk : ∀ j, ∀ᵐ x ∂(M.bvol g.toFrameMetric j), ((N : ℝ) - 1) * g.H x = -k j x) :
    R.mass = 1 / ((N : ℝ) - 1) * ∑ j, R.mBY j (k j) := by
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hj : ∀ j, R.mBY j (k j) =
      ((N : ℝ) - 1) * ∫ x, (g.H x - R.Href j x) ∂(M.bvol g.toFrameMetric j) := by
    intro j
    unfold mBY
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hk j] with x hx
    have h0 := (R.body j).sub_one_mul_Href hN (R.ι j x)
    simp only [k₀, Href] at h0 ⊢
    linarith
  simp only [hj, ← Finset.mul_sum, mass]
  field_simp

/-- `B_j` is a minimal round sphere of radius `r`: `H_g = 0` on it, its area is `ω_{N−1} r^{N−1}`,
and its reference body is the round ball `closedBall c r` with the radial normal near `∂C_j`. -/
structure RoundMinimal (j : Fin n) (c : E N) (r : ℝ) : Prop where
  pos : 0 < r
  minimal : ∀ᵐ x ∂(M.bvol g.toFrameMetric j), g.H x = 0
  ball : (R.body j).C = closedBall c r
  radial : ∀ y ∈ sphere c r, (R.body j).ν =ᶠ[𝓝 y] innerNormal c

/-- The area of a round `B_j` is `ω_{N−1} r^{N−1}`: derived from `RefEmbedding.area`. -/
theorem RoundMinimal.area {j : Fin n} {c : E N} {r : ℝ}
    (hR : R.RoundMinimal j c r) :
    (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r ^ (N - 1) := by
  have h := R.area j
  rw [hR.ball] at h
  exact h.unique (hasBdryArea_closedBall c hR.pos)

/-- For a minimal round `B_j` of radius `r`: `m_BY(B_j) = (N−1) ω_{N−1} r^{N−2}` (l.395). -/
theorem mBY_round (hN : 2 ≤ N) {j : Fin n} {c : E N} {r : ℝ} (hR : R.RoundMinimal j c r)
    (k : X → ℝ) (hk : ∀ᵐ x ∂(M.bvol g.toFrameMetric j), ((N : ℝ) - 1) * g.H x = -k x) :
    R.mBY j k = ((N : ℝ) - 1) * sphereArea N * r ^ (N - 2) := by
  have hr := hR.pos
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hae : ∀ᵐ x ∂(M.bvol g.toFrameMetric j), R.k₀ j x - k x = ((N : ℝ) - 1) / r := by
    filter_upwards [R.onto j, hk, hR.minimal] with x hx hkx hHx
    rw [hR.ball, frontier_closedBall c hr.ne'] at hx
    have hk0 : k x = 0 := by rw [hHx, mul_zero] at hkx; linarith
    have hev : (fun y => -(R.body j).ν y) =ᶠ[𝓝 (R.ι j x)] (fun y => -innerNormal c y) :=
      (hR.radial _ hx).mono fun y hy => by simp only [hy]
    have hfd := hev.fderiv_eq (𝕜 := ℝ)
    have : R.k₀ j x = (ballBody c hr).k₀ (R.ι j x) := by
      simp only [k₀, RefBody.k₀, divergence, hfd]; rfl
    rw [hk0, sub_zero, this, ballBody_k₀ c hr hx]
  rw [mBY, integral_congr_ae hae, integral_const, smul_eq_mul, Measure.real, hR.area]
  obtain ⟨p, rfl⟩ : ∃ p, N = p + 2 := ⟨N - 2, by omega⟩
  rw [show p + 2 - 1 = p + 1 by omega, show p + 2 - 2 = p by omega, pow_succ]
  field_simp

/-- `N = 3`: `m_BY(B_j) = 8πr` (l.396). -/
theorem mBY_round_three {M : MeasuredModel X D 3 n} {g : CurvedMetric X 3}
    (R : M.RefEmbedding g.toFrameMetric) {j : Fin n} {c : E 3} {r : ℝ}
    (hR : R.RoundMinimal j c r) (k : X → ℝ)
    (hk : ∀ᵐ x ∂(M.bvol g.toFrameMetric j), ((3 : ℕ) - 1 : ℝ) * g.H x = -k x) :
    R.mBY j k = 8 * Real.pi * r := by
  rw [R.mBY_round (by norm_num) hR k hk, sphereArea_three,
    show (3 : ℕ) - 2 = 1 from rfl, pow_one]
  push_cast
  ring

/-- l.467: if every `B_j` is a minimal round sphere of radius `r_j`, `M = ω_{N−1} Σ_j r_j^{N−2}`. -/
theorem mass_round (hN : 2 ≤ N) {c : Fin n → E N} {r : Fin n → ℝ}
    (hR : ∀ j, R.RoundMinimal j (c j) (r j)) : R.mass = roundMass N r := by
  have h1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  let k : Fin n → X → ℝ := fun _ x => -(((N : ℝ) - 1) * g.H x)
  have hk : ∀ j, ∀ᵐ x ∂(M.bvol g.toFrameMetric j), ((N : ℝ) - 1) * g.H x = -k j x :=
    fun j => ae_of_all _ fun x => by simp [k]
  rw [R.prop_brown_york hN k hk]
  simp only [fun j => R.mBY_round hN (hR j) (k j) (hk j), roundMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- prop:brown-york, the Schwarzschild clause at `N = 3`: if `B_j` is a minimal round sphere
whose radius is the horizon of the Schwarzschild solution of mass `m` and `8πG = 1`, then
`r = m/(4π)`, `m_BY(B_j) = 8πr = 2m`, `m_BY/2 = m`, and the contribution `m_BY/(N−1)` of `B_j`
to `M` (eq:mass-BY) is `m`. -/
theorem prop_brown_york_schwarzschild {M : MeasuredModel X D 3 n} {g : CurvedMetric X 3}
    (R : M.RefEmbedding g.toFrameMetric) {j : Fin n} {c : E 3} {r G m : ℝ}
    (hR : R.RoundMinimal j c r) (hG : 8 * Real.pi * G = 1)
    (hhor : schwarzschildLapse G m r = 0) (k : X → ℝ)
    (hk : ∀ᵐ x ∂(M.bvol g.toFrameMetric j), ((3 : ℕ) - 1 : ℝ) * g.H x = -k x) :
    r = m / (4 * Real.pi) ∧ R.mBY j k = 8 * Real.pi * r ∧ R.mBY j k = 2 * m ∧
      R.mBY j k / 2 = m ∧ R.mBY j k / ((3 : ℕ) - 1 : ℝ) = m := by
  have hr := hR.pos
  have hπ : 0 < Real.pi := Real.pi_pos
  have hrs : r = 2 * G * m := (schwarzschild_horizon_iff hr.ne').mp hhor
  have hG' : G = 1 / (8 * Real.pi) := by field_simp; linarith
  have hr' : r = m / (4 * Real.pi) := by rw [hrs, hG']; field_simp; ring
  have hm := R.mBY_round_three hR k hk
  have h2 : R.mBY j k = 2 * m := by rw [hm, hr']; field_simp; ring
  refine ⟨hr', hm, h2, by rw [h2]; ring, by rw [h2]; norm_num⟩

/-- **Finding**: at general `N`, with the Tangherlini horizon of mass `m` (`8πG = 1`), still
`m_BY = 2m`, but the contribution `m_BY/(N−1)` of `B_j` to `M` is `2m/(N−1)`. -/
theorem tangherlini_contribution (hN : 3 ≤ N) {j : Fin n} {c : E N} {r G m : ℝ}
    (hR : R.RoundMinimal j c r) (hG : 8 * Real.pi * G = 1)
    (hhor : tangherliniLapse N G m r = 0) (k : X → ℝ)
    (hk : ∀ᵐ x ∂(M.bvol g.toFrameMetric j), ((N : ℝ) - 1) * g.H x = -k x) :
    R.mBY j k = 2 * m ∧ R.mBY j k / ((N : ℝ) - 1) = 2 * m / ((N : ℝ) - 1) := by
  have hr := hR.pos
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hω := sphereArea_pos (N := N) (by omega)
  have hden : ((N : ℝ) - 1) * sphereArea N * r ^ (N - 2) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    positivity
  have hmBY := R.mBY_round (by omega) hR k hk
  unfold tangherliniLapse at hhor
  rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hden] at hhor
  have h2 : R.mBY j k = 2 * m := by
    rw [hmBY, ← hhor, show 16 * Real.pi * G * m = 2 * (8 * Real.pi * G) * m by ring, hG]; ring
  exact ⟨h2, by rw [h2]⟩

end RefEmbedding

/-- def:reference with prop:brown-york at `N = 3`: under the cited Weyl–Nirenberg input a reference
embedding exists, and for it `M = (m_BY(B_1) + ⋯ + m_BY(B_n))/2`. -/
theorem exists_mass_brown_york {M : MeasuredModel X D 3 n} {g : CurvedMetric X 3}
    (hW : M.WeylNirenberg g.toFrameMetric) (k : Fin n → X → ℝ)
    (hk : ∀ j, ∀ᵐ x ∂(M.bvol g.toFrameMetric j), ((3 : ℕ) - 1 : ℝ) * g.H x = -k j x) :
    ∃ R : M.RefEmbedding g.toFrameMetric, R.mass = 1 / 2 * ∑ j, R.mBY j (k j) := by
  obtain ⟨R⟩ := hW
  refine ⟨R, ?_⟩
  rw [R.prop_brown_york (by norm_num) k hk]
  norm_num

end MeasuredModel

/-- **Finding**: `2m/(N−1) = m` iff `N = 3` (for `m ≠ 0`); at `N = 4` the contribution is `2m/3`. -/
theorem tangherlini_contribution_eq_iff {N : ℕ} (hN : 3 ≤ N) {m : ℝ} (hm : m ≠ 0) :
    2 * m / ((N : ℝ) - 1) = m ↔ N = 3 := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  rw [div_eq_iff h1]
  constructor
  · intro h
    have : (N : ℝ) = 3 := by
      have := mul_left_cancel₀ hm (show m * 2 = m * ((N : ℝ) - 1) by linarith)
      linarith
    exact_mod_cast this
  · rintro rfl; norm_num; ring

end Yamabe

namespace Yamabe

/-- **Finding**, the counterexample at `N = 4`: the contribution `2m/3` is not `m`. -/
theorem tangherlini_contribution_four {m : ℝ} (hm : m ≠ 0) :
    2 * m / ((4 : ℕ) - 1 : ℝ) ≠ m := by
  intro h
  have := (tangherlini_contribution_eq_iff (N := 4) (by norm_num) hm).mp h
  omega

open Ref

/-! ## Witness: the two-point toy model with a round reference ball -/

/-- The radius of a round sphere of area `1`: `4π r₀² = 1`. -/
def toyRadius : ℝ := 1 / Real.sqrt (4 * Real.pi)

lemma toyRadius_pos : 0 < toyRadius := by
  unfold toyRadius; have := Real.pi_pos; positivity

/-- A point of the sphere of radius `r₀` about `0` in `𝔼³`. -/
def toyPoint : E 3 := toyRadius • EuclideanSpace.single 0 1

lemma toyPoint_mem : toyPoint ∈ sphere (0 : E 3) toyRadius := by
  rw [mem_sphere_zero_iff_norm, toyPoint, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs, abs_of_pos toyRadius_pos]

lemma toy_area : sphereArea 3 * toyRadius ^ (3 - 1) = 1 := by
  rw [sphereArea_three, show (3 : ℕ) - 1 = 2 from rfl]
  unfold toyRadius
  have := Real.pi_pos
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- The toy model's one boundary point embedded on the round sphere of radius `r₀`, of area
`1 = Vol(B, g)`. -/
def toyRef : toyModel.RefEmbedding toyCurved.toFrameMetric where
  body := fun _ => ballBody 0 toyRadius_pos
  ι := fun _ _ => toyPoint
  measurable := fun _ => measurable_const
  onto := fun _ => ae_of_all _ fun _ => by
    show toyPoint ∈ frontier (closedBall (0 : E 3) toyRadius)
    rw [frontier_closedBall _ toyRadius_pos.ne']; exact toyPoint_mem
  area := fun j => by
    show HasBdryArea (closedBall (0 : E 3) toyRadius) _
    rw [toyCurved_toFrameMetric, toy_bvol, measure_univ, ENNReal.toReal_one, ← toy_area]
    exact hasBdryArea_closedBall 0 toyRadius_pos

/-- The hypotheses of the round clause hold on the toy model. -/
lemma toyRef_round (j : Fin 1) : toyRef.RoundMinimal j 0 toyRadius where
  pos := toyRadius_pos
  minimal := toy_minimal j
  ball := rfl
  radial := fun _ _ => Filter.EventuallyEq.rfl

/-- On the toy model, `M = 4π r₀`. -/
theorem toy_mass : toyRef.mass = 4 * Real.pi * toyRadius := by
  rw [toyRef.mass_round (by norm_num) (c := fun _ => 0) (fun j => toyRef_round j), roundMass,
    sphereArea_three]
  simp

end Yamabe
