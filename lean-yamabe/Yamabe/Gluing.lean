import Yamabe.Kobayashi
import Yamabe.Stability

/-!
# The gluing estimate and the `τ → 0` step of the upper bound, over the measured model

Labels (abstract layer only; NOT marked: both rows stay partial, see SCOPE; these are lemmas, not
the rows' anchors):

* `lem:gluing-estimate` — `Yamabegap.tex:648` (statement l.648–656, proof l.657–683): the chain
  of the proof over the model of `Yamabe.Quotient` / `Yamabe.Kobayashi` extended by the pieces
  `D_j`, the geometric and cited inputs carried as named hypotheses;
* `thm:upper-bound` — `Yamabegap.tex:493` (statement l.493–500, proof l.723–728): the step
  "after dropping its non-positive last term" (l.724–726), the `τ → 0` limit (l.728), and the
  assembly of the proof from its inputs.

> Let $(\Sigbar,\gbar)$ be a smooth closed Riemannian $N$-manifold with $\Y_{[\gbar]}(\Sigbar)\le0$,
> let $\Sigma\subset\Sigbar$ be a compact connected domain with smooth boundary
> $\partial\Sigma=\bigsqcup_jB_j$, and let $D_j$ be the closures of the components of
> $\Sigbar\setminus\Sigma$, each $D_j$ meeting $\Sigma$ along $B_j$. Put $\g:=\gbar|_\Sigma$,
> $\g_j:=\gbar|_{D_j}$, and assume $H_\g\equiv0$ on $\partial\Sigma$ and
> $\beta_j:=\YB_{[\g_j]}(D_j)>-\infty$. Then there exists a smooth positive function $u$ on
> $\Sigma$ such that, with $m:=\min(0,\min_\Sigma\Rs_\g)$,
> $m\,\Vol(\Sigma,\g)^{2/N}\ \le\ -\Fq^{(\beta)}_\g(u)+\Y_{[\gbar]}(\Sigbar)\Big(\frac{\Vol(\Sigbar,\bar h)}{\Vol(\Sigma,\bar h)}\Big)^{\frac{N-2}{N}}$ ,
> where $\bar h$ is a Yamabe metric of $[\gbar]$; the last term is non-positive. (l.650–655)

> By Theorem~\ref{thm:yamabe}(b) there is a smooth $\psi>0$ on $\Sigbar$ such that
> $\bar h:=\psi^{4/(N-2)}\gbar$ has constant scalar curvature
> $\Rs_{\bar h}=\Y_{[\gbar]}(\Sigbar)\Vol(\Sigbar,\bar h)^{-2/N}\le0$. Let $u:=\psi|_\Sigma$ and
> $h:=\bar h|_\Sigma=u^{4/(N-2)}\g$. By Lemma~\ref{lem:kobayashi}(a),
> $\EH(\Sigma,h)\ \ge\ \aN\frac{\|\nabla u\|^2_{2}}{\|u\|^2_{\pstar}}+m\Vol(\Sigma,\g)^{2/N}$ .
> [...] $H^{\Sigma}_{h}=-H^{D_j}_{\bar h}$ on $B_j$. By definition of the boundary Yamabe constant,
> with $A_j:=\Vol(B_j,\bar h)$,
> $\int_{D_j}\Rs_{\bar h}\,\vol_{\bar h}+2(N-1)\int_{B_j}H^{D_j}_{\bar h}\,\bvol_{\bar h}
> =\EHB(D_j,\bar h|_{D_j})\,A_j^{(N-2)/(N-1)}\ \ge\ \beta_jA_j^{(N-2)/(N-1)}$ , hence
> $2(N-1)\int_{B_j}H^{\Sigma}_h\,\bvol_{\bar h}\ \le\ \Rs_{\bar h}\Vol(D_j,\bar h)-\beta_jA_j^{(N-2)/(N-1)}$ .
> Summing over $j$ and using that $\Rs_{\bar h}$ is constant, with
> $\Vol(\Sigbar,\bar h)=\Vol(\Sigma,\bar h)+\sum_j\Vol(D_j,\bar h)$ and
> $\Rs_{\bar h}\Vol(\Sigbar,\bar h)=\Y_{[\gbar]}(\Sigbar)\Vol(\Sigbar,\bar h)^{(N-2)/N}$, we obtain
> $\Vol(\Sigma,\bar h)^{(N-2)/N}\,\EH(\Sigma,h)\ \le\ \Y_{[\gbar]}(\Sigbar)\Vol(\Sigbar,\bar h)^{(N-2)/N}
> -\sum_j\beta_jA_j^{(N-2)/(N-1)}$ .
> Finally, since $\vol_{\bar h}=u^{\pstar}\vol$ and $\bvol_{\bar h}=u^{\psharp}\bvol$,
> $\Vol(\Sigma,\bar h)^{\frac{N-2}{N}}=\|u\|^2_{L^{\pstar}(\Sigma)}\ ,\quad A_j^{\frac{N-2}{N-1}}=\|u\|^2_{L^{\psharp}(B_j)}$ .
> Dividing \eqref{eq:glue-upper} by $\|u\|^2_{L^{\pstar}(\Sigma)}$ and combining with
> \eqref{eq:glue-lower} gives \eqref{eq:gluing-estimate}. (l.658–682)

> Assume that $\sigma(\Sigbar)\le0$, that $\g$ has constant scalar curvature and minimal
> boundary, and that each $(B_j,\g|_{B_j})$ is conformally equivalent to the round sphere
> (automatic for $N=3$). Then
> $\Y_{[\g]}(\Sigma)\ \le\ -\inf_{u\in W^{1,2}(\Sigma)\setminus\{0\}}\Fq_{\g}(u)$ . (l.495–498)

> By Proposition~\ref{prop:nonpositive}, or directly by hypothesis, $\Rs_\g\le0$ is constant and
> $H_\g\equiv0$, so that $\Y_{[\g]}(\Sigma)=\EH(\Sigma,\g)$, i.e.\
> $\Y_{[\g]}(\Sigma)=\Rs_\g\Vol(\Sigma,\g)^{2/N}$, by Lemma~\ref{lem:kobayashi}(a). [...]
> Lemma~\ref{lem:gluing-estimate} applied to $(\Sigbar,\gbar_\tau)$, after dropping its
> non-positive last term, yields, with $m_\tau:=\min\big(0,\min_\Sigma\Rs_{\tilde\g_\tau}\big)$,
> $m_\tau\Vol(\Sigma,\tilde\g_\tau)^{2/N}\ \le\ -\inf_{u\ne0}\Fq_{\tilde\g_\tau}(u)$ .
> As $\tau\to0$, $m_\tau\Vol(\Sigma,\tilde\g_\tau)^{2/N}\to\Rs_\g\Vol(\Sigma,\g)^{2/N}=\Y_{[\g]}(\Sigma)$
> by the uniform convergence of $\Rs_{\tilde\g_\tau}$ and $\tilde\g_\tau$, and
> $\inf\Fq_{\tilde\g_\tau}\to\inf\Fq_\g$ by Lemma~\ref{lem:stability}. This proves
> \eqref{eq:upper-bound}. [...] (l.724–728)

## The model

`Σ` is a `MeasuredModel` `M` with a `CurvedMetric` `g` (`Yamabe.Kobayashi`). A `Filling` adds the
pieces: for each `j` a `MeasuredModel` of `D_j` with one boundary component, and a measurable map
identifying `B_j ⊂ ∂Σ` with `∂D_j`. A `GluedMetric` `h̄` is a pair: `h = h̄|_Σ` (`body`) and the
`h̄|_{D_j}` (`cap j`), each a `CurvedMetric` with its own scalar curvature and the mean curvature of
its boundary w.r.t. its own outward normal. `Vol(Σ̄, h̄)` is `volBar`, the sum of the pieces'
volumes. Over a model, `EHB` (eq:yamabe-energy-bdry-norm), `confEnergyB`, `YB`
(eq:boundary-yamabe through the conformal law). The inputs are named `Prop`s: `IsConformal`
(`h = u^{4/(N-2)} g`, `u > 0`), `IsYamabeMetric` (thm:yamabe (b)), `ConformalLaw`, `ConformalLawB`
(eq:conformal-energy-bdry and its boundary form), `MeanCurvatureFlip`, `BoundaryMatch`,
`BoundaryYamabe`; `GluingInput` bundles them for the assembly.

## What is proved

`sqrt_det_smul`, `normSq_eq_lintegral`; `vol_conformal_univ`, `bvol_conformal_univ` (l.678);
`normSq_pStar_conformal`, `normSq_pSharp_conformal` (the two identities of l.680);
`vol_conformal_pos`, `bvol_conformal_pos`; `YB_le_EHB` ("by definition of the boundary Yamabe
constant", l.663); `integral_flip`, `area_match`; `boundary_term_le` (l.670); `glue_upper`
(eq:glue-upper, l.674–676); `glue_lower` (eq:glue-lower, l.660–661, from `kobayashi`);
`gluing_estimate` (eq:gluing-estimate and "the last term is non-positive", every `m ≤ 0` below
`R_g`, every `β`), `lem_gluing_estimate` (the printed `m`, the `∃ u`), `gluing_estimate_YB`
(`β_j = YB_[g_j](D_j) > -∞`); `le_neg_infF_of_gluing` (l.724–726); `abs_kobM_sub_le`,
`tendsto_kobM`, `tendsto_vol_of_uniformlyClose`, `kobM_mul_le_neg_infF` (the limit of l.728);
`upper_bound_of_limit` (eq:upper-bound from the limit, `R_g ≡ c ≤ 0`),
`upper_bound_of_limit_of_pos` (from the limit and `inf F_g > 0`, no `R_g ≤ 0`);
`GluingInput.le_neg_infF`, `upper_bound_of_gluings`, `upper_bound_of_gluings_of_pos` (the
assembly of l.723–728); the witness `toyFilling`, `toyGlued`, `toy_gluing_estimate`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N ≥ 3` (l.605) | ✓ carried |
| `(Σ̄, ḡ)` smooth closed, `Σ ⊂ Σ̄` a compact domain, `∂Σ = ⊔ B_j`, the `D_j` closures of the components of `Σ̄ ∖ Σ` meeting `Σ` along `B_j` (l.650) | ⚠ read (SCOPE): `Σ` the model `M`, the `D_j` a `Filling`, `Σ̄` through its pieces; `B_j` seen from both sides with one area measure (`BoundaryMatch`, carried) |
| compactness | ✓ carried as `IsFiniteMeasure` of `vol_g`, `vol_h`, `bvol_h` |
| `Σ` connected | ⚠ weakened: not used |
| `Σ` and the `B_j` nonempty | ✓ carried as `vol_g ≠ 0`, `bvol_g j ≠ 0` |
| `g = ḡ|_Σ` smooth | ⚠ read: `R_g`, `H_g` data of `CurvedMetric`; `DensityMeasurable` (measurable `√det` densities) |
| `H_g ≡ 0` on `∂Σ` (l.650) | ✓ carried (`MinimalBoundary`, a.e.) |
| `Y_[ḡ](Σ̄) ≤ 0` (l.650) | ⚠ read: `y ≤ 0`, `y` entering only through thm:yamabe (b) (`IsYamabeMetric`) |
| `β_j := YB_[g_j](D_j) > -∞` (l.650) | ⚠ weakened in `gluing_estimate`: any `β` with `EHB(D_j, h̄) ≥ β_j` (`BoundaryYamabe`, carried); in `gluing_estimate_YB` `β_j` is the model's `YB`, `> -∞` read as `BddBelow`, and `BoundaryYamabe` is derived (`YB_le_EHB`) from the conformal law on `D_j` (`ConformalLawB`, carried) |
| `m := min(0, min_Σ R_g)` (l.650) | ⚠ weakened: any `m ≤ 0` with `m ≤ R_g` a.e.; the printed `m` (`kobM`) in `lem_gluing_estimate`, `gluing_estimate_YB` |
| thm:yamabe (b): `ψ > 0`, `h̄ = ψ^{4/(N-2)} ḡ`, `R_h̄ = Y_[ḡ](Σ̄) Vol(Σ̄, h̄)^{-2/N}` (l.658) | ⚠ carried (cited): `u`, `h̄` given, `IsConformal` on `Σ`, `IsYamabeMetric` |
| `u = ψ|_Σ` smooth positive | ⚠ read: `Pos u`, `val u` and `tr u` a.e.-measurable, `tr u = val u` on each `B_j` |
| eq:conformal-energy-bdry for `u` (inside lem:kobayashi (a), l.660) | ⚠ carried (cited, MR1152225, MR1173925): `ConformalLaw` |
| `H^Σ_h = -H^{D_j}_h̄` on `B_j` (l.663) | ⚠ carried: `MeanCurvatureFlip` |
| `Vol(Σ̄, h̄) = Vol(Σ, h̄) + Σ_j Vol(D_j, h̄)` (l.672) | ⚠ read: `volBar` is the sum |
| `vol_h̄ = u^{p*} vol`, `bvol_h̄ = u^{p♯} bvol`, the identities of l.680 | ✓ proved from `h.G = u^{4/(N-2)} g.G` |
| thm:upper-bound: `σ(Σ̄) ≤ 0` (l.495) | ⚠ used only as `Y_[ḡ_τ](Σ̄) ≤ 0` (`GluingInput.y_nonpos`, carried) |
| `g` of constant scalar curvature, minimal boundary (l.495) | ✓ carried: `R_g x = c` for every `x`, `MinimalBoundary` |
| `(B_j, g|_{B_j})` conformally round (l.495) | ⚠ used only through lem:gluing and fact (iv), carried: the family `g̃_τ` and `β_j = c_N` |
| `R_g ≤ 0` "by prop:nonpositive, or directly by hypothesis" (l.724) | ⚠ carried (`upper_bound_of_limit`, `upper_bound_of_gluings`), or replaced by `inf F_g > 0` (lem:positivity, carried; the `_of_pos` forms): finding |
| lem:gluing (l.724) | ⚠ carried: `g̃_τ` with `UniformlyClose (η τ)`, `η → 0`, `|R_{g̃_τ} - R_g| ≤ δ τ`, `δ → 0`, minimal boundary |
| `u ∈ W^{1,2}(Σ) ∖ {0}` in `inf F` (l.498) | ⚠ read as `Adm` (OQ-44) |

## SCOPE (disclosed)

* Abstract layer only (DEC-139): the passage from Riemannian manifolds to the model waits on
  T-yamabe-scope, the model's readings on OQ-44. Neither row is marked; neither assembly is an
  anchor.
* `Σ̄` is read through its pieces: `Vol(Σ̄, h̄)` is the sum `volBar`, and `Y_[ḡ](Σ̄)` is a real
  `y`, tied to `h̄` by thm:yamabe (b) (`c = y Vol(Σ̄, h̄)^{-2/N}`). The statements hold for every
  constant-scalar-curvature `h̄` in the conformal class on `Σ`, which contains the Yamabe metrics.
* The existence of `h̄` (thm:yamabe (b)), the conformal law, the flip and `BoundaryMatch` are
  carried; the existence of `u` in `lem_gluing_estimate` is witnessed by `u = ψ|_Σ`.
* `IsConformal` is asked on `Σ` only; on the `D_j` the chain needs no conformal relation, and
  `gluing_estimate_YB` uses one only through `ConformalLawB`.
* thm:upper-bound: lem:gluing (the family `g̃_τ`), fact (iv) (`β_j = c_N`), thm:yamabe (b) on
  `(Σ̄, ḡ_τ)`, the conformal law and the flip enter through `GluingInput`; `R_g ≤ 0` or
  lem:positivity is carried. The limit (l.728) is proved.
* Finding (l.724): prop:nonpositive assumes `Σ̄` enlargeable, which thm:upper-bound does not, and
  no hypothesis of thm:upper-bound states `R_g ≤ 0`. The gap closes in the proof: the limit gives
  `min(0, R_g) Vol(Σ, g)^{2/N} ≤ -inf F_g` (`kobM_mul_le_neg_infF`), and with `inf F_g > 0`
  (lem:positivity) `R_g < 0` (`upper_bound_of_limit_of_pos`, `upper_bound_of_gluings_of_pos`).
* `normSq` is `0` on an infinite norm, Bochner integrals are `0` when not integrable, `x / 0 = 0`.
  The measures of `h` are finite (carried), the boundary areas are positive (from `bvol_g j ≠ 0`),
  so every quotient in the chain is genuine.
* Witness: on the two-point toy model, `u = 1`, `h̄ = toyCurved` on `Σ` and on `D_0`, glued by the
  identity, satisfies every hypothesis of `gluing_estimate` (`toy_gluing_estimate`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

/-! ## The conformal metric `h = u^{4/(N-2)} g` on the model -/

section Conformal

/-- `√det (c • A) = c^{|m|/2} √det A` for `c ≥ 0`. -/
lemma sqrt_det_smul {m : Type*} [Fintype m] [DecidableEq m] {c : ℝ} (hc : 0 ≤ c)
    (A : Matrix m m ℝ) :
    Real.sqrt (c • A).det = c ^ ((Fintype.card m : ℝ) / 2) * Real.sqrt A.det := by
  rw [Matrix.det_smul, Real.sqrt_mul (pow_nonneg hc _), Real.sqrt_eq_rpow (c ^ _),
    ← Real.rpow_natCast, ← Real.rpow_mul hc]
  congr 2; ring

/-- `‖f‖²_{L^q(ν)} = (∫ |f|^q dν)^{2/q}`, with the junk value `0` when the integral is infinite. -/
lemma normSq_eq_lintegral {X : Type*} [MeasurableSpace X] {ν : Measure X} {q : ℝ} (hq : 0 < q)
    (f : X → ℝ) : normSq ν q f = (∫⁻ x, ‖f x‖ₑ ^ q ∂ν).toReal ^ (2 / q) := by
  unfold normSq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.toReal_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul ENNReal.toReal_nonneg]
  congr 1; push_cast; ring

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- `h = u^{4/(N-2)} g` with `u > 0` (l.658–659): the Gram matrix of `h` is `u^{4/(N-2)}` times
that of `g`. -/
def IsConformal (g h : FrameMetric X N) (u : D) : Prop :=
  M.Pos u ∧ ∀ x, h.G x = (M.val u x) ^ (4 / ((N : ℝ) - 2)) • g.G x

/-- The densities `√det G` of `vol_g` and `√det (Pᵀ G P)` of `bvol_g` are measurable, as for a
smooth metric. -/
def DensityMeasurable (g : FrameMetric X N) : Prop :=
  AEMeasurable (fun x => ENNReal.ofReal (Real.sqrt (g.G x).det)) M.μ ∧
    ∀ j, AEMeasurable (fun x => ENNReal.ofReal (Real.sqrt ((M.P x)ᵀ * g.G x * M.P x).det)) (M.μb j)

variable {M}

/-- `(4/(N-2)) · (N/2) = p*`. -/
lemma conf_exp_pStar (hN : 3 ≤ N) : 4 / ((N : ℝ) - 2) * ((N : ℝ) / 2) = pStar N := by
  have := three_le_cast hN
  have h2 : (N:ℝ) - 2 ≠ 0 := by linarith
  unfold pStar; field_simp; ring

/-- `(4/(N-2)) · ((N-1)/2) = p♯`. -/
lemma conf_exp_pSharp (hN : 3 ≤ N) : 4 / ((N : ℝ) - 2) * (((N - 1 : ℕ) : ℝ) / 2) = pSharp N := by
  have := three_le_cast hN
  have h2 : (N:ℝ) - 2 ≠ 0 := by linarith
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold pSharp; field_simp; ring

/-- `vol_h = u^{p*} vol_g` (l.678), evaluated on `Σ`. -/
theorem vol_conformal_univ (hN : 3 ≤ N) {g h : FrameMetric X N} {u : D}
    (hc : M.IsConformal g h u) (hρ : M.DensityMeasurable g) :
    M.vol h Set.univ = ∫⁻ x, ‖M.val u x‖ₑ ^ pStar N ∂(M.vol g) := by
  unfold vol
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hρ.1
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1; funext x
  have hv := hc.1 x
  simp only [Pi.mul_apply]
  rw [hc.2 x, sqrt_det_smul (Real.rpow_nonneg hv.le _), Fintype.card_fin,
    ← Real.rpow_mul hv.le, conf_exp_pStar hN, Real.enorm_eq_ofReal hv.le,
    ENNReal.ofReal_rpow_of_pos hv, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm]

/-- `bvol_h = u^{p♯} bvol_g` (l.678), evaluated on `B_j`. -/
theorem bvol_conformal_univ (hN : 3 ≤ N) {g h : FrameMetric X N} {u : D}
    (hc : M.IsConformal g h u) (hρ : M.DensityMeasurable g) (j : Fin n) :
    M.bvol h j Set.univ = ∫⁻ x, ‖M.val u x‖ₑ ^ pSharp N ∂(M.bvol g j) := by
  unfold bvol
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ (hρ.2 j)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1; funext x
  have hv := hc.1 x
  simp only [Pi.mul_apply]
  rw [hc.2 x, Matrix.mul_smul, Matrix.smul_mul, sqrt_det_smul (Real.rpow_nonneg hv.le _),
    Fintype.card_fin, ← Real.rpow_mul hv.le, conf_exp_pSharp hN, Real.enorm_eq_ofReal hv.le,
    ENNReal.ofReal_rpow_of_pos hv, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm]

/-- The first conformal identity of l.680: `Vol(Σ, h)^{(N-2)/N} = ‖u‖²_{L^{p*}(Σ, g)}`. -/
theorem normSq_pStar_conformal (hN : 3 ≤ N) {g h : FrameMetric X N} {u : D}
    (hc : M.IsConformal g h u) (hρ : M.DensityMeasurable g) :
    normSq (M.vol g) (pStar N) (M.val u) = (M.vol h Set.univ).toReal ^ (((N : ℝ) - 2) / N) := by
  rw [normSq_eq_lintegral (pStar_pos hN), ← vol_conformal_univ hN hc hρ, two_div_pStar hN]

/-- The second conformal identity of l.680: `A_j^{(N-2)/(N-1)} = ‖u‖²_{L^{p♯}(B_j, g)}`, the
trace of `u` being its boundary value. -/
theorem normSq_pSharp_conformal (hN : 3 ≤ N) {g h : FrameMetric X N} {u : D}
    (hc : M.IsConformal g h u) (hρ : M.DensityMeasurable g) (j : Fin n)
    (htr : M.tr u =ᵐ[M.bvol g j] M.val u) :
    normSq (M.bvol g j) (pSharp N) (M.tr u) =
      (M.bvol h j Set.univ).toReal ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) := by
  rw [normSq_eq_lintegral (pSharp_pos hN), bvol_conformal_univ hN hc hρ j, two_div_pSharp hN]
  congr 2
  exact lintegral_congr_ae (htr.mono fun x hx => by simp only [hx])

/-- `Vol(Σ, h) > 0` when `Σ` has positive `g`-volume and `u > 0`. -/
theorem vol_conformal_pos (hN : 3 ≤ N) {g h : FrameMetric X N} {u : D}
    (hc : M.IsConformal g h u) (hρ : M.DensityMeasurable g) [IsFiniteMeasure (M.vol h)]
    (hV : M.vol g ≠ 0) (hum : AEStronglyMeasurable (M.val u) (M.vol g)) :
    0 < (M.vol h Set.univ).toReal := by
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  rw [vol_conformal_univ hN hc hρ]
  intro h0
  rw [lintegral_eq_zero_iff' (hum.enorm.pow_const _)] at h0
  apply hV
  have hF : ∀ᵐ x ∂(M.vol g), False := h0.mono fun x hx => by
    have hv := hc.1 x
    simp only [Pi.zero_apply] at hx
    rw [Real.enorm_eq_ofReal hv.le, ENNReal.ofReal_rpow_of_pos hv, ENNReal.ofReal_eq_zero] at hx
    exact absurd hx (not_le.mpr (Real.rpow_pos_of_pos hv _))
  simpa using hF

/-- `A_j = Vol(B_j, h) > 0` when `B_j` has positive `g`-area and `u > 0`. -/
theorem bvol_conformal_pos (hN : 3 ≤ N) {g h : FrameMetric X N} {u : D}
    (hc : M.IsConformal g h u) (hρ : M.DensityMeasurable g) (j : Fin n)
    [IsFiniteMeasure (M.bvol h j)] (hB : M.bvol g j ≠ 0)
    (hut : AEStronglyMeasurable (M.tr u) (M.bvol g j)) (htr : M.tr u =ᵐ[M.bvol g j] M.val u) :
    0 < (M.bvol h j Set.univ).toReal := by
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  rw [bvol_conformal_univ hN hc hρ j]
  have e : ∫⁻ x, ‖M.val u x‖ₑ ^ pSharp N ∂(M.bvol g j) = ∫⁻ x, ‖M.tr u x‖ₑ ^ pSharp N ∂(M.bvol g j) :=
    lintegral_congr_ae (htr.mono fun x hx => by simp only [hx])
  rw [e]
  intro h0
  rw [lintegral_eq_zero_iff' (hut.enorm.pow_const _)] at h0
  apply hB
  have hF : ∀ᵐ x ∂(M.bvol g j), False := (h0.and htr).mono fun x ⟨hx, hx'⟩ => by
    have hv := hc.1 x
    simp only [Pi.zero_apply] at hx
    rw [hx', Real.enorm_eq_ofReal hv.le, ENNReal.ofReal_rpow_of_pos hv, ENNReal.ofReal_eq_zero] at hx
    exact absurd hx (not_le.mpr (Real.rpow_pos_of_pos hv _))
  simpa using hF

end MeasuredModel

end Conformal

/-! ## The boundary-normalized energy and the boundary Yamabe constant -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- `Vol(∂Σ, g) = Σ_j Vol(B_j, g)`. -/
def bdryVol (g : FrameMetric X N) : ℝ := ∑ j, (M.bvol g j Set.univ).toReal

/-- The boundary-normalized Yamabe energy `EHB(Σ, g) = 𝒮(Σ, g) / Vol(∂Σ, g)^{(N-2)/(N-1)}`
(eq:yamabe-energy-bdry-norm, l.313). -/
def EHB (g : CurvedMetric X N) : ℝ :=
  M.action g / M.bdryVol g.toFrameMetric ^ (((N : ℝ) - 2) / ((N : ℝ) - 1))

/-- The boundary-normalized conformal energy: the right side of eq:conformal-energy-bdry over
`‖u‖²_{L^{p♯}(∂Σ, g)}` (l.330), `EHB(Σ, u^{4/(N-2)} g)` through the conformal law. -/
def confEnergyB (g : CurvedMetric X N) (u : D) : ℝ :=
  M.confAction g u / normSq (∑ j, M.bvol g.toFrameMetric j) (pSharp N) (M.tr u)

/-- `u` is a competitor for the boundary Yamabe constant: `0 < ‖u‖²_{L^{p♯}(∂Σ, g)}`. -/
def AdmB (g : FrameMetric X N) (u : D) : Prop :=
  0 < normSq (∑ j, M.bvol g j) (pSharp N) (M.tr u)

/-- The boundary Yamabe constant `YB_[g](Σ) = inf_{φ > 0} EHB(Σ, φ^{4/(N-2)} g)`
(eq:boundary-yamabe, l.320), through the conformal law. -/
def YB (g : CurvedMetric X N) : ℝ :=
  sInf (M.confEnergyB g '' {u | M.Pos u ∧ M.AdmB g.toFrameMetric u})

/-- The conformal law eq:conformal-energy-bdry (l.326–328, cited: MR1152225, MR1173925) for the
conformal factor `u` and the metric `h = u^{4/(N-2)} g`:
`EH(Σ, h) ‖u‖²_{L^{p*}(Σ, g)} = a_N ‖∇u‖² + ∫ R_g u² + 2(N-1) ∫ H_g u²`. -/
def ConformalLaw (g : CurvedMetric X N) (u : D) (h : CurvedMetric X N) : Prop :=
  M.EH h * normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) = M.confAction g u

/-- Its boundary-normalized form (l.330): the same right side equals
`EHB(Σ, h) ‖u‖²_{L^{p♯}(∂Σ, g)}`. -/
def ConformalLawB (g : CurvedMetric X N) (u : D) (h : CurvedMetric X N) : Prop :=
  M.EHB h * normSq (∑ j, M.bvol g.toFrameMetric j) (pSharp N) (M.tr u) = M.confAction g u

variable {M}

/-- "By definition of the boundary Yamabe constant" (l.663): `YB_[g](Σ) ≤ EHB(Σ, h)` for
`h = ψ^{4/(N-2)} g`, `ψ > 0` a competitor, through the conformal law, when `YB_[g](Σ) > -∞`
(the energies are bounded below). -/
theorem YB_le_EHB {g h : CurvedMetric X N} {ψ : D} (hψ : M.Pos ψ) (hadm : M.AdmB g.toFrameMetric ψ)
    (hlaw : M.ConformalLawB g ψ h)
    (hbdd : BddBelow (M.confEnergyB g '' {u | M.Pos u ∧ M.AdmB g.toFrameMetric u})) :
    M.YB g ≤ M.EHB h := by
  have hE : M.EHB h = M.confEnergyB g ψ := by
    unfold confEnergyB
    rw [← hlaw, mul_div_assoc, div_self hadm.ne', mul_one]
  rw [hE]
  exact csInf_le hbdd ⟨ψ, ⟨hψ, hadm⟩, rfl⟩

end MeasuredModel

/-! ## The filling: the pieces `D_j` of `Σ̄ ∖ Σ` -/

/-- The pieces `D_j` (l.650): for each `j`, a measured model of the closure `D_j` of a component of
`Σ̄ ∖ Σ`, with one boundary component `∂D_j = B_j`, and the identification of `B_j ⊂ ∂Σ` with
`∂D_j` ("each `D_j` meeting `Σ` along `B_j`"). All pieces live over one carrier `Y`. -/
structure Filling (X : Type*) [MeasurableSpace X] (Y E : Type*) [MeasurableSpace Y]
    [AddCommGroup E] [Module ℝ E] (N n : ℕ) where
  /-- the model of `D_j` -/
  piece : Fin n → MeasuredModel Y E N 1
  /-- `B_j ⊂ ∂Σ`, identified with `∂D_j` -/
  glue : Fin n → X → Y
  glue_measurable : ∀ j, Measurable (glue j)

/-- A metric `h̄` on `Σ̄ = Σ ∪ ⊔ D_j`, through its restrictions `h = h̄|_Σ` and `h̄|_{D_j}`, each
with its scalar curvature and the mean curvature of its boundary w.r.t. its own outward normal. -/
structure GluedMetric (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] (N n : ℕ) where
  /-- `h = h̄|_Σ` -/
  body : CurvedMetric X N
  /-- `h̄|_{D_j}` -/
  cap : Fin n → CurvedMetric Y N

namespace Filling

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable (F : Filling X Y E N n) (M : MeasuredModel X D N n) (hb : GluedMetric X Y N n)

/-- `Vol(Σ̄, h̄) = Vol(Σ, h̄) + Σ_j Vol(D_j, h̄)` (l.672): `Σ̄` is read through its pieces. -/
def volBar : ℝ :=
  (M.vol hb.body.toFrameMetric Set.univ).toReal +
    ∑ j, ((F.piece j).vol (hb.cap j).toFrameMetric Set.univ).toReal

/-- thm:yamabe (b), as used at l.658: `h̄` has constant scalar curvature
`R_h̄ = c = Y_[ḡ](Σ̄) Vol(Σ̄, h̄)^{-2/N}`, with `y` standing for `Y_[ḡ](Σ̄)`. -/
def IsYamabeMetric (y c : ℝ) : Prop :=
  (∀ᵐ x ∂(M.vol hb.body.toFrameMetric), hb.body.R x = c) ∧
    (∀ j, ∀ᵐ x ∂((F.piece j).vol (hb.cap j).toFrameMetric), (hb.cap j).R x = c) ∧
    c = y * F.volBar M hb ^ (-(2 / (N : ℝ)))

/-- The mean-curvature flip (l.663): `H^Σ_h = -H^{D_j}_h̄` on `B_j`. -/
def MeanCurvatureFlip : Prop :=
  ∀ j, ∀ᵐ x ∂(M.bvol hb.body.toFrameMetric j), hb.body.H x = -(hb.cap j).H (F.glue j x)

/-- `B_j` carries one area measure, whether seen from `Σ` or from `D_j` (l.650, and
`A_j := Vol(B_j, h̄)`, l.663): the identification pushes `bvol_h` on `B_j` to `bvol_h̄` on `∂D_j`. -/
def BoundaryMatch : Prop :=
  ∀ j, (M.bvol hb.body.toFrameMetric j).map (F.glue j) =
    (F.piece j).bvol (hb.cap j).toFrameMetric 0

/-- The boundary Yamabe inequality on `D_j` (l.663–666): `EHB(D_j, h̄|_{D_j}) ≥ β_j`. -/
def BoundaryYamabe (β : Fin n → ℝ) : Prop :=
  ∀ j, β j ≤ (F.piece j).EHB (hb.cap j)

variable {F M hb}

/-- The flip, integrated: `∫_{B_j} H^Σ_h bvol_h = -∫_{∂D_j} H^{D_j}_h̄ bvol_h̄`. -/
theorem integral_flip (hflip : F.MeanCurvatureFlip M hb) (hmatch : F.BoundaryMatch M hb)
    (j : Fin n) :
    ∫ x, hb.body.H x ∂(M.bvol hb.body.toFrameMetric j) =
      -∫ y, (hb.cap j).H y ∂((F.piece j).bvol (hb.cap j).toFrameMetric 0) := by
  rw [← hmatch j, integral_map (F.glue_measurable j).aemeasurable
    (hb.cap j).H_measurable.aestronglyMeasurable, ← integral_neg]
  exact integral_congr_ae (hflip j)

/-- `A_j` is the same from both sides. -/
theorem area_match (hmatch : F.BoundaryMatch M hb) (j : Fin n) :
    ((F.piece j).bvol (hb.cap j).toFrameMetric 0 Set.univ).toReal =
      (M.bvol hb.body.toFrameMetric j Set.univ).toReal := by
  rw [← hmatch j, Measure.map_apply (F.glue_measurable j) MeasurableSet.univ, Set.preimage_univ]

/-- l.670: `2(N-1) ∫_{B_j} H^Σ_h bvol_h̄ ≤ R_h̄ Vol(D_j, h̄) - β_j A_j^{(N-2)/(N-1)}`. -/
theorem boundary_term_le {β : Fin n → ℝ} (hYB : F.BoundaryYamabe hb β) {c : ℝ}
    (hRc : ∀ j, ∀ᵐ x ∂((F.piece j).vol (hb.cap j).toFrameMetric), (hb.cap j).R x = c)
    (hflip : F.MeanCurvatureFlip M hb) (hmatch : F.BoundaryMatch M hb) (j : Fin n)
    (hA : 0 < (M.bvol hb.body.toFrameMetric j Set.univ).toReal) :
    2 * ((N : ℝ) - 1) * ∫ x, hb.body.H x ∂(M.bvol hb.body.toFrameMetric j) ≤
      c * ((F.piece j).vol (hb.cap j).toFrameMetric Set.univ).toReal -
        β j * (M.bvol hb.body.toFrameMetric j Set.univ).toReal ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) := by
  have hAe : 0 < (M.bvol hb.body.toFrameMetric j Set.univ).toReal ^
      (((N : ℝ) - 2) / ((N : ℝ) - 1)) := Real.rpow_pos_of_pos hA _
  have hbd : (F.piece j).bdryVol (hb.cap j).toFrameMetric =
      (M.bvol hb.body.toFrameMetric j Set.univ).toReal := by
    unfold MeasuredModel.bdryVol
    rw [Fin.sum_univ_one]
    exact area_match hmatch j
  have hR : ∫ x, (hb.cap j).R x ∂((F.piece j).vol (hb.cap j).toFrameMetric) =
      c * ((F.piece j).vol (hb.cap j).toFrameMetric Set.univ).toReal := by
    rw [integral_congr_ae (hRc j), integral_const, smul_eq_mul, measureReal_def, mul_comm]
  have hact : (F.piece j).action (hb.cap j) =
      c * ((F.piece j).vol (hb.cap j).toFrameMetric Set.univ).toReal +
        2 * ((N : ℝ) - 1) * ∫ y, (hb.cap j).H y ∂((F.piece j).bvol (hb.cap j).toFrameMetric 0) := by
    unfold MeasuredModel.action
    rw [hR, Fin.sum_univ_one]
  have h1 := hYB j
  unfold MeasuredModel.EHB at h1
  rw [hbd, hact, le_div_iff₀ hAe] at h1
  rw [integral_flip hflip hmatch j]
  linarith

/-- eq:glue-upper (l.674–676):
`Vol(Σ, h̄)^{(N-2)/N} EH(Σ, h) ≤ Y_[ḡ](Σ̄) Vol(Σ̄, h̄)^{(N-2)/N} - Σ_j β_j A_j^{(N-2)/(N-1)}`. -/
theorem glue_upper (hN : 3 ≤ N) {β : Fin n → ℝ} (hYB : F.BoundaryYamabe hb β) {y c : ℝ}
    (hyam : F.IsYamabeMetric M hb y c) (hflip : F.MeanCurvatureFlip M hb)
    (hmatch : F.BoundaryMatch M hb) (hV : 0 < (M.vol hb.body.toFrameMetric Set.univ).toReal)
    (hA : ∀ j, 0 < (M.bvol hb.body.toFrameMetric j Set.univ).toReal) :
    (M.vol hb.body.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) * M.EH hb.body ≤
      y * F.volBar M hb ^ (((N : ℝ) - 2) / N) -
        ∑ j, β j * (M.bvol hb.body.toFrameMetric j Set.univ).toReal ^
          (((N : ℝ) - 2) / ((N : ℝ) - 1)) := by
  have hN' := three_le_cast hN
  set V := (M.vol hb.body.toFrameMetric Set.univ).toReal with hVdef
  have hVe : 0 < V ^ (((N : ℝ) - 2) / N) := Real.rpow_pos_of_pos hV _
  have hEH : V ^ (((N : ℝ) - 2) / N) * M.EH hb.body = M.action hb.body := by
    unfold MeasuredModel.EH
    rw [← hVdef]
    field_simp
  have hRint : ∫ x, hb.body.R x ∂(M.vol hb.body.toFrameMetric) = c * V := by
    rw [integral_congr_ae hyam.1, integral_const, smul_eq_mul, measureReal_def, mul_comm]
  have hsum : 2 * ((N : ℝ) - 1) * ∑ j, ∫ x, hb.body.H x ∂(M.bvol hb.body.toFrameMetric j) ≤
      ∑ j, (c * ((F.piece j).vol (hb.cap j).toFrameMetric Set.univ).toReal -
        β j * (M.bvol hb.body.toFrameMetric j Set.univ).toReal ^
          (((N : ℝ) - 2) / ((N : ℝ) - 1))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => boundary_term_le hYB hyam.2.1 hflip hmatch j (hA j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hbar_pos : 0 < F.volBar M hb := by
    unfold volBar
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      (ENNReal.toReal_nonneg : 0 ≤ ((F.piece j).vol (hb.cap j).toFrameMetric Set.univ).toReal)
    rw [← hVdef]
    linarith
  have hcV : c * F.volBar M hb = y * F.volBar M hb ^ (((N : ℝ) - 2) / N) := by
    rw [hyam.2.2, mul_assoc, ← Real.rpow_add_one hbar_pos.ne']
    congr 2
    field_simp
    ring
  have hsplit : c * F.volBar M hb = c * V +
      c * ∑ j, ((F.piece j).vol (hb.cap j).toFrameMetric Set.univ).toReal := by
    unfold volBar
    rw [← hVdef]
    ring
  rw [hEH]
  unfold MeasuredModel.action
  rw [hRint]
  linarith

end Filling

/-! ## The lower bound eq:glue-lower and the gluing estimate -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable {M : MeasuredModel X D N n}

/-- eq:glue-lower (l.660–661), from lem:kobayashi (a) and the conformal law:
`EH(Σ, h) ≥ a_N ‖∇u‖²_2 / ‖u‖²_{p*} + m Vol(Σ, g)^{2/N}`. -/
theorem glue_lower (hN : 3 ≤ N) {g : CurvedMetric X N} [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hH : M.MinimalBoundary g) {m : ℝ} (hm : m ≤ 0)
    (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x) {u : D}
    (hum : AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric)) {h : CurvedMetric X N}
    (hlaw : M.ConformalLaw g u h) (hQ : 0 < normSq (M.vol g.toFrameMetric) (pStar N) (M.val u)) :
    aN N * M.dirichlet g.toFrameMetric u / normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) +
        m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤ M.EH h := by
  have hk := M.kobayashi g hN hH hm hmR u hum
  have hE : M.confEnergy g u = M.EH h := by
    unfold confEnergy
    rw [← hlaw, mul_div_assoc, div_self hQ.ne', mul_one]
  rw [← hE]
  exact hk

end MeasuredModel

namespace Filling

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}

/-- lem:gluing-estimate (eq:gluing-estimate, l.651–655), its chain (l.657–683), over the model
extended by the pieces `D_j`, for every `m ≤ 0` below `R_g` and every `β`, the inputs carried as
hypotheses: `hyam` (thm:yamabe (b), l.658), `hlaw` (eq:conformal-energy-bdry, l.326–328),
`hYB` (the boundary Yamabe inequality on `D_j`, l.663–666), `hflip` (the mean-curvature flip,
l.663), `hmatch` (`B_j` seen from both sides, l.650). -/
theorem gluing_estimate (hN : 3 ≤ N) (F : Filling X Y E N n) (M : MeasuredModel X D N n)
    (g : CurvedMetric X N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hV : M.vol g.toFrameMetric ≠ 0) (hB : ∀ j, M.bvol g.toFrameMetric j ≠ 0)
    (hρ : M.DensityMeasurable g.toFrameMetric) (hH : M.MinimalBoundary g) {m : ℝ} (hm : m ≤ 0)
    (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x)
    (hb : GluedMetric X Y N n) (u : D) (hconf : M.IsConformal g.toFrameMetric hb.body.toFrameMetric u)
    (hum : AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hut : ∀ j, AEStronglyMeasurable (M.tr u) (M.bvol g.toFrameMetric j))
    (htr : ∀ j, M.tr u =ᵐ[M.bvol g.toFrameMetric j] M.val u)
    [IsFiniteMeasure (M.vol hb.body.toFrameMetric)]
    [∀ j, IsFiniteMeasure (M.bvol hb.body.toFrameMetric j)]
    {y c : ℝ} (hy : y ≤ 0) (hyam : F.IsYamabeMetric M hb y c) (hlaw : M.ConformalLaw g u hb.body)
    (β : Fin n → ℝ) (hYB : F.BoundaryYamabe hb β) (hflip : F.MeanCurvatureFlip M hb)
    (hmatch : F.BoundaryMatch M hb) :
    m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
        -M.F g.toFrameMetric β u +
          y * (F.volBar M hb / (M.vol hb.body.toFrameMetric Set.univ).toReal) ^
            (((N : ℝ) - 2) / N) ∧
      y * (F.volBar M hb / (M.vol hb.body.toFrameMetric Set.univ).toReal) ^
          (((N : ℝ) - 2) / N) ≤ 0 := by
  have hN' := three_le_cast hN
  have hVpos := MeasuredModel.vol_conformal_pos hN hconf hρ hV hum
  have hApos : ∀ j, 0 < (M.bvol hb.body.toFrameMetric j Set.univ).toReal := fun j =>
    MeasuredModel.bvol_conformal_pos hN hconf hρ j (hB j) (hut j) (htr j)
  have hQ := MeasuredModel.normSq_pStar_conformal hN hconf hρ
  have hT : ∀ j, normSq (M.bvol g.toFrameMetric j) (pSharp N) (M.tr u) =
      (M.bvol hb.body.toFrameMetric j Set.univ).toReal ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) :=
    fun j => MeasuredModel.normSq_pSharp_conformal hN hconf hρ j (htr j)
  set V := (M.vol hb.body.toFrameMetric Set.univ).toReal with hVdef
  have hVe : 0 < V ^ (((N : ℝ) - 2) / N) := Real.rpow_pos_of_pos hVpos _
  have hlo := MeasuredModel.glue_lower hN hH hm hmR hum hlaw (by rw [hQ]; exact hVe)
  have hup := glue_upper hN hYB hyam hflip hmatch hVpos hApos
  have hbar_nonneg : 0 ≤ F.volBar M hb := by
    unfold volBar
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      (ENNReal.toReal_nonneg : 0 ≤ ((F.piece j).vol (hb.cap j).toFrameMetric Set.univ).toReal)
    rw [← hVdef]
    linarith
  have hlast : y * (F.volBar M hb / V) ^ (((N : ℝ) - 2) / N) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hy (Real.rpow_nonneg (div_nonneg hbar_nonneg hVpos.le) _)
  refine ⟨?_, hlast⟩
  rw [hQ] at hlo
  unfold MeasuredModel.F traceSobolevQuot
  simp only [hT]
  rw [hQ, Real.div_rpow hbar_nonneg hVpos.le]
  set S := ∑ j, β j * (M.bvol hb.body.toFrameMetric j Set.univ).toReal ^
    (((N : ℝ) - 2) / ((N : ℝ) - 1)) with hS
  have hEH : M.EH hb.body ≤ (y * F.volBar M hb ^ (((N : ℝ) - 2) / N) - S) /
      V ^ (((N : ℝ) - 2) / N) := by
    rw [le_div_iff₀ hVe]
    linarith
  have e : -((aN N * M.dirichlet g.toFrameMetric u + S) / V ^ (((N : ℝ) - 2) / N)) +
      y * (F.volBar M hb ^ (((N : ℝ) - 2) / N) / V ^ (((N : ℝ) - 2) / N)) =
      (y * F.volBar M hb ^ (((N : ℝ) - 2) / N) - S) / V ^ (((N : ℝ) - 2) / N) -
        aN N * M.dirichlet g.toFrameMetric u / V ^ (((N : ℝ) - 2) / N) := by
    field_simp
    ring
  rw [e]
  linarith

/-- lem:gluing-estimate with the printed `m = min(0, min_Σ R_g)` (l.650), stated as printed:
there is a positive `u` (here `u = ψ|_Σ`) for which eq:gluing-estimate holds, and its last term is
non-positive. -/
theorem lem_gluing_estimate (hN : 3 ≤ N) (F : Filling X Y E N n) (M : MeasuredModel X D N n)
    (g : CurvedMetric X N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hV : M.vol g.toFrameMetric ≠ 0) (hB : ∀ j, M.bvol g.toFrameMetric j ≠ 0)
    (hρ : M.DensityMeasurable g.toFrameMetric) (hH : M.MinimalBoundary g)
    (hb : GluedMetric X Y N n) (ψ : D) (hconf : M.IsConformal g.toFrameMetric hb.body.toFrameMetric ψ)
    (hum : AEStronglyMeasurable (M.val ψ) (M.vol g.toFrameMetric))
    (hut : ∀ j, AEStronglyMeasurable (M.tr ψ) (M.bvol g.toFrameMetric j))
    (htr : ∀ j, M.tr ψ =ᵐ[M.bvol g.toFrameMetric j] M.val ψ)
    [IsFiniteMeasure (M.vol hb.body.toFrameMetric)]
    [∀ j, IsFiniteMeasure (M.bvol hb.body.toFrameMetric j)]
    {y c : ℝ} (hy : y ≤ 0) (hyam : F.IsYamabeMetric M hb y c) (hlaw : M.ConformalLaw g ψ hb.body)
    (β : Fin n → ℝ) (hYB : F.BoundaryYamabe hb β) (hflip : F.MeanCurvatureFlip M hb)
    (hmatch : F.BoundaryMatch M hb) :
    ∃ u : D, M.Pos u ∧
      g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
          -M.F g.toFrameMetric β u +
            y * (F.volBar M hb / (M.vol hb.body.toFrameMetric Set.univ).toReal) ^
              (((N : ℝ) - 2) / N) ∧
        y * (F.volBar M hb / (M.vol hb.body.toFrameMetric Set.univ).toReal) ^
            (((N : ℝ) - 2) / N) ≤ 0 := by
  exact ⟨ψ, hconf.1, gluing_estimate hN F M g hV hB hρ hH g.kobM_nonpos (ae_of_all _ g.kobM_le)
    hb ψ hconf hum hut htr hy hyam hlaw β hYB hflip hmatch⟩

/-- lem:gluing-estimate with `β_j := YB_[g_j](D_j) > -∞` (l.650), the boundary Yamabe inequality
on `D_j` derived "by definition of the boundary Yamabe constant" (l.663) from the conformal law
on `D_j` (l.330) for `h̄|_{D_j} = ψ_j^{4/(N-2)} g_j`. -/
theorem gluing_estimate_YB (hN : 3 ≤ N) (F : Filling X Y E N n) (M : MeasuredModel X D N n)
    (g : CurvedMetric X N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hV : M.vol g.toFrameMetric ≠ 0) (hB : ∀ j, M.bvol g.toFrameMetric j ≠ 0)
    (hρ : M.DensityMeasurable g.toFrameMetric) (hH : M.MinimalBoundary g)
    (hb : GluedMetric X Y N n) (u : D) (hconf : M.IsConformal g.toFrameMetric hb.body.toFrameMetric u)
    (hum : AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hut : ∀ j, AEStronglyMeasurable (M.tr u) (M.bvol g.toFrameMetric j))
    (htr : ∀ j, M.tr u =ᵐ[M.bvol g.toFrameMetric j] M.val u)
    [IsFiniteMeasure (M.vol hb.body.toFrameMetric)]
    [∀ j, IsFiniteMeasure (M.bvol hb.body.toFrameMetric j)]
    {y c : ℝ} (hy : y ≤ 0) (hyam : F.IsYamabeMetric M hb y c) (hlaw : M.ConformalLaw g u hb.body)
    (gj : Fin n → CurvedMetric Y N) (ψj : Fin n → E) (hψj : ∀ j, (F.piece j).Pos (ψj j))
    (hadm : ∀ j, (F.piece j).AdmB (gj j).toFrameMetric (ψj j))
    (hlawj : ∀ j, (F.piece j).ConformalLawB (gj j) (ψj j) (hb.cap j))
    (hfin : ∀ j, BddBelow ((F.piece j).confEnergyB (gj j) ''
      {v | (F.piece j).Pos v ∧ (F.piece j).AdmB (gj j).toFrameMetric v}))
    (hflip : F.MeanCurvatureFlip M hb) (hmatch : F.BoundaryMatch M hb) :
    g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
        -M.F g.toFrameMetric (fun j => (F.piece j).YB (gj j)) u +
          y * (F.volBar M hb / (M.vol hb.body.toFrameMetric Set.univ).toReal) ^
            (((N : ℝ) - 2) / N) ∧
      y * (F.volBar M hb / (M.vol hb.body.toFrameMetric Set.univ).toReal) ^
          (((N : ℝ) - 2) / N) ≤ 0 := by
  exact gluing_estimate hN F M g hV hB hρ hH g.kobM_nonpos (ae_of_all _ g.kobM_le)
    hb u hconf hum hut htr hy hyam hlaw _
    (fun j => MeasuredModel.YB_le_EHB (hψj j) (hadm j) (hlawj j) (hfin j)) hflip hmatch

/-- thm:upper-bound's proof, l.724–726: with `β_j = c_N` (fact (iv)) and `Y_[ḡ](Σ̄) ≤ 0`, the
gluing estimate "after dropping its non-positive last term" gives
`m Vol(Σ, g)^{2/N} ≤ -inf_{u ≠ 0} F_g(u)`. -/
theorem le_neg_infF_of_gluing (hN : 3 ≤ N) (F : Filling X Y E N n) (M : MeasuredModel X D N n)
    (g : CurvedMetric X N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hV : M.vol g.toFrameMetric ≠ 0) (hB : ∀ j, M.bvol g.toFrameMetric j ≠ 0)
    (hρ : M.DensityMeasurable g.toFrameMetric) (hH : M.MinimalBoundary g) {m : ℝ} (hm : m ≤ 0)
    (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x)
    (hb : GluedMetric X Y N n) (u : D) (hconf : M.IsConformal g.toFrameMetric hb.body.toFrameMetric u)
    (hum : AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hut : ∀ j, AEStronglyMeasurable (M.tr u) (M.bvol g.toFrameMetric j))
    (htr : ∀ j, M.tr u =ᵐ[M.bvol g.toFrameMetric j] M.val u)
    [IsFiniteMeasure (M.vol hb.body.toFrameMetric)]
    [∀ j, IsFiniteMeasure (M.bvol hb.body.toFrameMetric j)]
    {y c : ℝ} (hy : y ≤ 0) (hyam : F.IsYamabeMetric M hb y c) (hlaw : M.ConformalLaw g u hb.body)
    (hYB : F.BoundaryYamabe hb (fun _ => cN N)) (hflip : F.MeanCurvatureFlip M hb)
    (hmatch : F.BoundaryMatch M hb) :
    m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      -M.infF g.toFrameMetric (fun _ => cN N) := by
  have h := gluing_estimate hN F M g hV hB hρ hH hm hmR hb u hconf hum hut htr hy hyam hlaw _
    hYB hflip hmatch
  have hadm : M.Adm g.toFrameMetric u := by
    unfold MeasuredModel.Adm
    rw [MeasuredModel.normSq_pStar_conformal hN hconf hρ]
    exact Real.rpow_pos_of_pos (MeasuredModel.vol_conformal_pos hN hconf hρ hV hum) _
  have hinf : M.infF g.toFrameMetric (fun _ => cN N) ≤ M.F g.toFrameMetric (fun _ => cN N) u := by
    unfold MeasuredModel.infF
    refine csInf_le ⟨0, ?_⟩ ⟨u, hadm, rfl⟩
    rintro _ ⟨v, _, rfl⟩
    exact M.F_nonneg g.toFrameMetric hN (fun _ => (cN_pos (by omega)).le) v
  linarith [h.1, h.2]

end Filling

/-! ## The `τ → 0` step of thm:upper-bound (l.728) -/

namespace CurvedMetric

variable {X : Type*} [MeasurableSpace X] {N : ℕ}

/-- `m = min(0, min_Σ R)` is `1`-Lipschitz in `R` for the uniform distance. -/
theorem abs_kobM_sub_le [Nonempty X] (g g' : CurvedMetric X N) {δ : ℝ}
    (h : ∀ x, |g'.R x - g.R x| ≤ δ) : |g'.kobM - g.kobM| ≤ δ := by
  have hb := g.bddBelow_R
  have hb' := g'.bddBelow_R
  have h1 : (⨅ x, g'.R x) - δ ≤ ⨅ x, g.R x := le_ciInf fun x => by
    have := ciInf_le hb' x
    have := (abs_le.mp (h x)).2
    linarith
  have h2 : (⨅ x, g.R x) - δ ≤ ⨅ x, g'.R x := le_ciInf fun x => by
    have := ciInf_le hb x
    have := (abs_le.mp (h x)).1
    linarith
  have hδ : 0 ≤ δ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (abs_nonneg _).trans (h x)
  unfold kobM
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [sub_self, abs_zero]; exact hδ
  · exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- `m_τ → m` when `R_{g̃_τ} → R_g` uniformly (l.728). -/
theorem tendsto_kobM (g : CurvedMetric X N) {ι : Type*} {l : Filter ι} (gs : ι → CurvedMetric X N)
    (δ : ι → ℝ) (hδt : Tendsto δ l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ δ i) :
    Tendsto (fun i => (gs i).kobM) l (𝓝 g.kobM) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have e : ∀ g' : CurvedMetric X N, g'.kobM = 0 := fun g' => by
      simp [kobM, Real.iInf_of_isEmpty]
    simp only [e]
    exact tendsto_const_nhds
  · refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [hδt.eventually (gt_mem_nhds hε)] with i hi
    rw [Real.dist_eq]
    exact (abs_kobM_sub_le g (gs i) (hR i)).trans_lt hi

end CurvedMetric

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- `Vol(Σ, g̃_τ) → Vol(Σ, g)` when `g̃_τ → g` uniformly (l.728). -/
theorem tendsto_vol_of_uniformlyClose {g : FrameMetric X N} [IsFiniteMeasure (M.vol g)]
    {ι : Type*} {l : Filter ι} (gs : ι → FrameMetric X N) (η : ι → ℝ) (hη : ∀ i, 0 ≤ η i)
    (hηt : Tendsto η l (𝓝 0)) (h : ∀ i, UniformlyClose (η i) g (gs i)) :
    Tendsto (fun i => (M.vol (gs i) Set.univ).toReal) l (𝓝 (M.vol g Set.univ).toReal) := by
  set V := (M.vol g Set.univ).toReal with hVdef
  have hsmall : ∀ᶠ i in l, η i < 1 := hηt.eventually (gt_mem_nhds zero_lt_one)
  have hεt : Tendsto (fun i => η i / (1 - η i)) l (𝓝 0) := by
    have := hηt.div (tendsto_const_nhds.sub hηt) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [sub_zero, div_one] at this
    exact this
  have hk : Tendsto (fun i => (1 + η i / (1 - η i)) ^ ((N : ℝ) / 2)) l (𝓝 1) := by
    have := (hεt.const_add 1).rpow_const (p := (N : ℝ) / 2) (Or.inl (by norm_num))
    simpa using this
  have hkpos : ∀ i, η i < 1 → 0 < (1 + η i / (1 - η i)) ^ ((N : ℝ) / 2) := fun i hi =>
    Real.rpow_pos_of_pos (by have := div_nonneg (hη i) (by linarith : (0 : ℝ) ≤ 1 - η i); linarith) _
  have hbounds : ∀ i, η i < 1 →
      (M.vol (gs i) Set.univ).toReal ≤ (1 + η i / (1 - η i)) ^ ((N : ℝ) / 2) * V ∧
        V ≤ (1 + η i / (1 - η i)) ^ ((N : ℝ) / 2) * (M.vol (gs i) Set.univ).toReal := by
    intro i hi
    have hε0 : 0 ≤ η i / (1 - η i) := div_nonneg (hη i) (by linarith)
    have hc := comparable_of_uniformlyClose (hη i) hi (h i)
    set k := (1 + η i / (1 - η i)) ^ ((N : ℝ) / 2) with hkdef
    have hk0 : 0 ≤ k := (hkpos i hi).le
    have h1 : M.vol (gs i) Set.univ ≤ ENNReal.ofReal k * M.vol g Set.univ := by
      have := Measure.le_iff'.mp (vol_le (M := M) hε0 hc) Set.univ
      simpa using this
    have h2 : M.vol g Set.univ ≤ ENNReal.ofReal k * M.vol (gs i) Set.univ := by
      have := Measure.le_iff'.mp (vol_le (M := M) hε0 (hc.symm hε0)) Set.univ
      simpa using this
    have hfin : ENNReal.ofReal k * M.vol g Set.univ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have hfin' : M.vol (gs i) Set.univ ≠ ∞ := ne_top_of_le_ne_top hfin h1
    have hfin'' : ENNReal.ofReal k * M.vol (gs i) Set.univ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin'
    constructor
    · have := ENNReal.toReal_mono hfin h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk0] at this
    · have := ENNReal.toReal_mono hfin'' h2
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk0] at this
  have hlo : Tendsto (fun i => V / (1 + η i / (1 - η i)) ^ ((N : ℝ) / 2)) l (𝓝 V) := by
    have := (tendsto_const_nhds (x := V)).div hk one_ne_zero
    rw [div_one] at this
    exact this
  have hup : Tendsto (fun i => (1 + η i / (1 - η i)) ^ ((N : ℝ) / 2) * V) l (𝓝 V) := by
    simpa using hk.mul_const V
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [hsmall] with i hi
    rw [div_le_iff₀ (hkpos i hi), mul_comm]
    exact (hbounds i hi).2
  · filter_upwards [hsmall] with i hi
    exact (hbounds i hi).1

/-- The `τ → 0` limit of l.728: if `g̃_τ → g` and `R_{g̃_τ} → R_g` uniformly, and
`m_τ Vol(Σ, g̃_τ)^{2/N} ≤ -inf F_{g̃_τ}` for `τ` near `0`, then
`m Vol(Σ, g)^{2/N} ≤ -inf F_g`, with `m = min(0, min_Σ R_g)`. -/
theorem kobM_mul_le_neg_infF (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η δ : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hδt : Tendsto δ l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ δ i)
    (hτ : ∀ᶠ i in l, (gs i).kobM * (M.vol (gs i).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      -M.infF (gs i).toFrameMetric (fun _ => cN N)) :
    g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      -M.infF g.toFrameMetric (fun _ => cN N) := by
  have hβ : ∀ j : Fin n, 0 ≤ (fun _ => cN N) j := fun _ => (cN_pos (by omega)).le
  have hF := tendsto_infF_of_uniformlyClose (M := M) hN hβ (fun i => (gs i).toFrameMetric) η hη
    hηt hclose
  have hV := M.tendsto_vol_of_uniformlyClose (fun i => (gs i).toFrameMetric) η hη hηt hclose
  have hm := g.tendsto_kobM gs δ hδt hR
  have hL := hm.mul (hV.rpow_const (p := 2 / (N : ℝ)) (Or.inr (by positivity)))
  exact le_of_tendsto_of_tendsto hL hF.neg hτ

/-- thm:upper-bound's conclusion from the `τ → 0` limit (l.724, l.728): for `R_g ≡ c ≤ 0` on a
minimal boundary, `Y_[g](Σ) = R_g Vol(Σ, g)^{2/N} ≤ -inf F_g` (eq:upper-bound). -/
theorem upper_bound_of_limit (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hc : c ≤ 0) (hRc : ∀ x, g.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η δ : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hδt : Tendsto δ l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ δ i)
    (hτ : ∀ᶠ i in l, (gs i).kobM * (M.vol (gs i).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      -M.infF (gs i).toFrameMetric (fun _ => cN N)) :
    M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) := by
  have hN' := three_le_cast hN
  have hlim := M.kobM_mul_le_neg_infF hN g gs η δ hη hηt hclose hδt hR hτ
  have hY := M.Y_eq_const_mul g hN hD hH hc (ae_of_all _ hRc)
  have hk : g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) =
      c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) := by
    rcases isEmpty_or_nonempty X with hX | hX
    · have h0 : M.vol g.toFrameMetric Set.univ = 0 := by
        rw [Set.univ_eq_empty_iff.mpr hX, measure_empty]
      rw [h0, ENNReal.toReal_zero, Real.zero_rpow (by positivity), mul_zero, mul_zero]
    · have : g.kobM = c := by
        unfold CurvedMetric.kobM
        simp only [hRc, ciInf_const]
        exact min_eq_right hc
      rw [this]
  exact ⟨hY, by rw [hY, ← hk]; exact hlim⟩

/-- The same, without `R_g ≤ 0` but with `inf F_g > 0` (lem:positivity, carried): the limit
itself forces `R_g < 0`, so prop:nonpositive is not needed at l.724. -/
theorem upper_bound_of_limit_of_pos (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    (hpos : 0 < M.infF g.toFrameMetric (fun _ => cN N))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η δ : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hδt : Tendsto δ l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ δ i)
    (hτ : ∀ᶠ i in l, (gs i).kobM * (M.vol (gs i).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      -M.infF (gs i).toFrameMetric (fun _ => cN N)) :
    c < 0 ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) := by
  have hN' := three_le_cast hN
  have hlim := M.kobM_mul_le_neg_infF hN g gs η δ hη hηt hclose hδt hR hτ
  rcases isEmpty_or_nonempty X with hX | hX
  · exfalso
    have h0 : M.vol g.toFrameMetric Set.univ = 0 := by
      rw [Set.univ_eq_empty_iff.mpr hX, measure_empty]
    rw [h0, ENNReal.toReal_zero, Real.zero_rpow (by positivity), mul_zero] at hlim
    linarith
  · have hk : g.kobM = min 0 c := by
      unfold CurvedMetric.kobM
      simp only [hRc, ciInf_const]
    have hc : c < 0 := by
      by_contra hc'
      rw [hk, min_eq_left (not_lt.mp hc'), zero_mul] at hlim
      linarith
    have hY := M.Y_eq_const_mul g hN hD hH hc.le (ae_of_all _ hRc)
    rw [hk, min_eq_right hc.le] at hlim
    exact ⟨hc, hY, by rw [hY]; exact hlim⟩

end MeasuredModel

/-! ## Assembly of thm:upper-bound's proof (l.723–728) -/

/-- The data and the carried inputs of lem:gluing-estimate for a metric `g` on `Σ` and constants
`β` (l.650–666), bundled: a filling `F`, a glued metric `h̄` with `h̄|_Σ = u^{4/(N-2)} g`,
`y = Y_[ḡ](Σ̄) ≤ 0` (`y_nonpos`), and the inputs `yamabe` (thm:yamabe (b), l.658), `law`
(eq:conformal-energy-bdry, l.326–328), `bdryYamabe` (l.663–666), `flip` (l.663), `bmatch`
(l.650, l.663). -/
structure GluingInput {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
    (M : MeasuredModel X D N n) (Y E : Type*) [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E]
    (g : CurvedMetric X N) (β : Fin n → ℝ) where
  /-- the pieces `D_j` -/
  F : Filling X Y E N n
  /-- the Yamabe metric `h̄` of `[ḡ]`, through its restrictions -/
  hb : GluedMetric X Y N n
  /-- `u = ψ|_Σ` -/
  u : D
  /-- `Y_[ḡ](Σ̄)` -/
  y : ℝ
  /-- `R_h̄` -/
  c : ℝ
  conf : M.IsConformal g.toFrameMetric hb.body.toFrameMetric u
  val_meas : AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric)
  tr_meas : ∀ j, AEStronglyMeasurable (M.tr u) (M.bvol g.toFrameMetric j)
  tr_eq : ∀ j, M.tr u =ᵐ[M.bvol g.toFrameMetric j] M.val u
  vol_finite : IsFiniteMeasure (M.vol hb.body.toFrameMetric)
  bvol_finite : ∀ j, IsFiniteMeasure (M.bvol hb.body.toFrameMetric j)
  y_nonpos : y ≤ 0
  yamabe : F.IsYamabeMetric M hb y c
  law : M.ConformalLaw g u hb.body
  bdryYamabe : F.BoundaryYamabe hb β
  flip : F.MeanCurvatureFlip M hb
  bmatch : F.BoundaryMatch M hb

namespace GluingInput

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ} {M : MeasuredModel X D N n}

/-- l.724–726 from bundled inputs: `m Vol(Σ, g)^{2/N} ≤ -inf F_g`. -/
theorem le_neg_infF (hN : 3 ≤ N) {g : CurvedMetric X N} [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hV : M.vol g.toFrameMetric ≠ 0) (hB : ∀ j, M.bvol g.toFrameMetric j ≠ 0)
    (hρ : M.DensityMeasurable g.toFrameMetric) (hH : M.MinimalBoundary g) {m : ℝ} (hm : m ≤ 0)
    (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x) (S : GluingInput M Y E g (fun _ => cN N)) :
    m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      -M.infF g.toFrameMetric (fun _ => cN N) :=
  haveI := S.vol_finite
  haveI := S.bvol_finite
  Filling.le_neg_infF_of_gluing hN S.F M g hV hB hρ hH hm hmR S.hb S.u S.conf S.val_meas S.tr_meas
    S.tr_eq S.y_nonpos S.yamabe S.law S.bdryYamabe S.flip S.bmatch

end GluingInput

namespace MeasuredModel

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- Assembly of thm:upper-bound's proof (l.723–728) over the model. `g` has constant scalar
curvature `c ≤ 0` (l.724) and minimal boundary; `g̃_τ = gs τ` are metrics on `Σ` with minimal
boundary, `g̃_τ → g` and `R_{g̃_τ} → R_g` uniformly (lem:gluing, carried as the family), and each
`g̃_τ` comes with the inputs of lem:gluing-estimate for `β_j = c_N` (fact (iv)) and
`Y_[ḡ_τ](Σ̄) ≤ 0` (from `σ(Σ̄) ≤ 0`). Then `Y_[g](Σ) = R_g Vol(Σ, g)^{2/N} ≤ -inf F_g`
(eq:upper-bound). -/
theorem upper_bound_of_gluings (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hc : c ≤ 0) (hRc : ∀ x, g.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η δ : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hδt : Tendsto δ l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ δ i)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gs i).toFrameMetric))
    (hV : ∀ i, M.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, M.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, M.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput M Y E (gs i) (fun _ => cN N)) :
    M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) := by
  refine M.upper_bound_of_limit hN g hD hH hc hRc gs η δ hη hηt hclose hδt hR
    (Eventually.of_forall fun i => ?_)
  haveI := hfin i
  exact (S i).le_neg_infF hN (hV i) (hB i) (hρ i) (hHτ i) (gs i).kobM_nonpos
    (ae_of_all _ (gs i).kobM_le)

/-- The assembly without `R_g ≤ 0` (which l.724 takes from prop:nonpositive, whose hypothesis
"`Σ̄` enlargeable" thm:upper-bound does not have), with `inf F_g > 0` (lem:positivity, carried)
instead: then `R_g < 0` and `Y_[g](Σ) = R_g Vol(Σ, g)^{2/N} ≤ -inf F_g`. -/
theorem upper_bound_of_gluings_of_pos (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    (hpos : 0 < M.infF g.toFrameMetric (fun _ => cN N))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η δ : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hδt : Tendsto δ l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ δ i)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gs i).toFrameMetric))
    (hV : ∀ i, M.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, M.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, M.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput M Y E (gs i) (fun _ => cN N)) :
    c < 0 ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) := by
  refine M.upper_bound_of_limit_of_pos hN g hD hH hRc hpos gs η δ hη hηt hclose hδt hR
    (Eventually.of_forall fun i => ?_)
  haveI := hfin i
  exact (S i).le_neg_infF hN (hV i) (hB i) (hρ i) (hHτ i) (gs i).kobM_nonpos
    (ae_of_all _ (gs i).kobM_le)

end MeasuredModel

/-! ## A witness: the hypotheses of the gluing estimate are jointly satisfiable -/

section Toy

/-- The toy filling: one piece `D_0`, a copy of the two-point toy model, glued by the identity. -/
def toyFilling : Filling Bool Bool (Bool → ℝ) 3 1 where
  piece := fun _ => toyModel
  glue := fun _ => id
  glue_measurable := fun _ => measurable_id

/-- The toy glued metric: `toyCurved` (`G = 1`, `R ≡ -1`, `H ≡ 0`) on `Σ` and on `D_0`. -/
def toyGlued : GluedMetric Bool Bool 3 1 where
  body := toyCurved
  cap := fun _ => toyCurved

lemma toy_volBar_pos : 0 < toyFilling.volBar toyModel toyGlued := by
  have hV : (toyModel.vol toyCurved.toFrameMetric Set.univ).toReal = 2 := by
    rw [toyCurved_toFrameMetric, toy_vol, Measure.count_apply_finite _ Set.finite_univ]
    simp
  unfold Filling.volBar
  simp only [toyGlued, toyFilling, Fin.sum_univ_one]
  rw [hV]
  positivity

/-- Every hypothesis of `Filling.gluing_estimate` holds on the toy model, with `u = 1`, `m = -1`,
`R_h̄ = c = -1`, `Y_[ḡ](Σ̄) = y = -Vol(Σ̄, h̄)^{2/3}` and `β_0 = EHB(D_0, h̄)`. -/
theorem toy_gluing_estimate :
    (-1) * (toyModel.vol toyCurved.toFrameMetric Set.univ).toReal ^ (2 / ((3 : ℕ) : ℝ)) ≤
        -toyModel.F toyCurved.toFrameMetric
            (fun j => (toyFilling.piece j).EHB (toyGlued.cap j)) toyModel.one +
          -(toyFilling.volBar toyModel toyGlued) ^ (2 / ((3 : ℕ) : ℝ)) *
            (toyFilling.volBar toyModel toyGlued /
              (toyModel.vol toyGlued.body.toFrameMetric Set.univ).toReal) ^
              ((((3 : ℕ) : ℝ) - 2) / ((3 : ℕ) : ℝ)) ∧
      -(toyFilling.volBar toyModel toyGlued) ^ (2 / ((3 : ℕ) : ℝ)) *
          (toyFilling.volBar toyModel toyGlued /
            (toyModel.vol toyGlued.body.toFrameMetric Set.univ).toReal) ^
            ((((3 : ℕ) : ℝ) - 2) / ((3 : ℕ) : ℝ)) ≤ 0 := by
  haveI := toy_isFiniteMeasure
  haveI : ∀ j, IsFiniteMeasure (toyModel.bvol toyCurved.toFrameMetric j) := fun j => by
    rw [toyCurved_toFrameMetric, toy_bvol]; infer_instance
  haveI : IsFiniteMeasure (toyModel.vol toyGlued.body.toFrameMetric) := toy_isFiniteMeasure
  haveI : ∀ j, IsFiniteMeasure (toyModel.bvol toyGlued.body.toFrameMetric j) := fun j => by
    rw [show toyGlued.body = toyCurved from rfl, toyCurved_toFrameMetric, toy_bvol]; infer_instance
  have hb := toy_volBar_pos
  have hcount : Measure.count {true} ≠ 0 := by simp
  have hV : toyModel.vol toyCurved.toFrameMetric ≠ 0 := by
    rw [toyCurved_toFrameMetric, toy_vol]; intro h; apply hcount; rw [h]; rfl
  have hB : ∀ j, toyModel.bvol toyCurved.toFrameMetric j ≠ 0 := fun j => by
    rw [toyCurved_toFrameMetric, toy_bvol]; exact Measure.dirac_ne_zero
  have hρ : toyModel.DensityMeasurable toyCurved.toFrameMetric :=
    ⟨Measurable.of_discrete.aemeasurable, fun _ => Measurable.of_discrete.aemeasurable⟩
  have hconf : toyModel.IsConformal toyCurved.toFrameMetric toyGlued.body.toFrameMetric
      toyModel.one :=
    ⟨fun x => by rw [toyModel.val_one]; exact one_pos,
      fun x => by rw [toyModel.val_one]; simp [toyGlued]⟩
  have hyam : toyFilling.IsYamabeMetric toyModel toyGlued
      (-(toyFilling.volBar toyModel toyGlued) ^ (2 / ((3 : ℕ) : ℝ))) (-1) := by
    refine ⟨ae_of_all _ fun _ => rfl, fun _ => ae_of_all _ fun _ => rfl, ?_⟩
    rw [neg_mul, ← Real.rpow_add hb]
    simp
  have hlaw : toyModel.ConformalLaw toyCurved toyModel.one toyGlued.body := by
    have hQ : 0 < normSq (toyModel.vol toyCurved.toFrameMetric) (pStar 3) (toyModel.val toyModel.one) := by
      rw [toyModel.val_one, normSq_one _ (pStar_pos (le_refl 3))]
      refine Real.rpow_pos_of_pos (ENNReal.toReal_pos ?_ (measure_ne_top _ _)) _
      exact Measure.measure_univ_ne_zero.mpr hV
    unfold MeasuredModel.ConformalLaw
    rw [show toyGlued.body = toyCurved from rfl, toyModel.EH_eq_confEnergy_one toyCurved (le_refl 3)]
    unfold MeasuredModel.confEnergy
    field_simp
  have hflip : toyFilling.MeanCurvatureFlip toyModel toyGlued :=
    fun _ => ae_of_all _ fun _ => by simp [toyGlued, toyCurved, toyFilling]
  have hmatch : toyFilling.BoundaryMatch toyModel toyGlued := fun j => by
    rw [Subsingleton.elim j 0]
    simp [toyFilling, toyGlued, Measure.map_id]
  exact Filling.gluing_estimate (le_refl 3) toyFilling toyModel toyCurved hV hB hρ toy_minimal
    (m := -1) (by norm_num) (ae_of_all _ fun _ => le_refl _) toyGlued toyModel.one hconf
    Measurable.of_discrete.aestronglyMeasurable
    (fun _ => Measurable.of_discrete.aestronglyMeasurable)
    (fun _ => by rw [toyModel.tr_one, toyModel.val_one])
    (neg_nonpos.mpr (Real.rpow_nonneg hb.le _)) hyam hlaw _ (fun _ => le_refl _) hflip hmatch

end Toy

end Yamabe
