import Yamabe.LowerBound

/-!
# Perforated cor:yamabe over the measured model: on a punctured torus, `|R_g| Vol^{2/N} = δ ≥ θ/(1+θ) · 2(N−1)M/Vol^{(N−2)/N} · (1 + O(F_g(1)))`, restated over yamabe's thm:lower-bound

Label (the companion BrunswicPerforated, `papers/perforated`; lines of
`papers/perforated/legacy/labeled/perforated.tex`). NOT marked: partial (see SCOPE).

* `cor:yamabe` — `perforated.tex:929` (statement l.929–939, no proof; the lead-in l.913–927,
  with eq:yamabe-upper at l.921). Its content is yamabe's thm:lower-bound
  (`Yamabegap.tex:512`, strict `Yamabe.LowerBound`), restated in the companion's notation: the
  gap `δ = Yb(Σ) − Y_[g](Σ)` of l.924, `λ_∂`, and the factor `1 + O(F_g(1))`.

> Let $\overline\Sigma$ be a closed $N$-manifold, $\Sigma=\overline\Sigma\setminus
> \bigsqcup_j\operatorname{int}D_j$ the complement of $n$ disjointly embedded balls,
> and $\Yb(\Sigma)$ the relative Yamabe invariant of Akutagawa and Botvinnik
> \cite{AkutagawaBotvinnik2002}, the supremum over conformal classes of the
> boundary Yamabe energy. If $\sigma(\overline\Sigma)\le0$, if $g$ has constant
> scalar curvature and minimal boundary, and if each $(B_j,g|_{B_j})$ is
> conformally round (automatic for $N=3$), then a gluing estimate gives
> $\Y_{[g]}(\Sigma)\;\le\;-\lambda_\partial(\Sigma,g),$
> so that the \emph{gap} $\delta:=\Yb(\Sigma)-\Y_{[g]}(\Sigma)$ obeys
> $\delta\ge\lambda_\partial$ whenever $\Yb(\Sigma)\ge0$. For a punctured flat
> torus $\Yb(\Sigma)=0$, and Theorem~\ref{thm:main} converts \eqref{eq:yamabe-upper}
> into a quantitative statement: (l.913–927)

> Under the above hypotheses on a punctured torus, with $M$ the total boundary
> mean curvature relative to the Euclidean reference embedding,
> $|\mathrm{R}_g|\Vol(\Sigma,g)^{2/N}\;=\;\delta\;\ge\;
>   \frac{\theta}{1+\theta}\,\frac{2(N-1)M}{\Vol(\Sigma,g)^{(N-2)/N}}\,
>   \bigl(1+O(\Fq_g(1))\bigr),$
> and $\theta\to1$ for Schwarzschild collars, so the constant is $1/2$. (l.931–938)

## The model

`Σ` is a `MeasuredModel` with a `CurvedMetric` `g` (DEC-186), as in `Yamabe.LowerBound`:
`λ_∂ = infF (fun _ => c_N)`, `F_g(1) = Fq one`, `θ = theta` (the companion's def:capstar, with its
own weights `w_j`), `Y_[g](Σ) = Y`. The hypotheses are thm:lower-bound's, one to one:
thm:upper-bound's as the strict `upper_bound_of_gluings_of_pos` reads them, thm:main's as
`thm_main` (eq:star for `u ≥ 0`, `AbsLatticeApprox`) or `thm_main_signed` (eq:star for every `u`)
read them. New here: `gapYb σb g = σb − Y_[g](Σ)` (the companion's `δ` at a value `σb` of
`Yb(Σ)`) and `corRem` (the `O(F_g(1))`).

## What is proved (no `sorry` in this file)

* `corRem` with `eq_main_cor_identity` (`F/Λ_max = θ/(1+θ) F (1 + corRem)`), `kappa_eq_corRem`
  (`κ = θ/(1+θ)(1 + corRem)`), `corRem_isBigO` (`O(F)` at fixed `θ`, `Ã`), `corRem_le_uniform`
  (`|corRem| ≤ (3/7)|ÃF/a_N|` for `|ÃF/a_N| ≤ 1/4`, every `θ > 0`).
* `corConst_tendsto_half`: « so the constant is 1/2 » as an implication: along any family with
  `θ → 1` and `Ã F_g(1) → 0`, `θ/(1+θ)(1 + corRem) → 1/2`.
* `cor_yamabe_of_eq_main`, the assembly from eq:main through the strict
  `lower_bound_of_eq_main` (thm:lower-bound) and `upper_bound_of_gluings_of_pos`
  (eq:yamabe-upper). Anchors, with its conclusions: `cor_yamabe` (thm:main as printed),
  `cor_yamabe_signed`, `cor_yamabe_three` (`N = 3`, `Ã = star3AtilCorr V λ C`),
  `cor_yamabe_starN` (`Ã = starNAtil`), and on a manifold reading (`Mfd.Reads`, OQ-93)
  `Mfd.Reads.cor_yamabe_three`, `Mfd.Reads.cor_yamabe_starN`: thm:lower-bound's six forms.
* Witness: `toy_cor_yamabe` (every hypothesis of `cor_yamabe` holds on the two-point toy model,
  `R_g ≡ −8`, and the bound is positive).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N ≥ 3`; `Σ` compact, `Σ ≠ ∅`, `n ≥ 1` balls (l.913–914) | ✓ carried: `hN`; finite `vol`, `bvol`; `vol ≠ 0`; `∃ j, bvol j ≠ 0` (DEC-186) |
| `σ(Σ̄) ≤ 0`, constant scalar curvature, minimal boundary, `B_j` conformally round (l.917–919) | ⚠ read as in `upper_bound_of_gluings_of_pos`: `R_g x = c` for every `x`, `MinimalBoundary`, the lem:gluing family `g̃_τ` with a `GluingInput` per `τ` (`β_j = c_N`, `Y_[ḡ_τ](Σ̄) ≤ 0`) |
| « a gluing estimate gives » eq:yamabe-upper (l.919–922) | ✓ a conclusion, from the strict `upper_bound_of_gluings_of_pos` on the inputs above; its `λ_∂ > 0` comes from thm:main (kb 0080) |
| thm:main's hypothesis eq:star with `Ã` (l.926) | ⚠ every real `Ã` with eq:star; instances `star3AtilCorr` (OQ-109), `starNAtil` (OQ-118); discharged on a manifold reading at `λ₁`, `C_SP` |
| connected, the trace theorem, `cap* < ∞` (thm:main) | model: ⚠ carried `MeanPoincare`, `TraceBound`, `InteriorBump`; reading: the first two discharged, `NonConst` carried |
| `u ↦ |u|` (l.458–460) | ⚠ carried: `AbsLatticeApprox` (`cor_yamabe` only) |
| `Yb(Σ)`, « the supremum over conformal classes of the boundary Yamabe energy » (l.915–917) | ⚠ read: a real `σb`, the value of yamabe's `σ^∂(Σ)` (OQ-121 (c)); not definable on the model (kb 0083) |
| « on a punctured torus »: `Yb(Σ) = 0` (l.925–926, asserted) | ⚠ carried: `hYb : σb = 0`; the sign-free `δ = Yb + |R_g| Vol^{2/N} ≥ Yb + λ_∂` is a conclusion for every value; finding |
| `δ := Yb(Σ) − Y_[g](Σ)` (l.924) | ✓ `gapYb`; equal to yamabe's `gapBdry` (`EH = Y` proved) |
| `M` « relative to the Euclidean reference embedding » (l.931–932) | ⚠ read (OQ-44, DEC-186): `roundMass N r = ω_{N−1} Σ r_j^{N−2}` for round `B_j` of radii `r_j`; a conditional conjunct; finding |
| `1 + O(F_g(1))` (l.936) | ⚠ read (OQ-111 (b)): `1 + corRem N θ Ã F`, explicit, `O(F)` at fixed `θ`, `Ã`, and `≤ (3/7)|ÃF/a_N|` uniformly in `θ` |
| `|R_g|` (l.934) | ✓ `|c|`, with `c < 0` derived |
| « `θ → 1` for Schwarzschild collars » (l.938) | ✗ not formalized (T-perf-dilute-limit, needs-ruling); « so the constant is 1/2 » proved as an implication (`corConst_tendsto_half`) |

## SCOPE (disclosed)

* **Why partial.** (1) `Yb(Σ) = 0` for a punctured flat torus is asserted at l.925–926 and proved
  in neither paper (yamabe's eq:sigma-torus, `Yamabegap.tex` l.365–369, argues it for `T³`
  only): carried as `hYb : σb = 0`, used only for `|R_g| Vol^{2/N} = δ` and the bounds on `δ`;
  every other conclusion holds for every value of `Yb(Σ)`, and the bound on `|R_g| Vol^{2/N}`
  needs none. (2) The model carries `MeanPoincare`, `TraceBound`, `InteriorBump` and eq:star;
  the manifold forms discharge all but `InteriorBump` and `NonConst`, under the readings of
  OQ-93 (open). (3) thm:upper-bound's inputs enter through `GluingInput`, as in the strict
  library. (4) The `M` form is conditional on round `B_j` (finding). (5) « `θ → 1` for
  Schwarzschild collars » waits on T-perf-dilute-limit. (6) The readings of OQ-109, OQ-111,
  OQ-118 and OQ-121 (c) are open.
* **`Yb(Σ)` and `δ`.** `Yb(Σ)` is a supremum over conformal classes; on the model `R`, `H` are
  free data (kb 0018), so it is a real parameter `σb` (kb 0083). The companion's `δ` uses
  `Y_[g](Σ)`, yamabe's eq:gap-bdry uses `EH(Σ, g)`; they agree here (`gapYb = gapBdry`).
* **`M`.** The companion does not define `M` (its `M` is a matrix at l.529–543); the phrase of
  l.931–932 is yamabe's eq:mass-def (`Yamabegap.tex` l.383–387) over def:reference (l.378–381),
  which is `N = 3` with `B_j` of positive Gauss curvature. On the model only areas are seen, so
  `M = roundMass N r` for `B_j` of the areas of round spheres of radii `r_j` (yamabe's Setting,
  l.467). For a conformally round, non-round `B_j` at `N = 3`, Minkowski's inequality gives
  `F_g(1) < 2(N−1)M/Vol^{(N−2)/N}`, so the printed `M` form does not follow from the proof
  (argued, not formalized).
* **`O(F_g(1))`.** `κ = θ/(1+θ)(1 − ÃθF/(a_N(1+θ)²) + mainRem)` (eq:kappa) is
  `θ/(1+θ)(1 + corRem)`; for one `(Σ, g)` an existential `O(·)` is vacuous, so it is this fixed
  function of `F` (OQ-111 (b), extended from `O(F²)` to `O(F)`).
* **Not stated.** « `θ → 1` » itself, and which metric's `θ` is meant: prop:theta-examples (ii)
  (l.232–233) is the dilute limit, `N = 3`, of the scalar-flat collar `(1 + m/2s)⁴ δ`, while the
  `g` of cor:yamabe has constant negative scalar curvature, and `θ` is not conformally invariant.
* **Junk values.** As in `Yamabe.LowerBound`: `θ = 0` if `cap* = ∞`, excluded by `InteriorBump`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

/-! ## 1. The factor `1 + O(F_g(1))` -/

section Remainder

/-- The `O(F_g(1))` of cor:yamabe (l.936): eq:main-asymp's first-order loss
`−Ãθ F/(a_N(1+θ)²)` plus its explicit remainder `mainRem` (OQ-111 (b)), so that
`κ = θ/(1+θ) (1 + corRem)`. A function of `(θ, Ã, F)` only. -/
def corRem (N : ℕ) (θ A F : ℝ) : ℝ :=
  -(A * θ * F / (aN N * (1 + θ) ^ 2)) + mainRem N θ A F

variable {N : ℕ}

/-- eq:main in cor:yamabe's form: `F/Λ_max = θ/(1+θ) · F · (1 + corRem)`. -/
lemma eq_main_cor_identity {θ : ℝ} (hθ : 0 < θ) (A F : ℝ) :
    F / lamMax (1 / θ) 1 (A * F / aN N) = θ / (1 + θ) * F * (1 + corRem N θ A F) := by
  rw [eq_main_asymp_identity hθ A F]
  unfold corRem
  ring

/-- The remainder is `O(F)` uniformly in `θ`: `|corRem| ≤ (3/7)|ÃF/a_N|` whenever
`|ÃF/a_N| ≤ 1/4`, for every `θ > 0`. -/
theorem corRem_le_uniform (hN : 3 ≤ N) {θ : ℝ} (hθ : 0 < θ) {A F : ℝ}
    (hF : |A * F / aN N| ≤ 1 / 4) :
    |corRem N θ A F| ≤ 3 / 7 * |A * F / aN N| := by
  have ha := (aN_pos hN).ne'
  have h1θ : (1 + θ) ^ 2 ≠ 0 := by positivity
  have hm := mainRem_le_uniform hN hθ hF
  have hx : A * θ * F / (aN N * (1 + θ) ^ 2) = θ / (1 + θ) ^ 2 * (A * F / aN N) := by
    field_simp
  have hθ4 : θ / (1 + θ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (θ - 1)]
  have h2 : |A * θ * F / (aN N * (1 + θ) ^ 2)| ≤ 1 / 4 * |A * F / aN N| := by
    rw [hx, abs_mul, abs_of_nonneg (by positivity : 0 ≤ θ / (1 + θ) ^ 2)]
    exact mul_le_mul_of_nonneg_right hθ4 (abs_nonneg _)
  have h3 : (A * F / aN N) ^ 2 ≤ 1 / 4 * |A * F / aN N| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (A * F / aN N)]
  calc |corRem N θ A F|
      ≤ |A * θ * F / (aN N * (1 + θ) ^ 2)| + |mainRem N θ A F| := by
        unfold corRem
        exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ 1 / 4 * |A * F / aN N| + 5 / 7 * (1 / 4 * |A * F / aN N|) := by
        gcongr
        exact hm.trans (by gcongr)
    _ = 3 / 7 * |A * F / aN N| := by ring

/-- The `O(F_g(1))` of cor:yamabe, read at fixed `θ` and `Ã`: `corRem = O(F)` as `F → 0`. -/
theorem corRem_isBigO (hN : 3 ≤ N) {θ : ℝ} (hθ : 0 < θ) (A : ℝ) :
    (fun F => corRem N θ A F) =O[𝓝 0] (fun F => F) := by
  have ha := (aN_pos hN)
  refine IsBigO.of_bound (3 / 7 * |A / aN N|) ?_
  have hc : Tendsto (fun F : ℝ => |A * F / aN N|) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun F : ℝ => |A * F / aN N|) := by fun_prop
    simpa using this.tendsto 0
  filter_upwards [hc.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with F hF
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  refine (corRem_le_uniform hN hθ hF).trans (le_of_eq ?_)
  rw [mul_assoc, ← abs_mul]
  congr 2
  field_simp

/-- « so the constant is 1/2 » (l.938), as an implication: along any family with `θ → 1` and
`Ã F_g(1) → 0`, `θ/(1+θ) · (1 + corRem) → 1/2`. That `θ → 1` for Schwarzschild collars is not
proved here (T-perf-dilute-limit). -/
theorem corConst_tendsto_half (hN : 3 ≤ N) {ι : Type*} {l : Filter ι} {θ A F : ι → ℝ}
    (hθ : Tendsto θ l (𝓝 1)) (hAF : Tendsto (fun i => A i * F i) l (𝓝 0)) :
    Tendsto (fun i => θ i / (1 + θ i) * (1 + corRem N (θ i) (A i) (F i))) l (𝓝 (1 / 2)) := by
  have ha := aN_pos hN
  have hx : Tendsto (fun i => |A i * F i / aN N|) l (𝓝 0) := by
    have := (hAF.div_const (aN N)).abs
    simpa using this
  have hrem : Tendsto (fun i => corRem N (θ i) (A i) (F i)) l (𝓝 0) := by
    have hb : Tendsto (fun i => 3 / 7 * |A i * F i / aN N|) l (𝓝 0) := by
      simpa using hx.const_mul (3 / 7 : ℝ)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hθ.eventually_const_lt (by norm_num : (0 : ℝ) < 1),
      hx.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with i hi hF
    rw [Real.norm_eq_abs]
    exact corRem_le_uniform hN hi hF
  have hq : Tendsto (fun i => θ i / (1 + θ i)) l (𝓝 (1 / (1 + 1))) :=
    hθ.div (tendsto_const_nhds.add hθ) (by norm_num)
  have h1 : Tendsto (fun i => 1 + corRem N (θ i) (A i) (F i)) l (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hrem
  have := hq.mul h1
  convert this using 2
  norm_num

end Remainder

namespace MeasuredModel

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-! ## 2. The companion's gap -/

/-- The companion's gap (perforated l.924) at a value `σb` of the relative Yamabe invariant
`Yb(Σ)` (l.915–917): `δ = Yb(Σ) − Y_[g](Σ)`. -/
def gapYb (σb : ℝ) (g : CurvedMetric X N) : ℝ := σb - M.Y g

/-- `κ = θ/(1+θ) (1 + corRem)` (eq:kappa in cor:yamabe's form). -/
lemma kappa_eq_corRem (g : FrameMetric X N) (A : ℝ) :
    M.kappa g A =
      M.theta g / (1 + M.theta g) * (1 + corRem N (M.theta g) A (M.Fq g M.one)) := by
  unfold kappa corRem
  ring

/-! ## 3. cor:yamabe over the model -/

/-- The assembly of cor:yamabe from eq:main (`hmain`) and `θ > 0`, through the strict
`lower_bound_of_eq_main` (thm:lower-bound) and `upper_bound_of_gluings_of_pos`
(eq:yamabe-upper). Conclusions: `R_g ≡ c < 0`, `Y_[g](Σ) = c Vol^{2/N}`; eq:yamabe-upper
`Y_[g](Σ) ≤ −λ_∂`; for every value `σb` of `Yb(Σ)`, `δ` is yamabe's gap,
`δ = σb + |R_g| Vol^{2/N}` and `δ ≥ σb + λ_∂` (l.924–925); at `σb = 0` (the punctured torus,
l.925–926) `|R_g| Vol^{2/N} = δ`; `θ/(1+θ) F_g(1) (1 + corRem) > 0`, `≤ λ_∂` and `≤ δ`; for round
`B_j` of radii `r_j`, `F_g(1) = 2(N−1)M/Vol^{(N−2)/N}` and the printed
`δ ≥ θ/(1+θ) · 2(N−1)M/Vol^{(N−2)/N} · (1 + corRem)`; `corRem = O(F)` with the uniform bound. -/
theorem cor_yamabe_of_eq_main (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] [∀ j, IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (hV0 : M.vol g.toFrameMetric ≠ 0) (hB0 : ∃ j, M.bvol g.toFrameMetric j ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η ε : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hεt : Tendsto ε l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ ε i)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gs i).toFrameMetric))
    (hV : ∀ i, M.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, M.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, M.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput M Y E (gs i) (fun _ => cN N))
    (hθ : 0 < M.theta g.toFrameMetric) {A : ℝ}
    (hmain : M.Fq g.toFrameMetric M.one /
        lamMax (1 / M.theta g.toFrameMetric) 1 (A * M.Fq g.toFrameMetric M.one / aN N) ≤
      M.infF g.toFrameMetric (fun _ => cN N))
    {σb : ℝ} (hYb : σb = 0) :
    c < 0 ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) ∧
      (∀ s : ℝ, M.gapYb s g = M.gapBdry s g ∧
        M.gapYb s g = s + |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
        s + M.infF g.toFrameMetric (fun _ => cN N) ≤ M.gapYb s g) ∧
      |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) = M.gapYb σb g ∧
      0 < M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
        (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.infF g.toFrameMetric (fun _ => cN N) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.gapYb σb g ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) *
              (2 * ((N : ℝ) - 1) * roundMass N r /
                (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N)) *
              (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
            M.gapYb σb g) ∧
      (fun F => corRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |corRem N (M.theta g.toFrameMetric) A F| ≤ 3 / 7 * |A * F / aN N| := by
  subst hYb
  set V := (M.vol g.toFrameMetric Set.univ).toReal with hVdef
  set θ := M.theta g.toFrameMetric with hθdef
  set F := M.Fq g.toFrameMetric M.one with hFdef
  set lam := M.infF g.toFrameMetric (fun _ => cN N) with hlam
  have hF := M.Fq_one_pos g.toFrameMetric hN hV0 hB0
  have hα : 0 ≤ 1 / θ := (one_div_pos.mpr hθ).le
  have hΛ : 0 < lamMax (1 / θ) 1 (A * F / aN N) :=
    lt_of_lt_of_le one_pos (le_lamMax_right hα zero_le_one)
  have hpos : 0 < lam := lt_of_lt_of_le (div_pos hF hΛ) hmain
  obtain ⟨-, hYc, hub⟩ := M.upper_bound_of_gluings_of_pos hN g hD hH hRc hpos gs η ε hη hηt
    hclose hεt hR hfin hV hB hρ hHτ S
  obtain ⟨hc, hEH, hκ, -, -, -, hround, -, -⟩ := M.lower_bound_of_eq_main hN g hV0 hB0 hD hH hRc
    gs η ε hη hηt hclose hεt hR hfin hV hB hρ hHτ S hθ hmain (σb := 0) le_rfl
  have hid : F / lamMax (1 / θ) 1 (A * F / aN N) = θ / (1 + θ) * F * (1 + corRem N θ A F) :=
    eq_main_cor_identity hθ A F
  have hk : M.kappa g.toFrameMetric A * F = θ / (1 + θ) * F * (1 + corRem N θ A F) := by
    rw [M.kappa_eq_corRem]; ring
  have habs : |c| * V ^ (2 / (N : ℝ)) = -M.Y g := by
    rw [abs_of_neg hc, hYc]; ring
  have hgap : ∀ s : ℝ, M.gapYb s g = s + |c| * V ^ (2 / (N : ℝ)) := fun s => by
    rw [habs]; unfold gapYb; ring
  have hlow : θ / (1 + θ) * F * (1 + corRem N θ A F) ≤ lam := hid ▸ hmain
  have hδ : θ / (1 + θ) * F * (1 + corRem N θ A F) ≤ M.gapYb 0 g := by
    rw [hgap, zero_add, habs]; linarith
  refine ⟨hc, hYc, hub, fun s => ⟨by unfold gapYb gapBdry; rw [hEH], hgap s,
    by rw [hgap, habs]; linarith⟩, by rw [hgap, zero_add], hk ▸ hκ, hlow, hδ,
    fun r hr hround' => ?_, corRem_isBigO hN hθ A, fun F' hF' => corRem_le_uniform hN hθ hF'⟩
  have hF1 := (hround r hr hround').1
  refine ⟨hF1, ?_⟩
  rw [← hF1]
  exact hδ

/-- cor:yamabe (l.929–939) over the model, with thm:main as printed: eq:star for `u ≥ 0` with any
constant `Ã`, under the approximate lattice property of l.458–460, and `Yb(Σ) = 0` (the punctured
torus, l.925–926) carried as `hYb`. The conclusions of `cor_yamabe_of_eq_main`. The anchor of
thm:lower-bound in this form is `thm_lower_bound`, with the same hypotheses. -/
theorem cor_yamabe (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] [∀ j, IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (hV0 : M.vol g.toFrameMetric ≠ 0) (hB0 : ∃ j, M.bvol g.toFrameMetric j ≠ 0)
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η ε : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hεt : Tendsto ε l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ ε i)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gs i).toFrameMetric))
    (hV : ∀ i, M.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, M.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, M.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput M Y E (gs i) (fun _ => cN N))
    (hP : M.MeanPoincare g.toFrameMetric) (hT : M.TraceBound g.toFrameMetric)
    (hI : M.InteriorBump g.toFrameMetric) (hL : M.AbsLatticeApprox g.toFrameMetric)
    {A : ℝ} (hstar : M.StarIneq g.toFrameMetric A) {σb : ℝ} (hYb : σb = 0) :
    c < 0 ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) ∧
      (∀ s : ℝ, M.gapYb s g = M.gapBdry s g ∧
        M.gapYb s g = s + |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
        s + M.infF g.toFrameMetric (fun _ => cN N) ≤ M.gapYb s g) ∧
      |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) = M.gapYb σb g ∧
      0 < M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
        (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.infF g.toFrameMetric (fun _ => cN N) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.gapYb σb g ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) *
              (2 * ((N : ℝ) - 1) * roundMass N r /
                (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N)) *
              (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
            M.gapYb σb g) ∧
      (fun F => corRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |corRem N (M.theta g.toFrameMetric) A F| ≤ 3 / 7 * |A * F / aN N| := by
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.cor_yamabe_of_eq_main hN g hV0 hB0 hD hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB
    hρ hHτ S (M.theta_pos g.toFrameMetric hN hV0 hB0 hP hT hI)
    (M.eq_main_lattice g.toFrameMetric hN hV0 hB0 hP hT hL hstar) hYb

/-- cor:yamabe with eq:star for every `u` (thm:main's signed form, no lattice property), any
constant `Ã`, `Yb(Σ) = 0` carried (as `thm_lower_bound_signed`). -/
theorem cor_yamabe_signed (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] [∀ j, IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (hV0 : M.vol g.toFrameMetric ≠ 0) (hB0 : ∃ j, M.bvol g.toFrameMetric j ≠ 0)
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η ε : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hεt : Tendsto ε l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ ε i)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gs i).toFrameMetric))
    (hV : ∀ i, M.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, M.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, M.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput M Y E (gs i) (fun _ => cN N))
    (hP : M.MeanPoincare g.toFrameMetric) (hT : M.TraceBound g.toFrameMetric)
    (hI : M.InteriorBump g.toFrameMetric)
    {A : ℝ} (hstar : M.StarIneqSigned g.toFrameMetric A) {σb : ℝ} (hYb : σb = 0) :
    c < 0 ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) ∧
      (∀ s : ℝ, M.gapYb s g = M.gapBdry s g ∧
        M.gapYb s g = s + |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
        s + M.infF g.toFrameMetric (fun _ => cN N) ≤ M.gapYb s g) ∧
      |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) = M.gapYb σb g ∧
      0 < M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
        (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.infF g.toFrameMetric (fun _ => cN N) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.gapYb σb g ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) *
              (2 * ((N : ℝ) - 1) * roundMass N r /
                (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N)) *
              (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
            M.gapYb σb g) ∧
      (fun F => corRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |corRem N (M.theta g.toFrameMetric) A F| ≤ 3 / 7 * |A * F / aN N| := by
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.cor_yamabe_of_eq_main hN g hV0 hB0 hD hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB
    hρ hHτ S (M.theta_pos g.toFrameMetric hN hV0 hB0 hP hT hI)
    (M.eq_main_signed g.toFrameMetric hN hV0 hB0 hP hT hstar) hYb

/-- cor:yamabe for `N = 3` at the constant `Ã = star3AtilCorr V λ C` of the corrected thm:star3
(l.602; OQ-109), for any valid Poincaré and Sobolev–Poincaré constants `λ`, `C` (as
`thm_lower_bound_three`). -/
theorem cor_yamabe_three (hN3 : N = 3) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] [∀ j, IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (hV0 : M.vol g.toFrameMetric ≠ 0) (hB0 : ∃ j, M.bvol g.toFrameMetric j ≠ 0)
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η ε : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hεt : Tendsto ε l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ ε i)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gs i).toFrameMetric))
    (hV : ∀ i, M.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, M.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, M.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput M Y E (gs i) (fun _ => cN N))
    (hP : M.MeanPoincare g.toFrameMetric) (hT : M.TraceBound g.toFrameMetric)
    (hI : M.InteriorBump g.toFrameMetric) {lam C : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C)
    (hPl : M.IsPoincareConst g.toFrameMetric lam) (hS : M.IsSobolevPoincareConst g.toFrameMetric C)
    {σb : ℝ} (hYb : σb = 0) :
    let A := star3AtilCorr (M.vol g.toFrameMetric Set.univ).toReal lam C
    c < 0 ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) ∧
      (∀ s : ℝ, M.gapYb s g = M.gapBdry s g ∧
        M.gapYb s g = s + |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
        s + M.infF g.toFrameMetric (fun _ => cN N) ≤ M.gapYb s g) ∧
      |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) = M.gapYb σb g ∧
      0 < M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
        (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.infF g.toFrameMetric (fun _ => cN N) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.gapYb σb g ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) *
              (2 * ((N : ℝ) - 1) * roundMass N r /
                (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N)) *
              (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
            M.gapYb σb g) ∧
      (fun F => corRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |corRem N (M.theta g.toFrameMetric) A F| ≤ 3 / 7 * |A * F / aN N| := by
  intro A
  subst hN3
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.cor_yamabe_signed le_rfl g hV0 hB0 hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB
    hρ hHτ S hP hT hI (star3_of_consts M g.toFrameMetric hD hlam hC hPl hS) hYb

/-- cor:yamabe for every `N ≥ 3` at the explicit constant of prop:starN (l.680; OQ-118),
`Ã = starNAtil q (max c_q q) V λ C`, `q = p*`, for any constant `c_q` of lem:elem and any valid
Poincaré and Sobolev–Poincaré constants `λ`, `C` (as `thm_lower_bound_starN`). -/
theorem cor_yamabe_starN (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] [∀ j, IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (hV0 : M.vol g.toFrameMetric ≠ 0) (hB0 : ∃ j, M.bvol g.toFrameMetric j ≠ 0)
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η ε : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hεt : Tendsto ε l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ ε i)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gs i).toFrameMetric))
    (hV : ∀ i, M.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, M.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, M.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput M Y E (gs i) (fun _ => cN N))
    (hP : M.MeanPoincare g.toFrameMetric) (hT : M.TraceBound g.toFrameMetric)
    (hI : M.InteriorBump g.toFrameMetric) {lam C cq : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C)
    (hPl : M.IsPoincareConst g.toFrameMetric lam) (hS : M.IsSobolevPoincareConst g.toFrameMetric C)
    (hcq : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ pStar N ≤ 1 + pStar N * x + cq * (x ^ 2 + |x| ^ pStar N))
    {σb : ℝ} (hYb : σb = 0) :
    let A := starNAtil (pStar N) (max cq (pStar N)) (M.vol g.toFrameMetric Set.univ).toReal lam C
    c < 0 ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) ∧
      (∀ s : ℝ, M.gapYb s g = M.gapBdry s g ∧
        M.gapYb s g = s + |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
        s + M.infF g.toFrameMetric (fun _ => cN N) ≤ M.gapYb s g) ∧
      |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) = M.gapYb σb g ∧
      0 < M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
        (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.infF g.toFrameMetric (fun _ => cN N) ∧
      M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) * M.Fq g.toFrameMetric M.one *
          (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
        M.gapYb σb g ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.theta g.toFrameMetric / (1 + M.theta g.toFrameMetric) *
              (2 * ((N : ℝ) - 1) * roundMass N r /
                (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N)) *
              (1 + corRem N (M.theta g.toFrameMetric) A (M.Fq g.toFrameMetric M.one)) ≤
            M.gapYb σb g) ∧
      (fun F => corRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |corRem N (M.theta g.toFrameMetric) A F| ≤ 3 / 7 * |A * F / aN N| := by
  intro A
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.cor_yamabe_signed hN g hV0 hB0 hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB
    hρ hHτ S hP hT hI
    (M.starN_signed_of_consts g.toFrameMetric hN hD hlam hC hPl hS
      (elem_signed (two_le_pStar hN) hcq)) hYb

end MeasuredModel

/-! ## 4. On a model reading a compact connected manifold with boundary -/

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

namespace Reads

variable {D Y E : Type*} [AddCommGroup D] [Module ℝ D] [MeasurableSpace Y] [AddCommGroup E]
  [Module ℝ E] {n : ℕ} {Mm : MeasuredModel M D N n} {g : RiemannianMetric N M} {μ : Measure M}
  {σ : Fin n → Measure M}

/-- cor:yamabe for `N = 3` on a model reading a compact connected `3`-manifold with non-empty
boundary (OQ-93), at `Ã = star3AtilCorr V λ₁ C_SP` (def:constants' constants): `MeanPoincare`,
the trace theorem, `λ₁ ∈ (0, ∞)`, `C_SP < ∞` and eq:star are discharged; carried: `NonConst`,
`InteriorBump`, thm:upper-bound's inputs and `Yb(Σ) = 0` (as `Mfd.Reads.thm_lower_bound_three`). -/
theorem cor_yamabe_three (hN3 : N = 3) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    [∀ j, IsFiniteMeasure (σ j)] {gc : CurvedMetric M N}
    (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) (hV0 : μ ≠ 0) (hB0 : ∃ j, σ j ≠ 0)
    (hne : Mm.NonConst gc.toFrameMetric) (hI : Mm.InteriorBump gc.toFrameMetric)
    (hH : Mm.MinimalBoundary gc) {c : ℝ} (hRc : ∀ x, gc.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric M N) (η ε : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, MeasuredModel.UniformlyClose (η i) gc.toFrameMetric (gs i).toFrameMetric)
    (hεt : Tendsto ε l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - gc.R x| ≤ ε i)
    (hfin : ∀ i, IsFiniteMeasure (Mm.vol (gs i).toFrameMetric))
    (hV : ∀ i, Mm.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, Mm.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, Mm.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, Mm.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput Mm Y E (gs i) (fun _ => cN N)) {σb : ℝ} (hYb : σb = 0) :
    let A := star3AtilCorr (μ Set.univ).toReal (Mm.lambda1 gc.toFrameMetric) (Mm.Csp gc.toFrameMetric)
    c < 0 ∧ Mm.Y gc = c * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      Mm.Y gc ≤ -Mm.infF gc.toFrameMetric (fun _ => cN N) ∧
      (∀ s : ℝ, Mm.gapYb s gc = Mm.gapBdry s gc ∧
        Mm.gapYb s gc = s + |c| * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
        s + Mm.infF gc.toFrameMetric (fun _ => cN N) ≤ Mm.gapYb s gc) ∧
      |c| * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) = Mm.gapYb σb gc ∧
      0 < Mm.theta gc.toFrameMetric / (1 + Mm.theta gc.toFrameMetric) * Mm.Fq gc.toFrameMetric Mm.one *
        (1 + corRem N (Mm.theta gc.toFrameMetric) A (Mm.Fq gc.toFrameMetric Mm.one)) ∧
      Mm.theta gc.toFrameMetric / (1 + Mm.theta gc.toFrameMetric) * Mm.Fq gc.toFrameMetric Mm.one *
          (1 + corRem N (Mm.theta gc.toFrameMetric) A (Mm.Fq gc.toFrameMetric Mm.one)) ≤
        Mm.infF gc.toFrameMetric (fun _ => cN N) ∧
      Mm.theta gc.toFrameMetric / (1 + Mm.theta gc.toFrameMetric) * Mm.Fq gc.toFrameMetric Mm.one *
          (1 + corRem N (Mm.theta gc.toFrameMetric) A (Mm.Fq gc.toFrameMetric Mm.one)) ≤
        Mm.gapYb σb gc ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (Mm.bvol gc.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        Mm.Fq gc.toFrameMetric Mm.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          Mm.theta gc.toFrameMetric / (1 + Mm.theta gc.toFrameMetric) *
              (2 * ((N : ℝ) - 1) * roundMass N r /
                (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N)) *
              (1 + corRem N (Mm.theta gc.toFrameMetric) A (Mm.Fq gc.toFrameMetric Mm.one)) ≤
            Mm.gapYb σb gc) ∧
      (fun F => corRem N (Mm.theta gc.toFrameMetric) A F) =O[𝓝 0] (fun F => F) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |corRem N (Mm.theta gc.toFrameMetric) A F| ≤ 3 / 7 * |A * F / aN N| := by
  intro A
  subst hN3
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  haveI : ∀ j, IsFiniteMeasure (Mm.bvol gc.toFrameMetric j) := fun j => by
    rw [hr.bvol_eq j]; infer_instance
  obtain ⟨j, hj⟩ := hB0
  exact Mm.cor_yamabe_signed le_rfl gc (by rw [hr.vol_eq]; exact hV0)
    ⟨j, by rw [hr.bvol_eq j]; exact hj⟩ hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB hρ hHτ S
    (hr.meanPoincare hμ) (hr.traceIneq le_rfl hμ hσ) hI (hr.thm_star3_corrected hμ hne) hYb

/-- cor:yamabe for every `N ≥ 3` on a model reading a compact connected `N`-manifold with non-empty
boundary (OQ-93), at prop:starN's `Ã = starNAtil q (q² 2^q) V λ₁ C_SP`, `q = p*`: `MeanPoincare`,
the trace theorem, `λ₁ ∈ (0, ∞)`, `C_SP < ∞` and eq:star are discharged; carried: `NonConst`,
`InteriorBump`, thm:upper-bound's inputs and `Yb(Σ) = 0` (as `Mfd.Reads.thm_lower_bound_starN`). -/
theorem cor_yamabe_starN (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    [∀ j, IsFiniteMeasure (σ j)] {gc : CurvedMetric M N}
    (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) (hV0 : μ ≠ 0) (hB0 : ∃ j, σ j ≠ 0)
    (hne : Mm.NonConst gc.toFrameMetric) (hI : Mm.InteriorBump gc.toFrameMetric)
    (hH : Mm.MinimalBoundary gc) {c : ℝ} (hRc : ∀ x, gc.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric M N) (η ε : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, MeasuredModel.UniformlyClose (η i) gc.toFrameMetric (gs i).toFrameMetric)
    (hεt : Tendsto ε l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - gc.R x| ≤ ε i)
    (hfin : ∀ i, IsFiniteMeasure (Mm.vol (gs i).toFrameMetric))
    (hV : ∀ i, Mm.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, Mm.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, Mm.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, Mm.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput Mm Y E (gs i) (fun _ => cN N)) {σb : ℝ} (hYb : σb = 0) :
    let A := starNAtil (pStar N) (elemC (pStar N)) (μ Set.univ).toReal
      (Mm.lambda1 gc.toFrameMetric) (Mm.Csp gc.toFrameMetric)
    c < 0 ∧ Mm.Y gc = c * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      Mm.Y gc ≤ -Mm.infF gc.toFrameMetric (fun _ => cN N) ∧
      (∀ s : ℝ, Mm.gapYb s gc = Mm.gapBdry s gc ∧
        Mm.gapYb s gc = s + |c| * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
        s + Mm.infF gc.toFrameMetric (fun _ => cN N) ≤ Mm.gapYb s gc) ∧
      |c| * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) = Mm.gapYb σb gc ∧
      0 < Mm.theta gc.toFrameMetric / (1 + Mm.theta gc.toFrameMetric) * Mm.Fq gc.toFrameMetric Mm.one *
        (1 + corRem N (Mm.theta gc.toFrameMetric) A (Mm.Fq gc.toFrameMetric Mm.one)) ∧
      Mm.theta gc.toFrameMetric / (1 + Mm.theta gc.toFrameMetric) * Mm.Fq gc.toFrameMetric Mm.one *
          (1 + corRem N (Mm.theta gc.toFrameMetric) A (Mm.Fq gc.toFrameMetric Mm.one)) ≤
        Mm.infF gc.toFrameMetric (fun _ => cN N) ∧
      Mm.theta gc.toFrameMetric / (1 + Mm.theta gc.toFrameMetric) * Mm.Fq gc.toFrameMetric Mm.one *
          (1 + corRem N (Mm.theta gc.toFrameMetric) A (Mm.Fq gc.toFrameMetric Mm.one)) ≤
        Mm.gapYb σb gc ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (Mm.bvol gc.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        Mm.Fq gc.toFrameMetric Mm.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          Mm.theta gc.toFrameMetric / (1 + Mm.theta gc.toFrameMetric) *
              (2 * ((N : ℝ) - 1) * roundMass N r /
                (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N)) *
              (1 + corRem N (Mm.theta gc.toFrameMetric) A (Mm.Fq gc.toFrameMetric Mm.one)) ≤
            Mm.gapYb σb gc) ∧
      (fun F => corRem N (Mm.theta gc.toFrameMetric) A F) =O[𝓝 0] (fun F => F) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |corRem N (Mm.theta gc.toFrameMetric) A F| ≤ 3 / 7 * |A * F / aN N| := by
  intro A
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  haveI : ∀ j, IsFiniteMeasure (Mm.bvol gc.toFrameMetric j) := fun j => by
    rw [hr.bvol_eq j]; infer_instance
  obtain ⟨⟨hl1, -, -⟩, ⟨hCsp, -, -⟩, hP⟩ := hr.def_constants hN hμ hne
  have hstar := Mm.prop_starN_explicit gc.toFrameMetric hN hr.hD hl1 hCsp
  rw [hr.vol_eq] at hstar
  obtain ⟨j, hj⟩ := hB0
  exact Mm.cor_yamabe_signed hN gc (by rw [hr.vol_eq]; exact hV0)
    ⟨j, by rw [hr.bvol_eq j]; exact hj⟩ hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB hρ hHτ S
    hP (hr.traceIneq hN hμ hσ) hI hstar hYb

end Reads

end Mfd

/-! ## 5. A witness: every hypothesis holds on the two-point toy model -/

section Toy

/-- On the toy model with `g = toyConst (-8)` (`R_g ≡ -8`, minimal boundary), the constant family
`g̃_τ = g`, the gluing input `toyNegInput`, the exact lattice property `toy_absLattice`, the
corrected thm:star3 constant at `λ = 4`, `C = 1`, and `Yb = 0`: every hypothesis of the principal
anchor `cor_yamabe` holds, `|R_g| Vol^{2/3} = δ`, and `δ ≥ θ/(1+θ) F_g(1) (1 + corRem) > 0`. -/
theorem toy_cor_yamabe :
    let A := star3AtilCorr (toyModel.vol toyMetric Set.univ).toReal 4 1
    |(-8 : ℝ)| * (toyModel.vol toyMetric Set.univ).toReal ^ (2 / ((3 : ℕ) : ℝ)) =
        toyModel.gapYb 0 (toyConst (-8)) ∧
      0 < toyModel.theta toyMetric / (1 + toyModel.theta toyMetric) *
        toyModel.Fq toyMetric toyModel.one *
        (1 + corRem 3 (toyModel.theta toyMetric) A (toyModel.Fq toyMetric toyModel.one)) ∧
      toyModel.theta toyMetric / (1 + toyModel.theta toyMetric) *
          toyModel.Fq toyMetric toyModel.one *
          (1 + corRem 3 (toyModel.theta toyMetric) A (toyModel.Fq toyMetric toyModel.one)) ≤
        toyModel.gapYb 0 (toyConst (-8)) := by
  intro A
  obtain ⟨h1, h2, hV, hB, hP, hT, hI, hL, -, -, -, hstar⟩ := toy_thm_main_hyps
  haveI : IsFiniteMeasure (toyModel.vol (toyConst (-8)).toFrameMetric) := h1
  haveI : ∀ j, IsFiniteMeasure (toyModel.bvol (toyConst (-8)).toFrameMetric j) := h2
  have hclose : ∀ _ : ℕ, MeasuredModel.UniformlyClose ((fun _ : ℕ => (0 : ℝ)) 0)
      (toyConst (-8)).toFrameMetric (toyConst (-8)).toFrameMetric := fun _ x v => by simp
  have hρ : toyModel.DensityMeasurable toyMetric :=
    ⟨Measurable.of_discrete.aemeasurable, fun _ => Measurable.of_discrete.aemeasurable⟩
  obtain ⟨-, -, -, -, hEq, hpos, -, hgap, -⟩ := toyModel.cor_yamabe (le_refl 3)
    (toyConst (-8)) hV hB (toyConst_minimal _) (c := -8) (fun _ => rfl) (l := atTop)
    (fun _ : ℕ => toyConst (-8)) (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds
    hclose tendsto_const_nhds (fun _ _ => by simp) (fun _ => toy_isFiniteMeasure_vol)
    (fun _ => toy_vol_ne_zero)
    (fun _ j => by rw [toyConst_toFrameMetric, toy_bvol]; exact Measure.dirac_ne_zero)
    (fun _ => hρ) (fun _ => toyConst_minimal _) (fun _ => toyNegInput) hP hT hI
    (MeasuredModel.AbsLattice.approx _ _ hL) hstar.starIneq rfl
  exact ⟨hEq, hpos, hgap⟩

end Toy

end Yamabe
