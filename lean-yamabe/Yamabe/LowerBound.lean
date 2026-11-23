import Yamabe.Perforated.Poincare
import Yamabe.Perforated.StarN

/-!
# Yamabe § 6, thm:lower-bound over the measured model: `δ(Σ, g) ≥ κ F_g(1)`, from thm:upper-bound and the companion's thm:main

Label (lines of `papers/yamabe/legacy/labeled/Yamabegap.tex`). NOT marked: partial (see SCOPE).

* `thm:lower-bound` — `Yamabegap.tex:512` (statement l.512–536; « the proof … is given in the
  companion paper », shape l.538–545). The proof is the companion's (`papers/perforated`,
  lines of `perforated.tex`): eq:linear (l.505), eq:calib (l.512), thm:main (l.180), thm:star3
  (l.602), prop:starN (l.680) and § 8's « δ ≥ λ_∂ whenever Yb(Σ) ≥ 0 » (l.925).

> Under the hypotheses of Theorem~\ref{thm:upper-bound}, let $\cpst(\Sigma,\g)$ denote the
> capacity of $\partial\Sigma$ against a uniform neutralising background, i.e.\ the least
> Dirichlet energy of a function whose mean over $\Sigma$ exceeds its (area-weighted) mean over
> $\partial\Sigma$ by one, and set
> $\theta:=\frac{\aN\,\cpst(\Sigma,\g)}{\cN\sum_j\Vol(B_j,\g)^{(N-2)/(N-1)}}$ .
> Then
> $\delta(\Sigma,\g)\ \ge\ \kappa\,\Fq_\g(1) =\ \kappa\,\frac{2(N-1)M}{\Vol(\Sigma,\g)^{(N-2)/N}}$ ,
> with an explicit
> $\kappa=\frac{\theta}{1+\theta}\Big(1-\tfrac{\Atil\,\theta\,\Fq_\g(1)}{\aN(1+\theta)^2}+O(\Fq_\g(1)^2)\Big)$ ,
> where $\Atil$ depends only on the Sobolev--Poincar\'e and Poincar\'e constants of
> $(\Sigma,\g)$. The factor $\theta/(1+\theta)$ is optimal. One has $\theta=2$ for a Euclidean
> ball in every dimension and $\theta=1$ for a Schwarzschild collar, so that $\kappa\to1/2$ in
> the dilute limit relevant here, giving
> $|\Rs_\g|\,\Vol(\Sigma,\g)^{2/N}\ \ge\ \frac{(N-1)M}{\Vol(\Sigma,\g)^{(N-2)/N}}\big(1+o(1)\big)$ ,
> i.e.\ $|\Rs_\g|\ge2M/\Vol(\Sigma,\g)$ for $N=3$. (l.514–535)

> The proof is analytic rather than geometric and is given in the companion paper
> \cite{BrunswicPerforated}; we indicate only its shape. [...] minimizing $\aN X^2+\cN Y^2$
> under that linear constraint returns $\theta/(1+\theta)$ with no loss whatever. (l.538–543)

> $\delta(\Sigma,\g):=\sigbd(\Sigma)-\EH(\Sigma,\g)$ . (eq:gap-bdry, l.352–353)

> so that the \emph{gap} $\delta:=\Yb(\Sigma)-\Y_{[g]}(\Sigma)$ obeys
> $\delta\ge\lambda_\partial$ whenever $\Yb(\Sigma)\ge0$. For a punctured flat
> torus $\Yb(\Sigma)=0$, and Theorem~\ref{thm:main} converts \eqref{eq:yamabe-upper}
> into a quantitative statement: (perforated l.924–927)

## The model

`Σ` is a `MeasuredModel` `M` with a `CurvedMetric` `g` (DEC-186). thm:upper-bound's hypotheses
are read as the strict `Yamabe.MeasuredModel.upper_bound_of_gluings_of_pos` reads them; thm:main's
as `Yamabe.MeasuredModel.thm_main` (eq:star for `u ≥ 0` under `AbsLatticeApprox`) and
`thm_main_signed` (eq:star for every `u`) read them (OQ-111 (a) picks one; no Lean change).
`λ_∂ = inf F_g` is `infF (fun _ => c_N)`, `F_g(1) = Fq one`, `θ = theta`, `cap* = capStar`.
New here: `gapBdry σb g = σb − EH(Σ, g)` (eq:gap-bdry at a value `σb` of `σ^∂(Σ)`) and `kappa`
(eq:kappa with the explicit remainder `mainRem` of eq:main-asymp).

## What is proved (no `sorry` in this file)

* `gap_ge_of_le_infF` (the yamabe side): any `0 < b ≤ inf F_g` gives `R_g ≡ c < 0`,
  `EH = Y_[g] = c Vol^{2/N}`, `b ≤ −EH`, `b ≤ |R_g| Vol^{2/N}` and `δ ≥ σb + b` for every `σb`.
* `kappa_mul_Fq` (`κ F_g(1) = F_g(1)/Λ_max`), `le_abs_of_round` (the `M` form of eq:R-bound).
* `lower_bound_of_eq_main`: the assembly from eq:main.
* Anchors over the model, all with the same conclusions: `thm_lower_bound` (thm:main as printed,
  every `Ã` with eq:star for `u ≥ 0`), `thm_lower_bound_signed` (every `Ã` with eq:star for every
  `u`), `thm_lower_bound_three` (`N = 3`, `Ã = star3AtilCorr V λ C`, the corrected thm:star3),
  `thm_lower_bound_starN` (`N ≥ 3`, `Ã = starNAtil`, prop:starN).
* On a model reading a compact connected manifold with boundary (`Yamabe.Mfd.Reads`, OQ-93):
  `Mfd.Reads.thm_lower_bound_three`, `Mfd.Reads.thm_lower_bound_starN`, at `λ₁`, `C_SP` of
  def:constants, with `MeanPoincare`, the trace theorem and eq:star discharged.
* Witness: `toy_thm_lower_bound` (every hypothesis holds on the two-point toy model, `R_g ≡ −8`,
  `σb = 0`, and the bound is positive).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N ≥ 3` | ✓ carried (`hN`; `N = 3` as `hN3`) |
| thm:upper-bound: `σ(Σ̄) ≤ 0`, constant scalar curvature, minimal boundary, `B_j` conformally round (l.495, through l.514) | ⚠ read as in `upper_bound_of_gluings_of_pos`: `R_g x = c` for every `x`, `MinimalBoundary`; the family `g̃_τ` of lem:gluing with, per `τ`, a `GluingInput` (`β_j = c_N`, `Y_[ḡ_τ](Σ̄) ≤ 0`) |
| `R_g ≤ 0`, or lem:positivity, inside thm:upper-bound's proof (l.724, l.728) | ✓ derived: `inf F_g ≥ F_g(1)/Λ_max > 0` by thm:main |
| `Σ` compact, `Σ ≠ ∅`, `∂Σ ≠ ∅` (n ≥ 1 standing, DEC-186) | ✓ carried: finite `vol`, `bvol`; `vol ≠ 0`; `∃ j, bvol j ≠ 0` |
| `Σ` connected, the trace theorem (lem:capstar, eq:linear) | model: ⚠ carried `MeanPoincare`, `TraceBound`; manifold reading: ✓ discharged |
| `cap* < ∞`, so `θ > 0` (perforated l.399–401) | ⚠ carried: `InteriorBump` |
| `cap*`: « mean over `Σ` exceeds its (area-weighted) mean over `∂Σ` by one » (l.514) | ⚠ read: the companion's `ℓ`, weights `w_j = |B_j|^{(N−2)/(N−1)}/S` (perforated l.156–170); question |
| `θ` (eq:theta-def, l.515–518) | ✓ `theta` |
| eq:star with `Ã` (thm:main's hypothesis); « `Ã` depends only on the Sobolev–Poincaré and Poincaré constants » (l.530) | ⚠ every real `Ã` with eq:star; instances `star3AtilCorr V λ C`, `starNAtil q c V λ C` (they also depend on `V`); on a reading at `λ₁`, `C_SP`, with `NonConst` carried |
| `u ↦ |u|` (perforated l.458–460) | ⚠ carried: `AbsLatticeApprox` (`thm_lower_bound`); not used by the `_signed` form |
| `δ(Σ, g) = σ^∂(Σ) − EH(Σ, g)` (eq:gap-bdry, l.352–353) | ⚠ read: `gapBdry σb g` for a real `σb`; `σ^∂(Σ)` is not definable on the model |
| `σ^∂(Σ) ≥ 0` (used by the proof, perforated l.925; for `Σ̄ = T³` eq:sigma-torus, l.366–369, argued) | ⚠ carried: `hσb : 0 ≤ σb`; finding |
| `O(F_g(1)²)` (l.528) | ⚠ read (OQ-111 (b)): the explicit `mainRem N θ Ã F`, `O(F²)` at fixed `θ`, `Ã`, and `|R| ≤ (5/7)(ÃF/a_N)²` for `|ÃF/a_N| ≤ 1/4`, uniformly in `θ` |
| `κ F_g(1) = κ 2(N−1)M/Vol^{(N−2)/N}` (l.522–524) | ⚠ under round `B_j` of radii `r_j` (the Setting, l.467, eq:F1-torus l.469), `M = ω_{N−1} Σ r_j^{N−2}` (OQ-44): a conditional conjunct; finding |
| `|R_g|` (eq:R-bound) | ✓ `|c|`, with `c < 0` derived |
| « `θ/(1+θ)` is optimal », `θ = 2`, `θ = 1`, `κ → 1/2`, eq:R-bound's `(1 + o(1))` (l.530–535) | ✗ not formalized (T-perf-dilute-limit, needs-ruling); eq:R-bound before the limit is proved: `|R_g| ≥ 2(N−1) κ M / Vol` |

## SCOPE (disclosed)

* **Why partial.** (1) `σ^∂(Σ) ≥ 0` is carried (`hσb`): the proof needs it, the theorem does not
  state it, and the paper proves it for no `Σ̄` (eq:sigma-torus is argued for `T³`). Without a
  sign the strongest form is proved: `δ ≥ σ^∂(Σ) + κ F_g(1)` (`gap_ge_of_le_infF`), and the
  `σ`-free core `−EH(Σ, g) ≥ κ F_g(1)`, which is eq:R-bound before the limit. (2) The model
  carries `MeanPoincare`, `TraceBound`, `InteriorBump` and eq:star; the manifold forms discharge
  all but `InteriorBump` and `NonConst`, under the readings of OQ-93 (open). (3) thm:upper-bound's
  inputs (lem:gluing's family, thm:yamabe (b), the conformal law, fact (iv)) enter through
  `GluingInput`, as in the strict library. (4) Three clauses (optimality, the two `θ` values with
  `κ → 1/2`, eq:R-bound's `o(1)`) wait on T-perf-dilute-limit. (5) The marks wait on OQ-93 and
  OQ-111.
* **`σ^∂(Σ)`.** eq:sigma-bdry is a supremum over all conformal classes of `Σ`. On the model `R`
  and `H` are free data of `CurvedMetric` (kb 0018), so a supremum of `Y` over model metrics is
  unbounded and Lean's `sSup` would be the junk `0`: `σ^∂(Σ)` is a real parameter `σb` here, and
  every statement holds for every value (with `0 ≤ σb` where the printed bound is stated).
* **`δ` and the companion's `δ`.** eq:gap-bdry uses `EH(Σ, g)`, perforated l.924 uses `Y_[g](Σ)`;
  they agree here: `EH = Y` is proved (`R_g ≡ c < 0`, minimal boundary, `EH_eq_Y`).
* **`κ`.** `kappa g Ã = θ/(1+θ) (1 − Ãθ F/(a_N(1+θ)²) + mainRem N θ Ã F)`, `F = F_g(1)`, and
  `κ F_g(1) = F_g(1)/Λ_max` exactly (`kappa_mul_Fq`): the bound is eq:main's, rewritten.
* **`M`.** The model has no Weyl embedding and no `H_ref`; `M` is read at its round-sphere value
  `roundMass N r = ω_{N−1} Σ r_j^{N−2}` (the Setting, l.467; OQ-44), and the `M` forms are stated
  for every `r ≥ 0` matching the boundary areas.
* **Junk values.** If `cap* = ∞`, `θ = 0` in Lean; `InteriorBump` excludes it. `normSq`,
  `dirichlet` are `0` when infinite; the carried hypotheses use the same quantities.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

/-! ## 1. Arithmetic -/

/-- The `M` form of eq:R-bound before the limit: from `κ F ≤ a V^{2/N}` and
`F = K / V^{(N−2)/N}`, `κ K / V ≤ a`. -/
lemma le_abs_of_round {N : ℕ} (hN : 3 ≤ N) {V κ F K a : ℝ} (hV : 0 < V)
    (hF : F = K / V ^ (((N : ℝ) - 2) / N)) (h : κ * F ≤ a * V ^ (2 / (N : ℝ))) :
    κ * K / V ≤ a := by
  have hN' := three_le_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hb : 0 < V ^ (((N : ℝ) - 2) / N) := Real.rpow_pos_of_pos hV _
  have hab : V ^ (2 / (N : ℝ)) * V ^ (((N : ℝ) - 2) / N) = V := by
    rw [← Real.rpow_add hV]
    have e : 2 / (N : ℝ) + ((N : ℝ) - 2) / N = 1 := by field_simp; ring
    rw [e, Real.rpow_one]
  rw [hF] at h
  have h' := mul_le_mul_of_nonneg_right h hb.le
  have e : κ * (K / V ^ (((N : ℝ) - 2) / N)) * V ^ (((N : ℝ) - 2) / N) = κ * K := by
    field_simp
  rw [e, mul_assoc, hab] at h'
  rw [div_le_iff₀ hV]
  exact h'

namespace MeasuredModel

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-! ## 2. The gap and `κ` -/

/-- The Yamabe gap with boundary (eq:gap-bdry, l.352–353) at a value `σb` of the relative Yamabe
invariant `σ^∂(Σ)` (eq:sigma-bdry, l.346–348): `δ(Σ, g) = σb − EH(Σ, g)`. -/
def gapBdry (σb : ℝ) (g : CurvedMetric X N) : ℝ := σb - M.EH g

/-- `κ` of eq:kappa (l.526–529), with the explicit remainder `mainRem` of eq:main-asymp in place
of `O(F_g(1)²)` (OQ-111 (b)). -/
def kappa (g : FrameMetric X N) (A : ℝ) : ℝ :=
  M.theta g / (1 + M.theta g) *
    (1 - A * M.theta g * M.Fq g M.one / (aN N * (1 + M.theta g) ^ 2) +
      mainRem N (M.theta g) A (M.Fq g M.one))

/-- `κ F_g(1) = F_g(1) / Λ_max` (eq:main-asymp is eq:main rewritten). -/
lemma kappa_mul_Fq (g : FrameMetric X N) (hθ : 0 < M.theta g) (A : ℝ) :
    M.kappa g A * M.Fq g M.one =
      M.Fq g M.one / lamMax (1 / M.theta g) 1 (A * M.Fq g M.one / aN N) := by
  rw [eq_main_asymp_identity (N := N) hθ A (M.Fq g M.one)]
  unfold kappa
  ring

/-! ## 3. The yamabe side -/

/-- The yamabe side of thm:lower-bound (l.512–536 with perforated l.917–925), from any positive
lower bound `b` on `inf F_g`: under thm:upper-bound's hypotheses (as
`upper_bound_of_gluings_of_pos` reads them), `R_g ≡ c < 0`, `EH(Σ, g) = Y_[g](Σ) = c Vol^{2/N}`,
`b ≤ −EH(Σ, g) = |R_g| Vol^{2/N}`, and `δ(Σ, g) ≥ σb + b` for every value `σb` of `σ^∂(Σ)`. -/
theorem gap_ge_of_le_infF (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
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
    {b : ℝ} (hb : 0 < b) (hbF : b ≤ M.infF g.toFrameMetric (fun _ => cN N)) :
    c < 0 ∧ M.EH g = M.Y g ∧
      M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      b ≤ -M.EH g ∧
      b ≤ |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      ∀ σb : ℝ, σb + b ≤ M.gapBdry σb g := by
  obtain ⟨hc, hYc, hub⟩ := M.upper_bound_of_gluings_of_pos hN g hD hH hRc
    (lt_of_lt_of_le hb hbF) gs η ε hη hηt hclose hεt hR hfin hV hB hρ hHτ S
  have hEH : M.EH g = M.Y g := M.EH_eq_Y g hN hD hH hc.le (ae_of_all _ hRc)
  have hneg : b ≤ -M.EH g := by rw [hEH]; linarith
  refine ⟨hc, hEH, hYc, hneg, ?_, fun σb => ?_⟩
  · rw [abs_of_neg hc, neg_mul, ← hYc, ← hEH]
    exact hneg
  · unfold gapBdry
    linarith

/-! ## 4. thm:lower-bound over the model -/

/-- The assembly of thm:lower-bound from eq:main (`hmain`) and `θ > 0`. Conclusions: `R_g ≡ c < 0`
and `EH = Y_[g]`; `κ F_g(1) > 0`; eq:lower-bound in eq:main's form `δ ≥ F_g(1)/Λ_max` and in
eq:kappa's form `δ ≥ κ F_g(1)`; eq:R-bound before the limit, `|R_g| Vol^{2/N} ≥ κ F_g(1)`; for
round boundary spheres of radii `r_j`, `F_g(1) = 2(N−1)M/Vol^{(N−2)/N}` (eq:F1-torus) and
`|R_g| ≥ κ 2(N−1) M / Vol`; the remainder of eq:kappa is `O(F²)` at fixed `θ`, `Ã`, with the
uniform bound. -/
theorem lower_bound_of_eq_main (hN : 3 ≤ N) (g : CurvedMetric X N)
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
    {σb : ℝ} (hσb : 0 ≤ σb) :
    c < 0 ∧ M.EH g = M.Y g ∧
      0 < M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ∧
      M.Fq g.toFrameMetric M.one /
          lamMax (1 / M.theta g.toFrameMetric) 1 (A * M.Fq g.toFrameMetric M.one / aN N) ≤
        M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤ M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤
        |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.kappa g.toFrameMetric A * (2 * ((N : ℝ) - 1) * roundMass N r) /
            (M.vol g.toFrameMetric Set.univ).toReal ≤ |c|) ∧
      (fun F => mainRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |mainRem N (M.theta g.toFrameMetric) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  have hF := M.Fq_one_pos g.toFrameMetric hN hV0 hB0
  have hα : 0 ≤ 1 / M.theta g.toFrameMetric := (one_div_pos.mpr hθ).le
  have hΛ : 0 < lamMax (1 / M.theta g.toFrameMetric) 1 (A * M.Fq g.toFrameMetric M.one / aN N) :=
    lt_of_lt_of_le one_pos (le_lamMax_right hα zero_le_one)
  have hb := div_pos hF hΛ
  obtain ⟨hc, hEH, -, -, hRb, hgap⟩ := M.gap_ge_of_le_infF hN g hD hH hRc gs η ε hη hηt hclose
    hεt hR hfin hV hB hρ hHτ S hb hmain
  have hk := M.kappa_mul_Fq g.toFrameMetric hθ A
  have hgap' := (le_add_of_nonneg_left hσb).trans (hgap σb)
  have hVpos : 0 < (M.vol g.toFrameMetric Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV0) (measure_ne_top _ _)
  have hkR : M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤
      |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) := by rw [hk]; exact hRb
  refine ⟨hc, hEH, by rw [hk]; exact hb, hgap', by rw [hk]; exact hgap', hkR,
    fun r hr hround => ?_, mainRem_isBigO hN hθ A, fun F hF' => mainRem_le_uniform hN hθ hF'⟩
  have hF1 := M.Fq_one_round g.toFrameMetric hN r hr hround
  exact ⟨hF1, le_abs_of_round hN hVpos hF1 hkR⟩

/-- **thm:lower-bound** (l.512–536) over the model, with thm:main as printed: eq:star for `u ≥ 0`
with any constant `Ã`, under the approximate lattice property of perforated l.458–460, and the
reference `σb = σ^∂(Σ) ≥ 0` carried. The conclusions of `lower_bound_of_eq_main`. -/
theorem thm_lower_bound (hN : 3 ≤ N) (g : CurvedMetric X N)
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
    {A : ℝ} (hstar : M.StarIneq g.toFrameMetric A) {σb : ℝ} (hσb : 0 ≤ σb) :
    c < 0 ∧ M.EH g = M.Y g ∧
      0 < M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ∧
      M.Fq g.toFrameMetric M.one /
          lamMax (1 / M.theta g.toFrameMetric) 1 (A * M.Fq g.toFrameMetric M.one / aN N) ≤
        M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤ M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤
        |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.kappa g.toFrameMetric A * (2 * ((N : ℝ) - 1) * roundMass N r) /
            (M.vol g.toFrameMetric Set.univ).toReal ≤ |c|) ∧
      (fun F => mainRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |mainRem N (M.theta g.toFrameMetric) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.lower_bound_of_eq_main hN g hV0 hB0 hD hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB
    hρ hHτ S (M.theta_pos g.toFrameMetric hN hV0 hB0 hP hT hI)
    (M.eq_main_lattice g.toFrameMetric hN hV0 hB0 hP hT hL hstar) hσb

/-- **thm:lower-bound with eq:star for every `u`** (thm:main's signed form, no lattice property),
any constant `Ã`, `σb = σ^∂(Σ) ≥ 0` carried. -/
theorem thm_lower_bound_signed (hN : 3 ≤ N) (g : CurvedMetric X N)
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
    {A : ℝ} (hstar : M.StarIneqSigned g.toFrameMetric A) {σb : ℝ} (hσb : 0 ≤ σb) :
    c < 0 ∧ M.EH g = M.Y g ∧
      0 < M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ∧
      M.Fq g.toFrameMetric M.one /
          lamMax (1 / M.theta g.toFrameMetric) 1 (A * M.Fq g.toFrameMetric M.one / aN N) ≤
        M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤ M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤
        |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.kappa g.toFrameMetric A * (2 * ((N : ℝ) - 1) * roundMass N r) /
            (M.vol g.toFrameMetric Set.univ).toReal ≤ |c|) ∧
      (fun F => mainRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |mainRem N (M.theta g.toFrameMetric) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.lower_bound_of_eq_main hN g hV0 hB0 hD hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB
    hρ hHτ S (M.theta_pos g.toFrameMetric hN hV0 hB0 hP hT hI)
    (M.eq_main_signed g.toFrameMetric hN hV0 hB0 hP hT hstar) hσb

/-- thm:lower-bound for `N = 3` at the constant `Ã = star3AtilCorr V λ C` of the corrected
thm:star3 (perforated l.602; OQ-109), for any valid Poincaré and Sobolev–Poincaré constants
`λ`, `C`. -/
theorem thm_lower_bound_three (hN3 : N = 3) (g : CurvedMetric X N)
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
    {σb : ℝ} (hσb : 0 ≤ σb) :
    let A := star3AtilCorr (M.vol g.toFrameMetric Set.univ).toReal lam C
    c < 0 ∧ M.EH g = M.Y g ∧
      0 < M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ∧
      M.Fq g.toFrameMetric M.one /
          lamMax (1 / M.theta g.toFrameMetric) 1 (A * M.Fq g.toFrameMetric M.one / aN N) ≤
        M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤ M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤
        |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.kappa g.toFrameMetric A * (2 * ((N : ℝ) - 1) * roundMass N r) /
            (M.vol g.toFrameMetric Set.univ).toReal ≤ |c|) ∧
      (fun F => mainRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |mainRem N (M.theta g.toFrameMetric) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  intro A
  subst hN3
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.thm_lower_bound_signed le_rfl g hV0 hB0 hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB
    hρ hHτ S hP hT hI (star3_of_consts M g.toFrameMetric hD hlam hC hPl hS) hσb

/-- thm:lower-bound for every `N ≥ 3` at the explicit constant of prop:starN (perforated l.680;
OQ-118), `Ã = starNAtil q (max c_q q) V λ C`, `q = p*`, for any constant `c_q` of lem:elem and
any valid Poincaré and Sobolev–Poincaré constants `λ`, `C`. -/
theorem thm_lower_bound_starN (hN : 3 ≤ N) (g : CurvedMetric X N)
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
    {σb : ℝ} (hσb : 0 ≤ σb) :
    let A := starNAtil (pStar N) (max cq (pStar N)) (M.vol g.toFrameMetric Set.univ).toReal lam C
    c < 0 ∧ M.EH g = M.Y g ∧
      0 < M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ∧
      M.Fq g.toFrameMetric M.one /
          lamMax (1 / M.theta g.toFrameMetric) 1 (A * M.Fq g.toFrameMetric M.one / aN N) ≤
        M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤ M.gapBdry σb g ∧
      M.kappa g.toFrameMetric A * M.Fq g.toFrameMetric M.one ≤
        |c| * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (M.bvol g.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        M.Fq g.toFrameMetric M.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          M.kappa g.toFrameMetric A * (2 * ((N : ℝ) - 1) * roundMass N r) /
            (M.vol g.toFrameMetric Set.univ).toReal ≤ |c|) ∧
      (fun F => mainRem N (M.theta g.toFrameMetric) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |mainRem N (M.theta g.toFrameMetric) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  intro A
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.thm_lower_bound_signed hN g hV0 hB0 hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB
    hρ hHτ S hP hT hI
    (M.starN_signed_of_consts g.toFrameMetric hN hD hlam hC hPl hS
      (elem_signed (two_le_pStar hN) hcq)) hσb

end MeasuredModel

/-! ## 5. On a model reading a compact connected manifold with boundary -/

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

namespace Reads

variable {D Y E : Type*} [AddCommGroup D] [Module ℝ D] [MeasurableSpace Y] [AddCommGroup E]
  [Module ℝ E] {n : ℕ} {Mm : MeasuredModel M D N n} {g : RiemannianMetric N M} {μ : Measure M}
  {σ : Fin n → Measure M}

/-- thm:lower-bound for `N = 3` on a model reading a compact connected `3`-manifold with
non-empty boundary (OQ-93), at `Ã = star3AtilCorr V λ₁ C_SP` (def:constants' constants):
`MeanPoincare`, the trace theorem, `λ₁ ∈ (0, ∞)`, `C_SP < ∞` and eq:star are discharged; carried:
`NonConst`, `InteriorBump`, thm:upper-bound's inputs and `σb = σ^∂(Σ) ≥ 0`. -/
theorem thm_lower_bound_three (hN3 : N = 3) [CompactSpace M] [T2Space M] [ConnectedSpace M]
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
    (S : ∀ i, GluingInput Mm Y E (gs i) (fun _ => cN N)) {σb : ℝ} (hσb : 0 ≤ σb) :
    let A := star3AtilCorr (μ Set.univ).toReal (Mm.lambda1 gc.toFrameMetric) (Mm.Csp gc.toFrameMetric)
    c < 0 ∧ Mm.EH gc = Mm.Y gc ∧
      0 < Mm.kappa gc.toFrameMetric A * Mm.Fq gc.toFrameMetric Mm.one ∧
      Mm.Fq gc.toFrameMetric Mm.one /
          lamMax (1 / Mm.theta gc.toFrameMetric) 1 (A * Mm.Fq gc.toFrameMetric Mm.one / aN N) ≤
        Mm.gapBdry σb gc ∧
      Mm.kappa gc.toFrameMetric A * Mm.Fq gc.toFrameMetric Mm.one ≤ Mm.gapBdry σb gc ∧
      Mm.kappa gc.toFrameMetric A * Mm.Fq gc.toFrameMetric Mm.one ≤
        |c| * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (Mm.bvol gc.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        Mm.Fq gc.toFrameMetric Mm.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          Mm.kappa gc.toFrameMetric A * (2 * ((N : ℝ) - 1) * roundMass N r) /
            (Mm.vol gc.toFrameMetric Set.univ).toReal ≤ |c|) ∧
      (fun F => mainRem N (Mm.theta gc.toFrameMetric) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |mainRem N (Mm.theta gc.toFrameMetric) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  intro A
  subst hN3
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  haveI : ∀ j, IsFiniteMeasure (Mm.bvol gc.toFrameMetric j) := fun j => by
    rw [hr.bvol_eq j]; infer_instance
  obtain ⟨j, hj⟩ := hB0
  exact Mm.thm_lower_bound_signed le_rfl gc (by rw [hr.vol_eq]; exact hV0)
    ⟨j, by rw [hr.bvol_eq j]; exact hj⟩ hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB hρ hHτ S
    (hr.meanPoincare hμ) (hr.traceIneq le_rfl hμ hσ) hI (hr.thm_star3_corrected hμ hne) hσb

/-- thm:lower-bound for every `N ≥ 3` on a model reading a compact connected `N`-manifold with
non-empty boundary (OQ-93), at prop:starN's `Ã = starNAtil q (q² 2^q) V λ₁ C_SP`, `q = p*`:
`MeanPoincare`, the trace theorem, `λ₁ ∈ (0, ∞)`, `C_SP < ∞` and eq:star are discharged; carried:
`NonConst`, `InteriorBump`, thm:upper-bound's inputs and `σb = σ^∂(Σ) ≥ 0`. -/
theorem thm_lower_bound_starN (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
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
    (S : ∀ i, GluingInput Mm Y E (gs i) (fun _ => cN N)) {σb : ℝ} (hσb : 0 ≤ σb) :
    let A := starNAtil (pStar N) (elemC (pStar N)) (μ Set.univ).toReal
      (Mm.lambda1 gc.toFrameMetric) (Mm.Csp gc.toFrameMetric)
    c < 0 ∧ Mm.EH gc = Mm.Y gc ∧
      0 < Mm.kappa gc.toFrameMetric A * Mm.Fq gc.toFrameMetric Mm.one ∧
      Mm.Fq gc.toFrameMetric Mm.one /
          lamMax (1 / Mm.theta gc.toFrameMetric) 1 (A * Mm.Fq gc.toFrameMetric Mm.one / aN N) ≤
        Mm.gapBdry σb gc ∧
      Mm.kappa gc.toFrameMetric A * Mm.Fq gc.toFrameMetric Mm.one ≤ Mm.gapBdry σb gc ∧
      Mm.kappa gc.toFrameMetric A * Mm.Fq gc.toFrameMetric Mm.one ≤
        |c| * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      (∀ r : Fin n → ℝ, (∀ j, 0 ≤ r j) →
        (∀ j, (Mm.bvol gc.toFrameMetric j Set.univ).toReal = sphereArea N * r j ^ (N - 1)) →
        Mm.Fq gc.toFrameMetric Mm.one = 2 * ((N : ℝ) - 1) * roundMass N r /
            (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
          Mm.kappa gc.toFrameMetric A * (2 * ((N : ℝ) - 1) * roundMass N r) /
            (Mm.vol gc.toFrameMetric Set.univ).toReal ≤ |c|) ∧
      (fun F => mainRem N (Mm.theta gc.toFrameMetric) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 →
        |mainRem N (Mm.theta gc.toFrameMetric) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  intro A
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  haveI : ∀ j, IsFiniteMeasure (Mm.bvol gc.toFrameMetric j) := fun j => by
    rw [hr.bvol_eq j]; infer_instance
  obtain ⟨⟨hl1, -, -⟩, ⟨hCsp, -, -⟩, hP⟩ := hr.def_constants hN hμ hne
  have hstar := Mm.prop_starN_explicit gc.toFrameMetric hN hr.hD hl1 hCsp
  rw [hr.vol_eq] at hstar
  obtain ⟨j, hj⟩ := hB0
  exact Mm.thm_lower_bound_signed hN gc (by rw [hr.vol_eq]; exact hV0)
    ⟨j, by rw [hr.bvol_eq j]; exact hj⟩ hH hRc gs η ε hη hηt hclose hεt hR hfin hV hB hρ hHτ S
    hP (hr.traceIneq hN hμ hσ) hI hstar hσb

end Reads

end Mfd

/-! ## 6. A witness: every hypothesis holds on the two-point toy model -/

section Toy

/-- On the toy model with `g = toyConst (-8)` (`R_g ≡ -8`, minimal boundary), the constant family
`g̃_τ = g`, the gluing input `toyNegInput`, the corrected thm:star3 constant at `λ = 4`, `C = 1`,
and `σb = 0`: every hypothesis of `thm_lower_bound_signed` holds, `κ F_g(1) > 0`, and
`δ ≥ κ F_g(1)`. -/
theorem toy_thm_lower_bound :
    let A := star3AtilCorr (toyModel.vol toyMetric Set.univ).toReal 4 1
    0 < toyModel.kappa toyMetric A * toyModel.Fq toyMetric toyModel.one ∧
      toyModel.kappa toyMetric A * toyModel.Fq toyMetric toyModel.one ≤
        toyModel.gapBdry 0 (toyConst (-8)) := by
  intro A
  obtain ⟨h1, h2, hV, hB, hP, hT, hI, -, -, -, -, hstar⟩ := toy_thm_main_hyps
  haveI : IsFiniteMeasure (toyModel.vol (toyConst (-8)).toFrameMetric) := h1
  haveI : ∀ j, IsFiniteMeasure (toyModel.bvol (toyConst (-8)).toFrameMetric j) := h2
  have hclose : ∀ _ : ℕ, MeasuredModel.UniformlyClose ((fun _ : ℕ => (0 : ℝ)) 0)
      (toyConst (-8)).toFrameMetric (toyConst (-8)).toFrameMetric := fun _ x v => by simp
  have hρ : toyModel.DensityMeasurable toyMetric :=
    ⟨Measurable.of_discrete.aemeasurable, fun _ => Measurable.of_discrete.aemeasurable⟩
  obtain ⟨-, -, hpos, -, hgap, -⟩ := toyModel.thm_lower_bound_signed (le_refl 3) (toyConst (-8))
    hV hB (toyConst_minimal _) (c := -8) (fun _ => rfl) (l := atTop)
    (fun _ : ℕ => toyConst (-8)) (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds
    hclose tendsto_const_nhds (fun _ _ => by simp) (fun _ => toy_isFiniteMeasure_vol)
    (fun _ => toy_vol_ne_zero)
    (fun _ j => by rw [toyConst_toFrameMetric, toy_bvol]; exact Measure.dirac_ne_zero)
    (fun _ => hρ) (fun _ => toyConst_minimal _) (fun _ => toyNegInput) hP hT hI hstar le_rfl
  exact ⟨hpos, hgap⟩

end Toy

end Yamabe
