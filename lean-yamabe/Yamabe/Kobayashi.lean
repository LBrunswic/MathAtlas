import Yamabe.Quotient

/-!
# The lower bound of Kobayashi type, part (a), over the measured model of `(Σ, ⊔ B_j)`

Label (abstract layer only; NOT marked: the row is partial by design, see SCOPE):

* `lem:kobayashi` — `Yamabegap.tex:613` (statement l.613–625, proof l.626–638), part (a): the
  bound `eq:kobayashi` (l.619–621), its "in particular" and the constant-curvature sentence
  (l.622), over the model of `Yamabe.Quotient`, with the Einstein–Hilbert action `eq:EH-action`
  (l.305), the Yamabe energy `eq:yamabe-energy-bdry` (l.310), the relative Yamabe constant
  `eq:relative-yamabe` (l.317) and the right side of the conformal law `eq:conformal-energy-bdry`
  (l.326). Part (b) (l.623) is not formalized here.

> Assume $H_\g\equiv0$ (or $\partial\Sigma=\emptyset$).
> \item[(a)] If $m:=\min(0,\min_\Sigma\Rs_\g)$, then for every $u\in W^{1,2}(\Sigma)\setminus\{0\}$
> $\EH\big(\Sigma,u^{4/(N-2)}\g\big)\ \ge\ \aN\frac{\|\nabla u\|^2_{L^2(\Sigma)}}{\|u\|^2_{L^{\pstar}(\Sigma)}}+m\Vol(\Sigma)^{2/N}\ ;$
> in particular $\Y_{[\g]}(\Sigma)\ge m\Vol(\Sigma)^{2/N}$. If $\Rs_\g$ is constant and
> non-positive, then $\EH(\Sigma,\g)=\Y_{[\g]}(\Sigma)$. [...] (l.615–622)

> (a) With $H_\g\equiv0$, \eqref{eq:conformal-energy-bdry} and \eqref{eq:hoelder} give, since
> $m\le0$,
> $\EH\big(u^{4/(N-2)}\g\big)\,\|u\|^2_{\pstar}=\aN\|\nabla u\|^2_2+\int_\Sigma\Rs_\g u^2\,\vol
> \ge\aN\|\nabla u\|^2_2+m\Vol(\Sigma)^{2/N}\|u\|^2_{\pstar}$ .
> Taking the infimum gives $\Y_{[\g]}(\Sigma)\ge m\Vol(\Sigma)^{2/N}$. If $\Rs_\g\equiv m\le0$ is
> constant, then $\EH(\Sigma,\g)=m\Vol(\Sigma)^{2/N}$, so that
> $\EH(\Sigma,\g)\le\Y_{[\g]}(\Sigma)\le\EH(\Sigma,\g)$. [...] (l.627–632)

> $\mathcal{S}(\Sigma,\g):=\int_{\Sigma}\Rs_\g\,\vol+2(N-1)\int_{\partial \Sigma}H_\g\,\bvol$ [...]
> $\EH(\Sigma,\g) := \frac{\mathcal{S}(\Sigma,\g)}{\Vol(\Sigma,\g)^{(N-2)/N}}$ [...]
> $\Y_{[\g]}(\Sigma) := \inf_{\phi>0}\EH\big(\Sigma,\phi^{4/(N-2)}\g\big)$ (l.306–318)

> $\EH(\Sigma,\tilde\g)\,\|\phi\|^2_{L^{\pstar}(\Sigma,\g)}=\int_\Sigma\big(\aN|\nabla\phi|^2_\g+\Rs_\g\phi^2\big)\vol
> +2(N-1)\int_{\partial\Sigma}H_\g\phi^2\,\bvol$ (l.327–328)

## The model

`CurvedMetric X N` extends the `FrameMetric` of `Yamabe.Quotient` by the scalar curvature `R` of
`g` on `Σ` and the mean curvature `H` of `∂Σ`, both bounded and measurable. Over a
`MeasuredModel` it gives `action` (`𝒮(Σ, g)`), `EH` (`EH(Σ, g)`), `confAction u` (the right side
of eq:conformal-energy-bdry), `confEnergy u = confAction u / ‖u‖²_{L^{p*}}` (the conformal energy,
`EH(Σ, u^{4/(N-2)} g)` through the conformal law), `MinimalBoundary` (`H_g ≡ 0`), and
`Y = inf_{u > 0} confEnergy u` (eq:relative-yamabe through the conformal law).

## What is proved

`EH_eq_confEnergy_one` (the conformal law at `φ = 1`); `minimalBoundary_of_bvol_eq_zero` ("or
`∂Σ = ∅`"); `confAction_of_minimal`, `action_of_minimal` (the boundary terms vanish);
`integrable_R_mul_sq`, `integrable_H_mul_sq` (no junk integral on `L^{p*}`, `L^{p♯}`);
`scalar_term_ge` (the Hölder step, l.629–630, through `hoelder_interior`); `confAction_ge` (the
displayed inequality l.629–630); `kobayashi` (eq:kobayashi for every `m ≤ 0` below `R_g` a.e.),
`kobayashi_printed` (with the printed `m = min(0, min_Σ R_g)`, `CurvedMetric.kobM`);
`le_infConf`, `le_Y`, `le_Y_printed` ("in particular"); `EH_eq_const_mul`, `Y_le_EH`, `EH_eq_Y`,
`Y_eq_const_mul` (the constant-curvature sentence, and `Y = R_g Vol^{2/N}` as used at l.724); the
assembly `lem_kobayashi_a`; the witness `toyCurved`, `toy_kobM`, `toy_EH`, `toy_EH_eq_Y` (`EH = Y = -2^{2/3}`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(Σ, g)` compact Riemannian `N`-manifold with boundary, `N ≥ 3` (l.605) | ⚠ read in the abstract model (SCOPE); `N ≥ 3` ✓ carried; compactness as `IsFiniteMeasure (vol_g)` |
| `R_g`, `H_g` (smooth on compact `Σ`, `∂Σ`) | ⚠ read (SCOPE): free bounded measurable fields of `CurvedMetric`, not computed from the metric |
| `H_g ≡ 0` (or `∂Σ = ∅`) (l.615) | ⚠ weakened: `H_g = 0` `bvol_j`-a.e. for every `j` (`MinimalBoundary`); `∂Σ = ∅` gives it (`minimalBoundary_of_bvol_eq_zero`) |
| `m := min(0, min_Σ R_g)` (l.617) | ⚠ weakened: any `m ≤ 0` with `m ≤ R_g` `vol_g`-a.e. (`kobayashi`); the printed `m` in `kobayashi_printed` |
| `u ∈ W^{1,2}(Σ) ∖ {0}` (l.617) | ⚠ weakened: every `u : D` whose values are a.e.-strongly measurable (`0` included) |
| `EH(Σ, u^{4/(N-2)} g)` for such `u` | ⚠ read as `confEnergy u` (the conformal law, SCOPE) |
| `φ > 0` in eq:relative-yamabe | ⚠ read (SCOPE): `Pos u` (`val u > 0` everywhere), competitors with `0 < ‖u‖²_{L^{p*}}` (`Adm`), over an unspecified competitor set |
| `R_g` constant and non-positive (l.622) | ⚠ weakened: `R_g = c` `vol_g`-a.e., `c ≤ 0` |
| `Σ` connected | ⚠ weakened: not used |

## SCOPE (disclosed)

* Abstract layer only (DEC-139, T-yamabe-quotient): the passage from `(Σ, g)` to the model, and the
  fields `R`, `H` as the scalar and mean curvatures of `g`, wait on T-yamabe-scope; the model's
  readings are OQ-44's.
* **The conformal law** eq:conformal-energy-bdry (cited, MR1152225, MR1173925) is not proved: the
  model has no second derivatives, so the scalar curvature of `φ^{4/(N-2)} g` cannot be computed
  in it. `confEnergy u` is defined as the law's right side over `‖u‖²_{L^{p*}}`, and `Y` as the
  infimum of `confEnergy` over positive competitors; their identification with
  `EH(Σ, u^{4/(N-2)} g)` and with eq:relative-yamabe is the law, which belongs to the anchoring.
  At `φ = 1` the identification is proved (`EH_eq_confEnergy_one`).
* A `CurvedMetric` carries `R`, `H` as data: the model cannot compute them from `G`. That they are
  the curvatures of `g` is part of the anchoring.
* `min_Σ R_g` is read `⨅ x, R_g x` (the infimum over `X`; a minimum for continuous `R_g` on compact
  `Σ`). `u > 0` is read `val u > 0` everywhere (`Pos`), and the competitors of `Y` are, as for
  `infF`, those with `0 < ‖u‖²_{L^{p*}} < ∞` (`Adm`).
* The infimum statements (`le_Y`, `Y_le_EH`, `EH_eq_Y`) carry `∀ u, val u` a.e.-strongly
  measurable: `D ⊆ W^{1,2}(Σ)` consists of measurable functions. No `Σ ≠ ∅` is needed: if
  `vol_g = 0`, then `EH = Y = 0`.
* `normSq` and `dirichlet` are `0` when infinite, Bochner integrals are `0` when not integrable,
  and `x / 0 = 0`. Every inequality here holds for every `u` regardless (the junk values only
  help); an instance with a `D` containing functions of infinite energy would only lower the Lean
  `Y`, as for `infF`. On `L^{p*}` the scalar term is a genuine integral (`integrable_R_mul_sq`).
* **Finding (l.606–610, l.627, l.720), a cross-reference.** The interior Hölder line l.607 is
  `\nonumber` and `\label{eq:hoelder}` sits on the boundary line (l.608–609), so the citations at l.627
  (here) and l.720 print the number of the boundary line, which is false as printed (OQ-44). Both
  arguments use the interior line, which is correct (`hoelder_interior`, in `scalar_term_ge`).
* **Finding (l.617–620), wording.** `EH(Σ, u^{4/(N-2)} g)` is the energy of a metric only for
  `u > 0`; for `u ∈ W^{1,2} ∖ {0}` it is read as the conformal quotient, for which eq:kobayashi
  holds for every `u` (`kobayashi`). Its uses (l.622, l.660) take `u > 0`.
* Part (b) rests on the Sobolev embedding `W^{1,2} ↪ L^{p*}` (Hebey1996), one of the cited theorems
  of T-yamabe-scope; the model does not carry it (`d` is an arbitrary linear map), so (b) is out of
  scope.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

/-- A metric on the model together with its curvatures: the scalar curvature `R_g` on `Σ` and the
mean curvature `H_g` of `∂Σ` (w.r.t. the outward normal, normalized as the mean of the principal
curvatures, l.299), both bounded and measurable, as for a smooth metric on a compact manifold. -/
structure CurvedMetric (X : Type*) [MeasurableSpace X] (N : ℕ) extends FrameMetric X N where
  /-- the scalar curvature `R_g` -/
  R : X → ℝ
  /-- the mean curvature `H_g` of `∂Σ` -/
  H : X → ℝ
  R_measurable : Measurable R
  H_measurable : Measurable H
  R_bdd : ∃ C, ∀ x, |R x| ≤ C
  H_bdd : ∃ C, ∀ x, |H x| ≤ C

namespace CurvedMetric

variable {X : Type*} [MeasurableSpace X] {N : ℕ} (g : CurvedMetric X N)

/-- The printed `m = min(0, min_Σ R_g)` (l.617). -/
def kobM : ℝ := min 0 (⨅ x, g.R x)

lemma kobM_nonpos : g.kobM ≤ 0 := min_le_left _ _

/-- `R_g` is bounded below, so `min_Σ R_g` is its infimum. -/
lemma bddBelow_R : BddBelow (Set.range g.R) := by
  obtain ⟨C, hC⟩ := g.R_bdd
  exact ⟨-C, by rintro _ ⟨y, rfl⟩; exact (abs_le.mp (hC y)).1⟩

lemma kobM_le (x : X) : g.kobM ≤ g.R x :=
  (min_le_right _ _).trans (ciInf_le g.bddBelow_R x)

end CurvedMetric

section Norms

variable {X : Type*} [MeasurableSpace X]

/-- `∫ f² = ‖f‖²_{L²}` for `f ∈ L²`. -/
lemma integral_sq_eq_normSq {ν : Measure X} {f : X → ℝ} (hf : MemLp f 2 ν) :
    ∫ x, f x ^ 2 ∂ν = normSq ν 2 f := by
  unfold normSq
  rw [ENNReal.ofReal_ofNat, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have h0 : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂ν := integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h0 _), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

/-- An `L^{p*}` function is in `L²` on a finite measure (`p* ≥ 2`). -/
lemma memLp_two_of_pStar {N : ℕ} (hN : 3 ≤ N) {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℝ}
    (hf : MemLp f (ENNReal.ofReal (pStar N)) ν) : MemLp f 2 ν :=
  hf.mono_exponent (by
    rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal (two_le_pStar hN))

end Norms

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : CurvedMetric X N)

/-- The Einstein–Hilbert action with its Gibbons–Hawking–York term (eq:EH-action, l.306):
`𝒮(Σ, g) = ∫_Σ R_g vol + 2(N-1) ∫_{∂Σ} H_g bvol`. -/
def action : ℝ :=
  ∫ x, g.R x ∂(M.vol g.toFrameMetric) +
    2 * ((N : ℝ) - 1) * ∑ j, ∫ x, g.H x ∂(M.bvol g.toFrameMetric j)

/-- The Yamabe energy `EH(Σ, g) = 𝒮(Σ, g) / Vol(Σ, g)^{(N-2)/N}` (eq:yamabe-energy-bdry, l.311). -/
def EH : ℝ := M.action g / (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N)

/-- The right side of the conformal law eq:conformal-energy-bdry (l.327–328):
`a_N ‖∇u‖²_{L²} + ∫_Σ R_g u² vol + 2(N-1) ∫_{∂Σ} H_g u² bvol`. -/
def confAction (u : D) : ℝ :=
  aN N * M.dirichlet g.toFrameMetric u + ∫ x, g.R x * M.val u x ^ 2 ∂(M.vol g.toFrameMetric) +
    2 * ((N : ℝ) - 1) * ∑ j, ∫ x, g.H x * M.tr u x ^ 2 ∂(M.bvol g.toFrameMetric j)

/-- The conformal energy of `u`: `EH(Σ, u^{4/(N-2)} g)` through the conformal law
eq:conformal-energy-bdry, i.e. its right side over `‖u‖²_{L^{p*}(Σ, g)}`. -/
def confEnergy (u : D) : ℝ :=
  M.confAction g u / normSq (M.vol g.toFrameMetric) (pStar N) (M.val u)

/-- `H_g ≡ 0`: the boundary is minimal (l.615), read `bvol_j`-a.e. on every component. -/
def MinimalBoundary : Prop := ∀ j, ∀ᵐ x ∂(M.bvol g.toFrameMetric j), g.H x = 0

/-- `u > 0` on `Σ`: a conformal factor `φ > 0` of eq:relative-yamabe. -/
def Pos (u : D) : Prop := ∀ x, 0 < M.val u x

/-- The infimum of the conformal energy over the competitors of a set `S ⊆ D`. -/
def infConf (S : Set D) : ℝ :=
  sInf (M.confEnergy g '' {u | u ∈ S ∧ M.Adm g.toFrameMetric u})

/-- The relative Yamabe constant `Y_[g](Σ) = inf_{φ > 0} EH(Σ, φ^{4/(N-2)} g)`
(eq:relative-yamabe, l.318), through the conformal law. -/
def Y : ℝ := M.infConf g {u | M.Pos u}

/-! ### Basic facts -/

/-- "or `∂Σ = ∅`" (l.615): an empty boundary is minimal. -/
lemma minimalBoundary_of_bvol_eq_zero (h : ∀ j, M.bvol g.toFrameMetric j = 0) :
    M.MinimalBoundary g := by
  intro j
  rw [h j]
  exact ae_zero.le (by simp)

/-- The conformal law at `φ = 1` holds in the model: `EH(Σ, g) = confEnergy 1`. -/
theorem EH_eq_confEnergy_one (hN : 3 ≤ N) : M.EH g = M.confEnergy g M.one := by
  unfold EH confEnergy confAction action
  rw [M.dirichlet_one, M.val_one, M.tr_one, normSq_one _ (pStar_pos hN), two_div_pStar hN]
  simp only [one_pow, mul_one, mul_zero, zero_add]

/-- On a minimal boundary the boundary term of the conformal law vanishes (fact (i), l.332). -/
lemma confAction_of_minimal (hH : M.MinimalBoundary g) (u : D) :
    M.confAction g u = aN N * M.dirichlet g.toFrameMetric u +
      ∫ x, g.R x * M.val u x ^ 2 ∂(M.vol g.toFrameMetric) := by
  have hbd : ∑ j, ∫ x, g.H x * M.tr u x ^ 2 ∂(M.bvol g.toFrameMetric j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : (fun x => g.H x * M.tr u x ^ 2) =ᵐ[M.bvol g.toFrameMetric j] fun _ => (0 : ℝ) :=
      (hH j).mono fun x hx => by simp [hx]
    rw [integral_congr_ae h0, integral_zero]
  unfold confAction
  rw [hbd, mul_zero, add_zero]

/-- On a minimal boundary the action is `∫_Σ R_g vol`. -/
lemma action_of_minimal (hH : M.MinimalBoundary g) :
    M.action g = ∫ x, g.R x ∂(M.vol g.toFrameMetric) := by
  have hbd : ∑ j, ∫ x, g.H x ∂(M.bvol g.toFrameMetric j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_congr_ae (hH j), integral_zero]
  unfold action
  rw [hbd, mul_zero, add_zero]

/-- With `R_g` bounded and measurable, the scalar term of the conformal law is a genuine integral
for every `u ∈ L^{p*}` (no junk value). -/
lemma integrable_R_mul_sq (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)] (u : D)
    (hu : MemLp (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g.toFrameMetric)) :
    Integrable (fun x => g.R x * M.val u x ^ 2) (M.vol g.toFrameMetric) := by
  obtain ⟨C, hC⟩ := g.R_bdd
  exact (memLp_two_of_pStar hN hu).integrable_sq.bdd_mul g.R_measurable.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- With `H_g` bounded and measurable, the boundary term of the conformal law is a genuine
integral for every trace in `L^{p♯}(B_j)`. -/
lemma integrable_H_mul_sq (hN : 3 ≤ N) (j : Fin n) [IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (u : D) (hu : MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g.toFrameMetric j)) :
    Integrable (fun x => g.H x * M.tr u x ^ 2) (M.bvol g.toFrameMetric j) := by
  obtain ⟨C, hC⟩ := g.H_bdd
  have hu2 : MemLp (M.tr u) 2 (M.bvol g.toFrameMetric j) :=
    hu.mono_exponent (by
      rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal (two_le_pSharp hN))
  exact hu2.integrable_sq.bdd_mul g.H_measurable.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

/-! ### The bound eq:kobayashi -/

/-- The Hölder step of l.629–630: `∫_Σ R_g u² ≥ m Vol(Σ)^{2/N} ‖u‖²_{L^{p*}}` for `m ≤ 0` below
`R_g` a.e. and `u ∈ L^{p*}`. -/
theorem scalar_term_ge (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)] {m : ℝ}
    (hm : m ≤ 0) (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x) (u : D)
    (hu : MemLp (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g.toFrameMetric)) :
    m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) *
        normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) ≤
      ∫ x, g.R x * M.val u x ^ 2 ∂(M.vol g.toFrameMetric) := by
  set ν := M.vol g.toFrameMetric with hν
  have hu2 : MemLp (M.val u) 2 ν := memLp_two_of_pStar hN hu
  have hsq : Integrable (fun x => M.val u x ^ 2) ν := hu2.integrable_sq
  have hH := hoelder_interior hN hu
  have hint : ∫ x, M.val u x ^ 2 ∂ν = normSq ν 2 (M.val u) := integral_sq_eq_normSq hu2
  have hV0 : 0 ≤ (ν Set.univ).toReal ^ (2 / (N : ℝ)) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  by_cases hRi : Integrable (fun x => g.R x * M.val u x ^ 2) ν
  · calc m * (ν Set.univ).toReal ^ (2 / (N : ℝ)) * normSq ν (pStar N) (M.val u)
          = m * ((ν Set.univ).toReal ^ (2 / (N : ℝ)) * normSq ν (pStar N) (M.val u)) := by ring
      _ ≤ m * normSq ν 2 (M.val u) := mul_le_mul_of_nonpos_left hH hm
      _ = ∫ x, m * M.val u x ^ 2 ∂ν := by rw [integral_const_mul, hint]
      _ ≤ ∫ x, g.R x * M.val u x ^ 2 ∂ν :=
          integral_mono_ae (hsq.const_mul m) hRi
            (hmR.mono fun x hx => mul_le_mul_of_nonneg_right hx (sq_nonneg _))
  · rw [integral_undef hRi]
    have := mul_nonneg hV0 (normSq_nonneg ν (pStar N) (M.val u))
    nlinarith

/-- The displayed inequality of the proof (l.629–630), in product form, for `u ∈ L^{p*}`:
`a_N ‖∇u‖²_2 + m Vol(Σ)^{2/N} ‖u‖²_{p*} ≤ a_N ‖∇u‖²_2 + ∫_Σ R_g u² vol = confAction u`. -/
theorem confAction_ge (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hH : M.MinimalBoundary g) {m : ℝ} (hm : m ≤ 0)
    (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x) (u : D)
    (hu : MemLp (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g.toFrameMetric)) :
    aN N * M.dirichlet g.toFrameMetric u +
        m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) *
          normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) ≤
      M.confAction g u := by
  rw [M.confAction_of_minimal g hH u]
  linarith [M.scalar_term_ge g hN hm hmR u hu]

/-- eq:kobayashi (l.619–621), for every `m ≤ 0` with `m ≤ R_g` a.e. and every `u`. -/
theorem kobayashi (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hH : M.MinimalBoundary g) {m : ℝ} (hm : m ≤ 0)
    (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x) (u : D)
    (hu : AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric)) :
    aN N * M.dirichlet g.toFrameMetric u / normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) +
        m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      M.confEnergy g u := by
  set ν := M.vol g.toFrameMetric with hν
  have hV0 : 0 ≤ (ν Set.univ).toReal ^ (2 / (N : ℝ)) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  unfold confEnergy
  rw [M.confAction_of_minimal g hH u]
  rcases (normSq_nonneg ν (pStar N) (M.val u)).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, div_zero, zero_add]
    exact mul_nonpos_of_nonpos_of_nonneg hm hV0
  · have hmem : MemLp (M.val u) (ENNReal.ofReal (pStar N)) ν := by
      refine ⟨hu, lt_top_iff_ne_top.mpr fun htop => ?_⟩
      simp [normSq, htop] at hpos
    have key := M.scalar_term_ge g hN hm hmR u hmem
    rw [div_add' _ _ _ hpos.ne', div_le_div_iff_of_pos_right hpos]
    linarith

/-- eq:kobayashi with the printed `m = min(0, min_Σ R_g)`. -/
theorem kobayashi_printed (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hH : M.MinimalBoundary g) (u : D)
    (hu : AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric)) :
    aN N * M.dirichlet g.toFrameMetric u / normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) +
        g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      M.confEnergy g u :=
  M.kobayashi g hN hH g.kobM_nonpos (ae_of_all _ g.kobM_le) u hu

/-! ### "In particular" -/

/-- "Taking the infimum" (l.632), over any competitor set. -/
theorem le_infConf (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {m : ℝ} (hm : m ≤ 0)
    (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x) (S : Set D) :
    m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤ M.infConf g S := by
  refine Real.le_sInf ?_
    (mul_nonpos_of_nonpos_of_nonneg hm (Real.rpow_nonneg ENNReal.toReal_nonneg _))
  rintro _ ⟨u, -, rfl⟩
  have h := M.kobayashi g hN hH hm hmR u (hD u)
  have h0 : 0 ≤ aN N * M.dirichlet g.toFrameMetric u /
      normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) :=
    div_nonneg (mul_nonneg (aN_pos hN).le (M.dirichlet_nonneg _ u)) (normSq_nonneg _ _ _)
  linarith

/-- "in particular `Y_[g](Σ) ≥ m Vol(Σ)^{2/N}`" (l.622). -/
theorem le_Y (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {m : ℝ} (hm : m ≤ 0)
    (hmR : ∀ᵐ x ∂(M.vol g.toFrameMetric), m ≤ g.R x) :
    m * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤ M.Y g :=
  M.le_infConf g hN hD hH hm hmR _

/-- "in particular", with the printed `m`. -/
theorem le_Y_printed (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) :
    g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤ M.Y g :=
  M.le_Y g hN hD hH g.kobM_nonpos (ae_of_all _ g.kobM_le)

/-! ### Constant non-positive scalar curvature -/

/-- `R_g ≡ c` gives `EH(Σ, g) = c Vol(Σ)^{2/N}` (l.632), on a minimal boundary. -/
theorem EH_eq_const_mul (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hH : M.MinimalBoundary g) {c : ℝ} (hR : ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) :
    M.EH g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) := by
  set ν := M.vol g.toFrameMetric with hν
  have hN' := three_le_cast hN
  have hRint : ∫ x, g.R x ∂ν = c * (ν Set.univ).toReal := by
    rw [integral_congr_ae hR, integral_const, smul_eq_mul, measureReal_def, mul_comm]
  unfold EH
  rw [M.action_of_minimal g hH, hRint]
  rcases (ENNReal.toReal_nonneg : 0 ≤ (ν Set.univ).toReal).eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity : (2 : ℝ) / N ≠ 0)]
    simp
  · rw [mul_div_assoc]
    congr 1
    rw [div_eq_iff (Real.rpow_pos_of_pos hpos _).ne', ← Real.rpow_add hpos]
    have e : 2 / (N : ℝ) + ((N : ℝ) - 2) / N = 1 := by field_simp; ring
    rw [e, Real.rpow_one]

/-- `Y_[g](Σ) ≤ EH(Σ, g)`: the constant `1` is a competitor (l.632). -/
theorem Y_le_EH (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hV : M.vol g.toFrameMetric ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) : M.Y g ≤ M.EH g := by
  have hVpos : 0 < (M.vol g.toFrameMetric Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hadm : M.Adm g.toFrameMetric M.one := by
    unfold Adm
    rw [M.val_one, normSq_one _ (pStar_pos hN)]
    exact Real.rpow_pos_of_pos hVpos _
  have hpos1 : M.Pos M.one := fun x => by rw [M.val_one]; exact one_pos
  rw [M.EH_eq_confEnergy_one g hN]
  unfold Y infConf
  refine csInf_le ⟨g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)), ?_⟩
    ⟨M.one, ⟨hpos1, hadm⟩, rfl⟩
  rintro _ ⟨u, -, rfl⟩
  have h := M.kobayashi_printed g hN hH u (hD u)
  have h0 : 0 ≤ aN N * M.dirichlet g.toFrameMetric u /
      normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) :=
    div_nonneg (mul_nonneg (aN_pos hN).le (M.dirichlet_nonneg _ u)) (normSq_nonneg _ _ _)
  linarith

/-- "If `R_g` is constant and non-positive, then `EH(Σ, g) = Y_[g](Σ)`" (l.622). -/
theorem EH_eq_Y (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hc : c ≤ 0)
    (hR : ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) : M.EH g = M.Y g := by
  by_cases hV : M.vol g.toFrameMetric = 0
  · -- `Σ` of measure zero: no competitor, and both sides are `0`
    have hN' := three_le_cast hN
    have hEH : M.EH g = 0 := by
      rw [M.EH_eq_const_mul g hN hH hR, hV]
      simp [Real.zero_rpow (by positivity : (2 : ℝ) / N ≠ 0)]
    have hY : M.Y g = 0 := by
      unfold Y infConf
      have hempty : {u | u ∈ {u | M.Pos u} ∧ M.Adm g.toFrameMetric u} = ∅ := by
        ext u
        simp [Adm, normSq, hV]
      rw [hempty, Set.image_empty, Real.sInf_empty]
    rw [hEH, hY]
  · refine le_antisymm ?_ (M.Y_le_EH g hN hV hD hH)
    rw [M.EH_eq_const_mul g hN hH hR]
    exact M.le_Y g hN hD hH hc (hR.mono fun x hx => hx.ge)

/-- `Y_[g](Σ) = R_g Vol(Σ)^{2/N}` for constant `R_g ≤ 0` (as used at l.724). -/
theorem Y_eq_const_mul (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hc : c ≤ 0)
    (hR : ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) :
    M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) := by
  rw [← M.EH_eq_Y g hN hD hH hc hR, M.EH_eq_const_mul g hN hH hR]

/-! ### Assembly -/

/-- Assembly of lem:kobayashi (a) over the model (l.615–622, proof l.627–632). On a minimal
boundary (`H_g ≡ 0`, or `∂Σ = ∅`), with `m = min(0, min_Σ R_g)`:
(i) eq:kobayashi for every `u`; (ii) `Y_[g](Σ) ≥ m Vol(Σ)^{2/N}`; (iii) if `R_g ≡ c ≤ 0`
(a.e.), then `EH(Σ, g) = Y_[g](Σ) = c Vol(Σ)^{2/N}`. -/
theorem lem_kobayashi_a (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) :
    (∀ u : D, aN N * M.dirichlet g.toFrameMetric u /
          normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) +
        g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      M.confEnergy g u) ∧
    g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤ M.Y g ∧
    ∀ c : ℝ, c ≤ 0 → (∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) →
      M.EH g = M.Y g ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) :=
  ⟨fun u => M.kobayashi_printed g hN hH u (hD u), M.le_Y_printed g hN hD hH,
    fun _ hc hR => ⟨M.EH_eq_Y g hN hD hH hc hR, M.Y_eq_const_mul g hN hD hH hc hR⟩⟩

end MeasuredModel

/-! ## A witness: the toy model with `R ≡ -1` and a minimal boundary -/

section Toy

/-- The toy metric of `Yamabe.Quotient` with scalar curvature `-1` and minimal boundary. -/
def toyCurved : CurvedMetric Bool 3 where
  toFrameMetric := toyMetric
  R := fun _ => -1
  H := fun _ => 0
  R_measurable := measurable_const
  H_measurable := measurable_const
  R_bdd := ⟨1, fun _ => by norm_num⟩
  H_bdd := ⟨0, fun _ => by norm_num⟩

lemma toyCurved_toFrameMetric : toyCurved.toFrameMetric = toyMetric := rfl

/-- The printed `m` of the toy model: `min(0, min R) = -1`. -/
lemma toy_kobM : toyCurved.kobM = -1 := by
  simp [CurvedMetric.kobM, toyCurved]

lemma toy_minimal : toyModel.MinimalBoundary toyCurved := fun _ => ae_of_all _ fun _ => rfl

lemma toy_isFiniteMeasure : IsFiniteMeasure (toyModel.vol toyCurved.toFrameMetric) := by
  rw [toyCurved_toFrameMetric, toy_vol]; infer_instance

/-- `EH = -2^{2/3}` on the toy model (`Vol = 2`, `R ≡ -1`). -/
theorem toy_EH : toyModel.EH toyCurved = -(2 : ℝ) ^ ((2 : ℝ) / 3) := by
  haveI := toy_isFiniteMeasure
  rw [toyModel.EH_eq_const_mul toyCurved (le_refl 3) toy_minimal (c := -1)
    (ae_of_all _ fun _ => rfl), toyCurved_toFrameMetric, toy_vol]
  have h2 : (Measure.count (Set.univ : Set Bool)).toReal = 2 := by
    rw [Measure.count_apply_finite _ Set.finite_univ]
    simp
  rw [h2]
  norm_num

/-- Every hypothesis of `lem_kobayashi_a` and `EH_eq_Y` holds on the toy model, and
`EH = Y = -2^{2/3}` there: the hypotheses are jointly satisfiable and not degenerate. -/
theorem toy_EH_eq_Y :
    toyModel.EH toyCurved = toyModel.Y toyCurved ∧
      toyModel.Y toyCurved = -(2 : ℝ) ^ ((2 : ℝ) / 3) := by
  haveI := toy_isFiniteMeasure
  have hD : ∀ u, AEStronglyMeasurable (toyModel.val u) (toyModel.vol toyCurved.toFrameMetric) :=
    fun _ => (Measurable.of_discrete).aestronglyMeasurable
  have h := toyModel.EH_eq_Y toyCurved (le_refl 3) hD toy_minimal (c := -1) (by norm_num)
    (ae_of_all _ fun _ => rfl)
  exact ⟨h, by rw [← h]; exact toy_EH⟩

end Toy

end Yamabe
