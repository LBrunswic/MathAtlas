import Yamabe.BoundaryGap
import Yamabe.External
import Yamabe.ManifoldTheorems
import Yamabe.Negative

/-!
# Closed leaves: the Yamabe energy, constant and invariant, and constant scalar curvature

Labels (NOT marked: both rows are partial, see SCOPE):

* `def:yamabe` — `Yamabegap.tex:158` (l.158–172): the Yamabe energy eq:yamabe-energy in both printed
  forms, the Yamabe constant eq:yamabe-constant through the conformal law eq:conformal-energy
  (l.178), and the Yamabe invariant eq:yamabe-invariant through `ClosedConformal.sigma`, over the
  measured model with empty boundary (`n = 0`).
* `prop:csc-yamabe` — `Yamabegap.tex:193` (statement l.193–200, proof l.201–203): the first
  assertions of (a) and (b), as the closed case of lem:kobayashi (the paper's own step, l.202),
  over the model and over a model reading a closed manifold; the uniqueness in (a) carried as a
  cited input (Lee–Parker, Schoen), never an axiom; « the inequality may be strict » witnessed on a
  connected two-point model (not Schoen's example, which is cited and not formalized).

> \begin{definition}[Yamabe energy, Yamabe constant, Yamabe invariant]
> The \emph{Yamabe energy} of $(\Sigma,\g)$ is
> \EH(\Sigma,\g) := \frac{\int_{\Sigma}\Rs_{\g}\,\vol}{\Vol(\Sigma,\g)^{(N-2)/N}} = \langle\Rs_\g\rangle_\Sigma\,\Vol(\Sigma,\g)^{2/N}\ .
> The \emph{Yamabe constant} of the conformal class $[\g]$ and the \emph{Yamabe invariant} of $\Sigma$ are
> \Y(\Sigma,[\g]) := \inf_{\phi>0}\EH\big(\Sigma,\phi^{4/(N-2)}\g\big)\ ,\qquad
> \sigma(\Sigma) := \sup_{[\g]}\Y(\Sigma,[\g])\ ,
> the infimum being taken over smooth positive functions and the supremum over all conformal classes
> of Riemannian metrics on $\Sigma$. (l.158–172)

> \EH(\Sigma,\tilde\g) = \frac{\int_\Sigma\big(\aN|\nabla\phi|^2_\g + \Rs_\g\,\phi^2\big)\vol}{\|\phi\|^2_{L^{\pstar}(\Sigma,\g)}} (l.177–179)

> \begin{proposition}[Constant scalar curvature versus Yamabe metrics]
> Let $(\Sigma,\g)$ be closed, $N\ge3$, with constant scalar curvature $\Rs_\g$.
> (a) If $\Rs_\g\le 0$, then $\EH(\Sigma,\g)=\Y(\Sigma,[\g])$, i.e.\ $\g$ is a Yamabe metric, and
> $\g$ is, up to homotheties, the only constant scalar curvature metric in $[\g]$.
> (b) If $\Rs_\g>0$, then $\Y(\Sigma,[\g])>0$ and $\EH(\Sigma,\g)\ge\Y(\Sigma,[\g])$, where the
> inequality may be strict: the conformal class of the product metric on $\Sph^1(L)\times\Sph^{N-1}$
> contains, for $L$ large, constant scalar curvature metrics that are not Yamabe metrics. (l.193–200)

> The first assertion of (a) and the first assertion of (b) are the closed case of
> Lemma~\ref{lem:kobayashi} in Appendix~\ref{app:proofs}, cf.\ \cite[Lemma~1.6]{MR919505}. The
> uniqueness in (a) follows from the maximum principle applied to the Yamabe equation, see
> \cite{LeeParker1987,Schoen1989}; the examples in (b) are due to Schoen \cite{Schoen1989}. (l.202)

## What is proved (no `sorry`, standard axioms)

* def:yamabe: `closed_action` (no boundary term), `closedEH_eq_printed` (the first printed form),
  `closedEH_eq_avg` (the second, `⟨R_g⟩ Vol^{2/N}`, for every volume), `closed_confEnergy`
  (eq:conformal-energy, the closed conformal law's right side), `closed_EH_eq_confEnergy_one`;
  `yamabeClasses` (a closed model's conformal classes as a `ClosedConformal`), `sigma_yamabeClasses`
  (`σ = sup_C Y(Σ, C)`), `Y_le_sigma` (« Y ≤ σ by definition »);
* prop:csc-yamabe: `csc_yamabe_a` (EH = Y = c Vol^{2/N} for `R_g ≡ c ≤ 0`), `csc_yamabe_b` (from
  the Sobolev inequality), `prop_csc_yamabe` (the assembly, the uniqueness carried),
  `Mfd.Reads.csc_yamabe_b`, `Mfd.Reads.prop_csc_yamabe` (on a model reading a compact manifold:
  the Sobolev inequality discharged, sorry-free); `toyClosed_csc_not_yamabe`
  (« may be strict », connected two-point model, `R ≡ 100`);
* the uniqueness reading: `YamabeEq` (the weak Yamabe equation), `CSCUnique`;
  `toyClosed_cscUnique` (it holds on the connected two-point model with `R ≡ 0`) and
  `toyClosedCut_not_cscUnique` (it fails on the disconnected one, `R ≡ 0`: finding).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(Σ, g)` closed (compact, `∂Σ = ∅`), `N ≥ 3` (l.161) | ⚠ read in the measured model with `n = 0` boundary components (DEC-186); `N ≥ 3` ✓ carried; compact as `IsFiniteMeasure vol_g`; on a manifold: `CompactSpace`, `Reads` with `n = 0` |
| `Σ ≠ ∅` (a manifold of dimension `N`) | ✓ carried where used: `vol_g ≠ 0` (b), (`Y = 0` when `vol_g = 0`) |
| `R_g` constant | ✓ `∀ x, R_g x = c` (b); ⚠ weakened to `vol_g`-a.e. in (a) |
| `R_g ≤ 0` (a), `R_g > 0` (b) | ✓ `c ≤ 0`, `0 < c` |
| `EH(Σ, φ^{4/(N-2)} g)` for `φ > 0` | ⚠ read through the conformal law eq:conformal-energy (`confEnergy`, as `Yamabe.Kobayashi`) |
| « smooth positive functions » | ⚠ `Pos u` over the model's `D` (on a manifold reading: `C¹` functions) |
| « all conformal classes of Riemannian metrics on `Σ` » | ⚠ read: a family `rep : Cls → CurvedMetric X N` of representatives (SCOPE) |
| the Sobolev embedding (lem:kobayashi (b), l.637) | ✓ on a manifold reading, sorry-free (`Mfd.Reads.sobolevIneq`); ⚠ carried as `SobolevIneq` on a bare model |
| uniqueness up to homotheties (cited, LeeParker1987, Schoen1989) | ⚠ carried: `CSCUnique` (a named Prop, a hypothesis, not an axiom) |
| Schoen's `S¹(L) × S^{N-1}` (cited, Schoen1989) | ✗ not formalized; « may be strict » witnessed on the model |

## SCOPE (disclosed)

* **Model.** Everything is over the measured model of `Yamabe.Quotient` with `n = 0` (DEC-186,
  OQ-93): curvature is free data of `CurvedMetric`, and `EH(Σ, φ^{4/(N-2)} g)` is read through the
  conformal law (`confEnergy`), as in `Yamabe.Kobayashi`. With `n = 0`, `confEnergy` is the right
  side of the *closed* law eq:conformal-energy (`closed_confEnergy`).
* **σ(Σ).** The supremum over all conformal classes is not definable on the model (kb/0083: the
  curvature is free, so the supremum over all `CurvedMetric`s is unbounded and `Real.sSup` is junk
  `0`). It is read over a supplied family of class representatives `rep : Cls → CurvedMetric X N`
  (`yamabeClasses`, a `ClosedConformal`); `Y_le_sigma` asks the family's `Y` bounded above (thm:yamabe
  (a), Aubin's bound, is what bounds it; not formalized here).
* **Uniqueness (a).** A constant scalar curvature metric `h = u^{4/(N-2)} g` is read as a positive
  weak solution `u` of the Yamabe equation `a_N ⟨∇u, ∇v⟩ + ∫ R_g u v = c' ∫ u^{p*-1} v`
  for every `v ∈ D` (`YamabeEq`), with `⟨∇u, ∇v⟩` by polarisation of the Dirichlet energy; « up to
  homotheties » as `u` constant. `CSCUnique g` is the cited conclusion, carried.
  **Finding:** as printed (no connectedness) it fails for `R_g ≡ 0` on a disconnected closed `Σ`
  (`toyClosedCut_not_cscUnique`; on manifolds: `T³ ⊔ T³` flat, `u = 1` on one torus and `2` on the
  other gives a flat, non-homothetic metric in `[g]`). It holds on the connected two-point model
  (`toyClosed_cscUnique`).
* **(b), « may be strict ».** Schoen's `S¹(L) × S^{N-1}` (cited) has no counterpart in the model.
  The existence of a constant positive scalar curvature metric that is not a Yamabe metric is proved
  on the connected two-point model (`toyClosed_csc_not_yamabe`): a model fact, not Schoen's example.
* On a manifold reading, `Reads` with `n = 0` does not force `∂M = ∅` (the half-space charts may
  have boundary points); the conclusions hold for every such reading, hence for a closed `M`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N : ℕ}
variable (M : MeasuredModel X D N 0) (g : CurvedMetric X N)

/-! ## def:yamabe -/

/-- A closed model has a minimal (empty) boundary. -/
lemma closed_minimal : M.MinimalBoundary g := fun j => j.elim0

/-- The action of a closed leaf has no boundary term: `𝒮(Σ, g) = ∫_Σ R_g vol`. -/
lemma closed_action : M.action g = ∫ x, g.R x ∂(M.vol g.toFrameMetric) := by
  simp [action]

/-- eq:yamabe-energy (l.163), first form: `EH(Σ, g) = ∫_Σ R_g vol / Vol(Σ, g)^{(N-2)/N}`. -/
theorem closedEH_eq_printed :
    M.EH g = (∫ x, g.R x ∂(M.vol g.toFrameMetric)) /
      (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) := by
  unfold EH
  rw [M.closed_action g]

/-! The spatial average `⟨R_g⟩_Σ = ∫_Σ R_g vol / Vol(Σ, g)` (l.140) is `Yamabe.MeasuredModel.avgR`
of `Yamabe.BoundaryGap`, for any number of boundary components. -/

/-- eq:yamabe-energy (l.163), second form: `EH(Σ, g) = ⟨R_g⟩_Σ Vol(Σ, g)^{2/N}`, for every volume
(both sides are `0` when `Vol(Σ, g) = 0`). -/
theorem closedEH_eq_avg (hN : 3 ≤ N) :
    M.EH g = M.avgR g * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) := by
  have hN' := three_le_cast hN
  rw [M.closedEH_eq_printed g]
  unfold avgR
  have hV0 : 0 ≤ (M.vol g.toFrameMetric Set.univ).toReal := ENNReal.toReal_nonneg
  revert hV0
  generalize (M.vol g.toFrameMetric Set.univ).toReal = V
  generalize ∫ x, g.R x ∂(M.vol g.toFrameMetric) = I
  intro hV0
  rcases hV0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by
      have : (0 : ℝ) < ((N : ℝ) - 2) / N := div_pos (by linarith) (by linarith)
      exact this.ne')]
    simp
  · have e : V ^ (2 / (N : ℝ)) * V ^ (((N : ℝ) - 2) / N) = V := by
      rw [← Real.rpow_add hpos]
      have : 2 / (N : ℝ) + ((N : ℝ) - 2) / N = 1 := by field_simp; ring
      rw [this, Real.rpow_one]
    have h1 : 0 < V ^ (2 / (N : ℝ)) := Real.rpow_pos_of_pos hpos _
    have h2 : 0 < V ^ (((N : ℝ) - 2) / N) := Real.rpow_pos_of_pos hpos _
    generalize V ^ (2 / (N : ℝ)) = A at e h1
    generalize V ^ (((N : ℝ) - 2) / N) = B at e h2
    subst e
    field_simp

/-- eq:conformal-energy (l.177–179) on a closed leaf: the conformal energy is
`(∫_Σ a_N |∇u|² + R_g u²) / ‖u‖²_{L^{p*}}`. -/
theorem closed_confEnergy (u : D) :
    M.confEnergy g u = (aN N * M.dirichlet g.toFrameMetric u +
        ∫ x, g.R x * M.val u x ^ 2 ∂(M.vol g.toFrameMetric)) /
      normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) := by
  unfold confEnergy
  rw [M.confAction_of_minimal g (M.closed_minimal g)]

/-- The conformal law at `φ = 1` on a closed leaf. -/
theorem closed_EH_eq_confEnergy_one (hN : 3 ≤ N) : M.EH g = M.confEnergy g M.one :=
  M.EH_eq_confEnergy_one g hN

/-- The conformal classes of a closed model, read through a family of representatives
`rep : Cls → CurvedMetric X N`, as a `ClosedConformal`: `Y(Σ, C) = Y(Σ, [rep C])`, and `C` carries
a metric of positive scalar curvature as `psc C` (supplied: the model cannot decide it). -/
def yamabeClasses {Cls : Type} (rep : Cls → CurvedMetric X N) (psc : Cls → Prop) :
    ClosedConformal where
  Cls := Cls
  Y C := M.Y (rep C)
  PSC := psc

/-- eq:yamabe-invariant (l.170): `σ(Σ) = sup_{[g]} Y(Σ, [g])`, over the family. -/
theorem sigma_yamabeClasses {Cls : Type} (rep : Cls → CurvedMetric X N) (psc : Cls → Prop) :
    (M.yamabeClasses rep psc).sigma = ⨆ C, M.Y (rep C) := rfl

/-- « `Y(Σ, [g]) ≤ σ(Σ)` by definition » (as used at l.243), for a family bounded above. -/
theorem Y_le_sigma {Cls : Type} (rep : Cls → CurvedMetric X N) (psc : Cls → Prop)
    (hb : BddAbove (Set.range fun C => M.Y (rep C))) (C : Cls) :
    M.Y (rep C) ≤ (M.yamabeClasses rep psc).sigma := by
  exact le_ciSup hb C

/-! ## prop:csc-yamabe -/

/-- prop:csc-yamabe (a), first assertion (l.195), the closed case of lem:kobayashi (a): for
`R_g ≡ c ≤ 0`, `EH(Σ, g) = Y(Σ, [g]) = c Vol(Σ, g)^{2/N}`. -/
theorem csc_yamabe_a (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric)) {c : ℝ} (hc : c ≤ 0)
    (hR : ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) :
    M.EH g = M.Y g ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) := by
  exact (M.lem_kobayashi_a g hN hD (M.closed_minimal g)).2.2 c hc hR

/-- prop:csc-yamabe (b), first assertion (l.196), the closed case of lem:kobayashi (b): for
`R_g ≡ c > 0`, `Y(Σ, [g]) > 0` and `EH(Σ, g) ≥ Y(Σ, [g])`, from the Sobolev inequality. -/
theorem csc_yamabe_b (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hV : M.vol g.toFrameMetric ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hS : M.SobolevIneq g.toFrameMetric) {c : ℝ} (hc : 0 < c) (hR : ∀ x, g.R x = c) :
    0 < M.Y g ∧ M.Y g ≤ M.EH g := by
  have hne : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hV (Measure.eq_zero_of_isEmpty _)
  have hinf : (⨅ x, g.R x) = c := by simp only [hR, ciInf_const]
  refine ⟨M.kobayashiB_of_sobolev hN g hV hD (M.closed_minimal g) hS (by rw [hinf]; exact hc), ?_⟩
  exact M.Y_le_EH g hN hV hD (M.closed_minimal g)

/-! ### Uniqueness in (a): the reading of the cited input -/

/-- The Dirichlet form `⟨∇u, ∇v⟩_{L²(Σ, g)}`, by polarisation of `‖∇·‖²_{L²}`. -/
def dirichletBil (g : FrameMetric X N) (u v : D) : ℝ :=
  (M.dirichlet g (u + v) - M.dirichlet g (u - v)) / 4

/-- `h = u^{4/(N-2)} g` has constant scalar curvature `c'`: `u > 0` solves the Yamabe equation
`-a_N Δ_g u + R_g u = c' u^{p*-1}` weakly, against every `v ∈ D`. -/
def YamabeEq (u : D) (c' : ℝ) : Prop :=
  M.Pos u ∧ ∀ v : D, aN N * M.dirichletBil g.toFrameMetric u v +
      ∫ x, g.R x * M.val u x * M.val v x ∂(M.vol g.toFrameMetric) =
    c' * ∫ x, M.val u x ^ (pStar N - 1) * M.val v x ∂(M.vol g.toFrameMetric)

/-- prop:csc-yamabe (a), second assertion (l.195), the cited input (LeeParker1987, Schoen1989):
`g` is, up to homotheties, the only constant scalar curvature metric of `[g]`: every positive
solution of the Yamabe equation is constant. A named Prop, carried, never an axiom. -/
def CSCUnique : Prop := ∀ (u : D) (c' : ℝ), M.YamabeEq g u c' → ∃ l : ℝ, 0 < l ∧ M.val u = fun _ => l

/-- prop:csc-yamabe, the first assertions of (a) and (b) (the paper's own step, l.202), with the
uniqueness in (a) carried (`hU`, the cited input). -/
theorem prop_csc_yamabe (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hV : M.vol g.toFrameMetric ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hS : M.SobolevIneq g.toFrameMetric) {c : ℝ} (hR : ∀ x, g.R x = c)
    (hU : c ≤ 0 → M.CSCUnique g) :
    (c ≤ 0 → M.EH g = M.Y g ∧ M.CSCUnique g) ∧ (0 < c → 0 < M.Y g ∧ M.Y g ≤ M.EH g) := by
  refine ⟨fun hc => ⟨(M.csc_yamabe_a g hN hD hc (ae_of_all _ hR)).1, hU hc⟩, fun hc => ?_⟩
  exact M.csc_yamabe_b g hN hV hD hS hc hR

end MeasuredModel

/-! ## On a model reading a compact manifold: the Sobolev inequality discharged -/

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

namespace Reads

variable {D : Type*} [AddCommGroup D] [Module ℝ D] {Mm : MeasuredModel M D N 0}
  {g : RiemannianMetric N M} {μ : Measure M} {σ : Fin 0 → Measure M}

/-- prop:csc-yamabe (b), first assertion, on a model reading a compact manifold (no boundary
component): `R_g ≡ c > 0` gives `Y(Σ, [g]) > 0` and `EH(Σ, g) ≥ Y(Σ, [g])`, sorry-free. -/
theorem csc_yamabe_b (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    {gc : CurvedMetric M N} (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hV : μ ≠ 0) {c : ℝ} (hc : 0 < c) (hR : ∀ x, gc.R x = c) :
    0 < Mm.Y gc ∧ Mm.Y gc ≤ Mm.EH gc := by
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  exact Mm.csc_yamabe_b gc hN (by rw [hr.vol_eq]; exact hV) hr.hD (hr.sobolevIneq hN hμ) hc hR

/-- prop:csc-yamabe, the first assertions of (a) and (b), on a model reading a compact manifold,
with the uniqueness in (a) carried (`hU`). -/
theorem prop_csc_yamabe (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    {gc : CurvedMetric M N} (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hV : μ ≠ 0) {c : ℝ} (hR : ∀ x, gc.R x = c) (hU : c ≤ 0 → Mm.CSCUnique gc) :
    (c ≤ 0 → Mm.EH gc = Mm.Y gc ∧ Mm.CSCUnique gc) ∧
      (0 < c → 0 < Mm.Y gc ∧ Mm.Y gc ≤ Mm.EH gc) := by
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  exact Mm.prop_csc_yamabe gc hN (by rw [hr.vol_eq]; exact hV) hr.hD (hr.sobolevIneq hN hμ) hR hU

end Reads

end Mfd

/-! ## Witnesses on the closed two-point models -/

section Toy

lemma toyClosed_integral (c : ℝ) (f : Bool → ℝ) :
    ∫ x, f x ∂(toyClosed.vol (toyConst c).toFrameMetric) = f true + f false := by
  rw [toyConst_toFrameMetric, toyClosed_vol, integral_fintype]
  · simp [Measure.real]
  · exact .of_finite

lemma toyClosed_dirichlet (c : ℝ) (u : Bool → ℝ) :
    toyClosed.dirichlet (toyConst c).toFrameMetric u = 2 * (u true - u false) ^ 2 :=
  toy_dirichlet u

lemma toyClosed_normSq (c : ℝ) (u : Bool → ℝ) :
    normSq (toyClosed.vol (toyConst c).toFrameMetric) (pStar 3) u =
      ((u true ^ 2) ^ 3 + (u false ^ 2) ^ 3) ^ (2 / (6 : ℝ)) :=
  toy_normSq_vol_eq u

lemma six_fifths_le_two_rpow : (6 / 5 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  have h : ((6 / 5 : ℝ) ^ (3 : ℕ)) ^ ((3 : ℕ)⁻¹ : ℝ) ≤ ((2 : ℝ) ^ (2 : ℕ)) ^ ((3 : ℕ)⁻¹ : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by norm_num) (by positivity)
  rw [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)] at h
  convert h using 2
  norm_num

/-- The closed two-point model with the differential `0`: two points cut apart, a disconnected
closed `Σ`. -/
def toyClosedCut : MeasuredModel Bool (Bool → ℝ) 3 0 :=
  { toyClosed with d := 0, d_one := rfl }

/-- « The inequality may be strict » (l.196), on the model: on the connected closed two-point
model, `R_g ≡ 100` (constant, positive) and `Y(Σ, [g]) < EH(Σ, g)`: `g` is not a Yamabe metric. -/
theorem toyClosed_csc_not_yamabe :
    (∀ x, (toyConst 100).R x = 100) ∧ toyClosed.Y (toyConst 100) < toyClosed.EH (toyConst 100) := by
  refine ⟨fun _ => rfl, ?_⟩
  set u : Bool → ℝ := fun b => if b then 1 else 1 / 10 with hu
  have hval : ∀ w : Bool → ℝ, toyClosed.val w = w := fun _ => rfl
  have hEH : toyClosed.EH (toyConst 100) = 100 * (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    haveI : IsFiniteMeasure (toyClosed.vol (toyConst 100).toFrameMetric) := by
      show IsFiniteMeasure (toyClosed.vol toyMetric); rw [toyClosed_vol]; infer_instance
    rw [toyClosed.EH_eq_const_mul (toyConst 100) (le_refl 3) (toyClosed.closed_minimal _)
      (c := 100) (ae_of_all _ fun _ => rfl), toyConst_toFrameMetric, toyClosed_vol, toy_count_univ]
    norm_num
  have hden : 1 ≤ normSq (toyClosed.vol (toyConst 100).toFrameMetric) (pStar 3) (toyClosed.val u) := by
    rw [hval, toyClosed_normSq]
    exact Real.one_le_rpow (by simp [hu]) (by norm_num)
  have hnum : toyClosed.confAction (toyConst 100) u ≤ 114 := by
    rw [toyClosed.confAction_of_minimal _ (toyClosed.closed_minimal _), toyClosed_dirichlet,
      toyClosed_integral, aN_three]
    simp [hu, toyConst, hval]
    norm_num
  have hnn : 0 ≤ toyClosed.confAction (toyConst 100) u := by
    rw [toyClosed.confAction_of_minimal _ (toyClosed.closed_minimal _), toyClosed_dirichlet,
      toyClosed_integral, aN_three]
    simp [hu, toyConst, hval]
    norm_num
  have hE : toyClosed.confEnergy (toyConst 100) u ≤ 114 := by
    unfold MeasuredModel.confEnergy
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hbdd : BddBelow (toyClosed.confEnergy (toyConst 100) ''
      {w | w ∈ {w | toyClosed.Pos w} ∧ toyClosed.Adm (toyConst 100).toFrameMetric w}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, -, rfl⟩
    unfold MeasuredModel.confEnergy
    refine div_nonneg ?_ (normSq_nonneg _ _ _)
    rw [toyClosed.confAction_of_minimal _ (toyClosed.closed_minimal _), toyClosed_integral]
    have := toyClosed.dirichlet_nonneg (toyConst 100).toFrameMetric w
    have ha := aN_pos (le_refl 3)
    simp only [toyConst, hval]
    positivity
  have hY : toyClosed.Y (toyConst 100) ≤ toyClosed.confEnergy (toyConst 100) u := by
    unfold MeasuredModel.Y MeasuredModel.infConf
    refine csInf_le hbdd ⟨u, ⟨fun b => ?_, ?_⟩, rfl⟩
    · rw [hval]; cases b <;> simp [hu]
    · unfold MeasuredModel.Adm; linarith
  have h2 := six_fifths_le_two_rpow
  rw [hEH]
  linarith

/-- The uniqueness in (a) holds on the connected closed two-point model with `R_g ≡ 0`: the
carried input `CSCUnique` is satisfiable, and not vacuously. -/
theorem toyClosed_cscUnique : toyClosed.CSCUnique (toyConst 0) := by
  intro u c' ⟨hpos, heq⟩
  have hval : ∀ w : Bool → ℝ, toyClosed.val w = w := fun _ => rfl
  have hbil : ∀ v : Bool → ℝ, toyClosed.dirichletBil (toyConst 0).toFrameMetric u v =
      2 * (u true - u false) * (v true - v false) := by
    intro v
    unfold MeasuredModel.dirichletBil
    rw [toyClosed_dirichlet, toyClosed_dirichlet]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have h1 := heq (fun _ => 1)
  rw [hbil, toyClosed_integral, toyClosed_integral] at h1
  simp only [hval, toyConst, sub_self, mul_zero, zero_mul, add_zero, mul_one] at h1
  have hp : 0 < u true ^ (pStar 3 - 1) + u false ^ (pStar 3 - 1) := by
    have := hpos true; have := hpos false; rw [hval] at *
    positivity
  have hc : c' = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · linarith
  have h2 := heq (fun b => if b then 1 else 0)
  rw [hbil, toyClosed_integral, toyClosed_integral, hc] at h2
  simp only [hval, toyConst, zero_mul, add_zero, if_true, mul_one] at h2
  simp at h2
  rw [aN_three] at h2
  refine ⟨u true, by have := hpos true; rwa [hval] at this, ?_⟩
  funext b
  cases b
  · simp only [hval]
    rcases h2 with h | h
    · norm_num at h
    · linarith
  · rfl

/-- **Finding** (l.195): the uniqueness in (a) fails as printed on a disconnected closed `Σ` with
`R_g ≡ 0`: on the cut two-point model, `u = (2, 1)` solves the Yamabe equation with `c' = 0` and is
not constant. -/
theorem toyClosedCut_not_cscUnique : ¬ toyClosedCut.CSCUnique (toyConst 0) := by
  intro h
  set u : Bool → ℝ := fun b => if b then 2 else 1 with hu
  have hval : ∀ w : Bool → ℝ, toyClosedCut.val w = w := fun _ => rfl
  have hd : ∀ w, toyClosedCut.dirichlet (toyConst 0).toFrameMetric w = 0 := by
    intro w
    simp [MeasuredModel.dirichlet, MeasuredModel.gradSq, toyClosedCut]
  have hY : toyClosedCut.YamabeEq (toyConst 0) u 0 := by
    refine ⟨fun b => by rw [hval]; cases b <;> simp [hu], fun v => ?_⟩
    have e1 := hd (u + v)
    have e2 := hd (u - v)
    rw [toyConst_toFrameMetric] at e1 e2
    simp [MeasuredModel.dirichletBil, e1, e2, toyConst]
  obtain ⟨l, -, hl⟩ := h u 0 hY
  have h1 := congrFun hl true
  have h2 := congrFun hl false
  rw [hval] at h1 h2
  simp [hu] at h1 h2
  linarith

end Toy

end Yamabe
