import Yamabe.Kobayashi
import Yamabe.Gluing
import Yamabe.LowerBound

/-!
# Yamabe § 3, leaves with boundary: the definitions, the gap's sign and the acceleration law

Labels (lines of `papers/yamabe/legacy/labeled/Yamabegap.tex`). NOT marked: every row is partial
(the model's readings, see SCOPE).

* `def:yamabe-bdry` — `Yamabegap.tex:301` (l.301–322): `𝒮`, `EH`, `EHB`, `Y_[g]`, `YB_[g]` over
  the measured model, from the strict `Yamabe.MeasuredModel.action`, `EH`, `EHB`, `Y`, `YB`; the
  printed infima eq:relative-yamabe and eq:boundary-yamabe recovered through the conformal law.
* `prop:gap-bdry-nonneg` — `Yamabegap.tex:356` (statement l.356–359, proof l.360–362): `δ ≥ 0`
  for constant `R_g ≤ 0` and minimal boundary, from fact (iii) = lem:kobayashi (a) and
  eq:sigma-bdry (l.346–348).
* `prop:accel-bdry` — `Yamabegap.tex:407` (statement l.407–415, proof Appendix A, l.584–599):
  eq:accel-bdry, its punctured-torus form and its non-minimal form, from the averaged acceleration
  law eq:accel (l.140–144; Buchert_2007, brunswic2020gaussbonnetchern) carried as a hypothesis.

> Let $\mathcal{S}(\Sigma,\g):=\int_{\Sigma}\Rs_\g\,\vol+2(N-1)\int_{\partial \Sigma}H_\g\,\bvol$
> be the Einstein--Hilbert action with its Gibbons--Hawking--York boundary term. The \emph{Yamabe
> energy} of $(\Sigma,\g)$ and its \emph{boundary-normalized} version are
> $\EH(\Sigma,\g) := \frac{\mathcal{S}(\Sigma,\g)}{\Vol(\Sigma,\g)^{(N-2)/N}}$ ,
> $\EHB(\Sigma,\g) := \frac{\mathcal{S}(\Sigma,\g)}{\Vol(\partial\Sigma,\g)^{(N-2)/(N-1)}}$ ,
> and the \emph{relative Yamabe constant} and \emph{boundary Yamabe constant} of the conformal
> class $[\g]$ are
> $\Y_{[\g]}(\Sigma) := \inf_{\phi>0}\EH\big(\Sigma,\phi^{4/(N-2)}\g\big)$ ,
> $\YB_{[\g]}(\Sigma) := \inf_{\phi>0}\EHB\big(\Sigma,\phi^{4/(N-2)}\g\big)$ . (l.303–321)

> If $\g$ has constant scalar curvature, minimal boundary and $\Rs_\g\le0$, then
> $\delta(\Sigma,\g)\ge0$. (l.358)
> By fact (iii) of Sec.~\ref{sec:boundary}, $\EH(\Sigma,\g)=\Y_{[\g]}(\Sigma)$, and
> $\Y_{[\g]}(\Sigma)\le\sigbd(\Sigma)$ by \eqref{eq:sigma-bdry}. (l.361)

> $\sigbd(\Sigma):=\sup_{[\g]}\,\Y_{[\g]}(\Sigma)$ [...]
> $\delta(\Sigma,\g):=\sigbd(\Sigma)-\EH(\Sigma,\g)$ . (l.346–353)

> Let $\Sigma_t$ carry a metric $\g_t$ with minimal boundary, $H_{\g_t}\equiv0$, and let
> $\delta(\Sigma_t)=\sigbd(\Sigma)-\EH(\Sigma_t,\g_t)$ be the Yamabe gap \eqref{eq:gap-bdry}. Then
> $\frac{\partial_{tt} (a^N)}{a^N} = \frac{N}{N-1}\, \frac{\inirho}{a^N} + \frac{2N}{N-1}\Lambda
> + \frac{\delta(\Sigma_t)-\sigbd(\Sigma)}{\ini V^{2/N}a^2}$ .
> For a punctured flat torus, $\sigbd(\Sigma)=0$ by \eqref{eq:sigma-torus} and the last term is
> $\delta(\Sigma_t)/(\ini V^{2/N}a^2)$. If the boundary is not minimal, the right-hand side
> acquires the further term $2(N-1)\int_{\partial\Sigma}H_{\g_t}\bvol/(\ini V a^N)$. (l.409–414)

> We prove Proposition~\ref{prop:accel-bdry}. Write $V:=\Vol(\Sigma_t,\g_t)=a^N\ini V$ and omit
> the index $t$. By \eqref{eq:yamabe-energy-bdry},
> $\langle\Rs\rangle_\Sigma=\frac{1}{V}\int_\Sigma\Rs\,\vol=\frac{\EH(\Sigma,\g)}{V^{2/N}}
> -\frac{2(N-1)}{V}\int_{\partial\Sigma}H_\g\,\bvol$ .
> For a minimal boundary the last term vanishes, so that $\langle\Rs\rangle_\Sigma=\EH(\Sigma,\g)/V^{2/N}$.
> Inserting $\EH(\Sigma,\g)=\sigbd(\Sigma)-\delta$ and $V^{2/N}=\ini V^{2/N}a^2$,
> $\langle\Rs\rangle_\Sigma=\frac{\sigbd(\Sigma)-\delta(\Sigma_t)}{\ini V^{2/N}a^2}$ ,
> and substituting into \eqref{eq:accel} gives \eqref{eq:accel-bdry}. If $H_\g\not\equiv0$ the
> discarded term reappears as $2(N-1)\int_{\partial\Sigma}H_\g\bvol/(\ini V a^N)$. (l.588–594)

> $\frac{\partial_{tt} (a^N)}{a^N} = \frac{N}{N-1}\, \frac{\inirho}{a^N} + \frac{2N}{N-1}\Lambda
> - \langle \Rs_{\g_t} \rangle_{\Sigma_t}$ [...] with $\inirho := \langle\varrho\rangle_{\Sigma_{\ini t}}$.
> (eq:accel, l.141–144); $a(t) := \left[\Vol(\Sigma_t)/\Vol(\Sigma_{\ini t})\right]^{1/N}$ (l.137)

## The model

`Σ` is a `MeasuredModel` `M`, a metric a `CurvedMetric` `g` (`Yamabe.Kobayashi`): `𝒮 = action`,
`EH`, `EHB` (`Yamabe.Gluing`), `Y` and `YB` are the strict library's, the last two the infima of
the conformal energies `confEnergy`, `confEnergyB` (the right side of eq:conformal-energy-bdry over
`‖u‖²_{L^{p*}}`, resp. `‖u‖²_{L^{p♯}(∂Σ)}`) over the positive competitors. New here:

* `sigmaBdry C` — eq:sigma-bdry as the supremum, in `EReal`, of `Y_[g']` over a set `C` of metrics
  (the metrics of `Σ`: the model cannot define them, kb/0083), and `gapBdryE C g = σ^∂ − EH` in
  `EReal` (eq:gap-bdry, no finiteness assumed);
* `avgR g` — `⟨R_g⟩_Σ = ∫_Σ R_g vol / Vol(Σ, g)`; `scale g ti t` — `a(t)`; `AccelLaw` — eq:accel
  for a family `t ↦ g t` of metrics on the comoving `Σ`, at the parameters `ρ_i`, `Λ`, `t_i`.

## What is proved (no `sorry`)

def:yamabe-bdry: `action_def`, `EH_def`, `EHB_def` (the printed formulas, `rfl`);
`EH_mul_vol_eq_action`, `EHB_mul_bdryVol_eq_action` (both normalisations of one `𝒮`);
`Y_eq_inf_EH`, `YB_eq_inf_EHB` (eq:relative-yamabe and eq:boundary-yamabe as printed, the infimum of
`EH`, resp. `EHB`, of the conformal metrics `φ^{4/(N-2)} g`, through the conformal law).
prop:gap-bdry-nonneg: `Y_le_sigmaBdry`, `prop_gap_bdry_nonneg` (`0 ≤ δ` in `EReal`),
`prop_gap_bdry_nonneg_real` (`0 ≤ gapBdry σb g` for a real `σb ≥ Y_[g]`, in particular for
`σb = sSup` of a bounded set), witness `toy_prop_gap_bdry_nonneg`.
prop:accel-bdry: `avgR_eq` (Appendix A's first display, any boundary), `avgR_of_minimal`,
`vol_rpow_eq` (`V^{2/N} = V_i^{2/N} a²`, used in Appendix A's second display),
`prop_accel_bdry` (eq:accel-bdry, the torus form, the non-minimal form).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(Σ, g)` compact Riemannian, `N ≥ 3`, `∂Σ = ⊔ B_j` (l.298) | ⚠ read in the measured model (DEC-139, OQ-44); `N ≥ 3` ✓ carried; compactness as `IsFiniteMeasure (vol_g)` |
| `R_g`, `H_g` the curvatures of `g` | ⚠ read: free bounded measurable data of `CurvedMetric` |
| `EH(Σ, φ^{4/(N-2)} g)` in eq:relative-yamabe | ⚠ read through the conformal law (cited, MR1152225, MR1173925): `Y_eq_inf_EH` carries, for a family `φ ↦ h_φ` with `h_φ.G = φ^{4/(N-2)} g.G` (`IsConformal`), `ConformalLaw g φ h_φ` |
| `φ > 0` | ⚠ read: `Pos φ` and `0 < ‖φ‖_{L^{p*}} < ∞` (`Adm`), resp. on `∂Σ` (`AdmB`) |
| prop:gap-bdry-nonneg: `R_g` constant `≤ 0` | ✓ carried, weakened to `R_g = c` `vol_g`-a.e., `c ≤ 0` |
| minimal boundary `H_g ≡ 0` | ✓ carried, `bvol_g`-a.e. (`MinimalBoundary`) |
| `σ^∂(Σ) = sup_{[g]} Y_[g](Σ)` | ⚠ read: `⨆ g' ∈ C, Y_[g']` in `EReal` over a parameter set `C` of metrics with `g ∈ C` |
| `D ⊆ W^{1,2}(Σ)` measurable | ⚠ read: `∀ u, AEStronglyMeasurable (val u)` (as `lem_kobayashi_a`) |
| prop:accel-bdry: eq:accel (cited, Buchert_2007, brunswic2020gaussbonnetchern) | ⚠ carried at `t` (dispatch): `AccelLaw` |
| `Σ_t`, `g_t`: a comoving family | ⚠ read: one model `M`, a family `g : ℝ → CurvedMetric X N` |
| `Vol(Σ_t), Vol(Σ_{t_i}) > 0` (for `a`, `⟨·⟩` to make sense) | ✓ carried: `vol_{g t} ≠ 0`, `vol_{g t_i} ≠ 0`, finite |
| `H_{g_t} ≡ 0` | ✓ carried at `t` only |
| `σ^∂(Σ)` finite | ⚠ read: a real `σb`; the identity holds for every value (kb/0085); the torus form carries `σb = 0` |

## SCOPE (disclosed)

* Abstract layer, as the strict library (DEC-139): `R`, `H` are data, so a supremum over all
  `CurvedMetric`s is not the paper's `σ^∂` (kb/0083); `C` is a parameter, and `g ∈ C` is the
  reading of "`g` is a metric on `Σ`". In `EReal` no boundedness is needed: `σ^∂ = +∞` gives
  `δ = +∞ ≥ 0`.
* The conformal law is not proved in the model (no second derivatives): `Y`, `YB` are the strict
  library's infima of conformal energies; `Y_eq_inf_EH` and `YB_eq_inf_EHB` show that, given the
  law for each competitor, they are the printed infima of `EH`, `EHB` of the conformal metrics.
* eq:accel is a cited result about the Einstein flow, which the model does not carry: it is the
  hypothesis `AccelLaw` at the time `t` considered. `∂_tt` is `deriv (deriv …)`; the conclusion is
  the algebra of Appendix A and holds whatever value `deriv` takes. `ρ_i` and `Λ` are real
  parameters (the matter is not in the model).
* eq:sigma-torus (`σ^∂ = 0` for a punctured flat torus, l.366–369) is not this target's label: the
  torus form carries `σb = 0` (kb/0085).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Yamabe

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-! ## 1. def:yamabe-bdry -/

/-- eq:EH-action (l.305–306), as printed. -/
theorem action_def (g : CurvedMetric X N) :
    M.action g = ∫ x, g.R x ∂(M.vol g.toFrameMetric) +
      2 * ((N : ℝ) - 1) * ∑ j, ∫ x, g.H x ∂(M.bvol g.toFrameMetric j) := rfl

/-- eq:yamabe-energy-bdry (l.310–311), as printed. -/
theorem EH_def (g : CurvedMetric X N) :
    M.EH g = M.action g / (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) := rfl

/-- eq:yamabe-energy-bdry-norm (l.312–313), as printed, `Vol(∂Σ, g) = Σ_j Vol(B_j, g)`. -/
theorem EHB_def (g : CurvedMetric X N) :
    M.EHB g = M.action g /
      (∑ j, (M.bvol g.toFrameMetric j Set.univ).toReal) ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) := rfl

/-- `EH(Σ, g) Vol(Σ)^{(N-2)/N} = 𝒮(Σ, g)` when `Vol(Σ, g) > 0`. -/
theorem EH_mul_vol_eq_action (g : CurvedMetric X N)
    (hV : 0 < (M.vol g.toFrameMetric Set.univ).toReal) :
    M.EH g * (M.vol g.toFrameMetric Set.univ).toReal ^ (((N : ℝ) - 2) / N) = M.action g := by
  unfold EH
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hV _).ne'

/-- `EHB(Σ, g) Vol(∂Σ)^{(N-2)/(N-1)} = 𝒮(Σ, g)` when `Vol(∂Σ, g) > 0`. -/
theorem EHB_mul_bdryVol_eq_action (g : CurvedMetric X N)
    (hA : 0 < M.bdryVol g.toFrameMetric) :
    M.EHB g * M.bdryVol g.toFrameMetric ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) = M.action g := by
  unfold EHB
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hA _).ne'

/-- eq:relative-yamabe as printed (l.316–318): `Y_[g](Σ) = inf_{φ > 0} EH(Σ, φ^{4/(N-2)} g)`, for
any family `φ ↦ h φ` of metrics conformal to `g` (`h φ = φ^{4/(N-2)} g`) carrying the conformal law
eq:conformal-energy-bdry (cited). -/
theorem Y_eq_inf_EH (g : CurvedMetric X N) (h : D → CurvedMetric X N)
    (hlaw : ∀ φ, M.Pos φ → M.Adm g.toFrameMetric φ →
      M.IsConformal g.toFrameMetric (h φ).toFrameMetric φ ∧ M.ConformalLaw g φ (h φ)) :
    M.Y g = sInf ((fun φ => M.EH (h φ)) '' {φ | M.Pos φ ∧ M.Adm g.toFrameMetric φ}) := by
  unfold Y infConf
  congr 1
  refine Set.image_congr fun φ hφ => ?_
  obtain ⟨hpos, hadm⟩ := hφ
  have hl := (hlaw φ hpos hadm).2
  unfold ConformalLaw at hl
  unfold confEnergy
  rw [← hl, mul_div_assoc, div_self (ne_of_gt hadm), mul_one]

/-- eq:boundary-yamabe as printed (l.319–320): `YB_[g](Σ) = inf_{φ > 0} EHB(Σ, φ^{4/(N-2)} g)`,
through the boundary form of the conformal law (l.330). -/
theorem YB_eq_inf_EHB (g : CurvedMetric X N) (h : D → CurvedMetric X N)
    (hlaw : ∀ φ, M.Pos φ → M.AdmB g.toFrameMetric φ →
      M.IsConformal g.toFrameMetric (h φ).toFrameMetric φ ∧ M.ConformalLawB g φ (h φ)) :
    M.YB g = sInf ((fun φ => M.EHB (h φ)) '' {φ | M.Pos φ ∧ M.AdmB g.toFrameMetric φ}) := by
  unfold YB
  congr 1
  refine Set.image_congr fun φ hφ => ?_
  obtain ⟨hpos, hadm⟩ := hφ
  have hl := (hlaw φ hpos hadm).2
  unfold ConformalLawB at hl
  unfold confEnergyB
  rw [← hl, mul_div_assoc, div_self (ne_of_gt hadm), mul_one]

/-! ## 2. prop:gap-bdry-nonneg -/

/-- eq:sigma-bdry (l.346–348): `σ^∂(Σ) = sup_{[g]} Y_[g](Σ)`, in `EReal`, over a set `C` of
metrics of `Σ` (a parameter: kb/0083). -/
def sigmaBdry (C : Set (CurvedMetric X N)) : EReal := ⨆ g ∈ C, (M.Y g : EReal)

/-- eq:gap-bdry (l.352–353) in `EReal`: `δ(Σ, g) = σ^∂(Σ) − EH(Σ, g)`. -/
def gapBdryE (C : Set (CurvedMetric X N)) (g : CurvedMetric X N) : EReal :=
  M.sigmaBdry C - (M.EH g : EReal)

/-- "`Y_[g](Σ) ≤ σ^∂(Σ)` by eq:sigma-bdry" (l.361). -/
theorem Y_le_sigmaBdry {C : Set (CurvedMetric X N)} {g : CurvedMetric X N} (hg : g ∈ C) :
    (M.Y g : EReal) ≤ M.sigmaBdry C := by
  unfold sigmaBdry
  exact le_iSup₂_of_le g hg le_rfl

/-- prop:gap-bdry-nonneg (partial, unmarked) over the model (l.356–362): if `g` has constant scalar curvature
`c ≤ 0` and minimal boundary, then `δ(Σ, g) ≥ 0`, with `σ^∂` the supremum over any set of metrics
containing `g`. -/
theorem prop_gap_bdry_nonneg (hN : 3 ≤ N) {C : Set (CurvedMetric X N)} {g : CurvedMetric X N}
    (hg : g ∈ C) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hc : c ≤ 0)
    (hR : ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) :
    0 ≤ M.gapBdryE C g := by
  unfold gapBdryE
  rw [EReal.sub_nonneg (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _)),
    M.EH_eq_Y g hN hD hH hc hR]
  exact M.Y_le_sigmaBdry hg

/-- The real form: `0 ≤ δ = σb − EH(Σ, g)` for every real `σb ≥ Y_[g](Σ)` (the only property of
the supremum the proof uses), in particular `σb = sSup (Y '' C)` for a bounded `C ∋ g`. -/
theorem prop_gap_bdry_nonneg_real (hN : 3 ≤ N) {g : CurvedMetric X N}
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hc : c ≤ 0)
    (hR : ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) {σb : ℝ} (hσ : M.Y g ≤ σb) :
    0 ≤ M.gapBdry σb g := by
  unfold gapBdry
  rw [M.EH_eq_Y g hN hD hH hc hR]
  linarith

/-! ## 3. prop:accel-bdry -/

/-- The spatial average `⟨R_g⟩_Σ = ∫_Σ R_g vol / Vol(Σ, g)` (l.137). -/
def avgR (g : CurvedMetric X N) : ℝ :=
  (∫ x, g.R x ∂(M.vol g.toFrameMetric)) / (M.vol g.toFrameMetric Set.univ).toReal

/-- The volume scale factor `a(t) = [Vol(Σ_t)/Vol(Σ_{t_i})]^{1/N}` (l.137). -/
def scale (g : ℝ → CurvedMetric X N) (ti t : ℝ) : ℝ :=
  ((M.vol (g t).toFrameMetric Set.univ).toReal / (M.vol (g ti).toFrameMetric Set.univ).toReal) ^
    (1 / (N : ℝ))

/-- The averaged acceleration law eq:accel (l.141–144; cited: Buchert_2007,
brunswic2020gaussbonnetchern) at time `t`, for the family `g`, initial time `t_i`, initial mean
density `ρ_i` and cosmological constant `Λ`. -/
def AccelLaw (g : ℝ → CurvedMetric X N) (ti ρi Λ t : ℝ) : Prop :=
  deriv (deriv fun s => M.scale g ti s ^ N) t / M.scale g ti t ^ N =
    (N : ℝ) / ((N : ℝ) - 1) * (ρi / M.scale g ti t ^ N) + 2 * (N : ℝ) / ((N : ℝ) - 1) * Λ -
      M.avgR (g t)

/-- On a minimal boundary the boundary integral `Σ_j ∫_{B_j} H_g bvol` vanishes. -/
theorem sum_H_of_minimal (g : CurvedMetric X N) (hH : M.MinimalBoundary g) :
    ∑ j, ∫ x, g.H x ∂(M.bvol g.toFrameMetric j) = 0 :=
  Finset.sum_eq_zero fun j _ => by rw [integral_congr_ae (hH j), integral_zero]

/-- Appendix A's first display (l.589–590), any boundary: `⟨R⟩_Σ = EH/V^{2/N} − 2(N−1)/V ∫ H`. -/
theorem avgR_eq (hN : 3 ≤ N) (g : CurvedMetric X N)
    (hV : 0 < (M.vol g.toFrameMetric Set.univ).toReal) :
    M.avgR g = M.EH g / (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) -
      2 * ((N : ℝ) - 1) / (M.vol g.toFrameMetric Set.univ).toReal *
        ∑ j, ∫ x, g.H x ∂(M.bvol g.toFrameMetric j) := by
  have hN' := three_le_cast hN
  set V := (M.vol g.toFrameMetric Set.univ).toReal with hVdef
  have hsplit : V ^ (((N : ℝ) - 2) / N) * V ^ (2 / (N : ℝ)) = V := by
    rw [← Real.rpow_add hV]
    have e : ((N : ℝ) - 2) / N + 2 / (N : ℝ) = 1 := by field_simp; ring
    rw [e, Real.rpow_one]
  have hp1 : 0 < V ^ (((N : ℝ) - 2) / N) := Real.rpow_pos_of_pos hV _
  have hp2 : 0 < V ^ (2 / (N : ℝ)) := Real.rpow_pos_of_pos hV _
  unfold avgR EH action
  rw [← hVdef, div_div, hsplit]
  field_simp
  ring

/-- "For a minimal boundary … `⟨R⟩_Σ = EH(Σ, g)/V^{2/N}`" (l.591). -/
theorem avgR_of_minimal (hN : 3 ≤ N) (g : CurvedMetric X N) (hH : M.MinimalBoundary g)
    (hV : 0 < (M.vol g.toFrameMetric Set.univ).toReal) :
    M.avgR g = M.EH g / (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) := by
  rw [M.avgR_eq hN g hV, M.sum_H_of_minimal g hH, mul_zero, sub_zero]

/-- `V = a^N V_i` and `V^{2/N} = V_i^{2/N} a²` (l.588, l.592). -/
theorem vol_rpow_eq (hN : 3 ≤ N) (g : ℝ → CurvedMetric X N) (ti t : ℝ)
    (hVt : 0 < (M.vol (g t).toFrameMetric Set.univ).toReal)
    (hVi : 0 < (M.vol (g ti).toFrameMetric Set.univ).toReal) :
    (M.vol (g t).toFrameMetric Set.univ).toReal =
        M.scale g ti t ^ N * (M.vol (g ti).toFrameMetric Set.univ).toReal ∧
      (M.vol (g t).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) =
        (M.vol (g ti).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) * M.scale g ti t ^ 2 := by
  have hN' := three_le_cast hN
  set Vt := (M.vol (g t).toFrameMetric Set.univ).toReal
  set Vi := (M.vol (g ti).toFrameMetric Set.univ).toReal
  have hq : 0 ≤ Vt / Vi := (div_pos hVt hVi).le
  have hNpos : (0 : ℝ) < N := by linarith
  have haN : M.scale g ti t ^ N = Vt / Vi := by
    unfold scale
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq, one_div_mul_cancel hNpos.ne', Real.rpow_one]
  have ha2 : M.scale g ti t ^ 2 = (Vt / Vi) ^ (2 / (N : ℝ)) := by
    unfold scale
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
    congr 1
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [haN]; field_simp
  · rw [ha2, ← Real.mul_rpow hVi.le hq]
    congr 1
    field_simp

/-- prop:accel-bdry (partial, unmarked) over the model (l.407–415, Appendix A l.584–594), eq:accel carried at `t`:
(1) with `H_{g_t} ≡ 0`, eq:accel-bdry for every value `σb` of `σ^∂(Σ)`; (2) for `σb = 0` (a
punctured flat torus, eq:sigma-torus) the last term is `δ/(V_i^{2/N} a²)`; (3) with any boundary,
the right side acquires `2(N−1) ∫_{∂Σ} H_{g_t} bvol/(V_i a^N)`. -/
theorem prop_accel_bdry (hN : 3 ≤ N) (g : ℝ → CurvedMetric X N) (ti ρi Λ t : ℝ)
    (hVt : 0 < (M.vol (g t).toFrameMetric Set.univ).toReal)
    (hVi : 0 < (M.vol (g ti).toFrameMetric Set.univ).toReal)
    (hacc : M.AccelLaw g ti ρi Λ t) :
    (M.MinimalBoundary (g t) → ∀ σb : ℝ,
      deriv (deriv fun s => M.scale g ti s ^ N) t / M.scale g ti t ^ N =
        (N : ℝ) / ((N : ℝ) - 1) * (ρi / M.scale g ti t ^ N) + 2 * (N : ℝ) / ((N : ℝ) - 1) * Λ +
          (M.gapBdry σb (g t) - σb) /
            ((M.vol (g ti).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) * M.scale g ti t ^ 2)) ∧
    (M.MinimalBoundary (g t) → ∀ σb : ℝ, σb = 0 →
      deriv (deriv fun s => M.scale g ti s ^ N) t / M.scale g ti t ^ N =
        (N : ℝ) / ((N : ℝ) - 1) * (ρi / M.scale g ti t ^ N) + 2 * (N : ℝ) / ((N : ℝ) - 1) * Λ +
          M.gapBdry σb (g t) /
            ((M.vol (g ti).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) * M.scale g ti t ^ 2)) ∧
    (∀ σb : ℝ,
      deriv (deriv fun s => M.scale g ti s ^ N) t / M.scale g ti t ^ N =
        (N : ℝ) / ((N : ℝ) - 1) * (ρi / M.scale g ti t ^ N) + 2 * (N : ℝ) / ((N : ℝ) - 1) * Λ +
          (M.gapBdry σb (g t) - σb) /
            ((M.vol (g ti).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) * M.scale g ti t ^ 2) +
          2 * ((N : ℝ) - 1) * (∑ j, ∫ x, (g t).H x ∂(M.bvol (g t).toFrameMetric j)) /
            ((M.vol (g ti).toFrameMetric Set.univ).toReal * M.scale g ti t ^ N)) := by
  have hN' := three_le_cast hN
  obtain ⟨hV1, hV2⟩ := M.vol_rpow_eq hN g ti t hVt hVi
  have hav := M.avgR_eq hN (g t) hVt
  unfold AccelLaw at hacc
  rw [hav, hV2, hV1] at hacc
  have hmain : ∀ σb : ℝ,
      deriv (deriv fun s => M.scale g ti s ^ N) t / M.scale g ti t ^ N =
        (N : ℝ) / ((N : ℝ) - 1) * (ρi / M.scale g ti t ^ N) + 2 * (N : ℝ) / ((N : ℝ) - 1) * Λ +
          (M.gapBdry σb (g t) - σb) /
            ((M.vol (g ti).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) * M.scale g ti t ^ 2) +
          2 * ((N : ℝ) - 1) * (∑ j, ∫ x, (g t).H x ∂(M.bvol (g t).toFrameMetric j)) /
            ((M.vol (g ti).toFrameMetric Set.univ).toReal * M.scale g ti t ^ N) := by
    intro σb
    rw [hacc]
    unfold gapBdry
    ring
  refine ⟨fun hH σb => ?_, fun hH σb hσ => ?_, hmain⟩
  · rw [hmain σb, M.sum_H_of_minimal (g t) hH]
    ring
  · rw [hmain σb, M.sum_H_of_minimal (g t) hH, hσ]
    ring

end MeasuredModel

/-! ## 4. A witness for prop:gap-bdry-nonneg -/

/-- On the toy model (`R ≡ −1`, minimal boundary), every hypothesis of `prop_gap_bdry_nonneg`
holds with `C = {toyCurved}`, and there `δ = 0` (`σ^∂ = Y = EH`). -/
theorem toy_prop_gap_bdry_nonneg :
    toyModel.gapBdryE {toyCurved} toyCurved = 0 := by
  unfold MeasuredModel.gapBdryE MeasuredModel.sigmaBdry
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
  rw [← toy_EH_eq_Y.1, ← EReal.coe_sub, sub_self, EReal.coe_zero]

end Yamabe
