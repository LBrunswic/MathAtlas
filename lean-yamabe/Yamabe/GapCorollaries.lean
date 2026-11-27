import Yamabe.ClosedLeaves

/-!
# Yamabe § 2, the corollaries of the Yamabe gap on a closed leaf: sign, rigidity, volume

Labels (lines of `papers/yamabe/legacy/labeled/Yamabegap.tex`). NOT marked: both rows are partial
(the model's readings and the carried cited inputs, see SCOPE).

* `cor:gap-nonneg` — `Yamabegap.tex:234` (statement l.234–241, proof l.242–244): (a) `δ ≥ 0`,
  `δ = 0` iff `g_t` attains `σ(Σ)`, the automatic `σ(Σ) ≤ 0` for `R_{g_t} ≡ c ≤ 0`, and then
  Einstein (thm:extremal (a), carried) and constant curvature at `N = 3` (carried); (b) `k` is the
  scalar curvature of the constant-curvature leaf rescaled to volume `V_i`, `−k/a²` is the FLRW
  curvature term, and `δ/(V_i^{2/N} a²)` is the deviation of `⟨R_{g_t}⟩` from its FLRW value
  (thm:extremal (b), carried), with eq:accel-gap (l.226–232) from eq:accel.
* `cor:volume` — `Yamabegap.tex:246` (statement l.246–249, proof l.250–257): `Vol(Σ, g) ≥
  Vol(Σ, g_hyp)` at equal constant scalar curvature `c < 0`, with equality iff `g` is isometric to
  `g_hyp` (thm:extremal (a)/(b), the three-dimensional Einstein fact and Mostow rigidity, carried).

> \begin{corollary}[Non-negativity and rigidity of the Yamabe gap]
> Assume that the leaf $(\Sigma_t,\g_t)$ is closed, has constant scalar curvature $\Rs_{\g_t}\le 0$,
> or more generally that $\g_t$ is a Yamabe metric. Then:
> (a) $\delta(\Sigma_t)\ge 0$, and $\delta(\Sigma_t)=0$ if and only if $\g_t$ attains the Yamabe
> invariant; in that case, if $\sigma(\Sigma)\le0$ (which is automatic when $\Rs_{\g_t}\le0$),
> $\g_t$ is Einstein, hence of constant curvature when $N=3$, i.e.\ an FLRW leaf.
> (b) If $\Sigma$ is diffeomorphic to a closed hyperbolic $3$-manifold, a closed flat manifold,
> $\Sph^N$ or $\RR\mathrm{P}^3$, then $-k/a^2$ in \eqref{eq:accel-gap} is exactly the curvature
> term of the FLRW model whose leaf at time $\ini t$ has constant curvature and volume $\ini V$, and
> the Yamabe gap is the full deviation of the averaged scalar curvature from its Friedmannian value.
> \end{corollary} (l.234–241)

> (a) If $\g_t$ is a Yamabe metric then $\EH(\Sigma_t,\g_t)=\Y(\Sigma,[\g_t])\le\sigma(\Sigma)$ by
> definition; if $\Rs_{\g_t}\le0$ is constant, $\g_t$ is a Yamabe metric by
> Proposition~\ref{prop:csc-yamabe}(a). Equality $\delta=0$ means $\Y(\Sigma,[\g_t])=\sigma(\Sigma)$;
> if $\Rs_{\g_t}\le 0$ then $\sigma(\Sigma)=\EH(\Sigma_t,\g_t)\le0$ and
> Theorem~\ref{thm:extremal}(a) applies. In dimension three Einstein metrics have constant sectional
> curvature. (b) By Theorem~\ref{thm:extremal}(b), $\sigma(\Sigma)=\Rs_{\g_0}\Vol(\Sigma,\g_0)^{2/N}$
> for the constant-curvature metric $\g_0$; rescaling $\g_0$ to volume $\ini V$ gives $k=\Rs_{\g_0}$,
> and the FLRW curvature term is $\Rs_{\g_0}/a^2$. (l.242–244)

> \delta(\Sigma_t) := \sigma(\Sigma)-\EH(\Sigma_t,\g_t)\ ,\qquad k:=\frac{\sigma(\Sigma)}{\ini V^{2/N}}
> [...] \frac{\partial_{tt} (a^N)}{a^N} = \frac{N}{N-1}\, \frac{\inirho}{a^N} + \frac{2N}{N-1}\Lambda
> - \frac{k}{a^2} + \frac{\delta(\Sigma_t)}{\ini V^{2/N}a^2}\ . (eq:gap-def, eq:accel-gap, l.226–232)

> \begin{corollary}[Volume comparison]
> Let $\Sigma$ be a closed hyperbolic $3$-manifold with hyperbolic metric $\g_{\mathrm{hyp}}$, and let
> $\g$ be a metric on $\Sigma$ of constant scalar curvature $\Rs_\g=\Rs_{\g_{\mathrm{hyp}}}<0$. Then
> $\Vol(\Sigma,\g)\ge\Vol(\Sigma,\g_{\mathrm{hyp}})$, with equality if and only if $\g$ is isometric
> to $\g_{\mathrm{hyp}}$.
> \end{corollary} (l.246–249)

> By Proposition~\ref{prop:csc-yamabe}(a) and Theorem~\ref{thm:extremal}(b),
> \Rs_\g\Vol(\Sigma,\g)^{2/3}=\Y(\Sigma,[\g])\le\sigma(\Sigma)
> =\Rs_{\g_{\mathrm{hyp}}}\Vol(\Sigma,\g_{\mathrm{hyp}})^{2/3}\ .
> Dividing by the negative constant $\Rs_\g=\Rs_{\g_{\mathrm{hyp}}}$ reverses the inequality.
> Equality forces $\g$ to attain $\sigma(\Sigma)<0$, hence to be Einstein by
> Theorem~\ref{thm:extremal}(a), i.e.\ hyperbolic, and Mostow rigidity gives the isometry. (l.251–256)

## What is proved (no `sorry`, standard axioms)

* homotheties on the model: `CurvedMetric.homothety` (`G ↦ l G`, `R ↦ R/l`, `H ↦ H/√l`: the
  scaling laws, as data), `CurvedMetric.homothety_R`, `vol_homothety` (`vol_{lg} = l^{N/2} vol_g`),
  `volReal_homothety`, `integral_R_homothety`, `avgR_homothety` (`⟨R_{lg}⟩ = ⟨R_g⟩/l`),
  `closedEH_homothety` (« the Yamabe energy is invariant under homotheties », l.174, closed leaf);
* the carried inputs, named Props: `ExtremalA` (thm:extremal (a)), `EinsteinConstCurv3` (l.243),
  `MostowAt` (l.256); thm:extremal (b) is the hypothesis `hB` of `cor_gap_nonneg_b`, `cor_volume`;
* cor:gap-nonneg (a): `gapNonneg_core` (over any real `σ ≥ Y(Σ, [g])`), `cor_gap_nonneg_a` (over
  the family's `σ(Σ)`, `ClosedLeaves.yamabeClasses`);
* cor:gap-nonneg (b): `gapNonneg_k` (eq:gap-def's `k`), `accel_gap` (eq:accel-gap from eq:accel),
  `cor_gap_nonneg_b`;
* cor:volume: `cor_volume`;
* witnesses: `toyClosed_gapCor_finite`, `toyClosed_gapCor_sigma`, `toyClosed_gap_nonneg_witness`
  (on the connected closed two-point model with `R ≡ −1` and a one-class family, `cor_gap_nonneg_a`
  applies with `δ = 0`, and thm:extremal (b)'s carried value holds at `g_0 = toyConst (−1)`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the leaf `(Σ_t, g_t)` closed, `N ≥ 3` | ⚠ read in the measured model with `n = 0` (DEC-186, kb/0088); `3 ≤ N` ✓; compact as `IsFiniteMeasure vol_g` |
| `R_{g_t}` constant `≤ 0`, or `g_t` a Yamabe metric | ✓ `(∃ c ≤ 0, R = c vol_g-a.e.) ∨ EH(g) = Y(g)` (a Yamabe metric: « a minimizing metric », l.190, i.e. `φ = 1` attains `Y`) |
| `σ(Σ)` | ⚠ OQ-132 (b): over a supplied family `rep` of class representatives (`yamabeClasses`), bounded above (Aubin's bound, thm:yamabe (a), carried as `hb`); `[g_t]` a class of the family: `M.Y (rep C₀) = M.Y g` |
| (none: added) | ⚠ strengthened: `hD`, every `M.val u` a.e. strongly measurable for `vol_g` (as `lem_kobayashi_a`); and `hb`, `hC₀`, `hIsoVol` above, carried |
| Σ connected | not assumed (OQ-132 (a)): no step of this file needs it; Mostow's carried form does, see SCOPE |
| thm:extremal (a) (Schoen1989, MR867684, Anderson2005) | ⚠ carried: `ExtremalA σ Einstein g`, at the metric where it is invoked (kb/0018); `Einstein` a supplied predicate (no Ricci tensor on the model) |
| « in dimension three Einstein metrics have constant sectional curvature » (l.243) | ⚠ carried: `EinsteinConstCurv3 Einstein ConstCurv g` (no curvature tensor on the model) |
| thm:extremal (b) (MR2213687, MR569070, MR448404, Obata1971, BrayNeves2004, MR2081443) | ⚠ carried: `σ = R_{g_0} Vol(g_0)^{2/N}` for a metric `g_0` with `R_{g_0}` constant; the diffeomorphism type of `Σ` has no counterpart in the model |
| eq:accel (Buchert_2007, brunswic2020gaussbonnetchern) | ⚠ carried at `t`: `AccelLaw` (as `Yamabe.BoundaryGap`) |
| cor:volume: `g_hyp` hyperbolic, `R_g = R_{g_hyp} = c < 0` constant | ✓ `∀ x, g.R x = c`, `∀ x, g_hyp.R x = c`, `c < 0`; « hyperbolic » ⚠ carried as `ConstCurv g_hyp` |
| Mostow rigidity (l.256) | ⚠ carried: `MostowAt ConstCurv Isometric g g_hyp`; `Isometric` a supplied relation, with « isometric metrics have equal volume » carried (`hIsoVol`) |

## SCOPE (disclosed)

* **Model.** Over the measured model with no boundary component, as `Yamabe.ClosedLeaves`
  (DEC-186, OQ-93, OQ-132). `R` is free data of `CurvedMetric`; Ricci, sectional curvature,
  isometries and the diffeomorphism type of `Σ` have no counterpart. So « Einstein », « constant
  (sectional) curvature » and « isometric » are supplied predicates, and the cited facts about them
  (thm:extremal (a), the three-dimensional fact, Mostow) are carried hypotheses at the metrics where
  the paper invokes them, never axioms. Their content on the model is only what the hypotheses
  say: with `Einstein := fun _ => True` every such conclusion is trivial (kb/0095); the
  corollary's own steps are the inequality chains, the automatic `σ ≤ 0`, the rescaling and the
  FLRW identities, which are proved.
* **σ(Σ)** (OQ-132 (b)): `(M.yamabeClasses rep psc).sigma`, the supremum of `Y` over a supplied
  family, bounded above (`hb`: Aubin's bound, not formalized). `gapNonneg_core` needs only
  `Y(Σ, [g]) ≤ σ`.
* **δ, k.** `δ(Σ_t) = σ − EH(Σ_t, g_t)` is the strict `MeasuredModel.gapBdry σ g` (with `n = 0` it
  is the closed gap eq:gap-def); `k = σ/V_i^{2/N}` is `gapNonneg_k`.
* **« g_t attains the Yamabe invariant »**: read as `EH(g_t) = Y(Σ, [g_t]) ∧ Y(Σ, [g_t]) = σ`
  (`g_t` a Yamabe metric realising `σ`, thm:extremal (a)'s phrasing); under the corollary's
  hypothesis this is `EH(g_t) = σ` (also proved).
* **Homotheties and rescaling (b).** A homothety `l g` is built on the model with the scaling laws
  of the curvature data (`R_{lg} = R_g/l`, `H_{lg} = H_g/√l`) as its definition: the model cannot
  derive them. The FLRW model of (b) is the family `t ↦ a(t)² g_0'`, `g_0'` the rescaling of `g_0`
  to volume `V_i`; « constant curvature » of `g_0'` is read through its constant scalar curvature
  (the model has no sectional curvature). `−k/a²` is the FLRW leaf's `−⟨R⟩`, the curvature term of
  eq:accel.
* **Connectedness** (OQ-132 (a)). Nothing proved here uses it; the carried Mostow input is true for
  closed hyperbolic 3-manifolds with the same constant curvature, componentwise, so `cor_volume`
  takes no connectedness hypothesis.
* **cor:volume, « σ(Σ) < 0 »** (l.255): the proof uses only `σ ≤ 0` (for thm:extremal (a)).
  « Isometric to `g_hyp` » ⇒ equal volumes (the converse half of « equality iff ») is not argued in
  the paper; it is the carried `hIsoVol`.
* **« k = R_{g_0} »** (l.244) holds for the *rescaled* metric `g_0' = (V_i/Vol(g_0))^{2/N} g_0`,
  which the proof keeps calling `g_0`; for `g_0` itself `k = R_{g_0} (Vol(g_0)/V_i)^{2/N}`.
  `cor_gap_nonneg_b` states it for `g_0'` (a notational finding, no correction of substance).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace Yamabe

/-! ## Homotheties on the model -/

namespace CurvedMetric

variable {X : Type*} [MeasurableSpace X] {N : ℕ}

/-- The homothety `l g` (`l > 0`): Gram matrix `l G`, with the scaling laws of the curvature data,
`R_{lg} = R_g / l` and `H_{lg} = H_g / √l`, as its definition (the model cannot derive them). -/
def homothety (l : ℝ) (hl : 0 < l) (g : CurvedMetric X N) : CurvedMetric X N where
  G x := l • g.G x
  posDef x := (g.posDef x).smul hl
  R x := g.R x / l
  H x := g.H x / Real.sqrt l
  R_measurable := g.R_measurable.div_const l
  H_measurable := g.H_measurable.div_const _
  R_bdd := by
    obtain ⟨C, hC⟩ := g.R_bdd
    refine ⟨C / l, fun x => ?_⟩
    rw [abs_div, abs_of_pos hl]
    exact div_le_div_of_nonneg_right (hC x) hl.le
  H_bdd := by
    obtain ⟨C, hC⟩ := g.H_bdd
    have hs : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
    refine ⟨C / Real.sqrt l, fun x => ?_⟩
    rw [abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (hC x) hs.le

lemma homothety_R (l : ℝ) (hl : 0 < l) (g : CurvedMetric X N) (x : X) :
    (g.homothety l hl).R x = g.R x / l := rfl

end CurvedMetric

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}

section Homothety

variable (M : MeasuredModel X D N n)

/-- `vol_{l g} = l^{N/2} vol_g`. -/
theorem vol_homothety (g : CurvedMetric X N) (l : ℝ) (hl : 0 < l) :
    M.vol (g.homothety l hl).toFrameMetric =
      ENNReal.ofReal (l ^ ((N : ℝ) / 2)) • M.vol g.toFrameMetric := by
  unfold vol
  have h : (fun x => ENNReal.ofReal (Real.sqrt ((g.homothety l hl).G x).det)) =
      ENNReal.ofReal (l ^ ((N : ℝ) / 2)) • fun x => ENNReal.ofReal (Real.sqrt (g.G x).det) := by
    funext x
    show ENNReal.ofReal (Real.sqrt (l • g.G x).det) = _
    rw [sqrt_det_smul hl.le, Fintype.card_fin, ENNReal.ofReal_mul (Real.rpow_nonneg hl.le _)]
    rfl
  rw [h, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

/-- `Vol(Σ, l g) = l^{N/2} Vol(Σ, g)`. -/
theorem volReal_homothety (g : CurvedMetric X N) (l : ℝ) (hl : 0 < l) :
    (M.vol (g.homothety l hl).toFrameMetric Set.univ).toReal =
      l ^ ((N : ℝ) / 2) * (M.vol g.toFrameMetric Set.univ).toReal := by
  rw [M.vol_homothety g l hl, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hl.le _)]

/-- `∫_Σ R_{lg} vol_{lg} = l^{N/2} / l · ∫_Σ R_g vol_g`. -/
theorem integral_R_homothety (g : CurvedMetric X N) (l : ℝ) (hl : 0 < l) :
    ∫ x, (g.homothety l hl).R x ∂(M.vol (g.homothety l hl).toFrameMetric) =
      l ^ ((N : ℝ) / 2) / l * ∫ x, g.R x ∂(M.vol g.toFrameMetric) := by
  rw [M.vol_homothety g l hl, integral_smul_measure, ENNReal.toReal_ofReal (Real.rpow_nonneg hl.le _)]
  simp only [CurvedMetric.homothety_R, smul_eq_mul]
  rw [integral_div]
  ring

/-- `⟨R_{lg}⟩_Σ = ⟨R_g⟩_Σ / l`. -/
theorem avgR_homothety (g : CurvedMetric X N) (l : ℝ) (hl : 0 < l) :
    M.avgR (g.homothety l hl) = M.avgR g / l := by
  unfold avgR
  rw [M.integral_R_homothety g l hl, M.volReal_homothety g l hl]
  have hA : 0 < l ^ ((N : ℝ) / 2) := Real.rpow_pos_of_pos hl _
  rcases eq_or_ne (M.vol g.toFrameMetric Set.univ).toReal 0 with h0 | h0
  · rw [h0]; simp
  · field_simp

end Homothety

section Closed

variable (M : MeasuredModel X D N 0)

/-- « The Yamabe energy is invariant under homotheties » (l.174), on a closed leaf. -/
theorem closedEH_homothety (hN : 3 ≤ N) (g : CurvedMetric X N) (l : ℝ) (hl : 0 < l) :
    M.EH (g.homothety l hl) = M.EH g := by
  have hN' := three_le_cast hN
  unfold EH
  rw [M.closed_action, M.closed_action, M.integral_R_homothety g l hl, M.volReal_homothety g l hl,
    Real.mul_rpow (Real.rpow_nonneg hl.le _) ENNReal.toReal_nonneg, ← Real.rpow_mul hl.le]
  have e1 : l ^ ((N : ℝ) / 2) / l = l ^ ((N : ℝ) / 2 * (((N : ℝ) - 2) / N)) := by
    rw [← Real.rpow_sub_one hl.ne']
    congr 1
    field_simp
  rw [e1, mul_div_mul_left _ _ (Real.rpow_pos_of_pos hl _).ne']

/-! ## cor:gap-nonneg (a) -/

/-- thm:extremal (a) (l.209–210; Schoen1989, MR867684, Anderson2005), carried at the metric `h`
where it is invoked, in the branch the corollary uses: a Yamabe metric `h` with
`Y(Σ, [h]) = σ(Σ) ≤ 0` is Einstein. `Einstein` is supplied (the model has no Ricci tensor). A named
Prop, a hypothesis, never an axiom. -/
def ExtremalA (σ : ℝ) (Einstein : CurvedMetric X N → Prop) (h : CurvedMetric X N) : Prop :=
  M.EH h = M.Y h → M.Y h = σ → σ ≤ 0 → Einstein h

/-- « In dimension three Einstein metrics have constant sectional curvature » (l.243), carried at
`h` (the model has no curvature tensor). -/
def EinsteinConstCurv3 (Einstein ConstCurv : CurvedMetric X N → Prop) (h : CurvedMetric X N) :
    Prop :=
  N = 3 → Einstein h → ConstCurv h

/-- cor:gap-nonneg (a) over any real `σ` with `Y(Σ, [g]) ≤ σ` (the only property of the Yamabe
invariant the proof uses): under « `R_g ≡ c ≤ 0`, or more generally `g` a Yamabe metric »,
`δ ≥ 0`; `δ = 0` iff `g` is a Yamabe metric realising `σ`, iff `EH(g) = σ`; when `R_g ≡ c ≤ 0`,
`δ = 0` forces `σ ≤ 0`; and `δ = 0`, `σ ≤ 0` give Einstein, then constant curvature at `N = 3`. -/
theorem gapNonneg_core (hN : 3 ≤ N) (g : CurvedMetric X N) {σ : ℝ} (hYσ : M.Y g ≤ σ)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hg : (∃ c ≤ 0, ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) ∨ M.EH g = M.Y g)
    (Einstein ConstCurv : CurvedMetric X N → Prop)
    (hA : M.ExtremalA σ Einstein g) (h3 : EinsteinConstCurv3 Einstein ConstCurv g) :
    0 ≤ M.gapBdry σ g ∧
    (M.gapBdry σ g = 0 ↔ M.EH g = M.Y g ∧ M.Y g = σ) ∧
    (M.gapBdry σ g = 0 ↔ M.EH g = σ) ∧
    (M.gapBdry σ g = 0 → (∃ c ≤ 0, ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) → σ ≤ 0) ∧
    (M.gapBdry σ g = 0 → σ ≤ 0 → Einstein g ∧ (N = 3 → ConstCurv g)) := by
  have hYam : M.EH g = M.Y g := by
    rcases hg with ⟨c, hc, hR⟩ | h
    · exact (M.csc_yamabe_a g hN hD hc hR).1
    · exact h
  simp only [gapBdry]
  refine ⟨by linarith, ⟨fun h => ⟨hYam, by linarith⟩, fun h => by linarith [h.2]⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩, ?_, ?_⟩
  · rintro h ⟨c, hc, hR⟩
    have hY := (M.csc_yamabe_a g hN hD hc hR).2
    have hp : 0 ≤ (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have : c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc hp
    linarith
  · intro h hσ
    have hE := hA hYam (by linarith) hσ
    exact ⟨hE, fun h3' => h3 h3' hE⟩

/-- cor:gap-nonneg (a) (l.236), over the family's Yamabe invariant `σ(Σ) = sup_C Y(Σ, [rep C])`
(OQ-132 (b)), bounded above (`hb`, Aubin's bound), the class of `g` in the family (`hC₀`),
thm:extremal (a) and the three-dimensional fact carried. -/
theorem cor_gap_nonneg_a (hN : 3 ≤ N) {Cls : Type} (rep : Cls → CurvedMetric X N)
    (psc : Cls → Prop) (hb : BddAbove (Set.range fun C => M.Y (rep C)))
    (g : CurvedMetric X N) (C₀ : Cls) (hC₀ : M.Y (rep C₀) = M.Y g)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hg : (∃ c ≤ 0, ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) ∨ M.EH g = M.Y g)
    (Einstein ConstCurv : CurvedMetric X N → Prop)
    (hA : M.ExtremalA (M.yamabeClasses rep psc).sigma Einstein g)
    (h3 : EinsteinConstCurv3 Einstein ConstCurv g) :
    0 ≤ M.gapBdry (M.yamabeClasses rep psc).sigma g ∧
    (M.gapBdry (M.yamabeClasses rep psc).sigma g = 0 ↔
      M.EH g = M.Y g ∧ M.Y g = (M.yamabeClasses rep psc).sigma) ∧
    (M.gapBdry (M.yamabeClasses rep psc).sigma g = 0 ↔ M.EH g = (M.yamabeClasses rep psc).sigma) ∧
    (M.gapBdry (M.yamabeClasses rep psc).sigma g = 0 →
      (∃ c ≤ 0, ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) → (M.yamabeClasses rep psc).sigma ≤ 0) ∧
    (M.gapBdry (M.yamabeClasses rep psc).sigma g = 0 → (M.yamabeClasses rep psc).sigma ≤ 0 →
      Einstein g ∧ (N = 3 → ConstCurv g)) := by
  have hYσ : M.Y g ≤ (M.yamabeClasses rep psc).sigma := hC₀ ▸ M.Y_le_sigma rep psc hb C₀
  exact M.gapNonneg_core hN g hYσ hD hg Einstein ConstCurv hA h3

end Closed

/-! ## cor:gap-nonneg (b) -/

/-- eq:gap-def's `k := σ(Σ) / V_i^{2/N}` (l.227). -/
def gapNonneg_k (N : ℕ) (σ Vi : ℝ) : ℝ := σ / Vi ^ (2 / (N : ℝ))

section Closed

variable (M : MeasuredModel X D N 0)

/-- eq:accel-gap (l.230–232) from eq:accel (carried at `t`, `AccelLaw`): for every value `σ` of the
Yamabe invariant, the last term of eq:accel is `−k/a² + δ(Σ_t)/(V_i^{2/N} a²)`. -/
theorem accel_gap (hN : 3 ≤ N) (g : ℝ → CurvedMetric X N) (ti ρi Λ t : ℝ)
    (hVt : 0 < (M.vol (g t).toFrameMetric Set.univ).toReal)
    (hVi : 0 < (M.vol (g ti).toFrameMetric Set.univ).toReal)
    (hacc : M.AccelLaw g ti ρi Λ t) (σ : ℝ) :
    deriv (deriv fun s => M.scale g ti s ^ N) t / M.scale g ti t ^ N =
      (N : ℝ) / ((N : ℝ) - 1) * (ρi / M.scale g ti t ^ N) + 2 * (N : ℝ) / ((N : ℝ) - 1) * Λ -
        gapNonneg_k N σ (M.vol (g ti).toFrameMetric Set.univ).toReal / M.scale g ti t ^ 2 +
        M.gapBdry σ (g t) /
          ((M.vol (g ti).toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) * M.scale g ti t ^ 2) := by
  rw [(M.prop_accel_bdry hN g ti ρi Λ t hVt hVi hacc).1 (M.closed_minimal _) σ]
  unfold gapNonneg_k
  ring

/-- cor:gap-nonneg (b) (l.237–238, proof l.244), thm:extremal (b) carried as `hB`: if
`σ = R_{g_0} Vol(Σ, g_0)^{2/N}` for a metric `g_0` of constant scalar curvature `R_0`, then
(1) the rescaling `g_0' = l g_0` to volume `V_i` has `R_{g_0'} ≡ k`; (2) for every `a > 0` the FLRW
leaf `a² g_0'` has volume `a^N V_i`, `⟨R⟩ = k/a²` (so `−k/a²` is its curvature term in eq:accel)
and Yamabe energy `σ` (its gap vanishes); (3) for a leaf family `g` with `V_i = Vol(Σ_{t_i})`,
`δ(Σ_t)/(V_i^{2/N} a(t)²) = ⟨R⟩_{FLRW}(t) − ⟨R_{g_t}⟩_{Σ_t}`: the gap is the full deviation of the
averaged scalar curvature from its Friedmannian value. -/
theorem cor_gap_nonneg_b (hN : 3 ≤ N) {σ : ℝ} (g0 : CurvedMetric X N) {R0 : ℝ}
    [IsFiniteMeasure (M.vol g0.toFrameMetric)] (hV0 : M.vol g0.toFrameMetric ≠ 0)
    (hR0 : ∀ x, g0.R x = R0)
    (hB : σ = R0 * (M.vol g0.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)))
    {Vi : ℝ} (hVi : 0 < Vi) :
    ∃ (l : ℝ) (hl : 0 < l),
      (∀ x, (g0.homothety l hl).R x = gapNonneg_k N σ Vi) ∧
      (M.vol (g0.homothety l hl).toFrameMetric Set.univ).toReal = Vi ∧
      (∀ (a : ℝ) (ha : 0 < a),
        (M.vol ((g0.homothety l hl).homothety (a ^ 2) (pow_pos ha 2)).toFrameMetric
            Set.univ).toReal = a ^ N * Vi ∧
        M.avgR ((g0.homothety l hl).homothety (a ^ 2) (pow_pos ha 2)) = gapNonneg_k N σ Vi / a ^ 2 ∧
        M.EH ((g0.homothety l hl).homothety (a ^ 2) (pow_pos ha 2)) = σ) ∧
      (∀ (g : ℝ → CurvedMetric X N) (ti t : ℝ),
        0 < (M.vol (g t).toFrameMetric Set.univ).toReal →
        (M.vol (g ti).toFrameMetric Set.univ).toReal = Vi →
        ∃ ha : 0 < M.scale g ti t,
          M.gapBdry σ (g t) / (Vi ^ (2 / (N : ℝ)) * M.scale g ti t ^ 2) =
            M.avgR ((g0.homothety l hl).homothety (M.scale g ti t ^ 2) (pow_pos ha 2)) -
              M.avgR (g t)) := by
  have hN' := three_le_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hV0pos : 0 < (M.vol g0.toFrameMetric Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV0) (measure_ne_top _ _)
  set V0 := (M.vol g0.toFrameMetric Set.univ).toReal with hV0def
  have hq : 0 < Vi / V0 := div_pos hVi hV0pos
  set l := (Vi / V0) ^ (2 / (N : ℝ)) with hldef
  have hl : 0 < l := Real.rpow_pos_of_pos hq _
  have hlN : l ^ ((N : ℝ) / 2) = Vi / V0 := by
    rw [hldef, ← Real.rpow_mul hq.le]
    have : 2 / (N : ℝ) * ((N : ℝ) / 2) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hvol' : (M.vol (g0.homothety l hl).toFrameMetric Set.univ).toReal = Vi := by
    rw [M.volReal_homothety, hlN, ← hV0def]; field_simp
  have hk : ∀ x, (g0.homothety l hl).R x = gapNonneg_k N σ Vi := by
    intro x
    rw [CurvedMetric.homothety_R, hR0, gapNonneg_k, hB, hldef, Real.div_rpow hVi.le hV0pos.le]
    have h1 : 0 < Vi ^ (2 / (N : ℝ)) := Real.rpow_pos_of_pos hVi _
    have h2 : 0 < V0 ^ (2 / (N : ℝ)) := Real.rpow_pos_of_pos hV0pos _
    field_simp
  have havg' : M.avgR (g0.homothety l hl) = gapNonneg_k N σ Vi := by
    unfold avgR
    simp only [hk]
    rw [integral_const, smul_eq_mul, measureReal_def, hvol']
    field_simp
  have hEH0 : M.EH g0 = σ := by
    rw [M.EH_eq_const_mul g0 hN (M.closed_minimal g0) (ae_of_all _ hR0), hB]
  refine ⟨l, hl, hk, hvol', fun a ha => ⟨?_, ?_, ?_⟩, fun g ti t hVt hti => ?_⟩
  · rw [M.volReal_homothety, hvol', ← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
    have : ((2 : ℕ) : ℝ) * ((N : ℝ) / 2) = N := by push_cast; ring
    rw [this, Real.rpow_natCast]
  · rw [M.avgR_homothety, havg']
  · rw [M.closedEH_homothety hN, M.closedEH_homothety hN, hEH0]
  · have hVti : 0 < (M.vol (g ti).toFrameMetric Set.univ).toReal := by rw [hti]; exact hVi
    have ha : 0 < M.scale g ti t := by
      unfold scale
      exact Real.rpow_pos_of_pos (div_pos hVt hVti) _
    refine ⟨ha, ?_⟩
    rw [M.avgR_homothety, havg', M.avgR_of_minimal hN (g t) (M.closed_minimal _) hVt,
      (M.vol_rpow_eq hN g ti t hVt hVti).2, hti]
    unfold gapBdry gapNonneg_k
    ring

end Closed

/-! ## cor:volume -/

section Volume

variable (M : MeasuredModel X D 3 0)

/-- Mostow rigidity (l.256), carried at `g, g_hyp`: two metrics of constant curvature and equal
constant scalar curvature on a closed hyperbolic 3-manifold are isometric. `ConstCurv` and
`Isometric` are supplied (the model has neither). -/
def MostowAt (ConstCurv : CurvedMetric X 3 → Prop)
    (Isometric : CurvedMetric X 3 → CurvedMetric X 3 → Prop) (g ghyp : CurvedMetric X 3) : Prop :=
  ConstCurv g → ConstCurv ghyp → (∀ x, g.R x = ghyp.R x) → Isometric g ghyp

/-- cor:volume (l.246–257) over the family's `σ(Σ)` (OQ-132 (b)): for `R_g ≡ R_{g_hyp} ≡ c < 0`,
`Vol(Σ, g) ≥ Vol(Σ, g_hyp)`, with equality iff `g` is isometric to `g_hyp`; thm:extremal (b) at
`g_hyp` (`hB`), thm:extremal (a) and the three-dimensional fact at `g`, Mostow at `(g, g_hyp)`,
and « isometric metrics have equal volume » (`hIsoVol`) carried. -/
theorem cor_volume {Cls : Type} (rep : Cls → CurvedMetric X 3) (psc : Cls → Prop)
    (hb : BddAbove (Set.range fun C => M.Y (rep C)))
    (g ghyp : CurvedMetric X 3) (C₀ : Cls) (hC₀ : M.Y (rep C₀) = M.Y g)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] [IsFiniteMeasure (M.vol ghyp.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    {c : ℝ} (hc : c < 0) (hR : ∀ x, g.R x = c) (hRhyp : ∀ x, ghyp.R x = c)
    (hB : (M.yamabeClasses rep psc).sigma =
      c * (M.vol ghyp.toFrameMetric Set.univ).toReal ^ (2 / (3 : ℝ)))
    (Einstein ConstCurv : CurvedMetric X 3 → Prop)
    (Isometric : CurvedMetric X 3 → CurvedMetric X 3 → Prop)
    (hA : M.ExtremalA (M.yamabeClasses rep psc).sigma Einstein g)
    (h3 : EinsteinConstCurv3 Einstein ConstCurv g) (hhyp : ConstCurv ghyp)
    (hMostow : MostowAt ConstCurv Isometric g ghyp)
    (hIsoVol : Isometric g ghyp →
      M.vol g.toFrameMetric Set.univ = M.vol ghyp.toFrameMetric Set.univ) :
    (M.vol ghyp.toFrameMetric Set.univ).toReal ≤ (M.vol g.toFrameMetric Set.univ).toReal ∧
    ((M.vol g.toFrameMetric Set.univ).toReal = (M.vol ghyp.toFrameMetric Set.univ).toReal ↔
      Isometric g ghyp) := by
  set V := (M.vol g.toFrameMetric Set.univ).toReal with hVdef
  set Vh := (M.vol ghyp.toFrameMetric Set.univ).toReal with hVhdef
  have hYam := M.csc_yamabe_a g (le_refl 3) hD hc.le (ae_of_all _ hR)
  have e3 : (2 / ((3 : ℕ) : ℝ)) = 2 / (3 : ℝ) := by norm_num
  rw [e3, ← hVdef] at hYam
  have hYσ : M.Y g ≤ (M.yamabeClasses rep psc).sigma := hC₀ ▸ M.Y_le_sigma rep psc hb C₀
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hVh : 0 ≤ Vh := ENNReal.toReal_nonneg
  have hle : Vh ^ (2 / (3 : ℝ)) ≤ V ^ (2 / (3 : ℝ)) := by
    have h : c * V ^ (2 / (3 : ℝ)) ≤ c * Vh ^ (2 / (3 : ℝ)) := by
      rw [← hYam.2, ← hB]; exact hYσ
    exact (mul_le_mul_left_of_neg hc).mp h
  refine ⟨(Real.rpow_le_rpow_iff hVh hV (by norm_num)).mp hle, ⟨fun hEq => ?_, fun hIso => ?_⟩⟩
  · have hσ0 : (M.yamabeClasses rep psc).sigma ≤ 0 := by
      rw [hB]
      exact mul_nonpos_of_nonpos_of_nonneg hc.le (Real.rpow_nonneg hVh _)
    have hYeq : M.Y g = (M.yamabeClasses rep psc).sigma := by
      rw [hYam.2, hB, hEq]
    have hE := hA hYam.1 hYeq hσ0
    exact hMostow (h3 rfl hE) hhyp (fun x => by rw [hR, hRhyp])
  · rw [hVdef, hVhdef, hIsoVol hIso]

end Volume

end MeasuredModel

/-! ## Witnesses on the closed two-point model -/

section Toy

lemma toyClosed_gapCor_finite (c : ℝ) :
    IsFiniteMeasure (toyClosed.vol (toyConst c).toFrameMetric) := by
  show IsFiniteMeasure (toyClosed.vol toyMetric); rw [toyClosed_vol]; infer_instance

/-- The one-class family `{[toyConst (−1)]}` of the closed two-point model: `σ = Y(Σ, [g])`. -/
lemma toyClosed_gapCor_sigma :
    (toyClosed.yamabeClasses (fun _ : Unit => toyConst (-1)) (fun _ => False)).sigma =
      toyClosed.Y (toyConst (-1)) := by
  rw [MeasuredModel.sigma_yamabeClasses, ciSup_const]

/-- The hypotheses of `cor_gap_nonneg_a`, `cor_gap_nonneg_b` and `cor_volume` are satisfiable
together on the connected closed two-point model with `R ≡ −1` and the one-class family: the gap
vanishes (`δ = 0`, the leaf attains `σ`), and thm:extremal (b)'s carried value
`σ = R_{g_0} Vol(g_0)^{2/3}` holds at `g_0 = g_hyp = toyConst (−1)`. The predicates `Einstein`,
`ConstCurv`, `Isometric` are not tested by this witness (kb/0095, SCOPE). -/
theorem toyClosed_gap_nonneg_witness :
    toyClosed.gapBdry
        (toyClosed.yamabeClasses (fun _ : Unit => toyConst (-1)) (fun _ => False)).sigma
        (toyConst (-1)) = 0 ∧
    (toyClosed.yamabeClasses (fun _ : Unit => toyConst (-1)) (fun _ => False)).sigma =
      -1 * (toyClosed.vol (toyConst (-1)).toFrameMetric Set.univ).toReal ^ (2 / (3 : ℝ)) := by
  haveI := toyClosed_gapCor_finite (-1)
  have hD : ∀ u, AEStronglyMeasurable (toyClosed.val u)
      (toyClosed.vol (toyConst (-1)).toFrameMetric) :=
    fun _ => Measurable.of_discrete.aestronglyMeasurable
  have h := toyClosed.csc_yamabe_a (toyConst (-1)) (le_refl 3) hD (c := -1) (by norm_num)
    (ae_of_all _ fun _ => rfl)
  have e3 : (2 / ((3 : ℕ) : ℝ)) = 2 / (3 : ℝ) := by norm_num
  rw [e3] at h
  have hb : BddAbove (Set.range fun _ : Unit => toyClosed.Y (toyConst (-1))) := by
    rw [Set.range_const]; exact bddAbove_singleton
  have hcor := toyClosed.cor_gap_nonneg_a (le_refl 3) (fun _ : Unit => toyConst (-1))
    (fun _ => False) hb (toyConst (-1)) () rfl hD
    (Or.inl ⟨-1, by norm_num, ae_of_all _ fun _ => rfl⟩) (fun _ => True) (fun _ => True)
    (fun _ _ _ => trivial) (fun _ _ => trivial)
  rw [toyClosed_gapCor_sigma]
  refine ⟨?_, h.2⟩
  have := hcor.2.1.mpr ⟨h.1, toyClosed_gapCor_sigma.symm⟩
  rwa [toyClosed_gapCor_sigma] at this

end Toy

end Yamabe
