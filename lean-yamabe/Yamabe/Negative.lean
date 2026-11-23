import Yamabe.Gluing

/-!
# Strict negativity and the non-positive type, over the measured model

Labels (abstract layer only; NOT marked: both rows stay partial, see SCOPE):

* `cor:negative` — `Yamabegap.tex:502` (statement l.502–505; proved with thm:upper-bound, last
  sentence of the proof l.728): `inf F_g > 0`, hence `Y_[g](Σ) < 0` and `R_g < 0`, and "never
  scalar flat", over the model of `Yamabe.Gluing`, with lem:positivity carried;
* `prop:nonpositive` — `Yamabegap.tex:476` (statement l.476–479, proof l.640–646): its second
  sentence only ("Consequently …", proof l.645, last sentence), with its first sentence
  `Y_[g](Σ) ≤ 0` and the conclusion of lem:kobayashi (b) carried.

> Under the hypotheses of Theorem~\ref{thm:upper-bound}, $\inf\Fq_\g>0$; hence
> $\Y_{[\g]}(\Sigma)<0$ and $\Rs_\g<0$. In particular a Schwarzschild-like punctured torus is
> never scalar flat. (l.504)

> Corollary~\ref{cor:negative} follows from Lemma~\ref{lem:positivity}:
> $\Y_{[\g]}(\Sigma)\le-\inf\Fq_\g<0$, and
> $\Rs_\g=\Y_{[\g]}(\Sigma)\Vol(\Sigma,\g)^{-2/N}<0$. (l.728)

> Assume that $\Sigbar$ is enlargeable and that for each $j$ the conformal class of
> $\g|_{B_j}$ has positive Yamabe constant (automatic for $N=3$). Then
> $\Y_{[\g]}(\Sigma)\le0$. Consequently, if $\g$ has constant scalar curvature and minimal
> boundary, then $\Rs_\g\le0$ and $\EH(\Sigma,\g)=\Y_{[\g]}(\Sigma)$. (l.478)

> If moreover $\g$ has constant scalar curvature and minimal boundary,
> Lemma~\ref{lem:kobayashi}(b) excludes $\Rs_\g>0$, and Lemma~\ref{lem:kobayashi}(a) gives
> $\EH(\Sigma,\g)=\Y_{[\g]}(\Sigma)$. (l.645)

> \item[(b)] If $\min_\Sigma\Rs_\g>0$, then $\Y_{[\g]}(\Sigma)>0$. (l.623, under "Assume
> $H_\g\equiv0$", l.615)

> For every metric $\g$ on the compact connected manifold with non-empty boundary $\Sigma$,
> $\inf_{u\ne0}\Fq_\g(u)>0$. (lem:positivity, l.717)

## The model

`Σ` is a `MeasuredModel` with a `CurvedMetric` (`Yamabe.Kobayashi`); thm:upper-bound's
hypotheses are read as in `Yamabe.MeasuredModel.upper_bound_of_gluings_of_pos` (`Yamabe.Gluing`):
`R_g ≡ c` pointwise, `MinimalBoundary`, a family `g̃_τ` (lem:gluing) and, per `τ`, a
`GluingInput` with `β_j = c_N` and `Y_[ḡ_τ](Σ̄) ≤ 0`. New here: `KobayashiB`, the conclusion of
lem:kobayashi (b) for `g`, a `Prop`.

## What is proved

`neg_of_upper_bound` (l.728, from eq:upper-bound, `Y = R_g Vol^{2/N}` and lem:positivity:
`Y < 0`, `Vol(Σ, g) > 0`, `R_g = Y Vol^{-2/N} < 0`); `cor_negative` (the assembly of
cor:negative: `inf F_g > 0`, `Y < 0`, `R_g < 0`, `R_g = Y Vol^{-2/N}`, not scalar flat);
`nonpos_of_kobayashiB` ("(b) excludes `R_g > 0`"); `prop_nonpositive_csc` (the second sentence:
`R_g ≤ 0` and `EH = Y`). Witnesses on the two-point toy model: `toy_infF_pos` (lem:positivity
holds there, `inf F ≥ 2`), `toy_kobayashiB` (lem:kobayashi (b) holds there for every constant
`R`), `toyNegInput` and `toy_cor_negative` (every hypothesis of `cor_negative` discharged, with
`R_g ≡ -8`), `toy_prop_nonpositive`, `toyCurved_no_gluingInput` (the gluing input is not
automatic). Why lem:positivity is carried: `toyClosed_counterexample` (`n = 0`: the non-trivial
hypotheses of thm:upper-bound hold, `inf F = 0`, `Y = 0`, `R_g ≡ 0`) and `toyCut_infF` (a model of a
disconnected `Σ`, `inf F = 0` with `∂Σ ≠ ∅`).

## Hypothesis checklist

cor:negative:

| paper hypothesis | here |
|---|---|
| `N ≥ 3` (l.605) | ✓ carried |
| thm:upper-bound: `σ(Σ̄) ≤ 0`, constant scalar curvature, minimal boundary, `B_j` conformally round (l.495) | ⚠ read as in `upper_bound_of_gluings_of_pos`: `R_g x = c` for every `x`, `MinimalBoundary`; `σ(Σ̄) ≤ 0` only as `Y_[ḡ_τ](Σ̄) ≤ 0` per `τ`; roundness only through lem:gluing and fact (iv), carried (the family `g̃_τ`, `GluingInput` with `β = c_N`) |
| compactness | ✓ carried as `IsFiniteMeasure (vol_g)` |
| `inf F_g > 0` (lem:positivity, l.717, Rellich–Kondrachov, compact trace, Sobolev: Hebey1996) | ⚠ carried (`hpos`), as the dispatch requires; not a theorem of the model (`toyClosed_counterexample`, `toyCut_infF`) |
| `∂Σ ≠ ∅`, `Σ` connected (lem:positivity's hypotheses) | ⚠ not modelled; they enter only through `hpos`; `n ≥ 1` is not stated by thm:upper-bound nor at l.465 (finding) |
| `Vol(Σ, g) > 0` (for `Vol^{-2/N}`, l.728) | ✓ derived (`neg_of_upper_bound`) |
| `u ∈ W^{1,2}(Σ)` measurable | ✓ carried as `hD` (a.e.-strong measurability of every `val u`) |

prop:nonpositive, second sentence:

| paper hypothesis | here |
|---|---|
| `Σ̄` enlargeable, `[g|_{B_j}]` of positive Yamabe constant (l.478) | ⚠ weakened: used only through the first sentence |
| `Y_[g](Σ) ≤ 0` (first sentence, l.478; proof l.641–645: MR1957657 Cor. 5.3, thm:yamabe (b), MR569070) | ⚠ carried (`hY`), not formalized |
| `g` of constant scalar curvature (l.478) | ✓ carried: `R_g x = c` for every `x` |
| minimal boundary (l.478) | ✓ carried (`MinimalBoundary`) |
| lem:kobayashi (b) (l.623, Sobolev embedding, Hebey1996) | ⚠ carried as its conclusion for `g` (`KobayashiB`) |
| lem:kobayashi (a) (l.615–622) | ✓ the strict `lem_kobayashi_a` |
| compactness, `u` measurable | ✓ carried (`IsFiniteMeasure`, `hD`) |

## SCOPE (disclosed)

* Abstract layer only (DEC-139): the model's readings are accepted (DEC-186, OQ-44), and n ≥ 1 is standing
  in § 6 (DEC-186, OQ-74). Neither row is marked: both use lem:positivity, carried here (`hpos`).
  Its manifold reading (`Yamabe.Mfd.lem_positivity`, scaffold `YamabeScaffold.Rellich`) is proved,
  Rellich–Kondrachov included (`Yamabe.Mfd.rellich_kondrachov`, `YamabeScaffold.RellichManifold`),
  but under the readings of OQ-93, which is open.
* cor:negative: its first assertion `inf F_g > 0` is lem:positivity itself, carried; the model
  cannot prove it, since it carries neither connectedness nor Rellich–Kondrachov nor a compact
  trace (`toyCut_infF`; `toyClosed_counterexample` for `∂Σ = ∅`). The second and third
  assertions are proved from it and from the strict assembly `upper_bound_of_gluings_of_pos`.
  `R_g < 0` is `c < 0` (hence `R_g x < 0` everywhere).
* "In particular a Schwarzschild-like punctured torus is never scalar flat" (l.504) is read as
  `¬ ∀ x, R_g x = 0` under thm:upper-bound's hypotheses. The torus `Σ̄ = T³` and the round spheres
  are not modelled: that a Schwarzschild-like punctured torus satisfies thm:upper-bound's
  hypotheses (`σ(T³) ≤ 0`, round spheres conformally round, `N = 3`) is argued, not formalized.
* prop:nonpositive: the first sentence is not formalized (doubles, connected sums,
  enlargeability and thm:yamabe (b) on the double have no counterpart in the model): `Y ≤ 0` is
  carried. lem:kobayashi (b) is carried as `KobayashiB` for `g`: the model's differential is an
  arbitrary linear map and nothing bounds `‖u‖_{L^{p*}}` by `‖u‖_{W^{1,2}}`, so (b) is not a
  theorem of the model (argued, not formalized); it holds on the toy model (`toy_kobayashiB`).
  `min_Σ R_g` is read `⨅ x, R_g x`, as in `CurvedMetric.kobM`; `R_g ≤ 0` is read pointwise (for
  `Σ` empty it is vacuous, and `EH = Y = 0`).
* Witnesses: `toy_cor_negative` discharges every hypothesis of `cor_negative` on the toy model
  (`R_g ≡ -8`, the constant family `g̃_τ = g`, `toyNegInput`: `u = 1`, `y = 0`, `H_h ≡ -4`,
  `H_{D_0} ≡ 4`, `EHB(D_0) = 16 ≥ c_3`), lem:positivity included. `toy_prop_nonpositive`
  discharges every hypothesis of `prop_nonpositive_csc` (`toyCurved`, `Y = -2^{2/3}`).
* **Finding (l.465, l.495, l.504, l.717).** For `n = 0` (no puncture), thm:upper-bound's
  hypotheses hold for a flat `T³` and cor:negative fails: `inf F_g = 0` (`F_g(1) = 0`),
  `Y = R_g = 0`. lem:positivity needs `∂Σ ≠ ∅`, which neither the standing assumption (l.465)
  nor thm:upper-bound states. Model counterexample: `toyClosed_counterexample`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

namespace MeasuredModel

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-! ## cor:negative -/

/-- The last sentence of thm:upper-bound's proof (l.728), from eq:upper-bound
(`Y_[g](Σ) ≤ -inf F_g`), the identity `Y_[g](Σ) = R_g Vol(Σ, g)^{2/N}` (l.724) and
lem:positivity (`inf F_g > 0`, carried): `Y_[g](Σ) < 0`, `Vol(Σ, g) > 0`, and
`R_g = Y_[g](Σ) Vol(Σ, g)^{-2/N} < 0`. -/
theorem neg_of_upper_bound (hN : 3 ≤ N) (g : CurvedMetric X N) {c : ℝ}
    (hpos : 0 < M.infF g.toFrameMetric (fun _ => cN N))
    (hub : M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N))
    (hYc : M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ))) :
    M.Y g < 0 ∧ 0 < (M.vol g.toFrameMetric Set.univ).toReal ∧
      c = M.Y g * (M.vol g.toFrameMetric Set.univ).toReal ^ (-(2 / (N : ℝ))) ∧ c < 0 := by
  have hN' := three_le_cast hN
  set V := (M.vol g.toFrameMetric Set.univ).toReal with hVdef
  have hYneg : M.Y g < 0 := by linarith
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVpos : 0 < V := by
    rcases hV0.eq_or_lt with h0 | h0
    · exfalso
      rw [← h0, Real.zero_rpow (by positivity : (2 : ℝ) / N ≠ 0), mul_zero] at hYc
      linarith
    · exact h0
  have hVp : 0 < V ^ (2 / (N : ℝ)) := Real.rpow_pos_of_pos hVpos _
  have hc : c = M.Y g * V ^ (-(2 / (N : ℝ))) := by
    rw [Real.rpow_neg hV0, hYc, mul_assoc, mul_inv_cancel₀ hVp.ne', mul_one]
  refine ⟨hYneg, hVpos, hc, ?_⟩
  rw [hYc] at hYneg
  by_contra h
  have := mul_nonneg (not_lt.mp h) hVp.le
  linarith

/-- cor:negative over the model (l.502–505, proof l.728). Under the hypotheses of thm:upper-bound
as `upper_bound_of_gluings_of_pos` reads them (`R_g ≡ c` pointwise, minimal boundary, the family
`g̃_τ` of lem:gluing with, per `τ`, the inputs of lem:gluing-estimate for `β_j = c_N` and
`Y_[ḡ_τ](Σ̄) ≤ 0`), and with lem:positivity carried (`hpos`): `inf F_g > 0`; `Y_[g](Σ) < 0`;
`R_g = c < 0`, with `R_g = Y_[g](Σ) Vol(Σ, g)^{-2/N}`; and `g` is not scalar flat. -/
theorem cor_negative (hN : 3 ≤ N) (g : CurvedMetric X N)
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
    0 < M.infF g.toFrameMetric (fun _ => cN N) ∧ M.Y g < 0 ∧ c < 0 ∧
      c = M.Y g * (M.vol g.toFrameMetric Set.univ).toReal ^ (-(2 / (N : ℝ))) ∧
      ¬ ∀ x, g.R x = 0 := by
  obtain ⟨-, hYc, hub⟩ := M.upper_bound_of_gluings_of_pos hN g hD hH hRc hpos gs η δ hη hηt
    hclose hδt hR hfin hV hB hρ hHτ S
  obtain ⟨hYneg, hVpos, hc, hcneg⟩ := M.neg_of_upper_bound hN g hpos hub hYc
  refine ⟨hpos, hYneg, hcneg, hc, fun hflat => ?_⟩
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · rw [Set.univ_eq_empty_iff.mpr hX, measure_empty, ENNReal.toReal_zero] at hVpos
    exact lt_irrefl _ hVpos
  · exact hcneg.ne ((hRc x).symm.trans (hflat x))

/-! ## prop:nonpositive, second sentence -/

/-- The conclusion of lem:kobayashi (b) for `g` (l.623), under the lemma's standing assumption
`H_g ≡ 0` (l.615): if `min_Σ R_g > 0` then `Y_[g](Σ) > 0`. `min_Σ R_g` is read `⨅ x, R_g x`, as
in `CurvedMetric.kobM`. Its proof uses the Sobolev embedding `W^{1,2} ↪ L^{p*}` (Hebey1996),
which the model does not carry: it is a carried input. -/
def KobayashiB (g : CurvedMetric X N) : Prop := 0 < ⨅ x, g.R x → 0 < M.Y g

/-- "Lemma kobayashi (b) excludes `R_g > 0`" (l.645): for `R_g ≡ c` and `Y_[g](Σ) ≤ 0`,
`R_g ≤ 0`. -/
theorem nonpos_of_kobayashiB (g : CurvedMetric X N) {c : ℝ} (hRc : ∀ x, g.R x = c)
    (hY : M.Y g ≤ 0) (hb : M.KobayashiB g) : ∀ x, g.R x ≤ 0 := by
  intro x
  rw [hRc x]
  by_contra hc
  have hinf : (⨅ x, g.R x) = c := by
    haveI : Nonempty X := ⟨x⟩
    simp only [hRc, ciInf_const]
  have := hb (by rw [hinf]; exact lt_of_not_ge hc)
  linarith

/-- prop:nonpositive, second sentence (l.478, proof l.645), over the model: with its first
sentence `Y_[g](Σ) ≤ 0` (`hY`) and the conclusion of lem:kobayashi (b) (`hb`) carried, if `g` has
constant scalar curvature (`R_g ≡ c`) and minimal boundary, then `R_g ≤ 0` and
`EH(Σ, g) = Y_[g](Σ)`. -/
theorem prop_nonpositive_csc (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    (hY : M.Y g ≤ 0) (hb : M.KobayashiB g) :
    (∀ x, g.R x ≤ 0) ∧ M.EH g = M.Y g := by
  have hle := M.nonpos_of_kobayashiB g hRc hY hb
  refine ⟨hle, ?_⟩
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · -- `Σ` empty: `R_g ≡ 0` holds vacuously
    exact ((M.lem_kobayashi_a g hN hD hH).2.2 0 le_rfl
      (ae_of_all _ fun x => (IsEmpty.false x).elim)).1
  · exact ((M.lem_kobayashi_a g hN hD hH).2.2 c (hRc x ▸ hle x) (ae_of_all _ hRc)).1

end MeasuredModel

/-! ## Witnesses on the two-point toy model -/

section Toy

lemma toy_gradSq (u : Bool → ℝ) (x : Bool) :
    toyModel.gradSq toyMetric u x = (u true - u false) ^ 2 := by
  simp [MeasuredModel.gradSq, toyModel, toyMetric, toyD, dotProduct]
  ring

lemma toy_count_univ : (Measure.count (Set.univ : Set Bool)).toReal = 2 := by
  rw [Measure.count_apply_finite _ Set.finite_univ]
  simp

lemma toy_dirichlet (u : Bool → ℝ) :
    toyModel.dirichlet toyMetric u = 2 * (u true - u false) ^ 2 := by
  unfold MeasuredModel.dirichlet
  simp only [toy_gradSq]
  rw [toy_vol, lintegral_const, ENNReal.toReal_mul, toy_count_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
  ring

lemma toy_normSq_bvol (u : Bool → ℝ) (j : Fin 1) {q : ℝ} (hq : 0 < q) :
    normSq (toyModel.bvol toyMetric j) q u = u false ^ 2 := by
  rw [normSq_eq_lintegral hq, toy_bvol, lintegral_dirac, ← ENNReal.toReal_rpow, toReal_enorm,
    ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hq.ne', Real.rpow_two, Real.norm_eq_abs,
    sq_abs]

lemma pStar_three : pStar 3 = 6 := by norm_num [pStar]

/-- `‖u‖²_{L^6}` for the counting measure on the two points. -/
lemma toy_normSq_vol_eq (u : Bool → ℝ) :
    normSq (toyModel.vol toyMetric) (pStar 3) u =
      ((u true ^ 2) ^ 3 + (u false ^ 2) ^ 3) ^ (2 / (6 : ℝ)) := by
  have hne : ∀ t : ℝ, ‖t‖ₑ ^ pStar 3 ≠ ∞ := fun _ =>
    ENNReal.rpow_ne_top_of_nonneg (pStar_pos (le_refl 3)).le enorm_ne_top
  rw [normSq_eq_lintegral (pStar_pos (le_refl 3)), toy_vol, lintegral_count, tsum_fintype,
    Fintype.sum_bool, ENNReal.toReal_add (hne _) (hne _), ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, toReal_enorm, toReal_enorm, pStar_three]
  have e : ∀ t : ℝ, ‖t‖ ^ (6 : ℝ) = (t ^ 2) ^ 3 := fun t => by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
      ← pow_mul, pow_abs]
    exact abs_of_nonneg (by positivity)
  rw [e, e]

/-- `‖u‖²_{L^6} ≤ u(true)² + u(false)²` on the two points. -/
lemma toy_normSq_vol_le (u : Bool → ℝ) :
    normSq (toyModel.vol toyMetric) (pStar 3) u ≤ u true ^ 2 + u false ^ 2 := by
  rw [toy_normSq_vol_eq]
  set A := u true ^ 2
  set B := u false ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := sq_nonneg _
  have h1 : A ^ 3 + B ^ 3 ≤ (A + B) ^ 3 := by
    nlinarith [mul_nonneg hA hB, mul_nonneg (mul_nonneg hA hB) hA,
      mul_nonneg (mul_nonneg hA hB) hB]
  calc (A ^ 3 + B ^ 3) ^ (2 / (6 : ℝ)) ≤ ((A + B) ^ 3) ^ (2 / (6 : ℝ)) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = A + B := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num


lemma cN_three_ge : 12 ≤ cN 3 := by
  rw [cN_three]
  have h : Real.sqrt 9 ≤ Real.sqrt (4 * Real.pi) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  linarith

lemma cN_three_le : cN 3 ≤ 16 := by
  rw [cN_three]
  have h : Real.sqrt (4 * Real.pi) ≤ Real.sqrt 16 :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_le_four])
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  linarith

lemma aN_three : aN 3 = 8 := by norm_num [aN]

lemma toy_adm_one : toyModel.Adm toyMetric toyModel.one := by
  unfold MeasuredModel.Adm
  rw [toyModel.val_one, normSq_one _ (pStar_pos (le_refl 3)), toy_vol, toy_count_univ]
  positivity

lemma toy_F_ge (u : Bool → ℝ) (hu : toyModel.Adm toyMetric u) :
    2 ≤ toyModel.F toyMetric (fun _ => cN 3) u := by
  unfold MeasuredModel.Adm at hu
  have hv : toyModel.val u = u := rfl
  have ht : toyModel.tr u = u := rfl
  rw [hv] at hu
  unfold MeasuredModel.F traceSobolevQuot
  rw [hv, ht, toy_dirichlet, Fin.sum_univ_one, toy_normSq_bvol u 0 (pSharp_pos (le_refl 3)),
    aN_three, le_div_iff₀ hu]
  have hS := toy_normSq_vol_le u
  have hc := cN_three_ge
  nlinarith [sq_nonneg (u true - u false), sq_nonneg (u false),
    sq_nonneg (7 * u true - 8 * u false),
    mul_nonneg (by linarith : (0:ℝ) ≤ cN 3 - 12) (sq_nonneg (u false))]

/-- lem:positivity on the toy model: `inf F ≥ 2`. -/
theorem toy_two_le_infF : 2 ≤ toyModel.infF toyMetric (fun _ => cN 3) := by
  unfold MeasuredModel.infF
  refine le_csInf ⟨_, ⟨toyModel.one, toy_adm_one, rfl⟩⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  exact toy_F_ge u hu

theorem toy_infF_pos : 0 < toyModel.infF toyMetric (fun _ => cN 3) :=
  lt_of_lt_of_le two_pos toy_two_le_infF


/-- The toy metric `G = 1` with constant scalar curvature `c` and minimal boundary. -/
def toyConst (c : ℝ) : CurvedMetric Bool 3 where
  toFrameMetric := toyMetric
  R := fun _ => c
  H := fun _ => 0
  R_measurable := measurable_const
  H_measurable := measurable_const
  R_bdd := ⟨|c|, fun _ => le_rfl⟩
  H_bdd := ⟨0, fun _ => by simp⟩

lemma toyConst_toFrameMetric (c : ℝ) : (toyConst c).toFrameMetric = toyMetric := rfl

lemma toyConst_minimal (c : ℝ) : toyModel.MinimalBoundary (toyConst c) :=
  fun _ => ae_of_all _ fun _ => rfl

lemma toy_scalar_term (c : ℝ) (u : Bool → ℝ) :
    ∫ x, (toyConst c).R x * toyModel.val u x ^ 2 ∂(toyModel.vol (toyConst c).toFrameMetric) =
      c * (u true ^ 2 + u false ^ 2) := by
  rw [toyConst_toFrameMetric, toy_vol, integral_fintype]
  · simp [toyConst, toyModel, Measure.real]
    ring
  · exact .of_finite

/-- lem:kobayashi (b) holds on the toy model, for every constant scalar curvature `c`: if
`c > 0`, then `Y ≥ c > 0`. The carried input `KobayashiB` is satisfiable, and not vacuously. -/
theorem toy_kobayashiB (c : ℝ) : toyModel.KobayashiB (toyConst c) := by
  intro h
  have hc : 0 < c := by
    have e : (⨅ _ : Bool, c) = c := ciInf_const
    simpa [toyConst, e] using h
  refine lt_of_lt_of_le hc ?_
  unfold MeasuredModel.Y MeasuredModel.infConf
  refine le_csInf ⟨_, ⟨toyModel.one, ⟨fun x => by rw [toyModel.val_one]; exact one_pos,
    toy_adm_one⟩, rfl⟩⟩ ?_
  rintro _ ⟨u, ⟨-, hu⟩, rfl⟩
  have hu' : 0 < normSq (toyModel.vol toyMetric) (pStar 3) u := hu
  unfold MeasuredModel.confEnergy
  have hv : toyModel.val u = u := rfl
  rw [toyModel.confAction_of_minimal _ (toyConst_minimal c), toy_scalar_term,
    toyConst_toFrameMetric, hv, le_div_iff₀ hu']
  have hS := toy_normSq_vol_le u
  have hd := toyModel.dirichlet_nonneg toyMetric u
  have ha := aN_pos (le_refl 3)
  nlinarith [mul_nonneg ha.le hd]


/-- The body `h̄|_Σ` of the toy filling for `g = toyConst (-8)`: `G = 1`, `R ≡ 0`, `H ≡ -4`. -/
def toyNegBody : CurvedMetric Bool 3 where
  toFrameMetric := toyMetric
  R := fun _ => 0
  H := fun _ => -4
  R_measurable := measurable_const
  H_measurable := measurable_const
  R_bdd := ⟨0, fun _ => by simp⟩
  H_bdd := ⟨4, fun _ => by norm_num⟩

/-- The cap `h̄|_{D_0}`: `G = 1`, `R ≡ 0`, `H ≡ 4` (w.r.t. the outward normal of `D_0`). -/
def toyNegCap : CurvedMetric Bool 3 where
  toFrameMetric := toyMetric
  R := fun _ => 0
  H := fun _ => 4
  R_measurable := measurable_const
  H_measurable := measurable_const
  R_bdd := ⟨0, fun _ => by simp⟩
  H_bdd := ⟨4, fun _ => by norm_num⟩

/-- The toy glued metric for `g = toyConst (-8)`. -/
def toyNegGlued : GluedMetric Bool Bool 3 1 where
  body := toyNegBody
  cap := fun _ => toyNegCap

lemma toy_bvol_univ (j : Fin 1) : (toyModel.bvol toyMetric j Set.univ).toReal = 1 := by
  rw [toy_bvol]; simp

/-- `𝒮(Σ, h) = 2(N-1) · (-4) · Vol(B_0) = -16` for the toy body. -/
lemma toy_action_body : toyModel.action toyNegBody = -16 := by
  unfold MeasuredModel.action
  simp only [toyNegBody, integral_zero, integral_const, smul_eq_mul, Fin.sum_univ_one,
    measureReal_def, toy_bvol_univ]
  norm_num

/-- `𝒮(D_0, h̄) = 2(N-1) · 4 · Vol(∂D_0) = 16` for the toy cap. -/
lemma toy_action_cap : toyModel.action toyNegCap = 16 := by
  unfold MeasuredModel.action
  simp only [toyNegCap, integral_zero, integral_const, smul_eq_mul, Fin.sum_univ_one,
    measureReal_def, toy_bvol_univ]
  norm_num

/-- The right side of the conformal law for `g = toyConst (-8)` and `u = 1`: `-8 · Vol(Σ) = -16`. -/
lemma toy_confAction_neg : toyModel.confAction (toyConst (-8)) toyModel.one = -16 := by
  rw [toyModel.confAction_of_minimal _ (toyConst_minimal _), toyModel.dirichlet_one,
    toy_scalar_term]
  simp [toyModel]
  norm_num

lemma toy_isFiniteMeasure_vol : IsFiniteMeasure (toyModel.vol toyMetric) := by
  rw [toy_vol]; infer_instance

lemma toy_isFiniteMeasure_bvol (j : Fin 1) : IsFiniteMeasure (toyModel.bvol toyMetric j) := by
  rw [toy_bvol]; infer_instance

lemma toy_vol_ne_zero : toyModel.vol toyMetric ≠ 0 := by
  rw [toy_vol]
  intro h
  have : Measure.count ({true} : Set Bool) = 0 := by rw [h]; rfl
  simp at this

/-- The inputs of lem:gluing-estimate for `g = toyConst (-8)`, `β_0 = c_3`: the filling
`toyFilling` (one piece, a copy of the toy model, glued by the identity), `h̄ = (toyNegBody,
toyNegCap)`, `u = 1`, `Y_[ḡ](Σ̄) = y = 0`, `R_h̄ = 0`. The conformal law holds
(`𝒮(Σ, h) = -16 = confAction g 1`), the flip holds (`-4 = -4`), and
`EHB(D_0, h̄) = 16 ≥ c_3 = 4√(4π)`. -/
def toyNegInput : GluingInput toyModel Bool (Bool → ℝ) (toyConst (-8)) (fun _ => cN 3) where
  F := toyFilling
  hb := toyNegGlued
  u := toyModel.one
  y := 0
  c := 0
  conf := ⟨fun x => by rw [toyModel.val_one]; exact one_pos,
    fun x => by rw [toyModel.val_one]; simp [toyNegGlued, toyNegBody, toyConst]⟩
  val_meas := Measurable.of_discrete.aestronglyMeasurable
  tr_meas := fun _ => Measurable.of_discrete.aestronglyMeasurable
  tr_eq := fun _ => by rw [toyModel.tr_one, toyModel.val_one]
  vol_finite := toy_isFiniteMeasure_vol
  bvol_finite := toy_isFiniteMeasure_bvol
  y_nonpos := le_rfl
  yamabe := ⟨ae_of_all _ fun _ => rfl, fun _ => ae_of_all _ fun _ => rfl, by simp⟩
  law := by
    unfold MeasuredModel.ConformalLaw MeasuredModel.EH
    rw [show toyNegGlued.body = toyNegBody from rfl, toy_action_body, toy_confAction_neg,
      toyConst_toFrameMetric, show toyNegBody.toFrameMetric = toyMetric from rfl, toyModel.val_one, normSq_one _ (pStar_pos (le_refl 3)),
      two_div_pStar (le_refl 3), toy_vol, toy_count_univ]
    have : (0 : ℝ) < 2 ^ ((((3 : ℕ) : ℝ) - 2) / ((3 : ℕ) : ℝ)) := by positivity
    field_simp
  bdryYamabe := fun j => by
    have hc : (toyFilling.piece j).EHB (toyNegGlued.cap j) = 16 := by
      unfold MeasuredModel.EHB MeasuredModel.bdryVol
      have hb : (toyNegGlued.cap j).toFrameMetric = toyMetric := rfl
      rw [show toyFilling.piece j = toyModel from rfl, show toyNegGlued.cap j = toyNegCap from rfl,
        toy_action_cap, show toyNegCap.toFrameMetric = toyMetric from rfl, Fin.sum_univ_one,
        toy_bvol_univ, Real.one_rpow, div_one]
    rw [hc]
    exact cN_three_le
  flip := fun _ => ae_of_all _ fun _ => by simp [toyNegGlued, toyNegBody, toyNegCap]
  bmatch := fun j => by
    change (toyModel.bvol toyMetric j).map id = toyModel.bvol toyMetric 0
    rw [Measure.map_id, Subsingleton.elim j 0]


/-- Every hypothesis of `cor_negative` holds on the toy model with `g = toyConst (-8)`
(`R_g ≡ -8`, `H_g ≡ 0`), the constant family `g̃_τ = g` (`η = δ = 0`), the gluing input
`toyNegInput` for every `τ`, and lem:positivity proved there (`toy_infF_pos`): the hypotheses are
jointly satisfiable, and the conclusions hold. -/
theorem toy_cor_negative :
    0 < toyModel.infF toyMetric (fun _ => cN 3) ∧ toyModel.Y (toyConst (-8)) < 0 ∧
      (-8 : ℝ) < 0 ∧
      (-8 : ℝ) = toyModel.Y (toyConst (-8)) *
        (toyModel.vol toyMetric Set.univ).toReal ^ (-(2 / ((3 : ℕ) : ℝ))) ∧
      ¬ ∀ x, (toyConst (-8)).R x = 0 := by
  haveI : IsFiniteMeasure (toyModel.vol (toyConst (-8)).toFrameMetric) := toy_isFiniteMeasure_vol
  have hclose : ∀ _ : ℕ, MeasuredModel.UniformlyClose ((fun _ : ℕ => (0 : ℝ)) 0)
      (toyConst (-8)).toFrameMetric (toyConst (-8)).toFrameMetric := fun _ x v => by simp
  have hρ : toyModel.DensityMeasurable toyMetric :=
    ⟨Measurable.of_discrete.aemeasurable, fun _ => Measurable.of_discrete.aemeasurable⟩
  exact toyModel.cor_negative (le_refl 3) (toyConst (-8))
    (fun _ => Measurable.of_discrete.aestronglyMeasurable) (toyConst_minimal _) (c := -8)
    (fun _ => rfl) toy_infF_pos (l := atTop) (fun _ : ℕ => toyConst (-8)) (fun _ => 0)
    (fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds hclose tendsto_const_nhds
    (fun _ _ => by simp) (fun _ => toy_isFiniteMeasure_vol) (fun _ => toy_vol_ne_zero)
    (fun _ j => by rw [toyConst_toFrameMetric, toy_bvol]; exact Measure.dirac_ne_zero)
    (fun _ => hρ) (fun _ => toyConst_minimal _) (fun _ => toyNegInput)

/-- Every hypothesis of `prop_nonpositive_csc` holds on the toy model with `g = toyCurved`
(`R_g ≡ -1`, minimal boundary): `Y_[g](Σ) = -2^{2/3} ≤ 0` (`toy_EH_eq_Y`) and lem:kobayashi (b)
(`toy_kobayashiB`). -/
theorem toy_prop_nonpositive :
    (∀ x, toyCurved.R x ≤ 0) ∧ toyModel.EH toyCurved = toyModel.Y toyCurved := by
  haveI := toy_isFiniteMeasure
  have hY : toyModel.Y toyCurved ≤ 0 := by
    rw [← toy_EH_eq_Y.1, toy_EH]
    exact neg_nonpos.mpr (Real.rpow_nonneg (by norm_num) _)
  exact toyModel.prop_nonpositive_csc (le_refl 3) toyCurved
    (fun _ => Measurable.of_discrete.aestronglyMeasurable) toy_minimal (c := -1) (fun _ => rfl) hY
    (toy_kobayashiB (-1))


/-- The gluing input is a genuine restriction: `toyCurved` (`R_g ≡ -1`) admits none with
`β_j = c_N`, since it would give `-Vol(Σ)^{2/3} = -2^{2/3} ≤ -inf F_g ≤ -2`
(`GluingInput.le_neg_infF`, `toy_two_le_infF`). This is why `toy_cor_negative` uses `R_g ≡ -8`. -/
theorem toyCurved_no_gluingInput
    (S : GluingInput toyModel Bool (Bool → ℝ) toyCurved (fun _ => cN 3)) : False := by
  haveI := toy_isFiniteMeasure
  have hV : toyModel.vol toyCurved.toFrameMetric ≠ 0 := toy_vol_ne_zero
  have hB : ∀ j, toyModel.bvol toyCurved.toFrameMetric j ≠ 0 := fun j => by
    rw [toyCurved_toFrameMetric, toy_bvol]; exact Measure.dirac_ne_zero
  have hρ : toyModel.DensityMeasurable toyCurved.toFrameMetric :=
    ⟨Measurable.of_discrete.aemeasurable, fun _ => Measurable.of_discrete.aemeasurable⟩
  have h := S.le_neg_infF (le_refl 3) hV hB hρ toy_minimal (m := -1) (by norm_num)
    (ae_of_all _ fun _ => le_rfl)
  rw [toyCurved_toFrameMetric, toy_vol, toy_count_univ] at h
  have h2 := toy_two_le_infF
  have hlt : (2 : ℝ) ^ (2 / ((3 : ℕ) : ℝ)) < 2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by norm_num : 2 / ((3 : ℕ) : ℝ) < 1)
    rwa [Real.rpow_one] at this
  linarith

/-! ### Why lem:positivity is carried: two models where it fails -/

/-- The toy model without boundary (`n = 0`): `Σ = Σ̄` closed, two interior points. -/
def toyClosed : MeasuredModel Bool (Bool → ℝ) 3 0 where
  μ := Measure.count
  μb := Fin.elim0
  P := fun _ => toyP
  P_injective := fun _ => toyP_injective
  val := LinearMap.id
  tr := LinearMap.id
  d := toyD
  one := fun _ => 1
  val_one := rfl
  tr_one := rfl
  d_one := toyModel.d_one

lemma toyClosed_vol : toyClosed.vol toyMetric = Measure.count := toy_vol

/-- On the closed toy model `F_g(1) = 0`, so `inf F_g = 0`. -/
theorem toyClosed_infF : toyClosed.infF toyMetric (fun _ => cN 3) = 0 := by
  have h1 : toyClosed.F toyMetric (fun _ => cN 3) toyClosed.one = 0 := by
    rw [toyClosed.F_one toyMetric (le_refl 3)]
    simp
  have hadm : toyClosed.Adm toyMetric toyClosed.one := toy_adm_one
  have hnn : ∀ u, 0 ≤ toyClosed.F toyMetric (fun _ => cN 3) u :=
    toyClosed.F_nonneg toyMetric (le_refl 3) (fun j => j.elim0)
  unfold MeasuredModel.infF
  refine le_antisymm ?_ (le_csInf ⟨_, ⟨_, hadm, rfl⟩⟩ ?_)
  · rw [← h1]
    exact csInf_le ⟨0, by rintro _ ⟨u, -, rfl⟩; exact hnn u⟩ ⟨_, hadm, rfl⟩
  · rintro _ ⟨u, -, rfl⟩; exact hnn u

/-- The empty filling and the flat glued metric of the closed toy model. -/
def toyClosedInput : GluingInput toyClosed Bool (Bool → ℝ) (toyConst 0) (fun _ => cN 3) where
  F := ⟨Fin.elim0, Fin.elim0, fun j => j.elim0⟩
  hb := ⟨toyConst 0, Fin.elim0⟩
  u := toyClosed.one
  y := 0
  c := 0
  conf := ⟨fun x => by rw [toyClosed.val_one]; exact one_pos,
    fun x => by rw [toyClosed.val_one]; simp⟩
  val_meas := Measurable.of_discrete.aestronglyMeasurable
  tr_meas := fun j => j.elim0
  tr_eq := fun j => j.elim0
  vol_finite := by
    show IsFiniteMeasure (toyClosed.vol toyMetric); rw [toyClosed_vol]; infer_instance
  bvol_finite := fun j => j.elim0
  y_nonpos := le_rfl
  yamabe := ⟨ae_of_all _ fun _ => rfl, fun j => j.elim0, by simp⟩
  law := by
    haveI : IsFiniteMeasure (toyClosed.vol (toyConst 0).toFrameMetric) := by
      show IsFiniteMeasure (toyClosed.vol toyMetric); rw [toyClosed_vol]; infer_instance
    unfold MeasuredModel.ConformalLaw
    rw [toyClosed.EH_eq_const_mul (toyConst 0) (le_refl 3) (fun j => j.elim0) (c := 0)
      (ae_of_all _ fun _ => rfl), toyClosed.confAction_of_minimal _ (fun j => j.elim0),
      toyClosed.dirichlet_one]
    simp [toyConst]
  bdryYamabe := fun j => j.elim0
  flip := fun j => j.elim0
  bmatch := fun j => j.elim0

/-- **The case `n = 0`** (a counterexample to cor:negative read without `∂Σ ≠ ∅`): on the closed
toy model with the flat metric (`R ≡ 0`, the model of a flat `T³` with no puncture), the
non-trivial hypotheses of thm:upper-bound as `cor_negative` reads them hold (minimal boundary, `Σ`
nonempty, measurable densities, and the inputs of lem:gluing-estimate with `β_j = c_N`,
`Y_[ḡ](Σ̄) = 0`), but `inf F_g = 0`, `Y_[g](Σ) = 0` and `g` is scalar flat. lem:positivity needs
its non-empty boundary, while the paper allows `∂Σ = ∅` (l.615, « (or ∂Σ = ∅) »). -/
theorem toyClosed_counterexample :
    Nonempty (GluingInput toyClosed Bool (Bool → ℝ) (toyConst 0) (fun _ => cN 3)) ∧
      toyClosed.MinimalBoundary (toyConst 0) ∧ toyClosed.vol (toyConst 0).toFrameMetric ≠ 0 ∧
      toyClosed.DensityMeasurable (toyConst 0).toFrameMetric ∧
      toyClosed.infF (toyConst 0).toFrameMetric (fun _ => cN 3) = 0 ∧
      toyClosed.Y (toyConst 0) = 0 ∧ ∀ x, (toyConst 0).R x = 0 := by
  haveI : IsFiniteMeasure (toyClosed.vol (toyConst 0).toFrameMetric) := by
    show IsFiniteMeasure (toyClosed.vol toyMetric); rw [toyClosed_vol]; infer_instance
  have hH : toyClosed.MinimalBoundary (toyConst 0) := fun j => j.elim0
  have hY : toyClosed.Y (toyConst 0) = 0 := by
    rw [← toyClosed.EH_eq_Y (toyConst 0) (le_refl 3)
      (fun _ => Measurable.of_discrete.aestronglyMeasurable) hH (c := 0) le_rfl
      (ae_of_all _ fun _ => rfl),
      toyClosed.EH_eq_const_mul (toyConst 0) (le_refl 3) hH (c := 0) (ae_of_all _ fun _ => rfl),
      zero_mul]
  exact ⟨⟨toyClosedInput⟩, hH, toy_vol_ne_zero,
    ⟨Measurable.of_discrete.aemeasurable, fun j => j.elim0⟩, toyClosed_infF, hY, fun _ => rfl⟩

/-- The toy model with the differential `0`: the interior point is cut off from the boundary
point, a model of a disconnected `Σ` with a closed component. -/
def toyCut : MeasuredModel Bool (Bool → ℝ) 3 1 :=
  { toyModel with d := 0, d_one := rfl }

/-- On `toyCut`, `F(1_{true}) = 0`, so `inf F_g = 0` although `∂Σ ≠ ∅`: lem:positivity rests on
the connectedness of `Σ` (l.719), which the model does not carry. -/
theorem toyCut_infF : toyCut.infF toyMetric (fun _ => cN 3) = 0 := by
  set e : Bool → ℝ := fun b => if b then 1 else 0 with he
  have hv : toyCut.vol toyMetric = toyModel.vol toyMetric := rfl
  have hval : toyCut.val e = e := rfl
  have hadm : toyCut.Adm toyMetric e := by
    unfold MeasuredModel.Adm
    rw [hv, hval, toy_normSq_vol_eq]
    simp [he]
  have hF : toyCut.F toyMetric (fun _ => cN 3) e = 0 := by
    have hb : toyCut.bvol toyMetric 0 = toyModel.bvol toyMetric 0 := rfl
    have hd : toyCut.dirichlet toyMetric e = 0 := by
      simp [MeasuredModel.dirichlet, MeasuredModel.gradSq, toyCut]
    unfold MeasuredModel.F traceSobolevQuot
    rw [hd, Fin.sum_univ_one, hb, show toyCut.tr e = e from rfl,
      toy_normSq_bvol e 0 (pSharp_pos (le_refl 3))]
    simp [he]
  have hnn : ∀ u, 0 ≤ toyCut.F toyMetric (fun _ => cN 3) u :=
    toyCut.F_nonneg toyMetric (le_refl 3) (fun _ => (cN_pos (by norm_num)).le)
  unfold MeasuredModel.infF
  refine le_antisymm ?_ (le_csInf ⟨_, ⟨_, hadm, rfl⟩⟩ ?_)
  · rw [← hF]
    exact csInf_le ⟨0, by rintro _ ⟨u, -, rfl⟩; exact hnn u⟩ ⟨_, hadm, rfl⟩
  · rintro _ ⟨u, -, rfl⟩; exact hnn u

end Toy

end Yamabe
