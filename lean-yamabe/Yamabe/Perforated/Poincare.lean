import Yamabe.Rellich
import Yamabe.Perforated.Main

/-!
# Perforated def:constants, « both are finite »: `λ₁ ∈ (0, ∞)`, `C_SP < ∞` and the Poincaré inequality `MeanPoincare` from Rellich–Kondrachov and the constancy of energy-free limits, over the measured model and on a compact connected manifold with boundary

Labels (the companion BrunswicPerforated, `papers/perforated`; lines of
`papers/perforated/legacy/labeled/perforated.tex`). NOT marked: partial, see SCOPE.

* `def:constants` — `perforated.tex:316` (l.316–326, and the sentence l.328): the finiteness of
  the two constants that `Yamabe.Perforated.Star3` defines and carries (`0 < λ₁`; some
  Sobolev–Poincaré constant), and the Poincaré inequality `MeanPoincare` that
  `Yamabe.Perforated.Capacity` carries (lem:capstar « by Poincaré », l.394; thm:main). Proved
  over the model from `SobolevIneq`, `RellichProp`, the repaired `ConstLimit` and a non-constant
  function (`MeasuredModel.def_constants_of_analytic`), and with no carried hypothesis on the
  reading model of a compact connected manifold with boundary (`Mfd.readingModel_def_constants`),
  under the readings of OQ-93 and OQ-109, which are open: the mark waits on them.

> Throughout $(\Sigma,g)$ is a compact connected Riemannian $N$-manifold with
> non-empty boundary $\partial\Sigma=\bigsqcup_{j=1}^nB_j$ and Lipschitz metric, and
> $V=\Vol(\Sigma,g)$. We write $\bar u:=V^{-1}\int_\Sigma u\dd V$ [...] (l.311–313)

> \item $\lambda_1=\lambda_1(\Sigma,g)>0$ is the first non-zero Neumann eigenvalue,
>       equivalently the best constant in the Poincaré inequality
>       $\|v-\bar v\|^2_{L^2}\le\lambda_1^{-1}\|\nabla v\|^2_{L^2}$;
> \item $\Csp=\Csp(\Sigma,g)$ is the Sobolev--Poincaré constant, the least $C$ with
>       $\|v-\bar v\|_{L^{\pstar}(\Sigma)}\le C\|\nabla v\|_{L^2(\Sigma)}$ for all
>       $v\in W^{1,2}(\Sigma)$. (l.319–324)

> Both are finite because $\Sigma$ is compact, connected and Lipschitz. (l.328)

## What is proved (no `sorry` in this file)

* **Model layer.** `MeasuredModel.memLp_two_of_rellich` (every value in `L²`, from Rellich at
  the constant sequence); `meanPoincare_of_rellich` (`MeanPoincare`, by the contradiction of
  lem:positivity's proof, l.720: `‖w_k‖₂ = 1`, `w̄_k = 0`, `‖∇w_k‖ → 0`, Rellich, constancy,
  the limit has mean `0`, so it is `0`); `lambda1_pos_iff` (`λ₁ > 0` iff a positive Poincaré
  constant exists and some `v ≠ v̄` in `L²`); `normSq_sub_mean_pos`; `lambda1_pos_of_rellich`
  (`λ₁ ∈ (0, ∞)`); `lambda1_eq_zero_of_forall_const` (`NonConst` cannot be dropped);
  `exists_isSobolevPoincareConst` (`C_SP < ∞` from `SobolevIneq` and `MeanPoincare`, no measure
  hypothesis); the bridges `exists_isPoincareConst_of_meanPoincare`,
  `meanPoincare_of_isPoincareConst`; the assembly `def_constants_of_analytic`.
* **Witnesses.** `toy_def_constants` (every hypothesis of the assembly on the strict two-point
  toy model); `toyCut_lambda1_eq_zero` (on `toyCut`, cut in two, `λ₁ = 0`: connectedness is
  necessary).
* **Manifold layer** (`Yamabe.Mfd`). On a model reading a compact connected manifold with
  boundary: `Mfd.Reads.meanPoincare`, `Reads.exists_isSobolevPoincareConst`, `Reads.lambda1_pos`
  (with `NonConst`), `Reads.def_constants`, and, beyond the label, `Reads.capStar_pos`
  (lem:capstar's `0 < cap*` with `MeanPoincare` and the trace theorem discharged) and
  `Reads.thm_star3_corrected` (`N = 3`). On the reading model, `C¹(M)`:
  `Mfd.exists_ne_of_isLocallyLebesgue`, `Mfd.readingModel_nonConst` (a smooth Urysohn function),
  `Mfd.readingModel_def_constants` and `Mfd.readingModel_thm_star3_corrected`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact (l.311, l.328) | model: ⚠ carried as `IsFiniteMeasure (vol g)` and `RellichProp`; manifold: ✓ `CompactSpace`, `T2Space` (Rellich proved, `μ` finite derived) |
| `Σ` connected (l.311, l.328) | model: ⚠ carried as `ConstLimit` (`toyCut_lambda1_eq_zero`); manifold: ✓ `ConnectedSpace` |
| Lipschitz metric (l.311), « Lipschitz » (l.328) | ⚠ read (OQ-93 (a)): a smooth manifold with boundary and a smooth metric, narrower |
| `v ∈ W^{1,2}(Σ)` (l.324) | ⚠ read: model `D` with measurable values (`hD`); manifold `C¹(M)` (OQ-93 (b)) |
| the Sobolev embedding behind `C_SP` | model: ⚠ carried `SobolevIneq`; manifold: ✓ proved (`Reads.sobolevIneq`) |
| `N ≥ 3` (`p*` finite) | ✓ carried, for `C_SP` on the manifold only |
| `Σ ≠ ∅`, of positive dimension (implicit: some `v ≠ v̄`) | model: ⚠ carried `NonConst`; manifold: ✓ from `μ ≠ 0` (`readingModel_nonConst`) |
| `∂Σ ≠ ∅` (l.312) | ⚠ weakened: not used |
| `V = Vol(Σ, g)` | ⚠ read (OQ-93 (a)): every locally-Lebesgue `μ` |

## SCOPE (disclosed)

* **Not marked** (dispatch; OQ-109, OQ-93). `λ₁` is `Star3`'s best Poincaré constant; « the first
  non-zero Neumann eigenvalue » is not stated (the model has no Laplacian). The two readings of
  item 1 agree only on a connected `Σ` (l.311 assumes it): on a disconnected one the eigenvalue is
  positive and the best constant is `0` (`toyCut_lambda1_eq_zero` on the model). On the manifold,
  `W^{1,2}(Σ)` is `C¹(M)`: `λ₁` over `C¹` is at least, and `C_SP` at most, the `W^{1,2}` one,
  with equality by density (argued, not formalized); the metric is smooth, not Lipschitz.
* **« Both are finite »** is read as `0 < λ₁` (`Star3`'s `sSup` is `0` on an empty or unbounded
  set, so this is `λ₁ ∈ (0, ∞)`) and `∃ C` a Sobolev–Poincaré constant (`C_SP < ∞`); both
  constants are then attained (`Star3`).
* **`NonConst`.** `λ₁ > 0` does not follow from `RellichProp` and `ConstLimit` alone: on a model
  whose functions are all a.e. constant every `λ > 0` is a Poincaré constant and `λ₁ = 0`
  (`lambda1_eq_zero_of_forall_const`). A manifold reading supplies a non-constant function only
  when its `D` has one; the reading model `C¹(M)` does (`readingModel_nonConst`).
* **`hD`.** The values must be measurable: `eLpNorm` of a non-measurable function is an inner
  integral (kb 0023), so Rellich at a constant sequence gives `MemLp` only with `hD`.
* **Junk.** `dirichlet` is `0` at infinite energy; under the hypotheses `MeanPoincare` then forces
  such `v` to be a.e. constant. On a reading every energy is finite.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

/-! ## 1. The model layer -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- The model is not reduced to the constants: some function is not a.e. constant. A manifold of
positive dimension has such functions (`Mfd.readingModel_nonConst`); without one, `λ₁ = 0`
(`lambda1_eq_zero_of_forall_const`). -/
def NonConst : Prop := ∃ v : D, ¬ ∃ c : ℝ, M.val v =ᵐ[M.vol g] fun _ => c

/-- With measurable values, Rellich–Kondrachov puts every function of the model in `L²(Σ)`
(apply it to the constant sequence). -/
theorem memLp_two_of_rellich (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g))
    (hR : M.RellichProp g) (u : D) : MemLp (M.val u) 2 (M.vol g) := by
  obtain ⟨φ, -, f, hf, hlim⟩ := hR (fun _ => u) ⟨M.w12Sq g u, fun _ => le_rfl⟩
  have h0 : eLpNorm (M.val u - f) 2 (M.vol g) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  have hae : M.val u - f =ᵐ[M.vol g] 0 :=
    (eLpNorm_eq_zero_iff ((hD u).sub hf.1) two_ne_zero).mp h0
  have hfu : f =ᵐ[M.vol g] M.val u := by
    filter_upwards [hae] with x hx
    have hx' : M.val u x - f x = 0 := hx
    linarith
  exact hf.ae_eq hfu

/-- **The Poincaré inequality around the mean** (l.320–321, l.328, l.394): from
Rellich–Kondrachov and the constancy of energy-free `L²` limits (the connectedness of `Σ`),
by the contradiction of lem:positivity. -/
theorem meanPoincare_of_rellich [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g))
    (hR : M.RellichProp g) (hC : M.ConstLimit g) : M.MeanPoincare g := by
  set ν := M.vol g with hν
  have hL2 : ∀ u, MemLp (M.val u) 2 ν := M.memLp_two_of_rellich g hD hR
  suffices hK : ∃ K : ℝ, ∀ v : D,
      normSq ν 2 (M.val v - fun _ => M.volMean g v) ≤ K * M.dirichlet g v by
    obtain ⟨K, hK⟩ := hK
    exact ⟨K, fun v => ⟨hL2 v, hK v⟩⟩
  by_cases hV : ν = 0
  · refine ⟨0, fun v => ?_⟩
    rw [zero_mul]
    unfold normSq
    rw [hV, eLpNorm_measure_zero]
    simp
  have hVpos : 0 < (ν Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  by_contra hne
  push Not at hne
  have hseq : ∀ k : ℕ, ∃ v : D, ((k : ℝ) + 1) * M.dirichlet g v <
      normSq ν 2 (M.val v - fun _ => M.volMean g v) := fun k => hne _
  choose v hv using hseq
  set c : ℕ → ℝ := fun k => M.volMean g (v k) with hc
  set a : ℕ → ℝ := fun k => normSq ν 2 (M.val (v k) - fun _ => c k) with ha
  have hapos : ∀ k, 0 < a k := fun k =>
    lt_of_le_of_lt (mul_nonneg (by positivity) (M.dirichlet_nonneg g _)) (hv k)
  set t : ℕ → ℝ := fun k => 1 / Real.sqrt (a k) with ht
  set w : ℕ → D := fun k => t k • (v k - c k • M.one) with hw
  have hval : ∀ k, M.val (w k) = t k • (M.val (v k) - fun _ => c k) := by
    intro k
    simp only [hw, map_smul, M.val_sub_smul_one' (c k) (v k)]
  have ht2 : ∀ k, t k ^ 2 = 1 / a k := by
    intro k
    simp only [ht]
    rw [div_pow, one_pow, Real.sq_sqrt (hapos k).le]
  have hnorm : ∀ k, normSq ν 2 (M.val (w k)) = 1 := by
    intro k
    rw [hval, normSq_smul, ht2, one_div, inv_mul_cancel₀ (hapos k).ne']
  have hdir : ∀ k, M.dirichlet g (w k) < 1 / ((k : ℝ) + 1) := by
    intro k
    simp only [hw]
    rw [M.dirichlet_smul, M.dirichlet_sub_smul_one, ht2, div_mul_eq_mul_div, one_mul,
      div_lt_div_iff₀ (hapos k) (by positivity)]
    have := hv k
    simp only [ha, hc]
    linarith
  have hint : ∀ k, ∫ x, M.val (w k) x ∂ν = 0 := by
    intro k
    rw [hval]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [integral_const_mul, integral_sub ((hL2 _).integrable one_le_two) (integrable_const _),
      integral_const, smul_eq_mul, measureReal_def]
    simp only [hc, volMean]
    rw [← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul, sub_self, mul_zero]
  have hbd : ∃ K : ℝ, ∀ k, M.w12Sq g (w k) ≤ K := ⟨2, fun k => by
    unfold w12Sq
    rw [hnorm k]
    have h1 := hdir k
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith⟩
  obtain ⟨φ, hφ, f, hf, hlim⟩ := hR w hbd
  have hdir0 : Tendsto (fun k => M.dirichlet g (w (φ k))) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => M.dirichlet_nonneg g _) (fun k => (hdir (φ k)).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  obtain ⟨c0, hc0⟩ := hC (fun k => w (φ k)) f hf hdir0 hlim
  have hconv : Tendsto (fun k => ∫ x, M.val (w (φ k)) x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
    have hb : ∀ k, |∫ x, M.val (w (φ k)) x ∂ν - ∫ x, f x ∂ν| ≤
        (ν Set.univ).toReal ^ (1 / 2 : ℝ) * (eLpNorm (M.val (w (φ k)) - f) 2 ν).toReal := by
      intro k
      rw [← integral_sub ((hL2 _).integrable one_le_two) (hf.integrable one_le_two)]
      exact abs_integral_le_mul_eLpNorm_two ((hL2 _).sub hf)
    have hr : Tendsto (fun k => (ν Set.univ).toReal ^ (1 / 2 : ℝ) *
        (eLpNorm (M.val (w (φ k)) - f) 2 ν).toReal) atTop (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim).const_mul
        ((ν Set.univ).toReal ^ (1 / 2 : ℝ))
      simpa using this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact hb k) hr
  have hint0 : ∫ x, f x ∂ν = 0 :=
    tendsto_nhds_unique hconv (by simp only [hint]; exact tendsto_const_nhds)
  have hfc : ∫ x, f x ∂ν = (ν Set.univ).toReal * c0 := by
    rw [integral_congr_ae hc0, integral_const, smul_eq_mul, measureReal_def]
  have hc00 : c0 = 0 := by
    have h : (ν Set.univ).toReal * c0 = 0 := by rw [← hfc, hint0]
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hVpos.ne'
    · exact h
  have heq : ∀ k, eLpNorm (M.val (w (φ k)) - f) 2 ν = eLpNorm (M.val (w (φ k))) 2 ν := by
    intro k
    apply eLpNorm_congr_ae
    filter_upwards [hc0] with x hx
    simp [hx, hc00]
  have hone : ∀ k, eLpNorm (M.val (w k)) 2 ν = 1 := by
    intro k
    have h := hnorm k
    unfold normSq at h
    rw [ENNReal.ofReal_ofNat] at h
    have hfin : eLpNorm (M.val (w k)) 2 ν ≠ ⊤ := (hL2 _).eLpNorm_ne_top
    have h1 : (eLpNorm (M.val (w k)) 2 ν).toReal = 1 :=
      (pow_eq_one_iff_of_nonneg ENNReal.toReal_nonneg two_ne_zero).mp h
    rw [← ENNReal.ofReal_toReal hfin, h1, ENNReal.ofReal_one]
  have hlim' : Tendsto (fun k => eLpNorm (M.val (w (φ k)) - f) 2 ν) atTop (𝓝 0) := hlim
  simp only [heq, hone] at hlim'
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim')

/-- `MeanPoincare` gives a positive Poincaré constant in `Star3`'s sense. -/
theorem exists_isPoincareConst_of_meanPoincare (hP : M.MeanPoincare g) :
    ∃ lam : ℝ, 0 < lam ∧ M.IsPoincareConst g lam := by
  obtain ⟨K, hK⟩ := hP
  have hK1 : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / max K 1, by positivity, fun v => ?_⟩
  have e : (fun x => M.val v x - M.mean g v) = (M.val v - fun _ => M.volMean g v) := by
    rw [mean_eq_volMean]; rfl
  rw [e]
  have h2 : normSq (M.vol g) 2 (M.val v - fun _ => M.volMean g v) ≤ max K 1 * M.dirichlet g v :=
    (hK v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (M.dirichlet_nonneg g v))
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK1]
  linarith [mul_comm (max K 1) (M.dirichlet g v)]

/-- Conversely, a positive Poincaré constant and values in `L²` give `MeanPoincare`. -/
theorem meanPoincare_of_isPoincareConst (hL2 : ∀ v, MemLp (M.val v) 2 (M.vol g)) {lam : ℝ}
    (hl : 0 < lam) (hP : M.IsPoincareConst g lam) : M.MeanPoincare g := by
  refine ⟨1 / lam, fun v => ⟨hL2 v, ?_⟩⟩
  have e : (M.val v - fun _ => M.volMean g v) = (fun x => M.val v x - M.mean g v) := by
    rw [mean_eq_volMean]; rfl
  have h := hP v
  rw [e, div_mul_eq_mul_div, one_mul, le_div_iff₀ hl]
  linarith [mul_comm lam (normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v))]

/-- `λ₁ > 0` exactly when some `λ > 0` is a Poincaré constant and some `v` is not equal to its
mean in `L²` (the `sSup` of `Star3` is `0` on an empty or unbounded set). -/
theorem lambda1_pos_iff : 0 < M.lambda1 g ↔ (∃ lam : ℝ, 0 < lam ∧ M.IsPoincareConst g lam) ∧
    ∃ v : D, 0 < normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) := by
  constructor
  · intro h
    refine ⟨⟨M.lambda1 g, h, M.isPoincareConst_lambda1 g h⟩, ?_⟩
    by_contra hv
    push Not at hv
    have hzero : ∀ v : D, normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) = 0 := fun v =>
      le_antisymm (hv v) (normSq_nonneg _ _ _)
    have hb : ¬ BddAbove {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam} := by
      rintro ⟨B, hB⟩
      have hmem : max B 0 + 1 ∈ {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam} :=
        ⟨by positivity, fun v => by rw [hzero v, mul_zero]; exact M.dirichlet_nonneg g v⟩
      have := hB hmem
      linarith [le_max_left B 0]
    have : M.lambda1 g = 0 := Real.sSup_of_not_bddAbove hb
    linarith
  · rintro ⟨⟨lam, hl, hP⟩, v, hv⟩
    refine M.lambda1_pos g hl hP ⟨M.dirichlet g v / normSq (M.vol g) 2
      (fun x => M.val v x - M.mean g v), ?_⟩
    rintro l ⟨-, hlP⟩
    rw [le_div_iff₀ hv]
    exact hlP v

/-- A function of `L²` that is not a.e. constant is not equal to its mean in `L²`. -/
theorem normSq_sub_mean_pos [IsFiniteMeasure (M.vol g)] {v : D}
    (hv : MemLp (M.val v) 2 (M.vol g)) (hnc : ¬ ∃ c : ℝ, M.val v =ᵐ[M.vol g] fun _ => c) :
    0 < normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) := by
  have hm : MemLp (fun x => M.val v x - M.mean g v) 2 (M.vol g) := hv.sub (memLp_const _)
  rcases (normSq_nonneg (M.vol g) 2 (fun x => M.val v x - M.mean g v)).eq_or_lt with h0 | h0
  · exfalso
    apply hnc
    refine ⟨M.mean g v, ?_⟩
    unfold normSq at h0
    rw [ENNReal.ofReal_ofNat] at h0
    have h1 : (eLpNorm (fun x => M.val v x - M.mean g v) 2 (M.vol g)).toReal = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp h0.symm
    have h2 : eLpNorm (fun x => M.val v x - M.mean g v) 2 (M.vol g) = 0 := by
      rcases ENNReal.toReal_eq_zero_iff _ |>.mp h1 with h | h
      · exact h
      · exact absurd h hm.eLpNorm_ne_top
    have h3 := (eLpNorm_eq_zero_iff hm.1 two_ne_zero).mp h2
    filter_upwards [h3] with x hx
    have hx' : M.val v x - M.mean g v = 0 := hx
    linarith
  · exact h0

/-- **`NonConst` cannot be dropped**: on a model whose functions are all a.e. constant, every
`λ > 0` is a Poincaré constant, so `λ₁ = sSup (0, ∞) = 0`. -/
theorem lambda1_eq_zero_of_forall_const [IsFiniteMeasure (M.vol g)]
    (h : ∀ v : D, ∃ c : ℝ, M.val v =ᵐ[M.vol g] fun _ => c) : M.lambda1 g = 0 := by
  have hzero : ∀ v : D, normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) = 0 := by
    intro v
    obtain ⟨c, hc⟩ := h v
    by_cases hV : M.vol g = 0
    · unfold normSq
      rw [hV, eLpNorm_measure_zero]
      simp
    have hVpos : 0 < (M.vol g Set.univ).toReal :=
      ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
    have hmean : M.mean g v = c := by
      unfold mean
      rw [integral_congr_ae hc, integral_const, smul_eq_mul, measureReal_def,
        mul_div_cancel_left₀ _ hVpos.ne']
    have h0 : eLpNorm (fun x => M.val v x - M.mean g v) 2 (M.vol g) = 0 := by
      rw [← eLpNorm_zero (p := 2) (μ := M.vol g) (ε := ℝ)]
      apply eLpNorm_congr_ae
      filter_upwards [hc] with x hx
      simp [hx, hmean]
    unfold normSq
    rw [ENNReal.ofReal_ofNat, h0]
    simp
  refine le_antisymm (not_lt.mp fun hpos => ?_) ?_
  · obtain ⟨-, v, hv⟩ := (M.lambda1_pos_iff g).mp hpos
    rw [hzero v] at hv
    exact lt_irrefl _ hv
  · exact Real.sSup_nonneg fun _ hl => hl.1.le

/-- **`λ₁ ∈ (0, ∞)`** (l.319, l.328) from Rellich–Kondrachov, the constancy of energy-free limits
and a non-constant function. -/
theorem lambda1_pos_of_rellich [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g))
    (hR : M.RellichProp g) (hC : M.ConstLimit g) (hne : M.NonConst g) : 0 < M.lambda1 g := by
  obtain ⟨v, hv⟩ := hne
  exact (M.lambda1_pos_iff g).mpr
    ⟨M.exists_isPoincareConst_of_meanPoincare g (M.meanPoincare_of_rellich g hD hR hC),
      v, M.normSq_sub_mean_pos g (M.memLp_two_of_rellich g hD hR v) hv⟩

/-- **`C_SP < ∞`** (l.322–324, l.328): the Sobolev inequality applied to `v − v̄`, and the
Poincaré inequality. -/
theorem exists_isSobolevPoincareConst (hS : M.SobolevIneq g) (hP : M.MeanPoincare g) :
    ∃ C : ℝ, M.IsSobolevPoincareConst g C := by
  obtain ⟨CS, hCS⟩ := hS
  obtain ⟨K, hK⟩ := hP
  refine ⟨Real.sqrt (max CS 0 * (1 + max K 0)), fun v => ?_⟩
  set c := M.mean g v with hc
  have h1 := hCS (v - c • M.one)
  unfold w12Sq at h1
  rw [M.dirichlet_sub_smul_one, M.val_sub_smul_one'] at h1
  have h2 := (hK v).2
  rw [← mean_eq_volMean, ← hc] at h2
  have hd := M.dirichlet_nonneg g v
  have h3 : normSq (M.vol g) (pStar N) (M.val v - fun _ => c) ≤
      max CS 0 * (1 + max K 0) * M.dirichlet g v := by
    have hw : 0 ≤ M.dirichlet g v + normSq (M.vol g) 2 (M.val v - fun _ => c) :=
      add_nonneg hd (normSq_nonneg _ _ _)
    have h4 : normSq (M.vol g) 2 (M.val v - fun _ => c) ≤ max K 0 * M.dirichlet g v :=
      h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
    calc normSq (M.vol g) (pStar N) (M.val v - fun _ => c)
        ≤ CS * (M.dirichlet g v + normSq (M.vol g) 2 (M.val v - fun _ => c)) := h1
      _ ≤ max CS 0 * (M.dirichlet g v + normSq (M.vol g) 2 (M.val v - fun _ => c)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hw
      _ ≤ max CS 0 * (M.dirichlet g v + max K 0 * M.dirichlet g v) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
      _ = max CS 0 * (1 + max K 0) * M.dirichlet g v := by ring
  have e : (eLpNorm (fun x => M.val v x - c) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal =
      Real.sqrt (normSq (M.vol g) (pStar N) (M.val v - fun _ => c)) :=
    (sqrt_normSq _ _ _).symm
  rw [e, ← Real.sqrt_mul (mul_nonneg (le_max_right _ _) (by positivity))]
  exact Real.sqrt_le_sqrt h3

/-- **def:constants with « both are finite » (l.316–328) over the model**: from the Sobolev
inequality, Rellich–Kondrachov, the constancy of energy-free limits and a non-constant function,
`λ₁ ∈ (0, ∞)` is the best Poincaré constant, `C_SP < ∞` is the least Sobolev–Poincaré constant,
and the Poincaré inequality `MeanPoincare` holds. -/
theorem def_constants_of_analytic [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) (hS : M.SobolevIneq g)
    (hR : M.RellichProp g) (hC : M.ConstLimit g) (hne : M.NonConst g) :
    (0 < M.lambda1 g ∧ M.IsPoincareConst g (M.lambda1 g) ∧
      ∀ lam : ℝ, 0 < lam → M.IsPoincareConst g lam → lam ≤ M.lambda1 g) ∧
    ((∃ C : ℝ, M.IsSobolevPoincareConst g C) ∧ M.IsSobolevPoincareConst g (M.Csp g) ∧
      ∀ C : ℝ, 0 ≤ C → M.IsSobolevPoincareConst g C → M.Csp g ≤ C) ∧
    M.MeanPoincare g := by
  have hP := M.meanPoincare_of_rellich g hD hR hC
  have hl := M.lambda1_pos_of_rellich g hD hR hC hne
  have hSP := M.exists_isSobolevPoincareConst g hS hP
  exact ⟨⟨hl, M.isPoincareConst_lambda1 g hl, fun lam h1 h2 => M.le_lambda1 g hl h1 h2⟩,
    ⟨hSP, M.isSobolevPoincareConst_Csp g hSP, fun C h1 h2 => M.Csp_le g h1 h2⟩, hP⟩

end MeasuredModel

/-! ## 2. The two-point toy model -/

section Toy

/-- The hypotheses of `MeasuredModel.def_constants_of_analytic` hold jointly on the two-point toy
model, and it gives def:constants there. -/
theorem toy_def_constants :
    (0 < toyModel.lambda1 toyMetric ∧
      toyModel.IsPoincareConst toyMetric (toyModel.lambda1 toyMetric) ∧
      ∀ lam : ℝ, 0 < lam → toyModel.IsPoincareConst toyMetric lam →
        lam ≤ toyModel.lambda1 toyMetric) ∧
    ((∃ C : ℝ, toyModel.IsSobolevPoincareConst toyMetric C) ∧
      toyModel.IsSobolevPoincareConst toyMetric (toyModel.Csp toyMetric) ∧
      ∀ C : ℝ, 0 ≤ C → toyModel.IsSobolevPoincareConst toyMetric C →
        toyModel.Csp toyMetric ≤ C) ∧
    toyModel.MeanPoincare toyMetric := by
  haveI := toy_isFiniteMeasure_vol
  refine toyModel.def_constants_of_analytic toyMetric
    (fun _ => Measurable.of_discrete.aestronglyMeasurable) toy_sobolevIneq toy_rellichProp
    toy_constLimit ⟨fun b => if b then 1 else 0, ?_⟩
  rintro ⟨c, hc⟩
  rw [toy_vol] at hc
  have hc' := Measure.ae_count_iff.mp hc
  have h1 : (if true then (1 : ℝ) else 0) = c := hc' true
  have h2 : (if false then (1 : ℝ) else 0) = c := hc' false
  simp at h1 h2
  linarith

/-- On `toyCut` (an interior point cut off from the boundary point, `ConstLimit` fails),
`λ₁ = 0`: the connectedness is necessary. -/
theorem toyCut_lambda1_eq_zero : toyCut.lambda1 toyMetric = 0 := by
  haveI : IsFiniteMeasure (toyCut.vol toyMetric) := toy_isFiniteMeasure_vol
  set e : Bool → ℝ := fun b => if b then 1 else 0 with he
  have hd : toyCut.dirichlet toyMetric e = 0 := by
    simp [MeasuredModel.dirichlet, MeasuredModel.gradSq, toyCut]
  have hnc : ¬ ∃ c : ℝ, toyCut.val e =ᵐ[toyCut.vol toyMetric] fun _ => c := by
    rintro ⟨c, hc⟩
    have hv : toyCut.vol toyMetric = Measure.count := toy_vol
    rw [hv] at hc
    have hc' := Measure.ae_count_iff.mp hc
    have h1 : e true = c := hc' true
    have h2 : e false = c := hc' false
    simp only [he] at h1 h2
    simp at h1 h2
    linarith
  have hpos := toyCut.normSq_sub_mean_pos toyMetric (toy_memLp _ _ _) hnc
  refine le_antisymm (not_lt.mp fun h => ?_) (Real.sSup_nonneg fun _ hl => hl.1.le)
  obtain ⟨⟨lam, hl, hP⟩, -⟩ := (toyCut.lambda1_pos_iff toyMetric).mp h
  have h1 := hP e
  rw [hd] at h1
  have h2 := mul_pos hl hpos
  linarith

end Toy

/-! ## 3. The manifold layer -/

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

namespace Reads

variable {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ} {Mm : MeasuredModel M D N n}
  {gm : FrameMetric M N} {g : RiemannianMetric N M} {μ : Measure M} {σ : Fin n → Measure M}

/-- **The Poincaré inequality `MeanPoincare`** on a model reading a compact connected manifold
with boundary. -/
theorem meanPoincare [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) : Mm.MeanPoincare gm := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gm) := by rw [hr.vol_eq]; infer_instance
  exact Mm.meanPoincare_of_rellich gm hr.hD (hr.rellichProp hμ) (hr.constLimit hμ)

/-- **`C_SP < ∞`** on a model reading a compact connected manifold with boundary. -/
theorem exists_isSobolevPoincareConst (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) :
    ∃ C : ℝ, Mm.IsSobolevPoincareConst gm C := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  exact Mm.exists_isSobolevPoincareConst gm (hr.sobolevIneq hN hμ) (hr.meanPoincare hμ)

/-- **`λ₁ ∈ (0, ∞)`** on a model reading a compact connected manifold with boundary, once the
model has a non-constant function. -/
theorem lambda1_pos [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) (hne : Mm.NonConst gm) :
    0 < Mm.lambda1 gm := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gm) := by rw [hr.vol_eq]; infer_instance
  exact Mm.lambda1_pos_of_rellich gm hr.hD (hr.rellichProp hμ) (hr.constLimit hμ) hne

/-- **def:constants with « both are finite »** on a model reading a compact connected manifold
with boundary (with a non-constant function). -/
theorem def_constants (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) (hne : Mm.NonConst gm) :
    (0 < Mm.lambda1 gm ∧ Mm.IsPoincareConst gm (Mm.lambda1 gm) ∧
      ∀ lam : ℝ, 0 < lam → Mm.IsPoincareConst gm lam → lam ≤ Mm.lambda1 gm) ∧
    ((∃ C : ℝ, Mm.IsSobolevPoincareConst gm C) ∧ Mm.IsSobolevPoincareConst gm (Mm.Csp gm) ∧
      ∀ C : ℝ, 0 ≤ C → Mm.IsSobolevPoincareConst gm C → Mm.Csp gm ≤ C) ∧
    Mm.MeanPoincare gm := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gm) := by rw [hr.vol_eq]; infer_instance
  exact Mm.def_constants_of_analytic gm hr.hD (hr.sobolevIneq hN hμ) (hr.rellichProp hμ)
    (hr.constLimit hμ) hne

/-- `0 < cap*` (lem:capstar's positivity, l.394–400) on a model reading a compact connected
manifold with non-empty boundary: `MeanPoincare` and the trace theorem discharged. -/
theorem capStar_pos (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    [∀ j, IsFiniteMeasure (σ j)] (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) (hV : μ ≠ 0) (hB : ∃ j, σ j ≠ 0) :
    0 < Mm.capStar gm := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gm) := by rw [hr.vol_eq]; infer_instance
  haveI : ∀ j, IsFiniteMeasure (Mm.bvol gm j) := fun j => by rw [hr.bvol_eq j]; infer_instance
  obtain ⟨j, hj⟩ := hB
  exact Mm.capStar_pos gm hN (by rw [hr.vol_eq]; exact hV)
    (Mm.bdryS_pos gm ⟨j, by rw [hr.bvol_eq j]; exact hj⟩).ne' (hr.meanPoincare hμ)
    (hr.traceIneq hN hμ hσ)

end Reads

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- A locally-Lebesgue measure has no atoms, so a nonzero one lives on a manifold with two
distinct points. -/
theorem exists_ne_of_isLocallyLebesgue [T2Space M] {μ : Measure M} (hμ : IsLocallyLebesgue N μ)
    (hV : μ ≠ 0) (x : M) : ∃ y, y ≠ x := by
  by_contra h
  push Not at h
  obtain ⟨U, hU, C, hC⟩ := hμ x
  have hA : ({x} : Set M) ⊆ U ∩ (chartAt (EuclideanHalfSpace N) x).source :=
    singleton_subset_iff.mpr ⟨mem_of_mem_nhds hU, mem_chart_source _ x⟩
  have h1 := (hC {x} hA (measurableSet_singleton x)).1
  rw [image_singleton, measure_singleton (μ := (volume : Measure (EuclideanSpace ℝ (Fin N)))),
    mul_zero] at h1
  apply hV
  have huniv : (Set.univ : Set M) = {x} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨mem_univ x, fun y _ => h y⟩
  rw [← Measure.measure_univ_eq_zero, huniv]
  exact le_antisymm h1 bot_le

/-- **The reading model has a non-constant function**: on a compact manifold with boundary and a
nonzero locally-Lebesgue `μ`, a smooth Urysohn function, `0` near one point and `1` near another,
is not `μ`-a.e. constant. -/
theorem readingModel_nonConst [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ) (hV : μ ≠ 0) {n : ℕ} (σ : Fin n → Measure M) :
    (readingModel g μ σ).NonConst (flatFrame N M) := by
  have hne : Nonempty M := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hV (Measure.eq_zero_of_isEmpty μ)
  obtain ⟨x⟩ := hne
  obtain ⟨y, hyx⟩ := exists_ne_of_isLocallyLebesgue hμ hV x
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓡∂ N) (n := 1)
    (isClosed_singleton (x := x)) (isClosed_singleton (x := y))
    (disjoint_singleton.mpr hyx.symm)
  rw [nhdsSet_singleton] at hf0 hf1
  obtain ⟨U, hUf, hUo, hxU⟩ := eventually_nhds_iff.mp hf0
  obtain ⟨W, hWf, hWo, hyW⟩ := eventually_nhds_iff.mp hf1
  have hc1 : IsC1 N (f : M → ℝ) := f.contMDiff
  refine ⟨⟨f, hc1⟩, ?_⟩
  rintro ⟨c, hc⟩
  rw [(reads_readingModel g μ σ).vol_eq] at hc
  have hUpos := measure_pos_of_isOpen g hμ hUo ⟨x, hxU⟩
  have hWpos := measure_pos_of_isOpen g hμ hWo ⟨y, hyW⟩
  have hnull : μ {z | (readingModel g μ σ).val ⟨f, hc1⟩ z ≠ c} = 0 := ae_iff.mp hc
  have hc0 : c = 0 := by
    by_contra h
    apply hUpos.ne'
    refine measure_mono_null (fun z hz => ?_) hnull
    show f z ≠ c
    rw [hUf z hz]
    exact Ne.symm h
  have hc1' : c = 1 := by
    by_contra h
    apply hWpos.ne'
    refine measure_mono_null (fun z hz => ?_) hnull
    show f z ≠ c
    rw [hWf z hz]
    exact Ne.symm h
  rw [hc0] at hc1'
  exact zero_ne_one hc1'

/-- **def:constants with « both are finite » on a compact connected manifold with boundary**,
through its reading model (`W^{1,2}(Σ)` read as `C¹(M)`, OQ-93 (b)): `λ₁ ∈ (0, ∞)` is the best
Poincaré constant, `C_SP < ∞` the least Sobolev–Poincaré constant, and `MeanPoincare` holds. -/
theorem readingModel_def_constants (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (g : RiemannianMetric N M) {μ : Measure M} (hμ : IsLocallyLebesgue N μ) (hV : μ ≠ 0)
    {n : ℕ} (σ : Fin n → Measure M) :
    (0 < (readingModel g μ σ).lambda1 (flatFrame N M) ∧
      (readingModel g μ σ).IsPoincareConst (flatFrame N M)
        ((readingModel g μ σ).lambda1 (flatFrame N M)) ∧
      ∀ lam : ℝ, 0 < lam → (readingModel g μ σ).IsPoincareConst (flatFrame N M) lam →
        lam ≤ (readingModel g μ σ).lambda1 (flatFrame N M)) ∧
    ((∃ C : ℝ, (readingModel g μ σ).IsSobolevPoincareConst (flatFrame N M) C) ∧
      (readingModel g μ σ).IsSobolevPoincareConst (flatFrame N M)
        ((readingModel g μ σ).Csp (flatFrame N M)) ∧
      ∀ C : ℝ, 0 ≤ C → (readingModel g μ σ).IsSobolevPoincareConst (flatFrame N M) C →
        (readingModel g μ σ).Csp (flatFrame N M) ≤ C) ∧
    (readingModel g μ σ).MeanPoincare (flatFrame N M) := by
  exact (reads_readingModel g μ σ).def_constants hN hμ (readingModel_nonConst g hμ hV σ)

end Mfd

/-! ### `N = 3`: thm:star3's carried constants discharged -/

namespace Mfd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- The corrected thm:star3 (`MeasuredModel.thm_star3_corrected`, `Yamabe.Perforated.Star3`) on a
model reading a compact connected `3`-manifold with boundary and having a non-constant function:
its carried `0 < λ₁` and `∃ C` are discharged (`Reads.lambda1_pos`,
`Reads.exists_isSobolevPoincareConst`). -/
theorem Reads.thm_star3_corrected {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ}
    {Mm : MeasuredModel M D 3 n} {gm : FrameMetric M 3} {g : RiemannianMetric 3 M}
    {μ : Measure M} {σ : Fin n → Measure M} [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue 3 μ) (hne : Mm.NonConst gm) :
    Mm.StarIneqSigned gm (star3AtilCorr (μ Set.univ).toReal (Mm.lambda1 gm) (Mm.Csp gm)) := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gm) := by rw [hr.vol_eq]; infer_instance
  have h := Mm.thm_star3_corrected gm hr.hD (hr.lambda1_pos hμ hne)
    (hr.exists_isSobolevPoincareConst le_rfl hμ)
  rwa [hr.vol_eq] at h

/-- The corrected thm:star3 on the reading model of a compact connected `3`-manifold with
boundary (`W^{1,2}(Σ)` read as `C¹(M)`), with no carried hypothesis. -/
theorem readingModel_thm_star3_corrected [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) {μ : Measure M} (hμ : IsLocallyLebesgue 3 μ) (hV : μ ≠ 0)
    {n : ℕ} (σ : Fin n → Measure M) :
    (readingModel g μ σ).StarIneqSigned (flatFrame 3 M)
      (star3AtilCorr (μ Set.univ).toReal ((readingModel g μ σ).lambda1 (flatFrame 3 M))
        ((readingModel g μ σ).Csp (flatFrame 3 M))) :=
  (reads_readingModel g μ σ).thm_star3_corrected hμ (readingModel_nonConst g hμ hV σ)

end Mfd

end Yamabe
