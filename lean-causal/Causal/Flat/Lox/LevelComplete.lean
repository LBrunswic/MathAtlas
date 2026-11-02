import Causal.Flat.Cosmological
import Causal.Flat.CauchyComplete

/-!
# The level sets of the cosmological time are complete for their induced length

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §4.2
(line numbers of the labelled `papers/barbot/legacy/labeled/GHFspace.tex`). One label is marked
(DEC-88, the author's ruling):

* **`bcor:level_sets_complete`** — `GHFspace.tex:1109` (Cor 4.13, l.1109–1142):
  `completeSpace_inducedLength_cosmoLevel` (and `Lox.completeSpace_inducedLength_top_cosmoLevel`),
  every level set `S_t` (`t > 0`) of the cosmological time of `Ω⁺(Λ)` is complete for its induced
  length, no `sorry`; under `CosmoRegular Λ`, read as the paper's intended regular domain
  (DEC-88), "complete" in the reading of "the induced riemannian metric" as the Lipschitz-path
  Lorentzian length `InducedLengthSpace` (DEC-31/35).

Serves, unmarked here, `bprop:regular_cauchy_complete` — `GHFspace.tex:1148` (l.1148–1151, its
"Cauchy-complete"; marked in `Flat/Cosmological` and `Flat/Cla/RegularComplete`).

> Every $S_{t}$ is complete. (l.1110)

> Since $S_{t}$ is riemannian, completeness notions are all equivalent. (l.1114)

> Future complete regular convex domains are globally hyperbolic Cauchy-complete, admitting as
> Cauchy hypersurfaces the level sets of the cosmological time function. (l.1149–1151)

## What it is for
`completeSpace_inducedLength_cosmoLevel` (namespace `Causal.Flat`) is the upstairs half of
`loxo_cauchyComplete` (`Flat/Loxodromic.lean`, `bcor:loxo_proper`), whose former
`SORRY(bcor:loxo_proper)` it closes, with no `sorry`: with it,
`Lox.isCauchyComplete_flatQuotient_cosmo hc (completeSpace_inducedLength_cosmoLevel hc one_pos)`
(`Lox/QuotientComplete.lean`). The same triple is item (1) of `Classification`'s [11.i] family (b)
and of its Misner case (`misnerRegular` is a `CosmoRegular`).

## Main declarations (all proved, no `sorry`)
* `isSpacelikeLipschitzIn_opens_cosmoLevel` / `_top_`: `isSpacelikeLipschitz_cosmoLevel` repackaged
  (frame `g = 1`), in `Ω` and in `𝐌ⁿ` (acausality of `S_t` in `𝐌ⁿ`).
* `toTopIso`: `InducedLengthSpace d S ≃ᵢ InducedLength S ⊤` (`edist_inducedLengthSpace_minkowski`);
  continuity is then `IsSpacelikeLipschitzIn.continuous_toSubtype`.
* `exists_retract_bound`: `(p − r(p))₀ ≤ α + β ‖p⃗‖` on `S_t` (the two null planes); with
  `abs_fst_sub_le_of_mem_cosmoLevel` it bounds the slope of `S_t` over each ball by `c_R < 1`,
  `√(1 − c_R²) = t / (α + βR)`.
* `mul_norm_deriv_snd_le` (pointwise speed bound), `log_growth` (Gronwall, by the FTC for the
  Lipschitz `log (α + β √(‖x⃗‖² + 1))`), `mul_norm_sub_le` (Euclidean ≤ `M/t` × length),
  `bounds_of_edist_lt`, and `completeSpace_inducedLength_top_cosmoLevel`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `Ω⁺(Λ)` future complete regular (l.1148) | ✓ carried: regular domain, the intended reading (DEC-88) — `CosmoRegular Λ` (two null directions, Bonsante's regular domain, `Flat.Cosmological`); the literal "at least 2 elements" (Def 4.4) also admits the half-spaces bounded by a degenerate hyperplane (the unipotent family, l.222–226), where the cosmological time is infinite (`not_cosmoBoundedAsPrinted`); automatic for a nonelementary group (`cosmoRegular_of_invariant`) |
| `t > 0` | ✓ carried |
| "the induced riemannian metric" on `S_t` | ⚠ read: `InducedLengthSpace` (Lipschitz paths, `∫ √|γ'|²`) |

## SCOPE (disclosed)
* **The route differs from the paper's.** The library has no geodesics, and Barbot's proof
  (l.1112–1142) follows an incomplete geodesic through `bprop:lip`. Here: a Cauchy sequence is
  Euclidean-bounded, because along a curve of `S_t` the slope is `≤ √(1 − t²/(α + βρ)²)`, so
  `d/ds log (α + βρ) ≤ (β/t) · speed` (`ρ = √(‖x⃗‖² + 1)`); on a bounded part the Euclidean
  displacement is at most `(α + βR)/t` times the length, so the sequence is Euclidean-Cauchy; its
  limit lies on the closed `S_t` (`isClosed_cosmoLevel`), and the induced-length and subspace
  topologies agree (`IsSpacelikeLipschitzIn.isHomeomorph_toSubtype`'s two halves). The Gauss map
  and `bprop:lip` are not used.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written for the Barbot
campaign (Lox round, L1), after the plan `/tmp/loxplan/L1_LevelComplete.lean` (route changed, see
SCOPE).
-/

namespace Causal.Flat.Lox

open Set TopologicalSpace Topology Filter Metric MeasureTheory
open scoped NNReal ENNReal unitInterval Pointwise

variable {d : ℕ} {Λ : Set (PenroseSphere d × ℝ)}

/-! ### (1) The spacelike-Lipschitz field, in `Ω` and in `𝐌ⁿ` -/

/-- `isSpacelikeLipschitz_cosmoLevel` repackaged as `IsSpacelikeLipschitzIn Ω S_t` (frame `1`). -/
theorem isSpacelikeLipschitzIn_opens_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    IsSpacelikeLipschitzIn h.regular.opens (cosmoLevel Λ t) := by
  obtain ⟨hsub, hach, hloc⟩ := isSpacelikeLipschitz_cosmoLevel h ht
  refine ⟨hsub, hach, fun p hp => ?_⟩
  obtain ⟨O, U, f, c, hc, hpO, hOV, hU, hf, hgr⟩ := hloc p hp
  exact ⟨1, O, U, f, c, hc, hpO, hOV, hU, hf, by rw [one_smul, one_smul]; exact hgr⟩

/-- The same, in the whole of `𝐌ⁿ` (`S_t` is acausal in `𝐌ⁿ`). -/
theorem isSpacelikeLipschitzIn_top_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    IsSpacelikeLipschitzIn ⊤ (cosmoLevel Λ t) := by
  obtain ⟨-, -, hloc⟩ := isSpacelikeLipschitz_cosmoLevel h ht
  refine ⟨fun _ _ => trivial, fun p hp q hq hlt => ?_, fun p hp => ?_⟩
  · have hv := lt_top_iff_minkQ.1 hlt
    have := isAcausal_cosmoLevel h t p hp q hq (le_top_iff_minkQ.2 hv.isFutureCausal)
    have h0 := hv.1
    rw [this, sub_self] at h0
    exact lt_irrefl _ h0
  · obtain ⟨O, U, f, c, hc, hpO, -, hU, hf, hgr⟩ := hloc p hp
    exact ⟨1, O, U, f, c, hc, hpO, le_top, hU, hf, by rw [one_smul, one_smul]; exact hgr⟩

/-- The glued length space of `S ⊆ 𝐌ⁿ` is isometric to `InducedLength S ⊤`
(`edist_inducedLengthSpace_minkowski`). -/
noncomputable def toTopIso (S : Set (Minkowski d)) : InducedLengthSpace d S ≃ᵢ InducedLength S ⊤ :=
  IsometryEquiv.mk ((InducedLengthSpace.toSubtype.trans (interTopHomeo S).toEquiv).trans
    InducedLength.toSubtype.symm)
    fun x y => (edist_inducedLengthSpace_minkowski (InducedLengthSpace.toSubtype x)
      (InducedLengthSpace.toSubtype y)).symm

/-! ### The slope bound on bounded parts of `S_t` -/

/-- **The retraction is controlled by the position**: `(p − r(p))₀ ≤ α + β ‖p⃗‖` on `S_t`
(the two-direction bound `fst_sub_le_of_mem_closure`, as in `isSpacelikeLipschitz_cosmoLevel`). -/
theorem exists_retract_bound (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ p ∈ cosmoLevel Λ t,
      (p - cosmoRetract Λ p).1 ≤ α + β * ‖p.2‖ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := h.two
  set f := cosmoGraph Λ t
  have hf := lipschitzWith_cosmoGraph h ht
  set κ := 2 - ‖(w₁.1 : EuclideanSpace ℝ (Fin d)) + w₂.1‖
  have hκ : 0 < κ := sub_pos.2 (norm_add_penroseSphere_lt hne)
  refine ⟨abs (w₁.2 + w₂.2 + 4 * |f 0|) / κ + 1, 4 / κ, by positivity, by positivity, fun p hp => ?_⟩
  obtain ⟨hrf, hrp, -⟩ := cosmoRetract_spec h hp.1
  have hb := fst_sub_le_of_mem_closure hw₁ hw₂ (frontier_subset_closure hrf) hrp
  have h1 := abs_minkB_nullVec_le_two_mul_norm w₁.1 p
  have h2 := abs_minkB_nullVec_le_two_mul_norm w₂.1 p
  have hpf : p.1 = f p.2 := by
    have := hp; rw [cosmoLevel_eq_graph h ht] at this; exact mem_graph.1 this
  have hp1 : |p.1| ≤ |f 0| + ‖p.2‖ := by
    rw [hpf]
    have := hf.dist_le_mul p.2 0
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_zero_right] at this
    linarith [abs_sub_abs_le_abs_sub (f p.2) (f 0)]
  have hpn : ‖p‖ ≤ |f 0| + ‖p.2‖ :=
    norm_prod_le_iff.2 ⟨by rwa [Real.norm_eq_abs], by linarith [abs_nonneg (f 0)]⟩
  have key : (p - cosmoRetract Λ p).1 ≤ (w₁.2 + w₂.2 + 4 * |f 0| + 4 * ‖p.2‖) / κ := by
    rw [le_div_iff₀ hκ]
    linarith [neg_abs_le (minkB (nullVec w₁.1) p), neg_abs_le (minkB (nullVec w₂.1) p)]
  calc (p - cosmoRetract Λ p).1 ≤ (w₁.2 + w₂.2 + 4 * |f 0| + 4 * ‖p.2‖) / κ := key
    _ = (w₁.2 + w₂.2 + 4 * |f 0|) / κ + 4 / κ * ‖p.2‖ := by ring
    _ ≤ abs (w₁.2 + w₂.2 + 4 * |f 0|) / κ + 1 + 4 / κ * ‖p.2‖ := by
        have := div_le_div_of_nonneg_right (le_abs_self (w₁.2 + w₂.2 + 4 * |f 0|)) hκ.le
        linarith

/-- `t ≤ (p − r(p))₀` on `S_t`. -/
theorem le_fst_sub_cosmoRetract (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {p : Minkowski d}
    (hp : p ∈ cosmoLevel Λ t) : t ≤ (p - cosmoRetract Λ p).1 := by
  obtain ⟨hzt, hzq⟩ := cosmoRetract_facts h hp.1
  rw [hp.2] at hzq
  have h1 := hzt.1
  have : (p - cosmoRetract Λ p).1 ^ 2 = t ^ 2 + ‖(p - cosmoRetract Λ p).2‖ ^ 2 := by
    unfold minkQ at hzq; linarith
  nlinarith [sq_nonneg ‖(p - cosmoRetract Λ p).2‖]

/-- The slope bound on the part of `S_t` over the ball of radius `R`. -/
theorem abs_fst_sub_le_of_norm_le (h : CosmoRegular Λ) {t α β : ℝ} (hβ : 0 ≤ β)
    (hZ : ∀ p ∈ cosmoLevel Λ t, (p - cosmoRetract Λ p).1 ≤ α + β * ‖p.2‖) {R : ℝ}
    {p p' : Minkowski d} (hp : p ∈ cosmoLevel Λ t) (hp' : p' ∈ cosmoLevel Λ t)
    (hR : ‖p.2‖ ≤ R) (hR' : ‖p'.2‖ ≤ R) :
    |p'.1 - p.1| ≤ √(1 - t ^ 2 / (α + β * R) ^ 2) * ‖p'.2 - p.2‖ :=
  abs_fst_sub_le_of_mem_cosmoLevel h hp hp' ((hZ p hp).trans (by gcongr))
    ((hZ p' hp').trans (by gcongr))

/-! ### Two scalar inequalities -/

/-- `|log a − log b| ≤ |a − b| / m` for `a, b ≥ m > 0`. -/
theorem abs_log_sub_log_le {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have k : ∀ x y : ℝ, m ≤ x → m ≤ y → Real.log x - Real.log y ≤ |x - y| / m := fun x y hx hy => by
    have hx0 := hm.trans_le hx
    have hy0 := hm.trans_le hy
    rw [← Real.log_div hx0.ne' hy0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hx0 hy0)).trans ?_
    rw [div_sub_one hy0.ne']
    calc (x - y) / y ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
      _ ≤ |x - y| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hy
  rw [abs_sub_le_iff]
  exact ⟨k a b ha hb, by rw [abs_sub_comm]; exact k b a hb ha⟩

/-- `r ↦ √(r² + 1)` is `1`-Lipschitz. -/
theorem abs_sqrt_sq_add_one_sub_le (a b : ℝ) : |√(a ^ 2 + 1) - √(b ^ 2 + 1)| ≤ |a - b| := by
  have hA := Real.sq_sqrt (show 0 ≤ a ^ 2 + 1 by positivity)
  have hB := Real.sq_sqrt (show 0 ≤ b ^ 2 + 1 by positivity)
  have hAB : a * b + 1 ≤ √(a ^ 2 + 1) * √(b ^ 2 + 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    calc a * b + 1 ≤ |a * b + 1| := le_abs_self _
      _ = √((a * b + 1) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])
  rw [← sq_le_sq]
  nlinarith

theorem le_sqrt_sq_add_one {r : ℝ} (hr : 0 ≤ r) : r ≤ √(r ^ 2 + 1) :=
  calc r = √(r ^ 2) := (Real.sqrt_sq hr).symm
    _ ≤ √(r ^ 2 + 1) := Real.sqrt_le_sqrt (by linarith)

/-! ### The pointwise speed bound, the growth bound and the comparison along curves of `S_t` -/

/-- **The pointwise speed bound**: at a differentiability point of a curve of `S_t`,
`t ‖Γ'⃗‖ ≤ (α + β ρ) √|Γ'|²`, `ρ = √(‖Γ⃗‖² + 1)`. -/
theorem mul_norm_deriv_snd_le (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {α β : ℝ} (hβ : 0 ≤ β)
    (hZ : ∀ p ∈ cosmoLevel Λ t, (p - cosmoRetract Λ p).1 ≤ α + β * ‖p.2‖)
    {Γ : ℝ → Minkowski d} (hΓS : ∀ s, Γ s ∈ cosmoLevel Λ t) {s : ℝ}
    (hd : DifferentiableAt ℝ Γ s) :
    t * ‖(deriv Γ s).2‖ ≤ (α + β * √(‖(Γ s).2‖ ^ 2 + 1)) * √(minkQ (deriv Γ s)) := by
  set R := √(‖(Γ s).2‖ ^ 2 + 1)
  set B := α + β * R
  have hRlt : ‖(Γ s).2‖ < R := by
    rw [show ‖(Γ s).2‖ = √(‖(Γ s).2‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (lt_add_one _)
  have htB : t ≤ B := (le_fst_sub_cosmoRetract h ht (hΓS s)).trans
    ((hZ _ (hΓS s)).trans (by
      have := mul_le_mul_of_nonneg_left hRlt.le hβ
      simp only [B]; linarith))
  have hB : 0 < B := ht.trans_le htB
  have hev : ∀ᶠ s' in 𝓝 s, ‖(Γ s').2‖ < R :=
    ((continuous_norm.comp continuous_snd).continuousAt.tendsto.comp hd.continuousAt).eventually
      (gt_mem_nhds hRlt)
  have hslope := abs_deriv_fst_le hd (c := √(1 - t ^ 2 / B ^ 2)) (hev.mono fun s' hs' =>
    abs_fst_sub_le_of_norm_le h hβ hZ (hΓS s) (hΓS s') hRlt.le hs'.le)
  have h1 := le_sqrt_minkQ hslope
  have h0 : 0 ≤ 1 - t ^ 2 / B ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact pow_le_pow_left₀ ht.le htB 2
  have h2 : √(1 - √(1 - t ^ 2 / B ^ 2) ^ 2) = t / B := by
    rw [Real.sq_sqrt h0, sub_sub_cancel, ← div_pow, Real.sqrt_sq (by positivity)]
  rw [h2, div_mul_eq_mul_div, div_le_iff₀ hB] at h1
  linarith [mul_comm B (√(minkQ (deriv Γ s)))]

/-- **The growth bound** (a Gronwall inequality, by the fundamental theorem of calculus for the
Lipschitz function `log (α + β ρ)`): along a Lipschitz curve of `S_t`,
`log (α + β ρ(b)) ≤ log (α + β ρ(a)) + (β / t) · length`. -/
theorem log_growth (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 ≤ β) (hZ : ∀ p ∈ cosmoLevel Λ t, (p - cosmoRetract Λ p).1 ≤ α + β * ‖p.2‖)
    {Γ : ℝ → Minkowski d} {K : ℝ≥0} (hΓ : LipschitzWith K Γ) (hΓS : ∀ s, Γ s ∈ cosmoLevel Λ t)
    {a b : ℝ} (hab : a ≤ b) :
    Real.log (α + β * √(‖(Γ b).2‖ ^ 2 + 1)) ≤
      Real.log (α + β * √(‖(Γ a).2‖ ^ 2 + 1)) + β / t * ∫ s in a..b, √(minkQ (deriv Γ s)) := by
  set u : ℝ → ℝ := fun s => α + β * √(‖(Γ s).2‖ ^ 2 + 1) with hu_def
  set φ : ℝ → ℝ := fun s => Real.log (u s) with hφ_def
  have hu : ∀ s, α ≤ u s := fun s => by
    have := Real.sqrt_nonneg (‖(Γ s).2‖ ^ 2 + 1)
    simp only [u]; nlinarith
  have hX : LipschitzWith (1 * K) fun s => (Γ s).2 := LipschitzWith.prod_snd.comp hΓ
  have hφL : LipschitzWith (Real.toNNReal (β * K / α)) φ := LipschitzWith.of_dist_le_mul fun s s' => by
    rw [Real.dist_eq, Real.coe_toNNReal _ (div_nonneg (mul_nonneg hβ K.coe_nonneg) hα.le)]
    refine (abs_log_sub_log_le hα (hu s) (hu s')).trans ?_
    have e : u s - u s' = β * (√(‖(Γ s).2‖ ^ 2 + 1) - √(‖(Γ s').2‖ ^ 2 + 1)) := by
      simp only [u]; ring
    rw [e, abs_mul, abs_of_nonneg hβ]
    have h1 := (abs_sqrt_sq_add_one_sub_le ‖(Γ s).2‖ ‖(Γ s').2‖).trans
      (abs_norm_sub_norm_le (Γ s).2 (Γ s').2)
    have h2 := hX.dist_le_mul s s'
    rw [dist_eq_norm, one_mul] at h2
    rw [div_le_iff₀ hα]
    calc β * |√(‖(Γ s).2‖ ^ 2 + 1) - √(‖(Γ s').2‖ ^ 2 + 1)| ≤ β * (K * dist s s') :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hβ
      _ = β * K / α * dist s s' * α := by field_simp
  have hFTC : ∫ s in a..b, deriv φ s = φ b - φ a :=
    hφL.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hbdΓ : ∀ s, √(minkQ (deriv Γ s)) ≤ K := fun s =>
    (sqrt_minkQ_le _).trans ((norm_snd_le _).trans (norm_deriv_le_of_lipschitz hΓ))
  have hint1 : IntervalIntegrable (deriv φ) volume a b :=
    intervalIntegrable_of_bound (measurable_deriv φ) _ (fun s => norm_deriv_le_of_lipschitz hφL) a b
  have hint2 : IntervalIntegrable (fun s => β / t * √(minkQ (deriv Γ s))) volume a b :=
    intervalIntegrable_of_bound (measurable_const.mul (Real.continuous_sqrt.measurable.comp
      (continuous_minkQ.measurable.comp (measurable_deriv Γ)))) (β / t * K) (fun s => by
        simp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg hβ ht.le) (Real.sqrt_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hbdΓ s) (div_nonneg hβ ht.le)) a b
  have hae : ∀ᵐ s, deriv φ s ≤ β / t * √(minkQ (deriv Γ s)) := by
    filter_upwards [hΓ.ae_differentiableAt_real] with s hd
    set v := (deriv Γ s).2
    have hXd : HasDerivAt (fun s => (Γ s).2) v s :=
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d))).hasFDerivAt.comp_hasDerivAt s
        hd.hasDerivAt
    have hρpos : 0 < √(‖(Γ s).2‖ ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
    have hus : 0 < u s := hα.trans_le (hu s)
    have h1 : HasDerivAt (fun y => ‖(Γ y).2‖ ^ 2 + 1) (2 * inner ℝ (Γ s).2 v) s :=
      hXd.norm_sq.add_const 1
    have h2 := h1.sqrt (ne_of_gt (by positivity))
    have h3 := (h2.const_mul β).const_add α
    have h4 := h3.log hus.ne'
    rw [show φ = fun y => Real.log (α + β * √(‖(Γ y).2‖ ^ 2 + 1)) from rfl, h4.deriv]
    have hnorm := le_sqrt_sq_add_one (norm_nonneg (Γ s).2)
    have hin : inner ℝ (Γ s).2 v ≤ √(‖(Γ s).2‖ ^ 2 + 1) * ‖v‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have hq : 2 * inner ℝ (Γ s).2 v / (2 * √(‖(Γ s).2‖ ^ 2 + 1)) ≤ ‖v‖ := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hpt := mul_norm_deriv_snd_le h ht hβ hZ hΓS hd
    change β * (2 * inner ℝ (Γ s).2 v / (2 * √(‖(Γ s).2‖ ^ 2 + 1))) / u s ≤ _
    calc β * (2 * inner ℝ (Γ s).2 v / (2 * √(‖(Γ s).2‖ ^ 2 + 1))) / u s ≤ β * ‖v‖ / u s := by
          gcongr
      _ ≤ β / t * √(minkQ (deriv Γ s)) := by
          rw [div_le_iff₀ hus]
          calc β * ‖v‖ = β / t * (t * ‖v‖) := by field_simp
            _ ≤ β / t * (u s * √(minkQ (deriv Γ s))) := by gcongr
            _ = β / t * √(minkQ (deriv Γ s)) * u s := by ring
  have hmono := intervalIntegral.integral_mono_ae hab hint1 hint2 hae
  rw [hFTC, intervalIntegral.integral_const_mul] at hmono
  change φ b ≤ φ a + _
  linarith

/-- **The comparison** `t ‖ΔΓ⃗‖ ≤ M · length` along a Lipschitz curve of `S_t` on which
`α + β ρ ≤ M`. -/
theorem mul_norm_sub_le (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {α β : ℝ} (hβ : 0 ≤ β)
    (hZ : ∀ p ∈ cosmoLevel Λ t, (p - cosmoRetract Λ p).1 ≤ α + β * ‖p.2‖)
    {Γ : ℝ → Minkowski d} {K : ℝ≥0} (hΓ : LipschitzWith K Γ) (hΓS : ∀ s, Γ s ∈ cosmoLevel Λ t)
    {a b : ℝ} (hab : a ≤ b) {M : ℝ}
    (hM : ∀ s ∈ Icc a b, α + β * √(‖(Γ s).2‖ ^ 2 + 1) ≤ M) :
    t * ‖(Γ b).2 - (Γ a).2‖ ≤ M * ∫ s in a..b, √(minkQ (deriv Γ s)) := by
  have hX : LipschitzWith (1 * K) fun s => (Γ s).2 := LipschitzWith.prod_snd.comp hΓ
  have h1 := norm_sub_le_integral_norm_deriv hX hab
  have hbdX : ∀ s, ‖deriv (fun s => (Γ s).2) s‖ ≤ 1 * K := fun s => norm_deriv_le_of_lipschitz hX
  have hbdΓ : ∀ s, √(minkQ (deriv Γ s)) ≤ K := fun s =>
    (sqrt_minkQ_le _).trans ((norm_snd_le _).trans (norm_deriv_le_of_lipschitz hΓ))
  have hM0 : 0 ≤ M := by
    have := hM a ⟨le_rfl, hab⟩
    have := (le_fst_sub_cosmoRetract h ht (hΓS a)).trans (hZ _ (hΓS a))
    have := Real.sqrt_nonneg (‖(Γ a).2‖ ^ 2 + 1)
    have hn := le_sqrt_sq_add_one (norm_nonneg (Γ a).2)
    nlinarith
  have hint1 : IntervalIntegrable (fun s => t * ‖deriv (fun s => (Γ s).2) s‖) volume a b :=
    intervalIntegrable_of_bound (measurable_const.mul (measurable_deriv _).norm) (t * (1 * K))
      (fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hbdX s) ht.le) a b
  have hint2 : IntervalIntegrable (fun s => M * √(minkQ (deriv Γ s))) volume a b :=
    intervalIntegrable_of_bound (measurable_const.mul (Real.continuous_sqrt.measurable.comp
      (continuous_minkQ.measurable.comp (measurable_deriv Γ)))) (M * K) (fun s => by
        simp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM0 (Real.sqrt_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hbdΓ s) hM0) a b
  have h2 := intervalIntegral.integral_mono_ae_restrict hab hint1 hint2 (by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hΓ.ae_differentiableAt_real] with s hs hd
    rw [← snd_deriv_eq Γ hd]
    exact (mul_norm_deriv_snd_le h ht hβ hZ hΓS hd).trans
      (mul_le_mul_of_nonneg_right (hM s hs) (Real.sqrt_nonneg _)))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h2
  nlinarith

/-! ### (3) Completeness -/

/-- **The two bounds for a pair at induced distance `< L`**: with `ρ = √(‖p⃗‖² + 1)`,
`α + β ρ(y) ≤ (α + β ρ(x)) e^{βL/t}` and `t ‖y⃗ − x⃗‖ ≤ (α + β ρ(x)) e^{βL/t} L`. -/
theorem bounds_of_edist_lt (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 ≤ β) (hZ : ∀ p ∈ cosmoLevel Λ t, (p - cosmoRetract Λ p).1 ≤ α + β * ‖p.2‖)
    {x y : InducedLength (cosmoLevel Λ t) ⊤} {L : ℝ} (hL : 0 < L)
    (hxy : edist x y < ENNReal.ofReal L) :
    α + β * √(‖(InducedLength.toSubtype y : Minkowski d).2‖ ^ 2 + 1) ≤
        (α + β * √(‖(InducedLength.toSubtype x : Minkowski d).2‖ ^ 2 + 1)) *
          Real.exp (β / t * L) ∧
      t * ‖(InducedLength.toSubtype y : Minkowski d).2 -
          (InducedLength.toSubtype x : Minkowski d).2‖ ≤
        (α + β * √(‖(InducedLength.toSubtype x : Minkowski d).2‖ ^ 2 + 1)) *
          Real.exp (β / t * L) * L := by
  rw [InducedLength.edist_def, iInf_lt_iff] at hxy
  obtain ⟨γ, hγ⟩ := hxy
  by_cases hL' : IsLipschitzCurve γ.toContinuousMap
  swap
  · rw [lengthOn_of_not_isLipschitzCurve hL'] at hγ; exact absurd hγ (not_lt.2 le_top)
  obtain ⟨K, hK⟩ := hL'
  rw [lengthOn_of_isLipschitzCurve ⟨K, hK⟩, lorentzLength_eq_ofReal_integral hK zero_le_one,
    ENNReal.ofReal_lt_ofReal_iff hL] at hγ
  set Γ := curveExtend γ.toContinuousMap with hΓdef
  have hΓS : ∀ s, Γ s ∈ cosmoLevel Λ t := fun s => by
    rw [hΓdef, curveExtend_path]; exact (γ.extend s).2.1
  have e0 : (InducedLength.toSubtype x : Minkowski d) = Γ 0 := by
    rw [hΓdef, curveExtend_path]; simp
  have e1 : (InducedLength.toSubtype y : Minkowski d) = Γ 1 := by
    rw [hΓdef, curveExtend_path]; simp
  rw [e0, e1]
  have hbdΓ : ∀ s, √(minkQ (deriv Γ s)) ≤ K := fun s =>
    (sqrt_minkQ_le _).trans ((norm_snd_le _).trans (norm_deriv_le_of_lipschitz hK))
  have hint : IntervalIntegrable (fun s => √(minkQ (deriv Γ s))) volume 0 1 :=
    intervalIntegrable_of_bound (Real.continuous_sqrt.measurable.comp
      (continuous_minkQ.measurable.comp (measurable_deriv Γ))) K (fun s => by
        simp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact hbdΓ s) 0 1
  have hpos : ∀ s, 0 < α + β * √(‖(Γ s).2‖ ^ 2 + 1) := fun s =>
    add_pos_of_pos_of_nonneg hα (mul_nonneg hβ (Real.sqrt_nonneg _))
  have hgrow : ∀ s ∈ Icc (0 : ℝ) 1, α + β * √(‖(Γ s).2‖ ^ 2 + 1) ≤
      (α + β * √(‖(Γ 0).2‖ ^ 2 + 1)) * Real.exp (β / t * L) := fun s hs => by
    have h1 := log_growth h ht hα hβ hZ hK hΓS hs.1
    have h2 : ∫ r in (0 : ℝ)..s, √(minkQ (deriv Γ r)) ≤ ∫ r in (0 : ℝ)..1, √(minkQ (deriv Γ r)) :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (ae_of_all _ fun r => Real.sqrt_nonneg _) hint
    have h3 := mul_le_mul_of_nonneg_left (h2.trans hγ.le) (div_nonneg hβ ht.le)
    calc α + β * √(‖(Γ s).2‖ ^ 2 + 1) = Real.exp (Real.log (α + β * √(‖(Γ s).2‖ ^ 2 + 1))) :=
          (Real.exp_log (hpos s)).symm
      _ ≤ Real.exp (Real.log (α + β * √(‖(Γ 0).2‖ ^ 2 + 1)) + β / t * L) :=
          Real.exp_le_exp.2 (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log (hpos 0)]
  refine ⟨hgrow 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
  calc t * ‖(Γ 1).2 - (Γ 0).2‖
      ≤ (α + β * √(‖(Γ 0).2‖ ^ 2 + 1)) * Real.exp (β / t * L) *
          ∫ s in (0 : ℝ)..1, √(minkQ (deriv Γ s)) :=
        mul_norm_sub_le h ht hβ hZ hK hΓS zero_le_one hgrow
    _ ≤ _ := mul_le_mul_of_nonneg_left hγ.le (mul_pos (hpos 0) (Real.exp_pos _)).le

/-- **`bcor:level_sets_complete` in `𝐌ⁿ`** (l.1110): `S_t` is complete for its induced length.
A Cauchy sequence is Euclidean-bounded (the growth bound), hence Euclidean-Cauchy (the
comparison); its limit lies on the closed `S_t`, and the two topologies agree. -/
theorem completeSpace_inducedLength_top_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    CompleteSpace (InducedLength (cosmoLevel Λ t) ⊤) := by
  obtain ⟨α, β, hα, hβ', hZ⟩ := exists_retract_bound h ht
  have hβ := hβ'.le
  have hS := isSpacelikeLipschitzIn_top_cosmoLevel h ht
  set P : InducedLength (cosmoLevel Λ t) ⊤ → Minkowski d :=
    fun x => (InducedLength.toSubtype x : Minkowski d) with hPdef
  have hf := lipschitzWith_cosmoGraph h ht
  have hPf : ∀ x, (P x).1 = cosmoGraph Λ t (P x).2 := fun x => by
    have hmem : P x ∈ cosmoLevel Λ t := (InducedLength.toSubtype x).2.1
    rw [cosmoLevel_eq_graph h ht] at hmem
    exact mem_graph.1 hmem
  have hdist : ∀ x y, dist (P x) (P y) ≤ ‖(P x).2 - (P y).2‖ := fun x y => by
    rw [Prod.dist_eq, hPf x, hPf y]
    refine max_le ?_ (dist_eq_norm _ _).le
    have := hf.dist_le_mul (P x).2 (P y).2
    rwa [NNReal.coe_one, one_mul, dist_eq_norm] at this
  set ρ : InducedLength (cosmoLevel Λ t) ⊤ → ℝ := fun x => α + β * √(‖(P x).2‖ ^ 2 + 1)
    with hρdef
  have hρ0 : ∀ x, 0 < ρ x := fun x =>
    add_pos_of_pos_of_nonneg hα (mul_nonneg hβ (Real.sqrt_nonneg _))
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hP : CauchySeq (P ∘ u) := by
    rw [EMetric.cauchySeq_iff] at hu
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hu (ENNReal.ofReal 1) (by simp)
    set M₀ := ρ (u N₀) * Real.exp (β / t * 1)
    have hbd : ∀ m, N₀ ≤ m → ρ (u m) ≤ M₀ := fun m hm =>
      (bounds_of_edist_lt h ht hα hβ hZ one_pos (hN₀ N₀ le_rfl m hm)).1
    set M₁ := M₀ * Real.exp (β / t * 1)
    have hM₁ : 0 < M₁ := mul_pos (mul_pos (hρ0 _) (Real.exp_pos _)) (Real.exp_pos _)
    set η := min 1 (t * ε / (2 * M₁))
    have hη : 0 < η := lt_min one_pos (by positivity)
    obtain ⟨N₁, hN₁⟩ := hu (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
    refine ⟨max N₀ N₁, fun m hm n hn => ?_⟩
    have hmn := hN₁ m (le_of_max_le_right hm) n (le_of_max_le_right hn)
    obtain ⟨-, h2⟩ := bounds_of_edist_lt h ht hα hβ hZ hη hmn
    have e1 : Real.exp (β / t * η) ≤ Real.exp (β / t * 1) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_left _ _) (div_nonneg hβ ht.le))
    have h3 : ρ (u m) * Real.exp (β / t * η) * η ≤ M₁ * η :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hbd m (le_of_max_le_left hm)) e1
        (Real.exp_pos _).le (mul_pos (hρ0 _) (Real.exp_pos _)).le) hη.le
    have h4 : M₁ * η ≤ t * ε / 2 := by
      calc M₁ * η ≤ M₁ * (t * ε / (2 * M₁)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM₁.le
        _ = t * ε / 2 := by field_simp
    have h5 : t * ‖(P (u n)).2 - (P (u m)).2‖ ≤ t * (ε / 2) := by
      have := h2.trans (h3.trans h4); rw [mul_div_assoc] at this; exact this
    have h6 := le_of_mul_le_mul_left h5 ht
    calc dist ((P ∘ u) m) ((P ∘ u) n) ≤ ‖(P (u m)).2 - (P (u n)).2‖ := hdist _ _
      _ = ‖(P (u n)).2 - (P (u m)).2‖ := norm_sub_rev _ _
      _ < ε := by linarith
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hP
  have hpS : p ∈ cosmoLevel Λ t := (isClosed_cosmoLevel h ht).mem_of_tendsto hp
    (Eventually.of_forall fun n => (InducedLength.toSubtype (u n)).2.1)
  have hp' : p ∈ cosmoLevel Λ t ∩ ((⊤ : Opens (Minkowski d)) : Set (Minkowski d)) :=
    ⟨hpS, trivial⟩
  refine ⟨InducedLength.toSubtype.symm ⟨p, hp'⟩, ?_⟩
  have hcont := hS.toIsLipschitzHypersurfaceIn.continuous_toSubtype_symm
  have hsub : Tendsto (fun n => InducedLength.toSubtype (u n)) atTop (𝓝 ⟨p, hp'⟩) :=
    tendsto_subtype_rng.2 hp
  exact (hcont.tendsto _).comp hsub

end Causal.Flat.Lox

namespace Causal.Flat

variable {d : ℕ} {Λ : Set (PenroseSphere d × ℝ)}

/-- **`bcor:level_sets_complete` with the three fields the descent needs** (l.1110, in the
library's reading): `S_t` is spacelike Lipschitz in `Ω`, complete for its induced length, and the
length topology is finer than (in fact equal to) the subspace topology of `𝐌ⁿ`. -/
theorem completeSpace_inducedLength_cosmoLevel (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    IsSpacelikeLipschitzIn h.regular.opens (cosmoLevel Λ t) ∧
    CompleteSpace (InducedLengthSpace d (cosmoLevel Λ t)) ∧
    Continuous fun x : InducedLengthSpace d (cosmoLevel Λ t) =>
      (InducedLengthSpace.toSubtype x : Minkowski d) := by
  haveI := Lox.completeSpace_inducedLength_top_cosmoLevel h ht
  refine ⟨Lox.isSpacelikeLipschitzIn_opens_cosmoLevel h ht, (Lox.toTopIso _).completeSpace, ?_⟩
  have hc := (Lox.isSpacelikeLipschitzIn_top_cosmoLevel h ht).continuous_toSubtype
  have := continuous_subtype_val.comp (hc.comp (Lox.toTopIso (cosmoLevel Λ t)).continuous)
  exact this

end Causal.Flat
