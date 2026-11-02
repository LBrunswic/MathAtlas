import Causal.Flat.Lox.LevelComplete

/-!
# `Causal.Flat.LipLength` — the Gauss map of `S_t` is `1/t`-Lipschitz for the length metrics

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §4.2
(`papers/barbot/legacy/labeled/GHFspace.tex`; line numbers are those of the labelled copy).
One label, marked by the author's ruling (DEC-103; see the checklist and SCOPE for the readings
it rests on):

* **`bprop:lip`** — `GHFspace.tex:1074` (Prop 4.12), marked (DEC-103: length form, 'the usual
  hyperbolic metric' read as the hyperboloid's induced length; **no `sorry`**) — **length form**:
  `lipschitzWith_gaussInduced`
  (`S_t ∩ V` with `InducedLength`, `ℍᵈ` with the induced length of the hyperboloid),
  `lipschitzWith_gaussSpace` (the glued `InducedLengthSpace` of DEC-35), `edist_gaussInduced_le`.
  The chordal form is `minkQ_gaussMap_sub_le` (`Flat/Cosmological`); this file is the passage
  to the length metrics (l.1084–1091) that its `blocked_on` names.

> The Gauss map $n: S_{t} \rightarrow {\mathbb H}^{n-1}$, where ${\mathbb H}^{n-1}$ is equipped
> with its usual hyperbolic metric is $\frac{1}{t}$-Lipschitz. (l.1076–1078)

> Since $T$ is $C^{1}$ and has spacelike fibers, $S_{t}$ admits an induced riemannian metric, and
> for any $p$, $p'$ in $S_{t}$, the distance between them is the infimum of
> $\sum_{i=0}^{N-1} \mid p_{i+1}-p_{i} \mid$ when $p_{0}, \ldots, p_{N}$ describe all the finite
> sequences in $S_{t}$ with $p_{0} = p$, $p_{N}=p'$. (l.1084–1089)

> Since $\epsilon$ can be selected arbitrarly near $t$, the proposition follows. (l.1104–1105)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1` and his `ℍⁿ⁻¹` is `ℍᵈ = graph (hyperboloid d)`
(`= {v | |v|² = −1, v₀ > 0}`, `graph_hyperboloid`).

## What is proved

* **Transfer (general):** a chordal bound `√|F p − F q|² ≤ K √|p − q|²` on `Σ ∩ V`, for a map
  `F` sending `Σ ∩ V` into `Σ' ∩ V'` and Lipschitz curves to Lipschitz curves, makes `F`
  `K`-Lipschitz between `InducedLength Σ V` and `InducedLength Σ' V'`
  (`lipschitzWith_inducedMap`, `K ≠ 0`). Curve level: `lorentzLength (F ∘ γ) ≤ K ·
  lorentzLength γ` (`lorentzLength_le_of_chord`), from the infinitesimal chord: at a point where
  both curves are differentiable, `√|(F∘γ)'|² ≤ K √|γ'|²` (`sqrt_minkQ_deriv_le_of_chord`), the
  limit of the chord quotients.
* **The hyperboloid:** on `ℍᵈ ∩ {v₀ ≤ A}`, `‖u − v‖ ≤ A √|u − v|²`
  (`norm_sub_le_of_minkQ_eq_neg_one`), and `v₀ ≤ u₀ (2 + |u − v|²)`
  (`fst_le_of_minkQ_eq_neg_one`); so the Gauss map sends a Lipschitz curve of `S_t` to a Lipschitz
  curve of `ℍᵈ` (`lipschitzWith_gaussMap_comp`).
* **`bprop:lip`, length form:** for `CosmoRegular Λ`, `t > 0` and every open `V`, the Gauss map
  `S_t ∩ V → ℍᵈ` is `1/t`-Lipschitz (`lipschitzWith_gaussInduced`); the same between the glued
  spaces `InducedLengthSpace d (cosmoLevel Λ t) → InducedLengthSpace d (graph (hyperboloid d))`
  (`lipschitzWith_gaussSpace`). Non-vacuity: the future cone (`lipschitzWith_gaussInduced_cone`,
  `(t, 0) ∈ S_t`).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `Ω` a future complete regular convex domain, `S_t` a level set of `T`, `t > 0` | ✓ carried: `CosmoRegular Λ` (the regular-domain reading, DEC-88), `t > 0` |
| "the induced riemannian metric" of `S_t` (l.1085) | ✓ carried, in DEC-35's reading (the reading of `bcor:level_sets_complete`): the Lipschitz-path induced length, `InducedLength (cosmoLevel Λ t) V` for every open `V`, and `InducedLengthSpace` |
| "its usual hyperbolic metric" on `ℍⁿ⁻¹` (l.1077) | ⚠ reading, ruled DEC-103: the induced length of the hyperboloid `ℍᵈ ⊆ 𝐌ⁿ`, `InducedLength (graph (hyperboloid d)) ⊤` (see SCOPE); its agreement with `arccosh(−⟨u | v⟩)` is not proved |
| `bprop:lip` (**marked**, DEC-103) | the printed `1/t`-Lipschitz statement in **length form** (`lipschitzWith_gaussInduced`, `lipschitzWith_gaussSpace`), under the three readings of this table (DEC-35 induced length on `S_t`, DEC-88 `CosmoRegular`, DEC-103 hyperboloid length); the chordal form (`minkQ_gaussMap_sub_le`, `Flat/Cosmological`) is its input |
| `0 < ε < t`, then `ε → t` (l.1082, l.1104) | ✓ carried: the chordal inequality is taken at `ε = t` directly (`minkQ_gaussMap_sub_le`) |
| `T` is `C¹` (l.1084) | ⚠ weakened: not used |

## SCOPE (disclosed)

* **Ruled DEC-103 (2026-11-02):** `bprop:lip` is marked in length form, 'the usual hyperbolic
  metric' read as the hyperboloid's induced length. Finding kept: the proof (l.1073–1105) drops
  `|π(p) − π(p')|² ≥ 0`, the achronality of the boundary of `Ω`, silently.
* **The route differs from the paper's at the passage l.1084–1091.** The paper writes the
  distance of `S_t` as an infimum of chord sums and applies the chordal inequality chord by
  chord. Here the chordal inequality is applied to the chords `γ(u) − γ(s)` of a Lipschitz
  curve and passed to the limit `u → s` (the derivative is the limit of the chord quotients), so
  the length integrand of `n ∘ γ` is at most `1/t` times that of `γ`; the infimum over paths
  then gives the distance bound. **The chord-sum characterisation of the distance of `S_t`
  (l.1086–1089) is not proved and not used**; nor is the identity "distance = infimum of chord
  sums" for `ℍᵈ`.
* **"Usual hyperbolic metric"** is read as the induced length of `ℍᵈ` in `𝐌ⁿ` (Lipschitz paths,
  `√|γ'|²`), the same construction as for `S_t`. Its agreement with the closed form
  `arccosh(−⟨u | v⟩)` is not proved here (nothing downstream reads it).
* The hypothesis `K ≠ 0` of `lipschitzWith_inducedMap` is needed: with no path between two points
  the distance is `⊤`, and `0 · ⊤ = 0`.
* The Gauss map is not shown continuous on `S_t` here; only along Lipschitz curves, which is all
  the length metric sees.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
prover round for `bprop:lip` (2026-11-02).
-/

open Set Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal NNReal unitInterval

namespace Causal.Flat.LipLength

variable {d : ℕ}

/-! ### The infinitesimal chord -/

/-- **The infinitesimal chord inequality.** If `√|F u − F v|² ≤ K √|γ u − γ v|²` for all `u, v`,
then at a point where both are differentiable `√|F'|² ≤ K √|γ'|²`: the derivative is the limit of
the chord quotients, and `√|·|²` is continuous and absolutely homogeneous. -/
theorem sqrt_minkQ_deriv_le_of_chord {γ F : ℝ → Minkowski d} {K : ℝ}
    (hchord : ∀ u v, √(minkQ (F u - F v)) ≤ K * √(minkQ (γ u - γ v))) {s : ℝ}
    (hγ : DifferentiableAt ℝ γ s) (hF : DifferentiableAt ℝ F s) :
    √(minkQ (deriv F s)) ≤ K * √(minkQ (deriv γ s)) := by
  have hc : Continuous fun v : Minkowski d => √(minkQ v) :=
    Real.continuous_sqrt.comp continuous_minkQ
  have h1 := (hc.tendsto _).comp (hasDerivAt_iff_tendsto_slope.1 hF.hasDerivAt)
  have h2 := ((hc.tendsto _).comp (hasDerivAt_iff_tendsto_slope.1 hγ.hasDerivAt)).const_mul K
  refine le_of_tendsto_of_tendsto' h1 h2 fun u => ?_
  simp only [Function.comp_apply, slope_def_module, sqrt_minkQ_smul]
  calc |(u - s)⁻¹| * √(minkQ (F u - F s)) ≤ |(u - s)⁻¹| * (K * √(minkQ (γ u - γ s))) :=
        mul_le_mul_of_nonneg_left (hchord u s) (abs_nonneg _)
    _ = K * (|(u - s)⁻¹| * √(minkQ (γ u - γ s))) := by ring

/-- **A chordal bound passes to the Lorentzian lengths** of Lipschitz curves (Rademacher a.e.). -/
theorem lorentzLength_le_of_chord {γ F : ℝ → Minkowski d} {K : ℝ} (hK : 0 ≤ K)
    (hchord : ∀ u v, √(minkQ (F u - F v)) ≤ K * √(minkQ (γ u - γ v)))
    {Kγ KF : ℝ≥0} (hγ : LipschitzWith Kγ γ) (hF : LipschitzWith KF F) (a b : ℝ) :
    lorentzLength F a b ≤ ENNReal.ofReal K * lorentzLength γ a b := by
  unfold lorentzLength
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae hγ.ae_differentiableAt_real,
    ae_restrict_of_ae hF.ae_differentiableAt_real] with s hs hs'
  rw [← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (sqrt_minkQ_deriv_le_of_chord hchord hs hs')

/-! ### The hyperboloid: Euclidean against Minkowski chords -/

/-- **On `ℍᵈ ∩ {v₀ ≤ A}`, the Euclidean chord is at most `A` times the Minkowski chord.** With
`u = (a, x)`, `v = (b, y)`: `A²(a − b)² ≤ (A² − 1)‖x − y‖²`, from
`(a − b)(a + b) = ‖x‖² − ‖y‖²` and `A‖x‖ ≤ √(A² − 1) a`. -/
theorem norm_sub_le_of_minkQ_eq_neg_one {u v : Minkowski d} (hu : minkQ u = -1)
    (hv : minkQ v = -1) (hu0 : 0 < u.1) (hv0 : 0 < v.1) {A : ℝ} (huA : u.1 ≤ A) (hvA : v.1 ≤ A) :
    ‖u - v‖ ≤ A * √(minkQ (u - v)) := by
  set a := u.1
  set b := v.1
  set P := ‖u.2‖
  set Q := ‖v.2‖
  set D := ‖u.2 - v.2‖
  have hu' : P ^ 2 = a ^ 2 - 1 := by unfold minkQ at hu; linarith
  have hv' : Q ^ 2 = b ^ 2 - 1 := by unfold minkQ at hv; linarith
  have hP : 0 ≤ P := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  have hD : 0 ≤ D := norm_nonneg _
  have hPQ : |P - Q| ≤ D := abs_norm_sub_norm_le _ _
  have hPQ2 : (P - Q) ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hPQ 2
  have ha1 : 1 ≤ a := by nlinarith
  have hb1 : 1 ≤ b := by nlinarith
  have hA1 : 1 ≤ A := ha1.trans huA
  have hAP : A ^ 2 * P ^ 2 ≤ (A ^ 2 - 1) * a ^ 2 := by rw [hu']; nlinarith
  have hAQ : A ^ 2 * Q ^ 2 ≤ (A ^ 2 - 1) * b ^ 2 := by rw [hv']; nlinarith
  have hPQm : A ^ 2 * (P * Q) ≤ (A ^ 2 - 1) * (a * b) := by
    have h0 : 0 ≤ A ^ 2 * (P * Q) := by positivity
    have h1 : 0 ≤ (A ^ 2 - 1) * (a * b) := by
      have : 0 ≤ A ^ 2 - 1 := by nlinarith
      positivity
    have hsq : (A ^ 2 * (P * Q)) ^ 2 ≤ ((A ^ 2 - 1) * (a * b)) ^ 2 := by
      have := mul_le_mul hAP hAQ (by positivity) (by nlinarith)
      nlinarith
    exact (pow_le_pow_iff_left₀ h0 h1 two_ne_zero).1 hsq
  have hkey2 : A ^ 2 * (P + Q) ^ 2 ≤ (A ^ 2 - 1) * (a + b) ^ 2 := by
    calc A ^ 2 * (P + Q) ^ 2 = A ^ 2 * P ^ 2 + 2 * (A ^ 2 * (P * Q)) + A ^ 2 * Q ^ 2 := by ring
      _ ≤ (A ^ 2 - 1) * a ^ 2 + 2 * ((A ^ 2 - 1) * (a * b)) + (A ^ 2 - 1) * b ^ 2 := by linarith
      _ = (A ^ 2 - 1) * (a + b) ^ 2 := by ring
  have hkey1 : (a - b) ^ 2 * (a + b) ^ 2 ≤ D ^ 2 * (P + Q) ^ 2 := by
    have : (a - b) ^ 2 * (a + b) ^ 2 = (P - Q) ^ 2 * (P + Q) ^ 2 := by
      have e1 : (a - b) * (a + b) = (P - Q) * (P + Q) := by nlinarith
      calc (a - b) ^ 2 * (a + b) ^ 2 = ((a - b) * (a + b)) ^ 2 := by ring
        _ = ((P - Q) * (P + Q)) ^ 2 := by rw [e1]
        _ = _ := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hPQ2 (by positivity)
  have hab : 0 < (a + b) ^ 2 := by positivity
  have hmain : A ^ 2 * (a - b) ^ 2 ≤ (A ^ 2 - 1) * D ^ 2 := by
    have : A ^ 2 * (a - b) ^ 2 * (a + b) ^ 2 ≤ (A ^ 2 - 1) * D ^ 2 * (a + b) ^ 2 := by
      calc A ^ 2 * (a - b) ^ 2 * (a + b) ^ 2 = A ^ 2 * ((a - b) ^ 2 * (a + b) ^ 2) := by ring
        _ ≤ A ^ 2 * (D ^ 2 * (P + Q) ^ 2) := mul_le_mul_of_nonneg_left hkey1 (by positivity)
        _ = D ^ 2 * (A ^ 2 * (P + Q) ^ 2) := by ring
        _ ≤ D ^ 2 * ((A ^ 2 - 1) * (a + b) ^ 2) := mul_le_mul_of_nonneg_left hkey2 (by positivity)
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hab
  have hQd : minkQ (u - v) = -(a - b) ^ 2 + D ^ 2 := by
    simp only [minkQ, Prod.fst_sub, Prod.snd_sub]; rfl
  have hab' : |a - b| ≤ D := by
    have hA2 : 0 < A ^ 2 := by positivity
    have h2 : A ^ 2 * (a - b) ^ 2 ≤ A ^ 2 * D ^ 2 := by
      have : (A ^ 2 - 1) * D ^ 2 ≤ A ^ 2 * D ^ 2 := by nlinarith [sq_nonneg D]
      linarith
    have h3 : |a - b| ^ 2 ≤ D ^ 2 := by rw [sq_abs]; exact le_of_mul_le_mul_left h2 hA2
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) hD two_ne_zero).1 h3
  have hDle : D ≤ A * √(minkQ (u - v)) := by
    have hA0 : 0 ≤ A := by linarith
    rw [← Real.sqrt_sq hD, ← Real.sqrt_sq hA0, ← Real.sqrt_mul (sq_nonneg A)]
    exact Real.sqrt_le_sqrt (by rw [hQd]; nlinarith)
  have hn : ‖u - v‖ = max ‖a - b‖ D := Prod.norm_def _
  rw [hn, Real.norm_eq_abs]
  exact max_le (hab'.trans hDle) hDle

/-- **A bounded Minkowski chord bounds the time coordinate on `ℍᵈ`:**
`v₀ ≤ u₀ (2 + |u − v|²)` (`2 + |u − v|² = −2⟨u | v⟩`, and `−⟨u | v⟩ ≥ v₀ (u₀ − ‖u⃗‖) ≥ v₀/(2u₀)`). -/
theorem fst_le_of_minkQ_eq_neg_one {u v : Minkowski d} (hu : minkQ u = -1)
    (hv : minkQ v = -1) (hu0 : 0 < u.1) (hv0 : 0 < v.1) :
    v.1 ≤ u.1 * (2 + minkQ (u - v)) := by
  set a := u.1
  set b := v.1
  set P := ‖u.2‖
  set Q := ‖v.2‖
  set D := ‖u.2 - v.2‖
  have hu' : P ^ 2 = a ^ 2 - 1 := by unfold minkQ at hu; linarith
  have hv' : Q ^ 2 = b ^ 2 - 1 := by unfold minkQ at hv; linarith
  have hP : 0 ≤ P := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  have hPQ2 : (P - Q) ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_norm_sub_norm_le _ _) 2
  have hQd : minkQ (u - v) = -(a - b) ^ 2 + D ^ 2 := by
    simp only [minkQ, Prod.fst_sub, Prod.snd_sub]; rfl
  have hPa : P ≤ a := (pow_le_pow_iff_left₀ hP hu0.le two_ne_zero).1 (by linarith)
  have hQb : Q ≤ b := (pow_le_pow_iff_left₀ hQ hv0.le two_ne_zero).1 (by linarith)
  have hid : 2 - (a - b) ^ 2 + (P - Q) ^ 2 = 2 * (a * b - P * Q) := by nlinarith
  have h1 : a * (2 - (a - b) ^ 2 + (P - Q) ^ 2) ≤ a * (2 + minkQ (u - v)) := by
    rw [hQd]; exact mul_le_mul_of_nonneg_left (by linarith) hu0.le
  have h2 : b * (a - P) ≤ a * b - P * Q := by nlinarith [mul_le_mul_of_nonneg_left hQb hP]
  have h3 : 1 ≤ 2 * a * (a - P) := by nlinarith
  have h4 : b ≤ 2 * a * (b * (a - P)) := by nlinarith
  rw [hid] at h1
  nlinarith

/-! ### Transfer of a chordal bound to the induced lengths -/

section Transfer

variable {S S' : Set (Minkowski d)} {V V' : Opens (Minkowski d)} {F : Minkowski d → Minkowski d}

/-- The map `F`, read between induced length spaces. -/
def inducedMap (F : Minkowski d → Minkowski d)
    (hF : ∀ p ∈ S ∩ (V : Set (Minkowski d)), F p ∈ S' ∩ (V' : Set (Minkowski d))) :
    InducedLength S V → InducedLength S' V' := fun x =>
  InducedLength.toSubtype.symm
    ⟨F (InducedLength.toSubtype x : Minkowski d), hF _ (InducedLength.toSubtype x).2⟩

/-- `inducedMap F` is `F` on points. -/
theorem toSubtype_inducedMap
    (hF : ∀ p ∈ S ∩ (V : Set (Minkowski d)), F p ∈ S' ∩ (V' : Set (Minkowski d)))
    (x : InducedLength S V) :
    (InducedLength.toSubtype (inducedMap F hF x) : Minkowski d) =
      F (InducedLength.toSubtype x : Minkowski d) := rfl

/-- The extension of a curve of `X` stays in `X`. -/
theorem curveExtend_mem {X : Set (Minkowski d)} (γ : C(I, X)) (s : ℝ) : curveExtend γ s ∈ X :=
  (γ _).2

/-- The image of a path under `F`, when `F ∘ γ` is continuous. -/
def pathMap
    (hF : ∀ p ∈ S ∩ (V : Set (Minkowski d)), F p ∈ S' ∩ (V' : Set (Minkowski d)))
    {x y : ↥(S ∩ (V : Set (Minkowski d)))} (γ : Path x y)
    (hc : Continuous (F ∘ curveExtend γ.toContinuousMap)) :
    Path (⟨F x, hF _ x.2⟩ : ↥(S' ∩ (V' : Set (Minkowski d)))) ⟨F y, hF _ y.2⟩ where
  toFun t := ⟨F (γ t), hF _ (γ t).2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    convert hc.comp continuous_subtype_val using 1
    funext t
    simp only [Function.comp_apply, curveExtend, IccExtend_val]
    rfl
  source' := Subtype.ext (by simp only [Path.source])
  target' := Subtype.ext (by simp only [Path.target])

/-- The extension of the image path is `F` composed with the extension. -/
theorem curveExtend_pathMap
    (hF : ∀ p ∈ S ∩ (V : Set (Minkowski d)), F p ∈ S' ∩ (V' : Set (Minkowski d)))
    {x y : ↥(S ∩ (V : Set (Minkowski d)))} (γ : Path x y)
    (hc : Continuous (F ∘ curveExtend γ.toContinuousMap)) :
    curveExtend (pathMap hF γ hc).toContinuousMap = F ∘ curveExtend γ.toContinuousMap := rfl

/-- **A chordal Lipschitz bound passes to the induced lengths.** If `F` maps `Σ ∩ V` into
`Σ' ∩ V'`, satisfies the chordal bound `√|F p − F q|² ≤ K √|p − q|²` on `Σ ∩ V`, and maps
Lipschitz curves to Lipschitz curves, then `F` is `K`-Lipschitz for the induced length metrics. -/
theorem lipschitzWith_inducedMap {K : ℝ≥0} (hK : K ≠ 0)
    (hF : ∀ p ∈ S ∩ (V : Set (Minkowski d)), F p ∈ S' ∩ (V' : Set (Minkowski d)))
    (hchord : ∀ p ∈ S ∩ (V : Set (Minkowski d)), ∀ q ∈ S ∩ (V : Set (Minkowski d)),
      √(minkQ (F p - F q)) ≤ K * √(minkQ (p - q)))
    (hlip : ∀ γ : C(I, ↥(S ∩ (V : Set (Minkowski d)))), IsLipschitzCurve γ →
      ∃ L : ℝ≥0, LipschitzWith L (F ∘ curveExtend γ)) :
    LipschitzWith K (inducedMap F hF) := by
  intro x y
  rw [InducedLength.edist_def, InducedLength.edist_def,
    ENNReal.mul_iInf_of_ne (ENNReal.coe_ne_zero.2 hK) ENNReal.coe_ne_top]
  refine le_iInf fun γ => ?_
  by_cases hγ : IsLipschitzCurve γ.toContinuousMap
  · obtain ⟨Lγ, hLγ⟩ := hγ
    obtain ⟨L, hL⟩ := hlip _ ⟨Lγ, hLγ⟩
    let γ' := pathMap hF γ hL.continuous
    have hγ' : IsLipschitzCurve γ'.toContinuousMap := ⟨L, hL⟩
    refine (iInf_le _ γ').trans ?_
    rw [lengthOn_of_isLipschitzCurve hγ', lengthOn_of_isLipschitzCurve ⟨Lγ, hLγ⟩,
      curveExtend_pathMap, ← ENNReal.ofReal_coe_nnreal]
    exact lorentzLength_le_of_chord K.coe_nonneg
      (fun u v => hchord _ (curveExtend_mem _ u) _ (curveExtend_mem _ v)) hLγ hL 0 1
  · rw [lengthOn_of_not_isLipschitzCurve hγ, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hK)]
    exact le_top

end Transfer

/-! ### `bprop:lip`: the Gauss map -/

section Gauss

variable {Λ : Set (PenroseSphere d × ℝ)}

/-- The Gauss map lands in the unit future hyperboloid `ℍᵈ = graph (hyperboloid d)`. -/
theorem gaussMap_mem_hyperboloid (h : CosmoRegular Λ) {p : Minkowski d}
    (hp : p ∈ omegaPlus Λ) : gaussMap Λ p ∈ graph (hyperboloid d) := by
  rw [graph_hyperboloid]
  exact ⟨minkQ_gaussMap h hp, (isFutureTimelike_gaussMap h hp).1⟩

/-- The Gauss map sends `S_t ∩ V` into `ℍᵈ ∩ ⊤`. -/
theorem gaussMap_mem_hyperboloid_inter (h : CosmoRegular Λ) {t : ℝ} (V : Opens (Minkowski d)) :
    ∀ p ∈ cosmoLevel Λ t ∩ (V : Set (Minkowski d)),
      gaussMap Λ p ∈ graph (hyperboloid d) ∩ ((⊤ : Opens (Minkowski d)) : Set (Minkowski d)) :=
  fun _ hp => ⟨gaussMap_mem_hyperboloid h hp.1.1, trivial⟩

/-- `|n(p) − n(p')|² ≤ |p − p'|² / t² ≤ ‖p − p'‖² / t²` on `S_t`. -/
theorem minkQ_gaussMap_sub_le_norm (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) {p p' : Minkowski d}
    (hp : p ∈ cosmoLevel Λ t) (hp' : p' ∈ cosmoLevel Λ t) :
    minkQ (gaussMap Λ p - gaussMap Λ p') ≤ ‖p - p'‖ ^ 2 / t ^ 2 := by
  have h1 := minkQ_gaussMap_sub_le h ht hp hp'
  have h2 : minkQ (p - p') ≤ ‖p - p'‖ ^ 2 := by
    have : minkQ (p - p') ≤ ‖(p - p').2‖ ^ 2 := by unfold minkQ; nlinarith [sq_nonneg (p - p').1]
    exact this.trans (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le _) 2)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **The Gauss map maps Lipschitz curves of `S_t` to Lipschitz curves** (Euclidean norm of
`𝐌ⁿ`): along a `L`-Lipschitz curve the Gauss map stays in a bounded part
`n₀ ≤ A` of `ℍᵈ`, where the Euclidean chord is at most `A` times the Minkowski chord
(`norm_sub_le_of_minkQ_eq_neg_one`); the chordal `bprop:lip` concludes. -/
theorem lipschitzWith_gaussMap_comp (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t)
    {γ : ℝ → Minkowski d} (hγS : ∀ s, γ s ∈ cosmoLevel Λ t) {L : ℝ≥0} (hγ : LipschitzWith L γ)
    {s₀ : ℝ} {B : ℝ} (hB : ∀ s, ‖γ s - γ s₀‖ ≤ B) :
    ∃ K : ℝ≥0, LipschitzWith K (gaussMap Λ ∘ γ) := by
  set n₀ := gaussMap Λ (γ s₀)
  set A := n₀.1 * (2 + B ^ 2 / t ^ 2)
  have hH : ∀ s, minkQ (gaussMap Λ (γ s)) = -1 ∧ 0 < (gaussMap Λ (γ s)).1 := fun s =>
    ⟨minkQ_gaussMap h (hγS s).1, (isFutureTimelike_gaussMap h (hγS s).1).1⟩
  have hA : ∀ s, (gaussMap Λ (γ s)).1 ≤ A := fun s => by
    have h1 := fst_le_of_minkQ_eq_neg_one (hH s₀).1 (hH s).1 (hH s₀).2 (hH s).2
    have h2 := minkQ_gaussMap_sub_le_norm h ht (hγS s₀) (hγS s)
    have h3 : ‖γ s₀ - γ s‖ ^ 2 ≤ B ^ 2 := by
      rw [norm_sub_rev]
      exact pow_le_pow_left₀ (norm_nonneg _) (hB s) 2
    have h4 : minkQ (n₀ - gaussMap Λ (γ s)) ≤ B ^ 2 / t ^ 2 :=
      h2.trans (div_le_div_of_nonneg_right h3 (by positivity))
    exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) (hH s₀).2.le)
  refine ⟨Real.toNNReal (A * t⁻¹ * L), LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by
    have := (hH s₀).2.le.trans (hA s₀)
    positivity)]
  simp only [Function.comp_apply]
  have hA0 : 0 ≤ A := (hH s₀).2.le.trans (hA s₀)
  calc ‖gaussMap Λ (γ u) - gaussMap Λ (γ v)‖
      ≤ A * √(minkQ (gaussMap Λ (γ u) - gaussMap Λ (γ v))) :=
        norm_sub_le_of_minkQ_eq_neg_one (hH u).1 (hH v).1 (hH u).2 (hH v).2 (hA u) (hA v)
    _ ≤ A * (t⁻¹ * √(minkQ (γ u - γ v))) :=
        mul_le_mul_of_nonneg_left (sqrt_minkQ_gaussMap_sub_le h ht (hγS u) (hγS v)) hA0
    _ ≤ A * (t⁻¹ * ‖γ u - γ v‖) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hA0
        exact (sqrt_minkQ_le _).trans (norm_snd_le _)
    _ ≤ A * (t⁻¹ * (L * ‖u - v‖)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hA0
        rw [← dist_eq_norm, ← dist_eq_norm]; exact hγ.dist_le_mul u v
    _ = A * t⁻¹ * L * ‖u - v‖ := by ring

/-- A Lipschitz curve of `I` extended to `ℝ` stays within `L` of its initial point. -/
theorem norm_curveExtend_sub_le {X : Set (Minkowski d)} (γ : C(I, X)) {L : ℝ≥0}
    (hγ : LipschitzWith L (curveExtend γ)) (s : ℝ) :
    ‖curveExtend γ s - curveExtend γ 0‖ ≤ L := by
  have he : curveExtend γ s = curveExtend γ (projIcc (0 : ℝ) 1 zero_le_one s) := by
    unfold curveExtend; rw [IccExtend_val, IccExtend_apply]; rfl
  rw [he, ← dist_eq_norm]
  refine (hγ.dist_le_mul _ _).trans ?_
  have h1 : dist ((projIcc (0 : ℝ) 1 zero_le_one s : ℝ)) 0 ≤ 1 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (projIcc (0 : ℝ) 1 zero_le_one s).2.1]
    exact (projIcc (0 : ℝ) 1 zero_le_one s).2.2
  calc (L : ℝ) * dist _ 0 ≤ L * 1 := mul_le_mul_of_nonneg_left h1 L.coe_nonneg
    _ = L := mul_one _

/-- The Gauss map of `S_t ∩ V`, read between induced length spaces: `(S_t ∩ V, d_{S_t})` to
`(ℍᵈ, d_{ℍ})`, where `d_{ℍ}` is the induced length of the hyperboloid. -/
noncomputable def gaussInduced (h : CosmoRegular Λ) (t : ℝ) (V : Opens (Minkowski d)) :
    InducedLength (cosmoLevel Λ t) V → InducedLength (graph (hyperboloid d)) ⊤ :=
  inducedMap (gaussMap Λ) (gaussMap_mem_hyperboloid_inter h V)

/-- `gaussInduced` is the Gauss map on points. -/
theorem toSubtype_gaussInduced (h : CosmoRegular Λ) (t : ℝ) (V : Opens (Minkowski d))
    (x : InducedLength (cosmoLevel Λ t) V) :
    (InducedLength.toSubtype (gaussInduced h t V x) : Minkowski d) =
      gaussMap Λ (InducedLength.toSubtype x : Minkowski d) := rfl

/-- **`bprop:lip`, length form** (`GHFspace.tex:1074`): the Gauss map
`n : S_t → ℍᵈ` is `1/t`-Lipschitz for the induced length metrics of `S_t ∩ V` and of the
hyperboloid. -/
theorem lipschitzWith_gaussInduced (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t)
    (V : Opens (Minkowski d)) : LipschitzWith (Real.toNNReal t⁻¹) (gaussInduced h t V) := by
  have hc : ((Real.toNNReal t⁻¹ : ℝ≥0) : ℝ) = t⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 ht.le)
  refine lipschitzWith_inducedMap (by simpa using ht) _ (fun p hp q hq => ?_) fun γ ⟨L, hL⟩ => ?_
  · rw [hc]; exact sqrt_minkQ_gaussMap_sub_le h ht hp.1 hq.1
  · exact lipschitzWith_gaussMap_comp h ht (fun s => (curveExtend_mem γ s).1) hL
      (norm_curveExtend_sub_le γ hL)

/-- **`bprop:lip`, length form, as an inequality of distances.** -/
theorem edist_gaussInduced_le (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t)
    (V : Opens (Minkowski d)) (x y : InducedLength (cosmoLevel Λ t) V) :
    edist (gaussInduced h t V x) (gaussInduced h t V y) ≤ ENNReal.ofReal t⁻¹ * edist x y :=
  lipschitzWith_gaussInduced h ht V x y

/-- The Gauss map between the glued induced length spaces of DEC-35 (`InducedLengthSpace`,
the reading of `bcor:level_sets_complete`), through `Lox.toTopIso`. -/
noncomputable def gaussSpace (h : CosmoRegular Λ) (t : ℝ) :
    InducedLengthSpace d (cosmoLevel Λ t) → InducedLengthSpace d (graph (hyperboloid d)) :=
  fun x => (Lox.toTopIso _).symm (gaussInduced h t ⊤ (Lox.toTopIso _ x))

/-- `gaussSpace` is the Gauss map on points. -/
theorem toSubtype_gaussSpace (h : CosmoRegular Λ) (t : ℝ)
    (x : InducedLengthSpace d (cosmoLevel Λ t)) :
    (InducedLengthSpace.toSubtype (gaussSpace h t x) : Minkowski d) =
      gaussMap Λ (InducedLengthSpace.toSubtype x : Minkowski d) := rfl

/-- **`bprop:lip`, length form, for the glued induced length spaces** (DEC-35): the Gauss map
`n : S_t → ℍᵈ` is `1/t`-Lipschitz. -/
theorem lipschitzWith_gaussSpace (h : CosmoRegular Λ) {t : ℝ} (ht : 0 < t) :
    LipschitzWith (Real.toNNReal t⁻¹) (gaussSpace h t) := by
  have := (Lox.toTopIso (graph (hyperboloid d))).symm.isometry.lipschitz.comp
    ((lipschitzWith_gaussInduced h ht ⊤).comp (Lox.toTopIso (cosmoLevel Λ t)).isometry.lipschitz)
  rw [one_mul, mul_one] at this
  exact this

/-- **Non-vacuity**: the hypotheses are met by the future cone (`d ≥ 1`), whose level `S_t`
contains `(t, 0)`. -/
theorem lipschitzWith_gaussInduced_cone (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    ((t, 0) : Minkowski d) ∈ cosmoLevel (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) t ∧
      LipschitzWith (Real.toNNReal t⁻¹) (gaussInduced (cosmoRegular_cone hd) t ⊤) := by
  have hp : IsFutureTimelike ((t, 0) : Minkowski d) := ⟨ht, by simp [minkQ]; positivity⟩
  refine ⟨⟨by rw [omegaPlus_cone hd]; exact hp, ?_⟩, lipschitzWith_gaussInduced _ ht ⊤⟩
  rw [(cosmoTime_cone hd hp).1]
  simp [minkQ, Real.sqrt_sq ht.le]

end Gauss

end Causal.Flat.LipLength
