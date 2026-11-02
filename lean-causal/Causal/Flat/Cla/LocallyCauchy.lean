import Causal.Flat.Nonloxodromic
import Causal.Flat.TitsNull
import Causal.Flat.Loxodromic
import Causal.CompactCauchy
import Causal.CurvesExtend

/-!
# `Causal.Flat.Cla.LocallyCauchy` — the image of an acausal Cauchy surface under an isometric embedding of GH flat spacetimes is locally Cauchy and two-sided

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257). **No
b-label is marked**: `clomax` (Rem 2.3) is a remark, formalized corrected (DEC-44) in
`Flat/Classification.lean` (`absMax_of_cauchyCompact_of_mgh`), and this module proves the one
input of it that was a tagged `sorry` there, `isLocallyCauchyTwoSided_image`
(`Classification.lean:2380`): **sorry-free**, closing it by `exact`. Line numbers are those of the
**labelled** `papers/barbot/legacy/labeled/GHFspace.tex`. Barbot's `𝐌ⁿ` has total dimension `n`;
the library's `Minkowski d = ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's
`n` is `d + 1` (kb/0024).

* `clomax`, Rem 2.3 — `GHFspace.tex:571–578` (the sentence used, l.576–578), unmarked:

  > Cauchy-compact GH spacetimes are
  > automatically absolutely maximal. Indeed, any spacelike
  > hypersurface in a given CGH spacetime is a Cauchy hypersurface.

* §11, proof of Theorem B — `GHFspace.tex:3537–3540`, unmarked:

  > A fundamental observation is that in a GH spacetime, every
  > closed spacelike hypersurface is necessarely a Cauchy surface,
  > hence, every GH spacetime containing an embedded copy of
  > $M$ is necessarely Cauchy-compact.

  "Spacelike hypersurface" is read, as DEC-44's lemma K does (`Causal.CompactCauchy`),
  as **locally Cauchy and two-sided** (`IsLocallyCauchyTwoSided`); the theorem here is that the
  embedded copy `f(S)` of an acausal Cauchy surface `S` of `M` is such a hypersurface of `N`.

## What is proved

* **`isLocallyCauchyTwoSided_image_of_isIsometricEmbedding`** — for `M, N` GH flat spacetimes,
  `f : M → N` an isometric embedding (DEC-45) and `S` an acausal Cauchy surface of `M`, every
  point `x = f s` of `f(S)` has an open `U ∋ x`, causally convex in `N`, in which `f(S) ∩ U` is a
  Cauchy surface of `U`, with both sides `J^±_U(f(S) ∩ U) ∖ f(S)` open. The proof:
  1. **`M` side.** A splitting of `M` along `S` (`flat_exists_isCauchySplitting`, with Splitting's
     `flat_hasChronalCausalFlow`) makes `J^±(S)` closed with `J⁺(S) ∪ J⁻(S) = M` and
     `J⁺(S) ∩ J⁻(S) = S` (`sigma_separe`).
  2. **The chart.** `N` is strongly causal (GH and tarentin, `tarentin_flatCausality`), so a
     causally convex `V ∋ x` lies in the chart source at `x` and in `f(M)`; a ball `B` of the
     chart image of `V` is convex, so its relation is the cone (`le_iff_of_convex`), and the cone
     of `B` is a relation of `M` through the chart isomorphism and `IsIsometricEmbedding.rel_iff`.
  3. **The graph.** Over the small ball of radius `δ` about `x`'s spatial coordinate, every
     vertical segment of `B` meets the chart image of `f(S)`: it runs from `J⁻(S)` to `J⁺(S)`,
     both closed, and is connected (`isPreconnected_closed_iff`); acausality makes the meeting
     point unique and the resulting function `G` **strictly contracting** (no uniform constant).
  4. **The extension.** `F = G ∘ π`, `π` the radial retraction onto the closed ball of radius
     `δ/2` (`ballRetract`, 1-Lipschitz by the variational inequality), is an entire bounded strict
     contraction (`exists_isStrictContraction_extension`), equal to `G` near the centre.
  5. **The local domain** (`graphLocalDomain`, §2): the interior of the set of points within `r`
     of the centre, with `|t − F| < r`, whose causal past down to the graph (or future up to it)
     stays within `r` of the centre. It is saturated under `J⁻` in `{T ≥ 0}` and `J⁺` in
     `{T ≤ 0}` (the cone step `graphCone_past`: compactness of a sphere, not a uniform slope),
     contains the graph points near the centre, and so `graph F` is a Cauchy surface of it by
     LipschitzGraph's `isCauchySurfaceOn_graph_of_saturated`; it is causally convex for the cone
     (`graphLocalDomain_convex`), and its two sides are `{T > 0}`, `{T < 0}`
     (`Jplus_graphLocalDomain`, `Jminus_graphLocalDomain`).
  6. **Back to `N`.** `U` is the chart preimage of the local domain. Cauchy-ness transports along
     the chart (`isEMorphismOn_chartSource` and `IsEMorphismOn.isCauchySurfaceOn_image_iff`),
     the two sides through `mem_Jplus_chart_iff` / `mem_Jminus_chart_iff`, causal convexity
     through `V` and the cone.
* General lemmas, no `sorry`: `ballRetract` and its 1-Lipschitz bound (any real inner product
  space); `tarentin_flatCausality` (every flat spacetime is tarentin; the proof of
  `Flat.TheoremBInputs.flatCausality_tarentin`, which this module may not import); the chart
  morphism `isEMorphismOn_chartSource`.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| `M` GH (ETT's: causal, compact diamonds) | ✓ carried; only causality is used (`hM.1`) |
| `N` GH | ✓ carried; used through strong causality (`GloballyHyperbolic.stronglyCausal`) |
| `f` an isometric embedding (DEC-45: injective local `(Isom 𝐌ⁿ, 𝐌ⁿ)`-morphism) | ✓ carried |
| `S` a Cauchy surface of `M` (DEC-14) | ✓ carried |
| `S` acausal ("spacelike") | ✓ carried; redundant on a flat spacetime (`isAcausal_of_isCauchySurface_of_hasChronalCausalFlow`), kept as the consumer states it |
| second countability | ⚠ weakened: not a hypothesis; the instance `FlatSpacetime.secondCountableTopology` (DEC-49) feeds the flow |
| `M`, `N` in one universe (Classification's statement) | ⚠ weakened: `M : FlatSpacetime.{u} d`, `N : FlatSpacetime.{v} d` |
| `S` compact / closed (l.3538 "closed") | ⚠ weakened: not needed for the local statement |

## SCOPE (disclosed)

* **What is not claimed.** Lemma K itself (local ⇒ global Cauchy) is `Causal.CompactCauchy`;
  `clomax`'s corrected form is assembled in `Flat/Classification.lean`. This module certifies no
  label; it discharges `isLocallyCauchyTwoSided_image` (`Classification.lean:2380`), which it
  closes by `exact` (checked: the same statement, `M N : FlatSpacetime.{u} d`, typechecks as
  `exact Cla.isLocallyCauchyTwoSided_image_of_isIsometricEmbedding _hM _hN _hf _hS _hac`, axioms
  `propext`, `Classical.choice`, `Quot.sound`).
* **Departures from the dispatched plan, none in the statement.** The local graph is obtained
  from the closedness of `J^±(S)` along a splitting (step 1), not from `CurvesExtend`: an
  inextensible extension of a vertical segment need not stay on the segment's line, so it does not
  locate the meeting point on that line. The domain of dependence of a ball-graph is not built as
  `int D(graph|B')`; the local domain of step 5 plays its role with the saturation properties
  LipschitzGraph's criterion asks for, after extending the local graph to an entire strict
  contraction (step 4) so that the criterion applies verbatim.
* `d = 0` is covered uniformly (the sphere of the cone step is then empty; the `|T| < r` clause of
  the local set bounds the time).
* **gx contract (a)–(f)** (`docs/BARBOT.md`): not applicable — no length, metric or
  Lipschitz-slope uniformity is defined here; strict contraction is pointwise.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
prover pass for `Classification.lean`'s `isLocallyCauchyTwoSided_image`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace Metric

universe u v

variable {d : ℕ}


/-! ## §1 The retraction onto a closed ball; extending a local strict contraction -/

section Retraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial retraction of `E` onto `closedBall y₀ ρ`. -/
noncomputable def ballRetract (y₀ : E) (ρ : ℝ) (y : E) : E :=
  if ‖y - y₀‖ ≤ ρ then y else y₀ + (ρ / ‖y - y₀‖) • (y - y₀)

theorem ballRetract_of_le {y₀ y : E} {ρ : ℝ} (h : ‖y - y₀‖ ≤ ρ) : ballRetract y₀ ρ y = y :=
  if_pos h

theorem norm_ballRetract_sub_le {y₀ : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (y : E) :
    ‖ballRetract y₀ ρ y - y₀‖ ≤ ρ := by
  unfold ballRetract
  split_ifs with h
  · exact h
  · push Not at h
    have hpos : 0 < ‖y - y₀‖ := hρ.trans_lt h
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hρ hpos.le),
      div_mul_cancel₀ _ hpos.ne']

/-- The variational inequality of the retraction (it is the metric projection). -/
theorem inner_ballRetract_le {y₀ : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (y w : E) (hw : ‖w - y₀‖ ≤ ρ) :
    inner ℝ (y - ballRetract y₀ ρ y) (w - ballRetract y₀ ρ y) ≤ 0 := by
  unfold ballRetract
  split_ifs with h
  · simp
  · push Not at h
    have ha : 0 < ‖y - y₀‖ := hρ.trans_lt h
    have h1 : y - (y₀ + (ρ / ‖y - y₀‖) • (y - y₀)) = (1 - ρ / ‖y - y₀‖) • (y - y₀) := by
      rw [sub_smul, one_smul]; abel
    have h2 : w - (y₀ + (ρ / ‖y - y₀‖) • (y - y₀)) = (w - y₀) - (ρ / ‖y - y₀‖) • (y - y₀) := by
      abel
    rw [h1, h2, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hi : inner ℝ (y - y₀) (w - y₀) ≤ ‖y - y₀‖ * ρ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hw ha.le)
    have hc : 0 ≤ 1 - ρ / ‖y - y₀‖ := by rw [sub_nonneg, div_le_one ha]; exact h.le
    have h3 : ρ / ‖y - y₀‖ * ‖y - y₀‖ ^ 2 = ‖y - y₀‖ * ρ := by field_simp
    rw [h3]
    exact mul_nonpos_of_nonneg_of_nonpos hc (by linarith)

/-- **The retraction is 1-Lipschitz.** -/
theorem norm_ballRetract_sub_ballRetract_le {y₀ : E} {ρ : ℝ} (hρ : 0 ≤ ρ) (y y' : E) :
    ‖ballRetract y₀ ρ y - ballRetract y₀ ρ y'‖ ≤ ‖y - y'‖ := by
  set p := ballRetract y₀ ρ y
  set q := ballRetract y₀ ρ y'
  have h1 := inner_ballRetract_le hρ y q (norm_ballRetract_sub_le hρ y')
  have h2 := inner_ballRetract_le hρ y' p (norm_ballRetract_sub_le hρ y)
  have key : ‖p - q‖ ^ 2 ≤ inner ℝ (y - y') (p - q) := by
    have : inner ℝ (y - y') (p - q) - ‖p - q‖ ^ 2 =
        -inner ℝ (y - p) (q - p) - inner ℝ (y' - q) (p - q) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    linarith
  have h3 := real_inner_le_norm (y - y') (p - q)
  rcases (norm_nonneg (p - q)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

end Retraction

/-- **A strict contraction on a ball extends, near its centre, to an entire bounded strict
contraction**: `g ∘ π`, `π` the retraction onto `closedBall y₀ (δ/2)`. -/
theorem exists_isStrictContraction_extension {g : EuclideanSpace ℝ (Fin d) → ℝ}
    {y₀ : EuclideanSpace ℝ (Fin d)} {δ : ℝ} (hδ : 0 < δ)
    (hg : ∀ y ∈ ball y₀ δ, ∀ y' ∈ ball y₀ δ, y ≠ y' → |g y - g y'| < ‖y - y'‖) :
    ∃ F : EuclideanSpace ℝ (Fin d) → ℝ, IsStrictContraction F ∧ (∀ y, |F y - g y₀| ≤ δ) ∧
      ∀ y, ‖y - y₀‖ ≤ δ / 2 → F y = g y := by
  have hρ : (0 : ℝ) ≤ δ / 2 := by positivity
  set π := ballRetract y₀ (δ / 2) with hπ
  have hmem : ∀ y, π y ∈ ball y₀ δ := fun y => by
    rw [mem_ball, dist_eq_norm]
    exact (norm_ballRetract_sub_le hρ y).trans_lt (by linarith)
  refine ⟨g ∘ π, fun y y' hne => ?_, fun y => ?_, fun y hy => ?_⟩
  · simp only [comp_apply]
    by_cases he : π y = π y'
    · rw [he, sub_self, abs_zero]; exact norm_pos_iff.2 (sub_ne_zero.2 hne)
    · exact (hg _ (hmem y) _ (hmem y') he).trans_le (norm_ballRetract_sub_ballRetract_le hρ y y')
  · simp only [comp_apply]
    have h0 : π y₀ = y₀ := ballRetract_of_le (by simpa using hρ)
    by_cases he : π y = y₀
    · rw [he, sub_self, abs_zero]; exact hδ.le
    · have := hg _ (hmem y) _ (mem_ball_self hδ) he
      have h2 := norm_ballRetract_sub_le hρ (y₀ := y₀) y
      linarith
  · exact congrArg g (ballRetract_of_le hy)

/-! ## §2 The local domain of dependence of an entire strict contraction, cut to a cylinder -/

section LocalDomain

variable {F : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **The cone step, past side**: around `y₁`, the causal past of a point just above the graph,
down to the graph, stays within `ρ` of `y₁` spatially. -/
theorem graphCone_past (hF : IsStrictContraction F) (y₁ : EuclideanSpace ℝ (Fin d)) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ ε > 0, ∀ p : Minkowski d, ‖p.2 - y₁‖ < ε → timeSub F p < ε →
      ∀ p', (minkowski d).le ⊤ p' p → 0 ≤ timeSub F p' → ‖p'.2 - y₁‖ < ρ := by
  have hlip := hF.lipschitzWith
  have hL : ∀ x y, |F x - F y| ≤ ‖x - y‖ := abs_sub_le_norm_of_lipschitzWith_one hlip
  obtain ⟨c₀, hc₀, hc₀ρ, hsph⟩ : ∃ c₀ : ℝ, 0 ≤ c₀ ∧ c₀ < ρ ∧
      ∀ x ∈ sphere y₁ ρ, |F x - F y₁| ≤ c₀ := by
    rcases (sphere y₁ ρ).eq_empty_or_nonempty with h | h
    · exact ⟨0, le_rfl, hρ, fun x hx => by rw [h] at hx; exact absurd hx (notMem_empty x)⟩
    · obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_sphere y₁ ρ).exists_isMaxOn h
        ((continuous_abs.comp (hlip.continuous.sub continuous_const)).continuousOn)
      have hx₀n : ‖x₀ - y₁‖ = ρ := by rw [← dist_eq_norm]; exact hx₀
      refine ⟨|F x₀ - F y₁|, abs_nonneg _, ?_, fun x hx => hmax hx⟩
      rw [← hx₀n]
      exact hF x₀ y₁ fun h => by rw [h, sub_self, norm_zero] at hx₀n; exact hρ.ne hx₀n
  refine ⟨(ρ - c₀) / 4, by linarith, fun p hp hTp p' hle hT' => ?_⟩
  by_contra hcon
  push Not at hcon
  have hd := minkowski_le_top_iff.1 hle
  set φ : ℝ → ℝ := fun l => ‖(p'.2 + l • (p.2 - p'.2)) - y₁‖ with hφ
  have hφc : ContinuousOn φ (Icc 0 1) :=
    ((continuous_const.add (continuous_id.smul continuous_const)).sub
      continuous_const).norm.continuousOn
  have h0 : φ 0 = ‖p'.2 - y₁‖ := by simp [hφ]
  have h1 : φ 1 = ‖p.2 - y₁‖ := by simp [hφ]
  obtain ⟨l, hl, hlρ⟩ := intermediate_value_Icc' zero_le_one hφc
    (show ρ ∈ Icc (φ 1) (φ 0) by rw [h0, h1]; exact ⟨by linarith, hcon⟩)
  set w : Minkowski d := (p'.1 + l * (p.1 - p'.1), p'.2 + l • (p.2 - p'.2)) with hw
  have hw2 : ‖w.2 - y₁‖ = ρ := hlρ
  have hwp' : ‖w.2 - p'.2‖ ≤ w.1 - p'.1 := by
    simp only [hw, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl.1]
    exact mul_le_mul_of_nonneg_left hd hl.1
  have hpw : ‖p.2 - w.2‖ ≤ p.1 - w.1 := by
    have e1 : p.2 - w.2 = (1 - l) • (p.2 - p'.2) := by simp only [hw, sub_smul, one_smul]; abel
    have e2 : p.1 - w.1 = (1 - l) * (p.1 - p'.1) := by simp only [hw]; ring
    rw [e1, e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hl.2])]
    exact mul_le_mul_of_nonneg_left hd (by linarith [hl.2])
  have hTw : 0 ≤ timeSub F w :=
    hT'.trans (timeSub_le_of_le hlip (minkowski_le_top_iff.2 hwp'))
  have hFw : F y₁ - c₀ ≤ F w.2 := by
    have := hsph w.2 (by rw [mem_sphere, dist_eq_norm]; exact hw2)
    linarith [neg_abs_le (F w.2 - F y₁)]
  have htri : ‖w.2 - y₁‖ ≤ ‖p.2 - w.2‖ + ‖p.2 - y₁‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub w.2 p.2 y₁
    rwa [norm_sub_rev w.2 p.2] at this
  have hFp := hL p.2 y₁
  simp only [timeSub] at hTw hTp
  linarith [le_abs_self (F p.2 - F y₁)]

/-- Time reflection `(t, x) ↦ (−t, x)`. -/
def timeReflect (p : Minkowski d) : Minkowski d := (-p.1, p.2)

theorem le_timeReflect_iff {p q : Minkowski d} :
    (minkowski d).le ⊤ (timeReflect q) (timeReflect p) ↔ (minkowski d).le ⊤ p q := by
  simp only [minkowski_le_top_iff, timeReflect]
  rw [norm_sub_rev]; ring_nf

theorem timeSub_neg_timeReflect (p : Minkowski d) :
    timeSub (fun x => -F x) (timeReflect p) = -timeSub F p := by
  simp [timeSub, timeReflect]; ring

/-- **The cone step, future side**, by time reflection. -/
theorem graphCone_future (hF : IsStrictContraction F) (y₁ : EuclideanSpace ℝ (Fin d)) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ ε > 0, ∀ p : Minkowski d, ‖p.2 - y₁‖ < ε → -ε < timeSub F p →
      ∀ p', (minkowski d).le ⊤ p p' → timeSub F p' ≤ 0 → ‖p'.2 - y₁‖ < ρ := by
  obtain ⟨ε, hε, h⟩ := graphCone_past hF.neg y₁ hρ
  refine ⟨ε, hε, fun p hp hTp p' hle hT' => ?_⟩
  have := h (timeReflect p) hp (by rw [timeSub_neg_timeReflect]; linarith) (timeReflect p')
    (le_timeReflect_iff.2 hle) (by rw [timeSub_neg_timeReflect]; linarith)
  exact this

variable (F) in
/-- The set whose interior is the local domain: within `r` of `y₀` spatially, `|T| < r`, and the
causal past (resp. future) of each point, down (resp. up) to the graph, within `r` of `y₀`. -/
def graphLocalSet (y₀ : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Set (Minkowski d) :=
  {q | ‖q.2 - y₀‖ < r ∧ |timeSub F q| < r ∧
    (0 ≤ timeSub F q → ∀ p, (minkowski d).le ⊤ p q → 0 ≤ timeSub F p → ‖p.2 - y₀‖ < r) ∧
    (timeSub F q ≤ 0 → ∀ p, (minkowski d).le ⊤ q p → timeSub F p ≤ 0 → ‖p.2 - y₀‖ < r)}

variable {y₀ : EuclideanSpace ℝ (Fin d)} {r : ℝ}

theorem graphLocalSet_past (hF : IsStrictContraction F) {q p : Minkowski d}
    (hq : q ∈ graphLocalSet F y₀ r)
    (hpq : (minkowski d).le ⊤ p q) (hp : 0 ≤ timeSub F p) : p ∈ graphLocalSet F y₀ r := by
  have hlip := hF.lipschitzWith
  obtain ⟨-, hqT, hqp, -⟩ := hq
  have hTpq := timeSub_le_of_le hlip hpq
  have hq0 : 0 ≤ timeSub F q := hp.trans hTpq
  refine ⟨hqp hq0 p hpq hp, ?_, fun _ p' hp' hT' => hqp hq0 p' ((minkowski d).le_trans hp' hpq) hT',
    fun hT p' hp' hT' => ?_⟩
  · rw [abs_of_nonneg hp]; rw [abs_of_nonneg hq0] at hqT; linarith
  · have hp0 : timeSub F p = 0 := le_antisymm hT hp
    have hpp' : p = p' := by
      by_contra hne
      have := timeSub_lt_of_le hF hp' hne
      linarith
    subst hpp'
    exact hqp hq0 p hpq hp

theorem graphLocalSet_future (hF : IsStrictContraction F) {q p : Minkowski d}
    (hq : q ∈ graphLocalSet F y₀ r) (hqp : (minkowski d).le ⊤ q p) (hp : timeSub F p ≤ 0) :
    p ∈ graphLocalSet F y₀ r := by
  have hlip := hF.lipschitzWith
  obtain ⟨-, hqT, -, hqf⟩ := hq
  have hTqp := timeSub_le_of_le hlip hqp
  have hq0 : timeSub F q ≤ 0 := hTqp.trans hp
  refine ⟨hqf hq0 p hqp hp, ?_, fun hT p' hp' hT' => ?_,
    fun _ p' hp' hT' => hqf hq0 p' ((minkowski d).le_trans hqp hp') hT'⟩
  · rw [abs_of_nonpos hp]; rw [abs_of_nonpos hq0] at hqT; linarith
  · have hp0 : timeSub F p = 0 := le_antisymm hp hT
    have hpp' : p' = p := by
      by_contra hne
      have := timeSub_lt_of_le hF hp' hne
      linarith
    subst hpp'
    exact hqf hq0 p' hqp hp

/-- **A graph point within `r` of `y₀` is interior to the local set** (both cone steps). -/
theorem mem_interior_graphLocalSet_of_graph (hF : IsStrictContraction F) {q : Minkowski d}
    (hq : timeSub F q = 0) (hqr : ‖q.2 - y₀‖ < r) : q ∈ interior (graphLocalSet F y₀ r) := by
  have hlip := hF.lipschitzWith
  set ρ := r - ‖q.2 - y₀‖ with hρdef
  have hρ : 0 < ρ := by linarith
  have hr : 0 < r := (norm_nonneg _).trans_lt hqr
  obtain ⟨ε₁, hε₁, h₁⟩ := graphCone_past hF q.2 hρ
  obtain ⟨ε₂, hε₂, h₂⟩ := graphCone_future hF q.2 hρ
  set ε := min (min ε₁ ε₂) (min ρ r) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) (lt_min hρ hr)
  have hε1 : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hερ : ε ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  set O : Set (Minkowski d) := {p | ‖p.2 - q.2‖ < ε ∧ |timeSub F p| < ε} with hO
  have hOo : IsOpen O :=
    (isOpen_lt ((continuous_snd.sub continuous_const).norm) continuous_const).inter
      (isOpen_lt (continuous_timeSub hlip).abs continuous_const)
  have hqO : q ∈ O := ⟨by simpa using hε, by rw [hq, abs_zero]; exact hε⟩
  have hspace : ∀ p' : Minkowski d, ‖p'.2 - q.2‖ < ρ → ‖p'.2 - y₀‖ < r := fun p' h => by
    have := norm_sub_le_norm_sub_add_norm_sub p'.2 q.2 y₀
    linarith
  refine interior_maximal (fun p hp => ?_) hOo hqO
  obtain ⟨hp1, hp2⟩ := hp
  have hT := abs_lt.1 hp2
  refine ⟨hspace p (hp1.trans_le hερ), hp2.trans_le hεr, fun _ p' hp' hT' => ?_,
    fun _ p' hp' hT' => ?_⟩
  · exact hspace p' (h₁ p (hp1.trans_le hε1) (hT.2.trans_le hε1) p' hp' hT')
  · exact hspace p' (h₂ p (hp1.trans_le hε2) (by linarith) p' hp' hT')

/-- **The interior of the local set is closed under `J⁻` inside `{T ≥ 0}`.** -/
theorem interior_graphLocalSet_past (hF : IsStrictContraction F) {z q : Minkowski d}
    (hz : z ∈ interior (graphLocalSet F y₀ r)) (hqz : (minkowski d).le ⊤ q z)
    (hq : 0 ≤ timeSub F q) : q ∈ interior (graphLocalSet F y₀ r) := by
  have hlip := hF.lipschitzWith
  rcases hq.lt_or_eq with hq | hq
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
    set z' : Minkowski d := z + ((ε / 2, 0) : Minkowski d) with hz'def
    have hz' : z' ∈ graphLocalSet F y₀ r := by
      refine interior_subset (hball ?_)
      rw [mem_ball, dist_eq_norm, hz'def, add_sub_cancel_left, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      rw [max_eq_left (half_pos hε).le]
      exact half_lt_self hε
    have hz'1 : z'.1 = z.1 + ε / 2 := rfl
    have hz'2 : z'.2 = z.2 := by simp [hz'def]
    set U : Set (Minkowski d) := {p | ‖z'.2 - p.2‖ < z'.1 - p.1} ∩ {p | 0 < timeSub F p}
      with hUdef
    have hUo : IsOpen U :=
      (isOpen_lt (continuous_const.sub continuous_snd).norm
        (continuous_const.sub continuous_fst)).inter
        (isOpen_lt continuous_const (continuous_timeSub hlip))
    have hqU : q ∈ U := by
      refine ⟨?_, hq⟩
      have := minkowski_le_top_iff.1 hqz
      show ‖z'.2 - q.2‖ < z'.1 - q.1
      rw [hz'1, hz'2]
      linarith [half_pos hε]
    refine interior_maximal (fun p hp => ?_) hUo hqU
    exact graphLocalSet_past hF hz' (minkowski_le_top_iff.2 hp.1.le) hp.2.le
  · exact mem_interior_graphLocalSet_of_graph hF hq.symm
      (graphLocalSet_past hF (interior_subset hz) hqz (le_of_eq hq)).1

/-- **The interior of the local set is closed under `J⁺` inside `{T ≤ 0}`.** -/
theorem interior_graphLocalSet_future (hF : IsStrictContraction F) {z q : Minkowski d}
    (hz : z ∈ interior (graphLocalSet F y₀ r)) (hzq : (minkowski d).le ⊤ z q)
    (hq : timeSub F q ≤ 0) : q ∈ interior (graphLocalSet F y₀ r) := by
  have hlip := hF.lipschitzWith
  rcases hq.lt_or_eq with hq | hq
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
    set z' : Minkowski d := z - ((ε / 2, 0) : Minkowski d) with hz'def
    have hz' : z' ∈ graphLocalSet F y₀ r := by
      refine interior_subset (hball ?_)
      rw [mem_ball, dist_eq_norm, hz'def, sub_sub_cancel_left, norm_neg, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      rw [max_eq_left (half_pos hε).le]
      exact half_lt_self hε
    have hz'1 : z'.1 = z.1 - ε / 2 := rfl
    have hz'2 : z'.2 = z.2 := by simp [hz'def]
    set U : Set (Minkowski d) := {p | ‖p.2 - z'.2‖ < p.1 - z'.1} ∩ {p | timeSub F p < 0}
      with hUdef
    have hUo : IsOpen U :=
      (isOpen_lt (continuous_snd.sub continuous_const).norm
        (continuous_fst.sub continuous_const)).inter
        (isOpen_lt (continuous_timeSub hlip) continuous_const)
    have hqU : q ∈ U := by
      refine ⟨?_, hq⟩
      have := minkowski_le_top_iff.1 hzq
      show ‖q.2 - z'.2‖ < q.1 - z'.1
      rw [hz'1, hz'2]
      linarith [half_pos hε]
    refine interior_maximal (fun p hp => ?_) hUo hqU
    exact graphLocalSet_future hF hz' (minkowski_le_top_iff.2 hp.1.le) hp.2.le
  · exact mem_interior_graphLocalSet_of_graph hF hq
      (graphLocalSet_future hF (interior_subset hz) hzq (le_of_eq hq)).1

/-- A bounded `F`: every causal line meets its graph. -/
theorem exists_mem_graph_line_of_bounded {c B : ℝ} (hlip : LipschitzWith 1 F)
    (hB : ∀ y, |F y - c| ≤ B) (z v : Minkowski d) (hv : IsFutureCausal v) (hv0 : v ≠ 0) :
    ∃ s : ℝ, z + s • v ∈ graph F := by
  have hv1 : 0 < v.1 := lt_of_le_of_ne hv.1 fun h => hv0 (eq_zero_of_fst_eq_zero h.symm hv.2)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set K : ℝ := (|z.1| + |c| + B + 1) / v.1 with hK
  have hK0 : 0 ≤ K := div_nonneg (by positivity) hv1.le
  have hKv : K * v.1 = |z.1| + |c| + B + 1 := by rw [hK]; field_simp
  have hcont : ContinuousOn (fun s : ℝ => timeSub F (z + s • v)) (Icc (-K) K) :=
    ((continuous_timeSub hlip).comp (continuous_const.add
      (continuous_id.smul continuous_const))).continuousOn
  have hlo : timeSub F (z + (-K) • v) ≤ 0 := by
    have := hB (z + (-K) • v).2
    simp only [timeSub, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this ⊢
    have h1 := abs_le.1 this
    linarith [le_abs_self z.1, neg_abs_le c, le_abs_self c]
  have hhi : 0 ≤ timeSub F (z + K • v) := by
    have := hB (z + K • v).2
    simp only [timeSub, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this ⊢
    have h1 := abs_le.1 this
    linarith [neg_abs_le z.1, neg_abs_le c, le_abs_self c]
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (by linarith) hcont ⟨hlo, hhi⟩
  exact ⟨s, mem_graph_iff_timeSub.2 hs⟩

variable (F y₀ r) in
/-- **The local domain** `W = int (graphLocalSet F y₀ r)`, as an open set. -/
def graphLocalDomain : Opens (Minkowski d) := ⟨interior (graphLocalSet F y₀ r), isOpen_interior⟩

theorem mem_graphLocalDomain {q : Minkowski d} :
    q ∈ graphLocalDomain F y₀ r ↔ q ∈ interior (graphLocalSet F y₀ r) :=
  Iff.rfl

theorem graphLocalDomain_subset {q : Minkowski d} (hq : q ∈ graphLocalDomain F y₀ r) :
    ‖q.2 - y₀‖ < r ∧ |timeSub F q| < r :=
  let h := interior_subset hq; ⟨h.1, h.2.1⟩

/-- **The graph is a Cauchy surface of the local domain**, through LipschitzGraph's saturated
criterion `isCauchySurfaceOn_graph_of_saturated`. -/
theorem isCauchySurfaceOn_graphLocalDomain (hF : IsStrictContraction F) {c B : ℝ}
    (hB : ∀ y, |F y - c| ≤ B) :
    (minkowski d).IsCauchySurfaceOn (graphLocalDomain F y₀ r) (graph F) :=
  isCauchySurfaceOn_graph_of_saturated hF
    (fun z _ v hv hv0 => exists_mem_graph_line_of_bounded hF.lipschitzWith hB z v hv hv0)
    (fun _ hz _ hqz hq => interior_graphLocalSet_past hF hz hqz hq)
    (fun _ hz _ hzq hq => interior_graphLocalSet_future hF hz hzq hq)

/-- **The local domain is causally convex for the cone.** -/
theorem graphLocalDomain_convex (hF : IsStrictContraction F) {a b c : Minkowski d}
    (ha : a ∈ graphLocalDomain F y₀ r) (hc : c ∈ graphLocalDomain F y₀ r)
    (hab : (minkowski d).le ⊤ a b)
    (hbc : (minkowski d).le ⊤ b c) : b ∈ graphLocalDomain F y₀ r := by
  rcases le_total 0 (timeSub F b) with h | h
  · exact interior_graphLocalSet_past hF hc hbc h
  · exact interior_graphLocalSet_future hF ha hab h

/-- The vertical segment below a point of the local domain above the graph lies in it, so the
point is in the future of the graph inside the local domain. -/
theorem Jplus_graphLocalDomain (hF : IsStrictContraction F) :
    (minkowski d).Jplus (graphLocalDomain F y₀ r) (graph F ∩ graphLocalDomain F y₀ r) =
      {q | q ∈ graphLocalDomain F y₀ r ∧ 0 ≤ timeSub F q} := by
  have hlip := hF.lipschitzWith
  ext q
  constructor
  · rintro ⟨x, ⟨hxg, -⟩, hxq⟩
    refine ⟨(minkowski d).le_mem_right hxq, ?_⟩
    have := timeSub_le_of_le hlip ((minkowski d).le_mono le_top hxq)
    rw [mem_graph_iff_timeSub.1 hxg] at this
    exact this
  · rintro ⟨hqW, hq⟩
    have hseg : ∀ τ ∈ Icc (F q.2) q.1, ((τ, q.2) : Minkowski d) ∈ graphLocalDomain F y₀ r := by
      intro τ hτ
      refine interior_graphLocalSet_past hF hqW (minkowski_le_top_iff.2 ?_) ?_
      · simp only [sub_self, norm_zero]; linarith [hτ.2]
      · simp only [timeSub]; linarith [hτ.1]
    have hxW := hseg (F q.2) ⟨le_rfl, by simp only [timeSub] at hq; linarith⟩
    refine ⟨(F q.2, q.2), ⟨mk_mem_graph q.2, hxW⟩, ?_⟩
    refine staticCausality.le_iff.2 ⟨by simp only [timeSub] at hq; linarith, fun _ => q.2, rfl,
      rfl, ⟨fun _ _ _ _ => by simp, fun τ hτ => hseg τ hτ⟩⟩

theorem Jminus_graphLocalDomain (hF : IsStrictContraction F) :
    (minkowski d).Jminus (graphLocalDomain F y₀ r) (graph F ∩ graphLocalDomain F y₀ r) =
      {q | q ∈ graphLocalDomain F y₀ r ∧ timeSub F q ≤ 0} := by
  have hlip := hF.lipschitzWith
  ext q
  constructor
  · rintro ⟨x, ⟨hxg, -⟩, hqx⟩
    refine ⟨(minkowski d).le_mem_left hqx, ?_⟩
    have := timeSub_le_of_le hlip ((minkowski d).le_mono le_top hqx)
    rw [mem_graph_iff_timeSub.1 hxg] at this
    exact this
  · rintro ⟨hqW, hq⟩
    have hseg : ∀ τ ∈ Icc q.1 (F q.2), ((τ, q.2) : Minkowski d) ∈ graphLocalDomain F y₀ r := by
      intro τ hτ
      refine interior_graphLocalSet_future hF hqW (minkowski_le_top_iff.2 ?_) ?_
      · simp only [sub_self, norm_zero]; linarith [hτ.1]
      · simp only [timeSub]; linarith [hτ.2]
    have hxW := hseg (F q.2) ⟨by simp only [timeSub] at hq; linarith, le_rfl⟩
    refine ⟨(F q.2, q.2), ⟨mk_mem_graph q.2, hxW⟩, ?_⟩
    refine staticCausality.le_iff.2 ⟨by simp only [timeSub] at hq; linarith, fun _ => q.2, rfl,
      rfl, ⟨fun _ _ _ _ => by simp, fun τ hτ => hseg τ hτ⟩⟩

end LocalDomain

/-! ## §3 Charts of a flat spacetime -/

section Chart

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [HasGroupoid X (gxGroupoid (isom d) (Minkowski d))]

/-- Every flat spacetime is tarentin (the proof of `Flat.TheoremBInputs.flatCausality_tarentin`,
not imported here). -/
theorem tarentin_flatCausality : (flatCausality d X).Tarentin := by
  intro x U hU
  set e := chartAt (Minkowski d) x with he
  have hiso : ChartIso (flatCausality d X) (minkowski d) e := flatCausality_chartIso_chartAt x
  have hxs : x ∈ e.source := mem_chart_source _ x
  let W : Opens X := ⟨interior U ∩ e.source, isOpen_interior.inter e.open_source⟩
  have hxW : x ∈ W := ⟨mem_interior_iff_mem_nhds.2 hU, hxs⟩
  have hWe : W ≤ chartSource e := fun z hz => hz.2
  have hyW : e x ∈ chartImage e W := mem_chartImage_of_mem hxs hxW
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (chartImage e W).isOpen (e x) hyW
  set y := e x with hy
  set ε := ρ / 4 with hε
  have hε0 : 0 < ε := by positivity
  have key : ∀ w : Minkowski d, dist w y < 3 * ε → w ∈ chartImage e W := fun w hw =>
    hball (by rw [mem_ball]; linarith)
  set p' : Minkowski d := (y.1 - ε, y.2) with hp'
  set q' : Minkowski d := (y.1 + ε, y.2) with hq'
  have hp'y : dist p' y = ε := by
    rw [hp', Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
    exact max_eq_left hε0.le
  have hq'y : dist q' y = ε := by
    rw [hq', Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [add_sub_cancel_left, abs_of_pos hε0]
    exact max_eq_left hε0.le
  obtain ⟨p, -, hpW, hpe, -⟩ := exists_of_mem_chartImage (key p' (by linarith))
  obtain ⟨q, -, hqW, hqe, -⟩ := exists_of_mem_chartImage (key q' (by linarith))
  refine ⟨p, interior_subset hpW.1, q, interior_subset hqW.1, ?_⟩
  have hO : IsOpen ((W : Set X) ∩ (e.source ∩ e ⁻¹' ball y (ε / 2))) :=
    W.isOpen.inter (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball)
  refine interior_maximal (fun z hz => ?_) hO ⟨hxW, hxs, mem_ball_self (by linarith)⟩
  obtain ⟨hzW, -, hzb⟩ := hz
  have hzy : dist (e z) y < ε / 2 := hzb
  rw [mem_preimage, mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hzb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hzb
  rw [Causality.mem_diamond]
  constructor
  · refine (flatCausality d X).le_mono le_top ((hiso W hWe p hpW z hzW).1.2 ?_)
    rw [hpe]
    refine staticCausality.le_iff.2 (staticLe_of_ball (ρ := 2 * ε) (fun w hw => key w
      ((dist_triangle w p' y).trans_lt (by linarith))) ?_ ?_ ?_)
    · show y.1 - ε ≤ (e z).1
      linarith
    · show dist y.2 (e z).2 ≤ (e z).1 - (y.1 - ε)
      rw [dist_comm]; linarith
    · show (e z).1 - (y.1 - ε) < 2 * ε
      linarith
  · refine (flatCausality d X).le_mono le_top ((hiso W hWe z hzW q hqW).1.2 ?_)
    rw [hqe]
    refine staticCausality.le_iff.2 (staticLe_of_ball (ρ := 2 * ε) (fun w hw => key w
      ((dist_triangle w (e z) y).trans_lt (by linarith))) ?_ ?_ ?_)
    · show (e z).1 ≤ y.1 + ε
      linarith
    · show dist (e z).2 y.2 ≤ y.1 + ε - (e z).1
      linarith
    · show y.1 + ε - (e z).1 < 2 * ε
      linarith

/-- **A chart is an abstract `𝕄≥0`-morphism on its source** (`IsEMorphismOn`), from a chart
isomorphism (`flatCausality_chartIso_chartAt`). -/
theorem isEMorphismOn_chartSource {e : OpenPartialHomeomorph X (Minkowski d)}
    (hiso : ChartIso (flatCausality d X) (minkowski d) e) :
    IsEMorphismOn (flatCausality d X) (minkowski d) (chartSource e) e := by
  have himg : ∀ V : Opens X, V ≤ chartSource e → ((chartImage e V : Opens _) : Set _) = e '' V :=
    fun V hV => coe_chartImage_of_le hV
  have hsub : ∀ (V : Opens X) (U : Opens (Minkowski d)), V ≤ chartSource e → MapsTo e V U →
      chartImage e V ≤ U := fun V U hV hmaps p hp => by
    rw [← SetLike.mem_coe, himg V hV] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact hmaps hz
  exact
  { continuousOn := e.continuousOn
    isOpen_image := fun V hV => by rw [← himg V hV]; exact (chartImage e V).isOpen
    map_le := fun V U hV hmaps y z hyz =>
      (minkowski d).le_mono (hsub V U hV hmaps)
        (((hiso V hV y ((flatCausality d X).le_mem_left hyz) z
          ((flatCausality d X).le_mem_right hyz)).1).1 hyz)
    map_lt := fun V U hV hmaps y z hyz =>
      (minkowski d).lt_mono (hsub V U hV hmaps)
        (((hiso V hV y ((flatCausality d X).lt_mem_left hyz) z
          ((flatCausality d X).lt_mem_right hyz)).2).1 hyz)
    locally := fun z hz => ⟨chartSource e, le_rfl, hz, e.injOn, fun V' hV' U hU y hy w hw => by
      have hU' : chartImage e V' = U := SetLike.coe_injective (by rw [himg V' hV', hU])
      rw [← hU']; exact hiso V' hV' y hy w hw⟩ }

/-- `J⁺` through a chart. -/
theorem mem_Jplus_chart_iff {e : OpenPartialHomeomorph X (Minkowski d)}
    (hiso : ChartIso (flatCausality d X) (minkowski d) e) {U : Opens X} (hU : U ≤ chartSource e)
    {A : Set X} (hA : A ⊆ U) {n : X} :
    n ∈ (flatCausality d X).Jplus U A ↔
      n ∈ U ∧ e n ∈ (minkowski d).Jplus (chartImage e U) (e '' A) := by
  constructor
  · rintro ⟨a, ha, hle⟩
    have hn := (flatCausality d X).le_mem_right hle
    exact ⟨hn, _, ⟨a, ha, rfl⟩, ((hiso U hU a (hA ha) n hn).1).1 hle⟩
  · rintro ⟨hn, _, ⟨a, ha, rfl⟩, hle⟩
    exact ⟨a, ha, ((hiso U hU a (hA ha) n hn).1).2 hle⟩

/-- `J⁻` through a chart. -/
theorem mem_Jminus_chart_iff {e : OpenPartialHomeomorph X (Minkowski d)}
    (hiso : ChartIso (flatCausality d X) (minkowski d) e) {U : Opens X} (hU : U ≤ chartSource e)
    {A : Set X} (hA : A ⊆ U) {n : X} :
    n ∈ (flatCausality d X).Jminus U A ↔
      n ∈ U ∧ e n ∈ (minkowski d).Jminus (chartImage e U) (e '' A) := by
  constructor
  · rintro ⟨a, ha, hle⟩
    have hn := (flatCausality d X).le_mem_left hle
    exact ⟨hn, _, ⟨a, ha, rfl⟩, ((hiso U hU n hn a (hA ha)).1).1 hle⟩
  · rintro ⟨hn, _, ⟨a, ha, rfl⟩, hle⟩
    exact ⟨a, ha, ((hiso U hU n hn a (hA ha)).1).2 hle⟩

end Chart

/-- A Cauchy surface of `W` meets every inextensible curve of `W` inside `W`. -/
theorem isCauchySurfaceOn_inter_opens {X : Type*} [TopologicalSpace X] {C : Causality X}
    {W : Opens X} {A : Set X} (h : C.IsCauchySurfaceOn W A) : C.IsCauchySurfaceOn W (A ∩ W) := by
  intro I c hc
  obtain ⟨x, ⟨⟨t, ht, rfl⟩, hxA⟩, huniq⟩ := h I c hc
  exact ⟨c t, ⟨⟨t, ht, rfl⟩, hxA, hc.1.mem ht⟩, fun y hy => huniq y ⟨hy.1, hy.2.1⟩⟩

/-! ## §4 The theorem -/

/-- **The image of an acausal Cauchy surface under an isometric embedding of GH flat spacetimes
is locally Cauchy and two-sided** (Barbot, Rem 2.3 `clomax`, l.576–578, and §11, l.3537–3540: the
"spacelike hypersurface" input of lemma K). -/
theorem isLocallyCauchyTwoSided_image_of_isIsometricEmbedding {M : FlatSpacetime.{u} d}
    {N : FlatSpacetime.{v} d} (hM : GH M) (hN : GH N) {f : M → N}
    (hf : IsIsometricEmbedding d f) {S : Set M} (hS : (flatCausality d M).IsCauchySurface S)
    (hac : (flatCausality d M).IsAcausal S) :
    (flatCausality d N).IsLocallyCauchyTwoSided (f '' S) := by
  classical
  rintro _ ⟨s, hsS, rfl⟩
  haveI : Nonempty M := ⟨s⟩
  -- (1) the two sides of `S` in `M` are closed and cover `M` (a splitting along `S`)
  have hcausM : (flatCausality d M).IsCausal := hM.1
  obtain ⟨ψ, hψ⟩ := flat_exists_isCauchySplitting flat_hasChronalCausalFlow hcausM hS hac
  obtain ⟨hJp, hJm, hJpc, hJmc, hJint, -⟩ := Causality.sigma_separe hcausM hac hψ
  have hJcov : ∀ m : M, m ∈ (flatCausality d M).Jplus ⊤ S ∨
      m ∈ (flatCausality d M).Jminus ⊤ S := by
    intro m
    rw [hJp, hJm]
    rcases le_total 0 (ψ.symm m).2 with h | h
    · exact Or.inl ⟨ψ.symm m, ⟨trivial, h⟩, ψ.apply_symm_apply m⟩
    · exact Or.inr ⟨ψ.symm m, ⟨trivial, h⟩, ψ.apply_symm_apply m⟩
  -- (2) the inverse of `f` on its image
  obtain ⟨fi, hfic, hfil, hfir⟩ : ∃ g : N → M, ContinuousOn g (range f) ∧ (∀ m, g (f m) = m) ∧
      ∀ n ∈ range f, f (g n) = n := by
    refine ⟨(hf.isOpenEmbedding.toOpenPartialHomeomorph f).symm, ?_,
      fun m => hf.isOpenEmbedding.toOpenPartialHomeomorph_left_inv f,
      fun n hn => hf.isOpenEmbedding.toOpenPartialHomeomorph_right_inv f hn⟩
    have := (hf.isOpenEmbedding.toOpenPartialHomeomorph f).continuousOn_symm
    rwa [IsOpenEmbedding.toOpenPartialHomeomorph_target] at this
  -- (3) `N` is causally arc-connected and strongly causal; a chart at `f s`
  have hArcN := flatCausality_causallyArcConnected d N
  have hSC := Causality.GloballyHyperbolic.stronglyCausal (tarentin_flatCausality (X := N)) hN
  obtain ⟨e, hiso, hxe⟩ : ∃ e : OpenPartialHomeomorph N (Minkowski d),
      ChartIso (flatCausality d N) (minkowski d) e ∧ f s ∈ e.source :=
    ⟨_, flatCausality_chartIso_chartAt (f s), mem_chart_source _ _⟩
  have hEm := isEMorphismOn_chartSource hiso
  let O : Opens N := chartSource e ⊓ ⟨range f, hf.isOpenEmbedding.isOpen_range⟩
  have hOs : O ≤ chartSource e := inf_le_left
  have hxO : f s ∈ O := ⟨hxe, mem_range_self s⟩
  obtain ⟨V, hVn, hVO, hVcc⟩ := hSC (f s) O (O.isOpen.mem_nhds hxO)
  obtain ⟨p₀, hp₀⟩ : ∃ p, e (f s) = p := ⟨_, rfl⟩
  obtain ⟨β, hβ, hβsub⟩ : ∃ β > 0, ball p₀ β ⊆ e '' (e.source ∩ interior V) :=
    Metric.isOpen_iff.1 (e.isOpen_image_source_inter isOpen_interior) p₀
      ⟨f s, ⟨hxe, mem_interior_iff_mem_nhds.2 hVn⟩, hp₀⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Minkowski d → M, ∀ w, Ψ w = fi (e.symm w) := ⟨_, fun _ => rfl⟩
  have hball : ∀ w ∈ ball p₀ β, e.symm w ∈ e.source ∧ e.symm w ∈ V ∧ e (e.symm w) = w ∧
      e.symm w ∈ range f ∧ f (Ψ w) = e.symm w := by
    intro w hw
    obtain ⟨n, ⟨hns, hnV⟩, rfl⟩ := hβsub hw
    have h1 : e.symm (e n) = n := e.left_inv hns
    have hnV' : n ∈ V := interior_subset hnV
    have hnr : n ∈ range f := (hVO hnV').2
    refine ⟨by rw [h1]; exact hns, by rw [h1]; exact hnV', by rw [h1], by rw [h1]; exact hnr, ?_⟩
    rw [hΨ, h1]; exact hfir n hnr
  have hball_target : ball p₀ β ⊆ e.target := fun w hw => by
    obtain ⟨n, ⟨hns, -⟩, rfl⟩ := hβsub hw; exact e.map_source hns
  have hΨs : Ψ p₀ = s := by rw [hΨ, ← hp₀, e.left_inv hxe, hfil]
  -- (4) the cone of the chart ball is read in `M`
  let UB : Opens N := ⟨e.source ∩ e ⁻¹' ball p₀ β, e.isOpen_inter_preimage isOpen_ball⟩
  have hUBs : UB ≤ chartSource e := fun n hn => hn.1
  have hUBimg : chartImage e UB = ⟨ball p₀ β, isOpen_ball⟩ := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hUBs]
    ext w
    constructor
    · rintro ⟨n, hn, rfl⟩; exact hn.2
    · intro hw
      refine ⟨e.symm w, ⟨e.map_target (hball_target hw), ?_⟩, e.right_inv (hball_target hw)⟩
      show e (e.symm w) ∈ ball p₀ β
      rw [e.right_inv (hball_target hw)]; exact hw
  have hUBr : (UB : Set N) ⊆ range f := fun n hn => by
    have := hball (e n) hn.2
    rw [e.left_inv hn.1] at this
    exact this.2.2.2.1
  let VM : Opens M := ⟨f ⁻¹' UB, UB.isOpen.preimage hf.continuous⟩
  have hVM : (UB : Set N) = f '' VM := (image_preimage_eq_of_subset hUBr).symm
  have hkey : ∀ a ∈ ball p₀ β, ∀ b ∈ ball p₀ β, (minkowski d).le ⊤ a b →
      (flatCausality d M).le ⊤ (Ψ a) (Ψ b) := by
    intro a ha b hb hab
    obtain ⟨has, -, hae, -, hfa⟩ := hball a ha
    obtain ⟨hbs, -, hbe, -, hfb⟩ := hball b hb
    have hB : (minkowski d).le ⟨ball p₀ β, isOpen_ball⟩ a b :=
      (le_iff_of_convex (convex_ball p₀ β)).2 ⟨ha, hb, hab⟩
    have haU : e.symm a ∈ UB := ⟨has, by show e (e.symm a) ∈ ball p₀ β; rw [hae]; exact ha⟩
    have hbU : e.symm b ∈ UB := ⟨hbs, by show e (e.symm b) ∈ ball p₀ β; rw [hbe]; exact hb⟩
    have hN' : (flatCausality d N).le UB (e.symm a) (e.symm b) := by
      refine ((hiso UB hUBs _ haU _ hbU).1).2 ?_
      rw [hUBimg, hae, hbe]; exact hB
    have hM' : (flatCausality d M).le VM (Ψ a) (Ψ b) := by
      refine ((hf.rel_iff VM UB hVM (Ψ a) (Ψ b)).1).2 ?_
      rw [hfa, hfb]; exact hN'
    exact (flatCausality d M).le_mono le_top hM'
  have hcomp : ∀ a ∈ ball p₀ β, ∀ b ∈ ball p₀ β, Ψ a ∈ S → Ψ b ∈ S →
      (minkowski d).le ⊤ a b → a = b := by
    intro a ha b hb hSa hSb hab
    have h := hac _ hSa _ hSb (hkey a ha b hb hab)
    obtain ⟨-, -, hae, -, hfa⟩ := hball a ha
    obtain ⟨-, -, hbe, -, hfb⟩ := hball b hb
    rw [← hae, ← hbe, ← hfa, ← hfb, h]
  have hvert : ∀ t t' : ℝ, ∀ y, ((t, y) : Minkowski d) ∈ ball p₀ β →
      ((t', y) : Minkowski d) ∈ ball p₀ β → Ψ (t, y) ∈ S → Ψ (t', y) ∈ S → t = t' := by
    intro t t' y h1 h2 h3 h4
    rcases le_total t t' with h | h
    · exact congrArg Prod.fst (hcomp _ h1 _ h2 h3 h4 (minkowski_le_top_iff.2 (by
        show ‖y - y‖ ≤ t' - t
        rw [sub_self, norm_zero]; linarith)))
    · exact (congrArg Prod.fst (hcomp _ h2 _ h1 h4 h3 (minkowski_le_top_iff.2 (by
        show ‖y - y‖ ≤ t - t'
        rw [sub_self, norm_zero]; linarith)))).symm
  have hmemball : ∀ (q : Minkowski d) {ε : ℝ}, |q.1 - p₀.1| < ε → ‖q.2 - p₀.2‖ < ε →
      q ∈ ball p₀ ε := fun q ε ht hy => by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_lt ht hy
  -- (5) `S` is a graph over a small ball, in the chart
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = β / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hexists : ∀ y ∈ ball p₀.2 δ, ∃ t, |t - p₀.1| ≤ δ ∧ Ψ (t, y) ∈ S := by
    intro y hy
    have hy' : ‖y - p₀.2‖ < δ := by rwa [mem_ball, dist_eq_norm] at hy
    have hKB : closedBall p₀ (2 * δ) ⊆ ball p₀ β := closedBall_subset_ball (by linarith)
    have hΨc : ContinuousOn Ψ (closedBall p₀ (2 * δ)) := by
      have heq : Ψ = fi ∘ e.symm := funext hΨ
      rw [heq]
      refine hfic.comp (e.continuousOn_symm.mono (hKB.trans hball_target)) ?_
      intro w hw
      exact (hball w (hKB hw)).2.2.2.1
    have hQp := hΨc.preimage_isClosed_of_isClosed isClosed_closedBall hJpc
    have hQm := hΨc.preimage_isClosed_of_isClosed isClosed_closedBall hJmc
    have hsegc : IsPreconnected ((fun t : ℝ => ((t, y) : Minkowski d)) ''
        Icc (p₀.1 - δ) (p₀.1 + δ)) :=
      isPreconnected_Icc.image _ (by fun_prop)
    have hsegK : (fun t : ℝ => ((t, y) : Minkowski d)) '' Icc (p₀.1 - δ) (p₀.1 + δ) ⊆
        closedBall p₀ (2 * δ) := by
      rintro _ ⟨t, ht, rfl⟩
      rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, dist_eq_norm]
      refine max_le ?_ (by linarith)
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hp₀B : p₀ ∈ ball p₀ β := mem_ball_self hβ
    have htop : ((p₀.1 + δ, y) : Minkowski d) ∈
        (fun t : ℝ => ((t, y) : Minkowski d)) '' Icc (p₀.1 - δ) (p₀.1 + δ) :=
      ⟨p₀.1 + δ, ⟨by linarith, le_rfl⟩, rfl⟩
    have hbot : ((p₀.1 - δ, y) : Minkowski d) ∈
        (fun t : ℝ => ((t, y) : Minkowski d)) '' Icc (p₀.1 - δ) (p₀.1 + δ) :=
      ⟨p₀.1 - δ, ⟨le_rfl, by linarith⟩, rfl⟩
    obtain ⟨w, hwseg, hwp, hwm⟩ := isPreconnected_closed_iff.1 hsegc _ _ hQp hQm
      (fun w hw => (hJcov (Ψ w)).elim (fun h => Or.inl ⟨hsegK hw, h⟩)
        (fun h => Or.inr ⟨hsegK hw, h⟩))
      ⟨_, htop, hsegK htop, ⟨s, hsS, by
        rw [← hΨs]
        exact hkey _ hp₀B _ (hKB (hsegK htop)) (minkowski_le_top_iff.2 (by
          show ‖y - p₀.2‖ ≤ p₀.1 + δ - p₀.1
          linarith))⟩⟩
      ⟨_, hbot, hsegK hbot, ⟨s, hsS, by
        rw [← hΨs]
        exact hkey _ (hKB (hsegK hbot)) _ hp₀B (minkowski_le_top_iff.2 (by
          show ‖p₀.2 - y‖ ≤ p₀.1 - (p₀.1 - δ)
          rw [norm_sub_rev]; linarith))⟩⟩
    obtain ⟨t, ht, rfl⟩ := hwseg
    refine ⟨t, abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [← hJint]
    exact ⟨hwp.2, hwm.2⟩
  choose! G hG using hexists
  have hGball : ∀ y ∈ ball p₀.2 δ, ((G y, y) : Minkowski d) ∈ ball p₀ β := fun y hy =>
    hmemball (G y, y) (by linarith [(hG y hy).1]) (by
      show ‖y - p₀.2‖ < β
      rw [mem_ball, dist_eq_norm] at hy; linarith)
  have hy₀δ : p₀.2 ∈ ball p₀.2 δ := mem_ball_self hδ0
  have hGy₀ : G p₀.2 = p₀.1 :=
    hvert (G p₀.2) p₀.1 p₀.2 (hGball _ hy₀δ) (mem_ball_self hβ) (hG _ hy₀δ).2 (by
      show Ψ p₀ ∈ S
      rw [hΨs]; exact hsS)
  have hGstrict : ∀ y ∈ ball p₀.2 δ, ∀ y' ∈ ball p₀.2 δ, y ≠ y' → |G y - G y'| < ‖y - y'‖ := by
    intro y hy y' hy' hne
    by_contra hcon
    push Not at hcon
    rcases le_total (G y) (G y') with h | h
    · have habs : |G y - G y'| = G y' - G y := by
        rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.2 h)
      have := hcomp _ (hGball y hy) _ (hGball y' hy') (hG y hy).2 (hG y' hy').2
        (minkowski_le_top_iff.2 (by
          show ‖y' - y‖ ≤ G y' - G y
          rw [norm_sub_rev]; linarith))
      exact hne (congrArg Prod.snd this)
    · have habs : |G y - G y'| = G y - G y' := abs_of_nonneg (sub_nonneg.2 h)
      have := hcomp _ (hGball y' hy') _ (hGball y hy) (hG y' hy').2 (hG y hy).2
        (minkowski_le_top_iff.2 (by
          show ‖y - y'‖ ≤ G y - G y'
          linarith))
      exact hne (congrArg Prod.snd this).symm
  -- (6) the entire strict contraction `F`, and the local domain `W` of its graph
  obtain ⟨F, hF, hFb, hFG⟩ := exists_isStrictContraction_extension hδ0 hGstrict
  have hlip := hF.lipschitzWith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = δ / 4 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hFy₀ : F p₀.2 = p₀.1 := (hFG p₀.2 (by rw [sub_self, norm_zero]; positivity)).trans hGy₀
  have hWsub : ∀ q ∈ graphLocalDomain F p₀.2 r, |q.1 - p₀.1| < 2 * r ∧ ‖q.2 - p₀.2‖ < r := by
    intro q hq
    obtain ⟨h1, h2⟩ := graphLocalDomain_subset hq
    have h3 := abs_sub_le_norm_of_lipschitzWith_one hlip q.2 p₀.2
    rw [hFy₀] at h3
    simp only [timeSub] at h2
    refine ⟨?_, h1⟩
    calc |q.1 - p₀.1| = |(q.1 - F q.2) + (F q.2 - p₀.1)| := by ring_nf
      _ ≤ |q.1 - F q.2| + |F q.2 - p₀.1| := abs_add_le _ _
      _ < 2 * r := by linarith
  have hWB : ∀ q ∈ graphLocalDomain F p₀.2 r, q ∈ ball p₀ β := fun q hq =>
    hmemball q (by linarith [(hWsub q hq).1]) (by linarith [(hWsub q hq).2])
  have hgraphW : ∀ q ∈ graphLocalDomain F p₀.2 r, (Ψ q ∈ S ↔ timeSub F q = 0) := by
    intro q hq
    have h2 := (hWsub q hq).2
    have hq2 : q.2 ∈ ball p₀.2 δ := by rw [mem_ball, dist_eq_norm]; linarith
    have hFq : F q.2 = G q.2 := hFG q.2 (by linarith)
    rw [timeSub, sub_eq_zero, hFq]
    constructor
    · intro hΨq
      exact hvert q.1 (G q.2) q.2 (hWB q hq) (hGball q.2 hq2) hΨq (hG q.2 hq2).2
    · intro h
      have : q = (G q.2, q.2) := Prod.ext h rfl
      rw [this]; exact (hG q.2 hq2).2
  -- (7) the neighbourhood `U` of `f s` in `N`
  let U : Opens N := ⟨e.source ∩ e ⁻¹' (graphLocalDomain F p₀.2 r),
    e.isOpen_inter_preimage (graphLocalDomain F p₀.2 r).isOpen⟩
  have hUs : U ≤ chartSource e := fun n hn => hn.1
  have hUfacts : ∀ n ∈ U, e n ∈ graphLocalDomain F p₀.2 r ∧ n ∈ V ∧ n ∈ range f ∧
      Ψ (e n) = fi n := by
    intro n hn
    have hb := hball (e n) (hWB _ hn.2)
    rw [e.left_inv hn.1] at hb
    exact ⟨hn.2, hb.2.1, hb.2.2.2.1, by rw [hΨ, e.left_inv hn.1]⟩
  have hmemS : ∀ n ∈ U, (n ∈ f '' S ↔ timeSub F (e n) = 0) := by
    intro n hn
    obtain ⟨hnW, -, ⟨m, rfl⟩, hΨn⟩ := hUfacts n hn
    rw [← hgraphW _ hnW, hΨn, hfil]
    exact ⟨fun ⟨m', hm', he'⟩ => hf.injective he' ▸ hm', fun hm => ⟨m, hm, rfl⟩⟩
  have hWt : ((graphLocalDomain F p₀.2 r : Opens (Minkowski d)) : Set (Minkowski d)) ⊆ e.target :=
    fun q hq => hball_target (hWB q hq)
  have hUimg :
      ((graphLocalDomain F p₀.2 r : Opens (Minkowski d)) : Set (Minkowski d)) = e '' U := by
    ext q
    constructor
    · intro hq
      refine ⟨e.symm q, ⟨e.map_target (hWt hq), ?_⟩, e.right_inv (hWt hq)⟩
      show e (e.symm q) ∈ graphLocalDomain F p₀.2 r
      rw [e.right_inv (hWt hq)]; exact hq
    · rintro ⟨n, hn, rfl⟩; exact hn.2
  have hchartU : chartImage e U = graphLocalDomain F p₀.2 r :=
    SetLike.coe_injective (by rw [coe_chartImage_of_le hUs, ← hUimg])
  have hAimg : e '' (f '' S ∩ U) = graph F ∩ graphLocalDomain F p₀.2 r := by
    ext q
    constructor
    · rintro ⟨n, ⟨hnS, hnU⟩, rfl⟩
      exact ⟨mem_graph_iff_timeSub.2 ((hmemS n hnU).1 hnS), hnU.2⟩
    · rintro ⟨hqg, hqW⟩
      have hnU : e.symm q ∈ U := ⟨e.map_target (hWt hqW), by
        show e (e.symm q) ∈ graphLocalDomain F p₀.2 r
        rw [e.right_inv (hWt hqW)]; exact hqW⟩
      refine ⟨e.symm q, ⟨(hmemS _ hnU).2 ?_, hnU⟩, e.right_inv (hWt hqW)⟩
      rw [e.right_inv (hWt hqW)]; exact mem_graph_iff_timeSub.1 hqg
  have hxU : f s ∈ U := ⟨hxe, by
    show e (f s) ∈ graphLocalDomain F p₀.2 r
    rw [hp₀]
    exact mem_interior_graphLocalSet_of_graph hF (by rw [timeSub, hFy₀, sub_self])
      (by rw [sub_self, norm_zero]; exact hr0)⟩
  refine ⟨U, hxU, ⟨fun _ _ => trivial, fun p hp q hq r' hr' => ?_⟩, ?_, ?_, ?_⟩
  · -- causally convex
    obtain ⟨hpr, hrq⟩ := Causality.mem_diamond.1 hr'
    have hpV := (hUfacts p hp).2.1
    have hqV := (hUfacts q hq).2.1
    have hrV : r' ∈ V := hVcc.2 p hpV q hqV hr'
    have hrO : r' ∈ O := hVO hrV
    have h1 := Causality.le_of_causallyConvexIn hArcN hVcc hVO hpV hrV hpr
    have h2 := Causality.le_of_causallyConvexIn hArcN hVcc hVO hrV hqV hrq
    have h1' := (minkowski d).le_mono le_top (((hiso O hOs p (hVO hpV) r' hrO).1).1 h1)
    have h2' := (minkowski d).le_mono le_top (((hiso O hOs r' hrO q (hVO hqV)).1).1 h2)
    exact ⟨hOs hrO, graphLocalDomain_convex hF (hUfacts p hp).1 (hUfacts q hq).1 h1' h2'⟩
  · -- Cauchy
    have hC := isCauchySurfaceOn_inter_opens
      (isCauchySurfaceOn_graphLocalDomain (y₀ := p₀.2) (r := r) hF hFb)
    rw [← hAimg] at hC
    exact (hEm.isCauchySurfaceOn_image_iff e.injOn hUs hUimg inter_subset_right).2 hC
  · -- the future side
    have heq : (flatCausality d N).Jplus U (f '' S ∩ U) \ f '' S =
        e.source ∩ e ⁻¹' (((graphLocalDomain F p₀.2 r : Opens (Minkowski d)) : Set (Minkowski d)) ∩
          {q | 0 < timeSub F q}) := by
      ext n
      rw [Set.mem_sdiff, mem_Jplus_chart_iff hiso hUs inter_subset_right, hchartU, hAimg,
        Jplus_graphLocalDomain hF]
      constructor
      · rintro ⟨⟨hnU, hnW, hT⟩, hnS⟩
        exact ⟨hnU.1, hnW, lt_of_le_of_ne hT fun h => hnS ((hmemS n hnU).2 h.symm)⟩
      · rintro ⟨hns, hnW, hT⟩
        have hnU : n ∈ U := ⟨hns, hnW⟩
        exact ⟨⟨hnU, hnW, hT.le⟩, fun hnS => hT.ne' ((hmemS n hnU).1 hnS)⟩
    rw [heq]
    exact e.isOpen_inter_preimage ((graphLocalDomain F p₀.2 r).isOpen.inter
      (isOpen_lt continuous_const (continuous_timeSub hlip)))
  · -- the past side
    have heq : (flatCausality d N).Jminus U (f '' S ∩ U) \ f '' S =
        e.source ∩ e ⁻¹' (((graphLocalDomain F p₀.2 r : Opens (Minkowski d)) : Set (Minkowski d)) ∩
          {q | timeSub F q < 0}) := by
      ext n
      rw [Set.mem_sdiff, mem_Jminus_chart_iff hiso hUs inter_subset_right, hchartU, hAimg,
        Jminus_graphLocalDomain hF]
      constructor
      · rintro ⟨⟨hnU, hnW, hT⟩, hnS⟩
        exact ⟨hnU.1, hnW, lt_of_le_of_ne hT fun h => hnS ((hmemS n hnU).2 h)⟩
      · rintro ⟨hns, hnW, hT⟩
        have hnU : n ∈ U := ⟨hns, hnW⟩
        exact ⟨⟨hnU, hnW, hT.le⟩, fun hnS => hT.ne ((hmemS n hnU).1 hnS)⟩
    rw [heq]
    exact e.isOpen_inter_preimage ((graphLocalDomain F p₀.2 r).isOpen.inter
      (isOpen_lt (continuous_timeSub hlip) continuous_const))

end Causal.Flat.Cla
