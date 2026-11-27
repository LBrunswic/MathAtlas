import Causal.Ladder.Rules
import Causal.Galileo
import Causal.GluingModels.NonMinimal

/-!
# Galileo's spacetime in its curve form: absolutely minimal, causally open, tarentin and plain, and not locally strongly causal

No label of `ETT.tex` is certified or marked here. The file is the programme target
`T-abs-galileo-curve-form` (layer 1, `programme/roadmap.toml`), a ladder witness. The model is
Galileo's spacetime `ℝ × ℝⁿ` (`ℝⁿ` carried as `Fin n → ℝ`, with its product topology) with the
causality of its time-increasing curves, `Causal.galileoCurve n`:

* `p ≪_U q` iff a continuous curve of `U`, over `[0, 1]`, with strictly increasing time, runs from
  `p` to `q` (`galileoCurveLt`);
* `p ≤_U q` iff `p ≪_U q`, or `p = q ∈ U`.

It is **not** ETT's printed Galileo spacetime, item 4 of `ex:causalities_lines` (`ETT.tex:273`),
`Causal.galileo n` (`Causal/Galileo.lean`), which is not absolutely minimal for `n ≥ 1`
(`Causal.GluingModels.galileo_not_minimal`; OQ-108 is open):

> Galileo's spacetime $(\RR^{n+1},\leq,\ll)$, where for every open $\U$,
> $$(t,x_1,\cdots,x_n)\ll_{\U}  (t',x_1',\cdots,x_n')$$ if $t<t'$ and both points lie in the same
> connected component of $\U$; and $p\leq_\U q$ if $p\ll_\U q$ or $p=q$.

The two agree on convex open sets and differ for `n ≥ 1`. The ladder's note
(`programme/ladder.toml`, section `locally_strongly_causal`, the bullet "Galileo's spacetime in
its curve form (not in Lean)") argued the model's properties, among them:

> Not locally strongly causal: a set causally convex in a convex open W holding two points
> of distinct times holds the slab of W between them, which leaves every small neighbourhood
> (the argument of Causal.galileoOn_slab_subset, rem:galileo_spacetime_not_strongly, run in W).

* **`Causal.galileoCurve_separates`** (`1 ≤ n`) is the full form. It decides each of the
  ladder's 21 causality-sort nodes. It holds 16: causally arc-connected, absolutely minimal (and
  on every open set), push-up (and locally), causally open (two-sided), causally open in the
  future, both local forms, tarentin, chronal neighbours, a chronal neighbour at every point,
  causally plain, causal, a time function, future one-connected, curves extend. It lacks 5:
  locally strongly causal, strongly causal in either form, causally compact, globally hyperbolic.
  The time coordinate is a time function in both senses (`HasTimeFunction`, and
  `IsTimeFunction Prod.fst`, `defi:fonction_temps`).
* Proved directly: the causality, `galileoCurve_causallyArcConnected`, `galileoCurve_pushUp`,
  `galileoCurve_chronalNeighbours`, `galileoCurve_isCausal`, `galileoCurve_hasTimeFunction`,
  `galileoCurve_isTimeFunction_fst`, `galileoCurve_futureOneConnectedOn` (every convex open),
  `galileoCurve_not_causallyCompact`, `galileoCurve_not_stronglyCausalOn` (no non-empty open set
  is strongly causal as a spacetime), and `∀ W, AbsolutelyMinimalOn W` (through
  `CausallyArcConnectedOn.absolutelyMinimalOn`). The rest by `causal_ladder`.
* Against the printed causality: finer on every open set (`galileoCurve_lt_imp_galileo`), equal on
  convex ones (`galileoCurve_lt_iff_galileo_of_convex`, `galileoCurve_le_iff_galileo_of_convex`),
  different for `n ≥ 1` (`galileoCurve_ne_galileo`, `exists_galileo_lt_not_galileoCurve_lt`);
  and generated, by chains, by the printed relations of the convex open subsets of the members of
  any open cover (`galileoCurve_lt_iff_transGen_convex`).

## Hypothesis checklist

| target's assertion | here |
|---|---|
| `ℝ × ℝⁿ`, `n ≥ 1` (`n = 1` suffices) | ✓ `ℝ × (Fin n → ℝ)`, every `n ≥ 1`; the positive facts hold for every `n`, and `1 ≤ n` is used for the negative ones only |
| `x ≪_U y` iff a continuous curve of `U` with strictly increasing time runs from `x` to `y`; `x ≤_U y` iff `x = y ∈ U` or `x ≪_U y` | ✓ `galileoCurveLt`, `galileoCurve`; over any segment the same (`galileoCurveLt_of_continuousOn`); the graph form `galileoGraphLt` is equivalent (`galileoCurveLt_iff_graphLt`) |
| a causality (`I^±` open) | ✓ `galileoCurve n : Causality (ℝ × (Fin n → ℝ))` |
| causally arc-connected; absolutely minimal on every open set | ✓ conjuncts 1–3 (`AbsolutelyMinimal` and `∀ W, AbsolutelyMinimalOn W`) |
| push-up, causally open, tarentin, chronal neighbours, causally plain | ✓ conjuncts 4–13, with the local and one-sided forms and `HasChronalNeighbourEverywhere` |
| `¬ LocallyStronglyCausal` (the slab argument in a convex open `W`) | ✓ conjunct 19; stronger, `galileoCurve_not_stronglyCausalOn`; the slab lemma in a convex open, `galileoCurve_slab_subset_of_convex` |
| causal, the time coordinate a time function, future one-connected, curves extend, not causally compact | ✓ conjuncts 14–18 and 22; also `¬ StronglyCausal`, `¬ StronglyCausalOpen`, `¬ GloballyHyperbolic` |
| the curve form agrees with the printed causality on convex opens | ✓ `galileoCurve_lt_iff_galileo_of_convex`, `galileoCurve_le_iff_galileo_of_convex` |

## SCOPE (disclosed)

* **Layer 1.** The imports are `Causal.Ladder.Rules`, `Causal.Galileo` and
  `Causal.GluingModels.NonMinimal`. `tools/ladder.py`'s `model_path` is `None` for each (checked
  one at a time, in memory; kb/0247). No statement mentions a metric: `segment` and `Convex` are
  affine notions. Balls of the sup norm are used inside proofs only.
* **No reading is decided.** OQ-108 asks whether item 4 is meant with the causality its small open
  sets generate (reading (a)). This file proves facts about both causalities and marks no label.
  `galileoCurve_lt_iff_transGen_convex` says the curve form is generated, by chains, from the
  printed relations of the convex open sets. The paper's own generation
  (`def:precausality_generated_notation_lemma`, `ETT.tex:393`, in which absolute minimality is
  phrased; formalized as `Precausality.generated`: over a cover, relations in `V ⊓ O`) is a
  different operation, since `V ⊓ O` need not be convex. Argued, not formalized: over a cover by
  small sets that precausality depends on the cover and is not absolutely minimal.
* `rem:galileo_spacetime_not_strongly` (`ETT.tex:670`), about item 4 as printed, is not marked.
  Its argument holds verbatim for the curve form (`galileoCurve_diamond_top`,
  `galileoCurve_slab_subset_of_convex`; `¬ StronglyCausal`, `n ≥ 1`).
* For `n = 0` the negative conjuncts are not claimed (the space is a line).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function Filter Relation

variable {n : ℕ}

/-! ### The graph form of a time-increasing curve -/

/-- The graph form of the chronological relation: `p.1 < q.1`, and `q` is reached from `p` along
the graph `t ↦ (t, f t)`, over `[p.1, q.1]`, of a continuous `f : ℝ → ℝⁿ`, inside `U`. It is a
time-increasing curve reparametrised by its time (`galileoCurveLt_iff_graphLt`). -/
def galileoGraphLt (n : ℕ) (U : Opens (ℝ × (Fin n → ℝ))) (p q : ℝ × (Fin n → ℝ)) : Prop :=
  p.1 < q.1 ∧ ∃ f : ℝ → (Fin n → ℝ), Continuous f ∧ f p.1 = p.2 ∧ f q.1 = q.2 ∧
    ∀ t ∈ Icc p.1 q.1, (t, f t) ∈ U

theorem galileoGraphLt.mem_left {U : Opens (ℝ × (Fin n → ℝ))} {p q : ℝ × (Fin n → ℝ)}
    (h : galileoGraphLt n U p q) : p ∈ U := by
  obtain ⟨hpq, f, -, hp, -, hU⟩ := h
  simpa [hp] using hU p.1 ⟨le_rfl, hpq.le⟩

theorem galileoGraphLt.mem_right {U : Opens (ℝ × (Fin n → ℝ))} {p q : ℝ × (Fin n → ℝ)}
    (h : galileoGraphLt n U p q) : q ∈ U := by
  obtain ⟨hpq, f, -, -, hq, hU⟩ := h
  simpa [hq] using hU q.1 ⟨hpq.le, le_rfl⟩

/-- Concatenation of graphs: `if t ≤ q.1 then f t else g t`. -/
theorem galileoGraphLt.trans {U : Opens (ℝ × (Fin n → ℝ))} {p q r : ℝ × (Fin n → ℝ)}
    (h₁ : galileoGraphLt n U p q) (h₂ : galileoGraphLt n U q r) : galileoGraphLt n U p r := by
  obtain ⟨hpq, f, hf, hfp, hfq, hfU⟩ := h₁
  obtain ⟨hqr, g, hg, hgq, hgr, hgU⟩ := h₂
  refine ⟨hpq.trans hqr, fun t => if t ≤ q.1 then f t else g t,
    Continuous.if_le hf hg continuous_id continuous_const fun t ht => ?_, ?_, ?_, fun t ht => ?_⟩
  · rw [show t = q.1 from ht, hfq, hgq]
  · simp [hpq.le, hfp]
  · simp [not_le.2 hqr, hgr]
  · by_cases htq : t ≤ q.1
    · simp only [htq, if_true]
      exact hfU t ⟨ht.1, htq⟩
    · simp only [htq, if_false]
      exact hgU t ⟨(not_le.1 htq).le, ht.2⟩

theorem galileoGraphLt.mono {U V : Opens (ℝ × (Fin n → ℝ))} (hVU : V ≤ U)
    {p q : ℝ × (Fin n → ℝ)} (h : galileoGraphLt n V p q) : galileoGraphLt n U p q := by
  obtain ⟨hpq, f, hf, hfp, hfq, hfU⟩ := h
  exact ⟨hpq, f, hf, hfp, hfq, fun t ht => hVU (hfU t ht)⟩

theorem isRelFamily_galileoGraphLt : IsRelFamily (galileoGraphLt n) :=
  ⟨galileoGraphLt.mem_left, galileoGraphLt.mem_right, galileoGraphLt.trans,
    fun h _ _ h' => h'.mono h⟩

/-- The straight segment: two points of distinct times whose segment lies in `U`. -/
theorem galileoGraphLt_of_segment_subset {U : Opens (ℝ × (Fin n → ℝ))} {a b : ℝ × (Fin n → ℝ)}
    (hab : a.1 < b.1) (hs : segment ℝ a b ⊆ U) : galileoGraphLt n U a b := by
  have hd : 0 < b.1 - a.1 := sub_pos.2 hab
  refine ⟨hab, fun t => a.2 + ((t - a.1) / (b.1 - a.1)) • (b.2 - a.2), by fun_prop, by simp,
    ?_, fun t ht => hs ?_⟩
  · simp [div_self hd.ne']
  · rw [segment_eq_image']
    refine ⟨(t - a.1) / (b.1 - a.1),
      ⟨div_nonneg (by linarith [ht.1]) hd.le, (div_le_one hd).2 (by linarith [ht.2])⟩, ?_⟩
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp
      ring
    · simp

/-- `I⁺_U(x)` is open in the graph form: for `y` in it, a point `w` of the graph just before `y`,
and the straight segments from `w` to the points of a small ball about `y` above the time of `w`.
-/
theorem isOpen_galileoGraphLt_right (U : Opens (ℝ × (Fin n → ℝ))) (x : ℝ × (Fin n → ℝ)) :
    IsOpen {y | galileoGraphLt n U x y} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyU : y ∈ U := galileoGraphLt.mem_right hy
  obtain ⟨hxy, f, hf, hfx, hfy, hfU⟩ := hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 U.isOpen y hyU
  have hT : Tendsto (fun t => ((t, f t) : ℝ × (Fin n → ℝ))) (𝓝 y.1) (𝓝 y) := by
    have := (continuous_id.prodMk hf).tendsto y.1
    simpa [hfy] using this
  have h1 : ∀ᶠ t in 𝓝 y.1, x.1 < t := eventually_gt_nhds hxy
  have h2 : ∀ᶠ t in 𝓝 y.1, ((t, f t) : ℝ × (Fin n → ℝ)) ∈ Metric.ball y (ε / 2) :=
    hT.eventually (Metric.ball_mem_nhds y (half_pos hε))
  obtain ⟨t₀, ⟨hxt, hw⟩, ht₀y⟩ :=
    (((h1.and h2).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Iio y.1 ∈ 𝓝[<] y.1)).exists
  refine Filter.mem_of_superset (inter_mem (Metric.ball_mem_nhds y (half_pos hε))
    ((isOpen_lt continuous_const continuous_fst).mem_nhds (show t₀ < y.1 from ht₀y)))
    fun z hz => ?_
  have hxw : galileoGraphLt n U x (t₀, f t₀) :=
    ⟨hxt, f, hf, hfx, rfl, fun t ht => hfU t ⟨ht.1, ht.2.trans (le_of_lt ht₀y)⟩⟩
  have hwz : galileoGraphLt n U (t₀, f t₀) z := by
    refine galileoGraphLt_of_segment_subset hz.2 ?_
    exact ((convex_ball y (ε / 2)).segment_subset hw hz.1).trans
      ((Metric.ball_subset_ball (by linarith)).trans hball)
  exact hxw.trans hwz

/-- `I⁻_U(y)` is open in the graph form (the same argument at the start of the graph). -/
theorem isOpen_galileoGraphLt_left (U : Opens (ℝ × (Fin n → ℝ))) (y : ℝ × (Fin n → ℝ)) :
    IsOpen {x | galileoGraphLt n U x y} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxU : x ∈ U := galileoGraphLt.mem_left hx
  obtain ⟨hxy, f, hf, hfx, hfy, hfU⟩ := hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 U.isOpen x hxU
  have hT : Tendsto (fun t => ((t, f t) : ℝ × (Fin n → ℝ))) (𝓝 x.1) (𝓝 x) := by
    have := (continuous_id.prodMk hf).tendsto x.1
    simpa [hfx] using this
  have h1 : ∀ᶠ t in 𝓝 x.1, t < y.1 := eventually_lt_nhds hxy
  have h2 : ∀ᶠ t in 𝓝 x.1, ((t, f t) : ℝ × (Fin n → ℝ)) ∈ Metric.ball x (ε / 2) :=
    hT.eventually (Metric.ball_mem_nhds x (half_pos hε))
  obtain ⟨t₀, ⟨hty, hw⟩, hxt₀⟩ :=
    (((h1.and h2).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi x.1 ∈ 𝓝[>] x.1)).exists
  refine Filter.mem_of_superset (inter_mem (Metric.ball_mem_nhds x (half_pos hε))
    ((isOpen_lt continuous_fst continuous_const).mem_nhds (show x.1 < t₀ from hxt₀)))
    fun z hz => ?_
  have hwy : galileoGraphLt n U (t₀, f t₀) y :=
    ⟨hty, f, hf, rfl, hfy, fun t ht => hfU t ⟨(le_of_lt hxt₀).trans ht.1, ht.2⟩⟩
  have hzw : galileoGraphLt n U z (t₀, f t₀) := by
    refine galileoGraphLt_of_segment_subset hz.2 ?_
    exact ((convex_ball x (ε / 2)).segment_subset hz.1 hw).trans
      ((Metric.ball_subset_ball (by linarith)).trans hball)
  exact hzw.trans hwy

/-! ### The curve form -/

/-- **The chronological relation of the curve form**: a continuous curve of `U`, over `[0, 1]`,
with strictly increasing time, runs from `p` to `q`. -/
def galileoCurveLt (n : ℕ) (U : Opens (ℝ × (Fin n → ℝ))) (p q : ℝ × (Fin n → ℝ)) : Prop :=
  ∃ γ : ℝ → ℝ × (Fin n → ℝ), ContinuousOn γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧
    MapsTo γ (Icc 0 1) U ∧ StrictMonoOn (fun s => (γ s).1) (Icc 0 1)

/-- A curve over any segment `[s, s']`, `s < s'`, continuous, in `U`, with strictly increasing
time, gives the relation between its ends (affine reparametrisation). -/
theorem galileoCurveLt_of_continuousOn {U : Opens (ℝ × (Fin n → ℝ))} {c : ℝ → ℝ × (Fin n → ℝ)}
    {s s' : ℝ} (hss' : s < s') (hc : ContinuousOn c (Icc s s')) (hU : MapsTo c (Icc s s') U)
    (hm : StrictMonoOn (fun σ => (c σ).1) (Icc s s')) : galileoCurveLt n U (c s) (c s') := by
  have hA : MapsTo (fun σ : ℝ => s + σ * (s' - s)) (Icc 0 1) (Icc s s') := fun σ hσ =>
    ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩
  refine ⟨fun σ => c (s + σ * (s' - s)), hc.comp (by fun_prop) hA, by simp, by simp, ?_, ?_⟩
  · exact fun σ hσ => hU (hA hσ)
  · intro σ hσ σ' hσ' h
    exact hm (hA hσ) (hA hσ') (by nlinarith)

/-- **The curve form and the graph form agree.** From a curve to a graph: the curve is a curve of
the graph relations (locally, straight segments in small balls), whose ends are then related by
`CurveOn.rel_of_lt`. From a graph to a curve: `s ↦ (t s, f (t s))`, `t` affine. -/
theorem galileoCurveLt_iff_graphLt {U : Opens (ℝ × (Fin n → ℝ))} {p q : ℝ × (Fin n → ℝ)} :
    galileoCurveLt n U p q ↔ galileoGraphLt n U p q := by
  constructor
  · rintro ⟨γ, hγc, rfl, rfl, hγU, hγm⟩
    have hc : CurveOn (galileoGraphLt n) U γ 0 1 := by
      refine ⟨fun t ht => hγU ht, fun t ht N hN htN => ?_⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 N.isOpen (γ t) htN
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hγc t ht) ε hε
      refine ⟨t - δ, t + δ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
      have hd1 : dist s t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have hd2 : dist s' t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      let B : Opens (ℝ × (Fin n → ℝ)) := ⟨Metric.ball (γ t) ε, Metric.isOpen_ball⟩
      have hB : galileoGraphLt n B (γ s) (γ s') :=
        galileoGraphLt_of_segment_subset (hγm hs hs' h2)
          ((convex_ball (γ t) ε).segment_subset (hδc hs hd1) (hδc hs' hd2))
      exact hB.mono fun z hz => hball hz
    exact CurveOn.rel_of_lt isRelFamily_galileoGraphLt hc le_rfl zero_lt_one le_rfl
  · rintro ⟨hpq, f, hf, hfp, hfq, hfU⟩
    have hA : MapsTo (fun s : ℝ => p.1 + s * (q.1 - p.1)) (Icc 0 1) (Icc p.1 q.1) :=
      fun s hs => ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    refine ⟨fun s => (p.1 + s * (q.1 - p.1), f (p.1 + s * (q.1 - p.1))), by fun_prop,
      ?_, ?_, fun s hs => hfU _ (hA hs), fun s hs s' hs' h => ?_⟩
    · ext <;> simp [hfp]
    · ext <;> simp [hfq]
    · show p.1 + s * (q.1 - p.1) < p.1 + s' * (q.1 - p.1)
      nlinarith

/-- **Galileo's spacetime in its curve form**, on `ℝ × ℝⁿ`: `p ≪_U q` iff a continuous curve of
`U` with strictly increasing time runs from `p` to `q` (`galileoCurveLt`); `p ≤_U q` iff
`p ≪_U q` or `p = q ∈ U`. A causality: `≪_U` is transitive (concatenation) and open
(`isOpen_galileoGraphLt_right`, `_left`). Not the printed `Causal.galileo n`
(`galileoCurve_ne_galileo`). -/
def galileoCurve (n : ℕ) : Causality (ℝ × (Fin n → ℝ)) where
  le U p q := galileoCurveLt n U p q ∨ (p = q ∧ p ∈ U)
  lt := galileoCurveLt n
  le_mem_left h := h.elim (fun h => (galileoCurveLt_iff_graphLt.1 h).mem_left) fun h => h.2
  le_mem_right h := h.elim (fun h => (galileoCurveLt_iff_graphLt.1 h).mem_right)
    fun h => h.1 ▸ h.2
  lt_mem_left h := (galileoCurveLt_iff_graphLt.1 h).mem_left
  lt_mem_right h := (galileoCurveLt_iff_graphLt.1 h).mem_right
  le_refl hx := Or.inr ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with h₁ | ⟨rfl, -⟩
    · rcases h₂ with h₂ | ⟨rfl, -⟩
      · exact Or.inl (galileoCurveLt_iff_graphLt.2
          ((galileoCurveLt_iff_graphLt.1 h₁).trans (galileoCurveLt_iff_graphLt.1 h₂)))
      · exact Or.inl h₁
    · exact h₂
  lt_trans h₁ h₂ := galileoCurveLt_iff_graphLt.2
    ((galileoCurveLt_iff_graphLt.1 h₁).trans (galileoCurveLt_iff_graphLt.1 h₂))
  le_mono hVU _ _ h := h.elim
    (fun ⟨γ, hγc, h0, h1, hγU, hγm⟩ => Or.inl ⟨γ, hγc, h0, h1, fun _ hs => hVU (hγU hs), hγm⟩)
    fun h => Or.inr ⟨h.1, hVU h.2⟩
  lt_mono hVU _ _ := fun ⟨γ, hγc, h0, h1, hγU, hγm⟩ =>
    ⟨γ, hγc, h0, h1, fun _ hs => hVU (hγU hs), hγm⟩
  le_of_lt h := Or.inl h
  isOpen_lt_right U x := by
    have : {y | galileoCurveLt n U x y} = {y | galileoGraphLt n U x y} :=
      Set.ext fun _ => galileoCurveLt_iff_graphLt
    rw [this]
    exact isOpen_galileoGraphLt_right U x
  isOpen_lt_left U y := by
    have : {x | galileoCurveLt n U x y} = {x | galileoGraphLt n U x y} :=
      Set.ext fun _ => galileoCurveLt_iff_graphLt
    rw [this]
    exact isOpen_galileoGraphLt_left U y

variable {U W : Opens (ℝ × (Fin n → ℝ))} {p q r : ℝ × (Fin n → ℝ)}

@[simp] theorem galileoCurve_lt : (galileoCurve n).lt U p q ↔ galileoCurveLt n U p q := Iff.rfl

@[simp] theorem galileoCurve_le :
    (galileoCurve n).le U p q ↔ galileoCurveLt n U p q ∨ (p = q ∧ p ∈ U) := Iff.rfl

theorem galileoCurve_lt_iff_graphLt : (galileoCurve n).lt U p q ↔ galileoGraphLt n U p q :=
  galileoCurveLt_iff_graphLt

/-- Time increases strictly along `≪`. -/
theorem galileoCurve_lt_fst (h : (galileoCurve n).lt U p q) : p.1 < q.1 :=
  (galileoCurve_lt_iff_graphLt.1 h).1

/-- Time does not decrease along `≤`. -/
theorem galileoCurve_le_fst (h : (galileoCurve n).le U p q) : p.1 ≤ q.1 := by
  rcases h with h | ⟨rfl, -⟩
  · exact (galileoCurve_lt_fst h).le
  · exact le_rfl

/-- The straight segment between two points of distinct times, when it lies in `U`. -/
theorem galileoCurve_lt_of_segment_subset (hpq : p.1 < q.1)
    (hs : segment ℝ p q ⊆ U) : (galileoCurve n).lt U p q :=
  galileoCurve_lt_iff_graphLt.2 (galileoGraphLt_of_segment_subset hpq hs)

/-- In `M`, `≪` is the time order. -/
theorem galileoCurve_lt_top : (galileoCurve n).lt ⊤ p q ↔ p.1 < q.1 :=
  ⟨galileoCurve_lt_fst, fun h => galileoCurve_lt_of_segment_subset h fun _ _ => trivial⟩

/-! ### Curves -/

/-- **The chronal curves of the curve form**, in every open `W`: the continuous maps of `[a, b]`
into `W` with strictly increasing time. -/
theorem galileoCurve_chronalCurveOn_iff {c : ℝ → ℝ × (Fin n → ℝ)} {a b : ℝ} :
    (galileoCurve n).ChronalCurveOn W c a b ↔
      ContinuousOn c (Icc a b) ∧ MapsTo c (Icc a b) W ∧
        StrictMonoOn (fun s => (c s).1) (Icc a b) := by
  constructor
  · intro hc
    exact ⟨CurveOn.continuousOn (galileoCurve n).isRelFamily_lt hc, fun s hs => hc.mem s hs,
      fun s hs s' hs' h => galileoCurve_lt_fst (hc.lt_of_lt hs.1 h hs'.2)⟩
  · rintro ⟨hcont, hmaps, hm⟩
    refine ⟨fun t ht => hmaps ht, fun t ht N hN htN => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 N.isOpen (c t) htN
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hcont t ht) ε hε
    refine ⟨t - δ, t + δ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hsub : Icc s s' ⊆ Icc a b := Icc_subset_Icc hs.1 hs'.2
    refine galileoCurveLt_of_continuousOn h2 (hcont.mono hsub) (fun σ hσ => hball ?_)
      (hm.mono hsub)
    have hd : dist σ t < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hσ.1, hσ.2]
    exact hδc (hsub hσ) hd

/-- **The curve form is causally arc-connected**: a curve with strictly increasing time is a
chronal curve of every open set containing it. -/
theorem galileoCurve_causallyArcConnected : (galileoCurve n).CausallyArcConnected := by
  intro U _ p q
  have hlt : (galileoCurve n).lt U p q ↔
      ∃ c : ℝ → ℝ × (Fin n → ℝ), (galileoCurve n).ChronalCurveOn U c 0 1 ∧ c 0 = p ∧ c 1 = q := by
    constructor
    · rintro ⟨γ, hγc, hγ0, hγ1, hγU, hγm⟩
      exact ⟨γ, galileoCurve_chronalCurveOn_iff.2 ⟨hγc, hγU, hγm⟩, hγ0, hγ1⟩
    · rintro ⟨c, hc, rfl, rfl⟩
      exact hc.lt_of_lt le_rfl zero_lt_one le_rfl
  refine ⟨⟨?_, ?_⟩, hlt⟩
  · rintro (h | ⟨rfl, hp⟩)
    · obtain ⟨c, hc, h0, h1⟩ := hlt.1 h
      exact ⟨c, hc.causalCurveOn, h0, h1⟩
    · exact ⟨fun _ => p, Causality.causalCurveOn_const hp, rfl, rfl⟩
  · rintro ⟨c, hc, rfl, rfl⟩
    exact hc.le_of_le le_rfl zero_le_one le_rfl

/-! ### The ladder facts -/

theorem galileoCurve_lt_of_le_of_lt (h₁ : (galileoCurve n).le U p q)
    (h₂ : (galileoCurve n).lt U q r) : (galileoCurve n).lt U p r := by
  rcases h₁ with h₁ | ⟨rfl, -⟩
  · exact (galileoCurve n).lt_trans h₁ h₂
  · exact h₂

theorem galileoCurve_lt_of_lt_of_le (h₁ : (galileoCurve n).lt U p q)
    (h₂ : (galileoCurve n).le U q r) : (galileoCurve n).lt U p r := by
  rcases h₂ with h₂ | ⟨rfl, -⟩
  · exact (galileoCurve n).lt_trans h₁ h₂
  · exact h₁

/-- **Push-up**: `≤` is `=` or `≪`. -/
theorem galileoCurve_pushUp : (galileoCurve n).PushUp := by
  intro U x
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro z ⟨y, hy, hyz⟩
    exact Precausality.mem_Iplus_singleton.2
      (galileoCurve_lt_of_lt_of_le (Precausality.mem_Iplus_singleton.1 hy) hyz)
  · rintro z ⟨y, hy, hzy⟩
    exact Precausality.mem_Iminus_singleton.2
      (galileoCurve_lt_of_le_of_lt hzy (Precausality.mem_Iminus_singleton.1 hy))
  · rintro z ⟨y, hy, hyz⟩
    exact Precausality.mem_Iplus_singleton.2
      (galileoCurve_lt_of_le_of_lt (Precausality.mem_Jplus_singleton.1 hy) hyz)
  · rintro z ⟨y, hy, hzy⟩
    exact Precausality.mem_Iminus_singleton.2
      (galileoCurve_lt_of_lt_of_le hzy (Precausality.mem_Jminus_singleton.1 hy))

/-- A vertical segment `t ↦ (t, x)`, `t ∈ [a, b]`, `a < b`, inside `U`. -/
theorem galileoCurve_lt_vertical {a b : ℝ} {x : Fin n → ℝ} (hab : a < b)
    (hU : ∀ t ∈ Icc a b, ((t, x) : ℝ × (Fin n → ℝ)) ∈ U) :
    (galileoCurve n).lt U (a, x) (b, x) :=
  galileoCurve_lt_iff_graphLt.2 ⟨hab, fun _ => x, continuous_const, rfl, rfl, hU⟩

/-- The vertical through a point of an open set stays in it for a while. -/
theorem galileo_exists_vertical_subset {v : ℝ × (Fin n → ℝ)} (hv : v ∈ W) :
    ∃ δ > 0, ∀ t ∈ Icc (v.1 - δ) (v.1 + δ), ((t, v.2) : ℝ × (Fin n → ℝ)) ∈ W := by
  have hO : IsOpen ((fun t : ℝ => ((t, v.2) : ℝ × (Fin n → ℝ))) ⁻¹' W) :=
    W.isOpen.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO v.1 (by simpa using hv)
  refine ⟨ε / 2, half_pos hε, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- **Chronal neighbours**: in every open `V`, the points of `V` just before and just after `v` on
its vertical. -/
theorem galileoCurve_chronalNeighbours : (galileoCurve n).ChronalNeighbours := by
  refine ⟨fun V v hv => ?_, fun V v hv => ?_⟩
  · obtain ⟨δ, hδ, hV⟩ := galileo_exists_vertical_subset hv
    refine ⟨(v.1 - δ, v.2), hV _ ⟨le_rfl, by linarith⟩, ?_⟩
    have h := galileoCurve_lt_vertical (U := V) (a := v.1 - δ) (b := v.1) (x := v.2)
      (by linarith) fun t ht => hV t ⟨ht.1, by linarith [ht.2]⟩
    exact h
  · obtain ⟨δ, hδ, hV⟩ := galileo_exists_vertical_subset hv
    refine ⟨(v.1 + δ, v.2), hV _ ⟨by linarith, le_rfl⟩, ?_⟩
    have h := galileoCurve_lt_vertical (U := V) (a := v.1) (b := v.1 + δ) (x := v.2)
      (by linarith) fun t ht => hV t ⟨by linarith [ht.1], ht.2⟩
    exact h

/-- **Causal**: time increases strictly along `≪_M`. -/
theorem galileoCurve_isCausal : (galileoCurve n).IsCausal := by
  intro x y hxy hyx
  rcases hxy with hxy | ⟨rfl, -⟩
  · exact absurd (galileoCurve_le_fst hyx) (not_le.2 (galileoCurve_lt_fst hxy))
  · rfl

/-- **A time function** (the ladder node `time_function`): the time coordinate. -/
theorem galileoCurve_hasTimeFunction : (galileoCurve n).HasTimeFunction := by
  refine ⟨Prod.fst, continuous_fst, fun x y h hne => ?_⟩
  rcases h with h | ⟨rfl, -⟩
  · exact galileoCurve_lt_fst h
  · exact absurd rfl hne

/-- **The time coordinate is a time function** in the sense of `defi:fonction_temps` (DEC-10): a
strong morphism to the timelike line. A curve of `V = fst⁻¹ U` passes every time between its
ends, so those times lie in `U`. -/
theorem galileoCurve_isTimeFunction_fst :
    (galileoCurve n).IsTimeFunction (Prod.fst : ℝ × (Fin n → ℝ) → ℝ) := by
  have key : ∀ (U : Opens ℝ) (V : Opens (ℝ × (Fin n → ℝ))),
      (V : Set (ℝ × (Fin n → ℝ))) = Prod.fst ⁻¹' U → ∀ {x y : ℝ × (Fin n → ℝ)},
      (galileoCurve n).lt V x y → Icc x.1 y.1 ⊆ U := by
    intro U V hV x y h t ht
    obtain ⟨-, f, -, -, -, hfV⟩ := galileoCurve_lt_iff_graphLt.1 h
    have h' : ((t, f t) : ℝ × (Fin n → ℝ)) ∈ (V : Set (ℝ × (Fin n → ℝ))) := hfV t ht
    rw [hV] at h'
    exact h'
  refine ⟨continuous_fst, isOpenMap_fst, fun U V hV x y h => ?_,
    fun U V hV x y h => ⟨galileoCurve_lt_fst h, key U V hV h⟩⟩
  rcases h with h | ⟨rfl, hx⟩
  · exact ⟨(galileoCurve_lt_fst h).le, key U V hV h⟩
  · refine ⟨le_rfl, fun t ht => ?_⟩
    have h' : x ∈ (V : Set (ℝ × (Fin n → ℝ))) := hx
    rw [hV] at h'
    rw [Icc_self, mem_singleton_iff] at ht
    rw [ht]
    exact h'

/-- The convex combination `(1 − t)γ₀ + tγ₁` of two future chronal curves of a convex open `W`
with the same endpoints is a chronal homotopy with fixed endpoints in `W`: the time stays strictly
increasing. -/
theorem galileoCurve_chronalHomotopyOn_convexCombination
    (hW : Convex ℝ (W : Set (ℝ × (Fin n → ℝ)))) {γ₀ γ₁ : ℝ → ℝ × (Fin n → ℝ)}
    (h₀ : (galileoCurve n).ChronalCurveOn W γ₀ 0 1)
    (h₁ : (galileoCurve n).ChronalCurveOn W γ₁ 0 1) (hp : γ₁ 0 = γ₀ 0) (hq : γ₁ 1 = γ₀ 1) :
    (galileoCurve n).ChronalHomotopyOn W (fun t s => (1 - t) • γ₀ s + t • γ₁ s) γ₀ γ₁ := by
  obtain ⟨c₀, -, m₀⟩ := galileoCurve_chronalCurveOn_iff.1 h₀
  obtain ⟨c₁, -, m₁⟩ := galileoCurve_chronalCurveOn_iff.1 h₁
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have hc : ContinuousOn (fun x : ℝ × ℝ => (1 - x.1) • γ₀ x.2 + x.1 • γ₁ x.2)
        (Icc 0 1 ×ˢ Icc 0 1) :=
      ((continuousOn_const.sub continuousOn_fst).smul
        (c₀.comp continuousOn_snd fun x hx => hx.2)).add
        (continuousOn_fst.smul (c₁.comp continuousOn_snd fun x hx => hx.2))
    exact hc
  · have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    refine galileoCurve_chronalCurveOn_iff.2 ⟨(continuousOn_const.smul c₀).add
      (continuousOn_const.smul c₁), fun s hs => ?_, fun s hs s' hs' h => ?_⟩
    · exact hW (h₀.mem s hs) (h₁.mem s hs) h1t ht.1 (by ring)
    · have a : (γ₀ s).1 < (γ₀ s').1 := m₀ hs hs' h
      have b : (γ₁ s).1 < (γ₁ s').1 := m₁ hs hs' h
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rcases ht.2.lt_or_eq with ht1 | rfl
      · nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 a), mul_nonneg ht.1 (sub_pos.2 b).le]
      · simpa using b
  · show (1 - t) • γ₀ 0 + t • γ₁ 0 = γ₀ 0
    rw [hp, ← add_smul, sub_add_cancel, one_smul]
  · show (1 - t) • γ₀ 1 + t • γ₁ 1 = γ₀ 1
    rw [hq, ← add_smul, sub_add_cancel, one_smul]
  · show (1 - 0) • γ₀ s + (0 : ℝ) • γ₁ s = γ₀ s
    simp
  · show (1 - 1) • γ₀ s + (1 : ℝ) • γ₁ s = γ₁ s
    simp

/-- **Every convex open set is future one-connected.** -/
theorem galileoCurve_futureOneConnectedOn (hW : Convex ℝ (W : Set (ℝ × (Fin n → ℝ)))) :
    (galileoCurve n).FutureOneConnectedOn W := by
  intro p q γ₀ γ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
  exact ⟨_, galileoCurve_chronalHomotopyOn_convexCombination hW h₀ h₁ (hp₁.trans hp₀.symm)
    (hq₁.trans hq₀.symm)⟩

/-- **Future one-connected** (the ladder node `future_one_connected`). -/
theorem galileoCurve_futureOneConnected : (galileoCurve n).FutureOneConnected := by
  refine galileoCurve_futureOneConnectedOn ?_
  rw [Opens.coe_top]
  exact convex_univ

/-- Between two points of distinct times the full diamond of `M` is the open slab with its two
vertices, as for the printed causality (`galileoOn_diamond_top`). -/
theorem galileoCurve_diamond_top (hpq : p.1 < q.1) :
    (galileoCurve n).diamond ⊤ p q = {r | p.1 < r.1 ∧ r.1 < q.1} ∪ {p, q} := by
  have hlt : ∀ a b : ℝ × (Fin n → ℝ), galileoCurveLt n ⊤ a b ↔ a.1 < b.1 := fun _ _ =>
    galileoCurve_lt_top
  ext r
  rw [Causality.mem_diamond, galileoCurve_le, galileoCurve_le, hlt, hlt]
  simp only [Opens.mem_top, and_true, mem_union, mem_setOf_eq, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨h₁ | rfl, h₂ | rfl⟩
    · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
  · rintro (⟨h₁, h₂⟩ | rfl | rfl)
    · exact ⟨Or.inl h₁, Or.inl h₂⟩
    · exact ⟨Or.inr rfl, Or.inl hpq⟩
    · exact ⟨Or.inl hpq, Or.inr rfl⟩

/-- **The slab lemma in a convex open `W`**: a set causally convex in `W` holding two points of
times `t₀ < t₁` holds every point of `W` with time in `(t₀, t₁)`. -/
theorem galileoCurve_slab_subset_of_convex (hW : Convex ℝ (W : Set (ℝ × (Fin n → ℝ))))
    {V : Set (ℝ × (Fin n → ℝ))} (hV : (galileoCurve n).CausallyConvexIn V W) (hp : p ∈ V)
    (hq : q ∈ V) : {r | r ∈ W ∧ p.1 < r.1 ∧ r.1 < q.1} ⊆ V := by
  rintro r ⟨hrW, hpr, hrq⟩
  refine hV.2 p hp q hq (Causality.mem_diamond.2 ⟨Or.inl ?_, Or.inl ?_⟩)
  · exact galileoCurve_lt_of_segment_subset hpr (hW.segment_subset (hV.1 hp) hrW)
  · exact galileoCurve_lt_of_segment_subset hrq (hW.segment_subset hrW (hV.1 hq))

/-- **Not causally compact** (`n ≥ 1`): `J(p, q)` holds the open slab between the times of `p`
and `q`, whose first spatial coordinate is unbounded. -/
theorem galileoCurve_not_causallyCompact (hn : 1 ≤ n) : ¬ (galileoCurve n).CausallyCompact := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  have hK := (h ((0 : ℝ), 0) ((2 : ℝ), 0)).image
    (show Continuous fun r : ℝ × (Fin n → ℝ) => r.2 i by fun_prop)
  obtain ⟨B, hB⟩ := hK.bddAbove
  have hmem : (((1 : ℝ), fun _ : Fin n => B + 1) : ℝ × (Fin n → ℝ)) ∈
      (galileoCurve n).diamond ⊤ ((0 : ℝ), 0) ((2 : ℝ), 0) := by
    rw [galileoCurve_diamond_top (by norm_num)]
    exact Or.inl ⟨by norm_num, by norm_num⟩
  have := hB ⟨_, hmem, rfl⟩
  simp only at this
  linarith

/-- **No non-empty open set is strongly causal as a spacetime** (`n ≥ 1`), the slab argument run
in `W`: a ball `B ⊆ W` about `p ∈ W`; a neighbourhood of `p` causally convex in `W` holds a
point of `B` before `p` and one after, hence (straight segments in `B`) the point of `B` beside
`p` at the same time, which a small neighbourhood of `p` misses. -/
theorem galileoCurve_not_stronglyCausalOn (hn : 1 ≤ n)
    (hW : (W : Set (ℝ × (Fin n → ℝ))).Nonempty) : ¬ (galileoCurve n).StronglyCausalOn W := by
  intro h
  obtain ⟨p, hpW⟩ := hW
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 W.isOpen p hpW
  let x₁ : ℝ × (Fin n → ℝ) := (p.1, p.2 + fun _ => ε / 2)
  have hx₁ : x₁ ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp [x₁, dist_eq_norm, abs_of_pos hε, hε]
  have hne : p ≠ x₁ := by
    intro h
    have := congrArg (fun r : ℝ × (Fin n → ℝ) => r.2 ⟨0, hn⟩) h
    simp [x₁] at this
    linarith
  obtain ⟨V, hV, hVU, hVc⟩ := h p hpW ({x₁}ᶜ) (isOpen_compl_singleton.mem_nhds hne)
  obtain ⟨a, ⟨haV, haB⟩, b, ⟨hbV, hbB⟩, hap, hpb⟩ :=
    exists_before_after_of_mem_nhds (inter_mem hV (Metric.ball_mem_nhds p hε))
  have hax : (galileoCurve n).lt W a x₁ := galileoCurve_lt_of_segment_subset hap
    (((convex_ball p ε).segment_subset haB hx₁).trans hball)
  have hxb : (galileoCurve n).lt W x₁ b := galileoCurve_lt_of_segment_subset hpb
    (((convex_ball p ε).segment_subset hx₁ hbB).trans hball)
  have hx₁V : x₁ ∈ V := hVc.2 a haV b hbV (Causality.mem_diamond.2 ⟨Or.inl hax, Or.inl hxb⟩)
  exact hVU hx₁V rfl

/-- **Not locally strongly causal** (`n ≥ 1`). -/
theorem galileoCurve_not_locallyStronglyCausal (hn : 1 ≤ n) :
    ¬ (galileoCurve n).LocallyStronglyCausal := by
  intro h
  obtain ⟨W, hpW, hW⟩ := h 0
  exact galileoCurve_not_stronglyCausalOn hn ⟨0, hpW⟩ hW

/-! ### The printed causality -/

/-- The curve form is finer than the printed causality on every open set: a curve of `U` lies in
one connected component of `U`. -/
theorem galileoCurve_lt_imp_galileo (h : (galileoCurve n).lt U p q) : (galileo n).lt U p q := by
  obtain ⟨γ, hγc, rfl, rfl, hγU, hγm⟩ := h
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  exact ⟨hγU h0, hγm h0 h1 zero_lt_one,
    (isPreconnected_Icc.image γ hγc).subset_connectedComponentIn (mem_image_of_mem γ h0)
      hγU.image_subset (mem_image_of_mem γ h1)⟩

theorem galileoCurve_le_imp_galileo (h : (galileoCurve n).le U p q) : (galileo n).le U p q :=
  h.imp_left galileoCurve_lt_imp_galileo

/-- **On a convex open set the curve form is the printed causality**, chronological relations:
the straight segment. -/
theorem galileoCurve_lt_iff_galileo_of_convex (hU : Convex ℝ (U : Set (ℝ × (Fin n → ℝ)))) :
    (galileoCurve n).lt U p q ↔ (galileo n).lt U p q := by
  refine ⟨galileoCurve_lt_imp_galileo, fun ⟨hp, hpq, hq⟩ => ?_⟩
  exact galileoCurve_lt_of_segment_subset hpq
    (hU.segment_subset hp (connectedComponentIn_subset _ _ hq))

/-- **On a convex open set the curve form is the printed causality**, causal relations. -/
theorem galileoCurve_le_iff_galileo_of_convex (hU : Convex ℝ (U : Set (ℝ × (Fin n → ℝ)))) :
    (galileoCurve n).le U p q ↔ (galileo n).le U p q :=
  or_congr_left (galileoCurve_lt_iff_galileo_of_convex hU)

/-- **The curve form is generated by the printed relations of small convex open sets**: for any
open cover `S`, `p ≪_U q` iff a chain of steps joins `p` to `q`, each a printed relation
`≪_B` in a convex open `B ⊆ U ∩ O`, `O ∈ S`. -/
theorem galileoCurve_lt_iff_transGen_convex (S : Set (Opens (ℝ × (Fin n → ℝ))))
    (hS : ∀ x, ∃ O ∈ S, x ∈ O) :
    (galileoCurve n).lt U p q ↔
      TransGen (fun a b => ∃ B : Opens (ℝ × (Fin n → ℝ)), ∃ O ∈ S, B ≤ U ⊓ O ∧
        Convex ℝ (B : Set (ℝ × (Fin n → ℝ))) ∧ (galileo n).lt B a b) p q := by
  constructor
  · rintro ⟨γ, hγc, rfl, rfl, hγU, hγm⟩
    let r : Opens (ℝ × (Fin n → ℝ)) → ℝ × (Fin n → ℝ) → ℝ × (Fin n → ℝ) → Prop := fun N =>
      TransGen (fun a b => ∃ B : Opens (ℝ × (Fin n → ℝ)), ∃ O ∈ S, B ≤ N ⊓ O ∧
        Convex ℝ (B : Set (ℝ × (Fin n → ℝ))) ∧ (galileo n).lt B a b)
    have hr : IsRelFamily r := by
      refine ⟨fun h => ?_, fun h => ?_, fun h₁ h₂ => h₁.trans h₂, fun hN _ _ h => ?_⟩
      · obtain ⟨z, ⟨B, O, -, hB, -, hab⟩, -⟩ := TransGen.head'_iff.1 h
        exact (hB hab.1).1
      · obtain ⟨z, -, ⟨B, O, -, hB, -, hab⟩⟩ := TransGen.tail'_iff.1 h
        exact (hB hab.mem_right).1
      · exact h.mono fun a b ⟨B, O, hO, hB, hc, hab⟩ =>
          ⟨B, O, hO, hB.trans (inf_le_inf_right O hN), hc, hab⟩
    have hc : CurveOn r U γ 0 1 := by
      refine ⟨fun t ht => hγU ht, fun t ht N hN htN => ?_⟩
      obtain ⟨O, hOS, hO⟩ := hS (γ t)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (N ⊓ O).isOpen (γ t) ⟨htN, hO⟩
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hγc t ht) ε hε
      refine ⟨t - δ, t + δ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
      have hd1 : dist s t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have hd2 : dist s' t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      let B : Opens (ℝ × (Fin n → ℝ)) := ⟨Metric.ball (γ t) ε, Metric.isOpen_ball⟩
      have hBc : Convex ℝ (B : Set (ℝ × (Fin n → ℝ))) := convex_ball (γ t) ε
      refine TransGen.single ⟨B, O, hOS, fun z hz => hball hz, hBc, ?_⟩
      exact (galileoCurve_lt_iff_galileo_of_convex hBc).1
        (galileoCurve_lt_of_segment_subset (hγm hs hs' h2)
          ((convex_ball (γ t) ε).segment_subset (hδc hs hd1) (hδc hs' hd2)))
    exact CurveOn.rel_of_lt hr hc le_rfl zero_lt_one le_rfl
  · intro h
    induction h with
    | single hab =>
      obtain ⟨B, O, -, hB, hc, hab⟩ := hab
      exact (galileoCurve n).lt_mono (hB.trans inf_le_left)
        ((galileoCurve_lt_iff_galileo_of_convex hc).2 hab)
    | tail _ hbc ih =>
      obtain ⟨B, O, -, hB, hc, hbc⟩ := hbc
      exact (galileoCurve n).lt_trans ih ((galileoCurve n).lt_mono (hB.trans inf_le_left)
        ((galileoCurve_lt_iff_galileo_of_convex hc).2 hbc))

/-- **The curve form is not the printed causality** (`n ≥ 1`): one is absolutely minimal
(`galileoCurve_causallyArcConnected`), the other not (`GluingModels.galileo_not_minimal`). -/
theorem galileoCurve_ne_galileo (hn : 1 ≤ n) : galileoCurve n ≠ galileo n := by
  intro h
  have hAM : (galileoCurve n).AbsolutelyMinimal :=
    Causality.CausallyArcConnected.absolutelyMinimal galileoCurve_causallyArcConnected
  rw [h] at hAM
  exact GluingModels.galileo_not_minimal n hn hAM

/-- **The printed causality relates strictly more** (`n ≥ 1`): on some open set, a printed
chronological relation that no time-increasing curve of that set realises. -/
theorem exists_galileo_lt_not_galileoCurve_lt (hn : 1 ≤ n) :
    ∃ (U : Opens (ℝ × (Fin n → ℝ))) (p q : ℝ × (Fin n → ℝ)),
      (galileo n).lt U p q ∧ ¬ (galileoCurve n).lt U p q := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hlt : (galileoCurve n).lt = (galileo n).lt := by
    funext U p q
    exact propext ⟨galileoCurve_lt_imp_galileo, hcon U p q⟩
  refine galileoCurve_ne_galileo hn (Causality.ext ?_ hlt)
  funext U p q
  exact propext (or_congr_left (iff_of_eq (congrFun (congrFun (congrFun hlt U) p) q)))

/-! ### The full form -/

/-- **Galileo's spacetime in its curve form, full form** (`n ≥ 1`): every causality-sort node of
the ladder decided. Holding: causally arc-connected, absolutely minimal (and on every open set),
push-up (and locally), causally open (two-sided; in the future; both local forms), tarentin,
chronal neighbours, a chronal neighbour at every point, causally plain, causal, a time function
(and the time coordinate one, `defi:fonction_temps`), future one-connected, curves extend.
Failing: locally strongly causal, strongly causal in either form, causally compact, globally
hyperbolic. Proved directly: arc-connectedness, push-up, chronal neighbours, the time function,
future one-connectedness, `¬ LocallyStronglyCausal`, `¬ CausallyCompact`, and
`∀ W, AbsolutelyMinimalOn W` (through `CausallyArcConnectedOn.absolutelyMinimalOn`); the rest by
`causal_ladder`, through causally_arc_connected ⇒ absolutely_minimal, push_up ∧
chronal_neighbours ⇒ causally_open and ⇒ causally_plain, chronal_neighbours ⇒ tarentin and ⇒
has_chronal_neighbour, push_up ⇒ locally_push_up, causally_open ⇒ causally_open_future and ⇒
locally_causally_open, causally_open_future ⇒ locally_causally_open_future, time_function ⇒
is_causal, and curves_extend (time_function ⇒ curves_extend, or the fact on T1 second countable
spaces); and, under a negation, strongly_causal ⇒ locally_strongly_causal, strongly_causal_open ⇒
strongly_causal, globally_hyperbolic ⇒ causally_compact. -/
theorem galileoCurve_separates (hn : 1 ≤ n) :
    (galileoCurve n).CausallyArcConnected ∧ (galileoCurve n).AbsolutelyMinimal ∧
      (∀ W : Opens (ℝ × (Fin n → ℝ)), (galileoCurve n).AbsolutelyMinimalOn W) ∧
      (galileoCurve n).PushUp ∧ (galileoCurve n).LocallyPushUp ∧
      (galileoCurve n).CausallyOpen ∧ (galileoCurve n).CausallyOpenFuture ∧
      (galileoCurve n).LocallyCausallyOpen ∧ (galileoCurve n).LocallyCausallyOpenFuture ∧
      (galileoCurve n).Tarentin ∧ (galileoCurve n).ChronalNeighbours ∧
      (galileoCurve n).HasChronalNeighbourEverywhere ∧ (galileoCurve n).CausallyPlain ∧
      (galileoCurve n).IsCausal ∧ (galileoCurve n).HasTimeFunction ∧
      (galileoCurve n).IsTimeFunction (Prod.fst : ℝ × (Fin n → ℝ) → ℝ) ∧
      (galileoCurve n).FutureOneConnected ∧ (galileoCurve n).CurvesExtend ∧
      ¬ (galileoCurve n).LocallyStronglyCausal ∧ ¬ (galileoCurve n).StronglyCausal ∧
      ¬ (galileoCurve n).StronglyCausalOpen ∧ ¬ (galileoCurve n).CausallyCompact ∧
      ¬ (galileoCurve n).GloballyHyperbolic := by
  have hAC : (galileoCurve n).CausallyArcConnected := galileoCurve_causallyArcConnected
  have hPU : (galileoCurve n).PushUp := galileoCurve_pushUp
  have hCN : (galileoCurve n).ChronalNeighbours := galileoCurve_chronalNeighbours
  have hTF : (galileoCurve n).HasTimeFunction := galileoCurve_hasTimeFunction
  have hLSC : ¬ (galileoCurve n).LocallyStronglyCausal :=
    galileoCurve_not_locallyStronglyCausal hn
  have hNCC : ¬ (galileoCurve n).CausallyCompact := galileoCurve_not_causallyCompact hn
  have hAM : (galileoCurve n).AbsolutelyMinimal := by causal_ladder
  have hCO : (galileoCurve n).CausallyOpen := by causal_ladder
  have hNSC : ¬ (galileoCurve n).StronglyCausal := fun h => hLSC (by causal_ladder)
  exact ⟨hAC, hAM, fun W => Causality.CausallyArcConnectedOn.absolutelyMinimalOn
      (Causality.CausallyArcConnectedOn.mono hAC le_top), hPU, by causal_ladder, hCO,
    by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder, hCN,
    by causal_ladder, by causal_ladder, by causal_ladder, hTF, galileoCurve_isTimeFunction_fst,
    galileoCurve_futureOneConnected, by causal_ladder, hLSC, hNSC,
    fun h => hNSC (by causal_ladder), hNCC, fun h => hNCC (by causal_ladder)⟩

end Causal
