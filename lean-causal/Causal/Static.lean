import Causal.Cauchy
import Causal.Chains
import Causal.PushUp
import Causal.StrongCausality
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Static spacetimes `ℝ × X` over a geodesic metric space

No label of the paper is certified by this file: it is the foundation the model spaces of
`subsec:sing_spacetime_defi` instantiate. Minkowski space is the instance of
`Causal.Minkowski`. The paper's definition, `defi:causal_Ealpha` — `ETT.tex:1335`:

> The causal and chronological orders of $\mass{\alpha}$ give rise to a sheaf with values in
> $\mathbf{C}$: for $\U\subset \mass{\alpha}$ open and $x,y\in \U$, one sets $x\leq_\U y$ (resp.
> $x\ll_\U y$) if and only if there is a future causal (resp. chronological) curve from $x$ to $y$
> in $\U$.

> In the model spaces, the concatenation of a future causal curve with a future chronological one
> is future chronological. [...] Since this holds in every open subset of $\mass{\kappa}$, the
> model spaces have the push-up property of Definition \ref{defi:pushup}. (`rem:pushup`,
> `ETT.tex:1374`)

> For every $\kappa\geq 0$ and every $p\in \mass{\kappa}$,
> $\ring J^\pm(p)\cap Z^\mp(\mass{\kappa})=I^\pm(p)$. (`lem:IJ_calc`, `ETT.tex:1441`)

> (a) $J^+(p)=\overline{I^+(p)}$; (b) $J^-(p)=\overline{I^-(p)}$ if $\kappa>0$ [...] The same holds
> in any causally convex open subset of $\mass{\kappa}$, with $J^\pm$ and $I^\pm$ taken in that
> subset. (`lem:densite_modele`, `ETT.tex:1464`)

## The construction

`X` is a metric space which is **geodesic** (`GeodesicSpace`, defined here: mathlib has no such
notion at this pin): any two points are joined by `g : [0,1] → X` with
`d(g s, g s') = |s − s'|·d(x,y)`. Every real normed space is one. On `ℝ × X` (product topology,
the max metric):

* a **future causal curve** from `(s,x)` to `(t,y)`, `s ≤ t`, is the graph `τ ↦ (τ, γ τ)` over
  `[s,t]` of a 1-Lipschitz `γ` (`StaticCurve 1`);
* a **future chronological curve** is the same with `s < t` and `γ` `c`-Lipschitz for some
  `c < 1` (`StaticCurve c`);
* `x ≤_U y` (resp. `x ≪_U y`) iff such a curve has its graph in `U` (`staticLe`, `staticLt`),
  which is `staticCausality X`.

## What is proved

* `staticCausality X` is a `Causality`: (a)–(c), `≪` transitive and open; openness perturbs the
  end of a chronological curve by a geodesic segment inside a ball of `U`
  (`isOpen_setOf_staticLt`), and the past end by time reversal (`staticLt_flip_iff`).
* Globally `x ≤ y ⟺ t − s ≥ d(x,y)` and `x ≪ y ⟺ t − s > d(x,y)` (`le_top_iff`, `lt_top_iff`).
* Causal (`isCausal`), causally arc-connected (`causallyArcConnected`, the graphs being causal
  and chronal curves of `Causal.Curves`: `causalCurveOn_graph`, `chronalCurveOn_graph`), hence
  absolutely minimal (`cor:causalement_connexe_minimal`).
* Push-up in every open set (`pushUp`): a chronological curve followed by a causal one is
  re-timed inside a tube of the open set (`staticLt_of_staticLt_of_staticLe`).
* Tarentin, `Z^+ = Z^- = M`, strongly causal; globally hyperbolic when `X` is proper.
* `J^±(p) = closure(I^±(p))`, also in every causally convex open subset; `lem:IJ_calc`'s
  identity.
* With `X` complete, every inextensible causal curve over `ℝ` has its time coordinate tending to
  `±∞` (`tendsto_time_atTop`, `tendsto_time_atBot`), through two general facts: an
  inextensible curve over `ℝ` has no limit at its ends (`Inextensible.not_tendsto_atBot`,
  `…_atTop`, from `extensible_of_tendsto`), and a curve along which a monotone function is
  unbounded both ways is inextensible (`inextensible_of_unbounded`); a bounded 1-Lipschitz
  `g` gives a Cauchy time function `t − g(x)` (`isCauchyTimeFunction_sub`); with a geodesic line `ℓ` the null line `τ ↦ (τ, ℓ τ)`
  is inextensible (`inextensible_nullLine`). If `X` has two points, `≤` has two unrelated open sets
  in every open set, so there is no maximal causal chain (`not_isMaximalChain`).
* `K^±(A) = I^±(A)`, `J^±(A) \ K^±(A) ⊂ ∂I^±(A)`, and `J^-(q) \ J^-(p)` contains a non-empty
  open set for `p < q`: the two conditions of `defi:mesure_dieckmann` reduced to measure theory
  (used by `CausalScaffold.MinkowskiMeasure`).

## Hypothesis checklist

| paper | here |
|---|---|
| the model space `E^{1,2}` | ⚠ weakened: `ℝ × X`, `X` any geodesic metric space |
| chronological curve | read: graph of a `c`-Lipschitz map, `c < 1`, over a non-trivial segment; same `≪_U` as "speed `< 1` at every point" (see SCOPE) |
| strongly causal, globally hyperbolic | the latter with `X` proper |

## SCOPE (disclosed)

* **Chronological curves are uniformly timelike**: `c`-Lipschitz for one `c < 1` on the whole
  segment. For a `C¹` curve on a compact segment, `|γ'| < 1` everywhere is the same condition,
  and the relations it defines globally are the paper's (`lt_top_iff`). A curve whose speed
  is `< 1` at every point but has supremum 1 is not itself chronological here, **but the
  relation `≪_U` is the same under both readings, in every open `U`** (argument in prose, not
  formalized): such a curve has strict chords, `d(γ s, γ s') < |s − s'|` for `s ≠ s'` (the
  chord is at most the integral of the metric speed); a fine enough inscribed polygon of
  geodesic segments (`GeodesicSpace`) through points `(τᵢ, γ τᵢ)` stays in a thickening of the
  compact graph, hence in `U`, and its finitely many slopes
  `d(γ τᵢ, γ τᵢ₊₁) / (τᵢ₊₁ − τᵢ)` have a maximum `c < 1`, so it is a chronological curve of this
  file between the same end points. The reading is therefore not a restriction; independently,
  `causallyArcConnected` ties `≪_U` to the chronal curves of `Causal.Curves`.
* The curves of the definition are graphs over the time axis; a causal curve of
  `Causal.Curves` may pause, the graphs are the ones used to *define* the relations.
* Nothing here is a label of the paper: the paper's model spaces are `E^{1,2}` and cones over it
  (`Causal.Minkowski` for the former).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Metric

universe u

/-! ### Geodesic metric spaces -/

/-- A **geodesic** metric space: any two points `x, y` are joined by a map `g` on `[0, 1]` with
`d(g s, g s') = |s − s'| · d(x, y)`. Mathlib has no such notion at this pin. -/
class GeodesicSpace (X : Type u) [PseudoMetricSpace X] : Prop where
  exists_geodesic : ∀ x y : X, ∃ g : ℝ → X, g 0 = x ∧ g 1 = y ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, dist (g s) (g s') = |s - s'| * dist x y

/-- Every real normed space is geodesic, by the affine segments. -/
instance (priority := 100) GeodesicSpace.ofNormedSpace (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : GeodesicSpace E where
  exists_geodesic x y := ⟨fun s => x + s • (y - x), by simp, by simp, fun s _ s' _ => by
    rw [dist_eq_norm, show x + s • (y - x) - (x + s' • (y - x)) = (s - s') • (y - x) by
      rw [sub_smul]; abel, norm_smul, Real.norm_eq_abs, dist_comm, dist_eq_norm]⟩

/-- **Sanity.** `ℝ` is a geodesic space. -/
example : GeodesicSpace ℝ := inferInstance

variable {X : Type u} [MetricSpace X]

/-- A geodesic segment over a time interval `[a, b]`, `a < b`, with constant speed
`d(x, y)/(b − a)`. -/
theorem exists_segment [GeodesicSpace X] (x y : X) {a b : ℝ} (hab : a < b) :
    ∃ γ : ℝ → X, γ a = x ∧ γ b = y ∧ ∀ τ ∈ Icc a b, ∀ τ' ∈ Icc a b,
      dist (γ τ) (γ τ') = dist x y / (b - a) * |τ - τ'| := by
  obtain ⟨g, hg0, hg1, hg⟩ := GeodesicSpace.exists_geodesic x y
  have hba : 0 < b - a := sub_pos.2 hab
  refine ⟨fun τ => g ((τ - a) / (b - a)), by simpa using hg0, by
    simp only; rw [div_self hba.ne']; exact hg1, fun τ hτ τ' hτ' => ?_⟩
  have hmem : ∀ σ ∈ Icc a b, (σ - a) / (b - a) ∈ Icc (0 : ℝ) 1 := fun σ hσ =>
    ⟨div_nonneg (by linarith [hσ.1]) hba.le, (div_le_one hba).2 (by linarith [hσ.2])⟩
  simp only
  rw [hg _ (hmem τ hτ) _ (hmem τ' hτ'), ← sub_div, show τ - a - (τ' - a) = τ - τ' by ring,
    abs_div, abs_of_pos hba]
  ring

/-! ### Lipschitz graphs -/

/-- `γ` is `L`-Lipschitz on `[a, b]`. -/
def LipOn (L : ℝ) (γ : ℝ → X) (a b : ℝ) : Prop :=
  ∀ τ ∈ Icc a b, ∀ τ' ∈ Icc a b, dist (γ τ) (γ τ') ≤ L * |τ - τ'|

/-- The graph `τ ↦ (τ, γ τ)` over `[a, b]` of an `L`-Lipschitz `γ`, contained in `U`. -/
structure StaticCurve (L : ℝ) (U : Set (ℝ × X)) (γ : ℝ → X) (a b : ℝ) : Prop where
  lip : LipOn L γ a b
  mem : ∀ τ ∈ Icc a b, (τ, γ τ) ∈ U

namespace LipOn

variable {L L' : ℝ} {γ γ₁ γ₂ : ℝ → X} {a b c : ℝ}

theorem mono (h : LipOn L γ a b) (hL : L ≤ L') : LipOn L' γ a b := fun τ hτ τ' hτ' =>
  (h τ hτ τ' hτ').trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))

theorem restrict (h : LipOn L γ a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    LipOn L γ a' b' := fun τ hτ τ' hτ' =>
  h τ ⟨ha.trans hτ.1, hτ.2.trans hb⟩ τ' ⟨ha.trans hτ'.1, hτ'.2.trans hb⟩

/-- A Lipschitz constant over a non-trivial segment is non-negative. -/
theorem nonneg (h : LipOn L γ a b) (hab : a < b) : 0 ≤ L := by
  have h1 := h a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
  have h2 : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab.ne)
  by_contra hL
  have : L * |a - b| < 0 := mul_neg_of_neg_of_pos (not_le.1 hL) h2
  linarith [dist_nonneg (x := γ a) (y := γ b)]

/-- Concatenation of two Lipschitz maps with a common value. -/
theorem concat (h₁ : LipOn L γ₁ a b) (h₂ : LipOn L' γ₂ b c) (hb : γ₁ b = γ₂ b) :
    LipOn (max L L') (fun τ => if τ ≤ b then γ₁ τ else γ₂ τ) a c := by
  have key : ∀ τ ∈ Icc a c, ∀ τ' ∈ Icc a c, τ ≤ τ' →
      dist ((fun τ => if τ ≤ b then γ₁ τ else γ₂ τ) τ)
        ((fun τ => if τ ≤ b then γ₁ τ else γ₂ τ) τ') ≤ max L L' * |τ - τ'| := by
    intro τ hτ τ' hτ' hle
    simp only
    by_cases h' : τ' ≤ b
    · have hτb : τ ≤ b := hle.trans h'
      rw [if_pos hτb, if_pos h']
      exact (h₁ τ ⟨hτ.1, hτb⟩ τ' ⟨hτ'.1, h'⟩).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    · by_cases hτb : τ ≤ b
      · rw [if_pos hτb, if_neg h']
        have hbτ' : b < τ' := not_le.1 h'
        have e1 := h₁ τ ⟨hτ.1, hτb⟩ b ⟨hτ.1.trans hτb, le_rfl⟩
        have e2 := h₂ b ⟨le_rfl, hbτ'.le.trans hτ'.2⟩ τ' ⟨hbτ'.le, hτ'.2⟩
        rw [abs_of_nonpos (by linarith)] at e1 e2
        rw [abs_of_nonpos (by linarith)]
        have := dist_triangle (γ₁ τ) (γ₁ b) (γ₂ τ')
        rw [hb] at this e1
        have m1 : L * -(τ - b) ≤ max L L' * -(τ - b) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        have m2 : L' * -(b - τ') ≤ max L L' * -(b - τ') :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
        nlinarith
      · have hbτ : b < τ := not_le.1 hτb
        rw [if_neg hτb, if_neg h']
        exact (h₂ τ ⟨hbτ.le, hτ.2⟩ τ' ⟨hbτ.le.trans hle, hτ'.2⟩).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
  intro τ hτ τ' hτ'
  rcases le_total τ τ' with h | h
  · exact key τ hτ τ' hτ' h
  · rw [dist_comm, abs_sub_comm]; exact key τ' hτ' τ hτ h

/-- Reparametrisation by an increasing affine map multiplies the constant by the slope. -/
theorem comp_affine {k m : ℝ} (hk : 0 < k) (h : LipOn L γ (k * a + m) (k * b + m)) :
    LipOn (L * k) (fun τ => γ (k * τ + m)) a b := by
  intro τ hτ τ' hτ'
  have h1 := h (k * τ + m) ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩ (k * τ' + m)
    ⟨by nlinarith [hτ'.1], by nlinarith [hτ'.2]⟩
  rw [show k * τ + m - (k * τ' + m) = k * (τ - τ') by ring, abs_mul, abs_of_pos hk] at h1
  simp only
  linarith

/-- Time reversal. -/
theorem neg (h : LipOn L γ a b) : LipOn L (fun τ => γ (-τ)) (-b) (-a) := by
  intro τ hτ τ' hτ'
  have := h (-τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩ (-τ') ⟨by linarith [hτ'.2],
    by linarith [hτ'.1]⟩
  rwa [show -τ - -τ' = -(τ - τ') by ring, abs_neg] at this

/-- A Lipschitz map is continuous on its segment. -/
theorem continuousOn (h : LipOn L γ a b) : ContinuousOn γ (Icc a b) := by
  rw [Metric.continuousOn_iff]
  intro τ hτ ε hε
  refine ⟨ε / (|L| + 1), div_pos hε (by positivity), fun τ' hτ' hd => ?_⟩
  have h1 := h τ' hτ' τ hτ
  rw [Real.dist_eq] at hd
  have h2 : L * |τ' - τ| ≤ |L| * |τ' - τ| :=
    mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
  have h3 : |L| * |τ' - τ| ≤ |L| * (ε / (|L| + 1)) :=
    mul_le_mul_of_nonneg_left hd.le (abs_nonneg _)
  have h4 : |L| * (ε / (|L| + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg L]
  linarith

/-- On a graph of slope at most 1, the distance of two points of the graph is the time gap. -/
theorem dist_graph_le (h : LipOn L γ a b) (hL : L ≤ 1) {τ σ : ℝ} (hτ : τ ∈ Icc a b)
    (hσ : σ ∈ Icc a b) : dist ((τ, γ τ) : ℝ × X) (σ, γ σ) ≤ |τ - σ| := by
  rw [Prod.dist_eq, Real.dist_eq]
  refine max_le le_rfl ((h τ hτ σ hσ).trans ?_)
  nlinarith [abs_nonneg (τ - σ)]

end LipOn

namespace StaticCurve

variable {L L' : ℝ} {U V : Set (ℝ × X)} {γ γ₁ γ₂ : ℝ → X} {a b c : ℝ}

theorem mono_set (h : StaticCurve L U γ a b) (hUV : U ⊆ V) : StaticCurve L V γ a b :=
  ⟨h.lip, fun τ hτ => hUV (h.mem τ hτ)⟩

theorem mono (h : StaticCurve L U γ a b) (hL : L ≤ L') : StaticCurve L' U γ a b :=
  ⟨h.lip.mono hL, h.mem⟩

theorem restrict (h : StaticCurve L U γ a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    StaticCurve L U γ a' b' :=
  ⟨h.lip.restrict ha hb, fun τ hτ => h.mem τ ⟨ha.trans hτ.1, hτ.2.trans hb⟩⟩

/-- Concatenation of two static curves. -/
theorem concat (h₁ : StaticCurve L U γ₁ a b) (h₂ : StaticCurve L' U γ₂ b c)
    (hb : γ₁ b = γ₂ b) :
    StaticCurve (max L L') U (fun τ => if τ ≤ b then γ₁ τ else γ₂ τ) a c := by
  refine ⟨h₁.lip.concat h₂.lip hb, fun τ hτ => ?_⟩
  by_cases h : τ ≤ b
  · simp only [if_pos h]; exact h₁.mem τ ⟨hτ.1, h⟩
  · simp only [if_neg h]; exact h₂.mem τ ⟨(not_le.1 h).le, hτ.2⟩

/-- The graph of a static curve is compact. -/
theorem isCompact_graph (h : StaticCurve L U γ a b) :
    IsCompact ((fun τ => ((τ, γ τ) : ℝ × X)) '' Icc a b) :=
  isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk h.lip.continuousOn)

end StaticCurve

omit [MetricSpace X] in
theorem concat_left {γ₁ γ₂ : ℝ → X} {a b : ℝ} (hab : a ≤ b) :
    (fun τ => if τ ≤ b then γ₁ τ else γ₂ τ) a = γ₁ a := by simp [hab]

omit [MetricSpace X] in
theorem concat_right {γ₁ γ₂ : ℝ → X} {b c : ℝ} (hbc : b ≤ c) (hb : γ₁ b = γ₂ b) :
    (fun τ => if τ ≤ b then γ₁ τ else γ₂ τ) c = γ₂ c := by
  by_cases h : c ≤ b
  · have : c = b := le_antisymm h hbc
    subst this; simp [hb]
  · simp [h]

/-- The constant map over a point. -/
theorem staticCurve_const {U : Set (ℝ × X)} {p : ℝ × X} (hp : p ∈ U) (L : ℝ) (hL : 0 ≤ L) :
    StaticCurve L U (fun _ => p.2) p.1 p.1 :=
  ⟨fun _ _ _ _ => by simp only [dist_self]; positivity, fun τ hτ => by
    rw [show τ = p.1 from le_antisymm hτ.2 hτ.1]; exact hp⟩

/-! ### The relations -/

/-- `p ≤_U q`: a future causal curve, the graph of a 1-Lipschitz map, from `p` to `q` in `U`. -/
def staticLe (U : Set (ℝ × X)) (p q : ℝ × X) : Prop :=
  p.1 ≤ q.1 ∧ ∃ γ : ℝ → X, γ p.1 = p.2 ∧ γ q.1 = q.2 ∧ StaticCurve 1 U γ p.1 q.1

/-- `p ≪_U q`: a future chronological curve, the graph of a `c`-Lipschitz map for some `c < 1`
over a non-trivial segment, from `p` to `q` in `U`. -/
def staticLt (U : Set (ℝ × X)) (p q : ℝ × X) : Prop :=
  p.1 < q.1 ∧ ∃ L < 1, ∃ γ : ℝ → X, γ p.1 = p.2 ∧ γ q.1 = q.2 ∧ StaticCurve L U γ p.1 q.1

variable {U V : Set (ℝ × X)} {p q r : ℝ × X}

theorem staticCurve_mem_left {L : ℝ} {γ : ℝ → X} (h : StaticCurve L U γ p.1 q.1)
    (hpq : p.1 ≤ q.1) (hγ : γ p.1 = p.2) : p ∈ U := by
  have := h.mem p.1 ⟨le_rfl, hpq⟩
  rwa [hγ] at this

theorem staticCurve_mem_right {L : ℝ} {γ : ℝ → X} (h : StaticCurve L U γ p.1 q.1)
    (hpq : p.1 ≤ q.1) (hγ : γ q.1 = q.2) : q ∈ U := by
  have := h.mem q.1 ⟨hpq, le_rfl⟩
  rwa [hγ] at this

/-- The causal relation bounds the distance by the time gap. -/
theorem staticLe.dist_le (h : staticLe U p q) : dist p.2 q.2 ≤ q.1 - p.1 := by
  obtain ⟨hpq, γ, hγp, hγq, hγ⟩ := h
  have := hγ.lip p.1 ⟨le_rfl, hpq⟩ q.1 ⟨hpq, le_rfl⟩
  rw [hγp, hγq, abs_of_nonpos (by linarith)] at this
  linarith

/-- The chronological relation bounds the distance strictly by the time gap. -/
theorem staticLt.dist_lt (h : staticLt U p q) : dist p.2 q.2 < q.1 - p.1 := by
  obtain ⟨hpq, L, hL, γ, hγp, hγq, hγ⟩ := h
  have := hγ.lip p.1 ⟨le_rfl, hpq.le⟩ q.1 ⟨hpq.le, le_rfl⟩
  rw [hγp, hγq, abs_of_nonpos (by linarith)] at this
  nlinarith

theorem staticLt.staticLe (h : staticLt U p q) : staticLe U p q := by
  obtain ⟨hpq, L, hL, γ, hγp, hγq, hγ⟩ := h
  exact ⟨hpq.le, γ, hγp, hγq, hγ.mono hL.le⟩

theorem staticLe.mono (h : staticLe U p q) (hUV : U ⊆ V) : staticLe V p q := by
  obtain ⟨hpq, γ, hγp, hγq, hγ⟩ := h
  exact ⟨hpq, γ, hγp, hγq, hγ.mono_set hUV⟩

theorem staticLt.mono (h : staticLt U p q) (hUV : U ⊆ V) : staticLt V p q := by
  obtain ⟨hpq, L, hL, γ, hγp, hγq, hγ⟩ := h
  exact ⟨hpq, L, hL, γ, hγp, hγq, hγ.mono_set hUV⟩

theorem staticLe.mem_left (h : staticLe U p q) : p ∈ U :=
  staticCurve_mem_left h.2.choose_spec.2.2 h.1 h.2.choose_spec.1

theorem staticLe.mem_right (h : staticLe U p q) : q ∈ U :=
  staticCurve_mem_right h.2.choose_spec.2.2 h.1 h.2.choose_spec.2.1

theorem staticLe_refl (hp : p ∈ U) : staticLe U p p :=
  ⟨le_rfl, fun _ => p.2, rfl, rfl, staticCurve_const hp 1 zero_le_one⟩

theorem staticLe.trans (h₁ : staticLe U p q) (h₂ : staticLe U q r) : staticLe U p r := by
  obtain ⟨hpq, γ₁, hγ₁p, hγ₁q, hγ₁⟩ := h₁
  obtain ⟨hqr, γ₂, hγ₂q, hγ₂r, hγ₂⟩ := h₂
  have hb : γ₁ q.1 = γ₂ q.1 := hγ₁q.trans hγ₂q.symm
  refine ⟨hpq.trans hqr, fun τ => if τ ≤ q.1 then γ₁ τ else γ₂ τ,
    by rw [concat_left hpq, hγ₁p], by rw [concat_right hqr hb, hγ₂r], ?_⟩
  simpa using hγ₁.concat hγ₂ hb

theorem staticLt.trans (h₁ : staticLt U p q) (h₂ : staticLt U q r) : staticLt U p r := by
  obtain ⟨hpq, L₁, hL₁, γ₁, hγ₁p, hγ₁q, hγ₁⟩ := h₁
  obtain ⟨hqr, L₂, hL₂, γ₂, hγ₂q, hγ₂r, hγ₂⟩ := h₂
  have hb : γ₁ q.1 = γ₂ q.1 := hγ₁q.trans hγ₂q.symm
  exact ⟨hpq.trans hqr, max L₁ L₂, max_lt hL₁ hL₂, fun τ => if τ ≤ q.1 then γ₁ τ else γ₂ τ,
    by rw [concat_left hpq.le, hγ₁p],
    by rw [concat_right hqr.le hb, hγ₂r], hγ₁.concat hγ₂ hb⟩

/-- `p ≤ q` with equal times forces `p = q`. -/
theorem staticLe.eq_of_fst_eq (h : staticLe U p q) (he : p.1 = q.1) : p = q := by
  have := h.dist_le
  rw [he, sub_self] at this
  exact Prod.ext he (dist_le_zero.1 this)

/-! ### Segments, balls, the global relations -/

/-- The geodesic segment from `p` to `q`, as the graph of a map of slope `d(p, q)/(q.1 − p.1)`. -/
theorem exists_lipOn_segment [GeodesicSpace X] (hpq : p.1 < q.1) :
    ∃ γ : ℝ → X, γ p.1 = p.2 ∧ γ q.1 = q.2 ∧ LipOn (dist p.2 q.2 / (q.1 - p.1)) γ p.1 q.1 := by
  obtain ⟨γ, h0, h1, hγ⟩ := exists_segment p.2 q.2 hpq
  exact ⟨γ, h0, h1, fun τ hτ τ' hτ' => (hγ τ hτ τ' hτ').le⟩

/-- If the open ball of radius `ρ` around `p` lies in `U`, a point `q` in the closed future cone of
`p` with time gap less than `ρ` satisfies `p ≤_U q`. -/
theorem staticLe_of_ball [GeodesicSpace X] {ρ : ℝ} (hball : ∀ z, dist z p < ρ → z ∈ U)
    (hpq : p.1 ≤ q.1) (hd : dist p.2 q.2 ≤ q.1 - p.1) (hρ : q.1 - p.1 < ρ) :
    staticLe U p q := by
  rcases hpq.eq_or_lt with he | hlt
  · have hq : q.2 = p.2 := by
      rw [he, sub_self] at hd
      exact (dist_le_zero.1 hd).symm
    have : q = p := Prod.ext he.symm hq
    subst this
    exact staticLe_refl (hball _ (by rw [dist_self]; linarith))
  obtain ⟨γ, h0, h1, hγ⟩ := exists_lipOn_segment hlt
  have hK : dist p.2 q.2 / (q.1 - p.1) ≤ 1 := (div_le_one (sub_pos.2 hlt)).2 hd
  refine ⟨hpq, γ, h0, h1, hγ.mono hK, fun τ hτ => hball _ ?_⟩
  have := hγ.dist_graph_le hK hτ ⟨le_rfl, hpq⟩
  rw [h0, abs_of_nonneg (by linarith [hτ.1])] at this
  exact this.trans_lt (by linarith [hτ.2])

/-- The chronological form of `staticLe_of_ball`. -/
theorem staticLt_of_ball [GeodesicSpace X] {ρ : ℝ} (hball : ∀ z, dist z p < ρ → z ∈ U)
    (hd : dist p.2 q.2 < q.1 - p.1) (hρ : q.1 - p.1 < ρ) : staticLt U p q := by
  have hlt : p.1 < q.1 := by linarith [dist_nonneg (x := p.2) (y := q.2)]
  obtain ⟨γ, h0, h1, hγ⟩ := exists_lipOn_segment hlt
  have hK : dist p.2 q.2 / (q.1 - p.1) < 1 := (div_lt_one (sub_pos.2 hlt)).2 hd
  refine ⟨hlt, _, hK, γ, h0, h1, hγ, fun τ hτ => hball _ ?_⟩
  have := hγ.dist_graph_le hK.le hτ ⟨le_rfl, hlt.le⟩
  rw [h0, abs_of_nonneg (by linarith [hτ.1])] at this
  exact this.trans_lt (by linarith [hτ.2])

/-- Globally, `p ≤ q` iff `d(p, q) ≤ q.1 − p.1`. -/
theorem staticLe_univ_iff [GeodesicSpace X] : staticLe univ p q ↔ dist p.2 q.2 ≤ q.1 - p.1 :=
  ⟨staticLe.dist_le, fun h => staticLe_of_ball (ρ := q.1 - p.1 + 1) (fun _ _ => trivial)
    (by linarith [dist_nonneg (x := p.2) (y := q.2)]) h (by linarith)⟩

/-- Globally, `p ≪ q` iff `d(p, q) < q.1 − p.1`. -/
theorem staticLt_univ_iff [GeodesicSpace X] : staticLt univ p q ↔ dist p.2 q.2 < q.1 - p.1 :=
  ⟨staticLt.dist_lt, fun h => staticLt_of_ball (ρ := q.1 - p.1 + 1) (fun _ _ => trivial) h
    (by linarith)⟩

/-! ### Time reversal -/

/-- Time reversal `(t, x) ↦ (−t, x)`. -/
def flipT (p : ℝ × X) : ℝ × X := (-p.1, p.2)

omit [MetricSpace X] in
@[simp] theorem flipT_fst : (flipT p).1 = -p.1 := rfl
omit [MetricSpace X] in
@[simp] theorem flipT_snd : (flipT p).2 = p.2 := rfl
omit [MetricSpace X] in
@[simp] theorem flipT_flipT : flipT (flipT p) = p := by simp [flipT]

theorem continuous_flipT : Continuous (flipT (X := X)) :=
  continuous_fst.neg.prodMk continuous_snd

omit [MetricSpace X] in
theorem preimage_flipT_flipT : flipT ⁻¹' (flipT ⁻¹' U) = U := by ext; simp

theorem StaticCurve.flip {L : ℝ} {γ : ℝ → X} {a b : ℝ} (h : StaticCurve L U γ a b) :
    StaticCurve L (flipT ⁻¹' U) (fun τ => γ (-τ)) (-b) (-a) :=
  ⟨h.lip.neg, fun τ hτ => by
    show flipT (τ, γ (-τ)) ∈ U
    exact h.mem (-τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩⟩

theorem staticLe.flip (h : staticLe U p q) : staticLe (flipT ⁻¹' U) (flipT q) (flipT p) := by
  obtain ⟨hpq, γ, hγp, hγq, hγ⟩ := h
  exact ⟨by simpa using hpq, fun τ => γ (-τ), by simpa using hγq, by simpa using hγp, hγ.flip⟩

theorem staticLt.flip (h : staticLt U p q) : staticLt (flipT ⁻¹' U) (flipT q) (flipT p) := by
  obtain ⟨hpq, L, hL, γ, hγp, hγq, hγ⟩ := h
  exact ⟨by simpa using hpq, L, hL, fun τ => γ (-τ), by simpa using hγq, by simpa using hγp,
    hγ.flip⟩

theorem staticLe_flip_iff : staticLe (flipT ⁻¹' U) (flipT q) (flipT p) ↔ staticLe U p q :=
  ⟨fun h => by simpa [preimage_flipT_flipT] using h.flip, staticLe.flip⟩

theorem staticLt_flip_iff : staticLt (flipT ⁻¹' U) (flipT q) (flipT p) ↔ staticLt U p q :=
  ⟨fun h => by simpa [preimage_flipT_flipT] using h.flip, staticLt.flip⟩

/-! ### Openness of the chronological relation -/

/-- **`I^+_U(p)` is open.** A chronological curve from `p` to `q` is followed until a time `δ`
before `q`, then replaced by a geodesic segment to the perturbed endpoint, inside a ball of `U`
around `q`; the slope stays below `(1 + L)/2`. -/
theorem isOpen_setOf_staticLt [GeodesicSpace X] (hU : IsOpen U) (p : ℝ × X) :
    IsOpen {q | staticLt U p q} := by
  rw [Metric.isOpen_iff]
  rintro q ⟨hpq, L, hL, γ, hγp, hγq, hγ⟩
  have hqU : q ∈ U := staticCurve_mem_right hγ hpq.le hγq
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU q hqU
  have hL0 : 0 ≤ L := hγ.lip.nonneg hpq
  set δ := min (q.1 - p.1) (ρ / 4) with hδ
  have hδpos : 0 < δ := lt_min (sub_pos.2 hpq) (by linarith)
  have hδ1 : δ ≤ q.1 - p.1 := min_le_left _ _
  have hδ2 : δ ≤ ρ / 4 := min_le_right _ _
  set c := (1 + L) / 2 with hc
  have hcL : 0 ≤ c - L := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  set η := (c - L) * δ / 4 with hη
  have hηpos : 0 < η := by
    rw [hη]; have : 0 < c - L := by rw [hc]; linarith
    positivity
  have hη8 : η ≤ δ / 8 := by
    rw [hη]; have : c - L ≤ 1 / 2 := by rw [hc]; linarith
    nlinarith
  refine ⟨η, hηpos, fun q' hq' => ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq] at hq'
  obtain ⟨ht', hy'⟩ := hq'
  have ht'1 : q.1 - η < q'.1 := by linarith [neg_abs_le (q'.1 - q.1)]
  have ht'2 : q'.1 < q.1 + η := by linarith [le_abs_self (q'.1 - q.1)]
  set t₀ := q.1 - δ with ht₀
  have hpt₀ : p.1 ≤ t₀ := by linarith
  have ht₀q' : t₀ < q'.1 := by linarith
  obtain ⟨σ, hσ0, hσ1, hσ⟩ := exists_segment (γ t₀) q'.2 ht₀q'
  set K := dist (γ t₀) q'.2 / (q'.1 - t₀) with hK
  have hK0 : 0 ≤ K := div_nonneg dist_nonneg (by linarith)
  have hγt₀ : dist (γ t₀) q.2 ≤ L * δ := by
    have h1 := hγ.lip t₀ ⟨hpt₀, by linarith⟩ q.1 ⟨hpq.le, le_rfl⟩
    rwa [hγq, show t₀ - q.1 = -δ by rw [ht₀]; ring, abs_neg, abs_of_pos hδpos] at h1
  have hD : dist (γ t₀) q'.2 ≤ L * δ + η := by
    have h2 := dist_triangle (γ t₀) q.2 q'.2
    rw [dist_comm q.2] at h2
    linarith
  have hkey : L * δ + η ≤ c * (δ - η) := by
    have : c * (δ - η) - (L * δ + η) = (c - L) * δ * (3 - c) / 4 := by rw [hη]; ring
    have h3 : 0 ≤ (c - L) * δ * (3 - c) / 4 := by
      have : 0 ≤ 3 - c := by linarith
      positivity
    linarith
  have hKc : K ≤ c := by
    rw [hK, div_le_iff₀ (by linarith)]
    have : c * (δ - η) ≤ c * (q'.1 - t₀) :=
      mul_le_mul_of_nonneg_left (by linarith) (by rw [hc]; linarith)
    linarith
  have hb : γ t₀ = σ t₀ := hσ0.symm
  have hσc : StaticCurve K U σ t₀ q'.1 := by
    refine ⟨fun τ hτ τ' hτ' => (hσ τ hτ τ' hτ').le, fun τ hτ => hball ?_⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
    have hτ1 : |τ - q.1| ≤ δ := abs_le.2 ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    refine ⟨by linarith, ?_⟩
    have h4 := hσ τ hτ t₀ ⟨le_rfl, ht₀q'.le⟩
    rw [hσ0, abs_of_nonneg (by linarith [hτ.1])] at h4
    have h5 : K * (τ - t₀) ≤ K * (q'.1 - t₀) := mul_le_mul_of_nonneg_left (by linarith [hτ.2]) hK0
    have h6 : K * (q'.1 - t₀) = dist (γ t₀) q'.2 := by
      rw [hK, div_mul_cancel₀ _ (by linarith : q'.1 - t₀ ≠ 0)]
    have h7 := dist_triangle (σ τ) (γ t₀) q.2
    nlinarith
  refine ⟨by linarith, max L K, max_lt hL (hKc.trans_lt hc1),
    fun τ => if τ ≤ t₀ then γ τ else σ τ, by rw [concat_left hpt₀, hγp],
    by rw [concat_right ht₀q'.le hb, hσ1], (hγ.restrict le_rfl (by linarith)).concat hσc hb⟩

/-! ### Push-up -/

/-- **`p ≪_U q ≤_U r` gives `p ≪_U r`** (`rem:pushup`). The chronological curve is sped up to
reach `q` a time `η` early and the causal one slowed down to fill the gap: both slopes drop
below 1, and the graph moves by at most `η` in time, inside a tube of `U`. -/
theorem staticLt_of_staticLt_of_staticLe (hU : IsOpen U) (h₁ : staticLt U p q)
    (h₂ : staticLe U q r) : staticLt U p r := by
  rcases h₂.1.eq_or_lt with hqr | hqr
  · rw [← h₂.eq_of_fst_eq hqr]; exact h₁
  obtain ⟨hpq, L, hL, γ₁, hγ₁p, hγ₁q, hγ₁⟩ := h₁
  obtain ⟨-, γ₂, hγ₂q, hγ₂r, hγ₂⟩ := h₂
  have hL0 : 0 ≤ L := hγ₁.lip.nonneg hpq
  set G₁ := (fun τ => ((τ, γ₁ τ) : ℝ × X)) '' Icc p.1 q.1 with hG₁
  set G₂ := (fun τ => ((τ, γ₂ τ) : ℝ × X)) '' Icc q.1 r.1 with hG₂
  have hKU : G₁ ∪ G₂ ⊆ U :=
    union_subset (image_subset_iff.2 hγ₁.mem) (image_subset_iff.2 hγ₂.mem)
  obtain ⟨ρ, hρ, hthick⟩ :=
    (hγ₁.isCompact_graph.union hγ₂.isCompact_graph).exists_thickening_subset_open hU hKU
  have tube : ∀ (τ σ : ℝ) (y : X), (σ, y) ∈ G₁ ∪ G₂ → |τ - σ| < ρ → ((τ, y) : ℝ × X) ∈ U := by
    intro τ σ y hw hd
    refine hthick (mem_thickening_iff.2 ⟨(σ, y), hw, ?_⟩)
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_left (abs_nonneg _)]
    exact hd
  set η := min (ρ / 2) ((1 - L) * (q.1 - p.1) / 2) with hη
  have hgap : 0 < q.1 - p.1 := sub_pos.2 hpq
  have hηpos : 0 < η := lt_min (by linarith) (by
    have : 0 < 1 - L := by linarith
    positivity)
  have hηρ : η < ρ := (min_le_left _ _).trans_lt (by linarith)
  have hηL : η < (1 - L) * (q.1 - p.1) := (min_le_right _ _).trans_lt (by
    have : 0 < (1 - L) * (q.1 - p.1) := by
      have : 0 < 1 - L := by linarith
      positivity
    linarith)
  have hηt : η < q.1 - p.1 := hηL.trans_le (by nlinarith)
  set t' := q.1 - η with ht'
  have hpt' : 0 < t' - p.1 := by rw [ht']; linarith
  have ht'r : 0 < r.1 - t' := by rw [ht']; linarith
  set k₁ := (q.1 - p.1) / (t' - p.1) with hk₁
  set m₁ := p.1 - k₁ * p.1 with hm₁
  set k₂ := (r.1 - q.1) / (r.1 - t') with hk₂
  set m₂ := q.1 - k₂ * t' with hm₂
  have hk₁pos : 0 < k₁ := div_pos hgap hpt'
  have hk₂pos : 0 < k₂ := div_pos (sub_pos.2 hqr) ht'r
  have e₁ : k₁ * p.1 + m₁ = p.1 := by rw [hm₁]; ring
  have e₂ : k₁ * t' + m₁ = q.1 := by
    rw [hm₁, show k₁ * t' + (p.1 - k₁ * p.1) = p.1 + k₁ * (t' - p.1) by ring, hk₁,
      div_mul_cancel₀ _ hpt'.ne']; ring
  have e₃ : k₂ * t' + m₂ = q.1 := by rw [hm₂]; ring
  have e₄ : k₂ * r.1 + m₂ = r.1 := by
    rw [hm₂, show k₂ * r.1 + (q.1 - k₂ * t') = q.1 + k₂ * (r.1 - t') by ring, hk₂,
      div_mul_cancel₀ _ ht'r.ne']; ring
  have hk₁η : (k₁ - 1) * (t' - p.1) = η := by
    rw [sub_mul, hk₁, div_mul_cancel₀ _ hpt'.ne', ht']; ring
  have hk₂η : (1 - k₂) * (r.1 - t') = η := by
    rw [sub_mul, hk₂, div_mul_cancel₀ _ ht'r.ne', ht']; ring
  have hk₁1 : 1 ≤ k₁ := by nlinarith
  have hk₂1 : k₂ ≤ 1 := by nlinarith
  have hLk : L * k₁ < 1 := by
    rw [hk₁, mul_div_assoc', div_lt_one hpt', ht']; nlinarith
  have hk₂lt : 1 * k₂ < 1 := by
    rw [one_mul, hk₂, div_lt_one ht'r, ht']; linarith
  have lip₁ : LipOn (L * k₁) (fun τ => γ₁ (k₁ * τ + m₁)) p.1 t' :=
    LipOn.comp_affine hk₁pos (by rw [e₁, e₂]; exact hγ₁.lip)
  have lip₂ : LipOn (1 * k₂) (fun τ => γ₂ (k₂ * τ + m₂)) t' r.1 :=
    LipOn.comp_affine hk₂pos (by rw [e₃, e₄]; exact hγ₂.lip)
  have c₁ : StaticCurve (L * k₁) U (fun τ => γ₁ (k₁ * τ + m₁)) p.1 t' := by
    refine ⟨lip₁, fun τ hτ => ?_⟩
    have hσ : k₁ * τ + m₁ ∈ Icc p.1 q.1 := ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
    refine tube τ (k₁ * τ + m₁) _ (Or.inl ⟨_, hσ, rfl⟩) ?_
    have hd : k₁ * τ + m₁ - τ = (k₁ - 1) * (τ - p.1) := by rw [hm₁]; ring
    have h1 : 0 ≤ (k₁ - 1) * (τ - p.1) := mul_nonneg (by linarith) (by linarith [hτ.1])
    have h2 : (k₁ - 1) * (τ - p.1) ≤ (k₁ - 1) * (t' - p.1) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ.2]) (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have c₂ : StaticCurve (1 * k₂) U (fun τ => γ₂ (k₂ * τ + m₂)) t' r.1 := by
    refine ⟨lip₂, fun τ hτ => ?_⟩
    have hσ : k₂ * τ + m₂ ∈ Icc q.1 r.1 := ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
    refine tube τ (k₂ * τ + m₂) _ (Or.inr ⟨_, hσ, rfl⟩) ?_
    have hd : k₂ * τ + m₂ - τ = η - (1 - k₂) * (τ - t') := by rw [hm₂, ht']; ring
    have h1 : 0 ≤ (1 - k₂) * (τ - t') := mul_nonneg (by linarith) (by linarith [hτ.1])
    have h2 : (1 - k₂) * (τ - t') ≤ (1 - k₂) * (r.1 - t') :=
      mul_le_mul_of_nonneg_left (by linarith [hτ.2]) (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hb : (fun τ => γ₁ (k₁ * τ + m₁)) t' = (fun τ => γ₂ (k₂ * τ + m₂)) t' := by
    simp only; rw [e₂, e₃, hγ₁q, hγ₂q]
  refine ⟨hpq.trans hqr, max (L * k₁) (1 * k₂), max_lt hLk hk₂lt,
    fun τ => if τ ≤ t' then γ₁ (k₁ * τ + m₁) else γ₂ (k₂ * τ + m₂), ?_, ?_, c₁.concat c₂ hb⟩
  · show (if p.1 ≤ t' then _ else _) = _
    rw [if_pos (by linarith), e₁, hγ₁p]
  · show (if r.1 ≤ t' then _ else _) = _
    rw [if_neg (not_le.2 (by linarith)), e₄, hγ₂r]

/-- **`p ≤_U q ≪_U r` gives `p ≪_U r`**, by time reversal. -/
theorem staticLt_of_staticLe_of_staticLt (hU : IsOpen U) (h₁ : staticLe U p q)
    (h₂ : staticLt U q r) : staticLt U p r :=
  staticLt_flip_iff.1 (staticLt_of_staticLt_of_staticLe (hU.preimage continuous_flipT)
    h₂.flip h₁.flip)

/-! ### The causality -/

variable (X) in
/-- **The causality of the static spacetime `ℝ × X`** (`defi:causal_Ealpha`'s construction):
`x ≤_U y` (resp. `x ≪_U y`) iff there is a future causal (resp. chronological) curve from `x` to
`y` in `U`. -/
def staticCausality [GeodesicSpace X] : Causality (ℝ × X) where
  le U p q := staticLe (U : Set (ℝ × X)) p q
  lt U p q := staticLt (U : Set (ℝ × X)) p q
  le_mem_left h := h.mem_left
  le_mem_right h := h.mem_right
  lt_mem_left h := h.staticLe.mem_left
  lt_mem_right h := h.staticLe.mem_right
  le_refl hx := staticLe_refl hx
  le_trans h₁ h₂ := h₁.trans h₂
  lt_trans h₁ h₂ := h₁.trans h₂
  le_mono hVU _ _ h := h.mono hVU
  lt_mono hVU _ _ h := h.mono hVU
  le_of_lt h := h.staticLe
  isOpen_lt_right U x := isOpen_setOf_staticLt U.isOpen x
  isOpen_lt_left U x := by
    have : {y | staticLt (U : Set (ℝ × X)) y x} =
        flipT ⁻¹' {z | staticLt (flipT ⁻¹' (U : Set (ℝ × X))) (flipT x) z} := by
      ext y
      simp only [mem_setOf_eq, mem_preimage]
      exact staticLt_flip_iff.symm
    rw [this]
    exact (isOpen_setOf_staticLt (U.isOpen.preimage continuous_flipT) _).preimage
      continuous_flipT

namespace staticCausality

variable [GeodesicSpace X] {W N : Opens (ℝ × X)} {γ : ℝ → X} {a b : ℝ}

theorem le_iff : (staticCausality X).le W p q ↔ staticLe (W : Set (ℝ × X)) p q := Iff.rfl

theorem lt_iff : (staticCausality X).lt W p q ↔ staticLt (W : Set (ℝ × X)) p q := Iff.rfl

/-- **Globally, `x ≤ y ⟺ t − s ≥ d(x, y)`.** -/
theorem le_top_iff : (staticCausality X).le ⊤ p q ↔ dist p.2 q.2 ≤ q.1 - p.1 := by
  rw [le_iff, Opens.coe_top]; exact staticLe_univ_iff

/-- **Globally, `x ≪ y ⟺ t − s > d(x, y)`.** -/
theorem lt_top_iff : (staticCausality X).lt ⊤ p q ↔ dist p.2 q.2 < q.1 - p.1 := by
  rw [lt_iff, Opens.coe_top]; exact staticLt_univ_iff

theorem mem_Jplus_top : q ∈ (staticCausality X).Jplus ⊤ {p} ↔ dist p.2 q.2 ≤ q.1 - p.1 := by
  rw [Precausality.mem_Jplus_singleton]; exact le_top_iff

theorem mem_Jminus_top : q ∈ (staticCausality X).Jminus ⊤ {p} ↔ dist q.2 p.2 ≤ p.1 - q.1 := by
  rw [Precausality.mem_Jminus_singleton]; exact le_top_iff

theorem mem_Iplus_top : q ∈ (staticCausality X).Iplus ⊤ {p} ↔ dist p.2 q.2 < q.1 - p.1 := by
  rw [Precausality.mem_Iplus_singleton]; exact lt_top_iff

theorem mem_Iminus_top : q ∈ (staticCausality X).Iminus ⊤ {p} ↔ dist q.2 p.2 < p.1 - q.1 := by
  rw [Precausality.mem_Iminus_singleton]; exact lt_top_iff

/-- **Sanity.** The causality is not trivial: `(0, x) ≪ (1, x)` and `(0, x) ≰ (0, y)` for
`y ≠ x`. -/
theorem sanity (x y : X) (hxy : x ≠ y) :
    (staticCausality X).lt ⊤ (0, x) (1, x) ∧ ¬ (staticCausality X).le ⊤ (0, x) (0, y) := by
  rw [lt_top_iff, le_top_iff]
  simp only [dist_self, sub_self, sub_zero]
  exact ⟨one_pos, fun h => hxy (dist_le_zero.1 h)⟩

/-- **Causal**: `≤_M` is antisymmetric. -/
theorem isCausal : (staticCausality X).IsCausal := by
  intro p q h₁ h₂
  rw [le_top_iff] at h₁ h₂
  have h1 : p.1 = q.1 := by
    linarith [dist_nonneg (x := p.2) (y := q.2), dist_nonneg (x := q.2) (y := p.2)]
  rw [h1, sub_self] at h₁
  exact Prod.ext h1 (dist_le_zero.1 h₁)

theorem isClosed_Jplus_top (p : ℝ × X) : IsClosed ((staticCausality X).Jplus ⊤ {p}) := by
  have : (staticCausality X).Jplus ⊤ {p} = {q | dist p.2 q.2 ≤ q.1 - p.1} := by
    ext q; exact mem_Jplus_top
  rw [this]
  exact isClosed_le (continuous_const.dist continuous_snd) (continuous_fst.sub continuous_const)

theorem isClosed_Jminus_top (p : ℝ × X) : IsClosed ((staticCausality X).Jminus ⊤ {p}) := by
  have : (staticCausality X).Jminus ⊤ {p} = {q | dist q.2 p.2 ≤ p.1 - q.1} := by
    ext q; exact mem_Jminus_top
  rw [this]
  exact isClosed_le (continuous_snd.dist continuous_const) (continuous_const.sub continuous_fst)

/-! ### The graphs are curves of `Causal.Curves` -/

/-- The graph of a 1-Lipschitz map in `W` is a future causal curve of `Causal.Curves`. -/
theorem causalCurveOn_graph (hγ : StaticCurve 1 (W : Set (ℝ × X)) γ a b) :
    (staticCausality X).CausalCurveOn W (fun τ => (τ, γ τ)) a b := by
  refine ⟨fun τ hτ => hγ.mem τ hτ, fun t ht N _ htN => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 N.isOpen _ htN
  refine ⟨t - ρ, t + ρ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
  refine ⟨h2.le, γ, rfl, rfl, hγ.lip.restrict hs.1 hs'.2, fun σ hσ => hball ?_⟩
  have hσ' : σ ∈ Icc a b := ⟨hs.1.trans hσ.1, hσ.2.trans hs'.2⟩
  rw [mem_ball]
  refine (hγ.lip.dist_graph_le le_rfl hσ' ht).trans_lt ?_
  rw [abs_lt]; constructor <;> linarith [hσ.1, hσ.2]

/-- The graph of a `L`-Lipschitz map, `L < 1`, in `W` is a future chronal curve. -/
theorem chronalCurveOn_graph {L : ℝ} (hL : L < 1) (hγ : StaticCurve L (W : Set (ℝ × X)) γ a b) :
    (staticCausality X).ChronalCurveOn W (fun τ => (τ, γ τ)) a b := by
  refine ⟨fun τ hτ => hγ.mem τ hτ, fun t ht N _ htN => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 N.isOpen _ htN
  refine ⟨t - ρ, t + ρ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
  refine ⟨h2, L, hL, γ, rfl, rfl, hγ.lip.restrict hs.1 hs'.2, fun σ hσ => hball ?_⟩
  have hσ' : σ ∈ Icc a b := ⟨hs.1.trans hσ.1, hσ.2.trans hs'.2⟩
  rw [mem_ball]
  refine (hγ.lip.dist_graph_le hL.le hσ' ht).trans_lt ?_
  rw [abs_lt]; constructor <;> linarith [hσ.1, hσ.2]

omit [GeodesicSpace X] in
/-- The graph over `[p.1, q.1]`, run over `[0, 1]`. -/
theorem curveOn_graph_unit {r : Opens (ℝ × X) → ℝ × X → ℝ × X → Prop} (hpq : p.1 < q.1)
    (hγp : γ p.1 = p.2) (hγq : γ q.1 = q.2) (hc : CurveOn r W (fun τ => (τ, γ τ)) p.1 q.1) :
    ∃ c : ℝ → ℝ × X, CurveOn r W c 0 1 ∧ c 0 = p ∧ c 1 = q := by
  have hk : 0 < q.1 - p.1 := sub_pos.2 hpq
  have h := CurveOn.comp_affine (k := q.1 - p.1) (m := p.1) (a' := 0) (b' := 1) hk
    (by rw [show (q.1 - p.1) * 0 + p.1 = p.1 by ring, show (q.1 - p.1) * 1 + p.1 = q.1 by ring]
        exact hc)
  refine ⟨_, h, ?_, ?_⟩
  · simp only [mul_zero, zero_add]; rw [hγp]
  · simp only [mul_one, sub_add_cancel]; rw [hγq]

/-- **Causally arc-connected** (`def:causal_arc_connectedness`): two points are related in an
open set iff a causal (resp. chronal) curve of `Causal.Curves` joins them in it. -/
theorem causallyArcConnected : (staticCausality X).CausallyArcConnected := by
  intro U _ p q
  refine ⟨⟨fun h => ?_, fun ⟨c, hc, h0, h1⟩ => h0 ▸ h1 ▸ hc.le_of_le le_rfl zero_le_one le_rfl⟩,
    ⟨fun h => ?_, fun ⟨c, hc, h0, h1⟩ => h0 ▸ h1 ▸ hc.lt_of_lt le_rfl zero_lt_one le_rfl⟩⟩
  · rcases h.1.eq_or_lt with he | hlt
    · have hpq : p = q := h.eq_of_fst_eq he
      subst hpq
      exact ⟨fun _ => p, Causality.causalCurveOn_const h.mem_left, rfl, rfl⟩
    · obtain ⟨-, γ, hγp, hγq, hγ⟩ := h
      exact curveOn_graph_unit hlt hγp hγq (causalCurveOn_graph hγ)
  · obtain ⟨hlt, L, hL, γ, hγp, hγq, hγ⟩ := h
    exact curveOn_graph_unit hlt hγp hγq (chronalCurveOn_graph hL hγ)

/-- **Absolutely minimal**, by `cor:causalement_connexe_minimal`. -/
theorem absolutelyMinimal : (staticCausality X).AbsolutelyMinimal :=
  Causality.CausallyArcConnected.absolutelyMinimal causallyArcConnected

/-- **Push-up in every open set** (`rem:pushup`, `defi:pushup`). -/
theorem pushUp : (staticCausality X).PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h₁ h₂ => staticLt_of_staticLt_of_staticLe U.isOpen h₁ h₂,
    fun h₁ h₂ => staticLt_of_staticLe_of_staticLt U.isOpen h₁ h₂⟩

/-- Push-up for every open subset seen as a spacetime. -/
theorem pushUpOn (W : Opens (ℝ × X)) : (staticCausality X).PushUpOn W := fun U _ _ _ _ =>
  ⟨fun h₁ h₂ => staticLt_of_staticLt_of_staticLe U.isOpen h₁ h₂,
    fun h₁ h₂ => staticLt_of_staticLe_of_staticLt U.isOpen h₁ h₂⟩

/-! ### Tarentin, strongly tarentin, strongly causal, globally hyperbolic -/

/-- Every point is strongly tarentin in the future: `Z^+ = M`. -/
theorem mem_Zplus (p : ℝ × X) : p ∈ (staticCausality X).Zplus := by
  intro N hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨(p.1 + ε / 2, p.2), ?_, hball ?_⟩
  · rw [mem_Iplus_top]; simp only [dist_self]; linarith
  · rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [add_sub_cancel_left]
    rw [abs_of_pos (by linarith), max_eq_left (by linarith)]; linarith

/-- Every point is strongly tarentin in the past: `Z^- = M`. -/
theorem mem_Zminus (p : ℝ × X) : p ∈ (staticCausality X).Zminus := by
  intro N hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨(p.1 - ε / 2, p.2), ?_, hball ?_⟩
  · rw [mem_Iminus_top]; simp only [dist_self]; linarith
  · rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [sub_sub_cancel_left]
    rw [abs_neg, abs_of_pos (by linarith), max_eq_left (by linarith)]; linarith

theorem Zplus_eq : (staticCausality X).Zplus = univ := eq_univ_of_forall mem_Zplus

theorem Zminus_eq : (staticCausality X).Zminus = univ := eq_univ_of_forall mem_Zminus

/-- The full diamond between `(t − ε, x)` and `(t + ε, x)` lies in the closed ball of radius `ε`
and contains the open ball of radius `ε/2`. -/
theorem diamond_vertical (p : ℝ × X) {ε : ℝ} :
    ball p (ε / 2) ⊆ (staticCausality X).diamond ⊤ (p.1 - ε, p.2) (p.1 + ε, p.2) ∧
      (staticCausality X).diamond ⊤ (p.1 - ε, p.2) (p.1 + ε, p.2) ⊆ closedBall p ε := by
  constructor
  · intro z hz
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hz
    rw [Causality.mem_diamond, le_top_iff, le_top_iff]
    simp only
    constructor
    · rw [dist_comm]; linarith
    · linarith
  · intro z hz
    rw [Causality.mem_diamond, le_top_iff, le_top_iff] at hz
    simp only at hz
    rw [mem_closedBall, Prod.dist_eq, Real.dist_eq]
    refine max_le (abs_le.2 ⟨?_, ?_⟩) ?_
    · linarith [dist_nonneg (x := p.2) (y := z.2)]
    · linarith [dist_nonneg (x := z.2) (y := p.2)]
    · rw [dist_comm] at hz; linarith [hz.1, hz.2]

/-- **Tarentin** (`def:tarentin_spacetime`). -/
theorem tarentin : (staticCausality X).Tarentin := by
  intro x N hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨(x.1 - ε / 2, x.2), hball ?_, (x.1 + ε / 2, x.2), hball ?_, ?_⟩
  · rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [sub_sub_cancel_left]
    rw [abs_neg, abs_of_pos (by linarith), max_eq_left (by linarith)]; linarith
  · rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [add_sub_cancel_left]
    rw [abs_of_pos (by linarith), max_eq_left (by linarith)]; linarith
  · exact interior_maximal (diamond_vertical x).1 isOpen_ball (mem_ball_self (by linarith))

/-- **Strongly causal** (`def:strongly_causal_spacetime`): the vertical diamonds are causally
convex neighbourhoods inside any given neighbourhood. -/
theorem stronglyCausal : (staticCausality X).StronglyCausal := by
  intro p N hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨_, Filter.mem_of_superset (ball_mem_nhds p (by linarith : 0 < ε / 2 / 2))
    (diamond_vertical (ε := ε / 2) p).1, fun z hz => hball ?_, Causality.causallyConvexIn_diamond⟩
  have := (diamond_vertical (ε := ε / 2) p).2 hz
  rw [mem_closedBall] at this
  rw [mem_ball]; linarith

/-- **Globally hyperbolic** (`def:globally_hyperbolic`) when `X` is proper: the diamond `J(p, q)`
is closed and contained in the closed ball of radius `q.1 − p.1` around `p`. -/
theorem globallyHyperbolic [ProperSpace X] : (staticCausality X).GloballyHyperbolic := by
  refine ⟨isCausal, fun p q => ?_⟩
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_Jminus_top q).inter (isClosed_Jplus_top p))
    (isBounded_closedBall (x := p) (r := q.1 - p.1) |>.subset fun z hz => ?_)
  rw [Causality.mem_diamond, le_top_iff, le_top_iff] at hz
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, dist_comm z.2]
  refine max_le (abs_le.2 ⟨?_, ?_⟩) ?_
  · linarith [dist_nonneg (x := p.2) (y := z.2), dist_nonneg (x := z.2) (y := q.2), hz.1, hz.2]
  · linarith [dist_nonneg (x := z.2) (y := q.2), dist_nonneg (x := p.2) (y := z.2), hz.1, hz.2]
  · linarith [dist_nonneg (x := z.2) (y := q.2), hz.1, hz.2]

/-! ### `lem:IJ_calc`, `lem:densite_modele` -/

/-- `lem:IJ_calc` for the static spacetime: `Int J^+(p) ∩ Z^- = I^+(p)`, the paper's proof
through `lem:J_int` (absolute minimality and push-up). -/
theorem interior_Jplus_inter_Zminus (p : ℝ × X) :
    interior ((staticCausality X).Jplus ⊤ {p}) ∩ (staticCausality X).Zminus =
      (staticCausality X).Iplus ⊤ {p} :=
  Causality.interior_Jplus_inter_Zminus absolutelyMinimal pushUp p

theorem interior_Jminus_inter_Zplus (p : ℝ × X) :
    interior ((staticCausality X).Jminus ⊤ {p}) ∩ (staticCausality X).Zplus =
      (staticCausality X).Iminus ⊤ {p} :=
  Causality.interior_Jminus_inter_Zplus absolutelyMinimal pushUp p

/-- `Z^∓ = M`, so `lem:IJ_calc` reads `Int J^±(p) = I^±(p)`. -/
theorem interior_Jplus (p : ℝ × X) :
    interior ((staticCausality X).Jplus ⊤ {p}) = (staticCausality X).Iplus ⊤ {p} := by
  rw [← interior_Jplus_inter_Zminus, Zminus_eq, inter_univ]

theorem interior_Jminus (p : ℝ × X) :
    interior ((staticCausality X).Jminus ⊤ {p}) = (staticCausality X).Iminus ⊤ {p} := by
  rw [← interior_Jminus_inter_Zplus, Zplus_eq, inter_univ]

/-- `lem:densite_modele` (a): `J^+(p) = closure(I^+(p))`. -/
theorem closure_Iplus (p : ℝ × X) :
    closure ((staticCausality X).Iplus ⊤ {p}) = (staticCausality X).Jplus ⊤ {p} := by
  refine Subset.antisymm (closure_minimal Causality.Iplus_subset_Jplus (isClosed_Jplus_top p))
    fun q hq => Metric.mem_closure_iff.2 fun ε hε => ⟨(q.1 + ε / 2, q.2), ?_, ?_⟩
  · rw [mem_Jplus_top] at hq; rw [mem_Iplus_top]; simp only; linarith
  · rw [Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [sub_add_cancel_left]
    rw [abs_neg, abs_of_pos (by linarith), max_eq_left (by linarith)]; linarith

/-- `lem:densite_modele` (b): `J^-(p) = closure(I^-(p))`. -/
theorem closure_Iminus (p : ℝ × X) :
    closure ((staticCausality X).Iminus ⊤ {p}) = (staticCausality X).Jminus ⊤ {p} := by
  refine Subset.antisymm (closure_minimal Causality.Iminus_subset_Jminus (isClosed_Jminus_top p))
    fun q hq => Metric.mem_closure_iff.2 fun ε hε => ⟨(q.1 - ε / 2, q.2), ?_, ?_⟩
  · rw [mem_Jminus_top] at hq; rw [mem_Iminus_top]; simp only; linarith
  · rw [Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [sub_sub_cancel]
    rw [abs_of_pos (by linarith), max_eq_left (by linarith)]; linarith

/-- `lem:densite_modele`, "the same holds in any causally convex open subset": for `V` open and
causally convex and `p ∈ V`, `J^+_V(p) = closure(I^+_V(p)) ∩ V`, the closure in `V`. -/
theorem Jplus_eq_closure_Iplus_of_causallyConvexIn {V : Opens (ℝ × X)}
    (hV : (staticCausality X).CausallyConvexIn (V : Set (ℝ × X)) ⊤) {p : ℝ × X} (hp : p ∈ V) :
    (staticCausality X).Jplus V {p} = closure ((staticCausality X).Iplus V {p}) ∩ V := by
  obtain ⟨hJ, hI, -⟩ := Causality.restriction_convexe_future causallyArcConnected hV
    (singleton_subset_iff.2 hp)
  rw [hJ, hI, ← closure_Iplus]
  refine Subset.antisymm (fun x hx => ⟨?_, hx.2⟩) (fun x hx => ⟨closure_mono inter_subset_left hx.1, hx.2⟩)
  have := V.isOpen.inter_closure ⟨hx.2, hx.1⟩
  rwa [inter_comm] at this

/-- `lem:densite_modele` in a causally convex open subset, in the past. -/
theorem Jminus_eq_closure_Iminus_of_causallyConvexIn {V : Opens (ℝ × X)}
    (hV : (staticCausality X).CausallyConvexIn (V : Set (ℝ × X)) ⊤) {p : ℝ × X} (hp : p ∈ V) :
    (staticCausality X).Jminus V {p} = closure ((staticCausality X).Iminus V {p}) ∩ V := by
  obtain ⟨hJ, hI, -⟩ := Causality.restriction_convexe_past causallyArcConnected hV
    (singleton_subset_iff.2 hp)
  rw [hJ, hI, ← closure_Iminus]
  refine Subset.antisymm (fun x hx => ⟨?_, hx.2⟩) (fun x hx => ⟨closure_mono inter_subset_left hx.1, hx.2⟩)
  have := V.isOpen.inter_closure ⟨hx.2, hx.1⟩
  rwa [inter_comm] at this

end staticCausality

/-! ### Inextensible curves have no limit at their ends -/

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {c : ℝ → M}

/-- **An inextensible curve over `ℝ` has no limit at its past end**, under the hypotheses of
`extensible_of_tendsto` (`ETT.tex:1291`): the curve, run over `]0, +∞[` by `log`, would extend by
adjoining the limit and prepending. -/
theorem Inextensible.not_tendsto_atBot (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hc : C.Inextensible ⊤ univ c) (P : M) :
    ¬ Tendsto c atBot (𝓝 P) := by
  intro hlim
  apply hc.2
  have hd : C.CausalCurveIn ⊤ (Ioi 0) (c ∘ Real.log) :=
    hc.1.comp ⟨1, mem_Ioi.2 one_pos⟩ ordConnected_Ioi Real.strictMonoOn_log
      (Real.continuousOn_log.mono fun x hx => ne_of_gt hx) fun _ _ => trivial
  have hins : (insert (0 : ℝ) (Ioi 0)).OrdConnected := by
    have : insert (0 : ℝ) (Ioi 0) = Ici 0 := by
      ext x
      simp only [mem_insert_iff, mem_Ioi, mem_Ici]
      constructor
      · rintro (rfl | h)
        exacts [le_rfl, h.le]
      · intro h
        rcases h.eq_or_lt with h | h
        exacts [Or.inl h.symm, Or.inr h]
    rw [this]; exact ordConnected_Ici
  have hext := extensible_of_tendsto hJ hSC hC hcaus hd (a := 0) (fun _ ht => ht) hins
    (hlim.comp Real.tendsto_log_nhdsGT_zero) (hJm P)
  refine hext.of_comp (ψ := Real.exp) (Real.exp_strictMono.strictMonoOn univ)
    (fun t _ => Real.exp_pos t) (fun y hy => ⟨Real.log y, trivial, Real.exp_log hy⟩)
    (fun t _ => by simp)

/-- **An inextensible curve over `ℝ` has no limit at its future end**, by time reversal. -/
theorem Inextensible.not_tendsto_atTop (hJ : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hc : C.Inextensible ⊤ univ c) (P : M) :
    ¬ Tendsto c atTop (𝓝 P) := by
  intro hlim
  have hc' := hc.dual_reverse
  rw [Set.neg_univ] at hc'
  exact Inextensible.not_tendsto_atBot (C := C.dual) hJ (dual_stronglyCausal.2 hSC)
    (dual_causallyArcConnectedOn.2 hC) (dual_isCausal.2 hcaus) hJp hc' P
    (hlim.comp tendsto_neg_atBot_atTop)

/-- A causal curve over `ℝ` along which a function non-decreasing for `≤_M` is unbounded above and
below is inextensible: a new value would come after, or before, the whole curve. -/
theorem inextensible_of_unbounded {f : M → ℝ} (hf : ∀ x y, C.le ⊤ x y → f x ≤ f y)
    (hc : C.CausalCurveIn ⊤ univ c) (htop : ∀ b, ∃ s, b < f (c s))
    (hbot : ∀ b, ∃ s, f (c s) < b) : C.Inextensible ⊤ univ c := by
  refine ⟨hc, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, -, hφmaps, hφoc, hφeq⟩, ⟨t', ht', hgrow⟩⟩
  by_cases h1 : ∃ s, t' ≤ φ s
  · by_cases h2 : ∃ s, φ s ≤ t'
    · obtain ⟨s₁, hs₁⟩ := h1
      obtain ⟨s₂, hs₂⟩ := h2
      obtain ⟨s, -, hs⟩ := hφoc.out (mem_image_of_mem φ (mem_univ s₂))
        (mem_image_of_mem φ (mem_univ s₁)) ⟨hs₂, hs₁⟩
      exact hgrow s trivial (by rw [← hs, hφeq s trivial])
    · simp only [not_exists, not_le] at h2
      obtain ⟨s, hs⟩ := hbot (f (c' t'))
      have := hf _ _ (hcurve.le_of_le ht' (hφmaps (mem_univ s)) (h2 s).le)
      rw [hφeq s trivial] at this
      linarith
  · simp only [not_exists, not_le] at h1
    obtain ⟨s, hs⟩ := htop (f (c' t'))
    have := hf _ _ (hcurve.le_of_le (hφmaps (mem_univ s)) ht' (h1 s).le)
    rw [hφeq s trivial] at this
    linarith

end Causality

namespace staticCausality

variable [GeodesicSpace X] {c : ℝ → ℝ × X}

theorem Jplus_ne_singleton (p : ℝ × X) : (staticCausality X).Jplus ⊤ {p} ≠ {p} := by
  intro h
  have : ((p.1 + 1, p.2) : ℝ × X) ∈ (staticCausality X).Jplus ⊤ {p} := by
    rw [mem_Jplus_top]; simp
  rw [h, mem_singleton_iff, Prod.ext_iff] at this
  linarith [this.1]

theorem Jminus_ne_singleton (p : ℝ × X) : (staticCausality X).Jminus ⊤ {p} ≠ {p} := by
  intro h
  have : ((p.1 - 1, p.2) : ℝ × X) ∈ (staticCausality X).Jminus ⊤ {p} := by
    rw [mem_Jminus_top]; simp
  rw [h, mem_singleton_iff, Prod.ext_iff] at this
  linarith [this.1]

/-- Along a causal curve over `ℝ`, the spatial displacement is bounded by the elapsed time. -/
theorem CausalCurveIn.dist_le (hc : (staticCausality X).CausalCurveIn ⊤ univ c) {s s' : ℝ}
    (h : s ≤ s') : dist (c s).2 (c s').2 ≤ (c s').1 - (c s).1 :=
  le_top_iff.1 (hc.le_of_le trivial trivial h)

theorem CausalCurveIn.monotone_time (hc : (staticCausality X).CausalCurveIn ⊤ univ c) :
    Monotone fun s => (c s).1 := fun s s' h => by
  have := CausalCurveIn.dist_le hc h
  show (c s).1 ≤ (c s').1
  linarith [dist_nonneg (x := (c s).2) (y := (c s').2)]

/-- **Witness** (kb/0012): the static spacetime satisfies every hypothesis of
`Inextensible.not_tendsto_atBot` and `Inextensible.not_tendsto_atTop`. -/
theorem not_tendsto_hypotheses :
    (∀ x, IsClosed ((staticCausality X).Jminus ⊤ {x})) ∧
      (∀ x, IsClosed ((staticCausality X).Jplus ⊤ {x})) ∧ (staticCausality X).StronglyCausal ∧
      (staticCausality X).CausallyArcConnected ∧ (staticCausality X).IsCausal ∧
      (∀ p, (staticCausality X).Jminus ⊤ {p} ≠ {p}) ∧
      ∀ p, (staticCausality X).Jplus ⊤ {p} ≠ {p} :=
  ⟨isClosed_Jminus_top, isClosed_Jplus_top, stronglyCausal, causallyArcConnected, isCausal,
    Jminus_ne_singleton, Jplus_ne_singleton⟩

/-- **Along an inextensible causal curve over `ℝ`, time tends to `+∞`** when `X` is complete:
otherwise time converges, the spatial part is Cauchy, and the curve has a limit. -/
theorem tendsto_time_atTop [CompleteSpace X] (hc : (staticCausality X).Inextensible ⊤ univ c) :
    Tendsto (fun s => (c s).1) atTop atTop := by
  have hmono := CausalCurveIn.monotone_time hc.1
  by_cases h : ∀ b, ∃ a, b ≤ (c a).1
  · exact tendsto_atTop_atTop_of_monotone hmono h
  exfalso
  simp only [not_forall, not_exists, not_le] at h
  obtain ⟨b, hb⟩ := h
  have hbdd : BddAbove (range fun s => (c s).1) := ⟨b, by rintro _ ⟨a, rfl⟩; exact (hb a).le⟩
  have hf := tendsto_atTop_ciSup hmono hbdd
  have hcauchy : CauchySeq fun s => (c s).2 := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_lt_of_lt_ciSup (f := fun s => (c s).1)
      (show (⨆ s, (c s).1) - ε < ⨆ s, (c s).1 by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := CausalCurveIn.dist_le hc.1 hn
    have h2 : (c n).1 ≤ ⨆ s, (c s).1 := le_ciSup hbdd n
    rw [dist_comm]
    linarith
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact Causality.Inextensible.not_tendsto_atTop isClosed_Jplus_top stronglyCausal
    causallyArcConnected isCausal Jplus_ne_singleton hc _ (hf.prodMk_nhds hy)

/-- **Along an inextensible causal curve over `ℝ`, time tends to `−∞`** when `X` is complete. -/
theorem tendsto_time_atBot [CompleteSpace X] (hc : (staticCausality X).Inextensible ⊤ univ c) :
    Tendsto (fun s => (c s).1) atBot atBot := by
  have hmono := CausalCurveIn.monotone_time hc.1
  by_cases h : ∀ b, ∃ a, (c a).1 ≤ b
  · exact tendsto_atBot_atBot_of_monotone hmono h
  exfalso
  simp only [not_forall, not_exists, not_le] at h
  obtain ⟨b, hb⟩ := h
  have hanti : Antitone fun s => (c (-s)).1 := fun _ _ h => hmono (neg_le_neg h)
  have hbdd : BddBelow (range fun s => (c (-s)).1) := ⟨b, by rintro _ ⟨a, rfl⟩; exact (hb _).le⟩
  have hf := tendsto_atTop_ciInf hanti hbdd
  have hcauchy : CauchySeq fun s => (c (-s)).2 := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_lt_of_ciInf_lt (f := fun s => (c (-s)).1)
      (show (⨅ s, (c (-s)).1) < (⨅ s, (c (-s)).1) + ε by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := CausalCurveIn.dist_le hc.1 (neg_le_neg hn)
    have h2 : ⨅ s, (c (-s)).1 ≤ (c (-n)).1 := ciInf_le hbdd n
    linarith
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : Tendsto c atBot (𝓝 ((⨅ s, (c (-s)).1), y)) := by
    have := (hf.prodMk_nhds hy).comp tendsto_neg_atBot_atTop
    refine this.congr fun s => ?_
    simp
  exact Causality.Inextensible.not_tendsto_atBot isClosed_Jminus_top stronglyCausal
    causallyArcConnected isCausal Jminus_ne_singleton hc _ hlim

/-! ### `K^± = I^±`, and the two sets an admissible measure must see -/

/-- `K^-(A) = I^-(A)` for every `A`: push-up and `Z^- = M` (`PushUp.Kminus_eq_Iminus`). -/
theorem Kminus_eq_Iminus (A : Set (ℝ × X)) :
    (staticCausality X).Kminus ⊤ A = (staticCausality X).Iminus ⊤ A := by
  rw [Causality.Kminus_eq_biUnion, Precausality.Iminus_eq_biUnion]
  refine iUnion₂_congr fun p _ => ?_
  exact Causality.PushUp.Kminus_eq_Iminus pushUp (mem_Zminus p)

/-- `K^+(A) = I^+(A)` for every `A`. -/
theorem Kplus_eq_Iplus (A : Set (ℝ × X)) :
    (staticCausality X).Kplus ⊤ A = (staticCausality X).Iplus ⊤ A := by
  rw [Causality.Kplus_eq_biUnion, Precausality.Iplus_eq_biUnion]
  refine iUnion₂_congr fun p _ => ?_
  exact Causality.PushUp.Kplus_eq_Iplus pushUp (mem_Zplus p)

/-- `J^-(A) \ K^-(A)` lies in the frontier of the open past set `I^-(A)`: property 4. of
`defi:mesure_dieckmann` asks only that an admissible measure not charge these frontiers. -/
theorem Jminus_diff_Kminus_subset_frontier (A : Set (ℝ × X)) :
    (staticCausality X).Jminus ⊤ A \ (staticCausality X).Kminus ⊤ A ⊆
      frontier ((staticCausality X).Iminus ⊤ A) := by
  rintro x ⟨⟨a, ha, hxa⟩, hxK⟩
  rw [Kminus_eq_Iminus] at hxK
  refine ⟨?_, by rwa [Causality.isOpen_Iminus.interior_eq]⟩
  have : x ∈ closure ((staticCausality X).Iminus ⊤ {a}) := by
    rw [closure_Iminus]; simpa using hxa
  exact closure_mono (Precausality.Iminus_mono (singleton_subset_iff.2 ha)) this

theorem Jplus_diff_Kplus_subset_frontier (A : Set (ℝ × X)) :
    (staticCausality X).Jplus ⊤ A \ (staticCausality X).Kplus ⊤ A ⊆
      frontier ((staticCausality X).Iplus ⊤ A) := by
  rintro x ⟨⟨a, ha, hxa⟩, hxK⟩
  rw [Kplus_eq_Iplus] at hxK
  refine ⟨?_, by rwa [Causality.isOpen_Iplus.interior_eq]⟩
  have : x ∈ closure ((staticCausality X).Iplus ⊤ {a}) := by
    rw [closure_Iplus]; simpa using hxa
  exact closure_mono (Precausality.Iplus_mono (singleton_subset_iff.2 ha)) this

/-- For `p ≤ q`, `p ≠ q`, the set `J^-(q) \ J^-(p)` of property 3. contains a non-empty open
set. -/
theorem exists_isOpen_subset_Jminus_diff {p q : ℝ × X} (hpq : (staticCausality X).le ⊤ p q)
    (hne : p ≠ q) : ∃ O : Set (ℝ × X), IsOpen O ∧ O.Nonempty ∧
      O ⊆ (staticCausality X).Jminus ⊤ {q} \ (staticCausality X).Jminus ⊤ {p} := by
  have hq : q ∉ (staticCausality X).Jminus ⊤ {p} := fun h =>
    hne (isCausal hpq (by simpa using h))
  have hcl : q ∈ closure ((staticCausality X).Iminus ⊤ {q}) := by
    rw [closure_Iminus]; simpa using (staticCausality X).le_refl (U := ⊤) trivial
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (isClosed_Jminus_top p).isOpen_compl hq
  exact ⟨_, Causality.isOpen_Iminus.inter (isClosed_Jminus_top p).isOpen_compl, ⟨z, hz2, hz1⟩,
    fun w hw => ⟨Causality.Iminus_subset_Jminus hw.1, hw.2⟩⟩

/-- For `p ≤ q`, `p ≠ q`, the set `J^+(p) \ J^+(q)` contains a non-empty open set. -/
theorem exists_isOpen_subset_Jplus_diff {p q : ℝ × X} (hpq : (staticCausality X).le ⊤ p q)
    (hne : p ≠ q) : ∃ O : Set (ℝ × X), IsOpen O ∧ O.Nonempty ∧
      O ⊆ (staticCausality X).Jplus ⊤ {p} \ (staticCausality X).Jplus ⊤ {q} := by
  have hp : p ∉ (staticCausality X).Jplus ⊤ {q} := fun h =>
    hne (isCausal hpq (by simpa using h))
  have hcl : p ∈ closure ((staticCausality X).Iplus ⊤ {p}) := by
    rw [closure_Iplus]; simpa using (staticCausality X).le_refl (U := ⊤) trivial
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (isClosed_Jplus_top q).isOpen_compl hp
  exact ⟨_, Causality.isOpen_Iplus.inter (isClosed_Jplus_top q).isOpen_compl, ⟨z, hz2, hz1⟩,
    fun w hw => ⟨Causality.Iplus_subset_Jplus hw.1, hw.2⟩⟩

/-! ### Time functions of the form `t − g(x)` -/

/-- **`t − g(x)` is a time function** (`defi:fonction_temps`, DEC-10: a strong morphism to the
timelike line) for every 1-Lipschitz `g : X → ℝ`. -/
theorem isTimeFunction_sub (g : X → ℝ) (hg : ∀ x y, |g x - g y| ≤ dist x y) :
    (staticCausality X).IsTimeFunction fun p => p.1 - g p.2 := by
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, NNReal.coe_one, one_mul]; exact hg x y).continuous
  have hdiff : ∀ x y : ℝ × X, (staticCausality X).le ⊤ x y →
      x.1 - g x.2 ≤ y.1 - g y.2 := fun x y h => by
    have h1 := le_top_iff.1 h
    have h2 := hg y.2 x.2
    rw [dist_comm] at h2
    linarith [le_abs_self (g y.2 - g x.2)]
  -- the image of the curve is an interval in `U`
  have hIcc : ∀ (U : Opens ℝ) (V : Opens (ℝ × X)),
      (V : Set (ℝ × X)) = (fun p : ℝ × X => p.1 - g p.2) ⁻¹' U → ∀ {L : ℝ} {γ : ℝ → X}
      {x y : ℝ × X}, x.1 ≤ y.1 → γ x.1 = x.2 → γ y.1 = y.2 → StaticCurve L V γ x.1 y.1 →
      Icc (x.1 - g x.2) (y.1 - g y.2) ⊆ U := by
    intro U V hV L γ x y hxy hγx hγy hγ
    have hcont : ContinuousOn (fun τ => τ - g (γ τ)) (Icc x.1 y.1) :=
      continuousOn_id.sub (hgc.comp_continuousOn hγ.lip.continuousOn)
    have := intermediate_value_Icc hxy hcont
    simp only [hγx, hγy] at this
    refine this.trans ?_
    rintro _ ⟨τ, hτ, rfl⟩
    have := hγ.mem τ hτ
    rw [hV] at this
    exact this
  refine ⟨continuous_fst.sub (hgc.comp continuous_snd), ?_, ?_, ?_⟩
  · intro O hO
    rw [Metric.isOpen_iff]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO z hz
    refine ⟨ε, hε, fun w hw => ⟨(z.1 + (w - (z.1 - g z.2)), z.2), hball ?_, by
      show z.1 + (w - (z.1 - g z.2)) - g z.2 = w; ring⟩⟩
    rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    rw [mem_ball, Real.dist_eq] at hw
    simp only [add_sub_cancel_left]
    rw [max_eq_left (abs_nonneg _)]; exact hw
  · intro U V hV x y hxy
    obtain ⟨h1, γ, hγx, hγy, hγ⟩ := hxy
    exact ⟨hdiff x y ⟨h1, γ, hγx, hγy, hγ.mono_set (subset_univ _)⟩,
      hIcc U V hV h1 hγx hγy hγ⟩
  · intro U V hV x y hxy
    have hlt := hxy.dist_lt
    obtain ⟨h1, L, hL, γ, hγx, hγy, hγ⟩ := hxy
    refine ⟨?_, hIcc U V hV h1.le hγx hγy hγ⟩
    have h2 := hg y.2 x.2
    rw [dist_comm] at h2
    linarith [le_abs_self (g y.2 - g x.2)]

/-- **`t − g(x)` is a Cauchy time function** (`def:cauchy_time_function`) when `X` is complete
and `g` is 1-Lipschitz and bounded. -/
theorem isCauchyTimeFunction_sub [CompleteSpace X] (g : X → ℝ)
    (hg : ∀ x y, |g x - g y| ≤ dist x y) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    (staticCausality X).IsCauchyTimeFunction fun p => p.1 - g p.2 := by
  refine ⟨isTimeFunction_sub g hg, fun c hc => ⟨?_, ?_⟩⟩
  · refine tendsto_atBot_mono (fun s => ?_) (tendsto_atBot_add_const_right _ B (tendsto_time_atBot hc))
    simp only [Function.comp]
    linarith [neg_abs_le (g (c s).2), hB (c s).2]
  · refine tendsto_atTop_mono (fun s => ?_) (tendsto_atTop_add_const_right _ (-B) (tendsto_time_atTop hc))
    simp only [Function.comp]
    linarith [le_abs_self (g (c s).2), hB (c s).2]

/-- **Sanity.** The time coordinate is a Cauchy time function. -/
theorem isCauchyTimeFunction_fst [CompleteSpace X] :
    (staticCausality X).IsCauchyTimeFunction fun p => p.1 := by
  have := isCauchyTimeFunction_sub (X := X) (fun _ => 0) (fun _ _ => by simp) (B := 0)
    (fun _ => by simp)
  simpa using this

/-! ### Null lines -/

/-- The graph of a unit-speed geodesic line `ℓ` of `X`, a **null line**, is a causal curve over
`ℝ`. -/
theorem causalCurveIn_nullLine {ℓ : ℝ → X} (hℓ : ∀ s s', dist (ℓ s) (ℓ s') = |s - s'|) :
    (staticCausality X).CausalCurveIn ⊤ univ fun τ => (τ, ℓ τ) := by
  refine ⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ => ?_⟩
  rcases le_or_gt a b with hab | hab
  · exact causalCurveOn_graph ⟨fun τ _ τ' _ => by rw [hℓ, one_mul], fun _ _ => trivial⟩
  · exact CurveOn.of_lt hab

/-- **A null line is inextensible**: its time coordinate is unbounded both ways. -/
theorem inextensible_nullLine {ℓ : ℝ → X} (hℓ : ∀ s s', dist (ℓ s) (ℓ s') = |s - s'|) :
    (staticCausality X).Inextensible ⊤ univ fun τ => (τ, ℓ τ) :=
  Causality.inextensible_of_unbounded (f := Prod.fst)
    (fun x y h => by have := le_top_iff.1 h; linarith [dist_nonneg (x := x.2) (y := y.2)])
    (causalCurveIn_nullLine hℓ) (fun b => ⟨b + 1, by simp⟩) (fun b => ⟨b - 1, by simp⟩)

/-- **The counterexample behind DEC-15, abstractly.** Let `ℓ` be a unit-speed geodesic line of
`X` and `g : X → ℝ` with `g(ℓ τ) = τ` on `[0, 1]`. Then `T = t − g(x)` is not strictly increasing
along `≤` and `T⁻¹(0)` is not a Cauchy surface: the null line `τ ↦ (τ, ℓ τ)` lies in `T⁻¹(0)`
over `[0, 1]`. -/
theorem not_strict_and_not_isCauchySurface {ℓ : ℝ → X}
    (hℓ : ∀ s s', dist (ℓ s) (ℓ s') = |s - s'|) {g : X → ℝ} (hgℓ : ∀ τ ∈ Icc (0 : ℝ) 1, g (ℓ τ) = τ) :
    (∃ x y : ℝ × X, (staticCausality X).le ⊤ x y ∧ x ≠ y ∧ x.1 - g x.2 = y.1 - g y.2) ∧
      ¬ (staticCausality X).IsCauchySurface ((fun p : ℝ × X => p.1 - g p.2) ⁻¹' {0}) := by
  have h0 : g (ℓ 0) = 0 := hgℓ 0 ⟨le_rfl, zero_le_one⟩
  have h1 : g (ℓ 1) = 1 := hgℓ 1 ⟨zero_le_one, le_rfl⟩
  refine ⟨⟨(0, ℓ 0), (1, ℓ 1), ?_, fun h => by simp [Prod.ext_iff] at h, by simp [h0, h1]⟩, ?_⟩
  · rw [le_top_iff, hℓ]; norm_num
  · intro hS
    obtain ⟨x, -, huniq⟩ := hS univ _ (inextensible_nullLine hℓ)
    have e0 := huniq (0, ℓ 0) ⟨⟨0, trivial, rfl⟩, by simp [h0]⟩
    have e1 := huniq (1, ℓ 1) ⟨⟨1, trivial, rfl⟩, by simp [h1]⟩
    have := e0.trans e1.symm
    simp [Prod.ext_iff] at this

/-! ### No maximal chain -/

/-- If `X` has two points, every open set contains two non-empty open sets with no causal
relation between them: two small balls at the same time, spatially apart. -/
theorem hasUnrelatedOpensIn [Nontrivial X] (U : Opens (ℝ × X)) :
    (staticCausality X).HasUnrelatedOpensIn U := by
  intro O hO hne _
  obtain ⟨z, hz⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO z hz
  obtain ⟨y, hy⟩ := exists_ne z.2
  obtain ⟨g, hg0, -, hg⟩ := GeodesicSpace.exists_geodesic z.2 y
  have hd : 0 < dist z.2 y := dist_pos.2 hy.symm
  set s := min 1 (ρ / (4 * dist z.2 y)) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsρ : s * dist z.2 y ≤ ρ / 4 := by
    have := min_le_right 1 (ρ / (4 * dist z.2 y))
    rw [← hs, le_div_iff₀ (by positivity)] at this
    linarith
  set w := g s
  set r := s * dist z.2 y with hr
  have hr0 : 0 < r := by positivity
  have hw : dist z.2 w = r := by
    rw [← hg0]
    rw [hg 0 ⟨le_rfl, zero_le_one⟩ s ⟨hs0.le, hs1⟩, zero_sub, abs_neg, abs_of_pos hs0]
  refine ⟨ball z (r / 4), ball (z.1, w) (r / 4), isOpen_ball, isOpen_ball,
    ⟨z, mem_ball_self (by linarith)⟩, ⟨_, mem_ball_self (by linarith)⟩,
    (ball_subset_ball (by linarith)).trans hball, fun x hx => hball ?_, fun a ha b hb => ?_⟩
  · rw [mem_ball] at hx ⊢
    have : dist ((z.1, w) : ℝ × X) z = r := by
      rw [Prod.dist_eq, dist_self, dist_comm, hw, max_eq_right hr0.le]
    linarith [dist_triangle x (z.1, w) z]
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at ha hb
  simp only at hb
  have htri := dist_triangle4 z.2 a.2 b.2 w
  rw [dist_comm z.2 a.2] at htri
  have key : ∀ x y : ℝ × X, (staticCausality X).le U x y → dist x.2 y.2 ≤ y.1 - x.1 :=
    fun x y h => le_top_iff.1 ((staticCausality X).le_mono le_top h)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := key a b h
    linarith [ha.1.1, ha.1.2, hb.1.1, hb.1.2, ha.2, hb.2]
  · have := key b a h
    rw [dist_comm] at this
    linarith [ha.1.1, ha.1.2, hb.1.1, hb.1.2, ha.2, hb.2]

/-- **No maximal causal chain** (`def:maximal_chain`, as written) in a static spacetime over a
geodesic space with two points: by `not_isMaximalChain_of_hasUnrelatedOpensIn`. -/
theorem not_isMaximalChain [Nontrivial X] (S : Set (ℝ × X)) :
    ¬ (staticCausality X).IsMaximalChain S :=
  Causality.not_isMaximalChain_of_hasUnrelatedOpensIn_top (hasUnrelatedOpensIn ⊤) S

end staticCausality

end Causal
