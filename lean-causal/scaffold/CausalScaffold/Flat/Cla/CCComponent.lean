import CausalScaffold.Flat.CauchyComplete

/-!
# `CausalScaffold.Flat.Cla.CCComponent` — connectedness is free for spacelike Lipschitz hypersurfaces

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4.
**No label is marked**: these are infrastructure lemmas for the smoothing step of
`Flat/Cla/CompactComplete.lean` (`exists_isSpacelikeLipschitz_of_isCompact_cauchy`, serving
`bthm:cauclo`, `GHFspace.tex:353`, unmarked). Cited UNMARKED: `[2.4]` Cauchy-complete — l.551–553
(prose, DEC-35, a reading). Line numbers are those of the labelled
`papers/barbot/legacy/labeled/GHFspace.tex`.

> A GH spacetime is *Cauchy-complete* if it admits a Cauchy hypersurface where the ambiant
> lorentzian metric restricts as a complete riemanian metric. (l.551–553)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

## Main declarations
* `exists_opens_isPreconnected_of_isSpacelikeLipschitzIn` — a spacelike Lipschitz hypersurface
  `T` of an open `V ⊆ 𝐌ⁿ` is locally connected: every `p ∈ T` has an open `W ≤ V` around it with
  `T ∩ W` preconnected (in the frame of `locGraph`, `T ∩ W` is the graph of `f` over a ball).
* `isSpacelikeLipschitz_connectedComponentIn` — a connected component of a spacelike Lipschitz
  `H ⊆ M` is spacelike Lipschitz (cut each chart picture by such a `W`, then
  `IsSpacelikeLipschitzIn.restrict`).
* `exists_isConnected_isSpacelikeLipschitz_subset` — a nonempty compact spacelike Lipschitz `H` in
  a Hausdorff `M` contains a compact CONNECTED spacelike Lipschitz `H₀` (a connected component).
  This discharges the connectedness half of the smoothing step's obstruction (iii).
* `isSpacelikeLipschitz_singleton_zero` — for `d = 0` (Barbot's `n = 1`) every point is a spacelike
  Lipschitz hypersurface (the graph of a constant over the one-point `ℝ⁰`, slope `c = 0`). This
  closes the smoothing step at `d = 0`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| (none: infrastructure for l.551–553) | the lemmas hold for any `M` charted over `𝐌ⁿ`; `T2Space M` only for compactness of the component |

## SCOPE (disclosed)
* Nothing here constructs a spacelike Lipschitz hypersurface for `d ≥ 1`: the smoothing proper
  stays a tagged `sorry` in `CompactComplete.lean` (`exists_nonempty_isSpacelikeLipschitz_succ`).
* Namespace `Causal.Flat.Cla`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written for the
Barbot campaign (WP-34e closer pass on `CompactComplete`).
-/

namespace Causal.Flat.Cla

open Set TopologicalSpace Topology Metric
open scoped NNReal Pointwise

variable {d : ℕ}

/-- **A spacelike Lipschitz hypersurface of `V` is locally connected**: around every `p ∈ T` there
is an open `W ≤ V` with `T ∩ W` preconnected — in the frame `g` of `locGraph`, `T ∩ W` is
`g⁻¹` of the graph of the `c`-Lipschitz `f` over a ball (`W` the `g`-preimage of a sup-norm ball
inside `g • O`, whose radius also keeps the ball of `ℝᵈ` inside `U`). -/
theorem exists_opens_isPreconnected_of_isSpacelikeLipschitzIn {V : Opens (Minkowski d)}
    {T : Set (Minkowski d)} (h : IsSpacelikeLipschitzIn V T) {p : Minkowski d} (hp : p ∈ T) :
    ∃ W : Opens (Minkowski d), p ∈ W ∧ W ≤ V ∧ IsPreconnected (T ∩ (W : Set (Minkowski d))) := by
  obtain ⟨g, O, U, f, c, hc, hpO, hOV, hU, hf, hgr⟩ := h.locGraph p hp
  set q₀ : Minkowski d := g • p with hq₀def
  have hq₀ : q₀ ∈ g • (O : Set (Minkowski d)) ∩ graphOver U f := by
    rw [← hgr]; exact ⟨p, ⟨hp, hpO⟩, rfl⟩
  have hgO : IsOpen (g • (O : Set (Minkowski d))) := by
    rw [← coe_smulOpens]; exact (smulOpens g O).isOpen
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 hgO q₀ hq₀.1
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 hU q₀.2 hq₀.2.1
  set r := min r₁ r₂ with hrdef
  have hr : 0 < r := lt_min hr₁ hr₂
  have hball₁ : ball q₀ r ⊆ g • (O : Set (Minkowski d)) :=
    (ball_subset_ball (min_le_left _ _)).trans hb₁
  have hball₂ : ball q₀.2 r ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hb₂
  -- the graph of `f` over the ball
  set γ : EuclideanSpace ℝ (Fin d) → Minkowski d := fun y => (f y, y) with hγ
  have hγmem : ∀ y ∈ ball q₀.2 r, γ y ∈ ball q₀ r := by
    intro y hy
    have hyU := hball₂ hy
    have hfy : dist (f y) (f q₀.2) ≤ c * dist y q₀.2 := hf.dist_le_mul y hyU q₀.2 hq₀.2.1
    have hc1 : (c : ℝ) ≤ 1 := by exact_mod_cast hc.le
    have hd : dist y q₀.2 < r := hy
    rw [mem_ball, Prod.dist_eq]
    refine max_lt ?_ hd
    show dist (f y) q₀.1 < r
    rw [hq₀.2.2]
    calc dist (f y) (f q₀.2) ≤ c * dist y q₀.2 := hfy
      _ ≤ 1 * dist y q₀.2 := mul_le_mul_of_nonneg_right hc1 dist_nonneg
      _ < r := by rw [one_mul]; exact hd
  have hγcont : ContinuousOn γ (ball q₀.2 r) :=
    (hf.continuousOn.mono hball₂).prodMk continuousOn_id
  have hcont : Continuous fun q : Minkowski d => g • q := continuous_const_smul g
  let W : Opens (Minkowski d) :=
    ⟨(V : Set (Minkowski d)) ∩ (fun q => g • q) ⁻¹' ball q₀ r,
      V.isOpen.inter (isOpen_ball.preimage hcont)⟩
  have hTW : T ∩ (W : Set (Minkowski d)) = (fun q => g⁻¹ • q) '' (γ '' ball q₀.2 r) := by
    ext q
    constructor
    · rintro ⟨hqT, hqV, hqb⟩
      have hqO : q ∈ (O : Set (Minkowski d)) := by
        have := hball₁ hqb
        rwa [smul_mem_smul_set_iff] at this
      have hgq : g • q ∈ g • (T ∩ (O : Set (Minkowski d))) :=
        smul_mem_smul_set ⟨hqT, hqO⟩
      rw [hgr] at hgq
      have hy : (g • q).2 ∈ ball q₀.2 r := by
        have h1 : dist (g • q) q₀ < r := hqb
        rw [Prod.dist_eq] at h1
        exact (le_max_right _ _).trans_lt h1
      refine ⟨γ (g • q).2, ⟨(g • q).2, hy, rfl⟩, ?_⟩
      have hγeq : γ (g • q).2 = g • q := Prod.ext hgq.2.2.symm rfl
      show g⁻¹ • γ (g • q).2 = q
      rw [hγeq, inv_smul_smul]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hw : γ y ∈ g • (O : Set (Minkowski d)) ∩ graphOver U f :=
        ⟨hball₁ (hγmem y hy), hball₂ hy, rfl⟩
      rw [← hgr] at hw
      obtain ⟨t, ⟨htT, htO⟩, ht0⟩ := hw
      have ht : g • t = γ y := ht0
      have hq : g⁻¹ • γ y = t := by rw [← ht, inv_smul_smul]
      show g⁻¹ • γ y ∈ T ∩ (W : Set (Minkowski d))
      rw [hq]
      refine ⟨htT, hOV htO, ?_⟩
      show g • t ∈ ball q₀ r
      rw [ht]; exact hγmem y hy
  refine ⟨W, ⟨hOV hpO, mem_ball_self hr⟩, fun q hq => hq.1, ?_⟩
  rw [hTW]
  exact ((convex_ball _ _).isPreconnected.image γ hγcont).image _ (continuous_const_smul g⁻¹).continuousOn

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]

/-- **A connected component of a spacelike Lipschitz hypersurface is spacelike Lipschitz**: at
`y` in the component, the chart picture `T` of `H` is cut by the open `W` of
`exists_opens_isPreconnected_of_isSpacelikeLipschitzIn`; `e⁻¹(T ∩ W)` is a preconnected subset of
`H` through `y`, hence inside the component, so the component's picture in `W` is `T ∩ W`
(`IsSpacelikeLipschitzIn.restrict`). -/
theorem isSpacelikeLipschitz_connectedComponentIn {H : Set M} (hL : IsSpacelikeLipschitz d H)
    (x : M) : IsSpacelikeLipschitz d (connectedComponentIn H x) := by
  intro y hy
  have hyH : y ∈ H := connectedComponentIn_subset _ _ hy
  have hcomp : connectedComponentIn H x = connectedComponentIn H y := connectedComponentIn_eq hy
  obtain ⟨V, hyV, hVt, hT⟩ := hL y hyH
  set e := chartAt (Minkowski d) y with he
  have hys : y ∈ e.source := mem_chart_source _ _
  set T := e '' (H ∩ e.source) ∩ (V : Set (Minkowski d)) with hTdef
  have heyT : e y ∈ T := ⟨⟨y, ⟨hyH, hys⟩, rfl⟩, hyV⟩
  obtain ⟨W, heyW, hWV, hpc⟩ := exists_opens_isPreconnected_of_isSpacelikeLipschitzIn hT heyT
  have hWt : (W : Set (Minkowski d)) ⊆ e.target := fun q hq => hVt (hWV hq)
  -- the pull-back of `T ∩ W` lies in the component
  have hsub : e.symm '' (T ∩ (W : Set (Minkowski d))) ⊆ connectedComponentIn H x := by
    rw [hcomp]
    refine (hpc.image _ (e.continuousOn_symm.mono fun q hq => hWt hq.2)).subset_connectedComponentIn
      ⟨e y, ⟨heyT, heyW⟩, e.left_inv hys⟩ ?_
    rintro _ ⟨q, ⟨⟨⟨z, ⟨hzH, hzs⟩, rfl⟩, -⟩, -⟩, rfl⟩
    rw [e.left_inv hzs]; exact hzH
  have heq : e '' (connectedComponentIn H x ∩ e.source) ∩ (W : Set (Minkowski d)) =
      T ∩ (W : Set (Minkowski d)) := by
    ext q
    constructor
    · rintro ⟨⟨z, ⟨hz, hzs⟩, rfl⟩, hqW⟩
      exact ⟨⟨⟨z, ⟨connectedComponentIn_subset _ _ hz, hzs⟩, rfl⟩, hWV hqW⟩, hqW⟩
    · intro hq
      have hq' := hq
      obtain ⟨⟨⟨z, ⟨hzH, hzs⟩, rfl⟩, -⟩, hqW⟩ := hq'
      refine ⟨⟨z, ⟨?_, hzs⟩, rfl⟩, hqW⟩
      have := hsub ⟨e z, hq, e.left_inv hzs⟩
      exact this
  refine ⟨W, heyW, hWt, ?_⟩
  rw [heq]
  exact hT.restrict hWV

/-- **Connectedness is free**: a nonempty compact spacelike Lipschitz `H` in a Hausdorff `M`
contains a compact connected spacelike Lipschitz `H₀` — the connected component of any of its
points (closed, since its closure is a preconnected subset of the closed `H` through the point). -/
theorem exists_isConnected_isSpacelikeLipschitz_subset [T2Space M] {H : Set M}
    (hHc : IsCompact H) (hne : H.Nonempty) (hL : IsSpacelikeLipschitz d H) :
    ∃ H₀ ⊆ H, IsCompact H₀ ∧ IsConnected H₀ ∧ IsSpacelikeLipschitz d H₀ := by
  obtain ⟨x, hx⟩ := hne
  set H₀ := connectedComponentIn H x
  have hsub : H₀ ⊆ H := connectedComponentIn_subset _ _
  have hconn : IsConnected H₀ := isConnected_connectedComponentIn_iff.2 hx
  have hcl : IsClosed H₀ := by
    refine closure_subset_iff_isClosed.1 ?_
    exact hconn.isPreconnected.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal hsub hHc.isClosed)
  exact ⟨H₀, hsub, hHc.of_isClosed_subset hcl hsub, hconn,
    isSpacelikeLipschitz_connectedComponentIn hL x⟩

end Manifold

section Zero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski 0) M]

/-- **In dimension `d = 0` (Barbot's `n = 1`) a point is a spacelike Lipschitz hypersurface**:
`ℝ⁰` is one point, so in the chart at `x` the picture `{e x}` is the graph over `univ` of the
constant `(e x).1`, with slope `c = 0 < 1`; achronality is the irreflexivity of `≪` in `𝐌¹`. -/
theorem isSpacelikeLipschitz_singleton_zero (x : M) : IsSpacelikeLipschitz 0 ({x} : Set M) := by
  rintro y rfl
  set e := chartAt (Minkowski 0) y with he
  have hys : y ∈ e.source := mem_chart_source _ _
  let V : Opens (Minkowski 0) := ⟨e.target, e.open_target⟩
  have hT : e '' ({y} ∩ e.source) ∩ (V : Set (Minkowski 0)) = {e y} := by
    ext q
    constructor
    · rintro ⟨⟨z, ⟨rfl, -⟩, rfl⟩, -⟩; rfl
    · rintro rfl; exact ⟨⟨y, ⟨rfl, hys⟩, rfl⟩, e.map_source hys⟩
  refine ⟨V, e.map_source hys, subset_rfl, ?_⟩
  rw [hT]
  refine ⟨singleton_subset_iff.2 (e.map_source hys), ?_, ?_⟩
  · rintro p rfl q rfl hpq
    have := minkowski_lt_top_iff.1 ((minkowski 0).lt_mono le_top hpq)
    simp at this
  · rintro p rfl
    refine ⟨1, V, univ, fun _ => (e y).1, 0, zero_lt_one, e.map_source hys, le_rfl, isOpen_univ,
      (LipschitzWith.const _).lipschitzOnWith, ?_⟩
    rw [one_smul, one_smul]
    ext q
    constructor
    · rintro ⟨rfl, hq⟩; exact ⟨hq, trivial, rfl⟩
    · rintro ⟨hqV, -, hq1⟩
      refine ⟨Prod.ext hq1 (Subsingleton.elim _ _), hqV⟩

end Zero

end Causal.Flat.Cla
